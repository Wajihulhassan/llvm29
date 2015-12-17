//===- DirectedPass.cpp - Directed Symbolic Execution Pass ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//


#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/type_traits.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Analysis/DebugInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"

#include <vector>
#include <utility>
#include <fstream>

using namespace llvm;
namespace {
  class Hello : public ModulePass {
  public:
    static char ID; 
    std::vector<BasicBlock*> mod_bbs;
   
    std::vector<std::string> bbs;
    std::vector<BasicBlock*> *diff_bbs_vec;

    std::vector<std::vector<BasicBlock*> > paths;
    std::vector<BasicBlock*> *my_diff_bbs;
    DominatorTree* domTree;
    std::vector<Instruction*> write_vec;
    std::vector<Instruction*> cond_vec;
    std::set<BasicBlock*> ACN;
    std::set<BasicBlock*> AWN;

    int my_tt;
    int *g;
    bool called_from_klee = false;

    std::map<BasicBlock *, std::set<BasicBlock *> > controlDeps_;

   Hello() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) {
      errs() << "Starting my diff/control/data dependence Analysis" << "\n";
      if(!called_from_klee)
	diff_bbs_vec=new std::vector<BasicBlock*>();
      // It is essential that both the original and modified version should be in same module

      Function *F1 = M.getFunction("func");
      Function *F2 = M.getFunction("func_2");
      domTree = &getAnalysis<DominatorTree>(*F2); // For reachability
      PostDominatorTree &PDT = getAnalysis<PostDominatorTree>(*F2); // For control dependance
      MemoryDependenceAnalysis &MDA = getAnalysis<MemoryDependenceAnalysis>(*F2);  // For data depen

      getControlDependencies(*F2, PDT);
      //  All the basic blocks for original version
      std::vector<BasicBlock*> temp_bbs;
      for (Function::iterator bb = F1->begin() , e = F1->end(); bb !=e ;++bb ){
	temp_bbs.push_back(bb);
      }
      
      // Calculating simple diff at basic block level
      int counter = 0;
      for (Function::iterator bb = F2->begin() , e = F2->end(); bb !=e ;++bb ){
	BasicBlock * LL = temp_bbs.at(counter);
	BasicBlock * RR = bb;
	counter++;
	errs() << LL->getName() <<  " ---- " << RR->getName() <<"\n" ;
	if(LL->getName().compare(RR->getName()) != 0){
	  // Fixme handle the preprocessing
	  errs() << "[Warning] Basic Block Names are not equal FIXME" << "\n" ;
	  continue;
	}
	// This will update ACN and AWN sets
        diff(LL,RR);	
      }
      bool updated;
      // Updating the ACN and AWN sets until it converges
      typedef std::set<BasicBlock*>::iterator set_bb_iterator;
      typedef std::vector<Instruction*>::iterator vec_inst_iterator;

      // For each of the condition statement what is its data dependence
      std::map<Instruction* , Instruction*> cond_dep;
      for (vec_inst_iterator i_iter = cond_vec.begin(), i_iter_end = cond_vec.end();i_iter != i_iter_end ; i_iter++){
	Instruction* II = *i_iter;
	MemDepResult Res = MDA.getDependency(II);
	Instruction* temp_i = Res.getInst();
	cond_dep[II] = temp_i;
      }
      do{
	updated = false;
	// =======================================================================
	//  if n_i E ACN and n_j E Cond and Controldep(n_i, n_j)
	for (set_bb_iterator iter = ACN.begin(),iter_end=ACN.end();iter!=iter_end;iter++){
	  BasicBlock* acn_bb = *iter;
	  for (vec_inst_iterator i_iter = cond_vec.begin(), i_iter_end = cond_vec.end();i_iter != i_iter_end ; i_iter++){
	    Instruction* II = *i_iter;
	    BasicBlock* temp_bb = II->getParent();
	    if(!ACN.count(temp_bb)){
	      if(isControlDep(acn_bb,temp_bb)){
		ACN.insert(temp_bb);
		updated = true;
	      }
	    }
	  }
	} // outer loop for acn First condition

	// =======================================================================
	//  if n_i E ACN and n_j E write and Controldep(n_i, n_j)
	for (set_bb_iterator iter = ACN.begin(),iter_end=ACN.end();iter!=iter_end;iter++){
	  BasicBlock* acn_bb = *iter;
	  for (vec_inst_iterator i_iter = write_vec.begin(), i_iter_end = write_vec.end();i_iter != i_iter_end ; i_iter++){
	    Instruction* II = *i_iter;
	    BasicBlock* temp_bb = II->getParent();
	    if(!AWN.count(temp_bb)){
	      if(isControlDep(acn_bb,temp_bb)){
		AWN.insert(temp_bb);
	      }
	    }
	  }
	} // outer loop for awn Second condition

	// == Data dependence ===================================================
     
	std::map<Instruction*,std::set<Instruction*> > writeUseMap;
	for (set_bb_iterator iter = AWN.begin(),iter_end=AWN.end();iter!=iter_end;iter++){
	  BasicBlock* awn_bb = *iter;
	  for(BasicBlock::iterator inst = awn_bb->begin(), inst_end = awn_bb->end(); inst != inst_end ; inst++){
	    Instruction * write_inst = inst;
	    if(isa<StoreInst>(write_inst)){
	      Value *second_op = write_inst->getOperand(1);
	      std::set<Instruction*> temp_set;
	      for(Value::use_iterator i = second_op->use_begin(), ie = second_op->use_end(); i!=ie; ++i){
		if (Instruction *Inst = dyn_cast<Instruction>(*i)) {		  
		  // Only if there is path from store to to use
		  if(Ispotentiallyreachable(awn_bb,Inst->getParent(),domTree)){
		    temp_set.insert(Inst);
		  }
		}
	      } 
	      writeUseMap[inst]=temp_set;
	    } //if storeinst
	  }
	} // outer loop for datadepent
	// Updating ACN
	for(std::map<Instruction*,std::set<Instruction*> >::iterator  iter = writeUseMap.begin(), iter_end = writeUseMap.end();iter!=iter_end;iter++){
	  std::set<Instruction*> temp_set = iter->second;
	  for(std::map<Instruction*,Instruction*>::iterator cond_iter = cond_dep.begin(), cond_iter_end = cond_dep.end();cond_iter!=cond_iter_end;cond_iter++){
	    Instruction* dep = cond_iter->second;
	    if(temp_set.count(dep)){
	      BasicBlock* start_cfg = iter->first->getParent();
	      BasicBlock* end_cfg = cond_iter->first->getParent();
	      if(Ispotentiallyreachable(start_cfg,end_cfg,domTree)){
		if(!ACN.count(end_cfg)){
		  ACN.insert(end_cfg);
		  updated = true;
		}
	      }
	    }
	  }
	}

      }while(updated);
      errs() << "Size of ACN and AWN vectors(updated) " << ACN.size()<<" --- " << AWN.size()  <<"\n" ;
     
      std:: ofstream diff_file("/tmp/diff_file.txt");
      diff_bbs_vec->clear();
      for(std::set<BasicBlock*>::iterator iter = ACN.begin(), iter_end = ACN.end(); iter!=iter_end ; iter++){
	BasicBlock* bb = *iter;
	diff_bbs_vec->push_back(bb);
	errs() << "ACN = " << bb->getName() << '\n';
	std::string str = bb->getName();
	diff_file << str << "\n";
      }
      for(std::set<BasicBlock*>::iterator iter = AWN.begin(), iter_end = AWN.end(); iter!=iter_end ; iter++){
	BasicBlock* bb = *iter;
	errs() << "AWN = " << bb->getName() << '\n';
      }
      return false;
    } // runOnModule
    
    // ============= Finding instruction level differences and keeping track of them ========
    void diff(BasicBlock *L, BasicBlock *R) {
      BasicBlock::iterator LI = L->begin(), LE = L->end();
      BasicBlock::iterator RI = R->begin();
      bool flag = false;
      do {
	assert(LI != LE && RI != R->end());
	Instruction *LeftI = &*LI, *RightI = &*RI;
	// Adding cond and write statements to vector
	if(isa<StoreInst>(RI)){
	  write_vec.push_back(RI);
	}else if(isa<CmpInst>(RI)){
	  cond_vec.push_back(RI);
	}

	if (diff(LeftI, RightI, flag)) {
	  // Adding cond and write to affected sets
	  if(isa<StoreInst>(RI)){
	    AWN.insert(R);
	  }else if(isa<CmpInst>(RI)){
	    ACN.insert(R);
	  }
	  bbs.push_back(L->getName());
	  diff_bbs_vec->push_back(R);
	  return ;
	}	
	++LI, ++RI;
	flag = false;
      } while (LI != LE);

    }

    bool diff(Instruction *L, Instruction *R, bool complain) {
      // Different opcodes always imply different operations.
      if (L->getOpcode() != R->getOpcode()) {
	if (complain) errs() << "different instruction types" << "\n";
	return true;
      }
      if (isa<CmpInst>(L)) {
	if (cast<CmpInst>(L)->getPredicate()
            != cast<CmpInst>(R)->getPredicate()) {
	  if (complain) errs()<<"different predicates"<< "\n";
	  return true;
	}
      } else if (isa<PHINode>(L)) {
	if (L->getType() != R->getType()) {
	  if (!L->getType()->isPointerTy() || !R->getType()->isPointerTy()) {
	    if (complain) errs() << "different phi types" << "\n" ;
	    return true;
	  }
	}
	return false;
	// Terminators.
      }  else if (isa<BranchInst>(L)) {
	BranchInst *LI = cast<BranchInst>(L);
	BranchInst *RI = cast<BranchInst>(R);
	if (LI->isConditional() != RI->isConditional()) {
	  if (complain) errs() << "branch conditionality differs" << "\n" ;
	  return true;
	}

	if (LI->isConditional()) {
	  if (!equivalentAsOperands(LI->getCondition(), RI->getCondition())) {
	    if (complain) errs() << "branch conditions differ" << "\n" ;
	    return true;
	  }
	  
	}
	return false;
      }else if (isa<UnreachableInst>(L)) {
	return false;
      }
      if (L->getNumOperands() != R->getNumOperands()) {
	if (complain) errs() << "instructions have different operand counts" << "\n";
	return true;
      } 
      if (isa<CallInst>(L)){
	if (complain) errs() << "Ignoring Call instruction" << "\n";
	return false;
      }
      for (unsigned I = 0, E = L->getNumOperands(); I != E; ++I) {
	if (complain) errs() << "Operands Loop" << "\n";
	Value *LO = L->getOperand(I), *RO = R->getOperand(I);
	if (!equivalentAsOperands(LO, RO)) {
	  if (complain) errs()<< "operands differ" << "\n";
	  return true;
	}
      }
      return false;
    } // bool diff()

    bool equivalentAsOperands(Constant *L, Constant *R) {
      // Use equality as a preliminary filter.
      if (L == R)
	return true;

      if (L->getValueID() != R->getValueID())
	return false;
    
      // Ask the engine about global values.
      if (isa<GlobalValue>(L))
	return equivalentAsOperands(cast<GlobalValue>(L),
					   cast<GlobalValue>(R));

      // Compare constant expressions structurally.
      if (isa<ConstantExpr>(L))
	return equivalentAsOperands(cast<ConstantExpr>(L),
				    cast<ConstantExpr>(R));
      if (isa<ConstantPointerNull>(L))
	return true;
      return false;
    } // equivalent ..()

    bool equivalentAsOperands(ConstantExpr *L, ConstantExpr *R) {
      if (L == R)
	return true;
      if (L->getOpcode() != R->getOpcode())
	return false;
      switch (L->getOpcode()) {
      case Instruction::ICmp:
      case Instruction::FCmp:
	if (L->getPredicate() != R->getPredicate())
	  return false;
	break;
      case Instruction::GetElementPtr:
	break;
      default:
	break;
      }
      if (L->getNumOperands() != R->getNumOperands())
	return false;
      for (unsigned I = 0, E = L->getNumOperands(); I != E; ++I)
	if (!equivalentAsOperands(L->getOperand(I), R->getOperand(I)))
	  return false;
      return true;
    } // equivalent .. ()

    bool equivalentAsOperands(Value *L, Value *R) {
      if (L->getValueID() != R->getValueID())
	return false;
      if (isa<Constant>(L))
	return equivalentAsOperands(cast<Constant>(L), cast<Constant>(R));
      // Pretend everything else is identical.
      return true;
    } // equivalent() ..

    // ================ Control Dependency findings ========================================
    // is cond_bb control dependent on acn_bb
    bool isControlDep(BasicBlock* acn_bb, BasicBlock* cond_bb){
      // get all the basic blocks dependent on the acn
      std::set<BasicBlock*> cont_dep = controlDeps_[acn_bb];
      // check cond_bb exsit in set
      if(cont_dep.count(cond_bb)){
	return true;
      }
      return false;

    }
    std::vector<std::vector<BasicBlock*> > getNonPDomEdges(  Function &F, const PostDominatorTree &PDT) const {
      std::vector<std::vector<BasicBlock*> > S;
      for (Function::iterator BBi = F.begin(), BBe = F.end(); BBi != BBe; ++BBi) {
	BasicBlock *A = &(*BBi);
	// Get the edge A->B, ie get the successors of A
	//errs() << "HEAD --- " << A->getName()  << "\n";
	for (succ_iterator Si = succ_begin(A), Se = succ_end(A); 
	     Si != Se; ++ Si) {
	  BasicBlock *B = *Si;
	  //errs() << "SUCC --- " << B->getName()  << "\n";
	  if (!PDT.properlyDominates(B, A)) {
	    // B does not post-dominate A in the edge (A->B), this is the criteria
	    // for being in the set S
	    std::vector<BasicBlock*> temp_vec;
	    temp_vec.push_back(B); //head
	    temp_vec.push_back(A); // tail
	    S.push_back(temp_vec);
	  }
	}
      }

      return S;
    }

    void updateControlDependencies(const std::vector<std::vector<BasicBlock*> > &S, 
						      PostDominatorTree &PDT) {
      BasicBlock *L;
      for (std::vector<std::vector<BasicBlock*> >::size_type i = 0; i < S.size(); ++i) {
	std::vector<BasicBlock*> curEdge;
	curEdge = S[i];

	BasicBlock *A;
	BasicBlock *B;

	A = curEdge.at(1); // tail
 	B = curEdge.at(0); // head

	L = PDT.findNearestCommonDominator(A, B);
	if (L == NULL) {
	  continue;
	}

	DomTreeNode *domNodeA;
	domNodeA = PDT.getNode(A);

	DomTreeNode *parentA;
	parentA = domNodeA->getIDom();  // NULL?
	DomTreeNode *domNodeB;
	domNodeB = PDT.getNode(B);
	DomTreeNode *curNode;
	curNode = domNodeB;
	std::set<BasicBlock *> &depSet = controlDeps_[A];

	while (curNode != parentA) {

	  errs() << "[DEBUG] Iterating up post dom tree\n";

	  // Mark each node visited on our way to the parent of A, but not A's
	  // parent, as control dependent on A
	  depSet.insert(curNode->getBlock());

	  // Update cur
	  curNode = curNode->getIDom();
	} // end while (cur != parentA)
	// Because std::map::operator[] returns a reference to the set then I
	// believe we do not need to do any insertions

	//errs() << "[DEBUG] size of depSet: " << depSet.size() << '\n';
	//errs() << "[DEBUG] size of map value: " << controlDeps_[A].size() << '\n';
	assert(depSet.size() == controlDeps_[A].size() && "map size mis-match");
      } // end for(vector<>)
    }

    void getControlDependencies(Function &F, PostDominatorTree &PDT) {
      // All edges in the CFG (A->B) such that B does not post-dominate A
      std::vector<std::vector<BasicBlock*> > S;

      S = getNonPDomEdges(F, PDT);
      //errs() << "[DEBUG] Size of set S: " << S.size() << '\n';
      updateControlDependencies(S, PDT);
    }



    bool Ispotentiallyreachable(const BasicBlock *A, const BasicBlock *B , const DominatorTree *DT) {
      assert(A->getParent() == B->getParent() &&
	     "This analysis is function-local!");

      SmallVector<BasicBlock*, 32> Worklist;
      Worklist.push_back(const_cast<BasicBlock*>(A));

      return isPotentiallyReachableFromMany(Worklist, const_cast<BasicBlock *>(B),
					    DT);
    }

    bool isPotentiallyReachableFromMany( SmallVectorImpl<BasicBlock *> &Worklist, BasicBlock *StopBB,
					 const DominatorTree *DT ) {

      // Limit the number of blocks we visit. The goal is to avoid run-away compile
      // times on large CFGs without hampering sensible code. Arbitrarily chosen.
      unsigned Limit = 32;
      std::set<BasicBlock*> Visited;
      do {
	BasicBlock *BB = Worklist.pop_back_val();
	if (!Visited.insert(BB).second)
	  continue;
	if (BB == StopBB)
	  return true;
	if (DT && DT->dominates(BB, StopBB))
	  return true;
	if (!--Limit) {
	  // We haven't been able to prove it one way or the other. Conservatively
	  // answer true -- that there is potentially a path.
	  return true;
	}
	  Worklist.append(succ_begin(BB), succ_end(BB));
      } while (!Worklist.empty());

      // We have exhausted all possible paths and are certain that 'To' can not be
      // reached from 'From'.
      return false;
    }
  
 
    // Other passes I need =======================================================
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<MemoryDependenceAnalysis>();
    AU.setPreservesAll();
    AU.addRequired<DominatorTree>();
    AU.addRequired<PostDominatorTree>();
  }
}; // class
  // External Interface of this pass for KLEE
  ModulePass *createDiffBlocksPass(std::vector<BasicBlock*> *diff_bb_vec)
  {    
    Hello *cg = new Hello();
    errs() <<  " IN the create Diff Blocks Pass" << '\n';
    cg->called_from_klee = true;
    cg->diff_bbs_vec = diff_bb_vec;
    return cg;
  }

} //namespace



// ===========================================================================================
// ============================Second Pass for Reachability===================================
char Hello::ID = 0;
static RegisterPass<Hello> X("diffFinder", "Identify differences between two versions of program at basic block level");



namespace {
  // Hello2 - The second implementation with getAnalysisUsage implemented.
  class Hello2 : public ModulePass {
  public:
    static char ID; // Pass identification, replacement for typeid
    BasicBlock* targetBB;
    int * reachable;
    BasicBlock* startBB;
    std::vector<BasicBlock*> bb_vec;
    DominatorTree* domTree;
    std::string target_bb_name;
    Hello2() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) {
      errs() << "Function: I Am here wajih YYAYAYAY " << "\n";
      Function *F2 = M.getFunction("func_2");
      domTree = &getAnalysis<DominatorTree>(*F2);
      for (Function::iterator bb = F2->begin() , e = F2->end(); bb !=e ;++bb ){
	bb_vec.push_back(bb);
	std::string temp_str = bb->getName();
	if(target_bb_name.compare(temp_str) == 0){
	  //errs() << target_bb_name.c_str() << " YAYA Match found " << temp_str.c_str()  <<'\n' ;
	  targetBB = bb;
	}
      }
      errs().write_escaped(F2->getName()) << '\n';
      errs() << targetBB->getName()  <<  " checking reachability from  " <<  startBB->getName() << "\n" ;
      if(Ispotentiallyreachable(startBB,targetBB,domTree)){
  	  errs() << targetBB->getName()  <<  " is reachable from  " <<  startBB->getName() << "\n" ;
	  *(this->reachable) = 1;
      }else{
	errs() << targetBB->getName()  <<  " is not reachable from  " <<  startBB->getName() << "\n" ;
	*(this->reachable) = 0;
      }
      return false;
    }

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DominatorTree>();
    }

    bool Ispotentiallyreachable(const BasicBlock *A, const BasicBlock *B , const DominatorTree *DT) {
      errs() << A->getParent()->getName() <<  " can reach to  " <<  B->getParent()->getName() << "\n" ;
      assert(A->getParent() == B->getParent() &&
	     "This analysis is function-local!");

      SmallVector<BasicBlock*, 32> Worklist;
      Worklist.push_back(const_cast<BasicBlock*>(A));

      return isPotentiallyReachableFromMany(Worklist, const_cast<BasicBlock *>(B),
					    DT);
    }

    bool isPotentiallyReachableFromMany( SmallVectorImpl<BasicBlock *> &Worklist, BasicBlock *StopBB,
					 const DominatorTree *DT ) {

      // Limit the number of blocks we visit. The goal is to avoid run-away compile
      // times on large CFGs without hampering sensible code. Arbitrarily chosen.
      unsigned Limit = 32;
      std::set<BasicBlock*> Visited;
      do {
	BasicBlock *BB = Worklist.pop_back_val();
	if (!Visited.insert(BB).second)
	  continue;
	if (BB == StopBB)
	  return true;
	if (DT && DT->dominates(BB, StopBB))
	  return true;
	if (!--Limit) {
	  // We haven't been able to prove it one way or the other. Conservatively
	  // answer true -- that there is potentially a path.
	  return true;
	}
	  Worklist.append(succ_begin(BB), succ_end(BB));
      } while (!Worklist.empty());

      // We have exhausted all possible paths and are certain that 'To' can not be
      // reached from 'From'.
      return false;
    }

  };
  ModulePass *createReachabilityPass(std::string  t_bb, BasicBlock* s_bb, int* in)
  {    
    Hello2 *cg2 = new Hello2();
    cg2->target_bb_name = t_bb;
    cg2->reachable = in;
    cg2->startBB = s_bb;
    return cg2;
  }

}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("ReachabilityFinder", "Finds reachability from the source basicblock towards target basicblock");
