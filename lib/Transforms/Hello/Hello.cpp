//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
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

#define DEBUG_TYPE "hello"
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
#include "llvm/ADT/SmallSet.h"


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
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"

#include <vector>
#include <utility>
#include <fstream>

using namespace llvm;

//STATISTIC(HelloCounter, "Find the basic blocks that got changed");

namespace {
 
  class Hello : public ModulePass {
  public:
    static char ID; // Pass identification, replacement for typeid

    std::vector<BasicBlock*> mod_bbs;
    std::vector<BasicBlock*> temp_bbs;
    std::vector<std::string> bbs;
    std::vector<BasicBlock*> *diff_bbs_vec;
    std::vector<std::vector<BasicBlock*> > paths;
    std::vector<BasicBlock*> *my_diff_bbs;
    DominatorTree* domTree;
    int my_tt;
    int *g;

   Hello() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) {
      errs() << "Function: I Am here wajih " << "\n";
      Function *F1 = M.getFunction("func");
      Function *F2 = M.getFunction("func_2");
      domTree = &getAnalysis<DominatorTree>(*F2);


      errs() << "Function: " << F1->getName()<< "\n";
      for (Function::iterator bb = F1->begin() , e = F1->end(); bb !=e ;++bb ){
	temp_bbs.push_back(bb);
      }
      int counter = 0;


      for (Function::iterator bb = F2->begin() , e = F2->end(); bb !=e ;++bb ){
	BasicBlock * LL = temp_bbs.at(counter);
	BasicBlock * RR = bb;
	counter++;
	errs() << LL->getName() <<  " ---- " << RR->getName() <<"\n" ;
	if(LL->getName().compare(RR->getName()) != 0){
	  errs() << "Basic Block Names are not equal" << "\n" ;
	  continue;
	}
        diff(LL,RR);	
      }
      for (int c = 0; c<diff_bbs_vec->size();c++){
	BasicBlock * temp_bb=  diff_bbs_vec->at(c);
	errs()<< " Different BB ======= " << temp_bb->getName() << "\n" ;
      }
      *g = 3;

      // for (df_iterator<BasicBlock*> iter = df_begin(&F2->front()),iter_end = df_end(&F2->front()); iter != iter_end; ++iter) {
      // 	BasicBlock* BBB = *iter;
      // 	BasicBlock* diff_bb = diff_bbs_vec.at(2);
      // 	if(Ispotentiallyreachable(BBB,diff_bb,domTree))
      // 	  errs() << diff_bbs_vec.at(2)->getName()  <<  " is reachable from  " <<  BBB->getName() << "\n" ;
      // 	else
      // 	  errs() << diff_bbs_vec.at(2)->getName()  <<  " is not reachable from  " <<  BBB->getName() << "\n" ;
      // }
      
      
      return false;
    } // runOnModule
    void diff(BasicBlock *L, BasicBlock *R) {
      BasicBlock::iterator LI = L->begin(), LE = L->end();
      BasicBlock::iterator RI = R->begin();

      do {
	assert(LI != LE && RI != R->end());
	Instruction *LeftI = &*LI, *RightI = &*RI;
	// If the instructions differ, start the more sophisticated diff
	// algorithm at the start of the block.
	if (diff(LeftI, RightI, true)) {
	  bbs.push_back(L->getName());
	  diff_bbs_vec->push_back(R);
	  return ;
	}

	// // Otherwise, tentatively unify them.
	// if (!LeftI->use_empty())
	//   TentativeValues.insert(std::make_pair(LeftI, RightI));

	++LI, ++RI;
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

      // Nulls of the "same type" don't always actually have the same
      // type; I don't know why.  Just white-list them.
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
	// FIXME: inbounds?
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
      errs() << " I am here in equivalent Values " << "\n" ;
      // Fall out if the values have different kind.
      // This possibly shouldn't take priority over oracles.
      if (L->getValueID() != R->getValueID())
	return false;

      // Value subtypes:  Argument, Constant, Instruction, BasicBlock,
      //                  InlineAsm, MDNode, MDString, PseudoSourceValue

      if (isa<Constant>(L))
	return equivalentAsOperands(cast<Constant>(L), cast<Constant>(R));

      // if (isa<Instruction>(L))
      // 	return Values[L] == R || TentativeValues.count(std::make_pair(L, R));

      // if (isa<Argument>(L))
      // 	return Values[L] == R;

      // if (isa<BasicBlock>(L))
      // 	return Blocks[cast<BasicBlock>(L)] != R;

      // Pretend everything else is identical.
      return true;
    } // equivalent() ..


    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DominatorTree>();
      //AU.addRequired<CallGraph>();
      //AU.setPreservesCFG();
      AU.setPreservesAll();
      //AU.addRequired<MemoryDependenceAnalysis>();
      
      
    }

 
  }; // class
  ModulePass *createDiffBlocksPass(std::vector<BasicBlock*> *diff_bb_vec,int * in)
  {    
    Hello *cg = new Hello();
    cg->diff_bbs_vec = diff_bb_vec;
    cg->g = in;
    return cg;
  }

} //namespace

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass -Wajih");



namespace {
  // Hello2 - The second implementation with getAnalysisUsage implemented.
  class Hello2 : public ModulePass {
  public:
    static char ID; // Pass identification, replacement for typeid
    BasicBlock* targetBB;
    bool * reachable;
    BasicBlock* startBB;
    DominatorTree* domTree;
    Hello2() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) {
      errs() << "Function: I Am here wajih YYAYAYAY " << "\n";
      Function *F2 = M.getFunction("func_2");
      domTree = &getAnalysis<DominatorTree>(*F2);
      errs().write_escaped(F2->getName()) << '\n';
      errs() << targetBB->getName()  <<  " checking reachability from  " <<  startBB->getName() << "\n" ;
      if(Ispotentiallyreachable(startBB,targetBB,domTree))
  	  errs() << targetBB->getName()  <<  " is reachable from  " <<  startBB->getName() << "\n" ;
  	else
  	  errs() << targetBB->getName()  <<  " is not reachable from  " <<  startBB->getName() << "\n" ;
      return false;
    }

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DominatorTree>();
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

  };
  ModulePass *createReachabilityPass(BasicBlock*  t_bb, BasicBlock* s_bb, bool* in)
  {    
    Hello2 *cg2 = new Hello2();
    cg2->targetBB = t_bb;
    cg2->reachable = in;
    cg2->startBB = s_bb;
    return cg2;
  }

}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented) -WAJIH");
