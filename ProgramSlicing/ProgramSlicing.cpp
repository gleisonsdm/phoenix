#include "ProgramSlicing.h"

#include "../PDG/PDGAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm/CodeGen/UnreachableBlockElim.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/Sink.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include <iterator>
#include <queue>
#include <set>

namespace phoenix {

void DetatchDeadBlocks(
     ArrayRef<BasicBlock *> BBs,
     SmallVectorImpl<DominatorTree::UpdateType> *Updates,
     bool KeepOneInputPHIs) {
   for (auto *BB : BBs) {
     // Loop through all of our successors and make sure they know that one
     // of their predecessors is going away.
     SmallPtrSet<BasicBlock *, 4> UniqueSuccessors;
     for (BasicBlock *Succ : successors(BB)) {
       Succ->removePredecessor(BB, KeepOneInputPHIs);
       if (Updates && UniqueSuccessors.insert(Succ).second)
         Updates->push_back({DominatorTree::Delete, BB, Succ});
     }
 
     // Zap all the instructions in the block.
     while (!BB->empty()) {
       Instruction &I = BB->back();
       // If this instruction is used, replace uses with an arbitrary value.
       // Because control flow can't get here, we don't care what we replace the
       // value with.  Note that since this block is unreachable, and all values
       // contained within it must dominate their uses, that all uses will
       // eventually be removed (they are themselves dead).
       if (!I.use_empty())
         I.replaceAllUsesWith(UndefValue::get(I.getType()));
       BB->getInstList().pop_back();
     }
     new UnreachableInst(BB->getContext(), BB);
     assert(BB->getInstList().size() == 1 &&
            isa<UnreachableInst>(BB->getTerminator()) &&
            "The successor list of BB isn't empty before "
            "applying corresponding DTU updates.");
   }
 }

void DeleteDeadBlocks(ArrayRef<BasicBlock *> BBs, bool KeepOneInputPHIs) {
#ifndef NDEBUG
  // Make sure that all predecessors of each dead block is also dead.
  SmallPtrSet<BasicBlock *, 4> Dead(BBs.begin(), BBs.end());
  assert(Dead.size() == BBs.size() && "Duplicating blocks?");
  for (auto *BB : Dead)
    for (BasicBlock *Pred : predecessors(BB))
      assert(Dead.count(Pred) && "All predecessors must be dead!");
#endif

  SmallVector<DominatorTree::UpdateType, 4> Updates;
  DetatchDeadBlocks(BBs, nullptr, KeepOneInputPHIs);


  for (BasicBlock *BB : BBs)
    BB->eraseFromParent();
}

bool EliminateUnreachableBlocks(Function &F, bool KeepOneInputPHIs=false) {
  df_iterator_default_set<BasicBlock *> Reachable;

  // Mark all reachable blocks.
  for (BasicBlock *BB : depth_first_ext(&F, Reachable))
    (void)BB /* Mark all reachable blocks */;

  // Collect all dead blocks.
  std::vector<BasicBlock *> DeadBlocks;
  for (Function::iterator I = F.begin(), E = F.end(); I != E; ++I)
    if (!Reachable.count(&*I)) {
      BasicBlock *BB = &*I;
      DeadBlocks.push_back(BB);
    }

  // Delete the dead blocks.
  DeleteDeadBlocks(DeadBlocks, KeepOneInputPHIs);

  return !DeadBlocks.empty();
}

void ProgramSlicing::set_entry_block(Function *F, LoopInfo &LI, Loop *L) {

  BasicBlock *preheader = L->getLoopPreheader();
  BasicBlock *entry = &F->getEntryBlock();
  if (entry == preheader)
    return;

  // Walk on the parent chain changing the conditional branchs to a direct branch
  // until we reach *entry
  BasicBlock *child = preheader;
  while (child != entry){
    // if the child belongs to a loop, the parent is the loop preheader;
    // otherwise, the parent is the loop predecessor
    BasicBlock *parent = nullptr;

    if (LI.isLoopHeader(child))
      parent = LI.getLoopFor(child)->getLoopPreheader();
    else
      parent = child->getUniquePredecessor();

    assert(parent && "parent == nullptr");

    connect_basic_blocks(parent, child);
    child = parent;
  }

}

void ProgramSlicing::set_exit_block(Function *F) {
  BasicBlock *F_exit = nullptr;

  for (BasicBlock &BB : *F){
    if (isa<ReturnInst>(BB.getTerminator()))
      F_exit = &BB;
  }

  assert (F_exit != nullptr && "F_exit is nullptr");
  BasicBlock *exit = BasicBlock::Create(F->getContext(), "function_exit", F, F_exit);

  IRBuilder<> Builder(exit);
  Builder.CreateRetVoid();

  Instruction *ret = F_exit->getTerminator();

  Builder.SetInsertPoint(ret);
  Builder.CreateBr(exit);

  ret->dropAllReferences();
  ret->eraseFromParent();
}

std::set<BasicBlock*> compute_alive_blocks(Function *F, std::set<Instruction*> &dependences){
  std::set<BasicBlock*> alive;

  for (auto &BB : *F){
    for (Instruction &I : BB){
      if (dependences.find(&I) != dependences.end()){
        // errs() << "alive: " << BB.getName() << "\n";
        alive.insert(&BB);
        break;
      }
    }
  }

  return alive;
}

unsigned num_pred(BasicBlock *BB){
  unsigned i = 0;
  for (auto it = pred_begin(BB); it != pred_end(BB); ++it)
    ++i;
  return i;
}

unsigned num_succ(BasicBlock *BB){
  unsigned i = 0;
  for (auto it = succ_begin(BB); it != succ_end(BB); ++it)
    ++i;
  return i;
}

void connect_indirect_jump(BasicBlock *pred, BasicBlock *succ){
  // errs() << "Connecting: " << pred->getName() << " -> " << succ->getName();
  BranchInst *term = cast<BranchInst>(pred->getTerminator());
  assert(term->getNumSuccessors() == 1);
  term->setSuccessor(0, succ);
}

// Pred contains a conditional jump
void connect_cond_jump(BasicBlock *pred, BasicBlock *BB, BasicBlock *succ){
  BranchInst *term = cast<BranchInst>(pred->getTerminator());
  for (unsigned i = 0; i < term->getNumSuccessors(); i++){
    if (term->getSuccessor(i) == BB){
      // errs() << "Setting successor of : " << pred->getName() << " -> " << succ->getName() << "\n";
      term->setSuccessor(i, succ);
      return;
    }
  }
}

void connect_pred_to_succ(BasicBlock *pred, BasicBlock *BB, BasicBlock *succ){
  /*
    @pred -> @BB -> @succ
  */
  // errs() << "Connecting: " << pred->getName() << " to " << succ->getName() << "\n";
  if (num_succ(pred) == 1)
    connect_indirect_jump(pred, succ);
  else
    connect_cond_jump(pred, BB, succ);

}

bool conditional_to_direct(BasicBlock *BB){
  /*
    If BB contains a instruction of the form:
     br T %val, label %BB, label %succ 
    We replace it by a direct jump:
     br label %succ 
  */

  if (BB->empty()
      || BB->getTerminator() == nullptr)
    return false;

  if (!isa<BranchInst>(BB->getTerminator()))
    return false;

  BranchInst *term = cast<BranchInst>(BB->getTerminator());

  if (term->isUnconditional())
    return false;

  BasicBlock *succ = nullptr;

  if (term->getSuccessor(0) == BB)
    succ = term->getSuccessor(1);
  else if (term->getSuccessor(1) == BB)
    succ = term->getSuccessor(0);

  if (succ == nullptr)
    return false;

  BranchInst *rep = BranchInst::Create(succ, term);
  term->dropAllReferences();
  term->eraseFromParent();
  return true;
}

bool fix_conditional_jump_to_same_block(BasicBlock *BB){
  /*
    If BB contains a instruction of the form:
     br T %val, label %succ, label %succ 
    We replace it by a direct jump:
     br label %succ 
  */

  if (BB->empty()
      || BB->getTerminator() == nullptr)
    return false;

  if (!isa<BranchInst>(BB->getTerminator()))
    return false;

  BranchInst *term = cast<BranchInst>(BB->getTerminator());

  if (term->isUnconditional())
    return false;

  if (term->getSuccessor(0) == term->getSuccessor(1)){
    BranchInst *rep = BranchInst::Create(term->getSuccessor(0), term);
    term->dropAllReferences();
    term->eraseFromParent();
  }

  return true;
}

void delete_branch(BasicBlock *BB){
  assert(isa<BranchInst>(BB->getTerminator()));
  BranchInst *term = cast<BranchInst>(BB->getTerminator());
  term->dropAllReferences();
  term->eraseFromParent();
}

bool remove_successor(BasicBlock *BB, BasicBlock *succ){
  if (!isa<BranchInst>(BB->getTerminator()))
    return false;

  BranchInst *term = cast<BranchInst>(BB->getTerminator());

  if (term->isUnconditional()){
    delete_branch(BB);
  }
  else {
    unsigned idx = (term->getSuccessor(0) == succ) ? 1 : 0;
    BasicBlock *other = term->getSuccessor(idx);
    term->setSuccessor((idx+1)%2, other);
    fix_conditional_jump_to_same_block(BB);
  }

  return true;
}

void fix_phi_nodes(BasicBlock *prev, BasicBlock *BB, BasicBlock *succ) {

  auto *Old = BB;
  auto *New = prev;
  for (PHINode &phi : succ->phis()){
    for (unsigned Op = 0, NumOps = phi.getNumOperands(); Op != NumOps; ++Op)
      if (phi.getIncomingBlock(Op) == Old)
        phi.setIncomingBlock(Op, New);
  }

}

std::vector<BasicBlock*> collect_predecessors(BasicBlock *BB){
  std::vector<BasicBlock*> v;
  for (BasicBlock *pred : predecessors(BB)){
    v.push_back(pred);
  } 
  return v;
}

void erase_block(BasicBlock *BB){
  if (!BB->empty()){
    std::queue<Instruction*> q;
    for (Instruction &I : *BB){
      I.dropAllReferences();
      I.replaceAllUsesWith(UndefValue::get(I.getType()));
      q.push(&I);
    }

    while (!q.empty()) {
      Instruction *I = q.front();
      q.pop();
      I->eraseFromParent();
    }
  } 
  BB->dropAllReferences();
  BB->eraseFromParent();
}

bool merge_return_blocks(Function *F){

  std::vector<BasicBlock*> v;

  for (BasicBlock &BB : *F) {
    if (!BB.empty()
        && isa<ReturnInst>(BB.getTerminator()))
      v.push_back(&BB);
  }

  if (v.size() == 1)
    return false;

  BasicBlock *ret = BasicBlock::Create(F->getContext(), "function_exit", F, nullptr);
  auto *ri = ReturnInst::Create(F->getContext(), nullptr, ret);

  for (BasicBlock *BB : v){
    auto *term = BB->getTerminator();
    BranchInst *br = BranchInst::Create(ret, term);
    term->dropAllReferences();
    term->eraseFromParent();
  }

  return true;
}

void delete_block(BasicBlock *BB){
  /*
    1. If the block has a single predecessor/successor, connect them
  */

  // errs() << "deleting block: " << BB->getName() << "\n\n";
  Function *F = BB->getParent();

  conditional_to_direct(BB);
  fix_conditional_jump_to_same_block(BB);

  if (num_succ(BB) == 0){
    // BB->getParent()->viewCFG();
    auto preds = collect_predecessors(BB);
    for (auto *pred : preds){
      remove_successor(pred, BB);
    }
    // BB->getParent()->viewCFG();
  }
  else if (num_pred(BB) == 1 and num_succ(BB) == 1){
    auto *pred = BB->getSinglePredecessor();
    auto *succ = BB->getSingleSuccessor();
    if (pred != succ){
      connect_pred_to_succ(pred, BB, succ);
      fix_phi_nodes(pred, BB, succ);
    }
    else {
      // pred -> BB 
      //   ^      |
      //   |______|
      // errs() << "Disconnecting " << pred->getName() << " -> " << BB->getName() << "\n";
      remove_successor(pred, BB);
    }
  } 
  else if (num_pred(BB) > 1 and num_succ(BB) == 1){
    auto preds = collect_predecessors(BB);

    for (BasicBlock *pred : preds){
      auto *succ = BB->getSingleSuccessor();
      connect_pred_to_succ(pred, BB, succ);
      fix_phi_nodes(pred, BB, succ);
    }
  }
  else if (num_pred(BB) >= 1 and num_succ(BB) > 1){
    std::set<BasicBlock*> sucessors;
    for (auto it = succ_begin(BB); it != succ_end(BB); ++it) {
      if (it->getTerminator() != nullptr) {
        if (!isa<ReturnInst>(it->getTerminator())) {
          sucessors.insert(*it);
        }
      }
    }

    if (sucessors.size() > 1)
      assert("both #predecessors and #successors are greater than 1");

    // We are ignoring the branch to the Return inst, just to dead blocks.
    // The idea is that the unique control flow that should happen is the one
    // that could execute instructions.
    if (sucessors.size() == 1) {
      auto *pred = BB->getSinglePredecessor();
      auto *succ = *sucessors.begin();
      if (pred != succ){
        connect_pred_to_succ(pred, BB, succ);
        fix_phi_nodes(pred, BB, succ);
      }
      else {
        // pred -> BB 
        //   ^      |
        //   |______|
        // errs() << "Disconnecting " << pred->getName() << " -> " << BB->getName() << "\n";
        remove_successor(pred, BB);
      }
    }
  }
  
  erase_block(BB);
}

std::vector<BasicBlock*> get_dead_blocks(Function *F, std::set<BasicBlock*> &alive_blocks){
  df_iterator_default_set<BasicBlock *> Reachable;
  std::vector<BasicBlock*> d;

  for (BasicBlock *BB : depth_first_ext(F, Reachable)){
    if (BB->getTerminator() != nullptr) {
      if (!isa<ReturnInst>(BB->getTerminator())) {
        if (alive_blocks.find(BB) == alive_blocks.end()){
          d.push_back(BB);
	}
      }
    }
  }

  std::reverse(d.begin(), d.end());

  return d;
}

bool can_delete_block(Function *F, BasicBlock *BB){
  // if (&F->getEntryBlock() == BB)
  if (&F->getEntryBlock() == BB || isa<ReturnInst>(BB->getTerminator()))
    return false;

  std::set<BasicBlock*> sucessors;
  for (auto it = succ_begin(BB); it != succ_end(BB); ++it) {
    if (it->getTerminator() != nullptr) {
      if (!isa<ReturnInst>(it->getTerminator())) {
        sucessors.insert(*it);
      }
    }
  }
  if (sucessors.size() > 1)
    return false;

  return true;
}

void ProgramSlicing::delete_blocks(Function *F, Instruction *I){
  merge_return_blocks(F);

  ProgramDependenceGraph PDG;
  PDG.compute_dependences(F);
  std::set<Instruction*> dependences = PDG.get_dependences_for(I);
  std::set<BasicBlock*> alive_blocks = compute_alive_blocks(F, dependences);

  std::vector<BasicBlock*> dead_blocks = get_dead_blocks(F, alive_blocks);

  FunctionAnalysisManager FAM;
  PassBuilder PB;
  PB.registerFunctionAnalyses(FAM);

  DominatorTree DT(*F);
  LoopInfo LI(DT);
  auto &AA = FAM.getResult<AAManager>(*F);

  while (dead_blocks.size() > 0) {
    for (auto *BB : dead_blocks) {
      if (can_delete_block(F, BB)){
        delete_block(BB);
      }
    }
    iterativelySinkInstructions(*F, DT, LI, AA);
    alive_blocks = compute_alive_blocks(F, dependences);
    dead_blocks = get_dead_blocks(F, alive_blocks);
  }
}

void delete_empty_blocks(Function *F){
  std::queue<BasicBlock*> q;
  for (auto &BB : *F){
    if (BB.empty()){
      assert(num_pred(&BB) == 1 && "Basic Block has more than one predecessor here!");
      remove_successor(BB.getSinglePredecessor(), &BB);
      q.push(&BB);
    }
  }

  while (!q.empty()){
    auto *BB = q.front();
    BB->eraseFromParent();
    q.pop();
  }
}

/// Gleison wrote this

// Skin pass on demend, copied from:
// https://llvm.org/doxygen/Sink_8cpp_source.html

  /// AllUsesDominatedByBlock - Return true if all uses of the specified value
 /// occur in blocks dominated by the specified block.
 bool ProgramSlicing::AllUsesDominatedByBlock(Instruction *Inst, BasicBlock *BB,
                                     DominatorTree &DT) {
   // Ignoring debug uses is necessary so debug info doesn't affect the code.
   // This may leave a referencing dbg_value in the original block, before
   // the definition of the vreg.  Dwarf generator handles this although the
   // user might not get the right info at runtime.
   for (Use &U : Inst->uses()) {
     // Determine the block of the use.
     Instruction *UseInst = cast<Instruction>(U.getUser());
     BasicBlock *UseBlock = UseInst->getParent();
     if (PHINode *PN = dyn_cast<PHINode>(UseInst)) {
       // PHI nodes use the operand in the predecessor block, not the block with
       // the PHI.
       unsigned Num = PHINode::getIncomingValueNumForOperand(U.getOperandNo());
       UseBlock = PN->getIncomingBlock(Num);
     }
     // Check that it dominates.
     if (!DT.dominates(BB, UseBlock))
       return false;
   }
   return true;
 }

  bool ProgramSlicing::isSafeToMove(Instruction *Inst, AliasAnalysis &AA,
                          SmallPtrSetImpl<Instruction *> &Stores) {
 
   if (Inst->mayWriteToMemory()) {
     Stores.insert(Inst);
     return false;
   }
 
   if (LoadInst *L = dyn_cast<LoadInst>(Inst)) {
     MemoryLocation Loc = MemoryLocation::get(L);
     for (Instruction *S : Stores)
       if (isModSet(AA.getModRefInfo(S, Loc)))
         return false;
   }
 
   if (Inst->isTerminator() || isa<PHINode>(Inst) || Inst->isEHPad() ||
       Inst->mayThrow())
     return false;
 
   if (auto *Call = dyn_cast<CallInst>(Inst)) {
     // Convergent operations cannot be made control-dependent on additional
     // values.
     if (Call->hasFnAttr(Attribute::Convergent))
       return false;
 
     for (Instruction *S : Stores)
       if (isModSet(AA.getModRefInfo(S, Call)))
         return false;
   }
 
   return true;
 }

  bool ProgramSlicing::isExceptionalTerminator(unsigned OpCode) {
     switch (OpCode) {
     case Instruction::CatchSwitch:
     case Instruction::CatchRet:
     case Instruction::CleanupRet:
     case Instruction::Invoke:
     case Instruction::Resume:
       return true;
     default:
       return false;
     }
   }

 /// IsAcceptableTarget - Return true if it is possible to sink the instruction
 /// in the specified basic block.
 bool ProgramSlicing::IsAcceptableTarget(Instruction *Inst, BasicBlock *SuccToSinkTo,
                                DominatorTree &DT, LoopInfo &LI) {
   assert(Inst && "Instruction to be sunk is null");
   assert(SuccToSinkTo && "Candidate sink target is null");

   if (SuccToSinkTo == nullptr)
     return false;

   if ((SuccToSinkTo->getTerminator() == nullptr) ||
      (isa<UndefValue>(SuccToSinkTo->getTerminator())))
     return false;

   // It is not possible to sink an instruction into its own block.  This can
   // happen with loops.
   if (Inst->getParent() == SuccToSinkTo)
     return false;
 
   // It's never legal to sink an instruction into a block which terminates in an
   // EH-pad.
   Instruction *terminator = SuccToSinkTo->getTerminator();
   //errs() << "Terminator\n";
   //terminator->dump();
   //errs() << terminator->getOpcode() << "\n";
   if (isExceptionalTerminator(terminator->getOpcode()))
     return false;
 
   // If the block has multiple predecessors, this would introduce computation
   // on different code paths.  We could split the critical edge, but for now we
   // just punt.
   // FIXME: Split critical edges if not backedges.
   if (SuccToSinkTo->getUniquePredecessor() != Inst->getParent()) {
     // We cannot sink a load across a critical edge - there may be stores in
     // other code paths.
     if (Inst->mayReadFromMemory())
       return false;
 
     // We don't want to sink across a critical edge if we don't dominate the
     // successor. We could be introducing calculations to new code paths.
     if (!DT.dominates(Inst->getParent(), SuccToSinkTo))
       return false;
 
     // Don't sink instructions into a loop.
     Loop *succ = LI.getLoopFor(SuccToSinkTo);
     Loop *cur = LI.getLoopFor(Inst->getParent());
     if (succ != nullptr && succ != cur)
       return false;
   }
 
   // Finally, check that all the uses of the instruction are actually
   // dominated by the candidate
   return AllUsesDominatedByBlock(Inst, SuccToSinkTo, DT);
 }

 /// SinkInstruction - Determine whether it is safe to sink the specified machine
 /// instruction out of its current block into a successor.
 bool ProgramSlicing::SinkInstruction(Instruction *Inst,
                             SmallPtrSetImpl<Instruction *> &Stores,
                             DominatorTree &DT, LoopInfo &LI, AliasAnalysis &AA) {
 
   // Don't sink static alloca instructions.  CodeGen assumes allocas outside the
   // entry block are dynamically sized stack objects.
   if (AllocaInst *AI = dyn_cast<AllocaInst>(Inst))
     if (AI->isStaticAlloca())
       return false;
 
   // Check if it's safe to move the instruction.
   if (!isSafeToMove(Inst, AA, Stores))
     return false;
 
   // FIXME: This should include support for sinking instructions within the
   // block they are currently in to shorten the live ranges.  We often get
   // instructions sunk into the top of a large block, but it would be better to
   // also sink them down before their first use in the block.  This xform has to
   // be careful not to *increase* register pressure though, e.g. sinking
   // "x = y + z" down if it kills y and z would increase the live ranges of y
   // and z and only shrink the live range of x.
 
   // SuccToSinkTo - This is the successor to sink this instruction to, once we
   // decide.
   BasicBlock *SuccToSinkTo = nullptr;
 
   // Instructions can only be sunk if all their uses are in blocks
   // dominated by one of the successors.
   // Look at all the dominated blocks and see if we can sink it in one.
   DomTreeNode *DTN = DT.getNode(Inst->getParent());
   for (DomTreeNode::iterator I = DTN->begin(), E = DTN->end();
       I != E && SuccToSinkTo == nullptr; ++I) {
     BasicBlock *Candidate = (*I)->getBlock();
     // A node always immediate-dominates its children on the dominator
     // tree.
     if (IsAcceptableTarget(Inst, Candidate, DT, LI))
       SuccToSinkTo = Candidate;
   }
 
   // If no suitable postdominator was found, look at all the successors and
   // decide which one we should sink to, if any.
   for (succ_iterator I = succ_begin(Inst->getParent()),
       E = succ_end(Inst->getParent()); I != E && !SuccToSinkTo; ++I) {
     if (IsAcceptableTarget(Inst, *I, DT, LI))
       SuccToSinkTo = *I;
   }
 
   // If we couldn't find a block to sink to, ignore this instruction.
   if (!SuccToSinkTo)
     return false;
 
   // Move the instruction.
   Inst->moveBefore(&*SuccToSinkTo->getFirstInsertionPt());
   return true;
 }

 bool ProgramSlicing::ProcessBlock(BasicBlock &BB, DominatorTree &DT, LoopInfo &LI,
                          AliasAnalysis &AA) {
   // Can't sink anything out of a block that has less than two successors.
   if (BB.getTerminator()->getNumSuccessors() <= 1) return false;
 
   // Don't bother sinking code out of unreachable blocks. In addition to being
   // unprofitable, it can also lead to infinite looping, because in an
   // unreachable loop there may be nowhere to stop.
   if (!DT.isReachableFromEntry(&BB)) return false;
 
   bool MadeChange = false;
 
   // Walk the basic block bottom-up.  Remember if we saw a store.
   BasicBlock::iterator I = BB.end();
   --I;
   bool ProcessedBegin = false;
   SmallPtrSet<Instruction *, 8> Stores;
   do {
     Instruction *Inst = &*I; // The instruction to sink.
 
     // Predecrement I (if it's not begin) so that it isn't invalidated by
     // sinking.
     ProcessedBegin = I == BB.begin();
     if (!ProcessedBegin)
       --I;
 
     if (isa<DbgInfoIntrinsic>(Inst))
       continue;
 
     if (SinkInstruction(Inst, Stores, DT, LI, AA)) {
       MadeChange = true;
     }
 
     // If we just processed the first instruction in the block, we're done.
   } while (!ProcessedBegin);
 
   return MadeChange;
 }

 bool ProgramSlicing::iterativelySinkInstructions(Function &F, DominatorTree &DT,
                                         LoopInfo &LI, AliasAnalysis &AA) {
   bool MadeChange, EverMadeChange = false;
 
   do {
     MadeChange = false;
     // Process all basic blocks.
     for (BasicBlock &I : F)
       MadeChange |= ProcessBlock(I, DT, LI, AA);
     EverMadeChange |= MadeChange;
   } while (MadeChange);
 
   return EverMadeChange;
 }

/// End of Gleison Region

void ProgramSlicing::slice(Function *F, Instruction *I) {
  errs() << "[INFO]: Applying slicing on: " << F->getName() << "\n";

  DominatorTree DT(*F);
  PostDominatorTree PDT;
  PDT.recalculate(*F);
  LoopInfo LI(DT);

  set_exit_block(F);

  PassBuilder PB;
  FunctionAnalysisManager FAM;
  PB.registerFunctionAnalyses(FAM);

  UnreachableBlockElimPass u;
  u.run(*F, FAM);

  DCEPass d;
  d.run(*F, FAM);

  SimplifyCFGPass sf;
  sf.run(*F, FAM);

  //ProgramDependenceGraph PDG;
  //PDG.compute_dependences(F);
  //std::set<Instruction*> dependences = PDG.get_dependences_for(I);
  // PDG.get_dependence_graph()->to_dot();

  //std::set<BasicBlock*> alive_blocks = compute_alive_blocks(F, dependences);

  std::queue<Instruction *> q;

  bool valid_worklist = true;

  while (valid_worklist == true) {
    valid_worklist = false;
    ProgramDependenceGraph PDG;
    PDG.compute_dependences(F);
    std::set<Instruction*> dependences = PDG.get_dependences_for(I);
 
    for (Instruction &I : instructions(F)) {
      if (isa<BranchInst>(&I) || isa<ReturnInst>(&I) || dependences.find(&I) != dependences.end())
        continue;

      valid_worklist = true;
      I.dropAllReferences();
      I.replaceAllUsesWith(UndefValue::get(I.getType()));
     q.push(&I);
    }

    while (!q.empty()) {
      Instruction *I = q.front();
      q.pop();
      I->eraseFromParent();
    }

    delete_empty_blocks(F);

  //alive_blocks = compute_alive_blocks(F, dependences);

    u.run(*F, FAM);
    sf.run(*F, FAM);

    delete_blocks(F, I);
  }

  //F->viewCFG();

  u.run(*F, FAM);
  // sf.run(*F, FAM);

  // VerifierPass ver;
  // ver.run(*F, FAM);

}

}  // namespace phoenix
