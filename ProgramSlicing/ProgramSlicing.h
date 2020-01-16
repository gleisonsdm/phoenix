#pragma once

#include "../PDG/PDGAnalysis.h"
#include "../ProgramSlicing/ProgramSlicing.h"
#include "llvm/Analysis/AliasAnalysis.h"

namespace phoenix{

class ProgramSlicing {
 private:

  void set_entry_block(Function *F, LoopInfo &LI, Loop *L);
  void set_exit_block(Function *F);
  void connect_basic_blocks(BasicBlock *to, BasicBlock *from);
  void connect_body_to_latch(BasicBlock *body, BasicBlock *latch);
  void connect_header_to_body(Loop *L, BasicBlock *body);
  ///
  void remove_subloops(Loop *L, Loop *marked);
  Loop* remove_loops_outside_chain(LoopInfo &LI, BasicBlock *BB);
  Loop* remove_loops_outside_chain(Loop *L, Loop *keep = nullptr);

  /// Gleison wrote this

  // Skin pass on demend, copied from:
  // https://llvm.org/doxygen/Sink_8cpp_source.html

  bool AllUsesDominatedByBlock(Instruction *Inst, BasicBlock *BB, DominatorTree &DT);

  bool isSafeToMove(Instruction *Inst, AliasAnalysis &AA, SmallPtrSetImpl<Instruction *> &Stores);

  bool isExceptionalTerminator(unsigned OpCode);

  bool IsAcceptableTarget(Instruction *Inst, BasicBlock *SuccToSinkTo, DominatorTree &DT, LoopInfo &LI);

  bool SinkInstruction(Instruction *Inst, SmallPtrSetImpl<Instruction *> &Stores, DominatorTree &DT, LoopInfo &LI, AliasAnalysis &AA);

  bool ProcessBlock(BasicBlock &BB, DominatorTree &DT, LoopInfo &LI, AliasAnalysis &AA);

  bool iterativelySinkInstructions(Function &F, DominatorTree &DT, LoopInfo &LI, AliasAnalysis &AA);

  void delete_blocks(Function *F, Instruction *I);
  /// End of Gleison Region


 public:
  ProgramSlicing();

  /// Slice the program given the start point @V
  void slice(Function *F, Instruction *I);
};

};  // namespace phoenix
