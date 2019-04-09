#include "llvm/ADT/Statistic.h" // For the STATISTIC macro.
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Constants.h"         // For ConstantData, for instance.
#include "llvm/IR/DebugInfoMetadata.h" // For DILocation
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h" // To use the iterator instructions(f)
#include "llvm/IR/Instructions.h" // To have access to the Instructions.
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h" // To print error messages.
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h" // For dbgs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <queue>

#include "Optimize.h"

#define DEBUG_TYPE "Optimize"

Value *Optimize::get_identity(const Geps &g) {
  Instruction *I = g.get_instruction();
  switch (I->getOpcode()) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Xor:
  //
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
    return ConstantInt::get(I->getType(), 0);
  //
  case Instruction::Mul:
  case Instruction::UDiv:
  case Instruction::SDiv:
    return ConstantInt::get(I->getType(), 1);
  //
  case Instruction::FAdd:
  case Instruction::FSub:
    return ConstantFP::get(I->getType(), 0.0);
  case Instruction::FMul:
  case Instruction::FDiv:
    return ConstantFP::get(I->getType(), 1.0);

  case Instruction::And:
  case Instruction::Or:
    return g.get_p_before();
  default:
    std::string str = "Instruction not supported: ";
    llvm::raw_string_ostream rso(str);
    I->print(rso);
    llvm_unreachable(str.c_str());
  }
}

llvm::SmallVector<Instruction *, 10>
Optimize::mark_instructions_to_be_moved(StoreInst *store) {
  std::queue<Instruction *> q;
  llvm::SmallVector<Instruction *, 10> marked;

  for (Value *v : store->operands()) {
    if (Instruction *i = dyn_cast<Instruction>(v)) {
      q.push(i);
    }
  }

  marked.push_back(store);

  while (!q.empty()) {
    Instruction *v = q.front();
    q.pop();

    // Check if *v is only used in instructions already marked
    bool all_marked =
        std::all_of(begin(v->users()), end(v->users()), [&marked](Value *user) {
          return find(marked, user) != marked.end();
        });

    if (!all_marked){
      DEBUG(dbgs() << "-> Ignoring: " << *v << "\n");
      continue;
    }

    // Insert v in the list of marked values and its operands in the queue
    marked.push_back(v);

    if (User *u = dyn_cast<User>(v)) {
      for (Value *op : u->operands()) {
        if (Instruction *inst = dyn_cast<Instruction>(op)) {
          // restrict ourselves to instructions on the same basic block
          if (v->getParent() != inst->getParent()){
            DEBUG(dbgs() << "-> not in the same BB: " << *inst << "\n");
            continue;
          }

          if (isa<PHINode>(inst))
            continue;

          q.push(inst);
        }
      }
    }
  }

  return marked;
}

void Optimize::move_marked_to_basic_block(
    llvm::SmallVector<Instruction *, 10> &marked, Instruction *br) {
  for (Instruction *inst : reverse(marked)) {
    inst->moveBefore(br);
  }
}

void Optimize::move_from_prev_to_then(BasicBlock *BBPrev, BasicBlock *BBThen){
  llvm::SmallVector<Instruction*, 10> list;

  for (BasicBlock::reverse_iterator b = BBPrev->rbegin(), e = BBPrev->rend(); b != e; ++b){
    Instruction *I = &*b;

    if (isa<PHINode>(I) || isa<BranchInst>(I))
      continue;

    if (begin(I->users()) == end(I->users()))
      continue;

    // Move I from BBPrev to BBThen iff all users of I are in BBThen
    //
    // Def 1.
    //  Program P is in SSA form. Therefore, I dominates all its users
    // Def 2. 
    //  We are iterating from the end of BBPrev to the beginning. Thus, this gives us the guarantee
    //  that all users of I living in the same BB were previously visited.

    bool can_move_I = std::all_of(begin(I->users()), end(I->users()), [&BBThen](User *U){
      BasicBlock *parent = dyn_cast<Instruction>(U)->getParent();
      return (parent == BBThen);
    });

    if (can_move_I){
      DEBUG(dbgs() << "[BBPrev -> BBThen] " << *I << "\n");
      --b;
      I->moveBefore(BBThen->getFirstNonPHI());
    }
  }
}

void Optimize::move_from_prev_to_end(BasicBlock *BBPrev, BasicBlock *BBThen, BasicBlock *BBEnd){
  llvm::SmallVector<Instruction*, 10> marked;

  for (BasicBlock::reverse_iterator b = BBPrev->rbegin(), e = BBPrev->rend(); b != e; ++b){
    Instruction *I = &*b;

    if (isa<PHINode>(I) || isa<BranchInst>(I))
      continue;

    if (begin(I->users()) == end(I->users()))
      continue;

    // Move I from BBPrev to BBEnd iff all users of I are in BBEnd. 
    // 
    // Def 1. 
    //  The program is in SSA form
    // Def 2.
    //  We are iterating from the end of BBPrev to the beginning. 
    // 
    // Theorem: 
    //  Given an I that **has only users on BBend**, moving it from BBPrev -> BBEnd doesn't
    //  change the semanthics of the program P.
    // 
    // Proof:
    //  Let's assume that moving I from BBPrev to BBEnd changes the semantics of P. If it changes,
    //  there an instruction J that depends on I (is a user of I) and will be executed before I. There
    //  are two cases that can happen:
    //    J is in BBPrev: Because the program is in SSA form, I must dominate J. Therefore, to move I,
    //      we had to move J before to BBEnd. 
    //    J is in BBThen: Invalid. We don't move I if there is a user of it outside BBPrev.
    //

    bool can_move_I = std::all_of(begin(I->users()), end(I->users()), [&BBPrev, &BBThen, &BBEnd](User *U){
      BasicBlock *BB = dyn_cast<Instruction>(U)->getParent();
      return (BB != BBPrev) && (BB != BBThen);
    });

    if (can_move_I){
      DEBUG(dbgs() << "[BBPrev -> BBEnd]" << *I << "\n");
      --b;
      I->moveBefore(BBEnd->getFirstNonPHI());
    }
  }
}

void Optimize::insert_if(const Geps &g) {

  Value *v = g.get_v();
  Instruction *I = g.get_instruction();
  StoreInst *store = g.get_store_inst();
  IRBuilder<> Builder(store);

  Value *idnt;
  Value *cmp;

  if (v->getType()->isFloatingPointTy()) {
    cmp = Builder.CreateFCmpONE(v, get_identity(g));
  } else {
    cmp = Builder.CreateICmpNE(v, get_identity(g));
  }

  TerminatorInst *br = llvm::SplitBlockAndInsertIfThen(
      cmp, dyn_cast<Instruction>(cmp)->getNextNode(), false);

  BasicBlock *BBThen = br->getParent();
  BasicBlock *BBPrev = BBThen->getSinglePredecessor();
  BasicBlock *BBEnd = BBThen->getSingleSuccessor();

  store->moveBefore(br);

  // llvm::SmallVector<Instruction *, 10> marked =
  //   mark_instructions_to_be_moved(store);

  // for_each(marked, [](Instruction *inst) {
  //   DEBUG(dbgs() << " Marked: " << *inst << "\n");
  // });

  // move_marked_to_basic_block(marked, br);

  move_from_prev_to_then(BBPrev, BBThen);
  move_from_prev_to_end(BBPrev, BBThen, BBEnd);
}
// This should implement a cost model
// Right now we only insert the `if` if the depth is >= threshold(1)
// TO-DO: Use a more sophisticated solution
bool Optimize::worth_insert_if(Geps &g) {
  if (g.get_loop_depth() >= threshold)
    return true;

  DEBUG(dbgs() << "skipping: " << *g.get_instruction() << "\n"
    << " threshold " << g.get_loop_depth() << " is not greater than " << threshold << "\n\n");
  return false;
}

bool Optimize::filter_instructions(Geps &g){
  Instruction *I = g.get_instruction();
  
  switch(I->getOpcode()){
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::Xor:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::UDiv:
    case Instruction::SDiv:
      return true;
    default:
      return false;
  }
}

void print_gep(Function *F, Geps &g) {
  Instruction *I = g.get_instruction();
  DEBUG(dbgs() << "I: " << *I << "\n");

  const DebugLoc &loc = I->getDebugLoc();
  if (loc) {
    auto *Scope = cast<DIScope>(loc.getScope());
    DEBUG(dbgs() << " - File: " << Scope->getFilename() << ":" << loc.getLine() << "\n");
  }

  DEBUG(dbgs() << " - Function: " << F->getName() << "\n");
  DEBUG(dbgs() << " - Loop Depth:" << g.get_loop_depth() << "\n");
  DEBUG(dbgs() << " - v : " << *g.get_v() << "\n");
}

bool Optimize::runOnFunction(Function &F) {

  if (F.isDeclaration() || F.isIntrinsic() || F.hasAvailableExternallyLinkage())
    return true;

  Identify *Idn = &getAnalysis<Identify>();

  llvm::SmallVector<Geps, 10> gs = Idn->get_instructions_of_interest();

  // Let's give an id for each instruction of interest
  for (auto &g : gs) {
    Instruction *I = g.get_instruction();

    // sanity check for vector instructions
    if (I->getOperand(0)->getType()->isVectorTy() ||
        I->getOperand(1)->getType()->isVectorTy())
      continue;
      // assert(0 && "Vector type");

    // filter_instructions => Filter arithmetic instructions
    // can_insert_if       => Check for corner cases. i.e. in a SUB, the `v` 
    //                        value must be on the right and side (*p = *p - v) 
    //                        and not on the left (*p = v - *p)
    // worth_insert_if     => Cost model
    if (filter_instructions(g) && worth_insert_if(g)){
      print_gep(&F, g);
      insert_if(g);
      DEBUG(dbgs() << "\n");
    }

  }

  return false;
}

void Optimize::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<Identify>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.setPreservesAll();
}

char Optimize::ID = 0;
static RegisterPass<Optimize> X("Optimize", "Optimize pattern a = a OP b", false, false);
