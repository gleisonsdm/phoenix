#include "llvm/ADT/Statistic.h"               // For the STATISTIC macro.
#include "llvm/Analysis/DependenceAnalysis.h" // Dependency Analysis
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Constants.h"         // For ConstantData, for instance.
#include "llvm/IR/DebugInfoMetadata.h" // For DILocation
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h" // To use the iterator instructions(f)
#include "llvm/IR/Instructions.h" // To have access to the Instructions.
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"       // To print error messages.
#include "llvm/Support/raw_ostream.h" // For dbgs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <fstream>
#include <map>
#include <set>
#include <stack>

#include "Instrument.h"

#define DEBUG_TYPE "Instrument"

void Instrument::print_instructions(Module &M) {
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        errs() << I << "\n";
      }
    }
  }
}

/*
 Create (if necessary) and return a unique ID for each load/store instruction
*/
void Instrument::create_id(std::map<const Value *, unsigned> &IDs,
                           const Value *V) {
  IDs[V] = IDs.size();
}

void Instrument::create_id(const Instruction *inst) {
  if (isa<LoadInst>(inst))
    create_id(load_ids, dyn_cast<const Value>(inst));
  else
    create_id(store_ids, dyn_cast<const Value>(inst));
}

unsigned Instrument::get_id(std::map<const Value *, unsigned> &IDs,
                            const Value *V) {
  if (IDs.find(V) == IDs.end())
    IDs[V] = IDs.size();
  return IDs[V];
}

unsigned Instrument::get_id(const Instruction *inst) {
  if (isa<LoadInst>(inst)) {
    return get_id(load_ids, dyn_cast<const Value>(inst));
  } else if (isa<StoreInst>(inst)) {
    return get_id(store_ids, dyn_cast<const Value>(inst));
  }
}

/*****************************************************************************/

/*
  For a given load of interest:
    %x = load %ptr
  Record the memory position being loaded (%ptr)
*/
void Instrument::record_access(
    Module &M, StoreInst *I, Value *ptr,
    const std::string &function_name = "record_store") {
  IRBuilder<> Builder(I);

  Constant *const_function = M.getOrInsertFunction(
      function_name, FunctionType::getVoidTy(M.getContext()),
      Type::getInt64Ty(M.getContext()),    // ID
      Type::getInt8PtrTy(M.getContext())); // Address

  Function *f = cast<Function>(const_function);

  Value *address =
      Builder.CreateBitCast(ptr, Type::getInt8PtrTy(M.getContext()));

  // Create the call
  std::vector<Value *> params;
  params.push_back(Builder.getInt64(get_id(I))), // ID
      params.push_back(address);                 // address
  CallInst *call = Builder.CreateCall(f, params);
}

/*
  For a given store of interest:
    store %val, %ptr
  Record the memory position %ptr whose %val is being written.
*/

void Instrument::record_access(
    Module &M, LoadInst *I, Value *ptr,
    const std::string &function_name = "record_load") {
  IRBuilder<> Builder(I);

  Constant *const_function = M.getOrInsertFunction(
      function_name, FunctionType::getVoidTy(M.getContext()),
      Type::getInt64Ty(M.getContext()),    // ID
      Type::getInt8PtrTy(M.getContext())); // Address

  Function *f = cast<Function>(const_function);

  Value *address =
      Builder.CreateBitCast(ptr, Type::getInt8PtrTy(M.getContext()));

  // Create the call
  std::vector<Value *> params;
  params.push_back(Builder.getInt64(get_id(I))); // id
  params.push_back(address);                     // address
  CallInst *call = Builder.CreateCall(f, params);
}

/*
  This function counts the number of visible stores. For a better
  understand of what a visible instruction is, check the paper below:

    Leobas, Guilherme V., Breno CF Guimarães, and Fernando MQ Pereira.
    "More than meets the eye: invisible instructions."
    Proceedings of the XXII Brazilian Symposium on Programming Languages. ACM,
  2018.
*/
void Instrument::count_store(Module &M, StoreInst *I) {
  IRBuilder<> Builder(I);

  // Let's create the function call
  Constant *const_function = M.getOrInsertFunction(
      "count_store", FunctionType::getVoidTy(M.getContext())
  );

  Function *f = cast<Function>(const_function);

  // Create the call
  std::vector<Value*> args;
  Builder.CreateCall(f, args);
}

/*****************************************************************************/

/*
  Create a call to `dump_txt` function
*/
void Instrument::insert_dump_call(Module &M, Instruction *I) {
  IRBuilder<> Builder(I);

  // Let's create the function call
  Constant *const_function = M.getOrInsertFunction(
      "dump_txt", FunctionType::getVoidTy(M.getContext()));

  Function *f = cast<Function>(const_function);

  // Create the call
  Builder.CreateCall(f, std::vector<Value *>());
}

/*
  Find the return inst and create call to `dump_txt`
*/
void Instrument::insert_dump_call(Module &M) {
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (ReturnInst *ri = dyn_cast<ReturnInst>(&I)) {
          if (F.getName() == "main")
            insert_dump_call(M, ri);
        } else if (CallInst *ci = dyn_cast<CallInst>(&I)) {
          Function *fun = ci->getCalledFunction();
          if (fun && fun->getName() == "exit") {
            insert_dump_call(M, ci);
          }
        }
      }
    }
  }
}

/*****************************************************************************/

void Instrument::init_instrumentation(Module &M) {
  Function *F = M.getFunction("main");

  // Instruction *ins = F->front().getFirstNonPHI();
  Instruction *ins = F->front().getTerminator();

  IRBuilder<> Builder(ins);

  Constant *const_function = M.getOrInsertFunction(
      "init_instrumentation", FunctionType::getVoidTy(M.getContext()));

  Function *f = cast<Function>(const_function);

  CallInst *call = Builder.CreateCall(f, std::vector<Value *>());
}

/*****************************************************************************/

bool Instrument::is_arithmetic_inst(const Instruction *ins) {
  switch (ins->getOpcode()) {
  case Instruction::Add:
  case Instruction::FAdd:
  //
  case Instruction::Sub:
  case Instruction::FSub:
  //
  case Instruction::Mul:
  case Instruction::FMul:
  //
  case Instruction::UDiv:
  case Instruction::SDiv:
  case Instruction::FDiv:
  //
  case Instruction::URem:
  case Instruction::SRem:
  case Instruction::FRem:
  //
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
  //
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor:
    return true;
  default:
    return false;
  }
}

/*
  This function check if there is an information path from load -> store
  that goes by an arithmetic instruction
*/
bool Instrument::dfs(const Instruction *source, const Instruction *dest,
                     std::set<std::pair<const Instruction *, bool>> &visited,
                     bool valid = false) {

  if (source == dest && valid) {
    return true;
  }

  for (auto V : source->users()) {

    const Instruction *ins = dyn_cast<Instruction>(V);

    // check if we alredy visited this instruction
    if (visited.find(std::make_pair(ins, valid)) != visited.end())
      continue;

    // if no, add it to the list
    visited.insert(std::make_pair(ins, valid));

    bool r = dfs(dyn_cast<Instruction>(V), dest, visited,
                 is_arithmetic_inst(ins) || valid);
    if (r) {
      return true;
    }
  }

  return false;
}

void Instrument::mark_dependencies(Module &M) {

  // Create a unique ID for each load/store instruction
  // errs() << "Instructions:\n";
  for (auto &F : M) {
    for (auto inst = inst_begin(F); inst != inst_end(F); inst++) {
      if (isa<LoadInst>(*inst) || isa<StoreInst>(*inst)) {
        create_id(&*inst);
      }
    }
  }

  /*
    Map each store into its dependencies:
    store(0) -> load(1), load(3), load(xyz)
    store(1) -> load(0), load(1), ...
    and so on and so forth
  */
  std::map<int, std::vector<int>> dep;

  for (auto &F : M) {
    // DependenceInfo *DA =
    // &getAnalysis<DependenceAnalysisWrapperPass>(F).getDI();
    for (auto src = inst_begin(F); src != inst_end(F); src++) {
      for (auto dest = src; dest != inst_end(F); dest++) {
        if (src == dest)
          continue;

        if (!isa<LoadInst>(*src) || !isa<StoreInst>(*dest))
          continue;

        // std::unique_ptr<Dependence> ptr = DA->depends(&*src, &*dest, true);

        // check if there is a information flow from the load -> store
        std::set<std::pair<const Instruction *, bool>> visited;

        if (&*src->getParent() != &*dest->getParent())
          continue;

        bool has_flow = dfs(&*src, &*dest, visited);
        if (has_flow) {
          // errs() << "Flow:\n";
          // errs() << *src << "\n";
          // errs() << *dest << '\n';
          // errs() << '\n';
          dep[get_id(&*dest)].push_back(get_id(&*src));
        }
      }
    }
  }

  std::ofstream f;
  f.open("map.txt");

  std::set<int> inst_used;

  for (auto &it : dep) {
    f << it.first << ' ' << it.second.size() << " ";
    stores_used.insert(it.first);
    for (auto &i : it.second) {
      loads_used.insert(i);
      f << i << " ";
    }
    f << "\n";
  }

  f.close();
}

/*****************************************************************************/

bool Instrument::runOnModule(Module &M) {
  /*
    Mark all dependencies between loads and stores
    This is done to avoid false positives:
      v = *p;
      *p = 0;
    There is no dependency between the load and store above
  */
  mark_dependencies(M);

  /*
    Adds a call to init() and another to dump()
  */
  insert_dump_call(M);
  init_instrumentation(M);

  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (StoreInst *store = dyn_cast<StoreInst>(&I)) {

          count_store(M, store);

          int store_id = get_id(store);
          if (stores_used.find(store_id) != stores_used.end())
            record_access(M, store, store->getPointerOperand(), "record_store");
        }
        else if (LoadInst *load = dyn_cast<LoadInst>(&I)) {
          int load_id = get_id(load);
          if (loads_used.find(load_id) != loads_used.end())
            record_access(M, load, load->getPointerOperand(), "record_load");
        }
      }
    }
  }

  return true;
}

void Instrument::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addPreserved<DependenceAnalysisWrapperPass>();
  AU.setPreservesAll();
}

char Instrument::ID = 0;
static RegisterPass<Instrument> X("Instrument",
                                  "Instrument Binary Instructions");
