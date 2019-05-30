#include "llvm/ADT/Statistic.h"  // For the STATISTIC macro.
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Constants.h"          // For ConstantData, for instance.
#include "llvm/IR/DebugInfoMetadata.h"  // For DILocation
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"  // To use the iterator instructions(f)
#include "llvm/IR/Instructions.h"  // To have access to the Instructions.
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"  // To print error messages.
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"  // For dbgs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "dependenceAnalysisWrapperPass.h"

using namespace llvm;

namespace phoenix {

DependenceAnalysis* DependenceAnalysisWrapperPass::getDependenceAnalysis() {
  return this->DA;
}

bool DependenceAnalysisWrapperPass::runOnFunction(Function& F) {
  if (F.isDeclaration() || F.isIntrinsic() || F.hasAvailableExternallyLinkage())
    return false;

  auto* DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto* PDT = &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();

  this->DA = new DependenceAnalysis(DT, PDT);

  return false;
}

void DependenceAnalysisWrapperPass::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<PostDominatorTreeWrapperPass>();
  AU.setPreservesAll();
}

char DependenceAnalysisWrapperPass::ID = 0;
static RegisterPass<DependenceAnalysisWrapperPass> X(
    "DependenceAnalysis",
    "Run dependence analysis on each function");

}  // end namespace phoenix
