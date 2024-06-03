#ifndef CONTROLDEPENDENCYGRAPH2_H_
#define CONTROLDEPENDENCYGRAPH2_H_
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/GraphWriter.h"
#include "map"

#include "DependencyGraph.hpp"
#include "CallWrapper.hpp"
#include "FunctionWrapper.hpp"

namespace pdg
{
  class ControlDependencyGraph2
  {
  public:
    using cgdNode = pdg::DependencyNode<pdg::InstructionWrapper>;
    ControlDependencyGraph2(llvm::Function *F, llvm::PostDominatorTree *PDT)
    {
      CDG = new DependencyGraph<InstructionWrapper>();
      this->PDT = PDT;
      this->Func = F;
      this->dumpOnlyDep = false;
      PDGUtils::getInstance().constructInstMap(*F);
      computeDependencies(*F);
      initDijkstra();
    }

    ~ControlDependencyGraph2()
    {
      delete CDG;
    }

    void computeDependencies(llvm::Function &F);
    void addInstToBBDependency(InstructionWrapper *from, llvm::BasicBlock *to, DependencyType depType);
    void addBBToBBDependency(llvm::BasicBlock *from, llvm::BasicBlock *to, DependencyType depType);
    DependencyGraph<InstructionWrapper> *_getCDG() { return CDG; }
    void dump(std::string fileName);
    //TODO：我们需要更高效的算法,在此之前我们仅计算最短的path，而不是所有path
    void getRDep(llvm::Instruction *ins,std::vector<std::vector<llvm::Instruction *>>&pathVector);
    void initDijkstra();
    std::map<cgdNode *, cgdNode *> pre;
    std::map<cgdNode *, uint64_t> dis;
    bool dumpOnlyDep;

  private:
    DependencyGraph<InstructionWrapper> *CDG;
    llvm::PostDominatorTree *PDT;
    llvm::Function *Func;
    
  };
}

#endif