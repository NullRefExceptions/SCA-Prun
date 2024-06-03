/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */

/*This is the main header file for the BBOps. It defines a class BBOps, which contains 
attributes and methods for Basic Block (BB) operations such as initailzing BB information, 
marking BB visited or unreachable, creating/merging/duplicating/copying context etc.. All 
the methods of the class are defined in src/BBOps.cpp.*/
#ifndef BBOPS_H_
#define BBOPS_H_

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Constants.h"

#include <set>

#include "VecUtils.h"
#include "ContextInfo.h"
#include "BBInfo.h"

using namespace std;
using namespace llvm;

class BBOps
{
public:
  BBOps() {}
  bool isBBInfoInitialized(BasicBlock *BB);
  void initAndAddBBInfo(BasicBlock *BB, LoopInfo &LI);

  bool partOfLoop(Instruction *ins);
  bool partOfLoop(BasicBlock *BB);

  void markVisited(BasicBlock *BB);
  bool isUnReachable(BasicBlock *BB);

  // returns true if there is a single child and it is equal to succ
  bool isSingleSucc(BasicBlock *pred, BasicBlock *succ);
  // returns true if there is a single child and it is not equal to succ
  bool isnotSingleSucc(BasicBlock *pred, BasicBlock *succ);
  bool needToduplicate(BasicBlock *BB, BasicBlock *from);

  void addAncestor(BasicBlock *succ, BasicBlock *anc);
  bool visitBB(BasicBlock *BB, LoopInfo &LI);
  bool predecessorsVisited(BasicBlock *BB, LoopInfo &LI);

  bool mergeContext(BasicBlock *BB, BasicBlock *prev);
  void freePredecessors(BasicBlock *BB);
  void freeBB(BasicBlock *BB);
  void propagateUR(BasicBlock *BB, LoopInfo &LI);
  void checkReadyToVisit(BasicBlock *BB);
  void markSuccessorsAsUR(Instruction *termInst, LoopInfo &LI);
  bool foldToSingleSucc(Instruction *termInst, vector<BasicBlock *> &readyToVisit,
                        LoopInfo &LI);
  bool straightPath(BasicBlock *from, BasicBlock *to);
  Value *foldPhiNode(PHINode *phiNode, vector<Value *> &);
  BasicBlock *getRfromPred(BasicBlock *BB);
  void recomputeLoopInfo(Function *F, LoopInfo &LI, BasicBlock *);
  void copyFuncBlocksInfo(Function *F, ValueToValueMapTy &vmap);

  void createNewContext(BasicBlock *BB, Module *);
  void duplicateContext(BasicBlock *to, BasicBlock *);
  void imageContext(BasicBlock *to, BasicBlock *);
  Memory *duplicateMem(BasicBlock *);
  bool hasContext(BasicBlock *BB);
  void copyContext(Memory *mem, BasicBlock *);
  uint64_t allocateStack(uint64_t size, BasicBlock *);
  uint64_t allocateHeap(uint64_t size, BasicBlock *);
  uint64_t loadMem(uint64_t addr, uint64_t size, BasicBlock *);
  void storeToMem(uint64_t val, uint64_t size, uint64_t addr, BasicBlock *);
  void setConstMem(bool val, uint64_t addr, uint64_t size, BasicBlock *);
  void setConstContigous(bool val, uint64_t addr, BasicBlock *);

  void *getActualAddr(uint64_t addr, BasicBlock *);
  bool checkConstMem(uint64_t addr, uint64_t size, BasicBlock *);
  bool checkConstContigous(uint64_t addr, BasicBlock *);
  bool checkConstStr(uint64_t addr, BasicBlock *);
  bool checkConstStr(uint64_t addr, uint64_t max, BasicBlock *);

  void cleanUpFuncBBInfo(Function *f);

  void copyContexts(Function *to, Function *from, ValueToValueMapTy &vmap, Module *);

  void getVisitedPreds(BasicBlock *BB, vector<BasicBlock *> &preds);

  uint64_t getSizeContigous(uint64_t, BasicBlock *);

  bool contextMatch(Memory *, BasicBlock *);

  map<BasicBlock *, BBInfo *> BBInfoMap;
  map<BasicBlock *, ContextInfo *> BBContextMap;
  set<BasicBlock *> visited;
  set<BasicBlock *> unReachable;
  vector<BasicBlock *> readyToVisit;
};

extern BBOps bbOps;
#endif
