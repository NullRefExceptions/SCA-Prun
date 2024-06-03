#ifndef INTERCONSTPROP_H_
#define INTERCONSTPROP_H_
/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */
/* This is the main header file for the ConstantFolding Pass. It defines a class ConstantFolding, which is inherited from LLVM Module Pass. All the methods
of the class are defined in src/Transforms/ConstantFolding.cpp.*/

#include "llvm/IR/Function.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/SimplifyLibCalls.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/CallGraph.h"

#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"

#include "LoopUnroller.h"
#include "Mem.h"
#include "Debug.h"

using namespace llvm;
using namespace std;

typedef pair<Instruction *, Instruction *> InstPair;
typedef set<Value *> ValSet;
typedef vector<BasicBlock *> BBList;

struct ConstantFolding : public ModulePass
{
  static char ID;
  Module *module;
  const DataLayout *DL;
  TargetLibraryInfo *TLI;
  ProfileSummaryInfo *PSI;
  BasicBlock *currBB;
  Function *currfn;
  set<CallInst *> needToRemove;
  bool exit = 0;
  bool partOfLoop;
  bool PreserveLCSSA;

  unsigned trackedLoads = 0;
  unsigned fSkipped = 0;

  vector<LoopUnroller *> testStack;
  vector<BBList> worklistBB;
  vector<ValSet> funcValStack;

  void runOnFunction(CallInst *, Function *);
  bool runOnBB(BasicBlock *);
  void runOnInst(Instruction *);

  ProcResult processAllocaInst(AllocaInst *);
  ProcResult processStoreInst(StoreInst *);
  ProcResult processLoadInst(LoadInst *);
  ProcResult processGEPInst(GetElementPtrInst *);
  ProcResult processCallInst(CallInst *);
  ProcResult processBitCastInst(BitCastInst *);
  ProcResult processPHINode(PHINode *);
  ProcResult processReturnInst(ReturnInst *);
  ProcResult processTermInst(Instruction *);
  ProcResult processBinaryInst(BinaryOperator *);
  ProcResult processExtractValue(ExtractValueInst *inst);
  ProcResult tryfolding(Instruction *);
  Instruction *simplifyInst(Instruction *);
  CmpInst *foldCmp(CmpInst *);

  bool satisfyConds(Function *, CallInst *);

  CallInst *cloneAndAddFuncCall(CallInst *);

  Function *simplifyCallback(CallInst *, Instruction **);

  void replaceIfNotFD(Value *, Value *);

  void copyCallerContext(CallInst *, Function *);
  void duplicateContext(BasicBlock *, BasicBlock *);
  void propagateArgs(CallInst *, Function *);

  bool cloneRegister(Value *, Value *);
  bool replaceOrCloneRegister(Value *, Value *);
  Register *processInstAndGetRegister(Value *);
  void cloneFuncStackAndRegisters(ValueToValueMapTy &vmap, ValSet &);

  bool visitBB(BasicBlock *, BasicBlock *);
  Function *doFunctionClone(Function *func, ValueToValueMapTy &vmap, bool isUnroll);
  void addToWorklistBB(BasicBlock *);

  void pushFuncStack(Value *val);
  ValSet popFuncValStack();

  Loop *isLoopHeader(BasicBlock *BB, LoopInfo &LI);
  LoopUnroller *unrollLoop(BasicBlock *, BasicBlock *&);
  LoopUnroller *unrollLoopInClone(Loop *L, ValueToValueMapTy &, vector<ValSet> &);

  void copyFuncIntoClone(Function *, ValueToValueMapTy &, Function *, vector<ValSet> &);

  void checkPtrMemory(BasicBlock *currBB);
  BasicBlock *label2BB(string funcName, string bbLabel);
  string BB2label(BasicBlock *bb);

  string originName(Function *f);

  void markInstMemNonConst(Instruction *);
  void markMemNonConst(Type *, uint64_t, BasicBlock *);
  void markArgsAsNonConst(CallInst *callInst);

  bool getSingleVal(Value *, uint64_t &);
  void addSingleVal(Value *, uint64_t, bool replace64 = false, bool tracked = false);

  bool getStr(Value *ptr, char *&str, uint64_t size);
  bool getStr(uint64_t addr, char *&str);
  uint64_t createConstStr(string str);
  bool handleConstStr(Value *);
  bool getPointerAddr(Value *, uint64_t &);

  bool handleOverFlowInst(CallInst *callInst);
  ConstantFolding() : ModulePass(ID) {}
  void forcePeelLoop(uint64_t count);
  bool runOnModule(Module &M);
  void getAnalysisUsage(AnalysisUsage &AU) const;
  template <typename AnalysisType>
  AnalysisType &getFuncAnalysis(Function &f)
  {
    return getAnalysis<AnalysisType>(f);
  }
};

extern ConstantFolding *cf;

#endif
