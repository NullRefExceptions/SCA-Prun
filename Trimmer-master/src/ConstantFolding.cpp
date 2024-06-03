// Copyright (c) 2020 SRI International All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

/*This pass goes through the instructions in the bitcode file, folding and propagating constants, cloning functions, unrolling loops,
specializing file I/O and strings.*/
#include "ConstantFolding.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/SimplifyLibCalls.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/FormatVariadic.h"

#include <malloc.h>
#include <map>
#include <set>
#include <iostream>
#include <vector>
#include <assert.h>
#include <fstream>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <sstream>

#include <chrono>
#include <fstream>

#include "Utils.h"
#include "StringUtils.h"

#include "TrackInfo.h"
#include "Debug.h"
#include "BBOps.h"
#include "ContextInfo.h"
#include "BBInfo.h"
#include "FuncInfo.h"
#include "RegOps.h"
#include "Stats.h"
#include "ModSet.h"
#include "Global.h"
#include "spec/SpecFileIO.h"
#include "spec/SpecGetopt.h"
#include "spec/SpecHeap.h"
#include "spec/SpecLibc.h"
#include "spec/SpecString.h"
#include "spec/SpecSyscall.h"

using namespace llvm;
using namespace std;

static cl::opt<int> disableExit("disableExit", cl::desc("disable exiting on fork/pthread function"), cl::init(0));

static cl::opt<int> useGlob("useGlob", cl::desc("are the globals mod-ref to be used in choosing function specialisation"), cl::init(0));

static cl::opt<int> exceedLimit("exceedLimit", cl::desc("heuristic to limit function cloning to a limitted number"), cl::init(0));

string targetFunc = "main";
string targetBB = "%33";
string stopBB = "%33";

bool showFunc = false;
bool showBB = false;
bool showInst = false;
BasicBlock *ConstantFolding::label2BB(string funcName, string bbLabel)
{
  auto func = module->getFunction(funcName);
  for (auto &bb : *func)
  {
    SmallVector<char, 10> sv;
    raw_svector_ostream SO(sv);
    bb.printAsOperand(SO, false);
    if (SO.str() == bbLabel)
      return &bb;
  }
  return nullptr;
}

string ConstantFolding::BB2label(BasicBlock *bb)
{
  SmallVector<char, 10> sv;
  raw_svector_ostream SO(sv);
  bb->printAsOperand(SO, false);
  return SO.str().str();
}

string ConstantFolding::originName(Function *f)
{
  StringRef name = f->getName();
  auto pos = name.find(".");
  return name.substr(0, pos).str();
}

//==================Run On Inst====================
/**
 * Process Alloca Instructions:
 * ty * %a = ty
 * allocate shadow memory of bytes sizeof(ty) on the stack and add shadow register
 * with value equal to the starting address of the allocated memory
 */
ProcResult ConstantFolding::processAllocaInst(AllocaInst *ai)
{
  Type *ty = ai->getAllocatedType();
  unsigned size = DL->getTypeAllocSize(ty);
  uint64_t addr = bbOps.allocateStack(size, currBB);

  pushFuncStack(ai);
  regOps.addRegister(ai, ty, addr, false);
  debug(Yes) << "allocaInst : size " << size << " at address " << addr << "\n";
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

/*
 * Process Bitcast Instruction :
 * bitcast ty1 * %a, ty2 * %b
 * if shadow register for %b exists add shadow register for %a with same value
 * as %b but type ty1
 */
ProcResult ConstantFolding::processBitCastInst(BitCastInst *bi)
{

  Value *ptr = bi->getOperand(0);
  Register *reg = processInstAndGetRegister(ptr);
  if (!reg)
  {
    // try function
    if (dyn_cast<Function>(ptr))
    {
      addSingleVal(bi, (uint64_t)ptr, false, true);
      debug(Yes) << "in bitcast inst\n";
      return NOTFOLDED;
    }
    debug(Yes) << "BitCastInst : Not found in Map\n";
    return NOTFOLDED;
  }

  pushFuncStack(bi);
  debug(Yes) << reg->getValue() << "\n";
  regOps.addRegister(bi, bi->getType(), reg->getValue(), reg->getTracked());
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

ProcResult ConstantFolding::processStoreInst(StoreInst *si)
{
  Value *storeOp = si->getOperand(0);
  Value *ptr = si->getOperand(1);
  Register *reg = processInstAndGetRegister(ptr);
  if (!reg)
  {
    debug(Yes) << "StoreInst : not found in map\n";
    return NOTFOLDED;
  }
  uint64_t addr = reg->getValue();
  uint64_t size = DL->getTypeAllocSize(storeOp->getType());
  uint64_t val;
  if (!getSingleVal(storeOp, val))
  {
    debug(Yes) << "StoreInst : from cannot be determined\n";
    bbOps.setConstMem(false, addr, size, currBB);
    return NOTFOLDED;
  }

  bbOps.storeToMem(val, size, addr, currBB);
  bbOps.setConstMem(true, addr, size, currBB);
  stats.incrementInstructionsFolded();
  debug(Yes) << "StoreInst currBB: " << currBB->getParent()->getName() << "\n";
  return UNDECIDED;
}

// Process Load instructions: load memory and map the load value to the memory address loaded
ProcResult ConstantFolding::processLoadInst(LoadInst *li)
{
  stats.incrementTotalLoads();

  Value *ptr = li->getOperand(0);
  Register *reg = processInstAndGetRegister(ptr);
  if (!reg)
  {
    debug(Yes) << "LoadInst : Not found in Map\n";
    return NOTFOLDED;
  }
  uint64_t addr = reg->getValue();
  if (addr == 999999999)
  {
    pushFuncStack(li);
    regOps.addRegister(li, li->getType(), 999999999);
    return UNDECIDED;
  }
  uint64_t size = DL->getTypeAllocSize(li->getType());

  debug(Yes) << addr << " LoadInst\n";
  if (!bbOps.checkConstMem(addr, size, currBB))
  {
    debug(Yes) << " LoadInst : skipping non constant\n";
    return NOTFOLDED;
  }

  debug(Yes) << "Loading from operand: " << *ptr << "\n";

  if (reg->getTracked())
  {
    trackedLoads++;
  }

  uint64_t val = bbOps.loadMem(addr, size, currBB);
  debug(Yes) << "LoadInst currBB: " << currBB->getParent()->getName() << "\n";

  debug(Yes) << "LoadInst Val: " << val << "\n";
  addSingleVal(li, val, true, reg->getTracked());
  pushFuncStack(li);
  stats.incrementLoadsFolded();
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

// Process GetElementbyPtr Instructions: maps the GEP value to the resultant address in memory so that it can be used in further instructions.
ProcResult ConstantFolding::processGEPInst(GetElementPtrInst *gi)
{

  Value *ptr = gi->getOperand(0);

  Register *reg = processInstAndGetRegister(ptr);
  if (!reg)
  {
    debug(Yes) << "GepInst : Not found in map\n";
    return NOTFOLDED;
  }

  unsigned contSize = bbOps.getSizeContigous(reg->getValue(), currBB);
  unsigned OffsetBits = DL->getPointerTypeSizeInBits(gi->getType());
  APInt offset(OffsetBits, 0);
  bool isConst = gi->accumulateConstantOffset(*DL, offset);
  debug(Yes) << "[processGEPInst]isConst: " << isConst << "\n";

  Value *offsetVal = gi->getOperand(1);
  Register *regOffset = processInstAndGetRegister(offsetVal);

  if ((!isConst && !regOffset))
  {
    debug(Yes) << "GepInst : offset not constant\n";

    unsigned allocSize = DL->getTypeAllocSize(reg->getType());
    unsigned numArray = contSize / allocSize;
    uint64_t address = reg->getValue();
    for (unsigned i = 0; i < numArray; i++)
    {

      if (reg->getType()->isPointerTy())
      {
        debug(Yes) << "Marking memory non const! \n";
        markMemNonConst(dyn_cast<PointerType>(reg->getType())->getElementType(), address, currBB);
      }

      else
      {
        debug(Yes) << "Marking memory non const! \n";
        markMemNonConst(reg->getType(), address, currBB);
      }
      address = address + allocSize;
    }
    return NOTFOLDED;
  }
  if (reg->getValue() == 999999999)
  {
    unsigned short int num = traitsTable[offset.getZExtValue() / 2];
    uint64_t addr = bbOps.allocateHeap(sizeof(unsigned short int), currBB);
    unsigned short int *source = (unsigned short int *)bbOps.getActualAddr(addr, currBB);
    *source = num;
    regOps.addRegister(gi, gi->getType(), addr);
    pushFuncStack(gi);
    return UNDECIDED;
  }
  uint64_t val;

  if (regOffset && !isConst)
  {
    val = reg->getValue() + regOffset->getValue();
    debug(Yes) << "Register Offset value: " << regOffset->getValue() << "\n";
  }
  else
  {
    val = reg->getValue() + offset.getZExtValue();
    debug(Yes) << "APInt Offset value: " << offset.getZExtValue() << "\n";
  }

  debug(Yes) << "Resultant Address: " << val << "\n";
  pushFuncStack(gi);

  regOps.addRegister(gi, gi->getType(), val, reg->getTracked());
  debug(Yes) << val << " GEP Inst\n";
  stats.incrementInstructionsFolded();

  return UNDECIDED;
}

bool ConstantFolding::getStr(uint64_t addr, char *&str)
{
  if (!bbOps.checkConstContigous(addr, currBB))
  {
    debug(Yes) << "getStr : ptr not constant\n";
    return false;
  }
  str = (char *)bbOps.getActualAddr(addr, currBB);
  return true;
}

bool ConstantFolding::getStr(Value *ptr, char *&str, uint64_t size)
{
  StringRef stringRef;
  if (getConstantStringInfo(ptr, stringRef, 0, false))
  {
    str = new char[stringRef.str().size() + 1];
    strcpy(str, stringRef.str().c_str());
  }
  else if (Register *reg = processInstAndGetRegister(ptr))
  {
    if (!bbOps.checkConstMem(reg->getValue(), size, currBB))
    {
      debug(Yes) << "getStr : ptr not constant\n";
      return false;
    }
    str = (char *)bbOps.getActualAddr(reg->getValue(), currBB);
  }
  else
  {
    debug(Yes) << "getStr : ptr not found in Map\n";
    return false;
  }
  return true;
}

/*
 * Try folding phiNodes
 */
ProcResult ConstantFolding::processPHINode(PHINode *phiNode)
{
  debug(Yes) << "Invoked processPHINode...\n";
  vector<Value *> incPtrs;
  Value *val = bbOps.foldPhiNode(phiNode, incPtrs);
  // in case not folded, mark all memories as non constant
  if (!val)
  {
    debug(Yes) << "Unable to fold PHINode!\n";
    for (auto &val : incPtrs)
    {
      if (Register *reg = processInstAndGetRegister(val))
      {
        Value *val = regOps.getValue(reg);
        assert(val);
        if (val->getType()->isPointerTy())
        {
          debug(Yes) << "Marking PhiNode memory non const! \n";
          markMemNonConst(dyn_cast<PointerType>(val->getType())->getElementType(), reg->getValue(), currBB);
        }
      }
    }
  }

  if (val && replaceOrCloneRegister(phiNode, val))
  {
    debug(Yes) << "folded phiNode\n";
    stats.incrementInstructionsFolded();
    return FOLDED;
  }
  else
  {
    debug(Yes) << "failed to fold phiNode\n";
    return NOTFOLDED;
  }
}

ProcResult ConstantFolding::processExtractValue(ExtractValueInst *inst)
{
  Value *val = inst->getOperand(0);
  Register *reg = processInstAndGetRegister(val);
  if (!reg)
  {
    debug(Yes) << "extract value register not found"
               << "\n";
    return NOTFOLDED;
  }

  uint32_t off = inst->getIndices()[0];
  int32_t answer = 0;
  if (off == 0)
  {
    answer = (~(8589934592 - 1) & reg->getValue()) >> 32;
  }
  else
  {
    answer = (8589934592 - 1) & reg->getValue();
  }
  debug(Yes) << "extract value adding constant" << answer << "\n";
  addSingleVal(inst, answer, true, true);
  stats.incrementInstructionsFolded();
  return FOLDED;
}

ProcResult ConstantFolding::processBinaryInst(BinaryOperator *binInst)
{
  Value *op1 = binInst->getOperand(0);
  Value *op2 = binInst->getOperand(1);
  Constant *op1c = dyn_cast<Constant>(op1);
  Constant *op2c = dyn_cast<Constant>(op2);
  if (op1c && op2c)
  {
    Constant *constVal = ConstantFoldInstruction(binInst, *DL, TLI);
    if (constVal)
    {
      replaceIfNotFD(binInst, constVal);
      stats.incrementInstructionsFolded();
      return FOLDED;
    }
  }

  // If this is 0 / Y, it doesn't matter that the second operand is
  // overdefined, and we can replace it with zero.
  if (binInst->getOpcode() == Instruction::UDiv || binInst->getOpcode() == Instruction::SDiv)
    if (op1c && op1c->isNullValue())
    {
      replaceIfNotFD(binInst, op1c);
      stats.incrementInstructionsFolded();
      return FOLDED;
    }

  // If this is:
  // -> AND/MUL with 0
  // -> OR with -1
  // it doesn't matter that the other operand is overdefined.
  if (binInst->getOpcode() == Instruction::And || binInst->getOpcode() == Instruction::Mul ||
      binInst->getOpcode() == Instruction::Or)
  {
    Constant *constantOP = nullptr;
    if (op1c)
      constantOP = op1c;
    else if (op2c)
      constantOP = op2c;

    if (constantOP)
    {

      if (binInst->getOpcode() == Instruction::And ||
          binInst->getOpcode() == Instruction::Mul)
      {
        // X and 0 = 0
        // X * 0 = 0
        if (constantOP->isNullValue())
        {
          replaceIfNotFD(binInst, constantOP);
          stats.incrementInstructionsFolded();
          return FOLDED;
        }
      }
      else
      {
        // X or -1 = -1
        if (ConstantInt *CI = dyn_cast<ConstantInt>(constantOP))
          if (CI->isMinusOne())
          {
            replaceIfNotFD(binInst, constantOP);
            stats.incrementInstructionsFolded();
            return FOLDED;
          }
      }
    }
  }
  return NOTFOLDED;
}

bool ConstantFolding::getPointerAddr(Value *val, uint64_t &addr)
{
  if (Register *reg = processInstAndGetRegister(val))
  {
    addr = reg->getValue();
    return true;
  }
  if (isa<ConstantPointerNull>(val))
  {
    addr = 0;
    return true;
  }
  return false;
}

CmpInst *ConstantFolding::foldCmp(CmpInst *CI)
{
  Value *oldLHS = CI->getOperand(0);
  Value *oldRHS = CI->getOperand(1);
  uint64_t lAddr, rAddr;
  if (getPointerAddr(oldLHS, lAddr) &&
      getPointerAddr(oldRHS, rAddr))
  {
    IntegerType *intTy = IntegerType::get(module->getContext(), 64);
    Value *newLHS = ConstantInt::get(intTy, lAddr);
    Value *newRHS = ConstantInt::get(intTy, rAddr);
    CmpInst *NCI = CmpInst::Create(CI->getOpcode(), CI->getPredicate(),
                                   newLHS, newRHS);
    NCI->insertBefore(CI);
    debug(Yes) << *CI << " ";
    replaceIfNotFD(CI, NCI);
    return NCI;
  }
  return NULL;
}

Instruction *ConstantFolding::simplifyInst(Instruction *I)
{
  for (unsigned i = 0; i < I->getNumOperands(); i++)
  {
    Value *val = I->getOperand(i);
    if (Register *reg = processInstAndGetRegister(val))
    {
      if (IntegerType *intTy = dyn_cast<IntegerType>(val->getType()))
        replaceIfNotFD(val, ConstantInt::get(intTy, reg->getValue()));
    }
  }
  if (isa<CmpInst>(I) &&
      isa<PointerType>(I->getOperand(0)->getType()))
    return foldCmp(dyn_cast<CmpInst>(I));
  else if (auto CI = dyn_cast<CmpInst>(I))
  {
    for (unsigned i = 0; i < CI->getNumOperands(); i++)
    {
      Value *val = CI->getOperand(i);
      uint64_t sfd;
      if (getSingleVal(val, sfd) && fdInfoMap.find(sfd) != fdInfoMap.end())
      {
        debug(Yes) << "foldCmp: folding for file descriptor\n";
        CI->setOperand(i, ConstantInt::get(CI->getOperand(0)->getType(), sfd));
      }
    }
  }
  else if (SelectInst *SI = dyn_cast<SelectInst>(I))
  {
    if (ConstantInt *CI = dyn_cast<ConstantInt>(SI->getCondition()))
    {
      Value *rep = CI->getZExtValue() ? SI->getTrueValue() : SI->getFalseValue();
      replaceOrCloneRegister(I, rep);
    }
    else
    {
      // non constant select, mark mem non constant appropriately
      markInstMemNonConst(SI);
    }
  }
  return NULL;
}

/*
 * Try folding simple Instructions like icmps, sext, zexts
 */
ProcResult ConstantFolding::tryfolding(Instruction *I)
{
  if (Instruction *sI = simplifyInst(I))
    return tryfolding(sI);
  else
  {
    Constant *constVal = ConstantFoldInstruction(I, *DL, TLI);
    if (constVal)
    {
      replaceIfNotFD(I, constVal);
      stats.incrementInstructionsFolded();
      return FOLDED;
    }
  }
  return NOTFOLDED;
}

/**
 * Process a single instruction.
 Handles instructions according to Instruction Type, e.g., AllocaInst, StoreInst, LoadInst
 */
typedef uint64_t (*pngptr)[157];
typedef uint64_t (*pnginfoptr)[45];
void ConstantFolding::runOnInst(Instruction *I)
{
  ProcResult result;
  printInst(I, Yes);
  /*   if (!COInfo::remainConstant(1))
    {
      errs() << "";
    } */
  if (bbOps.partOfLoop(I))
  {
    debug(Yes) << "runOnInst: bbOps.partOfLoop(" << *I << "): true\n";
    partOfLoop = true;
    markInstMemNonConst(I);

    if (auto LI = dyn_cast<LoadInst>(I))
    {
      stats.incrementTotalLoads();
    }

    if (auto CI = dyn_cast<CallInst>(I))
    {
      if (CI->getCalledFunction() && CI->getCalledFunction()->isDeclaration())
        stats.incrementTotalLibCalls();
      else
        stats.incrementFunctionCalls();

      if (CI->getCalledFunction() && (CI->getCalledFunction()->getName() == "fork" || CI->getCalledFunction()->getName().substr(0, 7) == "pthread"))
      {
        debug(Yes) << "XXX fork or pthread invoked ...\n";
        if (!disableExit)
        {
          exit = 1;
        }
        return;
      }

      if (CI->getCalledFunction())
      {

        if (CI->getCalledFunction()->getName() == "getopt" || CI->getCalledFunction()->getName() == "getopt_long")
        {
          if (module->getNamedGlobal("optind"))
          {

            Register *optindReg = processInstAndGetRegister(module->getNamedGlobal("optind"));
            bbOps.setConstContigous(false, optindReg->getValue(), currBB);
          }

          if (module->getNamedGlobal("optarg"))
          {

            Register *optargReg = processInstAndGetRegister(module->getNamedGlobal("optarg"));
            bbOps.setConstContigous(false, optargReg->getValue(), currBB);
          }
        }
      }
    }

    if (!I->isTerminator())
    { // need terminator instruction to make BB graphs
      return;
    }
  }

  else if (I->getParent())
  {
    partOfLoop = false;
  }

  if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(I))
  {
    result = processAllocaInst(allocaInst);
  }
  else if (BitCastInst *bitCastInst = dyn_cast<BitCastInst>(I))
  {
    result = processBitCastInst(bitCastInst);
  }
  else if (StoreInst *storeInst = dyn_cast<StoreInst>(I))
  {
    result = processStoreInst(storeInst);
  }
  else if (LoadInst *loadInst = dyn_cast<LoadInst>(I))
  {
    result = processLoadInst(loadInst);
  }
  else if (GetElementPtrInst *GEPInst = dyn_cast<GetElementPtrInst>(I))
  {
    result = processGEPInst(GEPInst);
  }
  else if (PHINode *phiNode = dyn_cast<PHINode>(I))
  {
    result = processPHINode(phiNode);
  }
  else if (ReturnInst *retInst = dyn_cast<ReturnInst>(I))
  {
    result = processReturnInst(retInst);
  }
  else if (I->isTerminator())
  {
    result = processTermInst(I);
  }
  else if (CallInst *callInst = dyn_cast<CallInst>(I))
  {
    result = processCallInst(callInst);
  }
  // else if (ExtractValueInst *ev = dyn_cast<ExtractValueInst>(I))
  //{
  //   result = processExtractValue(ev);
  // }
  else if (BinaryOperator *binInst = dyn_cast<BinaryOperator>(I))
  {
    result = processBinaryInst(binInst);
  }
  else
  {
    result = tryfolding(I);
  }
}

//==================terminator related=====================
/*
 * For last processed BB, if after merging memory of its preds,
 * two pointers are non constant, mark their
 * memories as non const
 */
void ConstantFolding::checkPtrMemory(BasicBlock *currBB)
{
  vector<BasicBlock *> preds;
  bbOps.getVisitedPreds(currBB, preds);

  debug(Yes) << "SIZE : " << preds.size() << "\n";
  for (auto BB : preds)
  {
    for (auto &I : *BB)
    {

      if (!dyn_cast<StoreInst>(&I))
        continue;
      StoreInst *str = dyn_cast<StoreInst>(&I);
      Value *ptr = str->getOperand(1);
      PointerType *type = dyn_cast<PointerType>(ptr->getType());
      Register *reg = processInstAndGetRegister(ptr);
      if (!reg)
        continue;
      uint64_t size = DL->getTypeAllocSize(str->getOperand(0)->getType());
      // if some memory was marked non const after merging
      if (bbOps.checkConstMem(reg->getValue(), size, BB) &&
          !bbOps.checkConstMem(reg->getValue(), size, currBB))
      {
        if (type->getElementType()->isPointerTy())
        {
          uint64_t value = bbOps.loadMem(reg->getValue(), size, BB); // load the pointer in memory
          markMemNonConst(dyn_cast<PointerType>(type->getElementType())->getElementType(), value, currBB);
        }
      }
    }
  }
}

/**
 * Appropriately mirrors or duplicates succ BasicBlock, based on the
 * predecessor BasicBlock from. Also frees the predecessor if possible,
 * simplifies loops in succ, and runs runOnBB on successor
 */
bool ConstantFolding::visitBB(BasicBlock *succ, BasicBlock *from)
{
  if (bbOps.needToduplicate(succ, from))
  {
    debug(Yes) << "duplicating\n";
    debug(Yes) << "duplicating from " << BB2label(from) << " to " << BB2label(succ) << "\n";
    duplicateContext(succ, from);
    bbOps.mergeContext(succ, from);
    checkPtrMemory(succ);
  }
  else
  {
    debug(Yes) << "cloning\n";
    bbOps.imageContext(succ, from);
  }

  bbOps.addAncestor(succ, from);
  bbOps.freeBB(from);

  addToWorklistBB(succ);

  return true;
}

/*
   Process all terminator Instructions except Returns
   first try to fold a terminator Instruction to a single successor.
   e.g.
   %i = icmp eq i32 %a, 7
   br i1 %i, bb %x, bb %y

   if we can fold the icmp Instruction we can fold the branch Instruction
   to point to only one block. (Which might lead to code debloating).

   Then visit all successors one by one.
   bbOps.isnotSingleSucc(BB) returns true if the terminator has been folded to a
   single successor and BB is NOT that successor.
   e.g. if %i above is true bbOps.isnotSingleSucc(%y) will return true.
   */
ProcResult ConstantFolding::processTermInst(Instruction *termInst)
{
  /*
  检查能否fold到一个succ（包括无条件跳转），如果能，则传播这次fold的影响：
    1.被确定不能从此term到达的BB，其可能变成完全不可达（URfrom++以至于和numPreds相同），
      对这类BB，同样递归的计算其影响
    2.被确定不能从此term到达的BB，其可能变得可以执行（URfrom++以至于Rfrom+URfrom ==numPreds），
      将其记录在readyToVisit中。尽管其是从其他的term到达的
  */
  // COInfo::status();
  vector<BasicBlock *> readyToVisit;
  bool changed;
  LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*currfn, &changed).getLoopInfo();
  bool single = bbOps.foldToSingleSucc(termInst, readyToVisit, LI);
  if (single)
    stats.incrementInstructionsFolded();
  for (BasicBlock *BB : readyToVisit)
  {
    BasicBlock *pred = bbOps.getRfromPred(BB);
    if (pred == NULL)
    { // unreachable blocks only
      continue;
    }
    visitBB(BB, pred);
  }

  unsigned numS = termInst->getNumSuccessors();
  set<BasicBlock *> processed;

  for (unsigned int index = 0; index < numS; index++)
  {
    BasicBlock *succ = termInst->getSuccessor(index);

    if (processed.find(succ) != processed.end())
      continue;

    processed.insert(succ);
    if (bbOps.isnotSingleSucc(currBB, succ))
      continue;
    if (!bbOps.visitBB(succ, LI))
      continue;

    visitBB(succ, currBB);
  }

  ProcResult result = single ? FOLDED : NOTFOLDED;
  return result;
}

/*
   Process Return Instruction:
   At return Instruction we need to save the current memory context as this context
   will need to be replaced after we return to the calling function.
   */
ProcResult ConstantFolding::processReturnInst(ReturnInst *retInst)
{
  debug(Yes) << "Invoked Ret inst\n";
  if (currfn->getName().str() == "main")
    return NOTFOLDED;
  debug(Yes) << "Ret inst, current function: " << currfn->getName().str() << "\n";
  FuncInfo *fi = fimap[currfn];
  Value *ptr = retInst->getReturnValue();
  fi->context = bbOps.duplicateMem(currBB);
  debug(Yes) << "Duplicating Memory ... \n"
             << "fi->context: " << fi->context << "\n";
  if (!ptr)
    return NOTFOLDED;
  if (cloneRegister(retInst, ptr))
  {
    fi->retReg = new Register(*processInstAndGetRegister(retInst));
    stats.incrementInstructionsFolded();
  }
  return NOTFOLDED;
}

//=================Process Call inst related====================
bool ConstantFolding::satisfyConds(Function *F, CallInst *ci)
{
  // is this function exceeds clone limit?
  // todo check Recursion,(hint:worklistBB as callstack)
  if (exceedLimit != 0)
  {
    if (fimap[F]->fi_origin->clonedCounter > exceedLimit)
    {
      debug(Yes) << F->getName() << "\t[SATISFYCONDS] exceedLimit\n";
      return false;
    }
  }

  if (CSInfo::isContextObjRWM(ci))
  {
    for (size_t i = 0; i < CSInfo::getNumCSM(ci); i++)
    {
      csm_struct csm = CSInfo::getCSM(ci, i);
      if (csm.isMalloc)
      {
        debug(Yes) << "\t[SATISFYCONDS] satisfied specializing conditions due to malloc\n";
        return true;
      }
      if (csm.isRead || csm.isWrite)
      {
        if (COInfo::remainConstant(i))
        {
          debug(Yes) << "\t[SATISFYCONDS] satisfied specializing conditions due to read/write\n";
          return true;
        }
        else
        {
          // 如果相关CtxObj的精度已经损失殆尽，那就不必再进行分析了
          debug(Yes) << F->getName() << "\t[SATISFYCONDS] we have nothing to do\n";
          continue;
        }
      }
    }
  }

  // Do any of the parameters become constants? (we exclude var arg func)
  if (!F->isVarArg())
  {
    BitVector bv(F->arg_size());
    CSInfo::getConstantBV(ci, &bv);
    BitVector *obv = originBV[ci->getMetadata("csm")];
    bv ^= *obv;
    bool res = bv.any();
    if (res)
    {
      debug(Yes) << "\t[SATISFYCONDS] satisfied specializing conditions due to parameters become constants\n";
      return true;
    }
  }

  debug(Yes) << F->getName() << "\t[SATISFYCONDS] does not meet specializing conditions\n";
  return false;
}

/*
caller处的实参和形参以及返回值类型可能不匹配，此时需要手动加入bitcast和int2ptr、ptr2int等指令，用于：
  1.llvm内联了bitcast指令，我们目前处理不了
  2.间接调用被提升为直接调用
对每个参数间的bitcast指令，需要进行runOnInst，以保证常量信息传递到位
对返回值插入的指令，只能等此次callinst处理完成后，才能传递
 */
Function *ConstantFolding::simplifyCallback(CallInst *callInst, Instruction **pendingInst)
{
  Register *reg = processInstAndGetRegister(callInst->getCalledOperand());
  if (!reg)
    return NULL;
  Function *calledFunction = (Function *)reg->getValue();
  // if (calledFunction->isDeclaration())
  //   return calledFunction;

  callInst->setCalledFunction(calledFunction);
  MDNode *MDNode = MDNode::get(module->getContext(), ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(module->getContext()), 1)));
  callInst->setMetadata("indirect", MDNode);
  Type *callerType = dyn_cast<FunctionType>(dyn_cast<PointerType>(reg->getType())->getElementType())->getReturnType();
  if (calledFunction->getReturnType() != callerType)
  {
    debug(Yes) << formatv("caller type:{0},called type:{1}\n", *callerType, *calledFunction->getReturnType());
    Value *addedInst = nullptr;
    callInst->mutateType(calledFunction->getReturnType());
    IRBuilder<> Builder(callInst->getNextNode());
    if (!(calledFunction->getReturnType()->isPointerTy()) && callerType->isPointerTy())
    {
      debug(Yes) << "added int to ptr inst\n";
      addedInst = Builder.CreateIntToPtr(callInst, callerType);
    }
    else if (calledFunction->getReturnType()->isPointerTy() && !(callerType->isPointerTy()))
    {
      debug(Yes) << "added ptr to int inst\n";
      addedInst = Builder.CreatePtrToInt(callInst, callerType);
    }
    else
    {
      debug(Yes) << "added bitcast inst\n";
      addedInst = Builder.CreateBitCast(callInst, callerType);
    }
    callInst->replaceAllUsesWith(addedInst);
    dyn_cast<User>(addedInst)->setOperand(0, callInst);
    *pendingInst = dyn_cast<Instruction>(addedInst);
  }

  unsigned index = 0;
  for (auto arg = calledFunction->arg_begin(); arg != calledFunction->arg_end();
       arg++, index++)
  {
    Value *callerVal = callInst->getOperand(index);
    Value *calleeVal = getArg(calledFunction, index);
    if (callerVal->getType() != calleeVal->getType())
    {
      debug(Yes) << " type mismatched\n";
      if (isa<ConstantPointerNull>(callerVal))
      {
        ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(calleeVal->getType()));
        callInst->setOperand(index, nullP);
        continue;
      }
      IRBuilder<> Builder(callInst);
      Value *BitcastInst = Builder.CreateBitCast(callerVal, calleeVal->getType());
      debug(Yes) << " caller: " << *callerVal << " callee: " << *calleeVal << "\n";
      auto I = dyn_cast<Instruction>(BitcastInst);
      runOnInst(I);
      callInst->setOperand(index, BitcastInst);
      Register *reg = processInstAndGetRegister(callerVal);
      if (reg)
      {
        regOps.addRegister(BitcastInst, BitcastInst->getType(), reg->getValue(), reg->getTracked());
      }
    }
  }

  debug(Yes) << "set called Function to " << calledFunction->getName() << "\n";
  return calledFunction;
}

CallInst *ConstantFolding::cloneAndAddFuncCall(CallInst *callInst)
{
  ValueToValueMapTy vmap;
  Function *calledFunction = callInst->getCalledFunction();
  Function *cloned = doFunctionClone(calledFunction, vmap, false);
  Instruction *clonedCall = callInst->clone();
  dyn_cast<CallInst>(clonedCall)->setCalledFunction(cloned);
  return dyn_cast<CallInst>(clonedCall);
}

void ConstantFolding::markArgsAsNonConst(CallInst *callInst)
{
  Function *calledFunction = callInst->getCalledFunction();
  if (calledFunction && checkIfReadOnlyFunc(calledFunction))
    return;
  if (calledFunction && calledFunction->onlyReadsMemory())
  {
    return;
  }
  for (unsigned index = 0; index < callInst->arg_size(); index++)
  {
    Value *val = callInst->getOperand(index);
    Register *reg = processInstAndGetRegister(val);
    if (!reg)
      continue;

    if (val->getType()->isPointerTy())
    {
      uint64_t ctxIdx;
      // 如果是contextObj且func已知，我们进行更高精度的分析，否则直接标记
      if (COInfo::getContextObjIdx(reg->getValue(), ctxIdx) && calledFunction != nullptr)
      {
        // CallSite对显示对ContextObj的作用为仅读时，可以跳过，前提是该函数不是外部函数（指针分析工具会标记外部函数的影响为空）
        if (!calledFunction->isDeclaration())
        {
          if (CSInfo::getCSM(callInst, ctxIdx).isWrite == false)
            continue;
        }
        // 尝试根据modinfo标记非常量，如果是外部函数，使用caller的信息
        modinfo_struct ms;
        if (calledFunction->isDeclaration() || calledFunction->isIntrinsic())
          ms = getModInfo(callInst->getFunction(), ctxIdx);
        else
          ms = getModInfo(calledFunction, ctxIdx);

        if (ms.start == UINT64_MAX && ms.end == 0)
          continue; // not write
        else if (ms.start == 0 && ms.end == UINT64_MAX)
          markMemNonConst(dyn_cast<PointerType>(val->getType())->getElementType(), reg->getValue(), currBB); // mark all
        else
          bbOps.setConstMem(false, reg->getValue() + ms.start, ms.end - ms.start, currBB);
      }
      else
        markMemNonConst(dyn_cast<PointerType>(val->getType())->getElementType(), reg->getValue(), currBB);
    }
  }
}

/*
   Process Call Instruction:
   If the call is an indirect call, try to see if we can fold allocate the
   function because of propagation.

   1. TRIMMER debugging instructions added to the source
   2. getopt calls
   3. malloc, calloc etc
   4. Memcpy, Memset
   5. string function : e.g. strcmp, strchr, atoi
   6. fileIO calls : open, read, lseek
   7. external functions : dont visits
   8. internal functions : only visit if it satisfies certain conditions

   If the callInst is an external call, internal call that we dont visit or
   an indirect function call that we fail to simplify we mark all its input
   arguments and all globals as non constant

*/
ProcResult ConstantFolding::processCallInst(CallInst *callInst)
{
  Instruction *pendingInst = nullptr;
  if (!callInst->getCalledFunction() && !simplifyCallback(callInst, &pendingInst))
  {
    markAllGlobsAsNonConst();
    markArgsAsNonConst(callInst);
    stats.incrementFunctionCalls();
    return NOTFOLDED;
  }

  if (!callInst->getCalledFunction())
  {
    markArgsAsNonConst(callInst);
    stats.incrementFunctionCalls();
    return NOTFOLDED;
  }

  Function *calledFunction = callInst->getCalledFunction();
  string name = calledFunction->getName().str();
  if (name == "fork" || name.substr(0, 7) == "pthread")
  {

    if (!disableExit)
    {
      exit = 1;
    }
    return NOTFOLDED;
  }

  /* specialize for functions defined in spec */
  if (handleHeapAlloc(callInst))
  {
  }
  else if (handleGetOpt(callInst))
  {
  }
  else if (handleMemInst(callInst))
  {
  }
  else if (handleStringFunc(callInst))
  {
  }
  else if (handleFileIOCall(callInst))
  {
  }
  else if (handleSysCall(callInst))
  {
  }
  else if (handleLibCCall(callInst))
  {
  }
  else if (calledFunction->isDeclaration())
  {
    debug(Yes) << "skipping function : declaration\n";
    stats.incrementTotalLibCalls();
    // Assumption: Global variables not accessed in extern functions.
    markArgsAsNonConst(callInst);
    return NOTFOLDED;
  }
  else
  {
    stats.incrementFunctionCalls();
    if (!satisfyConds(calledFunction, callInst))
    { // 不对该函数进行分析
      fSkipped++;
      debug(Yes) << "skipping function : does not satisfy conds\n";

      markArgsAsNonConst(callInst);
      markGlobAsNonConst(calledFunction);
      return NOTFOLDED;
    }
    else
    {
      CallInst *clonedInst = cloneAndAddFuncCall(callInst);

      ReplaceInstWithInst(callInst, clonedInst);

      clonedInst->mutateType(clonedInst->getCalledFunction()->getReturnType());

      runOnFunction(clonedInst, clonedInst->getCalledFunction());
    }
  }

  if (pendingInst != nullptr)
  {
    debug(Yes) << "runOn pending Inst : " << *pendingInst << "\n";
    runOnInst(pendingInst);
  }
  return UNDECIDED;
}

//==================Run On BB====================
/*
由于simplifyCall时会添加inst，导致迭代器实效，因此我们在自己的list上执行
   */
bool ConstantFolding::runOnBB(BasicBlock *BB)
{
  if (currfn->getName() == "_tiffWriteProc_trcloned0" && BB2label(BB) == "%.lr.ph.peel")
  {
    errs() << "";
  }
  bbOps.markVisited(BB);
  currBB = BB;
  debug(Yes) << formatv("runBB {0} in {1}\n", BB2label(currBB), currfn->getName());
  // COInfo::status();
  vector<Instruction *> instToRun;
  for (Instruction &ins : *BB)
    instToRun.push_back(&ins);

  for (Instruction *I : instToRun)
  {
    if (exit)
      return false;
    // Whether running a loop unroll test
    if (testStack.size() != 0)
    {
      uint64_t seconds;
      stats.getLoopTime(seconds);
      debug(0) << "checking loop test. time elapsed = " << seconds << "\n";
      LoopUnroller *unroller = testStack.back();
      unroller->checkTermInst(I, seconds);
      if (unroller->testTerminated())
      { // test terminated in the  term condition above
        debug(1) << "Returning true in runOnBB\n\n\n\n";
        return true;
      }
    }
    runOnInst(I);
  }
  bbOps.freeBB(BB);
  debug(Yes) << "Returning false in runOnBB\n\n\n\n";
  return false;
}

//=================Run On Function====================
/*
func可能为origin或cloned，此外unloop stack可能为空或不为空
 */
Function *ConstantFolding::doFunctionClone(Function *func, ValueToValueMapTy &vmap, bool isUnroll)
{
  Function *cloned = llvm::CloneFunction(func, vmap);
  FuncInfo *fi_origin = fimap[func]->fi_origin;
  string newName;
  if (isUnroll)
  {
    newName = llvm::formatv("{0}_unrolled", func->getName()).str();
  }
  else
  {
    newName = llvm::formatv("{0}_trcloned{1}", fi_origin->func->getName(), fi_origin->clonedCounter).str();
    fi_origin->clonedCounter++;
  }
  cloned->setName(newName);

  FuncInfo *fi_cloned = initFuncInfo(cloned);
  fi_cloned->fi_origin = fi_origin;

  CSInfo::initFuncCallSiteInfo(*cloned);

  // todo: init cloned function's modset and global info
  return cloned;
}

void ConstantFolding::addToWorklistBB(BasicBlock *BB)
{
  assert(BB->getParent() == currfn);
  debug(Yes) << "worklistBB add " << BB2label(BB) << "\n";
  worklistBB[worklistBB.size() - 1].push_back(BB);
}

void ConstantFolding::cloneFuncStackAndRegisters(ValueToValueMapTy &vmap, ValSet &oldValSet)
{
  for (auto val : oldValSet)
  {
    if (!vmap[val])
      continue;
    Register *reg = processInstAndGetRegister(val);
    if (reg)
    {
      pushFuncStack(vmap[val]);
      regOps.addRegister(vmap[val], reg);
    }
    else
      continue;
  }
}

void ConstantFolding::copyFuncIntoClone(Function *cloned, ValueToValueMapTy &vmap, Function *current, vector<ValSet> &funcValStack)
{

  bbOps.copyFuncBlocksInfo(current, vmap); // copy over old function bbinfo into cloned function

  bbOps.copyContexts(cloned, current, vmap, module);

  assert(funcValStack.size() >= 2);
  ValSet oldValSet = funcValStack[funcValStack.size() - 2];
  cloneFuncStackAndRegisters(vmap, oldValSet); // copy over stack and registers
}

void ConstantFolding::propagateArgs(CallInst *ci, Function *toRun)
{
  unsigned index = 0;

  for (auto arg = toRun->arg_begin(); arg != toRun->arg_end();
       arg++, index++)
  {
    Value *callerVal = ci->getOperand(index);
    Value *calleeVal = getArg(toRun, index);
    replaceOrCloneRegister(calleeVal, callerVal);
  }
}

void ConstantFolding::duplicateContext(BasicBlock *to, BasicBlock *from)
{
  if (!bbOps.isBBInfoInitialized(to))
  {
    bool changed;
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*to->getParent(), &changed).getLoopInfo();
    bbOps.initAndAddBBInfo(to, LI);
  }
  bbOps.duplicateContext(to, from);
}

void ConstantFolding::copyCallerContext(CallInst *ci, Function *toRun)
{
  BasicBlock *entry = &toRun->getEntryBlock();
  duplicateContext(entry, currBB);
}

LoopUnroller *ConstantFolding::unrollLoop(BasicBlock *BB, BasicBlock *&entry)
{
  Function *cloned = BB->getParent();
  LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*cloned).getLoopInfo();
  ;
  AssumptionCache *AC = &getAnalysis<AssumptionCacheTracker>(*cloned).getAssumptionCache(*cloned);
  Loop *L = LI->getLoopFor(dyn_cast<BasicBlock>(BB));
  LoopUnroller *clonedFnUnroller = new LoopUnroller(module, PreserveLCSSA, L, LI);

  if (clonedFnUnroller->runtest(TLI, *AC, regOps, bbOps, fdInfoMap, currBB))
  {
    return clonedFnUnroller;
  }
  delete clonedFnUnroller;
  return NULL;
}

/*
 * Clones a function, and tries to unroll a loop in it
 */
LoopUnroller *ConstantFolding::unrollLoopInClone(Loop *L, ValueToValueMapTy &vmap, vector<ValSet> &funcValStack)
{

  LoopUnroller *unroller;
  Function *cloned = doFunctionClone(currfn, vmap, true);

  push_back(funcValStack);
  copyFuncIntoClone(cloned, vmap, currfn, funcValStack);

  BasicBlock *temp;
  BasicBlock *header = dyn_cast<BasicBlock>(vmap[L->getHeader()]);
  if (!(unroller = unrollLoop(dyn_cast<BasicBlock>(vmap[L->getHeader()]), temp)))
  {
    // remove clone info
    bbOps.cleanUpFuncBBInfo(cloned);
    regOps.cleanUpFuncBBRegisters(cloned, popFuncValStack());
    return NULL;
  }

  stats.incrementLoopsUnrolled();

  LoopInfo *&LI = unroller->LI;
  bool changed;
  LI = &getAnalysis<LoopInfoWrapperPass>(*cloned, &changed).getLoopInfo();
  debug(Yes) << "unrollLoopInClone: recomputing loop info \n";
  bbOps.recomputeLoopInfo(cloned, *LI, header);
  unroller->cloneOf = currfn;

  return unroller;
}

Loop *ConstantFolding::isLoopHeader(BasicBlock *BB, LoopInfo &LI)
{
  if (!bbOps.partOfLoop(BB))
  {
    return NULL;
  }
  Loop *L = LI.getLoopFor(BB);
  debug(Yes) << "isLoopHeader, getting loop NULL?: " << (L == NULL) << "\n";
  if (BB != L->getHeader())
    return NULL;

  return L;
}

/*
   Run on callee Function(or main at analysis start)
   The context used for the entry basic block will be the same as the currBB
   at the point of function call.
   After completing execution of the function, the context before the function call
   will be replaced by the context at the return Instruction of the callee
   */
void ConstantFolding::runOnFunction(CallInst *ci, Function *toRun)
{
  errs() << "toRun:" << toRun->getName();
  COInfo::status();

  if (toRun->getName() == "sf_open_trcloned0")
  {
    errs() << "\n";
  }
  if (exit)
    return;
  if (!ci)
    assert(toRun->getName().str() == "main" && "callInst not given");

  stats.functionCall(toRun);

  push_back(funcValStack);

  if (ci)
  {
    debug(Yes) << "runOnFunction: propagate args and copy context to callee\n";
    propagateArgs(ci, toRun);
    copyCallerContext(ci, toRun); // copy context
  }

  Function *temp = currfn;
  BasicBlock *tempBB = currBB; // preserve across recursion of this function
  currfn = toRun;              // update to callee
  debug(Yes) << "runOnFunction: " << toRun->stripPointerCasts()->getName() << "\n";
  BasicBlock *entry = &toRun->getEntryBlock();

  push_back(worklistBB);
  addToWorklistBB(entry);

  while (worklistBB[worklistBB.size() - 1].size())
  {

    if (exit)
      return;

    LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*currfn).getLoopInfo();
    int size = worklistBB.size() - 1;
    BasicBlock *current = worklistBB[size].back();
    worklistBB[size].pop_back();
    Loop *L = NULL;

    if (L = isLoopHeader(current, *LI))
      stats.incrementTotalLoops();

    assert(current->getParent() == currfn);
    if ((L = isLoopHeader(current, *LI)) && LoopUnroller::shouldSimplifyLoop(current, *LI, module))
    {
      ValueToValueMapTy vmap;
      if (auto *unroller = unrollLoopInClone(L, vmap, funcValStack))
      {
        /*
        当展开成功后，调整当前分析函数为cloned函数，包括
        1.调整WorklistBB
        2.
         */
        addToWorklistBB(current);
        Function *cloned = dyn_cast<BasicBlock>(vmap[current])->getParent();

        stats.swapFunction(currfn, cloned);
        stats.loopStart(dyn_cast<BasicBlock>(vmap[current]));

        testStack.push_back(unroller);
        push_back(worklistBB);

        currfn = cloned;
        int oldSize = worklistBB.size() - 2;
        for (auto it = worklistBB[oldSize].begin(), end = worklistBB[oldSize].end(); it != end; it++)
        {
          addToWorklistBB(dyn_cast<BasicBlock>(vmap[*it]));
        }

        LI = unroller->LI;

        for (map<uint64_t, FileInsts *>::iterator it = fileIOCalls.begin(); it != fileIOCalls.end(); ++it)
        {
          int sizeOfInsertedSeekCalls = (it->second)->insertedSeekCalls.size();
          for (int i = 0; i < sizeOfInsertedSeekCalls; i++)
          {
            if (vmap[(it->second)->insertedSeekCalls[i]])
            {
              (it->second)->insertedSeekCalls.push_back(dyn_cast<Instruction>(vmap[(it->second)->insertedSeekCalls[i]]));
            }
          }
          int sizeOfFileIOCalls = (it->second)->insts.size();
          for (int i = 0; i < sizeOfFileIOCalls; i++)
          {
            if (vmap[(it->second)->insts[i]])
            {
              (it->second)->insts.push_back(dyn_cast<Instruction>(vmap[(it->second)->insts[i]]));
            }
          }
        }

        continue;
      }
    }

    if (runOnBB(current))
    { // loop test terminated
      LoopUnroller *unroller = pop_back(testStack);
      if (!unroller->checkPassed())
      {
        debug(Yes) << " test not terminated\n";
        BasicBlock *failedLoop;
        bbOps.cleanUpFuncBBInfo(currfn);                          // remove cloned BBinfo
        regOps.cleanUpFuncBBRegisters(currfn, popFuncValStack()); // remove cloned registers and stack
        pop_back(worklistBB);

        failedLoop = worklistBB[worklistBB.size() - 1].back();
        worklistBB[worklistBB.size() - 1].pop_back();

        stats.loopFail();
        stats.swapFunction(currfn, unroller->cloneOf);
        currfn = unroller->cloneOf;
        toRun = currfn;
        stats.incrementLoopsRerolledBack();
        LI = &getAnalysis<LoopInfoWrapperPass>(*currfn).getLoopInfo();
        LoopUnroller::deleteLoop(failedLoop);
        runOnBB(failedLoop);
      }
      else
      {
        // replace old function with new one

        stats.loopSuccess();
        Function *oldFn = unroller->cloneOf;
        addToWorklistBB(current);
        debug(Yes) << "marking test at level " << testStack.size() << " as terminated\n";

        worklistBB[worklistBB.size() - 2].clear();
        auto clonedFnWorklist = worklistBB.back();
        pop_back(worklistBB);
        for (auto it = clonedFnWorklist.begin(), end = clonedFnWorklist.end(); it != end; it++)
          addToWorklistBB(*it);

        debug(Yes) << "Unroller checkPassed returned TRUE, cleaning up oldFunction with name " << oldFn->getName() << "\n";

        regOps.cleanUpFuncBBRegisters(oldFn, funcValStack[funcValStack.size() - 2]);
        bbOps.cleanUpFuncBBInfo(oldFn);

        funcValStack[funcValStack.size() - 2].clear();
        auto clonedFnValues = funcValStack.back();
        popFuncValStack();
        for (auto *t : clonedFnValues)
          pushFuncStack(t);

        delete unroller;

        // if not main function
        if (ci)
        {

          Instruction *clonedCall = ci->clone();
          dyn_cast<CallInst>(clonedCall)->setCalledFunction(currfn);
          ReplaceInstWithInst(ci, dyn_cast<CallInst>(clonedCall));
          ci = dyn_cast<CallInst>(clonedCall);
        }
        debug(Yes) << "Renaming Function!\n";
        needToRemove.insert(ci);
        toRun = currfn;
      }
    }
  }

  debug(0) << "runOnFunction: worklist has ended...\n";
  stats.functionReturn();

  debug(0) << "runOnFunction: restore to caller...\n";
  // debug(Yes) << "currFUn:\n"<<*currfn<<"\n";

  currBB = tempBB;
  currfn = temp;
  debug(Yes) << "runOnFunction: restored from caller...\n";
  pop_back(worklistBB);
  if (!ci)
    return;

  FuncInfo *fi = fimap[toRun];
  if (!fi->context)
  {
    fi->context = bbOps.duplicateMem(currBB);
    debug(Yes) << "runOnFunction: no context returned, possible if cant return from function, or unreachable instruction hit\n";
  }
  debug(0) << "runOnFunction: Copying Context...\n";
  bbOps.copyContext(fi->context, currBB);
  debug(0) << "Cleaning up called function BBInfo...\n";
  bbOps.cleanUpFuncBBInfo(toRun);
  regOps.cleanUpFuncBBRegisters(toRun, popFuncValStack());
  if (fi->retReg)
  {
    addSingleVal(ci, fi->retReg->getValue(), true, true);
    debug(Yes) << formatv("runOnFunction: ret, addr {0},type {1}. we are in {2}\n\n\n\n", fi->retReg->getValue(), *fi->retReg->getType(), currfn->getName());
  }
  else
  {
    debug(Yes) << formatv("runOnFunction: ret, void. we are in {0}\n\n\n\n", currfn->getName());
  }
}

//=================Utils===========================
/**
 * Replaces all uses of a value with another value
 */
void ConstantFolding::replaceIfNotFD(Value *from, Value *to)
{
  if (!from || !to)
    return;

  if (isFileDescriptor(to))
  {
    ConstantInt *CI = dyn_cast<ConstantInt>(to);
    uint64_t val = CI->getZExtValue();
    pushFuncStack(from);
    regOps.addRegister(from, from->getType(), val, true); // track set to true since we only have fds for config files
    return;
  }

  from->replaceAllUsesWith(to);
  if (Register *reg = regOps.getRegister(from))
    if (reg->getTracked())
      debug(Yes) << "replaced with " << *to << "\n";
}

/**
 * Given a type, and an address to that type, recursively marks memory at that address,
 * and any addresses (pointers) in the memory of that type as non const
 */

void ConstantFolding::markMemNonConst(Type *ty, uint64_t address, BasicBlock *BB)
{
  debug(Yes) << *ty << " " << address << "\n";
  if (!ty || ty->isFunctionTy())
    return;

  if (!address)
    return;

  if (address > 1000000000000000000)
    return;

  if (fdInfoMap.find(address) != fdInfoMap.end())
    return;

  debug(Yes) << "marking mem non const in loop at address " << address << " to " << address + DL->getTypeAllocSize(ty) << "\n";
  bbOps.setConstContigous(false, address, BB);

  if (ty->isStructTy())
  {

    debug(Yes) << "is struct type"
               << "\n";
    auto structLayout = DL->getStructLayout(dyn_cast<StructType>(ty));
    for (unsigned i = 0; i < ty->getStructNumElements(); i++)
    {
      Type *t = ty->getStructElementType(i);
      PointerType *pty = dyn_cast<PointerType>(t);
      if (!pty || pty->getElementType()->isFunctionTy())
      {
        continue;
      }

      if (ty == dyn_cast<PointerType>(t)->getElementType())
        continue;

      debug(Yes) << "\nMarkMemNonConst element " << i << "\n";

      uint64_t offset = address + structLayout->getElementOffset(i);
      debug(Yes) << "offset = " << offset << "\n";
      uint64_t size = DL->getTypeAllocSize(t);
      debug(Yes) << "size = " << size << "\n";

      if (offset < address)
      { // uint64_t max exceeded
        debug(Yes) << "offset exceeds uint64_t max value; skipping markconst\n";
        continue;
      }

      uint64_t val = bbOps.loadMem(offset, size, BB);
      debug(Yes) << "load from mem = " << val << "\n";

      markMemNonConst(dyn_cast<PointerType>(t)->getElementType(), val, BB);
    }
  }
  else if (ty->isArrayTy())
  {
    debug(Yes) << "is array type "
               << "\n";
    auto *arrayTy = dyn_cast<ArrayType>(ty);
    Type *t = arrayTy->getElementType();
    unsigned offsetTotal = 0;
    if (t->isPointerTy())
    {
      debug(Yes) << "array pointer ty "
                 << "\n";
      for (unsigned i = 0; i < arrayTy->getNumElements(); i++)
      {
        uint64_t offset = address + offsetTotal;
        uint64_t ptrSize = DL->getPointerSize();
        uint64_t value = bbOps.loadMem(offset, ptrSize, BB);
        if (offset < address)
        { // uint64_t max exceeded
          debug(Yes) << "offset exceeds uint64_t max value; skipping markconst\n";
          continue;
        }
        markMemNonConst(dyn_cast<PointerType>(t)->getElementType(), value, BB);
      }
    }
  }
  else if (auto *arrayTy = dyn_cast<FixedVectorType>(ty))
  {
    debug(Yes) << "is array type "
               << "\n";
    Type *t = arrayTy->getElementType();
    unsigned offsetTotal = 0;
    if (t->isPointerTy())
    {
      debug(Yes) << "array pointer ty "
                 << "\n";
      for (unsigned i = 0; i < arrayTy->getNumElements(); i++)
      {
        uint64_t offset = address + offsetTotal;
        uint64_t ptrSize = DL->getPointerSize();
        uint64_t value = bbOps.loadMem(offset, ptrSize, BB);
        if (offset < address)
        { // uint64_t max exceeded
          debug(Yes) << "offset exceeds uint64_t max value; skipping markconst\n";
          continue;
        }
        markMemNonConst(dyn_cast<PointerType>(t)->getElementType(), value, BB);
      }
    }
  }
  else if (ty->isPointerTy())
  {
    debug(Yes) << *ty << " is of pointer type\n";
    PointerType *t = dyn_cast<PointerType>(ty);
    if (!t->getElementType()->isFunctionTy())
    {
      if (t->getElementType()->isSized())
      {
        uint64_t value = bbOps.loadMem(address, DL->getTypeAllocSize(t->getElementType()), BB);
        markMemNonConst(t->getElementType(), value, BB);
      }
    }
  }
}

void ConstantFolding::markInstMemNonConst(Instruction *I)
{
  for (unsigned i = 0; i < I->getNumOperands(); i++)
  {
    Value *val = I->getOperand(i);
    Register *reg = processInstAndGetRegister(val);
    PointerType *pty = dyn_cast<PointerType>(val->getType());

    if (pty && pty->getElementType()->isFunctionTy())
    {
      // do not mark function pointee non constant since it points to actual llvm function
      debug(Yes) << "markInstMemNonConst: skipping function\n";
      continue;
    }

    if (reg && pty && !dyn_cast<CallInst>(I))
    {
      markMemNonConst(dyn_cast<PointerType>(val->getType())->getElementType(), reg->getValue(), currBB);
    }
  }

  if (auto callInst = dyn_cast<CallInst>(I))
  {
    markArgsAsNonConst(callInst);
    if (callInst->getCalledFunction() && !callInst->getCalledFunction()->isDeclaration())
      markGlobAsNonConst(callInst->getCalledFunction());
    return;
  }
}

//=================Register related================
bool ConstantFolding::cloneRegister(Value *from, Value *with)
{
  debug(Yes) << "attempting to copy Register for " << *with << "\n";

  // if this is a constant string, allocate memory for it
  handleConstStr(with);
  uint64_t val;
  if (!getSingleVal(with, val))
  {
    debug(Yes) << "failed to create Register\n";
    return false;
  }
  pushFuncStack(from);

  // addSingleVal(with, val, true, true);
  regOps.addRegister(from, from->getType(), val, true);
  return true;
}

bool ConstantFolding::replaceOrCloneRegister(Value *from, Value *with)
{
  debug(Yes) << "attempting to copy Register for " << *with << "\n";

  // if this is a constant string, allocate memory for it
  handleConstStr(with);

  Type *ty = from->getType();
  if (isa<ConstantInt>(with))
  {
    replaceIfNotFD(from, with);
    debug(Yes) << "replaced with constantInt\n";
  }
  else if (isa<ConstantPointerNull>(with))
  {
    replaceIfNotFD(from, with);
    debug(Yes) << "replaced with NULL pointer\n";
  }
  else if (Register *reg = processInstAndGetRegister(with))
  {
    pushFuncStack(from);
    regOps.addRegister(from, ty, reg->getValue(), reg->getTracked());
    debug(Yes) << "Register from Register\n";
  }
  else
  {
    debug(Yes) << "failed to simplify\n";
    return false;
  }
  return true;
}

Register *ConstantFolding::processInstAndGetRegister(Value *ptr)
{
  if (!ptr)
    return NULL;

  if (Register *r = regOps.getRegister(ptr))
    return r;

  Instruction *I = NULL;
  Register *reg = NULL;
  if (ConstantExpr *ce = dyn_cast<ConstantExpr>(ptr))
    I = ce->getAsInstruction();
  else if (auto gl = dyn_cast<GlobalVariable>(ptr))
  {
    addGlobal(gl);
    if (Register *reg = regOps.getRegister(ptr))
      return reg;
    else
      return NULL;
  }
  else
    I = dyn_cast<Instruction>(ptr);

  if (I && !I->getParent())
  { // if it has a parent then it must have been visited
    // 目前已知函数调用时的inline bitcast、初始化global时执行Initializer
    runOnInst(I);
    if ((reg = regOps.getRegister(I)))
    {
      regOps.addRegister(ptr, reg);
    }
    I->dropAllReferences();
  }

  return reg;
}

//=================Others=======================
/**
 * Since we can't replace pointers in IR, we make internal
 * registers for pointers. Otherwise, if constant integer,
 * replace in IR. (Temporarily not replacing 64 bit integers
 * due to potentially replacing casted pointers in IR)
 */
void ConstantFolding::addSingleVal(Value *val, uint64_t num, bool replace64, bool tracked)
{
  Type *ty = val->getType();
  if (ty->isPointerTy())
  {
    if (!num)
    {
      debug(Yes) << "replacing with null\n";
      ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(ty));
      replaceIfNotFD(val, nullP);
    }
    else
    {
      debug(Yes) << "adding Register\n";
      pushFuncStack(val);
      regOps.addRegister(val, ty, num, tracked);
    }
  }
  else if (IntegerType *intTy = dyn_cast<IntegerType>(ty))
  {
    if (replace64 || !ty->isIntegerTy(64))
    {
      debug(Yes) << "replacing with constant int\n";
      replaceIfNotFD(val, ConstantInt::get(intTy, num));
    }
    else
    {
      regOps.addRegister(val, ty, num, tracked);
    }
  }
}

bool ConstantFolding::getSingleVal(Value *val, uint64_t &num)
{
  if (ConstantInt *CI = dyn_cast<ConstantInt>(val))
    num = CI->getZExtValue();
  else if (isa<ConstantPointerNull>(val))
    num = 0;
  else if (Register *reg = processInstAndGetRegister(val))
    num = reg->getValue();
  else if (Constant *CC = dyn_cast<Constant>(val))
  {
    if (Function *callback = dyn_cast<Function>(CC))
    {
      // store its address
      int size = DL->getTypeAllocSize(callback->getType());
      uint64_t addr = bbOps.allocateStack(size, currBB);
      uint64_t faddr = (uint64_t)callback;
      bbOps.storeToMem(faddr, size, addr, currBB);
      debug(Yes) << "stored callback for function " << callback->getName() << "\n";
      num = faddr;
    }
    else if (isa<ConstantVector>(CC))
    {
      assert(false && "we still can not handle vector");
      return false;
    }
  }
  else
    return false;

  return true;
}

uint64_t ConstantFolding::createConstStr(string str)
{
  uint64_t size = str.size();
  uint64_t newAddr = bbOps.allocateHeap(size, currBB);
  char *source = (char *)bbOps.getActualAddr(newAddr, currBB);
  memcpy(source, str.c_str(), size);
  debug(Yes) << "created new constant string " << str << " at address " << newAddr << "\n";
  return newAddr;
}

bool ConstantFolding::handleConstStr(Value *ptr)
{
  StringRef stringRef;
  if (getConstantStringInfo(ptr, stringRef, 0, false))
  {
    regOps.addGlobalRegister(ptr, ptr->getType(), createConstStr(stringRef.str()));
    return true;
  }
  return false;
}

void ConstantFolding::pushFuncStack(Value *val)
{
  assert(val);
  if (funcValStack.size())
    funcValStack[funcValStack.size() - 1].insert(val);
}

ValSet ConstantFolding::popFuncValStack()
{
  assert(funcValStack.size());
  return pop_back(funcValStack);
}

bool ConstantFolding::handleOverFlowInst(CallInst *callInst)
{
  string name = callInst->getCalledFunction()->getName().str();
  if (name == "llvm.sadd.with.overflow.i32")
  {
    Value *v1 = callInst->getOperand(0);
    Value *v2 = callInst->getOperand(1);
    int value1;
    int value2;
    if (ConstantInt *c1 = dyn_cast<ConstantInt>(v1))
    {
      value1 = (int)c1->getZExtValue();
    }
    else
    {
      debug(Yes) << "Failed to simplify"
                 << "\n";
      return true;
    }

    if (ConstantInt *c1 = dyn_cast<ConstantInt>(v2))
    {
      value2 = (int)c1->getZExtValue();
    }
    else
    {
      debug(Yes) << "Failed to simplify"
                 << "\n";
      return true;
    }

    int answer = value1 + value2;
    uint64_t val = ((uint64_t)answer << 32);
    debug(Yes) << "adding single value " << answer << " shifted " << val << "\n";
    regOps.addRegister(callInst, llvm::IntegerType::getInt64Ty(module->getContext()), val, true);

    return true;
  }
  return false;
}

ConstantFolding *cf;

void ConstantFolding::forcePeelLoop(uint64_t tripCount)
{
  for (Function &f : *module)
  {
    if (f.isDeclaration())
      continue;

    DominatorTree DT(f);
    bool changed;
    AssumptionCache *AC = &getAnalysis<AssumptionCacheTracker>(f, &changed).getAssumptionCache(f);
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(f, &changed).getLoopInfo();
    for (auto L : LI)
    {
      BasicBlock *hdr = L->getHeader();
      Instruction *firstInst = const_cast<Instruction *>(&*hdr->getInstList().begin());
      if (firstInst->getMetadata("context_loop") != nullptr)
      {

        ScalarEvolution SE(f, *TLI, *AC, DT, LI);
        peelLoop(L, tripCount, &LI, &SE, DT, AC, PreserveLCSSA);
      }
    }
  }
}

bool ConstantFolding::runOnModule(Module &M)
{
  cf = this;
  initDebugLevel();
  debug(Yes) << "...................................ConstantFolding Pass started.......................................................................\n";
  module = &M;
  TargetLibraryInfoImpl tlii(Triple(M.getTargetTriple()));
  TLI = new TargetLibraryInfo(tlii);
  PSI = &getAnalysis<ProfileSummaryInfoWrapperPass>().getPSI();
  DL = &M.getDataLayout();
  PreserveLCSSA = mustPreserveAnalysisID(LCSSAID);
  // forcePeelLoop(10);
  CSInfo::initCallSiteInfos();
  initFileIO();
  getReadonlyFuncNames();
  initModSet(&getAnalysis<CallGraphWrapperPass>().getCallGraph());
  initFuncInfos();

  Function *func = M.getFunction("main");
  BasicBlock *entry = &func->getEntryBlock();
  bool changed;
  LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*func, &changed).getLoopInfo();
  bbOps.initAndAddBBInfo(entry, LI);
  bbOps.createNewContext(entry, &M);
  currBB = entry;
  initGlobals();
  runOnFunction(NULL, func);

  deleteFileIOCalls();

  stats.printStats(M.getFunction("main"));
  debug(Yes) << "Functions Skipped: " << fSkipped << "\n";
  debug(Yes) << "TrackedLoads = " << trackedLoads << "\n";

  debug(Yes) << "ConstantFolding Pass completed!\n";
  debug(Yes) << "...................................ConstantFolding Pass ended.......................................................................\n";
  return true;
}

void ConstantFolding::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<TargetLibraryInfoWrapperPass>();
  AU.addRequired<CallGraphWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequiredID(LoopSimplifyID);
  AU.addRequiredID(LCSSAID);
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<TargetTransformInfoWrapperPass>();
  AU.addRequired<ProfileSummaryInfoWrapperPass>();
  AU.addRequired<BlockFrequencyInfoWrapperPass>();
}

static RegisterPass<ConstantFolding> X("inter-constprop", "Constant Folding for strings", false, false);
char ConstantFolding::ID = 0;