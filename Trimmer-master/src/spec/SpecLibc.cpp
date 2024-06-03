#include "SpecLibc.h"
#include "../ConstantFolding.h"
#include "../Stats.h"
#include "../Debug.h"
bool handleCTypeBLoc(CallInst *callInst)
{
  stats.incrementTotalLibCalls();
  const unsigned short **ptr = __ctype_b_loc();
  uint64_t addrPtr = bbOps.allocateStack(cf->DL->getPointerSize(), cf->currBB);

  const unsigned short *arr = *ptr;
  uint64_t localArr = bbOps.allocateStack(sizeof(unsigned short) * (255 + 1 + 128), cf->currBB);
  unsigned short *localArrReal = ((unsigned short *)bbOps.getActualAddr(localArr, cf->currBB)) + 128; // move to 0
  // can just use a memcpy, but this is more explanatory
  for (int i = -128; i <= 255; i++)
  {
    localArrReal[i] = arr[i];
  }

  *((unsigned short **)bbOps.getActualAddr(addrPtr, cf->currBB)) = ((unsigned short *)localArr + 128);
  cf->addSingleVal(callInst, addrPtr, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleCTypeBLocLower(CallInst *callInst)
{
  stats.incrementTotalLibCalls();
  const int **ptr = __ctype_tolower_loc();
  uint64_t addrPtr = bbOps.allocateStack(cf->DL->getPointerSize(), cf->currBB);

  const int *arr = *ptr;
  uint64_t localArr = bbOps.allocateStack(sizeof(int) * (255 + 1 + 128), cf->currBB);
  int *localArrReal = ((int *)bbOps.getActualAddr(localArr, cf->currBB)) + 128; // move to 0
  // can just use a memcpy, but this is more explanatory
  for (int i = -128; i <= 255; i++)
  {
    localArrReal[i] = arr[i];
  }

  *((int **)bbOps.getActualAddr(addrPtr, cf->currBB)) = ((int *)localArr + 128);
  cf->addSingleVal(callInst, addrPtr, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleToLower(CallInst *callInst)
{
  stats.incrementTotalLibCalls();
  debug(Yes) << "Entering tolower \n";
  Value *arg = callInst->getOperand(0);
  int argValue;
  if (auto *cint = dyn_cast<ConstantInt>(arg))
  {
    argValue = (int)cint->getZExtValue();
  }
  else if (Register *reg = cf->processInstAndGetRegister(arg))
  {
    argValue = reg->getValue();
  }
  else
  {
    debug(Yes) << "tolower: register not found"
               << "\n";
    return false;
  }

  int answer = tolower(argValue);
  debug(Yes) << "tolower returned " << answer << "\n";
  cf->addSingleVal(callInst, answer, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleBasename(CallInst *ci)
{
  stats.incrementTotalLibCalls();
  Value *val1 = ci->getOperand(0);
  Register *reg1 = cf->processInstAndGetRegister(val1);
  char *path;

  if (!reg1 || !cf->getStr(reg1->getValue(), path))
  {
    debug(Yes) << "handleBasename: path not constant or register not found\n";
    return false;
  }

  char *result = basename(path);

  uint64_t virtAddr = bbOps.allocateHeap(strlen(result) + 1, cf->currBB);
  char *actualAddr = (char *)bbOps.getActualAddr(virtAddr, cf->currBB);
  strcpy(actualAddr, result);
  cf->addSingleVal(ci, virtAddr, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleCBM(CallInst *callInst)
{

  stats.incrementTotalLibCalls();
  debug(Yes) << "COMMAND_BY_NAME INVOKED\n";

  Value *op1 = callInst->getOperand(0);

  Register *reg = cf->processInstAndGetRegister(op1);

  if (!reg)
  {
    debug(Yes) << "CBM: register not found\n";
    return false;
  }

  char *buf = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  debug(Yes) << "CBM String: " << buf << "\n";
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  return false;
}

bool handleSetjmp(CallInst *callInst)
{
  cf->addSingleVal(callInst,0);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleLongjmp(CallInst *callInst)
{
  debug(Yes) << "Long jmp encounter!\n";
  return false;
}

bool handleLibCCall(CallInst *callInst)
{
  Function *F;
  if (!(F = callInst->getCalledFunction()))
    return false;

  if (F->getName().str() == "__ctype_b_loc")
    return handleCTypeBLoc(callInst);
  if (F->getName().str() == "__ctype_tolower_loc")
    return handleCTypeBLocLower(callInst);
  if (F->getName().str() == "tolower")
    return handleToLower(callInst);
  if (F->getName().str() == "__xpg_basename")
    return handleBasename(callInst);
  if (F->getName().str() == "command_by_name")
    return handleCBM(callInst);
  if (F->getName().str() == "_setjmp")
    return handleSetjmp(callInst);
  if (F->getName().str() == "longjmp")
    return handleLongjmp(callInst);
  return false;
}