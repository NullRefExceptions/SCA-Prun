#include "SpecHeap.h"
#include "../ConstantFolding.h"
#include "../Stats.h"
#include "../TrackInfo.h"
#include "../Debug.h"
// Process Malloc Instructions: Allocate heap memory
ProcResult processMallocInst(CallInst *mi)
{

  stats.incrementTotalLibCalls();

  Value *sizeVal = mi->getOperand(0);
  uint64_t size;
  if (!cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "mallocInst : size not constant\n";
    return NOTFOLDED;
  }
  uint64_t addr = bbOps.allocateHeap(size, cf->currBB);
  cf->pushFuncStack(mi);
  regOps.addRegister(mi, mi->getType(), addr, false);
  debug(Yes) << "mallocInst : size " << size << " at address " << addr << "\n";
  uint64_t ctxIdx;
  if (CSInfo::getContextObjIdx(mi, ctxIdx))
  {
    COInfo::addContextOBJ(ctxIdx, addr, size);
  }
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

ProcResult processMallocInst2(CallInst *mi)
{

  stats.incrementTotalLibCalls();

  Value *sizeVal = mi->getOperand(1);
  uint64_t size;
  if (!cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "mallocInst : size not constant\n";
    return NOTFOLDED;
  }
  uint64_t addr = bbOps.allocateHeap(size, cf->currBB);

  cf->pushFuncStack(mi);
  regOps.addRegister(mi, mi->getType(), addr, false);
  errs() << "mallocInst : size " << size << " at address " << addr << "\n";
  uint64_t ctxIdx;
  if (CSInfo::getContextObjIdx(mi, ctxIdx))
  {
    COInfo::addContextOBJ(ctxIdx, addr, size);
  }
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

ProcResult processFree(CallInst *mi)
{
  stats.incrementTotalLibCalls();
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

ProcResult processCallocInst(CallInst *ci)
{

  stats.incrementTotalLibCalls();
  Value *numVal = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  uint64_t num, bsize;

  if (!cf->getSingleVal(numVal, num))
  {
    debug(Yes) << "callocInst : num not constant\n";
    return NOTFOLDED;
  }
  if (!cf->getSingleVal(sizeVal, bsize))
  {
    debug(Yes) << "callocInst : size not constant\n";
    return NOTFOLDED;
  }
  unsigned size = num * bsize;
  uint64_t addr = bbOps.allocateHeap(size, cf->currBB);
  uint64_t ctxIdx;
  if (CSInfo::getContextObjIdx(ci, ctxIdx))
  {
    COInfo::addContextOBJ(ctxIdx, addr, size);
  }
  cf->pushFuncStack(ci);
  regOps.addRegister(ci, ci->getType(), addr, false);
  debug(Yes) << "callocInst : size " << size << " at address " << addr << "\n";
  memset((char *)bbOps.getActualAddr(addr, cf->currBB), '\0', size);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return UNDECIDED;
}

ProcResult processReallocInst(CallInst *ci)
{
  if (!ci)
  {
    debug(Yes) << "processReallocInst ci is null!\n";
  }
  stats.incrementTotalLibCalls();
  Value *ptr = ci->getOperand(0);
  ConstantInt *size = dyn_cast<ConstantInt>(ci->getOperand(1));
  Register *reg = cf->processInstAndGetRegister(ptr);

  if (!reg || !ptr || !size)
  {
    debug(Yes) << "realloc: register not found or size not constant\n";
    return NOTFOLDED;
  }

  uint64_t addr = bbOps.allocateHeap(size->getZExtValue(), cf->currBB);
  char *oldAddr = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  uint64_t size_old = bbOps.getSizeContigous(reg->getValue(), cf->currBB);
  debug(Yes) << "realloc: copying over memory size: " << size_old << "\n";
  memcpy((void *)bbOps.getActualAddr(addr, cf->currBB), (void *)oldAddr, size_old);
  cf->addSingleVal(ci, addr, false, true);
  debug(Yes) << "realloc processed successfully\n";
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return FOLDED;
}

bool handleHeapAlloc(CallInst *callInst)
{
  string name = callInst->getCalledFunction()->getName().str();
  if (name == "malloc" || name == "xmalloc" || name == "CRYPTO_zalloc" || name == "_TIFFmalloc")
    processMallocInst(callInst);
  else if (name == "calloc" || name == "xcalloc")
    processCallocInst(callInst);
  else if (name == "realloc" || name == "xrealloc")
    processReallocInst(callInst);
  else if (callInst->getCalledFunction()->getName().startswith("png_malloc"))
    processMallocInst2(callInst);
  else if (callInst->getCalledFunction()->getName() == "png_free" || callInst->getCalledFunction()->getName() == "png_free_default")
    processFree(callInst);
  else
    return false;
  return true;
}