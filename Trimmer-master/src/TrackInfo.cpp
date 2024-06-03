#include "TrackInfo.h"
#include "ConstantFolding.h"
#include "llvm/Support/FormatVariadic.h"
#include "spec/SpecFileIO.h"

map<MDNode *, BitVector *> originBV;
map<uint64_t, ctx_struct> ctxMap;

void CSInfo::initCallSiteInfos()
{
  for (auto &func : *cf->module)
    initFuncCallSiteInfo(func);
}

void CSInfo::initFuncCallSiteInfo(Function &func)
{
  for (auto &bb : func)
    for (auto &inst : bb)
      if (auto callins = dyn_cast<CallInst>(&inst))
      {
        BitVector *bv = new BitVector(callins->arg_size());
        getConstantBV(callins, bv);
        originBV[callins->getMetadata("csm")] = bv;
      }
}

void CSInfo::getConstantBV(CallInst *callins, BitVector *bv)
{
  int idx = 0;
  for (auto &arg : callins->args())
  {
    if (isa<Constant>(arg.get()))
      bv->set(idx);
    else if (arg.get()->getType()->isIntegerTy())
    {
      Register *reg = cf->processInstAndGetRegister(arg.get());
      if (reg && fdInfoMap.find(reg->getValue()) != fdInfoMap.end())
        bv->set(idx);
      else
        bv->reset(idx);
    }
    else
      bv->reset(idx);
    idx++;
  }
}

csm_struct CSInfo::getCSM(CallInst *callinst, uint64_t ctxIdx)
{
  csm_struct res = {ctxIdx, false, false, false};
  MDNode *MDctx = dyn_cast<MDNode>(callinst->getMetadata("csm")->getOperand(ctxIdx));
  ConstantInt *isRead = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(MDctx->getOperand(1))->getValue());
  ConstantInt *isWrite = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(MDctx->getOperand(2))->getValue());
  ConstantInt *isMalloc = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(MDctx->getOperand(3))->getValue());
  if (isRead->getZExtValue())
    res.isRead = true;
  if (isWrite->getZExtValue())
    res.isWrite = true;
  if (isMalloc->getZExtValue())
    res.isMalloc = true;
  return res;
}

uint64_t CSInfo::getNumCSM(CallInst *callinst)
{
  MDNode *MDCSM = callinst->getMetadata("csm");
  if (MDCSM == nullptr)
    return 0;
  else
    return MDCSM->getNumOperands();
}

bool CSInfo::isContextObjRWM(CallInst *callinst)
{
  for (size_t i = 0; i < getNumCSM(callinst); i++)
  {
    if (isContextObjRWM(callinst, i))
      return true;
  }
  return false;
}

bool CSInfo::isContextObjRWM(CallInst *callinst, uint64_t ctxIdx)
{
  csm_struct csm = getCSM(callinst, ctxIdx);
  return csm.isRead || csm.isWrite || csm.isMalloc;
}

bool CSInfo::getContextObjIdx(CallInst *callinst, uint64_t &ctxIdx)
{
  MDNode *mdn = callinst->getMetadata("context");
  if (mdn == nullptr)
    return false;
  ConstantInt *ctxI = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(mdn->getOperand(0))->getValue());
  ctxIdx = ctxI->getZExtValue();
  return true;
}

void *getTM(uint64_t fakeAddr)
{
  assert(!bbOps.BBContextMap[cf->currBB]->deleted);
  return bbOps.BBContextMap[cf->currBB]->memory->getActualAddr(fakeAddr);
}

void *getCM(uint64_t fakeAddr)
{
  assert(!bbOps.BBContextMap[cf->currBB]->deleted);
  bool *constMem = bbOps.BBContextMap[cf->currBB]->memory->stackOrHeapConst(fakeAddr);
  return &constMem[fakeAddr];
}

void *getTM(uint64_t fakeAddr, Memory *mem)
{
  return mem->getActualAddr(fakeAddr);
}

void *getCM(uint64_t fakeAddr, Memory *mem)
{
  bool *constMem = mem->stackOrHeapConst(fakeAddr);
  return &constMem[fakeAddr];
}

void COInfo::addContextOBJ(uint64_t ctxId, uint64_t faddr, uint64_t size)
{
  if (ctxMap.find(ctxId) != ctxMap.end())
  {
    debug(Yes) << formatv("error: context obj {0} redefined!\n", ctxId);
  }
  debug(Yes) << formatv("[Context]: defined new Context Obj, id:{0},addr:{1},size:{2}\n", ctxId, faddr, size);
  ctxMap[ctxId] = {ctxId, faddr, size};
}

uint64_t COInfo::remainConstantNum(uint64_t ctxId)
{
  if (ctxMap.find(ctxId) == ctxMap.end())
    return 0;
  ctx_struct ctx = ctxMap[ctxId];
  bool *buf = (bool *)getCM(ctx.faddr);
  uint64_t constantNum = 0;
  for (size_t i = 0; i < ctx.size; i++)
  {
    if (buf[i])
      constantNum++;
  }
  return constantNum;
}

bool COInfo::remainConstant(uint64_t ctxId)
{
  // 我们将还未遇到的情况视为常量状态，这包括常量上下文对象（永远不会遇到），以及还未malloc的普通上下文对象
  if (ctxMap.find(ctxId) == ctxMap.end())
    return true;

  ctx_struct ctx = ctxMap[ctxId];
  bool *buf = (bool *)getCM(ctx.faddr);
  bool allFalse = true;
  for (size_t i = 0; i < ctx.size; i++)
  {
    if (buf[i])
    {
      allFalse = false;
      return true;
    }
  }
  return false;
}

bool COInfo::remainConstant(uint64_t ctxId, uint64_t offset)
{
  // 我们将还未遇到的情况视为常量状态，这包括常量上下文对象（永远不会遇到），以及还未malloc的普通上下文对象
  if (ctxMap.find(ctxId) == ctxMap.end())
    return true;

  ctx_struct ctx = ctxMap[ctxId];
  bool *buf = (bool *)getCM(ctx.faddr);
  return buf[offset];
}

bool COInfo::getContextObjIdx(uint64_t faddr, uint64_t &ctxIdx)
{
  for (auto item : ctxMap)
  {
    if (faddr >= item.second.faddr && faddr < item.second.faddr + item.second.size)
    {
      ctxIdx = item.second.ctxId;
      return true;
    }
  }
  return false;
}

void COInfo::status()
{
  errs() << "\tCTXOBJ:";//debug(Yes)
  for (auto item : ctxMap)
  {
    errs() << formatv(" ctx_{0} conNum_{1}", item.first, remainConstantNum(item.first));
  }
  errs() << "\n";
}
