#include "Global.h"
#include "Debug.h"
#include "ConstantFolding.h"
#include "ModSet.h"

void markAllGlobsAsNonConst()
{

  for (auto &global : cf->module->globals())
  {
    if (global.isConstant())
      continue;
    auto reg = regOps.getRegister(&global);
    if (!reg)
      continue;
    debug(0) << "marking global non constant: " << global << "\n";
    bbOps.setConstMem(false, reg->getValue(), cf->DL->getTypeAllocSize(reg->getType()), cf->currBB);
  }
}

void markGlobAsNonConst(Function *F)
{
  if (!F)
    return;

  set<GlobalVariable *> &data = getFuncModset(F);
  debug(0) << "marking globals for " << F->getName() << " as non const\n";
  for (auto &gv : data)
  {
    if (gv->isConstant())
      continue;
    auto reg = cf->processInstAndGetRegister(gv);
    if (!reg)
      continue;
    debug(0) << "marking global non constant: " << *gv << "\n";
    bbOps.setConstMem(false, reg->getValue(), cf->DL->getTypeAllocSize(reg->getType()), cf->currBB);
  }
}

void initializeGlobal(uint64_t addr, Constant *CC)
{

  /* already initialize with zero */
  if (!CC)
    return;

  if (isa<ConstantPointerNull>(CC))
    return;

  if (isa<ConstantAggregateZero>(CC))
    return;

  if (auto gv = dyn_cast<GlobalVariable>(CC))
  {
    uint64_t address = addGlobal(gv);
    bbOps.storeToMem(address, cf->DL->getPointerSize(), addr, cf->currBB);
    return;
  }

  ConstantDataArray *CDA = dyn_cast<ConstantDataArray>(CC);
  debug(0) << "Global Value" << dyn_cast<GlobalValue>(CC) << "\n";
  debug(0) << "Constant expr" << dyn_cast<ConstantExpr>(CC) << "\n";
  if (CDA && CDA->isString())
  {
    char *source = (char *)bbOps.getActualAddr(addr, cf->currBB);
    string str = CDA->getAsString().str();
    int size = str.size();
    memcpy(source, str.c_str(), size);
    debug(0) << "storing : size " << size << " at address " << addr << " " << *CC << "\n";
  }
  else if (ConstantInt *CI = dyn_cast<ConstantInt>(CC))
  {
    uint64_t size = cf->DL->getTypeAllocSize(CI->getType());
    bbOps.storeToMem(CI->getZExtValue(), size, addr, cf->currBB);
    debug(0) << "storing : size " << size << " at address " << addr << " " << *CC << "\n";
  }
  else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(CC))
  {
    /* 1. either we have it in memory in which case runOnInst will work*/
    /* 2. we dont have it in memory but its a constant string - need to allocate new memory */
    /* 3. points to something which is not in memory */
    Instruction *I = dyn_cast<ConstantExpr>(CE)->getAsInstruction();
    assert(I);
    assert(I->getOperand(0));
    StringRef stringRef;
    if (cf->handleConstStr(I->getOperand(0)))
    {
      uint64_t newAddr = cf->processInstAndGetRegister(I->getOperand(0))->getValue();
      int size = cf->DL->getTypeAllocSize(CE->getType());
      bbOps.storeToMem(newAddr, size, addr, cf->currBB);
      debug(0) << "storing address " << newAddr << " at pointer " << addr << " size " << size << "\n";
    }
    else if (Register *reg = cf->processInstAndGetRegister(I))
    {
      uint64_t newAddr = reg->getValue();
      int size = cf->DL->getTypeAllocSize(CE->getType());
      bbOps.storeToMem(newAddr, size, addr, cf->currBB);
      debug(0) << "storing address " << newAddr << " at pointer " << addr << " size " << size << "\n";
    }
    I->dropAllReferences();
  }
  else if (Function *callback = dyn_cast<Function>(CC))
  {
    // store its address
    int size = cf->DL->getTypeAllocSize(callback->getType());
    uint64_t faddr = (uint64_t)callback;
    bbOps.storeToMem(faddr, size, addr, cf->currBB);
    debug(0) << "stored callback for function " << callback->getName() << "\n";
  }
  else if (ConstantStruct *cStruct = dyn_cast<ConstantStruct>(CC))
  {
    for (unsigned i = 0; i < cStruct->getNumOperands(); i++)
    {
      Constant *CGI = CC->getAggregateElement(i);
      auto layout = cf->DL->getStructLayout(cStruct->getType());
      initializeGlobal(addr + layout->getElementOffset(i), CGI);
    }
  }
  else
  {
    for (unsigned i = 0; i < CC->getNumOperands(); i++)
    {
      Constant *CGI = CC->getAggregateElement(i);
      debug(0) << "CGI: " << *CGI << "\n CC: " << *CC << "\n";
      if (!CGI)
      {
        debug(0) << "initializeGlobal: (Warning) aggregate element not found\n";
        return;
      }
      initializeGlobal(addr, CGI);
      addr += cf->DL->getTypeAllocSize(CGI->getType());
    }
  }
}

/*
  由于我们分析的时候并非从真正的main入口开始，因此我们不能保证初始时global对象的常量性
  因此需要将所有非constant global对象标记为非常量
 */
uint64_t addGlobal(GlobalVariable *gv)
{
  debug(0) << gv->getName() << "\n";

  if (Register *reg = regOps.getRegister(gv))
    return reg->getValue();

  if (gv->getName() == "stdin" || gv->getName() == "stderr" || gv->getName() == "stdout")
    return 0;

  Type *contTy = gv->getType()->getContainedType(0);

  uint64_t size = cf->DL->getTypeAllocSize(contTy);
  // uint64_t addr = bbOps.allocateStack(size, cf->currBB);
  uint64_t addr = bbOps.allocateHeap(size, cf->currBB);
  debug(0) << "add Global Variable : size " << size << " at address " << addr << "\n";
  regOps.addRegister(gv, contTy, addr, false);

  if (gv->isConstant() && gv->hasInitializer())
    initializeGlobal(addr, gv->getInitializer());
  else
    bbOps.setConstContigous(false, addr, cf->currBB);

  return addr;
}

void initGlobals()
{
  for (auto &global : cf->module->globals())
  {
    if (!regOps.getRegister(&global))
      addGlobal(&global);
  }

  for (Function &f : *cf->module)
  {
    debug(0) << "add Global function:" << f.getName()<<"\n";
    
    regOps.addRegister(&f, f.getType(), (uint64_t)&f, false);
  }
}