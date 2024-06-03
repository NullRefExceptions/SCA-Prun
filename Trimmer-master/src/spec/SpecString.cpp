#include "SpecString.h"
#include "../ConstantFolding.h"
#include "../Stats.h"
#include <ctype.h>
#include "../StringUtils.h"
#include "malloc.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../Debug.h"
#include <ffi.h>
#include "../TrackInfo.h"
static cl::opt<int> stringSpecialize("stringSpecialize", cl::init(1));

const unsigned short int *traitsTable;

void handleStrTol(CallInst *call)
{
  Value *arg1 = call->getOperand(0);
  Value *arg2 = call->getOperand(1);
  Value *arg3 = call->getOperand(2);

  Register *reg1 = cf->processInstAndGetRegister(arg1),
           *reg2 = cf->processInstAndGetRegister(arg2);

  if (!reg1 || !reg2)
  {
    debug(Yes) << "strtol: one of the registers not found\n";
    return;
  }

  char *str;
  char **endptr = NULL;
  char *strStart = NULL;
  int base;
  if (!cf->getStr(reg1->getValue(), str))
  {
    debug(Yes) << "strtol: string non constant\n";
    return;
  }

  strStart = str;
  if (!dyn_cast<ConstantInt>(arg2))
  {
    char *endptrAddr = (char *)bbOps.getActualAddr(bbOps.loadMem(reg2->getValue(), cf->DL->getPointerSize(), cf->currBB), cf->currBB);
    endptr = &endptrAddr;
  }

  if (auto constant = dyn_cast<ConstantInt>(arg3))
  {
    base = constant->getZExtValue();
  }
  else
  {
    debug(Yes) << "strtol: base not constant\n";
    return;
  }

  long int answer = strtol(str, endptr, base);

  if (endptr)
  {
    debug(Yes) << "strtol: moved endptr forward by: " << *endptr - strStart << "\n";
    uint64_t newEndPtr = reg1->getValue() + (*endptr - strStart);
    bbOps.storeToMem(reg2->getValue(), cf->DL->getPointerSize(), newEndPtr, cf->currBB);
  }
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  cf->addSingleVal(call, answer, true, true);
  return;
}

void handleStrnCpy(CallInst *callInst)
{
  Value *dest = callInst->getOperand(0);
  Value *src = callInst->getOperand(1);
  ConstantInt *ci = dyn_cast<ConstantInt>(callInst->getOperand(2));

  Register *reg1 = cf->processInstAndGetRegister(dest);
  Register *reg2 = cf->processInstAndGetRegister(src);

  if (!reg1)
  {
    debug(Yes) << "strncpy: destination not found\n";
    return;
  }

  if (!reg2 || !bbOps.checkConstContigous(reg2->getValue(), cf->currBB))
  {
    debug(Yes) << "strncpy: source not found or non const\n";
    return;
  }

  if (!ci)
  {
    debug(Yes) << "strncpy: n not constant\n";
    return;
  }

  if (!dest)
  {
    debug(Yes) << "strncpy: dest register not found\n";
    return;
  }

  char *destAddr = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);
  char *srcAddr = (char *)bbOps.getActualAddr(reg2->getValue(), cf->currBB);

  strncpy(destAddr, srcAddr, ci->getZExtValue());
  stats.incrementLibCallsFolded();

  debug(Yes) << "strncpy: folded, dest string = " << destAddr << "\n";
  stats.incrementInstructionsFolded();
  return;
}

void simplifyStrFunc(CallInst *callInst)
{
  if (callInst->use_empty())
    return;
  Instruction *next = callInst;
  for (unsigned index = 0; index < callInst->arg_size(); index++)
  {
    Value *pointerArg = callInst->getArgOperand(index);
    Register *reg = cf->processInstAndGetRegister(pointerArg);

    if (!reg)
    {
      StringRef stringRef;
      if (getConstantStringInfo(pointerArg, stringRef, 0, false))
        debug(Yes) << "constant string " << stringRef << "\n";
    }
    else
    {
      uint64_t addr = reg->getValue();
      uint64_t len;
      if (getStrLen(callInst, len))
      {
        if (!bbOps.checkConstStr(addr, len, cf->currBB))
        {
          debug(Yes) << "skipping non constant string\n";
          continue;
        }
      }
      else if (!bbOps.checkConstStr(addr, cf->currBB))
        continue;
      char *baseStringData = (char *)bbOps.getActualAddr(addr, cf->currBB);

      debug(Yes) << "baseStringData : " << baseStringData << "\n";
      ConstantInt *ind0 = ConstantInt::get(IntegerType::get(cf->module->getContext(), 64), 0);
      vector<Value *> indxList;
      indxList.push_back(ind0);
      indxList.push_back(ind0);
      Constant *stringConstant = ConstantDataArray::getString(cf->module->getContext(),
                                                              StringRef(baseStringData), true);
      GlobalVariable *globalReadString = new GlobalVariable(*cf->module, stringConstant->getType(), true,
                                                            GlobalValue::ExternalLinkage, stringConstant, "");
      Type *elType = globalReadString->getType()->getContainedType(0);
      GetElementPtrInst *stringPtr = GetElementPtrInst::Create(elType, globalReadString,
                                                               indxList, Twine(""), callInst);
      callInst->setOperand(index, stringPtr);
      next = stringPtr;
    }
  }
  Function *CalledFn = callInst->getCalledFunction();
  OptimizationRemarkEmitter ORE(CalledFn);
  BlockFrequencyInfo &BFI = cf->getFuncAnalysis<BlockFrequencyInfoWrapperPass>(*cf->currfn).getBFI();
  LibCallSimplifier Simplifier(*cf->DL, cf->TLI, ORE, &BFI, cf->PSI);
  IRBuilder<> Builder(callInst->getNextNode());
  if (Value *With = Simplifier.optimizeCall(callInst, Builder))
  {
    stats.incrementInstructionsFolded();
    stats.incrementLibCallsFolded();
    cf->replaceIfNotFD(callInst, With);
  }
}

void handleStrCaseCmp(CallInst *callInst)
{

  debug(Yes) << " in str case cmp"
             << "\n";
  Value *bufPtr0 = callInst->getOperand(0);
  Value *bufPtr1 = callInst->getOperand(1);

  Register *reg0 = cf->processInstAndGetRegister(bufPtr0);
  Register *reg1 = cf->processInstAndGetRegister(bufPtr1);

  if (!reg0)
  {
    debug(Yes) << "handleStrCaseCmp: not found in map"
               << "\n";
    return;
  }

  if (!reg1)
  {
    debug(Yes) << "handleStrCaseCmp: not found in map"
               << "\n";
    return;
  }

  if (!bbOps.checkConstContigous(reg0->getValue(), cf->currBB) || !bbOps.checkConstContigous(reg1->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrCaseCmp: non constant"
               << "\n";
    return;
  }

  char *buffer0 = (char *)bbOps.getActualAddr(reg0->getValue(), cf->currBB);
  char *buffer1 = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);

  int result = strcasecmp(buffer0, buffer1);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  debug(Yes) << "result = " << result << "\n";
  debug(Yes) << "buffer0 = " << buffer0 << "\n";
  debug(Yes) << "buffer1 = " << buffer1 << "\n";
  IntegerType *int32Ty = IntegerType::get(cf->module->getContext(), 32);
  cf->replaceIfNotFD(callInst, ConstantInt::get(int32Ty, result));
}

void handleStrChr(CallInst *callInst)
{
  Value *bufPtr = callInst->getOperand(0);
  Value *flagVal = callInst->getOperand(1);
  uint64_t flag;
  Register *reg = cf->processInstAndGetRegister(bufPtr);
  if (!reg)
  {
    debug(Yes) << "handleStrChr : buffer Not found in Map\n";
    return;
  }
  if (!cf->getSingleVal(flagVal, flag))
  {
    debug(Yes) << "handleStrChr : flag not constant\n";
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    return;
  }
  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  debug(Yes) << "strchr : " << buffer << " with flag " << (char)flag << "\n";
  char *remStr = strchr(buffer, flag);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  Type *ty = callInst->getType();
  if (!remStr)
  {
    debug(Yes) << "strchr : returned NULL\n";
    ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(ty));
    cf->replaceIfNotFD(callInst, nullP);
    return;
  }
  uint64_t addr;
  for (addr = reg->getValue(); *buffer && buffer != remStr; addr++, buffer++)
    ;
  debug(Yes) << "strchr : returned idx " << (addr - reg->getValue()) << "\n";
  cf->pushFuncStack(callInst);
  regOps.addRegister(callInst, ty, addr, reg->getTracked());
}

void handleStrpbrk(CallInst *callInst)
{
  Value *bufPtr = callInst->getOperand(0);
  Value *keyPtr = callInst->getOperand(1);
  cf->handleConstStr(keyPtr);
  Register *reg1 = cf->processInstAndGetRegister(bufPtr);
  if (!reg1)
  {
    debug(Yes) << "handleStrpbrk : buffer Not found in Map\n";
    return;
  }
  Register *reg2 = cf->processInstAndGetRegister(keyPtr);
  if (!reg2)
  {
    bbOps.setConstContigous(false, reg1->getValue(), cf->currBB);
    debug(Yes) << "handleStrpbrk : key Not found in Map\n";
    return;
  }
  char *buffer = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);
  char *key = (char *)bbOps.getActualAddr(reg2->getValue(), cf->currBB);
  char *remStr = strpbrk(buffer, key);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  Type *ty = callInst->getType();
  if (!remStr)
  {
    ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(ty));
    cf->replaceIfNotFD(callInst, nullP);
    return;
  }
  uint64_t addr;
  for (addr = reg1->getValue(); *buffer && buffer != remStr; addr++, buffer++)
    ;
  cf->pushFuncStack(callInst);
  regOps.addRegister(callInst, ty, addr, reg1->getTracked() | reg2->getTracked());
}

void handleAtoi(CallInst *callInst)
{
  Value *ptr = callInst->getArgOperand(0);
  Register *reg = cf->processInstAndGetRegister(ptr);
  if (!reg)
  {
    debug(Yes) << "handleAtoi : not found in map\n";
    return;
  }
  if (!bbOps.checkConstContigous(reg->getValue(), cf->currBB))
  {
    debug(Yes) << "handleAtoi : not constant\n";
    return;
  }
  char *str = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  int result = atoi(str);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  IntegerType *int32Ty = IntegerType::get(cf->module->getContext(), 32);
  cf->replaceIfNotFD(callInst, ConstantInt::get(int32Ty, result));
}

void handleStrDup(CallInst *callInst)
{

  debug(Yes) << " in strdup"
             << "\n";
  Value *bufPtr = callInst->getOperand(0);
  Register *reg = cf->processInstAndGetRegister(bufPtr);

  if (!reg)
  {
    debug(Yes) << "handleStrDup: not found in map"
               << "\n";
    return;
  }

  if (!bbOps.checkConstContigous(reg->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrDup: non constant"
               << "\n";
    return;
  }

  uint64_t length;
  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  string calledFunc = callInst->getCalledFunction()->getName().str();
  if (calledFunc == "strndup")
  {
    ConstantInt *num = dyn_cast<ConstantInt>(callInst->getOperand(1));
    if (!num)
      return;
    length = num->getZExtValue();
  }
  else
  {
    length = strlen(buffer) + 1;
  }

  uint64_t addr = bbOps.allocateHeap(length, cf->currBB);
  char *buffer1 = (char *)bbOps.getActualAddr(addr, cf->currBB);
  if (calledFunc == "strndup")
    strncpy(buffer1, buffer, length);
  else
    strcpy(buffer1, buffer);

  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  debug(Yes) << "strdup: adding register address: " << addr << "\n";
  cf->addSingleVal(callInst, addr, true, true);
}

void handleStrTok(CallInst *callInst)
{
  debug(Yes) << " in strtok"
             << "\n";
  Value *bufPtr0 = callInst->getOperand(0);
  Value *bufPtr1 = callInst->getOperand(1);

  Register *reg0 = cf->processInstAndGetRegister(bufPtr0);
  Register *reg1 = cf->processInstAndGetRegister(bufPtr1);
  ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(bufPtr0->getType()));

  if (bufPtr0 != nullP)
  {
    if (!reg0)
    {
      debug(Yes) << "handleStrTok: argument 1 not found in map"
                 << "\n";
      return;
    }

    if (!bbOps.checkConstContigous(reg0->getValue(), cf->currBB))
    {
      debug(Yes) << "handleStrTok: non constant"
                 << "\n";
      return;
    }
  }

  if (!reg1)
  {
    debug(Yes) << "handleStrTok: argument 2 not found in map"
               << "\n";
    return;
  }

  if (!bbOps.checkConstContigous(reg1->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrTok: non constant"
               << "\n";
    return;
  }
  char *buffer1 = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);
  char *result;
  char *buffer0;

  if (bufPtr0 != nullP)
  {
    buffer0 = (char *)bbOps.getActualAddr(reg0->getValue(), cf->currBB);
    result = strtok(buffer0, buffer1);
  }

  else
  {
    result = strtok(NULL, buffer1);
  }

  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  if (!result)
  {
    cf->replaceIfNotFD(callInst, nullP);
    return;
  }

  Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(result), true);
  GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
  MaybeAlign al(1);
  gv->setAlignment(al);

  IRBuilder<> Builder(callInst);
  Value *BitCastInst = Builder.CreateBitCast(gv, PointerType::getUnqual(llvm::IntegerType::getInt8Ty(cf->module->getContext())));
  callInst->replaceAllUsesWith(BitCastInst);

  uint64_t addr1 = bbOps.allocateHeap(strlen(result) + 1, cf->currBB);
  char *buffer2 = (char *)bbOps.getActualAddr(addr1, cf->currBB);
  strcpy(buffer2, result);
  buffer2[strlen(result)] = '\0';
  debug(Yes) << "buffer2 = " << buffer2 << "\n";
  debug(Yes) << "type = " << BitCastInst->getType() << "\n";
  cf->addSingleVal(BitCastInst, addr1, true, true);
}

void handleStrCpy(CallInst *callInst)
{
  Value *dest = callInst->getOperand(0);
  Value *src = callInst->getOperand(1);

  Register *srcReg = cf->processInstAndGetRegister(src);
  Register *destReg = cf->processInstAndGetRegister(dest);
  if (!srcReg || !bbOps.checkConstContigous(srcReg->getValue(), cf->currBB))
  {
    debug(Yes) << "strcpy: source string not constant"
               << "\n";
    // mark destination as non constant too
    if (destReg)
      bbOps.setConstContigous(false, destReg->getValue(), cf->currBB);
    else
      debug(Yes) << "strcpy: (Warning) strcpy, destination unknown"
                 << "\n";

    return;
  }

  if (!destReg)
  {
    debug(Yes) << "strcpy: Destination not found\n";
    return;
  }

  uint64_t upperLimit = 50000;
  uint64_t size = 0;
  char *addr = (char *)bbOps.getActualAddr(srcReg->getValue(), cf->currBB);
  char *destAddr = (char *)bbOps.getActualAddr(destReg->getValue(), cf->currBB);
  char *temp = addr;

  while (*temp && size <= upperLimit)
  {
    size++;
    temp++;
  }

  if (size > upperLimit)
  {
    debug(Yes) << "strcpy: (Warning), src null not found untill upper limit \n";

    if (destReg)
      bbOps.setConstContigous(false, destReg->getValue(), cf->currBB);

    return;
  }

  memcpy(destAddr, addr, size + 1);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  debug(Yes) << "strcpy: Successfully folded " << size << "\n";
  return;
}

void handleStrrChr(CallInst *callInst)
{
  Value *str = callInst->getOperand(0);
  Value *chr = callInst->getOperand(1);

  char *string;
  uint64_t character;
  Register *strReg = cf->processInstAndGetRegister(str);

  if (!strReg)
  {
    debug(Yes) << "handleStrrChr: string not found\n";
    return;
  }

  if (!cf->getStr(strReg->getValue(), string))
  {
    debug(Yes) << "handleStrrChr: string not constant\n";
    return;
  }

  if (!cf->getSingleVal(chr, character))
  {
    debug(Yes) << "handleStrrChr: failed to find character\n";
    return;
  }

  char *result = strrchr(string, (int)character);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  debug(Yes) << "handleStrrChr: successfully folded \n";
  if (!result)
  {
    cf->addSingleVal(callInst, 0, false, true);
    return;
  }

  cf->addSingleVal(callInst, (uint64_t)strReg->getValue() + (result - string), false, true);
  return;
}

void handleStrCat(CallInst *callInst)
{
  debug(Yes) << " in str cat"
             << "\n";
  Value *bufPtr0 = callInst->getOperand(0);
  Value *bufPtr1 = callInst->getOperand(1);

  Register *reg0 = cf->processInstAndGetRegister(bufPtr0);
  Register *reg1 = cf->processInstAndGetRegister(bufPtr1);

  if (!reg0)
  {
    debug(Yes) << "handleStrCat: not found in map"
               << "\n";
    return;
  }

  if (!reg1)
  {
    debug(Yes) << "handleStrCat: not found in map"
               << "\n";
    return;
  }

  if (!bbOps.checkConstContigous(reg0->getValue(), cf->currBB) || !bbOps.checkConstContigous(reg1->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrCat: non constant"
               << "\n";
    return;
  }

  char *buffer0 = (char *)bbOps.getActualAddr(reg0->getValue(), cf->currBB);
  char *buffer1 = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);

  char *result = strcat(buffer0, buffer1);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  debug(Yes) << "result = " << result << "\n";
  debug(Yes) << "buffer0 = " << buffer0 << "\n";
  debug(Yes) << "buffer1 = " << buffer1 << "\n";

  uint64_t addr = bbOps.allocateHeap(strlen(buffer0) + strlen(buffer1) + 1, cf->currBB);
  char *buffer3 = (char *)bbOps.getActualAddr(addr, cf->currBB);
  strcpy(buffer3, result);
  cf->addSingleVal(callInst, addr, true, true);
}

// This function handles string function strstr that returns pointer to first occurrence of the string argument2 in string argument 1.

bool handleStrStr(CallInst *callInst)
{

  Value *val1 = callInst->getOperand(0);
  Value *val2 = callInst->getOperand(1);

  Register *reg1 = cf->processInstAndGetRegister(val1);
  Register *reg2 = cf->processInstAndGetRegister(val2);

  if (!reg1)
  {
    debug(Yes) << "handleStrStr, argument one not found in map"
               << "\n";
    return false;
  }

  if (!reg2)
  {
    debug(Yes) << "handleStrStr, argument two not found in map"
               << "\n";
    return false;
  }

  if (!bbOps.checkConstContigous(reg1->getValue(), cf->currBB) || !bbOps.checkConstContigous(reg2->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrStr, one of the arguments is non constant \n";
    return false;
  }

  char *buffer1 = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);
  char *buffer2 = (char *)bbOps.getActualAddr(reg2->getValue(), cf->currBB);
  char *result = strstr(buffer1, buffer2);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  if (!result)
  {
    cf->addSingleVal(callInst, 0, true, true);
    return false;
  }
  debug(Yes) << "result = " << result << "\n";
  debug(Yes) << "buffer1 = " << buffer1 << "\n";
  debug(Yes) << "buffer2 = " << buffer2 << "\n";

  uint64_t size = strlen(result);
  uint64_t address = bbOps.allocateHeap(size, cf->currBB);
  char *pointer = (char *)bbOps.getActualAddr(address, cf->currBB);

  strcpy(pointer, result);
  cf->addSingleVal(callInst, address, true, true);

  return true;
}

bool handleStrSep(CallInst *callInst)
{
  Value *arg1 = callInst->getOperand(0);
  Value *arg2 = callInst->getOperand(1);
  Register *reg1 = cf->processInstAndGetRegister(arg1);
  Register *reg2 = cf->processInstAndGetRegister(arg2);

  if (!reg1 || !reg2)
  {
    debug(Yes) << "strsep: one of the registers not found \n";
    return false;
  }

  char *delim;
  if (!bbOps.checkConstMem(reg1->getValue(), cf->DL->getPointerSize(), cf->currBB) || !cf->getStr(reg2->getValue(), delim))
  {
    debug(Yes) << "strsep: non constant register \n";
    return false;
  }

  uint64_t stringpAddr = bbOps.loadMem(reg1->getValue(), cf->DL->getPointerSize(), cf->currBB);
  if (!stringpAddr)
  {
    cf->addSingleVal(callInst, 0, true, true);
    debug(Yes) << "strsep returned null\n";
    return true;
  }
  debug(Yes) << "stringpAddr: " << stringpAddr << "\n";
  char *string;
  if (!cf->getStr(stringpAddr, string))
  {
    debug(Yes) << "strsep: string not constant\n";
    return false;
  }
  char **stringp = &string;
  char *stringCopy = string;
  char *result = strsep(stringp, delim);

  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  cf->addSingleVal(callInst, stringpAddr, true, true);
  if (*stringp)
    bbOps.storeToMem(stringpAddr + (stringCopy - *stringp), cf->DL->getPointerSize(), reg1->getValue(), cf->currBB);
  else
  {
    bbOps.storeToMem(0, cf->DL->getPointerSize(), reg1->getValue(), cf->currBB);
    debug(Yes) << "after storing null: " << bbOps.loadMem(reg1->getValue(), cf->DL->getPointerSize(), cf->currBB) << "\n";
    debug(Yes) << "storing null"
               << "\n";
  }
  debug(Yes) << "strsep: returned " << result << "\n";
  return true;
}

bool handleStrlen(CallInst *callInst)
{
  Value *val1 = callInst->getOperand(0);
  Register *reg1 = cf->processInstAndGetRegister(val1);

  if (!reg1)
  {
    debug(Yes) << "handleStrlen, argument one not found in map"
               << "\n";
    return false;
  }

  if (!bbOps.checkConstContigous(reg1->getValue(), cf->currBB))
  {
    debug(Yes) << "handleStrlen, the arguments is non constant \n";
    return false;
  }

  char *buffer1 = (char *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);

  size_t result = strlen(buffer1);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  cf->addSingleVal(callInst, result, true, true);
  debug(Yes) << "result = " << result << "\n";
  debug(Yes) << "buffer1 = " << buffer1 << "\n";

  return true;
}

bool handleSnprintf(CallInst *callInst)
{
  uint32_t argSize = callInst->arg_size();
  ffi_cif cif;

  void **args = (void **)malloc(argSize * sizeof(void *));
  ffi_type **arg_types = (ffi_type **)malloc(argSize * sizeof(ffi_type *));
  vector<uint64_t> intBuf(argSize);
  vector<char *> strBuf(argSize);
  bool success = true;
  size_t i = 0;

  for (; i < argSize; i++)
  {
    Value *val = callInst->getArgOperand(i);
    if (i == 0)
    {
      // dest ptr
      if (Register *reg = cf->processInstAndGetRegister(val))
      {
        char *dest = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
        strBuf[i] = dest;
        args[i] = &strBuf[i];
        arg_types[i] = &ffi_type_pointer;
        continue;
      }
      else
      {
        success = false;
        break;
      }
    }

    if (ConstantInt *CI = dyn_cast<ConstantInt>(val))
    {
      intBuf[i] = CI->getZExtValue();
      args[i] = &intBuf[i];
      arg_types[i] = &ffi_type_uint64;
    }
    else if (isa<ConstantPointerNull>(val))
    {
      strBuf[i] = nullptr;
      args[i] = &strBuf[i];
      arg_types[i] = &ffi_type_pointer;
    }
    else if (Register *reg = cf->processInstAndGetRegister(val))
    {
      char *str;
      if (cf->getStr(reg->getValue(), str))
      {
        strBuf[i] = str;
        args[i] = &strBuf[i];
        arg_types[i] = &ffi_type_pointer;
      }
      else
      {
        success = false;
        break;
      }
    }
    else
    {
      success = false;
      break;
    }
  }

  if (success)
  {
    ffi_arg res = 0;
    ffi_prep_cif_var(&cif, FFI_DEFAULT_ABI, 2, argSize, &ffi_type_sint, arg_types);
    ffi_call(&cif, FFI_FN(snprintf), &res, args);
    stats.incrementLibCallsFolded();

    debug(Yes) << "snprintf: folded\n";
    stats.incrementInstructionsFolded();
  }
  else if (i >= 1)
  { // dest and size are constant
    debug(Yes) << "snprintf:some arg is not constant\n";
    uint64_t addr = cf->processInstAndGetRegister(callInst->getArgOperand(0))->getValue();
    bbOps.setConstMem(false, addr, intBuf[1], cf->currBB);
    success = true;
  }
  else
  {
    debug(Yes) << "snprintf:all arg is not constant\n";
  }

  free(args);
  free(arg_types);
  return success;
}
/*
Handle __ctype_b_loc function in ctype.h, which returns a pointer to a 'traits' table containing
some flags related with the characteristics of each single character.
 */
void handleCTypeFuncs(CallInst *callInst)
{

  traitsTable = *(__ctype_b_loc());
  cf->pushFuncStack(callInst);
  regOps.addRegister(callInst, callInst->getType(), 999999999);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

void handleCIsSpace(CallInst *callInst)
{
  debug(Yes) << "Invoked handleCIsSpace\n";

  Value *arg = callInst->getOperand(0);

  if (auto CI = dyn_cast<ConstantInt>(arg))
  {
    int constVal = CI->getSExtValue();
    debug(Yes) << "ConstantVal: " << constVal << "\n";

    int result = 0;

    switch (constVal)
    {
    case 32:
    case 9:
    case 10:
    case 11:
    case 12:
    case 13:
      result = 1;
      break;
    default:
      result = 0;
      break;
    }
    debug(Yes) << "Post Switch: Result = " << result << "\n";
    cf->addSingleVal(callInst, (uint64_t)(result != 0), true, false);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

void handleCIsalnum(CallInst *callInst)
{
  debug(Yes) << "Invoked handleCIsalnum\n";

  Value *arg = callInst->getOperand(0);

  if (auto CI = dyn_cast<ConstantInt>(arg))
  {
    int constVal = CI->getSExtValue();
    debug(Yes) << "ConstantVal: " << constVal << "\n";

    int result = isalnum(constVal);
    debug(Yes) << "Result = " << result << "\n";
    cf->addSingleVal(callInst, (uint64_t)(result != 0), true, false);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

void handleCToLower(CallInst *callInst)
{
  debug(Yes) << "Invoked handleCToLower\n";

  Value *arg = callInst->getOperand(0);

  if (auto CI = dyn_cast<ConstantInt>(arg))
  {
    int constVal = CI->getSExtValue();
    debug(Yes) << "ConstantVal: " << constVal << "\n";

    int result = tolower(constVal);
    debug(Yes) << "Result = " << result << "\n";
    cf->addSingleVal(callInst, (uint64_t)result, true, false);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

void handleCIsDigit(CallInst *callInst)
{
  debug(Yes) << "Invoked handleCIsDigit\n";

  Value *arg = callInst->getOperand(0);

  if (auto CI = dyn_cast<ConstantInt>(arg))
  {
    int constVal = CI->getSExtValue();
    debug(Yes) << "ConstantVal: " << constVal << "\n";

    int result = isdigit(constVal);
    debug(Yes) << "Result = " << result << " in bool: " << (result != 0) << "\n";
    cf->addSingleVal(callInst, (uint64_t)(result != 0), true, true);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

bool handleStringFunc(CallInst *callInst)
{

  stats.incrementTotalLibCalls();
  if (!stringSpecialize)
    return false;
  string name = callInst->getCalledFunction()->getName().str();

  if (name == "strtol")
    handleStrTol(callInst);
  else if (name == "strncpy")
    handleStrnCpy(callInst);
  else if (name == "strlen")
    handleStrlen(callInst);
  else if (name == "snprintf")
    return handleSnprintf(callInst);
  else if (simpleStrFunc(name))
    simplifyStrFunc(callInst);
  else if (name == "strcasecmp")
    handleStrCaseCmp(callInst);
  else if (name == "strchr")
    handleStrChr(callInst);
  else if (name == "strpbrk")
    handleStrpbrk(callInst);
  else if (name == "atoi")
    handleAtoi(callInst);
  else if (name == "strdup" || name == "__strdup" || name == "xstrdup" || name == "strndup")
    handleStrDup(callInst);
  else if (name == "strtok")
    handleStrTok(callInst);
  else if (name == "strcpy")
    handleStrCpy(callInst);
  else if (name == "strrchr")
    handleStrrChr(callInst);
  else if (name == "strcat")
    handleStrCat(callInst);
  else if (name == "strstr")
    handleStrStr(callInst);
  else if (name == "strsep")
    handleStrSep(callInst);
  //else if (name == "__ctype_b_loc")
  //  handleCTypeFuncs(callInst);
  else if (name == "c_isspace")
    handleCIsSpace(callInst);
  else if (name == "c_isalnum")
    handleCIsalnum(callInst);
  else if (name == "c_tolower")
    handleCToLower(callInst);
  else if (name == "c_isdigit")
    handleCIsDigit(callInst);
  else
    return false;

  return true;
}

bool handleMallocUsableSize(CallInst *callInst)
{
  return false;
  Value *val = callInst->getOperand(0);

  Register *reg = cf->processInstAndGetRegister(val);

  if (!reg)
  {
    debug(Yes) << "malloc_usable_size, failed to find register \n";
    return false;
  }

  uint64_t address = reg->getValue();
  void *pointer = bbOps.getActualAddr(address, cf->currBB);
  debug(Yes) << "malloc_usable_size: address " << pointer << "\n";
  size_t size = malloc_usable_size(pointer);
  debug(Yes) << "malloc_usable_size: result " << size << "\n";
  cf->addSingleVal(callInst, size, true, true);
  stats.incrementInstructionsFolded();
  return true;
}

ProcResult handleMemMoveInst(CallInst *memMoveInst)
{

  Value *toPtr = memMoveInst->getOperand(0);
  Value *fromPtr = memMoveInst->getOperand(1);
  char *fromString;
  Value *sizeVal = memMoveInst->getOperand(2);
  uint64_t size;
  Register *reg = cf->processInstAndGetRegister(toPtr);
  if (!reg)
  {
    debug(Yes) << "handleMemMoveInst : Not found in Map\n";
    return NOTFOLDED;
  }

  if (!cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "handleMemMoveInst : size not constant\n";
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    return NOTFOLDED;
  }

  if (!cf->getStr(fromPtr, fromString, size))
  {
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    return NOTFOLDED;
  }
  char *toString = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  // need to duplicate first since move
  char *dup = strdup(toString);
  debug(Yes) << "memmove : from " << fromString << "\n";
  memcpy(toString, dup, size);
  bbOps.setConstMem(true, reg->getValue(), size, cf->currBB);
  free(dup);
  stats.incrementInstructionsFolded();
  return NOTFOLDED;
}

// Handle memcpy instructions: copy the string address to the destination address so that it can be used in further instructions.
ProcResult handleMemcpyInst(CallInst *memcpyInst)
{

  Value *toPtr = memcpyInst->getOperand(0);
  Value *fromPtr = memcpyInst->getOperand(1);
  char *fromString;
  Value *sizeVal = memcpyInst->getOperand(2);
  uint64_t size;
  Register *reg = cf->processInstAndGetRegister(toPtr);

  if (!reg)
  {
    debug(Yes) << "handleMemcpyInst : Not found in Map\n";
    return NOTFOLDED;
  }

  if (!cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "handleMemcpyInst : size not constant\n";
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    return NOTFOLDED;
  }

  if (!cf->getStr(fromPtr, fromString, size))
  {
    bbOps.setConstMem(false, reg->getValue(), size, cf->currBB);
    return NOTFOLDED;
  }
  char *toString = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  debug(Yes) << "memcpy : from " << fromString << "\n";
  memcpy(toString, fromString, size);
  bbOps.setConstMem(true, reg->getValue(), size, cf->currBB);
  stats.incrementInstructionsFolded();
  return NOTFOLDED;
}

ProcResult handleMemSetInst(CallInst *memsetInst)
{
  Value *ptr = memsetInst->getOperand(0);
  Value *chrctr = memsetInst->getOperand(1);
  Value *sizeVal = memsetInst->getOperand(2);

  Register *ptrReg = cf->processInstAndGetRegister(ptr);
  if (!ptrReg)
  {
    debug(Yes) << "handleMemSetInst : Not found in Map\n";
    return NOTFOLDED;
  }

  uint64_t c;
  if (!cf->getSingleVal(chrctr, c))
  {
    debug(Yes) << "handleMemSetInst : character not found in Map\n";
    return NOTFOLDED;
  }

  uint64_t size;
  if (!cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "handleMemSetInst : size not found in Map\n";
    return NOTFOLDED;
  }

  char *ptrString = (char *)bbOps.getActualAddr(ptrReg->getValue(), cf->currBB);
  memset(ptrString, c, size);
  debug(Yes) << "set string to " << c << " size " << size << "\n";

  stats.incrementInstructionsFolded();
  return NOTFOLDED;
}

bool handleMemInst(CallInst *callInst)
{
  Function *callee = callInst->getCalledFunction();
  if (callee->isIntrinsic())
  {
    switch (callee->getIntrinsicID())
    {
    case Intrinsic::memcpy:
      handleMemcpyInst(callInst);
      break;
    case Intrinsic::memmove:
      handleMemMoveInst(callInst);
      break;
    case Intrinsic::memset:
      handleMemSetInst(callInst);
      break;
    default:
      return false;
    }
  }
  else
  {
    string name = callee->getName().str();
    if (name == "memset" || name == "__memset_chk")
      handleMemSetInst(callInst);
    else if (name == "memcpy")
      handleMemcpyInst(callInst);
    else if (name == "malloc_usable_size")
      handleMallocUsableSize(callInst);
    else
      return false;
  }
  return true;
}