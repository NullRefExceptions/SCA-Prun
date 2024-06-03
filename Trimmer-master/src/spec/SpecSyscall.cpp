#include "SpecSyscall.h"
#include <unistd.h>
#include <pwd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <algorithm>

#include "../ConstantFolding.h"
#include "SpecFileIO.h"
#include "../Stats.h"
#include "../Debug.h"
bool handleGetUid(CallInst *callInst)
{
  uid_t userId = getuid();
  cf->addSingleVal(callInst, (uint64_t)userId, true, true);
  stats.incrementTotalLibCalls();
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleGetGid(CallInst *callInst)
{
  gid_t groupId = getgid();
  cf->addSingleVal(callInst, (uint64_t)groupId, true, true);
  stats.incrementTotalLibCalls();
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool copyMemory(char *address, Type *ty, char *localAddress)
{
  debug(Yes) << "Copying over memory"
             << "\n";
  StructType *st = dyn_cast<StructType>(ty);
  debug(Yes) << st << "\n";
  auto structLayout = cf->DL->getStructLayout(st);
  for (unsigned i = 0; i < st->getStructNumElements(); i++)
  {
    PointerType *t = dyn_cast<PointerType>(st->getStructElementType(i));

    if (!t)
    {
      continue;
    }

    uint64_t offset = structLayout->getElementOffset(i);
    if (t->getElementType()->isPointerTy())
    {
      debug(Yes) << "Warning case not handled\n";
    }
    else
    {
      // assumption that this is char *

      // allocate memory
      char *pointer = *(char **)(address + offset);
      uint64_t allocationSize = strlen(pointer) + 1;
      uint64_t val = bbOps.allocateStack(allocationSize, cf->currBB);

      // copy over data
      char *actualAddr = (char *)bbOps.getActualAddr(val, cf->currBB);
      debug(Yes) << "Copying : " << string(pointer) << " at address: " << val << " real destination address: " << actualAddr << "\n";
      strcpy(actualAddr, pointer);
      debug(Yes) << "Copied : " << actualAddr << "\n";

      // store pointer
      uint64_t size = cf->DL->getTypeAllocSize(t);
      debug(Yes) << "Storing pointer at address: " << (uint64_t)localAddress + offset << "\n";
      bbOps.storeToMem(val, size, (uint64_t)localAddress + offset, cf->currBB);
    }
  }
  return true;
}

bool handleGetPwUid(CallInst *callInst)
{
  stats.incrementTotalLibCalls();
  Value *uidVal = callInst->getOperand(0);
  uint64_t uid;

  if (!cf->getSingleVal(uidVal, uid))
    return false;

  struct passwd *pwuid = getpwuid(uid);

  if (!pwuid)
    return false;

  PointerType *pointerTy = dyn_cast<PointerType>(callInst->getType());
  if (!pointerTy)
    return false;

  Type *ty = pointerTy->getElementType();

  unsigned size = cf->DL->getTypeAllocSize(ty);
  uint64_t addr = bbOps.allocateStack(size, cf->currBB);

  struct passwd *memPwUid = (struct passwd *)bbOps.getActualAddr(addr, cf->currBB);

  memcpy(memPwUid, pwuid, size);
  copyMemory((char *)pwuid, dyn_cast<PointerType>(callInst->getType())->getElementType(), (char *)addr);
  cf->addSingleVal(callInst, (uint64_t)addr, false, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  cf->pushFuncStack(callInst);
  return true;
}

bool handleStat(CallInst *ci)
{
  Value *path = ci->getOperand(0);
  Value *statBuf = ci->getOperand(1);
  Register *pathReg = cf->processInstAndGetRegister(path);
  Register *statBufRegister = cf->processInstAndGetRegister(statBuf);

  stats.incrementTotalLibCalls();

  if (!pathReg || !statBufRegister)
  {
    debug(Yes) << "stat: one of the registers not found\n";
    return false;
  }

  debug(Yes) << "calling stat on " << (char *)bbOps.getActualAddr(pathReg->getValue(), cf->currBB) << " virtual addr = " << pathReg->getValue() << " statbuf addr = " << statBufRegister->getValue() << "\n";
  string name = string((char *)bbOps.getActualAddr(pathReg->getValue(), cf->currBB));
  if (std::find(std::begin(configFileNames), std::end(configFileNames), name) == std::end(configFileNames))
  {
    debug(Yes) << "stat: marking arguments non constant returning\n";
    cf->markArgsAsNonConst(ci);
    debug(Yes) << "stat: on non config file. returning\n";
    return false;
  }

  int result = stat((char *)bbOps.getActualAddr(pathReg->getValue(), cf->currBB), (struct stat *)bbOps.getActualAddr(statBufRegister->getValue(), cf->currBB));

  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();

  debug(Yes) << "stat returned " << result << "\n";
  cf->addSingleVal(ci, result, true, true);
  return FOLDED;
}

bool handleFStat(CallInst *callInst)
{
  stats.incrementTotalLibCalls();

  Value *f = callInst->getOperand(0);
  Value *Stats = callInst->getOperand(1);
  uint64_t fileno;

  if (!cf->getSingleVal(f, fileno))
  {
    debug(Yes) << "file number is not constant\n";
    return false;
  }
  Register *statReg = cf->processInstAndGetRegister(Stats);
  if (!statReg)
  {
    debug(Yes) << "stat struct not found\n";
    return false;
  }

  struct stat st;
  int ofd = -1;
  int result;
  if (getfdi(fileno, ofd))
    result = fstat(ofd, &st);
  else
    result = fstat(fileno, &st);

  if (result != 0)
  {
    debug(Yes) << "fstat returns error\n";
    return false;
  }
  uint64_t addr = statReg->getValue();
  struct stat *temp = (struct stat *)bbOps.getActualAddr(addr, cf->currBB);
  memcpy(temp, &st, sizeof(struct stat));
  cf->addSingleVal(callInst, result, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

// handle the fileno function of libc. This function is used to return file descriptors for a specific file stream.
bool handleFileNo(CallInst *callInst)
{
  stats.incrementTotalLibCalls();

  Value *f = callInst->getOperand(0);

  uint64_t sfd;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(f, sfd) && getfptr(sfd, fptr);

  if (!fdConst)
  {
    debug(Yes) << "file pointer is not constant\n";
    return false;
  }

  int result = fileno(fptr);

  if (result == -1)
  {
    debug(Yes) << "fileno returns error\n";
    return false;
  }
  cf->addSingleVal(callInst, result, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

bool handleGetEnv(CallInst *ci)
{
  Value *arg1 = ci->getOperand(0);
  stats.incrementTotalLibCalls();

  Register *reg = cf->processInstAndGetRegister(arg1);
  if (!reg)
  {
    debug(Yes) << "handleGetEnv: Register not found\n";
    return false;
  }

  char *str;
  if (!cf->getStr(reg->getValue(), str))
  {
    debug(Yes) << "handleGetEnv: string not constant\n";
    return false;
  }

  char *result = getenv(str);

  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  if (!result)
  {
    debug(Yes) << "handleGetEnv: returned null\n";
    cf->addSingleVal(ci, 0, true, true);
    return true;
  }

  uint64_t addr = bbOps.allocateStack(strlen(result) + 1, cf->currBB);
  char *actualAddr = (char *)bbOps.getActualAddr(addr, cf->currBB);
  strcpy(actualAddr, result);
  cf->addSingleVal(ci, addr, true, true);
  debug(Yes) << "handleGetEnv: returned " << result << "\n";
  return true;
}

bool handleGetCwd(CallInst *callInst)
{
  stats.incrementTotalLibCalls();
  Value *val = callInst->getOperand(0);
  Value *val2 = callInst->getOperand(1);
  Register *reg = cf->processInstAndGetRegister(val);

  if (!reg || !dyn_cast<ConstantInt>(val2))
  {
    debug(Yes) << "getcwd: register not found or size not constant\n";
    return false;
  }

  size_t size = cast<ConstantInt>(val2)->getZExtValue();
  char *buf = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  char *result = getcwd(buf, size);

  if (!buf)
  {
    debug(Yes) << "getcwd: returned null\n";
    cf->addSingleVal(callInst, 0, true, true);
    return true;
  }

  debug(Yes) << "cwd = " << *buf << "\n";
  cf->addSingleVal(callInst, reg->getValue(), true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  return true;
}

// This function handles numerous system calls. This is used to get results from OS system calls for precise debloating.
bool handleSysCall(CallInst *callInst)
{
  Function *F;
  if (!(F = callInst->getCalledFunction()))
    return false;

  if (F->getName().str() == "getuid")
    return handleGetUid(callInst);
  else if (F->getName().str() == "getgid")
    return handleGetGid(callInst);
  else if (F->getName().str() == "getpwuid")
    return handleGetPwUid(callInst);
  else if (F->getName().str() == "stat" || F->getName().str() == "stat64")
    return handleStat(callInst);
  else if (F->getName().str() == "fstat")
    return handleFStat(callInst);
  else if (F->getName().str() == "fileno")
    return handleFileNo(callInst);
  else if (F->getName().str() == "getenv")
    return handleGetEnv(callInst);
  else if (F->getName().str() == "getcwd")
    return handleGetCwd(callInst);
  return false;
}