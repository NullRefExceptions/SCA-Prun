#ifndef SPECSYSCALL_H_
#define SPECSYSCALL_H_
#include "llvm/IR/Instructions.h"
using namespace llvm;

bool handleSysCall(CallInst *callInst);

#endif