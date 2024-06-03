#ifndef SPECLIBC_H_
#define SPECLIBC_H_
#include "llvm/IR/Instructions.h"
using namespace llvm;

bool handleLibCCall(CallInst *callInst);

#endif