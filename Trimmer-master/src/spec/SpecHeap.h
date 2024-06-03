#ifndef SPECHEAP_H_
#define SPECHEAP_H_
#include "llvm/IR/Instructions.h"
using namespace llvm;

bool handleHeapAlloc(CallInst *callInst);

#endif