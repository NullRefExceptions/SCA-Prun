#ifndef SPECSTRING_H_
#define SPECSTRING_H_
#include "llvm/IR/Instructions.h"
using namespace llvm;

bool handleStringFunc(CallInst *callInst);
bool handleMemInst(CallInst *callInst);

extern const unsigned short int *traitsTable;
#endif