#ifndef GLOBALS_H_
#define GLOBALS_H_

#include "llvm/IR/Function.h"

using namespace std;
using namespace llvm;

uint64_t addGlobal(GlobalVariable *gv);
void initGlobals();
void markAllGlobsAsNonConst();
void markGlobAsNonConst(Function *F);

#endif