#ifndef MODSET_H_
#define MODSET_H_
#include "map"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/CallGraph.h"

using namespace llvm;
using namespace std;

struct Cycle
{
  set<Function *> nodes;
  set<GlobalVariable *> values;
};

extern map<Function *, set<GlobalVariable *>> modSet;

set<GlobalVariable *> &getFuncModset(Function *F);
void initModSet(CallGraph *CG);

struct modinfo_struct
{
  uint64_t start; // start=max,end=0表明该函数一直处于初始状态，没有写ctx
  uint64_t end;   // end=max表明该函数写ctx，但范围无法确定
};

modinfo_struct getModInfo(Function *f, uint64_t ctxIdx);
#endif