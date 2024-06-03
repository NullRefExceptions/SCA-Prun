#include "FuncInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

map<Function *, FuncInfo *> fimap;

FuncInfo::FuncInfo(Function *F)
{
  addrTaken = F->hasAddressTaken();
  func = F;
  for (Use &U : F->uses())
  {
    User *FU = U.getUser();
    if (CallInst *ci = dyn_cast<CallInst>(FU))
    {
      if (!ci->getParent())
        continue;
      directCallInsts++;
    }
  }
}

void initFuncInfos()
{
  for (Function &f : *cf->module)
  {
    FuncInfo *fi = initFuncInfo(&f);
    fi->fi_origin = fi;
  }
}

FuncInfo *initFuncInfo(Function *F)
{
  FuncInfo *fi = new FuncInfo(F);
  fimap[F] = fi;
  return fi;
}
