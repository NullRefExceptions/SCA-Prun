/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */

/* This file consists of a structure FuncInfo keeping track of basic function
 information as well as value returned and context at return.*/

#ifndef FUNCINFO_H_
#define FUNCINFO_H_
#include "Mem.h"
#include "ConstantFolding.h"

using namespace std;
using namespace llvm;

struct FuncInfo
{
  Memory *context = nullptr;
  Register *retReg = nullptr;
  bool calledInLoop = false;
  bool addrTaken;
  unsigned directCallInsts = 0;
  unsigned clonedCounter = 0; // only used for origin function
  unsigned unrollCounter = 0; // only used for origin function
  FuncInfo *fi_origin = nullptr;
  Function *func = nullptr;
  FuncInfo(Function *F);
};

extern map<Function *, FuncInfo *> fimap;

void initFuncInfos();
FuncInfo *initFuncInfo(Function *F);

#endif
