/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */

// This file contains function prototypes for src/Utils.cpp.

#ifndef UTILS_H_
#define UTILS_H_

#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <string>

#include "BBOps.h"

using namespace llvm;
using namespace std;

void split(string str, vector<string> &tokens, char delim);
Value *getArg(Function *func, int index);
void getReadonlyFuncNames();
bool checkIfReadOnlyFunc(Function *F);

#endif
