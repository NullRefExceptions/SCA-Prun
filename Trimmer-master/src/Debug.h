/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */

/* This the main header class for debug purposes. It contains methods regarding debugging such as initailzaing debugging Level,
printing memory, instructions and basic blocks. All the methods  of the class are defined in src/Debug.cpp.*/

#ifndef DEBUG_H_
#define DEBUG_H_

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "Mem.h"
using namespace llvm;
using namespace std;

#define No 0
#define Yes 1


enum ProcResult
{
  UNDECIDED,
  NOTFOLDED,
  PARTOFLOOP,
  FOLDED
};

extern int debugLevel;
class debug
{
public:
  debug(int level);
  bool isCurrentFn();
  template <class T>
  debug &operator<<(const T &x)
  {
    if (!ignore && isCurrentFn())
    {
      errs() << x;
      errs().flush();
    }
    return *this;
  }

private:
  bool ignore;
};

void initDebugLevel();
void printBB(string before, BasicBlock *BB, string after, int level);
void printInst(Instruction *I, int level);
void printMem(Memory *mem, uint64_t addr, uint64_t size);
void printInt(Memory *mem, uint64_t addr, uint64_t size);
void printStr(Memory *mem, uint64_t addr, uint64_t ptrSize);
void printConstMem(Memory *mem, uint64_t addr, uint64_t size);
void addToDebugLevel(char *str);

#endif
