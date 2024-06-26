#ifndef TYPES_H_
#define TYPES_H_
/*
 * Copyright (c) 2020 SRI International All rights reserved.
 * Use of this source code is governed by a BSD-style
 * license that can be found in the LICENSE file.
 */

/*This file is the main header file for LoopUnrollTest. It contains a structure LoopUnrollTest that assists Loop Unrolling in checking whether the loop
has terminated  within the time and number of iterations, it should be. It inserts call instructions in every iteration and exit blocks of the loop,
which is used to determine the termination of the loop. All the methods of the structure are defined in src/LoopUnrollTest.cpp.*/

#include "llvm/Analysis/LoopInfo.h"
#include "Debug.h"
#define LOOPEXITBB "__loop_termination_test__"
#define LOOPITERBB "__loop_iteration_test__"
#define PRNTDBGSTR "__print_debug_string__"
#define SETDBGLEVEL "__set_debug_level__"

#define DEFAULT_TRIP_COUNT 0

using namespace std;
using namespace llvm;

/*
  structure used for loop unroll testing
*/

struct LoopUnrollTest
{
  static int GLOBAL_LOOP_ID;
  bool terminated, ConstTripCount, isFileIOLoop;
  vector<Instruction *> indepInsts;
  map<Instruction *, ProcResult> InstResults;
  unsigned numOrigInsts, partOfLoop, iterations;
  int id, fileTripCount;
  // vector<Instruction *> instrumented;
  LoopUnrollTest(Loop *L, Module *module, bool tripCount, bool isFileIOLoop, int fileCount);
  CallInst *getTestInst(string name, Module *module);
  string getExitName();
  string getIterName();

  Instruction *firstInst(BasicBlock *BB);
  bool checkTestInst(Instruction *I, string testName);
  bool containsTestInst(BasicBlock *BB, string testName);
  bool checkBreakInst(Instruction *I);
  void updateIter(Instruction *I);
  bool checkPassed();

  void removeInstructions(Function *F);
  void updateTime(Instruction *, uint64_t);
  uint64_t elapsedTime;
};
#endif
