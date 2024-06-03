#ifndef TRACKINFO_H_
#define TRACKINFO_H_

#include "llvm/IR/Instructions.h"
#include "map"
#include "llvm/ADT/BitVector.h"
#include "Mem.h"
using namespace llvm;
using namespace std;

struct csm_struct
{
    uint64_t ctx_id;
    bool isRead;
    bool isWrite;
    bool isMalloc;
};

struct CSInfo
{
    static void initCallSiteInfos();
    static void initFuncCallSiteInfo(Function &func);
    static void getConstantBV(CallInst *callins, BitVector *bv);

    static csm_struct getCSM(CallInst *callinst, uint64_t ctxIdx);
    static uint64_t getNumCSM(CallInst *callinst);
    static bool isContextObjRWM(CallInst *callinst);
    static bool isContextObjRWM(CallInst *callinst, uint64_t ctxIdx);
    static bool getContextObjIdx(CallInst *callinst, uint64_t &ctxIdx);
};

// context obj info
void *getTM(uint64_t fakeAddr);
void *getCM(uint64_t fakeAddr);

void *getTM(uint64_t fakeAddr, Memory *mem);
void *getCM(uint64_t fakeAddr, Memory *mem);

struct ctx_struct
{
    uint64_t ctxId;
    uint64_t faddr;
    uint64_t size;
};

struct COInfo
{
    static void addContextOBJ(uint64_t ctxId, uint64_t faddr, uint64_t size);
    static uint64_t remainConstantNum(uint64_t ctxId);
    static bool remainConstant(uint64_t ctxId);
    static bool remainConstant(uint64_t ctxId, uint64_t offset);
    static bool getContextObjIdx(uint64_t faddr, uint64_t &ctxIdx);
    static void status();
};

extern map<MDNode *, BitVector *> originBV;
extern map<uint64_t, ctx_struct> ctxMap;

#endif