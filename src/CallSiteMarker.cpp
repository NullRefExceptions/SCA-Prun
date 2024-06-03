#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Pass.h"

using namespace llvm;
using namespace std;

class Visitor : public InstVisitor<Visitor>
{
public:
  uint64_t num = 0;
  LLVMContext *ctx;

  void visitCallInst(CallInst &I)
  {
    MDNode* MDNode = MDNode::get(*ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), num++)));
    I.setMetadata("csm",MDNode);
    
  }

/*   void visitAllocaInst(AllocaInst &I)
  {
    MDNode* MDNode = MDNode::get(*ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), num++)));
    I.setMetadata("csm",MDNode);
  } */
  
};

class CallSiteMarker : public llvm::ModulePass
{
public:
  static char ID;
  CallSiteMarker() : ModulePass(ID) {}
  Visitor v;
  void getAnalysisUsage(AnalysisUsage &AU) const
  {
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M)
  {
    v.ctx = &M.getContext();
    v.visit(M);
    outs()<<"marked "<<v.num<<" callsites\n";
    return false;
  }
};

static RegisterPass<CallSiteMarker> X("csm","mark all callsite",false, false);
char CallSiteMarker::ID = 0;
