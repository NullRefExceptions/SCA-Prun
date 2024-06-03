// #undef NDEBUG

#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/ValueMap.h>
#include <stack>

#include "DDA/ContextDDA.h"
#include "DDA/DDAClient.h"
#include "DDA/DDAPass.h"
#include "Graphs/SVFGOPT.h"
#include "MSSA/MemSSA.h"
#include "MSSA/SVFGBuilder.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVFIR/SVFIR.h"
#include "WPA/Andersen.h"

#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/Analysis/CFG.h>
#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/SourceMgr.h>

#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/CommandLine.h"

using namespace SVF;
using namespace llvm;
using namespace std;

const Option<std::string> mainPath("main", "path to the main bc file", "");
const Option<std::string> libPath("lib", "path to the library bc file", "");
const Option<std::string> linkedPath("linked", "path to the linked bc file", "");

enum ArgType
{
    ArgTypeConstantInt,
    ArgTypeConstantNullPtr,
    ArgTypeConstantFuncPtr,
    ArgTypeConstantObjPtr,
    ArgTypeContextObjPtr,
    ArgTypeOthers
};
struct CallSiteSpec;
struct ApiSpec;
struct ArgSpec
{
    Value* aarg;
    const Value* farg;
    ArgType type;
    set<const MemObj*> memObjs;
    CallSiteSpec* parent;
};
struct CallSiteSpec
{
    const CallInst* inst;
    uint32_t callSiteId;
    vector<ArgSpec*> argSpecs;
    ApiSpec* parent;
};
struct ApiSpec
{
    Function* apiFunc;
    set<CallSiteSpec*> callSites;
    int argIndexBase;
};

enum ObjContentType
{
    ObjContentTypeContext,
    ObjContentTypeConstant,
    ObjContentTypeOthers
};
enum ObjAllocType
{
    ObjAllocInMainModule,
    ObjAllocInLibModuleHeap,
    ObjAllocInLibModuleGloble,
    ObjAllocOthers
};
struct MemObjSpec
{
    uint64_t refCount;
    const MemObj* memObj;
    set<FormalINSVFGNode*> FIns;
    PointerType* llvmType;
    ObjContentType contentType;
    ObjAllocType allocType;
    set<ArgSpec*> relatedArgs;
    Value* wrapperValue;
};

LLVMModuleSet* svfModuleSet;
Module* module;
Module* mainModule;
Module* libModule;
LLVMContext* ctx;
SVFIR* pag;
SVFG* svfg;
BVDataPTAImpl* pta;
DDAClient* ddaClient;
ContextDDA* cpta;
PTACallGraph* cg;
vector<ApiSpec*> apiSpecs;
Function* wrapFunc;
const DataLayout* DL;

set<const CallInst*> markedCallInst;
ContextCond currentCtx;
SVFGNode* targetNode;
const NodeBS* targetPts;
NodeID userPtr;

map<const MemObj*, MemObjSpec> memObjSpecs;

constexpr int maximumCxtLen = 1000;

SVFGNode* getSvfgNode(Value* v)
{
    return svfg->getSVFGNode(pag->getValueNode(svfModuleSet->getSVFValue(v)));
}

/*
我们分析API在callsite处指针参数指向的所有memobj，并标记对应的formalinNode

memobj是全局的，仅有1个，在初始化符号表时产生
而对应的ObjNode在生成pag时产生，此外当memobj在代码中被gep时，pag中会产生新的GepObjVar，来表示
子对象。之后的指针分析和memssa中的pts都指的是pag中的node（因此包括新产生的GepObjVar）
我们这里找出所有的fins（即memobj和其所有子对象）
 */
void getCallsiteObjs(ArgSpec* as)
{
    auto nodeId = pag->getValueNode(svfModuleSet->getSVFValue(as->aarg));
    auto formalIns = svfg->getFormalINSVFGNodes(cg->getCallerOfCallSite(as->parent->callSiteId));
    auto pts = pta->getPts(nodeId);
    for (auto objId : pts)
    {
        auto memObj = pag->getObject(objId);
        assert(memObj);
        as->memObjs.insert(memObj);
        if (memObj->isFunction())
        {
            as->type = ArgTypeConstantFuncPtr;
            continue;
        }
        assert(objId != pag->getConstantNode() && "model-consts is not enabled!\n");
        auto& objSpec = memObjSpecs[memObj];

        for (auto id : formalIns)
        {
            auto formalIn = dyn_cast<FormalINSVFGNode>(svfg->getSVFGNode(id));
            for (auto oid : formalIn->getPointsTo())
                if (pag->getObject(oid) == memObj)
                    objSpec.FIns.insert(formalIn);
        }

        if (memObj->isConstDataOrConstGlobal() || memObj->isConstantArray() || memObj->isConstantStruct())
        {
            errs() << "found const memobj: " << memObj->toString() << "\n";
            as->type = ArgTypeConstantObjPtr;
            objSpec.contentType = ObjContentTypeConstant;
            objSpec.wrapperValue = const_cast<Value*>(svfModuleSet->getLLVMValue(memObj->getValue()));
        }
        else
        {
            objSpec.contentType = ObjContentTypeOthers;
            as->type = ArgTypeOthers;
        }

        objSpec.memObj = memObj;
        auto llvmType = dyn_cast<PointerType>(as->farg->getType());
        assert(llvmType && "invialid obj type");
        objSpec.llvmType = llvmType;
        objSpec.allocType = ObjAllocOthers;
        if (memObj->isHeap() || memObj->isStack())
        {
            auto funcName = dyn_cast<SVFInstruction>(memObj->getValue())->getFunction()->getName();
            bool inMain =
                mainModule->getFunction(funcName) != nullptr && !mainModule->getFunction(funcName)->isDeclaration();
            bool inLib =
                libModule->getFunction(funcName) != nullptr && !libModule->getFunction(funcName)->isDeclaration();
            if (inMain && !inLib)
                objSpec.allocType = ObjAllocInMainModule;
            else if (!inMain && inLib && memObj->isHeap())
                objSpec.allocType = ObjAllocInLibModuleHeap;
        }
        else if (memObj->isGlobalObj())
        {
            auto valueName = memObj->getValue()->getName();
            bool inMain = mainModule->getGlobalVariable(valueName) != nullptr;
            bool inLib = libModule->getGlobalVariable(valueName) != nullptr;
            if (inMain && !inLib)
                objSpec.allocType = ObjAllocInMainModule;
            else if (!inMain && inLib)
                objSpec.allocType = ObjAllocInLibModuleGloble;
        }

        // 只有在不同的API中出现的才算
        auto apiFunc = as->parent->parent->apiFunc;
        bool added = false;
        for (auto i : objSpec.relatedArgs)
        {
            if (apiFunc == i->parent->parent->apiFunc)
                added = true;
        }
        if (!added)
            objSpec.refCount++;

        objSpec.relatedArgs.insert(as);
    }
}

bool hasConstantArg(const CallSiteSpec* cs)
{
    for (auto arg : cs->argSpecs)
    {
        if (arg->type <= ArgTypeConstantObjPtr)
            return true;
    }
    return false;
}

bool hasContextArg(const CallSiteSpec* cs)
{
    for (auto arg : cs->argSpecs)
    {
        if (arg->type == ArgTypeContextObjPtr)
            return true;
    }
    return false;
}

void analysisApiCallSites()
{
    vector<llvm::StringRef> apiFuncNames;
    for (auto& f : *mainModule)
        if (f.isDeclaration())
        {
            auto libFunc = libModule->getFunction(f.getName());
            if (libFunc != nullptr && !libFunc->isDeclaration() && !libFunc->hasInternalLinkage())
            {
                apiFuncNames.push_back(f.getName());
            }
        }

    for (auto fName : apiFuncNames)
    {
        // find callsites of apiFunc in linkedModule
        errs() << "analysis api " << fName << "\n";
        ApiSpec* spec = new ApiSpec();
        auto APIFunc = module->getFunction(fName);
        spec->apiFunc = APIFunc;
        auto node = cg->getCallGraphNode(svfModuleSet->getSVFFunction(APIFunc));
        for (auto inEdge : node->getInEdges())
        {
            auto callerName = inEdge->getSrcNode()->getFunction()->getName();
            bool inMain =
                mainModule->getFunction(callerName) != nullptr && !mainModule->getFunction(callerName)->isDeclaration();
            bool inLib =
                libModule->getFunction(callerName) != nullptr && !libModule->getFunction(callerName)->isDeclaration();

            if (inMain && !inLib)
            {
                for (auto i : inEdge->getDirectCalls())
                {
                    CallSiteSpec* css = new CallSiteSpec();
                    css->callSiteId = cg->getCallSiteID(i, node->getFunction());
                    css->inst = (CallInst*)svfModuleSet->getLLVMValue(i->getCallSite());
                    css->parent = spec;
                    spec->callSites.insert(css);
                }
                for (auto i : inEdge->getIndirectCalls())
                {
                    CallSiteSpec* css = new CallSiteSpec();
                    css->callSiteId = cg->getCallSiteID(i, node->getFunction());
                    css->inst = (CallInst*)svfModuleSet->getLLVMValue(i->getCallSite());
                    css->parent = spec;
                    spec->callSites.insert(css);
                }
            }
            else if (!(inMain ^ inLib))
                errs() << "invalid caller: " << callerName << "\n";
        }

        // analysis callsites
        for (auto css : spec->callSites)
        {
            auto ci = css->inst;
            errs() << "analysis callsite: " << *ci << "\n";
            int idx = 0;
            for (auto& arg : ci->arg_operands())
            {
                Value* v = arg.get();
                ArgSpec* as = new ArgSpec();
                as->farg = LLVMUtil::getCallee(ci)->arg_begin() + idx;
                as->aarg = v;
                as->parent = css;
                css->argSpecs.push_back(as);
                if (v->getType()->isPointerTy())
                {
                    // nullptr, constantExp
                    if (isa<ConstantPointerNull>(v))
                    {
                        as->type = ArgTypeConstantNullPtr;
                        errs() << "ConstantNullPtr\n";
                    }
                    else
                        getCallsiteObjs(as);
                }
                else if (v->getType()->isIntegerTy())
                {
                    // 我们是否需要在callsite处执行一次Simple constant
                    // propagation?
                    if (isa<ConstantInt>(v))
                    {
                        as->type = ArgTypeConstantInt;
                        errs() << "ConstantInt\n";
                    }
                    else
                        as->type = ArgTypeOthers;
                }
                else
                    errs() << "unhandled param in callinst: " << *ci << "\n";
                idx++;
            }
            errs() << "\n";
        }

        apiSpecs.push_back(spec);
    }
}

bool isReachable(const CallSiteSpec* from, const CallSiteSpec* to)
{
    auto current = from->inst;
    auto insTo = to->inst;
    while (current)
    {
        if (current == insTo)
            return true;
        current = dyn_cast<CallInst>(current->getNextNode());
    }
    return false;
}

bool isReachable(const Function* fun, const BasicBlock* from, const BasicBlock* to)
{
    SmallVector<std::pair<const llvm::BasicBlock*, const llvm::BasicBlock*>> backEdges;
    FindFunctionBackedges(*fun, backEdges);
    vector<const BasicBlock*> worklist;

    worklist.push_back(from);
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        if (current == to)
            return true;

        for (auto i = succ_begin(current); i != succ_end(current); i++)
        {
            auto edge = std::pair<const llvm::BasicBlock*, const llvm::BasicBlock*>(current, *i);
            if (find(backEdges, edge) != backEdges.end())
            {
                worklist.push_back(*i);
            }
        }
    }
    return false;
}

bool isReachable(set<PTACallGraphEdge*>& backEdges, const Function* from, const Function* to)
{
    vector<PTACallGraphNode*> worklist;
    auto svfFrom = cg->getCallGraphNode(svfModuleSet->getSVFFunction(from));
    auto svfTo = cg->getCallGraphNode(svfModuleSet->getSVFFunction(to));
    worklist.push_back(svfFrom);
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        if (current == svfTo)
            return true;

        for (auto edge : current->getOutEdges())
            if (backEdges.find(edge) != backEdges.end())
                worklist.push_back(edge->getDstNode());
    }
    return false;
}

void getSortCallsites(vector<const CallSiteSpec*>& sortedCss)
{
    map<const BasicBlock*, vector<const CallSiteSpec*>> bb2css;
    for (auto api : apiSpecs)
        for (auto css : api->callSites)
            bb2css[css->inst->getParent()].push_back(css);

    for (auto& i : bb2css)
    {
        sort(i.second, [](const CallSiteSpec* l, const CallSiteSpec* r) { return isReachable(l, r); });
    }

    map<const Function*, vector<const BasicBlock*>> fun2bbs;
    for (auto& i : bb2css)
        fun2bbs[i.first->getParent()].push_back(i.first);

    for (auto& i : fun2bbs)
    {
        sort(i.second, [](const BasicBlock* l, const BasicBlock* r) {
            bool l2r = isReachable(l->getParent(), l, r);
            assert(l2r != isReachable(l->getParent(), r, l));
            return l2r;
        });
    }

    set<PTACallGraphEdge*> backEdges;
    vector<PTACallGraphNode*> worklist;
    set<PTACallGraphNode*> visited;
    worklist.push_back(cg->getCallGraphNode(svfModuleSet->getSVFFunction("main")));
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        visited.insert(current);
        for (auto edge : current->getOutEdges())
        {
            auto dst = edge->getDstNode();
            if (visited.find(dst) != visited.end())
                backEdges.insert(edge);
            else
                worklist.push_back(dst);
        }
    }
    vector<const Function*> funcs;
    for (auto& i : fun2bbs)
        funcs.push_back(i.first);

    sort(funcs, [&backEdges](const Function* l, const Function* r) {
        bool l2r = isReachable(backEdges, l, r);
        assert(l2r != isReachable(backEdges, r, l));
        return l2r;
    });

    for (auto& fun : funcs)
        for (auto& bb : fun2bbs[fun])
            for (auto& css : bb2css[bb])
                sortedCss.push_back(css);
}

/*
    构造wrapper function：
        1.对api的callsite进行排序，确定调用顺序：
            同一个基本块中的callsite存在自然顺序，产生API-BB块
            同一个函数内的callsite进行排序，根据dom-tree的信息，产生API-FUNC块
            如果存在分散在多个函数的api调用，根据callgraph信息排序，产生最终排序结果

        2.根据根据原来的callsite参数，设定wrapper func中每个callsite的参数：
            原来是scalar常量的，仍然保持scalar常量
            原来是constantObj指针的，设定为对应的obj
            原来是contextObj的，根据类型不同分析：
                InMainModule下，我们添加malloc obj的代码，而对于其他两种情况不需要添加
 */
void generateWrapperForMutiApi()
{
    vector<const CallSiteSpec*> sortedCss;
    getSortCallsites(sortedCss);

    // create wrapper func
    auto retType = Type::getVoidTy(*ctx);
    vector<Type*> Params;
    int argIndexBase = 0;
    for (auto api : apiSpecs)
    {
        api->argIndexBase = argIndexBase;
        for (auto i : api->apiFunc->getFunctionType()->params())
            Params.push_back(i);
        assert(!api->apiFunc->isVarArg() && "unhandled var arg");
        argIndexBase += api->apiFunc->arg_size();
    }
    auto ft = FunctionType::get(retType, Params, false);
    wrapFunc = Function::Create(ft, GlobalValue::ExternalLinkage, "pa_wrapper", module);
    auto bb = BasicBlock::Create(*ctx, "", wrapFunc);
    SVF::IRBuilder ir(bb);

    /*     // get needed func
        Function* mallocFunc = module->getFunction("malloc");
        if (!mallocFunc)
        {
            vector<Type*> mallocArgs;
            mallocArgs.push_back(Type::getInt64Ty(*ctx));
            FunctionType* mallocFT = FunctionType::get(Type::getInt8PtrTy(*ctx), mallocArgs, false);
            mallocFunc = Function::Create(mallocFT, GlobalValue::ExternalLinkage, "malloc", module);
        }
        Function* memcpyFunc = module->getFunction("memcpy");
        if (!memcpyFunc)
        {
            vector<Type*> memcpyArgs;
            memcpyArgs.push_back(Type::getInt8PtrTy(*ctx));
            memcpyArgs.push_back(Type::getInt8PtrTy(*ctx));
            memcpyArgs.push_back(Type::getInt64Ty(*ctx));
            FunctionType* memcpyFT = FunctionType::get(Type::getVoidTy(*ctx), memcpyArgs, false);
            memcpyFunc = Function::Create(memcpyFT, GlobalValue::ExternalLinkage, "memcpy", module);
        } */

    // create needed obj
    for (auto& i : memObjSpecs)
    {
        auto& obj = i.second;
        if (obj.contentType == ObjContentTypeContext && obj.allocType == ObjAllocInMainModule)
        {
            auto objType = LLVMUtil::getPtrElementType(obj.llvmType);
            assert(LLVMUtil::getTypeSizeInBytes(objType) && "invalid obj size");
            obj.wrapperValue = ir.CreateAlloca(objType);
        }
    }

    // create callinst
    for (auto css : sortedCss)
    {
        auto callee = css->parent->apiFunc;
        vector<Value*> args;
        for (size_t i = 0; i < callee->arg_size(); i++)
        {
            auto as = css->argSpecs[i];
            if (as->type == ArgTypeConstantInt)
                args.push_back(as->aarg);
            else if (as->type == ArgTypeConstantNullPtr)
                args.push_back(as->aarg);
            else if (as->type == ArgTypeConstantFuncPtr)
            {
                assert(as->memObjs.size() == 1);
                auto funcObj = *as->memObjs.begin();
                args.push_back(const_cast<Value*>(svfModuleSet->getLLVMValue(funcObj->getValue())));
            }
            else if (as->type == ArgTypeConstantObjPtr)
            {
                if (Constant* constVal = ConstantFoldInstruction(dyn_cast<Instruction>(as->aarg), *DL))
                    args.push_back(constVal);
                else
                    assert(false && "can not fold constExp!");
            }
            else if (as->type == ArgTypeContextObjPtr)
            {
                assert(as->memObjs.size() == 1);
                auto memObj = *as->memObjs.begin();
                args.push_back(memObjSpecs[memObj].wrapperValue);
            }
            else
                args.push_back(wrapFunc->arg_begin() + i + css->parent->argIndexBase);
        }
        ir.CreateCall(callee, args);
    }

    // create ret
    ir.CreateRetVoid();
}

/*
    确定contextObj，可能的情况包括：
        1.mainModule栈上、堆上或全局的对象
        2.libModule堆上的对象
        3.libModule全局的对象(TODO)
    其中除了3以外，Context通常以指针的形式传入API，或作为API的输出
    我们目前考虑的启发式方法：
        1.过滤掉在多个API中仅出现过1次的memobj
        2.memobj的读写仅应该发生在libmodule中（Context对象通常是Opaque的）
        3.如果obj在libModule中的栈上被alloc，则排除其作为Context对象（应该不存在这样的情况？）
 */
bool contextAnalysis()
{
    bool res = false;
    for (auto& i : memObjSpecs)
    {
        auto& obj = i.second;
        if (obj.contentType == ObjContentTypeConstant)
            continue;
        if (obj.refCount > 1)
        {
            errs() << "candidate Context obj: \n" << obj.memObj->toString();
            errs() << "refCount: " << obj.refCount << "\n\n";
            obj.contentType = ObjContentTypeContext;
            for (auto arg : obj.relatedArgs)
            {
                assert(arg->memObjs.size() == 1);
                arg->type = ArgTypeContextObjPtr;
            }
            res = true;
        }
    }

    return res;
}

/*
单API模式：
    每个API的callsite都被检查，只有当其参数包含常量时，才会被添加到wrapper function中
且每个API的callsite都是独立的
    TODO：当前我们期望每个API仅被调用一次，这样常量传播的结果就可以直接使用
 */
void generateWrapperForSingleApi()
{
    auto retType = Type::getVoidTy(*ctx);
    vector<Type*> Params;
    int argIndexBase = 0;
    for (auto api : apiSpecs)
    {
        api->argIndexBase = argIndexBase;
        for (auto i : api->apiFunc->getFunctionType()->params())
            Params.push_back(i);
        assert(!api->apiFunc->isVarArg() && "unhandled var arg");
        argIndexBase += api->apiFunc->arg_size();
    }
    auto ft = FunctionType::get(retType, Params, false);
    wrapFunc = Function::Create(ft, GlobalValue::ExternalLinkage, "pa_wrapper", module);
    auto bb = BasicBlock::Create(*ctx, "", wrapFunc);
    SVF::IRBuilder ir(bb);
    for (auto api : apiSpecs)
        for (auto cs : api->callSites)
        {
            if (!hasConstantArg(cs))
                continue;
            auto callee = api->apiFunc;
            vector<Value*> args;
            for (size_t i = 0; i < callee->arg_size(); i++)
            {
                auto as = cs->argSpecs[i];
                if (as->type == ArgTypeConstantInt)
                    args.push_back(as->aarg);
                else if (as->type == ArgTypeConstantNullPtr)
                    args.push_back(as->aarg);
                else if (as->type == ArgTypeConstantFuncPtr)
                {
                    assert(as->memObjs.size() == 1);
                    auto funcObj = *as->memObjs.begin();
                    args.push_back(const_cast<Value*>(svfModuleSet->getLLVMValue(funcObj->getValue())));
                }
                else if (as->type == ArgTypeConstantObjPtr)
                {
                    if (Constant* constVal = ConstantFoldInstruction(dyn_cast<Instruction>(as->aarg), *DL))
                        args.push_back(constVal);
                    else
                        assert(false && "can not fold constExp!");
                }
                else
                    args.push_back(wrapFunc->arg_begin() + i + api->argIndexBase);
            }

            ir.CreateCall(callee, args);
        }

    ir.CreateRetVoid();
}

/*
每当探索到一个callsite时，检查在当前的ContextCond条件下，
目标指针是否依然指向该memRegion，如果否就不再继续

注意：mR和cpts中保存的只有初始obj的id，如果obj在过程中被def成为常量（比如常量obj
拷贝到另一个obj），则存在潜在的可能，在另一条非def为常量的路径上，checkCallContext返回
true，因为contextPta只计算了初始obj，而不是memSSA rename之后的
 */
bool checkCallContext(CallSiteID cId)
{

    CxtVar var(currentCtx, userPtr);
    bool res = false;
    const CxtPtSet& cpts = cpta->computeDDAPts(var);
    for (auto t : cpts)
        if (targetPts->test(t.get_id()))
        {
            res = true;
            break;
        }

    /*     errs() << "checking call in " << cg->getCallSite(cId)->getCallSite()->getFunction()->toString() << "res: " <<
       res
               << "\n"; */
    return res;
}

/* 从ptrs开始，向上探索，通过DDA判断是否是虚假的边来分析该user是否的确是来自targetNode
我们需要先在当前函数内探索完所有的节点，如果没有到达，我们继续跨函数寻找
*/
bool revExplore(SVFGNode* root)
{
    assert(root);
    bool result = false;
    vector<SVFGNode*> fins;
    vector<SVFGNode*> worklist;
    set<SVFGNode*> visited;
    worklist.push_back(root);
    // errs() << "we are in " << root->getFun()->getName() << ", ctx: " << currentCtx.toString() << "\n";
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        if (!visited.insert(current).second)
            continue;
        for (auto edge : current->getInEdges())
        {
            auto srcNode = edge->getSrcNode();
            if (auto inEdge = dyn_cast<IntraIndSVFGEdge>(edge))
            {
                if (srcNode == targetNode)
                {
                    result = true;
                    errs() << "find target node\n";
                    goto out;
                }
                else if (isa<FormalINSVFGNode>(srcNode))
                    fins.push_back(srcNode);
                else
                    worklist.push_back(inEdge->getSrcNode());
            }
        }
    }

    for (auto srcNode : fins)
    {
        for (auto edge : srcNode->getInEdges())
        {
            auto callEdge = dyn_cast<CallIndSVFGEdge>(edge);
            auto cId = callEdge->getCallSiteId();
            bool markCallsite = false;
            /* 如果存在递归，我们跳过这条边 */
            if (currentCtx.containCallStr(cId))
                continue;
            currentCtx.getContexts().insert(currentCtx.begin(), cId);
            if (currentCtx.cxtSize() >= maximumCxtLen)
                errs() << "context stackoverflow!\n ";
            if (checkCallContext(cId))
            {
                auto n = dyn_cast<ActualINSVFGNode>(edge->getSrcNode());
                markCallsite = revExplore(n);
            }
            else
                currentCtx.getContexts().erase(currentCtx.begin());

            /* 如果结果为true，说明这条路径的确对应memobj的移动，我们标记这个callsite */
            if (markCallsite)
            {
                auto svfCs = svfg->getCallSite(cId)->getCallSite();
                auto ci = dyn_cast<CallInst>(svfModuleSet->getLLVMValue(svfCs));
                assert(ci);
                markedCallInst.insert(ci);
                result = true;
            }
        }
    }

out:
    if (currentCtx.cxtSize())
    {
        currentCtx.getContexts().erase(currentCtx.begin());
        // errs() << "normal out!" << " ctx: " << currentCtx.toString() << "\n";
    }
    else
    {
        errs() << "top out!\n\n";
    }
    return result;
}

/*
我们这里标记新产生的ConstantObj，注意我们不希望引入太多的对象，这可能导致常量传播无法完成。新对象的来源有两种：
    TODO: 1.如果这次use是库函数（memcpy、strcpy等），而且被svf建模
    TODO: 2.如果这次use是load出scalar，我们需要看看其是否被store到另一个memobj（这部分在处理API的scalar常量参数时也会用到）
 */
void markNewConstantObj(StmtVFGNode* user,
                        vector<tuple<ObjContentType, SVF::SVFGNode*, std::set<SVF::StmtVFGNode*>*>>& worklist)
{
}

void getRalatedUsers(SVFGNode* node, set<StmtVFGNode*>* relatedNodes)
{
    auto mrNode = dyn_cast<MRSVFGNode>(node);
    for (auto objId : mrNode->getPointsTo())
    {
        errs() << "get related users for nodeId: " << objId << "\n";
        for (auto stmt : pag->getSVFStmtSet(SVFStmt::Load))
        {
            auto pts = pta->getPts(stmt->getSrcID());
            if (pts.test(objId))
            {
                auto nodeid = svfg->getStmtVFGNode(stmt);
                relatedNodes->insert(nodeid);
                errs() << stmt->getBB()->getFunction()->toString() << "\n";
                errs() << stmt->toString() << "\n";
            }
        }
        for (auto stmt : pag->getSVFStmtSet(SVFStmt::Store))
        {
            // ignore storeNode added by model-consts=true
            // make sure this node is from code
            if (stmt->getBB() == nullptr)
                continue;
            auto pts = pta->getPts(stmt->getDstID());
            if (pts.test(objId))
            {
                auto nodeid = svfg->getStmtVFGNode(stmt);
                relatedNodes->insert(nodeid);
                errs() << stmt->getBB()->getFunction()->toString() << "\n";
                errs() << stmt->toString() << "\n";
            }
        }
    }

    errs() << "\n\n";
}

/*
    我们在这里标记在常量传播中遇到的callsite，以此来引导整个常量传播过程。我们存在3类需要被标记的情况：
        1.函数及其后代访问了ContextObj

                    我们存在一个感兴趣的SSAmemobj，希望之后的常量传播中，能够探索所有对这个SSAmemobj访问的代码。
                我们首先找到SSAmemobj对应的memobj，之后通过getRaltedUsers拿到所有使用节点，然后从User反向搜索
                到SSAmemobj被def的地方，并标记沿途的callsite
                    这个过程中，通过checkCallContext减少了由于SVFG的context-insensitive导致的虚假的边，而且由于需要
                确保到达SSAmemobj被def的点，我们也保证了只分析了这个SSA及其之后的版本，其他不相关的版本被排除

        2.函数及其后代访问了ContantObj

                    整体和情况1类似，但情况1仅能针对某个SSAmemobj进行分析，比如Context对象的情况（我们假设Context对象仅有一个）
                然而对Constant对象，存在对象内容拷贝的情况，即会由1个constant对象产生其他constant对象，因此我们还需要追踪
                这些新对象。
                    当一次revExplore完成后，如果返回为true，说明该user的确访问了SSAmemobj的内容，此时如果是ConstantObj，我们还
                需要分析该user（应该只有load，因为在constantobj上进行store似乎是不符合逻辑的？）来寻找新对象。

        3.函数及其后代分配了ContextObj或ContantObj
            malloc wrapper function：
                有的库可能考虑到移植性，把堆内存对象的产生可能被包装在一个特殊函数中而不是直接使用malloc。然而在svfg堆对象是通过位置建模
                的，这使得太多的obj被合并，而且彼此实际上毫不相干。
                1.手工分析目标库，尽量去除自己包装的malloc类的函数（通常可以通过设置条件变量来完成）

            malloc function：
                在引导性常量传播中，堆对象不是一开始就被建模的，我们必须让常量传播引擎执行被追踪的堆对象被分配的地方，否则后面的分析无法进行
                TODO：1.判断当前的SSAmemobj是否为heapobj，如果是我们需要

    初始化worklist：
        如果API存在常量 entryChi，那么添加该节点
        如果callsite（每个都跑一次因为常量位置可能会变化）某个scalar参数是常量，那么分析其use，查找store进入的obj，之后添加obj到worklist
        所有被识别的context对象

    运算过程中，我们还需要发现常量节点在探索过程中遇到的load节点，后是否紧接着store节点，如果很可能store的obj也保存了常量，我们添加
    该obj到worklist（和Trimmer不同我们不需要回溯到alloc）

     */
void markCallSites()
{
    vector<tuple<ObjContentType, SVF::SVFGNode*, std::set<SVF::StmtVFGNode*>*>> worklist;
    set<Function*> fs;
    MDNode* funcMDNode = MDNode::get(*ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), 1)));
    /* for (auto api : apiSpecs)
    {
        for (auto ci : api->callSites)
        {
            for (auto arg : ci->argSpecs)
            {
                if (arg->type != ArgTypeConstantInt)
                    continue;
                for (auto user : arg->farg->users())
                {
                    errs() << *user << "\n";
                    if (!isa<StoreInst>(user))
                        continue;
                    auto storeNode = dyn_cast<StoreSVFGNode>(getSvfgNode(user));
                    if (!storeNode)
                    {
                        errs() << *user << "\n";
                        continue;
                    }
                    errs() << storeNode->toString() << "\n";
                    // assert(storeNode);
                    worklist.push(storeNode);
                }
            }
        }
    } */

    /*
    我们有一个constant的memobj，以及与其相关的formalin（这些formalin位于api的caller中）
    现在我们寻找整个程序中对这个memobj的use，并标记这些use实际到达formalin的路径（SVFG是context-insensitive的
    ，所以存在虚假路径），这些use最终都会追溯到formalin，我们关注的是路径而不是结果

    对于consantobj来说，不存在store的use，因此所有的load节点都可以追溯到formalin，但并不一定是1个。
    如果在mainModule的两个函数中都调用api且提供相同的常量对象，formalin就会有两个

    */
    for (auto& i : memObjSpecs)
    {
        auto& obj = i.second;
        if (obj.contentType == ObjContentTypeConstant)
        {
            for (auto fin : obj.FIns)
            {
                auto relatedUsers = new set<StmtVFGNode*>();
                getRalatedUsers(fin, relatedUsers);
                if (relatedUsers->size())
                    worklist.push_back(tuple<ObjContentType, SVF::SVFGNode*, std::set<SVF::StmtVFGNode*>*>(
                        obj.contentType, fin, relatedUsers));
                else
                    errs() << "no user found!\n";
            }
        }
    }

    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        targetNode = get<1>(current);
        errs() << "try on target node: " << targetNode->toString() << "\n";
        if (auto tempNode = dyn_cast<FormalINSVFGNode>(targetNode))
            targetPts = &tempNode->getPointsTo();
        else if (auto tempNode = dyn_cast<StoreSVFGNode>(targetNode))
        {
            auto src = dyn_cast<MRSVFGNode>((*(tempNode->getInEdges().begin()))->getSrcNode());
            targetPts = &src->getPointsTo();
        }
        else
            assert(false && "unexpected node type!");

        for (auto userNode : *get<2>(current))
        {
            if (isa<LoadSVFGNode>(userNode))
                userPtr = userNode->getPAGSrcNodeID();
            else if (isa<StoreSVFGNode>(userNode))
                userPtr = userNode->getPAGDstNodeID();
            else
                assert(false && "unexpected user type!");
            errs() << "start from: " << userNode->getFun()->toString() << "\n" << userNode->toString() << "\n";
            revExplore(userNode);
            errs() << "done!\n\n";

            markNewConstantObj(userNode, worklist);
        }

        for (auto I : markedCallInst)
        {
            ((CallInst*)I)->setMetadata("track_constant", funcMDNode);
            fs.insert(I->getCalledFunction());
        }
        markedCallInst.clear();
    }

    for (auto f : fs)
    {
        if (f)
            errs() << f->getName() << "\n";
        else
            errs() << "we get indirect call here\n";
    }
}

/*
API调用时的常量信息，可以简单的来自于写死的参数，也可以来自于api调用序列本身。
从mainModule抽取多个API组成一个调用序列组，这些调用可能会导致libModule自身状态
的改变（初始化->配置参数->调用方法）。
我们基于一个基本假设，多个API会集中化的共同访问一个Context的对象，同时API的行为变化主要取决于Context
对象
    1.因此wrapper函数中每个api都需要进入探索，但在探索过程中，我们需要考虑后续函数的探索策略。
    2.我们需要找到libModule的context对象，它们在多个API中被共享，因此对context对象进行访问和修改的func我们应该进入并探索
    3.此外常规的，对于每个API调用时，传递的obj和scalar常量，我们也应该传播它们

确定进入的范围是应该单独一个Pass决定，还是在常量传播时慢慢确定？

常量传播发生在非关键API时，我们标记Context的指针为tracked，只有参数中包含tracked指针的，或在modref能够操作Context
的函数才会被进入
常量传播发生在关键API时，除了和非关键API一样的进入条件外，我们还额外考虑直接在参数上写死的常量参数，即Const
ptr，和const scalar

和Trimmer不同的是，我们假设Context对象不会被拷贝（没有理由产生多个副本，你接下来用谁呢？何况Context对象在选取时就需要多个API共同
访问的属性。），但可以存在多个不同的Context对象
但关键API的ConstPTR可能被拷贝，因此我们需要追踪多个obj

关键API的实际执行路径除了受到直接调用参数的影响，还受到context对象的影响。因此，我们对于非关键API，
只需要追踪其对context对象的影响（使用modref分析，确定分析非关键API需要进入的函数），对于常量参数
以及它们对非关键API的影响我们不用考虑，因为它们影响不了关键API的行为
对于关键API，确定需要进入的函数同时由context访问，以及常量访问确定
 */
int main(int argc, char** argv)
{
    OptionBase::parseOptions(argc, argv, "pre analysis for Constant Folding", "");
    LLVMContext ctxs[2];
    SMDiagnostic Err;
    unique_ptr<Module> mP[3];
    mP[0] = parseIRFile(mainPath(), Err, ctxs[0]);
    mP[1] = parseIRFile(libPath(), Err, ctxs[0]);
    mP[2] = parseIRFile(linkedPath(), Err, ctxs[1]);

    mainModule = mP[0].get();
    libModule = mP[1].get();
    module = mP[2].get();

    if (mainModule == nullptr || libModule == nullptr || module == nullptr)
    {
        outs() << Err.getMessage() << "\n";
        return -1;
    }

    ctx = &module->getContext();
    DL = &module->getDataLayout();

    svfModuleSet = LLVMModuleSet::getLLVMModuleSet();
    SVFIRBuilder builder(svfModuleSet->buildSVFModule(*module));
    pag = builder.build();
    pta = AndersenWaveDiff::createAndersenWaveDiff(pag);

    // CxtBudget = 1000
    ContextCond::setMaxCxtLen(maximumCxtLen);
    ddaClient = new DDAClient(svfModuleSet->getSVFModule());
    ddaClient->initialise(svfModuleSet->getSVFModule());
    cpta = new ContextDDA(pag, ddaClient);
    cpta->initialize();

    cg = pta->getPTACallGraph();
    SVFGBuilder svfBuilder(true);
    svfg = svfBuilder.buildFullSVFG(pta);
    // cg->dump("cg");
    // svfg->dump("svfg");
    // pag->dump("pag");
    // pag->getICFG()->dump("icfg");
    analysisApiCallSites();

    /*
    接下来针对API进行分析，尝试找到context对象，并构造wrapper Function，如果最终失败，
    我们只能退回到单API分析模式
     */
    if (!contextAnalysis())
    {
        errs() << "no Context object found, back to single api mode\n";
    }

    markCallSites();

    if (!verifyModule(*module, &errs()))
    {
        error_code EC;
        raw_fd_ostream OS("linked_ann.bc", EC);
        WriteBitcodeToFile(*module, OS);
    }
    else
    {
        errs() << *wrapFunc;
    }
}