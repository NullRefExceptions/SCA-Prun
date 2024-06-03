#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/ValueMap.h>
#include <stack>

#include "Util/Options.h"
#include "DDA/ContextDDA.h"
#include "DDA/DDAClient.h"
#include "DDA/DDAPass.h"
#include "Graphs/SVFGOPT.h"
#include "MSSA/MemSSA.h"
#include "MSSA/SVFGBuilder.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVFIR/SVFIR.h"
#include "WPA/Andersen.h"
#include "WPA/AndersenPWC.h"
#include "WPA/VersionedFlowSensitive.h"

#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/Analysis/CFG.h>
#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/SourceMgr.h>
#include "llvm/Support/FormatVariadic.h"

#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/CommandLine.h"

#include "Analyzer.h"
#include "CallGraph.h"
#include "Config.h"

using namespace SVF;
using namespace llvm;
using namespace std;

const Option<std::string> mainPath("main", "path to the main bc file", "");
const Option<std::string> libPath("lib", "path to the library bc file", "");
const Option<std::string> linkedPath("linked", "path to the linked bc file", "");
const Option<std::string> outputPath("o", "path to the linked_csm.bc", "linked_csm.bc");

struct CallSiteSpec;
struct ApiSpec;
struct MemObjSpec;

struct ArgSpec
{
    Value *aarg;
    const Value *farg;
    CallSiteSpec *parent;
};
struct CallSiteSpec
{
    const CallInst *inst;
    uint32_t callSiteId;
    vector<ArgSpec *> argSpecs;
    ApiSpec *parent;
};
struct ApiSpec
{
    Function *apiFunc;
    set<CallSiteSpec *> callSites;
    set<MemObjSpec *> memObjSpecs;
    int argIndexBase;
};

enum MarkType
{
    MARK_READ = 1,
    MARK_WRITE = 2,
    MARK_MALLOC = 4
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
    const MemObj *memObj;
    set<NodeID> allIds;
    ObjContentType contentType;
    ObjAllocType allocType;
    set<ArgSpec *> relatedArgs;
    Type *objType;
    uint64_t ctx_id;
};

LLVMModuleSet *svfModuleSet;
Module *module;
Module *mainModule;
Module *libModule;
LLVMContext *ctx;
BVDataPTAImpl *pta;
SVFIR *pag;
PTACallGraph *cg;
vector<ApiSpec *> apiSpecs;
const DataLayout *DL;

map<const MemObj *, MemObjSpec> memObjSpecs;

set<const MemObj *> memObjSet; // for debug
uint64_t falseObj_filter = 0;
uint64_t unrelated_filter = 0;
struct csm_struct
{
    uint64_t ctx_id;
    bool isRead;
    bool isWrite;
    bool isMalloc;
};

struct modinfo_struct
{
    uint64_t start; // start=max,end=0表明该函数一直处于初始状态，没有写ctx
    uint64_t end;   // end=max表明该函数写ctx，但范围无法确定
    bool isConstant;
    // 其他情况为我们能够推断写ctx的范围
};

map<CallInst *, vector<csm_struct>> callSiteMarks;
set<Loop *> loopMarks;
map<GepStmt *, modinfo_struct> gepModMap;
map<const Function *, map<uint64_t, modinfo_struct>> funcModMap;

GlobalContext GlobalCtx;

void printPAGNode(const SVFValue *vv)
{
    auto node = pag->getGNode(pag->getValueNode(vv));
    errs() << node->toString() << "\n";
    errs() << formatv("in {0},out {1}\n", node->getInEdges().size(), node->getOutEdges().size());

    for (auto ie : node->getInEdges())
    {
        errs() << ie->toString() << "\n";
    }
    errs() << "==============\n";
    for (auto ie : node->getOutEdges())
    {
        errs() << ie->toString() << "\n";
    }
    auto pts = pta->getPts(pag->getValueNode(vv));
    errs() << pts.count();
    errs() << " pts:{";
    for (auto i = pts.begin(); i != pts.end(); i++)
    {
        errs() << *i << " ";
        // errs() << "FI:" << pag->getObject(*i)->isFieldInsensitive();
    }
    errs() << "}\n";
}

/*
过滤一些不需要的memobj
特别是由于SVFG的上下文不敏感导致的memobj，以及非top memobj
首先进行粗粒度过滤，比如根据memobj的alloc的位置是否在main函数可达的范围内
 */
bool filter(const MemObj *memobj,bool first)
{
    if (memobj->isFunction())
    {
        if (first)
            unrelated_filter++;

        return false;
    }
    /*     if (memobj->getId() == pag->getConstantNode())
            return false;

    if (memobj->getValue() == nullptr)
        return false; // dummy memobj*/
    if (!memobj->isGlobalObj())
    {
        auto allocFunc = dyn_cast<SVFInstruction>(memobj->getValue())->getFunction();
        auto mainFunc = svfModuleSet->getSVFFunction("main");
        if (!cg->isReachableBetweenFunctions(mainFunc, allocFunc))
        {
            if (first)
                falseObj_filter++;
            return false;
        }
    }
    return true;
}

/*
我们分析API在callsite处指针参数指向的所有memobj，并分析memspec

memobj是全局的，仅有1个，在初始化符号表时产生
而对应的ObjNode在生成pag时产生，此外当memobj在代码中被gep时，pag中会产生新的GepObjVar，来表示
子对象。之后的指针分析和memssa中的pts都指的是pag中的node（因此包括新产生的GepObjVar）
我们这里找出所有的obj和对应的fins，在默认的intra-disjoint策略下，在main中的mr应该是不重叠的，因此
一个obj仅会出现在一个fin中
 */
void getCallsiteObjs(ArgSpec *as)
{
    auto nodeId = pag->getValueNode(svfModuleSet->getSVFValue(as->aarg));
    auto pts = pta->getPts(nodeId);

    for (auto id : pts)
    {
        auto memObj = pag->getObject(id);
        bool first = memObjSet.insert(memObj).second;
        // errs()<<memObj->toString();
        if (!filter(memObj,first))
            continue;

        // assert(objId != pag->getConstantNode() && "model-consts is not enabled!\n");
        auto &objSpec = memObjSpecs[memObj];
        as->parent->parent->memObjSpecs.insert(&objSpec);
        objSpec.allIds.insert(memObj->getId());
        for (auto fieldId : pag->getAllFieldsObjVars(memObj))
        {
            objSpec.allIds.insert(fieldId);
        }

        // 第一次初始化，设置contentType,allocType和objType
        if (objSpec.memObj == nullptr)
        {
            objSpec.memObj = memObj;
            // 1. set contentType
            if (memObj->isConstDataOrConstGlobal() || memObj->isConstantArray() || memObj->isConstantStruct())
            {
                // errs() << "found const memobj: " << memObj->toString() << "\n";
                objSpec.contentType = ObjContentTypeConstant;
            }
            else
            {
                objSpec.contentType = ObjContentTypeOthers;
            }

            // 2. set allocType
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

            // 3. set objType
            if (memObj->isStack())
            {
                auto acInst = dyn_cast<AllocaInst>(svfModuleSet->getLLVMValue(memObj->getValue()));
                if (acInst)
                {
                    objSpec.objType = acInst->getType();
                }
                else
                    errs() << "not alloc inst for stack obj\n";
            }
            else if (memObj->isHeap())
            {
                auto callInst = dyn_cast<CallInst>(svfModuleSet->getLLVMValue(memObj->getValue()));
                if (callInst)
                {
                    for (auto user : callInst->users())
                    {
                        if (auto bcInst = dyn_cast<BitCastInst>(user))
                        {
                            // errs() << *bcInst << "\n";
                            objSpec.objType = bcInst->getType();
                            // break;TODO 多个user怎么办
                        }
                    }
                }
                else
                    errs() << "not call inst for heap obj\n";
            }
            else if (memObj->isGlobalObj())
            {
                auto gv = svfModuleSet->getLLVMValue(memObj->getValue());
                objSpec.objType = gv->getType();
            }
            else
            {
                errs() << "unexpected obj";
                errs() << memObj->toString() << "\n";
            }
        }

        // 计算refCount，只有在不同的API中出现的才算
        auto apiFunc = as->parent->parent->apiFunc;
        bool added = false;
        for (auto i : objSpec.relatedArgs)
        {
            if (apiFunc == i->parent->parent->apiFunc)
                added = true;
        }
        if (!added)
        {
            objSpec.refCount++;
        }

        objSpec.relatedArgs.insert(as);
    }
}

void analysisApiCallSites()
{
    vector<llvm::StringRef> apiFuncNames;
    for (auto &f : *mainModule)
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
        // errs() << "analysis api " << fName << "\n";
        ApiSpec *spec = new ApiSpec();
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
                    CallSiteSpec *css = new CallSiteSpec();
                    css->callSiteId = cg->getCallSiteID(i, node->getFunction());
                    css->inst = (CallInst *)svfModuleSet->getLLVMValue(i->getCallSite());
                    css->parent = spec;
                    spec->callSites.insert(css);
                }
                for (auto i : inEdge->getIndirectCalls())
                {
                    CallSiteSpec *css = new CallSiteSpec();
                    css->callSiteId = cg->getCallSiteID(i, node->getFunction());
                    css->inst = (CallInst *)svfModuleSet->getLLVMValue(i->getCallSite());
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
            // errs() << "analysis callsite: " << *ci << "\n";
            int idx = 0;
            for (auto &arg : ci->args())
            {
                Value *v = arg.get();
                ArgSpec *as = new ArgSpec();
                as->farg = LLVMUtil::getCallee(ci)->arg_begin() + idx;
                as->aarg = v;
                as->parent = css;
                css->argSpecs.push_back(as);
                if (v->getType()->isPointerTy())
                {
                    // nullptr, constantExp
                    if (isa<ConstantPointerNull>(v))
                    {
                        // errs() << "ConstantNullPtr\n";
                    }
                    else
                    {
                        // errs() << "UnknownPtr\n";
                        getCallsiteObjs(as);
                    }
                }
                else if (v->getType()->isIntegerTy())
                {
                    if (isa<ConstantInt>(v))
                    {
                        // errs() << "ConstantInt\n";
                    }
                    else
                    {
                        // errs() << "UnknownInt\n";
                    }
                }
                else
                {
                    // errs() << "unhandled param in callinst: " << *ci << "\n";
                }
                idx++;
            }
            // errs() << "\n";
        }

        apiSpecs.push_back(spec);
    }
}

void showMemObjSpec(MemObjSpec *obj)
{
    auto v = obj->memObj->getValue();
    if (v != nullptr)
    {
        errs() << obj->memObj->toString();
        errs() << "called in: ";
        if (auto inst = dyn_cast<SVFInstruction>(v))
            errs() << inst->getFunction()->getName() << "\n";
        else
            errs() << "not inst\n";
    }
    else
        errs() << "unknown obj?\n";

    errs() << "used by:\n";
    for (auto arg : obj->relatedArgs)
    {
        // errs() << *arg->farg << "\n";
        errs() << *arg->parent->inst << "\n\n";
    }
    errs() << "refCount: " << obj->refCount << "\n\n\n";
}

/*
递归的判断两类型是否相似
1. empty Literal struct type可以匹配任意function type
2. opaque类型可以匹配其他任意类型
3. 其他情况必须严格匹配
 */
bool areTypesIsomorphic(const Type *LTy, const Type *RTy, std::vector<const Type *> &visited)
{
    // errs() << "cp: " << *LTy << " whth " << *RTy << "\n";

    // 如果llvm已经判断两个type相同，我们直接返回即可,大部分简单类型在这一步直接会被过滤
    if (LTy == RTy)
        return true;

    if (const StructType *LSTy = dyn_cast<StructType>(LTy))
    {
        if (LSTy->isLiteral() && LSTy->getStructNumElements() == 0 && RTy->isFunctionTy())
            return true;

        if (LSTy->isOpaque())
            return true;
    }

    if (const StructType *RSTy = dyn_cast<StructType>(RTy))
    {
        if (RSTy->isLiteral() && RSTy->getStructNumElements() == 0 && LTy->isFunctionTy())
            return true;

        if (RSTy->isOpaque())
            return true;
    }

    // Two types with differing kinds are clearly not isomorphic.
    if (LTy->getTypeID() != RTy->getTypeID())
        return false;

    // If the number of subtypes disagree between the two types, then we fail.
    if (RTy->getNumContainedTypes() != LTy->getNumContainedTypes())
        return false;

    // Fail if any of the extra properties (e.g. array size) of the type disagree.
    if (isa<IntegerType>(LTy))
        return false; // bitwidth disagrees.
    if (const PointerType *PT = dyn_cast<PointerType>(LTy))
    {
        if (PT->getAddressSpace() != cast<PointerType>(RTy)->getAddressSpace())
            return false;
    }
    else if (const FunctionType *FT = dyn_cast<FunctionType>(LTy))
    {
        if (FT->isVarArg() != cast<FunctionType>(RTy)->isVarArg())
            return false;
    }
    else if (const StructType *LSTy = dyn_cast<StructType>(LTy))
    {
        const StructType *SSTy = cast<StructType>(RTy);
        if (LSTy->isLiteral() != SSTy->isLiteral() || LSTy->isPacked() != SSTy->isPacked())
            return false;
    }
    else if (auto *DArrTy = dyn_cast<ArrayType>(LTy))
    {
        if (DArrTy->getNumElements() != cast<ArrayType>(RTy)->getNumElements())
            return false;
    }
    else if (auto *DVecTy = dyn_cast<VectorType>(LTy))
    {
        if (DVecTy->getElementCount() != cast<VectorType>(RTy)->getElementCount())
            return false;
    }

    // 如果在我们判断L类型是否等于R类型的过程中，又遇到L类型，我们返回true
    if (std::find(visited.begin(), visited.end(), LTy) == visited.end())
    {
        visited.push_back(LTy);
        for (unsigned I = 0, E = RTy->getNumContainedTypes(); I != E; ++I)
            if (!areTypesIsomorphic(LTy->getContainedType(I), RTy->getContainedType(I), visited))
                return false;
        visited.pop_back();
    }

    return true;
}

bool areTypesEqual(const Type *LTy, const Type *RTy)
{
    std::vector<const Type *> visited;
    // errs() << "cp: " << *LTy << " whth " << *RTy << "\n";
    return areTypesIsomorphic(LTy, RTy, visited);
}

/*
    确定contextObj，可能的情况包括：
        1.mainModule栈上、堆上或全局的对象
        2.libModule堆上的对象
        3.libModule全局的对象(TODO)
    其中除了3以外，Context通常以指针的形式传入API，或作为API的输出
    我们目前考虑的启发式方法：
        1.过滤掉常量memobj
        2.过滤掉在多个API中仅出现过1次的memobj
        3.仅挑选多个API中出现最多的k个memobj
        (TODO).memobj应该是topobj，即其不应该作为其他obj的一部分
        (TODO).memobj的读写仅应该发生在libmodule中（Context对象通常是Opaque的）
        (TODO).如果obj在libModule中的栈上被alloc，则排除其作为Context对象（应该不存在这样的情况？）

    由于SVF的指针分析结果过于粗略，可能存在大量虚假的上下文对象，我们设置一个阈值(API调用次数)，当超过时进行强制筛除，
    找到上下文对象数量明显异常的api，并去除相关的对象

 */
uint64_t contextAnalysis()
{
    set<MemObjSpec *> candidateCtx;
    uint64_t CtxNum = 0;
    //errs() << formatv("Total MemObj {0}\nAfter first filter {1}\n", memObjSet.size(), memObjSpecs.size());
    for (auto &i : memObjSpecs)
    {
        auto &obj = i.second;
        auto ptrType = dyn_cast_or_null<PointerType>(obj.objType);

        if (obj.contentType == ObjContentTypeConstant)
        {
            obj.ctx_id = CtxNum++;
            //errs() << "\tConstant Obj\n";
            continue;
        }
        if (obj.refCount < 2)
        {
            unrelated_filter++;
            //errs() << "\trefCount too small \n";
            continue;
        }
        if (obj.objType == nullptr)
        {
            unrelated_filter++;
            //errs() << "\tunknown ObjType \n";
            continue;
        }

        // errs()<<obj.memObj->toString()<<"\n";
        if (!obj.objType->isPointerTy())
        {
            unrelated_filter++;
            //errs() << "\tnot Pointer Type\n";
            continue;
        }

        if (!ptrType->getPointerElementType()->isStructTy())
        {
            unrelated_filter++;
            //errs() << "\tnot Struct Type \n";
            continue;
        }

        // memobj 被引用的API的arg的type应该与objtype相同，但由于pta结果的不准确性，
        // obj可能被虚假的函数指针参数所引用，只要有1处比较通过，我们就认定其为context obj
        bool typeEqual = false;
        for (auto as : obj.relatedArgs)
        {
            if (areTypesEqual(obj.objType, as->farg->getType()))
            {
                candidateCtx.insert(&obj);
                typeEqual = true;
                break;
            }
            // errs() << "compare fail: " << *as->farg->getType() << " in " << as->parent->parent->apiFunc->getName() << "\n";
        }
        if (typeEqual)
        {
            //errs() << "\tType Equal\n";
        }
        else
        {
            falseObj_filter++;
            //errs() << "\tType Not Equal\n";
        }
    }

    for (auto obj : candidateCtx)
    {
        // errs() << "candidate Context obj:\n";
        // showMemObjSpec(obj);
        obj->contentType = ObjContentTypeContext;
        obj->ctx_id = CtxNum++;
    }
    //errs() << formatv("After second filter {0}\n", CtxNum);
    errs() << formatv("totalObj:{0},falseObj:{1},unrelateObj:{2},ctxObj:{3}\n", memObjSet.size(), falseObj_filter, unrelated_filter, CtxNum);
    return CtxNum;
}

modinfo_struct &getModInfo(GepStmt *gs, MemObjSpec *objSpec)
{
    if (gepModMap.find(gs) != gepModMap.end())
    {
        return gepModMap[gs];
    }

    modinfo_struct ms;
    uint64_t offset;
    uint64_t size;
    const MemObj *memobj = objSpec->memObj;
    if (gs->getAccessPath().gepSrcPointeeType() == nullptr)
    {
        // 这个gep由external api添加，我们暂时无法获得有用的信息
        ms.start = 0;
        ms.end = UINT64_MAX;
        ms.isConstant = false;
        gepModMap[gs] = ms;
        return gepModMap[gs];
    }

    // errs()<<gs->toString()<<"\n";
    const Type *llvmT = svfModuleSet->getLLVMType(gs->getAccessPath().gepSrcPointeeType());
    if (!areTypesEqual(memObjSpecs[memobj].objType->getPointerElementType(), llvmT))
    {
        /*
        如果我们不是最顶层gep，则使用上一层gep（value op0）的start和size,但需要确保上一层gep是合法的：
            1.上一层为gep，如果不是则无法推断该gep的信息（该gep指向了memobj，但我们无法得知其使用了哪一部分）
               ，我们只能标记它为全部：start=0,size=max,且constant为false

               典型情况，struct中包含一个指向其他区域的ptr，为了访问它，首先通过gep 该struct获得 ptr *，之后
               load获得ptr的值，之后将该值用在本次gep中作为value op0
            2.只有一个上一层
            3.祖先gep均为constant,否则本次不再分析而是直接使用最近的非constant gep的值

         */
        SVFVar *prveNode = gs->getRHSVar();
        const Value *prveValue = svfModuleSet->getLLVMValue(prveNode->getValue());
        if (!isa<GetElementPtrInst>(prveValue))
        {
            // errs() << "not gep inst\n";
            ms.start = 0;
            ms.end = UINT64_MAX;
            ms.isConstant = false;
            gepModMap[gs] = ms;
            return gepModMap[gs];
        }

        auto inEdges = prveNode->getIncomingEdges(SVFStmt::Gep);
        assert(inEdges.size() == 1 && "in gep edge not 1?");
        GepStmt *prveGepStmt = dyn_cast<GepStmt>(*inEdges.begin()); // assert
        modinfo_struct &prveInfo = getModInfo(prveGepStmt, objSpec);
        if (prveInfo.isConstant)
        {
            // 上层gep是constant的,使用它初始化我们的信息
            offset = prveInfo.start;
            size = prveInfo.start - prveInfo.end;
        }
        else
        {
            // 如果上层gep不是constant的，直接使用它的信息，因为我们无法基于它再推断出任何信息，此外也将
            // 我们标记为非constant的
            ms = prveInfo;
            gepModMap[gs] = ms;
            return gepModMap[gs];
        }
    }
    else
    {
        // 我们是最顶层gep,不需要获取上层gep信息
        offset = 0;
        size = 0;
    }

    // 获取本层gep信息
    ms.isConstant = gs->isConstantOffset();
    auto idxOperandPairs = gs->getAccessPath().getIdxOperandPairVec();
    for (auto &item : idxOperandPairs)
    {
        if (SVFUtil::isa<SVFConstantInt>(item.first->getValue()))
        {
            // 这一层是constant的，使用它优化start和size信息（start会更大或不变，size会更小或不变）
            const SVFValue *value = item.first->getValue();
            const SVFType *type = item.second;
            assert(type && "this GepStmt comes from ExternalAPI cannot call this api");
            const SVFType *type2 = type;
            const SVFConstantInt *op = SVFUtil::dyn_cast<SVFConstantInt>(value);
            if (const SVFArrayType *arrType = SVFUtil::dyn_cast<SVFArrayType>(type))
            {
                type2 = arrType->getTypeOfElement();
                offset += op->getSExtValue() * type2->getByteSize();
                size = type2->getByteSize();
            }
            else if (SVFUtil::isa<SVFPointerType>(type))
            {
                type2 = gs->getAccessPath().gepSrcPointeeType();
                offset += op->getSExtValue() * type2->getByteSize();
                size = type2->getByteSize();
            }
            else if (const SVFStructType *structType = SVFUtil::dyn_cast<SVFStructType>(type))
            {
                u32_t structField = 0;
                for (; structField < (u32_t)op->getSExtValue(); ++structField)
                {
                    u32_t flattenIdx = structType->getTypeInfo()->getFlattenedFieldIdxVec()[structField];
                    type2 = structType->getTypeInfo()->getOriginalElemType(flattenIdx);
                    offset += type2->getByteSize();
                }
                u32_t flattenIdx = structType->getTypeInfo()->getFlattenedFieldIdxVec()[structField];
                type2 = structType->getTypeInfo()->getOriginalElemType(flattenIdx);
                size = type2->getByteSize();
            }
            else
                assert(false && "unexpected type!");
        }
        else
        {
            // 这一层是非constant的，无法使用它优化start和size信息，并且我们直接退出
            break;
        }
    }
    ms.start = offset;
    ms.end = offset + size;
    gepModMap[gs] = ms;
    return gepModMap[gs];
}

/*
自带的getFlattenFieldTypes有问题, 其对array元素getFlattenFieldTypes返回其元素的type而不是array的
在我们的版本中，typeVec中返回array类型，同时填充null以保持和原版相同个数的Flattenfield
 */
void getTypeVec(const SVFType *baseType, vector<const SVFType *> &typeVec)
{
    // FlattenedFieldIdxVec的元素个数代表了本层struct中元素数量（不展开）
    auto FlattenedFieldIdxVec = baseType->getTypeInfo()->getFlattenedFieldIdxVec();
    for (auto FlattenedFieldId : FlattenedFieldIdxVec)
    {
        auto subT = baseType->getTypeInfo()->getOriginalElemType(FlattenedFieldId);
        if (subT->isStructTy())
        {
            getTypeVec(subT, typeVec);
        }
        else if (subT->isArrayTy())
        {
            typeVec.push_back(subT);
            for (size_t i = 0; i < subT->getTypeInfo()->getNumOfFlattenFields() - 1; i++)
            {
                typeVec.push_back(nullptr);
            }
        }
        else // array , int, pointer...
        {
            typeVec.push_back(subT);
        }
    }
}

modinfo_struct getModInfo(NodeID subNodeId, MemObjSpec *objSpec)
{
    GepObjVar *fieldObj = dyn_cast<GepObjVar>(pag->getGNode(subNodeId));
    const MemObj *baseObj = fieldObj->getMemObj();
    assert(fieldObj);
    APOffset idx = fieldObj->getConstantFieldIdx();
    vector<const SVFType *> FlattenFieldTypes;
    getTypeVec(baseObj->getType(), FlattenFieldTypes);
    /* errs()<<baseObj->getType()->toString()<<"\n";
    for(auto type:FlattenFieldTypes)
    {
        if(type != nullptr)
            errs()<<type->toString()<<"\n";
        else
            errs()<<"nullptr\n";
    }
    errs()<<"==================================\n";
    for(auto type:baseObj->getType()->getTypeInfo()->getFlattenFieldTypes())
    {
        if(type != nullptr)
            errs()<<type->toString()<<"\n";
        else
            errs()<<"nullptr\n";
    } */
    assert(FlattenFieldTypes.size() == baseObj->getType()->getTypeInfo()->getNumOfFlattenFields());

    modinfo_struct ms;
    ms.isConstant = true;

    /*
    某些情况下，idx可能指向了array中某个元素（按理说不应该发生因为array作为一个整体处理了），这种情况下
    我们将其mod范围扩大到整个array
    用lastNotNullIdx记录array的下标，一旦idx指向了array中间使得其值为null，我们就用lastNotNullIdx
    找到对应的array来计算size
    */
    uint64_t lastNotNullIdx = 0;
    for (size_t i = 0; i <= idx; i++)
    {
        if (FlattenFieldTypes[i] != nullptr)
            lastNotNullIdx = i;
    }

    uint64_t start = 0;
    for (size_t i = 0; i < lastNotNullIdx; i++)
    {
        if (FlattenFieldTypes[i] != nullptr)
            start += FlattenFieldTypes[i]->getByteSize();
    }
    ms.start = start;
    ms.end = start + FlattenFieldTypes[lastNotNullIdx]->getByteSize();

    return ms;
}

void revExploreOnCG_all(Value *root, MarkType mt, MemObjSpec *objSpec, NodeID nid)
{
    Function *rootF = nullptr;
    Instruction *inst = nullptr;
    if (inst = dyn_cast<Instruction>(root))
        rootF = inst->getFunction();
    else if (auto arg = dyn_cast<Argument>(root))
        rootF = arg->getParent();

    if (mt == MARK_WRITE)
    {
        /* 每个store类指令我们都尝试找到ptr的范围,如果查询失败则保守标记为全部。
        之后更新本func的信息。在向上探索过程中，会将本func信息更新至上层func信息中

        1.如果dst ptr的类型与memobj类型相容，则标记全部
        2.如果dst ptr的类型与memobj类型不相容（为其子部分），则尝试推断其范围。方法
          包括通过gep查询（当fieldSensitive不可用）或由子obj直接判断

        查询失败可能由于：
        1. dst ptr并非由gep指令产生，可能是load，bitcast，call等产生
        2. dst ptr来自函数实参，需要跨函数分析
         */
        if (areTypesEqual(root->getType(), objSpec->objType))
        {
            // errs() << formatv("wr:{0}:{1} :mark all due to type equal\n", rootF->getName(), *root);
            //  如果dst ptr的类型与memobj类型相容，则标记全部
            funcModMap[rootF][objSpec->ctx_id].start = 0;
            funcModMap[rootF][objSpec->ctx_id].end = UINT64_MAX;
        }
        else if (nid != objSpec->memObj->getId())
        {
            // 由子obj直接判断
            modinfo_struct ms = getModInfo(nid, objSpec);
            // 如果ms的左边界更小，则拓展左边界
            if (ms.start < funcModMap[rootF][objSpec->ctx_id].start)
            {
                funcModMap[rootF][objSpec->ctx_id].start = ms.start;
            }
            // 如果ms的右边界更大，则拓展右边界
            if (ms.end > funcModMap[rootF][objSpec->ctx_id].end)
            {
                funcModMap[rootF][objSpec->ctx_id].end = ms.end;
            }
        }
        else
        {
            // 通过gep查询
            const GetElementPtrInst *gi = dyn_cast_or_null<GetElementPtrInst>(inst);
            if (gi == nullptr)
            {
                // errs() << formatv("wr:{0}:{1} :mark all due to not gep\n", rootF->getName(), *root);
                //  无法推断，我们标记其访问全部
                funcModMap[rootF][objSpec->ctx_id].start = 0;
                funcModMap[rootF][objSpec->ctx_id].end = UINT64_MAX;
            }
            else
            {
                NodeID nodeId = pag->getValueNode(svfModuleSet->getSVFValue(inst));
                auto GepEdges = pag->getGNode(nodeId)->getIncomingEdges(SVFStmt::Gep);
                assert(GepEdges.size() == 1);
                GepStmt *ge = dyn_cast<GepStmt>(*GepEdges.begin());
                modinfo_struct ms = getModInfo(ge, objSpec);

                // 如果ms的左边界更小，则拓展左边界
                if (ms.start < funcModMap[rootF][objSpec->ctx_id].start)
                {
                    funcModMap[rootF][objSpec->ctx_id].start = ms.start;
                }
                // 如果ms的右边界更大，则拓展右边界
                if (ms.end > funcModMap[rootF][objSpec->ctx_id].end)
                {
                    funcModMap[rootF][objSpec->ctx_id].end = ms.end;
                }
            }
        }
    }

    std::set<Function *> visited;
    std::function<void(Function *)> markall = [&](Function *f)
    {
        if (visited.find(f) != visited.end())
            return;
        visited.insert(f);
        auto &callers = GlobalCtx.Callers[f];
        for (auto callinst : callers)
        {
            if (mt == MARK_READ)
                callSiteMarks[callinst][objSpec->ctx_id].isRead = true;
            if (mt == MARK_WRITE)
            {
                callSiteMarks[callinst][objSpec->ctx_id].isWrite = true;
                Function *upperF = callinst->getFunction();

                if (funcModMap[f][objSpec->ctx_id].start < funcModMap[upperF][objSpec->ctx_id].start)
                {
                    funcModMap[upperF][objSpec->ctx_id].start = funcModMap[f][objSpec->ctx_id].start;
                }
                if (funcModMap[f][objSpec->ctx_id].end > funcModMap[upperF][objSpec->ctx_id].end)
                {
                    funcModMap[upperF][objSpec->ctx_id].end = funcModMap[f][objSpec->ctx_id].end;
                }
            }
            if (mt == MARK_MALLOC)
                callSiteMarks[callinst][objSpec->ctx_id].isMalloc = true;
            markall(callinst->getFunction());
        }
    };

    assert(rootF != nullptr);
    markall(rootF);
}

void exploreLoop(Value *root)
{
    for (auto user : root->users())
    {
        Instruction *ins = dyn_cast<Instruction>(user);
        DominatorTree *dt = new DominatorTree(*ins->getFunction());
        LoopInfo *li = new LoopInfo(*dt);
        Loop *lp = li->getLoopFor(ins->getParent());
        while (lp != nullptr)
        {
            loopMarks.insert(lp);
            lp = lp->getParentLoop();
        }
    }
}

void exploreMalloc(Value *root, MemObjSpec *objSpec)
{
    Instruction *ins = dyn_cast<Instruction>(root);
    Metadata *MDIdx = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), objSpec->ctx_id));
    dyn_cast<CallInst>(ins)->setMetadata("context", MDNode::get(*ctx, MDIdx));
}
/*
根据对memobj的引用，找出所有读写和分配相关的指令
 */
void getRalatedUsers(NodeID objId, vector<pair<Value *, MarkType>> *relatedUsers, ObjAllocType allocType)
{
    for (auto stmt : pag->getSVFStmtSet(SVFStmt::Load))
    {
        auto pts = pta->getPts(stmt->getSrcID());
        if (pts.test(objId))
        {
            Value *v = (Value *)svfModuleSet->getLLVMValue(stmt->getSrcNode()->getValue());
            assert(v != nullptr);
            relatedUsers->push_back(pair<Value *, MarkType>(v, MARK_READ));
            /*             if (objId == 68948)
                        {
                            errs() << stmt->getBB()->getFunction()->toString() << "\n";
                            errs() << stmt->toString() << "\n\n";
                        } */
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
            Value *v = (Value *)svfModuleSet->getLLVMValue(stmt->getDstNode()->getValue());
            assert(v != nullptr);
            relatedUsers->push_back(pair<Value *, MarkType>(v, MARK_WRITE));
            /*             if (objId == 68948)
                        {
                            errs() << stmt->getBB()->getFunction()->toString() << "\n";
                            errs() << stmt->toString() << "\n\n";
                        } */
        }
    }
    for (auto &func : *module)
    {
        // 目前我们仅对外部函数和intrinsic函数进行mod分析：将所有指向memobj的ptr标记为write
        if (func.isDeclaration() || func.isIntrinsic())
        {
            auto &callers = GlobalCtx.Callers[&func];
            for (auto callinst : callers)
            {
                for (size_t i = 0; i < callinst->arg_size(); i++)
                {
                    Value *arg = callinst->getArgOperand(i);
                    if (!arg->getType()->isPointerTy())
                        continue;

                    NodeID id = pag->getValueNode(svfModuleSet->getSVFValue(arg));
                    auto pts = pta->getPts(id);
                    if (pts.test(objId))
                    {
                        // errs()<<formatv("mark {0} with arg {1}\n",func.getName(),i);
                        relatedUsers->push_back(pair<Value *, MarkType>(arg, MARK_WRITE));
                    }
                }
            }
        }
    }

    if (allocType == ObjAllocInLibModuleHeap)
    {
        for (auto stmt : pag->getSVFStmtSet(SVFStmt::Addr))
        {
            auto pts = pta->getPts(stmt->getDstID());
            if (pts.test(objId))
            {
                Value *v = (Value *)svfModuleSet->getLLVMValue(stmt->getDstNode()->getValue());
                assert(v != nullptr);
                relatedUsers->push_back(pair<Value *, MarkType>(v, MARK_MALLOC));
                /*                 if (objId == 68948)
                                {
                                    errs() << stmt->getBB()->getFunction()->toString() << "\n";
                                    errs() << stmt->toString() << "\n\n";
                                } */
            }
        }
    }
    // errs() << "get related users for nodeId: " << objId << " user count: " << relatedUsers->size() << "\n";
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
    vector<pair<Value *, MarkType>> toDolist;
    for (auto &i : memObjSpecs)
    {
        auto &objSpec = i.second;
        if (objSpec.contentType == ObjContentTypeContext)
        {
            // errs() << "mark callsite for ctx " << objSpec.ctx_id << "\n";
            for (auto id : objSpec.allIds)
            {
                getRalatedUsers(id, &toDolist, objSpec.allocType);
                while (toDolist.size())
                {
                    auto current = toDolist.back();
                    toDolist.pop_back();
                    Value *root = current.first;
                    MarkType mt = current.second;
                    if (mt == MARK_MALLOC)
                    {
                        revExploreOnCG_all(root, MARK_MALLOC, &objSpec, id);
                        exploreMalloc(root, &objSpec);
                    }
                    else if (mt == MARK_READ)
                    {
                        revExploreOnCG_all(root, MARK_READ, &objSpec, id);
                        exploreLoop(root);
                    }
                    else if (mt == MARK_WRITE)
                    {
                        revExploreOnCG_all(root, MARK_WRITE, &objSpec, id);
                        exploreLoop(root);
                    }
                    else
                        assert(false && "unexpected user type!");
                }
            }
        }
        else if (objSpec.contentType == ObjContentTypeConstant)
        {
            /*
            我们有一个constant的memobj，以及与其相关的formalin（这些formalin位于api的caller中）
            现在我们寻找整个程序中对这个memobj的use，并标记这些use实际到达formalin的路径（SVFG是context-insensitive的
            ，所以存在虚假路径），这些use最终都会追溯到formalin，我们关注的是路径而不是结果

            对于consantobj来说，不存在store的use，因此所有的load节点都可以追溯到formalin，但并不一定是1个。
            如果在mainModule的两个函数中都调用api且提供相同的常量对象，formalin就会有两个

            */
            // showMemObjSpec(&objSpec);
            // errs() << "mark callsite for ctx " << objSpec.ctx_id << "\n";
            for (auto id : objSpec.allIds)
            {
                getRalatedUsers(id, &toDolist, objSpec.allocType);
                while (toDolist.size())
                {
                    auto current = toDolist.back();
                    toDolist.pop_back();
                    Value *root = current.first;
                    MarkType mt = current.second;
                    if (mt == MARK_READ)
                    {
                        revExploreOnCG_all(root, MARK_READ, &objSpec, id);
                        exploreLoop(root);
                    }
                }
            }
        }
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
int main(int argc, char **argv)
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

    // pta = FlowSensitive::createFSWPA(pag);
    pta = AndersenWaveDiff::createAndersenWaveDiff(pag);

    /*     uint64_t total = 0;
        uint64_t var = 0;
        for(auto stmt:pag->getSVFStmtSet(SVFStmt::Store))
        {
            auto pts = pta->getPts(stmt->getDstID());
            if (!pts.test(9687))
                continue;
            total++;
            const Value *llvmV = svfModuleSet->getLLVMValue(stmt->getDstNode()->getValue());
            if (!isa<GetElementPtrInst>(llvmV))
            {
                var++;
                errs()<<*llvmV<<"\n";
            }

        }
        errs()<<formatv("total:{0},var:{1}\n",total,var); */

    cg = pta->getPTACallGraph();

    StringRef MName = StringRef(linkedPath());
    GlobalCtx.Modules.push_back(std::make_pair(module, MName));
    GlobalCtx.ModuleMaps[module] = MName;

    CallGraphPass CGPass(&GlobalCtx);
    CGPass.run(GlobalCtx.Modules);

    analysisApiCallSites();
    uint64_t ctxNum = contextAnalysis();
    if (ctxNum == 0)
    {
        errs() << "no Context object found\n";
        return 0;
    }

    for (Function &f : *module)
    {
        for (BasicBlock &b : f)
        {
            for (Instruction &i : b)
            {
                if (CallInst *callinst = dyn_cast<CallInst>(&i))
                {
                    for (size_t i = 0; i < ctxNum; i++)
                    {
                        callSiteMarks[callinst].push_back({i, false, false, false});
                    }
                }
            }
        }
        if (!f.isDeclaration())
        {
            for (size_t i = 0; i < ctxNum; i++)
            {
                funcModMap[&f][i].start = UINT64_MAX;
                funcModMap[&f][i].end = 0;
            }
        }
    }

    markCallSites();

    for (auto item : callSiteMarks)
    {
        //! csm = !{{ctxId,isRead,isWrite,isMalloc},{ctxId,isRead,isWrite,isMalloc},...}
        CallInst *callinst = item.first;
        Metadata *MDFalse = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), 0));
        Metadata *MDTrue = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), 1));
        vector<Metadata *> mds;
        for (csm_struct csm : item.second)
        {
            vector<Metadata *> smds;
            Metadata *MDIdx = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), csm.ctx_id));
            smds.push_back(MDIdx);
            if (csm.isRead)
                smds.push_back(MDTrue);
            else
                smds.push_back(MDFalse);
            if (csm.isWrite)
                smds.push_back(MDTrue);
            else
                smds.push_back(MDFalse);
            if (csm.isMalloc)
                smds.push_back(MDTrue);
            else
                smds.push_back(MDFalse);

            mds.push_back(MDTuple::get(*ctx, smds));
        }
        MDTuple *MDCSM = MDTuple::getDistinct(*ctx, mds);
        callinst->setMetadata("csm", MDCSM);
    }

    for (Loop *lp : loopMarks)
    {
        Instruction &firstInst = *lp->getHeader()->getInstList().begin();
        MDNode *MDTrue = MDNode::get(*ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), 1)));
        firstInst.setMetadata("context_loop", MDTrue);
    }

    // !mdinfo = !{{ctxId,start,end},{ctxId,start,end},...}
    for (auto item : funcModMap)
    {
        Function *func = const_cast<Function *>(item.first);

        map<uint64_t, modinfo_struct> &modInfos = item.second;
        vector<Metadata *> mds;

        for (auto modinfoPair : modInfos)
        {
            uint64_t ctx_id = modinfoPair.first;
            modinfo_struct ms = modinfoPair.second;
            vector<Metadata *> smds;
            Metadata *MDIdx = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), ctx_id));
            Metadata *MDStart = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), ms.start));
            Metadata *MDEnd = ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(*ctx), ms.end));
            smds.push_back(MDIdx);
            smds.push_back(MDStart);
            smds.push_back(MDEnd);
            mds.push_back(MDTuple::get(*ctx, smds));
            /*             if (ms.start == UINT64_MAX && ms.end == 0)
                            errs() << formatv("{0} ctxid:{1}, not write\n", func->getName(), ctx_id);
                        else if (ms.start == 0 && ms.end == UINT64_MAX)
                            errs() << formatv("{0} ctxid:{1}, mark all\n", func->getName(), ctx_id);
                        else
                            errs() << formatv("{0} ctxid:{1},start:{2},end:{3}\n", func->getName(), ctx_id, ms.start, ms.end); */
        }

        MDTuple *MDCSM = MDTuple::getDistinct(*ctx, mds);
        func->setMetadata("mdinfo", MDCSM);
    }
    std::error_code ec;
    raw_fd_ostream OS(outputPath(), ec);
    if (!verifyModule(*module, &errs()))
    {
        WriteBitcodeToFile(*module, OS);
    }
}

/*
SVFGNode *getSvfgNode(Value *v)
{
    return svfg->getSVFGNode(pag->getValueNode(svfModuleSet->getSVFValue(v)));
}

FormalINSVFGNode *getFin(NodeID nId, SVFG::FormalINSVFGNodeSet &formalIns)
{
    FormalINSVFGNode *res = nullptr;
    for (auto id : formalIns)
    {
        auto formalIn = dyn_cast<FormalINSVFGNode>(svfg->getSVFGNode(id));
        for (auto oid : formalIn->getPointsTo())
            if (oid == nId)
            {
                if (res != nullptr)
                    errs() << "error: nId in multi fins\n";
                res = formalIn;
            }
    }
    return res;
}
 */

/*
每当探索到一个callsite时，检查在当前的ContextCond条件下，
目标指针是否依然指向该memRegion，如果否就不再继续

注意：mR和cpts中保存的只有初始obj的id，如果obj在过程中被def成为常量（比如常量obj
拷贝到另一个obj），则存在潜在的可能，在另一条非def为常量的路径上，checkCallContext返回
true，因为contextPta只计算了初始obj，而不是memSSA rename之后的


DDAClient *ddaClient;
ContextDDA *cpta;

ContextCond currentCtx;
SVFGNode *targetFin;
NodeID targetNodeId;
NodeID userPtr;

bool checkCallContext(CallSiteID cId)
{
    if (!useContextSearchOnSVFG)
        return true;
    CxtVar var(currentCtx, userPtr);
    bool res = false;
    const CxtPtSet &cpts = cpta->computeDDAPts(var);
    for (auto t : cpts)
        if (targetNodeId == t.get_id())
        {
            res = true;
            break;
        }

    //errs() << "checking call in " << cg->getCallSite(cId)->getCallSite()->getFunction()->toString() << "res: " << res << "\n";
    return res;
}
 */

/*
obj被在main里的FIN被第一次define，之后在多个地方被def和use（统一为user），
对每一个user（store、load），存在指向该obj的ptr。我们需要所有的user都被常量传播
执行到，因此从user开始，向上探索直到main中的fin，沿途标记所有的callsite。
一个问题是，SVFG是context-insensitive的，因此会回溯到并未真正传递obj的callsite，所以
我们通过DDA来判断：当前的callsite下，如果ptr仍然能指向obj，我们就继续回溯，否则判断为虚假的
边，我们不再继续搜索。
注：
1.我们需要先在当前函数内探索完所有的节点，如果没有到达，我们再继续跨函数寻找

2.遇到ActualOUTSVFGNode，代表我们到达当前函数的fin（该obj在当前函数中的初始版本）前，
该obj被def。此时我们不进入def函数，继续搜索(如果只有fin-def-use一条路线，我们会发现找不到fin，
这并没有关系，在探索def对应user时，会接续未完成的探索直到main函数)。

if (useContextSearchOnSVFG)
{
    // CxtBudget = 1000
    ContextCond::setMaxCxtLen(maximumCxtLen);
    ddaClient = new DDAClient(svfModuleSet->getSVFModule());
    ddaClient->initialise(svfModuleSet->getSVFModule());
    cpta = new ContextDDA(pag, ddaClient);
    cpta->initialize();
}

string ctx2csm(void)
{
    SmallVector<char, 1024> sv;
    raw_svector_ostream SO(sv);
    SO << "{";
    for (auto ctx : currentCtx)
    {
        auto svfIns = cg->getCallSite(ctx)->getCallSite();
        auto callIns = dyn_cast<CallInst>(svfModuleSet->getLLVMValue(svfIns));
        auto num =
            mdconst::extract<ConstantInt>(callIns->getMetadata("csm")->getOperand(0))->getValue().getLimitedValue();
        SO << num << " ";
    }
    SO << "}\n";
    return SO.str().str();
}

bool revExploreOnSVFG(SVFGNode *root)
{
    assert(root);
    bool result = false;
    set<SVFGNode *> fins;
    vector<SVFGNode *> worklist;
    set<SVFGNode *> visited;
    worklist.push_back(root);
    // errs() << "we are in " << root->getFun()->getName() << ", ctx: " << ctx2csm() << "\n";
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        if (!visited.insert(current).second)
            continue;
        for (auto edge : current->getInEdges())
        {
            if (isa<IntraIndSVFGEdge>(edge))
            {
                auto srcNode = edge->getSrcNode();
                if (SVFUtil::isProgEntryFunction(root->getFun())) //(srcNode == targetFin)
                {
                    result = true;
                    // errs() << "find target node\n";
                    goto out;
                }
                else if (isa<FormalINSVFGNode>(srcNode))
                    fins.insert(srcNode);
                else
                    worklist.push_back(srcNode);
            }
        }
    }

    for (auto srcNode : fins)
    {
        for (auto edge : srcNode->getInEdges())
        {
            // 如果回溯到main，会存在global到main的fin对象，且edge为IntraIndSVFGEdge
            if (auto callEdge = dyn_cast<CallIndSVFGEdge>(edge))
            {
                auto cId = callEdge->getCallSiteId();
                bool markCallsite = false;
                //如果存在递归，我们跳过这条边
                if (currentCtx.containCallStr(cId))
                    continue;
                currentCtx.getContexts().insert(currentCtx.begin(), cId);
                if (currentCtx.cxtSize() >= maximumCxtLen)
                    errs() << "context stackoverflow!\n ";
                if (checkCallContext(cId))
                {

                    // errs() << "last fin: " << dyn_cast<FormalINSVFGNode>(srcNode)->toString() << "\n";
                    auto n = dyn_cast<ActualINSVFGNode>(edge->getSrcNode());
                    markCallsite = revExploreOnSVFG(n);
                }
                else
                    currentCtx.getContexts().erase(currentCtx.begin());

                //如果结果为true，说明这条路径的确对应memobj的移动，我们标记这个callsite
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
    }

out:
    if (currentCtx.cxtSize())
    {
        currentCtx.getContexts().erase(currentCtx.begin());
        // errs() << "normal out!"<< " ctx: " << currentCtx.toString() << "\n";
    }
    else
    {
        // errs() << "top out!\n\n";
    }
    return result;
}

*/

/*
在CallGraph上标记main到达某inst（call、load、store）的所有callsite

使用nodestack保存还未探索的邻接点，这使得算法不再是递归的
使用currentPath保存当前探索到的路径。如果当前点为main就输出当前路径作为一个结果

上下文不敏感：
currentPath中，两个节点之间可能存在多个callsite，因此需要mark所有callsite

上下文敏感：
使用一个callsite序列作为上下文，判断目标指针是否仍能够指向context obj，如果不能就
排除该路径。需要对currentPath进行处理，多个callsite会fork出多个路径
std::vector<const PTACallGraphNode*> currentPath;
int pathCounter;
void dfs(PTACallGraphNode* node)
{
    currentPath.push_back(node);
    if (SVFUtil::isProgEntryFunction(node->getFunction()))
    {
        // markedCallInst.insert(ci);
        pathCounter++;
        //for (auto n : currentPath)
        //    errs() << n->getFunction()->getName() << "\n";
    }
    else
    {
        for (auto it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
        {
            PTACallGraphNode* srcNode = (*it)->getSrcNode();
            if (find(currentPath.begin(), currentPath.end(), srcNode) == currentPath.end())
                dfs(srcNode);
        }
    }
    currentPath.pop_back();
}

void revExploreOnCG(SVFGNode* root)
{
    auto inst = dyn_cast<SVFInstruction>(root->getValue());
    auto Func = inst->getFunction();
    auto initNode = cg->getCallGraphNode(Func);
    pathCounter = 0;
    dfs(initNode);
    errs()<<"find "<< pathCounter << " path\n";
}
 */

/* int pathCounter;
std::vector<CallInst *> currentPath;
void dfs(CallInst *ci)
{
    currentPath.push_back(ci);
    Function *f = ci->getFunction();
    if (f->getName() == "main")
    {
        pathCounter++;
    }
    else
    {
        auto &callers = GlobalCtx.Callers[f];
        for (auto callinst : callers)
        {
            markedCallInst.insert(callinst);
            if (find(currentPath.begin(), currentPath.end(), callinst) == currentPath.end())
                dfs(callinst);
        }
    }
    currentPath.pop_back();
}

void revExploreOnCG(SVFGNode *root)
{
    pathCounter = 0;
    auto inst = dyn_cast<SVFInstruction>(root->getValue());
    const Function *f = dyn_cast<const Function>(svfModuleSet->getLLVMValue(inst->getFunction()));
    // errs()<<"start from: "<<f->getName()<<"\n";
    auto &callers = GlobalCtx.Callers[(Function *)f];
    for (auto callinst : callers)
    {
        markedCallInst.insert(callinst);
        dfs(callinst);
    }
    // errs()<<"find "<< pathCounter << " path\n";
} */

/*
void getTypeVec(const SVFType* baseType, vector<const SVFType*>& typeVec, u32_t& FieldIdxRemain)
{
   auto FlattenedFieldIdxVec = baseType->getTypeInfo()->getFlattenedFieldIdxVec();
   for (auto i : FlattenedFieldIdxVec)
   {

       auto subT = baseType->getTypeInfo()->getOriginalElemType(i);
       if (FieldIdxRemain >= subT->getTypeInfo()->getNumOfFlattenFields())
       {
           typeVec.emplace_back(subT);
           FieldIdxRemain -= subT->getTypeInfo()->getNumOfFlattenFields();
       }
       else
       {
           getTypeVec(subT, typeVec, FieldIdxRemain);
       }

       if (FieldIdxRemain == 0)
           break;
   }
}

SVFType* getLastField(const SVFType* baseType)
{
   auto fieldNum = baseType->getTypeInfo()->getNumOfFlattenFields();
   auto FlattenedFieldIdxVec = baseType->getTypeInfo()->getFlattenedFieldIdxVec();
   if (fieldNum == 1)
       return (SVFType*)baseType;
   return getLastField(baseType->getTypeInfo()->getOriginalElemType(FlattenedFieldIdxVec.back()));
}

 //由于field被展开了，Obj对应展开的最小单位。
void getObjFieldInfo(NodeID objId, uint64_t& offset, uint64_t& size)
{
   auto node = pag->getGNode(objId);
   if (auto gepNode = dyn_cast<GepObjVar>(node))
   {
       auto ls = gepNode->getLocationSet();
       if (ls.isConstantOffset())
       {
           vector<const SVFType*> typeVec;
           auto fieldIdxRemain = (u32_t)ls.getConstantFieldIdx() + 1;
           auto objStructType =
               dyn_cast<PointerType>(memObjSpecs[gepNode->getMemObj()].objType)->getPointerElementType();
           const SVFType* baseType = svfModuleSet->getSVFType(objStructType);
           getTypeVec(baseType, typeVec, fieldIdxRemain);
           for (auto i : typeVec)
           {
               offset += DL->getTypeAllocSize((llvm::Type*)svfModuleSet->getLLVMType(i));
           }
           auto lastField = getLastField(typeVec.back());
           size = DL->getTypeAllocSize((llvm::Type*)svfModuleSet->getLLVMType(lastField));
           offset -= size;
       }
       else
           errs() << "no constant offset\n";
   }
}

       for (auto& i : func2WriteObj)
       {
           auto srcFunc = svfModuleSet->getSVFFunction(i.first);
           // errs()<<i.first->getName()<<"\n";
           auto& srcSet = i.second;
           for (auto& j : func2WriteObj)
           {
               auto dstFunc = svfModuleSet->getSVFFunction(j.first);
               auto& dstSet = j.second;
               if (srcFunc != dstFunc && cg->isReachableBetweenFunctions(srcFunc, dstFunc))
               {
                   // errs()<<"\tadd subfunc: "<<j.first->getName()<<"\n";
                   for (auto objId : dstSet)
                       srcSet.insert(objId);
               }
           }
       }
       raw_fd_ostream fd_fw("fmi.txt", ec);
       for (auto& func2obj : func2WriteObj)
       {
           fd_fw << "f:"<<func2obj.first->getName() << "\n";
           for (auto& i : memObjSpecs)
           {
               auto& obj = i.second;
               if (obj.contentType == ObjContentTypeContext)
               {
                   auto value = svfModuleSet->getLLVMValue(obj.memObj->getValue());
                   if (auto I = dyn_cast<Instruction>(value))
                   {
                       auto num = mdconst::extract<ConstantInt>(I->getMetadata("csm")->getOperand(0))
                                      ->getValue()
                                      .getLimitedValue();
                       fd_fw << "c:" << num << " ";
                   }
                   else
                       errs()<<"TODO: global context obj\n";
                   for (auto& objId : func2obj.second)
                   {
                       if (pag->getObject(objId) == obj.memObj)
                       {
                           uint64_t offset = 0;
                           uint64_t size = 0;
                           getObjFieldInfo(objId, offset, size);
                           fd_fw << offset << ":" << size << " ";
                       }
                   }
                   fd_fw << "\n";
               }
           }
       }

    */

/*
我们这里标记新产生的ConstantObj，注意我们不希望引入太多的对象，这可能导致常量传播无法完成。新对象的来源有两种：
    TODO: 1.如果这次use是库函数（memcpy、strcpy等），而且被svf建模
    TODO: 2.如果这次use是load出scalar，我们需要看看其是否被store到另一个memobj（这部分在处理API的scalar常量参数时也会用到）
void markNewConstantObj(StmtVFGNode* user,vector<tuple<ObjContentType, SVF::SVFGNode*, std::set<SVF::StmtVFGNode*>*>>&
worklist);
 */

/*
对于heap malloc的obj，需要保证其分配函数也被常量传播框架所执行。考虑两种情况，ret和二级指针(TODO)，
前者将obj的ptr以返回值形式返回，而后者通过设置参数中的二级指针来完成
通过追踪direct边，直到命中store指令
void ExplorePtr(SVFGNode* root)
{
    vector<SVFGNode*> worklist;
    set<SVFGNode*> visited;
    set<SVFGNode*> frets;

    worklist.push_back(root);
    errs() << "we are in " << root->getFun()->getName() << "\n";
    while (worklist.size())
    {
        auto current = worklist.back();
        worklist.pop_back();
        if (!visited.insert(current).second)
            continue;
        for (auto edge : current->getOutEdges())
        {
            if (isa<IntraDirSVFGEdge>(edge))
            {
                auto dstNode = edge->getDstNode();
                if (isa<StoreSVFGNode>(dstNode))
                {
                    errs() << "reach store node\n";
                    errs() << dstNode->toString() << "\n";
                    errs() << "in: "<<dyn_cast<SVFInstruction>(dstNode->getValue())->getFunction()->getName()<<"\n";
                }
                else if (isa<FormalRetSVFGNode>(dstNode))
                    frets.insert(dstNode);
                else
                    worklist.push_back(dstNode);
            }
        }
    }

    for (auto fret : frets)
    {
        for (auto edge : fret->getOutEdges())
        {
            if (auto callEdge = dyn_cast<CallDirSVFGEdge>(edge))
            {
                auto cId = callEdge->getCallSiteId();
                auto svfCs = svfg->getCallSite(cId)->getCallSite();
                auto ci = dyn_cast<CallInst>(svfModuleSet->getLLVMValue(svfCs));
                assert(ci);
                markedCallInst.insert(ci);
                auto n = dyn_cast<ActualRetSVFGNode>(edge->getDstNode());
                ExplorePtr(n);
            }
        }
    }
} */