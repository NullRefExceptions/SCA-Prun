#include "llvm/IR/LLVMContext.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/FormatVariadic.h"

#include "iostream"
#include "fstream"
#include "set"
#include "string"
#include <sstream>

using namespace llvm;

cl::opt<std::string> libPath(cl::Positional, cl::desc("input bitcode file"));
cl::opt<std::string> action("a", cl::desc("action"));
cl::opt<std::string> output("o", cl::desc("output path"));
cl::opt<std::string> strFile("str", cl::init(""), cl::desc("path to lib api string"));
Module *module;
std::set<Function *> apiFuncs;
std::set<Function *> callerFuncs;

void printInfo()
{
    bool addressTaken = false;
    for (Function *api : apiFuncs)
    {
        if (api->hasAddressTaken() == true)
        {
            addressTaken = true;
            break;
        }
    }

    outs() << formatv("apiCount:{0},callerSize:{1},addrTaker:{2}\n", apiFuncs.size(), callerFuncs.size(), addressTaken);
}

// 直接删掉除callFuncs，和api函数之外的所有函数，将callfunc中调用的其他函数定义为external，之后直接分析
// 函数中引用全局变量，除非是readonly，否则应当想办法设定成非常量
void fastAnalysis(Function *callFunc)
{
    ValueToValueMapTy VMap;
    std::function<bool(const GlobalValue *gv)> filter = [callFunc](const GlobalValue *gv)
    {
        if (isa<Function>(gv))
        {
            return gv == callFunc;
        }
        else if (isa<GlobalVariable>(gv))
        {
            return true;
        }
        return false;
    };

    std::unique_ptr<Module> mP = CloneModule(*module, VMap, filter);
    Module *m = mP.get();

    // 修改callFunc名称为main
    if (callFunc->getName() != "main")
    {
        Function *main = m->getFunction("main");
        if (main != nullptr)
        {
            main->eraseFromParent();
        }
        Function *newCallFunc = dyn_cast<Function>(VMap[callFunc]);
        newCallFunc->setName("main");
    }

    for (GlobalValue &gv : m->global_values())
    {
        auto lt = gv.getLinkage();
        if (lt == GlobalValue::LinkageTypes::PrivateLinkage || lt == GlobalValue::LinkageTypes::InternalLinkage)
        {
            gv.setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
        }
    }

    if (!verifyModule(*m, &errs()))
    {
        std::error_code ec;
        raw_fd_ostream OS(output, ec);
        WriteBitcodeToFile(*m, OS);
        outs() << formatv("write to {0}\n", output);
    }
}

/*
精简原module，仅保留与api调用相关的代码
首先找到所有参与调用api的函数，定义为callerFuncs，所有调用api的指令，定义为call
 */
int main(int argc, char **argv)
{
    cl::ParseCommandLineOptions(argc, argv, "tiny anlysis");
    LLVMContext ctxs;
    SMDiagnostic Err;
    std::unique_ptr<Module> mP;

    mP = parseIRFile(libPath, Err, ctxs);
    module = mP.get();
    std::string apiString;
    const char *sf = strFile.c_str();
    const char *lp = libPath.c_str();
    if (strFile == "")
    {
        std::cin >> apiString;
    }
    else
    {
        std::fstream inFile(strFile);
        inFile >> apiString;
    }

    if (module == nullptr || apiString.empty())
    {
        outs() << "param error\n";
        return -1;
    }
    std::stringstream ss(apiString);
    std::string item;

    while (std::getline(ss, item, ':'))
    {
        Function *f = module->getFunction(item);
        if (f == nullptr)
            continue;
        apiFuncs.insert(f);
        for (User *user : f->users())
        {
            if (auto ins = dyn_cast<CallBase>(user))
                callerFuncs.insert(ins->getFunction());
        }
    }

    if (action == "t")
    {
        if (callerFuncs.size() == 1)
            fastAnalysis(*callerFuncs.begin());
        else
            errs() << "too many caller func\n";
    }

    if (action == "p")
        printInfo();

    return 0;
}