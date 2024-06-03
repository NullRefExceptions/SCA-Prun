#include "llvm/IR/LLVMContext.h"
#include "llvm/Pass.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Analysis/ConstantFolding.h"
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
cl::opt<std::string> outputDir("outDir", cl::init("tinyOutput"), cl::desc("output dir"));

Module *module;
std::set<Function *> apiFuncs;
std::set<Function *> callerFuncs;
std::set<Instruction *> userSet;

std::set<Function *> reservedSet;
std::set<Function *> wrapperSet;

enum UserGraphNodeType
{
    loop,
    normal
};

struct UserGraphNode
{
    SmallVector<UserGraphNode *> successors;
    BasicBlock *data = nullptr;
    UserGraphNodeType type = UserGraphNodeType::normal;
};

class UserGraph
{
    /*
    从原来的函数中提取api的callinst，并连接起来：
        保证其拥有和原来一样的控制流结构
        尽量还原def-use链
     */
private:
    UserGraphNode *root;
    LoopInfo *li;
    DominatorTree *dt;
    std::set<BasicBlock *> userBasicSet;
    std::set<Instruction *> userSet;
    std::set<UserGraphNode *> nodes;
    friend struct GraphTraits<UserGraph *>;
    friend struct DOTGraphTraits<UserGraph *>;

public:
    UserGraph(Function *func, std::set<Instruction *> userSet)
    {
        root = new UserGraphNode();
        this->nodes.insert(root);

        dt = new DominatorTree(*func);
        li = new LoopInfo(*dt);
        this->userSet = userSet;

        std::set<BasicBlock *> tmpuserBasicSet;
        for (Instruction *ins : userSet)
        {
            tmpuserBasicSet.insert(ins->getParent());
        }
        this->userBasicSet = tmpuserBasicSet;

        // 寻找root节点，我们不把函数的入口节点作为root节点
        while (tmpuserBasicSet.size() != 1)
        {
            auto it = tmpuserBasicSet.begin();
            BasicBlock *a = *it;
            BasicBlock *b = *(++it);
            tmpuserBasicSet.erase(a);
            tmpuserBasicSet.erase(b);
            tmpuserBasicSet.insert(dt->findNearestCommonDominator(a, b));
        }

        std::vector<BasicBlock *> path;

        std::function<void()> dumpPath = [&path]()
        {
            errs() << "path: ";
            for (BasicBlock *it : path)
            {
                it->printAsOperand(errs());
                errs() << "==> ";
            }
            errs() << "END\n";
        };

        std::function<void()> onExit = [&]()
        {
            addPath(path);
        };

        std::function<void(BasicBlock * root)> travel = [&](BasicBlock *root)
        {
            // 不应该出现循环
            assert(std::find(path.begin(), path.end(), root) == path.end());

            // 如果root是loopheader，我们将loop看作整个整体，从exit接着出发向下
            if (li->isLoopHeader(root))
            {
                path.push_back(root);
                Loop *loop = li->getLoopFor(root);
                SmallVector<BasicBlock *> exitBlocks;
                loop->getExitBlocks(exitBlocks);
                size_t numSucc = exitBlocks.size();
                if (numSucc == 0)
                {
                    onExit();
                }
                else
                {
                    for (BasicBlock *exitBlock : exitBlocks)
                    {
                        travel(exitBlock);
                    }
                }
            }
            else
            {
                path.push_back(root);
                Instruction *terminator = root->getTerminator();
                size_t numSucc = terminator->getNumSuccessors();
                if (numSucc == 0)
                {
                    onExit();
                }
                else
                {
                    for (size_t i = 0; i < numSucc; i++)
                    {
                        travel(terminator->getSuccessor(i));
                    }
                }
            }
            path.pop_back();
        };

        travel(*tmpuserBasicSet.begin());
    }

    ~UserGraph() {}

    /*
    注意！其提供的path中，第一个node为root节点，需要跳过！
     */
    void iteratePath(std::function<void(std::vector<UserGraphNode *> &)> &action)
    {
        std::vector<UserGraphNode *> path;
        std::function<void(UserGraphNode *)> travel = [&](UserGraphNode *node)
        {
            path.push_back(node);
            if (node->successors.size() == 0)
            {
                action(path);
            }
            for (UserGraphNode *child : node->successors)
            {
                travel(child);
            }
            path.pop_back();
        };
        travel(root);
    }

    void addPath(std::vector<BasicBlock *> &path)
    {
        // 添加该path，并且略过非user节点。这可能使得root实际上为森林
        UserGraphNode *parent = root;
        for (BasicBlock *b : path)
        {
            assert(parent != nullptr);
            if (userBasicSet.find(b) == userBasicSet.end())
                continue;
            // 找到或创建一个对应该bb的node
            UserGraphNode *next = nullptr;
            for (UserGraphNode *node : nodes)
            {
                if (node->data == b)
                {
                    next = node;
                    break;
                }
            }
            if (next == nullptr)
            {
                next = new UserGraphNode();
                this->nodes.insert(next);
                next->data = b;
                if (li->isLoopHeader(b))
                {
                    next->type = UserGraphNodeType::loop;
                }
            }
            assert(next != nullptr);
            // 添加parent->node的关系
            if (std::find(parent->successors.begin(), parent->successors.end(), next) == parent->successors.end())
            {
                parent->successors.push_back(next);
            }
            parent = next;
        }
    }

    size_t getPathNum()
    {
        size_t num = 0;
        std::function<void(std::vector<UserGraphNode *> &)> action = [&num](std::vector<UserGraphNode *> &path)
        {
            num++;
        };
        iteratePath(action);
        return num;
    }

    void dumpDot()
    {
        std::error_code ec;
        raw_fd_stream fd("UserGraph.dot", ec);
        WriteGraph(fd, this);
    }

    void printPath()
    {
        std::function<void(std::vector<UserGraphNode *> &)> dumpPath = [&](std::vector<UserGraphNode *> &path)
        {
            errs() << "path: ";
            for (UserGraphNode *it : path)
            {
                if (it->data == nullptr)
                {
                    errs() << "root";
                }
                else
                {
                    it->data->printAsOperand(errs());
                }
                errs() << "==> ";
            }
            errs() << "END\n";
        };
        iteratePath(dumpPath);
    }
};

namespace llvm
{
    template <>
    struct GraphTraits<UserGraph *>
    {
        typedef UserGraphNode *NodeRef;
        typedef SmallVector<NodeRef>::iterator ChildIteratorType;

        static ChildIteratorType child_begin(NodeRef node)
        {
            return node->successors.begin();
        }
        static ChildIteratorType child_end(NodeRef node)
        {
            return node->successors.end();
        }

        typedef std::set<NodeRef>::iterator nodes_iterator;
        static nodes_iterator nodes_begin(UserGraph *tree)
        {
            return tree->nodes.begin();
        }
        static nodes_iterator nodes_end(UserGraph *tree)
        {
            return tree->nodes.end();
        }
    };

    template <>
    struct DOTGraphTraits<UserGraph *> : public DefaultDOTGraphTraits
    {

        DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple) {}

        static std::string getGraphName(UserGraph *tree)
        {
            return "User Graph";
        }

        static bool isNodeHidden(const UserGraphNode *Node, const UserGraph *tree)
        {
            return false;
        }

        static std::string getNodeLabel(const UserGraphNode *Node, UserGraph *tree)
        {
            if (Node->data == nullptr)
            {
                return "root";
            }
            else
            {
                std::string res;
                raw_string_ostream os(res);
                BasicBlock *bb = Node->data;
                bb->printAsOperand(os);
                os << ":\n";
                for (Instruction &ins : *bb)
                {
                    if (tree->userSet.find(&ins) != tree->userSet.end())
                    {
                        os << ins << "\n";
                    }
                }
                return res;
            }
        }

        static std::string getNodeAttributes(const UserGraphNode *Node, UserGraph *tree)
        {
            if (Node->type == UserGraphNodeType::loop)
            {
                return "color=\"red\"";
            }
            else
            {
                return "";
            }
        }
    };

}

class WrapperBuilder
{
private:
    LLVMContext *ctx;
    Module *m;
    const DataLayout *dl;
    std::string nameSuffix;
    std::vector<Instruction *> insLine;
    std::map<Instruction *, Instruction *> insMap;
    std::vector<Type *> wrapperParams;
    std::set<Function *> *reservedSet;

    // 为insLine中的API配置参数，每种类型分配1个对应类型的形参即可。当wrapperFunc中API调用无法确定参数时，使用这些形参
    void generateFunctionType()
    {
        std::set<Type *> params;
        for (Instruction *ins : insLine)
        {
            if (CallBase *cb = dyn_cast<CallBase>(ins))
            {
                for (Type *t : cb->getFunctionType()->params())
                {
                    params.insert(t);
                }
            }
            else
            {
                llvm_unreachable("no callbase ins\n");
            }
        }
        for (Type *t : params)
        {
            wrapperParams.push_back(t);
        }
    }

    // 为该path建立初始的wrapperfunc框架
    void buildWrapperFunction()
    {
        auto retType = Type::getVoidTy(*ctx);
        generateFunctionType();
        auto ft = FunctionType::get(retType, wrapperParams, false);
        wrapperFunc = Function::Create(ft, GlobalValue::ExternalLinkage, "wrapper_" + nameSuffix, m);
        auto bb = BasicBlock::Create(*ctx, "", wrapperFunc);
        IRBuilder<> ir(bb);
        for (Instruction *ins : insLine)
        {
            if (CallBase *cb = dyn_cast<CallBase>(ins))
            {
                auto callee = cb->getCalledFunction();
                std::vector<Value *> args;
                for (Value *arg : cb->data_ops())
                {
                    // scalar和ptr常量将仍然保持不变
                    if (Constant *constVal = dyn_cast<Constant>(arg))
                    {
                        args.push_back(arg);
                        // 如果参数为函数指针，则保留该函数
                        if (Function *f = dyn_cast<Function>(constVal))
                        {
                            reservedSet->insert(f);
                        }
                    }
                    // scalar变量将指向wrapperFunction的形参
                    else if (!arg->getType()->isPointerTy())
                    {
                        Type *t = arg->getType();
                        bool found = false;
                        for (size_t i = 0; i < wrapperParams.size(); i++)
                        {
                            if (wrapperParams[i] == t)
                            {
                                args.push_back(wrapperFunc->getArg(i));
                                found = true;
                                break;
                            }
                        }
                        assert(found);
                    }
                    // ptr变量将通过allinst提供(TODO)
                    else if (arg->getType()->isPointerTy())
                    {
                        Type *t = arg->getType();
                        bool found = false;
                        for (size_t i = 0; i < wrapperParams.size(); i++)
                        {
                            if (wrapperParams[i] == t)
                            {
                                args.push_back(wrapperFunc->getArg(i));
                                found = true;
                                break;
                            }
                        }
                        assert(found);
                    }
                    else
                    {
                        llvm_unreachable("unhandled arg type\n");
                    }
                }
                Instruction *newIns = ir.CreateCall(callee, args);
                insMap[ins] = newIns;
            }
            else
            {
                llvm_unreachable("unhandled ins\n");
            }
        }
        ir.CreateRetVoid();
    }

    // 当该path中存在value依赖关系时，我们修改wrapperfunc以反映该关系
    void linkValues()
    {
        for (Instruction *v : insLine)
        {
            for (Instruction *ins : insLine)
            {
                for (Use &use : ins->operands())
                {
                    if (use.get() == v)
                    {
                        Value *newValue = insMap[v];
                        Instruction *newUser = insMap[ins];
                        newUser->getOperandUse(use.getOperandNo()).set(newValue);
                    }
                }
            }
        }
    }

public:
    Function *wrapperFunc;

    void build()
    {
        buildWrapperFunction();
        linkValues();
    }

    WrapperBuilder(Module *m, std::vector<Instruction *> *insline, std::string nameSuffix, std::set<Function *> *reservedSet)
    {
        this->m = m;
        this->ctx = &m->getContext();
        this->dl = &m->getDataLayout();
        this->insLine = *insline;
        this->nameSuffix = nameSuffix;
        this->reservedSet = reservedSet;
    }
    ~WrapperBuilder() {}
};

void outputModule(Module &module, std::set<std::string> &reservedNames, std::string outputName)
{
    std::unique_ptr<Module> mP = CloneModule(module);
    Module *m = mP.get();
    std::set<Function *> deleteSet;
    for (Function &f : *m)
    {
        if (reservedNames.find(f.getName().str()) == reservedNames.end())
        {
            deleteSet.insert(&f);
        }
    }
    for (Function *f : deleteSet)
    {
        f->replaceAllUsesWith(UndefValue::get(f->getType()));
        f->eraseFromParent();
    }

    if (!verifyModule(*m, &errs()))
    {
        std::error_code ec;
        raw_fd_ostream OS(outputName, ec);
        WriteBitcodeToFile(*m, OS);
    }
}

void generateWrapper()
{
    sys::fs::create_directory(outputDir);
    for (Function *w : wrapperSet)
    {
        std::set<std::string> reservedNames;
        for (Function *f : reservedSet)
        {
            reservedNames.insert(f->getName().str());
        }
        reservedNames.insert(w->getName().str());
        outputModule(*module, reservedNames, outputDir + "/" + w->getName().str() + ".bc");
    }
}

void analysis()
{
    if (callerFuncs.size() == 1)
    {
        for (Function *func : callerFuncs)
        {
            UserGraph ug(func, userSet);
            errs() << "pathNum: " << ug.getPathNum() << "\n";
            ug.dumpDot();
            // ug.printPath();
            size_t suffix = 0;
            std::function<void(std::vector<UserGraphNode *> &)> builder = [&](std::vector<UserGraphNode *> &path)
            {
                std::vector<Instruction *> insline;
                for (UserGraphNode *node : path)
                {
                    if (node->data == nullptr)
                    {
                        continue;
                    }

                    for (Instruction &ins : *node->data)
                    {
                        if (userSet.find(&ins) != userSet.end())
                        {
                            insline.push_back(&ins);
                        }
                    }
                }
                WrapperBuilder wb(module, &insline, std::to_string(suffix), &reservedSet);
                wb.build();
                wrapperSet.insert(wb.wrapperFunc);
                // errs() << *wb.wrapperFunc << "\n\n";
                suffix++;
            };
            ug.iteratePath(builder);
        }
    }
}

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
        else
        {
            return true;
        }
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
    std::cin >> apiString;
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
        reservedSet.insert(f);
        for (User *user : f->users())
        {
            if (auto ins = dyn_cast<CallInst>(user))
            {
                callerFuncs.insert(ins->getFunction());
                userSet.insert(ins);
            }
            else if (auto ins = dyn_cast<InvokeInst>(user))
            {
                callerFuncs.insert(ins->getFunction());
                userSet.insert(ins);
            }
            else
            {
                // errs() << "unknow user"<< *user << "\n";
            }
        }
    }

    if (action == "p")
    {
        printInfo();
    }
    else if (action == "t")
    {
        if (callerFuncs.size() == 1)
        {
            for (Function *func : callerFuncs)
            {
                fastAnalysis(func);
            }
        }
        else
        {
            errs() << "too many caller func\n";
        }
    }

    return 0;
}