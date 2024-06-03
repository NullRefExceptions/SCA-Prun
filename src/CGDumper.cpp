#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/Local.h"

#include "ControlDependencyGraph2.hpp"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/GraphTraits.h"

#include "Analyzer.h"
#include "CallGraph.h"
#include "Config.h"

using namespace llvm;

cl::opt<std::string> libPath(cl::Positional, cl::desc("<input bitcode files>"));
cl::opt<string> OutputFilename("o", cl::init("mltacg.dot"), cl::desc("Specify output filename"), cl::value_desc("filename"));
cl::opt<bool> reduceCG("r", cl::init(false), cl::desc("reduce the callgraph"));
cl::opt<bool> depInfo("depInfo", cl::init(false), cl::desc("show dep info"));

class MLTACGDOTInfo;
struct MLTACG_Node;
MLTACGDOTInfo *MI;

string BB2label(BasicBlock *bb)
{
  SmallVector<char, 10> sv;
  raw_svector_ostream SO(sv);
  bb->printAsOperand(SO, false);
  return SO.str().str();
}

struct MLTACG_Edge
{
  MLTACG_Node *src;
  MLTACG_Node *dst;
  CallInst *callSite;
  bool reduced;
  bool reached;

  MLTACG_Edge(MLTACG_Node *src, MLTACG_Node *dst, CallInst *cs)
  {
    this->src = src;
    this->dst = dst;
    callSite = cs;
    reduced = false;
    reached = false;
  }
};

struct MLTACG_Node
{
  // depInfo
  using pathVector = std::vector<std::vector<Instruction *>>;
  pdg::ControlDependencyGraph2 *cdg;
  llvm::PostDominatorTree *pdt;
  std::map<Instruction *, pathVector> pathMap;              // 每条call ins的cdg path集合
  std::map<MLTACG_Node *, std::set<Instruction *>> callMap; // 每个child对应的call ins

  Function *func;
  set<MLTACG_Edge *> in_edges;
  set<MLTACG_Edge *> out_edges;
  bool reduced;
  bool reached;
  MLTACG_Node(Function *f)
  {
    func = f;
    reduced = false;
    reached = false;
    if (!f->isDeclaration() && depInfo)
    {
      pdt = new llvm::PostDominatorTree(*f);
      cdg = new pdg::ControlDependencyGraph2(f, pdt);
    }
  }

  void reduceCallSite(CallInst *cs)
  {
    for (MLTACG_Edge *edge : out_edges)
    {
      if (edge->callSite == cs)
      {
        // if (!edge->dst->func->isIntrinsic() && !edge->dst->func->isDeclaration())
        // errs() << formatv("reduce edge:{0}-->{1}\n", edge->src->func->getName(), edge->dst->func->getName());
        edge->reduced = true;
      }
    }
  }

  // 检查并更新与该node相关的状态，返回false表明其不可能影响children节点的状态
  // 返回true则表明其可能会影响
  bool selfCheck()
  {
    if (reduced)
      return false;

    bool needToReduce = true;
    for (MLTACG_Edge *edge : in_edges)
    {
      if (edge->reduced == false)
      {
        needToReduce = false;
        break;
      }
    }
    if (needToReduce)
    {
      reduced = true;

      for (MLTACG_Edge *edge : out_edges)
      {
        edge->reduced = true;
      }
      return true;
    }
    return false;
  }

  ~MLTACG_Node()
  {
    delete cdg;
    delete pdt;
  }

  bool isCloned()
  {
    return StringRef::npos != func->getName().find("_trcloned");
  }

  bool isBug()
  {
    return func->getName().startswith("magma_bug");
  }
};

class MLTACGDOTInfo
{
  Module *M;
  GlobalContext *ctx;

public:
  set<MLTACG_Node *> nodes;
  set<MLTACG_Edge *> edges;
  MLTACG_Node *root;
  map<CallInst *, MLTACG_Edge *> inst2edges;

  map<Function *, MLTACG_Node *> func2node;

  MLTACGDOTInfo(Module *M, GlobalContext *ctx) : M(M), ctx(ctx)
  {
    for (auto &func : *M)
    {
      getNode(&func);
    }
  }

  MLTACG_Node *getNode(Function *func)
  {
    if (func2node.find(func) != func2node.end())
      return func2node[func];
    auto node = new MLTACG_Node(func);
    nodes.insert(node);
    func2node[func] = node;

    for (auto &bb : *func)
      for (auto &ins : bb)
        if (auto ci = dyn_cast<CallInst>(&ins))
        {
          // unlikely
          if (ctx->Callees.find(ci) == ctx->Callees.end())
            continue;

          for (auto f : ctx->Callees[ci])
          {
            MLTACG_Node *childNode = getNode(f);
            MLTACG_Edge *newE = new MLTACG_Edge(node, childNode, ci);
            edges.insert(newE);
            node->out_edges.insert(newE);
            childNode->in_edges.insert(newE);
            if (depInfo)
              node->callMap[childNode].insert(ci);
          }
          if (depInfo)
            node->cdg->getRDep(ci, node->pathMap[ci]);
        }

    return node;
  }

  void updateReduced()
  {
    /*
    除main函数外，如果某个函数的in边不存在或者全部被reduced，则reduced该节点,
    之后我们检查其对其他node的影响
     */
    vector<MLTACG_Node *> workList;
    for (MLTACG_Node *node : nodes)
    {
      if (node == root)
        continue;
      if (node->selfCheck())
      {
        workList.push_back(node);
        // errs()<<node->func->getName()<<"\n";
      }
    }
    while (!workList.empty())
    {
      MLTACG_Node *nodeToCheck = workList.back();
      workList.pop_back();

      for (MLTACG_Edge *e : nodeToCheck->out_edges)
      {
        MLTACG_Node *next = e->dst;
        // 预防一手
        if (next == root)
          continue;
        if (e->dst->selfCheck())
          workList.push_back(e->dst);
      }
    }
  }

  void printTotalInfo()
  {
    uint64_t totalBugs = 0;
    for (MLTACG_Node *node : MI->nodes)
    {
      if (node->isBug())
        totalBugs++;
    }
    errs() << formatv("total: nodes {0},edges {1},bugs {2}\n", MI->nodes.size(), MI->edges.size(), totalBugs);
  }

  void printReachedInfo()
  {
    //reset ReachedInfo
    for (MLTACG_Node *node : nodes)
    {
      node->reached = false;
    }

    for (MLTACG_Edge *edge : edges)
    {
      edge->reached = false;
    }

    //update ReachedInfo
    Function *mainF = M->getFunction("main");
    root = getNode(mainF);
    set<MLTACG_Node *> reachSet;
    function<void(MLTACG_Node *)> tr = [&](MLTACG_Node *node)
    {
      reachSet.insert(node);
      node->reached = true;
      for (MLTACG_Edge *edge : node->out_edges)
      {
        if (edge->reduced)
          continue;

        edge->reached = true;
        MLTACG_Node *dst = edge->dst;
        if (reachSet.find(dst) == reachSet.end())
        {
          tr(dst);
        }
      }
    };
    tr(root);

    //print ReachedInfo
    uint64_t reachedNodes = 0;
    uint64_t reachedEdges = 0;
    uint64_t reachedBugs = 0;

    for (MLTACG_Node *node : nodes)
    {
      if (node->reached)
        reachedNodes++;
      if (node->reached && node->isBug())
        reachedBugs++;
    }

    for (MLTACG_Edge *edge : edges)
    {
      if (edge->reached)
        reachedEdges++;
    }

    errs() << formatv("reached: nodes {0},edges {1},bug {2}\n", reachedNodes, reachedEdges, reachedBugs);
  }

  void dump(string fileName)
  {
    WriteGraph(this, "", false, "", fileName);
  }

  void prun()
  {
    vector<MLTACG_Edge *> needToRemoveEdges;
    for (MLTACG_Edge *edge : edges)
    {
      if (edge->reduced)
        needToRemoveEdges.push_back(edge);
    }

    for (MLTACG_Edge *edge : needToRemoveEdges)
    {
      edge->src->out_edges.erase(edge);
      edge->dst->in_edges.erase(edge);
      edges.erase(edge);
    }

    vector<MLTACG_Node *> needToRemoveNodes;
    for (MLTACG_Node *node : nodes)
    {
      if (node->reduced)
        needToRemoveNodes.push_back(node);
    }

    for (MLTACG_Node *node : needToRemoveNodes)
    {
      nodes.erase(node);
    }
  }

};

class CGVisitor : public InstVisitor<CGVisitor>
{
  SmallPtrSet<BasicBlock *, 8> BBExecutable;
  SmallVector<BasicBlock *, 64> BBWorkList;
  SmallPtrSet<CallInst *, 8> UnExecutableCallInst;

public:
  uint64_t Num_unreachBB = 0;
  uint64_t Num_reducedEdge = 0;

  void getFeasibleSuccessors(Instruction &TI, SmallVectorImpl<bool> &Succs)
  {
    Succs.resize(TI.getNumSuccessors());
    if (auto *BI = dyn_cast<BranchInst>(&TI))
    {
      if (BI->isUnconditional())
      {
        Succs[0] = true;
        return;
      }

      ConstantInt *CI = dyn_cast<ConstantInt>(BI->getCondition());
      if (!CI)
      {
        Succs[0] = Succs[1] = true;
        return;
      }

      // Constant condition variables mean the branch can only go a single way.
      Succs[CI->isZero()] = true;
      return;
    }

    // Unwinding instructions successors are always executable.
    if (TI.isExceptionalTerminator())
    {
      Succs.assign(TI.getNumSuccessors(), true);
      return;
    }

    if (auto *SI = dyn_cast<SwitchInst>(&TI))
    {
      if (!SI->getNumCases())
      {
        Succs[0] = true;
        return;
      }
      ConstantInt *CI = dyn_cast<ConstantInt>(SI->getCondition());
      if (!CI)
      {
        // unknown condition, all destinations are executable!
        Succs.assign(TI.getNumSuccessors(), true);
        return;
      }

      Succs[SI->findCaseValue(CI)->getSuccessorIndex()] = true;
      return;
    }

    // In case of indirect branch and its address is a blockaddress, we mark
    // the target as executable.
    if (auto *IBR = dyn_cast<IndirectBrInst>(&TI))
    {
      BlockAddress *Addr = dyn_cast<BlockAddress>(IBR->getAddress());
      if (!Addr)
      {
        // unknown condition, all destinations are executable!
        Succs.assign(TI.getNumSuccessors(), true);
        return;
      }
      BasicBlock *T = Addr->getBasicBlock();
      assert(Addr->getFunction() == T->getParent() && "Block address of a different function ?");
      for (unsigned i = 0; i < IBR->getNumSuccessors(); ++i)
      {
        // This is the target.
        if (IBR->getDestination(i) == T)
        {
          Succs[i] = true;
          return;
        }
      }

      // If we didn't find our destination in the IBR successor list, then we
      // have undefined behavior. Its ok to assume no successor is executable.
      return;
    }

    // In case of callbr, we pessimistically assume that all successors are
    // feasible.
    if (isa<CallBrInst>(&TI))
    {
      Succs.assign(TI.getNumSuccessors(), true);
      return;
    }
    dbgs() << "Unknown terminator instruction: " << TI << '\n';
    llvm_unreachable("SCCP: Don't know how to handle this terminator!");
  }

  void handleUnExecutableBB(BasicBlock &b, MLTACG_Node *node)
  {
    Num_unreachBB++;
    for (auto &i : b)
      if (auto ci = dyn_cast<CallInst>(&i))
      {
        node->reduceCallSite(ci);
        Num_reducedEdge++;
      }
  }

  void visitTerminator(Instruction &TI)
  {
    SmallVector<bool, 16> SuccFeasible;
    getFeasibleSuccessors(TI, SuccFeasible);

    // Mark all feasible successors executable.
    for (unsigned i = 0, e = SuccFeasible.size(); i != e; ++i)
    {
      if (!SuccFeasible[i])
        continue;

      BasicBlock *BB = TI.getSuccessor(i);
      if (BBExecutable.find(BB) == BBExecutable.end())
      {
        BBWorkList.push_back(TI.getSuccessor(i));
        BBExecutable.insert(TI.getSuccessor(i));
      }
    }
  }

  void visitReturnInst(ReturnInst &I) {}

  void visitUnreachableInst(UnreachableInst &I) {}

  void run(MLTACG_Node *node)
  {
    Function *f = node->func;
    if (f->isDeclaration())
      return;
    BBWorkList.push_back(&f->getEntryBlock());
    BBExecutable.insert(&f->getEntryBlock());
    while (!BBWorkList.empty())
    {
      BasicBlock *BB = BBWorkList.back();
      BBWorkList.pop_back();
      visit(BB->getTerminator());
    }

    for (auto &b : f->getBasicBlockList())
      if (BBExecutable.find(&b) == BBExecutable.end())
        handleUnExecutableBB(b, node);

    BBExecutable.clear();
  }

  void printInfo()
  {
    errs() << "Number of unreached BB: " << Num_unreachBB << "\n";
    errs() << "Number of reduced Edge: " << Num_reducedEdge << "\n";
  }
};

namespace llvm
{
  template <>
  struct GraphTraits<MLTACGDOTInfo *>
  {
    typedef MLTACG_Node *NodeRef;

    static MLTACG_Node *GetValuePtr(const MLTACG_Edge *edge) { return edge->dst; }

    typedef mapped_iterator<set<MLTACG_Edge *>::iterator, decltype(&GetValuePtr)> ChildIteratorType;

    static ChildIteratorType child_begin(NodeRef node)
    {
      return ChildIteratorType(node->out_edges.begin(), GetValuePtr);
    }
    static ChildIteratorType child_end(NodeRef node)
    {
      return ChildIteratorType(node->out_edges.end(), GetValuePtr);
    }

    typedef decltype(MLTACGDOTInfo::nodes.begin()) nodes_iterator;
    static nodes_iterator nodes_begin(MLTACGDOTInfo *G)
    {
      return G->nodes.begin();
    }
    static nodes_iterator nodes_end(MLTACGDOTInfo *G)
    {
      return G->nodes.end();
    }
  };

  template <>
  struct DOTGraphTraits<MLTACGDOTInfo *> : public DefaultDOTGraphTraits
  {

    DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple) {}

    static std::string getGraphName(MLTACGDOTInfo *CGInfo)
    {
      return "Call graph";
    }

    static bool isNodeHidden(const MLTACG_Node *Node, const MLTACGDOTInfo *CGInfo)
    {
      return false; // Node->reduced || Node->func->isIntrinsic() || Node->func->isDeclaration();
    }

    std::string getNodeLabel(const MLTACG_Node *Node, MLTACGDOTInfo *CGInfo)
    {
      return Node->func->getName().str();
    }

    static std::string getNodeAttributes(const MLTACG_Node *Node, MLTACGDOTInfo *CGInfo)
    {
      return formatv("addressTaken={0}", Node->func->hasAddressTaken());
    }

    static std::string getEdgeAttributes(const MLTACG_Node *Node, llvm::GraphTraits<MLTACGDOTInfo *>::ChildIteratorType c, const MLTACGDOTInfo *CGInfo)
    {
      if (depInfo)
      {
        const std::set<Instruction *> &callerSet = Node->callMap.at(*c);
        uint64_t instForChild = callerSet.size();
        uint64_t minControlDepNode = UINT64_MAX;

        for (Instruction *ins : callerSet)
        {
          const MLTACG_Node::pathVector &paths = Node->pathMap.at(ins);
          for (const std::vector<llvm::Instruction *> &path : paths)
          {
            if (path.size() < minControlDepNode)
              minControlDepNode = path.size();
          }
        }
        return llvm::formatv("label=\"instC={0},minDep={1}\"", instForChild, minControlDepNode);
      }
      else
      {
        return "";
      }
    }
  };

} // namespace llvm

int main(int argc, char **argv)
{
  cl::ParseCommandLineOptions(argc, argv, "Dump call graph");
  LLVMContext ctxs;
  SMDiagnostic Err;
  unique_ptr<Module> mP;
  mP = parseIRFile(libPath, Err, ctxs);
  Module *module = mP.get();

  if (module == nullptr)
  {
    outs() << Err.getMessage() << "\n";
    return -1;
  }
  StringRef MName = StringRef(strdup(libPath.data()));
  GlobalContext GlobalCtx;
  GlobalCtx.Modules.push_back(std::make_pair(module, MName));
  GlobalCtx.ModuleMaps[module] = MName;

  CallGraphPass CGPass(&GlobalCtx);
  CGPass.run(GlobalCtx.Modules);
  MI = new MLTACGDOTInfo(module, &GlobalCtx);

  MI->printTotalInfo();
  if (reduceCG)
  {
    MI->printReachedInfo();
    errs()<< "pruning...";
    CGVisitor v;
    for (MLTACG_Node *node : MI->nodes)
    {
      v.run(node);
    }
    // v.printInfo();
    MI->updateReduced();
    errs()<< "done\n";
    MI->printReachedInfo();
    MI->prun();
    MI->dump(OutputFilename.data());
  }
  else
  {
    MI->printReachedInfo();
    MI->dump(OutputFilename.data());
  }
  // 实际上，reducedEdge还应该包括在constant propation中由indirect call转变为direct call减少的边
}
