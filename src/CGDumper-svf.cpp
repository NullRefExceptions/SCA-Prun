#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/GraphWriter.h"

#include "Graphs/SVFGOPT.h"
#include "MSSA/MemSSA.h"
#include "MSSA/SVFGBuilder.h"
#include "SVF-LLVM/BasicTypes.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFIR.h"
#include "Util/CommandLine.h"
#include "WPA/Andersen.h"
#include "WPA/VersionedFlowSensitive.h"

using namespace llvm;
using namespace std;
using namespace SVF;

const Option<std::string> libPath("lib", "path to the bc file", "");
const Option<std::string> dotPath("o", "path to the dot file", "");

LLVMModuleSet* svfModuleSet;
SVFIR* pag;
BVDataPTAImpl* pta;

namespace SVF
{

  template <>
  struct DOTGraphTraits<PTACallGraph *> : public DefaultDOTGraphTraits
  {

    typedef PTACallGraphNode NodeType;
    typedef NodeType::iterator ChildIteratorType;
    DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple)
    {
    }

    /// Return name of the graph
    static std::string getGraphName(PTACallGraph *)
    {
      return "Call Graph";
    }
    /// Return function name;
    static std::string getNodeLabel(PTACallGraphNode *node, PTACallGraph *)
    {
      return node->getFunction()->getName();
    }



  };
}

class CGVisitor : public InstVisitor<CGVisitor>
{
    SmallPtrSet<BasicBlock*, 8> BBExecutable;
    SmallVector<BasicBlock*, 64> BBWorkList;
    SmallPtrSet<CallInst*, 8> UnExecutableCallInst;

public:
    void getFeasibleSuccessors(Instruction& TI, SmallVectorImpl<bool>& Succs)
    {
        Succs.resize(TI.getNumSuccessors());
        if (auto* BI = dyn_cast<BranchInst>(&TI))
        {
            if (BI->isUnconditional())
            {
                Succs[0] = true;
                return;
            }

            ConstantInt* CI = dyn_cast<ConstantInt>(BI->getCondition());
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

        if (auto* SI = dyn_cast<SwitchInst>(&TI))
        {
            if (!SI->getNumCases())
            {
                Succs[0] = true;
                return;
            }
            ConstantInt* CI = dyn_cast<ConstantInt>(SI->getCondition());
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
        if (auto* IBR = dyn_cast<IndirectBrInst>(&TI))
        {
            BlockAddress* Addr = dyn_cast<BlockAddress>(IBR->getAddress());
            if (!Addr)
            {
                // unknown condition, all destinations are executable!
                Succs.assign(TI.getNumSuccessors(), true);
                return;
            }
            BasicBlock* T = Addr->getBasicBlock();
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

    void handleUnExecutableBB(BasicBlock& b, set<const SVF::CallICFGNode*>& unreachedICFGNodes)
    {
        errs()<<"unreached BB in "<<b.getParent()->getName() <<"\n";
        for (auto& i : b)
        {
            auto inst = svfModuleSet->getSVFInstruction(&i);
            if (SVFUtil::isCallSite(inst) && SVFUtil::isNonInstricCallSite(inst))
            {
                auto node = pag->getICFG()->getCallICFGNode(inst);
                unreachedICFGNodes.insert(node);
            }
        }
    }

    void visitTerminator(Instruction& TI)
    {
        SmallVector<bool, 16> SuccFeasible;
        getFeasibleSuccessors(TI, SuccFeasible);

        // Mark all feasible successors executable.
        for (unsigned i = 0, e = SuccFeasible.size(); i != e; ++i)
        {
            if (!SuccFeasible[i])
              continue;
                
            BasicBlock* BB = TI.getSuccessor(i);
            if (BBExecutable.find(BB) == BBExecutable.end())
            {
                BBWorkList.push_back(TI.getSuccessor(i));
                BBExecutable.insert(TI.getSuccessor(i));
            }
        }
    }

    void visitReturnInst(ReturnInst& I)
    { /*returns void*/
    }

    void visitUnreachableInst(UnreachableInst& I)
    { /*returns void*/
    }

    void run(Function& f, set<const SVF::CallICFGNode*>& unreachedICFGNodes)
    {
        if (f.isDeclaration())
            return;
        BBWorkList.push_back(&f.getEntryBlock());
        BBExecutable.insert(&f.getEntryBlock());
        while (!BBWorkList.empty())
        {
            BasicBlock* BB = BBWorkList.back();
            BBWorkList.pop_back();
            visit(BB->getTerminator());
        }
        // auto reduce = f.getBasicBlockList().size() - BBExecutable.size();
        //  if (reduce > 0 && f.getName()=="_gcry_md_hash_buffer_clone")
        //    errs() << f.getName() << " reduced " << reduce << ", " <<BBExecutable.size()<<" left\n";

        for (auto& b : f.getBasicBlockList())
            if (BBExecutable.find(&b) == BBExecutable.end())
                handleUnExecutableBB(b, unreachedICFGNodes);
        BBExecutable.clear();
    }
};

int main(int argc, char** argv)
{
    OptionBase::parseOptions(argc, argv, "Dump call graph", "");
    LLVMContext ctxs[2];
    SMDiagnostic Err;
    unique_ptr<Module> mP;
    mP = parseIRFile(libPath(), Err, ctxs[0]);
    Module* module = mP.get();

    if (module == nullptr)
    {
        outs() << Err.getMessage() << "\n";
        return -1;
    }

    svfModuleSet = LLVMModuleSet::getLLVMModuleSet();
    SVFIRBuilder builder(svfModuleSet->buildSVFModule(*module));
    pag = builder.build();
    //pta = AndersenWaveDiff::createAndersenWaveDiff(pag);
    pta = VersionedFlowSensitive::createVFSWPA(pag);

    auto cg = pta->getPTACallGraph();
    WriteGraph(cg,false,"ptacg.dot");
    // GraphPrinter::WriteGraphToFile(errs(), "ptacg", cg);
    auto ci2edge = cg->getCallInstToCallGraphEdgesMap();

    set<const SVF::CallICFGNode*> unreachedICFGNodes;
    CGVisitor v;
    for (auto& f : *module)
    {
        v.run(f, unreachedICFGNodes);
        for (auto ci : unreachedICFGNodes)
        {
            auto edges = ci2edge.find(ci);
            // assert(edges != ci2edge.end());
            // SVF在构建cg时，指针分析会发现由于路径不可达导致的无效间接调用（通过删去函数指针目标集合中的无效对象）
            // 但无法处理不可达路径上的直接函数调用。因此我们仍然需要自行删去这些直接调用?
            if (edges == ci2edge.end())
            {
                errs()<<"node not found?\n";
                errs() << ci->toString() << "\n";
                continue;
            }
            // ci到callee的边，被保存在ci所在caller到callee的edge中，
            // edge中未必仅有ci一个，我们需要判断该ci是否为最后一个
            for (auto edge : (*edges).second)
            {
                auto& diCallSet = edge->getDirectCalls();
                auto& indiCallSet = edge->getIndirectCalls();

                if (ci->isIndirectCall())
                    indiCallSet.erase(ci);
                else
                    diCallSet.erase(ci);

                if ((diCallSet.size() + indiCallSet.size()) == 0)
                {
                    edge->getDstNode()->removeIncomingEdge(edge);
                    edge->getSrcNode()->removeOutgoingEdge(edge);
                }
            }
        }

        unreachedICFGNodes.clear();
    }
    //WriteGraph(cg,false,dotPath());
    WriteGraph(cg,false,"ptacg_reduced.dot");
    return 0;
}
