#include "ControlDependencyGraph2.hpp"

using namespace llvm;

void pdg::ControlDependencyGraph2::addInstToBBDependency(InstructionWrapper *from, BasicBlock *to, DependencyType depType)
{
  for (BasicBlock::iterator ii = to->begin(), ie = to->end(); ii != ie; ++ii)
  {
    if (Instruction *Ins = dyn_cast<Instruction>(ii))
    {
      InstructionWrapper *iw = PDGUtils::getInstance().getInstMap()[Ins];
      CDG->addDependency(from, iw, depType);
    }
  }
}

void pdg::ControlDependencyGraph2::addBBToBBDependency(BasicBlock *from, BasicBlock *to, DependencyType type)
{
  Instruction *Ins = from->getTerminator();
  InstructionWrapper *iw = PDGUtils::getInstance().getInstMap()[Ins];
  // self loop
  if (from == to)
  {
    for (BasicBlock::iterator ii = from->begin(), ie = from->end(); ii != ie; ++ii)
    {
      Instruction *inst = dyn_cast<Instruction>(ii);
      InstructionWrapper *iwTo = PDGUtils::getInstance().getInstMap()[inst];
      CDG->addDependency(iw, iwTo, type);
    }
  }
  else
  {
    for (BasicBlock::iterator ii = to->begin(), ie = to->end(); ii != ie; ++ii)
    {
      Instruction *inst = dyn_cast<Instruction>(ii);
      InstructionWrapper *iwTo = PDGUtils::getInstance().getInstMap()[inst];
      CDG->addDependency(iw, iwTo, type);
    }
  }
}

void pdg::ControlDependencyGraph2::computeDependencies(Function &F)
{
  PDGUtils::getInstance().constructFuncMap(*F.getParent());
  if (PDGUtils::getInstance().getFuncMap()[&F]->getEntryW() != nullptr)
  {
    return;
  }

  InstructionWrapper *entryW = new InstructionWrapper(&F, GraphNodeType::ENTRY);
  PDGUtils::getInstance().getFuncInstWMap()[&F].insert(entryW);
  PDGUtils::getInstance().getFuncMap()[&F]->setEntryW(entryW);

  DomTreeNodeBase<BasicBlock> *node = PDT->getNode(&F.getEntryBlock());
  while (node && node->getBlock())
  {
    // Walking the path backward and adding dependencies.
    addInstToBBDependency(entryW, node->getBlock(), DependencyType::CONTROL);
    node = node->getIDom();
  }
  std::vector<std::pair<BasicBlock *, BasicBlock *>> EdgeSet;

  for (Function::iterator BI = F.begin(), E = F.end(); BI != E; ++BI)
  {
    // Zhiyuan comment: find adjacent BasicBlock pairs in CFG, but the predecessor
    // does not dominate successor.
    BasicBlock *I = dyn_cast<BasicBlock>(BI);
    for (succ_iterator SI = succ_begin(I), SE = succ_end(I); SI != SE; ++SI)
    {
      assert(I && *SI);
      if (!PDT->dominates(*SI, I))
      {
        BasicBlock *B_second = dyn_cast<BasicBlock>(*SI);
        EdgeSet.push_back(std::make_pair(I, B_second));
      }
    }
  }

  for (auto Edge : EdgeSet)
  {
    BasicBlock *L = PDT->findNearestCommonDominator(Edge.first, Edge.second);

    // capture loop dependence
    if (L == Edge.first)
    {
      addBBToBBDependency(Edge.first, L, DependencyType::CONTROL);
    }
    DomTreeNode *domNode = PDT->getNode(Edge.second);
    if (domNode == nullptr)
    {
      continue;
    }
    while (domNode->getBlock() != L)
    {
      addBBToBBDependency(Edge.first, domNode->getBlock(), DependencyType::CONTROL);
      domNode = domNode->getIDom();
    }
  }
}

void pdg::ControlDependencyGraph2::initDijkstra()
{
  std::set<cgdNode *> unfinish;

  // 初始化数组
  cgdNode *entry = *CDG->begin_child();
  for (cgdNode *node : CDG->getNodeSet())
  {
    if (node == entry)
    {
      dis[node] = 0;
      pre[node] = nullptr;
    }
    else if (entry->isDepends(node))
    {
      dis[node] = 1;
      pre[node] = entry;
    }
    else
    {
      dis[node] = UINT64_MAX;
      pre[node] = nullptr;
    }
    unfinish.insert(node);
  }
  unfinish.erase(entry);

  while (!unfinish.empty())
  {
    cgdNode *next = *unfinish.begin();
    for (cgdNode *node : unfinish)
    {
      if (dis[node] < dis[next])
      {
        next = node;
      }
    }

    for (std::pair<cgdNode *, pdg::DependencyType> &child : next->getDependencyList())
    {
      if (dis[next] + 1 < dis[child.first])
      {
        dis[child.first] = dis[next] + 1;
        pre[child.first] = next;
      }
    }
    unfinish.erase(next);
  }
}

void pdg::ControlDependencyGraph2::getRDep(llvm::Instruction *ins, std::vector<std::vector<llvm::Instruction *>> &pathVector)
{
  if(Func->getName()=="krb5_ldap_lockout_audit")
  {
    this->dump("krb5.dot");
  }

  std::vector<llvm::Instruction *> path;
  cgdNode *dst = CDG->getNodeByData(PDGUtils::getInstance().getInstMap()[ins]);
  cgdNode *pre = this->pre[dst];
  while (pre!=nullptr)
  {
    Instruction *ins = pre->getData()->getInstruction();
    if (ins != nullptr)
      path.insert(path.begin(),ins);
    pre = this->pre[pre];
  }
  pathVector.push_back(std::move(path));
}

/* void pdg::ControlDependencyGraph2::getRDep(llvm::Instruction *ins, std::vector<std::vector<llvm::Instruction *>> &pathVector)
{
  using cgdNode = pdg::DependencyNode<pdg::InstructionWrapper>;
  std::vector<cgdNode *> path;

  std::function<void()> dumpPath = [&path]()
  {
    errs() << "path: ";
    for (cgdNode *it : path)
    {
      if (it->getData()->getInstruction() == nullptr)
        errs() << "Entry ";
      else
        errs() << *it->getData()->getInstruction();
      errs() << "==> ";
    }
    errs() << "END\n";
    errs().flush();
  };

  std::function<void(cgdNode *)> travel = [&](cgdNode *node)
  {
    if (node->getData()->getInstruction() == ins)
    {
      std::vector<llvm::Instruction *> tmpPath;
      for (cgdNode *n : path)
      {
        Instruction *ins = n->getData()->getInstruction();
        if (ins != nullptr)
          tmpPath.push_back(ins);
      }
      pathVector.push_back(std::move(tmpPath));
    }
    else
    {
      path.push_back(node);
      for (std::pair<cgdNode *, pdg::DependencyType> &child : node->getDependencyList())
      {
        cgdNode *cnode = child.first;
        if (std::find(path.begin(), path.end(), cnode) != path.end())
          continue;
        travel(cnode);
      }
      path.pop_back();
    }
  };

  travel(*CDG->begin_child());
} */

namespace llvm
{

  template <>
  struct GraphTraits<pdg::DependencyNode<pdg::InstructionWrapper> *>
  {
    using NodeRef = pdg::DependencyNode<pdg::InstructionWrapper> *;
    using ChildIteratorType = pdg::DependencyNode<InstructionWrapper>::iterator;
    using nodes_iterator = pdg::DependencyNode<InstructionWrapper>::iterator;

    static NodeRef getEntryNode(pdg::DependencyNode<pdg::InstructionWrapper> *N) { return N; }
    static inline ChildIteratorType child_begin(pdg::DependencyNode<InstructionWrapper> *N) { return ChildIteratorType(N->getDependencyList().begin()); }
    static inline ChildIteratorType child_end(pdg::DependencyNode<InstructionWrapper> *N) { return ChildIteratorType(N->getDependencyList().end()); }
    static nodes_iterator nodes_begin(pdg::DependencyNode<InstructionWrapper> *N) { return nodes_iterator(N->getDependencyList().begin()); }
    static nodes_iterator nodes_end(pdg::DependencyNode<InstructionWrapper> *N) { return nodes_iterator(N->getDependencyList().end()); }
  };

  template <>
  struct GraphTraits<pdg::DependencyGraph<pdg::InstructionWrapper> *> : public GraphTraits<pdg::DependencyNode<pdg::InstructionWrapper> *>
  {
    static NodeRef getEntryNode(pdg::DependencyGraph<InstructionWrapper> *N) { return *(N->getNodeSet().begin()); }
    using nodes_iterator = DependencyGraph<InstructionWrapper>::nodes_iterator;
    static nodes_iterator nodes_begin(pdg::DependencyGraph<InstructionWrapper> *N) { return nodes_iterator(N->getNodeSet().begin()); }
    static nodes_iterator nodes_end(pdg::DependencyGraph<InstructionWrapper> *N) { return nodes_iterator(N->getNodeSet().end()); }
  };

  template <>
  struct DOTGraphTraits<pdg::DependencyNode<pdg::InstructionWrapper> *> : public DefaultDOTGraphTraits
  {
    DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple) {}

    std::string getNodeLabel(pdg::DependencyNode<pdg::InstructionWrapper> *Node, pdg::DependencyNode<pdg::InstructionWrapper> *Graph)
    {
      using namespace pdg;
      const InstructionWrapper *instW = Node->getData();
      if (instW == nullptr)
      {
        errs() << "instW " << instW << "\n";
        return "null instW";
      }

      std::string Str;
      raw_string_ostream OS(Str);

      switch (instW->getGraphNodeType())
      {
      case GraphNodeType::ENTRY:
      {
        return ("<<ENTRY>> " + instW->getFunction()->getName().str());
      }
      case GraphNodeType::GLOBAL_VALUE:
      {
        OS << *instW->getValue();
        return ("GLOBAL_VALUE:" + OS.str());
      }
      case GraphNodeType::FORMAL_IN:
      {
        llvm::Argument *arg = instW->getArgument();
        int arg_pos = arg->getArgNo();
        OS << *instW->getArgument()->getType();
        return ("FORMAL_IN: " + std::to_string(arg_pos) + " " + OS.str());
      }
      case GraphNodeType::ACTUAL_IN:
      {
        llvm::Argument *arg = instW->getArgument();
        int arg_pos = arg->getArgNo();
        OS << *instW->getArgument()->getType();
        return ("ACTUAL_IN: " + std::to_string(arg_pos) + " " + OS.str());
      }
      case GraphNodeType::FORMAL_OUT:
      {
        llvm::Argument *arg = instW->getArgument();
        int arg_pos = arg->getArgNo();
        OS << *instW->getArgument()->getType();
        return ("FORMAL_OUT: " + std::to_string(arg_pos) + " " + OS.str());
      }

      case GraphNodeType::ACTUAL_OUT:
      {
        llvm::Argument *arg = instW->getArgument();
        int arg_pos = arg->getArgNo();
        OS << *instW->getArgument()->getType();
        return ("ACTUAL_OUT: " + std::to_string(arg_pos) + " " + OS.str());
      }
      case GraphNodeType::PARAMETER_FIELD:
      {
        llvm::Argument *arg = instW->getArgument();
        int arg_pos = arg->getArgNo();
        OS << *instW->getTreeNodeType() << " arg_pos: " << arg_pos << " - "
           << "f_id: " << instW->getNodeOffset();
        return OS.str();
      }
      case GraphNodeType::POINTER_RW:
      {
        OS << *instW->getArgument()->getType();
        return ("POINTER READ/WRITE : *" + OS.str());
      }
        // for pointer node, add a "*" sign before real node content
        // if multi level pointer, use a loop instead here

      case GraphNodeType::STRUCT_FIELD:
      {
        llvm::Instruction *inst = instW->getInstruction();
        llvm::AllocaInst *allocaInst = dyn_cast<AllocaInst>(inst);
        // processing differently when get a struct pointer
        llvm::StringRef struct_name = "";
        if (allocaInst->getAllocatedType()->isPointerTy())
        {
          llvm::PointerType *pt = dyn_cast<llvm::PointerType>(allocaInst->getAllocatedType());
          struct_name = pt->getElementType()->getStructName();
        }
        else
        {
          struct_name = allocaInst->getAllocatedType()->getStructName();
        }

        std::string struct_string = struct_name.str();
        std::vector<std::string> TYPE_NAMES = {
            "HalfTy",      ///<  0: 16-bit floating point type
            "BFloatTy",    ///<  1: 16-bit floating point type (7-bit significand)
            "FloatTy",     ///<  2: 32-bit floating point type
            "DoubleTy",    ///<  3: 64-bit floating point type
            "X86_FP80Ty",  ///<  4: 80-bit floating point type (X87)
            "FP128Ty",     ///<  5: 128-bit floating point type (112-bit mantissa)
            "PPC_FP128Ty", ///<  6: 128-bit floating point type (two 64-bits, PowerPC)
            "VoidTy",      ///<  7: type with no size
            "LabelTy",     ///<  8: Labels
            "MetadataTy",  ///<  9: Metadata
            "X86_MMXTy",   ///<  10: MMX vectors (64 bits, X86 specific)
            "X86_AMXTy",   ///<  11: AMX vectors (8192 bits, X86 specific)
            "TokenTy",     ///<  12: Tokens

            // Derived types... see DerivedTypes.h file.
            // Make sure FirstDerivedTyID stays up to date!
            "IntegerTy",        ///< 13: Arbitrary bit width integers
            "FunctionTy",       ///< 14: Functions
            "PointerTy",        ///< 15: Pointers
            "StructTy",         ///< 16: Structures
            "ArrayTy",          ///< 17: Arrays
            "FixedVectorTyID",  ///< Fixed width SIMD vector type
            "ScalableVectorTy", ///< Scalable SIMD vector type
        };
        llvm::Type *field_type = instW->getTreeNodeType();
        std::string type_name = TYPE_NAMES.at(field_type->getTypeID());

        std::string ret_string = "";
        std::string field_pos = std::to_string(instW->getNodeOffset());
        ret_string = struct_string + " (" + type_name + ") : " + std::to_string(instW->getNodeOffset());
        return (ret_string);
      }
      default:
        break;
      }

      // llvm::Instruction *inst = Node->getData()->getInstruction();
      llvm::Instruction *inst = instW->getInstruction();

      if (inst == nullptr)
        return OS.str();
      if (isSimple() && !inst->getName().empty())
        return inst->getName().str();
      else
      {
        std::string Str;
        raw_string_ostream OS(Str);
        OS << *inst;
        return OS.str();
      }
    }
  };

  template <>
  struct DOTGraphTraits<pdg::DependencyGraph<InstructionWrapper> *> : public DOTGraphTraits<pdg::DependencyNode<InstructionWrapper> *>
  {
    DOTGraphTraits(bool isSimple = false) : DOTGraphTraits<pdg::DependencyNode<InstructionWrapper> *>(isSimple) {}

    std::string getNodeLabel(pdg::DependencyNode<InstructionWrapper> *Node, pdg::DependencyGraph<InstructionWrapper> *Graph)
    {
      return DOTGraphTraits<pdg::DependencyNode<InstructionWrapper> *>::getNodeLabel(Node, *(Graph->begin_child()));
    }
  };

  template <>
  struct GraphTraits<pdg::ControlDependencyGraph2 *> : public GraphTraits<pdg::DependencyGraph<InstructionWrapper> *>
  {
    static NodeRef getEntryNode(pdg::ControlDependencyGraph2 *CG)
    {
      return *(CG->_getCDG()->begin_child());
    }

    static nodes_iterator nodes_begin(pdg::ControlDependencyGraph2 *CG)
    {
      return CG->_getCDG()->begin_child();
    }

    static nodes_iterator nodes_end(pdg::ControlDependencyGraph2 *CG)
    {
      return CG->_getCDG()->end_child();
    }
  };

  template <>
  struct DOTGraphTraits<pdg::ControlDependencyGraph2 *> : public DOTGraphTraits<pdg::DependencyGraph<InstructionWrapper> *>
  {
    DOTGraphTraits(bool isSimple = false) : DOTGraphTraits<pdg::DependencyGraph<pdg::InstructionWrapper> *>(isSimple) {}

    static std::string getGraphName(pdg::ControlDependencyGraph2 *)
    {
      return "Control Dependency Graph";
    }

    std::string getNodeLabel(pdg::DependencyNode<InstructionWrapper> *Node, pdg::ControlDependencyGraph2 *Graph)
    {
      return DOTGraphTraits<pdg::DependencyGraph<InstructionWrapper> *>::getNodeLabel(Node, Graph->_getCDG());
    }

    static bool isNodeHidden(pdg::DependencyNode<InstructionWrapper> *Node, pdg::ControlDependencyGraph2 *Graph)
    {
      if (Graph->dumpOnlyDep)
        return Node->getDependencyList().size() == 0;
      else
        return false;
    }
  };

}

void pdg::ControlDependencyGraph2::dump(std::string fileName)
{
  std::error_code ec;
  raw_fd_stream fd(fileName, ec);
  WriteGraph(fd, this);
}
