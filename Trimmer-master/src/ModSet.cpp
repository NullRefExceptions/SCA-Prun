#include "ModSet.h"
#include "Debug.h"
#include "ConstantFolding.h"
//==============ModSet related=======================
/*
// 1) collect any load on any global in current
// function. add globals to func mod set
// 2) traverse call graph of each function, and
// add mod sets of called functions in callees
// 3) In case a cycle is found, duplicate mod
//  set to all the functions in the cycle
// 4) A function calling a function part of a cycle
// will always be a superset of the mod set of the
// functions in the cycle
 */
map<Function *, set<GlobalVariable *>> modSet;

Cycle *mergeCycles(set<Cycle *> &cycles)
{
    Cycle *newCycle = new Cycle;
    for (auto &cycle : cycles)
    {
        newCycle->nodes.insert(cycle->nodes.begin(), cycle->nodes.end());
        newCycle->values.insert(cycle->values.begin(), cycle->values.end());
    }

    return newCycle;
}

set<GlobalVariable *> dfs(CallGraphNode *root, map<Function *, set<GlobalVariable *>> &modSet, set<Function *> &openNodes, vector<Function *> &recStack, map<Function *, Cycle *> &cycles)
{
    static set<Function *> processed;
    if (!root)
        return set<GlobalVariable *>();

    Function *F = root->getFunction();
    if (!F)
        return set<GlobalVariable *>();

    if (F->isDeclaration())
        return set<GlobalVariable *>();

    if (processed.find(F) != processed.end())
    {
        // might be part of a cycle. Need to add this function to that cycle too
        return modSet[F];
    }

    if (openNodes.find(F) != openNodes.end())
    {
        // handle cycle
        debug(0) << "Cycle found : "
                 << "\n";
        set<Cycle *> oldCycles;
        set<Function *> cycleFunctions;

        cycleFunctions.insert(F);
        // find if part of any cycle already
        for (int i = recStack.size() - 1; recStack[i] != F; i--)
        {
            assert(i > -1);
            if (cycles.find(recStack[i]) != cycles.end())
                oldCycles.insert(cycles[recStack[i]]);
            cycleFunctions.insert(recStack[i]);
        }

        if (cycles.find(F) != cycles.end())
            oldCycles.insert(cycles[F]);

        Cycle *newCycle;

        if (oldCycles.size() > 1)
            newCycle = mergeCycles(oldCycles);
        else
            newCycle = new Cycle;

        // merge cycle functions
        newCycle->nodes.insert(cycleFunctions.begin(), cycleFunctions.end());

        // merge values
        for (auto &func : cycleFunctions)
        {
            newCycle->values.insert(modSet[func].begin(), modSet[func].end());
        }

        for (auto &func : cycleFunctions)
            modSet[func] = newCycle->values;

        // update cycle reference
        for (auto &func : cycleFunctions)
            cycles[func] = newCycle;

        return set<GlobalVariable *>();
    }

    openNodes.insert(F);
    recStack.push_back(F);

    set<GlobalVariable *> data = modSet[F];

    set<CallGraphNode *> children_visited;

    for (unsigned i = 0, end = root->size(); i != end; i++)
    {
        auto called = (*root)[i];
        if (!called)
            continue;

        if (children_visited.find(called) != children_visited.end())
            continue;

        children_visited.insert(called);
        set<GlobalVariable *> childData = dfs(called, modSet, openNodes, recStack, cycles);

        data.insert(childData.begin(), childData.end());
    }

    openNodes.erase(F);
    recStack.pop_back();
    modSet[F].insert(data.begin(), data.end());
    processed.insert(F);
    return data;
}

set<GlobalVariable *> &getFuncModset(Function *F)
{

    if (modSet.find(F) != modSet.end())
        return modSet[F];
    else
    {
        modSet[NULL] = set<GlobalVariable *>();
        return modSet[NULL];
    }
}

void collectModSet(GlobalVariable *gv, map<Function *, set<GlobalVariable *>> &modSet)
{
    for (auto user : gv->users())
    {
        Instruction *I;
        if (!(I = dyn_cast<Instruction>(user)))
            continue;
        Function *F = I->getParent()->getParent();
        modSet[F].insert(gv);
    }
}

void initModSet(CallGraph *CG)
{
    auto start = std::chrono::high_resolution_clock::now();
    debug(0) << "PRINTING CALL GRAPH\n";
    map<Function *, Cycle *> cycles;
    set<Function *> openNodes;
    vector<Function *> recStack;

    for (auto &global : cf->module->global_objects())
        if (dyn_cast<GlobalVariable>(&global))
            collectModSet(dyn_cast<GlobalVariable>(&global), modSet);

    Function *main = CG->getModule().getFunction("main");
    assert(main);
    for (auto &kv : modSet)
    {
        Function *F = kv.first;
        debug(0) << "Function: " << F->getName() << "\n";
        for (auto &val : kv.second)
        {
        }
    }
    dfs(CG->getOrInsertFunction(main), modSet, openNodes, recStack, cycles);
    set<Function *> openNodes_two;
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    debug(0) << "[MODREF] Analysis took: " << duration.count() << " microseconds... \n";
}

modinfo_struct getModInfo(Function *f, uint64_t ctxIdx)
{
    if (f->isDeclaration() || f->isIntrinsic())
        assert(false);
    //! mdinfo = !{{ctxId,start,end},{ctxId,start,end},...}

    modinfo_struct res;
    MDNode *MDINFO = f->getMetadata("mdinfo");
    MDNode *MDctx = dyn_cast<MDNode>(MDINFO->getOperand(ctxIdx));
    ConstantInt *start = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(MDctx->getOperand(1))->getValue());
    ConstantInt *end = dyn_cast<ConstantInt>(dyn_cast<ConstantAsMetadata>(MDctx->getOperand(2))->getValue());
    res.start = start->getZExtValue();
    res.end = end->getZExtValue();
    //res.start = 0; // delete me
    //res.end = UINT64_MAX; // delete me
    return res;
}