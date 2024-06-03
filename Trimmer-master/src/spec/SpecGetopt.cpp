
#include "SpecGetopt.h"
#include "../ConstantFolding.h"
#include "unistd.h"
#include "getopt.h"
#include "../Stats.h"
#include "../Debug.h"
bool handleLongArgs(CallInst *callInst, option *long_opts, int *&long_index)
{
    Value *val = callInst->getOperand(3);
    Register *reg = cf->processInstAndGetRegister(val);
    if (!reg)
    {
        debug(Yes) << "long_opts not found\n";
        return false;
    }
    uint64_t addr = reg->getValue();

    debug(Yes) << "Checking if addr: " << addr << " is constant\n";
    if (!bbOps.checkConstContigous(addr, cf->currBB))
    {
        debug(Yes) << "long_opts not constant\n";
        return false;
    }
    unsigned i = 0;
    unsigned size = bbOps.getSizeContigous(addr, cf->currBB);
    debug(Yes) << "Size of long options " << size / 32 << "\n";

    for (;;)
    {
        uint64_t nameAddr = bbOps.loadMem(addr, 8, cf->currBB);
        if (!nameAddr)
            break;
        long_opts[i].name = (char *)bbOps.getActualAddr(nameAddr, cf->currBB);
        long_opts[i].has_arg = bbOps.loadMem(addr + 8, 4, cf->currBB);
        uint64_t flagAddr = bbOps.loadMem(addr + 16, 8, cf->currBB);
        long_opts[i].flag = !flagAddr ? 0 : (int *)bbOps.getActualAddr(flagAddr, cf->currBB);
        long_opts[i].val = bbOps.loadMem(addr + 24, 4, cf->currBB);
        if (!long_opts[i].name)
            break;
        debug(Yes) << "{name: " << long_opts[i].name << ", has_args: " << long_opts[i].has_arg << ", flag: " << long_opts[i].flag << ", val: " << long_opts[i].val << "}\n";
        i++;
        addr += 32;
    }
    debug(Yes) << "i: " << i << "\n";
    Value *indexVal = callInst->getOperand(4);
    debug(Yes) << indexVal << " indexVal printing"
               << "\n";
    if (dyn_cast<ConstantPointerNull>(indexVal))
    {
        debug(Yes) << "indexVal is a Constant Pointer Null\n";
        long_index = NULL;
    }
    else
    {
        reg = cf->processInstAndGetRegister(indexVal);
        if (!reg)
        {
            debug(Yes) << "long_index not found\n";
            return false;
        }
        if (!bbOps.checkConstContigous(reg->getValue(), cf->currBB))
        {
            debug(Yes) << "long_index not constant\n";
            return false;
        }
        long_index = (int *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
    }
    memset((char *)&long_opts[i], '\0', sizeof(option));
    return true;
}

/**
 * Assumption that flags in argv will be constant. Non flag (optarg) can be non
 * constant due to dynamic values
 */
bool handleGetOpt(CallInst *ci)
{
    string name = ci->getCalledFunction()->getName().str();
    if (name.size() < 6 || name.substr(0, 6) != "getopt")
        return false;
    debug(Yes) << "Invoked handleGetOpt\n";
    if (name == "getopt_long_only")
    {
        debug(Yes) << "case not handled " << name << "\n";
        return true;
    }

    stats.incrementTotalLibCalls();

    uint64_t argc;
    Register *argvReg = cf->processInstAndGetRegister(ci->getOperand(1));
    Register *optsReg = cf->processInstAndGetRegister(ci->getOperand(2));
    Register *optindReg = NULL;
    if (cf->module->getNamedGlobal("optind"))
    {
        optindReg = cf->processInstAndGetRegister(cf->module->getNamedGlobal("optind"));
        if (!bbOps.checkConstContigous(optindReg->getValue(), cf->currBB))
        {
            debug(Yes) << " optind conditions not satisfied\n";
            return true;
        }
    }

    if (!cf->getSingleVal(ci->getOperand(0), argc) || !argvReg ||
        !optsReg)
    {
        debug(Yes) << "conditions not satisfied\n";
        if (cf->module->getNamedGlobal("optind"))
        {
            optindReg = cf->processInstAndGetRegister(cf->module->getNamedGlobal("optind"));
            bbOps.setConstContigous(false, optindReg->getValue(), cf->currBB);
        }
        return true;
    }

    debug(Yes) << "Obtaining argvSize...\n";
    uint64_t ptrSize = cf->DL->getTypeAllocSize(argvReg->getType());
    uint64_t intSize = cf->DL->getTypeAllocSize(ci->getType());

    uint64_t argvSize = bbOps.getSizeContigous(argvReg->getValue(), cf->currBB) - ptrSize;
    debug(Yes) << "argvSize: " << argvSize << "(Excluding NULL ptr)\n";

    debug(Yes) << "Check getopt from: " << argvReg->getValue() << ", to " << argvReg->getValue() + argvSize << "\n";

    if (!bbOps.checkConstContigous(argvReg->getValue(), cf->currBB))
    {

        if (!bbOps.checkConstMem(argvReg->getValue(), ptrSize, cf->currBB))
        {
            debug(Yes) << "conditions not satisfied argv non-constant\n";
            return true;
        }
        if (!bbOps.checkConstMem(argvReg->getValue() + ptrSize, ptrSize, cf->currBB))
        {
            debug(Yes) << "conditions not satisfied argv non-constant\n";
            return true;
        }
    }

    unsigned indice = 0;
    vector<unsigned> array;

    for (uint64_t start = argvReg->getValue(); start < argvReg->getValue() + argvSize; start += ptrSize)
    {
        debug(Yes) << "Checking address: " << start << "\n";
        if (!bbOps.checkConstMem(start, ptrSize, cf->currBB))
        {
            debug(Yes) << "[ArgvReg] starting at " << start << " for " << ptrSize << " bytes is non const\n";
            array.push_back(indice);
        }
        indice = indice + 1;
    }

    uint64_t argcLimit = argc;

    uint64_t optindAddr;
    if (optindReg)
    {
        optindAddr = optindReg->getValue();
        optind = bbOps.loadMem(optindAddr, intSize, cf->currBB);
    }
    char **argv = (char **)malloc(sizeof(char *) * argc);
    uint64_t addr = argvReg->getValue();
    map<char *, uint64_t> realToVirt;
    for (unsigned i = 0, iter = addr; i < argcLimit; i++, iter += ptrSize)
    {
        uint64_t strAddr = bbOps.loadMem(iter, ptrSize, cf->currBB);
        debug(Yes) << "Checking for index: " << i << "\n";
        if (find(array.begin(), array.end(), i) != array.end())
        {
            argv[i] = "_";
            continue;
        }
        if (!cf->getStr(strAddr, argv[i]))
        {
            debug(Yes) << "handleGetOpt: Non Constant argv at index" << i << "\n";
            if (i == optind)
            {
                debug(Yes) << "handleGetOpt: Flag not constant. Can not handle getopt \n";
                return true;
            }
        }
        debug(Yes) << "Got String " << argv[i] << "\n";

        realToVirt[argv[i]] = strAddr;
    }
    char *opts = (char *)bbOps.getActualAddr(optsReg->getValue(), cf->currBB);
    int result;
    if (name == "getopt_long")
    {
        debug(Yes) << "handleGetOpt: getopt_long\n";
        int *long_index;
        Register *longReg = cf->processInstAndGetRegister(ci->getOperand(3));
        if (!longReg)
        {
            debug(Yes) << "long options not found\n";
            return true;
        }
        uint64_t longAddr = longReg->getValue();
        unsigned size = bbOps.getSizeContigous(longAddr, cf->currBB);
        debug(Yes) << "size of long options " << size << "\n";
        option *long_opts = (option *)malloc(size);

        if (!handleLongArgs(ci, long_opts, long_index))
            return true;
        debug(Yes) << "Calling getopt_long_local\n";
        result = getopt_long(argcLimit, argv, opts, long_opts, long_index);
    }
    else
        result = getopt(argcLimit, argv, opts);

    IntegerType *intTy = IntegerType::get(cf->module->getContext(), intSize * 8);
    ConstantInt *resInt = ConstantInt::get(intTy, result);

    debug(Yes) << "getopt returned " << (char)result << "\n";
    cf->replaceIfNotFD(ci, resInt);

    Register *optargReg = cf->processInstAndGetRegister(cf->module->getNamedGlobal("optarg"));
    if (optarg == "_")
    {
        debug(Yes) << "optarg is " << optarg << "\n";
        bbOps.setConstContigous(false, optargReg->getValue(), cf->currBB);
    }

    if ((optarg && !optindReg) || (optarg && bbOps.checkConstMem(addr + (optind - 1) * ptrSize, ptrSize, cf->currBB)))
    {
        debug(Yes) << "optarg is " << optarg << "\n";

        Register *optargReg = cf->processInstAndGetRegister(cf->module->getNamedGlobal("optarg"));
        uint64_t optArgAddr = optargReg->getValue();
        uint64_t strAddr = bbOps.loadMem(optArgAddr, ptrSize, cf->currBB);
        debug(Yes) << "optArgAddr: " << optArgAddr << ", strAddr " << strAddr << "\n";
        if (!strAddr)
        {
            Type *ty = optargReg->getType()->getContainedType(0);
            uint64_t charSize = cf->DL->getTypeAllocSize(ty);
            strAddr = bbOps.allocateHeap(charSize * 100, cf->currBB);
            bbOps.storeToMem(strAddr, ptrSize, optArgAddr, cf->currBB);
            debug(Yes) << "created new string at " << strAddr << "\n";
        }
        char *source = (char *)bbOps.getActualAddr(strAddr, cf->currBB);
        memcpy(source, optarg, strlen(optarg));
        if (optarg == "_")
        {
            bbOps.setConstContigous(false, strAddr, cf->currBB);
            bbOps.setConstContigous(false, optargReg->getValue(), cf->currBB);
        }
        else
        {
            bbOps.setConstContigous(true, strAddr, cf->currBB);
            bbOps.setConstContigous(true, optargReg->getValue(), cf->currBB);
        }
        source[strlen(optarg)] = '\0';
        debug(Yes) << "Pasted string: " << source << " to addr " << strAddr << "\n";
    }

    if (optindReg)
        bbOps.storeToMem(optind, intSize, optindAddr, cf->currBB);
    for (unsigned i = 0, iter = addr; i < argcLimit; i++, iter += ptrSize)
    {
        if (find(array.begin(), array.end(), i) != array.end())
            continue;
        bbOps.storeToMem(realToVirt[argv[i]], ptrSize, iter, cf->currBB);
    }
    debug(Yes) << "Returning from handleGetOpt\n";
    stats.incrementInstructionsFolded();
    stats.incrementLibCallsFolded();
    return true;
}
