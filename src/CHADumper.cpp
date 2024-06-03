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
#include "SVF-LLVM/CHGBuilder.h"


using namespace SVF;
using namespace llvm;
using namespace std;

const Option<std::string> mainPath("main", "path to the main bc file", "");

int main(int argc, char **argv)
{
    OptionBase::parseOptions(argc, argv, "pre analysis for Constant Folding", "");
    LLVMContext ctxs[2];
    SMDiagnostic Err;
    unique_ptr<Module> mP;
    mP = parseIRFile(mainPath(), Err, ctxs[0]);
    Module *module = mP.get();

    if (module == nullptr)
    {
        outs() << Err.getMessage() << "\n";
        return -1;
    }

    LLVMModuleSet *svfModuleSet = LLVMModuleSet::getLLVMModuleSet();
    svfModuleSet->buildSVFModule(*module);

    CHGraph* chg = new CHGraph(svfModuleSet->getSVFModule());
    CHGBuilder chgbuilder(chg);
    chgbuilder.buildCHG();
    chg->dump("chg");
}