import pickle
import os
import callgraph
import elf
import pathlib


class moduleInfo():
    """ 
    保存某个module中与漏洞相关的数据
    """
    def __init__(self,bcPath) -> None:
        self.bcPath =  pathlib.Path(bcPath)
        self.pkgname = self.bcPath.parent.name
        self.elfPath = bcPath.with_suffix("")
        self.exportFuncs = elf.getExportFuncList(self.elfPath)
        self.importSo = elf.getImportSO(self.elfPath)
        self.importFuncs = elf.getImportFuncList(self.elfPath)
    
    def getCG(self):
        return callgraph.CallGraph(str(self.bcPath))
                        
class __moduleInfoBuilder():
    def __init__(self) -> None:
        self.moduleInfos = {}
        if os.path.exists("cache/moduleInfos"): 
            self.moduleInfos = pickle.load(open("cache/moduleInfos","rb"))

    def getInfo(self,bcPath) -> moduleInfo:
        if bcPath in self.moduleInfos:
            return self.moduleInfos[bcPath]
        else:
            vi = moduleInfo(bcPath)
            self.moduleInfos[bcPath] = vi
            with open("cache/moduleInfos","wb") as fd:
                pickle.dump(self.moduleInfos,fd)
            return vi
        

moduleInfoBuilder = __moduleInfoBuilder()