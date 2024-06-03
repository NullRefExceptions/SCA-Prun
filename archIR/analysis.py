import pathlib
import moduleInfo as mi
import pkgInfo
import build
import json
import subprocess
import config

class tinyInfo():
    def __init__(self) -> None:
        self.depList = []
        self.apiStrMap = {}

class __pkgAnalysis():
    def __init__(self) -> None:
        self.__tinyInfo = tinyInfo()
        self.__mvInfoBuilder = mi.moduleInfoBuilder
        self.__pkgInfoBuilder = pkgInfo.pkgInfoBuilder

    def fillDep(self,mvinfo:mi.moduleInfo,rmvinfo:mi.moduleInfo):
        apiString = ":".join(mvinfo.exportFuncs)
        bcPath = str(mvinfo.bcPath.relative_to(config.ROOT_DIR))
        rbcPath = str(rmvinfo.bcPath.relative_to(config.ROOT_DIR))
        print("fill "+rbcPath)

        self.__tinyInfo.depList.append((rbcPath,bcPath))
        if bcPath not in self.__tinyInfo.apiStrMap:
            self.__tinyInfo.apiStrMap[bcPath] = apiString
        

    def dumpDep(self):
        with open("tiny.json","w") as fd:
            output = {}
            output["depList"] = self.__tinyInfo.depList
            output["apiStrMap"] = self.__tinyInfo.apiStrMap
            json.dump(output,fd)

    def checkDep(self,mvinfo:mi.moduleInfo,rmvinfo:mi.moduleInfo):
        def getSoName(soName:str):
            idx = soName.find(".so")
            return soName[:idx]+".so"
        elfName = mvinfo.elfPath.name
        if(".so" not in elfName):
            return False

        soName = getSoName(elfName)
        for rSo in rmvinfo.importSo:
            if getSoName(rSo) == soName:
                return True
        
        return False

    def analysisDepPkg(self,analysisSet):
        """ 
        对Dep进行分析,给定合法的pkg和dep的moduleInfo
        """

        for item in analysisSet:
            pkgname = item["name"]
            if not build.checkExtract(pkgname):
                continue

            pkginfo = self.__pkgInfoBuilder.getPkgInfo(pkgname)  
            for rpkgname in pkginfo.rdepends:
                if not build.checkExtract(rpkgname):
                    continue
                rpkginfo = self.__pkgInfoBuilder.getPkgInfo(rpkgname) 
                for bc in pkginfo.getBCList():
                    for rbc in rpkginfo.getBCList():
                        mvinfo = self.__mvInfoBuilder.getInfo(bc)
                        rmvinfo = self.__mvInfoBuilder.getInfo(rbc)
                        if self.checkDep(mvinfo,rmvinfo):
                            #self.analysisDep(mvinfo,rmvinfo)
                            #printInfoDep(mvinfo,rmvinfo)
                            self.fillDep(mvinfo,rmvinfo)

    def analysisVulPkg(self,analysisSet):
        """
        对Vulpkg进行分析,对其中包含的所有module进行可利用性的分析,包括：
            提取call graph,并判断api到cve之间的可达性

        """
        for item in analysisSet:
            pkgname = item["name"]
            pkginfo = self.__pkgInfoBuilder.getPkgInfo(pkgname)

            if not pkginfo.extracted():
                continue
            for bcPath in pathlib.Path(pkginfo.bcDir).iterdir():
                #跳过非bc文件
                if not bcPath.name.endswith(".bc"):
                    continue
                mvInfo = self.__mvInfoBuilder.getInfo(bcPath)
                self.getModuleVulSummary(mvInfo,pkginfo)

    def printInfoDep(self,mvinfo:mi.moduleInfo,rmvinfo:mi.moduleInfo):
        print("{} deps {}".format(rmvinfo.pkgname,mvinfo.pkgname))

    def getModuleVulSummary(self,mvinfo:mi.moduleInfo,pkginfo:pkgInfo.pkgInfo):
        """
        遍历api得到其到达所有可达cveFunc的Dep的最小值和平均值
        之后所有api的Dep的最小值和平均值作为module的
        """
        apiVulInfos = {} #我们将so的导出函数看作api函数
        for apiFunc in mvinfo.exportFuncs:
            apiVulInfos[apiFunc] = {}
        
        cg = mvinfo.getCG()

        def getApiVulSummary(apiVulInfo):
            depList = []
            for cveFunc,dep in apiVulInfo.items():
                if dep != -1:
                    depList.append(dep)
            return depList
        
        def analysisVulReach(cveinfos):
            """
            分析该module下所有cve的危害性,最终给出api安全性列表,其中包含该api函数能够到达的cve
            """
            def getMinDepOnApi(apiFunc,cveFunc):
                """
                在callgraph上检查api函数到达cveFunc的路径和其上的条件约束的数量,返回：
                    -1  --> 不存在api到达cveFunc的路径
                    其他 --> 所有路径中条件约束数量的最小值
                """
                paths = cg.getPath(apiFunc,cveFunc)
                if len(paths) == 0:
                    return -1
                
                minDepOnApi = 99999999
                for path in paths:
                    minDepOnPath = 0
                    for edge in path:
                        minDepOnPath += cg.getEdgeData(edge)["minDep"]
                    if minDepOnApi > minDepOnPath:
                        minDepOnApi = minDepOnPath
                return minDepOnApi

            for cveinfo in cveinfos:
                #我们没能获取该cve对应的FuncList信息,直接跳过
                if cveinfo.cveFuncList == None:
                    continue
                for cveFunc in cveinfo.cveFuncList:
                    #该cveFunc没有在该bc中出现,直接跳过
                    if cg.getNodeIdByName(cveFunc) == None:
                        continue
                    #计算每一个api到达该cveFunc的路径信息
                    for apiFunc in mvinfo.exportFuncs:
                        apiVulInfos[apiFunc][cveFunc] = getMinDepOnApi(apiFunc,cveFunc)

        
        analysisVulReach(pkginfo.cveinfos)
        apiDepList = []
        for api in mvinfo.exportFuncs:
            depList = getApiVulSummary(apiVulInfos[api])
            if len(depList)==0:
                continue
            apiDepList.append(sum(depList)/len(depList))
            
        if len(apiDepList) == 0:
            print("{} has no cve info".format(mvinfo.elfPath))
        else:
            avaReach = len(apiDepList)/len(mvinfo.exportFuncs)
            avaDep = sum(apiDepList)/len(apiDepList)
            print("{} with ava reach={} ,ava dep={}".format(mvinfo.elfPath,avaReach,avaDep))
    
    def analysisDep(self,mvinfo:mi.moduleInfo,rmvinfo:mi.moduleInfo):
        apiString = ":".join(mvinfo.exportFuncs)
        rbcPath = rmvinfo.bcPath
        cmd = ["./tiny",apiString,rbcPath]
        res = subprocess.run(cmd,capture_output=True).stdout.decode()
        if "caller size:" in res:
            print("info for {}:{}".format(rmvinfo.elfPath,res))
        else:
            print("err for {}:{}".format(rmvinfo.elfPath,res))


pkgAnalysis = __pkgAnalysis()