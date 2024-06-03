import subprocess
import pathlib
import os
import shutil
import elf
import pkgInfo
import config

typeSet = set()
def checkFileType(path:pathlib.Path):
    cmd = ["file",str(path)]
    res = subprocess.run(cmd,capture_output=True)
    msg = res.stdout.decode()
    if "ELF 64-bit LSB" in msg:
        return
    if "LLVM IR bitcode" in msg:
        return
    if "script" in msg:
        if path.with_name(path.name+".bc").exists():
            print("need to rebuild"+ str(path))
            return
        print("rm "+str(path))
        path.unlink()
        return
    typeSet.add(msg)

def iterExtract(pkgname):
    bcDir = "{}/{}".format(config.BC_DIR,pkgname)
    bcPath = pathlib.Path(bcDir)   
    items = list(bcPath.iterdir())
    if len(items) == 0:
        print("rm empty:"+str(bcPath))
        bcPath.rmdir()
    for item in items:
        checkFileType(item)

def checkExtract(pkgname):
    """
    判断pkg是否最终提取成功,即每一个elf文件都得到了对应的bc文件 
    """
    bcDir = "{}/{}".format(config.BC_DIR,pkgname)
    bcPath = pathlib.Path(bcDir)

    if not bcPath.exists():
        return False
    
    items = list(bcPath.iterdir())
    if len(items) == 0:
        return False
    
    for item in items:
        #文件夹下存在elf和对应的bc文件，此外还有.tmp结尾的分析过程文件
        if item.name.endswith(".bc") or item.name.endswith(".tmp"):
            continue

        #so和exec应该存在对应的bc文件
        bcFile = item.with_name(item.name+".bc")

        if not bcFile.exists():
            return False
    #print("{} is done".format(pkgname))
    return True 

class __pkgBuilder():
    def __init__(self) -> None:
        self.env = os.environ.copy()
        self.env["http_proxy"] = "http://192.168.1.106:10804"
        self.env["https_proxy"] = "http://192.168.1.106:10804"
        self.downloadErr = []
        self.buildErr = []
        self.extractErr= []
        self.doneList=[]
        self.pkgInfoBuilder = pkgInfo.pkgInfoBuilder

        #init done List
        for dir in pathlib.Path(config.BC_DIR).iterdir():
            #iterExtract(dir.name)
            if checkExtract(dir.name):
                self.doneList.append(dir.name)

    def downloadPkgFromGit(self,pkgname):
        url = "https://user:password@gitlab.archlinux.org/archlinux/packaging/packages/{}.git".format(pkgname)
        cmd = ["git","clone",url]    
        res = subprocess.run(cmd,env=self.env,cwd=config.BUILD_DIR,capture_output=True)
        if(res.returncode!=0):
            msg = res.stderr.decode()
            if("already exists and is not an empty directory." in msg):
                print("File exists, use old")
                return True
            else:
                #print("git error: "+res.stderr.decode())
                print("error,try ASP")
                return self.downloadPackageFromAsp(pkgname)

        return True

    def downloadPackageFromAsp(self,pkgname):
        cmd = ["asp","export",pkgname]
        res = subprocess.run(cmd,env=self.env,cwd=config.BUILD_DIR,capture_output=True)
        if(res.returncode!=0):
            msg = res.stderr.decode()
            if("File exists" in msg):
                print("File exists, use old")
                msg = True
            else:
                #print(res.stderr.decode())
                print("still error")
                msg = False
        else:
            msg = True

        if msg:
            pkginfo = self.pkgInfoBuilder.getPkgInfo(pkgname)
            if pkginfo.pkgbase != pkgname:
                rp = pathlib.Path("{}/{}".format(config.BUILD_DIR,pkginfo.pkgbase))
                p = pathlib.Path("{}/{}".format(config.BUILD_DIR,pkgname))
                assert(rp.exists() and (not p.exists()))
                rp.rename(p)
        return msg

    def sourceOnly(self,pkgname):
        pkgBuildDIr = "{}/{}/".format(config.BUILD_DIR,pkgname)
        for i in pathlib.Path(pkgBuildDIr).iterdir():
            if i.name == "src" and i.is_dir:
                print("use old")
                return True
        with open(pkgBuildDIr+"build.log","w") as logFd:
            cmd = ["makepkg","--nobuild","--skipinteg","--skippgpcheck","--rmdeps","--syncdeps","--noconfirm"]
            result = subprocess.run(cmd,cwd=pkgBuildDIr,env=self.env,text=True,stderr=subprocess.STDOUT,stdout=logFd)

        if(result.returncode!=0):
            print("error: get source failed, check build.log for details")
            return False

        return True

    def buildPkg(self,pkgname):
        pkgBuildDIr = "{}/{}/".format(config.BUILD_DIR,pkgname)
        for i in pathlib.Path(pkgBuildDIr).iterdir():
            if i.name.startswith(pkgname) and i.name.endswith("pkg.tar.zst"):
                #print("==> already build package, use old")
                return True
        #makepkg --config /home/xd/archIR/makepkg.conf  --skipinteg --rmdeps --syncdeps --noconfirm
        with open(pkgBuildDIr+"build.log","w") as logFd:
            cmd = ["makepkg","--config",config.MAKECONFIG,"--skipinteg","--rmdeps","--syncdeps","--noconfirm"]
            result = subprocess.run(cmd,cwd=pkgBuildDIr,env=self.env,text=True,stderr=subprocess.STDOUT,stdout=logFd)

        if(result.returncode!=0):
            with open(pkgBuildDIr+"build.log","r") as logFd:
                buf = logFd.read()
                if(buf.find("==> ERROR: A package has already been built. (use -f to overwrite)")!=-1 or
                buf.find("==> ERROR: The package group has already been built.")!=-1):
                    print("==> already build package, use old")
                    return True
                elif(buf.find("==> ERROR: 'pacman' failed to install missing dependencies.")!=-1):
                    print("error: failed to install missing dependencies")
                    return False
                else:
                    print("error: makepkg failed, check build.log for details")
                    return False
        return True

    def extractPkg(self,pkginfo,onlySo):
        """ 
        从pkg中提取bc (寻找so库和elf) 
        
        """
        def extractFile(elfPath,dstDir):
            """
            提取elf以及对应的bc文件 
            """
            elfName = pathlib.Path(elfPath).name
            targetPath = "{}/{}.bc".format(dstDir,elfName)
            shutil.copy(elfPath,dstDir)
            env = {"LLVM_LINK_NAME":"/usr/lib/llvm14/bin/llvm-link",
                "LLVM_AR_NAME":"/usr/lib/llvm14/bin/llvm-ar"}
            cmd = ["extract-bc","--output",targetPath,elfPath]
            subprocess.run(cmd,env=env)
                            
        execList,soList = elf.getElfFiles("{}/{}/pkg".format(config.BUILD_DIR,pkginfo.pkgname))   
        #没能在pkg下找到任何elf文件 
        if len(execList) == 0 and len(soList) == 0:
            return False
        
        dstDir = pkginfo.bcDir
        if not os.path.exists(dstDir):
            os.mkdir(dstDir)
            
        for so in soList:
            extractFile(so,dstDir)
        if not onlySo:
            for exec in execList:
                extractFile(exec,dstDir)

        return checkExtract(pkginfo.pkgname)
        
    def doInitPkg(self,pkgname,onlySo):
        if pkgname in self.doneList:
            return

        print("init pkg:{}".format(pkgname))
        pkginfo = self.pkgInfoBuilder.getPkgInfo(pkgname)

        if not self.downloadPkgFromGit(pkgname):
            self.downloadErr.append(pkgname)
            return False
        pkginfo.getVersionFromBUILD()
  
        if not self.buildPkg(pkgname):
            self.buildErr.append(pkgname)
            return False

        if not self.extractPkg(pkginfo,onlySo):
            self.extractErr.append(pkgname)
            return False
        return True

    def cleanfailPkg(self):
        """
        清理没能成功编译的软件包
        """
        buildSet = set().union(self.downloadErr).union(self.buildErr)

        for pkgname in buildSet:
            path = "{}/{}".format(config.BUILD_DIR,pkgname)
            if os.path.exists(path):
                os.rmdir(path)

    def initVulPkg(self,buildSet):
        """
        构建ossVul中的pkg,并提取so和bc保存到该pkg命名的bc-results文件夹下
        """
        for item in buildSet:
            pkgname = item["name"]
            self.doInitPkg(pkgname,True)

    def initDepPkg(self,buildSet):
        """
        构建依赖ossVul的pkg的包,并提取elf和bc保存到pkg命名的bc-results文件夹下
        目前每个pkg仅构建成功10个rdep包
        """
        for item in buildSet:
            pkgname = item["name"]
            pkginfo = self.pkgInfoBuilder.getPkgInfo(pkgname)
            limit = 100
            succ = 0
            
            doneSet = set().union(pkginfo.rdepends).intersection(self.doneList)
            rdone = 0
            for rpkgname in doneSet:
                rpkginfo = self.pkgInfoBuilder.getPkgInfo(rpkgname)
                if "lib" in rpkginfo.description.lower() or "lib" in rpkgname:
                    continue
                rdone +=1
            print("{}'s rdep pkg:{},done:{},rdone:{}".format(pkgname,len(pkginfo.rdepends),len(doneSet),rdone))
            #continue
            if rdone >= limit:
                continue

            
            for rpkgname in pkginfo.rdepends:
                #如果已经构建成功了limit个包，就退出。因为某些包的rdep数量过于多
                if succ >= limit:
                    break

                rpkginfo = self.pkgInfoBuilder.getPkgInfo(rpkgname)
                #别构建lib包，意义不大
                if "lib" in rpkginfo.description.lower() or "lib" in rpkgname:
                    continue
                
                #rpkg的install大小不超过10M，否则构建太慢
                if rpkginfo.sizeKB > 10*1024:
                    continue

                #之前失败过就先别再尝试了
                if pkgname in self.downloadErr or pkgname in self.buildErr or pkgname in self.extractErr:
                    continue

                if self.doInitPkg(rpkgname,False):
                    succ += 1

    def printResult(self):
        if len(self.downloadErr) != 0:
            print("download ERR:")
            print(self.downloadErr)
        if len(self.buildErr) != 0:
            print("build ERR:")
            print(self.buildErr)
        if len(self.extractErr) != 0:
            print("extract ERR:")
            print(self.extractErr)

pkgBuilder = __pkgBuilder()

""" def handleInstance(libName,pkgInfo:pkgInfo,buildOption):
    # 用llvm构建库
    print("handle RB package {} for {}".format(pkgInfo.pkgname,libName))
    resStr = ""
    downloadRequiredByPackage(pkgInfo,libName)
    packageName = pkgInfo.pkgbase
    #让用户确认是否真的要编译或直接编译
    while(True):
        an = buildOption
        if (buildOption == "a"):
            an = input("build {} ? (y/n)".format(packageName))
        if(an == "y"):
            print("==> building...")
            if(buildRequiredByPackage(packageName)):
                # 编译结束，从编译路径下，找出所有的elf和so输出，提取它们的bc文件 
                elfFiles = getElfFilesInBuildDir(packageName)
                print("==> extracting bc files")
                for elfFile in elfFiles:
                    requireLib = False
                    for soName in getImportSO(elfFile):
                        if libName in soName:
                            requireLib = True
                    if(requireLib):
                        #print(getImportFuncList(elfFile))
                        print("\t"+elfFile)
                        extractBC(elfFile,packageName)
                # 分析bc文件集合，找到调用库代码的部分
                resStr = "done"
            else:
                resStr = "error"
            break
        elif (an == "n"):
            break
    print(resStr+"\n")
    return resStr 
    
    
  
    
"""
