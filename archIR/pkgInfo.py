import config
import subprocess
import tarfile
import json
import pickle
import os
import build
import pathlib

def getDependsPkg(pkgname):
    """
    不包含makedepends和optdepends的情况 
    """
    cmd = ["pacman", "-Sii", pkgname]
    packages = []
    result = subprocess.run(cmd, capture_output=True)
    packageLine = False
    for line in result.stdout.decode().split('\n'):
        if line.startswith("Depends On      : "):
            packageLine = True
            packages.extend(line.split("Depends On      : ")[1].split())
            continue
        if ':' in line:
            packageLine = False
        if (packageLine):
            packages.extend(line.strip().split())
    return packages

def getRDependsPkg(pkgname):
    cmd = ["pacman", "-Sii", pkgname]
    packages = []
    result = subprocess.run(cmd, capture_output=True)
    if result.stderr.decode() == "error: package '{}' was not found\n".format(pkgname):
        return None
    packageLine = False
    for line in result.stdout.decode().split('\n'):
        if line.startswith("Required By     : "):
            packageLine = True
            packages.extend(line.split("Required By     : ")[1].split())
            continue
        if ':' in line:
            packageLine = False
        if (packageLine):
            packages.extend(line.strip().split())
    return packages

class pkgInfo():
    def __init__(self) -> None:
        self.pkgname = None
        self.pkgbase = None
        self.version = None
        self.description = None
        self.depends:list[str] = None
        self.rdepends:list[str] = None
        self.sizeKB = None
        self.cveinfos:list[cveInfo] = None
        self.pkgfile = None
        self.PKGBUILDPath = None
        self.bcDir = None
        self.rbcDir = None
    
    def getVersionFromBUILD(self):
        """
        版本信息必须从PKGBUILD文件获取,从pacman获得的不一定准确 
        """
        with open(self.PKGBUILDPath) as fd:
            for line in fd.readlines():
                if not line.startswith("pkgver"):
                    continue
                self.version = line.split("=")[1].removesuffix("\n")
                return
            
    def extracted(self):
        return build.checkExtract(self.pkgname)
    
    def getBCList(self):
        res = []
        for item in pathlib.Path(self.bcDir).iterdir():
            if item.name.endswith(".bc"):
               res.append(item.resolve())
        return res 

class cveInfo():
    def __init__(self) -> None:
        self.cveName = None
        self.cveFuncList = []

class __pkgInfoBuilder():
    """
    获取pkgInfo 
    """
    def __init__(self) -> None:
        self.dbs = []
        self.ossVul = json.load(open("dataset/ossVul.json"))
        self.cve2func= json.load(open("dataset/cve2func.json"))
        self.infos:dict[str,pkgInfo] = {}
        self.dbs.append(tarfile.open("/var/lib/pacman/sync/core.db"))
        self.dbs.append(tarfile.open("/var/lib/pacman/sync/extra.db"))
        if os.path.exists("cache/pkginfos"): 
            self.infos = pickle.load(open("cache/pkginfos","rb"))

    def dumpInfo(self):
        with open("cache/pkginfos","wb") as fd:
            pickle.dump(self.infos,fd)        

    def getDescContent(self,descContent,name):
        lines = descContent.split('\n')
        for i in range(len(lines)):
            if(lines[i]==name):
                return lines[i+1]

    def createPkgInfo(self,pkgname):
        info = pkgInfo()
        desc = None
        for db in self.dbs:
            for name in db.getnames():
                if(name.startswith(pkgname) and name.endswith("desc")):
                    desc = db.extractfile(name).read().decode()
                    break
        info.pkgname = pkgname
        info.pkgbase = self.getDescContent(desc,"%BASE%")
        info.sizeKB = int(self.getDescContent(desc,"%ISIZE%")) / 1024
        info.pkgfile = self.getDescContent(desc,"%FILENAME%")
        info.description = self.getDescContent(desc,"%DESC%")
        info.depends = getDependsPkg(pkgname)
        info.rdepends = getRDependsPkg(pkgname)
        info.PKGBUILDPath = "{}/{}/PKGBUILD".format(config.BUILD_DIR,info.pkgname)

        info.bcDir = "{}/{}".format(config.BC_DIR,pkgname)
        info.rbcDir = "{}/{}-dep/".format(config.BC_DIR,pkgname)

        info.cveinfos = []
        if pkgname in self.ossVul:
            for cve in self.ossVul[pkgname]:
                if cve in self.cve2func:
                    cveinfo = cveInfo()
                    cveinfo.cveName = cve
                    cveinfo.cveFuncList = self.cve2func[cve]                    
                    info.cveinfos.append(cveinfo)
        return info

    def getPkgInfo(self,pkgname):
        if(pkgname in self.infos):
            return self.infos[pkgname]
        else:
            info = self.createPkgInfo(pkgname)
            self.infos[pkgname] = info
            self.dumpInfo()
            return info


pkgInfoBuilder = __pkgInfoBuilder()

""" class pkgInfoNetWork():        
    def __eq__(self, __value: object) -> bool:
        return self.pkgbase == __value.pkgbase
    
    def __init__(self,pkgname) -> None:
        self.pkgname = pkgname
        proxies = {'http': 'http://192.168.1.106:10804','https': 'http://192.168.1.106:10804'}
        self.response = requests.get('https://archlinux.org/packages/search/json/?name={}'.format(pkgname),proxies=proxies).json()
        r = self.response
        if(len(r["results"])!=0):
            self.pkgbase = r["results"][0]["pkgbase"]
            self.depends = r["results"][0]["depends"]
            self.optdepends = r["results"][0]["optdepends"]
            self.makedepends = r["results"][0]["makedepends"]
            self.checkdepends = r["results"][0]["checkdepends"]
            self.found = True
            self.result = r["results"][0]
        else:
            self.found = False 
            
    def getPkgInstallSizeKB(pkgname):
    cmd = ["pacman", "-Sii", pkgname]
    result = subprocess.run(cmd, capture_output=True)
    sizeKB = 0
    for line in result.stdout.decode().split('\n'):
        if line.startswith("Installed Size  : "):
            res = line.split("Installed Size  : ")[1].split()
            if res[1] == "MiB":
                sizeKB = float(res[0])*1024
            elif res[1] == "KiB":
                sizeKB = float(res[0])
            else:
                print("unknown size:{} {}".format(res[0],res[1]))
    return sizeKB       
            
            """


