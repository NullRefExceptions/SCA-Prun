import json
import pkgInfo
import sqlite3

    
class cpeInfo():
    #cpe:2.3:a:wouter_verhelst:nbd:2.9.14:*:*:*:*:*:*:*
    def __init__(self,cpe:str) -> None:
        items = cpe.split(":")
        assert(len(items)==12)
        self.version = items[1]
        self.part = items[2]
        self.vendor = items[3]
        self.product = items[4]
        self.version = items[5]

class DBInfo():
    def __init__(self) -> None:
        self.db = sqlite3.connect("dataset/CVEfixes.db")
        self.cur = self.db.cursor()
        self.missCVE = set()
        self.okCVE = set()

    def getFuncList(self,cve):
        self.cur.execute("select cve_id ,name from cve2method where cve_id == '{}'".format(cve))
        res = self.cur.fetchall()
        if len(res)==0:
            self.missCVE.add(cve)
            return None
        funcList = []
        for line in res:
            funcList.append(line[1])
        self.okCVE.add(cve)
        return funcList
            
    def getNodes(self,cve):
        self.cur.execute("select cve_id ,nodes from cve where cve_id == '{}'".format(cve))
        res = self.cur.fetchall()
        if len(res)==0:
            self.missCVE.add(cve)
            return None
        else:
            self.okCVE.add(cve)
            return eval(res[0][1])

def importData():
    ossVul = {}
    def getdb(path):
        with open(path) as fd:
            db = json.load(fd)
        for name,cveList in db.items():
            if name not in ossVul:
                ossVul[name] = []
            for cve in cveList:
                if cve not in ossVul[name]:
                    ossVul[name].append(cve)

    getdb("dataset/diversevul/ossVul.json")
    getdb("dataset/patchdb/ossVul.json")
    getdb("dataset/v1scan/ossVul.json")
    return ossVul
        
def generateDB():
    """ 
    我们需要在dataset文件夹下构建3张表
        1.ossVul.json - 包含所有ossname到其存在的cve列表,以及该cve存在的版本
        2.cve2func.json - 包含所有cve到漏洞函数的列表
        3.cve2version.json - 包含所有cve到其影响的库的版本信息(TODO)
        需要注意,ossVul是由其他数据集提取出的,但cve2func和cve2version是由cvefixes数据库提取
        的，存在找不到信息的情况
    """    
    db = DBInfo()
    ossVul = importData()
    with open("dataset/ossVul.json","w") as fd:
        json.dump(ossVul,fd)
    
    cve2func = {}
    for ossname,cveList in ossVul.items():
        for cve in cveList:
            cve2func[cve] = db.getFuncList(cve)
    with open("dataset/cve2func.json","w") as fd:
        json.dump(cve2func,fd)

    print("miss:{},ok:{}".format(len(db.missCVE),len(db.okCVE)))

def printConfig():
    """
    对所有ossname,首先筛除不能被pacman找到的,将其放入dataset/unknown
    之后对能够找到的,产生buildSet和exculdeSet,用于粘贴到config文件中
    """
    ossVul = importData()
    knownList = []
    unknownList = []
    for pkgname in ossVul.keys():
        r = pkgInfo.getRDependsPkg(pkgname)
        if r == None:
            unknownList.append(pkgname)
        else:
            knownList.append(pkgname)
    with open("dataset/unknown","w") as fd:
        fd.writelines(unknownList) 

    def pp(infoSet):
        print("[",end="")
        for item in infoSet:
            print(json.dumps(item),end=",\n")
        print("]")

    buildSet = []
    exculdeSet = []

    pb = pkgInfo.pkgInfoBuilder
    for name in knownList:
        pi = pb.getPkgInfo(name)
        temp = {}
        temp["name"] = name
        temp["desc"] = pi.description
        temp["rdep"] = len(pi.rdepends)        
        if "lib" in pi.description.lower() or "lib" in name:
            buildSet.append(temp)
        else:
            exculdeSet.append(temp)

    def key(info):
        return info["rdep"]
    buildSet.sort(key=key,reverse=True)
    exculdeSet.sort(key=key,reverse=True)
    
    pp(buildSet)
    print("\n\n\n")
    pp(exculdeSet)


generateDB()