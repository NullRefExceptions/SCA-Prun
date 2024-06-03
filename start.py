import json
import subprocess
import pathlib
import pickle
import os
import networkx as nx
import signal
import resource
import enum

archIR_DIR = "./archIR"


class CallGraph():
    def __init__(self, dotFile) -> None:
        self.dotFile = dotFile
        self.g = nx.DiGraph(nx.nx_pydot.read_dot(self.dotFile))
        self.NameToId = {}

        for nodeId in self.g.nodes:
            name = self.getNodeNameById(nodeId)
            self.NameToId[name] = nodeId

    def getNodeNameById(self, nodeId):
        data = self.g.nodes[nodeId]
        if ("label" in data):
            return data["label"][2:-2]
        elif nodeId == "\\n":
            return "Void Node Name"
        else:
            return "Empty Name"

    def getNodeIdByName(self, name):
        if name in self.NameToId:
            return self.NameToId[name]
        else:
            return None

    def getNodeData(self, nodeId):
        return self.g.nodes[nodeId]

    def getEdgeData(self, edge):
        res = {}
        datas = self.g.get_edge_data(edge[0], edge[1])[
            "label"][1:-1].split(',')
        for data in datas:
            t = data.split('=')
            res[t[0]] = int(t[1])
        return res

    def getAnyPathToDst(self, srcName, dstName):
        srcNode = self.getNodeIdByName(srcName)
        dstNode = self.getNodeIdByName(dstName)
        if srcNode == None or dstNode == None:
            return None

        try:
            return nx.shortest_path(self.g, srcNode, dstNode)
        except nx.exception.NetworkXNoPath:
            return None

    def dumpPath(self, srcName, dstName):
        print("path from {} ==> {}".format(srcName, dstName))
        path = self.getAnyPathToDst(srcName, dstName)
        if path == None:
            print("no path found")
        else:
            for i in path:
                print(self.getNodeNameById(i))

    def saveGraph(self):
        nx.nx_pydot.write_dot(self.g, self.dotFile)


class TargetStatus(enum.Enum):
    notStarted = 1
    exitedNormal = 2
    exitedAbNormal = 3


class Target():
    def __init__(self, mbcPath, lbcPath) -> None:
        self.mbcPath: str = mbcPath  # 主模块路径
        self.lbcPath: str = lbcPath  # 库模块路径
        self.Data: dict = None  # 主模块数据

        mName = pathlib.Path(self.mbcPath).name
        lName = pathlib.Path(self.lbcPath).name
        workPath = pathlib.Path(self.mbcPath).parent
        self.mmbcPath: str = str(workPath.joinpath(
            "{}.{}.tiny.tmp".format(mName, lName)))  # 削减后主模块路径
        self.linkedbcPath: str = str(workPath.joinpath(
            "{}.{}.linked.tmp".format(mName, lName)))  # linked模块路径
        self.csmbcPath: str = str(workPath.joinpath(
            "{}.{}.csm.tmp".format(mName, lName)))  # csm模块路径
        self.conbcPath: str = str(workPath.joinpath(
            "{}.{}.con.tmp".format(mName, lName)))  # constant模块路径
        self.cgrPath: str = str(workPath.joinpath(
            "{}.{}.cgr.tmp".format(mName, lName)))  # 修剪后callgraph路径
        self.cgoPath: str = str(workPath.joinpath(
            "{}.{}.cgo.tmp".format(mName, lName)))  # 修剪前callgraph路径
        self.logPath: str = str(workPath.joinpath(
            "{}.{}.log.tmp".format(mName, lName)))  # 执行过程中的log文件
        self.status: TargetStatus = TargetStatus.notStarted

    def __eq__(self, __value) -> bool:
        if __value == None:
            return False
        return (self.mbcPath == __value.mbcPath) and self.lbcPath == __value.lbcPath


class Worker():
    def __init__(self, target) -> None:
        self.t: Target = target
        self.env = os.environ.copy()
        self.env["TRIMMER_HOME"] = "/home/xd/jzz/projects/SCA-Prun/Trimmer-master/"
        self.env["TRIMMER_DEBUG"] = "No"
        self.maxMem = 1024*1024*1024*55  # 55GB
        self.logFd = open(self.t.logPath, "w")

    def checkRes(self, p):
        if p[0].returncode != 0:
            self.logFd.close()
            self.t.status = TargetStatus.exitedAbNormal
            return False
        return True

    def getMainModule(self):
        cmd = ["tiny", self.t.mbcPath, "-o="+self.t.mmbcPath, "-a=t"]
        return self.checkRes(self.runCmd(cmd, self.t.Data["b_apiStr"]))

    def getLinkedModule(self):
        cmd = ["llvm-link-14", self.t.mmbcPath, self.t.lbcPath, ]

        p = self.runCmd(cmd, getStdOut=True)
        stdOut = p[1]
        cmd2 = ["opt-14", "-globaldce", "-mem2reg", "-mergereturn", "-simplifycfg", "-loops", "-lcssa",
                "-loop-simplify", "-scalar-evolution", "-licm", "-loop-rotate", "-indvars", "-loop-reduce", "-o", self.t.linkedbcPath]

        return self.checkRes(self.runCmd(cmd2, stdOut))

    def PreAnalysis(self):
        cmd = ["pa", "-field-limit=512000", "-model-consts=true", "-main="+self.t.mmbcPath, "-lib="+self.t.lbcPath, "-linked="+self.t.linkedbcPath,
               "-o="+self.t.csmbcPath]

        return self.checkRes(self.runCmd(cmd))

    def ConstantProp(self):
        cmd = ["opt-14", "--enable-new-pm=0", "-load=/home/xd/jzz/projects/SCA-Prun/Trimmer-master/build/ConstantFolding.so",
               "-mem2reg", "-mergereturn", "-simplifycfg", "-loops", "-lcssa", "-loop-simplify", "-scalar-evolution", "-licm",
               "-loop-rotate", "-indvars", "-loop-reduce", "-inter-constprop", "-exceedLimit=10", self.t.csmbcPath, "-o="+self.t.conbcPath]

        return self.checkRes(self.runCmd(cmd))

    def getCGR(self):
        cmd = ["cgd", self.t.conbcPath, "-r=true", "-o="+self.t.cgrPath]
        return self.checkRes(self.runCmd(cmd))

    def getCGO(self):
        cmd = ["cgd", self.t.conbcPath, "-o="+self.t.cgoPath]
        return self.checkRes(self.runCmd(cmd))

    def runCmd(self, cmd, input=None, getStdOut=False):
        def setlimits():
            resource.setrlimit(resource.RLIMIT_AS, (self.maxMem, self.maxMem))
        if getStdOut:
            p = subprocess.Popen(cmd, preexec_fn=setlimits, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, stdin=subprocess.PIPE, env=self.env)
        else:
            p = subprocess.Popen(cmd, preexec_fn=setlimits, stdout=self.logFd,
                                 stderr=subprocess.STDOUT, stdin=subprocess.PIPE, env=self.env)

        stdout, stderr = p.communicate(input)
        return p, stdout

    def start(self):
        if not self.getMainModule():
            return
        if not self.getLinkedModule():
            return
        if not self.PreAnalysis():
            return
        if not self.ConstantProp():
            return
        if not self.getCGR():
            return
        if not self.getCGO():
            return

        self.logFd.close()
        self.t.status = TargetStatus.exitedNormal


class Tiny():
    def __init__(self) -> None:
        self.exit = False
        self.tinyInfos = []
        if os.path.exists("tinyinfos"):
            print("reading from cache")
            self.tinyInfos = pickle.load(open("tinyinfos", "rb"))
        else:
            self.updateTinyInfo()
            self.dumpTinyInfo()

    def dumpTinyInfo(self):
        with open("tinyinfos", "wb") as fd:
            pickle.dump(self.tinyInfos, fd)

    def updateTinyInfo(self):

        def setData(target: Target, apiStr: str):
            Data = {}
            Data["b_apiStr"] = apiStr.encode()
            cmd = ["tiny", target.mbcPath, "-a=p"]
            res = subprocess.run(cmd, capture_output=True, input=Data["b_apiStr"]).stdout.decode(
            ).removesuffix('\n').split(",")
            for item in res:
                name = item.split(":")[0]
                value = item.split(":")[1]
                Data[name] = value
            target.Data = Data

        print("reading from tiny.json ...")
        with open("{}/{}".format(archIR_DIR, "tiny.json")) as fd:
            tinyFile = json.load(fd)
            depList = tinyFile["depList"]
            apiStrMap = tinyFile["apiStrMap"]
            for item in depList:
                mbcPath = "{}/{}".format(archIR_DIR, item[0])
                lbcPath = "{}/{}".format(archIR_DIR, item[1])
                print("init {}=>{}".format(mbcPath, lbcPath))
                tmp = Target(mbcPath, lbcPath)
                setData(tmp, apiStrMap[item[1]])
                self.tinyInfos.append(tmp)
        print("done")

    def launch(self, filterFunc, postFunc):
        for t in filter(filterFunc, self.tinyInfos):
            if self.exit:
                break

            w = Worker(t)
            w.start()
            postFunc(t)

        self.dumpTinyInfo()

    def iterTargets(self, filterFunc, postFunc):
        for t in filter(filterFunc, self.tinyInfos):
            if self.exit:
                break
            postFunc(t)


def diffCG(cgrPath, cgoPath):
    vulFuncSet = set()
    reachSetR = set()
    reachSetO = set()

    cgr = CallGraph(cgrPath)
    cgo = CallGraph(cgoPath)

    for name, id in cgo.NameToId.items():
        if name.startswith("magma_bug"):
            vulFuncSet.add(name)

    for vulFunc in vulFuncSet:
        cgoPath = cgo.getAnyPathToDst("main", vulFunc)
        cgrPath = cgr.getAnyPathToDst("main", vulFunc)
        if (cgoPath != None):
            reachSetO.add(vulFunc)
        if (cgrPath != None):
            reachSetR.add(vulFunc)

    diffSet = reachSetO.difference(reachSetR)
    print("\treachDiff:{}".format(diffSet))


def postFuncDump(t: Target):
    print("{},{},apiCount:{},callerSize:{},addrTaker:{}".format(t.mbcPath, t.lbcPath, t.Data["apiCount"],
                                                                t.Data["callerSize"], t.Data["addrTaker"]))


indexCounter = 0


def filterT1(t: Target):
    return True


def postFuncT1(t: Target):
    if t.status == TargetStatus.exitedAbNormal:
        print(t.logPath)


def filterT2(t: Target):
    global indexCounter
    if indexCounter > 44:
        return False

    if ("libsndfile" not in t.lbcPath) and ("libpng" not in t.lbcPath):
        return False

    if t.Data["callerSize"] != "1":
        return False

    #if "png2yuv" not in t.mbcPath:
    #    return False

    indexCounter += 1
    return True


def postFuncT2(t: Target):
    global indexCounter
    print("{} log:{}".format(indexCounter, t.logPath))
    print("\tstatus:{}\n".format(t.status))
    if t.status == TargetStatus.exitedNormal:
        diffCG(t.cgrPath, t.cgoPath)

    indexCounter += 1


def postFuncT3(t: Target):
    if t.status != TargetStatus.exitedNormal:
        return
    print(t.mbcPath)

    cmd = ["cgd", t.conbcPath, "-r=true", "-o="+t.cgrPath]
    # cmd = ["pa","-field-limit=512000", "-model-consts=true", "-main="+t.mmbcPath, "-lib="+t.lbcPath,
    #       "-linked="+t.linkedbcPath,"-o="+t.csmbcPath]

    env = os.environ.copy()
    env["TRIMMER_HOME"] = "/home/xd/jzz/projects/SCA-Prun/Trimmer-master/"
    env["TRIMMER_DEBUG"] = "No"
    #cmd = ["opt-14", "--enable-new-pm=0", "-load=/home/xd/jzz/projects/SCA-Prun/Trimmer-master/build/ConstantFolding.so",
    #       "-mem2reg", "-mergereturn", "-simplifycfg", "-loops", "-lcssa", "-loop-simplify", "-scalar-evolution", "-licm",
    #       "-loop-rotate", "-indvars", "-loop-reduce", "-inter-constprop", "-exceedLimit=15", t.csmbcPath, "-o="+t.conbcPath]
    
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, stdin=subprocess.PIPE,env=env)
    stdout, stderr = p.communicate()
    print(stderr.decode())
    # diffCG(t.cgrPath,t.cgoPath)


def postFuncClean(t: Target):
    def remove(path: str):
        p = pathlib.Path(path)
        if p.exists():
            print(p)
            p.unlink()

    remove(t.mmbcPath)
    remove(t.linkedbcPath)
    remove(t.csmbcPath)
    remove(t.conbcPath)
    remove(t.cgrPath)
    remove(t.cgoPath)
    remove(t.logPath)
    t.status = TargetStatus.notStarted


if __name__ == "__main__":
    t = Tiny()

    def exitHandler(signal, frame):
        print("exiting, please wait...")
        t.exit = True

    signal.signal(signal.SIGINT, exitHandler)
    # diffCG("test/xcur2png-r.dot","test/xcur2png.dot")

    # t.iterTargets(filterT1, postFuncClean)
    # t.launch(filterT2, postFuncT2)

    t.iterTargets(filterT2, postFuncT3)


# find -name *.tmp -exec rm {} \;


""" 
class CallGraph():
    def __init__(self, dotFile) -> None:
        self.dotFile = dotFile
        self.g = nx.DiGraph(nx.nx_pydot.read_dot(self.dotFile))
        self.NameToId = {}
        self.originNodes = []
        self.originToAlias = {}
        clonedNodes = []
        for nodeId in self.g.nodes:
            name = self.getNodeNameById(nodeId)
            self.NameToId[name] = nodeId
            if "_trcloned" not in name:
                self.originNodes.append(nodeId)
            else:
                clonedNodes.append(nodeId)

        for originId in self.originNodes:
            self.originToAlias[originId] = [originId]

        for clonedId in clonedNodes:
            clonedName = self.getNodeNameById(clonedId)
            originName = clonedName.split("_trcloned")[0]
            originId = self.NameToId[originName]
            self.originToAlias[originId].append(clonedId)

    def getNodeNameById(self, nodeId):
        data = self.g.nodes[nodeId]
        if ("label" in data):
            return data["label"][2:-2]
        elif nodeId == "\\n":
            return "Void Node Name"
        else:
            return "Empty Name"

    def getNodeIdByName(self, name):
        if name in self.NameToId:
            return self.NameToId[name]
        else:
            return None

    def getNodeData(self, nodeId):
        return self.g.nodes[nodeId]

    def getEdgeData(self, edge):
        res = {}
        datas = self.g.get_edge_data(edge[0], edge[1])[
            "label"][1:-1].split(',')
        for data in datas:
            t = data.split('=')
            res[t[0]] = int(t[1])
        return res

    def getAnyPathToAlias(self, srcName, dstName):

        srcNode = self.NameToId[srcName]
        dstNode = self.NameToId[dstName]
        for node in self.originToAlias[dstNode]:
            try:
                return nx.shortest_path(self.g, srcNode, node)
            except nx.exception.NetworkXNoPath:
                continue
        return None

    def dumpPath(self, srcName, dstName):
        print("path from {} ==> {}".format(srcName, dstName))
        path = self.getAnyPathToAlias(srcName, dstName)
        if path == None:
            print("no path found")
        else:
            for i in path:
                print(self.getNodeNameById(i))

    def saveGraph(self):
        nx.nx_pydot.write_dot(self.g, self.dotFile)

 """
