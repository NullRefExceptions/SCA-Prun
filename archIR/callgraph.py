import networkx as nx
import subprocess
import re
import os


class CallGraph():
    def __init__(self,bcFile) -> None:
        self.dotFile = bcFile +".dot"
        if(not os.path.exists(self.dotFile)):
            #生成dot
            cmd = ["opt-14","--lowerinvoke",bcFile,"-o",bcFile]
            subprocess.run(cmd)
            cmd = ["./cgd","-o",self.dotFile,bcFile]
            subprocess.run(cmd)

        #导入dot
        self.g = nx.DiGraph(nx.nx_pydot.read_dot(self.dotFile))
        self.NameToId={}
        for nodeId in self.g.nodes:
            name = self.getNodeNameById(nodeId)
            self.NameToId[name] = nodeId


    def getNodeNameById(self,nodeId):
        data = self.g.nodes[nodeId]
        if("label" in data):
            return data["label"][2:-2]
        elif nodeId == "\\n":
            return "Void Node Name"
        else:
            return "Empty Name"  

    def getNodeIdByName(self,name):
        if name in self.NameToId:
            return self.NameToId[name]
        else:
            return None

    def getNodeData(self,nodeId):
        return self.g.nodes[nodeId]

    def getEdgeData(self,edge):
        res = {}
        datas = self.g.get_edge_data(edge[0],edge[1])["label"][1:-1].split(',')
        for data in datas:
            t = data.split('=')
            res[t[0]] = int(t[1])
        return res

    def getPath(self,srcName,dstName):
        res = []
        srcNode = self.NameToId[srcName]
        for name in self.getAliasNames(dstName):
            dstNode = self.NameToId[name]
            for path in nx.all_simple_edge_paths(self.g,srcNode,dstNode):
                res.append(path)
        return res

    def getAliasNames(self,originName):
        aliasNames = []
        for name in self.NameToId:
            if name == originName:
                aliasNames.append(name)
            elif re.search("^"+originName+"(.\d+)*$", name):
                aliasNames.append(name)
        return aliasNames    

    def dumpPath(self,srcName,dstName):
        src = self.NameToId[srcName]
        for name in self.getAliasNames(dstName):
            dst = self.NameToId[name]
            try:
                path = nx.shortest_path(self.g,src,dst)
            except nx.exception.NetworkXNoPath:
                continue
            else:  
                for i in path:
                    print(self.getNodeNameById(self.g,i))
                return

        print("no path found")

