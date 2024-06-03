import networkx as nx
import re


def getNodeName(graph,nodeId):
    data = graph.nodes[nodeId]
    if("label" in data):
        return data["label"][2:-2]
    elif nodeId == "\\n":
        return "Void Node Name"
    else:
        return "Empty Name"

def init(graph:nx.DiGraph):
    NameToId={}
    for nodeId in graph.nodes:
        name = getNodeName(graph,nodeId)
        NameToId[name] = nodeId
        reducedNameList.append(name)
    return NameToId

def dumpPath(srcName,dstName):
    pathExist = False
    src = reducedNameToId[srcName]
    aliasName = []
    for name in reducedNameList:
        if name == dstName:
            aliasName.append(name)
        elif re.search("^"+dstName+"(.\d+)*$", name):
            aliasName.append(name)
    print(aliasName)
    for name in aliasName:
        dst = reducedNameToId[name]
        try:
            path = nx.shortest_path(reducedGraph,src,dst)
        except nx.exception.NetworkXNoPath:
            continue
        else:  
            for i in path:
                print(getNodeName(reducedGraph,i))
            return
    if not pathExist:
        print("no path found")


reducedNameList = []

#originGraph = nx.DiGraph(nx.nx_pydot.read_dot("mltacg.dot"))
reducedGraph = nx.DiGraph(nx.nx_pydot.read_dot("mltacg.dot"))

#nx.nx_pydot.write_dot(originGraph,"origin2.dot")
#nx.nx_pydot.write_dot(reducedGraph,"reduced2.dot")

#originNameToId = init(originGraph)
reducedNameToId = init(reducedGraph)

#dumpPath("main","GENERAL_NAME_cmp") CVE-2020-1971 openssl 1.1.1 (1.1.1) 
"""
linked_con.bc
['GENERAL_NAME_cmp']
no path found

linked.bc
['GENERAL_NAME_cmp']
main
TS_RESP_verify_response
int_ts_RESP_verify_token
ts_check_signer_name
GENERAL_NAME_cmp
"""

#dumpPath("main","evutil_parse_sockaddr_port") CVE-2016-10196 libevent 2.1.5 beta (before 2.1.6 beta)
"""
linked_con.bc
['evutil_parse_sockaddr_port']
no path found

linked.bc
['evutil_parse_sockaddr_port']
main
evdns_base_new
evdns_base_resolv_conf_parse
evdns_base_resolv_conf_parse_impl
evdns_base_nameserver_ip_add
evutil_parse_sockaddr_port
"""

#dumpPath("main","header_read") 	CVE-2017-7586 libsndfile 1.0.27 ( before 1.0.28)
"""
linked_con.bc
['header_read']
no path found

linked.bc
['header_read']
main
sf_open
psf_open_file
guess_file_type
psf_binheader_readf
header_read
"""

#dumpPath("main","smc_encode_stream")  CVE-2022-3965 ffmpeg n5.1 
"""
linked.bc
['smc_encode_stream']
no path found
"""

#dumpPath("main","elg_decrypt")  CVE-2021-33560 libgcrypt 1.8.7 (before 1.8.8)
"""
linked_con.bc
['elg_decrypt']
main
gcry_md_hash_buffer.6
_gcry_global_is_operational
_gcry_fips_is_operational
_gcry_fips_run_selftests
run_pubkey_selftests
_gcry_pk_selftest
run_selftests.1541
selftests_rsa
selftest_encr_2048
_gcry_pk_decrypt
elg_decrypt

linked.bc
['elg_decrypt']
main
gcry_md_hash_buffer
_gcry_global_is_operational
_gcry_fips_is_operational
_gcry_fips_run_selftests
run_pubkey_selftests
_gcry_pk_selftest
run_selftests.1541
selftests_rsa
selftest_encr_2048
_gcry_pk_decrypt
elg_decrypt
"""