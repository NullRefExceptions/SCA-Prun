import build
import analysis
import config
import pkgInfo
import signal



if __name__ == "__main__":
    pb = build.pkgBuilder
    pa = analysis.pkgAnalysis
    def exitHandler(signal,frame):
        pb.printResult()
        print("exiting")
        exit()

    signal.signal(signal.SIGINT,exitHandler)

    def tempBuild(list):
        for pkg in list:
            print("temp build "+pkg)
            pb.downloadPkgFromGit(pkg)
            pb.sourceOnly(pkg)
            #pb.buildPkg(pkg)
    

    #tempBuild(["djvulibre","geeqie","lcms2","libcamera-tools","libcupsfilters","libgeotiff","sdl2_image","swayimg"])
    tempBuild(["aribb24"])
    #pb.initVulPkg(config.buildSet)
    bset = [{"name": "libsndfile"}]
    
    #pb.initDepPkg(bset)
    
    #analysis.analysisVulPkg(config.buildSet)
    #pa.analysisDepPkg([{"name":"libsndfile"},{"name":"libpng"},{"name":"libxml2"},{"name":"libtiff"},{"name":"openssl"}])
    #pa.dumpDep()

    """     parser = argparse.ArgumentParser()
        parser.add_argument("-p",dest="package",type=str, help="package to process")
        parser.add_argument("-b",dest="buildOption",default="a",type=str,help="build option",choices=["y","n","a"])
        parser.add_argument("action",type=str, help="what you want?",choices=["build","getbc"])
        args = parser.parse_args()

        # 获取要测试的第三方库名称,导出函数列表(API列表)(还需要填充CVE到漏洞函数的对应关系)
        
        libList = ["openssl", "libsndfile"]
        # 对每个第三方库，获取依赖它的应用列表
        libName = "libsndfile"
        
        # 过滤列表中明显是第三方库的（应用价值不大）

        if args.action == "build":
            if args.package == None:
                statistic = {"done":0,"error":0}
                for pkginfo in getRequiredByPackages(libName):
                    result = handleInstance(libName,pkginfo,args.buildOption)
                    statistic[result] += 1
                print(statistic)
            else:
                handleInstance(libName,pkgInfo(args.package),args.buildOption)
        elif args.action == "getbc":
            print("get all bc file in build dir")
            pkglist = []
            if args.package != None:
                pkglist.append(args.package)
            else:
                for dir in pathlib.Path().iterdir():
                    if dir.is_dir() and dir.name != "bc-results":
                        pkglist.append(dir)
            for pkg in pkglist:
                for file in pathlib.Path(pkg).iterdir():
                    if file.is_file() and file.name.endswith(".bc"):
                        print(file.resolve())
                        shutil.copy(file,"bc-results")
        else:
            parser.print_help() """