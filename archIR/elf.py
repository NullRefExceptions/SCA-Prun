import elftools.elf.elffile as elff
import os
import subprocess

def getExportFuncList(soPath):
    """
    从so中提取能够作为api的函数列表
    """
    funcList = []
    fd = open(soPath,'rb')
    elf = elff.ELFFile(fd)
    dynsym = elf.get_section_by_name(".dynsym")
    for sym in dynsym.iter_symbols():
        stv = sym.entry['st_other']['visibility']
        stb = sym.entry['st_info']['bind']
        stt = sym.entry['st_info']['type']
        shn = sym.entry['st_shndx']
        if(shn == 'SHN_UNDEF'):
            continue
        if(stt != 'STT_FUNC'):
            continue
        if(stb != 'STB_GLOBAL' and stb != 'STB_WEAK'):
            continue
        if(stv != 'STV_DEFAULT' and stv != 'STV_PROTECTED'):
            continue
        funcList.append(sym.name)
    fd.close()
    return funcList

def getImportSO(elfPath):
    """
    获取elf或so文件所依赖的动态链接库列表 
    """
    soList = []
    fd = open(elfPath,'rb')
    elf = elff.ELFFile(fd)
    dyn = elf.get_section_by_name(".dynamic")
    if dyn == None:
        return soList
    strtab = dyn._get_stringtable()
    for tag in dyn.iter_tags(type="DT_NEEDED"):
        soName = strtab.get_string(tag.entry["d_val"])
        soList.append(soName)
    fd.close()
    return soList

def getImportFuncList(elfPath):
    """
    获取elf或so文件需要导入的api列表
    """
    funcList = []
    fd = open(elfPath,'rb')
    elf = elff.ELFFile(fd)
    dynsym = elf.get_section_by_name(".dynsym")
    for sym in dynsym.iter_symbols():
        stt = sym.entry['st_info']['type']
        shn = sym.entry['st_shndx']
        if(shn != 'SHN_UNDEF'):
            continue
        if(stt != 'STT_FUNC'):
            continue
        funcList.append(sym.name)
    fd.close()
    return funcList

def getElfFiles(pathName):
    execList = []
    soList = []
    for (dirpath, dirnames, filenames) in os.walk(pathName):
        for file in filenames:
            filePath = os.path.join(dirpath, file)
            #print(filePath)
            if(os.path.islink(filePath)):
                continue
            cmd = ["file",filePath]
            res = subprocess.run(cmd,capture_output=True)
            msg = res.stdout.decode()
            if "executable" in msg and "ELF" in msg:
                execList.append(filePath)
            elif "shared object" in msg:
                soList.append(filePath)

    return execList,soList

#print(":".join(getExportFuncList("test/libgcrypt.so.20.2.8")))