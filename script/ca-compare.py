
import matplotlib.pyplot as plt


def parseLine(lineStr:str):
    funcName = lineStr.split('\t')[0].split(':')[1]
    ctxStr = lineStr.split('\t')[1].split(':')[1]
    ctxTokens= ctxStr.split()
    constantSum = 0
    for i in range(0,len(ctxTokens),2):
        ctx = ctxTokens[i].split('_')[1]
        constantNum = ctxTokens[i+1].split('_')[1]
        constantSum += int(constantNum)

    return (funcName,constantSum)


def parseFile(path):
    res = {}
    fd = open(path)
    Lines = fd.readlines()
    CurrentItem = ""
    for i in range(len(Lines)):
        if Lines[i].startswith("./archIR/bc-results"):
            CurrentItem = Lines[i]
            res[CurrentItem] = {}
        if Lines[i].startswith("toRun:"):
            funcName,constantSum = parseLine(Lines[i])
            res[CurrentItem][funcName] = constantSum

    return res


def compare(infoOn:dict,infoOff:dict):
    sumON = 0
    for funcName,constantNum in infoOn.items():
        sumON += constantNum

    sumOFF = 0
    for funcName,constantNum in infoOff.items():
        sumOFF += constantNum
    
    if(sumOFF > sumON):
        pass
    return sumON,sumOFF

onDic = parseFile("ca-on.txt")
offDic = parseFile("ca-off.txt")
onData = []
offData = []

for k,v in onDic.items():
    sumON,sumOFF =compare(onDic[k],offDic[k])
    onData.append(sumON)
    offData.append(sumOFF)

# 准备数据
namesLibpng = ["libaribb24.so.bc","caph.bc","dosbox.bc","fbgrab.bc",
         "fig2dev.bc","fuzzel.bc","guetzli.bc","harvid.bc","libcupsfilters.so.bc","icns2png.bc",
         "png2icns.bc","png2dbl.bc","dbl2png.bc","png2yuv.bc","libply-splash-graphics.so.bc",
         "qrencode.bc","randtilegen.bc","slim.bc","libslim.so.bc","libsox.so.bc","patextract.bc",
         "pat2ppm.bc","visgrep.bc","rgb2pat.bc","png2pat.bc","xcur2png.bc","xcursorgen.bc"]

namesLibsndfile = ["make-sine.bc","akaiextract.bc","alhrtf.bc","almultireverb.bc","alreverb.bc",
         "allatency.bc","alplay.bc","rubberband-r3.bc","rubberband.bc","sound-gambit.bc",
         "twolame.bc","accuraterip.bc"]
fig, ax = plt.subplots()
 
ax.plot(namesLibpng, onData[12:39],label='Mod Range Analysis Enabled')
ax.plot(namesLibpng, offData[12:39],label='Mod Range Analysis Disabled')

#ax.plot(namesLibsndfile, onData[0:12],label='Mod Range Analysis Enabled')
#ax.plot(namesLibsndfile, offData[0:12],label='Mod Range Analysis Disabled')

ax.legend(loc='upper right', bbox_to_anchor=(1, 1.2))

plt.xticks(rotation = 90)
plt.savefig("ca-figure.png",bbox_inches='tight')

