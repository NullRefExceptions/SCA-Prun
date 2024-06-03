#include "SpecFileIO.h"
#include "../ConstantFolding.h"
#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include "../Stats.h"
#include "../Debug.h"
/*
   The following code specializes File IO Calls such as open, read, pread, lseek,
   fopen, fread, fgets, fseek, mmap, munmap, close,fclose

   For each opened file, a File Structure (FdInfo) is defined which stores its file pointer (in case of fopen()),
   file descriptor (in case of open()), file name, current offset and a tracked boolean, which
   tells whether it can be specialized. File Open calls will be only specialized if they
   are successful and have constant arguments.

   File Read calls will be specialized if they are successful and there exist a valid File structure associated with it
   (initialized when file is opened) and a valid buffer,where the contents of file read will be stored.
   Also the size of the file contents to be read and the offset of the file should be constant.
   Similarly, for File Seek Calls, offset and flag should be constant.

   After File Read Calls, the buffer where the file data is stored is marked as constant and
   the calls are replaced with memcpys instructions.

   Additional File Seek calls are added for replacing File Read Calls in case the file is not
   completely specialized. We are handling partial specialization.

   All File IO calls are added to fileIOCalls map so that if they are successfully specialized,
   they can be deleted at the end.

*/

map<int, uint64_t> fdInfoMap;
map<uint64_t, FileInsts *> fileIOCalls;
int numConfigFiles;
list<string> configFileNames;
vector<MMapInfo *> mMapBuffer;

static cl::opt<int> fileSpecialize("fileSpecialize", cl::init(1));
static cl::list<std::string> fileNames("fileNames", cl::ZeroOrMore, cl::desc("config filenames to specialize for"), cl::CommaSeparated);

void removeFileIOCallsFromMap(string buffer[], int sfd)
{

  if (fileIOCalls.find(sfd) == fileIOCalls.end())
  {
    return;
  }
  vector<Instruction *> insts = fileIOCalls[sfd]->insts;
  vector<Instruction *>::iterator it = insts.begin();
  while (it != insts.end())
  {
    CallInst *Inst = dyn_cast<CallInst>(*it);
    if (((Inst->getCalledFunction()->getName().str()).compare(buffer[0]) == 0 || (Inst->getCalledFunction()->getName().str()).compare(buffer[1]) == 0))
    {
      it = insts.erase(it);
    }
    else
    {
      ++it;
    }
  }

  fileIOCalls[sfd]->insts = insts;
  fileIOCalls[sfd]->isSpecialized = false;
}

/**
 * Allocates and Initializes File Structure (FDInfo) for open() call
 * Saves the address of structure in FdInfoMap
 */
int initfdi(int fd, char *fname)
{
  uint64_t addr = bbOps.allocateHeap(sizeof(FdInfo), cf->currBB);
  FdInfo *fdi = (FdInfo *)bbOps.getActualAddr(addr, cf->currBB);
  fdi->fd = fd;
  fdi->offset = 0;
  fdi->tracked = true;
  fdi->fileName = fname;
  int sfd = numConfigFiles;
  numConfigFiles++;
  fdInfoMap[sfd] = addr;
  debug(Yes) << addr;
  return sfd;
}

/**
 * Allocates and Initializes File Structure (FDInfo) for fopen() call
 * Saves the address of structure in FdInfoMap
 */
int initfptr(FILE *fptr, char *fname)
{
  uint64_t addr = bbOps.allocateHeap(sizeof(FdInfo), cf->currBB);
  FdInfo *fdi = (FdInfo *)bbOps.getActualAddr(addr, cf->currBB);
  fdi->fd = 0;
  fdi->fptr = fptr;
  fdi->offset = 0;
  fdi->tracked = true;
  fdi->fileName = fname;
  int sfd = numConfigFiles;
  numConfigFiles++;
  fdInfoMap[sfd] = addr;
  debug(Yes) << "address = " << addr << "sfd = " << sfd << "\n";

  return sfd;
}

/**
 * Returns true if a valid File Descriptor is found in FdInfoMap
 * For read, pread, lseek, mmap, close only
 */
bool getfdi(int sfd, int &fd)
{
  if (fdInfoMap.find(sfd) == fdInfoMap.end())
    return false;
  uint64_t addr = fdInfoMap[sfd];
  if (!bbOps.checkConstContigous(addr, cf->currBB))
  {
    debug(Yes) << "skipping non constant fd\n";
    return false;
  }
  FdInfo *fdi = (FdInfo *)bbOps.getActualAddr(addr, cf->currBB);
  if (!fdi->tracked)
  {
    debug(Yes) << "skipping untracked fd\n";
    return false;
  }
  fd = fdi->fd;
  lseek(fd, fdi->offset, SEEK_SET);
  return true;
}

/**
 * Returns true if a valid File Pointer is found in FdInfoMap
 * For fread, fgets, fseek, fclose only
 */
bool getfptr(int sfd, FILE *&fptr)
{
  if (fdInfoMap.find(sfd) == fdInfoMap.end())
    return false;

  uint64_t addr = fdInfoMap[sfd];
  if (!bbOps.checkConstContigous(addr, cf->currBB))
  {
    debug(Yes) << "skipping non constant fptr\n";
    return false;
  }
  FdInfo *fdi = (FdInfo *)bbOps.getActualAddr(addr, cf->currBB);
  if (!fdi->tracked)
  {
    debug(Yes) << "skipping untracked fptr\n";
    return false;
  }
  fptr = fdi->fptr;
  fseek(fptr, fdi->offset, SEEK_SET);
  return true;
}

/**
 * Sets tracking of File as false
 * Set as false in two cases:
 * 1.FileIO Calls can not be specialized e.g, arguments are non-constant
 * 2.FileIO functions returns an error
 */
void setfdiUntracked(int sfd)
{
  ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->tracked = false;
}

/**
 * Get tracked value of a File
 */
bool getfdiUntracked(int sfd)
{
  return ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->tracked;
}

/**
 * Sets File offset to the new offset of the File after it has being read or seeked
 * For read, pread and lseek only
 */
void setfdiOffset(int sfd, int fd)
{
  ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->offset = lseek(fd, 0, SEEK_CUR);
}

/**
 * Get File offset
 */
long getfdiOffset(int sfd, int fd)
{
  return ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->offset;
}

/**
 * Sets File offset to the new offset of the File after it has being read or seeked
 * For fread, fgets and fseek only
 */
void setfptrOffset(int sfd, FILE *fptr)
{
  ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->offset = ftell(fptr);
}

/**
 * Get File offset
 */
long getfptrOffset(int sfd, FILE *fptr)
{
  return ((FdInfo *)bbOps.getActualAddr(fdInfoMap[sfd], cf->currBB))->offset;
}

/**
 * Handle open() calls
 * Opens the file and if call is succesful, it creates, initializes and saves the File Structure (FDInfo) for that file
 */
void handleOpen(CallInst *ci)
{
  Value *nameptr = ci->getOperand(0);
  char *fname;
  Value *flagVal = ci->getOperand(1);
  uint64_t flag;
  if (!cf->getStr(nameptr, fname, 100))
  {
    debug(Yes) << "handleOpen : fname not found in map\n";
    return;
  }
  if (!cf->getSingleVal(flagVal, flag))
  {
    debug(Yes) << "handleOpen : flag not constant\n";
    return;
  }

  if ((uint64_t)(flag & O_ACCMODE) != (uint64_t)O_WRONLY)
  {
    debug(Yes) << "handleOpen : flag is not write only\n";
    return;
  }

  if (std::find(std::begin(configFileNames), std::end(configFileNames), fname) != std::end(configFileNames) && fileSpecialize)
  {
    int fd = open(fname, flag);
    if (fd < 0)
      return;
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
    fd = initfdi(fd, fname);
    cf->addSingleVal(ci, fd, true, true);
    FileInsts *insts = new FileInsts();
    insts->insts.push_back(ci);
    insts->isSpecialized = true;
    fileIOCalls[fd] = insts;
  }
  else
  {
    debug(Yes) << "open not specialized"
               << "\n";
  }
}

void handleFEOF(CallInst *ci)
{
  Value *fptrVal = ci->getOperand(0);
  uint64_t sfd;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  if (!fdConst)
  {
    debug(Yes) << "handleFEOF : failed to specialize\n";
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fopen";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  int fileC = feof(fptr);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
  cf->addSingleVal(ci, fileC, true, true);
  fileIOCalls[sfd]->insts.push_back(ci);
}

void handleGetLine(CallInst *ci)
{
  Value *bufPtr = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  Value *fptrVal = ci->getOperand(2);
  uint64_t sfd;
  size_t size;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  Register *reg = cf->processInstAndGetRegister(bufPtr);
  Register *reg1 = cf->processInstAndGetRegister(sizeVal);
  if (!reg || !reg1 || !fdConst)
  {
    debug(Yes) << "handleGetLine : failed to specialize\n";
    if (reg)
      bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  char **buffer = (char **)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  size_t *buffer2 = (size_t *)bbOps.getActualAddr(reg1->getValue(), cf->currBB);
  char *newBuf = NULL;

  size_t characters = getline(&newBuf, &size, fptr);

  if (characters == -1 && !feof(fptr))
  {
    debug(Yes) << "handleGetLine : read returned error\n";
    setfdiUntracked(sfd);
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    bbOps.setConstContigous(false, reg1->getValue(), cf->currBB);
    string funcNames[2];
    funcNames[0] = "fopen";
    funcNames[1] = "fseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }

  else
  {
    debug(Yes) << "buffer value " << newBuf << " " << strlen(newBuf) << " " << size << " " << characters << "\n";
    bbOps.setConstMem(true, reg1->getValue(), 8, cf->currBB);
    bbOps.setConstMem(true, reg->getValue(), 8, cf->currBB);
    *buffer2 = size;

    uint64_t addr1 = bbOps.allocateStack(strlen(newBuf), cf->currBB);
    char *buffer1 = (char *)bbOps.getActualAddr(addr1, cf->currBB);
    strcpy(buffer1, newBuf);

    bbOps.storeToMem(addr1, 8, reg->getValue(), cf->currBB);

    setfptrOffset(sfd, fptr);
    llvm::Type *type = llvm::IntegerType::getInt64Ty(cf->module->getContext());
    llvm::Constant *sizeNum = llvm::ConstantInt::get(type, characters, true);
    ci->replaceAllUsesWith(sizeNum);

    IRBuilder<> Builder(ci);

    Value *mallocFunc;
    mallocFunc = cf->module->getOrInsertFunction("malloc", Type::getInt8PtrTy(cf->module->getContext()), Type::getInt64Ty(cf->module->getContext())).getCallee();
    Function *hookM = cast<Function>(mallocFunc);

    ConstantInt *arg1 = Builder.getInt64(strlen(newBuf) + 1);
    CallInst *malloc = Builder.CreateCall(hookM, arg1);

    Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(newBuf), true);
    GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
    MaybeAlign al(1);
    gv->setAlignment(al);

    Instruction *MemCpyInst = Builder.CreateMemCpy(malloc, al, gv, al, strlen(newBuf));

    StoreInst *store = Builder.CreateStore(malloc, bufPtr, false);

    Value *hookFunc;
    hookFunc = cf->module->getOrInsertFunction("fseek", Type::getInt32Ty(cf->module->getContext()),
                                               fptrVal->getType(), Type::getInt64Ty(cf->module->getContext()), Type::getInt32Ty(cf->module->getContext()))
                   .getCallee();
    Function *hook = cast<Function>(hookFunc);

    ConstantInt *arg2 = Builder.getInt64(getfptrOffset(sfd, fptr));
    ConstantInt *arg3 = Builder.getInt32(0);
    std::vector<llvm::Value *> putsArgs;
    putsArgs.push_back(fptrVal);
    putsArgs.push_back(arg2);
    putsArgs.push_back(arg3);
    CallInst *seek = Builder.CreateCall(hook, putsArgs);

    fileIOCalls[sfd]->insts.push_back(ci);
    fileIOCalls[sfd]->insertedSeekCalls.push_back(seek);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

/**
 * Handle fopen() calls
 * Opens the file and if call is succesful, it creates, initializes and saves the File Structure (FDInfo) for that file
 */
void handleFOpen(CallInst *ci)
{
  Value *nameptr = ci->getOperand(0);
  char *fname;
  Value *modVal = ci->getOperand(1);
  char *fmode;
  if (!cf->getStr(nameptr, fname, 20))
  {
    debug(Yes) << "handleFOpen : fname not found in map\n";
    return;
  }
  if (!cf->getStr(modVal, fmode, 100))
  {
    debug(Yes) << "handleFOpen : fmode not found in map\n";
    return;
  }
  if (std::find(std::begin(configFileNames), std::end(configFileNames), fname) != std::end(configFileNames) && fileSpecialize && (strcmp(fmode, "wb") == 0 || strcmp(fmode, "w") == 0))
  {
    FILE *fptr = fopen(fname, fmode);
    if (!fptr)
    {
      debug(Yes) << "handleFOpen : fopen error\n";
      return;
    }
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
    int fd = initfptr(fptr, fname);
    cf->addSingleVal(ci, fd, true, true);
    FileInsts *insts = new FileInsts();
    insts->insts.push_back(ci);
    insts->isSpecialized = true;
    fileIOCalls[fd] = insts;
  }
  else
  {
    debug(Yes) << "fopen not specialized since name not found. Name: " << fname << "\n";
  }
}

/**
 * Handle read() calls
 * Reads the file and if call is successful, it initializes and sets the buffer(where
 the file data is read to) to constant
 * Add llvm.memcpy instruction to replace read calls
 * Also updates the file offset
 * Seek call added for partial specialization
 */
void handleRead(CallInst *ci)
{
  Value *fdVal = ci->getOperand(0);
  Value *bufPtr = ci->getOperand(1);
  Value *sizeVal = ci->getOperand(2);
  uint64_t size, sfd;
  int fd = 0;
  bool fdConst = cf->getSingleVal(fdVal, sfd) && getfdi(sfd, fd);

  if (fd <= 2)
    return;

  Register *reg = cf->processInstAndGetRegister(bufPtr);
  if (!reg || !fdConst || !cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "handleRead : failed to specialize\n";
    if (reg)
      bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fdVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "lseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  long bytes_read = read(fd, buffer, size);

  if (bytes_read < 0)
  {
    debug(Yes) << "handleRead : read returned error\n";
    setfdiUntracked(sfd);
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    string funcNames[2];
    funcNames[0] = "open";
    funcNames[1] = "lseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  bbOps.setConstMem(true, reg->getValue(), bytes_read, cf->currBB);
  setfdiOffset(sfd, fd);
  cf->addSingleVal(ci, bytes_read, true, true);
  buffer[bytes_read] = '\0';

  Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(buffer), true);
  GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
  MaybeAlign al(1);
  gv->setAlignment(al);
  IRBuilder<> Builder(ci);
  Instruction *MemCpyInst = Builder.CreateMemCpy(bufPtr, al, gv, al, bytes_read);

  Value *hookFunc;
  hookFunc = cf->module->getOrInsertFunction("lseek", Type::getInt64Ty(cf->module->getContext()), Type::getInt32Ty(cf->module->getContext()), Type::getInt64Ty(cf->module->getContext()), Type::getInt32Ty(cf->module->getContext())).getCallee();
  Function *hook = cast<Function>(hookFunc);

  ConstantInt *arg1 = Builder.getInt32(fd);
  ConstantInt *arg2 = Builder.getInt64(getfdiOffset(sfd, fd));
  ConstantInt *arg3 = Builder.getInt32(0);
  std::vector<llvm::Value *> putsArgs;
  putsArgs.push_back(arg1);
  putsArgs.push_back(arg2);
  putsArgs.push_back(arg3);
  CallInst *seek = Builder.CreateCall(hook, putsArgs);

  fileIOCalls[sfd]->insts.push_back(ci);
  fileIOCalls[sfd]->insertedSeekCalls.push_back(seek);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/* we asume write always sucesss */
void handleWrite(CallInst *ci)
{
  Value *fdVal = ci->getOperand(0);
  Value *bufPtr = ci->getOperand(1);
  Value *sizeVal = ci->getOperand(2);
  
  if (ConstantInt *con =dyn_cast<ConstantInt>(sizeVal))
  {
    ci->replaceAllUsesWith(con);
  }
  
}

/**
 * Handle pread() calls
 * Reads the file and if call is successful, it initializes and sets the buffer
 (where the file data is read to) to constant
 * Add llvm.memcpy instruction to replace read calls
 * Also updates the file offset
 */
void handlePRead(CallInst *ci)
{
  Value *fdVal = ci->getOperand(0);
  Value *bufPtr = ci->getOperand(1);
  Value *sizeVal = ci->getOperand(2);
  Value *offsetVal = ci->getOperand(3);
  uint64_t size, offset, sfd;
  int fd;
  bool fdConst = cf->getSingleVal(fdVal, sfd) && getfdi(sfd, fd);
  Register *reg = cf->processInstAndGetRegister(bufPtr);
  if (!reg || !fdConst || !cf->getSingleVal(sizeVal, size) || !cf->getSingleVal(offsetVal, offset))
  {
    debug(Yes) << "handlePRead : failed to specialize\n";
    if (reg)
      bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fdVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "open";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  long bytes_read = pread(fd, buffer, size, offset);

  if (bytes_read < 0)
  {
    debug(Yes) << "handlePRead : read returned error\n";
    setfdiUntracked(sfd);
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    string funcNames[2];
    funcNames[0] = "open";
    funcNames[1] = "open";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  bbOps.setConstMem(true, reg->getValue(), bytes_read, cf->currBB);
  cf->addSingleVal(ci, bytes_read, true, true);

  Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(buffer), true);
  GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
  MaybeAlign al(1);
  gv->setAlignment(al);
  IRBuilder<> Builder(ci);
  Instruction *MemCpyInst = Builder.CreateMemCpy(bufPtr, al, gv, al, bytes_read);
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

// handles mmap calls
void handleMMap(CallInst *ci)
{
  Value *bufPtr = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  Value *flagVal1 = ci->getOperand(2);
  Value *flagVal2 = ci->getOperand(3);
  Value *fdVal = ci->getOperand(4);
  Value *offsetVal = ci->getOperand(5);
  uint64_t size, offset, flag1, flag2, sfd;
  int fd;
  bool fdConst = cf->getSingleVal(fdVal, sfd) && getfdi(sfd, fd);
  Register *reg = cf->processInstAndGetRegister(bufPtr);

  if (!fdConst || !cf->getSingleVal(offsetVal, offset) || !cf->getSingleVal(flagVal1, flag1) || !cf->getSingleVal(flagVal2, flag2))
  {
    debug(Yes) << "handleMMap : failed to specialize\n";
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fdVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "open";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  char *buffer;
  if (!reg)
    buffer = NULL;
  else
    buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);

  uint64_t addr = fdInfoMap[sfd];
  FdInfo *fdi = (FdInfo *)bbOps.getActualAddr(addr, cf->currBB);

  if (!cf->getSingleVal(sizeVal, size))
  {

    struct stat st;
    stat(fdi->fileName, &st);
    size = st.st_size;
  }
  char *mmappedData = (char *)mmap(buffer, size, flag1, flag2, fd, offset);

  if (mmappedData == MAP_FAILED)
  {
    debug(Yes) << "handleMMap : read returned error\n";
    setfdiUntracked(sfd);
    string funcNames[2];
    funcNames[0] = "open";
    funcNames[1] = "open";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }

  uint64_t addr1 = bbOps.allocateHeap(size, cf->currBB);
  char *buffer1 = (char *)bbOps.getActualAddr(addr1, cf->currBB);
  strcpy(buffer1, mmappedData);

  Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(mmappedData), true);
  GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
  MaybeAlign al(1);
  gv->setAlignment(al);
  IRBuilder<> Builder(ci);
  Value *BitCastInst = Builder.CreateBitCast(gv, PointerType::getUnqual(llvm::IntegerType::getInt8Ty(cf->module->getContext())));
  ci->replaceAllUsesWith(BitCastInst);
  fileIOCalls[sfd]->insts.push_back(ci);
  MMapInfo *mmapInfo = new MMapInfo();
  mmapInfo->sfd = sfd;
  mmapInfo->buffer = mmappedData;
  mMapBuffer.push_back(mmapInfo);
  cf->addSingleVal(BitCastInst, addr1, true, true);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

// handle munmap calls
void handleMUnmap(CallInst *ci)
{

  Value *bufPtr = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  uint64_t size;
  uint64_t sfd;
  char *mmappedData;
  bool hasCorrespondingMmap = false;

  Register *reg = cf->processInstAndGetRegister(bufPtr);
  if (!reg)
  {
    debug(Yes) << "handleMUnmap : failed to specialize\n";
    return;
  }

  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);

  for (int i = 0; i < mMapBuffer.size(); i++)
  {

    if (strcmp(buffer, mMapBuffer[i]->buffer) == 0)
    {
      debug(Yes) << "sfd equals " << mMapBuffer[i]->sfd << "\n";
      debug(Yes) << "buffer equals " << mMapBuffer[i]->buffer << "\n";
      sfd = mMapBuffer[i]->sfd;
      mmappedData = mMapBuffer[i]->buffer;
      hasCorrespondingMmap = true;
      break;
    }
  }

  if (!cf->getSingleVal(sizeVal, size))
  {
    size = 1;
  }

  int ret = munmap(mmappedData, size);

  if (ret != 0)
  {
    debug(Yes) << "handleMUnmap : read returned error\n";
    if (hasCorrespondingMmap)
    {
      setfdiUntracked(sfd);
      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "mmap";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }

  cf->addSingleVal(ci, ret, true, true);
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * Handle fread() calls
 * Reads the file and if call is successful, it initializes and sets the buffer(where the file data is read to) to constant
 * Add llvm.memcpy instruction to replace read calls
 * Also updates the file offset
 * Seek call added for partial specialization
 */
void handleFRead(CallInst *ci)
{
  Value *bufPtr = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  Value *numVal = ci->getOperand(2);
  Value *fptrVal = ci->getOperand(3);
  uint64_t size, num, sfd;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  Register *reg = cf->processInstAndGetRegister(bufPtr);

  if (!reg || !fdConst || !cf->getSingleVal(sizeVal, size) || !cf->getSingleVal(numVal, num))
  {
    debug(Yes) << "handleFRead : failed to specialize\n";
    if (reg)
    {
      debug(Yes) << "memory non-constant" << reg->getValue() << "\n";
      bbOps.setConstMem(false, reg->getValue(), cf->DL->getTypeAllocSize(reg->getType()), cf->currBB);
    }
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  uint64_t bytes_read = fread(buffer, size, num, fptr);

  if (ferror(fptr))
  {
    debug(Yes) << "handleFRead : read returned error\n";
    setfdiUntracked(sfd);
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    string funcNames[2];
    funcNames[0] = "fopen";
    funcNames[1] = "fseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  bbOps.setConstMem(true, reg->getValue(), bytes_read, cf->currBB);
  setfptrOffset(sfd, fptr);
  cf->addSingleVal(ci, bytes_read, true, true);
  buffer[bytes_read] = '\0';

  Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(buffer), true);
  GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
  MaybeAlign al(1);
  gv->setAlignment(al);
  IRBuilder<> Builder(ci);
  Instruction *MemCpyInst = Builder.CreateMemCpy(bufPtr, al, gv, al, bytes_read);
  Value *hookFunc;
  hookFunc = cf->module->getOrInsertFunction("fseek", Type::getInt32Ty(cf->module->getContext()), fptrVal->getType(), Type::getInt64Ty(cf->module->getContext()), Type::getInt32Ty(cf->module->getContext())).getCallee();
  Function *hook = cast<Function>(hookFunc);

  ConstantInt *arg2 = Builder.getInt64(getfptrOffset(sfd, fptr));
  ConstantInt *arg3 = Builder.getInt32(0);
  std::vector<llvm::Value *> putsArgs;
  putsArgs.push_back(fptrVal);
  putsArgs.push_back(arg2);
  putsArgs.push_back(arg3);
  CallInst *seek = Builder.CreateCall(hook, putsArgs);

  fileIOCalls[sfd]->insts.push_back(ci);
  fileIOCalls[sfd]->insertedSeekCalls.push_back(seek);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * Handle fgets() calls
 * Reads the file and if call is successful, it initializes and sets the buffer(where the file data is read to) to constant
 * Add llvm.memcpy instruction to replace read calls
 * Also updates the file offset
 * Seek call added for partial specialization
 */
void handleFGets(CallInst *ci)
{
  Value *bufPtr = ci->getOperand(0);
  Value *sizeVal = ci->getOperand(1);
  Value *fptrVal = ci->getOperand(2);
  uint64_t size, sfd;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  Register *reg = cf->processInstAndGetRegister(bufPtr);
  if (!reg || !fdConst || !cf->getSingleVal(sizeVal, size))
  {
    debug(Yes) << "handleFGets : failed to specialize\n";
    if (reg)
      bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }

  char *buffer = (char *)bbOps.getActualAddr(reg->getValue(), cf->currBB);
  reg->tracked = 1;
  vector<Value *> worklist;
  set<Value *> processed;
  worklist.push_back(bufPtr);
  while (worklist.size())
  {
    Instruction *current = dyn_cast<Instruction>(worklist.back());
    worklist.pop_back();

    if (!current)
      continue;
    if (processed.find(current) != processed.end())
      continue;

    if (Register *reg = cf->processInstAndGetRegister(current))
    {
      reg->tracked = 1;
    }

    for (unsigned i = 0; i < current->getNumOperands(); i++)
    {
      worklist.push_back(current->getOperand(i));
    }
  }

  char *bytes_read = fgets(buffer, size, fptr);

  if (feof(fptr))
  {
    debug(Yes) << "handleFGets : read NULL value\n";
    ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(bufPtr->getType()));
    ci->replaceAllUsesWith(nullP);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
    fileIOCalls[sfd]->insts.push_back(ci);
  }

  else if (bytes_read == NULL)
  {
    debug(Yes) << "handleFGets : read returned error\n";
    setfdiUntracked(sfd);
    bbOps.setConstContigous(false, reg->getValue(), cf->currBB);
    string funcNames[2];
    funcNames[0] = "fopen";
    funcNames[1] = "fseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }

  else
  {
    bbOps.setConstMem(true, reg->getValue(), strlen(buffer), cf->currBB);
    setfptrOffset(sfd, fptr);
    debug(Yes) << "buffer value " << buffer << " " << strlen(buffer) << " address: " << reg->getValue() << "\n";
    Constant *const_array = ConstantDataArray::getString(cf->module->getContext(), StringRef(buffer), true);
    GlobalVariable *gv = new GlobalVariable(*cf->module, const_array->getType(), true, GlobalValue::ExternalLinkage, const_array, "");
    MaybeAlign al(1);
    gv->setAlignment(al);
    IRBuilder<> Builder(ci);
    Instruction *MemCpyInst = Builder.CreateMemCpy(bufPtr, al, gv, al, strlen(buffer) + 1);
    ci->replaceAllUsesWith(bufPtr);
    Value *hookFunc;
    hookFunc = cf->module->getOrInsertFunction("fseek", Type::getInt32Ty(cf->module->getContext()), fptrVal->getType(), Type::getInt64Ty(cf->module->getContext()), Type::getInt32Ty(cf->module->getContext())).getCallee();
    Function *hook = cast<Function>(hookFunc);

    ConstantInt *arg2 = Builder.getInt64(getfptrOffset(sfd, fptr));
    ConstantInt *arg3 = Builder.getInt32(0);
    std::vector<llvm::Value *> putsArgs;
    putsArgs.push_back(fptrVal);
    putsArgs.push_back(arg2);
    putsArgs.push_back(arg3);
    CallInst *seek = Builder.CreateCall(hook, putsArgs);

    fileIOCalls[sfd]->insts.push_back(ci);
    fileIOCalls[sfd]->insertedSeekCalls.push_back(seek);
    stats.incrementLibCallsFolded();
    stats.incrementInstructionsFolded();
  }
}

/**
 * Handle lseek() calls
 * Updates the file offset if the call is successful
 */
void handleLSeek(CallInst *ci)
{
  Value *fdVal = ci->getOperand(0);
  Value *offSetVal = ci->getOperand(1);
  Value *flagVal = ci->getOperand(2);
  uint64_t offset, sfd, flag;
  int fd = 0;
  bool fdConst = cf->getSingleVal(fdVal, sfd) && getfdi(sfd, fd);

  if (fd <= 2)
  {
    return;
  }

  if (!fdConst || !cf->getSingleVal(offSetVal, offset) ||
      !cf->getSingleVal(flagVal, flag))
  {
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fdVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "lseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  long ret = lseek(fd, offset, flag);

  if (ret < 0)
  {
    setfdiUntracked(sfd);
    debug(Yes) << "handleLSeek : seek returned error\n";
    string funcNames[2];
    funcNames[0] = "open";
    funcNames[1] = "lseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  setfdiOffset(sfd, fd);
  cf->addSingleVal(ci, ret, true, true);
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * Handle fseek() calls
 * Updates the file offset if the call is successful
 */
void handleFSeek(CallInst *ci)
{
  Value *fptrVal = ci->getOperand(0);
  Value *offSetVal = ci->getOperand(1);
  Value *flagVal = ci->getOperand(2);
  uint64_t offset, sfd, flag;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  if (!fdConst || !cf->getSingleVal(offSetVal, offset) ||
      !cf->getSingleVal(flagVal, flag))
  {
    if (fdConst)
      setfdiUntracked(sfd);
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fseek";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  int ret = fseek(fptr, offset, flag);

  if (ret != 0)
  {
    setfdiUntracked(sfd);
    debug(Yes) << "handleFSeek : seek returned error\n";
    string funcNames[2];
    funcNames[0] = "fopen";
    funcNames[1] = "fseek";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  setfptrOffset(sfd, fptr);
  cf->addSingleVal(ci, ret, true, true);
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * handle close() calls
 * Just add them to FileIOCalls map
 */
void handleClose(CallInst *ci)
{
  Value *fdVal = ci->getOperand(0);
  uint64_t sfd;
  int fd;
  bool fdConst = cf->getSingleVal(fdVal, sfd) && getfdi(sfd, fd);
  if (!fdConst)
  {
    debug(Yes) << "handleClose : failed to specialize\n";
    if (cf->getSingleVal(fdVal, sfd))
    {
      if (fdInfoMap.find(sfd) == fdInfoMap.end())
        return;

      string funcNames[2];
      funcNames[0] = "open";
      funcNames[1] = "open";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  int fileClose = close(fd);

  if (fileClose != 0)
  {
    debug(Yes) << "handleClose : close returned error\n";
    string funcNames[2];
    funcNames[0] = "open";
    funcNames[1] = "open";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * handle fclose() calls
 * Just add them to FileIOCalls map
 */
void handleFClose(CallInst *ci)
{
  Value *fptrVal = ci->getOperand(0);
  uint64_t sfd;
  FILE *fptr;
  bool fdConst = cf->getSingleVal(fptrVal, sfd) && getfptr(sfd, fptr);
  if (!fdConst)
  {
    debug(Yes) << "handleFClose : failed to specialize\n";
    if (cf->getSingleVal(fptrVal, sfd))
    {
      string funcNames[2];
      funcNames[0] = "fopen";
      funcNames[1] = "fopen";
      removeFileIOCallsFromMap(funcNames, sfd);
    }
    return;
  }
  int fileClose = fclose(fptr);

  if (fileClose != 0)
  {
    debug(Yes) << "handleFClose : fclose returned error\n";
    string funcNames[2];
    funcNames[0] = "fopen";
    funcNames[1] = "fopen";
    removeFileIOCallsFromMap(funcNames, sfd);
    return;
  }
  fileIOCalls[sfd]->insts.push_back(ci);
  stats.incrementLibCallsFolded();
  stats.incrementInstructionsFolded();
}

/**
 * Handle File IO calls such as open, read, pread,lseek,close,fopen,fread,fgets,fseek,fclose, map, munmap
 */
bool handleFileIOCall(CallInst *ci)
{
  string name = ci->getCalledFunction()->getName().str();
  if (name == "open" || name == "open64")
    handleOpen(ci);
  else if (name == "fopen" || name == "fopen64")
    handleFOpen(ci);
  else if (name == "read")
    handleRead(ci);
  else if (name == "write")
    handleWrite(ci);
  else if (name == "fread")
    handleFRead(ci);
  else if (name == "lseek")
    handleLSeek(ci);
  else if (name == "fseek")
    handleFSeek(ci);
  else if (name == "pread")
    handlePRead(ci);
  else if (name == "mmap" || name == "mmap64")
    handleMMap(ci);
  else if (name == "munmap")
    handleMUnmap(ci);
  else if (name == "fgets" || name == "fgets_unlocked")
    handleFGets(ci);
  else if (name == "getline")
    handleGetLine(ci);
  else if (name == "close")
    handleClose(ci);
  else if (name == "fclose")
    handleFClose(ci);
  else if (name == "feof")
    handleFEOF(ci);
  else
    return false;

  stats.incrementTotalLibCalls();
  return true;
}

bool isFileDescriptor(Value *value)
{
  if (ConstantInt *CI = dyn_cast<ConstantInt>(value))
  {
    uint64_t val = CI->getZExtValue();
    return fdInfoMap.find(val) != fdInfoMap.end();
  }
  return false;
}

void deleteFileIOCalls()
{
  auto Dstart = std::chrono::high_resolution_clock::now();
  for (map<uint64_t, FileInsts *>::iterator it = fileIOCalls.begin(); it != fileIOCalls.end(); ++it)
  {
    bool isSpecialized = (it->second)->isSpecialized;
    if (isSpecialized == true)
    {
      for (int i = (it->second)->insertedSeekCalls.size() - 1; i >= 0; i--)
      {
        (it->second)->insertedSeekCalls[i]->eraseFromParent();
      }
    }
    vector<Instruction *> insts = (it->second)->insts;
    for (int i = insts.size() - 1; i >= 0; i--)
    {
      debug(Yes) << "insts  " << dyn_cast<CallInst>(insts[i])->getCalledFunction()->getName().data() << insts[i]->getNumUses() << dyn_cast<CallInst>(insts[i])->getParent()->getParent()->getName() << "\n";
      if (insts[i]->getNumUses() > 0)
      {
        CallInst *Inst = dyn_cast<CallInst>(insts[i]);
        if (strcmp(Inst->getCalledFunction()->getName().data(), "open") == 0)
        {
          llvm::Type *type = llvm::IntegerType::getInt32Ty(cf->module->getContext());
          llvm::Constant *zeroVal = llvm::ConstantInt::get(type, 0, true);
          insts[i]->replaceAllUsesWith(zeroVal);
        }
        else if (strcmp(Inst->getCalledFunction()->getName().data(), "fopen") == 0)
        {
          ConstantPointerNull *nullP = ConstantPointerNull::get(dyn_cast<PointerType>(insts[i]->getType()));
          insts[i]->replaceAllUsesWith(nullP);
        }
      }
      insts[i]->eraseFromParent();
    }
  }
  auto Dstop = std::chrono::high_resolution_clock::now();
  auto Dduration = std::chrono::duration_cast<std::chrono::microseconds>(Dstop - Dstart);
  debug(Yes) << "[DELETEFILEIO] Analysis took: " << Dduration.count() << " microseconds... \n";
}

void initFileIO()
{
  numConfigFiles = rand() % 100000000 + 100000;
  for (auto &fileName : fileNames)
  {
    configFileNames.push_back(fileName);
  }
}