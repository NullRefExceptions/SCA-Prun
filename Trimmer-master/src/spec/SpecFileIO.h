#ifndef SPECFILEIO_H_
#define SPECFILEIO_H_
#include "llvm/IR/Instructions.h"
#include "map"
#include "list"
using namespace llvm;
using namespace std;
// used for tracking File IO instructions.
struct FileInsts
{
  vector<Instruction *> insts;             // collection of fileIO instructions which are specialized
  vector<Instruction *> insertedSeekCalls; // seek calls inserted on behalf of reads
  bool isSpecialized;                      // tracks whether the file is completely specialized or not
};
// used to bridge the gap between mmap and munmap instructions.
struct MMapInfo
{
  int sfd;      // the file descriptor number
  char *buffer; // the buffer where mmap instruction is mapped
};

struct FdInfo
{
  FILE *fptr;     // for fopen, fread, fseek, fgets, fclose calls
  char *fileName; // File name
  long offset;    // current offset of the File
  int fd;         // for open, read, lseek, pread, mmap, munmap, close calls
  bool tracked;   // tracks whether the file structure is valid or not
};

extern map<int, uint64_t> fdInfoMap;
extern map<uint64_t, FileInsts *> fileIOCalls;
extern list<string> configFileNames;

void initFileIO();
bool getfptr(int sfd, FILE *&fptr);
bool getfdi(int sfd, int &fd);
bool handleFileIOCall(CallInst *ci);
bool isFileDescriptor(Value *value);
void deleteFileIOCalls();
#endif