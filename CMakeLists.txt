cmake_minimum_required(VERSION 3.5.1)
project(analysis)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++14 support
# for your compiler.
# Check for C++14 support and set the compilation flag
include(CheckCXXCompilerFlag)

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})


#set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_FLAGS "-std=c++14 -fpic -fno-rtti")

add_subdirectory (mlta/src)
#add_subdirectory(SVF)
add_subdirectory(pdg)
#add_subdirectory(trimmer)
#set(LLVM_ENABLE_ASSERTIONS ON)
add_subdirectory(src)