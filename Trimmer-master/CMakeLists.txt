cmake_minimum_required(VERSION 3.22)

find_package(LLVM REQUIRED CONFIG)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

file(GLOB_RECURSE files "${CMAKE_CURRENT_SOURCE_DIR}/src/*")

add_library(ConstantFolding MODULE ${files})




# Use C++11 to compile your pass (i.e., supply -std=c++11).
target_compile_features(ConstantFolding PRIVATE cxx_range_for cxx_auto_type)


# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(ConstantFolding 
  PROPERTIES
  COMPILE_FLAGS " -fPIC -D__GLIBCXX_USE_CXX11_ABI=0 -fno-rtti" #-DNDEBUG  -fsanitize=address
  LINK_FLAGS "-rdynamic -lffi"
  ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/"
  LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/"
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/"
  PREFIX ""
  )