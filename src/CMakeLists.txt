include_directories(../mlta/src/lib)
link_directories(../mlta/build/lib)

set(llvm_libs LLVMAsmParser LLVMSupport LLVMCore LLVMAnalysis LLVMIRReader LLVMBitWriter LLVMTransformUtils)

add_executable(pa PreAnalysis.cpp)
set(SVF_OUTPUT "/home/xd/jzz/projects/SCA-Prun/SVF/build/output")
target_include_directories(pa SYSTEM PUBLIC ${LLVM_INCLUDE_DIRS} ${SVF_OUTPUT}/include/svf)
target_link_directories(pa PRIVATE ${SVF_OUTPUT}/lib)
target_link_libraries(pa SvfLLVM SvfCore z3 Analyzer ${llvm_libs})
#target_compile_options(pa PRIVATE -g -O2 -UNDEBUG)

add_executable(cgd CGDumper.cpp)
target_include_directories(cgd SYSTEM PUBLIC  ${PROJECT_SOURCE_DIR}/pdg/include ${PROJECT_SOURCE_DIR}/pdg/src)
target_link_libraries(cgd AnalyzerStatic ${llvm_libs} pdgStatic)
#target_compile_options(cgd PRIVATE -g -O2 -UNDEBUG)

add_executable(tiny tinyAnalysis.cpp)
target_include_directories(tiny SYSTEM PUBLIC ${LLVM_INCLUDE_DIRS})
target_link_libraries(tiny ${llvm_libs})
#target_compile_options(tiny PRIVATE -g -O2 -UNDEBUG)


set_target_properties(tiny pa cgd 
PROPERTIES 
RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)