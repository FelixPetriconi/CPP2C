set(LLVM_LINK_COMPONENTS
  Support
  )

add_clang_executable(CPP2C
  CPP2C.cpp
  )

target_link_libraries(CPP2C
  PRIVATE
  clangAST
  clangASTMatchers
  clangBasic
  clangFrontend
  clangTooling
  clangToolingRefactor
  )
