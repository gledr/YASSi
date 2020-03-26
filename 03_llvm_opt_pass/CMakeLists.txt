project(llvm_pass)

add_custom_target(llvm_pass COMMAND make  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

add_dependencies(llvm_pass 
    build_sqlite3
    build_llvm
)
