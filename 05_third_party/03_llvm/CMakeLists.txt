project (build_llvm)

add_custom_target(build_llvm WORKING_DIRECTORY ${yassi_root_SOURCE_DIR}/05_third_party/03_llvm COMMAND ./install_llvm.sh)
