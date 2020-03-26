project (build_gtest)

add_custom_target(build_gtest WORKING_DIRECTORY ${yassi_nextgen_SOURCE_DIR}/05_third_party/05_gtest COMMAND ./install_gtest.sh)
