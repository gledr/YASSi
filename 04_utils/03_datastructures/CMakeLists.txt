project(yassi_datastructures)

add_executable(testbench_datastructuretree
   yassi_datastructuretree.cpp
   yassi_datastructuretree_testbench.cpp
)

set(CMAKE_CXX_STANDARD 17)

target_include_directories(testbench_datastructuretree PUBLIC  
    ${yassi_utils_SOURCE_DIR}
)

set(EXECUTABLE_OUTPUT_PATH ${yassi_nextgen_SOURCE_DIR}/08_bin)
