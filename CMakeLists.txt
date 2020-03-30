cmake_minimum_required(VERSION 3.10)

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
endif()

set(EXECUTABLE_OUTPUT_PATH ${yassi_root_SOURCE_DIR}/08_bin)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${yassi_root_SOURCE_DIR}/09_lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${yassi_root_SOURCE_DIR}/09_lib)

set(CMAKE_CXX_STANDARD 17)
project (yassi_root)

add_subdirectory(01_back_end)
add_subdirectory(02_front_end)
add_subdirectory(03_llvm_opt_pass)
add_subdirectory(04_utils)
add_subdirectory(05_third_party)
add_subdirectory(06_test)
add_subdirectory(07_configuration)


set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -pedantic -Wextra")
set(CMAKE_BUILD_TYPE Debug)
#set(CMAKE_BUILD_TYPE Release)

enable_testing()
add_test(NAME yassi_build_test COMMAND ${yassi_root_SOURCE_DIR}/08_bin/yassi_test)
