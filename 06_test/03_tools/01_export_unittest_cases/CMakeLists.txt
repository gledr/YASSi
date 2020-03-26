project(yassi_unittestexporter)

add_executable(yassi_unittest_exporter 
    main.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baseutils.cpp
)

find_package(Boost REQUIRED COMPONENTS
    filesystem
)

include_directories(${yassi_utils_SOURCE_DIR})

target_link_libraries(yassi_unittest_exporter
    ${Boost_LIBRARIES}
)
