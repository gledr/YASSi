project (yassi_test)

add_executable(yassi_test
    main.cpp
    yassi_testengine.cpp
    ${yassi_frontend_SOURCE_DIR}/utils/yassi_database.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_basedatabase.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baseutils.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_resultchecker.cpp
)

add_dependencies(yassi_test build_gtest)

find_package(Boost REQUIRED COMPONENTS 
    filesystem
)

target_link_libraries(yassi_test
    ${Boost_LIBRARIES}
    gtest
    pthread
    jsoncpp
    dl
    ${yassi_nextgen_SOURCE_DIR}/05_third_party/lib/libsqlite3.a
)

target_include_directories(yassi_test PUBLIC
    ${yassi_utils_SOURCE_DIR}
    ${yassi_frontend_SOURCE_DIR}
    ${yassi_frontend_SOURCE_DIR}/utils
    ${yassi_datastructures_SOURCE_DIR}
)
