project(yassi_frontend)

add_executable(yassi
    main.cpp 
    ${yassi_utils_SOURCE_DIR}/yassi_baselogger.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baseutils.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_resultchecker.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_exception.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_basedatabase.cpp
    yassi_frontend.cpp
    yassi_bdd.cpp
    yassi_object.cpp
    replay/yassi_replay.cpp
    replay/yassi_testvectors.cpp
    debug/yassi_errorlocalization.cpp
    yassi_bitcode.cpp
    yassi_checkmodel.cpp
    yassi_executor.cpp
    yassi_common.cpp
    utils/yassi_timer.cpp
    utils/yassi_utils.cpp
    utils/yassi_database.cpp
    utils/yassi_logger.cpp
)

find_package(Boost REQUIRED COMPONENTS 
    filesystem
    program_options
)

add_dependencies(yassi
    build_sqlite3
    build_llvm
    llvm_pass
    yassi_config
    build_jsoncpp
)

target_link_libraries(yassi
    ${Boost_LIBRARIES}
    rt
    pthread
    jsoncpp
    dl
    sqlite3
)

target_include_directories(yassi PUBLIC 
    replay
    utils
    debug
    ${yassi_utils_SOURCE_DIR}
    ${yassi_datastructures_SOURCE_DIR}
    .
)
