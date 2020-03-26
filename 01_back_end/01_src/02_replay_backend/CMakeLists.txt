project (replay_backend)

add_subdirectory(01_core)
add_subdirectory(02_utils)

add_definitions(-DYASSI)

add_library(replay_backend
    01_core/wrapper/yassi_replay_wrapper.cpp
    01_core/wrapper/yassi_replay.cpp
    01_core/wrapper/yassi_object.cpp
    01_core/stimulator/yassi_stimulatemodel.cpp
    01_core/observer/yassi_observemodel.cpp
    02_utils/yassi_database.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baselogger.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baseutils.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_basedatabase.cpp
    02_utils/yassi_logger.cpp
)

target_include_directories(replay_backend PUBLIC
    01_core/observer
    01_core/stimulator
    01_core/wrapper
    02_utils
    ${yassi_utils_SOURCE_DIR}
    ${yassi_types_SOURCE_DIR}
    ${yassi_datastructures_SOURCE_DIR}
)
