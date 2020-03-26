# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.
if( NOT LLVM_REQUIRES_RTTI )
  if( NOT LLVM_REQUIRES_EH )
    set(LLVM_EXPORTED_SYMBOL_FILE ${CMAKE_CURRENT_SOURCE_DIR}/YassiReplay.exports)
  endif()
endif()

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
endif()

add_definitions(-DYASSI_MEAS_PASS)
add_definitions(-DYASSI_PASS)
set (BASE_PATH %%BASE_PATH_PATTERN%%)

set(CMAKE_CXX_STANDARD 17)

find_package(Boost REQUIRED)

add_llvm_loadable_module(YassiReplay
    yassi_replay_pass.cpp
    yassi_database.cpp
    yassi_basepass.cpp
    yassi_replaybase.cpp
    yassi_basedatabase.cpp
    yassi_baseutils.cpp
    yassi_basicblocks.cpp
    yassi_functions.cpp
    yassi_branch.cpp
    yassi_remove_nondet_functions.cpp
    yassi_changemainmeasure.cpp
    yassi_changeassigns.cpp
    yassi_removeprintf.cpp
    yassi_beginend.cpp
    yassi_fillnames.cpp
    yassi_removeforcefree.cpp
    02_types/yassi_basetype.cpp
    02_types/yassi_booltype.cpp
    02_types/yassi_doubletype.cpp
    02_types/yassi_floattype.cpp
    02_types/yassi_integer16type.cpp
    02_types/yassi_integer32type.cpp
    02_types/yassi_integer64type.cpp
    02_types/yassi_integer1type.cpp
    02_types/yassi_integer8type.cpp
    02_types/yassi_pointertype.cpp
    02_types/yassi_typefactory.cpp
    02_types/yassi_structtype.cpp
    02_types/yassi_arraytype.cpp
    02_types/yassi_voidtype.cpp
    02_types/yassi_functiontype.cpp

    DEPENDS
    intrinsics_gen
)

include_directories(
    ${Boost_INCLUDE_DIRS}
)
target_link_libraries(YassiReplay
    ${BASE_PATH}/05_third_party/lib/libsqlite3.a
)
