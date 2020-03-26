# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.
if( NOT LLVM_REQUIRES_RTTI )
  if( NOT LLVM_REQUIRES_EH )
    set(LLVM_EXPORTED_SYMBOL_FILE ${CMAKE_CURRENT_SOURCE_DIR}/YassiInstr.exports)
  endif()
endif()

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
endif()

set(CMAKE_CXX_STANDARD 17)

add_definitions(-DYASSI_INSTR_PASS)
add_definitions(-DYASSI_PASS)

set (BASE_PATH %%BASE_PATH_PATTERN%%)

find_package(Boost REQUIRED)

add_llvm_loadable_module(YassiInstr
  yassi_instrumentation_pass.cpp
  yassi_database.cpp
  yassi_baseutils.cpp
  yassi_basicblocks.cpp
  yassi_basepass.cpp
  yassi_instrbase.cpp
  yassi_isolatefunction.cpp
  yassi_functions.cpp
  yassi_alloca.cpp
  yassi_changemallocfree.cpp
  yassi_beginend.cpp
  yassi_binaryop.cpp
  yassi_compare.cpp
  yassi_cmdline_arguments.cpp
  yassi_loadstore.cpp
  yassi_cast.cpp
  yassi_functioncall.cpp
  yassi_memset.cpp
  yassi_memcpy.cpp
  yassi_switch.cpp
  yassi_branch.cpp
  yassi_select.cpp
  yassi_getelementptr.cpp
  yassi_globalinit.cpp
  yassi_functionpointer.cpp
  yassi_seperategeteleptr.cpp
  yassi_seperatecastinstr.cpp
  yassi_fillnames.cpp
  yassi_removeinstructions.cpp
  yassi_removeerrorfunction.cpp
  yassi_changeassertfunction.cpp
  yassi_changeprintf.cpp
  yassi_changeassumefunction.cpp
  yassi_changeerrorfunction.cpp
  yassi_demangle.cpp
  yassi_listexternalfunctions.cpp
  yassi_explore_external_functions.cpp
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
  yassi_datastructuretree.cpp
  yassi_cleanphi.cpp
  yassi_basedatabase.cpp

  DEPENDS
  intrinsics_gen
  )
  
target_link_libraries(ForestInstr 
    ${BASE_PATH}/05_third_party/lib/libsqlite3.a
)

include_directories(
    ${Boost_INCLUDE_DIRS}
)
