project(symbolic_backend)

add_subdirectory(01_core)
add_subdirectory(02_utils)

add_definitions(-DYASSI)

add_library(symbolic_backend
    01_core/wrapper/yassi_object.cpp
    01_core/wrapper/yassi_backend_wrapper.cpp
    01_core/wrapper/yassi_backend.cpp
    01_core/memory/yassi_memory.cpp
    01_core/memory/yassi_memoryexporter.cpp
    01_core/solver/yassi_allsat.cpp
    01_core/solver/yassi_arithmetic_operators.cpp
    01_core/solver/yassi_compare_operators.cpp
    01_core/solver/yassi_fpa.cpp
    01_core/solver/yassi_pointerinstruction.cpp
    01_core/solver/yassi_propagation.cpp
    01_core/solver/yassi_symbolicexecutor.cpp
    01_core/solver/yassi_typecast.cpp
    01_core/solver/yassi_z3utils.cpp
    01_core/solver/yassi_solver.cpp
    01_core/solver/yassi_loadstore.cpp
    01_core/solver/yassi_forcefree.cpp
    01_core/variables/yassi_basevariable.cpp
    01_core/variables/yassi_integervariable.cpp
    01_core/variables/yassi_realvariable.cpp
    01_core/variables/yassi_boolvariable.cpp
    01_core/variables/yassi_pointervariable.cpp
    01_core/variables/yassi_voidvariable.cpp
    01_core/variables/yassi_structvariable.cpp
    01_core/variables/yassi_arrayvariable.cpp
    01_core/variables/yassi_functionvariable.cpp
    01_core/variables/yassi_variablefactory.cpp
    01_core/intrinsics/yassi_intrinsics.cpp
    02_utils/yassi_timer.cpp
    02_utils/yassi_namemangling.cpp
    02_utils/yassi_database.cpp
    02_utils/yassi_logger.cpp
    02_utils/yassi_utils.cpp
    02_utils/yassi_callstack.cpp
    02_utils/yassi_pathstack.cpp
    02_utils/yassi_runtimeexception.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_exception.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baselogger.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_baseutils.cpp
    ${yassi_utils_SOURCE_DIR}/yassi_basedatabase.cpp
    ${yassi_types_SOURCE_DIR}/yassi_basetype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_booltype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_integer1type.cpp
    ${yassi_types_SOURCE_DIR}/yassi_integer8type.cpp
    ${yassi_types_SOURCE_DIR}/yassi_integer16type.cpp
    ${yassi_types_SOURCE_DIR}/yassi_integer32type.cpp
    ${yassi_types_SOURCE_DIR}/yassi_integer64type.cpp
    ${yassi_types_SOURCE_DIR}/yassi_voidtype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_pointertype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_floattype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_doubletype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_structtype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_arraytype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_functiontype.cpp
    ${yassi_types_SOURCE_DIR}/yassi_typefactory.cpp
    ${yassi_datastructures_SOURCE_DIR}/yassi_datastructuretree.cpp
)

add_dependencies(symbolic_backend build_z3)

target_include_directories(symbolic_backend PUBLIC  
    01_core/wrapper
    01_core/solver
    01_core/variables
    01_core/memory
    01_core/intrinsics
    02_utils
    ${yassi_utils_SOURCE_DIR}
    ${yassi_types_SOURCE_DIR}
    ${yassi_datastructures_SOURCE_DIR}
    ${yassi_nextgen_SOURCE_DIR}/01_back_end/02_include
)

