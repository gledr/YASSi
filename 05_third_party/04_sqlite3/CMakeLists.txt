project (build_sqlite3)

add_custom_target(build_sqlite3 WORKING_DIRECTORY ${yassi_nextgen_SOURCE_DIR}/05_third_party/04_sqlite3 COMMAND ./install_sqlite3.sh)
