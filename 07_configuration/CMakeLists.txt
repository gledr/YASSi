project(yassi_config)

add_custom_target(yassi_config COMMAND ${yassi_config_SOURCE_DIR}/install_yassi.sh WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
