/** 
 * @file yassi_object.cpp
 * @brief Virtual Base Class of  the Execution Backend Library
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include "yassi_object.hpp"

using namespace Yassi::Backend::Execute;


std::string                 Object::p_current_function = "empty";
std::string                 Object::p_bin_dir = "";
std::string                 Object::p_backend_bin = "";
std::string                 Object::p_smt_dir = "";
std::string                 Object::p_execution_url = "";
std::string                 Object::p_file_being_exected = "empty";
std::string                 Object::p_logfile_name = "";
std::string                 Object::p_database_url = "";
std::vector<std::string>    Object::p_current_path_history;
PathStack                   Object::p_path_stack;
size_t                      Object::p_max_depth = 0;
size_t                      Object::p_timeout = 0;
size_t                      Object::p_line_num_is_executed = 0;
bool                        Object::p_debug = false;
bool                        Object::p_quiet = false;
bool                        Object::p_log_file_enabled = false;
bool                        Object::p_error_localization = false;
bool                        Object::p_dump_memory = false;
bool                        Object::p_dump_smt = false;


/**
 * @brief Constructor
 */
Object::Object()
{
}

/**
 * @brief Destructor
 */
Object::~Object()
{
}

/**
 * @brief Get the function currently executed 
 * 
 * @return std::string
 */
std::string Object::get_current_function()
{
    return Object::p_current_function;
}

/**
 * @brief Set the function currently beeing executed
 * 
 * @param function: The function as std::string
 */
void Object::set_current_function(std::string const & function)
{
    Object::p_current_function = function;
}

/**
 * @brief Get the path history (basic blocks and functions) 
 * 
 * @return std::vector<std::string>>
 */
std::vector<std::string> Object::get_path_history()
{
    return Object::p_current_path_history;
}

/**
 * @brief Get the path history (basic blocks and functions)
 * 
 * @return std::string
 */
std::string Object::get_path_history_debug()
{
    std::stringstream ret_val;

    for(auto& itor:  Object::p_current_path_history){
        ret_val << itor << ",";
    }

    return ret_val.str();
}

/**
 * @brief Add an element to the path history
 * 
 * @param element: The path element as std::string
 */
void Object::add_path_element(std::string const & element)
{
    assertion_check(!element.empty());
    Object::p_current_path_history.push_back(element);
}

/**
 * @brief Get the linenumber currently beeing executed
 *
 * @return std::string
 */
size_t Object::get_line_num_execution()
{
    return Object::p_line_num_is_executed;
}

/**
 * @brief Set the linenumber currently being executed
 * 
 * @param line_num: The linenumber as std::string
 */
void Object::set_line_num_in_execution(size_t const line_num)
{
    Object::p_line_num_is_executed = line_num - 2; // TODO CONSTANT FOR INTRINSIC HEADER ADD
}

/**
 * @brief Set the name of the file beeing executed
 * 
 * @param file: The name of the file as std::string
 */
void Object::set_file_being_executed(std::string const & file)
{
    Object::p_file_being_exected = file;
}

/**
 * @brief Get the name of the file beeing executed
 * 
 * @return std::string
 */
std::string Object::get_file_being_executed()
{
    return Object::p_file_being_exected;
}

/**
 * @brief Wrapper function for name mangling
 * 
 * Adds the filename and the line number automatically
 * 
 * @param name: The name to be mangled
 * @return std::string
 */
std::string Object::mangle_name(std::string const & name) 
{
    assert (Object::p_current_function != "");
    
    return NameMangling::mangle_name(name, Object::p_current_function, Object::p_file_being_exected);
}

/**
 * @brief Resolve the url where backend binaries are stored
 * 
 * @return std::string
 */
std::string Object::get_bin_dir()
{
    return Object::p_bin_dir;
}

/**
 * @brief Set the url where backend binaries are getting stored
 * 
 * @param url p_url: The url where backend binaries are getting stored
 */
void Object::set_bin_dir(std::string const & url)
{
    Object::p_bin_dir = url;
}

/**
 * @brief Get the name of the backend binary
 * 
 * @return std::string
 */
std::string Object::get_bin_name()
{
    return Object::p_backend_bin;
}

/**
 * @brief Set the name of the backend binary
 * 
 * @param name: The nmae as std::string
 */
void Object::set_bin_name(std::string const & name)
{
    Object::p_backend_bin = name;
}

/**
 * @brief Get the maximal depth beeing used a bound
 * 
 * @return size_t
 */
size_t Object::get_max_depth()
{
    return Object::p_max_depth;
}

/**
 * @brief Set the maximal depth being used as bound
 * 
 * @param depth: The depth as size_t
 */
void Object::set_max_depth(size_t const depth)
{
    Object::p_max_depth = depth;
}

/**
 * @brief Resolve the url where SMT2 instances are getting dumped
 * 
 * @return std::string
 */
std::string Object::get_smt_dir()
{
    return Object::p_smt_dir;
}

/**
 * @brief Set the url where SMT2 instanced are getting dumped
 * 
 * @param url: The url as std::string
 */
void Object::set_smt_dir(std::string const & url)
{
    Object::p_smt_dir = url;
}

/**
 * @brief Get verbobse mode
 * 
 * @return bool
 */
bool Object::get_debug()
{
    return p_debug;
}

/**
 * @brief Set verbose mode
 * 
 * @param val: The mode as bool flag
 */
void Object::set_debug(bool const val)
{
    Object::p_debug = val;
}

/**
 * @brief Set quiet mode
 * 
 * @param val: The mode as bool flag
 */
void Object::set_quiet(bool const val)
{
    Object::p_quiet = val;
}

/**
 * @brief Get quiet mode
 * 
 * @return bool
 */
bool Object::get_quiet()
{
    return p_quiet;
}

/**
 * @brief Get the url of the directory called Yassi
 * 
 * @return std::string
 */
std::string Object::get_execution_url()
{
    return Object::p_execution_url;
}

/**
 * @brief Set the url of the directory called Yassi
 * 
 * @param url
 */
void Object::set_execution_url(std::string const & url)
{
    Object::p_execution_url = url;
}

/**
 * @brief Get logfile enabled mode
 * 
 * @return bool
 */
bool Object::get_log_file_enabled()
{
    return Object::p_log_file_enabled;
}

/**
 * @brief Set the mode for logfiles
 * 
 * @param val The logfile mode
 */
void Object::set_log_file_enabled(bool const  val)
{
    Object::p_log_file_enabled = val;
}

/**
 * @brief Get Error Localization Mode Active
 * 
 * @return bool
 */
bool Object::get_error_localization()
{
    return Object::p_error_localization;
}

/**
 * @brief Set Error Locatliation Model
 * 
 * @param val Active/Disabled
 */
void Object::set_error_localization(bool const val)
{
    Object::p_error_localization = val;
}

/**
 * @brief Get Dump Memory Active
 * 
 * @return bool
 */
bool Object::get_dump_memory()
{
    return Object::p_dump_memory;
}

/**
 * @brief Set Dump Memory Mode
 * 
 * @param val Enabled/Disabled
 */
void Object::set_dump_memory(bool const val)
{
    Object::p_dump_memory = val;
}

/**
 * @brief Get the Value stored for SMT dummping
 * 
 * @return bool
 */
bool Object::get_dump_smt()
{
    return Object::p_dump_smt;
}

/**
 * @brief Set Dump SMT to store to the Filesystem
 *
 * @param val True/Valse
 */
void Object::set_dump_smt(bool const val)
{
    Object::p_dump_smt = val;
}

/**
 * @brief Get the Configured Timeout
 * 
 * @return size_t
 */
size_t Object::get_timeout()
{
    return Object::p_timeout;
}

/**
 * @brief Set the Timeout for the Backend
 * 
 * @param to Value
 */
void Object::set_timeout(size_t const to)
{
    Object::p_timeout = to;
}

/**
 * @brief Get the Name for the Logfile
 * 
 * @return std::string
 */
std::string Object::get_logfile_name()
{
    return Object::p_logfile_name;
}

/**
 * @brief Set the Name of the Logfile
 * 
 * @param name Logfile Name
 */
void Object::set_logfile_name(std::string const & name)
{
    Object::p_logfile_name = name;
}

/**
 * @brief Get Location of the Database File
 *
 * @return std::string
 */
std::string Object::get_database_url()
{
    return Object::p_database_url;
}

/**
 * @brief Set Location of the Database File
 * 
 * @param url Database Location
 */
void Object::set_database_url(std::string const & url)
{
    Object::p_database_url = url;
}
