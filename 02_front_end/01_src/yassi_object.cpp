/** 
 * @file yassi_object.cpp
 * @brief Virtual Base Class for the Yassi Frontend
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

using namespace Yassi::Frontend;


std::string Object::p_tmp_folder = "";
std::string Object::p_editor = "";
std::string Object::p_image_viewer = "";
std::string Object::p_compare_tool = "";
std::string Object::p_base_path = "";
std::string Object::p_modelcheck_backend_name = "";
std::string Object::p_replay_backend_name = "";
std::string Object::p_bughunter_backend_name = "";
std::string Object::p_current_url = "";
std::string Object::p_logfile_name = "";
std::string Object::p_seed_function = "";
size_t      Object::p_max_depth = 0;
size_t      Object::p_timeout = 0;

bool Object::p_debug            = false;
bool Object::p_quiet            = false;
bool Object::p_log_file_enabled = false;
bool Object::p_dump_memory      = false;
bool Object::p_dump_smt         = false;

std::vector<std::string> Object::p_source_files;


/**
 * @brief Constructor
 */
Object::Object()
{
    p_database = new Database(this->get_db_dir() + "database.db");
}

/**
 * @brief Destructor
 */
Object::~Object()
{
    delete p_database; p_database = nullptr;
}

/**
 * @brief Configure the location of the temporary generated data
 * 
 * @param path Path to the location
 */
void Object::set_tmp_folder(std::string const & path)
{
    /*
     * Ensure, that all paths have an ending Slash 
     */
    if(path.back() != '/'){
        Object::p_tmp_folder = path + "/";
    } else {
        Object::p_tmp_folder = path;
    }
}

/**
 * @brief Get the configured path for the temporary data
 * 
 * @return std::string
 */
std::string Object::get_tmp_folder()
{
    return Object::p_tmp_folder;
}

/**
 * @brief Check which compare tool has been enabled
 * kompare, meld, etc.
 * 
 * @return std::string
 */
std::string Object::get_compare_tool()
{
    return Object::p_compare_tool;
}

/**
 * @brief Set which compare tool should be used 
 * kompare, meld, etc.
 * 
 * @param tool Name of the compare tool
 */
void Object::set_compare_tool(std::string const & tool)
{
    Object::p_compare_tool = tool;
}

/**
 * @brief Check which editor has been configured
 * 
 * @return std::string
 */
std::string Object::get_editor()
{
    return Object::p_editor;
}

/**
 * @brief Set which editor should be used 
 * 
 * @param editor Name of the editor
 */

void Object::set_editor(std::string const & editor)
{
    Object::p_editor = editor;
}

/**
 * @brief Check which image viewer should be used
 * 
 * @return std::string
 */
std::string Object::get_image_viewer()
{
    return Object::p_image_viewer;
}

/**
 * @brief Configure the image viewer to be used
 * 
 * @param viewer Name of the image viewer
 */
void Object::set_image_viewer(std::string const& viewer)
{
    Object::p_image_viewer = viewer;
}

/**
 * @brief Get the location of the temporary source files
 * 
 * @return std::string
 */
std::string Object::get_src_dir() 
{
    return Object::p_tmp_folder + "/src/";
}

/**
 * @brief Get the location of the temporary binaries
 * 
 * @return std::string
 */
std::string Object::get_bin_dir() 
{
    return Object::p_tmp_folder + "/bin/";
}

/**
 * @brief Get the location of the temporary database
 * 
 * @return std::string
 */
std::string Object::get_db_dir()
{
    return Object::p_tmp_folder + "/db/";
}

/**
 * @brief Get the location of the temporary image files
 * 
 * @return std::string
 */
std::string Object::get_img_dir() 
{
    return Object::p_tmp_folder + "/img/";
}

/**
 * @brief Get the location of the temporary SMT files
 * 
 * @return std::string
 */
std::string Object::get_smt_dir()
{
    return Object::p_tmp_folder + "/smt2/";
}

/**
 * @brief Get the location of the temporary logfiles
 * 
 * @return std::string
 */
std::string Object::get_log_dir()
{
    return Object::p_tmp_folder + "/log/";
}

/**
 * @brief Get the path to the configured C++ Compiler
 * 
 * @return std::string
 */
std::string Object::get_cxx()
{
    return Object::p_base_path + "05_third_party/bin/clang++";
}

/**
 * @brief Get the path to the configured LLVM Optimizer
 * 
 * @return std::string
 */
std::string Object::get_opt()
{
    return Object::p_base_path + "05_third_party/bin/opt";
}

/**
 * @brief Get the path to the configured LLVM Disasembly
 * 
 * @return std::string
 */
std::string Object::get_dis_asm()
{
    return Object::p_base_path + "05_third_party/bin/llvm-dis";
}

/**
 * @brief Get the names of all source files
 * 
 * @return std::vector< std::string >
 */
std::vector<std::string> Object::get_source_files()
{
     return Object::p_source_files;
}

/**
 * @brief Set all source file to used 
 * 
 * @param files Names of the files
 */
void Object::set_source_files(std::vector<std::string> const & files)
{
    Object::p_source_files = files;
}

/**
 * @brief Get the configured base path
 * 
 * @return std::string
 */
std::string Object::get_base_path()
{
    return Object::p_base_path;
}

/**
 * @brief Set the currently used base path
 * 
 * @param path: The url of the base_path
 */
void Object::set_base_path(std::string const & path)
{
    /*
     * Ensure, that all paths have an ending Slash 
     */
    if(path.back() != '/'){
        Object::p_base_path = path + "/";
    } else {
        Object::p_base_path = path;
    }
}

/**
 * @brief Get the name of the modelchecker binary
 * 
 * @return std::string
 */
std::string Object::get_modelcheck_backend_name()
{
    return Object::p_modelcheck_backend_name;
}

/**
 * @brief Set the name to be used for the model checking binary
 * 
 * @param name: The name
 */
void Object::set_modelcheck_backend_name(std::string const & name)
{
    Object::p_modelcheck_backend_name = name;
}

/**
 * @brief Get the url of the folder yassi has been started
 * 
 * @return std::string
 */
std::string Object::get_execution_url()
{
    return Object::p_current_url;
}

/**
 * @brief Set the url of the folder has been started
 * 
 * @param url: The url
 */
void Object::set_execution_url(std::string const & url)
{
    /*
     * Ensure, that all paths have an ending Slash 
     */
    if(url.back() != '/'){
        Object::p_current_url = url + "/";
    } else {
        Object::p_current_url = url;
    }
}

/**
 * @brief Shows if Yassi is in Verbose Mode
 * 
 * @return bool
 */
bool Object::get_debug()
{
    return Object::p_debug;
}

/**
 * @brief Set Verbose Mode of Yassi
 * 
 * @param val Next Verbose Mode
 */
void Object::set_debug(bool val)
{
    Object::p_debug = val;
}

/**
 * @brief Get the name used for the replay backend binary
 * 
 * @return std::string
 */
std::string Object::get_replay_backend_name()
{
    return Object::p_replay_backend_name;
}

/**
 * @brief Set the name used for the replay backend binary
 * 
 * @param name The name to be used for the binary
 */
void Object::set_replay_backend_name(std::string const & name)
{
    Object::p_replay_backend_name = name;
}

/**
 * @brief Get the Maximun Depth for Bounded Model Checking
 * 
 * @return size_t
 */
size_t Object::get_max_depth()
{
    return Object::p_max_depth;
}

/**
 * @brief Set the Maximun Depth for Bounded Model Checking
 * 
 * @param depth p_depth:...
 */
void Object::set_max_depth(size_t const depth)
{
    Object::p_max_depth = depth;
}

/**
 * @brief ...
 * 
 * @return std::string
 */
std::string Object::get_bughunter_binary_name()
{
    return Object::p_bughunter_backend_name;
}

/**
 * @brief ...
 * 
 * @param name p_name:...
 */
void Object::set_bughunter_binary_name(std::string const & name)
{
    Object::p_bughunter_backend_name = name;
}

/**
 * @brief Check if quiet mode has been enabled
 * 
 * @return bool
 */
bool Object::get_quiet()
{
    return Object::p_quiet;
}

/**
 * @brief Enable quiet mode - no output - for unit testing
 * 
 * @param mode Enable/Disable
 */
void Object::set_quiet(bool const mode)
{
    Object::p_quiet = mode;
}

/**
 * @brief Check if logging to the filesystem is enabled
 * 
 * @return bool
 */
bool Object::get_log_file_enabled()
{
    return Object::p_log_file_enabled;
}

/**
 * @brief Enable Logging to the filesystem
 * 
 * @param val Enabled/Disabled
 */
void Object::set_log_file_enabled(bool val)
{
    Object::p_log_file_enabled = val;
}

/**
 * @brief Check if memory layout dumping is enabled
 * 
 * @return bool
 */
bool Object::get_dump_memory()
{
    return Object::p_dump_memory;
}

/**
 * @brief Dump the memory layout to the filesystem
 * 
 * @param val Enable/Disable
 */
void Object::set_dump_memory(bool const val)
{
    Object::p_dump_memory = val;
}

/**
 * @brief Get the status of SMT dumping to the filesystem
 * 
 * @return bool
 */
bool Object::get_dump_smt()
{
    return Object::p_dump_smt;
}

/**
 * @brief Enable SMT dump to the filesystem
 * 
 * @param val Enable/Disable
 */
void Object::set_dump_smt(bool const val)
{
    Object::p_dump_smt = val;
}

/**
 * @brief Get the currently configured execution timeout
 * 
 * @return size_t
 */
size_t Object::get_timeout()
{
    return Object::p_timeout;
}

/**
 * @brief Set the timeout used for the backend execution
 * 
 * @param to New timeout.
 */
void Object::set_timeout(size_t const to)
{
    Object::p_timeout = to;
}

/**
 * @brief Get the configured logfile name
 * 
 * @return std::string
 */
std::string Object::get_logfile_name()
{
    return Object::p_logfile_name;
}

/**
 * @brief Set the name of the logfile
 * 
 * @param name Name of the logfile
 */
void Object::set_logfile_name(std::string const & name)
{
    Object::p_logfile_name = name;
}

/**
 * @brief Return Seed Function to Isolate
 * 
 * @return std::string
 */
std::string Object::get_isolate_function()
{
    return Object::p_seed_function;
}

/**
 * @brief Shows if a Seed Function has been set
 * 
 * @return bool
 */
bool Object::has_seed_function()
{
    return !Object::p_seed_function.empty();
}

/**
 * @brief Set Function to be Isolated 
 * 
 * @param function Seedfunction
 * @return std::string
 */
void Object::set_isolate_function(std::string const & function)
{
    Object::p_seed_function = function;
}
