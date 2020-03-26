/** 
 * @file yassi_object.hpp
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
#ifndef YASSI_OBJECT_HPP
#define YASSI_OBJECT_HPP

#include <vector>
#include <memory>
#include <string>
#include <stack>

#include <signal.h>

#include <boost/algorithm/string.hpp>

#include <yassi_namemangling.hpp>
#include <yassi_pathstack.hpp>

namespace Yassi::Backend::Execute {
    
class Object {
public:

    virtual ~Object();

    static PathStack p_path_stack;

    static std::vector<std::string> p_function_call_arguments;
    static std::stack<std::string> p_function_return_register;  // The register beeing returned from the called function
    static std::stack<std::string> p_caller_function_register;  // The register to assign the returned register from the function

protected:
  
    Object();

    static std::string get_current_function();
    static void set_current_function(std::string const & function);

    static std::vector<std::string> get_path_history();
    static std::string get_path_history_debug();
    static void add_path_element(std::string const & element);

    static void set_line_num_in_execution(size_t const line_num);
    static size_t get_line_num_execution();

    static void set_file_being_executed(std::string const & file);
    static std::string get_file_being_executed();

    static std::string mangle_name(std::string const & name);

    static std::string get_bin_dir();
    static void set_bin_dir(std::string const & url);

    static std::string get_bin_name();
    static void set_bin_name(std::string const & name);

    static void set_max_depth(size_t const  depth);
    static size_t get_max_depth();

    static std::string get_smt_dir();
    static void set_smt_dir(std::string const & url);

    static bool get_debug();
    static void set_debug(bool const val);

    static bool get_quiet();
    static void set_quiet(bool const val);

    static std::string get_execution_url();
    static void set_execution_url(std::string const & url);

    static bool get_log_file_enabled();
    static void set_log_file_enabled(bool const val);

    static bool get_error_localization();
    static void set_error_localization(bool const val);

    static bool get_dump_memory();
    static void set_dump_memory(bool const val);

    static bool get_dump_smt();
    static void set_dump_smt(bool const val);

    std::string const TAKEN = "1";
    std::string const NOT_TAKEN = "0";

    static void set_timeout(size_t const to);
    static size_t get_timeout();

    static std::string get_logfile_name();
    static void set_logfile_name(std::string const & name);

    static std::string get_database_url();
    void set_database_url(std::string const & url);

private:
    Object(const Object& other);
    Object& operator=(const Object& other);
    bool operator==(const Object& other) const;
    bool operator!=(const Object& other) const;

    static std::string p_bin_dir;
    static std::string p_backend_bin;
    static std::string p_execution_url;
    static std::string p_logfile_name;
    static size_t p_max_depth;
    static size_t p_timeout;
    static std::string p_smt_dir;
    static bool p_debug;
    static bool p_quiet;
    static bool p_log_file_enabled;
    static bool p_error_localization;
    static bool p_dump_memory;
    static bool p_dump_smt;
    static std::string p_database_url;

    static std::string p_current_function;

    //functions and basic blocks executed to get there
    static std::vector<std::string> p_current_path_history; 

    static size_t p_line_num_is_executed;
    static std::string p_file_being_exected;
};

}

#endif /* YASSI_OBJECT_HPP */
