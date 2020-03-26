/** 
 * @file yassi_object.hpp
 * @brief Virtual Baseclass for the Replay Backend
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
#ifndef YASSI_REPLAY_OBJECT_HPP
#define YASSI_REPLAY_OBJECT_HPP

#include <boost/algorithm/string.hpp>

#include <yassi_database.hpp>

namespace Yassi::Backend::Replay {

class Database;

class Object {
public:

    virtual ~Object();

protected:
  
    Object();

    static bool get_log_file_enabled();
    static void set_log_file_enabled(bool const val);
    
    static bool get_debug();
    static void set_debug(bool const val);

    static std::string get_execution_url();
    static void set_execution_url(std::string const & url);

    static std::string get_bin_name();
    static void set_bin_name(std::string const & name);

    Database* p_database;

private:
    static bool p_debug;
    static bool p_log_file_enabled;
    static std::string p_execution_url;
    static std::string p_backend_bin;
};

}

#endif /* YASSI_REPLAY_OBJECT_HPP */
