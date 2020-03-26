/** 
 * @file yassi_object.cpp
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
#include "yassi_object.hpp"

using namespace Yassi::Backend::Replay;
using namespace Yassi::Utils;


bool Object::p_debug = false;
bool Object::p_log_file_enabled = false;
std::string Object::p_execution_url = "";
std::string Object::p_backend_bin = "";

Object::Object() 
{
    std::string tmp_path = BaseUtils::get_tmp_folder();
    p_database = new Database(tmp_path + "/db/database.db");
}

Object::~Object() 
{
    delete p_database; p_database = nullptr;
}

/**
 * @brief Get verbose mode
 * 
 * @return bool
 */
bool Object::get_debug()
{
    return Object::p_debug;
}

/**
 * @brief Set verbose mode
 * 
 * @param val p_val: The mode as bool flag
 */
void Object::set_debug(bool const val)
{
    Object::p_debug = val;
}

bool Object::get_log_file_enabled()
{
    return Object::p_log_file_enabled;
}

void Object::set_log_file_enabled(const bool val)
{
    Object::p_log_file_enabled = val;
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
 * @param url p_url:...
 */
void Object::set_execution_url(std::string const & url)
{
    Object::p_execution_url = url;
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
 * @param name p_name: The nmae as std::string
 */
void Object::set_bin_name(std::string const & name)
{
    Object::p_backend_bin = name;
}
