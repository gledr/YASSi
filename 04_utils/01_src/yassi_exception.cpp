/** 
 * @file yassi_exception.cpp
 * @brief Exception Types for Yassi
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
 * @author Pablo Gonzales de Aledo
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
#include "yassi_exception.hpp"

using namespace Yassi::Utils;


/**
 * @brief Type Safe Function called by Macro to check Assertion
 * 
 * @param file File where Assertion Failed
 * @param line Line Number where Assertion Failed
 */
void RunTimeCheck::__assertion_check__(std::string const & file, size_t const line)
{
    throw YassiException("Assertion Violated (" + file + ":" + std::to_string(line) + ")");
}

/**
 * @brief Type Safe Function Called by Macro to check Null Pointer
 * 
 * @param file File where Null Pointer Occured
 * @param line Line where Null Pointer was found
 */
void RunTimeCheck::__nullpointer_check__(std::string const & file, size_t const line)
{
    throw YassiNullPointerException("Yassi NullPointerException! " + file + ":" + std::to_string(line));
}

/**
 * @brief Type Safe Function Called by Macro to Report Not Implemented Functions
 * 
 * @param file File where not implemented feature was found
 * @param line Line Number where not implemented feature was found
 */
void RunTimeCheck::__notimplemented_check__(std::string const & file, size_t const line)
{
    throw YassiNotImplemented("Feature Not Implemented! " + file + ":" + std::to_string(line));
}

/**
 * @brief Type Safe Function called by Macro to Report Not Supported Functionality
 * 
 * @param msg Error Message
 * @param file File where Macro was called
 * @param line Line where Macro was called
 */
void RunTimeCheck::__notsupported_check__(std::string const & msg, std::string const & file, size_t const line)
{
    std::stringstream msg_str;
    msg_str << msg << "(" << file << ":" << line << ")";
    throw YassiNotSupported(msg_str.str());
}
