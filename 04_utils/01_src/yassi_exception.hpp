/** 
 * @file yassi_exception.hpp
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
#ifndef YASSI_EXCEPTIONS_HPP
#define YASSI_EXCEPTIONS_HPP

#include <exception>
#include <iostream>
#include <execinfo.h>
#include <sstream>

namespace Yassi::Utils {

/**
 * @class RunTimeCheck
 * @brief Type Safe Functions to be called by Macros
 */
class RunTimeCheck {
public:
    static void __nullpointer_check__(std::string const & file, size_t const line);
    static void __assertion_check__(std::string const & file, size_t const line);
    static void __notimplemented_check__(std::string const & file, size_t const line);
    static void __notsupported_check__(std::string const & msg, std::string const & file, size_t const line);
};

}

#define nullpointer_check(expr)                                                         \
    if(!expr)                                                                           \
	{                                                                                   \
        using Yassi::Utils::RunTimeCheck;                                              \
		RunTimeCheck::__nullpointer_check__(__FILE__, __LINE__);                        \
	}

#define assertion_check(expr)                                                           \
    if(!static_cast<bool>(expr))                                                        \
    {                                                                                   \
        Yassi::Utils::RunTimeCheck::__assertion_check__(__FILE__, __LINE__);           \
    }

#define notimplemented_check()                                                          \
    Yassi::Utils::RunTimeCheck::__notimplemented_check__(__FILE__, __LINE__);

#define notsupported_check(expr)                                                        \
    Yassi::Utils::RunTimeCheck::__notsupported_check__(expr, __FILE__, __LINE__);

namespace Yassi::Utils {

/**
 * @class YassiNotImplemented
 * @brief Not Implemented Exception Type
 */ 
class YassiNotImplemented: public std::logic_error {
public:
    /**
     * @brief Constructor
     * 
     * @param what Error Message
     */
    YassiNotImplemented(std::string const & what):
        std::logic_error(what) 
    {

    }
};

/**
 * @class YassiNotSupported
 * @brief Not Supported Exception Type
 */ 
class YassiNotSupported: public std::logic_error {
public:
    /**
     * @brief Constructor 
     * 
     * @param what Error Message
     */
    YassiNotSupported(std::string const & what):
        std::logic_error ("YassiNotSupported: " + what) 
        {

        }
};

/**
 * @class YassiException
 * @brief Yassi Basic Exception Type
 */ 
class YassiException: public std::logic_error {
public:
    /**
     * @brief Constructor
     * 
     * @param what Error Message
     */
    YassiException (std::string const & what):
        std::logic_error("YassiException: " + what)
        {

        }

        /**
         * @brief Destructor
         */
        ~YassiException()
    {
        exit(-1);
    }
};

/**
 * @class YassiNullPointerException
 * @brief Yassi Null Pointer Exception Type
 */ 
class YassiNullPointerException: public std::exception {
public:
    /**
     * @brief Constructor 
     * 
     * @param what Error Message
     */
    YassiNullPointerException (std::string const & what):
        std::exception() 
    {
        std::cerr << std::endl;
        std::cerr << what << std::endl;
        exit(-1);
    }
};

}

#endif /* YASSI_EXCEPTIONS_HPP */
