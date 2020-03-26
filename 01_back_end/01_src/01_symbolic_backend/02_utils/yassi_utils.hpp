/** 
 * @file yassi_utils.hpp
 * @brief Utilities for the Yassi Execution Backend
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
 */
#ifndef YASSI_UTILS_HPP
#define YASSI_UTILS_HPP

#include <string>
#include <vector>
#include <fstream>
#include <execinfo.h>
#include <iostream>

#include <yassi_baseutils.hpp>
#include <yassi_namemangling.hpp>

namespace Yassi::Backend::Execute {

enum eException {e_assertion_fail,  ///< Assertion Failed
                 e_assertion_pass,  ///< Assertion Passed
                 e_out_of_bounds,   ///< Array Out of Indexes
                 e_divide_by_zero,  ///< Division by Zero
                 e_rem_zero,        ///< Modulo by Zero
                 e_deref_range,     ///< Deference Range to big
                 e_memory_leak,     ///< Memory Leak found
                 e_double_free      ///< Memory Freed Second Time
};


class Utils {
public:
    Utils ();

    virtual ~Utils();

    static bool is_register(std::string const & name);

    static bool is_global(std::string const & name);

    static bool is_function_pointer (std::string const & fp);

    static bool is_function(std::string const & name);

    static std::string decode_function_pointer(std::string const & fn_ptr);

    static void print_stack_trace(std::ostream& stream=std::cout);
};

}

#endif // YASSI_UTILS_HPP
