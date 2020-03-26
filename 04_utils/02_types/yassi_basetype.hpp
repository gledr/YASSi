/** 
 * @file yassi_basetype.hpp
 * @brief BaseType used for Yassi
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
#ifndef YASSI_BASETYPE_HPP
#define YASSI_BASETYPE_HPP

#include <string>
#include <iostream>
#include <limits>
#include <sstream>
#include <iostream>

#include "yassi_typedefinitions.hpp"

#ifdef YASSI
    #include <yassi_exception.hpp>
#else
    #include <cassert>
    #define nullpointer_check(expr) assert (expr != nullptr);
    #define notimplemented_check() assert (0);
    #define notsupported_check(expr) assert (0 && expr);
#endif

namespace Yassi::Types {

/**
 * @class BaseType
 * @brief Virtual Base Class for all Types
 * 
 * Virtual Base Type which can not be instantiated directy.
 */
class BaseType {
public:
    void dump(std::ostream & stream = std::cout);

    size_t get_bytes();

    size_t get_bits();

    std::string get_type_identifier();

    std::string get_type_class();

    bool operator== (BaseType* type);

    bool operator!= (BaseType* type);

    bool is_int1();

    bool is_int8();

    bool is_int16();

    bool is_int32();

    bool is_int64();

    bool is_float();

    bool is_double();

    bool is_pointer();

    bool is_struct();

    bool is_array();

    bool is_void();

    bool is_function();

    static bool is_int(std::string const & identifier);

    bool is_integer_class();

    static bool is_real(std::string const & identifier);

    bool is_real_class();

    bool is_bool_class();

    virtual std::string get_max_value() = 0;

    virtual std::string get_min_value() = 0;

protected:
    BaseType();

    virtual ~BaseType();

    std::string p_type_name;
    std::string p_type_class;
    TypeID p_id;
    size_t p_bit_width;
};

}

#endif /* YASSI_BASETYPE_HPP */
