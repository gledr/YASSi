/** 
 * @file yassi_integer16type.hpp
 * @brief Intger16Type used for Yassi
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
#ifndef YASSI_INTEGER16TYPE_HPP
#define YASSI_INTEGER16TYPE_HPP

#include "yassi_basetype.hpp"

namespace Yassi::Types {

/**
 * @class Integer16Type
 * @brief Type for 16 Bit Integer used in Yassi
 * 
 * Integer16Type is used in the Yassi Backend as well
 * as in the LLVM Optimization passes
 */
class Integer16Type: public BaseType {
public:
    Integer16Type();

    virtual ~Integer16Type();

    virtual std::string get_max_value();

    virtual std::string get_min_value();
};

}

#endif /* YASSI_INTEGER16TYPE_HPP */
