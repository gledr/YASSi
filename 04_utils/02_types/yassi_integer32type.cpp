/** 
 * @file yassi_integer32type.cpp
 * @brief Intger32Type used for Yassi
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
#include "yassi_integer32type.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
Integer32Type::Integer32Type():
    BaseType()
{
    this->p_type_name  = INTEGER32TYPE;
    this->p_type_class = INTEGERTYPECLASS;
    this->p_bit_width  = 32;
    this->p_id         = IntegerTyID;
}

Integer32Type::~Integer32Type()
{
}

/**
 * @brief Get Maximum Value the type can hold
 * 
 * @return std::string
 */
std::string Integer32Type::get_max_value()
{
   return std::to_string(std::numeric_limits<int>::max());
}

/**
 * @brief Get Minimum Value the type can hold
 * 
 * @return std::string
 */
std::string Integer32Type::get_min_value()
{
    return std::to_string(std::numeric_limits<int>::min());
}
