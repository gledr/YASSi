/** 
 * @file yassi_floattype.hpp
 * @brief FloatType used for Yassi
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
#include "yassi_floattype.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
FloatType::FloatType():
    BaseType()
{
    this->p_type_name  = FLOATTYPE;
    this->p_type_class = REALTYPECLASS;
    this->p_bit_width  = 32;
    this->p_exponent   = 8;
    this->p_fraction   = 24;
    this->p_id         = FloatTyID ;
}

/**
 * @brief Destructor
 */
FloatType::~FloatType()
{
}

/**
 * @brief Get Number of bits used for exponent
 *
 * @return size_t
 */
size_t FloatType::get_exponent()
{
    return p_exponent;
}

/**
 * @brief Get Number of bits used for fraction
 *
 * @return size_t
 */
size_t FloatType::get_fraction()
{
    return p_fraction;
}

/**
 * @brief Get Maximum Value the type can hold
 * 
 * @return std::string
 */
std::string FloatType::get_max_value()
{
    return std::to_string(std::numeric_limits<float>::min());
}

/**
 * @brief Get Minimum Value the type can hold
 * 
 * @return std::string
 */
std::string FloatType::get_min_value()
{
    return std::to_string(std::numeric_limits<float>::max());
}
