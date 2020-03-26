/** 
 * @file yassi_doubletype.cpp
 * @brief DoubleType used for Yassi
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
#include "yassi_doubletype.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
DoubleType::DoubleType():
    BaseType()
{
    this->p_type_name  = DOUBLETYPE;
    this->p_type_class = REALTYPECLASS;
    this->p_bit_width  = 64;
    this->p_exponent   = 11;
    this->p_fraction   = 53;
    this->p_id         = DoubleTyID;
}

/**
 * @brief Destructor
 */
DoubleType::~DoubleType()
{
}

/**
 * @brief Get Number of bits used for exponent
 *
 * @return size_t
 */
size_t DoubleType::get_exponent()
{
    return this->p_exponent;
}

/**
 * @brief Get Number of bits used for fraction
 *
 * @return size_t
 */
size_t DoubleType::get_fraction()
{
    return this->p_fraction;
}

/**
 * @brief Get Minimum Value the type can hold
 *
 * @return std::string
 */
std::string DoubleType::get_min_value()
{
    return std::to_string(std::numeric_limits<double>::min());
}

/**
 * @brief Get Maximum Value the type can hold
 *
 * @return std::string
 */
std::string DoubleType::get_max_value()
{
    return std::to_string(std::numeric_limits<double>::max());
}
