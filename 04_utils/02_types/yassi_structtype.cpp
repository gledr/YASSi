/** 
 * @file yassi_structtype.cpp
 * @brief StructType used for Yassi
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
 * 51 
 */
#include "yassi_structtype.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
StructType::StructType():
    BaseType()
{
    this->p_type_name  = STRUCTTYPE;
    this->p_type_class = STRUCTTYPECLASS;
    this->p_bit_width  = 0;
    this->p_id         = StructTyID;
}

StructType::~StructType()
{
}

/**
 * @brief Get Maximum Value the type can hold
 * 
 * @return std::string
 */
std::string StructType::get_max_value()
{
    notsupported_check("Not supported for StructType");
    exit(-1);
}

/**
 * @brief Get Minimum Value the type can hold
 * 
 * @return std::string
 */
std::string StructType::get_min_value()
{
    notsupported_check("Not supported for StructType");
    exit(-1);
}
