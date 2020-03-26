/** 
 * @file yassi_pathstack.cpp
 * @brief Path Stack for Execution History
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
#include "yassi_pathstack.hpp"

using namespace Yassi::Backend::Execute;


/**
 * @brief Constructor
 */
PathStack::PathStack()
{
}

/**
 * @brief Destructor
 */
PathStack::~PathStack()
{
}

/**
 * @brief Pop Top Element from Stack
 * 
 * @return bool
 */
bool PathStack::pop()
{
    bool tmp = p_stack.back();
    p_stack.pop_back();
    return tmp;
}

/**
 * @brief Get Top Element from Stack
 * 
 * @return bool
 */
bool PathStack::top()
{
    return p_stack.back();
}

/**
 * @brief Push Element to Stack
 * 
 * @param val: New Element
 */
void PathStack::push(bool const& val)
{
    p_stack.push_back(val);
}

/**
 * @brief Get String Representation of Stack
 * 
 * @return std::string
 */
std::string PathStack::to_string()
{
    std::stringstream retval;

    for(auto itor: p_stack){
        if(itor){
            retval << "T";
        } else {
            retval << "F";
        }
    }

    return retval.str();
}
