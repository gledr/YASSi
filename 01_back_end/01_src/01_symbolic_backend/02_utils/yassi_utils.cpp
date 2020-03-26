/** 
 * @file yassi_utils.cpp
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
#include "yassi_utils.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Utils;


/**
 * @brief Check if name is register name
 * 
 * @param name: The name to check
 * @return bool
 */
bool Utils::is_register(std::string const & name)
{
    std::vector<std::string> token =
        BaseUtils::tokenize(name, NameMangling::MANGELING_SEPERATOR);
    
    if(token.size() != 4){
        return false;
    } else {
        return token[token.size()-2] == "register";
    }
}

/**
 * @brief Check if name is global variable
 * 
 * @param name: The name to check
 * @return bool
 */
bool Utils::is_global(std::string const & name)
{
    std::vector<std::string> token =
        BaseUtils::tokenize(name, NameMangling::MANGELING_SEPERATOR);
    return token[token.size()-2] == "global";
}

/**
 * @brief Check if name is function pointer
 *
 * @param fp: The name to check
 * @return bool
 */
bool Utils::is_function_pointer(std::string const& fp) 
{
    std::vector<std::string> token = 
        BaseUtils::tokenize(fp, NameMangling::MANGELING_SEPERATOR);
    if (token.size() != 4) {
        return false;
    } 
    return Utils::is_function(token[token.size()-2]); 
}

/**
 * @brief Check if name is function
 * 
 * @param name: The name to check
 * @return bool
 */
bool Utils::is_function(std::string const & name)
{
    return name.compare("function") == 0;
}

/**
 * @brief Decode function pointer string
 * 
 * @param fn_ptr: The incoming name to decode
 * @return std::string
 */
std::string Utils::decode_function_pointer(std::string const & fn_ptr)
{
    assertion_check(Utils::is_function_pointer(fn_ptr));
    return BaseUtils::tokenize(fn_ptr, NameMangling::MANGELING_SEPERATOR)[3];
}
