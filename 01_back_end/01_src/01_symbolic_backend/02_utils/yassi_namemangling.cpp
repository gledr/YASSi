/** 
 * @file yassi_namemangling.cpp
 * @brief Name Mangling for Yassi Variables
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
 */
#include "yassi_namemangling.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Utils;

std::string NameMangling::MANGELING_SEPERATOR = "%";
std::string NameMangling::VARIABLE_SEPERATOR = ",";


/**
 * @brief In order to make every variable name unique we are
 *        going to mangle the name by adding the source file
 *        and function name to the variable name
 * 
 * @param name: The variable name to mangle
 * @return The mangled name
 */
std::string NameMangling::mangle_name(std::string const & name,
                                      std::string const & function,
                                      std::string const & file) 
{
    std::vector<std::string> token =
        BaseUtils::tokenize(name, NameMangling::VARIABLE_SEPERATOR);
    std::stringstream retval;

    for(auto& itor : token){
        std::vector<std::string> type_token =
            BaseUtils::tokenize(itor, NameMangling::MANGELING_SEPERATOR);

        if(retval.str() != ""){
            retval << NameMangling::VARIABLE_SEPERATOR;
        }

        // constant%type%value
        if(type_token.size() == 3){
            retval << itor;
        }
        // register%name global%name function%name
        else if (type_token.size() == 2){
            
            if(type_token[0] == "register" || type_token[0] == "function"){
                retval << file;
                retval << NameMangling::MANGELING_SEPERATOR;
                retval << function;
                retval << NameMangling::MANGELING_SEPERATOR;
                retval << itor; 
            } else if (type_token[0] == "global"){
                retval << file;
                retval << NameMangling::MANGELING_SEPERATOR;
                retval << itor;
            } else {
                throw YassiException("Invalid Format!");
            }
        } else {
            std::stringstream msg;
            std::cout << itor << std::endl;
            msg << "Unknown Format for NameMangling: " << itor;
            throw YassiException(msg.str());
        }
    }
    return retval.str();
}

/**
  * @brief In order to get the original variable name back
  *        you may use this function
  * 
  * @return The demangled name
  */ 
std::string NameMangling::demangle_name(std::string const & name)
{
    std::vector<std::string> token
        = BaseUtils::tokenize(name, NameMangling::MANGELING_SEPERATOR);
    return token[token.size()-2] +
        NameMangling::MANGELING_SEPERATOR +
        token[token.size()-1];
}

/**
 * @brief Check if the name is in the correct mangled form
 *
 * @param name p_name: The name to check
 * @return bool True if name is okay, False else
 */
void NameMangling::__check_name_mangling(std::string const & name,
                                         int const line,
                                         std::string const & file)
{
    std::vector<std::string> variables = 
        BaseUtils::tokenize(name, NameMangling::VARIABLE_SEPERATOR);

    for(auto& itor: variables){
        std::vector<std::string> token = 
            BaseUtils::tokenize(itor, NameMangling::MANGELING_SEPERATOR);
        bool okay = true;
        if(token.size() == 3){
            if(BaseUtils::is_constant(itor)){
            // constant%type%value
            } else if (Utils::is_global(itor)){
                // file%global%name
            } else {
                okay = false;
            }

        } else if (token.size() == 4){
            if(Utils::is_register(itor)){
                // file%function%register%name
            } else if (Utils::is_function_pointer(itor)){
            // file%function%function%name
            } else {
                okay = false;
            }
        } else {
        okay = false;
        }

        if(!okay){
            std::stringstream msg;
            msg << "Bad Name Mangling: " 
                << itor 
                << " Line: " 
                << line 
                << " File: " 
                << file;
            throw YassiException(msg.str());
        }
    }
}

/**
 * @brief Check if the name is in the correct mangled form
 * 
 * @param name p_name: The name to check
 * @return bool True if name is okay, False else
 */
void NameMangling::__check_name_mangling(std::vector<std::string> const & name,
                                        int const line,
                                        std::string const & file)
{
    for(auto& itor: name){
        NameMangling::__check_name_mangling(itor, line, file);
    }
}
