/** 
 * @file yassi_namemangling.hpp
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
#ifndef YASSI_NAMEMANGLING_HPP
#define YASSI_NAMEMANGLING_HPP

#include <string>
#include <sstream>
#include <vector>

#include <yassi_utils.hpp>
#include <yassi_exception.hpp>

namespace Yassi::Backend::Execute {

/**
 * @class NameMangling
 * @brief Name Mangling for Yassi Variables
 */
class NameMangling {
public:

    static std::string mangle_name(std::string const & name,
                                   std::string const & function,
                                   std::string const & file);

    static std::string demangle_name(std::string const & name);

    static void __check_name_mangling(std::string const & name,
                                      int const line,
                                      std::string const & file);

    static void __check_name_mangling(std::vector<std::string> const & name,
                                      int const line, std::string const & file);

    static std::string MANGELING_SEPERATOR;
    static std::string VARIABLE_SEPERATOR;
};

#define check_namemangling(expr)  NameMangling::__check_name_mangling(expr,  __LINE__, __FILE__);

}

#endif /* YASSI_NAMEMANGLING_HPP */
