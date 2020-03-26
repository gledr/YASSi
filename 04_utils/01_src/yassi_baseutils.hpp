/** 
 * @file yassi_baseutils.hpp
 * @brief Global Utility Class for Yassi
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
#ifndef YASSI_BASEUTILS_HPP
#define YASSI_BASEUTILS_HPP

#include <string>
#include <vector>
#include <fstream>

namespace Yassi::Utils {

/**
 * @class BaseUtils
 * @brief Shared Utilities for all Yassi Components
 */ 
class BaseUtils {
public:
    static std::vector<std::string> tokenize(std::string const & str, std::string const & delimiters);
    
    static void replace(std::string & str, std::string const & oldStr, std::string const & newStr);

    static std::string get_bash_string_blink_red(std::string const & str);

    static std::string get_bash_string_cyan(std::string const & str);

    static std::string get_bash_string_orange(std::string const & str);

    static std::string get_bash_string_purple(const std::string& str);

    static std::string get_bash_string_red(std::string const & str);

    static std::string get_bash_string_green(std::string const & str);

    static std::string get_bash_string_blue(std::string const & str);

    static std::string get_bash_string_blink_purple(std::string const & str);

    static std::string get_tmp_folder();

    static std::string get_base_path();

    static bool is_uninitialized_value(std::string const & value);

    static std::string decode_constant(std::string const & constant);

    static std::vector<std::string> decode_constants(std::string const & constants);

    static bool is_constant(std::string const & varname);

    static bool is_constant(std::vector<std::string> const & var);
};

}

#endif /* YASSI_BASEUTILS_HPP */
