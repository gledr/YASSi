/** 
 * @file yassi_baselogger.hpp
 * @brief BaseLogger Class  for Yassi
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
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include "yassi_baseutils.hpp"

using namespace Yassi::Utils;


/**
 * @brief Split a string into token separated by a given delimiter
 * 
 * @param str: The string to tokenize
 * @param delimiters: The delimiter to split the string
 * @return std::vector< std::string >
 */
std::vector<std::string> BaseUtils::tokenize(std::string const & str, std::string const & delimiters) 
{
    std::vector<std::string> tokens;
    // skip delimiters at beginning.
    std::string::size_type lastPos = str.find_first_not_of(delimiters, 0);

    // find first "non-delimiter".
    std::string::size_type pos = str.find_first_of(delimiters, lastPos);

    while (std::string::npos != pos || std::string::npos != lastPos) {
        // found a token, add it to the vector.
        tokens.push_back(str.substr(lastPos, pos - lastPos));
        
        // skip delimiters.  Note the "not_of"
        lastPos = str.find_first_not_of(delimiters, pos);
        
        // find next "non-delimiter"
        pos = str.find_first_of(delimiters, lastPos);
    }

    return tokens;
}

/**
 * @brief Replace a Part of a String
 * 
 * @param str       String to replace
 * @param oldStr    Original String
 * @param newStr    Modified String
 */
void BaseUtils::replace(std::string & str, std::string const & oldStr, std::string const & newStr) 
{
    size_t pos = 0;
    while((pos = str.find(oldStr, pos)) != std::string::npos){
        str.replace(pos, oldStr.length(), newStr);
        pos += newStr.length();
    }
}

/**
 * @brief Return a string which will blink red in the bash shell
 * 
 * @param str: The string to blink red in the terminal
 */ 
std::string BaseUtils::get_bash_string_blink_red(const std::string& str) 
{
    return "\033[31;5m" + str + "\033[m";
}

/**
 * @brief Return a string which will appear cyan in the bash shell
 * 
 * @param str: The string to be cyan in the terminal
 */ 
std::string BaseUtils::get_bash_string_cyan(const std::string& str)
{
    return "\033[36m" + str + "\033[0m";
}

/**
 * @brief Return a string which will blink purple in the bash shell
 * 
 * @param str: The string to blink red in the terminal
 */ 
std::string BaseUtils::get_bash_string_purple(const std::string& str) 
{
    return "\033[35m" + str + "\033[m";
}

/**
 * @brief Resolve the URL of the temporary folder used by Yassi
 * 
 * @return std::string
 */
std::string BaseUtils::get_tmp_folder() 
{
    std::string base_path = BaseUtils::get_base_path();
    std::string file_content;
    std::string config_file = base_path + "/07_configuration/yassi_settings.ini";
    std::vector<std::string> settings;
    std::fstream settings_file(config_file, std::ios::in);

    while(std::getline(settings_file, file_content)){
        settings.push_back(file_content);
    }
    settings_file.close();

    std::string retVal = "";

    for(auto itor : settings){
        if(BaseUtils::tokenize(itor, "=")[0].compare("tmp_folder") == 0){
            retVal = BaseUtils::tokenize(itor, "=")[1];
            break;
        }
    }
    return retVal;
}

/**
 * @brief Resolve Yassi's BasePath (Installation Root)
 * 
 * @return std::string
 */
std::string BaseUtils::get_base_path()
{   
    std::string file_content;
    std::string home_folder = getenv("HOME");
    std::string path = home_folder + "/.yassi/config.txt";
    std::fstream in_file(path, std::ios::in);
    std::getline(in_file, file_content);
    in_file.close();
    
    return BaseUtils::tokenize(file_content, "=")[1];
}

/**
 * @brief Return a string which will appear orange in the bash shell
 * 
 * @param str: The string to be orange in the terminal
 */ 
std::string BaseUtils::get_bash_string_orange(const std::string& str)
{
    return "\033[33m" + str + "\033[0m";
}

/**
 * @brief Return a string which will appear red in the bash shell
 * 
 * @param str: The string to be red in the terminal
 */ 
std::string BaseUtils::get_bash_string_red(const std::string& str)
{
    return "\033[31m" + str + "\033[0m";
}

/**
 * @brief Return a string which will blink purple in the bash shell
 * 
 * @param str: The string to blink red in the terminal
 */ 
std::string BaseUtils::get_bash_string_blink_purple(const std::string& str) 
{
     return "\033[35;5m" + str + "\033[m";
}

/**
 * @brief Return a string which will appear green in the bash shell
 * 
 * @param str: The string to be green in the terminal
 */ 
std::string BaseUtils::get_bash_string_green(const std::string& str)
{
    return "\033[32m" + str + "\033[0m";
}

/**
 * @brief Return a string which will appear blue in the bash shell
 * 
 * @param str: The string to be blue in the terminal
 */ 
std::string BaseUtils::get_bash_string_blue(const std::string& str)
{
    return "\033[34m" + str + "\033[0m";
}

/**
 * @brief Check if Value is Uninilized
 * 
 * @param value Value to Check
 * @return bool
 */
bool BaseUtils::is_uninitialized_value(std::string const & value)
{
    return value == "X";
}

/**
 * @brief Decode Value from Constant Description String
 * 
 * @param constant Constant Description String
 * @return std::string
 */
std::string BaseUtils::decode_constant(std::string const & constant)
{
    if(BaseUtils::is_constant(constant)){
        return BaseUtils::tokenize(constant, "%")[2];
    } else if (BaseUtils::is_uninitialized_value(constant)){
        return constant;
    } else {
        return "";
    }
}

/**
 * @brief Check if all values are constants
 * 
 * @param constants Constants separated by collon
 * @return std::vector< std::string >
 */
std::vector<std::string> BaseUtils::decode_constants(std::string const & constants) 
{
    std::vector<std::string> retVal;
    std::vector<std::string> token = BaseUtils::tokenize(constants, ",");
    
    for(auto& itor: token){
        retVal.push_back(BaseUtils::decode_constant(itor));
    }
    return retVal;
}

/**
 * @brief Check if variable is constant
 * 
 * @param varname Variable to be checked
 * @return bool
 */
bool BaseUtils::is_constant(std::string const & varname)
{
    std::vector<std::string> token = BaseUtils::tokenize(varname, "%");
    return token.front() == "constant" && token.size() == 3;
}

/**
 * @brief Check if all variables are constants
 * 
 * @param var Variables to be checked
 * @return bool
 */
bool BaseUtils::is_constant(std::vector<std::string> const & var)
{
    bool flag = true;
    for(auto itor : var){
        flag = flag & BaseUtils::is_constant(itor);
    }
    return flag;
}
