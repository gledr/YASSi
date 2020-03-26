#include "yassi_utils.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief Check if a file is a LLVM Bitcode
 * 
 * @param file: The source file to check
 * @return bool
 */
bool Utils::is_bc(std::string const & file)
{
    return get_filetype(file) == ".bc" || get_filetype(file) == ".ll";
}

/**
 * @brief Check if file is source file
 * 
 * @param file: The file to check
 * @return bool
 */
bool Utils::is_source(std::string const & file)
{
    return get_filetype(file) == ".c" || get_filetype(file) == ".cpp";
}

/**
 * @brief Check if file is header file
 * 
 * @param file: The file to check
 * @return bool
 */
bool Utils::is_header(std::string const & file)
{
    return get_filetype(file) == ".h" || get_filetype(file) == ".hpp";
}

/**
 * @brief Extract the type ending from a filename
 * 
 * @param file: The filename
 * @return std::string
 */
std::string Utils::get_filetype(std::string const & file)
{
    if(file.find(".") != std::string::npos){
        int comma = -1;
        for(int i = file.length(); i >= 0; i--){
            if (file[i] == '.'){
                comma = i;
                break;
            }
        }
        return file.substr(comma, file.length()-comma);
    } else {
        return "directory";
    }
}

/**
 * @brief Check if file is in dot format
 * 
 * @param file: The file to check
 * @return bool
 */
bool Utils::is_dot(std::string const & file)
{
    return get_filetype(file) == ".dot";
}

/**
 * @brief Check if file is in png format
 * 
 * @param file: The file to check
 * @return bool
 */
bool Utils::is_png(std::string const & file)
{
    return get_filetype(file) == ".png";
}

/**
 * @brief Extract the name of a file 
 * 
 * @param file: The filename including type ending
 * @return std::string
 */
std::string Utils::get_filename(std::string const & file)
{
    std::vector<std::string> token = BaseUtils::tokenize(file, ".");
    
    if(token.size() != 2){
        throw YassiException("Invalid Number of dot Seperators found!");
    }

    return token[0];
}
