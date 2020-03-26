#ifndef YASSI_UITLS_HPP
#define YASSI_UITLS_HPP

#include <yassi_baseutils.hpp>
#include <yassi_exception.hpp>

#include <string>
#include <vector>

namespace Yassi::Frontend {

class Utils {
public:

    static bool is_bc(std::string const & file);

    static bool is_source(std::string const & file);

    static bool is_header(std::string const & file);

    static bool is_dot(std::string const & file);

    static bool is_png(std::string const & file);

    static std::string get_filetype(std::string const & file);

    static std::string get_filename(std::string const & file);
};

}

#endif /* YASSI_UITLS_HPP */
