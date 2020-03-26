/** 
 * @file yassi_common.hpp
 * @brief Yassi Common acts as collection of supporting Tools
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
#ifndef YASSI_COMMON_HPP
#define YASSI_COMMON_HPP

#include <cstdlib>

#include <boost/filesystem.hpp>
#include <boost/process.hpp>

#include <yassi_object.hpp>
#include <yassi_logger.hpp>

namespace Yassi::Frontend {

/**
 * @class Common
 * @brief Common Utils for the Execution 
 */
class Common: public virtual Object {
public:
    Common();

    virtual ~Common();

    void clean_environment();

    void show_db();

    void check_external_tools();

    int system_execute(std::string const & bin, std::vector<std::string> & args, std::string const & output, int & pid, bool wait_for_termination);

    int system_execute(std::string const & bin, std::vector<std::string> & args, std::string const & output, bool wait_for_termination);

private:
    Logger* p_logger;
};

}

#endif /* YASSI_COMMON_HPP */
