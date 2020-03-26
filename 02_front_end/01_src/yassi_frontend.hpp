/** 
 * @file yassi_frontend.hpp
 * @brief Yassi Frontend is generating the Backend Binary and Execution
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
#ifndef YASSI_FRONTEND_HPP
#define YASSI_FRONTEND_HPP

#include <sstream>
#include <fstream>
#include <vector>
#include <string>

#include <boost/program_options.hpp>
#include <boost/filesystem.hpp>

#include <yassi_object.hpp>
#include <yassi_executor.hpp>
#include <yassi_version.hpp>
#include <yassi_logger.hpp>

namespace Yassi::Frontend {

class Frontend: public virtual Object{

public:

    Frontend();

    virtual ~Frontend();

    void init_frontend(int argc, char ** argv);

    void run_frontend();

private:
    Executor* p_exec;
    boost::program_options::options_description* p_options_functions;
    boost::program_options::variables_map p_vm;

    std::string p_frontend_name;
    std::string p_version_info;

    void program_options(int const argc, char ** argv);
    void bash_completion_script();
};

}

#endif /* YASSI_FRONTEND_HPP */
