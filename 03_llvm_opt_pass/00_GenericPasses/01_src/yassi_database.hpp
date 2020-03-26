/** 
 * @file yassi_database.hpp
 * @brief Database Connection for Optimization Passes
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2020 Johannes Kepler University
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
#ifndef YASSI_DATABASE_HPP
#define YASSI_DATABASE_HPP

#include <string>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include <iostream>
#include <cassert>

#include <sqlite3.h>

#ifndef YASSI_PASS
    #include "../../../04_utils/03_datastructures/yassi_genericdatastructures.hpp"
    #include "../../../04_utils/01_src/yassi_baseutils.hpp"
    #include "../../../04_utils/01_src/yassi_basedatabase.hpp"
#else 
    #include "yassi_genericdatastructures.hpp"
    #include "yassi_baseutils.hpp"
    #include "yassi_basedatabase.hpp"
#endif

namespace Yassi::OptPass {

/**
 * @class Database
 * @brief Database Connection for Optimization Passes
 */
class Database: public Utils::BaseDatabase {
public:
    Database();

    virtual ~Database();

    virtual int __callback__(int argc, char **argv, char **azColName);

    void insert_internal_function(std::string const & name);
    void insert_external_function(std::string const & name);

    void insert_basic_block(std::string const & file, std::string const & fn, std::string const & bb);

    std::map<std::string, std::string> get_options();
    std::vector<Yassi::Utils::VariableInfo> get_variables();
    std::vector<Yassi::Utils::VariableInfo> get_test_vector_variables();
    std::vector<Yassi::Utils::TestVector> get_test_vectors();
    std::vector<std::string> get_blacklisted_lines();
    std::string get_current_build_file();

private:
    /*     Make Canonic Class       */
    Database (Database const & db);
    Database operator= (Database const & db);
    bool operator== (Database const & db);
    
    std::ostream& db_logger();
    
    enum db_transaction {e_init,
                         e_get_variables,
                         e_get_test_vector_variables,
                         e_options,
                         e_test_vectors,
                         e_verbose,
                         e_blacklist,
                         e_build
    };
    
    db_transaction p_active_transaction;
    std::map<std::string, std::string> p_options;
    std::vector<Yassi::Utils::VariableInfo> p_variables;
    std::vector<Yassi::Utils::VariableInfo> p_test_vector_variables;
    std::vector<Yassi::Utils::TestVector> p_test_vectors;
    std::vector<std::string> p_blacklisted_lines;
    std::vector<std::string> p_build_files;
};

}

#endif /* YASSI_DATABASE_HPP */
