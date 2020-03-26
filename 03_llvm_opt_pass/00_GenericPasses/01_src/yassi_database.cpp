/** 
 * @file yassi_database.cpp
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
#include "yassi_database.hpp"

using namespace Yassi::OptPass;
using namespace Yassi::Utils;

Database::Database(): 
    BaseDatabase("")
{
    p_db = nullptr;
    p_debug = false;
    
    p_db_url = BaseUtils::get_tmp_folder() + "/db/database.db";
    
    this->open_database();
}

Database::~Database()
{
    this->close_database();
}


/**
 * @brief Callback function used by the Sqlite3 API - has access to the this pointer
 * 
 * The azColName parameter is unused - since the interface is predefined we told GCC 
 * to ignore this.
 */ 
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int Database::__callback__(int argc, char **argv, char **azColName)
{
#pragma GCC diagnostic pop
    if (*argv == nullptr){
        // If the Table is empty we receive a nullptr
        return 0;
    } else {
        if (p_active_transaction == e_init){
            // Chill dude
        } else if (p_active_transaction == e_verbose){
            // Maybe print it to stdout
        } else if (p_active_transaction == e_get_variables){
            VariableInfo var;
            var.name = argv[0];
            var.position = argv[2];
            var.type = argv[1];
            var.free = std::stoi(argv[3]);
            p_variables.push_back(var);
         } else if (p_active_transaction == e_get_test_vector_variables){
            VariableInfo var;
            var.name = argv[0];
            var.position = argv[2];
            var.type = argv[1];
            var.free = std::stoi(argv[3]);
            p_test_vector_variables.push_back(var);
        } else if (p_active_transaction == e_options){
            assert(argc == 2);
            p_options[argv[0]] = argv[1];
        } else if (p_active_transaction == e_test_vectors){
            TestVector v;
            v.vector_id = argv[0];
            v.variable_name = argv[1];
            v.variable_hint = argv[2];
            v.value =argv[3];
            p_test_vectors.push_back(v);
            assert (argc == 4);
        } else if (p_active_transaction == e_blacklist){
            p_blacklisted_lines.push_back(argv[0]);
            assert(argc == 1);
        } else if (p_active_transaction == e_build){
            p_build_files.push_back(argv[0]);
            assert (argc == 1);
        } else {
            assert (0 && "Transaction does not exist!");
        }
        return 0;
    }
}

void Database::insert_external_function(const std::string& name)
{
    std::stringstream query;
    query << "INSERT INTO external_functions (name) values ('"<< name << "');"; 

    this->db_command(query.str());
}

void Database::insert_internal_function(const std::string& name)
{
    std::stringstream query;
    query << "INSERT INTO internal_functions (name) values ('" << name  << "');"; 

    this->db_command(query.str());
}

void Database::insert_basic_block(std::string const & file, std::string const & fn, std::string const & bb)
{
    std::stringstream query;
    query << "INSERT INTO basic_blocks (file, function, bb) values ('" << file << "','" << fn << "','" << bb << "');";
    
    this->db_command(query.str());
}

std::map<std::string, std::string> Database::get_options()
{
    std::stringstream query;
    query << "SELECT * FROM options;";
    
    p_active_transaction = e_options;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    return p_options;
}

/**
 * @brief Get the variables from the database
 */
std::vector<VariableInfo> Database::get_variables()
{
    std::string query = "SELECT DISTINCT name,type,position,free FROM variables;";
	p_variables.clear();
  
    p_active_transaction = e_get_variables;
    this->db_command(query);
    p_active_transaction = e_init;
    
	return p_variables;
}

std::vector<VariableInfo> Database::get_test_vector_variables()
{
    p_test_vector_variables.clear();
    
    std::string query = "SELECT name, type, name_hint,is_free from variables where variables.name in (select name from results);";
   
    p_active_transaction = e_get_test_vector_variables;
    this->db_command(query);
    p_active_transaction = e_init;
 
    return p_test_vector_variables;
}

std::vector<TestVector> Database::get_test_vectors()
{
    std::string query = "SELECT * FROM minimal_vectors;";
    p_test_vectors.clear();
    
    p_active_transaction = e_test_vectors;
    this->db_command(query);
    p_active_transaction = e_init;
    
    return p_test_vectors;
}

/**
 * @brief Get the blacklisted lines from the database
 * 
 * Blacklisted lines will not be instrumented with select variables
 * in order to avoid manipulating the forcing assertions
 * 
 * @return std::vector< std::string >
 */
std::vector<std::string> Database::get_blacklisted_lines()
{
    std::string query = "SELECT * FROM blacklist;";
    p_blacklisted_lines.clear();
    
    p_active_transaction = e_blacklist;
    this->db_command(query);
    p_active_transaction = e_init;
    
    return p_blacklisted_lines;
}

std::string Database::get_current_build_file()
{
    std::string query = "SELECT * FROM build;";
    p_build_files.clear();
    
    p_active_transaction = e_build;
    this->db_command(query);
    p_active_transaction = e_init;
    
    return p_build_files[p_build_files.size() -1];
}
