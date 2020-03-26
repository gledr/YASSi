/** 
 * @file yassi_baselogger.cpp
 * @brief BaseLogger Class for Yassi
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
#include "yassi_database.hpp"

using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param url: Location of the database file
 */
BaseDatabase::BaseDatabase(std::string const & url)
{
    p_db_url = url;
    p_debug = false;
}

/**
 * @brief Destructor
 */
BaseDatabase::~BaseDatabase()
{
}

////////////////////////////////////////////////////////////////////////////
//                  BaseDatabase Basic Communication Functions
////////////////////////////////////////////////////////////////////////////
/**
 * @brief Execute an SQL query
 * @param command The SQL query to be executed
 */
void BaseDatabase::db_command(std::string const & command)
{
    this->open_database();
    p_debug && std::cout << BaseUtils::get_bash_string_orange("db_command: " + command) << std::endl;
   
    char const * str = command.c_str();
    if(sqlite3_exec(p_db, str, c_callback, this, NULL) != 0){
#ifdef YASSI
        throw YassiException(std::string(sqlite3_errmsg(p_db)));
#else 
        assert (0);
#endif
    }
    this->close_database();
}

/**
 * @brief Opens the BaseDatabase for a transaction
 */
void BaseDatabase::open_database()
{
    p_debug && std::cout<< "Open BaseDatabase Connection (" << p_db_url << ")" << std::endl;
    if((sqlite3_open(p_db_url.c_str(), &p_db)) != SQLITE_OK){
#ifdef YASSI
        throw YassiException(std::string(sqlite3_errmsg(p_db)));
#else 
        assert (0);
#endif
    }
    p_debug && std::cout << "BaseDatabase Connection Established!" << std::endl;
}

/**
 * @brief Close the BaseDatabase after a transation has been performed
 */ 
void BaseDatabase::close_database()
{
    p_debug && std::cout << "Close BaseDatabase has been called" << std::endl;
    if(p_db){
        sqlite3_close(p_db);
    }
}

/**
 * @brief Static Callback function for the Sqlite3 API
 * This function calls a member function in order to get access to the
 * this pointer and performs the operations in this function finally
 */
int BaseDatabase::c_callback(void *data, int argc, char **argv, char **azColName)
{
    BaseDatabase* tmp = reinterpret_cast<BaseDatabase*>(data);
    return tmp->__callback__(argc, argv, azColName);
}
