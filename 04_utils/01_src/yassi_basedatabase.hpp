/** 
 * @file yassi_baselogger.hpp
 * @brief BaseDatabase Class for Yassi
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
#ifndef YASSI_BASE_DATABASE_HPP
#define YASSI_BASE_DATABASE_HPP

#include <sqlite3.h>

namespace Yassi::Utils {

/**
 * @class BaseDatabase
 * @brief Base Class for all Database Communication
 */ 
class BaseDatabase {
public:
 
    virtual int __callback__(int argc, char **argv, char **azColName) = 0;
    static int c_callback(void *data, int argc, char **argv, char **azColName);

    void db_command(std::string const & query);

protected:
    BaseDatabase(std::string const & url);

    virtual ~BaseDatabase();
    
    void open_database();
    void close_database();

    sqlite3* p_db;
    std::string p_db_url;
    bool p_debug;
};

}

#endif /* YASSI_BASE_DATABASE_HPP */
