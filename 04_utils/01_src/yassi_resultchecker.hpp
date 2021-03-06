/** 
 * @file yassi_resultschecker.hpp
 * @brief Check the results generated by Yassi
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
#ifndef YASSI_RESULTCHECKER_HPP
#define YASSI_RESULTCHECKER_HPP

#include <boost/filesystem.hpp>

#include <yassi_baseutils.hpp>
#include <yassi_database.hpp>

#include <json/json.h>

namespace Yassi::Utils {
    
enum eCmpStatus {eINIT, eSUCCESS, eFAIL, eUnknown};

/**
 * @class ResultChecker
 * @brief Check Results for Frontend and Unit Tests
 */ 
class ResultChecker {
public:
    ResultChecker(std::string const & project_url, std::string const & tmp_url);
    
    virtual ~ResultChecker();
    
    eCmpStatus check_results();
    
    void write_golden_results();
    
    std::vector<SingleResultPair> get_golden_results();
    std::vector<SingleException> get_golden_exceptions();
private:
    Frontend::Database* p_database;
    std::string p_tmp_url;
    std::string p_project_url;
    
    void read_golden_results_file();
    
    std::vector<SingleResultPair> p_golden_results;
    std::vector<SingleException> p_golden_exceptions;
    
    std::string p_result_identifier;
    std::string p_exception_identifier;
    std::string p_seperation_token;
};

}

#endif /* YASSI_RESULTCHECKER_HPP */
