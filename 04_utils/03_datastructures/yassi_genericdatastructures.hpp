/** 
 * @file yassi_genericdatastructures.hpp
 * @brief Generic Datastructures for Yassi
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
#ifndef YASSI_GENERIC_DATASTRUCTURES_HPP
#define YASSI_GENERIC_DATASTRUCTURES_HPP

#include <string>
#include <ostream>

namespace Yassi::Utils {

class VariableInfo {
public:
    std::string name;
    std::string type;
    std::string position;
    bool free;
};

struct TestVector {
    std::string vector_id;
    std::string variable_name;
    std::string variable_hint;
    std::string value;
};

class SingleResultPair {
public:
    std::string reg_name;
    std::string reg_hint;
    std::string reg_val;
    int solution;
    
    bool operator== (SingleResultPair a)
    {
        return this->reg_val == a.reg_val &&
            this->reg_name == a.reg_name  &&
            this->solution == a.solution  &&
            this->reg_hint == a.reg_hint;
    }
    
    friend std::ostream& operator<<(std::ostream& stream, SingleResultPair const & res)
    {
        stream << "=== SingleResultPair Dump ===" << std::endl
               << "Name Hint      : "  << res.reg_hint << std::endl
               << "Register Name  : " << res.reg_name << std::endl
               << "Register Value : " << res.reg_val << std::endl
               << "Solution       : " << res.solution << std::endl
               << "=============================" << std::endl;
        return stream;
    }
};

/**
 * @brief Funktor used to sort result vectors of SingleResultPair
 */ 
struct SingleResultPairSortFunktor {
    /**
     * @brief Compare solution numbers from SingleResultPairs
     * 
     * @param a The first object to compare
     * @param b The second object to compare
     * @return True: if a.solution < b.solution, False: Else
     */ 
    bool operator() (SingleResultPair const & a, SingleResultPair const & b) {
        return a.solution < b.solution;
    }
};
    
class BasicBlock {
public:
    std::string file;
    std::string fn;
    std::string bb;
};


struct SingleException {
    std::string type;
    std::string id;
    std::string location;
    std::string file;
    
    bool operator== (SingleException a)
    {
        return this->type == a.type      &&
            this->id == a.id             &&
            this->location == a.location &&
            this->file == a.file;
    }
};

}

#endif /* YASSI_GENERIC_DATASTRUCTURES_HPP */
