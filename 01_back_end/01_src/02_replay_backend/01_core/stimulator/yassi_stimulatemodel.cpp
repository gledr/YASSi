/** 
 * @file yassi_stimulatemodel.cpp
 * @brief Trigger the Execution of the Replay Model using Test Vectors
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
#include "yassi_stimulatemodel.hpp"

using namespace Yassi::Backend::Replay;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
StimulateModel::StimulateModel():
    Object()
{
    p_logger = Logger::getInstance();
}

/**
 * @brief Destructor
 */
StimulateModel::~StimulateModel() 
{
    p_logger = nullptr;
}

/**
 * @brief Start Replay 
 */
void StimulateModel::begin_sim() 
{
    this->load_test_vectors();
}

/**
 * @brief Finish Replay
 */
void StimulateModel::end_sim() 
{

}

/**
 * @brief Apply the next Integer Test Vector (32 Bit)
 * 
 * @param name: Variable Name
 * @return int
 */
int StimulateModel::vector_int(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_int(name, ret);
  
    if(std::stol(ret) > std::numeric_limits<int>::max()){
        return std::numeric_limits<int>::max();
    } else {
        return std::stoi(ret);
    }
}

/**
 * @brief Apply the next Char Test Vector (8 Bit)
 * 
 * @param name: Variable Name
 * @return char
 */
char StimulateModel::vector_char(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_char(name, ret);
    
    return std::stoi(ret);
}

/**
 * @brief Apply the next Floating Point Test Vector (Single Precision)
 * 
 * @param name: Variable Name
 * @return float
 */
float StimulateModel::vector_float(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_float(name, ret);
    
    return std::stof(ret);
}

/**
 * @brief Apply the next Floating Point Test Vector (Double Precision)
 * 
 * @param name Variable Name
 * @return double
 */
double StimulateModel::vector_double(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_double(name, ret);
    
    return std::stod(ret);
}

/**
 * @brief Apply the next Integer Test Vector (64 Bit)
 * 
 * @param name Variable Name 
 * @return long int
 */
long StimulateModel::vector_long(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_long(name, ret);

    return  std::stol(ret);
}

/**
 * @brief Apply the next Integer Test Vector (16 Bit)
 * 
 * @param name Variable Name 
 * @return short int
 */
short StimulateModel::vector_short(std::string const & name) 
{
    std::string ret = p_test_vectors[name][0];
    p_test_vectors[name].erase(p_test_vectors[name].begin());
    p_logger->apply_vector_short(name, ret);
    
    return static_cast<short>(std::stoi(ret));
}

/**
 * @brief Load Test Vector from Database
 */
void StimulateModel::load_test_vectors()
{
    std::vector<VariableInfo> test_vector_variables = p_database->get_test_vector_variables();
    std::vector<TestVector> vectors = p_database->get_test_vectors();
    
    for(auto itor : vectors) {
        p_test_vectors[itor.variable_name].push_back(itor.value);
    }
}
