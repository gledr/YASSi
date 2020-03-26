/** 
 * @file yassi_forcefree.cpp
 * @brief This class realizes the ForceFree Intrinsic Functions
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
#include "yassi_forcefree.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param z3_ctx: Z3 Context
 */
ForceFree::ForceFree(z3::context* z3_ctx):
    Object(), p_z3_ctx(z3_ctx)
{
    nullpointer_check(z3_ctx);

    p_logger = Logger::getInstance();
    p_memory = Memory::getInstance(p_z3_ctx);
}

/**
 * @brief Destructor
 */
ForceFree::~ForceFree()
{
    p_logger = nullptr;
    p_memory = nullptr;
}

/**
 * @brief Force a Variable to be free for the reasoning engine
 *
 * @param var:  The variable to set free
 * @param size: The size of the variable (identify combined types)
 */
void ForceFree::force_free_variable(BaseVariable* var,
                                    size_t const size)
{
    nullpointer_check(var);
    
    if(this->is_pointer_to_element(var)){
        this->free_pointer_to_element(var, size);
    } else if (is_pointer_to_pointer_to_element(var)) {
        this->free_pointer_to_pointer_to_element(var, size);
    } else {
        throw YassiException("Unknown ForceFree Constellation detected!");
    }
}

/**
 * @brief Target element is accessible by dereferencing the variable pointer
 * 
 * @param var: The variable to derereference
 * @param size The size of the target variable
 */
void ForceFree::free_pointer_to_element(BaseVariable* var,
                                        unsigned long size)
{
    nullpointer_check(var);
    BaseVariable* deref = var->get_pointer();

    size_t mem_block = size;
    size_t mem_pos = deref->get_alloc_point();
    size_t elem_cnt = 0;
    while(mem_block > 0) {
        BaseVariable* element = p_memory->get_variable_by_mem_pos(mem_pos);

        element->set_force_free();
        p_memory->update_free_variables(element);
        element->clear_smt_formula();
        element->unset_constant();
        element->set_is_linear(false);

        mem_block -= element->get_type()->get_bytes();
        mem_pos++;
        elem_cnt++;
    }
    p_logger->force_free(var->get_name_hint(), std::to_string(elem_cnt));
}

/**
 * @brief The target variable is accessible by following 2 pointer.
 * 
 * @param var: The base variable to follow
 * @param size: The size of the target variable
 */
void ForceFree::free_pointer_to_pointer_to_element(BaseVariable* var,
                                                   unsigned long size)
{
    (void) size;

    nullpointer_check(var);
    
    BaseVariable* deref_var_ptr = var->get_pointer();
    BaseVariable* array_ptr = deref_var_ptr->get_pointer();
    
    size_t mem_pos = array_ptr->get_alloc_point();
    size_t first_addr = array_ptr->get_firstaddress();
    size_t last_addr = array_ptr->get_lastaddress();
    size_t mem_size = last_addr - first_addr + 1;
    size_t elem_cnt = 0;
    
    while(mem_size > 0){
        BaseVariable* element = p_memory->get_variable_by_mem_pos(mem_pos);
        
        element->set_force_free();
        element->unset_constant();
        element->clear_smt_formula();
        element->set_is_linear(false);
        p_memory->update_free_variables(element);
        
        mem_size -= element->get_type()->get_bytes();
        mem_pos++;
        elem_cnt++;
    }
    p_logger->force_free(var->get_name_hint(), std::to_string(elem_cnt));
}

/**
 * @brief Check if a variable is a pointer to an element
 * 
 * @param var The variable to check
 * @return bool
 */
bool ForceFree::is_pointer_to_element(BaseVariable* var)
{
    nullpointer_check(var);
    
    return var->get_type()->is_pointer() &&
           var->get_pointer() != nullptr &&
           !var->get_pointer()->get_type()->is_pointer();
}

/**
 * @brief Check if a variable is a pointer to a pointer to an element
 * 
 * @param var: The variable to check
 * @return bool
 */
bool ForceFree::is_pointer_to_pointer_to_element(BaseVariable* var)
{
    nullpointer_check(var);
    
    return var->get_type()->is_pointer() && 
           var->get_pointer() != nullptr && 
           var->get_pointer()->get_type()->is_pointer() &&
           var->get_pointer()->get_pointer() != nullptr &&
           !var->get_pointer()->get_pointer()->get_type()->is_pointer();
}
