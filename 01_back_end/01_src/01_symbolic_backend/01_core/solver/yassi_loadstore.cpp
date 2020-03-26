/** 
 * @file yassi_loadstore.cpp
 * @brief This class realizes the Load and Store operations
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
#include "yassi_loadstore.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param z3_ctx:        Set the z3 context
 * @param pointer_instr: Set the pointer instruction handler.
 */
LoadStore::LoadStore(z3::context* z3_ctx,
                     PointerInstruction* pointer_instr):
    Object(), p_pointer_instr(pointer_instr), p_z3_ctx(z3_ctx)
{
    nullpointer_check(z3_ctx);
    nullpointer_check(pointer_instr);

    p_propagation       = new Propagation();
    p_var_factory       = new VariableFactory(z3_ctx);
    p_type_factory      = new TypeFactory();
    p_memory            = Memory::getInstance(z3_ctx);
}

/**
 * @brief Destructor
 */
LoadStore::~LoadStore()
{
    delete p_propagation;       p_propagation = nullptr;
    delete p_var_factory;       p_var_factory = nullptr;
    delete p_type_factory;      p_type_factory = nullptr;
                                p_memory = nullptr;
                                p_pointer_instr = nullptr;
}

/**
 * @brief Load Instruction
 * 
 * @param dst:  Destination to store variable
 * @param addr: Address to load variable
 */
void LoadStore::load_instruction(BaseVariable* dst,
                                 PointerVariable* addr)
{
    try {
        nullpointer_check(dst);
        nullpointer_check(addr);

        this->check_valid_load_instruction(dst, addr);

        if(addr->get_pointer()->get_index_values().empty()){
            if(this->is_load_pointer(dst, addr)){
                if(!addr->get_pointer()->get_type()->is_void()){
                    dst->set_smt_formula(addr->get_pointer()->get_smt_formula());
                }

                dst->set_value(addr->get_pointer()->get_value_as_string());
                p_propagation->propagate_unary(addr->get_pointer(), dst);
                p_memory->update_free_variables(dst);

            } else if (this->is_load_pointer_to_pointer(dst, addr)){
                if(addr->get_pointer()->is_function_pointer()){
                    dst->set_pointer(addr->get_pointer());
                } else {
                    dst->set_pointer(addr->get_pointer()->get_pointer());
                }
                p_memory->update_free_variables(dst);
            } else {
                //addr->dump();
                //addr->get_pointer()->dump();
                throw YassiNotImplemented("Load Pointer Depth 3");
            }
        } else {
            p_pointer_instr->symbolic_load(dst, addr->get_pointer());
        }
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Store Instruction
 * 
 * @param src:  Object to store
 * @param addr: Address to store to
 */
void LoadStore::store_instruction(BaseVariable* src,
                                  PointerVariable* addr)
{
    nullpointer_check(src);
    nullpointer_check(addr);

    this->check_valid_store_instruction(src, addr);

    if(addr->get_pointer() != nullptr && !addr->get_pointer()->has_indexes()){
        if(src->get_comes_from_nonannotated()){
            this->store_non_annotated(src, addr);
        } else if(this->is_store_to_pointer(src, addr)){
            addr->get_pointer()->unset_free_variable();
            p_memory->update_free_variables(addr->get_pointer());
            src->set_parent(addr);
            addr->get_pointer()->set_value(src->get_value_as_string());
            addr->get_pointer()->set_smt_formula(src->get_smt_formula());
            if(src->is_propaged_constant()){
                addr->get_pointer()->set_propagated_from(src->get_propagated_from());
            }
            addr->get_pointer()->set_is_linear(src->get_is_linear());
        } else if (this->is_store_pointer_to_pointer(src, addr)){
            BaseVariable* deref = addr->get_pointer();
            nullpointer_check(deref)

            deref->set_pointer(src->get_pointer());
            deref->get_pointer()->set_propagated_from(src->get_pointer());
            addr->get_pointer()->unset_free_variable();
            p_memory->update_free_variables(addr->get_pointer());
        } else {
            throw YassiNotImplemented("Store Depth 3");
        }
    } else {
        p_pointer_instr->symbolic_store(src, addr);
    }  
}

/**
 * @brief Store the Result of a Non Annoated Function Call
 * 
 * @param src:  Object to store
 * @param addr: Address to store to
 */
void LoadStore::store_non_annotated(BaseVariable* src,
                                    PointerVariable* addr)
{
    nullpointer_check(src);
    nullpointer_check(addr);
    
    if(this->is_store_to_pointer(src, addr)){
        std::cout << "First Level" << std::endl;
        src->unset_free_variable();
        p_memory->update_free_variables(src);
        addr->set_force_free();
        p_memory->update_free_variables(addr);
    } else if (this->is_store_pointer_to_pointer(src, addr)){
        std::cout << "Second Level" << std::endl;
        src->unset_free_variable();
        p_memory->update_free_variables(src);
        addr->get_pointer()->set_force_free();
        p_memory->update_free_variables(addr->get_pointer());
    } else {
        throw YassiException("Store Non Annoated Third Level!");
    }
}

/**
 * @brief Check if address is pointer
 * 
 * @param dst: The variable to store the variable to
 * @param addr The variable to load
 * @return bool
 */
bool LoadStore::is_load_pointer(BaseVariable* dst,
                                BaseVariable* addr)
{
    nullpointer_check(dst);
    nullpointer_check(addr);
    
    return !dst->get_type()->is_pointer() &&
           addr->get_type()->is_pointer() &&
           addr->get_pointer() != nullptr &&
           !addr->get_pointer()->get_type()->is_pointer();
}

/**
 * @brief Check if variable is pointer and address is pointer
 * 
 * @param dst: The variable to store to
 * @param addr The variabel to load
 * @return bool
 */
bool LoadStore::is_load_pointer_to_pointer(BaseVariable* dst,
                                           BaseVariable* addr)
{
    nullpointer_check(dst);
    nullpointer_check(addr);
    
    return dst->get_type()->is_pointer() && addr->get_type()->is_pointer() &&
           addr->get_pointer() != nullptr && addr->get_pointer()->get_type()->is_pointer();
}

/**
 * @brief Check if address is pointer
 * 
 * @param src:  The variabel to store
 * @param addr: The address to store to
 * @return bool
 */
bool LoadStore::is_store_to_pointer(BaseVariable* src,
                                    BaseVariable* addr)
{
    nullpointer_check(src);
    nullpointer_check(addr);
    
    return !src->get_type()->is_pointer() && addr->get_type()->is_pointer() &&
            addr->get_type()->is_pointer() && addr->get_pointer() != nullptr &&
            !addr->get_pointer()->get_type()->is_pointer();
}

/**
 * @brief Check if variable and address are pointer
 * 
 * @param src:  The variable to store
 * @param addr: The address to store to
 * @return bool
 */
bool LoadStore::is_store_pointer_to_pointer(BaseVariable* src,
                                            BaseVariable* addr)
{
    nullpointer_check(src);
    nullpointer_check(addr);
    
    return src->get_type()->is_pointer() && addr->get_type()->is_pointer();
}

/**
 * @brief Check if load instruction is on valid memory
 * 
 * @param dst: The load destination
 * @param addr The address to load
 */
void LoadStore::check_valid_load_instruction(BaseVariable* dst,
                                             PointerVariable* addr)
{
    nullpointer_check(dst);
    nullpointer_check(addr);

    BaseType* type_obj = dst->get_type();
    BaseType* load_type = addr->get_pointer()->get_type();

    (void) load_type;
    (void) type_obj;

}

/**
 * @brief Check if store instruction is on valid memory
 * 
 * @param src:  The variable to store
 * @param addr: The address to store to
 */
void LoadStore::check_valid_store_instruction(BaseVariable* src,
                                              PointerVariable* addr)
{
    (void) src;
    (void) addr;
}
