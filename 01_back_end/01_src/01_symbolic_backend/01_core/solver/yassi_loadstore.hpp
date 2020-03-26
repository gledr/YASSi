/** 
 * @file yassi_loadstore.hpp
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
#ifndef YASSI_LOADSTORE_HPP
#define YASSI_LOADSTORE_HPP

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_pointerinstruction.hpp>
#include <yassi_propagation.hpp>
#include <yassi_memory.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class LoadStore
 * @brief This class realizes the Load and Store operations
 */
class LoadStore: public virtual Object {
public:

    LoadStore(z3::context * z3_ctx,
              PointerInstruction* pointer_instr);

    virtual ~LoadStore();

    void load_instruction(Variables::BaseVariable* dst,
                          Variables::PointerVariable* addr);

    void store_instruction(Variables::BaseVariable* src,
                           Variables::PointerVariable* addr);
    
private:
    inline bool is_load_pointer(Variables::BaseVariable* dst,
                                Variables::BaseVariable* addr);
    inline bool is_load_pointer_to_pointer(Variables::BaseVariable* dst,
                                           Variables::BaseVariable* addr);

    inline bool is_store_to_pointer(Variables::BaseVariable* src,
                                    Variables::BaseVariable* addr);
    inline bool is_store_pointer_to_pointer(Variables::BaseVariable* src,
                                            Variables::BaseVariable* addr);

    void check_valid_load_instruction(Variables::BaseVariable* dst,
                                      Variables::PointerVariable* addr);
    void check_valid_store_instruction(Variables::BaseVariable* src,
                                       Variables::PointerVariable* addr);
    
    void store_non_annotated(Variables::BaseVariable* src,
                             Variables::PointerVariable* addr);

    PointerInstruction* p_pointer_instr;
    Propagation* p_propagation;
    Variables::VariableFactory* p_var_factory;
    Yassi::Types::TypeFactory* p_type_factory;
    Memory* p_memory;
    z3::context* p_z3_ctx;
};

}

#endif /* YASSI_LOADSTORE_HPP */
