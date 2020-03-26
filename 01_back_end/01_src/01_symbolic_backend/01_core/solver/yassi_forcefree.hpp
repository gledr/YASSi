/** 
 * @file yassi_forcefree.hpp
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
#ifndef YASSI_FORCEFREE_HPP
#define YASSI_FORCEFREE_HPP

#include <yassi_object.hpp>
#include <yassi_logger.hpp>
#include <yassi_memory.hpp>
#include <yassi_variables.hpp>
#include <yassi_exception.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class ForceFree
 * @brief Include Const/Fixed Values into the SMT Instance
 */
class ForceFree: public virtual Object {
public:
    ForceFree(z3::context* z3_ctx);

    virtual ~ForceFree();

    void force_free_variable(Variables::BaseVariable* var,
                             size_t const size);

private:
    Logger* p_logger;
    Memory* p_memory;
    z3::context* p_z3_ctx;
    
    bool is_pointer_to_element(Variables::BaseVariable* var);
    bool is_pointer_to_pointer_to_element(Variables::BaseVariable* var);
    
    void free_pointer_to_element(Variables::BaseVariable* var,
                                 unsigned long size);
    void free_pointer_to_pointer_to_element(Variables::BaseVariable* var,
                                            unsigned long size);
};

}

#endif /* YASSI_FORCEFREE_HPP */
