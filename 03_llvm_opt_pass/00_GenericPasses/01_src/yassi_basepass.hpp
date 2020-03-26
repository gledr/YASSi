/** 
 * @file yassi_basepass.hpp
 * @brief Base Class for all Optimization Passes
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
#ifndef YASSI_BASE_PASS_HPP
#define YASSI_BASE_PASS_HPP

#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>

#include <boost/core/demangle.hpp>

#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/TypeBuilder.h"

#ifndef YASSI_PASS
    #include "yassi_database.hpp"
    #include "../../../04_utils/02_types/yassi_types.hpp"
    #include "../../../04_utils/03_datastructures/yassi_genericdatastructures.hpp"
#else 
    #include "yassi_database.hpp"
    #include "02_types/yassi_types.hpp"
    #include "yassi_baseutils.hpp"
    #include "yassi_genericdatastructures.hpp"
#endif


namespace Yassi::OptPass {

std::string const BACKEND_METHOD_GLOBAL_INIT    = "yassi_global_init";         ///<
std::string const BACKEND_FN_GLOBAL_INIT        = "global_var_init";            ///<

std::string const BACKEND_FN_FP                 = "fp_hook";                    ///<

std::string const BACKEND_FN_ASSUME             = "__YASSI_assume";            ///<
std::string const BACKEND_FN_VERIFIER_ASSUME    = "__VERIFIER_assume";          ///<

std::string const BACKEND_FN_ASSERTION          = "__YASSI_assert";            ///<
std::string const BACKEND_FN_VERIFIER_ASSERT    = "__VERIFIER_assert";          ///<

std::string const BACKEND_FN_ERROR              = "__YASSI_error";             ///<
std::string const BACKEND_FN_VERIFIER_ERROR     = "__VERIFIER_error";           ///<

std::string const BACKEND_FN_FORCEFREE_LOCAL    = "__YASSI_force_free_local";  ///<
std::string const BACKEND_FN_FORCEFREE_GLOBAL   = "__YASSI_force_free_global"; ///<
std::string const BACKEND_FN_FORCE_ASSERTION    = "__YASSI_force_assertion";   ///<

std::string const LLVM_FUNCTION_RET_REG_NAME    = "call";                       ///<
std::string const YASSI_VARIABLE_PREFIX_FN_RET = "return_of_";                 ///<

std::string const BACKEND_FN_MALLOC             = "malloc";                     ///<
std::string const BACKEND_FN_YASSI_MALLOC      = "__YASSI_malloc";            ///<

std::string const BACKEND_FN_FREE               = "free";                       ///<
std::string const BACKEND_FN_YASSI_FREE        = "__YASSI_free";              ///<

std::string const BACKEND_FN_DEBUG_MSG          = "__YASSI_debug";             ///<

/**
 * @class BasePass
 * @brief Virtual Base Class
 */
class BasePass {
public: 
    virtual ~BasePass();

protected:
    BasePass();

    llvm::GlobalVariable* make_global_str(llvm::Module& M, std::string const & name);
    llvm::GlobalVariable* make_global_int(llvm::Module& M, std::string const & name, size_t const width);
    llvm::GlobalVariable* make_global_float(llvm::Module& M, std::string const & name);
    llvm::GlobalVariable* make_global_double(llvm::Module& M, std::string const & name);

    llvm::Constant* pointerToArray(llvm::Module& M, llvm::GlobalVariable* global_var);

    std::string operandname(llvm::Value* operand);

    std::string floatvalue(llvm::ConstantFP * CF);

    std::string get_flattened_types(const llvm::Type* t);
    std::string get_flattened_types_recursive(const llvm::Type* t);

    int get_size(const llvm::Type* t );

    int element_size(const llvm::ArrayType* t );

    std::vector<int> get_dimensions( const llvm::ArrayType* t );

    int sizeofstruct(const llvm::Type* t);

    std::string get_offset_tree(llvm::Type* t);
    std::string get_offset_tree_rec(llvm::Type* t, int & base);

    int get_offset(llvm::Type* t);

    std::string make_register_name(std::string const & name);

    std::string make_function_name(std::string const & name);

    std::string make_global_name(std::string const & name);

    std::string make_constant(std::string const & type, std::string const & value="");

  
    bool is_special_llvm_function(std::string const & fn_name);
    bool is_internal_yassi_function(std::string const & fn_name);

    std::string line_number_of_instruction(llvm::Instruction const & ins);
    
    std::string demangle_fn_name(std::string const & str);
    
    int product(std::vector<int> elem);

    Database* p_db;
    Yassi::Types::TypeFactory* p_type_factory;
    std::string p_tmp_folder;
    std::string p_current_source_file;
    std::map<std::string, std::string> p_settings;
    std::string p_entry_function_name;
    bool p_verbose;
    bool p_recursive;

    std::string MANGLING_SEPERATOR;
    std::string VARIABLE_SEPERATOR;
};

}

#endif /* YASSI_BASE_PASS_HPP */
