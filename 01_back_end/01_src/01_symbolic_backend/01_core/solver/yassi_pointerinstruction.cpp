/** 
 * @file yassi_pointerinstruction.cpp
 * @brief This class realizes operations on Pointer
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
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
#include "yassi_pointerinstruction.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param z3_ctx Get access to the Z3 Context
 */
PointerInstruction::PointerInstruction(z3::context* z3_ctx):
    Object()
{
    nullpointer_check(z3_ctx);
    
    p_z3_ctx = z3_ctx;
    p_database = new Database(this->get_database_url());

    p_memory         = Memory::getInstance(p_z3_ctx);
    p_logger         = Logger::getInstance();
    p_allsat         = new AllSAT(p_z3_ctx);
    p_var_factory    = new VariableFactory(p_z3_ctx);
    p_run_time_exception = new RunTimeException();
    p_type_tree = new DatastructureTree();
}

/**
 * @brief Destructor
 */
PointerInstruction::~PointerInstruction()
{
    delete p_allsat;                p_allsat                = nullptr;
    delete p_database;              p_database              = nullptr;
    delete p_var_factory;           p_var_factory           = nullptr;
    delete p_run_time_exception;    p_run_time_exception    = nullptr;
    delete p_type_tree;             p_type_tree             = nullptr;
                                    p_memory                = nullptr;
                                    p_logger                = nullptr;
}

/**
 * @brief Getelement Pointer Instruction
 * 
 * @param dst_var Variable to Load Result into
 * @param pointer_var Pointer to the Datastructure
 * @param index_vars Offset Variables 
 * @param _offset_tree Offset Tree showing the Memory Allignment of the Data
 */
void PointerInstruction::getelementptr(BaseVariable* dst_var,
                                       BaseVariable* pointer_var,
                                       std::vector<BaseVariable*> & index_vars,
                                       std::string const & _offset_tree)
{
    nullpointer_check(dst_var);
    nullpointer_check(pointer_var);
    
    for(auto& itor : index_vars){
       nullpointer_check(itor);
    }

    if(this->is_constant_getelementptr(index_vars)){
        this->constant_gep(dst_var, pointer_var, index_vars, _offset_tree);
    } else {
        this->non_constant_gep(dst_var, pointer_var, index_vars, _offset_tree);
    }
}

/**
 * @brief Check if GEP Instruction is Constant
 * 
 * @param var Variables holding the Indexes
 * @return bool
 */
bool PointerInstruction::is_constant_getelementptr(std::vector<BaseVariable *> var)
{
    std::vector<bool> parity;
    parity.resize(var.size());
    
    for(size_t i = 0; i < var.size(); ++i){
        parity[i] = var[i]->is_constant();
    }

    for(size_t i = 0; i < var.size(); ++i){
        if(parity[i] == false){
            if(!var[i]->get_propagated_from()->is_free_variable()){
                parity[i] = true;
            }
        }
    }

    bool ret_val = true;
    for(size_t i = 0; i < var.size(); ++i){
        if(parity[i] == false){
            ret_val = false;
            break;
        }
    }
    return ret_val;
}

/**
 * @brief Perform Constant GEP Instruction
 * 
 * @param dst_var Variable to Load Result into
 * @param pointer_var Pointer to the Datastructure
 * @param index_vars Offset Variables
 * @param _offset_tree Offset Tree showing the Memory Allignment of the Data
 */
void PointerInstruction::constant_gep(BaseVariable* dst_var,
                                      BaseVariable* pointer_var,
                                      std::vector<BaseVariable*> & indexes,
                                      std::string const & _offset_tree)
{
    try {
        nullpointer_check(dst_var);
        nullpointer_check(pointer_var);

        BaseVariable* deref_ptr = pointer_var->get_pointer();

        std::vector<size_t> index_real_values;
        for(auto itor : indexes){
            index_real_values.push_back(itor->get_value_i32());
        }

        BaseVariable* dst_mem  = nullptr;

        if(!deref_ptr->has_indexes()){
            p_type_tree->read_tree(_offset_tree);
            auto tree_alignment = p_type_tree->get_alignment();

            // Pointer Increment
            if(index_real_values.size() == 1){
                size_t offset_bytes = tree_alignment[0].second * tree_alignment.size() * index_real_values[0];
                int offset = p_memory->address_offset_to_mem_address(deref_ptr, offset_bytes);
                dst_mem = p_memory->get_variable_by_mem_pos(offset); // the location we are adding a pointer to

            // Pointer Access
            } else {
                size_t offset_bytes = p_type_tree->get_offset(index_real_values);
                int offset = p_memory->address_offset_to_mem_address(deref_ptr, offset_bytes);
                dst_mem = p_memory->get_variable_by_mem_pos(offset); // the location we are adding a pointer to
            }

            if(pointer_var->get_pointer()->get_index_var().size() > 0){
                BaseVariable* index_var = pointer_var->get_pointer()->get_index_var()[0];

                assertion_check(indexes.size() == 2);
                dst_mem->set_index_assertion(index_var->get_smt_formula() == indexes[1]->get_smt_formula());
            }
            
            dst_mem->set_offset_tree(_offset_tree);
            dst_var->set_pointer(dst_mem);
            dst_var->unset_free_variable();

        } else {
            // Insert the indexes 
            PointerVariable* dst_ptr = dynamic_cast<PointerVariable*>(dst_var);
            BaseVariable* elem_ptr = p_var_factory->create_variable("", pointer_var->get_pointer()->get_type()->get_type_identifier());
            dst_ptr->set_pointer(elem_ptr);

            auto indexes_phase_1 = pointer_var->get_pointer()->get_index_values();
            BaseVariable* index_var = pointer_var->get_pointer()->get_index_var()[0];

            for(auto itor: indexes_phase_1){
                elem_ptr->insert_index(itor);
            }

            std::vector<size_t> indexes;
            indexes.push_back(index_real_values[1]);
            elem_ptr->set_constant();
            elem_ptr->set_offset_tree(_offset_tree);
            elem_ptr->set_propagated_from(pointer_var->get_pointer()->get_propagated_from());
            elem_ptr->add_index_var(index_var);
            elem_ptr->insert_index(indexes);
            for(auto itor: deref_ptr->get_index_base_pointer()){
                elem_ptr->add_index_base_pointer(itor);
            }
            elem_ptr->unset_free_variable();
        }
        p_logger->constant_elementptr(deref_ptr, dst_var, indexes);
    } catch (z3::exception const & ex){
        std::cout << ex.msg() << std::endl;
    }
}

/**
 * @brief Perform Non Constant GEP
 * 
 * @param dst_var Variable to Load Result into
 * @param pointer_var Pointer to the Datastructure
 * @param index_vars Offset Variables 
 * @param _offset_tree Offset Tree showing the Memory Allignment of the Data
 */
void PointerInstruction::non_constant_gep(BaseVariable* dst_var,
                                          BaseVariable* pointer_var,
                                          std::vector<BaseVariable*> & indexes,
                                          std::string const & _offset_tree)
{
    try {
        nullpointer_check(dst_var);
        nullpointer_check(pointer_var);

        assertion_check(indexes.size() == 2);
        assertion_check(indexes.at(0)->is_constant());

        p_type_tree->read_tree(_offset_tree);
        auto alignment = p_type_tree->get_alignment();
        std::vector<size_t> idx_vals;

        std::vector<size_t> subtrees = p_type_tree->subtree();

        std::vector<std::vector<size_t>> index_vals = pointer_var->get_pointer()->get_index_values();
        std::vector<BaseVariable*> index_vars = pointer_var->get_pointer()->get_index_var();

        PointerVariable* dst_ptr = dynamic_cast<PointerVariable*>(dst_var);
        pointer_var->get_pointer()->add_index_var(indexes[1]);

        BaseVariable* elem_ptr = p_var_factory->create_variable("", pointer_var->get_pointer()->get_type()->get_type_identifier());
        dst_ptr->set_pointer(elem_ptr);
        
        for(auto& itor :indexes){
            if(!itor->is_constant()){
                elem_ptr->set_propagated_from(itor->get_propagated_from());
            }
        }
    
        for(auto itor: index_vars){
            elem_ptr->add_index_var(itor);
        }
    
        for(auto itor: pointer_var->get_pointer()->get_index_base_pointer()){
                elem_ptr->add_index_base_pointer(itor);
            }

        for(auto itor: index_vals){
            elem_ptr->insert_index(itor);
        }

        if(subtrees.size() > 1){
            for(auto itor: subtrees){
                for(size_t i = 0; i < alignment.size(); ++i){
                    if(itor == alignment[i].first){
                        idx_vals.push_back(i);
                    }
                }
            }
        } else {
             for(size_t i = 0; i < alignment.size(); ++i){
                idx_vals.push_back(i);
            }
        }

        elem_ptr->unset_constant();
        elem_ptr->insert_index(idx_vals);
        elem_ptr->add_index_base_pointer(pointer_var);
        elem_ptr->add_index_var(indexes[1]);
        elem_ptr->unset_free_variable();
        p_logger->non_constant_elementptr(pointer_var, dst_ptr, idx_vals);

    } catch (z3::exception const & ex){
        throw YassiException(ex.msg());
    }
}

/**
 * @brief Symbolic Load: Load Memory with undefined Content
 * 
 * @param dst Variable to Store result to
 * @param addr Address to Load
 */
void PointerInstruction::symbolic_load(BaseVariable* dst,
                                       BaseVariable* addr)
{
    nullpointer_check(dst);
    nullpointer_check(addr);
    
    p_logger->symbolic_load();
        
    if(this->is_symbolic_load_1d(addr)){
        this->symbolic_load_1d(dst, addr);
    } else if (is_symbolic_load_2d(addr)){
        this->symbolic_load_2d(dst, addr);
    } else {
        throw YassiException("Symbolic Load for 3D Arrays not implemented!");
    }
    
    this->clean_up_symbolic_load(addr);
}

/**
 * @brief Check if Memory for Symbolic Load is 1D
 * 
 * @param addr Address to Load
 * @return bool
 */
bool PointerInstruction::is_symbolic_load_1d(BaseVariable* addr)
{
    nullpointer_check(addr);
    return addr->get_index_values().size() == 1;
}

/**
 * @brief Check if Memory for Symbolic Load is 2D
 * 
 * @param addr Address to Load
 * @return bool
 */
bool PointerInstruction::is_symbolic_load_2d(BaseVariable* addr)
{
    nullpointer_check(addr);
    return addr->get_index_values().size() == 2;
}

/**
 * @brief Perform Symbolic Load Operation for 1D Problems
 * 
 * @param dst Variable to Store result to
 * @param addr Address to Load
 */
void PointerInstruction::symbolic_load_1d(BaseVariable* dst,
                                          BaseVariable* addr)
{
    try {
        nullpointer_check(dst);
        nullpointer_check(addr);

        dst->set_propagated_from(addr->get_propagated_from());
        dst->set_propagated_constant();
        dst->clear_smt_formula();

        BaseVariable* index_var = addr->get_index_var()[0];
        z3::expr idx_var_smt = index_var->get_smt_formula();
        std::vector<size_t> idx_vals = addr->get_index_values()[0];

        BaseVariable* index_base_ptr = addr->get_index_base_pointer()[0]->get_pointer();
        size_t base_ptr_location = index_base_ptr->get_alloc_point();

        //
        // Construct the SMT Variables for all Indexes
        //
        z3::expr_vector idx_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals.size(); ++i) {
            idx_smt.push_back(p_z3_ctx->bv_val(idx_vals[i], index_var->get_type()->get_bits()));
        }

        //
        // Construct a Boolean Variable for each Index Value in order to use it for an ITE
        //
        z3::expr_vector ite_bool(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals.size(); ++i) {
            ite_bool.push_back(idx_smt[i] == idx_var_smt);
        }

        //
        // Construct a Vector Containing all Memory Values
        //
        z3::expr_vector mem_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals.size(); ++i) {
            z3::expr tmp = p_memory->get_variable_by_mem_pos(base_ptr_location + i)->get_smt_formula();
            mem_smt.push_back(tmp);
        }

        size_t last_ite_pos = idx_vals.size()-1;
        z3::expr dummy = p_z3_ctx->bv_val(std::stol(index_base_ptr->get_type()->get_max_value()), index_base_ptr->get_type()->get_bits());
        z3::expr last_ite = z3::ite(ite_bool[last_ite_pos], mem_smt[last_ite_pos], dummy);
        z3::expr_vector ite_builder(*p_z3_ctx);

        ite_builder.push_back(last_ite);
        for(int i = idx_vals.size()-2; i >= 0; --i) {
            ite_builder.push_back(z3::ite(ite_bool[i], mem_smt[i], ite_builder[ite_builder.size()-1]));
        }

        z3::expr deref = ite_builder[ite_builder.size()-1];
        dst->set_smt_formula(deref);
        dst->unset_free_variable();

    } catch (std::exception const & exp) {
        throw YassiException(exp.what());
    } catch (z3::exception const & exp){
       throw YassiException(exp.msg());
    }
}

/**
 * @brief Perform Symbolic Load Operation for 2D Problems
 * 
 * @param dst Variable to Store result to
 * @param addr Address to Load
 */
void PointerInstruction::symbolic_load_2d(BaseVariable* dst,
                                          BaseVariable* addr)
{
    if(addr->is_constant()){
        this->symbolic_load_2d_free_const(dst, addr);
    } else {
        this->symbolic_load_2d_free_free(dst, addr);
    }
}

/**
 * @brief Clean Environment of Variable for Symblic Load
 * 
 * @param addr Loaded Address
 */
void PointerInstruction::clean_up_symbolic_load(BaseVariable* addr)
{
    nullpointer_check(addr);
    
    addr->clear_index_base_pointer();
    addr->clear_index_var();
    addr->clear_indexes();
}

/**
 * @brief Perform a Symbolic Load Operation for the case Free/Const
 * 
 * @param dst Variable to Store result to
 * @param addr Address to Load
 */
void PointerInstruction::symbolic_load_2d_free_const(BaseVariable* dst,
                                                     BaseVariable* addr)
{
    try {
        dst->set_propagated_from(addr->get_propagated_from());
        dst->set_propagated_constant();
        dst->clear_smt_formula();

        z3::expr idx_var_smt = dst->get_smt_formula();
        std::vector<size_t> idx_l1 = addr->get_index_values()[0];
        std::vector<size_t> idx_l2 = addr->get_index_values()[1];

        BaseVariable* index_base_ptr = addr->get_index_base_pointer()[0]->get_pointer();
        size_t base_ptr_location = index_base_ptr->get_alloc_point();

        //
        // Construct the SMT Variables for all Indexes
        //
        z3::expr_vector idx_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_l1.size(); ++i) {
            idx_smt.push_back(p_z3_ctx->bv_val(i, index_base_ptr->get_type()->get_bits()));
        }

        //
        // Construct a Boolean Variable for each Index Value in order to use it for an ITE
        //
        z3::expr_vector ite_bool(*p_z3_ctx);
        for(size_t i = 0; i < idx_l1.size(); ++i) {
            ite_bool.push_back(idx_smt[i] == idx_var_smt);
        }

        //
        // Construct a Vector Containing all Memory Values
        //
        z3::expr_vector mem_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_l1.size(); ++i) {
            size_t pos = base_ptr_location + (i * (idx_l1.size())) + idx_l2[0];
            z3::expr tmp = p_memory->get_variable_by_mem_pos(pos)->get_smt_formula();
            mem_smt.push_back(tmp);
        }

        size_t last_ite_pos = idx_l1.size()-1;
        z3::expr dummy = p_z3_ctx->bv_val(std::stol(index_base_ptr->get_type()->get_max_value()), index_base_ptr->get_type()->get_bits());
        z3::expr last_ite = z3::ite(ite_bool[last_ite_pos], mem_smt[last_ite_pos], dummy);
        z3::expr_vector ite_builder(*p_z3_ctx);

        ite_builder.push_back(last_ite);
        for(int i = idx_l1.size()-2; i >= 0; --i) {
            ite_builder.push_back(z3::ite(ite_bool[i], mem_smt[i], ite_builder[ite_builder.size()-1]));
        }

        z3::expr deref = ite_builder[ite_builder.size()-1];
        dst->set_smt_formula(deref);
        dst->unset_free_variable();

    } catch (std::exception const & expr) {
        std::cerr << expr.what() << std::endl;
    } catch (z3::exception const & expr){
        std::cerr << expr.msg() << std::endl;
    }
}

/**
 * @brief Perform a Symbolic Load Operation for the case Free/Free
 * 
 * @param dst Variable to Store result to
 * @param addr Address to Load
 */
void PointerInstruction::symbolic_load_2d_free_free(BaseVariable* dst,
                                                    BaseVariable* addr)
{
    try {
        dst->set_propagated_from(addr->get_propagated_from());
        dst->set_propagated_constant();
        dst->clear_smt_formula();

        BaseVariable* idx_var_l1 = addr->get_index_var()[0];
        BaseVariable* idx_var_l2 = addr->get_index_var()[1];

        z3::expr idx_smt_l1 = idx_var_l1->get_smt_formula();
        z3::expr idx_smt_l2 = idx_var_l2->get_smt_formula();

        std::vector<size_t> idx_val_l1 = addr->get_index_values()[0];
        std::vector<size_t> idx_val_l2 = addr->get_index_values()[1];

        BaseVariable* index_base_ptr = addr->get_index_base_pointer()[0]->get_pointer();
        size_t base_ptr_location = index_base_ptr->get_alloc_point();
        
        //
        // Construct the SMT Variables for all Indexes
        //
        z3::expr_vector idx_l1_expr(*p_z3_ctx);
        z3::expr_vector idx_l2_expr(*p_z3_ctx);
        
        for(size_t i = 0; i < idx_val_l1.size(); ++i) {
            idx_l1_expr.push_back(p_z3_ctx->bv_val(i, idx_var_l1->get_type()->get_bits()));
        }
        for(size_t i = 0; i < idx_val_l2.size(); ++i) {
            idx_l2_expr.push_back(p_z3_ctx->bv_val(i, idx_var_l2->get_type()->get_bits()));
        }

        //
        // Construct a Boolean Variable for each Index Value in order to use it for an ITE
        //
        z3::expr_vector ite_bool_l1(*p_z3_ctx);
        z3::expr_vector ite_bool_l2(*p_z3_ctx);

        for(size_t i = 0; i < idx_l1_expr.size(); ++i) {
            ite_bool_l1.push_back(idx_l1_expr[i] == idx_smt_l1);
        }
        for(size_t i = 0; i < idx_l2_expr.size(); ++i) {
            ite_bool_l2.push_back(idx_l2_expr[i] == idx_smt_l2);
        }

        //
        // Construct a Vector Containing all Memory Values
        //
        z3::expr_vector mem_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_val_l1.size(); ++i) {
            for(size_t j = 0; j < idx_val_l2.size(); ++j){
                size_t pos = base_ptr_location + (i * (idx_val_l1.size())) + j;
                z3::expr tmp = p_memory->get_variable_by_mem_pos(pos)->get_smt_formula();
                mem_smt.push_back(tmp);
            }
        }
        //
        // Construct the cross product of all index values
        //
        z3::expr_vector idx_cross_product(*p_z3_ctx);
        for(size_t i = 0; i < ite_bool_l1.size(); ++i){
            for(size_t j = 0; j < ite_bool_l2.size(); ++j){
                z3::expr_vector tmp(*p_z3_ctx);
                tmp.push_back(ite_bool_l1[i]);
                tmp.push_back(ite_bool_l2[j]);
                idx_cross_product.push_back(z3::mk_and(tmp));
            }
        }

        size_t last_ite_pos = idx_cross_product.size()-1;
        z3::expr dummy = p_z3_ctx->bv_val(std::stol(index_base_ptr->get_type()->get_max_value()), index_base_ptr->get_type()->get_bits());
        z3::expr last_ite = z3::ite(idx_cross_product[last_ite_pos], mem_smt[last_ite_pos], dummy);
        z3::expr_vector ite_builder(*p_z3_ctx);

        ite_builder.push_back(last_ite);
        for(int i = idx_cross_product.size()-2; i >= 0; --i) {
            ite_builder.push_back(z3::ite(idx_cross_product[i], mem_smt[i], ite_builder[ite_builder.size()-1]));
        }

        z3::expr deref = ite_builder[ite_builder.size()-1];
        dst->set_smt_formula(deref);
        dst->unset_free_variable();
    } catch (z3::exception const & msg){
        throw YassiException(msg.msg());
    }
}

/**
 * @brief Perform a Store Operation to an not yet known Memory Address
 * 
 * @param src Load Variable from
 * @param addr Store Variable to Address
 */
void PointerInstruction::symbolic_store(BaseVariable* src,
                                        BaseVariable* addr)
{
    try {
        nullpointer_check(src);
        nullpointer_check(addr);

        p_logger->symbolic_store();

        src->add_index_var(addr->get_pointer()->get_index_var()[0]);
        PointerVariable* addr_ptr = dynamic_cast<PointerVariable*>(addr);
        z3::expr src_smt = src->get_smt_formula();    
        std::vector<std::vector<size_t>> idx_vals = addr_ptr->get_pointer()->get_index_values();
        
        BaseVariable* index_base_ptr = addr_ptr->get_pointer()->get_index_base_pointer()[0];
        size_t base_ptr_location = index_base_ptr->get_pointer()->get_alloc_point();
        BaseVariable * index_smt_var = addr->get_pointer()->get_propagated_from();
        
        //
        // Construct the SMT Variables for all Indexes
        //

        // FIXME 32 Bit ?!?
        z3::expr_vector idx_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals[0].size(); ++i){
            idx_smt.push_back(p_z3_ctx->bv_val(idx_vals[0][i], 32));
        }

        //
        // Construct a Vector Containing all Memory Values
        //
        z3::expr_vector mem_smt(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals[0].size(); ++i){
            BaseVariable*  var = p_memory->get_variable_by_mem_pos(base_ptr_location + i);
            z3::expr tmp = var->get_smt_formula();
            mem_smt.push_back(tmp);
        }

        //
        // Construct a Boolean Variable for each Index Value in order to use it for an ITE
        //
        z3::expr_vector ite_bool(*p_z3_ctx);
        for(size_t i = 0; i < idx_vals.size(); ++i){
            ite_bool.push_back(idx_smt[i] == index_smt_var->get_smt_formula());
        }

        size_t last_ite_pos = idx_vals.size()-1;
        z3::expr dummy = p_z3_ctx->bv_val(0, p_memory->get_variable_by_mem_pos(base_ptr_location + idx_vals[0].back())->get_type()->get_bits());
        
        z3::expr last_ite = z3::ite(ite_bool[last_ite_pos], mem_smt[last_ite_pos], dummy);
        z3::expr_vector ite_builder(*p_z3_ctx);

        ite_builder.push_back(last_ite);
        for(int i = idx_vals.size()-2; i >= 0; --i){
            ite_builder.push_back(z3::ite(ite_bool[i], mem_smt[i], ite_builder[ite_builder.size()-1]));
        }
      
        z3::expr deref = ite_builder[ite_builder.size()-1]; 

        for(size_t i = 0; i < idx_vals.size(); ++i){
            BaseVariable* tmp = p_memory->get_variable_by_mem_pos(base_ptr_location + i);
            tmp->set_smt_formula(deref);
        }

        src->insert_index(idx_vals[0]);

        src->add_index_base_pointer(index_base_ptr);
    } catch (z3::exception const & ex){
        throw YassiException(ex.msg());
    }
}

/**
 * @brief Dummy Function for Function Pointer Calls
 * 
 * @param fp_var Function Pointer Address
 * @return void*
 */
void* PointerInstruction::function_pointer_hook(BaseVariable* fp_var)
{
    nullpointer_check(fp_var);
    assertion_check(fp_var->is_function_pointer());
    
    std::string fn_name = fp_var->get_value_as_string();

    p_logger->function_pointer(fn_name);
    std::string backend_bin = this->get_bin_dir() + "/" + this->get_bin_name();
    std::string objdump = this->get_bin_dir() + "objdump.txt";
    
    std::stringstream cmd;
    cmd << "objdump -t " << backend_bin << " | grep " << fn_name << " > " << objdump;
    system(cmd.str().c_str());
    
    std::vector<std::string> dump_file;
    std::string line;
    std::ifstream in_file(objdump);
    while(std::getline(in_file, line)){
        dump_file.push_back(line);
    }
    in_file.close();
    
    std::string information;
    if(dump_file.size() == 0){
        throw YassiException("Empty Object Dump Function Pointer!");
    } else if (dump_file.size() == 1){
        information = dump_file[0]; 
        
    // For the case that there are object files which have a similiar name to the function pointer
    } else{
        size_t hits = 0;
        size_t line = 0;
        for(size_t i = 0; i < dump_file.size(); ++i){
            if(dump_file[i].find(".cpp") == std::string::npos){
                line = i;
                hits++;
            }   
        }
        if(hits > 1){
            throw YassiException("Could not find function pointer address!");
        }
        information = dump_file[line];
    }
    
    information = information.substr(0, information.find(" "));
   
    size_t address;
    std::stringstream ss;
    ss << std::hex << information;
    ss >> address;
    
    remove(objdump.c_str());
    return reinterpret_cast<void*>(address);
}

/**
 * @brief Check Constant GEP Instruction for Exceptions
 * 
 * @param dst Variable to Load Result into
 * @param pointer Pointer to the Datastructure
 * @param indexes Offset Variables 
 * @param _offset_tree Offset Tree showing the Memory Allignment of the Data
 */
void PointerInstruction::check_constant_gep(BaseVariable* dst,
                                            BaseVariable* pointer,
                                            std::vector<BaseVariable *> const & indexes,
                                            std::string const & _offset_tree)
{
    (void) dst;
    (void) _offset_tree;
    
    std::list<int> idx;
    for(auto itor: indexes){
        idx.push_back(itor->get_value_ui32());
    }
 
    BaseVariable* var = pointer->get_pointer();
    nullpointer_check(var);
  
    std::cout << var->get_allocation_type() << std::endl;
    if(var->get_allocation_type() == eHeapAllocated){
    
    } else if (var->get_allocation_type() == eStack){
    
    } else {
        throw YassiNotImplemented("");
    }
}

/**
 * @brief Check Non Constant GEP Instruction for Exceptions
 * 
 * @param dst_var Variable to Load Result into
 * @param pointer_var Pointer to the Datastructure
 * @param index_vars Offset Variables 
 * @param _offset_tree Offset Tree showing the Memory Allignment of the Data
 */
void PointerInstruction::check_non_constant_gep(BaseVariable* dst_var,
                                                BaseVariable* pointer_var,
                                                std::vector<BaseVariable *> const & indexes,
                                                std::string const & _offset_tree)
{
    (void) dst_var;
    (void) pointer_var;
    (void) indexes;
    (void) _offset_tree;
}
