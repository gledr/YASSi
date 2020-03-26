/** 
 * @file yassi_typecast.cpp
 * @brief Class realizing Yassi's Typecasts
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
#include "yassi_typecast.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param z3_ctx: Set the z3 context
 */
TypeCast::TypeCast(z3::context* z3_ctx):
    Object()
{
    nullpointer_check(z3_ctx);
    
    p_z3_ctx = z3_ctx;
    p_propagation = new Propagation();
    p_var_factory = new VariableFactory(z3_ctx);
    p_type_factory = new TypeFactory();
    p_memory = Memory::getInstance(p_z3_ctx);
}

/**
 * @brief Destructor
 */
TypeCast::~TypeCast()
{
    delete p_propagation;   p_propagation  = nullptr;
    delete p_var_factory;   p_var_factory  = nullptr;
    delete p_type_factory;  p_type_factory = nullptr;
                            p_memory       = nullptr;
}

/**
 * @brief Cast a variable from the type of the
 *        source to the type of the destination
 * 
 * @param src_var: The variable to be casted
 * @param dst_var  The destination for the cast
 * @param sext:    Apply Sign Extension
 */
void TypeCast::cast_instruction(BaseVariable* src_var,
                                BaseVariable* dst_var,
                                bool const sext)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        dst_var->unset_free_variable();
        p_memory->update_free_variables(dst_var);

        if(src_var->get_type()->is_integer_class() &&
           dst_var->get_type()->is_integer_class()){
            p_propagation->propagate_unary(src_var, dst_var);

            if(dst_var->get_type()->get_bits() > src_var->get_type()->get_bits()){
                this->extend_bitvector(dynamic_cast<IntegerVariable*>(src_var), 
                                       dynamic_cast<IntegerVariable*>(dst_var) ,sext);
            } else if (src_var->get_type()->get_bits() > dst_var->get_type()->get_bits()){
                this->extract_bitvector(src_var, dst_var);
            }
          
        } else if (src_var->get_type()->is_integer_class() &&
                   dst_var->get_type()->is_bool_class()){
            IntegerVariable* int_src = dynamic_cast<IntegerVariable*>(src_var);
            BoolVariable* bool_dst = dynamic_cast<BoolVariable*>(dst_var);
            nullpointer_check(int_src);
            nullpointer_check(bool_dst);
            this->to_bool(int_src, bool_dst);
            
        } else if (src_var->get_type()->is_bool_class() &&
                   dst_var->get_type()->is_integer_class()){
            BoolVariable* bool_src = dynamic_cast<BoolVariable*>(src_var);
            IntegerVariable* int_dst = dynamic_cast<IntegerVariable*>(dst_var);
            nullpointer_check(bool_src);
            nullpointer_check(int_dst);
            this->from_bool(bool_src, int_dst);
            
        } else if (src_var->get_type()->is_integer_class() &&
                   dst_var->get_type()->is_real_class()){
            IntegerVariable* int_src = dynamic_cast<IntegerVariable*>(src_var);
            if(dst_var->get_type()->is_float()){
                RealVariable* float_dst = dynamic_cast<RealVariable*>(dst_var);
                this->int_to_float(int_src, float_dst);
            } else if(dst_var->get_type()->is_double()) {
                RealVariable* double_dst = dynamic_cast<RealVariable*>(dst_var);
                this->int_to_double(int_src, double_dst);
            }
        } else if (src_var->get_type()->is_real_class() &&
                   dst_var->get_type()->is_integer_class()){
            IntegerVariable* int_dst = dynamic_cast<IntegerVariable*>(dst_var);
            if(src_var->get_type()->is_double()){
                RealVariable* double_src = dynamic_cast<RealVariable*>(src_var);
                this->double_to_int(double_src, int_dst);
            } else if (src_var->get_type()->is_float()){
                RealVariable* float_src = dynamic_cast<RealVariable*>(src_var);
                this->float_to_int(float_src, int_dst);
            } else {
                notimplemented_check();
            }
        } else if (src_var->get_type()->is_pointer() &&
                   dst_var->get_type()->is_pointer()){
            PointerVariable* ptr_src = dynamic_cast<PointerVariable*>(src_var);
            PointerVariable* ptr_dst = dynamic_cast<PointerVariable*>(dst_var);

            nullpointer_check(ptr_src->get_pointer());
            nullpointer_check(ptr_dst->get_pointer());

          if (ptr_src->get_allocation_type() == eHeapAllocated){
                size_t origin_alloc_point = ptr_src->get_alloc_point();
                size_t allocated_bytes = ptr_src->get_lastaddress() - ptr_src->get_firstaddress() + 1;
                size_t new_type_size = ptr_dst->get_type()->get_bytes();
                size_t elements = allocated_bytes / new_type_size;
                ptr_dst->set_parent(ptr_src->get_parent());
              
                for(size_t i = 1; i < elements; ++i){
                    BaseVariable* concat_elem = p_var_factory->create_variable("", ptr_dst->get_type()->get_type_identifier());
                    p_memory->alloc_llvm_variable(concat_elem);
                    concat_elem->set_parent(p_memory->get_variable_by_mem_pos(origin_alloc_point + i)->get_parent());
                    ptr_dst->set_lastaddress(concat_elem->get_lastaddress());
                }
              
          } else {
                ptr_dst->set_pointer(ptr_src);
          }
        } else {
            notimplemented_check();
        }
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Cast a double variable to an integer
 * 
 * @param src_var: The double variable
 * @param dst_var  The integer variable
 */
void TypeCast::double_to_int(RealVariable* src_var,
                             IntegerVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        Z3_context ctx = *p_z3_ctx;
        Z3_ast src_ast = src_var->get_smt_formula().decl()();
        size_t bits = dst_var->get_type()->get_bits();
        Z3_ast rounding = Z3_mk_fpa_round_nearest_ties_to_even(ctx);

        Z3_ast result =  Z3_mk_fpa_to_sbv(ctx, rounding, src_ast, bits);
        z3::expr result_expr = z3::to_expr(*p_z3_ctx, result);

        assertion_check(result_expr.is_bv());
        dst_var->set_smt_formula(result_expr);
    } catch (z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Cast a float variable to an integer
 * 
 * @param src_var: The float variable
 * @param dst_var  The integer variable
 */
void TypeCast::float_to_int(RealVariable* src_var,
                            IntegerVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        Z3_context ctx = *p_z3_ctx;
        Z3_ast src_ast = src_var->get_smt_formula().decl()();

        size_t bits = src_var->get_type()->get_bits();
        Z3_ast rounding = Z3_mk_fpa_round_nearest_ties_to_even(ctx);
        Z3_ast result =  Z3_mk_fpa_to_sbv(ctx, rounding, src_ast, bits);
        z3::expr result_expr = z3::to_expr(*p_z3_ctx, result);

        assertion_check(result_expr.is_bv());
        dst_var->set_smt_formula(result_expr);
    } catch (z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Cast an integer variable to a float
 * 
 * @param src_var: The integer variable
 * @param dst_var  The float variable
 */
void TypeCast::int_to_float(IntegerVariable* src_var,
                            RealVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        Z3_context ctx = *p_z3_ctx;
        Z3_ast     src_ast = src_var->get_smt_formula().decl()();
        FloatType* fp_type = dynamic_cast<FloatType*>(dst_var->get_type());
        Z3_sort    dst_sort = Z3_mk_fpa_sort(ctx, 
                                             fp_type->get_exponent(),
                                             fp_type->get_fraction());
        
        Z3_ast      result = Z3_mk_fpa_to_fp_bv(ctx, src_ast, dst_sort);
        z3::expr   result_expr = z3::to_expr(*p_z3_ctx, result);

        assertion_check(result_expr.is_fpa());
        dst_var->set_smt_formula(result_expr);
    } catch (z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Cast an integer variable to a double
 * 
 * @param src_var: The integer variable
 * @param dst_var  The double variable
 */
void TypeCast::int_to_double(IntegerVariable* src_var,
                             RealVariable* dst_var)
{   
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        Z3_context ctx = *p_z3_ctx;
        Z3_ast     src_ast = src_var->get_smt_formula().decl()();
        DoubleType* db_type = dynamic_cast<DoubleType*>(dst_var->get_type());
        Z3_sort    dst_sort = Z3_mk_fpa_sort(ctx, db_type->get_exponent(), db_type->get_fraction());
        
        Z3_ast     result = Z3_mk_fpa_to_fp_bv(ctx, src_ast, dst_sort);
        z3::expr   result_expr = z3::to_expr(*p_z3_ctx, result);

        assert (result_expr.is_fpa());
        dst_var->set_smt_formula(result_expr);
    } catch (z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Extend the size of an existing bitvector
 * 
 * @param src_var: The source bitvector
 * @param dst_var: The destination bitvector
 * @param sext:    Apply sign extension
 */
void TypeCast::extend_bitvector (IntegerVariable* src_var,
                                 IntegerVariable* dst_var,
                                 bool const sext)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        /**
         * Miss-matches between Boolean and 1-Bit Vectors are a common challenge
         */
        if(src_var->get_type()->is_int1() && src_var->get_smt_formula().is_bool()){
            BoolType* bool_type = p_type_factory->get_booltype();
            BoolVariable* tmp = p_var_factory->create_bool_variable(bool_type, "");
            tmp->set_smt_formula(src_var->get_smt_formula());
            this->from_bool(tmp, src_var);
        }

        if(src_var->get_type()->get_bits() != src_var->get_smt_formula().get_sort().bv_size()){
            std::cout << src_var->get_type()->get_type_identifier() << std::endl;
            std::cout << src_var->get_smt_formula().get_sort().to_string() << std::endl;
            kill(0, SIGKILL);
            throw YassiException("Inconsistent Variable (Bits of Object and SMT2 Instance) detected!");
        }

        size_t extend_by_bits = dst_var->get_type()->get_bits() - src_var->get_type()->get_bits();
        if (sext) {
            dst_var->set_smt_formula (z3::sext (src_var->get_smt_formula(), extend_by_bits));
        } else {
            dst_var->set_smt_formula (z3::zext (src_var->get_smt_formula(), extend_by_bits));
        }

        assertion_check(dst_var->get_smt_formula().get_sort().bv_size() == dst_var->get_type()->get_bits());

        dst_var->set_value(src_var->get_value_as_string());
    } catch (z3::exception const & ex){
        throw YassiException(ex.msg());
    }
}

/**
 * @brief Extract a part of an existing bitvector
 * 
 * @param src_var: The source bitvector
 * @param dst_var: The destination bitvector
 */
void TypeCast::extract_bitvector (BaseVariable* src_var,
                                  BaseVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        z3::expr src_expr = src_var->get_smt_formula();
        z3::expr cast_expr = src_expr.extract(dst_var->get_type()->get_bits()-1, 0);
        dst_var->set_smt_formula (cast_expr);
        dst_var->set_value(src_var->get_value_as_string());

        assert (dst_var->get_type()->get_bits() == dst_var->get_smt_formula().get_sort().bv_size());
    } catch (z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Cast an integer to bool
 * 
 * @param src_var: The integer variable
 * @param dst_var: The destination bool variable
 */
void TypeCast::to_bool (IntegerVariable* src_var,
                        BoolVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        z3::expr casted(*p_z3_ctx);
        z3::expr src_expr = src_var->get_smt_formula();
        z3::expr zero = p_z3_ctx->bv_val (0, src_var->get_type()->get_bits() );
        z3::expr _false = p_z3_ctx->bool_val(false);
        z3::expr _true = p_z3_ctx->bool_val(true);

        if (src_var->get_type()->get_bits() == 1){
            if(src_var->get_smt_formula().get_sort().is_bool()){
                casted = src_var->get_smt_formula();
            } else {
                z3::expr bigger = z3::ugt(src_expr, zero);
                casted = z3::ite (bigger, _true, _false );
            }
        } else {
            z3::expr bigger =  z3::expr(src_expr > zero);
            casted = z3::ite (bigger, _true, _false );
        }

        assert (casted.is_bool());
        dst_var->set_smt_formula (casted);
    } catch (z3::exception const & ex){
        throw YassiException(ex.msg());
    }
}

/**
 * @brief Cast a bool to an integer
 * 
 * @param src_var: The bool variable
 * @param dst_var: The destination integer variable
 */
void TypeCast::from_bool(BoolVariable* src_var,
                         IntegerVariable* dst_var)
{
    try {
        nullpointer_check(src_var);
        nullpointer_check(dst_var);

        z3::expr one = p_z3_ctx->bv_val(1, dst_var->get_type()->get_bits());
        z3::expr zero = p_z3_ctx->bv_val(0, dst_var->get_type()->get_bits());
        z3::expr ite = z3::ite(src_var->get_smt_formula(), one, zero);
        dst_var->set_smt_formula(ite);
        
    } catch (z3::exception const & ex){
        throw YassiException(ex.msg());
    }
}
