/** 
 * @file yassi_compare_operators.cpp
 * @brief This class realizes all compare operations
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
#include "yassi_compare_operators.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
CompareOperators::CompareOperators(z3::context* z3_ctx):  
    Object(), p_smt_result(z3_ctx->bool_const(0))
{
    nullpointer_check(z3_ctx);
    
    p_z3_ctx = z3_ctx;
}

/**
 * @brief Destructor
 */
CompareOperators::~CompareOperators() 
{
}

/**
 * @brief Public Compare Function
 * 
 * Compare Two BaseVariable Objects using Operation op
 * 
 * @param dst: The destination object
 * @param op1: The compare operator 1
 * @param op2: The compare operator 2
 * @param op:  The compare operation
 */
void CompareOperators::compare(BaseVariable* dst,
                               BaseVariable* op1,
                               BaseVariable* op2,
                               int const & op) 
{    
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);
  
    bool devel_debug = false;
    
    if(op >= LLVMOpcode::LLVMAdd) {
        this->compare_integer(dst, op1, op2, static_cast<LLVMIntPredicate>(op));
    } else {
        this->compare_real(dst, op1, op2, static_cast<LLVMRealPredicate>(op));
    }
    
    devel_debug && std::cout << p_smt_result << std::endl;
}

/**
 * @brief Compare Two Integer Objects
 * 
 * @param dst_var: Compare Destination Object
 * @param var_op1: Compare Operator 1
 * @param var_op2: Compare Operator 2
 * @param op:      Compare Operation
 */
void CompareOperators::compare_integer(BaseVariable* dst_var,
                                       BaseVariable* var_op1,
                                       BaseVariable* var_op2,
                                       LLVMIntPredicate const & op) 
{
    switch (op) {
        case LLVMIntEQ:         { /* equal */
            this->integer_equal(dst_var, var_op1, var_op2);
            break;
        }

        case LLVMIntNE:       { /* not equal */
            this->integer_unequal(dst_var, var_op1, var_op2);
            break;
        }

        case LLVMIntUGT:      { /* unsigned greater than */
            this->integer_unsigned_greater_than(dst_var, var_op1, var_op2);
            break;
        }
        
        case LLVMIntUGE:      { /* unsigned greater or equal */
            this->integer_unsigned_greater_equal(dst_var, var_op1, var_op2);
            break;
        }

        case LLVMIntULT:      { /* unsigned less than */
            this->integer_unsigned_less_than(dst_var, var_op1, var_op2);
            break;
        }

        case LLVMIntULE:      { /* unsigned less or equal */
            this->integer_unsigned_less_equal(dst_var, var_op1, var_op2);
            break;

        } case LLVMIntSGT:      { /* signed greater than */
            this->integer_signed_greater_than(dst_var, var_op1, var_op2);
            break;

        } case LLVMIntSGE:      { /* signed greater or equal */
            this->integer_signed_greater_equal(dst_var, var_op1, var_op2);
            break;

        } case LLVMIntSLT:      { /* signed less than */
            this->integer_signed_less_than(dst_var, var_op1, var_op2);
            break;
            
        } case LLVMIntSLE:        { /* signed less or equal */
            this->integer_signed_less_equal(dst_var, var_op1, var_op2);
            break;

        } default:              {
            throw YassiNotSupported("Integer Compare Operator Not Supported");
        }
    }
}

/**
 * @brief Compare Two Real Objects
 * 
 * @param dst_var: Compare Destination Object
 * @param var_op1: Compare Operator 1
 * @param var_op2: Compare Operator 2
 * @param op:      Compare Operation
 */
void CompareOperators::compare_real(BaseVariable* dst_var,
                                    BaseVariable* var_op1,
                                    BaseVariable* var_op2,
                                    LLVMRealPredicate const & op) 
{
    switch ( op ) {
    case LLVMRealPredicateFalse: {  /* Always false (always folded) */
        throw YassiNotImplemented("Not implemented yet");
        break;
        
    } case LLVMRealOEQ:              { /* True if ordered and equal */
        this->real_equal(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealOGT:              { /* True if ordered and greater than */
        this->real_greater_than(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealOGE:              { /* True if ordered and greater than or equal */
        this->real_greater_equal(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealOLT:              { /* True if ordered and less than */
        this->real_less_than(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealOLE:              { /* True if ordered and less than or equal */
        this->real_less_equal(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealONE:              { /* True if ordered and operands are unequal */
        this->real_equal(dst_var, var_op1, var_op2);
        break;

    } case LLVMRealORD:              { /* True if ordered (no nans) */
        throw YassiNotImplemented("Not implemented yet");
        break;
        
    } case LLVMRealUNO:              { /* True if unordered: isnan(X) | isnan(Y) */
        notimplemented_check();
        exit(-1);
        
    } case LLVMRealUEQ:              { /* True if unordered or equal */
        notimplemented_check();
        exit(-1);
        
    } case LLVMRealUGT:              { /* True if unordered or greater than */
        this->real_greater_than(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealUGE:              { /* True if unordered, greater than, or equal */
       this->real_greater_equal(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealULT:              { /* True if unordered or less than */
       this->real_less_than(dst_var, var_op1, var_op2);
       break;
       
    } case LLVMRealULE:              { /* True if unordered, less than, or equal */
        this->real_equal(dst_var, var_op1, var_op2);
        break;
        
    } case LLVMRealUNE:              { /* True if unordered or not equal */
        notimplemented_check();
        exit(-1);
        
    } case LLVMRealPredicateTrue:    { /* Always true (always folded) */
        notimplemented_check();
        exit(-1);
        
    } default:                       {
        notimplemented_check();
        exit(-1);
    }
    }
}

/**
 * @brief Check incoming BaseVariable Objects for Null Pointer
 * 
 * @param dst: The destination object
 * @param op1: The compare operator 1
 * @param op2: The compare operator 2
 */
void CompareOperators::compare_pre(BaseVariable* dst,
                                   BaseVariable* op1,
                                   BaseVariable* op2)
{
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);
}

/**
 * @brief Assign the result of the compare operations 
 * 
 * @param dst: The destination object
 * @param op1: The compare operator 1
 * @param op2: The compare operator 2
 */
void CompareOperators::compare_post(BaseVariable* dst,
                                    BaseVariable* op1,
                                    BaseVariable* op2)
{
    compare_pre(dst, op1, op2);
    
    if(op1->get_is_linear() && op2->get_is_linear()){
        dst->set_value(p_logic_result);
    } else {
        dst->set_value(p_logic_result);
        dst->set_smt_formula(p_smt_result);
    }
    
    if(op1->has_index_assertion()){
        dst->set_index_assertion(op1->get_index_assertion());
    } 
    if (op2->has_index_assertion()){
        dst->set_index_assertion(op2->get_index_assertion());
    }
}

/**
 * @brief Resolve the sign of the compare operators to signed
 * 
 * @param dst dst: The destination object
 * @param op1 op1: The compare operator 1
 * @param op2 op2: The compare operator 2
 */
void CompareOperators::set_signed(BaseVariable* dst,
                                  BaseVariable* op1,
                                  BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    
    dst->set_sign(eSigned);
    op1->set_sign(eSigned);
    op2->set_sign(eSigned);
    
    if(op1->get_propagated_from() != nullptr){ 
        op1->get_propagated_from()->set_sign(eSigned);
    }
    if(op2->get_propagated_from() != nullptr){ 
        op2->get_propagated_from()->set_sign(eSigned);
    }
}

/**
 * @brief Resolve the sign of the compare operators to unsigned
 * 
 * @param dst dst: The destination object
 * @param op1 op1: The compare operator 1
 * @param op2 op2: The compare operator 2
 */
void CompareOperators::set_unsigned(BaseVariable* dst,
                                    BaseVariable* op1,
                                    BaseVariable* op2)
{ 
    this->compare_pre(dst, op1, op2);
    
    dst->set_sign(eUnsigned);
    op1->set_sign(eUnsigned);
    op2->set_sign(eUnsigned);
    
    if(op1->get_propagated_from() != nullptr){ 
        op1->get_propagated_from()->set_sign(eUnsigned);
    }
    if(op2->get_propagated_from() != nullptr){ 
        op2->get_propagated_from()->set_sign(eUnsigned);
    }
}

bool CompareOperators::is_unsigned(BaseVariable* op1,
                                   BaseVariable* op2)
{
    nullpointer_check(op1);
    nullpointer_check(op2);
    
    return op1->get_sign() == eUnsigned || op2->get_sign() == eUnsigned;
}

void CompareOperators::set_signed_unsigned(BaseVariable* dst,
                                           BaseVariable* op1,
                                           BaseVariable* op2)
{
    compare_pre(dst, op1, op2);
    
    if(op1->get_sign() == eUnsigned || op2->get_sign() == eUnsigned){
        dst->set_sign(eUnsigned);
    } else if (op1->get_sign() == eSigned || op2->get_sign() == eSigned) {
        dst->set_sign(eSigned);
    } else {
        // No need to handle Unknown sign here
    }
}

/**
 * @brief  * @brief Compare Two Signed Integer For Greater or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_signed_greater_equal(BaseVariable* dst,
                                                    BaseVariable* op1,
                                                    BaseVariable* op2) 
{
    this->compare_pre(dst, op1, op2);
    this->set_signed(dst, op1, op2);
        
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_i8() >= op2->get_value_i8() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_i16() >= op2->get_value_i16() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_i32() >= op2->get_value_i32() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_i64() >= op2->get_value_i64() ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Greater Equal Detected!");
    }
    
    p_smt_result = z3::expr(op1->get_smt_formula() >= op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Integer Objects For Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_equal(BaseVariable* dst,
                                     BaseVariable* op1,
                                     BaseVariable* op2)
{
    try {
        this->compare_pre(dst, op1, op2);
            
        assert (op1->get_type() == op2->get_type());
            
        if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
            if(this->is_unsigned(op1, op2)){
                p_logic_result = (op1->get_value_ui8() == op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i8() == op2->get_value_i8()   ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int16()){
            if(this->is_unsigned(op1, op2)){
                p_logic_result = (op1->get_value_ui16() == op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i16() == op2->get_value_i16()   ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int32()){
            if(this->is_unsigned(op1, op2)){
                p_logic_result = (op1->get_value_ui32() == op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i32() == op2->get_value_i32()   ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int64() || op1->get_type()->is_pointer()){
            if(this->is_unsigned(op1, op2)){
                p_logic_result = (op1->get_value_ui64() == op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i64() == op2->get_value_i64()   ? TAKEN : NOT_TAKEN);
            }
        } else {
            throw YassiException("Unknown Datatype for Integer Equal Detected!");
        }
            
        this->set_signed_unsigned(dst, op1, op2);
        p_smt_result = z3::expr (op1->get_smt_formula() == op2->get_smt_formula());
        
        this->compare_post(dst, op1, op2);
    } catch (z3::exception const & ex){
        std::cerr << ex.msg() << std::endl;
    }
}

/**
 * @brief Compare Two Integer Objects For Unequal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_unequal(BaseVariable* dst,
                                       BaseVariable* op1,
                                       BaseVariable* op2) 
{
    try {
        this->compare_pre(dst, op1, op2);

        assert (op1->get_type() == op2->get_type());

        if (op1->get_type()->is_int1() || op1->get_type()->is_int8()) {
            if (this->is_unsigned(op1, op2)) {
                p_logic_result = (op1->get_value_ui8() != op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i8() != op2->get_value_i8() ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int16()) {
            if (this->is_unsigned(op1, op2)) {
                p_logic_result = (op1->get_value_ui16() != op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i16() != op2->get_value_i16() ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int32()) {
            if (this->is_unsigned(op1, op2)) {
                p_logic_result = (op1->get_value_ui32() != op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i32() != op2->get_value_i32() ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_int64()) {
            if (this->is_unsigned(op1, op2)) {
                p_logic_result = (op1->get_value_ui64() != op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
            } else {
                p_logic_result = (op1->get_value_i64() != op2->get_value_i64() ? TAKEN : NOT_TAKEN);
            }
        } else if (op1->get_type()->is_pointer()) {
            p_logic_result = (op1->get_value_ui64() != op2->get_value_ui64() ? TAKEN : NOT_TAKEN);

        } else {
            throw YassiException("Unknown Datatype for Integer Unequal Detected!");
        }

        this->set_signed_unsigned(dst, op1, op2);
        p_smt_result = z3::expr(op1->get_smt_formula() != op2->get_smt_formula());

        this->compare_post(dst, op1, op2);

    } catch (z3::exception const & exp){
        std::cerr << exp.msg() << std::endl;
        std::cout << op1->get_type()->get_type_identifier() << " " << op1->get_smt_formula().get_sort() << std::endl;
        std::cout << op2->get_type()->get_type_identifier() << " " << op2->get_smt_formula().get_sort() << std::endl;
        assert (0);
    }
}

/**
 * @brief Compare Two Signed Integer For Greater Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_unsigned_greater_than(BaseVariable* dst,
                                                     BaseVariable* op1,
                                                     BaseVariable* op2) 
{
    this->compare_pre(dst, op1, op2);
    this->set_unsigned(dst, op1, op2);
    
    assert (op1->get_type() == op2->get_type());
        
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_ui8() > op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_ui16() > op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_ui32() > op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_ui64() > op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Greater Than Detected!");
    }
    
    p_smt_result = z3::ugt(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Unsigned Integer For Greater or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_unsigned_greater_equal(BaseVariable* dst,
                                                      BaseVariable* op1,
                                                      BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_unsigned(dst, op1, op2);
    
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_ui8() >= op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_ui16() >= op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_ui32() >= op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_ui64() >= op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Greater Equal Detected!");
    }
    
    p_smt_result = z3::uge(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Unsigned Integer For Less Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_unsigned_less_than(BaseVariable* dst,
                                                  BaseVariable* op1,
                                                  BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_unsigned(dst, op1, op2);
    
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_ui8() < op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_ui16() < op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_ui32() < op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_ui64() < op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Less Than Detected!");
    }
    
    p_smt_result = z3::ult(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Unsigned Integer For Less Or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_unsigned_less_equal(BaseVariable* dst,
                                                   BaseVariable* op1,
                                                   BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_unsigned(dst, op1, op2);
   
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_ui8() <= op2->get_value_ui8() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_ui16() <= op2->get_value_ui16() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_ui32() <= op2->get_value_ui32() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_ui64() <= op2->get_value_ui64() ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Less Equal Detected!");
    }
    
    p_smt_result = z3::ule(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Unsigned Integer For Greater Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_signed_greater_than(BaseVariable* dst,
                                                   BaseVariable* op1,
                                                   BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_signed(dst, op1, op2);
    
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_i8() > op2->get_value_i8()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_i16() > op2->get_value_i16()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_i32() > op2->get_value_i32()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_i64() > op2->get_value_i64()   ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Signed Greater Than Detected!");
    }
    
    p_smt_result = z3::expr(op1->get_smt_formula() > op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Signed Integer For Less Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_signed_less_than(BaseVariable* dst,
                                                BaseVariable* op1,
                                                BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_signed(dst, op1, op2);
    
    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_i8() < op2->get_value_i8()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_i16() < op2->get_value_i16()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_i32() < op2->get_value_i32()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_i64() < op2->get_value_i64()   ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Signed Less Than Detected!");
    }
    
    p_smt_result = z3::expr(op1->get_smt_formula() < op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Signed Integer For Less or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::integer_signed_less_equal(BaseVariable* dst,
                                                 BaseVariable* op1,
                                                 BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);
    this->set_signed(dst, op1, op2);

    assert (op1->get_type() == op2->get_type());
    
    if(op1->get_type()->is_int1() || op1->get_type()->is_int8()){
        p_logic_result = (op1->get_value_i8() <= op2->get_value_i8()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int16()){
        p_logic_result = (op1->get_value_i16() <= op2->get_value_i16()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int32()){
        p_logic_result = (op1->get_value_i32() <= op2->get_value_i32()   ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_int64()){
        p_logic_result = (op1->get_value_i64() <= op2->get_value_i64()   ? TAKEN : NOT_TAKEN);
    } else {
        throw YassiException("Unknown Datatype for Integer Signed Less Equal Detected!");
    }
    
    p_smt_result = z3::expr(op1->get_smt_formula() <= op2->get_smt_formula());
    
    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_equal(BaseVariable* dst,
                                  BaseVariable* op1,
                                  BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);

    notimplemented_check();

    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Greater or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_greater_equal(BaseVariable* dst,
                                          BaseVariable* op1,
                                          BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);

    if (op1->get_type()->is_double() && op2->get_type()->is_double() ) {
        p_logic_result = (op1->get_value_double_precision() >= op2->get_value_double_precision() ? TAKEN : NOT_TAKEN );
    } else  {
        assert ( 0 && "Not implemented" );
    }
    p_smt_result = z3::expr (op1->get_smt_formula() >= op2->get_smt_formula());

    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Greater Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_greater_than(BaseVariable* dst,
                                         BaseVariable* op1,
                                         BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);

    if(op1->get_type()->is_float() && op2->get_type()->is_float() ) {
        p_logic_result = (op1->get_value_single_precision() > op2->get_value_single_precision() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_double() && op2->get_type()->is_double()) {
        p_logic_result = (op1->get_value_double_precision() > op2->get_value_double_precision() ? TAKEN : NOT_TAKEN);
    } else {
        assert (0 && "Not implemented yet");
    }
    p_smt_result = z3::expr (op1->get_smt_formula() > op2->get_smt_formula());

    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Less or Equal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_less_equal(BaseVariable* dst,
                                       BaseVariable* op1,
                                       BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);;

    if(op1->get_type()->is_float() && op2->get_type()->is_float() ) {
        p_logic_result = (op1->get_value_single_precision() <= op2->get_value_single_precision() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_double() && op2->get_type()->is_double()) {
        p_logic_result = (op1->get_value_double_precision() <= op2->get_value_double_precision() ? TAKEN : NOT_TAKEN);
    } else {
        assert (0 && "Not implemented yet");
    }
    p_smt_result = z3::expr (op1->get_smt_formula() <= op2->get_smt_formula());

    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Less Than
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_less_than(BaseVariable* dst,
                                      BaseVariable* op1,
                                      BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);

    if(op1->get_type()->is_float() && op2->get_type()->is_float() ) {
        p_logic_result = (op1->get_value_single_precision() < op2->get_value_single_precision() ? TAKEN : NOT_TAKEN);
    } else if (op1->get_type()->is_double() && op2->get_type()->is_double()) {
        p_logic_result = (op1->get_value_double_precision() < op2->get_value_double_precision() ? TAKEN : NOT_TAKEN);
    } else {
        assert (0 && "Not implemented yet");
    }
    p_smt_result = z3::expr (op1->get_smt_formula() < op2->get_smt_formula());

    this->compare_post(dst, op1, op2);
}

/**
 * @brief Compare Two Real Objects for Unequal
 * 
 * @param dst: Compare Destination Object
 * @param op1: Compare Operator 1
 * @param op2: Compare Operator 2
 */
void CompareOperators::real_unequal(BaseVariable* dst,
                                    BaseVariable* op1,
                                    BaseVariable* op2)
{
    this->compare_pre(dst, op1, op2);

    notimplemented_check();
    
    this->compare_post(dst, op1, op2);
}
