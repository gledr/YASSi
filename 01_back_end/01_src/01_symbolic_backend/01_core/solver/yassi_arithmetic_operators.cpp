#include "yassi_arithmetic_operators.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
ArithmeticOperators::ArithmeticOperators(z3::context* z3_ctx,
                                         z3::solver* z3_slv):
    Object(), p_smt_result(z3_ctx->bool_const(0))
{
    nullpointer_check(z3_ctx);
    nullpointer_check(z3_slv);

    p_z3_ctx = z3_ctx;
    p_z3_slv = z3_slv;

    p_run_time_exception = new RunTimeException();
}

/**
 * @brief Destructor
 */
ArithmeticOperators::~ArithmeticOperators()
{
    delete p_run_time_exception;    p_run_time_exception = nullptr;
}

/**
 * @brief Perform a Calculation with Real and Symbolic Values
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 * @param op:  The operation to perform
 */
void ArithmeticOperators::calculate(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2,
                                    LLVMOpcode const & op)
{    
    switch (op) {
    case LLVMAdd: {
        this->int_add (dst, op1, op2);
        break;
    }
    case LLVMFAdd: {
        this->float_add (dst, op1, op2);
        break;
    }
    case LLVMSub: {
        this->int_sub (dst, op1, op2);
        break;
    }
    case LLVMFSub: {
        this->float_sub (dst, op1, op2);
        break;
    }
    case LLVMMul: {
        this->int_mul (dst, op1, op2);
        break;
    }
    case LLVMFMul: {
        this->float_mul (dst, op1, op2);
        break;
    }
    case LLVMOr: {
        this->or_op (dst, op1, op2);
        break;
    }
    case LLVMAnd: {
        this->and_op (dst, op1, op2);
        break;
    }
    case LLVMAShr: {
        this->arith_shift_right (dst, op1, op2);
        break;
    }
    case LLVMLShr: {
        this->logic_shift_right (dst, op1, op2);
        break;
    }
    case LLVMXor: {
        this->xor_op (dst, op1, op2);
        break;
    }
    case LLVMUDiv: {
        this->int_unsigned_div (dst, op1, op2);
        break;
    }
    case LLVMSDiv: {
        this->int_signed_div (dst, op1, op2);
        break;
    }
    case LLVMFDiv: {
        this->float_div (dst, op1, op2);
        break;
    }
    case LLVMShl: {
        this->shift_left (dst, op1, op2);
        break;
    }
    case LLVMFRem: {
        this->float_rem (dst, op1, op2);
        break;
    }
    case LLVMSRem: {
        this->int_signed_rem (dst, op1, op2);
        break;
    }
    case LLVMURem: {
        this->int_unsigned_rem (dst, op1, op2);
        break;
    }
    default: {
        throw YassiNotImplemented("Unknown ArithmeticOperator detected!");
    }
    }
}

/**
 * @brief Resolve the sign of the arithmetic operators to signed
 * 
 * @param dst dst: The destination object
 * @param op1 op1: The compare operator 1
 * @param op2 op2: The compare operator 2
 */
void ArithmeticOperators::set_signed(Variables::BaseVariable* dst,
                                     Variables::BaseVariable* op1,
                                     Variables::BaseVariable* op2)
{
    this->arith_pre(dst, op1, op2);

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
 * @brief Resolve the sign of the arithmetic operators to unsigned
 * 
 * @param dst dst: The destination object
 * @param op1 op1: The compare operator 1
 * @param op2 op2: The compare operator 2
 */
void ArithmeticOperators::set_unsigned(Variables::BaseVariable* dst,
                                       Variables::BaseVariable* op1,
                                       Variables::BaseVariable* op2)
{ 
    this->arith_pre(dst, op1, op2);

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

/**
 * @brief Perform a logic AND of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::and_op(Variables::BaseVariable* dst,
                                 Variables::BaseVariable* op1,
                                 Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() & op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() & op2->get_value_i8());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() & op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() & op2->get_value_i8());
        }
    } else if (dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() & op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() & op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() & op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() & op2->get_value_i64());
        }
    } else {
        throw YassiException("Unknown Datatype for And Operation Detected!");
    }

    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() & op2->get_smt_formula());

    this->arith_post(dst, op1, op2);
}

/**
 * @brief Set value and SMT formula
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::arith_post(Variables::BaseVariable* dst,
                                     Variables::BaseVariable* op1,
                                     Variables::BaseVariable* op2) 
{
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);

    if(op1->get_is_linear() && op2->get_is_linear()){
        dst->set_value(p_arith_result);
    } else {
        dst->set_value(p_arith_result);
        dst->set_smt_formula(p_smt_result);
    }
}

/**
 * @brief Check for nullpointer objects
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::arith_pre(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);
}

/**
 * @brief
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::arith_shift_right(Variables::BaseVariable* dst,
                                            Variables::BaseVariable* op1,
                                            Variables::BaseVariable* op2) 
{
    /**
     * C/C++ Only offers the >> Operator which implements the  Arithmetic Shift
     * However, if an Arithmetic Shift occurs it can be seen as an hint for a Signed Datatype
     */ 
    
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        p_arith_result = std::to_string(op1->get_value_i8() >> op2->get_value_i8());
    } else if (dst->get_type()->is_int16()){
        p_arith_result = std::to_string(op1->get_value_i16() >> op2->get_value_i16());
    } else if (dst->get_type()->is_int32()){
        p_arith_result = std::to_string(op1->get_value_i32() >> op2->get_value_i32());
    } else if (dst->get_type()->is_int64()){
        p_arith_result = std::to_string(op1->get_value_i64() >> op2->get_value_i64());
    } else {
        throw YassiException("Unknown Datatype for Arithmetic Shift Right Detected");
    }

    this->set_signed(dst, op1, op2);
    p_smt_result = z3::ashr(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst,op1, op2);
}

/**
 * @brief Perform a floating point addition of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::float_add(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);

    if(dst->get_type()->is_float()){
        p_arith_result = std::to_string(op1->get_value_single_precision() + op2->get_value_single_precision());
    } else if (dst->get_type()->is_double()) {
        p_arith_result = std::to_string(op1->get_value_double_precision() + op2->get_value_double_precision());
    } else {
        throw YassiException("Unknown Datatype for Float Addition Detetcted!");
    }

    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() + op2->get_smt_formula());

    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a floating point division of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::float_div(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_real_zero_division(op2);

    if(dst->get_type()->is_float()){
        p_arith_result = std::to_string(op1->get_value_single_precision() / op2->get_value_single_precision());
    } else if (dst->get_type()->is_double()){
        p_arith_result = std::to_string(op1->get_value_single_precision() / op2->get_value_single_precision());
    } else {
        throw YassiException("Unknown Datatype for Float Division Detected!");
    }

    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() / op2->get_smt_formula());

    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a floating point multiplication of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::float_mul(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_double()){
        p_arith_result = std::to_string(op1->get_value_double_precision() * op2->get_value_double_precision());
    } else if (dst->get_type()->is_float()){
        p_arith_result = std::to_string(op1->get_value_single_precision() * op2->get_value_single_precision());
    } else {
        throw YassiException("Unknown Datatype for Float Multiplication Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() * op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Performa a floating point remainder operation of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::float_rem(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_real_zero_rem(op2);
       
    if(dst->get_type()->is_float()){
        p_arith_result = std::to_string(fmod(op1->get_value_single_precision(), op2->get_value_single_precision()));
    } else if (dst->get_type()->is_double()) {
        p_arith_result = std::to_string(fmod(op1->get_value_double_precision(), op2->get_value_double_precision()));
    } else {
        throw YassiException("Unknown Datatype for Float Remainder Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::rem(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a floating point subtraction of op1 and op2
 *
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::float_sub(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_float()){
        p_arith_result = std::to_string(op1->get_value_single_precision() - op2->get_value_single_precision());
    } else if (dst->get_type()->is_double()){
        p_arith_result = std::to_string(op1->get_value_double_precision() - op2->get_value_double_precision());
    } else {
        throw YassiException("Unknown Datatype for Float Subtraction Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = op1->get_smt_formula() - op2->get_smt_formula();
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform an integer addition of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_add(Variables::BaseVariable* dst,
                                  Variables::BaseVariable* op1,
                                  Variables::BaseVariable* op2)
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() + op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() + op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() + op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() + op2->get_value_i16());
        }
     } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() + op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() + op2->get_value_i64());
        }
     } else if (dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() + op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() + op2->get_value_i8());
        }
    } else {
        throw YassiException("Unknown Datatype for Integer Addition Detected!");
    }
    
    p_smt_result = op1->get_smt_formula() + op2->get_smt_formula();
    
    this->set_signed_unsigned(dst, op1, op2);
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform an integer multiplication of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_mul(Variables::BaseVariable* dst,
                                  Variables::BaseVariable* op1,
                                  Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
     if(dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() * op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() * op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() * op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() * op2->get_value_i16());
        }
     } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() * op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() * op2->get_value_i64());
        }
     } else if (dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() * op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() * op2->get_value_i8());
        }
    } else {
        throw YassiException("Unknown Datatype for Integer Multiplication Detected!");
    }
    
    p_smt_result = op1->get_smt_formula() * op2->get_smt_formula();
    
    this->set_signed_unsigned(dst, op1, op2);
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a signed integer remainder operation of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_signed_rem(Variables::BaseVariable* dst,
                                         Variables::BaseVariable* op1,
                                         Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_integer_zero_rem(op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        p_arith_result = std::to_string(op1->get_value_i8() % op2->get_value_i8());
    } else if (dst->get_type()->is_int16()){
        p_arith_result = std::to_string(op1->get_value_i16() % op2->get_value_i16());
    } else if (dst->get_type()->is_int32()){
        p_arith_result = std::to_string(op1->get_value_i32() % op2->get_value_i32());
    } else if (dst->get_type()->is_int64()){
        p_arith_result = std::to_string(op1->get_value_i64() % op2->get_value_i64());
    } else {
        throw YassiException("Unknown Datatype for Integer Signed Remainder Detected!");
    }
    
    this->set_signed(dst, op1, op2);
    p_smt_result = z3::srem(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform an unsigned integer remainder operation of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_unsigned_rem(Variables::BaseVariable* dst,
                                           Variables::BaseVariable* op1,
                                           Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_integer_zero_rem(op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
         p_arith_result = std::to_string(op1->get_value_ui8() % op2->get_value_ui8());
    } else if (dst->get_type()->is_int16()){
         p_arith_result = std::to_string(op1->get_value_ui16() % op2->get_value_ui16());
    } else if (dst->get_type()->is_int32()){
        p_arith_result = std::to_string(op1->get_value_ui32() % op2->get_value_ui32());
    } else if (dst->get_type()->is_int64()){
        p_arith_result = std::to_string(op1->get_value_ui64() % op2->get_value_ui64());
    } else {
        throw YassiException("Unknown Datatype for Integer Unsigned Remainder Detected!");
    }
   
    this->set_unsigned(dst, op1, op2);
    p_smt_result = z3::urem(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform an integer subtraction of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_sub(Variables::BaseVariable* dst,
                                  Variables::BaseVariable* op1,
                                  Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() - op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() - op2->get_value_i8());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() - op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() - op2->get_value_i16());
        }
    } else if (dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() - op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() - op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() - op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() - op2->get_value_i64());
        }
    } else {
        throw YassiException("Unknown Datatype for Integer Subtraction Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = op1->get_smt_formula() - op2->get_smt_formula();
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform an unsigned integer division of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_unsigned_div(Variables::BaseVariable* dst,
                                           Variables::BaseVariable* op1,
                                           Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_integer_zero_division(op2);
    
    if(op2->get_value_i64() != 0){
        if (dst->get_type()->is_int1() || dst->get_type()->is_int8()){
            p_arith_result = std::to_string(op1->get_value_ui8() / op2->get_value_ui8());
        } else if (dst->get_type()->is_int16()){
            p_arith_result = std::to_string(op1->get_value_ui16() / op2->get_value_ui16());
        } else if (dst->get_type()->is_int32()){
            p_arith_result = std::to_string(op1->get_value_ui32() / op2->get_value_ui32());
        } else if (dst->get_type()->is_int64()){
            p_arith_result = std::to_string(op1->get_value_ui64() / op2->get_value_ui64());
        } else {
            throw YassiException("Unknown Datatype for Unsigned Integer Division Detected!");
        }
    }
    
    this->set_unsigned(dst, op1, op2);
    p_smt_result = z3::udiv(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a signed integer division of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::int_signed_div(Variables::BaseVariable* dst,
                                         Variables::BaseVariable* op1,
                                         Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    this->check_integer_zero_division(op2);
    
    if(op2->get_value_i64() != 0){
        if (dst->get_type()->is_int1() || dst->get_type()->is_int8()){
            p_arith_result = std::to_string(op1->get_value_i8() / op2->get_value_i8());
        } else if (dst->get_type()->is_int16()){
            p_arith_result = std::to_string(op1->get_value_i16() / op2->get_value_i16());
        } else if (dst->get_type()->is_int32()){
            p_arith_result = std::to_string(op1->get_value_i32() / op2->get_value_i32());
        } else if (dst->get_type()->is_int64()){
            p_arith_result = std::to_string(op1->get_value_i64() / op2->get_value_i64());
        } else {
            throw YassiException("Unknown Datatype for Signed Integer Division Detected!");
        }
    }
    
    this->set_signed(dst, op1, op2);
    p_smt_result = op1->get_smt_formula() / op2->get_smt_formula();
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a logic shift right right of op1 by op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::logic_shift_right(Variables::BaseVariable* dst,
                                            Variables::BaseVariable* op1,
                                            Variables::BaseVariable* op2) 
{
    /*
     * C/C++ don't support Logic Shift Right (>> ends up in an arithmetic shift)
     * For our purpose we handle Logic Shifts as Unsigned Values 
     */ 
    
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        p_arith_result = std::to_string(op1->get_value_ui8() >> op2->get_value_ui8());
    } else if (dst->get_type()->is_int16()){
        p_arith_result = std::to_string(op1->get_value_ui16() >> op2->get_value_ui16());
    } else if (dst->get_type()->is_int32()){
        p_arith_result = std::to_string(op1->get_value_ui32() >> op2->get_value_ui32());
    } else if (dst->get_type()->is_int64()){
        p_arith_result = std::to_string(op1->get_value_ui64() >> op2->get_value_ui64());
    } else {
        throw YassiException("Unknown Datatype for Logic Shift Right Detected!");
    }
    
    this->set_unsigned(dst, op1, op2);
    p_smt_result = z3::lshr(op1->get_smt_formula(), op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a logic or operation of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::or_op(Variables::BaseVariable* dst,
                                Variables::BaseVariable* op1,
                                Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() | op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() | op2->get_value_i8());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() | op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() | op2->get_value_i16());
        }
    } else if (dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() | op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() | op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() | op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() | op2->get_value_i64());
        }
    } else {
        throw YassiException("Unknown Datatype for Or Operation Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() | op2->get_smt_formula());
    
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a shift left operation of op1 by op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::shift_left(Variables::BaseVariable* dst,
                                     Variables::BaseVariable* op1,
                                     Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() << op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() << op2->get_value_i8());
        }
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() << op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() << op2->get_value_i16());
        }
    } else if (dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() << op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() << op2->get_value_i32());
        }
    } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() << op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() << op2->get_value_i64());
        }
    } else {
        throw YassiException("Unknown Datatype for Shift Left Operation!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::shl(op1->get_smt_formula(), op2->get_smt_formula());
  
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Perform a logic xor operation of op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::xor_op(Variables::BaseVariable* dst,
                                 Variables::BaseVariable* op1,
                                 Variables::BaseVariable* op2) 
{
    this->arith_pre(dst, op1, op2);
    
    if(dst->get_type()->is_int1() || dst->get_type()->is_int8()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui8() ^ op2->get_value_ui8());
        } else {
            p_arith_result = std::to_string(op1->get_value_i8() ^ op2->get_value_i8());
        }        
    } else if (dst->get_type()->is_int16()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui16() ^ op2->get_value_ui16());
        } else {
            p_arith_result = std::to_string(op1->get_value_i16() ^ op2->get_value_i16());
        } 
    } else if (dst->get_type()->is_int32()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui32() ^ op2->get_value_ui32());
        } else {
            p_arith_result = std::to_string(op1->get_value_i32() ^ op2->get_value_i32());
        } 
    } else if (dst->get_type()->is_int64()){
        if(this->is_unsigned(op1, op2)){
            p_arith_result = std::to_string(op1->get_value_ui64() ^ op2->get_value_ui64());
        } else {
            p_arith_result = std::to_string(op1->get_value_i64() ^ op2->get_value_i64());
        } 
    } else {
        throw YassiException("Unknown Datatype for Xor Operation Detected!");
    }
    
    this->set_signed_unsigned(dst, op1, op2);
    p_smt_result = z3::expr(op1->get_smt_formula() ^ op2->get_smt_formula());
    this->arith_post(dst, op1, op2);
}

/**
 * @brief Check is one of both operators is unsigned
 * 
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 * @return bool
 */
bool ArithmeticOperators::is_unsigned(Variables::BaseVariable* op1,
                                      Variables::BaseVariable* op2)
{
    nullpointer_check(op1);
    nullpointer_check(op2);
    
    return op1->get_sign() == eUnsigned || op2->get_sign() == eUnsigned;
}

/**
 * @brief Set destination signed/unsigned according to op1 and op2
 * 
 * @param dst: The Destination Object
 * @param op1: The first Operator Object
 * @param op2: The second Operator Object
 */
void ArithmeticOperators::set_signed_unsigned(Variables::BaseVariable* dst,
                                              Variables::BaseVariable* op1,
                                              Variables::BaseVariable* op2)
{
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);
    
    if(op1->get_sign() == eUnsigned || op2->get_sign() == eUnsigned){
        dst->set_sign(eUnsigned);
        if(dst->is_propaged_constant()){
            dst->get_propagated_from()->set_sign(eUnsigned);
        }
    } else if (op1->get_sign() == eSigned || op2->get_sign() == eSigned) {
        dst->set_sign(eSigned);
        if(dst->is_propaged_constant()){
            dst->get_propagated_from()->set_sign(eSigned);
        }
    } else {
        // No need to handle Unknown sign here
    }
}

/*************************************************************************************************/
/*                                                                                               */
/*                                                                                               */
/*                                          Checker Functions                                    */
/*                                                                                               */
/*                                                                                               */
/*************************************************************************************************/

/**
 * @brief Make sure that no division by zero is possible
 * 
 * @param denominator: The object containing the denominator
 */
void ArithmeticOperators::check_integer_zero_division(Variables::BaseVariable* denominator)
{
    nullpointer_check(denominator);
    
    p_z3_slv->push();
    z3::expr zero = p_z3_ctx->bv_val(0,  denominator->get_type()->get_bits());
    z3::expr zero_check = denominator->get_smt_formula() == zero;
    p_z3_slv->add(zero_check);

    z3::check_result result = p_z3_slv->check();
    
    if(result == z3::check_result::sat){
       p_run_time_exception->trigger_exception(e_divide_by_zero);
    }

    p_z3_slv->pop();
}

/**
 * @brief Make sure that no division by zero is possible
 * 
 * @param denominator: The object containing the denominator
 */
void ArithmeticOperators::check_real_zero_division(Variables::BaseVariable* denominator)
{
    nullpointer_check(denominator);
    
    notimplemented_check();
}

/**
 * @brief Make sure that no remainder by zero is possible
 * 
 * @param base: The object containing the divider
 */
void ArithmeticOperators::check_integer_zero_rem(Variables::BaseVariable* base)
{
    nullpointer_check(base);

    p_z3_slv->push();
    z3::expr zero = p_z3_ctx->bv_val(0,  base->get_type()->get_bits());
    z3::expr zero_check = base->get_smt_formula() == zero;
    p_z3_slv->add(zero_check);

    z3::check_result result = p_z3_slv->check();

    if(result == z3::check_result::sat){
       p_run_time_exception->trigger_exception(e_rem_zero);
    }
    
    p_z3_slv->pop();
}

/**
 * @brief Make sure that no remainder by zero is possible
 * 
 * @param base: The object containing the divider
 */
void ArithmeticOperators::check_real_zero_rem(Variables::BaseVariable* base)
{
    nullpointer_check(base);

    notimplemented_check();
}
