/** 
 * @file yassi_intrinsics.cpp
 * @brief This class realizes the Instrinsic Functions for Verification
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
#include "yassi_intrinsics.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param ctx Z3 Context
 * @param slv Z3 Solver
 */
Intrinsics::Intrinsics(z3::context* ctx, z3::solver* slv):
    Object()
{
    nullpointer_check(ctx);
    nullpointer_check(slv);

    p_logger = Logger::getInstance();
    p_memory = Memory::getInstance();
    p_database = new Database(this->get_database_url());
    p_run_time_exception = new RunTimeException();
    p_var_factory = new VariableFactory(ctx);

    p_type_factory = new TypeFactory();
    p_type_cast = new TypeCast(ctx);

    p_z3_ctx = ctx;
    p_z3_slv = slv;
}

/**
 * @brief Destructor
 */
Intrinsics::~Intrinsics()
{
    p_logger = nullptr;
    p_memory = nullptr;
    delete p_database; p_database = nullptr;
    delete p_var_factory; p_var_factory = nullptr;
    delete p_type_factory; p_type_factory = nullptr;
    delete p_type_cast; p_type_cast = nullptr;
}

/**
 * @brief
 * 
 * @return bool
 */
bool Intrinsics::nondet_bool() 
{
    return false;
}

/**
 * @brief
 * 
 * @return char
 */
char Intrinsics::nondet_char() 
{
    return 0;
}

/**
 * @brief
 * 
 * @return int
 */
int Intrinsics::nondet_int() 
{
    return 0;
}

/**
 * @brief
 * 
 * @return long int
 */
long Intrinsics::nondet_long() 
{
    return 0;
}

/**
 * @brief
 * 
 * @return unsigned int
 */
unsigned int Intrinsics::nondet_uint() 
{
    return 0;
}

/**
 * @brief 
 * 
 * @return void*
 */
void* Intrinsics::nondet_pointer() 
{
    return nullptr;
}

/**
 * @brief
 */
void Intrinsics::error()
{
    p_logger->error();
    kill(0, SIGKILL);
}

/**
 * @brief
 * 
 * @param assumption_register:
 */
void Intrinsics::assume(std::string const & assumption_register)
{
    check_namemangling(assumption_register);

    BaseVariable* assumption = p_memory->get_variable_by_name_hint(assumption_register);

    p_logger->assume(assumption_register, assumption->get_smt_formula().to_string());

    if(!assumption->get_type()->is_bool_class()){
        z3::expr a = p_z3_ctx->bv_val(0, 32);
        z3::expr b = assumption->get_smt_formula() > a;
        z3::expr c = z3::ite(b, p_z3_ctx->bool_val(true), p_z3_ctx->bool_val(false));
        z3::expr d = (c == p_z3_ctx->bool_val(true));
        p_z3_slv->add(d);
    } else {
        p_z3_slv->add(assumption->get_smt_formula() == p_z3_ctx->bool_val(true));
    }
}

/**
 * @brief
 * 
 * @param assertion_register:
 */
void Intrinsics::assertion(const std::string& assertion_register) 
{
    check_namemangling(assertion_register);

    IntegerVariable* assertion = dynamic_cast<IntegerVariable*>(p_memory->get_variable_by_name_hint(assertion_register));

    if(assertion->is_constant()){
        int val = assertion->get_value_i32();

        if (val == 0){
            p_run_time_exception->trigger_exception(e_assertion_pass);
        } else {
            p_run_time_exception->trigger_exception(e_assertion_fail);
        }
    } else {
        BaseType* bool_type = p_type_factory->get_booltype();
        BoolVariable* bool_assertion = p_var_factory->create_bool_variable(bool_type, "bool_" + assertion_register);
        p_type_cast->to_bool(assertion, bool_assertion);

        bool check_register = false;
        bool check_inverted_register = false;

        // Step 1: Try if SMT instance is SAT (has to be SAT)
        p_z3_slv->push();
            p_z3_slv->add(bool_assertion->get_smt_formula());
            check_register = p_z3_slv->check();
        p_z3_slv->pop();

        // Step 2: Try if negated SMT instance is SAT (has to be UNSAT)
        p_z3_slv->push();
            z3::expr tmp = bool_assertion->get_smt_formula();
            z3::expr negation = p_z3_ctx->bool_val(false);
            z3::expr tmp2(tmp == negation);
            p_z3_slv->add((tmp2));
            check_inverted_register = p_z3_slv->check();
        p_z3_slv->pop();
    
        // Step 3: Analyze Results
        // Case1: 00
        if(!check_register && !check_inverted_register){
            assert (0 && "Should not be reachable from here");
        }
        // Case2: 01
        else if (!check_register && check_inverted_register){
            // FAIL
           p_run_time_exception->trigger_exception(e_assertion_fail);
        }
        // Case3: 10
        else if (check_register && !check_inverted_register){
            //PASS
            p_run_time_exception->trigger_exception(e_assertion_pass);
        }
        // Case4: 11
        else if (check_register && check_inverted_register){
           // FAIL
            p_run_time_exception->trigger_exception(e_assertion_fail);
        }
        else {
            throw YassiException("Must not happen!");
        }
    }
}
