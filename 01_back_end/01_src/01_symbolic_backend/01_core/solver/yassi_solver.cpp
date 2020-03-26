/** 
 * @file yassi_solver.cpp
 * @brief Solve SMT Problems using the Z3 Library
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
#include "yassi_solver.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param database: Pointer to the database object
 * @param z3_ctx:   Pointer to the current solver context
 * @param z3_slv:   Pointer to the current solver state
 */
Solver::Solver(Database* database,
               z3::context* z3_ctx,
               z3::solver* z3_slv):
    Object(),
    p_database(database),
    p_z3_ctx(z3_ctx),
    p_z3_slv(z3_slv)
{
    nullpointer_check(database);
    nullpointer_check(z3_ctx);
    nullpointer_check(z3_slv);

    p_memory = Memory::getInstance(z3_ctx);
    p_sat = z3::check_result::unknown;
    p_fpa = new FloatingPointArithmetic();
}

/**
 * @brief Destructor
 */
Solver::~Solver()
{
    delete p_fpa;   p_fpa = nullptr;
                    p_z3_ctx = nullptr;
                    p_z3_slv = nullptr;
                    p_database = nullptr;
}

/**
 * @brief Handle the solver result of an integer type.
 * 
 * @param expr: The solver result.
 * @param var:  The variable to store the result to.
 */
void Solver::handle_integer_type(z3::expr& expr,
                                 BaseVariable* var)
{
    nullpointer_check(var);

    BaseType* type = var->get_type();
    if(var->get_sign() == eSigned || var->get_sign() == eUnknown){
        if(type->is_int1()){
            bool a = expr.get_numeral_int64();
            var->set_value_free_variable(std::to_string(a));
        } else if (type->is_int8()){
            int8_t val = expr.get_numeral_int64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int16()){
            int16_t val = expr.get_numeral_int64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int32()){
            int32_t val = expr.get_numeral_int64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int64()){
            int64_t val = expr.get_numeral_int64();
            var->set_value_free_variable(std::to_string(val));
        } else {
            throw YassiException("Unknown Signed IntegerType Detected!");
        }
    } else {
        if(type->is_int1()){
            bool a = expr.get_numeral_uint64();
            var->set_value_free_variable(std::to_string(a));
        } else if (type->is_int8()){
            uint8_t val = expr.get_numeral_uint64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int16()){
            uint16_t val = expr.get_numeral_uint64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int32()){
            uint32_t val = expr.get_numeral_uint64();
            var->set_value_free_variable(std::to_string(val));
        } else if (type->is_int64()){
            uint64_t val = expr.get_numeral_uint64();
            var->set_value_free_variable(std::to_string(val));
        } else {
            throw YassiException("Unknown Unsigned IntegerType Detected!");
        }
    }
}

/**
 * @brief Handle the solver result of a pointer type.
 * 
 * @param expr: The solver result.
 * @param var:  The variable to store the result to.
 */
void Solver::handle_pointer_type(z3::expr & expr,
                                 BaseVariable* var)
{
    nullpointer_check(var);

    int64_t val = expr.get_numeral_uint64();
    var->set_value_free_variable(std::to_string(val));
}

/**
 * @brief Handle the solver result of a real type.
 * 
 * @param expr: The solver result.
 * @param var:  The variable to store the result to.
 */
void Solver::handle_real_type(z3::expr& expr,
                              BaseVariable* var)
{
    nullpointer_check(var);

    long exponent;
    unsigned long significant;
    int sign;
    Z3_context ctx = *p_z3_ctx;

    Z3_fpa_get_numeral_sign(ctx,expr.decl()(), &sign);
    Z3_fpa_get_numeral_exponent_int64(ctx, expr.decl()(), &exponent, true);
    Z3_fpa_get_numeral_significand_uint64(ctx, expr.decl()(), &significant);
    
    std::string clear_value;
    if(var->get_type()->is_float()){
        clear_value = p_fpa->single_precision_to_string(sign, exponent, significant);
    } else if (var->get_type()->is_double()){
        clear_value = p_fpa->double_precision_to_string(sign, exponent, significant);
    } else {
        throw YassiNotSupported("Type not supported!");
    }
    var->set_value_free_variable(clear_value);
}

/**
 * @brief Solve an existing SMT Problem by calling the SMT Solver.
 */
void Solver::solve_problem()
{
    try {
        // Bounded Model Checking - Set a max depth
        if(p_z3_slv->assertions().size() > Object::get_max_depth()){
            p_sat = z3::check_result::unknown;
            std::cout << "Bound Reached!" << std::endl;
            return;
        }

        if(this->get_dump_smt()){
            this->dump_problem_to_directory();
        }

        p_sat = p_z3_slv->check();
        if(p_sat == z3::check_result::sat) {
            z3::model model = p_z3_slv->get_model();
            if(model.size() > 0){
                // Set Variable for Free Variables
                for(auto& free_var : p_memory->get_free_variables()) {
                    for(size_t i = 0; i < model.size(); ++i){
                        if(free_var->get_name().compare(model[i].name().str()) == 0){
                            if(free_var->get_type()->is_integer_class()){
                                auto tmp = model.eval(free_var->get_formula_to_evaluate());
                                this->handle_integer_type(tmp, free_var);
                            } else if(free_var->get_type()->is_real_class()) {
                                auto tmp = model.eval(free_var->get_formula_to_evaluate());
                                this->handle_real_type(tmp, free_var);
                            } else if (free_var->get_type()->is_pointer()){
                                auto tmp = model.eval(free_var->get_formula_to_evaluate());
                                this->handle_pointer_type(tmp, free_var);
                            } else {
                                std::cout << free_var->get_type()->get_type_identifier() << std::endl;
                                assert (0 &&  "Type not supported");
                            }
                        }
                    }
                }
            }
        }
    } catch (std::exception const & exp){
        std::cerr << exp.what() << std::endl;
        assert (0 && "Caught exception in Solver::solve_problem");
    } catch (z3::exception const & exp) {
        std::cerr << exp.msg() << std::endl;
        assert (0 && "Caught exception in Solver::solve_problem");
    }
}

/**
 * @brief Dump the existing SMT Problem to the filesystem for debugging.
 */
void Solver::dump_problem_to_directory()
{
    try {
        size_t problem_id = p_database->get_problem_num();
        std::string filename = this->get_smt_dir() + "smt_problem_" + std::to_string(problem_id) + ".smt2";
        std::ofstream out_file(filename);
        out_file << *p_z3_slv << std::endl;
        out_file << "(check-sat)" << std::endl;
        out_file << ("(get-model)") << std::endl;
        for (auto itor : p_memory->get_free_variables()) {
            if (itor->used()) {
                out_file << "(get-value(" << itor->get_name() << "))" << std::endl;
            }
        }
        out_file.close();
    } catch (std::exception const & exp) {
        std::cout << exp.what() << std::endl;
        assert (0);
    }
}

/**
 * @brief Check if the last problem could be solved.
 * 
 * @return bool
 */
bool Solver::sat()
{
    return p_sat == z3::check_result::sat;
}

/**
 * @brief Get the collected assertions of the current solver state.
 * 
 * @return Vector of Assertions as std::string
 */
std::vector<std::string> Solver::get_assertions_smt2()
{
    z3::expr_vector assertions = p_z3_slv->assertions();
    std::vector<std::string> retval;

    for(size_t i = 0; i < assertions.size(); ++i){
        std::stringstream tmp;
        tmp << assertions[i];
        retval.push_back(tmp.str());
    }
    return retval;
}

/**
 * @brief Get the collected assertions of the current solver state.
 * 
 * @return std::string of concated Assertions.
 */
std::string Solver::get_assertions_smt2_concat()
{
    std::string retval;
    
    for(auto itor: this->get_assertions_smt2()){
        retval += itor;
        retval += ",";
    }
    return retval;
}

/**
 * @brief Insert the variables used in the SMT instance into the database.
 */
void Solver::insert_variables_to_db()
{
    std::vector<BaseVariable*> vars = p_memory->get_variables();

    for(auto var: vars){
        assert (var != nullptr);
        std::string name = var->get_name();
        std::string hint; 
        if(var->get_parent() != nullptr){
            hint = var->get_parent()->get_name_hint();
        }
        std::string type = var->get_type()->get_type_identifier();
        bool        free = var->is_free_variable() || var->is_forced_free();
        
        p_database->insert_variable(name,
                                    hint,
                                    type,
                                    free,
                                    var->get_sign() == eSign::eUnsigned);
    }
}

/**
 * @brief Insert explored problems into the database.
 */
void Solver::insert_problem_to_db() 
{
    std::stringstream query;
    
    // The result might be SAT, UNSAT or UNKNOWN
    std::string status = p_sat == z3::check_result::sat ? "1" : "0";

    p_database->insert_problem(status, Object::p_path_stack.to_string());
    this->insert_variables_to_db();

    if(p_sat == z3::check_result::sat){
        int id = p_database->get_problem_num();
        for(auto& it : p_memory->get_free_variables()){
            if(it->used()){
                query.str("");
                std::string name  = it->get_name();
                std::string hint;
                if(it->get_parent() != nullptr){
                    hint  = it->get_parent()->get_name_hint();
                } else {
                    hint  = it->get_name_hint();
                }
                std::string value = it->get_value_as_string();
                p_database->insert_result(name, value, hint, std::to_string(id));
            }
        }
    }
}
