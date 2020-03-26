/** 
 * @file yassi_allsat.cpp
 * @brief This class realizes AllSAT for Pointer Instructions
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
#include "yassi_allsat.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param z3_ctx Z3 Context
 */
AllSAT::AllSAT(z3::context* z3_ctx):
    Object()
{
    nullpointer_check(z3_ctx);

    p_z3_ctx = z3_ctx;
    p_solver = new z3::solver(*p_z3_ctx);
}

/**
 * @brief Destructor
 */
AllSAT::~AllSAT()
{
    delete p_solver;    p_solver = nullptr;
}

/**
 * @brief Set SMT Instance to run AllSAT for
 * 
 * @param expr The BaseVariable holding the SMT Instance
 */
void AllSAT::set_smt_instance(BaseVariable* expr)
{
    nullpointer_check(expr);

    p_solver->reset();
    p_expr = expr;
    p_allsat_var = expr->get_propagated_from()->get_name();
    p_solver->add(expr->get_smt_formula());
}

/**
 * @brief Execute AllSAT
 */
void AllSAT::run()
{
    try {
        //
        // NOTE: Please note, that AllSAT has been implemented for just
        //       one variable at the moment.
        //
        p_allsat_values.clear();

        for(;;){
            z3::check_result sat = p_solver->check();
            this->dump_to_filesystem();
            //
            // Insert Result and Exclude it for the next run
            //
            if(sat == z3::check_result::sat){
                z3::model results = p_solver->get_model();

                if(results.size() == 0){
                    throw YassiException("AllSAT: No FreeVariable in SAT Instance!");
                }

                for(size_t i = 0; i < results.size(); ++i){
                    if(p_allsat_var.compare(results[i].name().str()) == 0){
                        z3::func_decl res = results[i];

                        size_t possible_val =  results.get_const_interp(res).get_numeral_int64();
                        z3::expr excl_val = p_z3_ctx->bv_val(possible_val, 32);
                        p_allsat_values.push_back(possible_val);
                        
                        z3::expr orig = results[i].operator()();
                        z3::expr excl = orig != excl_val;
                        p_solver->add(excl);
                    }
                }

                //
                // No (more) sat results, we are done here
                //
            } else {
                break;
            }
        }

    } catch(z3::exception const & exp){
    throw YassiException(exp.msg());
    }
}

/**
 * @brief Get the Results for AllSAT
 * 
 * @return std::vector< size_t >
 */
std::vector<size_t> AllSAT::get_results()
{
    std::sort(p_allsat_values.begin(), p_allsat_values.end());
    return p_allsat_values;
}

/**
 * @brief Dump the SMT Instance to the filesystem for debugging purpose
 */
void AllSAT::dump_to_filesystem()
{
    static int cnt = 0;
    std::string filename = this->get_smt_dir() + std::string("allsat_problem_") + std::to_string(cnt) + ".smt2";

    std::fstream out_file(filename, std::ios::out);
    out_file << *p_solver << std::endl;
    out_file << "(check-sat)" << std::endl;
    out_file << ("(get-model)") << std::endl;
    out_file << "(get-value(" << p_allsat_var << "))" << std::endl;
    out_file.close();

    cnt++;
}
