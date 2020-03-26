/** 
 * @file yassi_symbolicexecutor.cpp
 * @brief Symbolic Execution Core Class
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
#include "yassi_symbolicexecutor.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param database: Access to the global database
 * @param z3_ctx:   Access to the z3 context
 * @param z3_slv:   Access to the z3 solver
 */
SymbolicExecutor::SymbolicExecutor(Database* database,
                                   z3::context* z3_ctx,
                                   z3::solver* z3_slv):
    Object()
{
    nullpointer_check(database);
    nullpointer_check(z3_ctx);
    nullpointer_check(z3_slv);

    p_database              = database;
    p_z3_ctx                = z3_ctx;
    p_z3_slv                = z3_slv;
    p_type_factory          = new TypeFactory();
    p_memory                = Memory::getInstance(p_z3_ctx);
    p_var_factory           = new VariableFactory(p_z3_ctx);
    p_problem               = new Solver(p_database, p_z3_ctx, p_z3_slv);
    p_propagation           = new Propagation();
    p_logger                = Logger::getInstance();
    p_type_cast             = new TypeCast(p_z3_ctx);
    p_cmp_operators         = new CompareOperators(p_z3_ctx);
    p_arith_operators       = new ArithmeticOperators(p_z3_ctx, p_z3_slv);
    p_pointer_instr         = new PointerInstruction(p_z3_ctx);
    p_mem_export            = new MemoryExporter(p_z3_ctx);
    p_load_store            = new LoadStore(p_z3_ctx, p_pointer_instr);
    p_force_free            = new ForceFree(p_z3_ctx);
    p_malloc_obj            = nullptr;
}

/**
 * @brief Destructor
 */
SymbolicExecutor::~SymbolicExecutor()
{
    delete p_type_factory;      p_type_factory      = nullptr;
    delete p_var_factory;       p_var_factory       = nullptr;
    delete p_problem;           p_problem           = nullptr;
    delete p_propagation;       p_propagation       = nullptr;
    delete p_type_cast;         p_type_cast         = nullptr;
    delete p_cmp_operators;     p_cmp_operators     = nullptr;
    delete p_arith_operators;   p_arith_operators   = nullptr;
    delete p_pointer_instr;     p_pointer_instr     = nullptr;
    delete p_mem_export;        p_mem_export        = nullptr;
    delete p_load_store;        p_load_store        = nullptr;
    delete p_force_free;        p_force_free        = nullptr;
    Memory::destroy();          p_memory            = nullptr;
}

/**
 * @brief Allocate a new variable (single or collection datatype)
 * 
 * @param name:    Name of the new variable
 * @param subtype: Types included into the new variable (e.g. struct)
 */
void SymbolicExecutor::alloca_instruction(std::string const & name,
                                          std::string const& subtype)
{
    check_namemangling(name);

    std::vector<std::string> types = 
        BaseUtils::tokenize(subtype, NameMangling::VARIABLE_SEPERATOR);
    
    if(types.size() == 1){
        this->alloca_instruction_single(name, types[0]);
    } else {
        size_t cnt = 0;
        for(auto itor : types){
            std::string cnt_name = name;
            if(cnt != 0){
               cnt_name = name + "+" + std::to_string(cnt);
            }
            this->alloca_instruction_single(cnt_name, itor);
            cnt++;
        }
        BaseVariable* first_var = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(name))->get_pointer();
        first_var->set_lastaddress(p_memory->get_last_used_address());
    }
}

/**
 * @brief Allocate a new variable consisting of a single datatype
 * 
 * @param name: Name of the new variable
 * @param type: datatype of the new variable
 */
void SymbolicExecutor::alloca_instruction_single(std::string const & name,
                                                 std::string const & type)
{
    std::vector<std::string> type_structure = BaseUtils::tokenize(type, ":");

    PointerType* ptr_type = p_type_factory->get_pointertype();
    PointerVariable* obj_ptr = p_var_factory->create_pointer_variable(ptr_type, name);

    if(type_structure.size() == 1){
        BaseVariable * var_obj = p_var_factory->create_variable("", type_structure[0]);
        p_memory->alloc_program_variable(obj_ptr, var_obj);

        p_logger->alloca_instr(obj_ptr);
        p_logger->alloca_instr(var_obj);

    } else if (type_structure.size() == 2){
        BaseVariable * var_obj = p_var_factory->create_variable("", type_structure[0]);
        p_memory->alloc_program_variable(obj_ptr, var_obj);

        p_logger->alloca_instr(obj_ptr);
        p_logger->alloca_instr(var_obj);

        BaseVariable* point_to = p_var_factory->create_variable("", type_structure[1]);
        p_memory->alloc_llvm_variable(point_to);
        p_logger->alloca_instr(point_to);
        var_obj->set_pointer(point_to);

    } else {
        notimplemented_check();
    }
}

/**
 * @brief Perform a Binary Instruction (e.g. an ALU Instruction)
 * 
 * @param dst: Destination to store the calculation
 * @param op1: Operand 1
 * @param op2: Operand 2
 * @param op:  Operation to perform
 */
void SymbolicExecutor::binary_instruction(std::string const & dst,
                                          std::string const & op1,
                                          std::string const & op2,
                                          LLVMOpcode const & op) 
{
    try {
        check_namemangling(dst);
        check_namemangling(op1);
        check_namemangling(op2);

        p_logger->binary_instruction(dst, op1, op2, op);

        BaseVariable* var_op1;
        BaseVariable* var_op2;

        if(BaseUtils::is_constant(op1)) {
            var_op1 = p_var_factory->create_variable_from_constant(op1);
        } else {
            var_op1 = p_memory->get_variable_by_name_hint(op1);
        }

        if(BaseUtils::is_constant(op2)) {
            var_op2 = p_var_factory->create_variable_from_constant(op2);
        } else {
            var_op2 = p_memory->get_variable_by_name_hint(op2);
        }

        BaseVariable* dst_op1;
        BaseVariable* dst_op2;

        if(var_op1->get_type()->is_bool_class()){
            dst_op1 = p_var_factory->create_variable(var_op1->get_name_hint(), INTEGER1TYPE);
            p_type_cast->cast_instruction(var_op1, dst_op1, false);
        } else {
            dst_op1 = var_op1;
        }

        if (var_op2->get_type()->is_bool_class()){
            dst_op2 = p_var_factory->create_variable(var_op2->get_name_hint(), INTEGER1TYPE);
            p_type_cast->cast_instruction(var_op2, dst_op2, false);
        } else {
            dst_op2 = var_op2;
        }

        BaseVariable* dst_var = p_var_factory->create_variable(dst, dst_op1->get_type()->get_type_identifier());
        p_memory->alloc_llvm_variable(dst_var);
        p_logger->alloca_instr(dst_var);

        p_arith_operators->calculate(dst_var, dst_op1, dst_op2, op);
        p_propagation->propagate_binary(dst_var, dst_op1, dst_op2);
     
    } catch(z3::exception const & exp) {
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Perform a Compare Instruction (e.g. Compare Equal)
 * 
 * @param dst: Destination to store the calculation
 * @param op1: Operand 1
 * @param op2: Operand 2
 * @param op:  Operation to perform
 */
void SymbolicExecutor::compare_instruction(std::string const & dst,
                                           std::string const & op1,
                                           std::string const & op2,
                                           int const & op) 
{
    check_namemangling(dst);
    check_namemangling(op1);
    check_namemangling(op2);

    p_logger->compare_instruction(dst, op1, op2, op);

    BaseVariable* var_op1;
    BaseVariable* var_op2;

    if(p_memory->var_exists(op1)){
        var_op1 = p_memory->get_variable_by_name_hint(op1);
    } else if (BaseUtils::is_constant(op1)){
        var_op1 = p_var_factory->create_variable_from_constant(op1);
    } else {
        throw YassiException("Unknown Behaviour!");
    }

    if(p_memory->var_exists(op2)){
        var_op2 = p_memory->get_variable_by_name_hint(op2);
    } else if (BaseUtils::is_constant(op2)){
        var_op2 = p_var_factory->create_variable_from_constant(op2);
    } else {
        throw YassiException("Unknown Behaviour!");
    }

    BaseVariable* dst_var = p_var_factory->create_variable(dst, BOOLTYPE);
    p_memory->alloc_llvm_variable(dst_var);
    p_logger->alloca_instr(dst_var);

    p_cmp_operators->compare(dst_var, var_op1, var_op2, op);    
    p_propagation->propagate_binary(dst_var, var_op1, var_op2);
}

/**
 * @brief Store Instruction
 * 
 * @param src:  Variable to store
 * @param addr: Address to store the variable to
 */
void SymbolicExecutor::store_instruction(std::string const & src,
                                         std::string const & addr)
{
    check_namemangling(src);
    check_namemangling(addr);

    p_logger->store_instr(src, addr);

    PointerVariable* addr_var = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(addr));
    BaseVariable* src_var = nullptr;
    
    if(!p_memory->var_exists(src)){
        if (BaseUtils::is_constant(src)){
            src_var = p_var_factory->create_variable_from_constant(src);
            src_var->set_parent(addr_var);
            p_memory->alloc_llvm_variable(src_var);
            p_logger->alloca_instr(src_var);
        } else {
            src_var = p_var_factory->create_variable(src, POINTERTYPE);
            src_var->set_funtion_pointer(true);
            p_memory->alloc_llvm_variable(src_var);
            p_logger->alloca_instr(src_var);
        }
    }

    if(Utils::is_function_pointer(src)){
        src_var = p_var_factory->create_variable(src,POINTERTYPE);
        p_memory->alloc_llvm_variable(src_var);
        p_logger->alloca_instr(src_var);
        src_var->set_funtion_pointer(true);
        std::string fn_name = Utils::decode_function_pointer(src_var->get_name_hint());

        src_var->set_value(fn_name);
        addr_var->set_pointer(src_var);

    } else {
        if(src_var == nullptr){
            src_var = p_memory->get_variable_by_name_hint(src);
        }
         if(src.find("___YASSI_malloc") != std::string::npos){
            addr_var->get_pointer()->set_pointer(p_malloc_obj);
        } else {
            src_var->unset_free_variable();
            p_memory->update_free_variables(src_var);

            p_load_store->store_instruction(src_var, addr_var);
        }
    }
}

/**
 * @brief Load Instruction
 * 
 * @param dst:      Destination to load the variable to
 * @param dst_type: Type of the variable to load
 * @param addr:     Address of the variable to load
 */
void SymbolicExecutor::load_instruction(std::string const & dst,
                                        std::string const & dst_type,
                                        std::string const & addr) 
{
    check_namemangling(dst);
    check_namemangling(addr);

    p_logger->load_instr(addr, dst);

    BaseVariable* dst_var = p_var_factory->create_variable(dst, dst_type);
    p_memory->alloc_llvm_variable(dst_var);
    p_logger->alloca_instr(dst_var);

    PointerVariable* addr_var = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(addr));

    p_load_store->load_instruction(dst_var, addr_var);
}

/**
 * @brief Primitive Method to check if stuck in an infinite loop
 * 
 * TODO
 * 
 * @param condition: Current problem to solve
 * @return bool
 */
bool SymbolicExecutor::check_infinite_loop(z3::expr const & condition)
{
    /*
     * >3 out of 5 Detection
     */
    size_t cnt = 0;
    for(auto itor : p_last_assertions){
        if(itor == condition){
            cnt++;
        }
    }

    if(p_last_assertions.size() == 5){
        p_last_assertions.pop_front();
    }
    p_last_assertions.push_back(condition);

    if(cnt > 3){
        //std::cout << "Infinite Loop" << std::endl;
        return true;
    } else {
        return false;
    }
}

/**
 * @brief Conditional Branch Instruction
 * 
 * @param condition: Condition to be fulfilled
 * @param joints: TODO
 * @return bool
 */
bool SymbolicExecutor::conditional_branch_instruction(std::string const & condition,
                                                      std::string const & joints) 
{
    (void) joints;
    check_namemangling(condition);

    try { 
        /*
         * Reject Branch: Negative Branch
         */ 
        if(int pid = fork()) {

            int r = prctl(PR_SET_PDEATHSIG, SIGTERM);
            if (r == -1) {
                std::cerr << "parent has died" << std::endl;
                exit(1); 
            }
            int status;
            waitpid(pid, &status, 0); // Wait for Childprocess to terminate
            
            BaseVariable * comp_var = p_memory->get_variable_by_name_hint(condition);

            if(!comp_var->get_type()->is_bool_class()){
                BaseType* bool_type = p_type_factory->get_booltype(); 
                BaseVariable* bool_cond = p_var_factory->create_bool_variable(bool_type, "");
                p_type_cast->cast_instruction(comp_var, bool_cond, false);
                bool_cond->set_name(comp_var->get_name());
                comp_var = bool_cond;
            }

            nullpointer_check(comp_var);
            bool taken = false;

            if(!comp_var->get_is_linear()){
                z3::expr tmp = comp_var->get_smt_formula();
                z3::expr negation = p_z3_ctx->bool_val(false);
                z3::expr tmp2(tmp == negation);

                if(this->check_infinite_loop(tmp2)){
                    p_problem->insert_problem_to_db();
                    return !taken;
                }
                p_z3_slv->add((tmp2));
                if(comp_var->has_index_assertion()){
                    z3::expr tmp = comp_var->get_smt_formula();
                    z3::expr negation = p_z3_ctx->bool_val(false);
                    z3::expr tmp2(tmp == negation);
                    p_z3_slv->add((tmp2));
                }

                p_problem->solve_problem();
                Object::p_path_stack.push(taken);
                p_problem->insert_problem_to_db();

                p_logger->branch_instruction_conditional(comp_var->get_name_hint(), taken);

                if(!p_problem->sat()){
                    exit(4);
                }

                p_database->insert_branch(comp_var->get_name(), comp_var->get_value_as_string(), p_problem->get_assertions_smt2_concat(), std::to_string(taken));
                return taken;
            } else {
                /*
                 * We don't follow the negative branch when the instance is linear! 
                 */
                exit(0);
            }

        /*
         *  Taken Branch --> Positive Branch
         */
        } else {
            int r = prctl(PR_SET_PDEATHSIG, SIGTERM);
            if (r == -1) {
                std::cerr << "parent has died" << std::endl;
                exit(1); 
            }
            BaseVariable* comp_var = p_memory->get_variable_by_name_hint(condition);
            if(!comp_var->get_type()->is_bool_class()){
                BaseType* bool_type = p_type_factory->get_booltype(); 
                BaseVariable* bool_cond = p_var_factory->create_bool_variable(bool_type, "");
                p_type_cast->cast_instruction(comp_var, bool_cond, false);
                bool_cond->set_name(comp_var->get_name());
                comp_var = bool_cond;
            }
            nullpointer_check(comp_var);
            bool taken = true;

            if(!comp_var->get_is_linear()){
                z3::expr tmp = comp_var->get_smt_formula();

                if(this->check_infinite_loop(tmp)){
                    p_problem->insert_problem_to_db();
                    exit(0);
                }
                p_z3_slv->add(tmp);

                if(comp_var->has_index_assertion()){
                    z3::expr tmp = comp_var->get_index_assertion();
                    p_z3_slv->add((tmp));
                }
                p_problem->solve_problem();
                Object::p_path_stack.push(taken);
                p_problem->insert_problem_to_db();

                p_logger->branch_instruction_conditional(comp_var->get_name_hint(), taken);

                if(!p_problem->sat()){
                    exit(5);
                }

                p_database->insert_branch(comp_var->get_name(), comp_var->get_value_as_string(), p_problem->get_assertions_smt2_concat(), std::to_string(taken));
                return taken;
            } else {
                return comp_var->get_value_bool() == taken;
            }
        }
    } catch (z3::exception const & exp) {
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Initilaize Global Variables
 * 
 * @param name:  Name of the variable(s)
 * @param type:  Identifier of the type(s)
 * @param value: Value(s) to be assigned
 */
void SymbolicExecutor::global_variable_init(std::string const & name,
                                            std::string const & type,
                                            std::string const & value)
{
    check_namemangling(name);

    p_logger->global_variable_init(name, type, value);

    this->alloca_instruction(name, type);
    if(!value.empty()){
        std::vector<std::string> token = BaseUtils::tokenize(value, NameMangling::VARIABLE_SEPERATOR);

        BaseVariable* global_var =  p_memory->get_variable_by_name_hint(name);
        global_var->set_global();

        int mem_pos = global_var->get_pointer()->get_alloc_point();
        for(auto& itor: token){
            std::vector<std::string> values = BaseUtils::tokenize(itor, ":");

            if(values.size() == 1){
                if(BaseUtils::is_constant(itor)){
                    std::string value = BaseUtils::decode_constant(itor);
                    if (BaseUtils::is_uninitialized_value(value)){
                        continue;
                    } else {
                        BaseVariable* tmp = p_var_factory->create_variable_from_constant(itor);
                        BaseVariable* set_val_obj = p_memory->get_variable_by_mem_pos(mem_pos);
                        
                        if(set_val_obj->get_type()->is_pointer()){
                            set_val_obj->set_pointer(p_memory->get_variable_by_mem_pos(tmp->get_value_ui32()));
                        } else {
                            set_val_obj->set_value(tmp->get_value_as_string());
                            set_val_obj->set_global();
                            p_memory->update_free_variables(set_val_obj);
                        }
                    }
                }
                mem_pos++;
            } else if (values.size() == 2){
                std::cerr << "Type 2" << std::endl;

            } else {
                notimplemented_check();
            }
        }
    }
}

/**
 * @brief Type Cast
 * 
 * @param src:   Variable to be casted 
 * @param dst:   Destination to save the new variable to
 * @param types: Destination type after cast
 * @param sext:  Apply sign extension
 */
void SymbolicExecutor::cast_instruction(std::string const & src,
                                        std::string const & dst,
                                        std::string const & types_string,
                                        bool const sext)
{
    check_namemangling(src);
    check_namemangling(dst);

    std::vector<std::string> types = BaseUtils::tokenize(types_string, ":");
    assertion_check (types.size() > 0);

    if(types.size() == 1){
        p_logger->cast_instr(src, dst, types[0], sext);

        BaseVariable * src_var = p_memory->get_variable_by_name_hint(src);
        BaseVariable* dst_var = p_var_factory->create_variable(dst, types[0]);

        p_memory->alloc_llvm_variable(dst_var);
        p_logger->alloca_instr(dst_var);
        p_type_cast->cast_instruction(src_var, dst_var, sext);

    } else if (types.size() == 2){
        p_logger->cast_instr(src, dst, types[1], sext);

        BaseVariable* src_var = p_memory->get_variable_by_name_hint(src);
        BaseVariable* dst_ptr = p_var_factory->create_variable(dst, types[0]);
        BaseVariable* dst_var = p_var_factory->create_variable("", types[1]);
        
        dst_ptr->set_pointer(dst_var);

        p_memory->alloc_llvm_variable(dst_ptr);
        p_memory->alloc_llvm_variable(dst_var);
        p_logger->alloca_instr(dst_ptr);
        p_logger->alloca_instr(dst_var);

        p_type_cast->cast_instruction(src_var, dst_ptr, sext);

    } else {
        notimplemented_check();
    }
}

/**
 * @brief Function Call
 * 
 * @param oplist:   Parameters to call the function with
 * @param returnto: Register to store the return value
 */
void SymbolicExecutor::call_instruction(std::vector<std::string> const & oplist,
                                        std::string const & returnto) 
{
    check_namemangling(oplist);
    check_namemangling(returnto);

    p_logger->call_instr(returnto, oplist);

    p_function_call_arguments.clear();
    for(auto& itor: oplist){
        // Must only happen for function pointer as argument!
        if(BaseUtils::is_constant(itor)){
            BaseVariable* constant = p_var_factory->create_variable_from_constant(itor);
            p_function_call_arguments.push_back(constant);
        } else {
            if(!p_memory->var_exists(itor)){
                this->alloca_instruction(itor, POINTERTYPE);
                PointerVariable* tmp = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(itor));
                tmp->set_funtion_pointer(true);
            }
            p_function_call_arguments.push_back(p_memory->get_variable_by_name_hint(itor));
        }
    }

    p_caller_function_register.push(returnto);
}

/**
 * @brief Call Instruction Post
 * 
 * @param fn_name:  Function Ending
 * @param ret_type: Return Type
 * @param caller:   Function called the other Function
 */
void SymbolicExecutor::call_instruction_post(std::string const & fn_name,
                                             std::string const & ret_type,
                                             std::string const & caller)
{
    p_logger->call_instr_post(fn_name, ret_type, caller);
    std::string resolved_name = fn_name;

    if(Utils::is_register(fn_name)){
        BaseVariable* function_pointer = p_memory->get_variable_by_name_hint(fn_name)->get_pointer();
        resolved_name = function_pointer->get_value_as_string();
    }

    if(p_database->is_internal_function(resolved_name)){
        this->call_instruction_post_instrumented(resolved_name, ret_type);
    } else if (p_database->is_external_function(resolved_name)){
        this->call_instruction_post_non_instrumented(resolved_name, ret_type);
    } else {
        throw YassiException("This Must not Happen!");
    }

    p_caller_function_register.pop();
}

/**
 * @brief Call Instruction Post (Instrumented Functions)
 * 
 * @param function_name Function Ending
 * @param ret_type      Return Type
 */
void SymbolicExecutor::call_instruction_post_instrumented(std::string const & function_name,
                                                          std::string const & ret_type)
{
    (void) function_name;

    /*
     * LLVM allocates a register and uses this register to return.
     * When the return type is void, the is no such register allocated.
     */ 
    if(ret_type != VOIDTYPE){
        BaseVariable* ret_reg = p_var_factory->create_variable(p_caller_function_register.top(), ret_type);
        p_memory->alloc_llvm_variable(ret_reg);
        
        BaseVariable* caller_var = p_memory->get_variable_by_name_hint(p_caller_function_register.top());
        BaseVariable* return_var = p_memory->get_variable_by_name_hint(p_function_return_register.back());

        this->assign_instruction(return_var, caller_var);
    }

    p_function_return_register.pop_back();
}

/**
 * @brief Call Instruction Post (Non-Instrumented)
 * 
 * @param function_name: Function Ending
 * @param ret_type:      Return Type
 */
void SymbolicExecutor::call_instruction_post_non_instrumented(std::string const & function_name,
                                                              std::string const & ret_type)
{
    p_non_annotated_function_calls[function_name]++;
    BaseVariable* retVal = p_var_factory->create_variable(p_caller_function_register.top(), ret_type);
    nullpointer_check(retVal);

    retVal->set_comes_from_nonannoated(true);
    p_memory->alloc_program_variable(nullptr, retVal);

    if(function_name == "__YASSI_malloc"){
        nullpointer_check(p_malloc_obj);
        retVal->set_pointer(p_malloc_obj);
    }

    p_logger->alloca_instr(retVal);
}

/**
 * @brief Begin the Execution of a Function
 * 
 * @param function_name: Name of the Function
 * @param oplist:        Argumen List of the Function
 */
void SymbolicExecutor::begin_function(std::string const & function_name,
                                      std::vector<std::string> const & oplist) 
{
    check_namemangling(oplist);

    p_logger->begin_function(function_name, oplist);

    if(function_name.compare("main") == 0){
         std::string global_return = this->get_file_being_executed() + "%main%register%retval";
        p_function_return_register.push_back(global_return);
    }

    assertion_check (oplist.size() == p_function_call_arguments.size());

    for(size_t i = 0; i < oplist.size(); ++i){
        BaseVariable* parameter;
        if(p_function_call_arguments[i]->is_constant()){
            parameter = p_var_factory->create_variable_from_constant(p_function_call_arguments[i]->get_name_hint());
        } else {
            parameter = p_memory->get_variable_by_name_hint(p_function_call_arguments[i]->get_name_hint());
        }

        size_t variable_mem = parameter->get_lastaddress() - parameter->get_firstaddress();
        size_t type_mem = parameter->get_type()->get_bytes();

        // If there is a container used as parameter we have to split the container up into it's parts
        if(variable_mem > type_mem){
           size_t first_addr = p_function_call_arguments[i]->get_firstaddress();
           size_t const last_addr = p_function_call_arguments[i]->get_lastaddress();
           size_t pos = p_memory->get_variable_by_name_hint(p_function_call_arguments[i]->get_name_hint())->get_alloc_point();

           size_t element_cnt = 0;
           while(first_addr < last_addr){
                BaseVariable* element = p_memory->get_variable_by_mem_pos(pos);

                if(element_cnt > 0){
                    BaseVariable* tmp = p_var_factory->create_variable(oplist[i] + "+" + std::to_string(element_cnt), element->get_type()->get_type_identifier());
                    p_memory->alloc_llvm_variable(tmp);
                } else {
                    BaseVariable* tmp = p_var_factory->create_variable(oplist[i], element->get_type()->get_type_identifier());
                    p_memory->alloc_llvm_variable(tmp);
                }

                size_t pos_to = p_memory->get_variable_by_name_hint(oplist[i])->get_alloc_point() + element_cnt;
                
                this->assign_instruction(p_memory->get_variable_by_mem_pos(pos), p_memory->get_variable_by_mem_pos(pos_to));
                element_cnt++;
                pos++;
                first_addr += element->get_type()->get_bytes();
            }
        } else {
            BaseVariable* tmp = p_var_factory->create_variable(oplist[i], p_function_call_arguments[i]->get_type()->get_type_identifier());
            p_memory->alloc_llvm_variable(tmp);

            BaseVariable* call_arg = p_function_call_arguments[i];
            BaseVariable* oplist_arg = p_memory->get_variable_by_name_hint(oplist[i]);
            PointerVariable* call_arg_ptr = dynamic_cast<PointerVariable*>(p_function_call_arguments[i]);

            if(call_arg_ptr && call_arg_ptr->is_function_pointer()){
                this->assign_function_pointer(call_arg_ptr, oplist_arg);
            } else {
                this->assign_instruction(call_arg, oplist_arg);
            }
        }
    }
}

/**
 * @brief Function Ending
 */
void SymbolicExecutor::end_function()
{
    p_memory->clean_memory(this->get_file_being_executed(), this->get_current_function(), p_function_return_register);
    p_logger->end_function(this->get_current_function());
}

/**
 * @brief Return Instruction
 * 
 * @param return_name: Name of the the Register beeing returned
 */
void SymbolicExecutor::return_instruction(std::string const & return_name)
{
    check_namemangling(return_name);

    BaseVariable* ret_var = nullptr;
    if(BaseUtils::is_constant(return_name)){
        ret_var = p_var_factory->create_variable_from_constant(return_name);
    } else {
        ret_var = p_memory->get_variable_by_name_hint(return_name);
    }

    nullpointer_check(ret_var);
    p_logger->return_instr(ret_var);

    p_function_return_register.push_back(return_name);
}

/**
 * @brief Selecti Instruction (If-Then-Else)
 *
 * @param dst:  Register to Store Result
 * @param cond: Condition
 * @param sel1: Option 1
 * @param sel2: Option 2
 */
void SymbolicExecutor::select_instruction(std::string const & dst,
                                          std::string const & cond,
                                          std::string const & sel1,
                                          std::string const & sel2)
{
    try {
        check_namemangling(dst);
        check_namemangling(cond);
        check_namemangling(sel1);
        check_namemangling(sel2);

        static std::vector<z3::expr> ite;

        p_logger->select(dst, cond, sel1, sel2);

        BaseVariable* cond_var = p_memory->get_variable_by_name_hint(cond);
        BaseVariable* sel1_var = p_memory->get_variable_by_name_hint(sel1);
        BaseVariable* sel2_var = p_memory->get_variable_by_name_hint(sel2);
        BoolVariable* bool_cond_var = p_var_factory->create_bool_variable(p_type_factory->get_booltype(), "bool" + cond);

        p_type_cast->to_bool(dynamic_cast<IntegerVariable*>(cond_var), bool_cond_var);
        nullpointer_check(bool_cond_var);
        assertion_check (bool_cond_var->get_type()->is_bool_class());

        BaseVariable* casted_sel1_var = nullptr;
        if(sel2_var->get_type()->is_bool_class() && sel1_var->get_type()->is_integer_class()){
            casted_sel1_var = p_var_factory->create_bool_variable(p_type_factory->get_booltype(), "bool" + sel1);
            p_type_cast->to_bool(dynamic_cast<IntegerVariable*>(sel1_var), dynamic_cast<BoolVariable*>(casted_sel1_var));
        } else if (sel1_var->get_type()->get_type_identifier() == sel2_var->get_type()->get_type_identifier()){
            casted_sel1_var = sel1_var;
        }
        nullpointer_check(casted_sel1_var);

        BaseType* target_type = sel2_var->get_type();
        BaseVariable* dst_var = p_var_factory->create_variable(dst, target_type->get_type_identifier());
        p_memory->alloc_llvm_variable(dst_var);
        dst_var->unset_free_variable();
        p_memory->update_free_variables(dst_var);

        ite.push_back(z3::ite(bool_cond_var->get_smt_formula(), casted_sel1_var->get_smt_formula(), sel2_var->get_smt_formula())); 
        dst_var->set_smt_formula(ite.back());
        p_propagation->propagate_binary(dst_var, sel1_var, sel2_var);

    } catch (z3::exception const & exp){
        std::cerr << "Z3 Exception caught!" << std::endl;
        std::cerr << exp.msg() << std::endl;
    }
}

/**
 * @brief Simulation Starting
 */
void SymbolicExecutor::begin_simulation()
{
    p_logger->begin_simulation();
}

/**
 * @brief Simulation Ending
 */
void SymbolicExecutor::end_simulation()
{
    p_logger->end_simulation();

    Object::add_path_element("end_sim");

    p_database->insert_trace(Object::get_path_history());

    if(Object::get_dump_memory()){
        p_mem_export->export_memory();
    }
}

/**
 * @brief Function Pointer Hook
 * 
 * @param fp_register: Register Holding the Address of the Function
 * @return void*
 */
void* SymbolicExecutor::function_pointer_hook(std::string const & fp_register)
{
    check_namemangling(fp_register);

    BaseVariable* fp_obj = p_memory->get_variable_by_name_hint(fp_register)->get_pointer();

    return p_pointer_instr->function_pointer_hook(fp_obj);
}

/**
 * @brief Copy a block of memory 
 *
 * @param addr_dst: Pointer to the beginning of the destination memory block
 * @param addr_src: Pointer to the beginning of the source memory block
 * @param size_bytes: Bytes to copy in total
 * @param align: Internal memory alignment used
 * @param is_volatile:
 */
void SymbolicExecutor::memcpy(std::string const & addr_dst,
                              std::string const & addr_src,
                              std::string const & size_bytes,
                              std::string const & align,
                              std::string const & is_volatile)
{
    (void) is_volatile;
    
    check_namemangling(addr_dst);
    check_namemangling(addr_src);

    PointerVariable* dst_pointer = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(addr_dst));
    PointerVariable* src_pointer = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(addr_src));
    BaseVariable* size_obj = p_var_factory->create_variable_from_constant(size_bytes);
    BaseVariable* align_obj = p_var_factory->create_variable_from_constant(align);
    
    p_memory->memcpy(src_pointer, dst_pointer, size_obj->get_value_ui32());
    

    p_logger->memcpy(addr_src, addr_dst, size_obj->get_value_as_string(), align_obj->get_value_as_string());
}

/**
 * @brief Memory Set: Set a block of Memory to a given Value
 * 
 * @param addr_dst:     Pointer to the begin of the block
 * @param val:          Value to set
 * @param len:          Block Len
 * @param align:        Block Alignment
 * @param _is_volatile: Volatile Memory
 */
void SymbolicExecutor::memset(std::string const & addr_dst,
                              std::string const & val,
                              std::string const & len,
                              std::string const & align,
                              std::string const & _is_volatile) 
{
    PointerVariable* dst_obj = dynamic_cast<PointerVariable*>(p_memory->get_variable_by_name_hint(addr_dst));
    BaseVariable* val_obj = p_var_factory->create_variable_from_constant(val);
    BaseVariable* len_obj = p_var_factory->create_variable_from_constant(len);
    BaseVariable* align_obj = p_var_factory->create_variable_from_constant(align);
    BaseVariable* is_volatile_obj = p_var_factory->create_variable_from_constant(_is_volatile);

    (void) align_obj;

    p_memory->memset(dst_obj, val_obj->get_value_ui32(), len_obj->get_value_ui32());
    
    p_logger->memset(dst_obj->get_name_hint(),
                     val_obj->get_value_as_string(),
                     len_obj->get_value_as_string(),
                     is_volatile_obj->get_value_as_string());
}

/**
 * @brief Assign Register to Register
 * 
 * @param src_var: Source Register
 * @param dst_var: Target Register
 */
void SymbolicExecutor::assign_instruction(BaseVariable* src_var, BaseVariable* dst_var)
{
   nullpointer_check(src_var);
   nullpointer_check(dst_var);

   assertion_check(src_var->get_type()->get_type_identifier() == dst_var->get_type()->get_type_identifier());
   
    if(Utils::is_register(src_var->get_name_hint())  || src_var->is_constant() || Utils::is_global(src_var->get_name_hint())){
        p_logger->assign_instr(src_var, dst_var);

        if(src_var->get_comes_from_nonannotated()){
            // Use the return value of a non annotated function call 
            src_var->unset_free_variable();
            dst_var->set_force_free();
            
            p_memory->update_free_variables(src_var);
            p_memory->update_free_variables(dst_var);
        } else {
            if(dst_var->get_type()->is_pointer() && src_var->get_type()->is_pointer()){
                PointerVariable* src_ptr = dynamic_cast<PointerVariable*>(src_var);
                if(src_ptr->is_function_pointer()){
                    dst_var->set_pointer(src_var);
                } else {
                    if(src_var->get_pointer() != nullptr){
                        dst_var->set_pointer(src_var->get_pointer());
                    } else {
                        dst_var->set_pointer(src_var);
                    }
                }
                p_propagation->propagate_unary(src_var, dst_var);
            } else if (src_var->get_type()->is_pointer()){
                dst_var->set_value(src_var->get_pointer()->get_value_as_string());
                dst_var->set_smt_formula(src_var->get_pointer()->get_smt_formula());
                p_propagation->propagate_unary(src_var->get_pointer(), dst_var);
            } else if (dst_var->get_type()->is_pointer()){
                if(src_var->is_constant()){
                    dst_var->set_value(src_var->get_value_as_string());
                    dst_var->set_smt_formula(src_var->get_smt_formula());
                    p_propagation->propagate_unary(src_var, dst_var->get_pointer());
                } else if(dst_var->get_pointer() != nullptr){
                    dst_var->get_pointer()->set_value(src_var->get_value_as_string());
                    dst_var->get_pointer()->set_smt_formula(src_var->get_smt_formula());
                   
                } else {
                    dst_var->set_pointer(src_var);
                    dst_var->unset_free_variable();
                    p_memory->update_free_variables(dst_var);
                }
            } else {
                dst_var->set_value(src_var->get_value_as_string());
                dst_var->set_smt_formula(src_var->get_smt_formula());
                p_propagation->propagate_unary(src_var, dst_var);
            }
        }
    } else {
        notsupported_check("Unknown Assign Instruction");
    }
}

/**
 * @brief Assign Function Pointer Register
 * 
 * @param src_var: Source Register
 * @param dst_var: Target Register
 */
void SymbolicExecutor::assign_function_pointer(BaseVariable* src_var, BaseVariable* dst_var)
{
    nullpointer_check(src_var);
    nullpointer_check(dst_var);
    
    PointerVariable* dst_var_fp = dynamic_cast<PointerVariable*>(dst_var);
    dst_var_fp->set_funtion_pointer(true);
    std::vector<std::string> token = BaseUtils::tokenize(src_var->get_name_hint(), NameMangling::MANGELING_SEPERATOR);
    std::string demangled_fn = token[3];
    dst_var_fp->set_value(demangled_fn);
}

/**
 * @brief Get Element Pointer Instruction (Access Datatype)
 * 
 * @param dst:          Target to store to
 * @param pointer:      Pointer to the memory block
 * @param indexes:      Index to access
 * @param offset_tree:  Offset Tree (Internal Memory Structure)
 */
void SymbolicExecutor::getelementptr(std::string const & dst,
                                     std::string const & pointer,
                                     std::vector<std::string> const & indexes,
                                     std::string const & offset_tree)
{
    check_namemangling(dst);
    check_namemangling(pointer);
    check_namemangling(indexes);

    BaseVariable* dst_var = p_var_factory->create_variable(dst, POINTERTYPE);
    p_memory->alloc_llvm_variable(dst_var);
    p_logger->alloca_instr(dst_var);
    
    BaseVariable* pointer_var = p_memory->get_variable_by_name_hint(pointer);

    std::vector<BaseVariable*> index_vars;
    
    for(auto& itor : indexes){
        if(BaseUtils::is_constant(itor)){
            BaseVariable* tmp = p_var_factory->create_variable_from_constant(itor);
            index_vars.push_back(tmp);
        } else {
            BaseVariable* tmp = p_memory->get_variable_by_name_hint(itor);
            index_vars.push_back(tmp);
        }
    }

    p_pointer_instr->getelementptr(dst_var, pointer_var, index_vars, offset_tree);
}

/**
 * @brief Set a variable force free - Always part of the SMT instance
 * 
 * @param variable: The source code variable to be free
 */ 
void SymbolicExecutor::__YASSI_force_free(std::string const & variable, size_t const size) 
{
    check_namemangling(variable);
    
    BaseVariable* var = p_memory->get_variable_by_name_hint(variable);

    p_force_free->force_free_variable(var, size);
}

/**
 * @brief Force an assertion to be true
 *
 * @param _register: Register holding the SMT Instance
 */
void SymbolicExecutor::__YASSI_force_assertion(std::string const & _register)
{
    check_namemangling(_register);

    IntegerVariable* assertion = dynamic_cast<IntegerVariable*>(p_memory->get_variable_by_name_hint(_register));
    BaseType* bool_type = p_type_factory->get_booltype();
    BoolVariable* bool_assertion = p_var_factory->create_bool_variable(bool_type, "bool_" + _register);
    p_type_cast->to_bool(assertion, bool_assertion);

    p_z3_slv->add(bool_assertion->get_smt_formula());

    if(this->get_error_localization()){
        std::vector<BaseVariable*> select_variables = p_memory->get_select_variables();
        z3::expr_vector sum_expr(*p_z3_ctx);

        for(auto& itor : select_variables){
            BaseVariable* extend = p_var_factory->create_variable("", INTEGER8TYPE);
            p_type_cast->extend_bitvector(dynamic_cast<IntegerVariable*>(itor), dynamic_cast<IntegerVariable*>(extend), false);
            sum_expr.push_back(extend->get_smt_formula());
        }

       z3::expr sum = Z3Utils::mk_add_bv(sum_expr);
       z3::expr one = p_z3_ctx->bv_val(1, 8);

       z3::expr bool_sum = (sum == one);

        p_z3_slv->add(bool_sum);
    }

    p_problem->solve_problem();
    p_problem->insert_problem_to_db();
}

/**
 * @brief Print a Debug Message 
 * 
 * @param message_register: Register Holding the Message
 */
void SymbolicExecutor::__YASSI_debug(std::string const & message_register)
{
    BaseVariable* reg = p_memory->get_variable_by_name_hint(message_register)->get_pointer();

    size_t msg_begin = reg->get_alloc_point();
    size_t const msg_end   = msg_begin + reg->get_lastaddress() - reg->get_firstaddress();

    std::string dump_message;

    while(msg_begin <= msg_end){

    BaseVariable* tmp = p_memory->get_variable_by_mem_pos(msg_begin);  
        size_t ascii_char = tmp->get_value_ui32();
        dump_message += (char)ascii_char;
        msg_begin++;
    }

    p_logger->dump(dump_message);
}

/**
 * @brief Allocate Memory on the Heap
 *
 * @param bytes
 */
void* SymbolicExecutor::__YASSI_malloc(std::string const & argument)
{
    BaseVariable* first_obj = nullptr;
    BaseVariable* last_obj = nullptr;
    BaseType* int8_obj = p_type_factory->get_int8type();
    BaseVariable* bytes_obj = p_var_factory->create_variable_from_constant(argument);
    size_t bytes = bytes_obj->get_value_ui32();

    p_logger->malloc(argument);
    
    for(size_t i = 0; i < bytes; ++i) {
        IntegerVariable* var_obj = p_var_factory->create_integer_variable(int8_obj, "");

        if(i == 0) {
            first_obj = var_obj;
        } else {
            last_obj = var_obj;
        }

        p_memory->malloc(var_obj);
        p_logger->alloca_instr(var_obj);
    }
    
    nullpointer_check(first_obj);
    nullpointer_check(last_obj);

    first_obj->set_lastaddress(last_obj->get_lastaddress());
    p_malloc_obj = first_obj;
    
    return first_obj;
}

/**
 * @brief Free Memory on the Heap
 *
 * @param variable Variable hodling the memory
 */
void SymbolicExecutor::__YASSI_free(std::string const & variable)
{
    p_logger->free(variable);

    BaseVariable* free_me = p_memory->get_variable_by_name_hint(variable);
    p_memory->free(free_me);
}
