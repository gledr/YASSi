/** 
 * @file yassi_backend.cpp
 * @brief Class Implementing the Backend Interface
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
#include "yassi_backend.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
Backend::Backend():
    Object()
{
    std::string tmp_path = BaseUtils::get_tmp_folder();
    this->set_database_url(tmp_path + "/db/database.db");
    p_database = new Database(this->get_database_url());
    this->options_from_db();

    p_z3_ctx        = new z3::context();
    p_z3_slv        = new z3::solver(*p_z3_ctx);
    p_timer         = new Timer(p_database);
    p_sym_exec      = new SymbolicExecutor(p_database, p_z3_ctx, p_z3_slv);
    p_callstack     = new Callstack();
    p_intrinsics    = new Intrinsics(p_z3_ctx, p_z3_slv);
    p_logger        = Logger::getInstance();

    p_logger->begin_backend(Z3Utils::get_solver_version());
}

/**
 * @brief Destructor
 */
Backend::~Backend()
{
    delete p_database;      p_database = nullptr;
    delete p_callstack;     p_callstack = nullptr;
    delete p_sym_exec;      p_sym_exec = nullptr;
    delete p_timer;         p_timer = nullptr;
    p_z3_slv->reset();
    delete p_z3_slv;        p_z3_slv = nullptr;
    delete p_z3_ctx;        p_z3_ctx = nullptr;

    Logger::destroy();      p_logger = nullptr;
}

/**
 * @brief Initialize Backend Options
 * Read options from database and set flags in Object.
 */
void Backend::options_from_db()
{
    nullpointer_check(p_database);
    std::map<std::string, std::string> options = p_database->get_options();

    Object::set_bin_dir(options["bin_dir"]);
    Object::set_bin_name(options["backend_binary"]);
    Object::set_max_depth(std::stoi(options["max_depth"]));
    Object::set_smt_dir(options["smt_dir"]);
    Object::set_debug(options["verbose"] == "true" ? true : false);
    Object::set_quiet(options["quiet"] == "true" ? true : false);
    Object::set_execution_url(options["execution_url"]);
    Object::set_log_file_enabled(options["log_file_enabled"] == "true" ? true : false);
    Object::set_error_localization(options["error_localization"] == "true" ? true : false);
    Object::set_dump_memory(options["dump_memory"] == "true" ? true : false);
    Object::set_dump_smt(options["dump_smt"] == "true" ? true : false);
    Object::set_timeout(std::stoi(options["timeout"]));
    Object::set_logfile_name(options["logfile_name"]);
}

/**
 * @brief Begin of the symbolic execution (simulation)
 * 
 * @param _source_file: The source file where the simulations starts
 */
 void Backend::begin_sim(char* _source_file) 
{
    nullpointer_check(_source_file);

    Object::set_file_being_executed(_source_file);

    p_timer->start_timer(eBeginSim);

    p_sym_exec->begin_simulation();

    p_timer->end_timer(eBeginSim);
}

/**
 * @brief End of the symbolic execution (simulation)
 */
void Backend::end_sim() 
{
    p_timer->start_timer(eEndSim);

    p_sym_exec->end_simulation();

    p_timer->end_timer(eEndSim);
    p_timer->results_to_db();
}

/**
 * @brief Store the content of a register to an address
 * 
 * @param _addr: The address to store the content
 * @param _src:  The register to store
 * @param _line:
*/
void Backend::store_instr(char* _src, char* _addr, char* _line)
{
    p_timer->start_timer(eStore);

    nullpointer_check(_src);
    nullpointer_check(_addr);
    nullpointer_check(_line);

    std::string decode_line = BaseUtils::decode_constant(_line);
    size_t i_line = std::stoi(decode_line);

    Object::set_line_num_in_execution(i_line);

    p_sym_exec->store_instruction(this->mangle_name(_src), this->mangle_name(_addr));

    p_timer->end_timer(eStore);
}

/**
 * @brief Function Pointer Dummy function.
 * 
 * @param _register_name:  The register holding the address of the function.
 * @return void*
 */
void* Backend::fp_hook(char* _register_name)
{
    nullpointer_check(_register_name);

    return p_sym_exec->function_pointer_hook(this->mangle_name(_register_name));
}

/**
 * @brief Allocate a new register 
 * 
 * @param _name: Name of the pointer to access the register
 * @param _type: Type of the register to allocate
 */
void Backend::alloca_instr(char* _name, char* _type) 
{
    p_timer->start_timer(eAlloca);

    nullpointer_check(_name);
    nullpointer_check(_type);

    p_sym_exec->alloca_instruction(this->mangle_name(_name), _type);

    p_timer->end_timer(eAlloca);
}

/**
 * @brief: Load the content of an address 
 * 
 * @param _dst:      Name of the register to load the pointer content
 * @param _dst_type: Type of the destination register
 * @param _addr:     Pointer to the address to load
 * @param _line:
 */
void Backend::load_instr(char* _dst, char* _dst_type, char* _addr, char* _line) 
{
    p_timer->start_timer(eLoad);

    nullpointer_check(_dst);
    nullpointer_check(_addr);
    nullpointer_check(_dst_type);
    nullpointer_check(_line);

    std::string decode_line = BaseUtils::decode_constant(_line);
    size_t i_line = std::stoi(decode_line);

    this->set_line_num_in_execution(i_line);

    p_sym_exec->load_instruction(this->mangle_name(_dst), _dst_type, this->mangle_name(_addr));

    p_timer->end_timer(eLoad);
}

/**
 * @brief: Compare the content of two registers
 * 
 * @param _dst:  Name of the destination register (may contain true or false) 
 * @param _cmp1: Name of the first compare register
 * @param _cmp2: Name of the second compare register
 * @param _type: Type of comparison to perform
 */
void Backend::cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type)
{
    p_timer->start_timer(eCmp);

    nullpointer_check(_dst);
    nullpointer_check(_cmp1);
    nullpointer_check(_cmp2);
    nullpointer_check(_type);

    p_sym_exec->compare_instruction(this->mangle_name(_dst), this->mangle_name(_cmp1), this->mangle_name(_cmp2), std::stoi(_type));

    p_timer->end_timer(eCmp); 
}

/**
 * @brief Conditional Branch 
 * 
 * @param _cond:   The name of the register holding the branch condition
 * @param _joints: TODO
 * 
 * @return bool
 */
bool Backend::br_instr_cond(char* _cond, char* _joints)
{
    nullpointer_check(_cond);
    nullpointer_check(_joints);

    return p_sym_exec->conditional_branch_instruction(this->mangle_name(_cond), _joints);
}

/**
 * @brief Inconditional Branch Instruction (Goto)
 */
void Backend::br_instr_incond()
{
    // TODO
}

/**
 * @brief Begin a Basic Block
 * 
 * @param _bb: Name of the basic block
 */
void Backend::begin_bb(char* _bb) 
{
    p_timer->start_timer(eBeginBb);

    nullpointer_check(_bb);

    Object::add_path_element(_bb);
    p_logger->begin_bb(_bb);

    p_timer->end_timer(eBeginBb);
}

/**
 * @brief: End a Basic Block
 * 
 * @param _bb: Name of the basic block
 */
void Backend::end_bb(char* _bb) 
{
    p_timer->start_timer(eEndBb);

    nullpointer_check(_bb);

    Object::add_path_element(_bb);
    p_logger->end_bb(_bb);

    p_timer->end_timer(eEndBb);
}

/**
 * @brief Begin the execution of a function
 * 
 * @param _fn_name:     Name of the function to be executed
 * @param _fn_oplist:   Execution arguments to be applied
 * @param _source_file: Name of the source file containing the function implementation
 */
void Backend::begin_fn(char* _fn_name, char* _fn_oplist, char* _source_file)
{
    p_timer->start_timer(eBeginFn);

    nullpointer_check(_fn_name);
    nullpointer_check(_fn_oplist);
    nullpointer_check(_source_file);

    std::string fn_oplist = std::string(_fn_oplist);
    std::string source_file = std::string(_source_file);

    Object::set_file_being_executed(source_file);
    Object::set_current_function(_fn_name);
    Object::add_path_element(_fn_name);

    std::string mangled_ops = Object::mangle_name(fn_oplist);
    std::vector<std::string> ops = BaseUtils::tokenize(mangled_ops, NameMangling::VARIABLE_SEPERATOR);

    p_sym_exec->begin_function(_fn_name, ops);
    
    if(!p_callstack->empty()){
        p_callstack->push(p_callstack->top().function_name, _fn_name, Object::get_file_being_executed());
    } else {
        p_callstack->push("", _fn_name, Object::get_file_being_executed());
    }

    p_callstack->print_callstack();

    p_timer->end_timer(eBeginFn);
}

/**
 * @brief End execution of a function
 */ 
void Backend::end_fun()
{
    p_sym_exec->end_function();
}

/**
 * @brief Return from a called instruction.
 * 
 * @param _retname: The register name to returned to the caller.
 */
void Backend::return_instr(char* _retname)
{
    p_timer->start_timer(eReturn);

    nullpointer_check(_retname);

    p_sym_exec->return_instruction(this->mangle_name(_retname));

    p_timer->end_timer(eReturn);
}

/**
 * @brief Binary Operation
 * 
 * @param _dst:  Name of the destination register
 * @param _op1:  Name of the first operation register
 * @param _op2:  Name of the second operation  register
 * @param _type: The operation to perform on the data
 * @param _line: Line number of operation.
*/
void Backend::binary_op(char* _dst, char* _op1, char* _op2, char* _type, char* _line)
{
    p_timer->start_timer(eBinOp);
    
    nullpointer_check(_dst);
    nullpointer_check(_op1);
    nullpointer_check(_op2);
    nullpointer_check(_type);
    nullpointer_check(_line);

    std::string decode_line = BaseUtils::decode_constant(_line);
    size_t i_line = std::stoi(decode_line);

    Object::set_line_num_in_execution(i_line);
    LLVMOpcode etype = LLVMOpcode(std::stoi(_type));

    p_sym_exec->binary_instruction(this->mangle_name(_dst), this->mangle_name(_op1), this->mangle_name(_op2), etype);

    p_timer->end_timer(eBinOp);
}

/**
 * @brief Cast the content of the source register into the destination register type
 * 
 * @param _dst:  Name of the destination register
 * @param _src:  Name of the source register
 * @param _type: Type of the new allocated destination register
 * @param _sext: Sign Extension or Zero Extension
*/
void Backend::cast_instruction(char* _dst, char* _src, char* _type, char* _sext)
{
    p_timer->start_timer(eCast);

    nullpointer_check(_dst);
    nullpointer_check(_src);
    nullpointer_check(_type);
    nullpointer_check(_sext);

    std::string sext = std::string(_sext);

    bool b_sext;
    if(sext.compare("true") == 0){
        b_sext = true;
    } else if (sext.compare("false") == 0){
        b_sext = false;
    } else {
        throw YassiException("Non valid sext value detected!");
    }

    p_sym_exec->cast_instruction(this->mangle_name(_src), this->mangle_name(_dst), _type, b_sext);
   
    p_timer->end_timer(eCast);
}

/**
 * @brief Initialisation of global variables (not called within main).
 * 
 * @param _name:  The name of the variable/register.
 * @param _type:  The type of the register.
 * @param _value: The value to initialize the register.
 */
void Backend::global_var_init(char* _name, char* _type, char* _value)
{
    p_timer->start_timer(eGlobalVarInit);

    nullpointer_check(_name);
    nullpointer_check(_type);
    nullpointer_check(_value);

    p_sym_exec->global_variable_init(this->mangle_name(_name), _type, _value);

    p_timer->end_timer(eGlobalVarInit);
}

/**
 * @brief Getelementptr Operation
 * 
 * @param _dst: Destination to write the operation result to
 * @param _pointer: Pointer to the data 
 * @param _index: Indexes used for Getelementptr Operation
 * @param _offset_tree: OffsetTree of the datastructure
 * @param _line_num: Line number of code instruction caused GEP operation
 */
void Backend::getelementptr(char* _dst, char* _pointer, char* _index, char* _offset_tree, char* _line_num)
{
    p_timer->start_timer(eGEOP);
    
    nullpointer_check(_dst);
    nullpointer_check(_pointer);
    nullpointer_check(_index);
    nullpointer_check(_offset_tree);
    nullpointer_check(_line_num);

    std::string decode_line = BaseUtils::decode_constant(_line_num);
    size_t i_line = std::stoi(decode_line);
    this->set_line_num_in_execution(i_line);

    std::vector<std::string> index_vectors = BaseUtils::tokenize(this->mangle_name(_index), NameMangling::VARIABLE_SEPERATOR);

    p_sym_exec->getelementptr(this->mangle_name(_dst), this->mangle_name(_pointer), index_vectors, _offset_tree);

    p_timer->end_timer(eGEOP);
}

/**
 * @brief Call Instruction
 * 
 * @param _fn_name: Name of the function to call
 * @param _oplist:  Function Call Arguments
 * @param _ret_to:  Return Value of the Function to be assigned to
 */
void Backend::call_instr(char* _fn_name, char* _oplist, char* _ret_to) 
{
    p_timer->start_timer(eFnCall);

    nullpointer_check(_fn_name);
    nullpointer_check(_ret_to);

    std::vector<std::string> ops = BaseUtils::tokenize(this->mangle_name(_oplist), NameMangling::VARIABLE_SEPERATOR);

    p_sym_exec->call_instruction(ops, this->mangle_name(_ret_to));

    p_timer->end_timer(eFnCall);
}

/**
 * @brief Call Instruction Post
 * 
 * @param _fn_name:  Name of the function execution finished
 * @param _ret_type: Type of the function return register
 * @param _caller:   Name of the function caller
 */
void Backend::call_instr_post(char* _fn_name, char* _ret_type, char* _caller) 
{
    p_timer->start_timer(eFnCallPost);
    
    nullpointer_check(_fn_name);
    nullpointer_check(_ret_type);
    nullpointer_check(_caller);

    // Has to be done here before name mangling since name mangling
    // is using the static members of Object
    if(p_database->is_external_function(_fn_name)){
       // dummy TODO
    } else if(p_database->is_internal_function(_fn_name) || Utils::is_register(Object::mangle_name(_fn_name))){
        p_callstack->pop();
        Object::set_current_function(p_callstack->top().function_name);
        Object::set_file_being_executed(p_callstack->top().source_file);
        p_callstack->print_callstack();
    }
    
    std::string mangled_fn_name;    
    std::vector<std::string> token = BaseUtils::tokenize(_fn_name, NameMangling::MANGELING_SEPERATOR);
  
    if(token.size() == 2 && token[0] == "register") {
        mangled_fn_name = Object::mangle_name(_fn_name);
    } else {
        mangled_fn_name = _fn_name;
    }

    p_sym_exec->call_instruction_post(mangled_fn_name, _ret_type, _caller);

    p_timer->end_timer(eFnCallPost);
}

/**
 * @brief Select Operator for If-Then-Else realisation.
 * 
 * @param _dst:  Name of the register to store the result.
 * @param _cond: Name of the register holding the condition.
 * @param _sel1: Name of the first possible solution.
 * @param _sel2: Name of the second possible solution.
 */
void Backend::select_op(char* _dst, char* _cond, char* _sel1, char* _sel2) 
{
    p_timer->start_timer(eSelOp);

    nullpointer_check(_dst);
    nullpointer_check(_cond);
    nullpointer_check(_sel1);
    nullpointer_check(_sel2);

    p_sym_exec->select_instruction(this->mangle_name(_dst), this->mangle_name(_cond), this->mangle_name(_sel1), this->mangle_name(_sel2));

    p_timer->end_timer(eSelOp);
}

/**
 * @brief Memory Copy according to LLVM's llvm.memcpy
 * 
 * @param _addr_dst:    Name of the register holding the address to the destination register.
 * @param _addr_src:    Name of the register holding the address to the source register.
 * @param _size_bytes:  Number of bytes to copy.
 * @param _align:       Alignment of the memory block.
 * @param _is_volatile: Volatile memory.
 */
void Backend::memcpy(char* _addr_dst, char* _addr_src, char* _size_bytes, char* _align, char* _is_volatile) 
{
    p_timer->start_timer(eMemCpy);

    nullpointer_check(_addr_dst);
    nullpointer_check(_addr_src);
    nullpointer_check(_size_bytes);
    nullpointer_check(_align);
    nullpointer_check(_is_volatile);

    p_sym_exec->memcpy(this->mangle_name(_addr_dst), this->mangle_name(_addr_src), _size_bytes, _align, _is_volatile);

    p_timer->end_timer(eMemCpy);
}

/**
 * @brief Memory Set according to LLVM's llvm.memset
 * 
 * @param _addr_dst:    Name of the register holding the address to the destination register.
 * @param _val:         Value to be applied for all register.
 * @param _len:         Number of bytes/registers to set.
 * @param _align:       Alignment of the memory block.
 * @param _is_volatile: Volatile memory.
 */
void Backend::memset(char* _addr_dst, char* _val, char* _len, char* _align, char* _is_volatile) 
{
    p_timer->start_timer(eMemSet);

    nullpointer_check(_addr_dst);
    nullpointer_check(_align);
    nullpointer_check(_len);
    nullpointer_check(_val);
    nullpointer_check(_is_volatile);

    p_timer->end_timer(eMemSet);
}

/**
 * @brief Add an assumption for the execution.
 * 
 * @param _assumption_register: Register holding the SMT instance.
 */
void Backend::assume(char* _assumption_register) 
{
    p_timer->start_timer(eAssume);

    nullpointer_check(_assumption_register);

    p_intrinsics->assume(this->mangle_name(_assumption_register));

    p_timer->end_timer(eAssume);
}

/**
 * @brief Add an assertion to check properties.
 * 
 * @param _assertion_register:  The register holding the SMT instance to proof.
 * @param _line_num:            The linenumber where the assertion has been called.
 */
void Backend::assertion(char* _assertion_register, char* _line_num) 
{
    p_timer->start_timer(eAssert);

    nullpointer_check(_assertion_register);
    nullpointer_check(_line_num);

    std::string assertion_register = std::string(_assertion_register);
    std::string line_num = std::string(_line_num);

    std::string decode_line = BaseUtils::decode_constant(_line_num);
    size_t i_line = std::stoi(decode_line);

    Object::set_line_num_in_execution(i_line);

    std::string mangled_assertion_register = Object::mangle_name(assertion_register);

    p_intrinsics->assertion(mangled_assertion_register);

    p_timer->end_timer(eAssert);
}

/**
 * @brief An Error has been detected.
 * Terminate the execution and store all information to the database.
 * 
 * @param _line_num: The linenumber where error has been called.
 */
void Backend::__YASSI_error(char* _line_num) 
{
    nullpointer_check(_line_num);

    std::string decode_line = BaseUtils::decode_constant(_line_num);
    size_t i_line = std::stoi(decode_line);

    Object::set_line_num_in_execution(i_line);

    p_intrinsics->error();
}

/**
 * @brief Set a pointer variable non-determinstic (free).
 * 
 * @return void*
 */
void* Backend::nondet_pointer() 
{
    return p_intrinsics->nondet_pointer();
}

/**
 * @brief Set a boolean variable non-determinstic (free).
 * 
 * @return bool
 */
bool Backend::nondet_bool() 
{
    return p_intrinsics->nondet_bool();
}

/**
 * @brief Set a character variable non-determinstic (free).
 * 
 * @return char
 */
char Backend::nondet_char() 
{
    return p_intrinsics->nondet_char();
}

/**
 * @brief Set a signed integer variable non-determinstic (free).
 * 
 * @return int
 */
int Backend::nondet_int() 
{
    return p_intrinsics->nondet_int();
}

/**
 * @brief Set a long variable non-determinstic (free).
 * 
 * @return long int
 */
long Backend::nondet_long() 
{
    return p_intrinsics->nondet_long();
}

/**
 * @brief Set a unsigned integer variable non-determinstic (free).
 * 
 * @return unsigned int
 */
unsigned int Backend::nondet_uint() 
{
    return p_intrinsics->nondet_uint();
}

/**
 * @brief Force a local variable to be free and allow the reasoning engine to change it's value.
 * 
 * @param _variable: The name of the variable
 * @param _size:     The number of bytes allocated by the variable (needed to identify struct types)
 */
void Backend::__YASSI_force_free_local(char* _variable, unsigned long _size) 
{
    nullpointer_check(_variable);

    p_sym_exec->__YASSI_force_free(this->mangle_name("register" + NameMangling::MANGELING_SEPERATOR + _variable), _size);
}

/**
 * @brief Force a global variable to be free and allow the reasoning engine to change it's value.
 * 
 * @param _variable: The name of the variable
 * @param _size:     The number of bytes allocated by the variable (needed to identify struct types)
 */
void Backend::__YASSI_force_free_global(char* _variable, unsigned long size) 
{
    nullpointer_check(_variable);

    p_sym_exec->__YASSI_force_free(this->mangle_name("global" + NameMangling::MANGELING_SEPERATOR + _variable), size);
}

/**
 * @brief Force the reasoning engine for a particular result. 
 * 
 * @param _variable: The register whose instance must be true.
 */
void Backend::__YASSI_force_assertion(char* _variable)
{
    nullpointer_check(_variable);

    p_sym_exec->__YASSI_force_assertion(this->mangle_name(_variable));
}

/**
 * @brief Print a debug message to stdout during execution.
 * 
 * @param _msg: The message to be displayed.
 */
void Backend::__YASSI_debug(char* _msg)
{
    nullpointer_check(_msg);

    p_sym_exec->__YASSI_debug(this->mangle_name(_msg));
}

/**
 * @brief Allocate memory.
 * 
 * @param argument: The number of bytes to allocate.
 * @return void*
 */
void* Backend::__YASSI_malloc(char* argument)
{
    return p_sym_exec->__YASSI_malloc(argument);
}

/**
 * @brief Release memory.
 * 
 * @param _variable_name:
 */
void Backend::__YASSI_free(char* _variable_name)
{
    nullpointer_check(_variable_name);

    p_sym_exec->__YASSI_free(this->mangle_name(_variable_name));
}

/**
 * @brief Signal handler to terminate the backend after a timeout.
 */
void Backend::alarm_handler()
{
    p_logger->timeout();
    kill(0, SIGKILL);
}
