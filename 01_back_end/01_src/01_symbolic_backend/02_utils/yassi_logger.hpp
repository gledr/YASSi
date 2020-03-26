#ifndef YASSI_BACKEND_LOGGER_HPP
#define YASSI_BACKEND_LOGGER_HPP

#include <chrono>
#include <memory>
#include <string>
#include <ctime>
#include <iomanip>
#include <fstream>

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_llvm_enums.hpp>
#include <yassi_baselogger.hpp>
#include <yassi_utils.hpp>

namespace Yassi::Backend::Execute {

class Logger : public virtual Object, public virtual Yassi::Utils::BaseLogger {
public:

    static Logger* getInstance();
    static void destroy();

    void begin_backend(std::string const & z3_version);

    void begin_simulation();
    void end_simulation();

    void begin_bb(std::string const & bb);
    void end_bb(std::string const & bb);

    void alloca_instr(Variables::BaseVariable* var);
    void clean_stack_variable(Variables::BaseVariable* var);
    void global_variable_init(std::string const & name,
                              std::string const & type,
                              std::string const & val);

    void load_instr(std::string const & addr, std::string const & dst);
    void store_instr(std::string const & src, std::string const & addr);

    void symbolic_load();
    void symbolic_store();

    void assign_instr(Variables::BaseVariable* src,
                      Variables::BaseVariable* dst);

    void constant_elementptr(Variables::BaseVariable* ptr,
                             Variables::BaseVariable* dst,
                             std::vector<Variables::BaseVariable*> indexes);
    void non_constant_elementptr(Variables::BaseVariable* ptr,
                                 Variables::BaseVariable* dst,
                                 std::vector<size_t> possible_inx);
    void deref_elementptr(Variables::BaseVariable* ptr, Variables::BaseVariable* dst);

    void cast_instr(std::string const & src,
                    std::string const & dst,
                    std::string const & type,
                    bool const sext);

    void call_instr(std::string const & return_to,
                    std::vector<std::string> const & arguments);
    void call_instr_post(std::string const & fn_name,
                         std::string const & return_type,
                         std::string const & caller);

    void begin_function(std::string const & function_name,
                        std::vector<std::string> const & arguments);
    void end_function(std::string const & function_name);
    void return_instr(Variables::BaseVariable* var);

    void binary_instruction(std::string const & dst,
                            std::string const & op1,
                            std::string const & op2,
                            LLVMOpcode const & op);
    void compare_instruction(std::string const & dst,
                             std::string const & op1,
                             std::string const & op2,
                             int const & op);

    void branch_instruction_conditional(std::string const & conditional_variable,
                                        bool branch_taken);

    void exception_found(eException const what,
                         std::string const & file,
                         std::string const & line,
                         std::string const & description);

    void assume(std::string const & assume_register,
                std::string const & assume_expr);

    void error();

    void memcpy(std::string const & from_element,
                std::string to_element,
                std::string const & bytes,
                std::string const & align);
    void memset(std::string to_element,
                std::string const & val,
                std::string const & bytes,
                std::string const & align);
    
    void malloc(std::string const & bytes);
    void free(std::string const & obj);

    void function_pointer(std::string const & fp);

    void select(std::string const & dst,
                std::string const & cond,
                std::string const & sel1,
                std::string const & sel2);

    void force_free(std::string variable_name, std::string containing_items);

    void print_callstack(std::string const & msg);

    void terminate_backend();
    void timeout();

    void dump(std::string const & msg);
    
private:
    Logger();
    virtual ~Logger();

    static Logger* p_singleton;
    static bool p_instance;

    std::string binop2string(LLVMOpcode const & op);
    std::string cmpop2string (int const & op);
    std::string cmprealop2string(LLVMRealPredicate const & op);
    std::string cmpintop2string(LLVMIntPredicate const & op);
    
    void outofbounds(std::string const & file, std::string const & line);
    void double_free(std::string const & file, std::string const & line);
    void memory_leak(std::string const & file,
                     std::string const & line,
                     std::string const & description);

    void division_by_zero(std::string const & file, std::string const & line);
    void rem_by_zero(std::string const & file, std::string const & line);
    
    void assertion_pass(std::string const & file, std::string const & line);
    void assertion_fail(std::string const & file, std::string const & line);
};

}

#endif /* YASSI_BACKEND_LOGGER_HPP */
