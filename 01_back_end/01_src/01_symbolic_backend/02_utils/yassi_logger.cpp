#include <yassi_logger.hpp>

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;


Logger* Logger::p_singleton = nullptr;
bool Logger::p_instance = false;

Logger* Logger::getInstance() 
{
    if(Logger::p_instance == false){
        p_instance = true;
        p_singleton = new Logger();
    }
    return p_singleton;
}

void Logger::destroy()
{
    delete Logger::p_singleton;     p_singleton = nullptr;
    Logger::p_instance = false;
}

Logger::Logger():
    Object(), BaseLogger()
{
    p_log_stream->set_working_directory(this->get_execution_url());
    p_log_stream->set_file_name(this->get_logfile_name());
    
    if(this->get_quiet()){
        p_log_stream->set_enabled(false);
        p_log_stream->set_quiet(true);
    } else {
        p_log_stream->set_enabled(true);
    }
    if(this->get_debug()){
        p_log_stream->set_dump_to_shell(true);
    }
    if(this->get_log_file_enabled()){
        p_log_stream->set_dump_to_file(true);
    }
}

Logger::~Logger()
{
}

void Logger::begin_bb(std::string const & bb)
{
    LOG(eDebug) << BaseUtils::get_bash_string_purple("Entering Basic Block: " + bb);
}

void Logger::end_bb(std::string const & bb)
{
    LOG(eDebug) <<
        BaseUtils::get_bash_string_purple("Leaving Basic Block: " + bb);
}

void Logger::begin_simulation()
{
    LOG(eDebug) <<
        BaseUtils::get_bash_string_blink_red("Begin Simulation!");
}

void Logger::end_simulation()
{
    LOG(eDebug) <<
    BaseUtils::get_bash_string_blink_red("End Stimulation @PID: " +
                                          std::to_string(getpid()));
}

void Logger::alloca_instr(BaseVariable* var)
{
    nullpointer_check(var);

    std::stringstream debug_msg;
    debug_msg << "Alloca Instruction: ";
    debug_msg << var->get_name() << " ";
    debug_msg << std::left << std::setfill (' ') << std::setw (40) << var->get_name_hint();
    debug_msg <<  std::left << std::setfill (' ') << std::setw (20) << var->get_type()->get_type_identifier() << " ";
    debug_msg << var->get_firstaddress() <<  " " << var->get_lastaddress();
    LOG(eDebug) << BaseUtils::get_bash_string_orange(debug_msg.str());
}

void Logger::clean_stack_variable(BaseVariable* var)
{
    nullpointer_check(var);

    LOG(eDebug) << 
        BaseUtils::get_bash_string_orange("Release Memory: " + 
                                          var->get_name() +
                                          " Type: Stack Scope: " +
                                          var->get_sourcefile() +
                                          "@" + var->get_function());
}

void Logger::store_instr(std::string const & src, std::string const & addr)
{
    LOG(eDebug) << 
        BaseUtils::get_bash_string_cyan("Store Instruction: " + src + " => " + addr);
}

void Logger::load_instr(std::string const & addr, std::string const & dst) 
{
    LOG(eDebug) 
        << BaseUtils::get_bash_string_cyan("Load Instruction: " + dst + " <= " + addr);
}

void Logger::assign_instr(BaseVariable* src, BaseVariable* dst)
{
    nullpointer_check (src);
    nullpointer_check (dst);

    LOG(eDebug) << BaseUtils::get_bash_string_blue("Assign Instruction: " +
                                                   dst->get_name_hint() +
                                                   ":= " +
                                                   src->get_name_hint());
}

void Logger::return_instr(BaseVariable* var)
{
    nullpointer_check(var);

    LOG(eDebug) << 
        BaseUtils::get_bash_string_cyan("Return Instruction: " +
                                        var->get_name_hint());
}

void Logger::begin_function(std::string const & function_name,
                            std::vector<std::string> const & arguments)
{
    std::string debug_msg = "Begin Function: " + function_name + " (" + this->get_file_being_executed() + ")";
    LOG(eDebug) << BaseUtils::get_bash_string_orange(debug_msg);
    if(!arguments.empty()){
        std::stringstream msg;
        msg << BaseUtils::get_bash_string_orange("Arguments:");

        for(auto itor : arguments){
           msg << itor << " ";
        }
        LOG(eDebug) << msg.str();
    }
}

void Logger::end_function(std::string const & function_name)
{
    LOG(eDebug) << 
        BaseUtils::get_bash_string_orange("End Function: " + function_name + " (" + this->get_file_being_executed() + ")");
}

void Logger::binary_instruction(std::string const& dst,
                                std::string const & op1,
                                std::string const & op2,
                                LLVMOpcode const & op)
{
    LOG(eDebug) << BaseUtils::get_bash_string_red("Binary Instruction: " + dst + ":= " + op1 + " " + this->binop2string(op) + " " + op2);
}

void Logger::compare_instruction(std::string const & dst,
                                 std::string const & op1,
                                 std::string const & op2, 
                                 int const & op) 
{
    LOG(eDebug) << BaseUtils::get_bash_string_red( "Compare Instruction: " + dst + ":= " + op1 + " " + this->cmpop2string(op) + " " + op2);
}

void Logger::branch_instruction_conditional(std::string const & conditional_variable,
                                            bool branch_taken) 
{
    LOG(eDebug) << BaseUtils::get_bash_string_cyan("Conditional Branch Instruction: " + conditional_variable + " Branch Taken: " + std::to_string(branch_taken));
}

void Logger::call_instr(std::string const & return_to,
                        std::vector<std::string> const & arguments)
{
    std::stringstream debug_msg;
    debug_msg << BaseUtils::get_bash_string_cyan("Call Instruction: Return Register " + return_to);
    LOG(eDebug) << debug_msg.str();
    debug_msg.str("");
    debug_msg << "Arguments: ";
    if(this->get_debug()){
        std::copy(arguments.begin(), arguments.end(), std::ostream_iterator<std::string>(debug_msg, " "));
    }
    LOG(eDebug) << debug_msg.str();
}

void Logger::call_instr_post(std::string const & fn_name,
                             std::string const & return_type,
                             std::string const & caller)
{
    LOG(eDebug) << BaseUtils::get_bash_string_cyan("Call Instruction Post: " + fn_name + " " + return_type + " " + caller);
}

void Logger::cast_instr(std::string const & src,
                        std::string const & dst,
                        std::string const & type,
                        bool const sext)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("Cast Instruction " + dst + " (" + type + ") := " + src + " sext: " + std::to_string(static_cast<int>(sext)));
}

std::string Logger::binop2string(LLVMOpcode const & op)
{
    switch(op) {
    case LLVMAdd:
        return "+";
    case LLVMFAdd:
        return "+";
    case LLVMSub:
        return "-";
    case LLVMFSub:
        return "-";
    case LLVMMul:
        return "*";
    case LLVMFMul:
        return "*";
    case LLVMOr:
        return "or";
    case LLVMAnd:
        return "and";
    case LLVMAShr:
        return ">>";
    case LLVMLShr:
        return ">>";
    case LLVMXor:
        return "xor";
    case LLVMUDiv:
        return "/";
    case LLVMSDiv:
        return "/";
    case LLVMFDiv:
        return "/";
    case LLVMShl:
        return "<<";
    case LLVMFRem:
        return "frem";
    case LLVMSRem:
        return "srem";
    case LLVMURem:
        return "urem";
    default:
        notimplemented_check();
        exit(-1);
    }
}

std::string Logger::cmpop2string(int const & _op)
{
    if ( _op >= 32 ) {
        return this->cmpintop2string (static_cast<LLVMIntPredicate>(_op));
    } else {
        return this->cmprealop2string(static_cast<LLVMRealPredicate>(_op));
    }
}

std::string Logger::cmprealop2string(LLVMRealPredicate const & op)
{
    if (op == LLVMRealPredicateFalse)          { /* Always false (always folded) */
       notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealOEQ)               { /* True if ordered and equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealOGT)              { /* True if ordered and greater than */
        return ">";
    } else if (op == LLVMRealOGE)               { /* True if ordered and greater than or equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealOLT)               { /* True if ordered and less than */
        return "<";
    } else if ( op == LLVMRealOLE)              { /* True if ordered and less than or equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealONE)               { /* True if ordered and operands are unequal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealORD)              { /* True if ordered (no nans) */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealUNO)              { /* True if unordered: isnan(X) | isnan(Y) */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealUEQ)              { /* True if unordered or equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealUGT)              { /* True if unordered or greater than */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealUGE)              { /* True if unordered, greater than, or equal */
        notimplemented_check();
        exit(-1);
    } else if ( op == LLVMRealULT)              { /* True if unordered or less than */
        notimplemented_check();
    } else if ( op == LLVMRealULE)              { /* True if unordered, less than, or equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealUNE)              { /* True if unordered or not equal */
        notimplemented_check();
        exit(-1);
    } else if (op == LLVMRealPredicateTrue)    { /* Always true (always folded) */
        notimplemented_check();
        exit(-1);
    } else                                      {
        notimplemented_check();
        exit(-1);
    }
    exit(-1);
}

std::string Logger::cmpintop2string (LLVMIntPredicate const & op)
{
    if ( op == LLVMIntEQ )                       { /* equal */
        return "eq";
    } else if ( op == LLVMIntNE )                { /* not equal */
        return "ne";
    } else if ( op == LLVMIntUGT )               { /* unsigned greater than */
        return "ugt";
    } else if ( op == LLVMIntUGE )               { /* unsigned greater or equal */
        return "uge";
    } else if ( op == LLVMIntULT )               { /* unsigned less than */
        return "ult";
    } else if ( op == LLVMIntULE )               { /* unsigned less or equal */
        return "ule";
    } else if ( op == LLVMIntSGT )               { /* signed greater than */
        return "sgt";
    } else if ( op == LLVMIntSGE )               { /* signed greater or equal */
        return "sge";
    } else if ( op == LLVMIntSLT )               { /* signed less than */
        return "slt";
    } else if ( op == LLVMIntSLE )               { /* signed less or equal */
        return "sle";
    } else                                       {
        notimplemented_check();
        exit(-1);
    }
}

void Logger::assume(std::string const & assume_register,
                    std::string const & assume_expr) 
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("Assumption: " + assume_expr + " (" + assume_register + ")");
}

void Logger::memcpy(std::string const & from_element,
                    std::string to_element,
                    std::string const & bytes,
                    std::string const & align) 
{
    LOG(eDebug) << BaseUtils::get_bash_string_purple("MemCpy Instruction: " + from_element + " := " + to_element + " Bytes(" + bytes + ") Align(" + align + ")");
}

void Logger::memset(std::string to_element,
                    std::string const & val,
                    std::string const & bytes,
                    std::string const & align)
{
    LOG(eDebug) << BaseUtils::get_bash_string_purple("MemSet Instruction " + to_element + " := " + val + " Bytes(" + bytes + ") Align(" + align + ")");
}

void Logger::function_pointer(std::string const & fp)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("Function Pointer: " + fp);
}

void Logger::global_variable_init(std::string const & name,
                                  std::string const & type,
                                  std::string const & val)
{
    std::stringstream debug_msg;
    std::vector<std::string> decoded_vals = BaseUtils::decode_constants(val);

    std::string vals;
    for(auto& itor : decoded_vals){
        vals += itor;
        vals += ",";
    }

    debug_msg << "Global Variable Init: " << name << " " << type << " " << vals;
    LOG(eDebug) << BaseUtils::get_bash_string_orange(debug_msg.str());
}

void Logger::constant_elementptr(BaseVariable* ptr,
                                 BaseVariable* dst,
                                 std::vector<BaseVariable*> indexes)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange( "Constant Elementptr: " + dst->get_name_hint() + " = " + ptr->get_name_hint() + "[" + indexes.back()->get_value_as_string() + "]");
}

void Logger::non_constant_elementptr(BaseVariable* ptr,
                                     BaseVariable* dst,
                                     std::vector<size_t> possible_idx)
{
    std::stringstream debug_msg;
    debug_msg << "Non-Constant Elementptr: " << dst->get_name_hint() << " " << ptr->get_name_hint() << "[";
    for (auto itor : possible_idx){
        debug_msg << itor << ",";
    }
    debug_msg << "]";
    
    LOG(eDebug) << BaseUtils::get_bash_string_orange(debug_msg.str());
}

void Logger::deref_elementptr(BaseVariable* ptr,
                              BaseVariable* dst)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("Deref Elementptr: " + dst->get_name_hint() + " *" + ptr->get_name_hint());
}

void Logger::select(std::string const & dst,
                    std::string const & cond,
                    std::string const & sel1,
                    std::string const & sel2)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("Select: " + dst + " == " + cond + " ? " + sel1 + " : " + sel2);
}

void Logger::assertion_pass(std::string const & file,
                            std::string const & line)
{
    LOG(eInfo) << BaseUtils::get_bash_string_green("Assertion PASS: File: " + file + " Line: " + line);
}

void Logger::assertion_fail(std::string const & file,
                            std::string const & line)
{
    LOG(eError) << BaseUtils::get_bash_string_blink_red("Assertion FAILED: File: " + file + " Line: " + line);
}

void Logger::outofbounds(std::string const & file,
                         std::string const & line)
{
    LOG(eError) << BaseUtils::get_bash_string_blink_red("OutOfBounds Detected: File: " + file + " Line: " + line);
}

void Logger::double_free(std::string const & file,
                         std::string const & line)
{
    LOG(eError) << BaseUtils::get_bash_string_blink_red("DoubleFree Detected: File: " + file + " Line: " + line);
}

void Logger::force_free(std::string variable_name,
                        std::string containing_items)
{
    LOG(eDebug) << BaseUtils::get_bash_string_orange("ForceFree: Variable(" + variable_name + ") ContainigElements: " + containing_items);
}

void Logger::print_callstack(std::string const & msg)
{
    LOG(eDebug) << BaseUtils::get_bash_string_cyan(msg);
}

void Logger::error()
{
    LOG(eError) << BaseUtils::get_bash_string_blink_red("== __VERIFIER_error() has been called ==");
    LOG(eError) << "Source: " << this->get_file_being_executed() << " Line: " << this->get_line_num_execution();
}

void Logger::symbolic_load()
{
    LOG(eDebug) << BaseUtils::get_bash_string_blink_purple("=== Symbolic Load ===");
}

void Logger::symbolic_store()
{
    LOG(eDebug) << BaseUtils::get_bash_string_blink_purple( "=== Symbolic Store ===");
}

void Logger::division_by_zero(std::string const & file,
                              std::string const & line)
{
    LOG(eFatal) << BaseUtils::get_bash_string_red("Division by zero detected! File: " + file + " Line: " + line);
}

void Logger::rem_by_zero(std::string const & file,
                         std::string const & line)
{
    LOG(eFatal) << BaseUtils::get_bash_string_red("Remainder by zero detected! File: " + file + " Line: " + line);
}

void Logger::memory_leak(std::string const & file,
                         std::string const & line,
                         std::string const & description)
{
    (void) file;
    (void) line;
    
    std::stringstream msg;
    msg << "Memory Leaks Detected! (" << description << ")";
    LOG(eFatal) << BaseUtils::get_bash_string_blink_red(msg.str());
}

void Logger::terminate_backend()
{
    LOG(eFatal) << BaseUtils::get_bash_string_blink_red("Backend Terminated after detected exception!");
}

void Logger::timeout()
{
    LOG(eWarning) << "Timeout Alarm after " << Object::get_timeout() << " seconds";
    LOG(eWarning) << "Backend Terminating...";
}

void Logger::dump(std::string const & msg)
{
    std::string clean_msg = msg;
    
    /*
     * C-Strings are Null Terminated
     */
    if(msg.back() == 0){
        clean_msg = msg.substr(0, msg.size()-2);
    }
    /*
     * If there is a \n, remove it 
     */
    if(clean_msg.back() == 10){
         clean_msg = msg.substr(0, clean_msg.size()-2);
    }
   
    LOG(eStdOut) << clean_msg;
}

void Logger::exception_found(eException const what,
                             std::string const & file,
                             std::string const & line,
                             std::string const & description)
{
    switch (what){
        case e_assertion_fail:
            this->assertion_fail(file, line);
            break;
            
        case e_assertion_pass:
            this->assertion_pass(file, line);
            break;
            
        case e_deref_range:
            
            break;
            
        case e_divide_by_zero:
            this->division_by_zero(file, line);
            break;
            
        case e_double_free:
            this->double_free(file, line);
            break;
            
        case e_memory_leak:
            this->memory_leak(file, line, description);
            break;
            
        case e_out_of_bounds:
            this->outofbounds(file, line);
            break;
            
        case e_rem_zero:
            this->rem_by_zero(file, line);
            break;
    }
}

void Logger::begin_backend(std::string const & z3_version)
{
    LOG(eInfo) << "Using Backend: " << z3_version;
}

void Logger::malloc(std::string const & bytes)
{
    std::string msg = "Malloc: " + bytes;
    LOG(eDebug) << BaseUtils::get_bash_string_orange(msg);
}

void Logger::free(std::string const & obj)
{
    std::string msg = "Free: " + obj;
    LOG(eDebug) << BaseUtils::get_bash_string_orange(msg);
}
