#include "yassi_logger.hpp"

using namespace Yassi::Backend::Replay;
using namespace Yassi::Utils;

std::shared_ptr<Logger> Logger::p_singleton = nullptr;
bool Logger::p_instance = false;

Logger* Logger::getInstance() 
{
    if(Logger::p_instance == false){
        p_instance = true;
        p_singleton.reset(new Logger);
    }
    return p_singleton.get();
}

Logger::Logger():
    Object(), BaseLogger()
{
    if(!this->get_debug() && !this->get_log_file_enabled()){
        p_log_stream->set_enabled(false);
    } else {
        p_log_stream->set_enabled(true);
    }
    if(this->get_debug()){
        p_log_stream->set_dump_to_shell(true);
    }
}

Logger::~Logger() 
{

}

void Logger::begin_simulation()
{
    LOG(eInfo) << BaseUtils::get_bash_string_blink_red("Begin Replay!");
}

void Logger::end_simulation() 
{
    LOG(eInfo) << BaseUtils::get_bash_string_blink_red("End Replay!");
}

void Logger::begin_bb(std::string const & bb) 
{
    LOG(eInfo) << BaseUtils::get_bash_string_purple("Entering Basic Block: " + bb);
}

void Logger::end_bb(std::string const & bb)
{
    LOG(eInfo) << BaseUtils::get_bash_string_purple("Leaving Basic Block: " + bb);
}

void Logger::begin_fn(const std::string& fn)
{
    LOG(eInfo) << BaseUtils::get_bash_string_orange("Begin Function: " + fn);
}

void Logger::end_fn(const std::string& fn)
{
    LOG(eInfo) << BaseUtils::get_bash_string_orange("End Function: " + fn);
}

void Logger::conditional_branch(bool taken)
{
    std::stringstream msg;
    
    if(taken) {
        msg << "Conditional Branch: TAKEN";
    } else {
        msg << "Conditional Branch: NOT TAKEN";
    }
    LOG(eInfo) << BaseUtils::get_bash_string_blink_red(msg.str());
}

void Logger::assertion_fail()
{
    LOG(eInfo) << BaseUtils::get_bash_string_blink_red("Assertion Fail!");
}

void Logger::assertion_pass()
{
    LOG(eInfo) << BaseUtils::get_bash_string_purple("Assertion Pass!");
}

void Logger::apply_vector_char(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Char): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::apply_vector_double(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Double): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::apply_vector_float(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Float): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::apply_vector_int(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Int): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::apply_vector_long(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Long): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::apply_vector_short(std::string const & name, std::string const & value)
{
    std::stringstream msg;
    msg << "Applying Vector (Short): " << name << " := " << value;
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}
