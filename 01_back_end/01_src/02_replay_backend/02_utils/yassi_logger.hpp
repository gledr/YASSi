#ifndef YASSI_REPLAY_LOGGER_HPP
#define YASSI_REPLAY_LOGGER_HPP

#include <yassi_object.hpp>
#include <yassi_baselogger.hpp>

#include <chrono>
#include <memory>
#include <string>
#include <ctime>
#include <iomanip>

namespace Yassi::Backend::Replay {
    
class Logger: public virtual Object, public virtual Yassi::Utils::BaseLogger{
public:
    
    static Logger* getInstance();
    
    virtual ~Logger();
    
    void begin_simulation();
    void end_simulation();
    
    void begin_bb(std::string const & bb);
    void end_bb(std::string const & bb);
    
    void begin_fn(std::string const & fn);
    void end_fn(std::string const & fn);
    
    void conditional_branch(bool taken);
    
    void apply_vector_int(std::string const & name, std::string const & value);
    void apply_vector_short(std::string const & name, std::string const & value);
    void apply_vector_char(std::string const & name, std::string const & value);
    void apply_vector_long(std::string const & name, std::string const & value);
    void apply_vector_float(std::string const & name, std::string const & value);
    void apply_vector_double(std::string const & name, std::string const & value);
    
    void assertion_pass();
    void assertion_fail();
    
private:
    Logger();
    
    static std::shared_ptr<Logger> p_singleton;
    static bool p_instance;
};

}

#endif /* YASSI_REPLAY_LOGGER_HPP */
