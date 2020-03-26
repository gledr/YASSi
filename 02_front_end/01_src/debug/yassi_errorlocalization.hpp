#ifndef YASSI_ERRORLOCALIZATION_HPP
#define YASSI_ERRORLOCALIZATION_HPP

#include <yassi_object.hpp>
#include <yassi_bitcode.hpp>
#include <yassi_timer.hpp>

#include <sys/stat.h>

namespace Yassi {
    
namespace Frontend {
    
class ErrorLocalization : public Bitcode {
public:
    ErrorLocalization();
    
    virtual ~ErrorLocalization();
    
    void instrument_bitcode();
    
    void generate_backend_binary();
    
    void run_backend_binary();
    
private:
    Timer* p_timer;
    
    void write_blacklist();
};

}

}

#endif /* YASSI_ERRORLOCALIZATION_HPP */
