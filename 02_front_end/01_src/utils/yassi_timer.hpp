#ifndef YASSI_FRONTEND_TIMER_HPP
#define YASSI_FRONTEND_TIMER_HPP

#include <chrono>
#include <map>

#include <yassi_object.hpp>

namespace Yassi::Frontend {

enum eTimerBinary {eCheckModel, eReplay, eErrorLocal};

class Timer: public virtual Object {
public:
    Timer();

    virtual ~Timer();

    void start_timer(eTimerBinary const & target);

    void end_timer(eTimerBinary const & target);

    void results_to_db();

private:
    std::map<eTimerBinary, std::chrono::time_point<std::chrono::system_clock>> p_start_times;
    std::map<eTimerBinary, std::chrono::time_point<std::chrono::system_clock>> p_end_times;

    std::string enum_to_string(eTimerBinary const & item);
};

}
#endif /* YASSI_FRONTEND_TIMER_HPP */
