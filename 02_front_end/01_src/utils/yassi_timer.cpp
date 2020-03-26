#include "yassi_timer.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


Timer::Timer():
    Object()
{
    
}

Timer::~Timer()
{
    
}

void Timer::start_timer(eTimerBinary const & target)
{
    p_start_times[target] = std::chrono::system_clock::now();
}

void Timer::end_timer(eTimerBinary const & target)
{
    p_end_times[target] = std::chrono::system_clock::now();
}

void Timer::results_to_db()
{
    for(auto& itor : p_start_times){
        std::chrono::time_point<std::chrono::system_clock> begin = p_start_times[itor.first];
        std::chrono::time_point<std::chrono::system_clock> end   = p_end_times[itor.first];
        
        double time_in_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count();
        
        std::stringstream query;
        query << "insert into timer values ('" << enum_to_string(itor.first) << "'," << time_in_ms << ");";
        p_database->db_command(query.str());
    }
}

std::string Timer::enum_to_string(eTimerBinary const & item)
{
    if (item == eCheckModel){
        return this->get_modelcheck_backend_name();
    } else if (item == eReplay){
        return this->get_replay_backend_name();
    } else if (item == eErrorLocal){
        return "error";
    } else {
        throw YassiException("Unknown Enum!");
    }
}
