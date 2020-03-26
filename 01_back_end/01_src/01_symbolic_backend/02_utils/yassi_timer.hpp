#ifndef YASSI_BACKEND_TIMER_HPP
#define YASSI_BACKEND_TIMER_HPP

#include <chrono>
#include <map>

#include <yassi_object.hpp>
#include <yassi_database.hpp>

namespace Yassi::Backend::Execute {
    
enum eBackendOps {eBeginSim, 
                  eEndSim,
                  eStore,
                  eLoad,
                  eAlloca,
                  eCmp,
                  eBeginBb,
                  eEndBb,
                  eBeginFn,
                  eEndFn,
                  eCast,
                  eBinOp,
                  eReturn,
                  eGlobalVarInit,
                  eGEOP,
                  eFnCall,
                  eFnCallPost,
                  eSelOp,
                  eMemCpy,
                  eMemSet,
                  eAssume,
                  eAssert};
    
class Timer: public virtual Object {
public:
    Timer(Database* database);
    
    virtual ~Timer();
    
    void start_timer(eBackendOps const & op);
    
    void end_timer(eBackendOps const & op);
    
    void results_to_db();
    
private:
    Database* p_database;
    
    std::map<eBackendOps, std::chrono::time_point<std::chrono::system_clock>> p_start_times;
    std::map<eBackendOps, std::chrono::time_point<std::chrono::system_clock>> p_end_times; 
    std::map<eBackendOps, double> p_old_results;
    std::map<eBackendOps, std::string> p_enum_dictionary;
    std::map<std::string, eBackendOps> p_string_dictionary;

    void init_dictionaries();
};

}

#endif /* YASSI_BACKEND_TIMER_HPP */
