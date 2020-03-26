#include "yassi_timer.hpp"

using namespace Yassi::Backend::Execute;


/**
 * @brief ...
 * 
 * @param database p_database:...
 */
Timer::Timer(Database* database):
    Object()
{
    p_database = database;
    this->init_dictionaries();
}

/**
 * @brief ...
 * 
 */
Timer::~Timer()
{
}

/**
 * @brief ...
 * 
 * @param op p_op:...
 */
void Timer::start_timer(eBackendOps const & op)
{
    p_start_times[op] = std::chrono::system_clock::now();
}

/**
 * @brief ...
 * 
 * @param op p_op:...
 */
void Timer::end_timer(eBackendOps const & op)
{
    p_end_times[op] = std::chrono::system_clock::now();
    
    std::chrono::time_point<std::chrono::system_clock> begin = p_start_times[op];
    std::chrono::time_point<std::chrono::system_clock> end   = p_end_times[op];
    double time_in_ms = std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
    
    double total_ms = p_old_results[op] + time_in_ms;
    p_old_results[op] = total_ms;
}

/**
 * @brief ...
 */
void Timer::results_to_db()
{
    std::vector<std::pair<std::string, std::string>> timer_table = p_database->get_timer_results();
    std::map<eBackendOps, double> stored_values;
    
    for(auto& itor : timer_table){
        stored_values[p_string_dictionary[itor.first]] = std::stod(itor.second);
    }
    
    // Clear Current Timer Table 
    std::stringstream query;
    query << "DROP TABLE timer;";
    p_database->db_command(query.str());
    
    query.str("");
    query << "create table timer(";
    query << "id varchar(50),";
    query << "time_ms float";
    query << ");";
    p_database->db_command(query.str());
    
    for(auto& itor : p_start_times){
       
        query.str("");
        
        double total_time = stored_values[itor.first] + p_old_results[itor.first];
        
        query << "insert into timer values ('" << p_enum_dictionary[itor.first] << "'," << total_time << ");";
        p_database->db_command(query.str());
    }
}

/**
 * @brief ...
 * 
 */
void Timer::init_dictionaries()
{
    p_enum_dictionary[eAlloca]          = "Alloca";
    p_enum_dictionary[eAssert]          = "Assert";
    p_enum_dictionary[eAssume]          = "Assume";
    p_enum_dictionary[eBeginBb]         = "BeginBb";
    p_enum_dictionary[eBeginFn]         = "BeginFn";
    p_enum_dictionary[eBeginSim]        = "BeginSim";
    p_enum_dictionary[eBinOp]           = "BinaryOp";
    p_enum_dictionary[eCast]            = "CastOp";
    p_enum_dictionary[eCmp]             = "CmpOp";
    p_enum_dictionary[eEndBb]           = "EndBb";
    p_enum_dictionary[eEndFn]           = "EndFn";
    p_enum_dictionary[eEndSim]          = "EndSim";
    p_enum_dictionary[eFnCall]          = "FnCall";
    p_enum_dictionary[eFnCallPost]      = "FnCallPost";
    p_enum_dictionary[eGEOP]            = "GetElementPtr";
    p_enum_dictionary[eGlobalVarInit]   = "eGlobalVarInit";
    p_enum_dictionary[eLoad]            = "LoadInstr";
    p_enum_dictionary[eMemCpy]          = "MemCpy";
    p_enum_dictionary[eMemSet]          = "MemSet";
    p_enum_dictionary[eReturn]          = "Return";
    p_enum_dictionary[eSelOp]           = "SelectOp";
    p_enum_dictionary[eStore]           = "StoreInstr";
    
    p_string_dictionary["Alloca"]           = eAlloca;
    p_string_dictionary["Assert"]           = eAssert;
    p_string_dictionary["Assume"]           = eAssume;
    p_string_dictionary["BeginBb"]          = eBeginBb;
    p_string_dictionary["BeginFn"]          = eBeginFn;
    p_string_dictionary["BeginSim"]         = eBeginSim;
    p_string_dictionary["BinaryOp"]         = eBinOp;
    p_string_dictionary["CastOp"]           = eCast;
    p_string_dictionary["CmpOp"]            = eCmp;
    p_string_dictionary["EndBb"]            = eEndBb;
    p_string_dictionary["EndFn"]            = eEndFn;
    p_string_dictionary["eEndSim"]          = eEndSim;
    p_string_dictionary["FnCall"]           = eFnCall;
    p_string_dictionary["FnCallPost"]       = eFnCallPost;
    p_string_dictionary["GetElementPtr"]    = eGEOP;
    p_string_dictionary["eGlobalVarInit"]   = eGlobalVarInit;
    p_string_dictionary["LoadInstr"]        = eLoad;
    p_string_dictionary["MemCpy"]           = eMemCpy;
    p_string_dictionary["MemSet"]           = eMemSet;
    p_string_dictionary["Return"]           = eReturn;
    p_string_dictionary["SelectOp"]         = eSelOp;
    p_string_dictionary["StoreInstr"]       = eStore;
}
