#ifndef YASSI_REPLAY_HPP
#define YASSI_REPLAY_HPP

#include <iomanip>

#include <boost/filesystem.hpp>

#include <yassi_object.hpp>
#include <yassi_timer.hpp>
#include <yassi_logger.hpp>
#include <yassi_common.hpp>

namespace Yassi {

namespace Frontend {

class Replay: public virtual Object {
public:
    Replay();
    
    virtual ~Replay();
    
    void instrument_bitcode();
    
    void generate_replay_binary();
    
    void run_replay();
    
    void compare_bitcode();
    
    void show_result();
    
    void show_bb();
    
private:
    Common* p_common;
    
    Timer* p_timer;
    Logger* p_logger;
    
    /**
     * @brief 
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_first_ll(std::string const & filename)
    {
        return filename + ".ll";
    }
    
    /**
     * @brief 
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_second_bc(std::string const & filename)
    {
        return "replay_" + filename + "-1.bc";
    }
    
    /**
     * @brief
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_second_ll(std::string const & filename)
    {
        return "replay_" + filename + "-1.ll";
    }
    /**
     * @brief
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_third_bc(std::string const & filename)
    {
        return "replay_" + filename + "-2.bc";
    }
    
    /**
     * @brief
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_third_obj(std::string const & filename)
    {
        return "replay_" + filename + "-2.o";
    }
    
    /**
     * @brief
     * 
     * @param filename
     * @return std::string
     */
    inline std::string make_third_ll(std::string const & filename)
    {
        return "replay_" + filename + "-2.ll";
    }
};

}

}

#endif /* YASSI_REPLAY_HPP */
