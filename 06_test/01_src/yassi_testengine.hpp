#ifndef TESTENGINE_HPP
#define TESTENGINE_HPP

#include <gtest/gtest.h>
#include <json/json.h>
#include <iterator>
#include <fstream>
#include <algorithm>

#include <boost/filesystem.hpp>

#include <yassi_database.hpp>
#include <yassi_baseutils.hpp>
#include <yassi_resultchecker.hpp>
#include <yassi_exception.hpp>

#define YASSI_TEST_SIMPLE
//#define YASSI_TEST_EXCEPTIONS

namespace Yassi {

class TestEngine {
public:
    TestEngine();
    
    ~TestEngine();
    
    void InitEngine(int argc, char ** argv);
    
    int RunAll();
    
    static bool CompareResult(std::string const & current_path);
};

}

#endif /* TESTENGINE_HPP */
