#include "yassi_testengine.hpp"

using namespace Yassi;
using namespace Yassi::Utils;

std::string yassi_frontend_binary;
std::string yassi_tmp_path;

TestEngine::TestEngine() {

    std::string base_path;
    std::string home_path = getenv("HOME");
    std::fstream ini_file(home_path + "/.yassi/config.txt", std::ios::in);
    ini_file >>  base_path;
    std::vector<std::string> token = BaseUtils::tokenize(base_path, "=");
    base_path = token[1] + "/";
    
    ini_file.close();
    
    yassi_frontend_binary = base_path + "/08_bin/yassi --quiet";
    yassi_tmp_path = BaseUtils::get_tmp_folder();
}

bool TestEngine::CompareResult (std::string const & current_path){
    
    ResultChecker * p_checker = new ResultChecker(current_path, yassi_tmp_path);
    
    eCmpStatus status = p_checker->check_results();
   
    delete p_checker; p_checker = nullptr;
    
    return status == eSUCCESS;    
}

TestEngine::~TestEngine() {
    
}

int TestEngine::RunAll() {
    return RUN_ALL_TESTS();
}

void TestEngine::InitEngine(int argc, char ** argv) {
    testing::InitGoogleTest(&argc, argv);
}

#ifdef YASSI_TEST_SIMPLE
    #include "unittest_simple.hpp"
#endif

#ifdef YASSI_TEST_EXCEPTIONS
    #include "unittest_exceptions.hpp"
#endif
