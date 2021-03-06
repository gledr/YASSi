#include "yassi_testengine.hpp"

#include <memory>

int main(int argc, char **argv) {
   
    std::shared_ptr<Yassi::TestEngine> yassi_test(new Yassi::TestEngine());
    yassi_test->InitEngine(argc, argv);
    yassi_test->RunAll();
    
    return 0;
}
