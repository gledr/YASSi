#include <iostream>
#include <string>
#include <vector>
#include <fstream>

#include <boost/range.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>

#include <yassi_baseutils.hpp>

int main (){
    std::string dir;
    std::vector<std::string> single_directories;
    std::string name;
    std::cout << "Yassi Unittest Directory Exporter" << std::endl;
    std::cout << "Please the absolute path to the directory!" << std::endl;
    std::cout << "Input:";
    std::cin >> dir;

    if(!boost::filesystem::exists(dir)){
        std::cerr << "Invalid Directory Entered!" << std::endl;
    }

    std::vector<std::string> url;
    boost::split(url,dir,boost::is_any_of("/"));
    if(url.back().empty()){
        name = url[url.size()-2];
    } else {
        name = url.back();
    }

    std::fstream file("unittest_" + name + ".hpp", std::ios::out);

    file << "/*" << std::endl;
    file << " * Generated File - do not modify!" << std::endl,
    file << " * File has been generated using the Yassi Unittest Case Exporter" << std::endl;
    file << "*/" << std::endl;
    file << std::endl;
    
    boost::filesystem::path base_path = boost::filesystem::path(Yassi::Utils::BaseUtils::get_base_path());
    
    for(auto& file : boost::make_iterator_range(boost::filesystem::directory_iterator(dir), {})){
        single_directories.push_back(file.path().string());
    }

    for(auto& test_case : single_directories){
        if(boost::filesystem::is_directory(test_case)){                
            std::vector<std::string> token;
            boost::filesystem::path relative_path = boost::filesystem::relative(test_case, base_path);
            std::cout << relative_path.string() << std::endl;
            boost::split(token, test_case, boost::is_any_of("/"));
            file << "TEST(" << token.back() << ", " << name << ")" << std::endl;
            file << "{" << std::endl;
            file << "\tstd::string current_base_path = BaseUtils::get_base_path();" << std::endl;
            file << "\tboost::filesystem::current_path(current_base_path + \"/" + relative_path.string() << "\");" << std::endl;
            file << "\tsystem(yassi_frontend_binary.c_str());" << std::endl;
            file << "\tbool result = TestEngine::CompareResult(current_base_path + \"/" + relative_path.string() << "\");" << std::endl;
            file << "\tASSERT_EQ(result, true);" << std::endl;
            file << "}" << std::endl;
            file << std::endl;
        } 
    }

    file.close();

    return 0;
}
