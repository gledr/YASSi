/** 
 * @file yassi_datastructuretree_testbench.cpp
 * @brief DatastructureTree Testbench
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include <iostream>
#include <string>

#include "yassi_datastructuretree.hpp"

using namespace Yassi::Utils;

//#define CASE1
//#define CASE2
//#define CASE3
//#define CASE4
//#define CASE5
//#define CASE6
//#define CASE7


int main() {

    DatastructureTree * tree = new DatastructureTree();
#ifdef CASE1
    std::string test_case_1 = "(((0,4)(4,4)(8,4),12),12)";
    std::vector<size_t> index_test_case_1;
    index_test_case_1.push_back(0);
    index_test_case_1.push_back(1);

    std::cout << "Test Case 1 " << test_case_1 << std::endl;
    
    size_t expected_1 = 4;
    tree->read_tree(test_case_1);
    size_t val_1 = tree->get_offset(index_test_case_1);
    
    if(val_1 == expected_1) {
        std::cout << "Test Case 1 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 1 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif

#ifdef CASE2
    std::string test_case_2 = "((0,4),4)";
    std::vector<size_t> index_test_case_2;
    index_test_case_2.push_back(0);

    std::cout << "Test Case 2 " << test_case_2 << std::endl;

    size_t expected_2 = 0;
    tree->read_tree(test_case_2);
    size_t val_2 = tree->get_offset(index_test_case_2);

    if(val_2 == expected_2) {
        std::cout << "Test Case 2 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 2 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif

#ifdef CASE3
    std::string test_case_3 = "((((0,4)(4,4),8)((8,4)(12,4),8),16),16)";
    std::vector<size_t> index_test_case_3;
    index_test_case_3.push_back(0);
    index_test_case_3.push_back(1);
    index_test_case_3.push_back(1);

    std::cout << "Test Case 3 " << test_case_3 << std::endl;

    size_t expected_3 = 12;
    tree->read_tree(test_case_3);
    size_t val_3 = tree->get_offset(index_test_case_3);
    
    if(val_3 == expected_3) {
        std::cout << "Test Case 3 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 3 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif

#ifdef CASE4
    std::string test_case_4 = "(((0,4),4),4)";
    std::vector<size_t> index_test_case_4;
    index_test_case_4.push_back(0);
    index_test_case_4.push_back(0);

    std::cout << "Test Case 4 " << test_case_4 << std::endl;

    size_t expected_4 = 0;
    tree->read_tree(test_case_4);
    size_t val_4 = tree->get_offset(index_test_case_4);

    if(val_4 == expected_4) {
        std::cout << "Test Case 4 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 4 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif

#ifdef CASE5
    std::string test_case_5 = "((((0,1)(1,1)(2,1)(3,1),4)((4,1)(5,1)(6,1)(7,1),4)((8,1)(9,1)(10,1)(11,1),4)((12,1)(13,1)(14,1)(15,1),4)((16,1)(17,1)(18,1)(19,1),4),20),20)";
    tree->read_tree(test_case_5);
    std::vector<size_t> index_test_case_5;
    index_test_case_5.push_back(0);
    index_test_case_5.push_back(2);

    std::cout << "Test Case 5 " << test_case_5 << std::endl;

    size_t expected_5 = 8;
    size_t val_5 = tree->get_offset(index_test_case_5);

    if(val_5 == expected_5) {
        std::cout << "Test Case 5 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 5 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif
    
#ifdef CASE6
    std::string test_case_6 = "((0,1),1)";
    tree->read_tree(test_case_6);
    std::vector<size_t> index_test_case_6;
    index_test_case_6.push_back(0);
    index_test_case_6.push_back(0);

    std::cout << "Test Case 6 " << test_case_6 << std::endl;

    size_t expected_6 = 0;
    size_t val_6 = tree->get_offset(index_test_case_6);

    if(val_6 == expected_6) {
        std::cout << "Test Case 6 Passed" << std::endl << std::endl;
    } else {
        std::cout << "Test Case 6 Failed!" << std::endl << std::endl;
    }
    tree->destroy_tree();
#endif

#ifdef CASE7
    std::string test_case_7 = "(((0,8)(8,4)((12,4)(16,4),1),1),20)";
    tree->read_tree(test_case_7);
    std::vector<size_t> index_test_case_7;
    index_test_case_7.push_back(0);
    index_test_case_7.push_back(2);

    std::cout << "Test Case 7 " << test_case_7 << std::endl;

    auto subtree = tree->subtree();
    for(auto itor: subtree){
        std::cout << itor << std::endl;
    }
    
    size_t expected_7 = 12;
    size_t val_7 = tree->get_offset(index_test_case_7);

    if(val_7 == expected_7) {
        std::cout << "Test Case 7 Passed" << std::endl;
    } else {
        std::cout << "Test Case 7 Failed!" << std::endl;
    }
    tree->destroy_tree();
#endif
    
    delete tree; tree = nullptr;

    return 0;
}
