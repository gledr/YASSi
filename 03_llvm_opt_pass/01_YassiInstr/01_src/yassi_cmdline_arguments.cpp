/** 
 * @file yassi_cmdline_arguments.cpp
 * @brief Optimization Pass to handle commandline arguments
 *
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2020 Johannes Kepler University
 * @author Sebastian Pointner
 * @author Pablo Gonzales de Aledo
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
#include "yassi_cmdline_arguments.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Utils;

char CommandLineArgumentsPass::ID = 0;

CommandLineArgumentsPass::CommandLineArgumentsPass(): 
    InstrBase(),
    llvm::ModulePass(CommandLineArgumentsPass::ID) 
{
}

CommandLineArgumentsPass::~CommandLineArgumentsPass() 
{
}

bool CommandLineArgumentsPass::runOnModule(llvm::Module& M) 
{   // Read number of arguments

    //std::string args_str; // = cmd_option_str("sym_argvs");
    std::string args_str = "1 2 3";

    if(args_str == "") return false;
    std::vector<std::string> tokens = BaseUtils::tokenize(args_str, " ");
    int min_argvs = std::stoi(tokens[0]);
    int max_argvs = std::stoi(tokens[1]);
    int max_len   = std::stoi(tokens[2]); max_len++;

    // Finds main Function
    llvm::Function* fn = M.getFunction("main");
    llvm::Function::arg_iterator arg_begin = fn->arg_begin();
    llvm::Function::arg_iterator arg_end   = fn->arg_end();
    if(arg_begin == arg_end) return false;

    llvm::BasicBlock* fnbegin = llvm::cast<llvm::BasicBlock>(fn->begin());
    llvm::Instruction* inbegin = llvm::cast<llvm::Instruction>(fnbegin->begin());

    // Allocate space for argc
    llvm::AllocaInst* argc_addr = new llvm::AllocaInst(llvm::Type::getInt32Ty(M.getContext()), 0, "argc_addr", inbegin);
                      
    // Allocate space for argv
    llvm::PointerType* PointerTy_4 = llvm::PointerType::get(llvm::IntegerType::get(M.getContext(), 8), 0);
    llvm::ArrayType* ArrayTy_3 = llvm::ArrayType::get(PointerTy_4, max_argvs);
    llvm::AllocaInst*  argv_addr   = new llvm::AllocaInst(ArrayTy_3, 0, "argv_addr", inbegin);

    // Allocate space for argvs
    llvm::ArrayType* ArrayTy     = llvm::ArrayType::get(llvm::IntegerType::get(M.getContext(), 8), max_len*max_argvs);
    llvm::AllocaInst*  argvs      = new llvm::AllocaInst(ArrayTy, 0, "argvs", inbegin);

    // Set each argv
    for ( int i = 0; i < max_argvs; i++) {
        llvm::Instruction* ptr_13;
        llvm::Instruction* ptr_14;
        llvm::Instruction* ptr_15;
        {
            std::string elem = std::to_string(i);
            llvm::ConstantInt* const_int64_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef("0"), 10));
            llvm::ConstantInt* const_int64_11 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef(elem), 10));
            std::vector<llvm::Value*> ptr_13_indices;
            ptr_13_indices.push_back(const_int64_10);
            ptr_13_indices.push_back(const_int64_11);
            ptr_13 = llvm::GetElementPtrInst::Create(NULL,argv_addr, ptr_13_indices, "", inbegin);
        }

        {
            std::string elem = std::to_string(max_len*i);
            llvm::ConstantInt* const_int64_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef("0"), 10));
            llvm::ConstantInt* const_int64_11 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef(elem), 10));
            std::vector<llvm::Value*> ptr_14_indices;
            ptr_14_indices.push_back(const_int64_10);
            ptr_14_indices.push_back(const_int64_11);
            ptr_14 = llvm::GetElementPtrInst::Create(NULL,argvs, ptr_14_indices, "", inbegin);
        }
    
        {
            std::string elem = std::to_string(max_len*i + max_len - 1);
            llvm::ConstantInt* const_int64_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef("0"), 10));
            llvm::ConstantInt* const_int64_11 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef(elem), 10));
            std::vector<llvm::Value*> ptr_15_indices;
            ptr_15_indices.push_back(const_int64_10);
            ptr_15_indices.push_back(const_int64_11);
            ptr_15 = llvm::GetElementPtrInst::Create(NULL, argvs, ptr_15_indices, "", inbegin);
        }

        llvm::ConstantInt* const_int64_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(8, llvm::StringRef("0"), 10));
        new llvm::StoreInst(ptr_14, ptr_13, false, inbegin);
        new llvm::StoreInst(const_int64_10, ptr_15, false, inbegin);
    }

    // Load argc and argv
    llvm::LoadInst* argc = new llvm::LoadInst(argc_addr, "argc", false, inbegin);
    //LoadInst* argv = new LoadInst(argv_addr, "argv", false, inbegin);

    // Cast argv instruction
    llvm::PointerType* PointerTy_2 = llvm::PointerType::get(llvm::IntegerType::get(M.getContext(), 8), 0);
    llvm::PointerType* PointerTy_1 = llvm::PointerType::get(PointerTy_2, 0);
    llvm::CastInst* argv_cast = new llvm::BitCastInst(argv_addr, PointerTy_1, "argv_cast", inbegin);

    // Substitute in subsequent instructions
     for(auto bb = fn->begin(), block_end = fn->end(); bb != block_end; ++bb) {
        for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
            if(llvm::isa<llvm::StoreInst>(in) ){
                std::string name = in->getOperand(0)->getName().str();
                if(name == "argc"){
                    in->setOperand(0, argc);
                }
                if(name == "argv"){
                    in->setOperand(0, argv_cast);
                }
            }
        }
    }

    // Icmp for minimum argc
    
    auto insertpos = argv_cast; 
    
    return false;
    while( insertpos->getName() != "retval" ){
        insertpos++; insertpos++;
    }
    
    llvm::ConstantInt* const_int32_4 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef(std::to_string(min_argvs)), 10));
    llvm::ICmpInst* int1_8 = new llvm::ICmpInst(insertpos, llvm::ICmpInst::ICMP_SLT,argc, const_int32_4, "min");

    // Icmp for maximum argc
    llvm::Instruction* insertpos_2 = int1_8;
    llvm::ConstantInt* const_int32_4_2 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef(std::to_string(max_argvs)), 10));
    llvm::ICmpInst* int1_8_2 = new llvm::ICmpInst(insertpos_2, llvm::ICmpInst::ICMP_SGT,argc, const_int32_4_2, "max");

    // First slice
    auto splitpos = int1_8_2; splitpos++; splitpos++;
    fnbegin->splitBasicBlock(splitpos);

    // Second slice
    auto splitpos_2 = int1_8_2; splitpos_2++;
    fnbegin->splitBasicBlock(splitpos_2);

    // Basic Blocks
    llvm::BasicBlock* bb1 = llvm::cast<llvm::BasicBlock>(fn->begin());
    llvm::BasicBlock* bb2 = bb1; bb2++;
    llvm::BasicBlock* bb3 = bb2; bb3++;
    llvm::BasicBlock* bbl = llvm::cast<llvm::BasicBlock>(fn->end()); bbl--;

    // Change terminator
    bb1->getTerminator()->eraseFromParent();
    llvm::BranchInst::Create(bbl,bb2, int1_8_2, bb1);

    // Change terminator
    bb2->getTerminator()->eraseFromParent();
    llvm::BranchInst::Create(bbl,bb3, int1_8, bb2);

    return false;
}
