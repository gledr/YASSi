/**
 * @file yassi_instrumentation_pass.cpp
 * @brief Optimization Pass for Execution Code Instrumentation
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
#include "yassi_instrumentation_pass.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Utils;

char CheckModel::ID = 0;
static llvm::RegisterPass<CheckModel> CheckModel( "instr_check_model" ,"Instrument for Model Checking");


CheckModel::CheckModel():
    BasePass(),
    ModulePass(CheckModel::ID)
{
}

CheckModel::~CheckModel()
{
}

bool CheckModel::runOnModule(llvm::Module & M)
{
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Starting Instrumentation Pass...") << std::endl;
    p_verbose && std::cerr << "FillNamesPass" << std::flush << std::endl;
    {
        FillNamesPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "CleanPhiNodes" << std::endl; 
    {
        CleanPhiPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "SwitchInstr" << std::endl;
    {
        SwitchPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "SeparateGetElm" << std::endl;
    {
        SeperateGetElePtrPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "SeperateCastInstr" << std::endl;
    {
        SeperateCastInstrPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ChMallocFree" << std::endl;
    {
        ChangeMallocFreePass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ChPrintf" << std::endl;
    {
        ChangePrintfPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "FillNamesPass" << std::endl;
    {
        FillNamesPass pass;
        pass.runOnModule(M);
    }
    //p_verbose && std::cerr << "CmdLineArgs" << std::endl;
    {
        //CommandLineArgumentsPass pass;
        //pass.runOnModule(M);
    }
    p_verbose && std::cerr << "RmErrorFn" << std::endl;
    {
        RemoveErrorFunctionPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "GlobalInit" << std::endl;
    {
        GlobalInitPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "BbMarks" << std::endl;
    {
        BasicBlocksPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "CallInstr" << std::endl;
    {
        FunctionCallPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "SelectInstr" << std::endl;
    {
        SelectPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "BinaryOp" << std::endl;
    {
        BinaryOpPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "CastInstr" << std::endl;
    {
        CastPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "LoadStore" << std::endl;
    {
        LoadStorePass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "IcmpInstr" << std::endl;
    {
        ComparePass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "BrInstr" << std::endl;
    {
        BranchPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "FnMarks" << std::endl;
    {
        FunctionsPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "AllocaInstr" << std::endl;
    {
        AllocaPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "BeginEnd" << std::endl;
    {
        BeginEndPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "GetelementPtr" << std::endl;
    {
        GetElementPtrPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "Memcpy" << std::endl;
    {
        MemcpyPass  pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "Memset" << std::endl;
    {
        MemsetPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ChAssumeFn" << std::endl;
    {
        ChangeAssumeFunctionPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ChAssertFn" << std::endl;
    {
        ChangeAssertFunctionPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ChErrorFn" << std::endl;
    {
        ChangeErrorFunctionPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "FPointerhook" << std::endl;
    {
        FunctionPointerPass pass;
        pass.runOnModule(M);
    }
    p_verbose && std::cerr << "ExportFunctions" << std::endl;
    {
        ExploreExternalFunctionsPass pass;
        pass.runOnModule(M);
    }
    //p_verbose && std::cerr << "RmInstr" << std::endl;
    {
    //    RemoveInstructionsPass pass;
    //    pass.runOnModule(M);
    }
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Instrumentation Pass Finished") << std::endl;
    p_verbose && std::cerr << std::endl;
    
    return false;
}
