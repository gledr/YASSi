/**
 * @file yassi_instrumentation_pass.hpp
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
#ifndef YASSI_INSTRUMENTATION_PASS
#define YASSI_INSTRUMENTATION_PASS

/*
 * Resolve include files for the usage of an IDE and code completion.
 * For the compilation itself, the files are located in the same folder.
 */ 
#ifdef YASSI_INSTR_PASS
    #include "yassi_basepass.hpp"
    #include "yassi_basicblocks.hpp"
    #include "yassi_functions.hpp"
    #include "yassi_alloca.hpp"
    #include "yassi_beginend.hpp"
    #include "yassi_binaryop.hpp"
    #include "yassi_compare.hpp"
    #include "yassi_loadstore.hpp"
    #include "yassi_cast.hpp"
    #include "yassi_memset.hpp"
    #include "yassi_memcpy.hpp"
    #include "yassi_functioncall.hpp"
    #include "yassi_switch.hpp"
    #include "yassi_branch.hpp"
    #include "yassi_select.hpp"
    #include "yassi_getelementptr.hpp"
    #include "yassi_globalinit.hpp"
    #include "yassi_functionpointer.hpp"
    #include "yassi_seperategeteleptr.hpp"
    #include "yassi_seperatecastinstr.hpp"
    #include "yassi_fillnames.hpp"
    #include "yassi_removeinstructions.hpp"
    #include "yassi_removeerrorfunction.hpp"
    #include "yassi_changeassertfunction.hpp"
    #include "yassi_changeprintf.hpp"
    #include "yassi_changeassumefunction.hpp"
    #include "yassi_changeerrorfunction.hpp"
    #include "yassi_changemallocfree.hpp"
    #include "yassi_demangle.hpp"
    #include "yassi_listexternalfunctions.hpp"
    #include "yassi_explore_external_functions.hpp"
    #include "yassi_cmdline_arguments.hpp"
    #include "yassi_cleanphi.hpp"
#else
    #include "../00_GenericPasses/01_src/yassi_basepass.hpp"
    #include "../00_GenericPasses/01_src/yassi_demangle.hpp"
    #include "../00_GenericPasses/01_src/yassi_listexternalfunctions.hpp"
    #include "../00_GenericPasses/01_src/yassi_fillnames.hpp"
    #include "01_src/yassi_basicblocks.hpp"
    #include "01_src/yassi_functions.hpp"
    #include "01_src/yassi_branch.hpp"
    #include "01_src/yassi_beginend.hpp"
    #include "01_src/yassi_alloca.hpp"
    #include "01_src/yassi_binaryop.hpp"
    #include "01_src/yassi_compare.hpp"
    #include "01_src/yassi_loadstore.hpp"
    #include "01_src/yassi_cast.hpp"
    #include "01_src/yassi_memset.hpp"
    #include "01_src/yassi_memcpy.hpp"
    #include "01_src/yassi_functioncall.hpp"
    #include "01_src/yassi_switch.hpp"
    #include "01_src/yassi_select.hpp"
    #include "01_src/yassi_getelementptr.hpp"
    #include "01_src/yassi_globalinit.hpp"
    #include "01_src/yassi_functionpointer.hpp"
    #include "01_src/yassi_seperategeteleptr.hpp"
    #include "01_src/yassi_seperatecastinstr.hpp"
    #include "01_src/yassi_removeinstructions.hpp"
    #include "01_src/yassi_removeerrorfunction.hpp"
    #include "01_src/yassi_changeassertfunction.hpp"
    #include "01_src/yassi_changeprintf.hpp"
    #include "01_src/yassi_changeassumefunction.hpp"
    #include "01_src/yassi_changeerrorfunction.hpp"
    #include "01_src/yassi_changemallocfree.hpp"
    #include "01_src/yassi_cmdline_arguments.hpp"
    #include "01_src/yassi_cleanphi.hpp"
#endif

namespace Yassi::OptPass::Execute {

class CheckModel: public llvm::ModulePass, public virtual Yassi::OptPass::BasePass {
public:
    CheckModel();
    
    virtual ~CheckModel();

    bool runOnModule(llvm::Module & M) override;

    static char ID;
};

}

#endif /* YASSI_INSTRUMENTATION_PASS */
