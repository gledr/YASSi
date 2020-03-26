/** 
 * @file yassi_executor.hpp
 * @brief Yassi Executor is Controlling the Execution of Yassi
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
#ifndef YASSI_EXECUTOR_HPP
#define YASSI_EXECUTOR_HPP

#include <yassi_bitcode.hpp>
#include <yassi_checkmodel.hpp>
#include <yassi_replay.hpp>
#include <yassi_common.hpp>
#include <yassi_errorlocalization.hpp>
#include <yassi_bdd.hpp>
#include <yassi_testvectors.hpp>

namespace Yassi::Frontend {

enum eTarget {eInit                         = 0,  ///< Default Target
              eClean                        = 1,  ///< Clean Environment
              eMakeBitcode                  = 2,  ///< Compile LLVM Bitcode
              eInstrumentCheckModel         = 3,  ///< Instrument Bitcode Execute
              eLinkCheckModelBinary         = 4,  ///< Link Backend Binary
              eRunCheckModelBackend         = 5,  ///< Execute Backend
              eCheckModelResults            = 6,  ///< Check Generated Results
              eShowBC                       = 7,  ///< Show Bitcode
              eShowCFG                      = 8,  ///< Show Call Flow Graph
              eCompareBC                    = 9,  ///< Compare Bitcode with instrumented Bitcode
              eListExternalFunctions        = 10, ///< List External (not instrumented) functions
              eInstrumentReplay             = 11, ///< Instrument Bitcode Replay
              eLinkReplay                   = 12, ///< Link Replay Binary
              eRunReplay                    = 13, ///< Run Replay Binary
              eCompareReplayBC              = 14, ///< Comapare with Replay Bitcode
              eShowModelCheckCFG            = 15, ///< Show Instrumented Bitcode CFG
              eShowReplayResult             = 16, ///< Show Replay Coverage
              eCheckModelGoldResult         = 17, ///< Get Golden Result 
              eShowResultsCheckModel        = 18, ///< Show Results
              eShowExceptionCheckModel      = 19, ///< Show Exceptions
              eShowCheckModelTimer          = 20, ///< Show Timer
              eConstructBDD                 = 21, ///< Create BDD from Clauses
              eShowBDD                      = 22, ///< Show BDD
              eShowTestVectors              = 23, ///< Show Generated Test Vectors
              eDebugInstrument              = 24, ///< Instrument Debug Bitcode
              eDebugLinkBinary              = 25, ///< Link Debug Binary
              eDebugRun                     = 26, ///< Run Debug Binary
              eTestVectorsToDatabase        = 27, ///< Store Test Vectors to Database
              eShowGoldenResults            = 28, ///< Show Golden Results
              eShowGoldenExceptions         = 29, ///< Show Golden Exceptions
              eShowDB                       = 30, ///< Show Database
              eRunMemoryCheck               = 31, ///< Run Check for Memory Leaks
              eShowBB                       = 32, ///< Show Basic Blocks
              eShowReplayBB                 = 33, ///< Show Replayed Basic Blocks
              eShowInstrBC                  = 34  ///< Show Instrumented Bitcode
    };

class Executor {
public:
    Executor();

    virtual ~Executor();

    void runTarget(eTarget const target);

private:
    Bitcode* p_bitcode;
    CheckModel* p_checkmodel;
    Common* p_common;
    Replay* p_replay;
    BDD* p_bdd;
    ErrorLocalization* p_error_local;
    TestVectors* p_test_vectors;
};

}

#endif /* YASSI_EXECUTOR_HPP */
