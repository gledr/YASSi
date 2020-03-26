/** 
 * @file yassi_executor.cpp
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
#include "yassi_executor.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
Executor::Executor()
{
    p_bitcode = new Bitcode();
    p_checkmodel = new CheckModel();
    p_common = new Common();
    p_replay = new Replay();
    p_bdd = new BDD();
    p_error_local = new ErrorLocalization();
    p_test_vectors = new TestVectors();
}

/**
 * @brief Destructor
 */
Executor::~Executor()
{
    delete p_bitcode; p_bitcode = nullptr;
    delete p_checkmodel; p_checkmodel = nullptr;
    delete p_common; p_common = nullptr;
    delete p_replay; p_replay = nullptr;
    delete p_bdd; p_bdd = nullptr;
    delete p_error_local; p_error_local = nullptr;
    delete p_test_vectors; p_test_vectors = nullptr;
}

/**
 * @brief Execute the Commandline Configured Target
 * 
 * @param target: The target to execute
 */
void Executor::runTarget(eTarget const target)
{
    try {
        if(target == eInit) {
            // No Dependency
        } else if(target == eClean) {
            p_common->clean_environment();
        } else if (target == eMakeBitcode) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
        } else if (target == eInstrumentCheckModel) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
        } else if (target == eLinkCheckModelBinary) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
        } else if (target == eRunCheckModelBackend) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
        } else if (target == eCheckModelResults) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
            p_checkmodel->check_results();
        } else if (target == eShowBC) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_bitcode->show_bitcode();
        } else if (target == eShowCFG) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_bitcode->show_cfg();
        } else if (target == eCompareBC) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->compare_bitcode();
        } else if (target == eInstrumentReplay) {
            p_bitcode->generate_bitcode();
            p_replay->instrument_bitcode();
        } else if (target == eLinkReplay) {
            p_bitcode->generate_bitcode();
            p_replay->instrument_bitcode();
            p_replay->generate_replay_binary();
        } else if (target == eRunReplay) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
            p_test_vectors->test_vectors_to_db();
            p_replay->instrument_bitcode();
            p_replay->generate_replay_binary();
            p_replay->run_replay();
        } else if (target == eCompareReplayBC) {
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
            p_test_vectors->test_vectors_to_db();
            p_replay->instrument_bitcode();
            p_replay->compare_bitcode();
        } else if (target == eShowModelCheckCFG) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->show_cfg();
        } else if (target == eShowReplayResult) {
            p_replay->show_result();
        } else if (target == eCheckModelGoldResult) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
            p_checkmodel->get_gold_result();
        } else if (target == eShowResultsCheckModel) {
            p_checkmodel->show_results(eDatabase);
        } else if (target == eShowExceptionCheckModel) {
            p_checkmodel->show_exceptions(eDatabase);
        } else if (target == eConstructBDD) {
            p_bdd->construct_bdd();
        } else if (target == eShowBDD) {
            p_bdd->show_bdd();
        } else if (target == eDebugInstrument) {
            p_error_local->instrument_bitcode();
        } else if (target == eDebugLinkBinary) {
            p_error_local->generate_backend_binary();
        } else if (target == eDebugRun) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_error_local->instrument_bitcode();
            p_error_local->generate_backend_binary();
            p_error_local->run_backend_binary();
        } else if (target == eTestVectorsToDatabase) {
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->link_backend_binary();
            p_checkmodel->execute_backend();
            p_test_vectors->test_vectors_to_db();
        } else if (target == eShowTestVectors) {
            p_test_vectors->test_vectors_to_db();
            p_test_vectors->show_test_vectors();
        } else if (target == eShowGoldenResults){
            p_checkmodel->show_results(eGoldenResult);
        } else if (target == eShowGoldenExceptions){
            p_checkmodel->show_exceptions(eGoldenResult);
        } else if (target == eShowDB){
            p_common->show_db();
        } else if (target == eRunMemoryCheck){
            p_common->clean_environment();
        } else if (target == eShowBB){
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_bitcode->show_bb();
        } else if (target == eShowReplayBB){
            p_replay->show_bb();
        } else if (target == eShowInstrBC){
            p_common->clean_environment();
            p_bitcode->generate_bitcode();
            p_checkmodel->instrument_bitcode();
            p_checkmodel->show_instr_bitcode();
        }
    } catch (YassiException const & exp){
        std::cerr << BaseUtils::get_bash_string_blink_red("Execution Terminated due to error!") << std::endl;
        std::cerr << BaseUtils::get_bash_string_blink_red(exp.what()) << std::endl;
    }
}
