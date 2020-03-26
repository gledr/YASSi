#include "yassi_cleanphi.hpp"

using namespace Yassi::OptPass::Execute;

char CleanPhiPass::ID = 0;

CleanPhiPass::CleanPhiPass(): 
    InstrBase(), llvm::ModulePass(CleanPhiPass::ID) 
{

}

CleanPhiPass::~CleanPhiPass() 
{

}

bool CleanPhiPass::runOnModule(llvm::Module& M) 
{
    bool changed = false;
    
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::PHINode>(in)) {
                    llvm::PHINode *reference = llvm::dyn_cast<llvm::PHINode>(in);
      
                    std::set<llvm::Value*> phis;
                    phis.insert(reference);

                    size_t numBlocks = reference->getNumIncomingValues();
                    for (++in; llvm::isa<llvm::PHINode>(*in); ++in) {
                        llvm::PHINode *pi = llvm::dyn_cast<llvm::PHINode>(in);

                        assert(numBlocks == pi->getNumIncomingValues());

                        size_t i = 0;
                        // see if it is out of order
                        for (i = 0; i <numBlocks; i++) {
                            if (pi->getIncomingBlock(i) != reference->getIncomingBlock(i)){
                                break;
                            }
                        }

                        if (i != numBlocks) {
                            std::vector<llvm::Value*> values;
                            values.reserve(numBlocks);
                            for (unsigned i = 0; i<numBlocks; i++){
                                values.push_back(pi->getIncomingValueForBlock(reference->getIncomingBlock(i)));
                            }
                            for (unsigned i = 0; i<numBlocks; i++) {
                                pi->setIncomingBlock(i, reference->getIncomingBlock(i));
                                pi->setIncomingValue(i, values[i]);
                            }
                            changed = true;
                        }

                        // see if it uses any previously defined phi nodes
                        for (i=0; i<numBlocks; i++) {
                            llvm::Value *value = pi->getIncomingValue(i);

                            if (phis.find(value) != phis.end()) {
                                // fix by making a "move" at the end of the incoming block
                                // to a new temporary, which is thus known not to be a phi
                                // result. we could be somewhat more efficient about this
                                // by sharing temps and by reordering phi instructions so
                                // this isn't completely necessary, but in the end this is
                                // just a pathological case which does not occur very
                                // often.
                                llvm::Instruction *tmp = 
                                    new llvm::BitCastInst(value, 
                                    value->getType(),
                                    value->getName() + ".phiclean",
                                    pi->getIncomingBlock(i)->getTerminator());
                                    pi->setIncomingValue(i, tmp);
                            }
                            changed = true;
                        }
                        phis.insert(pi);
                    }
                }
            }
        }
        return changed;
    }
}    
