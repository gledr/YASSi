#include "yassi_changemainmeasure.hpp"

using namespace Yassi::OptPass::Replay;
using namespace Yassi::Types;
using namespace Yassi::Utils;

char ChangeMainMeasurePass::ID = 0;

ChangeMainMeasurePass::ChangeMainMeasurePass(): 
    ReplayBase(), llvm::ModulePass(ChangeMainMeasurePass::ID) 
{

}

ChangeMainMeasurePass::~ChangeMainMeasurePass() 
{

}

bool ChangeMainMeasurePass::runOnModule(llvm::Module& M)  
{
    M.getFunction("main")->setName("test");
    llvm::Value* InitFn = llvm::cast<llvm::Value> ( M.getFunction( "test" ));
    p_test_vector_variables = p_db->get_test_vector_variables();
    
    std::vector<TestVector> test_vectors = p_db->get_test_vectors();

    size_t iterations = std::stoi(test_vectors.back().vector_id) + 1; // IDs start with 0
    this->insert_main_function_calling(InitFn, M, iterations);

    return false;
}

void ChangeMainMeasurePass::insert_main_function_calling(llvm::Value* func_test, llvm::Module & M, size_t const iterations)
{
    llvm::FunctionType* func_type = llvm::TypeBuilder<int(int, char**), false>::get(M.getContext());
    llvm::Function* func_main = llvm::Function::Create(func_type, llvm::GlobalValue::ExternalLinkage, "main", &M);
    
    llvm::BasicBlock* label_entry = llvm::BasicBlock::Create(M.getContext(), "entry",func_main,0);
    llvm::BasicBlock* label_bb = llvm::BasicBlock::Create(M.getContext(), "bb",func_main,0);
    llvm::BasicBlock* label_bb2 = llvm::BasicBlock::Create(M.getContext(), "bb2",func_main,0);

    // Block entry (label_entry)
    llvm::BranchInst::Create(label_bb, label_entry);
    
    // Block bb (label_bb)
    llvm::Argument* fwdref_16 = new llvm::Argument(llvm::IntegerType::get(M.getContext(), 32));
    llvm::PHINode* int32_i_04 = llvm::PHINode::Create(llvm::Type::getInt32Ty(M.getContext()), 2, "index", label_bb);
    llvm::ConstantInt* const_int32_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("0"), 10));
    int32_i_04->addIncoming(const_int32_10, label_entry);
    int32_i_04->addIncoming(fwdref_16, label_bb);
    
    for(auto& it : p_test_vector_variables) {
        llvm::Function* func_vector;
        llvm::GlobalVariable* global_var;
        BaseType* type = p_type_factory->get_type_by_identifier(it.type);
        
        if (type->is_int8()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<char(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_CHAR, vector_type));
            global_var = this->make_global_int(M, it.position, type->get_bits());
        
        } else if(type->is_int16()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<short(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_SHORT, vector_type));
            global_var = this->make_global_int(M, it.position, type->get_bits());

        } else if (type->is_int32()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<int(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_INT, vector_type));
            global_var = this->make_global_int(M, it.position, type->get_bits());

        } else if (type->is_int64()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<long(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_LONG, vector_type));
            global_var = this->make_global_int(M, it.position, type->get_bits());

        } else if (type->is_float()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<float(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_FLOAT, vector_type));
            global_var = this->make_global_float(M, it.position);

        } else if (type->is_double()) {
            llvm::FunctionType* vector_type = llvm::TypeBuilder<float(char*), false>::get(M.getContext());
            func_vector = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_VECTOR_DOUBLE, vector_type));
            global_var = this->make_global_double(M, it.position);

        } else {
            std::cerr << it.type << std::endl;
            assert(0 && "Unknown type");
        }

        llvm::Constant* const_array_9 = llvm::ConstantDataArray::getString(M.getContext(), it.name, true);
        std::vector<llvm::Constant*> const_ptr_11_indices;
        const_ptr_11_indices.push_back(llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("0"), 10)));
        const_ptr_11_indices.push_back(llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("0"), 10)));
        llvm::GlobalVariable* gvar_array__str = new llvm::GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(M.getContext(), 8), it.name.length() + 1), true,
                llvm::GlobalValue::PrivateLinkage, 0, this->make_global_name(it.name));
        gvar_array__str->setInitializer(const_array_9);
        llvm::CallInst* int32_17 = llvm::CallInst::Create(func_vector,
                                   llvm::ConstantExpr::getGetElementPtr(NULL, gvar_array__str, const_ptr_11_indices),
                                   "",
                                   label_bb);

        new llvm::StoreInst(int32_17, global_var, false, label_bb);
    }
    
    llvm::Value* test_fun = llvm::CallInst::Create(func_test, "", label_bb);

    llvm::FunctionType* next_trace_type = llvm::TypeBuilder<void(void), false>::get(M.getContext());
    llvm::Function* next_trace_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction("next_trace", next_trace_type));
    
    std::vector<llvm::Value*> params;
    llvm::CallInst::Create(next_trace_fun, params, "", llvm::cast<llvm::Instruction>(test_fun));

    llvm::BinaryOperator* int32_20 = llvm::BinaryOperator::Create(llvm::Instruction::Add, int32_i_04, llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("1"), 10)), "", label_bb);
    llvm::ConstantInt* const_int32_14 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef(std::to_string(iterations)), 10));
    llvm::ICmpInst* int1_exitcond = new llvm::ICmpInst(*label_bb, llvm::ICmpInst::ICMP_EQ, int32_20, const_int32_14, "exitcond");
    llvm::BranchInst::Create(label_bb2, label_bb, int1_exitcond, label_bb);

    // Block bb2 (label_bb2)
    llvm::ReturnInst::Create(M.getContext(), const_int32_10, label_bb2);

    // Resolve Forward References
    fwdref_16->replaceAllUsesWith(int32_20);
    delete fwdref_16;
}
