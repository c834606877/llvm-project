#define DEBUG_TYPE "objdiv"
#include <string>
#include <sstream>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/StringObfuscation.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"


using namespace std;
using namespace llvm;

STATISTIC(GlobalsEncoded, "Counts number of global variables encoded");



class GlobalString {
    public:
        GlobalVariable* Glob;
        unsigned int index;
        int type;

        static const int SIMPLE_STRING_TYPE = 1;
        static const int STRUCT_STRING_TYPE = 2;

        GlobalString(GlobalVariable* Glob) : Glob(Glob), index(-1), type(SIMPLE_STRING_TYPE) {}
        GlobalString(GlobalVariable* Glob, unsigned int index) : Glob(Glob), index(index), type(STRUCT_STRING_TYPE) {}
};

#if 0
namespace {


        class StringObfuscationPass: public llvm::ModulePass {
                public:
                static char ID; // pass identification
                std::vector<GlobalVariable*> staticStrings;

                bool is_flag = false;

                StringObfuscationPass() : ModulePass(ID) {}
                StringObfuscationPass(bool flag) : ModulePass(ID)
                {
                    is_flag = flag;
                }

                virtual bool runOnModule(Module &M) {
                        if(!is_flag)
                            return false;


                        for (Module::global_iterator gi = M.global_begin(), ge = M.global_end();
                                                gi != ge; ++gi) {
                            GlobalVariable *global = &(*gi);
                            std::string section(global->getSection());

                            if (global->getName().str().substr(0,4)==".str"&&
                                  global->isConstant() &&
                                global->hasInitializer() &&
                                isa<ConstantDataSequential>(global->getInitializer()) &&
                                section != "llvm.metadata" &&
                                section.find("__objc_methname") == std::string::npos){

                                ConstantDataArray *str = dyn_cast<ConstantDataArray>(global->getInitializer());

                                if(str == nullptr) {
                                    continue;
                                }
                                staticStrings.push_back(global);

                            }
                        }


                     //   for(Function &F : M) {
                        for (Module::iterator Fref = M.getFunctionList().begin(), Fe = M.getFunctionList().end(); 
                                                    Fref != Fe; ++Fref) {
                            continue;
                            Function *F = &(*Fref);
                            errs() << "String Obfuscation - Processing Function: " << F << "\n";

                            errs().write_escaped(F->getName()) << "\n";

                            errs() << "Function printed\n ";
                            continue;

                            for(BasicBlock &B : *F) {
                                errs() << "Block:\n";
                                errs().write_escaped(B.getName()) << "\n";
                                for(Instruction &I:B) {
                                    errs() << "Instruction \n";

                                    for(Use &arg : I.operands()) {
                                        errs() << "arg \n";
                                        if(isa<GEPOperator>(arg)) {
                                            GEPOperator *gepo = dyn_cast<GEPOperator>(arg);

                                            if(isa<GlobalVariable>(gepo->getPointerOperand())) {

                                                GlobalVariable *gv=dyn_cast<GlobalVariable>(gepo->getPointerOperand());
                                                errs() << "GEPOperator == GlobalVariable" << "\n";
                                                errs() << "GV:" << *gv << "\n";

                                                auto entry = std::find(staticStrings.begin(), staticStrings.end(), gv);
                                                if(entry != staticStrings.end()) {
                                                    errs() << "Found Entry in Static Strings" << "\n";

                                                    LLVMContext &Context = B.getContext();
                                                    IRBuilder<NoFolder> builder(&B);
                                                    builder.SetInsertPoint(&I);

                                                    ConstantDataArray *strObject = dyn_cast<ConstantDataArray>(gv->getInitializer());
                                                    StringRef strRef = strObject->getAsCString();
                                                    const char *constStr = strRef.data();
                                                    size_t constStrSize = strRef.size();

                                                    AllocaInst *decryptStrBuf = builder.CreateAlloca(
                                                        builder.getInt8Ty(),
                                                        builder.getInt32(constStrSize + 1)
                                                        );

                                                    for(size_t i = 0; i< constStrSize; i++) {
                                                        int8_t key = rand()%254+1;
                                                        Value *plaintext = builder.CreateXor(
                                                            ConstantInt::get(Type::getInt8Ty(Context), constStr[i]^key),
                                                            ConstantInt::get(Type::getInt8Ty(Context), key)
                                                            );

                                                        std::vector<Value *> values;
                                                        values.push_back(
                                                            ConstantInt::getIntegerValue(Type::getInt8Ty(Context), APInt(32, i))
                                                            );

                                                        Value *gep = builder.CreateGEP(
                                                            decryptStrBuf,
                                                            values
                                                            );

                                                        Value *store = builder.CreateStore(plaintext,
                                                            gep,true);

                                                    }
                                                    I.setOperand(arg.getOperandNo(), decryptStrBuf);

                                                }

                                            }
                                        }
                                    }
                                }
                            }
                        }

                        while(!staticStrings.empty()) {
                            GlobalVariable *gv = staticStrings.back();
                            staticStrings.pop_back();

                            gv->eraseFromParent();

                        }



        
                        return true;
                }


        };

};


#else

namespace {


        class StringObfuscationPass: public llvm::FunctionPass {
            public:
            static char ID; // pass identification
            std::vector<GlobalVariable*> staticStrings;

            bool is_flag = false;

            StringObfuscationPass() : FunctionPass(ID) {}
            StringObfuscationPass(bool flag) : FunctionPass(ID)
            {
                is_flag = flag;
            }

            bool runOnFunction(Function &F) override {
                bool is_mod = false;

                if(is_flag == false)
                    return false;
//                ++HelloCounter;
                errs() << "Hello: ";
                errs().write_escaped(F.getName()) << '\n';

                    for(BasicBlock &B : F) {
                for(Instruction &I:B) {
                    for(Use &arg : I.operands()) {
//                        errs() << "arg \n";
                        if(isa<GEPOperator>(arg)) {
                            GEPOperator *gepo = dyn_cast<GEPOperator>(arg);

                            if(isa<GlobalVariable>(gepo->getPointerOperand())) {

                                GlobalVariable *gv=dyn_cast<GlobalVariable>(gepo->getPointerOperand());


                                errs() << "GEPOperator == GlobalVariable" << "\n";
                                errs() << "GV:" << *gv << "\n";

                                //auto entry = std::find(staticStrings.begin(), staticStrings.end(), gv);
                                //if(entry != staticStrings.end()) {

                            std::string section(gv->getSection());

                            if (gv->getName().str().substr(0,4)==".str"&&
                                gv->isConstant() &&
                                gv->hasInitializer() &&
                                isa<ConstantDataSequential>(gv->getInitializer()) &&
                                section != "llvm.metadata" &&
                                section.find("__objc_methname") == std::string::npos){

                                    errs() << "Found Entry in Static Strings" << "\n";

                                    LLVMContext &Context = B.getContext();
                                    IRBuilder<NoFolder> builder(&B);
                                    builder.SetInsertPoint(&I);

                                    ConstantDataArray *strObject = dyn_cast<ConstantDataArray>(gv->getInitializer());
                                    StringRef strRef = strObject->getAsCString();
                                    const char *constStr = strRef.data();
                                    size_t constStrSize = strRef.size();

                                    AllocaInst *decryptStrBuf = builder.CreateAlloca(
                                        builder.getInt8Ty(),
                                        builder.getInt32(constStrSize + 1)
                                        );

                                    for(size_t i = 0; i< constStrSize; i++) {
                                        int8_t key = rand()%254+1;
                                        Value *plaintext = builder.CreateXor(
                                            ConstantInt::get(Type::getInt8Ty(Context), constStr[i]^key),
                                            ConstantInt::get(Type::getInt8Ty(Context), key)
                                            );

                                        std::vector<Value *> values;
                                        values.push_back(
                                            ConstantInt::getIntegerValue(Type::getInt8Ty(Context), APInt(32, i))
                                            );

                                        Value *gep = builder.CreateGEP(
                                            decryptStrBuf,
                                            values
                                            );

                                        Value *store = builder.CreateStore(plaintext,
                                            gep,true);

                                    }
                                    I.setOperand(arg.getOperandNo(), decryptStrBuf);
                                    is_mod = true;


                                }
                            }

                            }
                        }
                    }
                }



                  return is_mod;
                }




            };



};

#endif



char StringObfuscationPass::ID = 0;
static RegisterPass<StringObfuscationPass> X("GVDiv", "Global variable (i.e., const char*) diversification pass", false, true);

Pass * llvm::createStringObfuscationPass(bool flag) {
    return new StringObfuscationPass(flag);
}
