#include <stdio.h>
#include <string>
#include <sstream>
#include <strstream>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"

#include "llvm/Support/Debug.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/StringObfuscation.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Config/llvm-config.h"

#if defined(LLVM_VERSION_MAJOR) && LLVM_VERSION_MAJOR > 10
#include "llvm/IR/AbstractCallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#define DEBUG_TYPE "obf"

#ifndef DEBUG
#define DEBUG 1
#endif

#ifdef DEBUG
#define DEBUG_OUT(s) do { \
    DEBUG_WITH_TYPE(DEBUG_TYPE, dbgs() << __PRETTY_FUNCTION__ << ": " << s << "\n" ); \
    if (DEBUG) errs() << __PRETTY_FUNCTION__ << ": " << s << "\n";  \
} while(0)
#else
#define DEBUG_OUT(s) do { \
    DEBUG_WITH_TYPE(DEBUG_TYPE, dbgs() << __PRETTY_FUNCTION__ << ": " << s << "\n" ); \
} while(0)
#endif

using namespace std;
using namespace llvm;

STATISTIC(GlobalsEncoded, "Counts number of global variables encoded");

namespace  {

  struct encVar {
  public:
    GlobalVariable *var;
    char key;
  };

  class StringObfuscationPass: public llvm::ModulePass {
  public:
    static char ID; // pass identification
    bool is_flag = false;

    StringObfuscationPass() :
      ModulePass(ID) {
    }

    StringObfuscationPass(bool flag) :
      ModulePass(ID) {
      is_flag = flag;
    }

    virtual bool runOnModule(Module &M) {

      if (!is_flag)
    return false;

      std::vector<GlobalVariable*> toDelConstGlob;
      //std::vector<GlobalVariable*> encGlob;
      std::vector<encVar*> encGlob;

      DEBUG_OUT(" -- Parse for Global Variables --" );

      // Loop over all global variables
      Module::global_iterator gi = M.global_begin(), ge = M.global_end();
      while (gi != ge) {

    GlobalVariable* gv = &(*gi);
    DEBUG_OUT("Global var " << gv->getName());
    std::string section = (gv->getSection()).str();
    Type * gv_type = gv->getValueType();

    if( true == gv_type->isArrayTy() ) {
      Type * gv_elt_type = gv_type->getArrayElementType() ;
      if( true == gv_elt_type->isIntegerTy() ) {
      }
      if( true == gv_elt_type->isIntegerTy(8) ) {
      }
    }
    // Let's encode the static ones
    if (gv->isConstant() && gv->hasInitializer()
           && isa<ConstantDataSequential>(gv->getInitializer())
           && section != "llvm.metadata"
           && section.find("__objc_methname") == std::string::npos
           && gv->getName().find("llvm.") == std::string::npos
           && gv->getName().find("_ZT") == std::string::npos
           && gv->getName().find("_ZS") == std::string::npos
           && gv_type->isArrayTy()
           ) {
      if( gv_type->getArrayElementType()->isIntegerTy(8) ) {
        ++GlobalsEncoded;
        std::string gv_name = (gv->getName()).str();
        gv->setName(gv_name + "_old" ) ;
        // Duplicate global variable
        GlobalVariable *dynGV = new GlobalVariable(M,
                               gv->getType()->getElementType(), !(gv->isConstant()),
                               gv->getLinkage(), (Constant*) 0, gv_name,
                               (GlobalVariable*) 0, gv->getThreadLocalMode(),
                               gv->getType()->getAddressSpace());
        // dynGV->copyAttributesFrom(gv);
        dynGV->setInitializer(gv->getInitializer());

        Constant *initializer = gv->getInitializer();
        ConstantDataSequential *cdata =
          dyn_cast<ConstantDataSequential>(initializer);

        bool performEncrypt = false;
        if (cdata) {

          // There is data. Ok for encryption
          performEncrypt = true;

          const char *orig = cdata->getRawDataValues().data();
          unsigned int len = cdata->getNumElements()
        * cdata->getElementByteSize();

          DEBUG_OUT(
            "  - value : "
            << orig << " / len : " << len << '\n');

          if (performEncrypt) {

        encVar *cur = new encVar();
        cur->var = dynGV;
        cur->key = llvm::cryptoutils->get_uint8_t();

        // casting away const is undef. behavior in C++
        // TODO a clean implementation would retrieve the data, generate a new constant
        // set the correct type, and copy the data over.
        //char *encr = new char[len];
        //Constant *initnew = ConstantDataArray::getString(M.getContext(), encr, true);
        char *encr = (char*) orig; // ugly but works for now

        // Simple xor encoding
        for (unsigned i = 0; i <= len; ++i) {
          encr[i] = orig[i] ^ cur->key;
        }

        // FIXME Second part of the unclean hack.
        dynGV->setInitializer(initializer);

        // Prepare to add decode function for this variable
        DEBUG_OUT( "  - " << cur->var->getName() << " is being pushed back to encGlob vector.\n" );
        encGlob.push_back(cur);
          }

        } else {

          DEBUG_OUT( "  - undhandled!\n" );
          // just copying default initializer for now
          dynGV->setInitializer(initializer);

        }

        // redirect references to new GV and remove old one
        gv->replaceAllUsesWith(dynGV);
        toDelConstGlob.push_back(gv);
      } else {
        DEBUG_OUT(
              " [NOT ELIGIBLE] : false == getArrayElementType()->isIntegerTy(8)"
              << '\n');
      }
    } else {
      DEBUG_OUT(
            " [NOT ELIGIBLE]"
            << '\n');
    }

    DEBUG_OUT( " -----------------------------------\n" );

    gi++;
      } //while( gi != ge ) ;


      // actuallte delete marked globals
      //for (unsigned i = 0, e = toDelConstGlob.size(); i != e; ++i)
      for (GlobalVariable* gvToDel : toDelConstGlob) {
    DEBUG_OUT(
          "  - "
          << gvToDel->getName() << " is being removed."
          << '\n');
    gvToDel->eraseFromParent();
      }

      DEBUG_OUT( " -----------------------------------\n" );

      // create code to initialize global variables at runtime
      if( false == encGlob.empty() ) {
    addDecodeFunction(&M, &encGlob);

    return true;
      } else {
    return false ;
      }
    }

  private:
    void addDecodeFunction(Module *mod, std::vector<encVar*> *gvars) {

      // Declare and add the function definition
      std::vector<Type*> FuncTy_args;
      FunctionType* FuncTy = FunctionType::get(
                           /* Result   = */ Type::getVoidTy(mod->getContext()),  // returning void
                           /* Params   = */ FuncTy_args,  // taking no args
                           /* isVarArg = */ false);

      uint64_t StringObfDecodeRandomName = cryptoutils->get_uint64_t();
      std::string random_str; 
      std::strstream random_stream;
      random_stream << StringObfDecodeRandomName;
      random_stream >> random_str;

      StringObfDecodeRandomName++;



      Constant* c = (Constant *)mod->getOrInsertFunction(".datadiv_decode" + random_str,
                             FuncTy).getCallee();
      DEBUG_OUT( " Function name is " << ".datadiv_decode" + random_str << "\n" );

      Function* fdecode = cast<Function>(c);
      fdecode->setCallingConv(CallingConv::C);

      // Declare some constants we'll use in the loop
      ConstantInt* const_0 = ConstantInt::get(mod->getContext(),
                          APInt(32, 0));
      ConstantInt* const_1 = ConstantInt::get(mod->getContext(),
                          APInt(32, 1));
      BasicBlock* label_entry = BasicBlock::Create(mod->getContext(), "entry",
                           fdecode);


      if (NULL != gvars) {

    for (encVar* encVar : *gvars) {

      DEBUG_OUT( " -----------------------------------\n" );

      GlobalVariable *gvar = encVar->var;
      char key = encVar->key;
      DEBUG_OUT( " Adding code for " << gvar->getName() << '\n' );

      Constant *init = gvar->getInitializer();
      ConstantDataSequential *cdata =
        dyn_cast<ConstantDataSequential>(init);
      unsigned len = cdata->getNumElements()
        * cdata->getElementByteSize();

      // Add per-GV local decode code:
      // for len(globVar): globVar[i] = globVar[i]^key

      ConstantInt* const_len = ConstantInt::get(mod->getContext(),
                            APInt(32, len));
      BasicBlock* label_for_body = BasicBlock::Create(
                              mod->getContext(), "for.body", fdecode, 0);
      BasicBlock* label_for_end = BasicBlock::Create(
                             mod->getContext(), "for.end", fdecode, 0);

      ICmpInst* cmp = new ICmpInst(*label_entry, ICmpInst::ICMP_EQ,
                       const_len, const_0, "cmp");

      BranchInst::Create(label_for_end, label_for_body, cmp,
                 label_entry);

      // Block for.body (label_for_body)
      Argument* fwdref_18 = new Argument(
                         IntegerType::get(mod->getContext(), 32));

      PHINode* int32_i = PHINode::Create(
                         IntegerType::get(mod->getContext(), 32), 2, "i.09",
                         label_for_body);
      int32_i->addIncoming(fwdref_18, label_for_body);
      int32_i->addIncoming(const_0, label_entry);

      CastInst* int64_idxprom = new ZExtInst(int32_i,
                         IntegerType::get(mod->getContext(), 64), "idxprom",
                         label_for_body);
      LoadInst* ptr_19 = new LoadInst(gvar->getType(), gvar, "", false,
                      label_for_body);
      ptr_19->setAlignment(Align(8));

      // Array/ptr load (GetElementPtr can be a bitch about this!)
      std::vector<Value*> ptr_32_indices;
      ptr_32_indices.push_back(const_0);
      ptr_32_indices.push_back(int64_idxprom);
      ArrayRef<Value*> ref_ptr_32_indices = ArrayRef<Value*>(
                                 ptr_32_indices);
      Instruction* ptr_arrayidx = GetElementPtrInst::Create(NULL,
                                gvar, ref_ptr_32_indices, "arrayidx", label_for_body);
      // Load
      LoadInst* int8_20 = new LoadInst(ptr_arrayidx->getType(), ptr_arrayidx, "", false,
                       label_for_body);
      DEBUG_OUT( " int8_20 : " << int8_20->getOpcodeName() << '\n' );
      DEBUG_OUT( " int8_20 : " << int8_20->getName() << '\n' );

      int8_20->setAlignment(Align(1));
      // Decode
      ConstantInt* const_key = ConstantInt::get(mod->getContext(),
                            APInt(8, key));
      //BinaryOperator* int8_dec = BinaryOperator::Create(Instruction::Add, int8_20, const_key, "sub", label_for_body);
      DEBUG_OUT( " Creating XOR BinaryOperator for " << gvar->getName() << '\n' );

      BinaryOperator* int8_dec = BinaryOperator::Create(
                                Instruction::Xor, int8_20, const_key, "xor",
                                label_for_body);
      // Store
      StoreInst* void_21 = new StoreInst(int8_dec, ptr_arrayidx,
                         false, label_for_body);
      void_21->setAlignment(Align(1));
      // Adjust loop counter
      DEBUG_OUT( " Creating INC BinaryOperator for " << gvar->getName() << '\n' );
      BinaryOperator* int32_inc = BinaryOperator::Create(
                                 Instruction::Add, int32_i, const_1, "inc",
                                 label_for_body);

      ICmpInst* int1_cmp = new ICmpInst(*label_for_body,
                        ICmpInst::ICMP_EQ, int32_inc, const_len, "cmp");
      BranchInst::Create(label_for_end, label_for_body, int1_cmp,
                 label_for_body);

      // Resolve Forward References
      fwdref_18->replaceAllUsesWith(int32_inc);
      delete fwdref_18;
      // adjust for next iteration
      label_entry = label_for_end;
    }

    DEBUG_OUT( " ----------------------------------- \n" );

    // Block for.end (label_for_end)
    ReturnInst::Create(mod->getContext(), label_entry);

    // Lets add our function to the constructors
    std::vector<Type*> StructTy_4_fields;
    StructTy_4_fields.push_back(IntegerType::get(mod->getContext(), 32));
    std::vector<Type*> FuncTy_6_args;
    FunctionType* FuncTy_6 = FunctionType::get(
                           /*Result   = */Type::getVoidTy(mod->getContext()),
                           /*Params   = */FuncTy_6_args,
                           /*isVarArg = */false );
    PointerType* PointerTy_5 = PointerType::get(FuncTy_6, 0);
    StructTy_4_fields.push_back(PointerTy_5);
    PointerType* PointerTy_6 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
    StructTy_4_fields.push_back(PointerTy_6);

    StructType *StructTy_4 = StructType::get(mod->getContext(),
                         StructTy_4_fields, /*isPacked=*/false);

    std::vector<Constant*> const_struct_11_fields;
    ConstantInt* const_int32_16max = ConstantInt::get(
                              mod->getContext(),
                              APInt(32, StringRef("65535"), 10));

    //PointerType* PointerTy_8 = PointerType::get(ConstantIn::, 0);
    //ConstantPointerNull*  const_int8ptr = ConstantPointerNull::get(PointerTy_8) ;
    //PointerType* PointerTy_6 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
    Constant*  const_int8ptr = Constant::getNullValue(PointerTy_6) ;

    const_struct_11_fields.push_back(const_int32_16max) ;
    const_struct_11_fields.push_back(fdecode) ;
    const_struct_11_fields.push_back(const_int8ptr) ;

    Constant* const_struct_11 = ConstantStruct::get(
                            StructTy_4,
                            const_struct_11_fields);

    std::vector<Constant*> const_array_10_elems;
    const_array_10_elems.push_back(const_struct_11);

    DEBUG_OUT( " - Looking for llvm.global_ctors... \n" );

    GlobalVariable* gvar_array_llvm_global_ctors = NULL;
    for (Module::global_iterator gi = mod->global_begin() ; gi != mod->global_end() ; ++gi ) {

        DEBUG_OUT( "Func:" << gi->getName() );

      if ( gi->getName() == "llvm.global_ctors" ) {
        gvar_array_llvm_global_ctors = &(*gi);
        DEBUG_OUT( "    ==> FOUND !\n" );
      }
    }

    Constant* initer = NULL ;
    if (NULL != gvar_array_llvm_global_ctors) {
      initer = dyn_cast<Constant>(gvar_array_llvm_global_ctors->getInitializer()) ;

      if (NULL != initer) {
        for (Use &f : initer->operands()) {
          DEBUG_OUT(" - f->getName() : " << f->getName()
            << " - f->getType() : " << f->getType()
            << " - f->getType()->isStructTy() : " << (f->getType()->isStructTy() ? "true" : "false" ));
          const_array_10_elems.push_back(dyn_cast<Constant>(&*f));
        }
      }
    }

    ArrayRef<Constant*> array_ref_const_array_10_elems = (ArrayRef<Constant*>)const_array_10_elems ;
    ArrayType* ArrayTy_3 = ArrayType::get(StructTy_4, array_ref_const_array_10_elems.size() ) ;
    if( true == ArrayTy_3->isArrayTy() ) {
    }
    for (unsigned i = 0, e = array_ref_const_array_10_elems.size(); i != e; ++i) {
    }
    Constant* const_array_10 = ConstantArray::get(
                              ArrayTy_3,
                              const_array_10_elems);

    // Global Variable Definitions
    //if (NULL == gvar_array_llvm_global_ctors) {

    DEBUG_OUT( " - Setting initializer... " << '\n' );

    if (NULL != gvar_array_llvm_global_ctors)
      gvar_array_llvm_global_ctors->removeFromParent() ;

    GlobalVariable* new_gvar_array_llvm_global_ctors =
      new GlobalVariable(*mod,
                 ArrayTy_3,
                 false,
                 GlobalValue::AppendingLinkage,
                 0,
                 "llvm.global_ctors");

    new_gvar_array_llvm_global_ctors->setInitializer(const_array_10);
      } else {
    DEBUG_OUT("gvars is NULL" << '\n');
      }

    }

  };

}

char StringObfuscationPass::ID = 0;
static RegisterPass<StringObfuscationPass> X("GVDiv",
                         "Global variable (i.e., const char*) diversification Pass");

Pass * llvm::createStringObfuscationPass(bool flag) {
  return new StringObfuscationPass(flag);
}

