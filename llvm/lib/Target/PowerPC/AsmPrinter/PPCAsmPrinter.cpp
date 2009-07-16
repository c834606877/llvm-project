//===-- PPCAsmPrinter.cpp - Print machine instrs to PowerPC assembly --------=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains a printer that converts from our internal representation
// of machine-dependent LLVM code to PowerPC assembly language. This printer is
// the output mechanism used by `llc'.
//
// Documentation at http://developer.apple.com/documentation/DeveloperTools/
// Reference/Assembler/ASMIntroduction/chapter_1_section_1.html
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "asmprinter"
#include "PPC.h"
#include "PPCPredicates.h"
#include "PPCTargetMachine.h"
#include "PPCSubtarget.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/MDNode.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/CodeGen/AsmPrinter.h"
#include "llvm/CodeGen/DwarfWriter.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/Support/Mangler.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Target/TargetAsmInfo.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
using namespace llvm;

STATISTIC(EmittedInsts, "Number of machine instrs printed");

namespace {
  class VISIBILITY_HIDDEN PPCAsmPrinter : public AsmPrinter {
  protected:
    struct FnStubInfo {
      std::string Stub, LazyPtr, AnonSymbol;
      
      FnStubInfo() {}
      
      void Init(const GlobalValue *GV, Mangler *Mang) {
        // Already initialized.
        if (!Stub.empty()) return;
        Stub = Mang->getMangledName(GV, "$stub", true);
        LazyPtr = Mang->getMangledName(GV, "$lazy_ptr", true);
        AnonSymbol = Mang->getMangledName(GV, "$stub$tmp", true);
      }

      void Init(const std::string &GV, Mangler *Mang) {
        // Already initialized.
        if (!Stub.empty()) return;
        Stub = Mang->makeNameProper(GV+"$stub", true);
        LazyPtr = Mang->makeNameProper(GV+"$lazy_ptr", true);
        AnonSymbol = Mang->makeNameProper(GV+"$stub$tmp", true);
      }
    };
    
    StringMap<FnStubInfo> FnStubs;
    StringMap<std::string> GVStubs, HiddenGVStubs;
    const PPCSubtarget &Subtarget;
  public:
    explicit PPCAsmPrinter(formatted_raw_ostream &O, TargetMachine &TM,
                           const TargetAsmInfo *T, bool V)
      : AsmPrinter(O, TM, T, V),
        Subtarget(TM.getSubtarget<PPCSubtarget>()) {}

    virtual const char *getPassName() const {
      return "PowerPC Assembly Printer";
    }

    PPCTargetMachine &getTM() {
      return static_cast<PPCTargetMachine&>(TM);
    }

    unsigned enumRegToMachineReg(unsigned enumReg) {
      switch (enumReg) {
      default: llvm_unreachable("Unhandled register!");
      case PPC::CR0:  return  0;
      case PPC::CR1:  return  1;
      case PPC::CR2:  return  2;
      case PPC::CR3:  return  3;
      case PPC::CR4:  return  4;
      case PPC::CR5:  return  5;
      case PPC::CR6:  return  6;
      case PPC::CR7:  return  7;
      }
      llvm_unreachable(0);
    }

    /// printInstruction - This method is automatically generated by tablegen
    /// from the instruction set description.  This method returns true if the
    /// machine instruction was sufficiently described to print it, otherwise it
    /// returns false.
    bool printInstruction(const MachineInstr *MI);

    void printMachineInstruction(const MachineInstr *MI);
    void printOp(const MachineOperand &MO);

    /// stripRegisterPrefix - This method strips the character prefix from a
    /// register name so that only the number is left.  Used by for linux asm.
    const char *stripRegisterPrefix(const char *RegName) {
      switch (RegName[0]) {
      case 'r':
      case 'f':
      case 'v': return RegName + 1;
      case 'c': if (RegName[1] == 'r') return RegName + 2;
      }

      return RegName;
    }

    /// printRegister - Print register according to target requirements.
    ///
    void printRegister(const MachineOperand &MO, bool R0AsZero) {
      unsigned RegNo = MO.getReg();
      assert(TargetRegisterInfo::isPhysicalRegister(RegNo) && "Not physreg??");

      // If we should use 0 for R0.
      if (R0AsZero && RegNo == PPC::R0) {
        O << "0";
        return;
      }

      const char *RegName = TM.getRegisterInfo()->get(RegNo).AsmName;
      // Linux assembler (Others?) does not take register mnemonics.
      // FIXME - What about special registers used in mfspr/mtspr?
      if (!Subtarget.isDarwin()) RegName = stripRegisterPrefix(RegName);
      O << RegName;
    }

    void printOperand(const MachineInstr *MI, unsigned OpNo) {
      const MachineOperand &MO = MI->getOperand(OpNo);
      if (MO.isReg()) {
        printRegister(MO, false);
      } else if (MO.isImm()) {
        O << MO.getImm();
      } else {
        printOp(MO);
      }
    }

    bool PrintAsmOperand(const MachineInstr *MI, unsigned OpNo,
                         unsigned AsmVariant, const char *ExtraCode);
    bool PrintAsmMemoryOperand(const MachineInstr *MI, unsigned OpNo,
                               unsigned AsmVariant, const char *ExtraCode);


    void printS5ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      char value = MI->getOperand(OpNo).getImm();
      value = (value << (32-5)) >> (32-5);
      O << (int)value;
    }
    void printU5ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      unsigned char value = MI->getOperand(OpNo).getImm();
      assert(value <= 31 && "Invalid u5imm argument!");
      O << (unsigned int)value;
    }
    void printU6ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      unsigned char value = MI->getOperand(OpNo).getImm();
      assert(value <= 63 && "Invalid u6imm argument!");
      O << (unsigned int)value;
    }
    void printS16ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      O << (short)MI->getOperand(OpNo).getImm();
    }
    void printU16ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      O << (unsigned short)MI->getOperand(OpNo).getImm();
    }
    void printS16X4ImmOperand(const MachineInstr *MI, unsigned OpNo) {
      if (MI->getOperand(OpNo).isImm()) {
        O << (short)(MI->getOperand(OpNo).getImm()*4);
      } else {
        O << "lo16(";
        printOp(MI->getOperand(OpNo));
        if (TM.getRelocationModel() == Reloc::PIC_)
          O << "-\"L" << getFunctionNumber() << "$pb\")";
        else
          O << ')';
      }
    }
    void printBranchOperand(const MachineInstr *MI, unsigned OpNo) {
      // Branches can take an immediate operand.  This is used by the branch
      // selection pass to print $+8, an eight byte displacement from the PC.
      if (MI->getOperand(OpNo).isImm()) {
        O << "$+" << MI->getOperand(OpNo).getImm()*4;
      } else {
        printOp(MI->getOperand(OpNo));
      }
    }
    void printCallOperand(const MachineInstr *MI, unsigned OpNo) {
      const MachineOperand &MO = MI->getOperand(OpNo);
      if (TM.getRelocationModel() != Reloc::Static) {
        if (MO.getType() == MachineOperand::MO_GlobalAddress) {
          GlobalValue *GV = MO.getGlobal();
          if (GV->isDeclaration() || GV->isWeakForLinker()) {
            // Dynamically-resolved functions need a stub for the function.
            FnStubInfo &FnInfo = FnStubs[Mang->getMangledName(GV)];
            FnInfo.Init(GV, Mang);
            O << FnInfo.Stub;
            return;
          }
        }
        if (MO.getType() == MachineOperand::MO_ExternalSymbol) {
          FnStubInfo &FnInfo =FnStubs[Mang->makeNameProper(MO.getSymbolName())];
          FnInfo.Init(MO.getSymbolName(), Mang);
          O << FnInfo.Stub;
          return;
        }
      }

      printOp(MI->getOperand(OpNo));
    }
    void printAbsAddrOperand(const MachineInstr *MI, unsigned OpNo) {
     O << (int)MI->getOperand(OpNo).getImm()*4;
    }
    void printPICLabel(const MachineInstr *MI, unsigned OpNo) {
      O << "\"L" << getFunctionNumber() << "$pb\"\n";
      O << "\"L" << getFunctionNumber() << "$pb\":";
    }
    void printSymbolHi(const MachineInstr *MI, unsigned OpNo) {
      if (MI->getOperand(OpNo).isImm()) {
        printS16ImmOperand(MI, OpNo);
      } else {
        if (Subtarget.isDarwin()) O << "ha16(";
        printOp(MI->getOperand(OpNo));
        if (TM.getRelocationModel() == Reloc::PIC_)
          O << "-\"L" << getFunctionNumber() << "$pb\"";
        if (Subtarget.isDarwin())
          O << ')';
        else
          O << "@ha";
      }
    }
    void printSymbolLo(const MachineInstr *MI, unsigned OpNo) {
      if (MI->getOperand(OpNo).isImm()) {
        printS16ImmOperand(MI, OpNo);
      } else {
        if (Subtarget.isDarwin()) O << "lo16(";
        printOp(MI->getOperand(OpNo));
        if (TM.getRelocationModel() == Reloc::PIC_)
          O << "-\"L" << getFunctionNumber() << "$pb\"";
        if (Subtarget.isDarwin())
          O << ')';
        else
          O << "@l";
      }
    }
    void printcrbitm(const MachineInstr *MI, unsigned OpNo) {
      unsigned CCReg = MI->getOperand(OpNo).getReg();
      unsigned RegNo = enumRegToMachineReg(CCReg);
      O << (0x80 >> RegNo);
    }
    // The new addressing mode printers.
    void printMemRegImm(const MachineInstr *MI, unsigned OpNo) {
      printSymbolLo(MI, OpNo);
      O << '(';
      if (MI->getOperand(OpNo+1).isReg() &&
          MI->getOperand(OpNo+1).getReg() == PPC::R0)
        O << "0";
      else
        printOperand(MI, OpNo+1);
      O << ')';
    }
    void printMemRegImmShifted(const MachineInstr *MI, unsigned OpNo) {
      if (MI->getOperand(OpNo).isImm())
        printS16X4ImmOperand(MI, OpNo);
      else
        printSymbolLo(MI, OpNo);
      O << '(';
      if (MI->getOperand(OpNo+1).isReg() &&
          MI->getOperand(OpNo+1).getReg() == PPC::R0)
        O << "0";
      else
        printOperand(MI, OpNo+1);
      O << ')';
    }

    void printMemRegReg(const MachineInstr *MI, unsigned OpNo) {
      // When used as the base register, r0 reads constant zero rather than
      // the value contained in the register.  For this reason, the darwin
      // assembler requires that we print r0 as 0 (no r) when used as the base.
      const MachineOperand &MO = MI->getOperand(OpNo);
      printRegister(MO, true);
      O << ", ";
      printOperand(MI, OpNo+1);
    }

    void printPredicateOperand(const MachineInstr *MI, unsigned OpNo,
                               const char *Modifier);

    virtual bool runOnMachineFunction(MachineFunction &F) = 0;
    virtual bool doFinalization(Module &M) = 0;

    virtual void EmitExternalGlobal(const GlobalVariable *GV);
  };

  /// PPCLinuxAsmPrinter - PowerPC assembly printer, customized for Linux
  class VISIBILITY_HIDDEN PPCLinuxAsmPrinter : public PPCAsmPrinter {
  public:
    explicit PPCLinuxAsmPrinter(formatted_raw_ostream &O, TargetMachine &TM,
                                const TargetAsmInfo *T, bool V)
      : PPCAsmPrinter(O, TM, T, V){}

    virtual const char *getPassName() const {
      return "Linux PPC Assembly Printer";
    }

    bool runOnMachineFunction(MachineFunction &F);
    bool doFinalization(Module &M);

    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<MachineModuleInfo>();
      AU.addRequired<DwarfWriter>();
      PPCAsmPrinter::getAnalysisUsage(AU);
    }

    void printModuleLevelGV(const GlobalVariable* GVar);
  };

  /// PPCDarwinAsmPrinter - PowerPC assembly printer, customized for Darwin/Mac
  /// OS X
  class VISIBILITY_HIDDEN PPCDarwinAsmPrinter : public PPCAsmPrinter {
    formatted_raw_ostream &OS;
  public:
    explicit PPCDarwinAsmPrinter(formatted_raw_ostream &O, TargetMachine &TM,
                                 const TargetAsmInfo *T, bool V)
      : PPCAsmPrinter(O, TM, T, V), OS(O) {}

    virtual const char *getPassName() const {
      return "Darwin PPC Assembly Printer";
    }

    bool runOnMachineFunction(MachineFunction &F);
    bool doInitialization(Module &M);
    bool doFinalization(Module &M);

    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<MachineModuleInfo>();
      AU.addRequired<DwarfWriter>();
      PPCAsmPrinter::getAnalysisUsage(AU);
    }

    void printModuleLevelGV(const GlobalVariable* GVar);
  };
} // end of anonymous namespace

// Include the auto-generated portion of the assembly writer
#include "PPCGenAsmWriter.inc"

void PPCAsmPrinter::printOp(const MachineOperand &MO) {
  switch (MO.getType()) {
  case MachineOperand::MO_Immediate:
    llvm_unreachable("printOp() does not handle immediate values");

  case MachineOperand::MO_MachineBasicBlock:
    printBasicBlockLabel(MO.getMBB());
    return;
  case MachineOperand::MO_JumpTableIndex:
    O << TAI->getPrivateGlobalPrefix() << "JTI" << getFunctionNumber()
      << '_' << MO.getIndex();
    // FIXME: PIC relocation model
    return;
  case MachineOperand::MO_ConstantPoolIndex:
    O << TAI->getPrivateGlobalPrefix() << "CPI" << getFunctionNumber()
      << '_' << MO.getIndex();
    return;
  case MachineOperand::MO_ExternalSymbol: {
    // Computing the address of an external symbol, not calling it.
    std::string Name(TAI->getGlobalPrefix());
    Name += MO.getSymbolName();
    
    if (TM.getRelocationModel() != Reloc::Static) {
      GVStubs[Name] = Name+"$non_lazy_ptr";
      Name += "$non_lazy_ptr";
    }
    O << Name;
    return;
  }
  case MachineOperand::MO_GlobalAddress: {
    // Computing the address of a global symbol, not calling it.
    GlobalValue *GV = MO.getGlobal();
    std::string Name;

    // External or weakly linked global variables need non-lazily-resolved stubs
    if (TM.getRelocationModel() != Reloc::Static &&
        (GV->isDeclaration() || GV->isWeakForLinker())) {
      if (!GV->hasHiddenVisibility()) {
        Name = Mang->getMangledName(GV, "$non_lazy_ptr", true);
        GVStubs[Mang->getMangledName(GV)] = Name;
      } else if (GV->isDeclaration() || GV->hasCommonLinkage() ||
                 GV->hasAvailableExternallyLinkage()) {
        Name = Mang->getMangledName(GV, "$non_lazy_ptr", true);
        HiddenGVStubs[Mang->getMangledName(GV)] = Name;
      } else {
        Name = Mang->getMangledName(GV);
      }
    } else {
      Name = Mang->getMangledName(GV);
    }
    O << Name;

    printOffset(MO.getOffset());
    return;
  }

  default:
    O << "<unknown operand type: " << MO.getType() << ">";
    return;
  }
}

/// EmitExternalGlobal - In this case we need to use the indirect symbol.
///
void PPCAsmPrinter::EmitExternalGlobal(const GlobalVariable *GV) {
  std::string Name;
  
  if (TM.getRelocationModel() != Reloc::Static) {
    Name = Mang->getMangledName(GV, "$non_lazy_ptr", true);
  } else {
    Name = Mang->getMangledName(GV);
  }
  O << Name;
}

/// PrintAsmOperand - Print out an operand for an inline asm expression.
///
bool PPCAsmPrinter::PrintAsmOperand(const MachineInstr *MI, unsigned OpNo,
                                    unsigned AsmVariant,
                                    const char *ExtraCode) {
  // Does this asm operand have a single letter operand modifier?
  if (ExtraCode && ExtraCode[0]) {
    if (ExtraCode[1] != 0) return true; // Unknown modifier.

    switch (ExtraCode[0]) {
    default: return true;  // Unknown modifier.
    case 'c': // Don't print "$" before a global var name or constant.
      // PPC never has a prefix.
      printOperand(MI, OpNo);
      return false;
    case 'L': // Write second word of DImode reference.
      // Verify that this operand has two consecutive registers.
      if (!MI->getOperand(OpNo).isReg() ||
          OpNo+1 == MI->getNumOperands() ||
          !MI->getOperand(OpNo+1).isReg())
        return true;
      ++OpNo;   // Return the high-part.
      break;
    case 'I':
      // Write 'i' if an integer constant, otherwise nothing.  Used to print
      // addi vs add, etc.
      if (MI->getOperand(OpNo).isImm())
        O << "i";
      return false;
    }
  }

  printOperand(MI, OpNo);
  return false;
}

bool PPCAsmPrinter::PrintAsmMemoryOperand(const MachineInstr *MI, unsigned OpNo,
                                          unsigned AsmVariant,
                                          const char *ExtraCode) {
  if (ExtraCode && ExtraCode[0])
    return true; // Unknown modifier.
  if (MI->getOperand(OpNo).isReg())
    printMemRegReg(MI, OpNo);
  else
    printMemRegImm(MI, OpNo);
  return false;
}

void PPCAsmPrinter::printPredicateOperand(const MachineInstr *MI, unsigned OpNo,
                                          const char *Modifier) {
  assert(Modifier && "Must specify 'cc' or 'reg' as predicate op modifier!");
  unsigned Code = MI->getOperand(OpNo).getImm();
  if (!strcmp(Modifier, "cc")) {
    switch ((PPC::Predicate)Code) {
    case PPC::PRED_ALWAYS: return; // Don't print anything for always.
    case PPC::PRED_LT: O << "lt"; return;
    case PPC::PRED_LE: O << "le"; return;
    case PPC::PRED_EQ: O << "eq"; return;
    case PPC::PRED_GE: O << "ge"; return;
    case PPC::PRED_GT: O << "gt"; return;
    case PPC::PRED_NE: O << "ne"; return;
    case PPC::PRED_UN: O << "un"; return;
    case PPC::PRED_NU: O << "nu"; return;
    }

  } else {
    assert(!strcmp(Modifier, "reg") &&
           "Need to specify 'cc' or 'reg' as predicate op modifier!");
    // Don't print the register for 'always'.
    if (Code == PPC::PRED_ALWAYS) return;
    printOperand(MI, OpNo+1);
  }
}


/// printMachineInstruction -- Print out a single PowerPC MI in Darwin syntax to
/// the current output stream.
///
void PPCAsmPrinter::printMachineInstruction(const MachineInstr *MI) {
  ++EmittedInsts;

  // Check for slwi/srwi mnemonics.
  if (MI->getOpcode() == PPC::RLWINM) {
    bool FoundMnemonic = false;
    unsigned char SH = MI->getOperand(2).getImm();
    unsigned char MB = MI->getOperand(3).getImm();
    unsigned char ME = MI->getOperand(4).getImm();
    if (SH <= 31 && MB == 0 && ME == (31-SH)) {
      O << "\tslwi "; FoundMnemonic = true;
    }
    if (SH <= 31 && MB == (32-SH) && ME == 31) {
      O << "\tsrwi "; FoundMnemonic = true;
      SH = 32-SH;
    }
    if (FoundMnemonic) {
      printOperand(MI, 0);
      O << ", ";
      printOperand(MI, 1);
      O << ", " << (unsigned int)SH << '\n';
      return;
    }
  } else if (MI->getOpcode() == PPC::OR || MI->getOpcode() == PPC::OR8) {
    if (MI->getOperand(1).getReg() == MI->getOperand(2).getReg()) {
      O << "\tmr ";
      printOperand(MI, 0);
      O << ", ";
      printOperand(MI, 1);
      O << '\n';
      return;
    }
  } else if (MI->getOpcode() == PPC::RLDICR) {
    unsigned char SH = MI->getOperand(2).getImm();
    unsigned char ME = MI->getOperand(3).getImm();
    // rldicr RA, RS, SH, 63-SH == sldi RA, RS, SH
    if (63-SH == ME) {
      O << "\tsldi ";
      printOperand(MI, 0);
      O << ", ";
      printOperand(MI, 1);
      O << ", " << (unsigned int)SH << '\n';
      return;
    }
  }

  if (printInstruction(MI))
    return; // Printer was automatically generated

  llvm_unreachable("Unhandled instruction in asm writer!");
}

/// runOnMachineFunction - This uses the printMachineInstruction()
/// method to print assembly for each instruction.
///
bool PPCLinuxAsmPrinter::runOnMachineFunction(MachineFunction &MF) {
  this->MF = &MF;

  SetupMachineFunction(MF);
  O << "\n\n";

  // Print out constants referenced by the function
  EmitConstantPool(MF.getConstantPool());

  // Print out labels for the function.
  const Function *F = MF.getFunction();
  SwitchToSection(TAI->SectionForGlobal(F));

  switch (F->getLinkage()) {
  default: llvm_unreachable("Unknown linkage type!");
  case Function::PrivateLinkage:
  case Function::InternalLinkage:  // Symbols default to internal.
    break;
  case Function::ExternalLinkage:
    O << "\t.global\t" << CurrentFnName << '\n'
      << "\t.type\t" << CurrentFnName << ", @function\n";
    break;
  case Function::WeakAnyLinkage:
  case Function::WeakODRLinkage:
  case Function::LinkOnceAnyLinkage:
  case Function::LinkOnceODRLinkage:
    O << "\t.global\t" << CurrentFnName << '\n';
    O << "\t.weak\t" << CurrentFnName << '\n';
    break;
  }

  printVisibility(CurrentFnName, F->getVisibility());

  EmitAlignment(MF.getAlignment(), F);
  O << CurrentFnName << ":\n";

  // Emit pre-function debug information.
  DW->BeginFunction(&MF);

  // Print out code for the function.
  for (MachineFunction::const_iterator I = MF.begin(), E = MF.end();
       I != E; ++I) {
    // Print a label for the basic block.
    if (I != MF.begin()) {
      printBasicBlockLabel(I, true, true);
      O << '\n';
    }
    for (MachineBasicBlock::const_iterator II = I->begin(), E = I->end();
         II != E; ++II) {
      // Print the assembly for the instruction.
      printMachineInstruction(II);
    }
  }

  O << "\t.size\t" << CurrentFnName << ",.-" << CurrentFnName << '\n';

  // Print out jump tables referenced by the function.
  EmitJumpTableInfo(MF.getJumpTableInfo(), MF);

  SwitchToSection(TAI->SectionForGlobal(F));

  // Emit post-function debug information.
  DW->EndFunction(&MF);

  O.flush();

  // We didn't modify anything.
  return false;
}

/// PrintUnmangledNameSafely - Print out the printable characters in the name.
/// Don't print things like \\n or \\0.
static void PrintUnmangledNameSafely(const Value *V, formatted_raw_ostream &OS) {
  for (const char *Name = V->getNameStart(), *E = Name+V->getNameLen();
       Name != E; ++Name)
    if (isprint(*Name))
      OS << *Name;
}

void PPCLinuxAsmPrinter::printModuleLevelGV(const GlobalVariable* GVar) {
  const TargetData *TD = TM.getTargetData();

  if (!GVar->hasInitializer())
    return;   // External global require no code

  // Check to see if this is a special global used by LLVM, if so, emit it.
  if (EmitSpecialLLVMGlobal(GVar))
    return;

  std::string name = Mang->getMangledName(GVar);

  printVisibility(name, GVar->getVisibility());

  Constant *C = GVar->getInitializer();
  if (isa<MDNode>(C) || isa<MDString>(C))
    return;
  const Type *Type = C->getType();
  unsigned Size = TD->getTypeAllocSize(Type);
  unsigned Align = TD->getPreferredAlignmentLog(GVar);

  SwitchToSection(TAI->SectionForGlobal(GVar));

  if (C->isNullValue() && /* FIXME: Verify correct */
      !GVar->hasSection() &&
      (GVar->hasLocalLinkage() || GVar->hasExternalLinkage() ||
       GVar->isWeakForLinker())) {
      if (Size == 0) Size = 1;   // .comm Foo, 0 is undefined, avoid it.

      if (GVar->hasExternalLinkage()) {
        O << "\t.global " << name << '\n';
        O << "\t.type " << name << ", @object\n";
        O << name << ":\n";
        O << "\t.zero " << Size << '\n';
      } else if (GVar->hasLocalLinkage()) {
        O << TAI->getLCOMMDirective() << name << ',' << Size;
      } else {
        O << ".comm " << name << ',' << Size;
      }
      if (VerboseAsm) {
        O << "\t\t" << TAI->getCommentString() << " '";
        PrintUnmangledNameSafely(GVar, O);
        O << "'";
      }
      O << '\n';
      return;
  }

  switch (GVar->getLinkage()) {
   case GlobalValue::LinkOnceAnyLinkage:
   case GlobalValue::LinkOnceODRLinkage:
   case GlobalValue::WeakAnyLinkage:
   case GlobalValue::WeakODRLinkage:
   case GlobalValue::CommonLinkage:
    O << "\t.global " << name << '\n'
      << "\t.type " << name << ", @object\n"
      << "\t.weak " << name << '\n';
    break;
   case GlobalValue::AppendingLinkage:
    // FIXME: appending linkage variables should go into a section of
    // their name or something.  For now, just emit them as external.
   case GlobalValue::ExternalLinkage:
    // If external or appending, declare as a global symbol
    O << "\t.global " << name << '\n'
      << "\t.type " << name << ", @object\n";
    // FALL THROUGH
   case GlobalValue::InternalLinkage:
   case GlobalValue::PrivateLinkage:
    break;
   default:
    llvm_unreachable("Unknown linkage type!");
  }

  EmitAlignment(Align, GVar);
  O << name << ":";
  if (VerboseAsm) {
    O << "\t\t\t\t" << TAI->getCommentString() << " '";
    PrintUnmangledNameSafely(GVar, O);
    O << "'";
  }
  O << '\n';

  EmitGlobalConstant(C);
  O << '\n';
}

bool PPCLinuxAsmPrinter::doFinalization(Module &M) {
  // Print out module-level global variables here.
  for (Module::const_global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I)
    printModuleLevelGV(I);

  return AsmPrinter::doFinalization(M);
}

/// runOnMachineFunction - This uses the printMachineInstruction()
/// method to print assembly for each instruction.
///
bool PPCDarwinAsmPrinter::runOnMachineFunction(MachineFunction &MF) {
  this->MF = &MF;

  SetupMachineFunction(MF);
  O << "\n\n";

  // Print out constants referenced by the function
  EmitConstantPool(MF.getConstantPool());

  // Print out labels for the function.
  const Function *F = MF.getFunction();
  SwitchToSection(TAI->SectionForGlobal(F));

  switch (F->getLinkage()) {
  default: llvm_unreachable("Unknown linkage type!");
  case Function::PrivateLinkage:
  case Function::InternalLinkage:  // Symbols default to internal.
    break;
  case Function::ExternalLinkage:
    O << "\t.globl\t" << CurrentFnName << '\n';
    break;
  case Function::WeakAnyLinkage:
  case Function::WeakODRLinkage:
  case Function::LinkOnceAnyLinkage:
  case Function::LinkOnceODRLinkage:
    O << "\t.globl\t" << CurrentFnName << '\n';
    O << "\t.weak_definition\t" << CurrentFnName << '\n';
    break;
  }

  printVisibility(CurrentFnName, F->getVisibility());

  EmitAlignment(MF.getAlignment(), F);
  O << CurrentFnName << ":\n";

  // Emit pre-function debug information.
  DW->BeginFunction(&MF);

  // If the function is empty, then we need to emit *something*. Otherwise, the
  // function's label might be associated with something that it wasn't meant to
  // be associated with. We emit a noop in this situation.
  MachineFunction::iterator I = MF.begin();

  if (++I == MF.end() && MF.front().empty())
    O << "\tnop\n";

  // Print out code for the function.
  for (MachineFunction::const_iterator I = MF.begin(), E = MF.end();
       I != E; ++I) {
    // Print a label for the basic block.
    if (I != MF.begin()) {
      printBasicBlockLabel(I, true, true, VerboseAsm);
      O << '\n';
    }
    for (MachineBasicBlock::const_iterator II = I->begin(), IE = I->end();
         II != IE; ++II) {
      // Print the assembly for the instruction.
      printMachineInstruction(II);
    }
  }

  // Print out jump tables referenced by the function.
  EmitJumpTableInfo(MF.getJumpTableInfo(), MF);

  // Emit post-function debug information.
  DW->EndFunction(&MF);

  // We didn't modify anything.
  return false;
}


bool PPCDarwinAsmPrinter::doInitialization(Module &M) {
  static const char *const CPUDirectives[] = {
    "",
    "ppc",
    "ppc601",
    "ppc602",
    "ppc603",
    "ppc7400",
    "ppc750",
    "ppc970",
    "ppc64"
  };

  unsigned Directive = Subtarget.getDarwinDirective();
  if (Subtarget.isGigaProcessor() && Directive < PPC::DIR_970)
    Directive = PPC::DIR_970;
  if (Subtarget.hasAltivec() && Directive < PPC::DIR_7400)
    Directive = PPC::DIR_7400;
  if (Subtarget.isPPC64() && Directive < PPC::DIR_970)
    Directive = PPC::DIR_64;
  assert(Directive <= PPC::DIR_64 && "Directive out of range.");
  O << "\t.machine " << CPUDirectives[Directive] << '\n';

  bool Result = AsmPrinter::doInitialization(M);
  assert(MMI);

  // Prime text sections so they are adjacent.  This reduces the likelihood a
  // large data or debug section causes a branch to exceed 16M limit.
  SwitchToTextSection("\t.section __TEXT,__textcoal_nt,coalesced,"
                      "pure_instructions");
  if (TM.getRelocationModel() == Reloc::PIC_) {
    SwitchToTextSection("\t.section __TEXT,__picsymbolstub1,symbol_stubs,"
                          "pure_instructions,32");
  } else if (TM.getRelocationModel() == Reloc::DynamicNoPIC) {
    SwitchToTextSection("\t.section __TEXT,__symbol_stub1,symbol_stubs,"
                        "pure_instructions,16");
  }
  SwitchToSection(TAI->getTextSection());

  return Result;
}

void PPCDarwinAsmPrinter::printModuleLevelGV(const GlobalVariable* GVar) {
  const TargetData *TD = TM.getTargetData();

  if (!GVar->hasInitializer())
    return;   // External global require no code

  // Check to see if this is a special global used by LLVM, if so, emit it.
  if (EmitSpecialLLVMGlobal(GVar)) {
    if (TM.getRelocationModel() == Reloc::Static) {
      if (GVar->getName() == "llvm.global_ctors")
        O << ".reference .constructors_used\n";
      else if (GVar->getName() == "llvm.global_dtors")
        O << ".reference .destructors_used\n";
    }
    return;
  }

  std::string name = Mang->getMangledName(GVar);
  printVisibility(name, GVar->getVisibility());

  Constant *C = GVar->getInitializer();
  const Type *Type = C->getType();
  unsigned Size = TD->getTypeAllocSize(Type);
  unsigned Align = TD->getPreferredAlignmentLog(GVar);

  SwitchToSection(TAI->SectionForGlobal(GVar));

  if (C->isNullValue() && /* FIXME: Verify correct */
      !GVar->hasSection() &&
      (GVar->hasLocalLinkage() || GVar->hasExternalLinkage() ||
       GVar->isWeakForLinker()) &&
      TAI->SectionKindForGlobal(GVar) != SectionKind::RODataMergeStr) {
    if (Size == 0) Size = 1;   // .comm Foo, 0 is undefined, avoid it.

    if (GVar->hasExternalLinkage()) {
      O << "\t.globl " << name << '\n';
      O << "\t.zerofill __DATA, __common, " << name << ", "
        << Size << ", " << Align;
    } else if (GVar->hasLocalLinkage()) {
      O << TAI->getLCOMMDirective() << name << ',' << Size << ',' << Align;
    } else if (!GVar->hasCommonLinkage()) {
      O << "\t.globl " << name << '\n'
        << TAI->getWeakDefDirective() << name << '\n';
      EmitAlignment(Align, GVar);
      O << name << ":";
      if (VerboseAsm) {
        O << "\t\t\t\t" << TAI->getCommentString() << " ";
        PrintUnmangledNameSafely(GVar, O);
      }
      O << '\n';
      EmitGlobalConstant(C);
      return;
    } else {
      O << ".comm " << name << ',' << Size;
      // Darwin 9 and above support aligned common data.
      if (Subtarget.isDarwin9())
        O << ',' << Align;
    }
    if (VerboseAsm) {
      O << "\t\t" << TAI->getCommentString() << " '";
      PrintUnmangledNameSafely(GVar, O);
      O << "'";
    }
    O << '\n';
    return;
  }

  switch (GVar->getLinkage()) {
   case GlobalValue::LinkOnceAnyLinkage:
   case GlobalValue::LinkOnceODRLinkage:
   case GlobalValue::WeakAnyLinkage:
   case GlobalValue::WeakODRLinkage:
   case GlobalValue::CommonLinkage:
    O << "\t.globl " << name << '\n'
      << "\t.weak_definition " << name << '\n';
    break;
   case GlobalValue::AppendingLinkage:
    // FIXME: appending linkage variables should go into a section of
    // their name or something.  For now, just emit them as external.
   case GlobalValue::ExternalLinkage:
    // If external or appending, declare as a global symbol
    O << "\t.globl " << name << '\n';
    // FALL THROUGH
   case GlobalValue::InternalLinkage:
   case GlobalValue::PrivateLinkage:
    break;
   default:
    llvm_unreachable("Unknown linkage type!");
  }

  EmitAlignment(Align, GVar);
  O << name << ":";
  if (VerboseAsm) {
    O << "\t\t\t\t" << TAI->getCommentString() << " '";
    PrintUnmangledNameSafely(GVar, O);
    O << "'";
  }
  O << '\n';

  EmitGlobalConstant(C);
  O << '\n';
}

bool PPCDarwinAsmPrinter::doFinalization(Module &M) {
  const TargetData *TD = TM.getTargetData();

  // Print out module-level global variables here.
  for (Module::const_global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I)
    printModuleLevelGV(I);

  bool isPPC64 = TD->getPointerSizeInBits() == 64;

  // Output stubs for dynamically-linked functions
  if (TM.getRelocationModel() == Reloc::PIC_ && !FnStubs.empty()) {
    for (StringMap<FnStubInfo>::iterator I = FnStubs.begin(), E = FnStubs.end();
         I != E; ++I) {
      SwitchToTextSection("\t.section __TEXT,__picsymbolstub1,symbol_stubs,"
                          "pure_instructions,32");
      EmitAlignment(4);
      const FnStubInfo &Info = I->second;
      O << Info.Stub << ":\n";
      O << "\t.indirect_symbol " << I->getKeyData() << '\n';
      O << "\tmflr r0\n";
      O << "\tbcl 20,31," << Info.AnonSymbol << '\n';
      O << Info.AnonSymbol << ":\n";
      O << "\tmflr r11\n";
      O << "\taddis r11,r11,ha16(" << Info.LazyPtr << "-" << Info.AnonSymbol;
      O << ")\n";
      O << "\tmtlr r0\n";
      O << (isPPC64 ? "\tldu" : "\tlwzu") << " r12,lo16(";
      O << Info.LazyPtr << "-" << Info.AnonSymbol << ")(r11)\n";
      O << "\tmtctr r12\n";
      O << "\tbctr\n";
      
      SwitchToDataSection(".lazy_symbol_pointer");
      O << Info.LazyPtr << ":\n";
      O << "\t.indirect_symbol " << I->getKeyData() << '\n';
      O << (isPPC64 ? "\t.quad" : "\t.long") << " dyld_stub_binding_helper\n";
    }
  } else if (!FnStubs.empty()) {
    for (StringMap<FnStubInfo>::iterator I = FnStubs.begin(), E = FnStubs.end();
         I != E; ++I) {
      SwitchToTextSection("\t.section __TEXT,__symbol_stub1,symbol_stubs,"
                          "pure_instructions,16");
      EmitAlignment(4);
      const FnStubInfo &Info = I->second;
      O << Info.Stub << ":\n";
      O << "\t.indirect_symbol " << I->getKeyData() << '\n';
      O << "\tlis r11,ha16(" << Info.LazyPtr << ")\n";
      O << (isPPC64 ? "\tldu" :  "\tlwzu") << " r12,lo16(";
      O << Info.LazyPtr << ")(r11)\n";
      O << "\tmtctr r12\n";
      O << "\tbctr\n";
      SwitchToDataSection(".lazy_symbol_pointer");
      O << Info.LazyPtr << ":\n";
      O << "\t.indirect_symbol " << I->getKeyData() << '\n';
      O << (isPPC64 ? "\t.quad" : "\t.long") << " dyld_stub_binding_helper\n";
    }
  }

  O << '\n';

  if (TAI->doesSupportExceptionHandling() && MMI) {
    // Add the (possibly multiple) personalities to the set of global values.
    // Only referenced functions get into the Personalities list.
    const std::vector<Function *> &Personalities = MMI->getPersonalities();
    for (std::vector<Function *>::const_iterator I = Personalities.begin(),
         E = Personalities.end(); I != E; ++I) {
      if (*I)
        GVStubs[Mang->getMangledName(*I)] =
          Mang->getMangledName(*I, "$non_lazy_ptr", true);
    }
  }

  // Output stubs for external and common global variables.
  if (!GVStubs.empty()) {
    SwitchToDataSection(".non_lazy_symbol_pointer");
    for (StringMap<std::string>::iterator I = GVStubs.begin(),
         E = GVStubs.end(); I != E; ++I) {
      O << I->second << ":\n";
      O << "\t.indirect_symbol " << I->getKeyData() << '\n';
      O << (isPPC64 ? "\t.quad\t0\n" : "\t.long\t0\n");
    }
  }

  if (!HiddenGVStubs.empty()) {
    SwitchToSection(TAI->getDataSection());
    EmitAlignment(isPPC64 ? 3 : 2);
    for (StringMap<std::string>::iterator I = HiddenGVStubs.begin(),
         E = HiddenGVStubs.end(); I != E; ++I) {
      O << I->second << ":\n";
      O << (isPPC64 ? "\t.quad\t" : "\t.long\t") << I->getKeyData() << '\n';
    }
  }

  // Funny Darwin hack: This flag tells the linker that no global symbols
  // contain code that falls through to other global symbols (e.g. the obvious
  // implementation of multiple entry points).  If this doesn't occur, the
  // linker can safely perform dead code stripping.  Since LLVM never generates
  // code that does this, it is always safe to set.
  O << "\t.subsections_via_symbols\n";

  return AsmPrinter::doFinalization(M);
}



/// createPPCAsmPrinterPass - Returns a pass that prints the PPC assembly code
/// for a MachineFunction to the given output stream, in a format that the
/// Darwin assembler can deal with.
///
FunctionPass *llvm::createPPCAsmPrinterPass(formatted_raw_ostream &o,
                                            TargetMachine &tm,
                                            bool verbose) {
  const PPCSubtarget *Subtarget = &tm.getSubtarget<PPCSubtarget>();

  if (Subtarget->isDarwin()) {
    return new PPCDarwinAsmPrinter(o, tm, tm.getTargetAsmInfo(), verbose);
  } else {
    return new PPCLinuxAsmPrinter(o, tm, tm.getTargetAsmInfo(), verbose);
  }
}

extern "C" int PowerPCAsmPrinterForceLink;
int PowerPCAsmPrinterForceLink = 0;

// Force static initialization.
extern "C" void LLVMInitializePowerPCAsmPrinter() { 
  extern Target ThePPC32Target;
  TargetRegistry::RegisterAsmPrinter(ThePPC32Target, createPPCAsmPrinterPass);

  extern Target ThePPC64Target;
  TargetRegistry::RegisterAsmPrinter(ThePPC64Target, createPPCAsmPrinterPass);
}
