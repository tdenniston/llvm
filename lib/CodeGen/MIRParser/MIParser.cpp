//===- MIParser.cpp - Machine instructions parser implementation ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the parsing of machine instructions.
//
//===----------------------------------------------------------------------===//

#include "MIParser.h"
#include "MILexer.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/AsmParser/SlotMapping.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Target/TargetSubtargetInfo.h"
#include "llvm/Target/TargetInstrInfo.h"

using namespace llvm;

namespace {

struct StringValueUtility {
  StringRef String;
  std::string UnescapedString;

  StringValueUtility(const MIToken &Token) {
    if (Token.isStringValueQuoted()) {
      Token.unescapeQuotedStringValue(UnescapedString);
      String = UnescapedString;
      return;
    }
    String = Token.stringValue();
  }

  operator StringRef() const { return String; }
};

/// A wrapper struct around the 'MachineOperand' struct that includes a source
/// range.
struct MachineOperandWithLocation {
  MachineOperand Operand;
  StringRef::iterator Begin;
  StringRef::iterator End;

  MachineOperandWithLocation(const MachineOperand &Operand,
                             StringRef::iterator Begin, StringRef::iterator End)
      : Operand(Operand), Begin(Begin), End(End) {}
};

class MIParser {
  SourceMgr &SM;
  MachineFunction &MF;
  SMDiagnostic &Error;
  StringRef Source, CurrentSource;
  MIToken Token;
  const PerFunctionMIParsingState &PFS;
  /// Maps from indices to unnamed global values and metadata nodes.
  const SlotMapping &IRSlots;
  /// Maps from instruction names to op codes.
  StringMap<unsigned> Names2InstrOpCodes;
  /// Maps from register names to registers.
  StringMap<unsigned> Names2Regs;
  /// Maps from register mask names to register masks.
  StringMap<const uint32_t *> Names2RegMasks;
  /// Maps from subregister names to subregister indices.
  StringMap<unsigned> Names2SubRegIndices;
  /// Maps from slot numbers to function's unnamed basic blocks.
  DenseMap<unsigned, const BasicBlock *> Slots2BasicBlocks;
  /// Maps from target index names to target indices.
  StringMap<int> Names2TargetIndices;

public:
  MIParser(SourceMgr &SM, MachineFunction &MF, SMDiagnostic &Error,
           StringRef Source, const PerFunctionMIParsingState &PFS,
           const SlotMapping &IRSlots);

  void lex();

  /// Report an error at the current location with the given message.
  ///
  /// This function always return true.
  bool error(const Twine &Msg);

  /// Report an error at the given location with the given message.
  ///
  /// This function always return true.
  bool error(StringRef::iterator Loc, const Twine &Msg);

  bool parse(MachineInstr *&MI);
  bool parseStandaloneMBB(MachineBasicBlock *&MBB);
  bool parseStandaloneNamedRegister(unsigned &Reg);
  bool parseStandaloneVirtualRegister(unsigned &Reg);
  bool parseStandaloneIRBlockReference(const BasicBlock *&BB);

  bool parseRegister(unsigned &Reg);
  bool parseRegisterFlag(unsigned &Flags);
  bool parseSubRegisterIndex(unsigned &SubReg);
  bool parseRegisterOperand(MachineOperand &Dest, bool IsDef = false);
  bool parseImmediateOperand(MachineOperand &Dest);
  bool parseMBBReference(MachineBasicBlock *&MBB);
  bool parseMBBOperand(MachineOperand &Dest);
  bool parseStackObjectOperand(MachineOperand &Dest);
  bool parseFixedStackObjectOperand(MachineOperand &Dest);
  bool parseGlobalValue(GlobalValue *&GV);
  bool parseGlobalAddressOperand(MachineOperand &Dest);
  bool parseConstantPoolIndexOperand(MachineOperand &Dest);
  bool parseJumpTableIndexOperand(MachineOperand &Dest);
  bool parseExternalSymbolOperand(MachineOperand &Dest);
  bool parseMDNode(MDNode *&Node);
  bool parseMetadataOperand(MachineOperand &Dest);
  bool parseCFIOffset(int &Offset);
  bool parseCFIRegister(unsigned &Reg);
  bool parseCFIOperand(MachineOperand &Dest);
  bool parseIRBlock(BasicBlock *&BB, const Function &F);
  bool parseBlockAddressOperand(MachineOperand &Dest);
  bool parseTargetIndexOperand(MachineOperand &Dest);
  bool parseMachineOperand(MachineOperand &Dest);

private:
  /// Convert the integer literal in the current token into an unsigned integer.
  ///
  /// Return true if an error occurred.
  bool getUnsigned(unsigned &Result);

  /// If the current token is of the given kind, consume it and return false.
  /// Otherwise report an error and return true.
  bool expectAndConsume(MIToken::TokenKind TokenKind);

  void initNames2InstrOpCodes();

  /// Try to convert an instruction name to an opcode. Return true if the
  /// instruction name is invalid.
  bool parseInstrName(StringRef InstrName, unsigned &OpCode);

  bool parseInstruction(unsigned &OpCode, unsigned &Flags);

  bool verifyImplicitOperands(ArrayRef<MachineOperandWithLocation> Operands,
                              const MCInstrDesc &MCID);

  void initNames2Regs();

  /// Try to convert a register name to a register number. Return true if the
  /// register name is invalid.
  bool getRegisterByName(StringRef RegName, unsigned &Reg);

  void initNames2RegMasks();

  /// Check if the given identifier is a name of a register mask.
  ///
  /// Return null if the identifier isn't a register mask.
  const uint32_t *getRegMask(StringRef Identifier);

  void initNames2SubRegIndices();

  /// Check if the given identifier is a name of a subregister index.
  ///
  /// Return 0 if the name isn't a subregister index class.
  unsigned getSubRegIndex(StringRef Name);

  void initSlots2BasicBlocks();

  const BasicBlock *getIRBlock(unsigned Slot);

  void initNames2TargetIndices();

  /// Try to convert a name of target index to the corresponding target index.
  ///
  /// Return true if the name isn't a name of a target index.
  bool getTargetIndex(StringRef Name, int &Index);
};

} // end anonymous namespace

MIParser::MIParser(SourceMgr &SM, MachineFunction &MF, SMDiagnostic &Error,
                   StringRef Source, const PerFunctionMIParsingState &PFS,
                   const SlotMapping &IRSlots)
    : SM(SM), MF(MF), Error(Error), Source(Source), CurrentSource(Source),
      Token(MIToken::Error, StringRef()), PFS(PFS), IRSlots(IRSlots) {}

void MIParser::lex() {
  CurrentSource = lexMIToken(
      CurrentSource, Token,
      [this](StringRef::iterator Loc, const Twine &Msg) { error(Loc, Msg); });
}

bool MIParser::error(const Twine &Msg) { return error(Token.location(), Msg); }

bool MIParser::error(StringRef::iterator Loc, const Twine &Msg) {
  assert(Loc >= Source.data() && Loc <= (Source.data() + Source.size()));
  Error = SMDiagnostic(
      SM, SMLoc(),
      SM.getMemoryBuffer(SM.getMainFileID())->getBufferIdentifier(), 1,
      Loc - Source.data(), SourceMgr::DK_Error, Msg.str(), Source, None, None);
  return true;
}

static const char *toString(MIToken::TokenKind TokenKind) {
  switch (TokenKind) {
  case MIToken::comma:
    return "','";
  case MIToken::lparen:
    return "'('";
  case MIToken::rparen:
    return "')'";
  default:
    return "<unknown token>";
  }
}

bool MIParser::expectAndConsume(MIToken::TokenKind TokenKind) {
  if (Token.isNot(TokenKind))
    return error(Twine("expected ") + toString(TokenKind));
  lex();
  return false;
}

bool MIParser::parse(MachineInstr *&MI) {
  lex();

  // Parse any register operands before '='
  // TODO: Allow parsing of multiple operands before '='
  MachineOperand MO = MachineOperand::CreateImm(0);
  SmallVector<MachineOperandWithLocation, 8> Operands;
  if (Token.isRegister() || Token.isRegisterFlag()) {
    auto Loc = Token.location();
    if (parseRegisterOperand(MO, /*IsDef=*/true))
      return true;
    Operands.push_back(MachineOperandWithLocation(MO, Loc, Token.location()));
    if (Token.isNot(MIToken::equal))
      return error("expected '='");
    lex();
  }

  unsigned OpCode, Flags = 0;
  if (Token.isError() || parseInstruction(OpCode, Flags))
    return true;

  // TODO: Parse the bundle instruction flags and memory operands.

  // Parse the remaining machine operands.
  while (Token.isNot(MIToken::Eof) && Token.isNot(MIToken::kw_debug_location)) {
    auto Loc = Token.location();
    if (parseMachineOperand(MO))
      return true;
    Operands.push_back(MachineOperandWithLocation(MO, Loc, Token.location()));
    if (Token.is(MIToken::Eof))
      break;
    if (Token.isNot(MIToken::comma))
      return error("expected ',' before the next machine operand");
    lex();
  }

  DebugLoc DebugLocation;
  if (Token.is(MIToken::kw_debug_location)) {
    lex();
    if (Token.isNot(MIToken::exclaim))
      return error("expected a metadata node after 'debug-location'");
    MDNode *Node = nullptr;
    if (parseMDNode(Node))
      return true;
    DebugLocation = DebugLoc(Node);
  }

  const auto &MCID = MF.getSubtarget().getInstrInfo()->get(OpCode);
  if (!MCID.isVariadic()) {
    // FIXME: Move the implicit operand verification to the machine verifier.
    if (verifyImplicitOperands(Operands, MCID))
      return true;
  }

  // TODO: Check for extraneous machine operands.
  MI = MF.CreateMachineInstr(MCID, DebugLocation, /*NoImplicit=*/true);
  MI->setFlags(Flags);
  for (const auto &Operand : Operands)
    MI->addOperand(MF, Operand.Operand);
  return false;
}

bool MIParser::parseStandaloneMBB(MachineBasicBlock *&MBB) {
  lex();
  if (Token.isNot(MIToken::MachineBasicBlock))
    return error("expected a machine basic block reference");
  if (parseMBBReference(MBB))
    return true;
  lex();
  if (Token.isNot(MIToken::Eof))
    return error(
        "expected end of string after the machine basic block reference");
  return false;
}

bool MIParser::parseStandaloneNamedRegister(unsigned &Reg) {
  lex();
  if (Token.isNot(MIToken::NamedRegister))
    return error("expected a named register");
  if (parseRegister(Reg))
    return 0;
  lex();
  if (Token.isNot(MIToken::Eof))
    return error("expected end of string after the register reference");
  return false;
}

bool MIParser::parseStandaloneVirtualRegister(unsigned &Reg) {
  lex();
  if (Token.isNot(MIToken::VirtualRegister))
    return error("expected a virtual register");
  if (parseRegister(Reg))
    return 0;
  lex();
  if (Token.isNot(MIToken::Eof))
    return error("expected end of string after the register reference");
  return false;
}

bool MIParser::parseStandaloneIRBlockReference(const BasicBlock *&BB) {
  lex();
  if (Token.isNot(MIToken::IRBlock))
    return error("expected an IR block reference");
  unsigned SlotNumber = 0;
  if (getUnsigned(SlotNumber))
    return true;
  BB = getIRBlock(SlotNumber);
  if (!BB)
    return error(Twine("use of undefined IR block '%ir-block.") +
                 Twine(SlotNumber) + "'");
  lex();
  if (Token.isNot(MIToken::Eof))
    return error("expected end of string after the IR block reference");
  return false;
}

static const char *printImplicitRegisterFlag(const MachineOperand &MO) {
  assert(MO.isImplicit());
  return MO.isDef() ? "implicit-def" : "implicit";
}

static std::string getRegisterName(const TargetRegisterInfo *TRI,
                                   unsigned Reg) {
  assert(TargetRegisterInfo::isPhysicalRegister(Reg) && "expected phys reg");
  return StringRef(TRI->getName(Reg)).lower();
}

bool MIParser::verifyImplicitOperands(
    ArrayRef<MachineOperandWithLocation> Operands, const MCInstrDesc &MCID) {
  if (MCID.isCall())
    // We can't verify call instructions as they can contain arbitrary implicit
    // register and register mask operands.
    return false;

  // Gather all the expected implicit operands.
  SmallVector<MachineOperand, 4> ImplicitOperands;
  if (MCID.ImplicitDefs)
    for (const uint16_t *ImpDefs = MCID.getImplicitDefs(); *ImpDefs; ++ImpDefs)
      ImplicitOperands.push_back(
          MachineOperand::CreateReg(*ImpDefs, true, true));
  if (MCID.ImplicitUses)
    for (const uint16_t *ImpUses = MCID.getImplicitUses(); *ImpUses; ++ImpUses)
      ImplicitOperands.push_back(
          MachineOperand::CreateReg(*ImpUses, false, true));

  const auto *TRI = MF.getSubtarget().getRegisterInfo();
  assert(TRI && "Expected target register info");
  size_t I = ImplicitOperands.size(), J = Operands.size();
  while (I) {
    --I;
    if (J) {
      --J;
      const auto &ImplicitOperand = ImplicitOperands[I];
      const auto &Operand = Operands[J].Operand;
      if (ImplicitOperand.isIdenticalTo(Operand))
        continue;
      if (Operand.isReg() && Operand.isImplicit()) {
        return error(Operands[J].Begin,
                     Twine("expected an implicit register operand '") +
                         printImplicitRegisterFlag(ImplicitOperand) + " %" +
                         getRegisterName(TRI, ImplicitOperand.getReg()) + "'");
      }
    }
    // TODO: Fix source location when Operands[J].end is right before '=', i.e:
    // insead of reporting an error at this location:
    //            %eax = MOV32r0
    //                 ^
    // report the error at the following location:
    //            %eax = MOV32r0
    //                          ^
    return error(J < Operands.size() ? Operands[J].End : Token.location(),
                 Twine("missing implicit register operand '") +
                     printImplicitRegisterFlag(ImplicitOperands[I]) + " %" +
                     getRegisterName(TRI, ImplicitOperands[I].getReg()) + "'");
  }
  return false;
}

bool MIParser::parseInstruction(unsigned &OpCode, unsigned &Flags) {
  if (Token.is(MIToken::kw_frame_setup)) {
    Flags |= MachineInstr::FrameSetup;
    lex();
  }
  if (Token.isNot(MIToken::Identifier))
    return error("expected a machine instruction");
  StringRef InstrName = Token.stringValue();
  if (parseInstrName(InstrName, OpCode))
    return error(Twine("unknown machine instruction name '") + InstrName + "'");
  lex();
  return false;
}

bool MIParser::parseRegister(unsigned &Reg) {
  switch (Token.kind()) {
  case MIToken::underscore:
    Reg = 0;
    break;
  case MIToken::NamedRegister: {
    StringRef Name = Token.stringValue();
    if (getRegisterByName(Name, Reg))
      return error(Twine("unknown register name '") + Name + "'");
    break;
  }
  case MIToken::VirtualRegister: {
    unsigned ID;
    if (getUnsigned(ID))
      return true;
    const auto RegInfo = PFS.VirtualRegisterSlots.find(ID);
    if (RegInfo == PFS.VirtualRegisterSlots.end())
      return error(Twine("use of undefined virtual register '%") + Twine(ID) +
                   "'");
    Reg = RegInfo->second;
    break;
  }
  // TODO: Parse other register kinds.
  default:
    llvm_unreachable("The current token should be a register");
  }
  return false;
}

bool MIParser::parseRegisterFlag(unsigned &Flags) {
  switch (Token.kind()) {
  case MIToken::kw_implicit:
    Flags |= RegState::Implicit;
    break;
  case MIToken::kw_implicit_define:
    Flags |= RegState::ImplicitDefine;
    break;
  case MIToken::kw_dead:
    Flags |= RegState::Dead;
    break;
  case MIToken::kw_killed:
    Flags |= RegState::Kill;
    break;
  case MIToken::kw_undef:
    Flags |= RegState::Undef;
    break;
  // TODO: report an error when we specify the same flag more than once.
  // TODO: parse the other register flags.
  default:
    llvm_unreachable("The current token should be a register flag");
  }
  lex();
  return false;
}

bool MIParser::parseSubRegisterIndex(unsigned &SubReg) {
  assert(Token.is(MIToken::colon));
  lex();
  if (Token.isNot(MIToken::Identifier))
    return error("expected a subregister index after ':'");
  auto Name = Token.stringValue();
  SubReg = getSubRegIndex(Name);
  if (!SubReg)
    return error(Twine("use of unknown subregister index '") + Name + "'");
  lex();
  return false;
}

bool MIParser::parseRegisterOperand(MachineOperand &Dest, bool IsDef) {
  unsigned Reg;
  unsigned Flags = IsDef ? RegState::Define : 0;
  while (Token.isRegisterFlag()) {
    if (parseRegisterFlag(Flags))
      return true;
  }
  if (!Token.isRegister())
    return error("expected a register after register flags");
  if (parseRegister(Reg))
    return true;
  lex();
  unsigned SubReg = 0;
  if (Token.is(MIToken::colon)) {
    if (parseSubRegisterIndex(SubReg))
      return true;
  }
  Dest = MachineOperand::CreateReg(
      Reg, Flags & RegState::Define, Flags & RegState::Implicit,
      Flags & RegState::Kill, Flags & RegState::Dead, Flags & RegState::Undef,
      /*isEarlyClobber=*/false, SubReg);
  return false;
}

bool MIParser::parseImmediateOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::IntegerLiteral));
  const APSInt &Int = Token.integerValue();
  if (Int.getMinSignedBits() > 64)
    // TODO: Replace this with an error when we can parse CIMM Machine Operands.
    llvm_unreachable("Can't parse large integer literals yet!");
  Dest = MachineOperand::CreateImm(Int.getExtValue());
  lex();
  return false;
}

bool MIParser::getUnsigned(unsigned &Result) {
  assert(Token.hasIntegerValue() && "Expected a token with an integer value");
  const uint64_t Limit = uint64_t(std::numeric_limits<unsigned>::max()) + 1;
  uint64_t Val64 = Token.integerValue().getLimitedValue(Limit);
  if (Val64 == Limit)
    return error("expected 32-bit integer (too large)");
  Result = Val64;
  return false;
}

bool MIParser::parseMBBReference(MachineBasicBlock *&MBB) {
  assert(Token.is(MIToken::MachineBasicBlock));
  unsigned Number;
  if (getUnsigned(Number))
    return true;
  auto MBBInfo = PFS.MBBSlots.find(Number);
  if (MBBInfo == PFS.MBBSlots.end())
    return error(Twine("use of undefined machine basic block #") +
                 Twine(Number));
  MBB = MBBInfo->second;
  if (!Token.stringValue().empty() && Token.stringValue() != MBB->getName())
    return error(Twine("the name of machine basic block #") + Twine(Number) +
                 " isn't '" + Token.stringValue() + "'");
  return false;
}

bool MIParser::parseMBBOperand(MachineOperand &Dest) {
  MachineBasicBlock *MBB;
  if (parseMBBReference(MBB))
    return true;
  Dest = MachineOperand::CreateMBB(MBB);
  lex();
  return false;
}

bool MIParser::parseStackObjectOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::StackObject));
  unsigned ID;
  if (getUnsigned(ID))
    return true;
  auto ObjectInfo = PFS.StackObjectSlots.find(ID);
  if (ObjectInfo == PFS.StackObjectSlots.end())
    return error(Twine("use of undefined stack object '%stack.") + Twine(ID) +
                 "'");
  StringRef Name;
  if (const auto *Alloca =
          MF.getFrameInfo()->getObjectAllocation(ObjectInfo->second))
    Name = Alloca->getName();
  if (!Token.stringValue().empty() && Token.stringValue() != Name)
    return error(Twine("the name of the stack object '%stack.") + Twine(ID) +
                 "' isn't '" + Token.stringValue() + "'");
  lex();
  Dest = MachineOperand::CreateFI(ObjectInfo->second);
  return false;
}

bool MIParser::parseFixedStackObjectOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::FixedStackObject));
  unsigned ID;
  if (getUnsigned(ID))
    return true;
  auto ObjectInfo = PFS.FixedStackObjectSlots.find(ID);
  if (ObjectInfo == PFS.FixedStackObjectSlots.end())
    return error(Twine("use of undefined fixed stack object '%fixed-stack.") +
                 Twine(ID) + "'");
  lex();
  Dest = MachineOperand::CreateFI(ObjectInfo->second);
  return false;
}

bool MIParser::parseGlobalValue(GlobalValue *&GV) {
  switch (Token.kind()) {
  case MIToken::NamedGlobalValue:
  case MIToken::QuotedNamedGlobalValue: {
    StringValueUtility Name(Token);
    const Module *M = MF.getFunction()->getParent();
    GV = M->getNamedValue(Name);
    if (!GV)
      return error(Twine("use of undefined global value '@") +
                   Token.rawStringValue() + "'");
    break;
  }
  case MIToken::GlobalValue: {
    unsigned GVIdx;
    if (getUnsigned(GVIdx))
      return true;
    if (GVIdx >= IRSlots.GlobalValues.size())
      return error(Twine("use of undefined global value '@") + Twine(GVIdx) +
                   "'");
    GV = IRSlots.GlobalValues[GVIdx];
    break;
  }
  default:
    llvm_unreachable("The current token should be a global value");
  }
  return false;
}

bool MIParser::parseGlobalAddressOperand(MachineOperand &Dest) {
  GlobalValue *GV = nullptr;
  if (parseGlobalValue(GV))
    return true;
  Dest = MachineOperand::CreateGA(GV, /*Offset=*/0);
  // TODO: Parse offset and target flags.
  lex();
  return false;
}

bool MIParser::parseConstantPoolIndexOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::ConstantPoolItem));
  unsigned ID;
  if (getUnsigned(ID))
    return true;
  auto ConstantInfo = PFS.ConstantPoolSlots.find(ID);
  if (ConstantInfo == PFS.ConstantPoolSlots.end())
    return error("use of undefined constant '%const." + Twine(ID) + "'");
  lex();
  // TODO: Parse offset and target flags.
  Dest = MachineOperand::CreateCPI(ID, /*Offset=*/0);
  return false;
}

bool MIParser::parseJumpTableIndexOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::JumpTableIndex));
  unsigned ID;
  if (getUnsigned(ID))
    return true;
  auto JumpTableEntryInfo = PFS.JumpTableSlots.find(ID);
  if (JumpTableEntryInfo == PFS.JumpTableSlots.end())
    return error("use of undefined jump table '%jump-table." + Twine(ID) + "'");
  lex();
  // TODO: Parse target flags.
  Dest = MachineOperand::CreateJTI(JumpTableEntryInfo->second);
  return false;
}

bool MIParser::parseExternalSymbolOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::ExternalSymbol) ||
         Token.is(MIToken::QuotedExternalSymbol));
  StringValueUtility Name(Token);
  const char *Symbol = MF.createExternalSymbolName(Name);
  lex();
  // TODO: Parse the target flags.
  Dest = MachineOperand::CreateES(Symbol);
  return false;
}

bool MIParser::parseMDNode(MDNode *&Node) {
  assert(Token.is(MIToken::exclaim));
  auto Loc = Token.location();
  lex();
  if (Token.isNot(MIToken::IntegerLiteral) || Token.integerValue().isSigned())
    return error("expected metadata id after '!'");
  unsigned ID;
  if (getUnsigned(ID))
    return true;
  auto NodeInfo = IRSlots.MetadataNodes.find(ID);
  if (NodeInfo == IRSlots.MetadataNodes.end())
    return error(Loc, "use of undefined metadata '!" + Twine(ID) + "'");
  lex();
  Node = NodeInfo->second.get();
  return false;
}

bool MIParser::parseMetadataOperand(MachineOperand &Dest) {
  MDNode *Node = nullptr;
  if (parseMDNode(Node))
    return true;
  Dest = MachineOperand::CreateMetadata(Node);
  return false;
}

bool MIParser::parseCFIOffset(int &Offset) {
  if (Token.isNot(MIToken::IntegerLiteral))
    return error("expected a cfi offset");
  if (Token.integerValue().getMinSignedBits() > 32)
    return error("expected a 32 bit integer (the cfi offset is too large)");
  Offset = (int)Token.integerValue().getExtValue();
  lex();
  return false;
}

bool MIParser::parseCFIRegister(unsigned &Reg) {
  if (Token.isNot(MIToken::NamedRegister))
    return error("expected a cfi register");
  unsigned LLVMReg;
  if (parseRegister(LLVMReg))
    return true;
  const auto *TRI = MF.getSubtarget().getRegisterInfo();
  assert(TRI && "Expected target register info");
  int DwarfReg = TRI->getDwarfRegNum(LLVMReg, true);
  if (DwarfReg < 0)
    return error("invalid DWARF register");
  Reg = (unsigned)DwarfReg;
  lex();
  return false;
}

bool MIParser::parseCFIOperand(MachineOperand &Dest) {
  auto Kind = Token.kind();
  lex();
  auto &MMI = MF.getMMI();
  int Offset;
  unsigned Reg;
  unsigned CFIIndex;
  switch (Kind) {
  case MIToken::kw_cfi_offset:
    if (parseCFIRegister(Reg) || expectAndConsume(MIToken::comma) ||
        parseCFIOffset(Offset))
      return true;
    CFIIndex =
        MMI.addFrameInst(MCCFIInstruction::createOffset(nullptr, Reg, Offset));
    break;
  case MIToken::kw_cfi_def_cfa_register:
    if (parseCFIRegister(Reg))
      return true;
    CFIIndex =
        MMI.addFrameInst(MCCFIInstruction::createDefCfaRegister(nullptr, Reg));
    break;
  case MIToken::kw_cfi_def_cfa_offset:
    if (parseCFIOffset(Offset))
      return true;
    // NB: MCCFIInstruction::createDefCfaOffset negates the offset.
    CFIIndex = MMI.addFrameInst(
        MCCFIInstruction::createDefCfaOffset(nullptr, -Offset));
    break;
  default:
    // TODO: Parse the other CFI operands.
    llvm_unreachable("The current token should be a cfi operand");
  }
  Dest = MachineOperand::CreateCFIIndex(CFIIndex);
  return false;
}

bool MIParser::parseIRBlock(BasicBlock *&BB, const Function &F) {
  switch (Token.kind()) {
  case MIToken::NamedIRBlock:
  case MIToken::QuotedNamedIRBlock: {
    StringValueUtility Name(Token);
    BB = dyn_cast_or_null<BasicBlock>(F.getValueSymbolTable().lookup(Name));
    if (!BB)
      return error(Twine("use of undefined IR block '%ir-block.") +
                   Token.rawStringValue() + "'");
    break;
  }
  case MIToken::IRBlock: {
    unsigned SlotNumber = 0;
    if (getUnsigned(SlotNumber))
      return true;
    BB = const_cast<BasicBlock *>(getIRBlock(SlotNumber));
    if (!BB)
      return error(Twine("use of undefined IR block '%ir-block.") +
                   Twine(SlotNumber) + "'");
    break;
  }
  default:
    llvm_unreachable("The current token should be an IR block reference");
  }
  return false;
}

bool MIParser::parseBlockAddressOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::kw_blockaddress));
  lex();
  if (expectAndConsume(MIToken::lparen))
    return true;
  if (Token.isNot(MIToken::GlobalValue) &&
      Token.isNot(MIToken::NamedGlobalValue) &&
      Token.isNot(MIToken::QuotedNamedGlobalValue))
    return error("expected a global value");
  GlobalValue *GV = nullptr;
  if (parseGlobalValue(GV))
    return true;
  auto *F = dyn_cast<Function>(GV);
  if (!F)
    return error("expected an IR function reference");
  lex();
  if (expectAndConsume(MIToken::comma))
    return true;
  BasicBlock *BB = nullptr;
  if (Token.isNot(MIToken::IRBlock) && Token.isNot(MIToken::NamedIRBlock) &&
      Token.isNot(MIToken::QuotedNamedIRBlock))
    return error("expected an IR block reference");
  if (parseIRBlock(BB, *F))
    return true;
  lex();
  if (expectAndConsume(MIToken::rparen))
    return true;
  // TODO: parse offset and target flags.
  Dest = MachineOperand::CreateBA(BlockAddress::get(F, BB), /*Offset=*/0);
  return false;
}

bool MIParser::parseTargetIndexOperand(MachineOperand &Dest) {
  assert(Token.is(MIToken::kw_target_index));
  lex();
  if (expectAndConsume(MIToken::lparen))
    return true;
  if (Token.isNot(MIToken::Identifier))
    return error("expected the name of the target index");
  int Index = 0;
  if (getTargetIndex(Token.stringValue(), Index))
    return error("use of undefined target index '" + Token.stringValue() + "'");
  lex();
  if (expectAndConsume(MIToken::rparen))
    return true;
  // TODO: Parse the offset and target flags.
  Dest = MachineOperand::CreateTargetIndex(unsigned(Index), /*Offset=*/0);
  return false;
}

bool MIParser::parseMachineOperand(MachineOperand &Dest) {
  switch (Token.kind()) {
  case MIToken::kw_implicit:
  case MIToken::kw_implicit_define:
  case MIToken::kw_dead:
  case MIToken::kw_killed:
  case MIToken::kw_undef:
  case MIToken::underscore:
  case MIToken::NamedRegister:
  case MIToken::VirtualRegister:
    return parseRegisterOperand(Dest);
  case MIToken::IntegerLiteral:
    return parseImmediateOperand(Dest);
  case MIToken::MachineBasicBlock:
    return parseMBBOperand(Dest);
  case MIToken::StackObject:
    return parseStackObjectOperand(Dest);
  case MIToken::FixedStackObject:
    return parseFixedStackObjectOperand(Dest);
  case MIToken::GlobalValue:
  case MIToken::NamedGlobalValue:
  case MIToken::QuotedNamedGlobalValue:
    return parseGlobalAddressOperand(Dest);
  case MIToken::ConstantPoolItem:
    return parseConstantPoolIndexOperand(Dest);
  case MIToken::JumpTableIndex:
    return parseJumpTableIndexOperand(Dest);
  case MIToken::ExternalSymbol:
  case MIToken::QuotedExternalSymbol:
    return parseExternalSymbolOperand(Dest);
  case MIToken::exclaim:
    return parseMetadataOperand(Dest);
  case MIToken::kw_cfi_offset:
  case MIToken::kw_cfi_def_cfa_register:
  case MIToken::kw_cfi_def_cfa_offset:
    return parseCFIOperand(Dest);
  case MIToken::kw_blockaddress:
    return parseBlockAddressOperand(Dest);
  case MIToken::kw_target_index:
    return parseTargetIndexOperand(Dest);
  case MIToken::Error:
    return true;
  case MIToken::Identifier:
    if (const auto *RegMask = getRegMask(Token.stringValue())) {
      Dest = MachineOperand::CreateRegMask(RegMask);
      lex();
      break;
    }
  // fallthrough
  default:
    // TODO: parse the other machine operands.
    return error("expected a machine operand");
  }
  return false;
}

void MIParser::initNames2InstrOpCodes() {
  if (!Names2InstrOpCodes.empty())
    return;
  const auto *TII = MF.getSubtarget().getInstrInfo();
  assert(TII && "Expected target instruction info");
  for (unsigned I = 0, E = TII->getNumOpcodes(); I < E; ++I)
    Names2InstrOpCodes.insert(std::make_pair(StringRef(TII->getName(I)), I));
}

bool MIParser::parseInstrName(StringRef InstrName, unsigned &OpCode) {
  initNames2InstrOpCodes();
  auto InstrInfo = Names2InstrOpCodes.find(InstrName);
  if (InstrInfo == Names2InstrOpCodes.end())
    return true;
  OpCode = InstrInfo->getValue();
  return false;
}

void MIParser::initNames2Regs() {
  if (!Names2Regs.empty())
    return;
  // The '%noreg' register is the register 0.
  Names2Regs.insert(std::make_pair("noreg", 0));
  const auto *TRI = MF.getSubtarget().getRegisterInfo();
  assert(TRI && "Expected target register info");
  for (unsigned I = 0, E = TRI->getNumRegs(); I < E; ++I) {
    bool WasInserted =
        Names2Regs.insert(std::make_pair(StringRef(TRI->getName(I)).lower(), I))
            .second;
    (void)WasInserted;
    assert(WasInserted && "Expected registers to be unique case-insensitively");
  }
}

bool MIParser::getRegisterByName(StringRef RegName, unsigned &Reg) {
  initNames2Regs();
  auto RegInfo = Names2Regs.find(RegName);
  if (RegInfo == Names2Regs.end())
    return true;
  Reg = RegInfo->getValue();
  return false;
}

void MIParser::initNames2RegMasks() {
  if (!Names2RegMasks.empty())
    return;
  const auto *TRI = MF.getSubtarget().getRegisterInfo();
  assert(TRI && "Expected target register info");
  ArrayRef<const uint32_t *> RegMasks = TRI->getRegMasks();
  ArrayRef<const char *> RegMaskNames = TRI->getRegMaskNames();
  assert(RegMasks.size() == RegMaskNames.size());
  for (size_t I = 0, E = RegMasks.size(); I < E; ++I)
    Names2RegMasks.insert(
        std::make_pair(StringRef(RegMaskNames[I]).lower(), RegMasks[I]));
}

const uint32_t *MIParser::getRegMask(StringRef Identifier) {
  initNames2RegMasks();
  auto RegMaskInfo = Names2RegMasks.find(Identifier);
  if (RegMaskInfo == Names2RegMasks.end())
    return nullptr;
  return RegMaskInfo->getValue();
}

void MIParser::initNames2SubRegIndices() {
  if (!Names2SubRegIndices.empty())
    return;
  const TargetRegisterInfo *TRI = MF.getSubtarget().getRegisterInfo();
  for (unsigned I = 1, E = TRI->getNumSubRegIndices(); I < E; ++I)
    Names2SubRegIndices.insert(
        std::make_pair(StringRef(TRI->getSubRegIndexName(I)).lower(), I));
}

unsigned MIParser::getSubRegIndex(StringRef Name) {
  initNames2SubRegIndices();
  auto SubRegInfo = Names2SubRegIndices.find(Name);
  if (SubRegInfo == Names2SubRegIndices.end())
    return 0;
  return SubRegInfo->getValue();
}

void MIParser::initSlots2BasicBlocks() {
  if (!Slots2BasicBlocks.empty())
    return;
  const auto &F = *MF.getFunction();
  ModuleSlotTracker MST(F.getParent());
  MST.incorporateFunction(F);
  for (auto &BB : F) {
    if (BB.hasName())
      continue;
    int Slot = MST.getLocalSlot(&BB);
    if (Slot == -1)
      continue;
    Slots2BasicBlocks.insert(std::make_pair(unsigned(Slot), &BB));
  }
}

const BasicBlock *MIParser::getIRBlock(unsigned Slot) {
  initSlots2BasicBlocks();
  auto BlockInfo = Slots2BasicBlocks.find(Slot);
  if (BlockInfo == Slots2BasicBlocks.end())
    return nullptr;
  return BlockInfo->second;
}

void MIParser::initNames2TargetIndices() {
  if (!Names2TargetIndices.empty())
    return;
  const auto *TII = MF.getSubtarget().getInstrInfo();
  assert(TII && "Expected target instruction info");
  auto Indices = TII->getSerializableTargetIndices();
  for (const auto &I : Indices)
    Names2TargetIndices.insert(std::make_pair(StringRef(I.second), I.first));
}

bool MIParser::getTargetIndex(StringRef Name, int &Index) {
  initNames2TargetIndices();
  auto IndexInfo = Names2TargetIndices.find(Name);
  if (IndexInfo == Names2TargetIndices.end())
    return true;
  Index = IndexInfo->second;
  return false;
}

bool llvm::parseMachineInstr(MachineInstr *&MI, SourceMgr &SM,
                             MachineFunction &MF, StringRef Src,
                             const PerFunctionMIParsingState &PFS,
                             const SlotMapping &IRSlots, SMDiagnostic &Error) {
  return MIParser(SM, MF, Error, Src, PFS, IRSlots).parse(MI);
}

bool llvm::parseMBBReference(MachineBasicBlock *&MBB, SourceMgr &SM,
                             MachineFunction &MF, StringRef Src,
                             const PerFunctionMIParsingState &PFS,
                             const SlotMapping &IRSlots, SMDiagnostic &Error) {
  return MIParser(SM, MF, Error, Src, PFS, IRSlots).parseStandaloneMBB(MBB);
}

bool llvm::parseNamedRegisterReference(unsigned &Reg, SourceMgr &SM,
                                       MachineFunction &MF, StringRef Src,
                                       const PerFunctionMIParsingState &PFS,
                                       const SlotMapping &IRSlots,
                                       SMDiagnostic &Error) {
  return MIParser(SM, MF, Error, Src, PFS, IRSlots)
      .parseStandaloneNamedRegister(Reg);
}

bool llvm::parseVirtualRegisterReference(unsigned &Reg, SourceMgr &SM,
                                         MachineFunction &MF, StringRef Src,
                                         const PerFunctionMIParsingState &PFS,
                                         const SlotMapping &IRSlots,
                                         SMDiagnostic &Error) {
  return MIParser(SM, MF, Error, Src, PFS, IRSlots)
      .parseStandaloneVirtualRegister(Reg);
}

bool llvm::parseIRBlockReference(const BasicBlock *&BB, SourceMgr &SM,
                                 MachineFunction &MF, StringRef Src,
                                 const PerFunctionMIParsingState &PFS,
                                 const SlotMapping &IRSlots,
                                 SMDiagnostic &Error) {
  return MIParser(SM, MF, Error, Src, PFS, IRSlots)
      .parseStandaloneIRBlockReference(BB);
}
