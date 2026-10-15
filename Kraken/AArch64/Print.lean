module

public import Kraken.AArch64.Syntax

public section
/-!
# AArch64 printer
Prints Kraken AArch64 syntax in the assembly dialect accepted by `Kraken.AArch64.Parser.parse`.
The intended property is `parse (print p) = .ok p` for every program `p` that `parse` can
produce (see `PrintTests.lean`). Values outside the parser's image (e.g. `ConstExpr`
arithmetic or `NOP` at `.W32`) are still printed, but won't round-trip.
-/
namespace Kraken.AArch64.Print

def xreg (w : RegWidth) (r : XReg) : String :=
  let p := match w with | .W32 => "w" | .W64 => "x"
  let n : Nat := match r with
    | .X0 => 0 | .X1 => 1 | .X2 => 2 | .X3 => 3 | .X4 => 4 | .X5 => 5 | .X6 => 6 | .X7 => 7
    | .X8 => 8 | .X9 => 9 | .X10 => 10 | .X11 => 11 | .X12 => 12 | .X13 => 13 | .X14 => 14 | .X15 => 15
    | .X16 => 16 | .X17 => 17 | .X18 => 18 | .X19 => 19 | .X20 => 20 | .X21 => 21 | .X22 => 22 | .X23 => 23
    | .X24 => 24 | .X25 => 25 | .X26 => 26 | .X27 => 27 | .X28 => 28 | .X29 => 29 | .X30 => 30
  s!"{p}{n}"

def regOrSp {w} : RegOrSp w → String
  | .low (.reg r) w => xreg w r
  | .low .SP .W32 => "wsp"
  | .low .SP .W64 => "sp"

def regOrZr {w} : RegOrZr w → String
  | .low (.reg r) w => xreg w r
  | .low .XZR .W32 => "wzr"
  | .low .XZR .W64 => "xzr"

def constRaw : ConstExpr → String
  | .label l => l
  | .int64 i => toString i
  | .pg_hi21 e => s!":pg_hi21:{constRaw e}"
  | .lo12 e => s!":lo12:{constRaw e}"
  | .before_current_instruction | .after_current_instruction => "."
  | .add a b => s!"({constRaw a} + {constRaw b})"
  | .sub a b => s!"({constRaw a} - {constRaw b})"

def const : ConstExpr → String
  | .int64 i => s!"#{i}"
  | e => constRaw e

def immConst : ConstExpr → String
  | .int64 i => s!"#{i}"
  | .label l => s!"#{l}"
  | e => constRaw e

def extendType : ExtendType → String
  | .UXTB => "uxtb" | .SXTB => "sxtb" | .UXTH => "uxth" | .SXTH => "sxth"
  | .UXTW => "uxtw" | .SXTW => "sxtw" | .UXTX => "uxtx" | .SXTX => "sxtx"

def extendAmount : ExtendAmount → String
  | .E0 => "#0" | .E1 => "#1" | .E2 => "#2" | .E3 => "#3" | .E4 => "#4"

def memExtendAmount : MemExtendAmount → String
  | .E0 => "#0" | .E1 => "#1" | .E2 => "#2" | .E3 => "#3"

def shiftType : ShiftType → String
  | .LSL => "lsl" | .LSR => "lsr" | .ASR => "asr" | .ROR => "ror"

def cond : CondCode → String
  | .EQ => "eq" | .NE => "ne" | .CS => "cs" | .CC => "cc"
  | .MI => "mi" | .PL => "pl" | .VS => "vs" | .VC => "vc"
  | .HI => "hi" | .LS => "ls" | .GE => "ge" | .LT => "lt"
  | .GT => "gt" | .LE => "le" | .AL => "al" | .NV => "nv"

def extOrImm : ExtOrImmReg → String
  | .ext { reg, ext := { type, amount } } => s!"{regOrZr reg.reg}, {extendType type} {extendAmount amount}"
  | .imm { imm, shift := .S0 } => immConst imm
  | .imm { imm, shift := .S12 } => s!"{immConst imm}, lsl #12"

def shiftReg {w} (s : ShiftRegExpr w) : String :=
  if s.shift == .LSL && s.amount == 0 then regOrZr s.reg
  else s!"{regOrZr s.reg}, {shiftType s.shift} #{s.amount}"

def addr (a : AddrExpr) : String :=
  let b := regOrSp a.base
  match a.off with
  | .imm { imm := .int64 0, index := none } => s!"[{b}]"
  | .imm { imm, index := none } => s!"[{b}, {immConst imm}]"
  | .imm { imm, index := some .Pre } => s!"[{b}, {immConst imm}]!"
  | .imm { imm, index := some .Post } => s!"[{b}], {immConst imm}"
  | .reg { reg, ext := { type, amount } } =>
    let r := regOrZr reg.reg
    let ty := match reg.w, type with
      | .W64, .UXTX => "lsl"
      | _, .UXTW => "uxtw" | _, .SXTW => "sxtw"
      | _, .UXTX => "uxtx" | _, .SXTX => "sxtx"
    s!"[{b}, {r}, {ty} {memExtendAmount amount}]"

def unscaledAddr (a : UnscaledAddrExpr) : String :=
  match a.imm with
  | .int64 0 => s!"[{regOrSp a.base}]"
  | imm => s!"[{regOrSp a.base}, {immConst imm}]"

def addrOrLit : AddrOrLit → String
  | .addr a => addr a
  | .lit (.addr { label }) => label
  | .lit (.pool { expr }) => s!"={constRaw expr}"

def operation {w} (op : Operation w) : String :=
  let two (mn a b : String) := s!"{mn} {a}, {b}"
  let three (mn a b c : String) := s!"{mn} {a}, {b}, {c}"
  let four (mn a b c d : String) := s!"{mn} {a}, {b}, {c}, {d}"
  match op with
  | .LDR d s => two "ldr" (regOrZr d) (addrOrLit s)
  | .STR s d => two "str" (regOrZr s) (addr d)
  | .LDUR d s => two "ldur" (regOrZr d) (unscaledAddr s)
  | .STUR s d => two "stur" (regOrZr s) (unscaledAddr d)
  | .LDP d1 d2 s => three "ldp" (regOrZr d1) (regOrZr d2) (addr s)
  | .STP s1 s2 d => three "stp" (regOrZr s1) (regOrZr s2) (addr d)
  | .LDRB d s => two "ldrb" (regOrZr d) (addr s)
  | .LDURB d s => two "ldurb" (regOrZr d) (unscaledAddr s)
  | .STRB s d => two "strb" (regOrZr s) (addr d)
  | .STURB s d => two "sturb" (regOrZr s) (unscaledAddr d)
  | .LDRSB d s => two "ldrsb" (regOrZr d) (addr s)
  | .LDURSB d s => two "ldursb" (regOrZr d) (unscaledAddr s)
  | .LDRH d s => two "ldrh" (regOrZr d) (addr s)
  | .LDURH d s => two "ldurh" (regOrZr d) (unscaledAddr s)
  | .STRH s d => two "strh" (regOrZr s) (addr d)
  | .STURH s d => two "sturh" (regOrZr s) (unscaledAddr d)
  | .LDRSH d s => two "ldrsh" (regOrZr d) (addr s)
  | .LDURSH d s => two "ldursh" (regOrZr d) (unscaledAddr s)
  | .LDRSW d s => two "ldrsw" (regOrZr d) (addrOrLit s)
  | .LDURSW d s => two "ldursw" (regOrZr d) (unscaledAddr s)
  | .LDPSW d1 d2 s => three "ldpsw" (regOrZr d1) (regOrZr d2) (addr s)
  | .ADD_e d s1 s2 => three "add" (regOrSp d) (regOrSp s1) (extOrImm s2)
  | .ADD_s d s1 s2 => three "add" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .ADDS_e d s1 s2 => three "adds" (regOrZr d) (regOrSp s1) (extOrImm s2)
  | .ADDS_s d s1 s2 => three "adds" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .SUB_e d s1 s2 => three "sub" (regOrSp d) (regOrSp s1) (extOrImm s2)
  | .SUB_s d s1 s2 => three "sub" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .SUBS_e d s1 s2 => three "subs" (regOrZr d) (regOrSp s1) (extOrImm s2)
  | .SUBS_s d s1 s2 => three "subs" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .ADC d s1 s2 => three "adc" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .ADCS d s1 s2 => three "adcs" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .SBC d s1 s2 => three "sbc" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .SBCS d s1 s2 => three "sbcs" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .SDIV d s1 s2 => three "sdiv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .UDIV d s1 s2 => three "udiv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .MADD d s1 s2 s3 => four "madd" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .MSUB d s1 s2 s3 => four "msub" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .SMULH d s1 s2 => three "smulh" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .UMULH d s1 s2 => three "umulh" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .SMADDL d s1 s2 s3 => four "smaddl" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .UMADDL d s1 s2 s3 => four "umaddl" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .SMSUBL d s1 s2 s3 => four "smsubl" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .UMSUBL d s1 s2 s3 => four "umsubl" (regOrZr d) (regOrZr s1) (regOrZr s2) (regOrZr s3)
  | .AND_i d s1 imm => three "and" (regOrSp d) (regOrZr s1) (immConst imm)
  | .AND_s d s1 s2 => three "and" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .ANDS_i d s1 imm => three "ands" (regOrZr d) (regOrZr s1) (immConst imm)
  | .ANDS_s d s1 s2 => three "ands" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .ORR_i d s1 imm => three "orr" (regOrSp d) (regOrZr s1) (immConst imm)
  | .ORR_s d s1 s2 => three "orr" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .ORN_s d s1 s2 => three "orn" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .EOR_i d s1 imm => three "eor" (regOrSp d) (regOrZr s1) (immConst imm)
  | .EOR_s d s1 s2 => three "eor" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .EON_s d s1 s2 => three "eon" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .BIC_s d s1 s2 => three "bic" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .BICS_s d s1 s2 => three "bics" (regOrZr d) (regOrZr s1) (shiftReg s2)
  | .BFM d s r m => four "bfm" (regOrZr d) (regOrZr s) s!"#{r}" s!"#{m}"
  | .SBFM d s r m => four "sbfm" (regOrZr d) (regOrZr s) s!"#{r}" s!"#{m}"
  | .UBFM d s r m => four "ubfm" (regOrZr d) (regOrZr s) s!"#{r}" s!"#{m}"
  | .CLZ d s => two "clz" (regOrZr d) (regOrZr s)
  | .CLS d s => two "cls" (regOrZr d) (regOrZr s)
  | .RBIT d s => two "rbit" (regOrZr d) (regOrZr s)
  | .REV d s => two "rev" (regOrZr d) (regOrZr s)
  | .REV16 d s => two "rev16" (regOrZr d) (regOrZr s)
  | .REV32 d s => two "rev32" (regOrZr d) (regOrZr s)
  | .EXTR d s1 s2 lsb => four "extr" (regOrZr d) (regOrZr s1) (regOrZr s2) s!"#{lsb}"
  | .MOVZ d imm sh => three "movz" (regOrZr d) (const imm) s!"lsl #{sh.toNat}"
  | .MOVK d imm sh => three "movk" (regOrZr d) (const imm) s!"lsl #{sh.toNat}"
  | .MOVN d imm sh => three "movn" (regOrZr d) (const imm) s!"lsl #{sh.toNat}"
  | .LSLV d s1 s2 => three "lslv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .LSRV d s1 s2 => three "lsrv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .ASRV d s1 s2 => three "asrv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .RORV d s1 s2 => three "rorv" (regOrZr d) (regOrZr s1) (regOrZr s2)
  | .CSEL d s1 s2 cc => four "csel" (regOrZr d) (regOrZr s1) (regOrZr s2) (cond cc)
  | .CSINC d s1 s2 cc => four "csinc" (regOrZr d) (regOrZr s1) (regOrZr s2) (cond cc)
  | .CSINV d s1 s2 cc => four "csinv" (regOrZr d) (regOrZr s1) (regOrZr s2) (cond cc)
  | .CSNEG d s1 s2 cc => four "csneg" (regOrZr d) (regOrZr s1) (regOrZr s2) (cond cc)
  | .CCMP_reg s1 s2 nzcv cc => four "ccmp" (regOrZr s1) (regOrZr s2) s!"#{nzcv}" (cond cc)
  | .CCMP_imm s1 imm nzcv cc => four "ccmp" (regOrZr s1) s!"#{imm}" s!"#{nzcv}" (cond cc)
  | .CCMN_reg s1 s2 nzcv cc => four "ccmn" (regOrZr s1) (regOrZr s2) s!"#{nzcv}" (cond cc)
  | .CCMN_imm s1 imm nzcv cc => four "ccmn" (regOrZr s1) s!"#{imm}" s!"#{nzcv}" (cond cc)
  | .ADR d t => two "adr" (regOrZr d) (const t)
  | .ADRP d t => two "adrp" (regOrZr d) (const t)
  | .B t => s!"b {const t}"
  | .B_cond cc t => s!"b.{cond cc} {const t}"
  | .BL t => s!"bl {const t}"
  | .BLR t => s!"blr {regOrZr t}"
  | .BR t => s!"br {regOrZr t}"
  | .RET t => if t == .X30 then "ret" else s!"ret {regOrZr t}"
  | .CBZ r t => two "cbz" (regOrZr r) (const t)
  | .CBNZ r t => two "cbnz" (regOrZr r) (const t)
  | .TBZ r b t => three "tbz" (regOrZr r) s!"#{b}" (const t)
  | .TBNZ r b t => three "tbnz" (regOrZr r) s!"#{b}" (const t)
  | .NOP => "nop"

def instr (i : Instr) : String := operation i.operation

def directive : Directive → String
  | .instr i => instr i
  | .label l => s!"{l}:"
  | .byteArray bs => ".byte " ++ ", ".intercalate (bs.toList.map toString)

end Kraken.AArch64.Print

instance : ToString Instr := ⟨Kraken.AArch64.Print.instr⟩
instance : ToString Directive := ⟨Kraken.AArch64.Print.directive⟩

/-- Print a program in AArch64 assembly syntax, one directive per line. -/
def Kraken.AArch64.print (p : Program) : String :=
  "\n".intercalate (p.map Print.directive)
