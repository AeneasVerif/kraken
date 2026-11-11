module

public import Kraken.AArch64.Parser.Syntax
public meta import Kraken.AArch64.Parser.Syntax
public import Kraken.AArch64.Syntax
public meta import Kraken.AArch64.Syntax
public meta import Lean

/-!
Delaborators for Kraken AArch64 assembly terms into the embedded `⸨prog| ...⸩` syntax defined in
`Kraken.AArch64.Parser.Syntax`.

Closed directives, instructions, operands and registers delaborate to their canonical AArch64 syntax.
Open or non-canonical subterms at any position that admits an antiquotation (`❰t❱` for registers, labels,
constants, memory operands, condition codes and directives, `#❰t❱` for integer immediates) fall back to
Lean's standard delaborator at that subexpression position.
-/

namespace Kraken.AArch64.Parser

open Lean Meta PrettyPrinter Delaborator SubExpr Kraken.Parser

public meta section

-- ============================================================================
-- Low-Level Syntax & Expression Helpers
-- ============================================================================

/-- Construct an affixed keyword node of category `cat` in `Kraken.AArch64.Parser`. -/
private def mkAffixed (cat : Name) (pre stem sfx : String) : TSyntax cat :=
  Kraken.mkAffixed `Kraken.AArch64.Parser cat pre stem sfx

/-- Construct a suffixed keyword node of category `cat` in `Kraken.AArch64.Parser`. -/
private def mkSuffixed (cat : Name) (stem sfx : String) : TSyntax cat :=
  Kraken.mkSuffixed `Kraken.AArch64.Parser cat stem sfx

/-- Annotate a syntax node of any category with the current `SubExpr` term info. -/
private def annotateStx {cat : Name} (stx : TSyntax cat) : DelabM (TSyntax cat) := do
  return ⟨(← annotateTermInfo ⟨stx.raw⟩).raw⟩

private def evalNat? (e : Expr) : Option Nat :=
  e.nat? <|> e.rawNatLit?

private def evalInt64? (e : Expr) : Option Int :=
  e.int?.map fun i => (Int64.ofInt i).toInt

private def evalRegWidth? (e : Expr) : Option RegWidth :=
  match_expr e with
  | RegWidth.W32 => some .W32
  | RegWidth.W64 => some .W64
  | _            => none

private def evalXReg? (e : Expr) : Option XReg :=
  match_expr e with
  | XReg.X0  => some .X0  | XReg.X1  => some .X1  | XReg.X2  => some .X2  | XReg.X3  => some .X3
  | XReg.X4  => some .X4  | XReg.X5  => some .X5  | XReg.X6  => some .X6  | XReg.X7  => some .X7
  | XReg.X8  => some .X8  | XReg.X9  => some .X9  | XReg.X10 => some .X10 | XReg.X11 => some .X11
  | XReg.X12 => some .X12 | XReg.X13 => some .X13 | XReg.X14 => some .X14 | XReg.X15 => some .X15
  | XReg.X16 => some .X16 | XReg.X17 => some .X17 | XReg.X18 => some .X18 | XReg.X19 => some .X19
  | XReg.X20 => some .X20 | XReg.X21 => some .X21 | XReg.X22 => some .X22 | XReg.X23 => some .X23
  | XReg.X24 => some .X24 | XReg.X25 => some .X25 | XReg.X26 => some .X26 | XReg.X27 => some .X27
  | XReg.X28 => some .X28 | XReg.X29 => some .X29 | XReg.X30 => some .X30
  | _        => none

private def evalXRegOrSp? (e : Expr) : Option XRegOrSp :=
  match_expr e with
  | XRegOrSp.reg rExpr => .reg <$> evalXReg? rExpr
  | XRegOrSp.SP        => some .SP
  | _                  => none

private def evalXRegOrXzr? (e : Expr) : Option XRegOrXzr :=
  match_expr e with
  | XRegOrXzr.reg rExpr => .reg <$> evalXReg? rExpr
  | XRegOrXzr.XZR       => some .XZR
  | _                   => none

private def evalExtendType? (e : Expr) : Option ExtendType :=
  match_expr e with
  | ExtendType.UXTB => some .UXTB | ExtendType.SXTB => some .SXTB
  | ExtendType.UXTH => some .UXTH | ExtendType.SXTH => some .SXTH
  | ExtendType.UXTW => some .UXTW | ExtendType.SXTW => some .SXTW
  | ExtendType.UXTX => some .UXTX | ExtendType.SXTX => some .SXTX
  | _               => none

private def evalExtendAmount? (e : Expr) : Option Nat :=
  match_expr e with
  | ExtendAmount.E0 => some 0 | ExtendAmount.E1 => some 1 | ExtendAmount.E2 => some 2
  | ExtendAmount.E3 => some 3 | ExtendAmount.E4 => some 4
  | _               => none

private def evalMemExtendType? (e : Expr) : Option MemExtendType :=
  match_expr e with
  | MemExtendType.UXTW => some .UXTW | MemExtendType.SXTW => some .SXTW
  | MemExtendType.UXTX => some .UXTX | MemExtendType.SXTX => some .SXTX
  | _                  => none

private def evalMemExtendAmount? (e : Expr) : Option Nat :=
  match_expr e with
  | MemExtendAmount.E0 => some 0 | MemExtendAmount.E1 => some 1
  | MemExtendAmount.E2 => some 2 | MemExtendAmount.E3 => some 3
  | _                  => none

private def evalShiftType? (e : Expr) : Option ShiftType :=
  match_expr e with
  | ShiftType.LSL => some .LSL | ShiftType.LSR => some .LSR
  | ShiftType.ASR => some .ASR | ShiftType.ROR => some .ROR
  | _             => none

private def evalImmShift? (e : Expr) : Option ImmShift :=
  match_expr e with
  | ImmShift.S0  => some .S0
  | ImmShift.S12 => some .S12
  | _            => none

private def evalMovShift? (e : Expr) : Option Nat :=
  match_expr e with
  | MovShift.LSL0 _  => some 0
  | MovShift.LSL16 _ => some 16
  | MovShift.LSL32   => some 32
  | MovShift.LSL48   => some 48
  | _                => none

private def evalCondCode? (e : Expr) : Option CondCode :=
  match_expr e with
  | CondCode.EQ => some .EQ | CondCode.NE => some .NE
  | CondCode.CS => some .CS | CondCode.HS => some .CS
  | CondCode.CC => some .CC | CondCode.LO => some .CC
  | CondCode.MI => some .MI | CondCode.PL => some .PL
  | CondCode.VS => some .VS | CondCode.VC => some .VC
  | CondCode.HI => some .HI | CondCode.LS => some .LS
  | CondCode.GE => some .GE | CondCode.LT => some .LT
  | CondCode.GT => some .GT | CondCode.LE => some .LE
  | CondCode.AL => some .AL | CondCode.NV => some .NV
  | _           => none

-- ============================================================================
-- Identifiers, Labels, Immediates, Constants & Condition Codes
-- ============================================================================

/-- Whether `s` is a concrete register token (`aarch64_reg`), which `aarch64_ident` excludes via
    `notFollowedBy(aarch64_reg)`. -/
private def isRegName : String → Bool
  | "sp" | "wsp" | "lr" | "xzr" | "wzr" => true
  | s => (s.startsWith "x" || s.startsWith "w") &&
    let idx := (s.drop 1).toString
    match idx.toNat? with
    | some n => n ≤ 30 && toString n == idx
    | none   => false

private def mkIdentStx (s : String) : TSyntax `aarch64_ident :=
  ⟨Syntax.node .none ``aarch64_ident__ #[Syntax.atom .none s]⟩

/-- Delaborate a `String` literal into an `aarch64_ident` if it is a valid assembly identifier other than
    a register name. -/
def delabIdent : DelabM (TSyntax `aarch64_ident) := do
  let .lit (.strVal s) ← getExpr | failure
  unless isAsmIdent s && !isRegName s do failure
  annotateStx (mkIdentStx s)

/-- Delaborate a `Label` (`String`) into an `aarch64_label`, falling back to `❰t❱` for open terms. -/
def delabLabel : DelabM (TSyntax `aarch64_label) := do
  try
    let id ← delabIdent
    annotateStx (← `(aarch64_label| $id:aarch64_ident))
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_label| ❰ $t ❱))

/-- Construct an `aarch64_imm` `#n` or `#-n` from a signed integer `i`. -/
private def mkImmInt (i : Int) : DelabM (TSyntax `aarch64_imm) := do
  if i ≥ 0 then
    let n := Syntax.mkNumLit (toString i.toNat)
    `(aarch64_imm| #$n:num)
  else
    let n := Syntax.mkNumLit (toString (-i).toNat)
    `(aarch64_imm| #-$n:num)

/-- Delaborate a `Nat` expression into an `aarch64_imm`, falling back to `#❰t❱` for open terms. -/
def delabImmNat : DelabM (TSyntax `aarch64_imm) := do
  if let some n := evalNat? (← getExpr) then
    annotateStx (← mkImmInt n)
  else
    let t ← delab
    annotateStx (← `(aarch64_imm| #❰ $t ❱))

/-- Delaborate an `Int64` expression into an `aarch64_imm`, falling back to `#❰t❱` for open terms. -/
def delabImm64 : DelabM (TSyntax `aarch64_imm) := do
  if let some i := evalInt64? (← getExpr) then
    annotateStx (← mkImmInt i)
  else
    let t ← delab
    annotateStx (← `(aarch64_imm| #❰ $t ❱))

/-- Delaborate a `ConstExpr.int64 v` into an `aarch64_imm` (`#v` or `#❰v❱`). -/
def delabImmConst : DelabM (TSyntax `aarch64_imm) := do
  match_expr ← getExpr with
  | ConstExpr.int64 _ => withAppArg delabImm64
  | _                 => failure

/-- Delaborate a `ConstExpr` into an `aarch64_const`, falling back to `❰t❱` for open or non-canonical terms. -/
def delabConstExpr : DelabM (TSyntax `aarch64_const) := do
  try
    let stx ← match_expr ← getExpr with
      | ConstExpr.int64 _ =>
        let imm ← withAppArg delabImm64
        `(aarch64_const| $imm:aarch64_imm)
      | ConstExpr.label _ =>
        try
          let id ← withAppArg delabIdent
          `(aarch64_const| $id:aarch64_ident)
        catch _ =>
          let t ← withAppArg delab
          `(aarch64_const| ❰ $t ❱)
      | ConstExpr.pg_hi21 inner =>
        unless inner.isAppOfArity ``ConstExpr.label 1 do failure
        let modId := mkIdentStx "pg_hi21"
        let lbl ← withAppArg (withAppArg delabLabel)
        `(aarch64_const| : $modId:aarch64_ident : $lbl:aarch64_label)
      | ConstExpr.lo12 inner =>
        unless inner.isAppOfArity ``ConstExpr.label 1 do failure
        let modId := mkIdentStx "lo12"
        let lbl ← withAppArg (withAppArg delabLabel)
        `(aarch64_const| : $modId:aarch64_ident : $lbl:aarch64_label)
      | _ => failure
    annotateStx stx
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_const| ❰ $t ❱))

private def condCodeSuffix : CondCode → String
  | .EQ => "eq" | .NE => "ne" | .CS => "cs" | .CC => "cc"
  | .MI => "mi" | .PL => "pl" | .VS => "vs" | .VC => "vc"
  | .HI => "hi" | .LS => "ls" | .GE => "ge" | .LT => "lt"
  | .GT => "gt" | .LE => "le" | .AL => "al" | .NV => "nv"

/-- Delaborate a `CondCode` into an `aarch64_cond`, falling back to `❰t❱` for open terms. -/
def delabCond : DelabM (TSyntax `aarch64_cond) := do
  if let some cc := evalCondCode? (← getExpr) then
    annotateStx (mkSuffixed `aarch64_cond "" (condCodeSuffix cc))
  else
    let t ← delab
    annotateStx (← `(aarch64_cond| ❰ $t ❱))

-- ============================================================================
-- Registers
-- ============================================================================

private def xregIndex : XReg → String
  | .X0  => "0"  | .X1  => "1"  | .X2  => "2"  | .X3  => "3"  | .X4  => "4"  | .X5  => "5"
  | .X6  => "6"  | .X7  => "7"  | .X8  => "8"  | .X9  => "9"  | .X10 => "10" | .X11 => "11"
  | .X12 => "12" | .X13 => "13" | .X14 => "14" | .X15 => "15" | .X16 => "16" | .X17 => "17"
  | .X18 => "18" | .X19 => "19" | .X20 => "20" | .X21 => "21" | .X22 => "22" | .X23 => "23"
  | .X24 => "24" | .X25 => "25" | .X26 => "26" | .X27 => "27" | .X28 => "28" | .X29 => "29"
  | .X30 => "30"

private def regWidthStem : RegWidth → String
  | .W32 => "w"
  | .W64 => "x"

private def evalRegOrSp? (e : Expr) : Option (RegWidth × XRegOrSp) :=
  match_expr e with
  | RegOrSp.low rExpr wExpr => do
    let r ← evalXRegOrSp? rExpr
    let w ← evalRegWidth? wExpr
    pure (w, r)
  | RegOrSp.X0  => some (.W64, .reg .X0)  | RegOrSp.X1  => some (.W64, .reg .X1)  | RegOrSp.X2  => some (.W64, .reg .X2)
  | RegOrSp.X3  => some (.W64, .reg .X3)  | RegOrSp.X4  => some (.W64, .reg .X4)  | RegOrSp.X5  => some (.W64, .reg .X5)
  | RegOrSp.X6  => some (.W64, .reg .X6)  | RegOrSp.X7  => some (.W64, .reg .X7)  | RegOrSp.X8  => some (.W64, .reg .X8)
  | RegOrSp.X9  => some (.W64, .reg .X9)  | RegOrSp.X10 => some (.W64, .reg .X10) | RegOrSp.X11 => some (.W64, .reg .X11)
  | RegOrSp.X12 => some (.W64, .reg .X12) | RegOrSp.X13 => some (.W64, .reg .X13) | RegOrSp.X14 => some (.W64, .reg .X14)
  | RegOrSp.X15 => some (.W64, .reg .X15) | RegOrSp.X16 => some (.W64, .reg .X16) | RegOrSp.X17 => some (.W64, .reg .X17)
  | RegOrSp.X18 => some (.W64, .reg .X18) | RegOrSp.X19 => some (.W64, .reg .X19) | RegOrSp.X20 => some (.W64, .reg .X20)
  | RegOrSp.X21 => some (.W64, .reg .X21) | RegOrSp.X22 => some (.W64, .reg .X22) | RegOrSp.X23 => some (.W64, .reg .X23)
  | RegOrSp.X24 => some (.W64, .reg .X24) | RegOrSp.X25 => some (.W64, .reg .X25) | RegOrSp.X26 => some (.W64, .reg .X26)
  | RegOrSp.X27 => some (.W64, .reg .X27) | RegOrSp.X28 => some (.W64, .reg .X28) | RegOrSp.X29 => some (.W64, .reg .X29)
  | RegOrSp.X30 => some (.W64, .reg .X30) | RegOrSp.SP  => some (.W64, .SP)
  | RegOrSp.W0  => some (.W32, .reg .X0)  | RegOrSp.W1  => some (.W32, .reg .X1)  | RegOrSp.W2  => some (.W32, .reg .X2)
  | RegOrSp.W3  => some (.W32, .reg .X3)  | RegOrSp.W4  => some (.W32, .reg .X4)  | RegOrSp.W5  => some (.W32, .reg .X5)
  | RegOrSp.W6  => some (.W32, .reg .X6)  | RegOrSp.W7  => some (.W32, .reg .X7)  | RegOrSp.W8  => some (.W32, .reg .X8)
  | RegOrSp.W9  => some (.W32, .reg .X9)  | RegOrSp.W10 => some (.W32, .reg .X10) | RegOrSp.W11 => some (.W32, .reg .X11)
  | RegOrSp.W12 => some (.W32, .reg .X12) | RegOrSp.W13 => some (.W32, .reg .X13) | RegOrSp.W14 => some (.W32, .reg .X14)
  | RegOrSp.W15 => some (.W32, .reg .X15) | RegOrSp.W16 => some (.W32, .reg .X16) | RegOrSp.W17 => some (.W32, .reg .X17)
  | RegOrSp.W18 => some (.W32, .reg .X18) | RegOrSp.W19 => some (.W32, .reg .X19) | RegOrSp.W20 => some (.W32, .reg .X20)
  | RegOrSp.W21 => some (.W32, .reg .X21) | RegOrSp.W22 => some (.W32, .reg .X22) | RegOrSp.W23 => some (.W32, .reg .X23)
  | RegOrSp.W24 => some (.W32, .reg .X24) | RegOrSp.W25 => some (.W32, .reg .X25) | RegOrSp.W26 => some (.W32, .reg .X26)
  | RegOrSp.W27 => some (.W32, .reg .X27) | RegOrSp.W28 => some (.W32, .reg .X28) | RegOrSp.W29 => some (.W32, .reg .X29)
  | RegOrSp.W30 => some (.W32, .reg .X30) | RegOrSp.WSP => some (.W32, .SP)
  | _           => none

private def evalRegOrZr? (e : Expr) : Option (RegWidth × XRegOrXzr) :=
  match_expr e with
  | RegOrZr.low rExpr wExpr => do
    let r ← evalXRegOrXzr? rExpr
    let w ← evalRegWidth? wExpr
    pure (w, r)
  | RegOrZr.X0  => some (.W64, .reg .X0)  | RegOrZr.X1  => some (.W64, .reg .X1)  | RegOrZr.X2  => some (.W64, .reg .X2)
  | RegOrZr.X3  => some (.W64, .reg .X3)  | RegOrZr.X4  => some (.W64, .reg .X4)  | RegOrZr.X5  => some (.W64, .reg .X5)
  | RegOrZr.X6  => some (.W64, .reg .X6)  | RegOrZr.X7  => some (.W64, .reg .X7)  | RegOrZr.X8  => some (.W64, .reg .X8)
  | RegOrZr.X9  => some (.W64, .reg .X9)  | RegOrZr.X10 => some (.W64, .reg .X10) | RegOrZr.X11 => some (.W64, .reg .X11)
  | RegOrZr.X12 => some (.W64, .reg .X12) | RegOrZr.X13 => some (.W64, .reg .X13) | RegOrZr.X14 => some (.W64, .reg .X14)
  | RegOrZr.X15 => some (.W64, .reg .X15) | RegOrZr.X16 => some (.W64, .reg .X16) | RegOrZr.X17 => some (.W64, .reg .X17)
  | RegOrZr.X18 => some (.W64, .reg .X18) | RegOrZr.X19 => some (.W64, .reg .X19) | RegOrZr.X20 => some (.W64, .reg .X20)
  | RegOrZr.X21 => some (.W64, .reg .X21) | RegOrZr.X22 => some (.W64, .reg .X22) | RegOrZr.X23 => some (.W64, .reg .X23)
  | RegOrZr.X24 => some (.W64, .reg .X24) | RegOrZr.X25 => some (.W64, .reg .X25) | RegOrZr.X26 => some (.W64, .reg .X26)
  | RegOrZr.X27 => some (.W64, .reg .X27) | RegOrZr.X28 => some (.W64, .reg .X28) | RegOrZr.X29 => some (.W64, .reg .X29)
  | RegOrZr.X30 => some (.W64, .reg .X30) | RegOrZr.XZR => some (.W64, .XZR)
  | RegOrZr.W0  => some (.W32, .reg .X0)  | RegOrZr.W1  => some (.W32, .reg .X1)  | RegOrZr.W2  => some (.W32, .reg .X2)
  | RegOrZr.W3  => some (.W32, .reg .X3)  | RegOrZr.W4  => some (.W32, .reg .X4)  | RegOrZr.W5  => some (.W32, .reg .X5)
  | RegOrZr.W6  => some (.W32, .reg .X6)  | RegOrZr.W7  => some (.W32, .reg .X7)  | RegOrZr.W8  => some (.W32, .reg .X8)
  | RegOrZr.W9  => some (.W32, .reg .X9)  | RegOrZr.W10 => some (.W32, .reg .X10) | RegOrZr.W11 => some (.W32, .reg .X11)
  | RegOrZr.W12 => some (.W32, .reg .X12) | RegOrZr.W13 => some (.W32, .reg .X13) | RegOrZr.W14 => some (.W32, .reg .X14)
  | RegOrZr.W15 => some (.W32, .reg .X15) | RegOrZr.W16 => some (.W32, .reg .X16) | RegOrZr.W17 => some (.W32, .reg .X17)
  | RegOrZr.W18 => some (.W32, .reg .X18) | RegOrZr.W19 => some (.W32, .reg .X19) | RegOrZr.W20 => some (.W32, .reg .X20)
  | RegOrZr.W21 => some (.W32, .reg .X21) | RegOrZr.W22 => some (.W32, .reg .X22) | RegOrZr.W23 => some (.W32, .reg .X23)
  | RegOrZr.W24 => some (.W32, .reg .X24) | RegOrZr.W25 => some (.W32, .reg .X25) | RegOrZr.W26 => some (.W32, .reg .X26)
  | RegOrZr.W27 => some (.W32, .reg .X27) | RegOrZr.W28 => some (.W32, .reg .X28) | RegOrZr.W29 => some (.W32, .reg .X29)
  | RegOrZr.W30 => some (.W32, .reg .X30) | RegOrZr.WZR => some (.W32, .XZR)
  | _           => none

/-- Delaborate a `RegOrSp w` expression into an `aarch64_reg`, falling back to `❰t❱` for open terms. -/
def delabRegOrSp : DelabM (TSyntax `aarch64_reg) := do
  if let some (w, r) := evalRegOrSp? (← getExpr) then
    let stx ← match w, r with
      | _,    .reg xr => pure (mkSuffixed `aarch64_reg (regWidthStem w) (xregIndex xr))
      | .W64, .SP     => `(aarch64_reg| sp)
      | .W32, .SP     => `(aarch64_reg| wsp)
    annotateStx stx
  else
    let t ← delab
    annotateStx (← `(aarch64_reg| ❰ $t ❱))

/-- Delaborate a `RegOrZr w` expression into an `aarch64_reg`, falling back to `❰t❱` for open terms. -/
def delabRegOrZr : DelabM (TSyntax `aarch64_reg) := do
  if let some (w, r) := evalRegOrZr? (← getExpr) then
    let stx := match r with
      | .reg xr => mkSuffixed `aarch64_reg (regWidthStem w) (xregIndex xr)
      | .XZR    => mkSuffixed `aarch64_reg (regWidthStem w) "zr"
    annotateStx stx
  else
    let t ← delab
    annotateStx (← `(aarch64_reg| ❰ $t ❱))

/-- Delaborate a `RegOrZrW` structure into its `RegWidth` and `aarch64_reg`. -/
def delabRegOrZrW : DelabM (RegWidth × TSyntax `aarch64_reg) := do
  match_expr ← getExpr with
  | RegOrZrW.mk wExpr _ =>
    let some w := evalRegWidth? wExpr | failure
    let r ← withAppArg delabRegOrZr
    return (w, r)
  | _ => failure

-- ============================================================================
-- Modifiers, Flexible Sources & Memory Operands
-- ============================================================================

private def shiftTypeSuffix : ShiftType → String
  | .LSL => "lsl" | .LSR => "lsr" | .ASR => "asr" | .ROR => "ror"

private def extendTypeAffixes : ExtendType → String × String
  | .UXTB => ("u", "b") | .SXTB => ("s", "b")
  | .UXTH => ("u", "h") | .SXTH => ("s", "h")
  | .UXTW => ("u", "w") | .SXTW => ("s", "w")
  | .UXTX => ("u", "x") | .SXTX => ("s", "x")

private def mkModifier (pre stem sfx : String) (amt : TSyntax `aarch64_imm) : DelabM (TSyntax `aarch64_modifier) := do
  let kind := mkAffixed `aarch64_modifier_kind pre stem sfx
  annotateStx (← `(aarch64_modifier| $kind:aarch64_modifier_kind $amt:aarch64_imm))

/-- Delaborate an `ExtOrImmReg` into an `aarch64_src`. -/
def delabExtOrImm : DelabM (TSyntax `aarch64_src) := do
  let stx ← match_expr ← getExpr with
    | ExtOrImmReg.imm immExpr =>
      match_expr immExpr with
      | ImmExpr.mk _ shiftExpr =>
        match evalImmShift? shiftExpr with
        | some .S0 =>
          let c ← withAppArg (withNaryArg 0 delabConstExpr)
          `(aarch64_src| $c:aarch64_const)
        | some .S12 =>
          let imm ← withAppArg (withNaryArg 0 delabImmConst)
          let c ← `(aarch64_const| $imm:aarch64_imm)
          let mod ← mkModifier "" "" "lsl" (← mkImmInt 12)
          `(aarch64_src| $c:aarch64_const, $mod:aarch64_modifier)
        | none => failure
      | _ => failure
    | ExtOrImmReg.ext extRegExpr =>
      match_expr extRegExpr with
      | ExtRegExpr.mk _ extExpr =>
        match_expr extExpr with
        | Extend.mk typeExpr amtExpr =>
          let (_, rm) ← withAppArg (withNaryArg 0 delabRegOrZrW)
          let some ty := evalExtendType? typeExpr | failure
          let some amt := evalExtendAmount? amtExpr | failure
          let (pre, sfx) := extendTypeAffixes ty
          let mod ← mkModifier pre "xt" sfx (← mkImmInt amt)
          `(aarch64_src| $rm:aarch64_reg, $mod:aarch64_modifier)
        | _ => failure
      | _ => failure
    | _ => failure
  annotateStx stx

/-- Delaborate a `ShiftRegExpr w` into an `aarch64_src`. -/
def delabShiftReg : DelabM (TSyntax `aarch64_src) := do
  match_expr ← getExpr with
  | ShiftRegExpr.mk _ _ amtExpr shiftExpr =>
    let rm ← withNaryArg 1 delabRegOrZr
    let some sh := evalShiftType? shiftExpr | failure
    if sh == .LSL && evalInt64? amtExpr == some 0 then
      annotateStx (← `(aarch64_src| $rm:aarch64_reg))
    else
      let amt ← withNaryArg 2 delabImm64
      let mod ← mkModifier "" "" (shiftTypeSuffix sh) amt
      annotateStx (← `(aarch64_src| $rm:aarch64_reg, $mod:aarch64_modifier))
  | _ => failure

private def evalConstInt64? (e : Expr) : Option Int :=
  match_expr e with
  | ConstExpr.int64 iExpr => evalInt64? iExpr
  | _                     => none

private def isZeroConst (e : Expr) : Bool :=
  evalConstInt64? e == some 0

/-- Delaborate an `AddrExpr` of a single-register scaled load/store with access size `scale?` into an
    `aarch64_mem`, falling back to `❰t❱` for open terms. -/
def delabScaledAddr (scale? : Option Nat) : DelabM (TSyntax `aarch64_mem) := do
  try
    let stx ← match_expr ← getExpr with
      | AddrExpr.mk _ offExpr =>
        let base ← withNaryArg 0 delabRegOrSp
        match_expr offExpr with
        | AddrOff.imm immAddrExpr =>
          match_expr immAddrExpr with
          | ImmAddrExpr.mk immExpr idxOpt =>
            match_expr idxOpt with
            | Option.none _ =>
              if isZeroConst immExpr then
                `(aarch64_mem| [$base:aarch64_reg])
              else
                -- A concrete integer offset requires a known access scale and must be non-negative and
                -- aligned to `scale`, otherwise `elabMemAccess` would select the unscaled `LDUR`/`STUR` form.
                if let some v := evalConstInt64? immExpr then
                  let some scale := scale? | failure
                  unless v ≥ 0 && v % scale == 0 do failure
                let off ← withNaryArg 1 (withAppArg (withNaryArg 0 delabConstExpr))
                `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const])
            | Option.some _ idxExpr =>
              let imm ← withNaryArg 1 (withAppArg (withNaryArg 0 delabImmConst))
              let off ← `(aarch64_const| $imm:aarch64_imm)
              match_expr idxExpr with
              | Index.Pre  => `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const]!)
              | Index.Post => `(aarch64_mem| [$base:aarch64_reg], $off:aarch64_const)
              | _          => failure
            | _ => failure
          | _ => failure
        | AddrOff.reg memExtExpr =>
          match_expr memExtExpr with
          | MemExtRegExpr.mk _ extExpr =>
            match_expr extExpr with
            | MemExtend.mk typeExpr amtExpr =>
              let (regW, rm) ← withNaryArg 1 (withAppArg (withNaryArg 0 delabRegOrZrW))
              let some ty := evalMemExtendType? typeExpr | failure
              let some amt := evalMemExtendAmount? amtExpr | failure
              if scale?.isNone then
                unless amt == 0 && ((regW == .W64 && ty == .UXTX) || (regW == .W32 && ty == .UXTW)) do failure
                `(aarch64_mem| [$base:aarch64_reg, $rm:aarch64_reg])
              else
                let mod ← match regW, ty with
                  | .W64, .UXTX => mkModifier "" "" "lsl" (← mkImmInt amt)
                  | _,    .UXTW => mkModifier "u" "xt" "w" (← mkImmInt amt)
                  | _,    .SXTW => mkModifier "s" "xt" "w" (← mkImmInt amt)
                  | _,    .UXTX => mkModifier "u" "xt" "x" (← mkImmInt amt)
                  | _,    .SXTX => mkModifier "s" "xt" "x" (← mkImmInt amt)
                `(aarch64_mem| [$base:aarch64_reg, $rm:aarch64_reg, $mod:aarch64_modifier])
            | _ => failure
          | _ => failure
        | _ => failure
      | _ => failure
    annotateStx stx
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_mem| ❰ $t ❱))

/-- Delaborate an `AddrExpr` of a register-pair load/store (`ldp`, `ldpsw`, `stp`) into an `aarch64_mem`,
    falling back to `❰t❱` for open terms. -/
def delabPairAddr : DelabM (TSyntax `aarch64_mem) := do
  try
    let stx ← match_expr ← getExpr with
      | AddrExpr.mk _ offExpr =>
        let base ← withNaryArg 0 delabRegOrSp
        match_expr offExpr with
        | AddrOff.imm immAddrExpr =>
          match_expr immAddrExpr with
          | ImmAddrExpr.mk immExpr idxOpt =>
            match_expr idxOpt with
            | Option.none _ =>
              if isZeroConst immExpr then
                `(aarch64_mem| [$base:aarch64_reg])
              else
                let imm ← withNaryArg 1 (withAppArg (withNaryArg 0 delabImmConst))
                let off ← `(aarch64_const| $imm:aarch64_imm)
                `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const])
            | Option.some _ idxExpr =>
              let imm ← withNaryArg 1 (withAppArg (withNaryArg 0 delabImmConst))
              let off ← `(aarch64_const| $imm:aarch64_imm)
              match_expr idxExpr with
              | Index.Pre  => `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const]!)
              | Index.Post => `(aarch64_mem| [$base:aarch64_reg], $off:aarch64_const)
              | _          => failure
            | _ => failure
          | _ => failure
        | _ => failure
      | _ => failure
    annotateStx stx
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_mem| ❰ $t ❱))

/-- Delaborate an `UnscaledAddrExpr` into an `aarch64_mem`, falling back to `❰t❱` for open terms. -/
def delabUnscaledAddr : DelabM (TSyntax `aarch64_mem) := do
  try
    let stx ← match_expr ← getExpr with
      | UnscaledAddrExpr.mk _ immExpr =>
        let base ← withNaryArg 0 delabRegOrSp
        if isZeroConst immExpr then
          `(aarch64_mem| [$base:aarch64_reg])
        else
          let off ← withNaryArg 1 delabConstExpr
          `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const])
      | _ => failure
    annotateStx stx
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_mem| ❰ $t ❱))

/-- Delaborate an `AddrOrLit` into an `aarch64_load_src`. -/
def delabAddrOrLit (scale? : Option Nat) : DelabM (TSyntax `aarch64_load_src) := do
  match_expr ← getExpr with
  | AddrOrLit.addr _ =>
    let m ← withAppArg (delabScaledAddr scale?)
    annotateStx (← `(aarch64_load_src| $m:aarch64_mem))
  | AddrOrLit.lit litExpr =>
    let lit ← match_expr litExpr with
      | Literal.addr addrLitExpr =>
        match_expr addrLitExpr with
        | LitAddrExpr.mk _ =>
          let id ← withAppArg (withAppArg (withAppArg delabIdent))
          annotateStx (← `(aarch64_lit| $id:aarch64_ident))
        | _ => failure
      | Literal.pool poolLitExpr =>
        match_expr poolLitExpr with
        | LitPoolExpr.mk _ =>
          let c ← withAppArg (withAppArg (withAppArg delabConstExpr))
          annotateStx (← `(aarch64_lit| =$c:aarch64_const))
        | _ => failure
      | _ => failure
    annotateStx (← `(aarch64_load_src| $lit:aarch64_lit))
  | _ => failure

-- ============================================================================
-- Instruction Delaboration
-- ============================================================================

private def delabScaledLdr (sfx : String) (rtIdx addrIdx : Nat) (scale? : Option Nat) :
    DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_ldr_op "ldr" sfx
  let rt ← withNaryArg rtIdx delabRegOrZr
  let m ← withNaryArg addrIdx (delabScaledAddr scale?)
  let src ← `(aarch64_load_src| $m:aarch64_mem)
  `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $src:aarch64_load_src)

private def delabUnscaledLdr (sfx : String) (rtIdx addrIdx : Nat) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_ldur_op "ldur" sfx
  let rt ← withNaryArg rtIdx delabRegOrZr
  let m ← withNaryArg addrIdx delabUnscaledAddr
  `(aarch64_instr| $op:aarch64_ldur_op $rt:aarch64_reg, $m:aarch64_mem)

private def delabScaledStr (sfx : String) (rtIdx addrIdx : Nat) (scale? : Option Nat) :
    DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_str_op "str" sfx
  let rt ← withNaryArg rtIdx delabRegOrZr
  let m ← withNaryArg addrIdx (delabScaledAddr scale?)
  `(aarch64_instr| $op:aarch64_str_op $rt:aarch64_reg, $m:aarch64_mem)

private def delabUnscaledStr (sfx : String) (rtIdx addrIdx : Nat) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_stur_op "stur" sfx
  let rt ← withNaryArg rtIdx delabRegOrZr
  let m ← withNaryArg addrIdx delabUnscaledAddr
  `(aarch64_instr| $op:aarch64_stur_op $rt:aarch64_reg, $m:aarch64_mem)

private def delabArithExt (stem sfx : String) (rdSp : Bool) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_arith_op stem sfx
  let rd ← withNaryArg 1 (if rdSp then delabRegOrSp else delabRegOrZr)
  let rn ← withNaryArg 2 delabRegOrSp
  let src ← withNaryArg 3 delabExtOrImm
  `(aarch64_instr| $op:aarch64_arith_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src)

private def delabArithShift (stem sfx : String) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_arith_op stem sfx
  let rd ← withNaryArg 1 delabRegOrZr
  let rn ← withNaryArg 2 delabRegOrZr
  let src ← withNaryArg 3 delabShiftReg
  `(aarch64_instr| $op:aarch64_arith_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src)

private def delabRrr (op : TSyntax `aarch64_rrr_op) (rdIdx : Nat := 1) : DelabM (TSyntax `aarch64_instr) := do
  let rd ← withNaryArg rdIdx delabRegOrZr
  let rn ← withNaryArg (rdIdx + 1) delabRegOrZr
  let rm ← withNaryArg (rdIdx + 2) delabRegOrZr
  `(aarch64_instr| $op:aarch64_rrr_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg)

private def delabMaddl (pre stem : String) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkAffixed `aarch64_maddl_op pre stem ""
  let rd ← withNaryArg 0 delabRegOrZr
  let rn ← withNaryArg 1 delabRegOrZr
  let rm ← withNaryArg 2 delabRegOrZr
  let ra ← withNaryArg 3 delabRegOrZr
  `(aarch64_instr| $op:aarch64_maddl_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg)

private def delabLogicImm (op : TSyntax `aarch64_logic_op) (rdSp : Bool) : DelabM (TSyntax `aarch64_instr) := do
  let rd ← withNaryArg 1 (if rdSp then delabRegOrSp else delabRegOrZr)
  let rn ← withNaryArg 2 delabRegOrZr
  let c ← withNaryArg 3 delabConstExpr
  let src ← `(aarch64_src| $c:aarch64_const)
  `(aarch64_instr| $op:aarch64_logic_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src)

private def delabLogicShift (op : TSyntax `aarch64_logic_op) : DelabM (TSyntax `aarch64_instr) := do
  let rd ← withNaryArg 1 delabRegOrZr
  let rn ← withNaryArg 2 delabRegOrZr
  let src ← withNaryArg 3 delabShiftReg
  `(aarch64_instr| $op:aarch64_logic_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src)

private def delabBitfield (pre : String) : DelabM (TSyntax `aarch64_instr) := do
  let op := mkAffixed `aarch64_bitfield_op pre "bfm" ""
  let rd ← withNaryArg 1 delabRegOrZr
  let rn ← withNaryArg 2 delabRegOrZr
  let immr ← withNaryArg 3 delabImmNat
  let imms ← withNaryArg 4 delabImmNat
  `(aarch64_instr| $op:aarch64_bitfield_op $rd:aarch64_reg, $rn:aarch64_reg, $immr:aarch64_imm, $imms:aarch64_imm)

private def delabRr (op : TSyntax `aarch64_rr_op) (rdIdx : Nat := 1) : DelabM (TSyntax `aarch64_instr) := do
  let rd ← withNaryArg rdIdx delabRegOrZr
  let rn ← withNaryArg (rdIdx + 1) delabRegOrZr
  `(aarch64_instr| $op:aarch64_rr_op $rd:aarch64_reg, $rn:aarch64_reg)

private def delabMovw (sfx : String) (w? : Option RegWidth) (shiftExpr : Expr) :
    DelabM (TSyntax `aarch64_instr) := do
  let op := mkSuffixed `aarch64_movw_op "mov" sfx
  let rd ← withNaryArg 1 delabRegOrZr
  let imm ← withNaryArg 2 delabConstExpr
  let some sh := evalMovShift? shiftExpr | failure
  if w?.isNone && sh == 0 then
    `(aarch64_instr| $op:aarch64_movw_op $rd:aarch64_reg, $imm:aarch64_const)
  else
    unless w?.isSome do failure
    let mod ← mkModifier "" "" "lsl" (← mkImmInt sh)
    `(aarch64_instr| $op:aarch64_movw_op $rd:aarch64_reg, $imm:aarch64_const, $mod:aarch64_modifier)

private def delabCsel (op : TSyntax `aarch64_csel_op) : DelabM (TSyntax `aarch64_instr) := do
  let rd ← withNaryArg 1 delabRegOrZr
  let rn ← withNaryArg 2 delabRegOrZr
  let rm ← withNaryArg 3 delabRegOrZr
  let cc ← withNaryArg 4 delabCond
  `(aarch64_instr| $op:aarch64_csel_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $cc:aarch64_cond)

private def delabCcmp (op : TSyntax `aarch64_ccmp_op) (isImm : Bool) : DelabM (TSyntax `aarch64_instr) := do
  let rn ← withNaryArg 1 delabRegOrZr
  let src2 ← withNaryArg 2 do
    if isImm then
      let i ← delabImmNat
      `(aarch64_reg_or_imm| $i:aarch64_imm)
    else
      let r ← delabRegOrZr
      `(aarch64_reg_or_imm| $r:aarch64_reg)
  let nzcv ← withNaryArg 3 delabImmNat
  let cc ← withNaryArg 4 delabCond
  `(aarch64_instr| $op:aarch64_ccmp_op $rn:aarch64_reg, $src2:aarch64_reg_or_imm, $nzcv:aarch64_imm, $cc:aarch64_cond)

/-- Delaborate a load/store `Operation` constructor into an `aarch64_instr`. -/
private def delabLoadStoreOp (w? : Option RegWidth) : DelabM (TSyntax `aarch64_instr) := do
  match_expr ← getExpr with
  | Operation.LDR _ _ _ =>
    let op := mkSuffixed `aarch64_ldr_op "ldr" ""
    let rt ← withNaryArg 1 delabRegOrZr
    let src ← withNaryArg 2 (delabAddrOrLit (w?.map (·.bytes)))
    `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $src:aarch64_load_src)
  | Operation.STR _ _ _    => delabScaledStr "" 1 2 (w?.map (·.bytes))
  | Operation.LDUR _ _ _   => delabUnscaledLdr "" 1 2
  | Operation.STUR _ _ _   => delabUnscaledStr "" 1 2
  | Operation.LDP _ _ _ _  =>
    let rt1 ← withNaryArg 1 delabRegOrZr
    let rt2 ← withNaryArg 2 delabRegOrZr
    let m ← withNaryArg 3 delabPairAddr
    `(aarch64_instr| ldp $rt1:aarch64_reg, $rt2:aarch64_reg, $m:aarch64_mem)
  | Operation.STP _ _ _ _  =>
    let rt1 ← withNaryArg 1 delabRegOrZr
    let rt2 ← withNaryArg 2 delabRegOrZr
    let m ← withNaryArg 3 delabPairAddr
    `(aarch64_instr| stp $rt1:aarch64_reg, $rt2:aarch64_reg, $m:aarch64_mem)
  | Operation.LDRB _ _     => delabScaledLdr "b" 0 1 (some 1)
  | Operation.LDURB _ _    => delabUnscaledLdr "b" 0 1
  | Operation.STRB _ _     => delabScaledStr "b" 0 1 (some 1)
  | Operation.STURB _ _    => delabUnscaledStr "b" 0 1
  | Operation.LDRSB _ _ _  => delabScaledLdr "sb" 1 2 (w?.map fun _ => 1)
  | Operation.LDURSB _ _ _ => delabUnscaledLdr "sb" 1 2
  | Operation.LDRH _ _     => delabScaledLdr "h" 0 1 (some 2)
  | Operation.LDURH _ _    => delabUnscaledLdr "h" 0 1
  | Operation.STRH _ _     => delabScaledStr "h" 0 1 (some 2)
  | Operation.STURH _ _    => delabUnscaledStr "h" 0 1
  | Operation.LDRSH _ _ _  => delabScaledLdr "sh" 1 2 (w?.map fun _ => 2)
  | Operation.LDURSH _ _ _ => delabUnscaledLdr "sh" 1 2
  | Operation.LDRSW _ _    =>
    let op := mkSuffixed `aarch64_ldr_op "ldr" "sw"
    let rt ← withNaryArg 0 delabRegOrZr
    let src ← withNaryArg 1 (delabAddrOrLit (some 4))
    `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $src:aarch64_load_src)
  | Operation.LDURSW _ _   => delabUnscaledLdr "sw" 0 1
  | Operation.LDPSW _ _ _  =>
    let rt1 ← withNaryArg 0 delabRegOrZr
    let rt2 ← withNaryArg 1 delabRegOrZr
    let m ← withNaryArg 2 delabPairAddr
    `(aarch64_instr| ldpsw $rt1:aarch64_reg, $rt2:aarch64_reg, $m:aarch64_mem)
  | _ => failure

/-- Delaborate an arithmetic, multiply, division or variable-shift `Operation` constructor. -/
private def delabArithMulOp : DelabM (TSyntax `aarch64_instr) := do
  match_expr ← getExpr with
  -- Arithmetic
  | Operation.ADD_e _ _ _ _  => delabArithExt "add" "" (rdSp := true)
  | Operation.ADD_s _ _ _ _  => delabArithShift "add" ""
  | Operation.ADDS_e _ _ _ _ => delabArithExt "add" "s" (rdSp := false)
  | Operation.ADDS_s _ _ _ _ => delabArithShift "add" "s"
  | Operation.SUB_e _ _ _ _  => delabArithExt "sub" "" (rdSp := true)
  | Operation.SUB_s _ _ _ _  => delabArithShift "sub" ""
  | Operation.SUBS_e _ _ _ _ => delabArithExt "sub" "s" (rdSp := false)
  | Operation.SUBS_s _ _ _ _ => delabArithShift "sub" "s"
  -- Carry arithmetic, division, multiply & variable shifts
  | Operation.ADC _ _ _ _  => delabRrr (mkSuffixed `aarch64_rrr_op "adc" "")
  | Operation.ADCS _ _ _ _ => delabRrr (mkSuffixed `aarch64_rrr_op "adc" "s")
  | Operation.SBC _ _ _ _  => delabRrr (mkSuffixed `aarch64_rrr_op "sbc" "")
  | Operation.SBCS _ _ _ _ => delabRrr (mkSuffixed `aarch64_rrr_op "sbc" "s")
  | Operation.SDIV _ _ _ _ => delabRrr (mkAffixed `aarch64_rrr_op "s" "div" "")
  | Operation.UDIV _ _ _ _ => delabRrr (mkAffixed `aarch64_rrr_op "u" "div" "")
  | Operation.SMULH _ _ _  => delabRrr (mkAffixed `aarch64_rrr_op "s" "mulh" "") (rdIdx := 0)
  | Operation.UMULH _ _ _  => delabRrr (mkAffixed `aarch64_rrr_op "u" "mulh" "") (rdIdx := 0)
  | Operation.LSLV _ _ _ _ => delabRrr (← `(aarch64_rrr_op| lslv))
  | Operation.LSRV _ _ _ _ => delabRrr (← `(aarch64_rrr_op| lsrv))
  | Operation.ASRV _ _ _ _ => delabRrr (← `(aarch64_rrr_op| asrv))
  | Operation.RORV _ _ _ _ => delabRrr (← `(aarch64_rrr_op| rorv))
  | Operation.MADD _ _ _ _ _ =>
    let rd ← withNaryArg 1 delabRegOrZr
    let rn ← withNaryArg 2 delabRegOrZr
    let rm ← withNaryArg 3 delabRegOrZr
    let ra ← withNaryArg 4 delabRegOrZr
    `(aarch64_instr| madd $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg)
  | Operation.MSUB _ _ _ _ _ =>
    let rd ← withNaryArg 1 delabRegOrZr
    let rn ← withNaryArg 2 delabRegOrZr
    let rm ← withNaryArg 3 delabRegOrZr
    let ra ← withNaryArg 4 delabRegOrZr
    `(aarch64_instr| msub $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg)
  | Operation.SMADDL _ _ _ _ => delabMaddl "s" "maddl"
  | Operation.UMADDL _ _ _ _ => delabMaddl "u" "maddl"
  | Operation.SMSUBL _ _ _ _ => delabMaddl "s" "msubl"
  | Operation.UMSUBL _ _ _ _ => delabMaddl "u" "msubl"
  | _ => failure

/-- Delaborate a logical, bitfield, bit-manipulation or move-wide `Operation` constructor. -/
private def delabLogicBitOp (w? : Option RegWidth) : DelabM (TSyntax `aarch64_instr) := do
  match_expr ← getExpr with
  -- Logical
  | Operation.AND_i _ _ _ _  => delabLogicImm (mkSuffixed `aarch64_logic_op "and" "") (rdSp := true)
  | Operation.AND_s _ _ _ _  => delabLogicShift (mkSuffixed `aarch64_logic_op "and" "")
  | Operation.ANDS_i _ _ _ _ => delabLogicImm (mkSuffixed `aarch64_logic_op "and" "s") (rdSp := false)
  | Operation.ANDS_s _ _ _ _ => delabLogicShift (mkSuffixed `aarch64_logic_op "and" "s")
  | Operation.ORR_i _ _ _ _  => delabLogicImm (← `(aarch64_logic_op| orr)) (rdSp := true)
  | Operation.ORR_s _ _ _ _  => delabLogicShift (← `(aarch64_logic_op| orr))
  | Operation.ORN_s _ _ _ _  => delabLogicShift (← `(aarch64_logic_op| orn))
  | Operation.EOR_i _ _ _ _  => delabLogicImm (← `(aarch64_logic_op| eor)) (rdSp := true)
  | Operation.EOR_s _ _ _ _  => delabLogicShift (← `(aarch64_logic_op| eor))
  | Operation.EON_s _ _ _ _  => delabLogicShift (← `(aarch64_logic_op| eon))
  | Operation.BIC_s _ _ _ _  => delabLogicShift (mkSuffixed `aarch64_logic_op "bic" "")
  | Operation.BICS_s _ _ _ _ => delabLogicShift (mkSuffixed `aarch64_logic_op "bic" "s")
  -- Bitfield & bit manipulation
  | Operation.BFM _ _ _ _ _  => delabBitfield ""
  | Operation.SBFM _ _ _ _ _ => delabBitfield "s"
  | Operation.UBFM _ _ _ _ _ => delabBitfield "u"
  | Operation.CLZ _ _ _      => delabRr (← `(aarch64_rr_op| clz))
  | Operation.CLS _ _ _      => delabRr (← `(aarch64_rr_op| cls))
  | Operation.RBIT _ _ _     => delabRr (← `(aarch64_rr_op| rbit))
  | Operation.REV _ _ _      => delabRr (mkSuffixed `aarch64_rr_op "rev" "")
  | Operation.REV16 _ _ _    => delabRr (mkSuffixed `aarch64_rr_op "rev" "16")
  | Operation.REV32 _ _      => delabRr (mkSuffixed `aarch64_rr_op "rev" "32") (rdIdx := 0)
  | Operation.EXTR _ _ _ _ _ =>
    let rd ← withNaryArg 1 delabRegOrZr
    let rn ← withNaryArg 2 delabRegOrZr
    let rm ← withNaryArg 3 delabRegOrZr
    let lsb ← withNaryArg 4 delabImmNat
    `(aarch64_instr| extr $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $lsb:aarch64_imm)
  -- Move wide
  | Operation.MOVZ _ _ _ shiftExpr => delabMovw "z" w? shiftExpr
  | Operation.MOVK _ _ _ shiftExpr => delabMovw "k" w? shiftExpr
  | Operation.MOVN _ _ _ shiftExpr => delabMovw "n" w? shiftExpr
  | _ => failure

/-- Delaborate a conditional, addressing, branch or `nop` `Operation` constructor. -/
private def delabCondBranchOp (w? : Option RegWidth) : DelabM (TSyntax `aarch64_instr) := do
  match_expr ← getExpr with
  -- Conditional select & compare
  | Operation.CSEL _ _ _ _ _     => delabCsel (← `(aarch64_csel_op| csel))
  | Operation.CSINC _ _ _ _ _    => delabCsel (← `(aarch64_csel_op| csinc))
  | Operation.CSINV _ _ _ _ _    => delabCsel (← `(aarch64_csel_op| csinv))
  | Operation.CSNEG _ _ _ _ _    => delabCsel (← `(aarch64_csel_op| csneg))
  | Operation.CCMP_reg _ _ _ _ _ => delabCcmp (← `(aarch64_ccmp_op| ccmp)) (isImm := false)
  | Operation.CCMP_imm _ _ _ _ _ => delabCcmp (← `(aarch64_ccmp_op| ccmp)) (isImm := true)
  | Operation.CCMN_reg _ _ _ _ _ => delabCcmp (← `(aarch64_ccmp_op| ccmn)) (isImm := false)
  | Operation.CCMN_imm _ _ _ _ _ => delabCcmp (← `(aarch64_ccmp_op| ccmn)) (isImm := true)
  -- Addressing & control flow
  | Operation.ADR _ _ =>
    let rd ← withNaryArg 0 delabRegOrZr
    let target ← withNaryArg 1 delabConstExpr
    `(aarch64_instr| adr $rd:aarch64_reg, $target:aarch64_const)
  | Operation.ADRP _ _ =>
    let rd ← withNaryArg 0 delabRegOrZr
    let target ← withNaryArg 1 delabConstExpr
    `(aarch64_instr| adrp $rd:aarch64_reg, $target:aarch64_const)
  | Operation.B _ =>
    let target ← withNaryArg 0 delabConstExpr
    `(aarch64_instr| b $target:aarch64_const)
  | Operation.BL _ =>
    let target ← withNaryArg 0 delabConstExpr
    `(aarch64_instr| bl $target:aarch64_const)
  | Operation.B_cond ccExpr _ =>
    let some cc := evalCondCode? ccExpr | failure
    let op := mkSuffixed `aarch64_bcond_op "b." (condCodeSuffix cc)
    let target ← withNaryArg 1 delabConstExpr
    `(aarch64_instr| $op:aarch64_bcond_op $target:aarch64_const)
  | Operation.BR _ =>
    let rn ← withNaryArg 0 delabRegOrZr
    `(aarch64_instr| br $rn:aarch64_reg)
  | Operation.BLR _ =>
    let rn ← withNaryArg 0 delabRegOrZr
    `(aarch64_instr| blr $rn:aarch64_reg)
  | Operation.RET rnExpr =>
    if evalRegOrZr? rnExpr == some (.W64, .reg .X30) then
      `(aarch64_instr| ret)
    else
      let rn ← withNaryArg 0 delabRegOrZr
      `(aarch64_instr| ret $rn:aarch64_reg)
  | Operation.CBZ _ _ _ =>
    let op := mkSuffixed `aarch64_cbz_op "cb" "z"
    let rt ← withNaryArg 1 delabRegOrZr
    let target ← withNaryArg 2 delabConstExpr
    `(aarch64_instr| $op:aarch64_cbz_op $rt:aarch64_reg, $target:aarch64_const)
  | Operation.CBNZ _ _ _ =>
    let op := mkSuffixed `aarch64_cbz_op "cb" "nz"
    let rt ← withNaryArg 1 delabRegOrZr
    let target ← withNaryArg 2 delabConstExpr
    `(aarch64_instr| $op:aarch64_cbz_op $rt:aarch64_reg, $target:aarch64_const)
  | Operation.TBZ _ _ _ _ =>
    let op := mkSuffixed `aarch64_tbz_op "tb" "z"
    let rt ← withNaryArg 1 delabRegOrZr
    let bit ← withNaryArg 2 delabImmNat
    let target ← withNaryArg 3 delabConstExpr
    `(aarch64_instr| $op:aarch64_tbz_op $rt:aarch64_reg, $bit:aarch64_imm, $target:aarch64_const)
  | Operation.TBNZ _ _ _ _ =>
    let op := mkSuffixed `aarch64_tbz_op "tb" "nz"
    let rt ← withNaryArg 1 delabRegOrZr
    let bit ← withNaryArg 2 delabImmNat
    let target ← withNaryArg 3 delabConstExpr
    `(aarch64_instr| $op:aarch64_tbz_op $rt:aarch64_reg, $bit:aarch64_imm, $target:aarch64_const)
  | Operation.NOP _ =>
    unless w? == some .W64 do failure
    `(aarch64_instr| nop)
  | _ => failure

/-- Delaborate an `Operation w` inside `Instr.mk w op` into an `aarch64_instr`. -/
private def delabOperation (w? : Option RegWidth) : DelabM (TSyntax `aarch64_instr) :=
  delabLoadStoreOp w? <|> delabArithMulOp <|> delabLogicBitOp w? <|> delabCondBranchOp w?

/-- Delaborate an `Instr` into an `aarch64_instr`. Fails for open or non-canonical instructions so the
    enclosing `delabDirective` falls back to `❰t❱`. -/
def delabInstr : DelabM (TSyntax `aarch64_instr) := do
  match_expr ← getExpr with
  | Instr.mk wExpr _ =>
    let w? := evalRegWidth? wExpr
    let stx ← withNaryArg 1 (delabOperation w?)
    annotateStx stx
  | _ => failure

-- ============================================================================
-- Directive & Program Delaboration
-- ============================================================================

/-- Delaborate a `Directive` into concrete assembly syntax, failing on open or unsupported terms. -/
private def delabDirectiveCore : DelabM (TSyntax `aarch64_directive) := do
  match_expr ← getExpr with
  | Kraken.Directive.label _ _ _ =>
    let lbl ← withAppArg delabLabel
    annotateStx (← `(aarch64_directive| $lbl:aarch64_label :))
  | Kraken.Directive.instr _ _ _ =>
    let ins ← withAppArg delabInstr
    annotateStx (← `(aarch64_directive| $ins:aarch64_instr))
  | _ => failure

/-- Delaborate a `Directive` into an `aarch64_directive`, falling back to `❰t❱` for open or non-canonical terms. -/
def delabDirective : DelabM (TSyntax `aarch64_directive) := do
  try
    delabDirectiveCore
  catch _ =>
    let t ← delab
    annotateStx (← `(aarch64_directive| ❰ $t ❱))

/-- Delaborate the spine of a `List Directive`, returning its delaborated directives and any non-`[]` tail. -/
private partial def delabDirectiveListSpine :
    DelabM (Array (TSyntax `aarch64_directive) × Option Term) := do
  match_expr ← getExpr with
  | List.cons _ _ _ =>
    let hd ← withAppFn (withAppArg delabDirective)
    let (tl, tail?) ← withAppArg delabDirectiveListSpine
    return (#[hd] ++ tl, tail?)
  | List.nil _ =>
    return (#[], none)
  | _ =>
    return (#[], some (← delab))

@[app_delab Kraken.Directive.instr, app_delab Kraken.Directive.label, app_delab Kraken.Directive.byteArray, app_delab Kraken.Directive.word]
def delabDirective' : Delab := do
  if ← getPPOption getPPExplicit then failure
  let stx ← delabDirectiveCore
  `(⸨dir| $stx ⸩)

@[app_unexpander Kraken.Sized.mk]
def sizedUnexpander : Unexpander
  | `($_ $dir $sz) => do
    let `(⸨dir| $dir⸩) := dir | throw ()
    let i ← match sz with
      | `(Kraken.Layout.size $_ $_ $i) | `(Layout.size $_ $_ $i) | `(size $_ $_ $i) => pure i
      | _ => throw ()
    `(⸨dir $i | $dir ⸩)
  | _ => throw ()

/-- Delaborate a non-empty `List Directive` (`Program`) into a `⸨prog| ...⸩` block (or
    `⸨prog| ...⸩ ++ tail` when the list ends in an open tail). -/
@[app_delab List.cons]
def delabProgram : Delab := do
  if ← getPPOption getPPExplicit then failure
  match ← getExpr with
  | mkApp3 (.const ``List.cons _) (.const ``_root_.Directive _) _ _
  | mkApp3 (.const ``List.cons _) (mkApp2 (.const ``Kraken.Directive _) (.const ``_root_.Instr _) _) _ _ =>
    let (dirs, tail?) ← delabDirectiveListSpine
    let prog ← `(aarch64_prog| $dirs:aarch64_directive*)
    let listing ← annotateTermInfo (← `(⸨prog| $prog:aarch64_prog⸩))
    match tail? with
    | none => return listing
    | some tail => `($listing ++ $tail)
  | _ => failure

-- ============================================================================
-- Standalone Embeddings (`⸨instr|`, `⸨mem|`, `⸨reg|`, `⸨const|`, `⸨cc|`)
-- ============================================================================

/-! Values that are not part of a larger directive or program delaborate to their standalone embedding.
These delaborators only fire on closed (canonical) values, so that the fallback to `❰t❱` of the
delaborators they reuse, which delaborates the same expression again, is never reached. -/

/-- `⸨instr| ... ⸩` for an `Instr`. -/
@[app_delab Instr.mk]
def delabInstrEmbedding : Delab := do
  if ← getPPOption getPPExplicit then failure
  let i ← delabInstr
  annotateTermInfo (← `(⸨instr| $i ⸩))

/-- Delaborate an `AddrExpr` into an `aarch64_mem` that `elabAddrExpr` elaborates back to it: unlike in
    `delabScaledAddr`, there is no access size that immediate offsets must be aligned to, and the amount of
    a register offset's shift is always printed unless it is the default `[Xn, Xm]`/`[Xn, Wm]`. -/
private def delabAddrExpr : DelabM (TSyntax `aarch64_mem) := do
  let_expr AddrExpr.mk _ offExpr := ← getExpr | failure
  let base ← withNaryArg 0 delabRegOrSp
  let stx ← match_expr offExpr with
    | AddrOff.imm immAddrExpr =>
      let_expr ImmAddrExpr.mk immExpr idxOpt := immAddrExpr | failure
      match_expr idxOpt with
      | Option.none _ =>
        if isZeroConst immExpr then
          `(aarch64_mem| [$base:aarch64_reg])
        else
          let off ← withNaryArg 1 (withAppArg (withNaryArg 0 delabConstExpr))
          `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const])
      | Option.some _ idxExpr =>
        let imm ← withNaryArg 1 (withAppArg (withNaryArg 0 delabImmConst))
        let off ← `(aarch64_const| $imm:aarch64_imm)
        match_expr idxExpr with
        | Index.Pre  => `(aarch64_mem| [$base:aarch64_reg, $off:aarch64_const]!)
        | Index.Post => `(aarch64_mem| [$base:aarch64_reg], $off:aarch64_const)
        | _          => failure
      | _ => failure
    | AddrOff.reg memExtExpr =>
      let_expr MemExtRegExpr.mk _ extExpr := memExtExpr | failure
      let_expr MemExtend.mk typeExpr amtExpr := extExpr | failure
      let (regW, rm) ← withNaryArg 1 (withAppArg (withNaryArg 0 delabRegOrZrW))
      let some ty := evalMemExtendType? typeExpr | failure
      let some amt := evalMemExtendAmount? amtExpr | failure
      if amt == 0 && ((regW == .W64 && ty == .UXTX) || (regW == .W32 && ty == .UXTW)) then
        `(aarch64_mem| [$base:aarch64_reg, $rm:aarch64_reg])
      else
        -- An omitted amount (`sxtw`) is `#0`.
        let mkMod (pre stem sfx : String) : DelabM (TSyntax `aarch64_modifier) := do
          if amt != 0 then return ← mkModifier pre stem sfx (← mkImmInt amt)
          let kind := mkAffixed `aarch64_modifier_kind pre stem sfx
          annotateStx (← `(aarch64_modifier| $kind:aarch64_modifier_kind))
        let mod ← match regW, ty with
          | .W64, .UXTX => mkMod "" "" "lsl"
          | _,    .UXTW => mkMod "u" "xt" "w"
          | _,    .SXTW => mkMod "s" "xt" "w"
          | _,    .UXTX => mkMod "u" "xt" "x"
          | _,    .SXTX => mkMod "s" "xt" "x"
        `(aarch64_mem| [$base:aarch64_reg, $rm:aarch64_reg, $mod:aarch64_modifier])
    | _ => failure
  annotateStx stx

/-- `⸨mem| ... ⸩` for an `AddrExpr` or an `UnscaledAddrExpr`. -/
@[app_delab AddrExpr.mk, app_delab UnscaledAddrExpr.mk]
def delabAddrExprEmbedding : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let m ←
    if e.isAppOfArity ``AddrExpr.mk 2 then delabAddrExpr
    else if e.isAppOfArity ``UnscaledAddrExpr.mk 2 then delabUnscaledAddr
    else failure
  annotateTermInfo (← `(⸨mem| $m ⸩))

/-- `⸨reg| ... ⸩` for a concrete `RegOrZr w` or `RegOrSp w`. -/
@[app_delab RegOrZr.low, app_delab RegOrSp.low]
def delabRegEmbedding : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let r ←
    if (evalRegOrZr? e).isSome then delabRegOrZr
    else if (evalRegOrSp? e).isSome then delabRegOrSp
    else failure
  annotateTermInfo (← `(⸨reg| $r ⸩))

/-- Whether `delabConstExpr` delaborates the `ConstExpr` `e` without falling back to `❰t❱` at its root:
    integer literals, labels that are identifiers, and relocations of labels. -/
private def isConcreteConstExpr (e : Expr) : Bool :=
  match_expr e with
  | ConstExpr.int64 i => (evalInt64? i).isSome
  | ConstExpr.label lbl => if let .lit (.strVal s) := lbl then isAsmIdent s && !isRegName s else false
  | ConstExpr.pg_hi21 inner => inner.isAppOfArity ``ConstExpr.label 1
  | ConstExpr.lo12 inner => inner.isAppOfArity ``ConstExpr.label 1
  | _ => false

/-- `⸨const| ... ⸩` for a `ConstExpr` written in `aarch64_const`. -/
@[app_delab ConstExpr.int64, app_delab ConstExpr.label, app_delab ConstExpr.pg_hi21, app_delab ConstExpr.lo12]
def delabConstExprEmbedding : Delab := do
  if ← getPPOption getPPExplicit then failure
  unless isConcreteConstExpr (← getExpr) do failure
  let c ← delabConstExpr
  annotateTermInfo (← `(⸨const| $c ⸩))

/-- `⸨cc| ... ⸩` for a `CondCode`. -/
@[app_delab CondCode.EQ, app_delab CondCode.NE, app_delab CondCode.CS, app_delab CondCode.CC,
  app_delab CondCode.MI, app_delab CondCode.PL, app_delab CondCode.VS, app_delab CondCode.VC,
  app_delab CondCode.HI, app_delab CondCode.LS, app_delab CondCode.GE, app_delab CondCode.LT,
  app_delab CondCode.GT, app_delab CondCode.LE, app_delab CondCode.AL, app_delab CondCode.NV]
def delabCondEmbedding : Delab := do
  if ← getPPOption getPPExplicit then failure
  unless (evalCondCode? (← getExpr)).isSome do failure
  let c ← delabCond
  annotateTermInfo (← `(⸨cc| $c ⸩))

end

end Kraken.AArch64.Parser
