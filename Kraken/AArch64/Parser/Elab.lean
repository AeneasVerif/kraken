module

public import Kraken.AArch64.Parser.Basic
public meta import Kraken.AArch64.Parser.Basic
public import Kraken.AArch64.Parser.Syntax
public meta import Kraken.AArch64.Parser.Syntax
public meta import Lean

/-!
Operands may contain antiquotations (`❰t❱`, `#❰t❱`), whose value is only known as a term, so everything
from operands upwards is elaborated to `Expr`s. The operand width of an instruction is kept in the
`AArch64ElabM` state rather than threaded through the operand elaborators: a concrete register reports its
width, which must agree with what the mnemonic and the other operands determined; an antiquotation is
elaborated at the instruction's width. Registers whose width is not the instruction's (memory base and
index registers, extended registers, the narrow sources of widening operations) are elaborated in a scope
of their own. An immediate antiquotation `#❰t❱` always denotes an integer: `t` is elaborated at the type
of the field it fills (`Nat` or `Int64`), and where a constant expression is expected (offsets, targets,
arithmetic immediates), at `Int64`, as the integer constant `ConstExpr.int64 t`. A constant expression
antiquotation `❰t❱` denotes a `ConstExpr`, and a label antiquotation `❰t❱` (in label declarations and
relocations) a `Label`. Where a register may also stand (a flexible source, `[Xn, ❰t❱]`), the parser leaves
a `choice` between the register and the constant expression readings, which is resolved by the type of `t`
before the instruction is elaborated (`resolveRegOrConstChoice`).
-/

namespace Kraken.AArch64.Parser

open Lean Meta Elab Kraken.Parser
open Term hiding mkConst  -- `mkConst` is the pure `Lean.mkConst`, not the environment lookup `Term.mkConst`

@[expose] public section

/-- Re-tag a register with another width, for operations whose source register is narrower than their
    width index (`sxtb Xd, Wn` is `SBFM Xd, Xn, #0, #7`). -/
def _root_.RegOrZr.withWidth {w' : RegWidth} : RegOrZr w' → (w : RegWidth) → RegOrZr w
  | .low r _, w => .low r w

end

public meta section

-- ============================================================================
-- Named Ranges & Immediate Validation
-- ============================================================================

private def checkRange (valType : String) (val : Int) (r : Std.Rcc Int) (mod : Int := 1) : Except String Unit := do
  unless val ∈ r do throw s!"{valType} {val} out of range [{r.lower}, {r.upper}]"
  unless mod ∣ val do throw s!"{valType} {val} must be multiple of {mod}"

/-- Validate a pre/post-indexed (`mode`) load/store immediate offset. -/
def checkIndexedOffset (mode : String) (imm : Int64) : Except String Unit :=
  checkRange s!"{mode} offset" imm.toInt (-256...=255)
  -- if imm.toInt ∈ -256...=255 then .ok ()
  -- else .error s!"{mode} offset {imm.toInt} out of range [-256, 255]"

/-- Validate the 16-bit unsigned immediate of a move wide instruction. -/
def checkMovWideImmediate (imm : Int64) : Except String Unit :=
  checkRange s!"move wide immediate" imm.toInt (0...=UInt16.size-1)

/-- Validate a literal pool constant (`ldr Rt, =imm`) loaded into a `w`-bit register. -/
def checkLiteralPoolImmediate (w : RegWidth) (imm : Int64) : Except String Unit := do
  if w == .W32 then
    checkRange s!"literal pool immediate" imm.toInt (Int32.minValue.toInt...=Int32.maxValue.toInt)

-- ============================================================================
-- Elaboration Monad: Operand Width Inference
-- ============================================================================

structure AArch64ElabM.State where
  /-- Operand width (`RegWidth`) of the scope being elaborated: either a metavariable if it has not been
      inferred yet, or a value of type `RegWidth` (`.W32`, `.W64`, or a variable). -/
  operandWidth : Expr

abbrev AArch64ElabM := StateRefT AArch64ElabM.State TermElabM

/-- Run the elaboration of an instruction, whose operand width is yet to be determined. -/
nonrec def AArch64ElabM.run' {α : Type} (x : AArch64ElabM α) : TermElabM α := do
  x.run' { operandWidth := ← mkFreshExprMVar (toTypeExpr RegWidth) }

/-- Extract a concrete `RegWidth` value from an expression if it has already been determined. -/
def evalWidth? (wExpr : Expr) : MetaM (Option RegWidth) := do
  let wExpr ← instantiateMVars wExpr
  return [RegWidth.W32, .W64].find? (toExpr · == wExpr)

/-- Print a `RegWidth` expression as a value if possible, using its `ToString` instance. -/
def ppWidth (wExpr : Expr) : MetaM MessageData := do
  if let some w ← evalWidth? wExpr then return m!"{w}"
  return m!"{wExpr}"

/-- The operand width of the current instruction or scope. -/
def getOperandWidth : AArch64ElabM Expr :=
  return (← get).operandWidth

/-- The operand width of the current scope as a value, if already determined. -/
def evalOperandWidth? : AArch64ElabM (Option RegWidth) := do
  evalWidth? (← getOperandWidth)

/-- The operand width of the current scope as a value, for instructions whose encoding depends on it. -/
def evalOperandWidth : AArch64ElabM RegWidth := do
  let some w ← evalOperandWidth? | throwError "could not infer operand width"
  return w

/-- The width that concrete immediates are validated against: the operand width, or the most permissive
    one (64 bits) while it is undetermined (an antiquoted register of variable width). -/
def evalBoundsWidth : AArch64ElabM RegWidth :=
  return (← evalOperandWidth?).getD .W64

/-- Check that a register of width `w` may be used where a register of width `expected` is required. -/
def unifyWidth (expected w : Expr) : MetaM Unit := do
  unless ← isDefEq expected w do throwError "expected {← ppWidth expected} register, got {← ppWidth w}"

/-- Record that the current operand has width `w`, which must agree with the width already determined by
    the already processed part of the instruction. -/
def setOperandWidth (w : Expr) : AArch64ElabM Unit := do
  unifyWidth (← getOperandWidth) w

/-- Restrict the instruction's operand width to `w₀`, for mnemonics that only exist at one width. -/
def requireWidth (w₀ : RegWidth) : AArch64ElabM Unit := do
  let w ← getOperandWidth
  unless ← isDefEq w (toExpr w₀) do
    let got := match ← evalWidth? w with
      | some w => m!"{w.bits}-bit"
      | none   => m!"{w}"
    throwError "requires {w₀.bits}-bit registers (got {got})"

/-- Apply `f`, whose first argument is a `RegWidth` (a constructor `c {w} ...` or a type `T w`), to the
    instruction's operand width and to `args`. -/
def mkAppWidth (f : Expr) (args : Array Expr := #[]) : AArch64ElabM Expr :=
  return mkAppN (f.app <| ← getOperandWidth) args

/-- Run `body` with its own operand width, initially `w?`, and return the width it determined. -/
def withOperandWidth {α : Type} (w? : Option RegWidth) (body : AArch64ElabM α) : AArch64ElabM (α × Expr) := do
  let w ← (toExpr <$> w?).getDM <| mkFreshExprMVar (toTypeExpr RegWidth)
  let ⟨res, {operandWidth, ..}⟩ ← body.run {operandWidth := w}
  return ⟨res, operandWidth⟩

/-- Run `body` at the fixed operand width `w`, independently of the instruction's operand width. -/
def atOperandWidth {α : Type} (w : RegWidth) (body : AArch64ElabM α) : AArch64ElabM α := do
  let (res, _) ← body.run { operandWidth := toExpr w }
  return res

/-- Build `Instr.mk` from the instruction's operand width and its operation `op`. -/
def mkInstr (op : Expr) : AArch64ElabM Expr := do
  let w ← instantiateMVars (← getOperandWidth)
  if w.isMVar then throwError "could not infer operand width"
  instantiateMVars (mkApp2 (mkConst ``Instr.mk) w op)

/-- Elaborate the term `t` of an antiquotation at the type `ty` expected by its position. Elaboration is
    forced to finish here (`withSynthesize`) because the instruction inspects the result right away: the
    unification of `ty` against `t`'s type is what determines the operand width, and `mkInstr` rejects a
    width that is still a metavariable. A postponed `t` would leave a placeholder of type `ty` behind,
    with the width undetermined. A type mismatch aborts the instruction instead of being recovered as
    `sorry`. -/
def elabAntiquot (t : Term) (ty : Expr) : TermElabM Expr :=
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringType t ty

-- ============================================================================
-- Register Evaluation & Elaboration
-- ============================================================================

/-- Map a register index suffix (`0`..`30`) to its `XReg`. -/
def xreg? : String → Option XReg
  | "0"  => some .X0  | "1"  => some .X1  | "2"  => some .X2  | "3"  => some .X3
  | "4"  => some .X4  | "5"  => some .X5  | "6"  => some .X6  | "7"  => some .X7
  | "8"  => some .X8  | "9"  => some .X9  | "10" => some .X10 | "11" => some .X11
  | "12" => some .X12 | "13" => some .X13 | "14" => some .X14 | "15" => some .X15
  | "16" => some .X16 | "17" => some .X17 | "18" => some .X18 | "19" => some .X19
  | "20" => some .X20 | "21" => some .X21 | "22" => some .X22 | "23" => some .X23
  | "24" => some .X24 | "25" => some .X25 | "26" => some .X26 | "27" => some .X27
  | "28" => some .X28 | "29" => some .X29 | "30" => some .X30
  | _    => none

/-- Whether a register syntax node is syntactically the stack pointer (`sp` or `wsp`). -/
def isSpSyntax (stx : TSyntax `aarch64_reg) : Bool :=
  match stx with
  | `(aarch64_reg| sp) | `(aarch64_reg| wsp) => true
  | _ => false

/-- Evaluate a concrete `aarch64_reg` into a width-tagged register, before the instruction decides whether
    register 31 denotes `sp` or `xzr`. -/
def evalAnyReg (stx : TSyntax `aarch64_reg) : TermElabM AnyRegW := withRef stx do
  match stx with
  | `(aarch64_reg| sp)  => pure ⟨.W64, .sp⟩
  | `(aarch64_reg| wsp) => pure ⟨.W32, .sp⟩
  | `(aarch64_reg| lr)  => pure ⟨.W64, .gpr .X30⟩
  | _ =>
    let (stem, idx) ← splitSuffixed stx
    let w ← match stem with
      | "x" => pure RegWidth.W64
      | "w" => pure RegWidth.W32
      | _   => throwError "expected register"
    if let "zr" := idx then return ⟨w, .xzr⟩
    let some r := xreg? idx
      | throwError "invalid register index '{idx}'"
    pure ⟨w, .gpr r⟩

/-- Interpret register 31 as the stack pointer; the zero register is rejected. -/
def AnyReg.toRegOrSpM {w : RegWidth} : AnyReg w → TermElabM (RegOrSp w)
  | .gpr r => pure (.low (.reg r) w)
  | .sp    => pure (.low .SP w)
  | .xzr   => throwError "xzr/wzr not allowed here (sp/wsp expected)"

/-- Interpret register 31 as the zero register; the stack pointer is rejected. -/
def AnyReg.toXRegOrXzrM {w : RegWidth} : AnyReg w → TermElabM XRegOrXzr
  | .gpr r => pure (.reg r)
  | .xzr   => pure .XZR
  | .sp    => throwError "sp/wsp not allowed here (xzr/wzr expected)"

/-- Elaborate an `aarch64_reg` into an `Expr` of type `RegOrSp w` if `sp` (register 31 is `sp`/`wsp`), or
    `RegOrZr w` otherwise (register 31 is `xzr`/`wzr`), where `w` is the operand width of the current scope:
    a concrete register determines it, an antiquotation `❰t❱` is elaborated at it. -/
def elabReg (stx : TSyntax `aarch64_reg) (sp : Bool) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_reg| ❰ $t ❱) =>
    elabAntiquot t (← mkAppWidth (mkConst (if sp then ``RegOrSp else ``RegOrZr)))
  | _ =>
    let ⟨w, r⟩ ← evalAnyReg stx
    setOperandWidth (toExpr w)
    if sp then return toExpr (← r.toRegOrSpM)
    return toExpr (RegOrZr.low (← r.toXRegOrXzrM) w)

/-- Elaborate an `aarch64_reg` into an `Expr` of type `RegOrSp w` (see `elabReg`). -/
def elabRegOrSp (stx : TSyntax `aarch64_reg) : AArch64ElabM Expr :=
  elabReg stx (sp := true)

/-- Elaborate an `aarch64_reg` into an `Expr` of type `RegOrZr w` (see `elabReg`). -/
def elabRegOrZr (stx : TSyntax `aarch64_reg) : AArch64ElabM Expr :=
  elabReg stx (sp := false)

/-- Elaborate the base register (`Xn` or `sp`) of a memory operand into an `Expr` of type `RegOrSp .W64`. It
    is always 64-bit, whatever the operand width of the instruction (`ldr w0, [x1]`). -/
def elabBaseReg (stx : TSyntax `aarch64_reg) : AArch64ElabM Expr :=
  atOperandWidth .W64 (elabRegOrSp stx)

/-- Elaborate a register whose width is its own rather than the instruction's (an index or extended
    register) into an `Expr` of type `RegOrZrW`, together with that width, which is `default` when an
    antiquotation leaves it undetermined. -/
def elabRegOrZrW (stx : TSyntax `aarch64_reg) (default : RegWidth) : AArch64ElabM (Expr × RegWidth) := do
  let (reg, wExpr) ← withOperandWidth none (elabRegOrZr stx)
  let w ← match ← evalWidth? wExpr with
    | some w => pure w
    | none =>
      unless ← isDefEq wExpr (toExpr default) do throwErrorAt stx "could not infer register width"
      pure default
  return (mkApp2 (mkConst ``RegOrZrW.mk) (toExpr w) reg, w)

/-- Elaborate the 32-bit source `Wn` of an extension into an `Expr` of type `RegOrZr w`, `w` being the
    operand width: `sxtb Xd, Wn` is the bitfield move `SBFM Xd, Xn, #0, #7`, whose source has the width of
    its destination. An antiquotation `t : RegOrZr .W32` is re-tagged as `t.withWidth w`. -/
def elabExtendSrc (stx : TSyntax `aarch64_reg) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_reg| ❰ $t ❱) =>
    let rn ← elabAntiquot t (mkApp (mkConst ``RegOrZr) (toExpr RegWidth.W32))
    mkAppWidth (mkApp2 (mkConst ``RegOrZr.withWidth) (toExpr RegWidth.W32) rn)
  | _ =>
    let ⟨w, r⟩ ← evalAnyReg stx
    unifyWidth (toExpr RegWidth.W32) (toExpr w)
    return mkApp2 (mkConst ``RegOrZr.low) (toExpr (← r.toXRegOrXzrM)) (← getOperandWidth)

/-- The zero register `xzr`/`wzr` at the instruction's operand width (`RegOrZr.low .XZR w`). -/
def mkXzr : AArch64ElabM Expr := do
  return mkApp2 (mkConst ``RegOrZr.low) (toExpr XRegOrXzr.XZR) (← getOperandWidth)

/-- The register index (`XRegOrXzr`/`XRegOrSp`) of a concrete register `RegOrZr.low r w`/`RegOrSp.low r w`;
    `none` for an antiquotation that is not syntactically a concrete register. -/
def regIndex? : Expr → Option Expr
  | mkApp2 (.const ``RegOrZr.low _) r _ | mkApp2 (.const ``RegOrSp.low _) r _ => some r
  | _ => none

/-- The general-purpose register (`XReg`) of a concrete register; `none` for register 31 (`sp`/`xzr`) and
    for antiquotations that are not syntactically concrete. -/
def gpr? : Expr → Option Expr
  | mkApp2 (.const ``RegOrZr.low _) (mkApp (.const ``XRegOrXzr.reg _) r) _
  | mkApp2 (.const ``RegOrSp.low _) (mkApp (.const ``XRegOrSp.reg _) r) _ => some r
  | _ => none

-- ============================================================================
-- Immediate, Constant Expression & Condition Code Evaluation / Elaboration
-- ============================================================================

/-- Evaluate an `aarch64_int` into a signed integer. -/
def evalInt (stx : TSyntax `aarch64_int) : TermElabM Int := withRef stx do
  match stx with
  | `(aarch64_int| $n:num)
  | `(aarch64_int| +$n:num) => pure n.getNat
  | `(aarch64_int| -$n:num) => pure (-n.getNat)
  | _ => throwError "expected integer literal"

/-- Evaluate a concrete `aarch64_imm` into a signed integer. -/
def evalImm (stx : TSyntax `aarch64_imm) : TermElabM Int := withRef stx do
  match stx with
  | `(aarch64_imm| $[#]? $i:aarch64_int) => evalInt i
  | _ => throwError "expected integer immediate"

/-- Evaluate a concrete `aarch64_imm` as a non-negative `Nat`. -/
def evalImmNat (stx : TSyntax `aarch64_imm) : TermElabM Nat := withRef stx do
  let v ← evalImm stx
  if v < 0 then throwError "expected non-negative immediate, got {v}"
  pure v.toNat

/-- Evaluate a concrete `aarch64_imm` as `Int64`, checking the 64-bit range. -/
def evalImm64 (stx : TSyntax `aarch64_imm) : TermElabM Int64 := withRef stx do
  _root_.Int64.ofIntNoOverflow (← evalImm stx)

/-- Elaborate an `aarch64_imm` into an `Expr` of type `Nat`, validating concrete values with `check`. -/
def elabImmNat (stx : TSyntax `aarch64_imm) (check : Nat → Except String Unit := fun _ => .ok ()) :
    TermElabM Expr := withRef stx do
  if let `(aarch64_imm| #❰ $t ❱) := stx then return ← elabAntiquot t (mkConst ``Nat)
  let n ← evalImmNat stx
  ofExcept (check n)
  return toExpr n

/-- Elaborate an `aarch64_imm` into an `Expr` of type `Int64`, validating concrete values with `check`. -/
def elabImm64 (stx : TSyntax `aarch64_imm) (check : Int64 → Except String Unit := fun _ => .ok ()) :
    TermElabM Expr := withRef stx do
  if let `(aarch64_imm| #❰ $t ❱) := stx then return ← elabAntiquot t (mkConst ``Int64)
  let v ← evalImm64 stx
  ofExcept (check v)
  return toExpr v

/-- Elaborate an `aarch64_imm` into an `Expr` of type `ConstExpr`: the integer constant `.int64 v` of the
    `Int64` immediate `v`, validated with `check` when concrete. -/
def elabImmConst (stx : TSyntax `aarch64_imm) (check : Int64 → Except String Unit := fun _ => .ok ()) :
    TermElabM Expr :=
  return mkApp (mkConst ``ConstExpr.int64) (← elabImm64 stx check)

/-- Elaborate an `aarch64_label` into an `Expr` of type `Label`. -/
def elabLabel (stx : TSyntax `aarch64_label) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_label| ❰ $t ❱)            => elabAntiquot t (mkConst ``Label)
  | `(aarch64_label| $id:aarch64_ident) => return toExpr (← getAsmIdent id)
  | _                                   => throwError "expected label"

/-- The `ConstExpr` constructor of a relocation modifier (`pg_hi21`, `lo12`). -/
def elabRelocation (stx : TSyntax `aarch64_ident) : TermElabM Expr := withRef stx do
  match (← getAsmIdent stx).toLower with
  | "pg_hi21" => pure (mkConst ``ConstExpr.pg_hi21)
  | "lo12"    => pure (mkConst ``ConstExpr.lo12)
  | name      => throwError "unknown relocation modifier: {name}"

/-- Elaborate an `aarch64_const` into an `Expr` of type `ConstExpr`, validating integer immediates with
    `check` (symbols, relocations and antiquoted constants `❰t❱` are left to the assembler). An immediate,
    including an antiquoted one, is an integer constant (see `elabImmConst`). -/
def elabConst (stx : TSyntax `aarch64_const) (check : Int64 → Except String Unit := fun _ => .ok ()) :
    TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_const| ❰ $t ❱) =>
    elabAntiquot t (mkConst ``ConstExpr)
  | `(aarch64_const| $i:aarch64_imm) =>
    elabImmConst i check
  | `(aarch64_const| $[#]? : $modifier:aarch64_ident : $sym:aarch64_label) =>
    return mkApp (← elabRelocation modifier) (mkApp (mkConst ``ConstExpr.label) (← elabLabel sym))
  | `(aarch64_const| $id:aarch64_ident) =>
    return toExpr (ConstExpr.label (← getAsmIdent id))
  | _ => throwError "invalid constant expression"

/-- The `ConstExpr` of an omitted immediate offset. -/
def zeroOffset : Expr := toExpr (ConstExpr.int64 0)

/-- Evaluate the condition code carried by the suffix of an `aarch64_cond` operand or `b.<cond>` mnemonic. -/
def evalCond (stx : Syntax) : TermElabM CondCode := withRef stx do
  let (_, sfx) ← splitSuffixed stx
  let some cond := parseCondCode sfx | throwError "invalid condition code '{sfx}'"
  pure cond

/-- Elaborate an `aarch64_cond` operand into an `Expr` of type `CondCode`, inverting the condition when
    `invert = true` (for `cinc`/`cinv`/`cneg`/`cset`/`csetm` aliases). -/
def elabCond (stx : TSyntax `aarch64_cond) (invert : Bool := false) : TermElabM Expr := withRef stx do
  if let `(aarch64_cond| ❰ $t ❱) := stx then
    let c ← elabAntiquot t (mkConst ``CondCode)
    return if invert then mkApp (mkConst ``CondCode.invert) c else c
  let c ← evalCond stx
  return toExpr (if invert then c.invert else c)

-- ============================================================================
-- Shift & Extend Modifier Evaluation / Elaboration
-- ============================================================================

/-- A shift or extend modifier as written (`lsl #2`, `uxtw`): its keyword and its amount, if any. -/
structure Modifier where
  ref : Syntax
  /-- Keyword (`lsl`, `uxtw`, ...). -/
  name : String
  /-- Amount, as written (`#2`, `#❰n❱`); `0` when omitted. -/
  amount? : Option (TSyntax `aarch64_imm)
  /-- Whether the keyword is an extension (`uxtb`..`sxtx`) rather than a shift (`lsl`, `lsr`, `asr`, `ror`). -/
  isExtend : Bool

def evalModifier (stx : TSyntax `aarch64_modifier) : TermElabM Modifier := withRef stx do
  let `(aarch64_modifier| $kind:aarch64_modifier_kind $[$amount?:aarch64_imm]?) := stx
    | throwError "expected shift or extend modifier"
  let (stem, sfx) ← splitSuffixed kind
  return { ref := stx, name := stem ++ sfx, amount?, isExtend := stem == "uxt" || stem == "sxt" }

/-- Evaluate the amount of a modifier (`0` when omitted). -/
def Modifier.evalAmount (m : Modifier) : TermElabM Nat :=
  return (← m.amount?.mapM evalImmNat).getD 0

/-- Elaborate a shift applied to a register operand (`ror` only for logical instructions) into its type and
    an `Expr` of type `Int64` for its amount. -/
def elabShift (m : Modifier) (allowRor : Bool) : AArch64ElabM (ShiftType × Expr) := withRef m.ref do
  let type ← match m.name with
    | "lsl" => pure ShiftType.LSL
    | "lsr" => pure ShiftType.LSR
    | "asr" => pure ShiftType.ASR
    | "ror" => if allowRor then pure ShiftType.ROR else throwError "arithmetic instructions do not support ROR shift"
    | name  => throwError "unknown shift type: {name}"
  let some amount := m.amount? | return (type, toExpr (0 : Int64))
  return (type, ← elabImm64 amount (checkShiftAmount (← evalBoundsWidth)))

/-- Evaluate an extension applied to a `regW`-bit register operand of a `w`-bit arithmetic instruction. -/
def evalExtend (m : Modifier) (w regW : RegWidth) : TermElabM Extend := withRef m.ref do
  let type ← ofExcept (getExtendType m.name w regW)
  let amount ← match ← m.evalAmount with
    | 0 => pure ExtendAmount.E0
    | 1 => pure ExtendAmount.E1
    | 2 => pure ExtendAmount.E2
    | 3 => pure ExtendAmount.E3
    | 4 => pure ExtendAmount.E4
    | n => throwError "invalid extend amount: {n}"
  pure { type, amount }

/-- The width of the register an arithmetic extension applies to, when an antiquotation leaves it open:
    `Xm` for `uxtx`/`sxtx`, the instruction's width `w` for `lsl` (an alias of either), `Wm` otherwise. -/
def Modifier.extendedWidth (m : Modifier) (w : RegWidth) : RegWidth :=
  match m.name with
  | "uxtx" | "sxtx" => .W64
  | "lsl"           => w
  | _               => .W32

/-- Evaluate a shift applied to the immediate of an arithmetic instruction (`lsl #0` or `lsl #12`). -/
def evalImmShift (m : Modifier) : TermElabM ImmShift := withRef m.ref do
  unless m.name == "lsl" do throwError "expected lsl for immediate shift, got {m.name}"
  match ← m.evalAmount with
  | 0  => pure .S0
  | 12 => pure .S12
  | n  => throwError "invalid immediate shift {n} (must be 0 or 12)"

/-- Evaluate a shift applied to the immediate of a `w`-bit move wide instruction. -/
def evalMovShift (m : Modifier) (w : RegWidth) : TermElabM (MovShift w) := withRef m.ref do
  unless m.name == "lsl" do throwError "only lsl shift supported for move wide"
  ofExcept (getMovShift w (← m.evalAmount))

-- ============================================================================
-- Source Operand Elaboration
-- ============================================================================

/-- Elaborate a register with optional shift (`Rm`, `Rm, lsl #n`) into an `Expr` of type `ShiftRegExpr w`. -/
def elabShiftedReg (rm : TSyntax `aarch64_reg) (shift? : Option Modifier) (allowRor : Bool) :
    AArch64ElabM Expr := do
  let reg ← elabRegOrZr rm
  let (shift, amount) ← match shift? with
    | none   => pure (ShiftType.LSL, toExpr (0 : Int64))
    | some m => elabShift m allowRor
  mkAppWidth (mkConst ``ShiftRegExpr.mk) #[reg, amount, toExpr shift]

/-- Elaborate the bitmask immediate source of a logical instruction (`_i` form) into an `Expr` of type
    `ConstExpr`. -/
def elabLogicalImm (c : TSyntax `aarch64_const) (mod? : Option (TSyntax `aarch64_modifier)) :
    AArch64ElabM Expr := do
  if let some mod := mod? then throwErrorAt mod "logical immediates cannot be shifted"
  elabConst c (checkLogicalImmediate (← evalBoundsWidth))

/-- The flexible source operand of an add/subtract/compare, classified by the instruction form it selects. -/
inductive ArithSrc
  /-- Immediate with optional `lsl #0`/`lsl #12` (extended-register/immediate `_e` form). -/
  | imm (c : TSyntax `aarch64_const) (shift? : Option Modifier)
  /-- Extended register (`_e` form). -/
  | ext (rm : TSyntax `aarch64_reg) (ext? : Option Modifier)
  /-- Shifted register (`_s` form). -/
  | shift (rm : TSyntax `aarch64_reg) (shift? : Option Modifier)

/-- Whether the source selects the extended-register/immediate (`_e`) form. -/
def ArithSrc.isExt : ArithSrc → Bool
  | .shift .. => false
  | _         => true

/-- Classify the flexible source of an add/subtract/compare. A register with no modifier or a shift uses
    the shifted-register form, unless the stack pointer is involved (`sp`), in which case `lsl` is the
    `uxtx`/`uxtw` alias of the extended-register form. -/
def evalArithSrc (stx : TSyntax `aarch64_src) (sp : Bool) : TermElabM ArithSrc := withRef stx do
  match stx with
  | `(aarch64_src| $c:aarch64_const $[, $mod?]?) =>
    return .imm c (← mod?.mapM evalModifier)
  | `(aarch64_src| $rm:aarch64_reg $[, $mod?]?) =>
    let m? ← mod?.mapM evalModifier
    return if sp || m?.any (·.isExtend) then .ext rm m? else .shift rm m?
  | _ => throwError "invalid source operand"

/-- Elaborate the immediate source (`#imm{, lsl #0|12}`) of an add/subtract into an `Expr` of type
    `ExtOrImmReg`. -/
def elabArithImm (c : TSyntax `aarch64_const) (shift? : Option Modifier) : TermElabM Expr := do
  unless shift?.isNone || c matches `(aarch64_const| $_:aarch64_imm) do
    throwErrorAt c "relocation modifiers and labels cannot be shifted with lsl in immediate operands"
  let imm ← elabConst c checkArithmeticImmediate
  let shift ← match shift? with
    | some m => evalImmShift m
    | none   => pure .S0
  return mkApp (mkConst ``ExtOrImmReg.imm) (mkApp2 (mkConst ``ImmExpr.mk) imm (toExpr shift))

/-- Elaborate the extended-register source (`Rm{, extend #amount}`) of an add/subtract into an `Expr` of
    type `ExtOrImmReg`. Without an extension, the register must have the instruction's width. -/
def elabExtendedReg (rm : TSyntax `aarch64_reg) (ext? : Option Modifier) : AArch64ElabM Expr := do
  let w ← evalOperandWidth
  let (reg, regW) ← elabRegOrZrW rm (ext?.elim w (·.extendedWidth w))
  let ext ← match ext? with
    | some m => evalExtend m w regW
    | none =>
      unless regW == w do throwErrorAt rm "expected {w} register, got {regW}"
      pure { type := if w == .W64 then .UXTX else .UXTW, amount := .E0 }
  return mkApp (mkConst ``ExtOrImmReg.ext) (mkApp2 (mkConst ``ExtRegExpr.mk) reg (toExpr ext))

/-- Elaborate the flexible source of an add/subtract/compare into an `Expr` of type `ExtOrImmReg` (`_e`
    form) or `ShiftRegExpr w` (`_s` form). -/
def elabArithSrc : ArithSrc → AArch64ElabM Expr
  | .imm c shift?    => elabArithImm c shift?
  | .ext rm ext?     => elabExtendedReg rm ext?
  | .shift rm shift? => elabShiftedReg rm shift? (allowRor := false)

-- ============================================================================
-- Memory Operand Elaboration
-- ============================================================================

/-- The operation constructors of a single-register load/store mnemonic (`ldr`, `strb`, ...). The
    constructors of mnemonics that only exist at one width (`ldrb`, `ldrsw`, ...) take no width argument;
    the others are already applied to the operand width. -/
structure MemOp where
  /-- Scaled unsigned offset, pre/post-indexed and register offset addressing (`LDR`, `STRB`, ...). -/
  scaled : Expr
  /-- Unscaled signed 9-bit offset addressing (`LDUR`, `STURB`, ...). -/
  unscaled : Expr
  /-- Whether `scaled` takes an `AddrOrLit`, that is, whether PC-relative literals are supported. -/
  literal : Bool := false
  /-- Whether literal pool constants (`=imm`) are supported. -/
  pool : Bool := true
  /-- Width of the transfer register, if determined. -/
  width? : Option RegWidth
  /-- Size of the memory access in bytes, by which immediate offsets are scaled, if determined. -/
  scale? : Option Nat

/-- The `MemOp` of a mnemonic that exists at both widths, whose memory access has size `access?` (the
    transfer register width when `none`). -/
def mkMemOp (scaled unscaled : Name) (access? : Option MemWidth := none) (literal := false) :
    AArch64ElabM MemOp := do
  let width? ← evalOperandWidth?
  return { scaled := ← mkAppWidth (mkConst scaled), unscaled := ← mkAppWidth (mkConst unscaled), literal,
           width?, scale? := access?.map (·.bytes) <|> width?.map (·.bytes) }

/-- The `MemOp` of a mnemonic that only exists at width `w`, whose memory access has size `access`. -/
def mkFixedMemOp (w : RegWidth) (access : MemWidth) (scaled unscaled : Name) (literal := false)
    (pool := true) : AArch64ElabM MemOp := do
  requireWidth w
  return { scaled := mkConst scaled, unscaled := mkConst unscaled, literal, pool,
           width? := some w, scale? := some access.bytes }

/-- The transfer register width and access size of a load/store, which validating and scaling a concrete
    immediate offset requires. -/
def MemOp.evalSizes (op : MemOp) : MetaM (RegWidth × Nat) := do
  let (some w, some scale) := (op.width?, op.scale?) | throwError "could not infer operand width"
  return (w, scale)

/-- The operation `scaled rt addr` of a load/store with an `AddrExpr` operand `addr`. -/
def MemOp.mkScaled (op : MemOp) (rt addr : Expr) : Expr :=
  mkApp2 op.scaled rt (if op.literal then mkApp (mkConst ``AddrOrLit.addr) addr else addr)

/-- The `MemOp` of a load mnemonic (`ldr`, `ldur`, and their size suffixes), whose suffix may fix the
    operand width. -/
def elabLoadOp (stx : Syntax) : AArch64ElabM MemOp := withRef stx do
  match (← splitSuffixed stx).2 with
  | ""   => mkMemOp ``Operation.LDR ``Operation.LDUR (literal := true)
  | "b"  => mkFixedMemOp .W32 .W8 ``Operation.LDRB ``Operation.LDURB
  | "h"  => mkFixedMemOp .W32 .W16 ``Operation.LDRH ``Operation.LDURH
  | "sb" => mkMemOp ``Operation.LDRSB ``Operation.LDURSB (access? := some .W8)
  | "sh" => mkMemOp ``Operation.LDRSH ``Operation.LDURSH (access? := some .W16)
  | "sw" => mkFixedMemOp .W64 .W32 ``Operation.LDRSW ``Operation.LDURSW (literal := true) (pool := false)
  | _    => throwError "invalid load mnemonic"

/-- The `MemOp` of a store mnemonic (`str`, `stur`, and their size suffixes), whose suffix may fix the
    operand width. -/
def elabStoreOp (stx : Syntax) : AArch64ElabM MemOp := withRef stx do
  match (← splitSuffixed stx).2 with
  | ""  => mkMemOp ``Operation.STR ``Operation.STUR
  | "b" => mkFixedMemOp .W32 .W8 ``Operation.STRB ``Operation.STURB
  | "h" => mkFixedMemOp .W32 .W16 ``Operation.STRH ``Operation.STURH
  | _   => throwError "invalid store mnemonic"

/-- Build `AddrOff.imm (ImmAddrExpr.mk imm index)`. -/
def mkImmAddrOff (imm : Expr) (index : Option Index) : Expr :=
  mkApp (mkConst ``AddrOff.imm) (mkApp2 (mkConst ``ImmAddrExpr.mk) imm (toExpr index))

/-- Build `AddrExpr.mk base off`. -/
def mkAddrExpr (base off : Expr) : Expr :=
  mkApp2 (mkConst ``AddrExpr.mk) base off

/-- Build `UnscaledAddrExpr.mk base imm`. -/
def mkUnscaledAddrExpr (base imm : Expr) : Expr :=
  mkApp2 (mkConst ``UnscaledAddrExpr.mk) base imm

/-- Reject a writeback to the base register `base` of a load/store that also transfers `rt`. The check is
    only possible when both are concrete registers; antiquotations are left to the assembler. -/
def checkWriteback (rt base : Expr) : MetaM Unit := do
  match gpr? rt, gpr? base with
  | some r, some b => if r == b then throwError "unpredictable: writeback base register is also a transfer register"
  | _, _ => pure ()

/-- Reject identical destination registers in `ldp` (including `xzr`, both being register 31). -/
def checkLdpRegisters (rt1 rt2 : Expr) : MetaM Unit := do
  match regIndex? rt1, regIndex? rt2 with
  | some r1, some r2 => if r1 == r2 then throwError "unpredictable: identical destination registers in ldp instruction"
  | _, _ => pure ()

/-- Build the `AddrExpr` of a pre/post-indexed operand (`[Xn, #imm]!`, `[Xn], #imm`), whose base `Xn` is
    updated and therefore must not be one of the transfer registers `rts`. -/
def mkIndexedAddr (base imm : Expr) (index : Index) (rts : Array Expr) : MetaM Expr := do
  for rt in rts do checkWriteback rt base
  return mkAddrExpr base (mkImmAddrOff imm (some index))

/-- Elaborate a pre/post-indexed immediate offset (signed 9-bit, `[-256, 255]`) into an `Expr` of type
    `ConstExpr`. -/
def elabIndexedOffset (stx : TSyntax `aarch64_const) (mode : String) : TermElabM Expr := withRef stx do
  let `(aarch64_const| $i:aarch64_imm) := stx
    | throwError "pre-indexed / post-indexed offsets must be constant numeric immediates"
  elabImmConst i (checkIndexedOffset mode)

/-- Elaborate the immediate offset of `[Xn, #imm]` into an `Expr` of type `ConstExpr`, and whether it
    requires the unscaled encoding (`ldur`, `stur`, ...) for being negative or not a multiple of the access
    size. Offsets may be unsigned scaled (`[0, 4095 * scale]`) or signed 9-bit (`[-256, 255]`); offsets
    that are not concrete integers (symbols, relocations, antiquotations) are assumed to be scaled. -/
def elabScaledOffset (op : MemOp) (stx : TSyntax `aarch64_const) : AArch64ElabM (Expr × Bool) := withRef stx do
  let `(aarch64_const| $i:aarch64_imm) := stx | return (← elabConst stx, false)
  if i matches `(aarch64_imm| #❰ $_ ❱) then return (← elabImmConst i, false)
  let v ← evalImm64 i
  let (w, scale) ← op.evalSizes
  ofExcept (checkLoadStoreOffset w v (allowUnscaled := true) scale)
  return (toExpr (ConstExpr.int64 v), v.toInt < 0 || v.toInt % scale != 0)

/-- Elaborate the register offset (`Rm{, extend #amount}`) of a `[Xn, Rm, ...]` operand into an `Expr` of
    type `AddrOff`. An antiquoted index register of undetermined width is a `Wm` for `uxtw`/`sxtw`, an `Xm`
    otherwise. -/
def elabRegOffset (op : MemOp) (rm : TSyntax `aarch64_reg) (mod? : Option (TSyntax `aarch64_modifier)) :
    AArch64ElabM Expr := do
  let m? ← mod?.mapM (evalModifier ·)
  let default := match m?.map (·.name) with
    | some "uxtw" | some "sxtw" => RegWidth.W32
    | _                         => .W64
  let (reg, regW) ← elabRegOrZrW rm default
  let ext ← match m? with
    | none   => pure { type := if regW == .W64 then .UXTX else .UXTW, amount := .E0 }
    | some m => withRef m.ref do
      let (w, scale) ← op.evalSizes
      pure { type := ← ofExcept (getMemExtendType m.name regW),
             amount := ← ofExcept (getMemExtendAmount w (← m.evalAmount) scale) : MemExtend }
  return mkApp (mkConst ``AddrOff.reg) (mkApp2 (mkConst ``MemExtRegExpr.mk) reg (toExpr ext))

/-- Elaborate the memory operand of a single-register load/store `op` transferring `rt` into the `Expr`
    of the operation. An unindexed immediate offset that is negative or misaligned selects the unscaled
    encoding. -/
def elabMemAccess (op : MemOp) (rt : Expr) (stx : TSyntax `aarch64_mem) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    let base ← elabBaseReg b
    let (imm, unscaled) := (← off?.mapM (elabScaledOffset op)).getD (zeroOffset, false)
    if unscaled then return mkApp2 op.unscaled rt (mkUnscaledAddrExpr base imm)
    return op.mkScaled rt (mkAddrExpr base (mkImmAddrOff imm none))
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]!) =>
    let base ← elabBaseReg b
    let imm ← elabIndexedOffset off "pre-indexed"
    return op.mkScaled rt (← mkIndexedAddr base imm .Pre #[rt])
  | `(aarch64_mem| [$b:aarch64_reg], $off:aarch64_const) =>
    let base ← elabBaseReg b
    let imm ← elabIndexedOffset off "post-indexed"
    return op.mkScaled rt (← mkIndexedAddr base imm .Post #[rt])
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg $[, $mod?:aarch64_modifier]?]) =>
    let base ← elabBaseReg b
    return op.mkScaled rt (mkAddrExpr base (← elabRegOffset op rm mod?))
  | `(aarch64_mem| ❰ $t ❱) =>
    return op.mkScaled rt (← elabAntiquot t (mkConst ``AddrExpr))
  | _ => throwError "invalid memory operand"

/-- Elaborate the memory operand of an unscaled load/store (`[Xn]`, `[Xn, #simm9]`, or `❰t❱`) into an
    `Expr` of type `UnscaledAddrExpr`. -/
def elabUnscaledMem (stx : TSyntax `aarch64_mem) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    let base ← elabBaseReg b
    let imm := (← off?.mapM (elabConst · checkUnscaledOffset)).getD zeroOffset
    return mkUnscaledAddrExpr base imm
  | `(aarch64_mem| [$_:aarch64_reg, $_:aarch64_reg $[, $_]?]) =>
    throwError "expected immediate offset in unscaled address operand"
  | `(aarch64_mem| ❰ $t ❱) =>
    elabAntiquot t (mkConst ``UnscaledAddrExpr)
  | _ => throwError "invalid unscaled address operand"

/-- Elaborate the immediate offset of a register-pair load/store with accesses of width `w?` (7-bit signed
    and scaled) into an `Expr` of type `ConstExpr`. -/
def elabPairOffset (w? : Option RegWidth) (stx : TSyntax `aarch64_const) : TermElabM Expr := withRef stx do
  let `(aarch64_const| $i:aarch64_imm) := stx | throwError "pair offsets must be constant numeric immediates"
  match w? with
  | some w => elabImmConst i (checkPairOffset w)
  | none   => elabImmConst i

/-- Elaborate the memory operand of a register-pair load/store with accesses of width `w?`, transferring
    `rt1` and `rt2`, into an `Expr` of type `AddrExpr`. -/
def elabPairMem (stx : TSyntax `aarch64_mem) (w? : Option RegWidth) (rt1 rt2 : Expr) : AArch64ElabM Expr :=
    withRef stx do
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    let base ← elabBaseReg b
    let imm := (← off?.mapM (elabPairOffset w? ·)).getD zeroOffset
    return mkAddrExpr base (mkImmAddrOff imm none)
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]!) =>
    let base ← elabBaseReg b
    mkIndexedAddr base (← elabPairOffset w? off) .Pre #[rt1, rt2]
  | `(aarch64_mem| [$b:aarch64_reg], $off:aarch64_const) =>
    let base ← elabBaseReg b
    mkIndexedAddr base (← elabPairOffset w? off) .Post #[rt1, rt2]
  | `(aarch64_mem| [$_:aarch64_reg, $_:aarch64_reg $[, $_]?]) =>
    throwError "register offsets are not supported for ldp/stp instructions"
  | `(aarch64_mem| ❰ $t ❱) =>
    elabAntiquot t (mkConst ``AddrExpr)
  | _ => throwError "invalid memory operand"

/-- Elaborate a PC-relative literal load source (`=expr` or label) of a load `op` into an `Expr` of type
    `Literal`. -/
def elabLit (op : MemOp) (stx : TSyntax `aarch64_lit) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_lit| = $c:aarch64_const) =>
    unless op.pool do throwError "literal pool (=expr) is not supported for ldrsw"
    let expr ← elabConst c (checkLiteralPoolImmediate (op.width?.getD .W64))
    return mkApp (mkConst ``Literal.pool) (mkApp (mkConst ``LitPoolExpr.mk) expr)
  | `(aarch64_lit| $lbl:aarch64_ident) =>
    return toExpr (_root_.Literal.addr { label := ← getAsmIdent lbl })
  | _ => throwError "invalid literal operand"

/-- Elaborate a load `op` of `rt` from a PC-relative literal into the `Expr` of the operation. -/
def elabLitAccess (op : MemOp) (rt : Expr) (stx : TSyntax `aarch64_lit) : TermElabM Expr := withRef stx do
  unless op.literal do throwError "literal operands are only supported by ldr and ldrsw"
  return mkApp2 op.scaled rt (mkApp (mkConst ``AddrOrLit.lit) (← elabLit op stx))

-- ============================================================================
-- Mnemonic Category Elaborators
-- ============================================================================

/-- The `Operation` constructor of an `aarch64_pair_op`, applied to the operand width when it takes one,
    together with the width of each memory access (if determined) and whether it is a load. -/
def elabPairOp (stx : TSyntax `aarch64_pair_op) : AArch64ElabM (Expr × Option RegWidth × Bool) := withRef stx do
  match stx with
  | `(aarch64_pair_op| ldp)   => return (← mkAppWidth (mkConst ``Operation.LDP), ← evalOperandWidth?, true)
  | `(aarch64_pair_op| ldpsw) => requireWidth .W64; return (mkConst ``Operation.LDPSW, some .W32, true)
  | `(aarch64_pair_op| stp)   => return (← mkAppWidth (mkConst ``Operation.STP), ← evalOperandWidth?, false)
  | _ => throwError "invalid register-pair mnemonic"

/-- The `Operation` constructor of an `aarch64_arith_op` in the extended-register/immediate (`ext`) or
    shifted-register form, and whether its destination register 31 is `sp` rather than `xzr`. -/
def elabArithOp (stx : TSyntax `aarch64_arith_op) (ext : Bool) : TermElabM (Expr × Bool) := withRef stx do
  match ← splitSuffixed stx, ext with
  | ("add", ""),  true  => pure (mkConst ``Operation.ADD_e,  true)
  | ("add", "s"), true  => pure (mkConst ``Operation.ADDS_e, false)
  | ("sub", ""),  true  => pure (mkConst ``Operation.SUB_e,  true)
  | ("sub", "s"), true  => pure (mkConst ``Operation.SUBS_e, false)
  | ("add", ""),  false => pure (mkConst ``Operation.ADD_s,  false)
  | ("add", "s"), false => pure (mkConst ``Operation.ADDS_s, false)
  | ("sub", ""),  false => pure (mkConst ``Operation.SUB_s,  false)
  | ("sub", "s"), false => pure (mkConst ``Operation.SUBS_s, false)
  | _, _ => throwError "invalid add/subtract mnemonic"

/-- The `Operation` constructor of an `aarch64_cmp_op` in the extended-register/immediate (`ext`) or
    shifted-register form (applied to `xzr` as destination). -/
def elabCmpOp (stx : TSyntax `aarch64_cmp_op) (ext : Bool) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_cmp_op| cmp) => pure (mkConst (if ext then ``Operation.SUBS_e else ``Operation.SUBS_s))
  | `(aarch64_cmp_op| cmn) => pure (mkConst (if ext then ``Operation.ADDS_e else ``Operation.ADDS_s))
  | _ => throwError "invalid compare mnemonic"

/-- The `Operation` constructor of an `aarch64_unary_op` (applied to `xzr` as first source), and whether
    its shift may be `ror`. -/
def elabUnaryOp (stx : TSyntax `aarch64_unary_op) : TermElabM (Expr × Bool) := withRef stx do
  match stx with
  | `(aarch64_unary_op| neg)  => pure (mkConst ``Operation.SUB_s,  false)
  | `(aarch64_unary_op| negs) => pure (mkConst ``Operation.SUBS_s, false)
  | `(aarch64_unary_op| mvn)  => pure (mkConst ``Operation.ORN_s,  true)
  | _ => throwError "invalid negate/invert mnemonic"

/-- The bitmask immediate (`_i` form) `Operation` constructor of an `aarch64_logic_op`, and whether its
    destination register 31 is `sp` rather than `xzr`. -/
def elabLogicImmOp (stx : TSyntax `aarch64_logic_op) : TermElabM (Expr × Bool) := withRef stx do
  match stx with
  | `(aarch64_logic_op| and)  => pure (mkConst ``Operation.AND_i,  true)
  | `(aarch64_logic_op| ands) => pure (mkConst ``Operation.ANDS_i, false)
  | `(aarch64_logic_op| orr)  => pure (mkConst ``Operation.ORR_i,  true)
  | `(aarch64_logic_op| eor)  => pure (mkConst ``Operation.EOR_i,  true)
  | _ => throwError "expected register"

/-- The shifted-register (`_s` form) `Operation` constructor of an `aarch64_logic_op`. -/
def elabLogicShiftOp (stx : TSyntax `aarch64_logic_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_logic_op| and)  => pure (mkConst ``Operation.AND_s)
  | `(aarch64_logic_op| ands) => pure (mkConst ``Operation.ANDS_s)
  | `(aarch64_logic_op| orr)  => pure (mkConst ``Operation.ORR_s)
  | `(aarch64_logic_op| orn)  => pure (mkConst ``Operation.ORN_s)
  | `(aarch64_logic_op| eor)  => pure (mkConst ``Operation.EOR_s)
  | `(aarch64_logic_op| eon)  => pure (mkConst ``Operation.EON_s)
  | `(aarch64_logic_op| bic)  => pure (mkConst ``Operation.BIC_s)
  | `(aarch64_logic_op| bics) => pure (mkConst ``Operation.BICS_s)
  | _ => throwError "invalid logical mnemonic"

/-- Elaborate the operation of an `aarch64_rrr_op` on the registers `rd`, `rn`, `rm`. -/
def elabRrrOp (stx : TSyntax `aarch64_rrr_op) (rd rn rm : Expr) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_rrr_op| adc)   => mkAppWidth (mkConst ``Operation.ADC)  #[rd, rn, rm]
  | `(aarch64_rrr_op| adcs)  => mkAppWidth (mkConst ``Operation.ADCS) #[rd, rn, rm]
  | `(aarch64_rrr_op| sbc)   => mkAppWidth (mkConst ``Operation.SBC)  #[rd, rn, rm]
  | `(aarch64_rrr_op| sbcs)  => mkAppWidth (mkConst ``Operation.SBCS) #[rd, rn, rm]
  | `(aarch64_rrr_op| sdiv)  => mkAppWidth (mkConst ``Operation.SDIV) #[rd, rn, rm]
  | `(aarch64_rrr_op| udiv)  => mkAppWidth (mkConst ``Operation.UDIV) #[rd, rn, rm]
  | `(aarch64_rrr_op| mul)   => mkAppWidth (mkConst ``Operation.MADD) #[rd, rn, rm, ← mkXzr]
  | `(aarch64_rrr_op| mneg)  => mkAppWidth (mkConst ``Operation.MSUB) #[rd, rn, rm, ← mkXzr]
  | `(aarch64_rrr_op| smulh) => requireWidth .W64; return mkApp3 (mkConst ``Operation.SMULH) rd rn rm
  | `(aarch64_rrr_op| umulh) => requireWidth .W64; return mkApp3 (mkConst ``Operation.UMULH) rd rn rm
  | `(aarch64_rrr_op| lslv)  => mkAppWidth (mkConst ``Operation.LSLV) #[rd, rn, rm]
  | `(aarch64_rrr_op| lsrv)  => mkAppWidth (mkConst ``Operation.LSRV) #[rd, rn, rm]
  | `(aarch64_rrr_op| asrv)  => mkAppWidth (mkConst ``Operation.ASRV) #[rd, rn, rm]
  | `(aarch64_rrr_op| rorv)  => mkAppWidth (mkConst ``Operation.RORV) #[rd, rn, rm]
  | _ => throwError "invalid three-register mnemonic"

/-- The `Operation` constructor of an `aarch64_madd_op`. -/
def elabMaddOp (stx : TSyntax `aarch64_madd_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_madd_op| madd) => pure (mkConst ``Operation.MADD)
  | `(aarch64_madd_op| msub) => pure (mkConst ``Operation.MSUB)
  | _ => throwError "invalid multiply-accumulate mnemonic"

/-- The `Operation` constructor of an `aarch64_maddl_op`. -/
def elabMaddlOp (stx : TSyntax `aarch64_maddl_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_maddl_op| smaddl) => pure (mkConst ``Operation.SMADDL)
  | `(aarch64_maddl_op| umaddl) => pure (mkConst ``Operation.UMADDL)
  | `(aarch64_maddl_op| smsubl) => pure (mkConst ``Operation.SMSUBL)
  | `(aarch64_maddl_op| umsubl) => pure (mkConst ``Operation.UMSUBL)
  | _ => throwError "invalid widening multiply-accumulate mnemonic"

/-- The multiply-accumulate `Operation` constructor of an `aarch64_mull_op` (the accumulator is `xzr`). -/
def elabMullOp (stx : TSyntax `aarch64_mull_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_mull_op| smull)  => pure (mkConst ``Operation.SMADDL)
  | `(aarch64_mull_op| umull)  => pure (mkConst ``Operation.UMADDL)
  | `(aarch64_mull_op| smnegl) => pure (mkConst ``Operation.SMSUBL)
  | `(aarch64_mull_op| umnegl) => pure (mkConst ``Operation.UMSUBL)
  | _ => throwError "invalid widening multiply mnemonic"

/-- Elaborate the operation of an `aarch64_rr_op` on the registers `rd`, `rn`. -/
def elabRrOp (stx : TSyntax `aarch64_rr_op) (rd rn : Expr) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_rr_op| clz)   => mkAppWidth (mkConst ``Operation.CLZ)   #[rd, rn]
  | `(aarch64_rr_op| cls)   => mkAppWidth (mkConst ``Operation.CLS)   #[rd, rn]
  | `(aarch64_rr_op| rbit)  => mkAppWidth (mkConst ``Operation.RBIT)  #[rd, rn]
  | `(aarch64_rr_op| rev)   => mkAppWidth (mkConst ``Operation.REV)   #[rd, rn]
  | `(aarch64_rr_op| rev16) => mkAppWidth (mkConst ``Operation.REV16) #[rd, rn]
  | `(aarch64_rr_op| rev32) => requireWidth .W64; return mkApp2 (mkConst ``Operation.REV32) rd rn
  | `(aarch64_rr_op| rev64) => requireWidth .W64; mkAppWidth (mkConst ``Operation.REV) #[rd, rn]
  | _ => throwError "invalid bit manipulation mnemonic"

/-- The bitfield-move `Operation` constructor of an `aarch64_extend_op` and its `imms` (the top bit of the
    source field); `sxtw`/`uxtw` require a 64-bit destination. -/
def elabExtendOp (stx : TSyntax `aarch64_extend_op) : AArch64ElabM (Expr × Nat) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  let mk ← match stem with
    | "sxt" => pure (mkConst ``Operation.SBFM)
    | "uxt" => pure (mkConst ``Operation.UBFM)
    | _     => throwError "invalid extension mnemonic"
  match sfx with
  | "b" => pure (mk, 7)
  | "h" => pure (mk, 15)
  | "w" => requireWidth .W64; pure (mk, 31)
  | _   => throwError "invalid extension width '{sfx}'"

/-- The register-amount `Operation` constructor of an `aarch64_shift_op`. -/
def elabShiftRegOp (stx : TSyntax `aarch64_shift_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_shift_op| lsl) => pure (mkConst ``Operation.LSLV)
  | `(aarch64_shift_op| lsr) => pure (mkConst ``Operation.LSRV)
  | `(aarch64_shift_op| asr) => pure (mkConst ``Operation.ASRV)
  | `(aarch64_shift_op| ror) => pure (mkConst ``Operation.RORV)
  | _ => throwError "invalid shift mnemonic"

/-- `immr` field of the `UBFM` encoding of `lsl Rd, Rn, #n`. -/
def lslImmr (w : RegWidth) (n : Nat) : Nat := (w.bits - n) % w.bits

/-- `imms` field of the `UBFM` encoding of `lsl Rd, Rn, #n`. -/
def lslImms (w : RegWidth) (n : Nat) : Nat := w.bits - 1 - n

/-- Elaborate `lsl Rd, Rn, #n` at width `w`, the alias of `ubfm Rd, Rn, #((w - n) % w), #(w - 1 - n)`. -/
def elabLslImm (w : RegWidth) (rd rn : Expr) (stx : TSyntax `aarch64_imm) : AArch64ElabM Expr := withRef stx do
  let (immr, imms) ← match stx with
    | `(aarch64_imm| #❰ $t ❱) =>
      let n ← elabAntiquot t (mkConst ``Nat)
      pure (mkApp2 (mkConst ``lslImmr) (toExpr w) n, mkApp2 (mkConst ``lslImms) (toExpr w) n)
    | _ =>
      let n ← evalImmNat stx
      ofExcept (checkBitWidthBound "shift" w n)
      pure (toExpr (lslImmr w n), toExpr (lslImms w n))
  mkAppWidth (mkConst ``Operation.UBFM) #[rd, rn, immr, imms]

/-- Elaborate the operation of an `aarch64_shift_op` by an immediate on the registers `rd`, `rn`. Its
    bitfield encoding depends on the operand width, which must be determined. -/
def elabShiftImmOp (stx : TSyntax `aarch64_shift_op) (rd rn : Expr) (i : TSyntax `aarch64_imm) :
    AArch64ElabM Expr := withRef stx do
  let w ← evalOperandWidth
  if stx matches `(aarch64_shift_op| lsl) then return ← elabLslImm w rd rn i
  let n ← elabImmNat i (checkBitWidthBound "shift" w)
  match stx with
  | `(aarch64_shift_op| lsr) => mkAppWidth (mkConst ``Operation.UBFM) #[rd, rn, n, toExpr (w.bits - 1)]
  | `(aarch64_shift_op| asr) => mkAppWidth (mkConst ``Operation.SBFM) #[rd, rn, n, toExpr (w.bits - 1)]
  | `(aarch64_shift_op| ror) => mkAppWidth (mkConst ``Operation.EXTR) #[rd, rn, rn, n]
  | _ => throwError "invalid shift mnemonic"

/-- How the two immediates of a bitfield mnemonic encode `immr` and `imms`. -/
inductive BitfieldForm
  /-- `(immr, imms)` as written. -/
  | raw
  /-- `(lsb, width)` of an extracted field. -/
  | extract
  /-- `(lsb, width)` of an inserted field. -/
  | insert

/-- The `Operation` constructor of an `aarch64_bitfield_op` and its immediate encoding. -/
def elabBitfieldOp (stx : TSyntax `aarch64_bitfield_op) : TermElabM (Expr × BitfieldForm) := withRef stx do
  match stx with
  | `(aarch64_bitfield_op| bfm)   => pure (mkConst ``Operation.BFM,  .raw)
  | `(aarch64_bitfield_op| sbfm)  => pure (mkConst ``Operation.SBFM, .raw)
  | `(aarch64_bitfield_op| ubfm)  => pure (mkConst ``Operation.UBFM, .raw)
  | `(aarch64_bitfield_op| sbfx)  => pure (mkConst ``Operation.SBFM, .extract)
  | `(aarch64_bitfield_op| ubfx)  => pure (mkConst ``Operation.UBFM, .extract)
  | `(aarch64_bitfield_op| bfxil) => pure (mkConst ``Operation.BFM,  .extract)
  | `(aarch64_bitfield_op| bfi)   => pure (mkConst ``Operation.BFM,  .insert)
  | `(aarch64_bitfield_op| sbfiz) => pure (mkConst ``Operation.SBFM, .insert)
  | `(aarch64_bitfield_op| ubfiz) => pure (mkConst ``Operation.UBFM, .insert)
  | _ => throwError "invalid bitfield mnemonic"

/-- Elaborate the two immediates of a bitfield mnemonic of the given form into `Expr`s of type `Nat` for
    its `immr` and `imms` fields. Only the raw form admits antiquotations. -/
def elabBitfieldImms (form : BitfieldForm) (a b : TSyntax `aarch64_imm) : AArch64ElabM (Expr × Expr) := do
  match form with
  | .raw =>
    let w ← evalBoundsWidth
    return (← elabImmNat a (checkBitWidthBound "bitfield" w), ← elabImmNat b (checkBitWidthBound "bitfield" w))
  | .extract =>
    let (w, a, b) := (← evalBoundsWidth, ← evalImmNat a, ← evalImmNat b)
    ofExcept (checkBitfieldBounds "bitfield extract" w a b)
    return (toExpr a, toExpr (a + b - 1))
  | .insert =>
    let (w, a, b) := (← evalOperandWidth, ← evalImmNat a, ← evalImmNat b)
    ofExcept (checkBitfieldBounds "bitfield insert" w a b)
    return (toExpr ((w.bits - a) % w.bits), toExpr (b - 1))

/-- The `Operation` constructor of an `aarch64_csel_op`. -/
def elabCselOp (stx : TSyntax `aarch64_csel_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_csel_op| csel)  => pure (mkConst ``Operation.CSEL)
  | `(aarch64_csel_op| csinc) => pure (mkConst ``Operation.CSINC)
  | `(aarch64_csel_op| csinv) => pure (mkConst ``Operation.CSINV)
  | `(aarch64_csel_op| csneg) => pure (mkConst ``Operation.CSNEG)
  | _ => throwError "invalid conditional select mnemonic"

/-- The conditional select `Operation` constructor of an `aarch64_cinc_op` (applied with the inverted
    condition and both sources equal). -/
def elabCincOp (stx : TSyntax `aarch64_cinc_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_cinc_op| cinc) => pure (mkConst ``Operation.CSINC)
  | `(aarch64_cinc_op| cinv) => pure (mkConst ``Operation.CSINV)
  | `(aarch64_cinc_op| cneg) => pure (mkConst ``Operation.CSNEG)
  | _ => throwError "invalid conditional increment mnemonic"

/-- The conditional select `Operation` constructor of an `aarch64_cset_op` (applied with the inverted
    condition and `xzr` sources). -/
def elabCsetOp (stx : TSyntax `aarch64_cset_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_cset_op| cset)  => pure (mkConst ``Operation.CSINC)
  | `(aarch64_cset_op| csetm) => pure (mkConst ``Operation.CSINV)
  | _ => throwError "invalid conditional set mnemonic"

/-- The register and immediate `Operation` constructors of an `aarch64_ccmp_op`. -/
def elabCcmpOp (stx : TSyntax `aarch64_ccmp_op) : TermElabM (Expr × Expr) := withRef stx do
  match stx with
  | `(aarch64_ccmp_op| ccmp) => pure (mkConst ``Operation.CCMP_reg, mkConst ``Operation.CCMP_imm)
  | `(aarch64_ccmp_op| ccmn) => pure (mkConst ``Operation.CCMN_reg, mkConst ``Operation.CCMN_imm)
  | _ => throwError "invalid conditional compare mnemonic"

/-- The `Operation` constructor of an `aarch64_movw_op`. -/
def elabMovwOp (stx : TSyntax `aarch64_movw_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_movw_op| movz) => pure (mkConst ``Operation.MOVZ)
  | `(aarch64_movw_op| movk) => pure (mkConst ``Operation.MOVK)
  | `(aarch64_movw_op| movn) => pure (mkConst ``Operation.MOVN)
  | _ => throwError "invalid move wide mnemonic"

/-- The `Operation` constructor of an `aarch64_adr_op` and its offset validator. -/
def elabAdrOp (stx : TSyntax `aarch64_adr_op) : TermElabM (Expr × (Int64 → Except String Unit)) := withRef stx do
  match stx with
  | `(aarch64_adr_op| adr)  => pure (mkConst ``Operation.ADR,  checkAdrOffset)
  | `(aarch64_adr_op| adrp) => pure (mkConst ``Operation.ADRP, checkAdrpOffset)
  | _ => throwError "invalid address mnemonic"

/-- The `Operation` constructor of an `aarch64_b_op`. -/
def elabBOp (stx : TSyntax `aarch64_b_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_b_op| b)  => pure (mkConst ``Operation.B)
  | `(aarch64_b_op| bl) => pure (mkConst ``Operation.BL)
  | _ => throwError "invalid branch mnemonic"

/-- The `Operation` constructor of an `aarch64_br_op`. -/
def elabBrOp (stx : TSyntax `aarch64_br_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_br_op| br)  => pure (mkConst ``Operation.BR)
  | `(aarch64_br_op| blr) => pure (mkConst ``Operation.BLR)
  | _ => throwError "invalid indirect branch mnemonic"

/-- The mnemonic (for diagnostics) and `Operation` constructor of an `aarch64_cbz_op`. -/
def elabCbzOp (stx : TSyntax `aarch64_cbz_op) : TermElabM (String × Expr) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match sfx with
  | "z"  => pure (stem ++ sfx, mkConst ``Operation.CBZ)
  | "nz" => pure (stem ++ sfx, mkConst ``Operation.CBNZ)
  | _    => throwError "invalid compare-and-branch mnemonic"

/-- The mnemonic (for diagnostics) and `Operation` constructor of an `aarch64_tbz_op`. -/
def elabTbzOp (stx : TSyntax `aarch64_tbz_op) : TermElabM (String × Expr) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match sfx with
  | "z"  => pure (stem ++ sfx, mkConst ``Operation.TBZ)
  | "nz" => pure (stem ++ sfx, mkConst ``Operation.TBNZ)
  | _    => throwError "invalid test-bit-and-branch mnemonic"

-- ============================================================================
-- Register or Constant Antiquotations
-- ============================================================================

/-- The term `t` if `alt` is the register parse of an antiquotation `❰t❱` that may also be a constant
    expression: a flexible source `❰t❱{, modifier}` or a register offset `[Xn, ❰t❱{, modifier}]`. -/
def regAntiquot? (alt : Syntax) : Option Term := do
  let reg ← srcReg? ⟨alt⟩ <|> indexReg? ⟨alt⟩
  let `(aarch64_reg| ❰ $t ❱) := reg | none
  return t
where
  srcReg? (alt : TSyntax `aarch64_src) : Option (TSyntax `aarch64_reg) := do
    let `(aarch64_src| $reg:aarch64_reg $[, $_]?) := alt | none
    return reg
  indexReg? (alt : TSyntax `aarch64_mem) : Option (TSyntax `aarch64_reg) := do
    let `(aarch64_mem| [$_:aarch64_reg, $reg:aarch64_reg $[, $_]?]) := alt | none
    return reg

/-- Resolve the parser's `choice` between the register parse `reg` and the constant expression parse
    `const` of an antiquotation `❰t❱` by the type of `t`, elaborated without expected type: a register if
    it is a `RegOrZr w` or a `RegOrSp w`, a constant expression otherwise. In the chosen parse, `t` is
    replaced by its elaborated value, so that it is not elaborated again. -/
def resolveRegOrConst (t : Term) (reg const : Syntax) : TermElabM Syntax := do
  let e ← withoutErrToSorry <| withSynthesize <| elabTerm t none
  let alt := match ← whnfR (← inferType e) with
    | .app (.const ``RegOrZr _) _ | .app (.const ``RegOrSp _) _ => reg
    | _ => const
  let some range := t.raw.getRange? | return alt
  let e ← withRef t <| exprToSyntax e
  alt.replaceM fun s => return if s.getRange? == some range then some e else none

/-- Resolve `stx` if it is the parser's `choice` between a register and a constant expression parse of an
    antiquotation; other syntax, including the `choice` nodes of overloaded Lean notation, is left alone. -/
def resolveRegOrConstChoice (stx : Syntax) : TermElabM (Option Syntax) := do
  let .node _ `choice #[a, b] := stx | return none
  match regAntiquot? a, regAntiquot? b with
  | some t, none => return some (← resolveRegOrConst t a b)
  | none, some t => return some (← resolveRegOrConst t b a)
  | _, _         => return none

-- ============================================================================
-- Instruction Elaboration
-- ============================================================================

/-- Elaborate the register move `mov Rd, Rn`: an alias of `add Rd, Rn, #0` if `sp` is involved, of
    `orr Rd, xzr, Rn` otherwise. -/
def elabMovReg (rd rn : TSyntax `aarch64_reg) : AArch64ElabM Expr := do
  if isSpSyntax rd || isSpSyntax rn then
    let imm : ExtOrImmReg := .imm { imm := 0, shift := .S0 }
    return ← mkInstr (← mkAppWidth (mkConst ``Operation.ADD_e) #[← elabRegOrSp rd, ← elabRegOrSp rn, toExpr imm])
  let rd ← elabRegOrZr rd
  let rn ← mkAppWidth (mkConst ``ShiftRegExpr.mk) #[← elabRegOrZr rn, toExpr (0 : Int64), toExpr ShiftType.LSL]
  mkInstr (← mkAppWidth (mkConst ``Operation.ORR_s) #[rd, ← mkXzr, rn])

/-- Evaluate `mov Rd, #imm` with a concrete destination: a single `movz`/`movn`, or `orr Rd, xzr, #imm`
    for `sp` destinations and immediates that no move wide can produce. -/
def evalMovImm (rd : TSyntax `aarch64_reg) (i : TSyntax `aarch64_imm) : TermElabM Instr := do
  let ⟨w, r⟩ ← evalAnyReg rd
  let imm ← evalImm64 i
  if let (false, some (inv, imm16, shift)) := (r.isSp, tryMovzOrMovn w (BitVec.ofInt w.bits imm.toInt)) then
    let rd : RegOrZr w := .low (← r.toXRegOrXzrM) w
    return ⟨w, if inv then .MOVN rd imm16 shift else .MOVZ rd imm16 shift⟩
  unless checkLogicalImmediate w imm matches .ok _ do
    throwErrorAt i "immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence)"
  return ⟨w, .ORR_i (← r.toRegOrSpM) (.low .XZR w) imm⟩

/-- Elaborate `mov Rd, #imm` (see `evalMovImm`). An antiquoted destination is a `RegOrZr w`, so the immediate
    must be producible by a single `movz`/`movn`. -/
def elabMovImm (rd : TSyntax `aarch64_reg) (i : TSyntax `aarch64_imm) : AArch64ElabM Expr := do
  let `(aarch64_reg| ❰ $_ ❱) := rd | return toExpr (← evalMovImm rd i)
  let rd ← elabRegOrZr rd
  let w ← evalOperandWidth
  let some (inv, imm16, shift) := tryMovzOrMovn w (BitVec.ofInt w.bits (← evalImm64 i).toInt)
    | throwErrorAt i "immediate cannot be moved into an antiquoted register by a single movz/movn"
  let mk := mkConst (if inv then ``Operation.MOVN else ``Operation.MOVZ)
  mkInstr (← mkAppWidth mk #[rd, toExpr (ConstExpr.int64 imm16), toExpr shift])

/-- Elaborate an `aarch64_instr` syntax node into a `Lean.Expr` of type `Instr`. The registers determining
    the operand width are elaborated before the mnemonic, so that a mnemonic that only exists at one width
    is reported against the registers. -/
def elabInstr (stx : TSyntax `aarch64_instr) : AArch64ElabM Expr := withRef stx do
  match stx with
  | `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $m:aarch64_mem) =>
    let rt ← elabRegOrZr rt
    let op ← elabLoadOp op
    mkInstr (← elabMemAccess op rt m)
  | `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $lit:aarch64_lit) =>
    let rt ← elabRegOrZr rt
    let op ← elabLoadOp op
    mkInstr (← elabLitAccess op rt lit)
  | `(aarch64_instr| $op:aarch64_ldur_op $rt:aarch64_reg, $m:aarch64_mem) =>
    let rt ← elabRegOrZr rt
    let op ← elabLoadOp op
    mkInstr (mkApp2 op.unscaled rt (← elabUnscaledMem m))
  | `(aarch64_instr| $op:aarch64_str_op $rt:aarch64_reg, $m:aarch64_mem) =>
    let rt ← elabRegOrZr rt
    let op ← elabStoreOp op
    mkInstr (← elabMemAccess op rt m)
  | `(aarch64_instr| $op:aarch64_stur_op $rt:aarch64_reg, $m:aarch64_mem) =>
    let rt ← elabRegOrZr rt
    let op ← elabStoreOp op
    mkInstr (mkApp2 op.unscaled rt (← elabUnscaledMem m))
  | `(aarch64_instr| $op:aarch64_pair_op $rt1:aarch64_reg, $rt2:aarch64_reg, $m:aarch64_mem) =>
    let rt1 ← elabRegOrZr rt1
    let rt2 ← elabRegOrZr rt2
    let (mk, accessW?, isLoad) ← elabPairOp op
    if isLoad then withRef stx <| checkLdpRegisters rt1 rt2
    mkInstr (mkApp3 mk rt1 rt2 (← elabPairMem m accessW? rt1 rt2))
  | `(aarch64_instr| $op:aarch64_arith_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src) =>
    let src ← evalArithSrc src (isSpSyntax rd || isSpSyntax rn)
    let (mk, rdSp) ← elabArithOp op src.isExt
    let rd ← elabReg rd rdSp
    let rn ← elabReg rn src.isExt
    mkInstr (← mkAppWidth mk #[rd, rn, ← elabArithSrc src])
  | `(aarch64_instr| $op:aarch64_cmp_op $rn:aarch64_reg, $src:aarch64_src) =>
    let src ← evalArithSrc src (isSpSyntax rn)
    let mk ← elabCmpOp op src.isExt
    let rn ← elabReg rn src.isExt
    mkInstr (← mkAppWidth mk #[← mkXzr, rn, ← elabArithSrc src])
  | `(aarch64_instr| $op:aarch64_unary_op $rd:aarch64_reg, $rm:aarch64_reg $[, $mod?]?) =>
    let (mk, allowRor) ← elabUnaryOp op
    let rd ← elabRegOrZr rd
    let src ← elabShiftedReg rm (← mod?.mapM (evalModifier ·)) allowRor
    mkInstr (← mkAppWidth mk #[rd, ← mkXzr, src])
  | `(aarch64_instr| $op:aarch64_logic_op $rd:aarch64_reg, $rn:aarch64_reg, $c:aarch64_const $[, $mod?]?) =>
    let (mk, rdSp) ← elabLogicImmOp op
    let rd ← elabReg rd rdSp
    let rn ← elabRegOrZr rn
    mkInstr (← mkAppWidth mk #[rd, rn, ← elabLogicalImm c mod?])
  | `(aarch64_instr| $op:aarch64_logic_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg $[, $mod?]?) =>
    let mk ← elabLogicShiftOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let src ← elabShiftedReg rm (← mod?.mapM (evalModifier ·)) (allowRor := true)
    mkInstr (← mkAppWidth mk #[rd, rn, src])
  | `(aarch64_instr| tst $rn:aarch64_reg, $c:aarch64_const $[, $mod?]?) =>
    let rn ← elabRegOrZr rn
    mkInstr (← mkAppWidth (mkConst ``Operation.ANDS_i) #[← mkXzr, rn, ← elabLogicalImm c mod?])
  | `(aarch64_instr| tst $rn:aarch64_reg, $rm:aarch64_reg $[, $mod?]?) =>
    let rn ← elabRegOrZr rn
    let src ← elabShiftedReg rm (← mod?.mapM (evalModifier ·)) (allowRor := true)
    mkInstr (← mkAppWidth (mkConst ``Operation.ANDS_s) #[← mkXzr, rn, src])
  | `(aarch64_instr| $op:aarch64_rrr_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg) =>
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    mkInstr (← elabRrrOp op rd rn rm)
  | `(aarch64_instr| $op:aarch64_madd_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg) =>
    let mk ← elabMaddOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    let ra ← elabRegOrZr ra
    mkInstr (← mkAppWidth mk #[rd, rn, rm, ra])
  | `(aarch64_instr| $op:aarch64_maddl_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg) =>
    let mk ← elabMaddlOp op
    setOperandWidth (toExpr RegWidth.W64)
    let rd ← elabRegOrZr rd
    let rn ← atOperandWidth .W32 (elabRegOrZr rn)
    let rm ← atOperandWidth .W32 (elabRegOrZr rm)
    let ra ← elabRegOrZr ra
    mkInstr (mkApp4 mk rd rn rm ra)
  | `(aarch64_instr| $op:aarch64_mull_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg) =>
    let mk ← elabMullOp op
    setOperandWidth (toExpr RegWidth.W64)
    let rd ← elabRegOrZr rd
    let rn ← atOperandWidth .W32 (elabRegOrZr rn)
    let rm ← atOperandWidth .W32 (elabRegOrZr rm)
    mkInstr (mkApp4 mk rd rn rm (← mkXzr))
  | `(aarch64_instr| $op:aarch64_rr_op $rd:aarch64_reg, $rn:aarch64_reg) =>
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    mkInstr (← elabRrOp op rd rn)
  | `(aarch64_instr| $op:aarch64_extend_op $rd:aarch64_reg, $rn:aarch64_reg) =>
    let rd ← elabRegOrZr rd
    let (mk, imms) ← elabExtendOp op
    let rn ← elabExtendSrc rn
    mkInstr (← mkAppWidth mk #[rd, rn, toExpr (0 : Nat), toExpr imms])
  | `(aarch64_instr| $op:aarch64_shift_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg) =>
    let mk ← elabShiftRegOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    mkInstr (← mkAppWidth mk #[rd, rn, rm])
  | `(aarch64_instr| $op:aarch64_shift_op $rd:aarch64_reg, $rn:aarch64_reg, $i:aarch64_imm) =>
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    mkInstr (← elabShiftImmOp op rd rn i)
  | `(aarch64_instr| extr $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $lsb:aarch64_imm) =>
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    let lsb ← elabImmNat lsb (checkBitWidthBound "extr" (← evalBoundsWidth))
    mkInstr (← mkAppWidth (mkConst ``Operation.EXTR) #[rd, rn, rm, lsb])
  | `(aarch64_instr| $op:aarch64_bitfield_op $rd:aarch64_reg, $rn:aarch64_reg, $a:aarch64_imm, $b:aarch64_imm) =>
    let (mk, form) ← elabBitfieldOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let (immr, imms) ← elabBitfieldImms form a b
    mkInstr (← mkAppWidth mk #[rd, rn, immr, imms])
  | `(aarch64_instr| $op:aarch64_csel_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $cond:aarch64_cond) =>
    let mk ← elabCselOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    mkInstr (← mkAppWidth mk #[rd, rn, rm, ← elabCond cond])
  | `(aarch64_instr| $op:aarch64_cinc_op $rd:aarch64_reg, $rn:aarch64_reg, $cond:aarch64_cond) =>
    let mk ← elabCincOp op
    let rd ← elabRegOrZr rd
    let rn ← elabRegOrZr rn
    mkInstr (← mkAppWidth mk #[rd, rn, rn, ← elabCond cond (invert := true)])
  | `(aarch64_instr| $op:aarch64_cset_op $rd:aarch64_reg, $cond:aarch64_cond) =>
    let mk ← elabCsetOp op
    let rd ← elabRegOrZr rd
    let xzr ← mkXzr
    mkInstr (← mkAppWidth mk #[rd, xzr, xzr, ← elabCond cond (invert := true)])
  | `(aarch64_instr| $op:aarch64_ccmp_op $rn:aarch64_reg, $rm:aarch64_reg, $flags:aarch64_imm, $cond:aarch64_cond) =>
    let (mk, _) ← elabCcmpOp op
    let rn ← elabRegOrZr rn
    let rm ← elabRegOrZr rm
    let nzcv ← elabImmNat flags checkNzcvFlags
    mkInstr (← mkAppWidth mk #[rn, rm, nzcv, ← elabCond cond])
  | `(aarch64_instr| $op:aarch64_ccmp_op $rn:aarch64_reg, $i:aarch64_imm, $flags:aarch64_imm, $cond:aarch64_cond) =>
    let (_, mk) ← elabCcmpOp op
    let rn ← elabRegOrZr rn
    let imm ← elabImmNat i checkCcmpImmediate
    let nzcv ← elabImmNat flags checkNzcvFlags
    mkInstr (← mkAppWidth mk #[rn, imm, nzcv, ← elabCond cond])
  | `(aarch64_instr| mov $rd:aarch64_reg, $rn:aarch64_reg) =>
    elabMovReg rd rn
  | `(aarch64_instr| mov $rd:aarch64_reg, $i:aarch64_imm) =>
    elabMovImm rd i
  | `(aarch64_instr| $op:aarch64_movw_op $rd:aarch64_reg, $imm:aarch64_const $[, $shift?:aarch64_modifier]?) =>
    let mk ← elabMovwOp op
    let rd ← elabRegOrZr rd
    let imm ← elabConst imm checkMovWideImmediate
    let shift ← match shift? with
      | none    => mkAppWidth (mkConst ``MovShift.LSL0)
      | some sh =>
        let w ← evalOperandWidth
        pure (toExpr (← evalMovShift (← evalModifier sh) w))
    mkInstr (← mkAppWidth mk #[rd, imm, shift])
  | `(aarch64_instr| $op:aarch64_adr_op $rd:aarch64_reg, $target:aarch64_const) =>
    let (mk, check) ← elabAdrOp op
    setOperandWidth (toExpr RegWidth.W64)
    let rd ← elabRegOrZr rd
    mkInstr (mkApp2 mk rd (← elabConst target check))
  | `(aarch64_instr| $op:aarch64_b_op $target:aarch64_const) =>
    let mk ← elabBOp op
    setOperandWidth (toExpr RegWidth.W64)
    mkInstr (mkApp mk (← elabConst target checkBOffset))
  | `(aarch64_instr| $op:aarch64_br_op $rn:aarch64_reg) =>
    let mk ← elabBrOp op
    setOperandWidth (toExpr RegWidth.W64)
    mkInstr (mkApp mk (← elabRegOrZr rn))
  | `(aarch64_instr| ret $[$rn?:aarch64_reg]?) =>
    setOperandWidth (toExpr RegWidth.W64)
    let rn := (← rn?.mapM elabRegOrZr).getD (toExpr RegOrZr.X30)
    mkInstr (mkApp (mkConst ``Operation.RET) rn)
  | `(aarch64_instr| $op:aarch64_cbz_op $rt:aarch64_reg, $target:aarch64_const) =>
    let (name, mk) ← elabCbzOp op
    let rt ← elabRegOrZr rt
    mkInstr (← mkAppWidth mk #[rt, ← elabConst target (checkCbzOffset name)])
  | `(aarch64_instr| $op:aarch64_tbz_op $rt:aarch64_reg, $bit:aarch64_imm, $target:aarch64_const) =>
    let (name, mk) ← elabTbzOp op
    let rt ← elabRegOrZr rt
    let bit ← elabImmNat bit (checkTbzBitPosition name (← evalBoundsWidth))
    mkInstr (← mkAppWidth mk #[rt, bit, ← elabConst target (checkTbzOffset name)])
  | `(aarch64_instr| $op:aarch64_bcond_op $target:aarch64_const) =>
    let cond ← evalCond op
    setOperandWidth (toExpr RegWidth.W64)
    mkInstr (mkApp2 (mkConst ``Operation.B_cond) (toExpr cond) (← elabConst target checkBCondOffset))
  | `(aarch64_instr| nop) =>
    mkClosedInstr .NOP
  | _ => throwError "invalid instruction syntax"
where
  /-- A 64-bit instruction without operands to infer widths from. -/
  mkClosedInstr (op : Operation .W64) : AArch64ElabM Expr :=
    pure (toExpr (Instr.mk .W64 op))

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `aarch64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `aarch64_directive) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_directive| $lbl:aarch64_label :) =>
    return mkApp2 (mkConst ``Directive.label) (mkConst ``Instr) (← elabLabel lbl)
  | `(aarch64_directive| $ins:aarch64_instr) =>
    let ins ← ins.raw.replaceM resolveRegOrConstChoice
    return mkApp2 (mkConst ``Directive.instr) (mkConst ``Instr) (← (elabInstr ⟨ins⟩).run')
  | `(aarch64_directive| ❰ $t:term ❱) =>
    elabAntiquot t (mkConst ``_root_.Directive)
  | _ => throwError "invalid assembly directive"

/-- Elaborate an `aarch64_prog` syntax node into a `Lean.Expr` of type `Program` (`List Directive`). -/
def elabProgram (stx : TSyntax `aarch64_prog) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_prog| $dirs:aarch64_directive*) =>
    let dirExprs ← dirs.mapM elabDirective
    mkListLit (mkConst ``_root_.Directive) dirExprs.toList
  | _ => throwError "invalid assembly program"

-- ============================================================================
-- Public String Parser/Elaborator & Macros
-- ============================================================================

/-- Replace AArch64 `// ...` line comments and line-leading `# ...` comments with Lean `--` comments
    (elsewhere `#` prefixes immediates). -/
private def replaceAArch64Comments (input : String) : String :=
  "\n".intercalate <| (replaceLineComments "//" input).splitOn "\n" |>.map fun line =>
    let code := line.trimAsciiStart.toString
    if code.startsWith "#" then (line.take (line.length - code.length)).toString ++ "--" ++ (code.drop 1).toString
    else line

/-- Parse and elaborate an AArch64 assembly string into a `Lean.Expr` representing a Kraken `Program`. -/
public def elabAArch64 (input : String) : TermElabM Expr :=
  elabCategory `aarch64_prog elabProgram (replaceAArch64Comments input)

end

/-- Inline unquoted AArch64 assembly block macro/elaborator (`[aarch64| ... ]`). -/
elab "[aarch64|" p:aarch64_prog "]" : term => elabProgram p

/-- Read an AArch64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_aarch64 " path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabAArch64 (stripDirectives content)

/-- Function-call style `include_aarch64("path")` alias. -/
elab "include_aarch64(" path:str ")" : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabAArch64 (stripDirectives content)

end Kraken.AArch64.Parser
