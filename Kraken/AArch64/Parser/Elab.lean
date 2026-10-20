module

public import Kraken.AArch64.Parser.Basic
public meta import Kraken.AArch64.Parser.Basic
public import Kraken.AArch64.Parser.Syntax
public meta import Kraken.AArch64.Parser.Syntax
public meta import Lean

namespace Kraken.AArch64.Parser

open Lean Meta Elab Term Kraken.Parser

public meta section

-- ============================================================================
-- Named Range Constants
-- ============================================================================

/-- Maximum value of `UInt16` as an `Int` (`2^16 - 1`). -/
def UInt16.maxValue.toInt : Int := 0xffff

/-- Maximum value of `UInt32` as an `Int` (`2^32 - 1`). -/
def UInt32.maxValue.toInt : Int := 0xffffffff

/-- Minimum signed 9-bit pre/post-indexed load/store immediate offset (`-256`). -/
def prePostOffsetMin : Int := -256

/-- Maximum signed 9-bit pre/post-indexed load/store immediate offset (`255`). -/
def prePostOffsetMax : Int := 255

-- ============================================================================
-- Register Elaboration
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

/-- Elaborate an `aarch64_reg` into a width-tagged register, before the instruction decides whether
    register 31 denotes `sp` or `xzr`. -/
def elabAnyRegW (stx : TSyntax `aarch64_reg) : TermElabM AnyRegW := withRef stx do
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
    match idx with
    | "zr" => pure ⟨w, .xzr⟩
    | _ =>
      let some r := xreg? idx | throwError "invalid register index '{idx}'"
      pure ⟨w, .gpr r⟩

/-- Elaborate a register operand that must have width `w`. -/
def elabAnyReg (stx : TSyntax `aarch64_reg) (w : RegWidth) : TermElabM (AnyReg w) := withRef stx do
  let ⟨w', r⟩ ← elabAnyRegW stx
  if h : w = w' then pure (h ▸ r) else throwError "expected {w} register, got {w'}"

/-- Interpret register 31 as the stack pointer; the zero register is rejected. -/
def AnyReg.toRegOrSpM {w : RegWidth} : AnyReg w → TermElabM (RegOrSp w)
  | .gpr r => pure (.low (.reg r) w)
  | .sp    => pure (.low .SP w)
  | .xzr   => throwError "xzr/wzr not allowed here (sp/wsp expected)"

/-- Interpret register 31 as the zero register; the stack pointer is rejected. -/
def AnyReg.toRegOrZrM {w : RegWidth} : AnyReg w → TermElabM (RegOrZr w)
  | .gpr r => pure (.low (.reg r) w)
  | .xzr   => pure (.low .XZR w)
  | .sp    => throwError "sp/wsp not allowed here (xzr/wzr expected)"

/-- Elaborate a register whose width is decided by the register itself (register 31 is `xzr`/`wzr`). -/
def elabRegOrZrW (stx : TSyntax `aarch64_reg) : TermElabM RegOrZrW := withRef stx do
  let ⟨w, r⟩ ← elabAnyRegW stx
  return ⟨w, ← r.toRegOrZrM⟩

/-- Elaborate a `w`-bit register where register 31 is `sp`/`wsp`. -/
def elabRegOrSp (stx : TSyntax `aarch64_reg) (w : RegWidth) : TermElabM (RegOrSp w) := withRef stx do
  (← elabAnyReg stx w).toRegOrSpM

/-- Elaborate a `w`-bit register where register 31 is `xzr`/`wzr`. -/
def elabRegOrZr (stx : TSyntax `aarch64_reg) (w : RegWidth) : TermElabM (RegOrZr w) := withRef stx do
  (← elabAnyReg stx w).toRegOrZrM

/-- Reject the `w`-bit operation of a mnemonic that only exists at width `w₀`. -/
def wrongWidth {α : Type} (w₀ w : RegWidth) : TermElabM α :=
  throwError "requires {w₀.bits}-bit registers (got {w.bits}-bit)"

/-- Re-tag a register with another width, for operations whose source register is narrower than their
    width index (`sxtb Xd, Wn` is `SBFM Xd, Wn, #0, #7`). -/
def _root_.RegOrZr.withWidth {w' : RegWidth} : RegOrZr w' → (w : RegWidth) → RegOrZr w
  | .low r _, w => .low r w

-- ============================================================================
-- Immediate, Constant Expression & Condition Code Elaboration
-- ============================================================================

/-- Elaborate an `aarch64_int` into a signed integer. -/
def elabInt (stx : TSyntax `aarch64_int) : TermElabM Int := withRef stx do
  match stx with
  | `(aarch64_int| $n:num)
  | `(aarch64_int| +$n:num) => pure n.getNat
  | `(aarch64_int| -$n:num) => pure (-n.getNat)
  | _ => throwError "expected integer literal"

/-- Elaborate an `aarch64_imm` into a signed integer. -/
def elabImm (stx : TSyntax `aarch64_imm) : TermElabM Int := withRef stx do
  match stx with
  | `(aarch64_imm| $[#]? $i:aarch64_int) => elabInt i
  | _ => throwError "expected integer immediate"

/-- Elaborate an `aarch64_imm` as a non-negative `Nat`. -/
def elabImmNat (stx : TSyntax `aarch64_imm) : TermElabM Nat := withRef stx do
  let v ← elabImm stx
  if v < 0 then throwError "expected non-negative immediate, got {v}"
  pure v.toNat

/-- Elaborate an `aarch64_imm` as `Int64`, checking the 64-bit range. -/
def elabImm64 (stx : TSyntax `aarch64_imm) : TermElabM Int64 := withRef stx do
  _root_.Int64.ofIntNoOverflow (← elabImm stx)

/-- Elaborate an `aarch64_const` into a `ConstExpr`. -/
def elabConst (stx : TSyntax `aarch64_const) : TermElabM ConstExpr := withRef stx do
  match stx with
  | `(aarch64_const| $i:aarch64_imm) => return .int64 (← elabImm64 i)
  | `(aarch64_const| $[#]? : $modifier:aarch64_ident : $sym:aarch64_ident) =>
    let sym : ConstExpr := .label (← getAsmIdent sym)
    match (← getAsmIdent modifier).toLower with
    | "pg_hi21" => pure (.pg_hi21 sym)
    | "lo12"    => pure (.lo12 sym)
    | name      => throwErrorAt modifier "unknown relocation modifier: {name}"
  | `(aarch64_const| $id:aarch64_ident) => return .label (← getAsmIdent id)
  | _ => throwError "invalid constant expression"

/-- Elaborate a constant, validating integer values with `check` (symbols and relocations are left to the
    assembler). -/
def elabCheckedConst (stx : TSyntax `aarch64_const) (check : Int64 → Except String Unit) : TermElabM ConstExpr := withRef stx do
  let c ← elabConst stx
  if let .int64 v := c then ofExcept (check v)
  pure c

/-- Elaborate the condition code carried by the suffix of an `aarch64_cond` operand or `b.<cond>` mnemonic. -/
def elabCond (stx : Syntax) : TermElabM CondCode := withRef stx do
  let (_, sfx) ← splitSuffixed stx
  let some cond := parseCondCode sfx | throwError "invalid condition code '{sfx}'"
  pure cond

-- ============================================================================
-- Shift & Extend Modifier Elaboration
-- ============================================================================

/-- A shift or extend modifier as written (`lsl #2`, `uxtw`): keyword and amount (`0` when omitted). -/
structure Modifier where
  name : String
  amount : Nat
  /-- Whether the keyword is an extension (`uxtb`..`sxtx`) rather than a shift (`lsl`, `lsr`, `asr`, `ror`). -/
  isExtend : Bool

def elabModifier (stx : TSyntax `aarch64_modifier) : TermElabM Modifier := withRef stx do
  let `(aarch64_modifier| $kind:aarch64_modifier_kind $[$amt?:aarch64_imm]?) := stx
    | throwError "expected shift or extend modifier"
  let (stem, sfx) ← splitSuffixed kind
  let amount := (← amt?.mapM elabImmNat).getD 0
  pure { name := stem ++ sfx, amount, isExtend := stem == "uxt" || stem == "sxt" }

/-- Shift applied to a register operand of a `w`-bit instruction (`ror` only for logical instructions). -/
def elabShift (stx : TSyntax `aarch64_modifier) (w : RegWidth) (allowRor : Bool) : TermElabM (ShiftType × Int64) := withRef stx do
  let m ← elabModifier stx
  let type ← match m.name with
    | "lsl" => pure ShiftType.LSL
    | "lsr" => pure ShiftType.LSR
    | "asr" => pure ShiftType.ASR
    | "ror" => if allowRor then pure ShiftType.ROR else throwError "arithmetic instructions do not support ROR shift"
    | name  => throwError "unknown shift type: {name}"
  let amount : Int64 := .ofNat m.amount
  ofExcept (checkShiftAmount w amount)
  pure (type, amount)

/-- Extension applied to a `regW`-bit register operand of a `w`-bit arithmetic instruction. -/
def elabExtend (stx : TSyntax `aarch64_modifier) (w regW : RegWidth) : TermElabM Extend := withRef stx do
  let m ← elabModifier stx
  let type ← ofExcept (getExtendType m.name w regW)
  let amount ← match m.amount with
    | 0 => pure ExtendAmount.E0
    | 1 => pure ExtendAmount.E1
    | 2 => pure ExtendAmount.E2
    | 3 => pure ExtendAmount.E3
    | 4 => pure ExtendAmount.E4
    | n => throwError "invalid extend amount: {n}"
  pure { type, amount }

/-- Extension applied to a `regW`-bit index register of a `scale`-byte memory access of width `w`. -/
def elabMemExtend (stx : TSyntax `aarch64_modifier) (w : RegWidth) (scale : Nat) (regW : RegWidth) : TermElabM MemExtend := withRef stx do
  let m ← elabModifier stx
  return { type := ← ofExcept (getMemExtendType m.name regW), amount := ← ofExcept (getMemExtendAmount w m.amount scale) }

/-- Shift applied to the immediate of an arithmetic instruction (`lsl #0` or `lsl #12`). -/
def elabImmShift (stx : TSyntax `aarch64_modifier) : TermElabM ImmShift := withRef stx do
  let m ← elabModifier stx
  unless m.name == "lsl" do throwError "expected lsl for immediate shift, got {m.name}"
  match m.amount with
  | 0  => pure .S0
  | 12 => pure .S12
  | n  => throwError "invalid immediate shift {n} (must be 0 or 12)"

/-- Shift applied to the immediate of a `w`-bit move wide instruction. -/
def elabMovShift (stx : TSyntax `aarch64_modifier) (w : RegWidth) : TermElabM (MovShift w) := withRef stx do
  let m ← elabModifier stx
  unless m.name == "lsl" do throwError "only lsl shift supported for move wide"
  ofExcept (getMovShift w m.amount)

-- ============================================================================
-- Source Operand Elaboration
-- ============================================================================

/-- Elaborate a register with optional shift (`Rm`, `Rm, lsl #n`) into a `w`-bit shifted-register operand. -/
def elabShiftedReg (rm : TSyntax `aarch64_reg) (mod? : Option (TSyntax `aarch64_modifier)) (w : RegWidth)
    (allowRor : Bool) : TermElabM (ShiftRegExpr w) := do
  let reg ← elabRegOrZr rm w
  let (shift, amount) ← match mod? with
    | none     => pure (.LSL, 0)
    | some mod => elabShift mod w allowRor
  pure { reg, amount, shift }

/-- Elaborate a flexible source operand that must be a shifted register. -/
def elabShiftedSrc (stx : TSyntax `aarch64_src) (w : RegWidth) (allowRor : Bool) : TermElabM (ShiftRegExpr w) := withRef stx do
  match stx with
  | `(aarch64_src| $rm:aarch64_reg $[, $mod?]?) => elabShiftedReg rm mod? w allowRor
  | _ => throwError "expected register"

/-- Source of a logical instruction: bitmask immediate (`_i` form) or shifted register (`_s` form). -/
inductive LogicalSrc (w : RegWidth)
  | imm (imm : ConstExpr)
  | shift (src : ShiftRegExpr w)

def elabLogicalSrc (stx : TSyntax `aarch64_src) (w : RegWidth) : TermElabM (LogicalSrc w) := withRef stx do
  match stx with
  | `(aarch64_src| $c:aarch64_const $[, $mod?]?) =>
    if let some mod := mod? then throwErrorAt mod "logical immediates cannot be shifted"
    return .imm (← elabCheckedConst c (checkLogicalImmediate w))
  | `(aarch64_src| $rm:aarch64_reg $[, $mod?]?) => return .shift (← elabShiftedReg rm mod? w (allowRor := true))
  | _ => throwError "invalid source operand"

/-- Source of an add/subtract instruction: extended register or immediate (`_e` form), or shifted
    register (`_s` form). -/
inductive ArithSrc (w : RegWidth)
  | ext (src : ExtOrImmReg)
  | shift (src : ShiftRegExpr w)

/-- Elaborate the flexible source of a `w`-bit add/subtract. A register with no modifier or an `lsl`
    shift uses the shifted-register form, unless the stack pointer is involved (`sp`), in which case
    `lsl` is the `uxtx`/`uxtw` alias of the extended-register form. -/
def elabArithSrc (stx : TSyntax `aarch64_src) (w : RegWidth) (sp : Bool) : TermElabM (ArithSrc w) := withRef stx do
  match stx with
  | `(aarch64_src| $c:aarch64_const $[, $mod?]?) =>
    let imm ← elabCheckedConst c checkArithmeticImmediate
    let shift ← match mod? with
      | none => pure .S0
      | some mod =>
        unless imm matches .int64 _ do
          throwErrorAt c "relocation modifiers and labels cannot be shifted with lsl in immediate operands"
        elabImmShift mod
    pure (.ext (.imm { imm, shift }))
  | `(aarch64_src| $rm:aarch64_reg $[, $mod?]?) =>
    if sp || (← mod?.mapM elabModifier).any (·.isExtend) then
      let reg ← elabRegOrZrW rm
      let ext ← match mod? with
        | some mod => elabExtend mod w reg.w
        | none =>
          unless reg.w == w do throwErrorAt rm "expected {w} register, got {reg.w}"
          pure { type := if w == .W64 then .UXTX else .UXTW, amount := .E0 }
      pure (.ext (.ext { reg, ext }))
    else
      pure (.shift (← elabShiftedReg rm mod? w (allowRor := false)))
  | _ => throwError "invalid source operand"

-- ============================================================================
-- Memory Operand Elaboration
-- ============================================================================

/-- Elaborate a pre/post-indexed immediate offset (signed 9-bit, `[-256, 255]`). -/
def elabIndexedOffset (stx : TSyntax `aarch64_const) (mode : String) : TermElabM Int64 := withRef stx do
  let .int64 imm ← elabConst stx
    | throwError "pre-indexed / post-indexed offsets must be constant numeric immediates"
  if imm.toInt < prePostOffsetMin || imm.toInt > prePostOffsetMax then
    throwError "{mode} offset {imm.toInt} out of range [{prePostOffsetMin}, {prePostOffsetMax}]"
  pure imm

/-- Elaborate the memory operand of a single-register load/store of `scale` bytes and transfer width `w`.
    Immediate offsets may be unsigned scaled (`[0, 4095 * scale]`) or signed 9-bit (`[-256, 255]`). -/
def elabMem (stx : TSyntax `aarch64_mem) (w : RegWidth) (scale : Nat) : TermElabM AddrExpr := withRef stx do
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    let imm ← off?.mapM (elabCheckedConst · (checkLoadStoreOffset w · (allowUnscaled := true) scale))
    return ⟨← elabRegOrSp b .W64, .imm { imm := imm.getD 0, index := none }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]!) =>
    return ⟨← elabRegOrSp b .W64, .imm { imm := ← elabIndexedOffset off "pre-indexed", index := some .Pre }⟩
  | `(aarch64_mem| [$b:aarch64_reg], $off:aarch64_const) =>
    return ⟨← elabRegOrSp b .W64, .imm { imm := ← elabIndexedOffset off "post-indexed", index := some .Post }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg $[, $mod?:aarch64_modifier]?]) =>
    let base ← elabRegOrSp b .W64
    let reg ← elabRegOrZrW rm
    let ext ← match mod? with
      | some mod => elabMemExtend mod w scale reg.w
      | none => pure { type := if reg.w == .W64 then .UXTX else .UXTW, amount := .E0 }
    pure ⟨base, .reg { reg, ext }⟩
  | _ => throwError "invalid memory operand"

/-- Elaborate the memory operand of an unscaled load/store (`[Xn]`, `[Xn, #simm9]`). -/
def elabUnscaledMem (stx : TSyntax `aarch64_mem) : TermElabM UnscaledAddrExpr := withRef stx do
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    let imm ← off?.mapM (elabCheckedConst · checkUnscaledOffset)
    return { base := ← elabRegOrSp b .W64, imm := imm.getD 0 }
  | `(aarch64_mem| [$_:aarch64_reg, $_:aarch64_reg $[, $_]?]) =>
    throwError "expected immediate offset in unscaled address operand"
  | _ => throwError "invalid unscaled address operand"

/-- Elaborate the memory operand of a `w`-bit register-pair load/store (7-bit scaled immediates only). -/
def elabPairMem (stx : TSyntax `aarch64_mem) (w : RegWidth) : TermElabM AddrExpr := withRef stx do
  let offset (off : TSyntax `aarch64_const) : TermElabM Int64 := withRef off do
    let .int64 imm ← elabConst off | throwError "pair offsets must be constant numeric immediates"
    ofExcept (checkPairOffset w imm)
    pure imm
  match stx with
  | `(aarch64_mem| [$b:aarch64_reg $[, $off?:aarch64_const]?]) =>
    return ⟨← elabRegOrSp b .W64, .imm { imm := (← off?.mapM offset).getD 0, index := none }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]!) =>
    return ⟨← elabRegOrSp b .W64, .imm { imm := ← offset off, index := some .Pre }⟩
  | `(aarch64_mem| [$b:aarch64_reg], $off:aarch64_const) =>
    return ⟨← elabRegOrSp b .W64, .imm { imm := ← offset off, index := some .Post }⟩
  | `(aarch64_mem| [$_:aarch64_reg, $_:aarch64_reg $[, $_]?]) =>
    throwError "register offsets are not supported for ldp/stp instructions"
  | _ => throwError "invalid memory operand"

/-- Elaborate a PC-relative literal load source (`=expr` or label) for a `w`-bit load. -/
def elabLit (stx : TSyntax `aarch64_lit) (w : RegWidth) (allowPool : Bool) : TermElabM _root_.Literal := withRef stx do
  match stx with
  | `(aarch64_lit| = $c:aarch64_const) =>
    unless allowPool do throwError "literal pool (=expr) is not supported for ldrsw"
    let expr ← elabConst c
    if w == .W32 then
      if let .int64 imm := expr then
        if imm.toInt < Int32.minValue.toInt || imm.toInt > UInt32.maxValue.toInt then
          throwErrorAt c "literal pool immediate {imm.toInt} too large for 32-bit register"
    pure (.pool { expr })
  | `(aarch64_lit| $lbl:aarch64_ident) => return .addr { label := ← getAsmIdent lbl }
  | _ => throwError "invalid literal operand"

-- ============================================================================
-- Load/Store Families
-- ============================================================================

/-- Instruction constructors of a load/store mnemonic with a `w`-bit transfer register. -/
structure MemCtors (w : RegWidth) where
  /-- Scaled unsigned offset, pre/post-indexed and register offset addressing (`ldr`, `str`, ...). -/
  mem : RegOrZr w → AddrExpr → Operation w
  /-- Unscaled signed 9-bit offset addressing (`ldur`, `stur`, ...). -/
  unscaled : RegOrZr w → UnscaledAddrExpr → Operation w
  /-- PC-relative literal (`ldr Rt, =imm`, `ldr Rt, label`), where supported. -/
  lit : Option (RegOrZr w → _root_.Literal → Operation w) := none
  /-- Whether literal pool constants (`=imm`) are supported. -/
  pool : Bool := true
  /-- Memory access width (the transfer register width unless the mnemonic narrows it). -/
  access : MemWidth := w

/-- Scale of the immediate offsets, in bytes. -/
def MemCtors.scale {w : RegWidth} (c : MemCtors w) : Nat := c.access.bytes

/-- Constructors of a load mnemonic suffix, for a `w`-bit transfer register. -/
def loadCtors : (w : RegWidth) → String → TermElabM (MemCtors w)
  | _,    ""   => pure { mem := fun rt a => .LDR rt (.addr a), unscaled := .LDUR, lit := some fun rt l => .LDR rt (.lit l) }
  | .W32, "b"  => pure { mem := .LDRB,  unscaled := .LDURB,  access := .W8 }
  | .W32, "h"  => pure { mem := .LDRH,  unscaled := .LDURH,  access := .W16 }
  | _,    "sb" => pure { mem := .LDRSB, unscaled := .LDURSB, access := .W8 }
  | _,    "sh" => pure { mem := .LDRSH, unscaled := .LDURSH, access := .W16 }
  | .W64, "sw" => pure { mem := fun rt a => .LDRSW rt (.addr a), unscaled := .LDURSW,
                         lit := some fun rt l => .LDRSW rt (.lit l), pool := false, access := .W32 }
  | w, "b" | w, "h" => wrongWidth .W32 w
  | w, "sw"         => wrongWidth .W64 w
  | _, _            => throwError "invalid load mnemonic"

/-- Constructors of a store mnemonic suffix, for a `w`-bit transfer register. -/
def storeCtors : (w : RegWidth) → String → TermElabM (MemCtors w)
  | _,    ""  => pure { mem := .STR, unscaled := .STUR }
  | .W32, "b" => pure { mem := .STRB, unscaled := .STURB, access := .W8 }
  | .W32, "h" => pure { mem := .STRH, unscaled := .STURH, access := .W16 }
  | w, "b" | w, "h" => wrongWidth .W32 w
  | _, _            => throwError "invalid store mnemonic"

/-- Elaborate the transfer register of a load/store mnemonic, which decides its width, and resolve its
    constructors from its size suffix. -/
def elabMemOp (ctors : (w : RegWidth) → String → TermElabM (MemCtors w)) (op : Syntax)
    (rt : TSyntax `aarch64_reg) : TermElabM (Σ w, MemCtors w × RegOrZr w) := do
  let ⟨w, rt⟩ ← elabRegOrZrW rt
  return ⟨w, ← withRef op <| ctors w (← splitSuffixed op).2, rt⟩

/-- Build a scaled load/store, falling back to the unscaled encoding when the immediate offset is negative
    or not a multiple of the access size. -/
def elabScaledAccess {w : RegWidth} (ctors : MemCtors w) (rt : RegOrZr w) (addr : AddrExpr) :
    TermElabM (Operation w) := do
  ofExcept (checkLdrStrRegisters rt addr)
  if addrExprNeedsUnscaled addr ctors.scale then
    let some unscaled := addrExprToUnscaled addr | throwError "unscaled access cannot use a register offset"
    pure (ctors.unscaled rt unscaled)
  else
    pure (ctors.mem rt addr)

-- ============================================================================
-- Mnemonic Category Elaborators
-- ============================================================================

/-- Elaborate an `aarch64_pair_op` for `w`-bit registers into its access width, constructor, and whether
    it is a load. -/
def elabPairOp (stx : TSyntax `aarch64_pair_op) (w : RegWidth) :
    TermElabM (RegWidth × (RegOrZr w → RegOrZr w → AddrExpr → Operation w) × Bool) := withRef stx <|
  match stx with
  | `(aarch64_pair_op| ldp)   => pure (w, .LDP, true)
  | `(aarch64_pair_op| ldpsw) => match w with | .W64 => pure (.W32, .LDPSW, true) | .W32 => wrongWidth .W64 w
  | `(aarch64_pair_op| stp)   => pure (w, .STP, false)
  | _ => throwError "invalid register-pair mnemonic"

/-- Elaborate an `aarch64_rrr_op` for `w`-bit registers into its constructor. -/
def elabRrrOp (stx : TSyntax `aarch64_rrr_op) (w : RegWidth) :
    TermElabM (RegOrZr w → RegOrZr w → RegOrZr w → Operation w) := withRef stx <|
  match stx with
  | `(aarch64_rrr_op| adc)   => pure .ADC
  | `(aarch64_rrr_op| adcs)  => pure .ADCS
  | `(aarch64_rrr_op| sbc)   => pure .SBC
  | `(aarch64_rrr_op| sbcs)  => pure .SBCS
  | `(aarch64_rrr_op| sdiv)  => pure .SDIV
  | `(aarch64_rrr_op| udiv)  => pure .UDIV
  | `(aarch64_rrr_op| mul)   => pure fun rd rn rm => .MADD rd rn rm (.low .XZR _)
  | `(aarch64_rrr_op| mneg)  => pure fun rd rn rm => .MSUB rd rn rm (.low .XZR _)
  | `(aarch64_rrr_op| smulh) => match w with | .W64 => pure .SMULH | .W32 => wrongWidth .W64 w
  | `(aarch64_rrr_op| umulh) => match w with | .W64 => pure .UMULH | .W32 => wrongWidth .W64 w
  | `(aarch64_rrr_op| lslv)  => pure .LSLV
  | `(aarch64_rrr_op| lsrv)  => pure .LSRV
  | `(aarch64_rrr_op| asrv)  => pure .ASRV
  | `(aarch64_rrr_op| rorv)  => pure .RORV
  | _ => throwError "invalid three-register mnemonic"

/-- Elaborate an `aarch64_madd_op` into its constructor. -/
def elabMaddOp (stx : TSyntax `aarch64_madd_op) :
    TermElabM ({w : RegWidth} → RegOrZr w → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) := withRef stx do
  match stx with
  | `(aarch64_madd_op| madd) => pure .MADD
  | `(aarch64_madd_op| msub) => pure .MSUB
  | _ => throwError "invalid multiply-accumulate mnemonic"

/-- Elaborate an `aarch64_maddl_op` into its constructor. -/
def elabMaddlOp (stx : TSyntax `aarch64_maddl_op) :
    TermElabM (RegOrZr .W64 → RegOrZr .W32 → RegOrZr .W32 → RegOrZr .W64 → Operation .W64) := withRef stx do
  match stx with
  | `(aarch64_maddl_op| smaddl) => pure .SMADDL
  | `(aarch64_maddl_op| umaddl) => pure .UMADDL
  | `(aarch64_maddl_op| smsubl) => pure .SMSUBL
  | `(aarch64_maddl_op| umsubl) => pure .UMSUBL
  | _ => throwError "invalid widening multiply-accumulate mnemonic"

/-- Elaborate an `aarch64_mull_op` into its multiply-accumulate constructor (the accumulator is `xzr`). -/
def elabMullOp (stx : TSyntax `aarch64_mull_op) :
    TermElabM (RegOrZr .W64 → RegOrZr .W32 → RegOrZr .W32 → RegOrZr .W64 → Operation .W64) := withRef stx do
  match stx with
  | `(aarch64_mull_op| smull)  => pure .SMADDL
  | `(aarch64_mull_op| umull)  => pure .UMADDL
  | `(aarch64_mull_op| smnegl) => pure .SMSUBL
  | `(aarch64_mull_op| umnegl) => pure .UMSUBL
  | _ => throwError "invalid widening multiply mnemonic"

/-- Elaborate an `aarch64_rr_op` for `w`-bit registers into its constructor. -/
def elabRrOp (stx : TSyntax `aarch64_rr_op) (w : RegWidth) :
    TermElabM (RegOrZr w → RegOrZr w → Operation w) := withRef stx <|
  match stx with
  | `(aarch64_rr_op| clz)   => pure .CLZ
  | `(aarch64_rr_op| cls)   => pure .CLS
  | `(aarch64_rr_op| rbit)  => pure .RBIT
  | `(aarch64_rr_op| rev)   => pure .REV
  | `(aarch64_rr_op| rev16) => pure .REV16
  | `(aarch64_rr_op| rev32) => match w with | .W64 => pure .REV32 | .W32 => wrongWidth .W64 w
  | `(aarch64_rr_op| rev64) => match w with | .W64 => pure .REV   | .W32 => wrongWidth .W64 w
  | _ => throwError "invalid bit manipulation mnemonic"

/-- Elaborate an `aarch64_extend_op` with a `w`-bit destination into its bitfield-move constructor and
    `imms` (the top bit of the source field); `sxtw`/`uxtw` require a 64-bit destination. -/
def elabExtendOp (stx : TSyntax `aarch64_extend_op) (w : RegWidth) :
    TermElabM (Nat × (RegOrZr w → RegOrZr w → Nat → Nat → Operation w)) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  let mk : {w : RegWidth} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w ← match stem with
    | "sxt" => pure .SBFM
    | "uxt" => pure .UBFM
    | _     => throwError "invalid extension mnemonic"
  match sfx, w with
  | "b", _    => pure (7,  mk)
  | "h", _    => pure (15, mk)
  | "w", .W64 => pure (31, mk)
  | "w", w    => wrongWidth .W64 w
  | _,   _    => throwError "invalid extension width '{sfx}'"

/-- Elaborate an `aarch64_shift_op` into its register (`lslv`-style) and immediate (bitfield-encoded)
    constructors. -/
def elabShiftOp (stx : TSyntax `aarch64_shift_op) :
    TermElabM (({w : RegWidth} → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) ×
               ({w : RegWidth} → RegOrZr w → RegOrZr w → Nat → Operation w)) := withRef stx do
  match stx with
  | `(aarch64_shift_op| lsl) => pure (.LSLV, fun {w} rd rn n => .UBFM rd rn ((w.bits - n) % w.bits) (w.bits - 1 - n))
  | `(aarch64_shift_op| lsr) => pure (.LSRV, fun {w} rd rn n => .UBFM rd rn n (w.bits - 1))
  | `(aarch64_shift_op| asr) => pure (.ASRV, fun {w} rd rn n => .SBFM rd rn n (w.bits - 1))
  | `(aarch64_shift_op| ror) => pure (.RORV, fun rd rn n => .EXTR rd rn rn n)
  | _ => throwError "invalid shift mnemonic"

/-- How the two immediates of a bitfield mnemonic encode `immr` and `imms`. -/
inductive BitfieldForm
  /-- `(immr, imms)` as written. -/
  | raw
  /-- `(lsb, width)` of an extracted field. -/
  | extract
  /-- `(lsb, width)` of an inserted field. -/
  | insert

/-- Elaborate an `aarch64_bitfield_op` into its constructor and immediate encoding. -/
def elabBitfieldOp (stx : TSyntax `aarch64_bitfield_op) :
    TermElabM (({w : RegWidth} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w) × BitfieldForm) := withRef stx do
  match stx with
  | `(aarch64_bitfield_op| bfm)   => pure (.BFM,  .raw)
  | `(aarch64_bitfield_op| sbfm)  => pure (.SBFM, .raw)
  | `(aarch64_bitfield_op| ubfm)  => pure (.UBFM, .raw)
  | `(aarch64_bitfield_op| sbfx)  => pure (.SBFM, .extract)
  | `(aarch64_bitfield_op| ubfx)  => pure (.UBFM, .extract)
  | `(aarch64_bitfield_op| bfxil) => pure (.BFM,  .extract)
  | `(aarch64_bitfield_op| bfi)   => pure (.BFM,  .insert)
  | `(aarch64_bitfield_op| sbfiz) => pure (.SBFM, .insert)
  | `(aarch64_bitfield_op| ubfiz) => pure (.UBFM, .insert)
  | _ => throwError "invalid bitfield mnemonic"

/-- Elaborate an `aarch64_csel_op` into its constructor. -/
def elabCselOp (stx : TSyntax `aarch64_csel_op) :
    TermElabM ({w : RegWidth} → RegOrZr w → RegOrZr w → RegOrZr w → CondCode → Operation w) := withRef stx do
  match stx with
  | `(aarch64_csel_op| csel)  => pure .CSEL
  | `(aarch64_csel_op| csinc) => pure .CSINC
  | `(aarch64_csel_op| csinv) => pure .CSINV
  | `(aarch64_csel_op| csneg) => pure .CSNEG
  | _ => throwError "invalid conditional select mnemonic"

/-- Elaborate an `aarch64_cinc_op` into its conditional select constructor (applied with the inverted
    condition and both sources equal). -/
def elabCincOp (stx : TSyntax `aarch64_cinc_op) :
    TermElabM ({w : RegWidth} → RegOrZr w → RegOrZr w → RegOrZr w → CondCode → Operation w) := withRef stx do
  match stx with
  | `(aarch64_cinc_op| cinc) => pure .CSINC
  | `(aarch64_cinc_op| cinv) => pure .CSINV
  | `(aarch64_cinc_op| cneg) => pure .CSNEG
  | _ => throwError "invalid conditional increment mnemonic"

/-- Elaborate an `aarch64_cset_op` into its conditional select constructor (applied with the inverted
    condition and `xzr` sources). -/
def elabCsetOp (stx : TSyntax `aarch64_cset_op) :
    TermElabM ({w : RegWidth} → RegOrZr w → RegOrZr w → RegOrZr w → CondCode → Operation w) := withRef stx do
  match stx with
  | `(aarch64_cset_op| cset)  => pure .CSINC
  | `(aarch64_cset_op| csetm) => pure .CSINV
  | _ => throwError "invalid conditional set mnemonic"

/-- Elaborate an `aarch64_ccmp_op` into its register and immediate constructors. -/
def elabCcmpOp (stx : TSyntax `aarch64_ccmp_op) :
    TermElabM (({w : RegWidth} → RegOrZr w → RegOrZr w → Nat → CondCode → Operation w) ×
               ({w : RegWidth} → RegOrZr w → Nat → Nat → CondCode → Operation w)) := withRef stx do
  match stx with
  | `(aarch64_ccmp_op| ccmp) => pure (.CCMP_reg, .CCMP_imm)
  | `(aarch64_ccmp_op| ccmn) => pure (.CCMN_reg, .CCMN_imm)
  | _ => throwError "invalid conditional compare mnemonic"

/-- Elaborate an `aarch64_movw_op` into its constructor. -/
def elabMovwOp (stx : TSyntax `aarch64_movw_op) :
    TermElabM ({w : RegWidth} → RegOrZr w → ConstExpr → MovShift w → Operation w) := withRef stx do
  match stx with
  | `(aarch64_movw_op| movz) => pure .MOVZ
  | `(aarch64_movw_op| movk) => pure .MOVK
  | `(aarch64_movw_op| movn) => pure .MOVN
  | _ => throwError "invalid move wide mnemonic"

/-- Elaborate an `aarch64_adr_op` into its constructor and offset validator. -/
def elabAdrOp (stx : TSyntax `aarch64_adr_op) :
    TermElabM ((RegOrZr .W64 → ConstExpr → Operation .W64) × (Int64 → Except String Unit)) := withRef stx do
  match stx with
  | `(aarch64_adr_op| adr)  => pure (.ADR, checkAdrOffset)
  | `(aarch64_adr_op| adrp) => pure (.ADRP, checkAdrpOffset)
  | _ => throwError "invalid address mnemonic"

/-- Elaborate an `aarch64_b_op` into its constructor. -/
def elabBOp (stx : TSyntax `aarch64_b_op) : TermElabM (ConstExpr → Operation .W64) := withRef stx do
  match stx with
  | `(aarch64_b_op| b)  => pure .B
  | `(aarch64_b_op| bl) => pure .BL
  | _ => throwError "invalid branch mnemonic"

/-- Elaborate an `aarch64_br_op` into its constructor. -/
def elabBrOp (stx : TSyntax `aarch64_br_op) : TermElabM (RegOrZr .W64 → Operation .W64) := withRef stx do
  match stx with
  | `(aarch64_br_op| br)  => pure .BR
  | `(aarch64_br_op| blr) => pure .BLR
  | _ => throwError "invalid indirect branch mnemonic"

/-- Elaborate an `aarch64_cbz_op` into its mnemonic (for diagnostics) and constructor. -/
def elabCbzOp (stx : TSyntax `aarch64_cbz_op) :
    TermElabM (String × ({w : RegWidth} → RegOrZr w → ConstExpr → Operation w)) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match sfx with
  | "z"  => pure (stem ++ sfx, .CBZ)
  | "nz" => pure (stem ++ sfx, .CBNZ)
  | _    => throwError "invalid compare-and-branch mnemonic"

/-- Elaborate an `aarch64_tbz_op` into its mnemonic (for diagnostics) and constructor. -/
def elabTbzOp (stx : TSyntax `aarch64_tbz_op) :
    TermElabM (String × ({w : RegWidth} → RegOrZr w → Nat → ConstExpr → Operation w)) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match sfx with
  | "z"  => pure (stem ++ sfx, .TBZ)
  | "nz" => pure (stem ++ sfx, .TBNZ)
  | _    => throwError "invalid test-bit-and-branch mnemonic"

-- ============================================================================
-- Instruction Family Elaboration
-- ============================================================================

/-- Elaborate a single-register load (`ldr`, `ldrb`, ..., with memory or literal source). -/
def elabLoad (op : TSyntax `aarch64_ldr_op) (rt : TSyntax `aarch64_reg) (src : TSyntax `aarch64_load_src) :
    TermElabM Instr := do
  let ⟨w, ctors, rt⟩ ← elabMemOp loadCtors op rt
  let operation ← match src with
    | `(aarch64_load_src| $m:aarch64_mem) => withRef m <| elabScaledAccess ctors rt (← elabMem m w ctors.scale)
    | `(aarch64_load_src| $lit:aarch64_lit) =>
      let some mkLiteral := ctors.lit | throwErrorAt op "literal operands are only supported by ldr and ldrsw"
      pure (mkLiteral rt (← elabLit lit w ctors.pool))
    | _ => throwErrorAt src "invalid load source operand"
  pure ⟨w, operation⟩

/-- Elaborate the `mov` alias: register moves become `orr`/`add`, immediates a single `movz`/`movn`/`orr`. -/
def elabMov (rd : TSyntax `aarch64_reg) (src : TSyntax `aarch64_reg_or_imm) : TermElabM Instr := do
  let ⟨w, rdAny⟩ ← elabAnyRegW rd
  match src with
  | `(aarch64_reg_or_imm| $rn:aarch64_reg) =>
    let rnAny ← elabAnyReg rn w
    if rdAny.isSp || rnAny.isSp then
      return ⟨w, .ADD_e (← elabRegOrSp rd w) (← elabRegOrSp rn w) (.imm { imm := 0, shift := .S0 })⟩
    else
      return ⟨w, .ORR_s (← elabRegOrZr rd w) (.low .XZR w) { reg := ← elabRegOrZr rn w, amount := 0, shift := .LSL }⟩
  | `(aarch64_reg_or_imm| $i:aarch64_imm) =>
    let imm ← elabImm64 i
    -- `sp` destinations and immediates beyond a single move-wide fall back to `orr Rd, xzr, #bitmask`.
    let orr : TermElabM Instr := withRef i do
      unless checkLogicalImmediate w imm matches .ok _ do
        throwError "immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence)"
      return ⟨w, .ORR_i (← elabRegOrSp rd w) (.low .XZR w) (.int64 imm)⟩
    if rdAny.isSp then orr
    else match tryMovzOrMovn w (BitVec.ofInt w.bits imm.toInt) with
      | some (false, imm16, shift) => return ⟨w, .MOVZ (← elabRegOrZr rd w) (.int64 imm16) shift⟩
      | some (true, imm16, shift)  => return ⟨w, .MOVN (← elabRegOrZr rd w) (.int64 imm16) shift⟩
      | none => orr
  | _ => throwErrorAt src "expected register or immediate"

/-- Elaborate a concrete `aarch64_instr` syntax node into a `Lean.Expr` of type `Instr`. -/
def elabInstr (stx : TSyntax `aarch64_instr) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_instr| ${ $t:term }) => elabTerm t (some (mkConst ``Instr))
  | _ =>
    let instr : Instr ← match stx with
      | `(aarch64_instr| $op:aarch64_ldr_op $rt:aarch64_reg, $src:aarch64_load_src) => elabLoad op rt src
      | `(aarch64_instr| $op:aarch64_ldur_op $rt:aarch64_reg, $m:aarch64_mem) =>
        let ⟨w, ctors, rt⟩ ← elabMemOp loadCtors op rt
        pure ⟨w, ctors.unscaled rt (← elabUnscaledMem m)⟩
      | `(aarch64_instr| $op:aarch64_str_op $rt:aarch64_reg, $m:aarch64_mem) =>
        let ⟨w, ctors, rt⟩ ← elabMemOp storeCtors op rt
        pure ⟨w, ← withRef m <| elabScaledAccess ctors rt (← elabMem m w ctors.scale)⟩
      | `(aarch64_instr| $op:aarch64_stur_op $rt:aarch64_reg, $m:aarch64_mem) =>
        let ⟨w, ctors, rt⟩ ← elabMemOp storeCtors op rt
        pure ⟨w, ctors.unscaled rt (← elabUnscaledMem m)⟩
      | `(aarch64_instr| $op:aarch64_pair_op $rt1:aarch64_reg, $rt2:aarch64_reg, $m:aarch64_mem) =>
        let ⟨w, rt1⟩ ← elabRegOrZrW rt1
        let rt2 ← elabRegOrZr rt2 w
        let (accW, mk, isLoad) ← elabPairOp op w
        let mem ← elabPairMem m accW
        withRef m <| ofExcept (checkLdpStpRegisters isLoad rt1 rt2 mem)
        pure ⟨w, mk rt1 rt2 mem⟩
      | `(aarch64_instr| $op:aarch64_arith_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src) =>
        let (stem, flags) ← splitSuffixed op
        let ⟨w, rdAny⟩ ← elabAnyRegW rd
        let rnAny ← elabAnyReg rn w
        let operation : Operation w ← match stem, flags, ← elabArithSrc src w (rdAny.isSp || rnAny.isSp) with
          | "add", "",  .ext e   => pure (.ADD_e  (← elabRegOrSp rd w) (← elabRegOrSp rn w) e)
          | "add", "",  .shift s => pure (.ADD_s  (← elabRegOrZr rd w) (← elabRegOrZr rn w) s)
          | "add", "s", .ext e   => pure (.ADDS_e (← elabRegOrZr rd w) (← elabRegOrSp rn w) e)
          | "add", "s", .shift s => pure (.ADDS_s (← elabRegOrZr rd w) (← elabRegOrZr rn w) s)
          | "sub", "",  .ext e   => pure (.SUB_e  (← elabRegOrSp rd w) (← elabRegOrSp rn w) e)
          | "sub", "",  .shift s => pure (.SUB_s  (← elabRegOrZr rd w) (← elabRegOrZr rn w) s)
          | "sub", "s", .ext e   => pure (.SUBS_e (← elabRegOrZr rd w) (← elabRegOrSp rn w) e)
          | "sub", "s", .shift s => pure (.SUBS_s (← elabRegOrZr rd w) (← elabRegOrZr rn w) s)
          | _, _, _ => throwErrorAt op "invalid add/subtract mnemonic"
        pure ⟨w, operation⟩
      | `(aarch64_instr| $op:aarch64_cmp_op $rn:aarch64_reg, $src:aarch64_src) =>
        let ⟨w, rnAny⟩ ← elabAnyRegW rn
        let xzr : RegOrZr w := .low .XZR w
        let operation : Operation w ← match ← elabArithSrc src w rnAny.isSp with
          | .ext e =>
            let rn ← elabRegOrSp rn w
            match op with
            | `(aarch64_cmp_op| cmp) => pure (.SUBS_e xzr rn e)
            | `(aarch64_cmp_op| cmn) => pure (.ADDS_e xzr rn e)
            | _ => throwErrorAt op "invalid compare mnemonic"
          | .shift s =>
            let rn ← elabRegOrZr rn w
            match op with
            | `(aarch64_cmp_op| cmp) => pure (.SUBS_s xzr rn s)
            | `(aarch64_cmp_op| cmn) => pure (.ADDS_s xzr rn s)
            | _ => throwErrorAt op "invalid compare mnemonic"
        pure ⟨w, operation⟩
      | `(aarch64_instr| $op:aarch64_unary_op $rd:aarch64_reg, $src:aarch64_src) =>
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let xzr : RegOrZr w := .low .XZR w
        let operation : Operation w ← match op with
          | `(aarch64_unary_op| neg)  => pure (.SUB_s  rd xzr (← elabShiftedSrc src w (allowRor := false)))
          | `(aarch64_unary_op| negs) => pure (.SUBS_s rd xzr (← elabShiftedSrc src w (allowRor := false)))
          | `(aarch64_unary_op| mvn)  => pure (.ORN_s  rd xzr (← elabShiftedSrc src w (allowRor := true)))
          | _ => throwErrorAt op "invalid negate/invert mnemonic"
        pure ⟨w, operation⟩
      | `(aarch64_instr| $op:aarch64_logic_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_src) =>
        let ⟨w, _⟩ ← elabAnyRegW rd
        let operation : Operation w ← match ← elabLogicalSrc src w with
          | .imm i =>
            let rn ← elabRegOrZr rn w
            match op with
            | `(aarch64_logic_op| and)  => pure (.AND_i  (← elabRegOrSp rd w) rn i)
            | `(aarch64_logic_op| ands) => pure (.ANDS_i (← elabRegOrZr rd w) rn i)
            | `(aarch64_logic_op| orr)  => pure (.ORR_i  (← elabRegOrSp rd w) rn i)
            | `(aarch64_logic_op| eor)  => pure (.EOR_i  (← elabRegOrSp rd w) rn i)
            | _ => throwErrorAt src "expected register"
          | .shift s =>
            let rd ← elabRegOrZr rd w
            let rn ← elabRegOrZr rn w
            match op with
            | `(aarch64_logic_op| and)  => pure (.AND_s  rd rn s)
            | `(aarch64_logic_op| ands) => pure (.ANDS_s rd rn s)
            | `(aarch64_logic_op| orr)  => pure (.ORR_s  rd rn s)
            | `(aarch64_logic_op| orn)  => pure (.ORN_s  rd rn s)
            | `(aarch64_logic_op| eor)  => pure (.EOR_s  rd rn s)
            | `(aarch64_logic_op| eon)  => pure (.EON_s  rd rn s)
            | `(aarch64_logic_op| bic)  => pure (.BIC_s  rd rn s)
            | `(aarch64_logic_op| bics) => pure (.BICS_s rd rn s)
            | _ => throwErrorAt op "invalid logical mnemonic"
        pure ⟨w, operation⟩
      | `(aarch64_instr| tst $rn:aarch64_reg, $src:aarch64_src) =>
        let ⟨w, rn⟩ ← elabRegOrZrW rn
        let xzr : RegOrZr w := .low .XZR w
        pure ⟨w, match ← elabLogicalSrc src w with
          | .imm i   => .ANDS_i xzr rn i
          | .shift s => .ANDS_s xzr rn s⟩
      | `(aarch64_instr| $op:aarch64_rrr_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg) =>
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let mk ← elabRrrOp op w
        pure ⟨w, mk rd (← elabRegOrZr rn w) (← elabRegOrZr rm w)⟩
      | `(aarch64_instr| $op:aarch64_madd_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg) =>
        let mk ← elabMaddOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        pure ⟨w, mk rd (← elabRegOrZr rn w) (← elabRegOrZr rm w) (← elabRegOrZr ra w)⟩
      | `(aarch64_instr| $op:aarch64_maddl_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $ra:aarch64_reg) =>
        let mk ← elabMaddlOp op
        pure ⟨.W64, mk (← elabRegOrZr rd .W64) (← elabRegOrZr rn .W32) (← elabRegOrZr rm .W32) (← elabRegOrZr ra .W64)⟩
      | `(aarch64_instr| $op:aarch64_mull_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg) =>
        let mk ← elabMullOp op
        pure ⟨.W64, mk (← elabRegOrZr rd .W64) (← elabRegOrZr rn .W32) (← elabRegOrZr rm .W32) .XZR⟩
      | `(aarch64_instr| $op:aarch64_rr_op $rd:aarch64_reg, $rn:aarch64_reg) =>
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let mk ← elabRrOp op w
        pure ⟨w, mk rd (← elabRegOrZr rn w)⟩
      | `(aarch64_instr| $op:aarch64_extend_op $rd:aarch64_reg, $rn:aarch64_reg) =>
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let (imms, mk) ← elabExtendOp op w
        pure ⟨w, mk rd ((← elabRegOrZr rn .W32).withWidth w) 0 imms⟩
      | `(aarch64_instr| $op:aarch64_shift_op $rd:aarch64_reg, $rn:aarch64_reg, $src:aarch64_reg_or_imm) =>
        let (byReg, byImm) ← elabShiftOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let rn ← elabRegOrZr rn w
        match src with
        | `(aarch64_reg_or_imm| $rm:aarch64_reg) => pure ⟨w, byReg rd rn (← elabRegOrZr rm w)⟩
        | `(aarch64_reg_or_imm| $i:aarch64_imm) =>
          let n ← elabImmNat i
          withRef i <| ofExcept (checkBitWidthBound "shift" w n)
          pure ⟨w, byImm rd rn n⟩
        | _ => throwErrorAt src "expected register or immediate"
      | `(aarch64_instr| extr $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $lsb:aarch64_imm) =>
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let n ← elabImmNat lsb
        withRef lsb <| ofExcept (checkBitWidthBound "extr" w n)
        pure ⟨w, .EXTR rd (← elabRegOrZr rn w) (← elabRegOrZr rm w) n⟩
      | `(aarch64_instr| $op:aarch64_bitfield_op $rd:aarch64_reg, $rn:aarch64_reg, $a:aarch64_imm, $b:aarch64_imm) =>
        let (mk, form) ← elabBitfieldOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let rn ← elabRegOrZr rn w
        let (a, b) := ((← elabImmNat a), (← elabImmNat b))
        let (immr, imms) ← match form with
          | .raw =>
            ofExcept (checkBitWidthBound "bitfield" w a)
            ofExcept (checkBitWidthBound "bitfield" w b)
            pure (a, b)
          | .extract =>
            ofExcept (checkBitfieldBounds "bitfield extract" w a b)
            pure (a, a + b - 1)
          | .insert =>
            ofExcept (checkBitfieldBounds "bitfield insert" w a b)
            pure ((w.bits - a) % w.bits, b - 1)
        pure ⟨w, mk rd rn immr imms⟩
      | `(aarch64_instr| $op:aarch64_csel_op $rd:aarch64_reg, $rn:aarch64_reg, $rm:aarch64_reg, $cond:aarch64_cond) =>
        let mk ← elabCselOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        pure ⟨w, mk rd (← elabRegOrZr rn w) (← elabRegOrZr rm w) (← elabCond cond)⟩
      | `(aarch64_instr| $op:aarch64_cinc_op $rd:aarch64_reg, $rn:aarch64_reg, $cond:aarch64_cond) =>
        let mk ← elabCincOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let rn ← elabRegOrZr rn w
        pure ⟨w, mk rd rn rn (← elabCond cond).invert⟩
      | `(aarch64_instr| $op:aarch64_cset_op $rd:aarch64_reg, $cond:aarch64_cond) =>
        let mk ← elabCsetOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let xzr : RegOrZr w := .low .XZR w
        pure ⟨w, mk rd xzr xzr (← elabCond cond).invert⟩
      | `(aarch64_instr| $op:aarch64_ccmp_op $rn:aarch64_reg, $src:aarch64_reg_or_imm, $flags:aarch64_imm, $cond:aarch64_cond) =>
        let (byReg, byImm) ← elabCcmpOp op
        let ⟨w, rn⟩ ← elabRegOrZrW rn
        let nzcv ← elabImmNat flags
        withRef flags <| ofExcept (checkNzcvFlags nzcv)
        let cond ← elabCond cond
        match src with
        | `(aarch64_reg_or_imm| $rm:aarch64_reg) => pure ⟨w, byReg rn (← elabRegOrZr rm w) nzcv cond⟩
        | `(aarch64_reg_or_imm| $i:aarch64_imm) =>
          let imm ← elabImmNat i
          withRef i <| ofExcept (checkCcmpImmediate imm)
          pure ⟨w, byImm rn imm nzcv cond⟩
        | _ => throwErrorAt src "expected register or immediate"
      | `(aarch64_instr| mov $rd:aarch64_reg, $src:aarch64_reg_or_imm) => elabMov rd src
      | `(aarch64_instr| $op:aarch64_movw_op $rd:aarch64_reg, $imm:aarch64_const $[, $shift?:aarch64_modifier]?) =>
        let mk ← elabMovwOp op
        let ⟨w, rd⟩ ← elabRegOrZrW rd
        let immExpr ← elabConst imm
        if let .int64 v := immExpr then
          if v.toInt < 0 || v.toInt > UInt16.maxValue.toInt then
            throwErrorAt imm "move wide immediate {v.toInt} out of range [0, {UInt16.maxValue.toInt}]"
        let shift ← match shift? with
          | none => ofExcept (getMovShift w 0)
          | some sh => elabMovShift sh w
        pure ⟨w, mk rd immExpr shift⟩
      | `(aarch64_instr| $op:aarch64_adr_op $rd:aarch64_reg, $target:aarch64_const) =>
        let (mk, check) ← elabAdrOp op
        pure ⟨.W64, mk (← elabRegOrZr rd .W64) (← elabCheckedConst target check)⟩
      | `(aarch64_instr| $op:aarch64_b_op $target:aarch64_const) =>
        pure ⟨.W64, (← elabBOp op) (← elabCheckedConst target checkBOffset)⟩
      | `(aarch64_instr| $op:aarch64_br_op $rn:aarch64_reg) =>
        pure ⟨.W64, (← elabBrOp op) (← elabRegOrZr rn .W64)⟩
      | `(aarch64_instr| ret $[$rn?:aarch64_reg]?) =>
        pure ⟨.W64, .RET ((← rn?.mapM (elabRegOrZr · .W64)).getD .X30)⟩
      | `(aarch64_instr| $op:aarch64_cbz_op $rt:aarch64_reg, $target:aarch64_const) =>
        let (name, mk) ← elabCbzOp op
        let ⟨w, rt⟩ ← elabRegOrZrW rt
        pure ⟨w, mk rt (← elabCheckedConst target (checkCbzOffset name))⟩
      | `(aarch64_instr| $op:aarch64_tbz_op $rt:aarch64_reg, $bit:aarch64_imm, $target:aarch64_const) =>
        let (name, mk) ← elabTbzOp op
        let ⟨w, rt⟩ ← elabRegOrZrW rt
        let n ← elabImmNat bit
        withRef bit <| ofExcept (checkTbzBitPosition name w n)
        pure ⟨w, mk rt n (← elabCheckedConst target (checkTbzOffset name))⟩
      | `(aarch64_instr| $op:aarch64_bcond_op $target:aarch64_const) =>
        pure ⟨.W64, .B_cond (← elabCond op) (← elabCheckedConst target checkBCondOffset)⟩
      | `(aarch64_instr| nop) => pure ⟨.W64, .NOP⟩
      | _ => throwError "invalid instruction syntax"
    pure (toExpr instr)

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `aarch64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `aarch64_directive) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_directive| $lbl:aarch64_ident :) =>
    return toExpr (Directive.label (← getAsmIdent lbl))
  | `(aarch64_directive| $ins:aarch64_instr) =>
    mkAppM ``Directive.instr #[← elabInstr ins]
  | `(aarch64_directive| ${ $t:term }) =>
    elabTerm t (some (mkConst ``Directive))
  | _ => throwError "invalid assembly directive"

/-- Elaborate an `aarch64_prog` syntax node into a `Lean.Expr` of type `Program` (`List Directive`). -/
def elabProgram (stx : TSyntax `aarch64_prog) : TermElabM Expr := withRef stx do
  match stx with
  | `(aarch64_prog| $dirs:aarch64_directive*) =>
    mkListLit (mkConst ``Directive) (← dirs.toList.mapM elabDirective)
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

/-- Inline unquoted AArch64 assembly block macro/elaborator (`parse( ... )`). -/
scoped elab "parse(" p:aarch64_prog ")" : term => elabProgram p

/-- Compile-time AArch64 string parser/elaborator (`parse("...")`). -/
scoped elab "parse(" s:str ")" : term => withRef s <| elabAArch64 s.getString

/-- Inline unquoted AArch64 assembly block macro/elaborator (`parseAArch64( ... )`). -/
elab "parseAArch64(" p:aarch64_prog ")" : term => elabProgram p

/-- Compile-time AArch64 string parser/elaborator (`parseAArch64("...")`). -/
elab "parseAArch64(" s:str ")" : term => withRef s <| elabAArch64 s.getString

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsStringAArch64(" path:str ")" : term => do
  let contents ← IO.FS.readFile path.getString
  return mkStrLit contents

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
