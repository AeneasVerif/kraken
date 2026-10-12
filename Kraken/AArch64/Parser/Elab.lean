module

public import Kraken.AArch64.Parser.Basic
public meta import Kraken.AArch64.Parser.Basic
public import Kraken.AArch64.Parser.Syntax
public meta import Kraken.AArch64.Parser.Syntax
public meta import Lean

namespace Kraken.AArch64.Parser

open Lean Meta Elab Term

public meta section

-- ============================================================================
-- Helper Types & Named Range Constants
-- ============================================================================

/-- Maximum value of `UInt16` as an `Int` (`2^16 - 1`). -/
def UInt16.maxValue.toInt : Int := 0xffff

/-- Maximum value of `UInt32` as an `Int` (`2^32 - 1`). -/
def UInt32.maxValue.toInt : Int := 0xffffffff

/-- Maximum value of `UInt64` as an `Int` (`2^64 - 1`). -/
def UInt64.maxValue.toInt : Int := 0xffffffffffffffff

/-- Total number of distinct `UInt64` values (`2^64`). -/
def UInt64.modulus : Int := UInt64.maxValue.toInt + 1

/-- Minimum signed 9-bit pre/post-indexed load/store immediate offset (`-256`). -/
def prePostOffsetMin : Int := -256

/-- Maximum signed 9-bit pre/post-indexed load/store immediate offset (`255`). -/
def prePostOffsetMax : Int := 255

/-- Lift an `Except String α` domain check into `TermElabM α`, anchoring errors at `stx`. -/
def liftCheck {α : Type} (stx : Syntax) (res : Except String α) : TermElabM α :=
  match res with
  | .ok v => pure v
  | .error msg => throwErrorAt stx msg

-- ============================================================================
-- Identifier, Constant Expression & Immediate Elaboration
-- ============================================================================

/-- Extract raw assembly identifier string from an `aarch64_ident` syntax node. -/
def getAsmIdent : TSyntax `aarch64_ident → TermElabM String
  | ⟨.node _ _ #[.atom _ s]⟩ => pure s
  | stx => throwErrorAt stx "expected assembly identifier"

/-- Convert a signed arbitrary-precision `Int` into `Int64`, checking 64-bit range. -/
def intToInt64Checked (stx : Syntax) (v : Int) : TermElabM Int64 := do
  if v < Int64.minValue.toInt || v > UInt64.maxValue.toInt then
    throwErrorAt stx "immediate {v} out of 64-bit range"
  if v > Int64.maxValue.toInt then
    pure (Int64.ofInt (v - UInt64.modulus))
  else
    pure (Int64.ofInt v)

/-- Elaborate an `aarch64_const` node as a signed integer `Int`. -/
def elabConstRawInt (stx : TSyntax `aarch64_const) : TermElabM Int :=
  match stx with
  | `(aarch64_const| $n:num)
  | `(aarch64_const| #$n:num)
  | `(aarch64_const| +$n:num)
  | `(aarch64_const| #+$n:num) => pure (Int.ofNat n.getNat)
  | `(aarch64_const| -$n:num)
  | `(aarch64_const| #-$n:num) => pure (-(Int.ofNat n.getNat))
  | _ => throwErrorAt stx "expected integer immediate"

/-- Elaborate an `aarch64_operand` node as a signed integer `Int`. -/
def elabRawInt (stx : TSyntax `aarch64_operand) : TermElabM Int :=
  match stx with
  | `(aarch64_operand| $c:aarch64_const) => elabConstRawInt c
  | _ => throwErrorAt stx "expected integer immediate"

/-- Elaborate an `aarch64_const` node as `Int64`. -/
def elabConstInt64 (stx : TSyntax `aarch64_const) : TermElabM Int64 := do
  let v ← elabConstRawInt stx
  intToInt64Checked stx v

/-- Elaborate an `aarch64_operand` immediate node as `Int64`. -/
def elabInt64 (stx : TSyntax `aarch64_operand) : TermElabM Int64 := do
  let v ← elabRawInt stx
  intToInt64Checked stx v

/-- Elaborate an `aarch64_const` node as a non-negative `Nat`. -/
def elabConstImmNat (stx : TSyntax `aarch64_const) : TermElabM Nat := do
  let v ← elabConstRawInt stx
  if v < 0 then
    throwErrorAt stx "expected non-negative immediate, got {v}"
  pure v.toNat

/-- Elaborate an `aarch64_operand` immediate node as a non-negative `Nat`. -/
def elabImmNat (stx : TSyntax `aarch64_operand) : TermElabM Nat := do
  let v ← elabRawInt stx
  if v < 0 then
    throwErrorAt stx "expected non-negative immediate, got {v}"
  pure v.toNat

/-- True when `c` represents an integer literal or relocation constant rather than a bare symbol. -/
def isConstLiteralOrReloc : TSyntax `aarch64_const → Bool
  | `(aarch64_const| $_:num)
  | `(aarch64_const| #$_:num)
  | `(aarch64_const| -$_:num)
  | `(aarch64_const| #-$_:num)
  | `(aarch64_const| +$_:num)
  | `(aarch64_const| #+$_:num)
  | `(aarch64_const| : $_:aarch64_ident : $_:aarch64_const)
  | `(aarch64_const| #: $_:aarch64_ident : $_:aarch64_const) => true
  | _ => false

/-- True when `op` represents an integer literal or relocation constant rather than a register/bare symbol. -/
def isConstOrReloc : TSyntax `aarch64_operand → Bool
  | `(aarch64_operand| $c:aarch64_const) => isConstLiteralOrReloc c
  | _ => false

/-- Elaborate an `aarch64_const` node into a `ConstExpr`. -/
partial def elabConstNode (stx : TSyntax `aarch64_const) : TermElabM ConstExpr := do
  match stx with
  | `(aarch64_const| $_:num)
  | `(aarch64_const| #$_:num)
  | `(aarch64_const| -$_:num)
  | `(aarch64_const| #-$_:num)
  | `(aarch64_const| +$_:num)
  | `(aarch64_const| #+$_:num) => do
    let i ← elabConstInt64 stx
    pure (.int64 i)
  | `(aarch64_const| : $modId:aarch64_ident : $innerStx:aarch64_const)
  | `(aarch64_const| #: $modId:aarch64_ident : $innerStx:aarch64_const) => do
    let modName ← getAsmIdent modId
    let inner ← elabConstNode innerStx
    match modName.toLower with
    | "pg_hi21" => pure (.pg_hi21 inner)
    | "lo12"    => pure (.lo12 inner)
    | _         => throwErrorAt modId "unknown relocation modifier: {modName}"
  | `(aarch64_const| $id:aarch64_ident) => do
    let s ← getAsmIdent id
    pure (.label s)
  | _ => throwErrorAt stx "invalid constant expression"

/-- Elaborate an `aarch64_operand` constant node into a `ConstExpr`. -/
def elabConstExpr (stx : TSyntax `aarch64_operand) : TermElabM ConstExpr :=
  match stx with
  | `(aarch64_operand| $c:aarch64_const) => elabConstNode c
  | _ => throwErrorAt stx "invalid constant expression"

-- ============================================================================
-- Register & Condition Code Elaboration
-- ============================================================================

/-- Elaborate an `aarch64_reg` syntax node directly into a width-tagged `AnyRegW`. -/
def elabRegSyntax (stx : TSyntax `aarch64_reg) : TermElabM AnyRegW :=
  match stx with
  | `(aarch64_reg| x0)  => pure ⟨.W64, .gpr .X0⟩  | `(aarch64_reg| x1)  => pure ⟨.W64, .gpr .X1⟩
  | `(aarch64_reg| x2)  => pure ⟨.W64, .gpr .X2⟩  | `(aarch64_reg| x3)  => pure ⟨.W64, .gpr .X3⟩
  | `(aarch64_reg| x4)  => pure ⟨.W64, .gpr .X4⟩  | `(aarch64_reg| x5)  => pure ⟨.W64, .gpr .X5⟩
  | `(aarch64_reg| x6)  => pure ⟨.W64, .gpr .X6⟩  | `(aarch64_reg| x7)  => pure ⟨.W64, .gpr .X7⟩
  | `(aarch64_reg| x8)  => pure ⟨.W64, .gpr .X8⟩  | `(aarch64_reg| x9)  => pure ⟨.W64, .gpr .X9⟩
  | `(aarch64_reg| x10) => pure ⟨.W64, .gpr .X10⟩ | `(aarch64_reg| x11) => pure ⟨.W64, .gpr .X11⟩
  | `(aarch64_reg| x12) => pure ⟨.W64, .gpr .X12⟩ | `(aarch64_reg| x13) => pure ⟨.W64, .gpr .X13⟩
  | `(aarch64_reg| x14) => pure ⟨.W64, .gpr .X14⟩ | `(aarch64_reg| x15) => pure ⟨.W64, .gpr .X15⟩
  | `(aarch64_reg| x16) => pure ⟨.W64, .gpr .X16⟩ | `(aarch64_reg| x17) => pure ⟨.W64, .gpr .X17⟩
  | `(aarch64_reg| x18) => pure ⟨.W64, .gpr .X18⟩ | `(aarch64_reg| x19) => pure ⟨.W64, .gpr .X19⟩
  | `(aarch64_reg| x20) => pure ⟨.W64, .gpr .X20⟩ | `(aarch64_reg| x21) => pure ⟨.W64, .gpr .X21⟩
  | `(aarch64_reg| x22) => pure ⟨.W64, .gpr .X22⟩ | `(aarch64_reg| x23) => pure ⟨.W64, .gpr .X23⟩
  | `(aarch64_reg| x24) => pure ⟨.W64, .gpr .X24⟩ | `(aarch64_reg| x25) => pure ⟨.W64, .gpr .X25⟩
  | `(aarch64_reg| x26) => pure ⟨.W64, .gpr .X26⟩ | `(aarch64_reg| x27) => pure ⟨.W64, .gpr .X27⟩
  | `(aarch64_reg| x28) => pure ⟨.W64, .gpr .X28⟩ | `(aarch64_reg| x29) => pure ⟨.W64, .gpr .X29⟩
  | `(aarch64_reg| x30) => pure ⟨.W64, .gpr .X30⟩ | `(aarch64_reg| lr)  => pure ⟨.W64, .gpr .X30⟩
  | `(aarch64_reg| w0)  => pure ⟨.W32, .gpr .X0⟩  | `(aarch64_reg| w1)  => pure ⟨.W32, .gpr .X1⟩
  | `(aarch64_reg| w2)  => pure ⟨.W32, .gpr .X2⟩  | `(aarch64_reg| w3)  => pure ⟨.W32, .gpr .X3⟩
  | `(aarch64_reg| w4)  => pure ⟨.W32, .gpr .X4⟩  | `(aarch64_reg| w5)  => pure ⟨.W32, .gpr .X5⟩
  | `(aarch64_reg| w6)  => pure ⟨.W32, .gpr .X6⟩  | `(aarch64_reg| w7)  => pure ⟨.W32, .gpr .X7⟩
  | `(aarch64_reg| w8)  => pure ⟨.W32, .gpr .X8⟩  | `(aarch64_reg| w9)  => pure ⟨.W32, .gpr .X9⟩
  | `(aarch64_reg| w10) => pure ⟨.W32, .gpr .X10⟩ | `(aarch64_reg| w11) => pure ⟨.W32, .gpr .X11⟩
  | `(aarch64_reg| w12) => pure ⟨.W32, .gpr .X12⟩ | `(aarch64_reg| w13) => pure ⟨.W32, .gpr .X13⟩
  | `(aarch64_reg| w14) => pure ⟨.W32, .gpr .X14⟩ | `(aarch64_reg| w15) => pure ⟨.W32, .gpr .X15⟩
  | `(aarch64_reg| w16) => pure ⟨.W32, .gpr .X16⟩ | `(aarch64_reg| w17) => pure ⟨.W32, .gpr .X17⟩
  | `(aarch64_reg| w18) => pure ⟨.W32, .gpr .X18⟩ | `(aarch64_reg| w19) => pure ⟨.W32, .gpr .X19⟩
  | `(aarch64_reg| w20) => pure ⟨.W32, .gpr .X20⟩ | `(aarch64_reg| w21) => pure ⟨.W32, .gpr .X21⟩
  | `(aarch64_reg| w22) => pure ⟨.W32, .gpr .X22⟩ | `(aarch64_reg| w23) => pure ⟨.W32, .gpr .X23⟩
  | `(aarch64_reg| w24) => pure ⟨.W32, .gpr .X24⟩ | `(aarch64_reg| w25) => pure ⟨.W32, .gpr .X25⟩
  | `(aarch64_reg| w26) => pure ⟨.W32, .gpr .X26⟩ | `(aarch64_reg| w27) => pure ⟨.W32, .gpr .X27⟩
  | `(aarch64_reg| w28) => pure ⟨.W32, .gpr .X28⟩ | `(aarch64_reg| w29) => pure ⟨.W32, .gpr .X29⟩
  | `(aarch64_reg| w30) => pure ⟨.W32, .gpr .X30⟩
  | `(aarch64_reg| sp)  => pure ⟨.W64, .sp⟩
  | `(aarch64_reg| wsp) => pure ⟨.W32, .sp⟩
  | `(aarch64_reg| xzr) => pure ⟨.W64, .xzr⟩
  | `(aarch64_reg| wzr) => pure ⟨.W32, .xzr⟩
  | _ => throwErrorAt stx "unknown register"

/-- Extract non-register symbol name from an operand syntax node (e.g. condition code, modifier, or label). -/
def getOperandSym (stx : TSyntax `aarch64_operand) : TermElabM String :=
  match stx with
  | `(aarch64_operand| $id:aarch64_ident) => getAsmIdent id
  | _ => throwErrorAt stx "expected identifier"

def checkRegWidthM {T : RegWidth → Type} (stx : Syntax) (expected actual : RegWidth) (val : T actual) :
    TermElabM (T expected) :=
  if h : expected = actual then
    pure (h ▸ val)
  else
    throwErrorAt stx "expected {expected} register, got {actual}"

def anyToRegOrSp (stx : Syntax) {w : RegWidth} : AnyReg w → TermElabM (RegOrSp w)
  | .gpr r => pure (.low (.reg r) w)
  | .sp    => pure (.low .SP w)
  | .xzr   => throwErrorAt stx "xzr/wzr not allowed in immediate/extended register instruction (sp expected)"

def anyToRegOrZr (stx : Syntax) {w : RegWidth} : AnyReg w → TermElabM (RegOrZr w)
  | .gpr r => pure (.low (.reg r) w)
  | .xzr   => pure (.low .XZR w)
  | .sp    => throwErrorAt stx "sp/wsp not allowed in shifted register instruction (xzr expected)"

def elabRegNodeOrSpW (stx : TSyntax `aarch64_reg) : TermElabM RegOrSpW := do
  let ⟨w, r⟩ ← elabRegSyntax stx
  pure ⟨w, ← anyToRegOrSp stx r⟩

def elabRegNodeOrZrW (stx : TSyntax `aarch64_reg) : TermElabM RegOrZrW := do
  let ⟨w, r⟩ ← elabRegSyntax stx
  pure ⟨w, ← anyToRegOrZr stx r⟩

def elabRegNodeOrSp (stx : TSyntax `aarch64_reg) (w : RegWidth) : TermElabM (RegOrSp w) := do
  let ⟨w', r⟩ ← elabRegNodeOrSpW stx
  checkRegWidthM stx w w' r

def elabAnyRegW (stx : TSyntax `aarch64_operand) : TermElabM AnyRegW :=
  match stx with
  | `(aarch64_operand| $r:aarch64_reg) => elabRegSyntax r
  | _ => throwErrorAt stx "expected register"

def elabAnyReg (stx : TSyntax `aarch64_operand) (w : RegWidth) : TermElabM (AnyReg w) := do
  let ⟨w', r⟩ ← elabAnyRegW stx
  checkRegWidthM stx w w' r

def elabRegOrSpW (stx : TSyntax `aarch64_operand) : TermElabM RegOrSpW := do
  let ⟨w, r⟩ ← elabAnyRegW stx
  pure ⟨w, ← anyToRegOrSp stx r⟩

def elabRegOrZrW (stx : TSyntax `aarch64_operand) : TermElabM RegOrZrW := do
  let ⟨w, r⟩ ← elabAnyRegW stx
  pure ⟨w, ← anyToRegOrZr stx r⟩

def elabRegOrSp (stx : TSyntax `aarch64_operand) (w : RegWidth) : TermElabM (RegOrSp w) := do
  let ⟨w', r⟩ ← elabRegOrSpW stx
  checkRegWidthM stx w w' r

def elabRegOrZr (stx : TSyntax `aarch64_operand) (w : RegWidth) : TermElabM (RegOrZr w) := do
  let ⟨w', r⟩ ← elabRegOrZrW stx
  checkRegWidthM stx w w' r

def elabCondArg (stx : TSyntax `aarch64_operand) : TermElabM CondCode := do
  let name ← getOperandSym stx
  match parseCondCode name with
  | some c => pure c
  | none   => throwErrorAt stx "unknown condition code: {name}"

-- ============================================================================
-- Memory Addressing & Shift/Extend Operand Elaboration
-- ============================================================================

/-- Elaborate an `aarch64_mem` node into an `AddrExpr`. -/
def elabMemAddr (mStx : TSyntax `aarch64_mem) (w : RegWidth) (allowUnscaled : Bool := false)
    (scale : Nat := w.bytes) : TermElabM AddrExpr :=
  match mStx with
  | `(aarch64_mem| [$b:aarch64_reg]) => do
    let base ← elabRegNodeOrSp b .W64
    pure ⟨base, .imm { imm := 0, index := none }⟩
  | `(aarch64_mem| [$b:aarch64_reg], $off:aarch64_const) => do
    let base ← elabRegNodeOrSp b .W64
    let imm ← elabConstInt64 off
    if imm.toInt < prePostOffsetMin || imm.toInt > prePostOffsetMax then
      throwErrorAt off "post-indexed offset {imm.toInt} out of range [-256, 255]"
    pure ⟨base, .imm { imm, index := some .Post }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]!) => do
    let base ← elabRegNodeOrSp b .W64
    let expr ← elabConstNode off
    match expr with
    | .int64 imm =>
      if imm.toInt < prePostOffsetMin || imm.toInt > prePostOffsetMax then
        throwErrorAt off "pre-indexed offset {imm.toInt} out of range [-256, 255]"
    | _ =>
      throwErrorAt off "pre-indexed / post-indexed offsets must be constant numeric immediates"
    pure ⟨base, .imm { imm := expr, index := some .Pre }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $off:aarch64_const]) => do
    let base ← elabRegNodeOrSp b .W64
    let expr ← elabConstNode off
    if let .int64 imm := expr then
      liftCheck off (checkLoadStoreOffset w imm allowUnscaled scale)
    pure ⟨base, .imm { imm := expr, index := none }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg]) => do
    let base ← elabRegNodeOrSp b .W64
    let regW ← elabRegNodeOrZrW rm
    let extType := match regW.w with
      | .W64 => MemExtendType.UXTX
      | .W32 => MemExtendType.UXTW
    pure ⟨base, .reg { reg := regW, ext := { type := extType, amount := .E0 } }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg, $extId:aarch64_ident]) => do
    let base ← elabRegNodeOrSp b .W64
    let regW ← elabRegNodeOrZrW rm
    let extName ← getAsmIdent extId
    let extType ← liftCheck extId (getMemExtendType extName regW.w)
    let amount ← liftCheck mStx (getMemExtendAmount w 0 scale)
    pure ⟨base, .reg { reg := regW, ext := { type := extType, amount } }⟩
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg, $extId:aarch64_ident $amtStx:aarch64_const])
  | `(aarch64_mem| [$b:aarch64_reg, $rm:aarch64_reg, $extId:aarch64_ident, $amtStx:aarch64_const]) => do
    let base ← elabRegNodeOrSp b .W64
    let regW ← elabRegNodeOrZrW rm
    let extName ← getAsmIdent extId
    let extType ← liftCheck extId (getMemExtendType extName regW.w)
    let amt ← elabConstImmNat amtStx
    let amount ← liftCheck mStx (getMemExtendAmount w amt scale)
    pure ⟨base, .reg { reg := regW, ext := { type := extType, amount } }⟩
  | _ => throwErrorAt mStx "invalid memory operand"

/-- Elaborate standard AArch64 memory addressing (`LDR` / `STR` / `LDRB` / `STRB` / etc.). -/
def elabAddr (stx : TSyntax `aarch64_operand) (w : RegWidth) (allowUnscaled : Bool := false)
    (scale : Nat := w.bytes) : TermElabM AddrExpr :=
  match stx with
  | `(aarch64_operand| $m:aarch64_mem) => elabMemAddr m w allowUnscaled scale
  | _ => throwErrorAt stx "expected memory operand `[base, ...]`"

/-- Elaborate unscaled memory addressing (`LDUR` / `STUR`). -/
def elabUnscaledAddr (stx : TSyntax `aarch64_operand) : TermElabM UnscaledAddrExpr :=
  match stx with
  | `(aarch64_operand| [$b:aarch64_reg]) => do
    let base ← elabRegNodeOrSp b .W64
    pure { base, imm := .int64 0 }
  | `(aarch64_operand| [$b:aarch64_reg, $off:aarch64_const]) => do
    let base ← elabRegNodeOrSp b .W64
    let expr ← elabConstNode off
    if let .int64 imm := expr then
      liftCheck off (checkUnscaledOffset imm)
    pure { base, imm := expr }
  | `(aarch64_operand| [$_:aarch64_reg, $rm:aarch64_reg]) =>
    throwErrorAt rm "expected immediate offset in unscaled address operand"
  | _ => throwErrorAt stx "invalid unscaled address operand"

/-- Elaborate `LDR` memory or literal-pool operand (`[base, ...]`, `=const`, or `label`). -/
def elabAddrOrLit (stx : TSyntax `aarch64_operand) (w : RegWidth) (allowUnscaled : Bool := false)
    (scale : Nat := w.bytes) (allowPool : Bool := true) : TermElabM AddrOrLit :=
  match stx with
  | `(aarch64_operand| $m:aarch64_mem) => do
    let addr ← elabMemAddr m w allowUnscaled scale
    pure (.addr addr)
  | `(aarch64_operand| = $c:aarch64_const) => do
    if !allowPool then
      throwErrorAt stx "literal pool (=expr) is not supported for ldrsw"
    let e ← elabConstNode c
    if w == .W32 then
      if let .int64 imm := e then
        if imm.toInt < Int32.minValue.toInt || imm.toInt > UInt32.maxValue.toInt then
          throwErrorAt c "literal pool immediate {imm.toInt} too large for 32-bit register"
    pure (.lit (.pool { expr := e }))
  | `(aarch64_operand| $_:aarch64_const) => do
    let l ← getOperandSym stx
    pure (.lit (.addr { label := l }))
  | _ => throwErrorAt stx "invalid load address or literal operand"

/-- Elaborate `LDP` / `STP` pair memory addressing. -/
def elabPairAddr (stx : TSyntax `aarch64_operand) (w : RegWidth) : TermElabM AddrExpr :=
  match stx with
  | `(aarch64_operand| [$b:aarch64_reg]) => do
    let base ← elabRegNodeOrSp b .W64
    pure ⟨base, .imm { imm := 0, index := none }⟩
  | `(aarch64_operand| [$b:aarch64_reg], $off:aarch64_const) => do
    let base ← elabRegNodeOrSp b .W64
    let imm ← elabConstInt64 off
    liftCheck off (checkPairOffset w imm)
    pure ⟨base, .imm { imm, index := some .Post }⟩
  | `(aarch64_operand| [$b:aarch64_reg, $off:aarch64_const]!) => do
    let base ← elabRegNodeOrSp b .W64
    let imm ← elabConstInt64 off
    liftCheck off (checkPairOffset w imm)
    pure ⟨base, .imm { imm, index := some .Pre }⟩
  | `(aarch64_operand| [$b:aarch64_reg, $off:aarch64_const]) => do
    let base ← elabRegNodeOrSp b .W64
    if isConstLiteralOrReloc off then
      let imm ← elabConstInt64 off
      liftCheck off (checkPairOffset w imm)
      pure ⟨base, .imm { imm, index := none }⟩
    else
      throwErrorAt off "register offsets are not supported for ldp/stp instructions"
  | `(aarch64_operand| $m:aarch64_mem) =>
    throwErrorAt m "register offsets are not supported for ldp/stp instructions"
  | _ => throwErrorAt stx "invalid pair memory operand"

/-- Elaborate an optional shift/extend modifier operand (`lsl #2`, `uxtw`, `uxtw #2`). -/
def elabExtendModifier (modStx : TSyntax `aarch64_operand) (instrW : RegWidth) (regW : RegWidth) :
    TermElabM (ExtendType × ExtendAmount) := do
  match modStx with
  | `(aarch64_operand| $extId:aarch64_ident $amtStx:aarch64_const) =>
    let extName ← getAsmIdent extId
    let extType ← liftCheck extId (getExtendType extName instrW regW)
    let val ← elabConstImmNat amtStx
    let amount ← match val with
      | 0 => pure ExtendAmount.E0
      | 1 => pure ExtendAmount.E1
      | 2 => pure ExtendAmount.E2
      | 3 => pure ExtendAmount.E3
      | 4 => pure ExtendAmount.E4
      | _ => throwErrorAt amtStx "invalid extend amount: {val}"
    pure (extType, amount)
  | `(aarch64_operand| $extId:aarch64_ident) =>
    let extName ← getAsmIdent extId
    let extType ← liftCheck extId (getExtendType extName instrW regW)
    pure (extType, .E0)
  | _ => throwErrorAt modStx "expected extension or shift modifier"

/-- Elaborate shifted register operands (`Rm` or `Rm, shift #amt`). -/
def elabShiftRegTail (stx : Syntax) (tail : List (TSyntax `aarch64_operand)) (w : RegWidth)
    (allowRor : Bool := false) : TermElabM (ShiftRegExpr w) := do
  match tail with
  | [rmStx] =>
    let reg ← elabRegOrZr rmStx w
    pure { reg, amount := 0, shift := .LSL }
  | [rmStx, modStx] =>
    let reg ← elabRegOrZr rmStx w
    match modStx with
    | `(aarch64_operand| $shiftId:aarch64_ident $amtStx:aarch64_const) =>
      let shiftName ← getAsmIdent shiftId
      let shiftType ← match shiftName.toLower with
        | "lsl" => pure ShiftType.LSL
        | "lsr" => pure ShiftType.LSR
        | "asr" => pure ShiftType.ASR
        | "ror" =>
          if allowRor then pure ShiftType.ROR
          else throwErrorAt shiftId "arithmetic instructions do not support ROR shift"
        | _ => throwErrorAt shiftId "unknown shift type: {shiftName}"
      let amt ← elabConstInt64 amtStx
      liftCheck amtStx (checkShiftAmount w amt)
      pure { reg, amount := amt, shift := shiftType }
    | _ => throwErrorAt modStx "expected shift modifier (e.g. `lsl #2`)"
  | _ => throwErrorAt stx "unexpected operand count"

/-- Elaborate immediate or extended-register tail operands (`#imm`, `#imm, lsl #12`, `Rm`, `Rm, ext #amt`). -/
def elabExtOrImmTail (stx : Syntax) (tail : List (TSyntax `aarch64_operand)) (w : RegWidth) :
    TermElabM ExtOrImmReg := do
  match tail with
  | [op] =>
    if isConstOrReloc op then
      let expr ← elabConstExpr op
      if let .int64 imm := expr then
        liftCheck op (checkArithmeticImmediate imm)
      pure (.imm { imm := expr, shift := .S0 })
    else
      let regW ← elabRegOrZrW op
      if regW.w != w then
        throwErrorAt op "expected {w} register, got {regW.w}"
      let extType := match regW.w with
        | .W64 => ExtendType.UXTX
        | .W32 => ExtendType.UXTW
      pure (.ext { reg := regW, ext := { type := extType, amount := .E0 } })
  | [op, modStx] =>
    if isConstOrReloc op then
      let expr ← elabConstExpr op
      match modStx with
      | `(aarch64_operand| $shiftId:aarch64_ident $amtStx:aarch64_const) =>
        let shiftName ← getAsmIdent shiftId
        if shiftName.toLower != "lsl" then
          throwErrorAt shiftId "expected lsl for immediate shift, got {shiftName}"
        let amt ← elabConstImmNat amtStx
        match expr with
        | .int64 imm =>
          liftCheck op (checkArithmeticImmediate imm)
          if amt == 12 then
            pure (.imm { imm := expr, shift := .S12 })
          else if amt == 0 then
            pure (.imm { imm := expr, shift := .S0 })
          else
            throwErrorAt amtStx "invalid immediate shift for add: {amt} (must be 0 or 12)"
        | _ =>
          throwErrorAt op "relocation modifiers and labels cannot be shifted with lsl in immediate operands"
      | _ => throwErrorAt modStx "expected `lsl #0` or `lsl #12`"
    else
      let regW ← elabRegOrZrW op
      let (extType, amount) ← elabExtendModifier modStx w regW.w
      pure (.ext { reg := regW, ext := { type := extType, amount } })
  | _ => throwErrorAt stx "unexpected operand count"

-- ============================================================================
-- Instruction Family Elaborators
-- ============================================================================

abbrev OperandStx := TSyntax `aarch64_operand

/-- Decide whether tail operands form a valid shifted-register operand (vs immediate/extended). -/
def tryShiftRegTail? (stx : Syntax) (tail : List OperandStx) (w : RegWidth) :
    TermElabM (Option (ShiftRegExpr w)) := do
  match tail with
  | first :: _ =>
    if isConstOrReloc first then
      return none
    try
      let sr ← withoutModifyingState (elabShiftRegTail stx tail w false)
      return some sr
    catch _ =>
      return none
  | [] => return none

def elabArithNoFlags (stx : Syntax) (ops : Array OperandStx)
    (mkE : {w : RegWidth} → RegOrSp w → RegOrSp w → ExtOrImmReg → Operation w)
    (mkS : {w : RegWidth} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | dstStx :: srcStx :: rest =>
    if rest.isEmpty || rest.length > 2 then
      throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"
    let op1W ← elabAnyRegW dstStx
    let w := op1W.1
    let op2 ← elabAnyReg srcStx w
    if op1W.2.isSp || op2.isSp then
      let dstSp ← anyToRegOrSp dstStx op1W.2
      let src1Sp ← anyToRegOrSp srcStx op2
      let op3 ← elabExtOrImmTail stx rest w
      pure ⟨w, mkE dstSp src1Sp op3⟩
    else if op1W.2.isXzr || op2.isXzr then
      let dstZr ← anyToRegOrZr dstStx op1W.2
      let src1Zr ← anyToRegOrZr srcStx op2
      let shiftOp ← elabShiftRegTail stx rest w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩
    else
      match ← tryShiftRegTail? stx rest w with
      | some shiftOp =>
        let dstZr ← anyToRegOrZr dstStx op1W.2
        let src1Zr ← anyToRegOrZr srcStx op2
        pure ⟨w, mkS dstZr src1Zr shiftOp⟩
      | none =>
        let dstSp ← anyToRegOrSp dstStx op1W.2
        let src1Sp ← anyToRegOrSp srcStx op2
        let extOp ← elabExtOrImmTail stx rest w
        pure ⟨w, mkE dstSp src1Sp extOp⟩
  | _ => throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"

def elabArithFlags (stx : Syntax) (instrName : String) (ops : Array OperandStx)
    (mkE : {w : RegWidth} → RegOrZr w → RegOrSp w → ExtOrImmReg → Operation w)
    (mkS : {w : RegWidth} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | dstStx :: srcStx :: rest =>
    if rest.isEmpty || rest.length > 2 then
      throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"
    let op1W ← elabAnyRegW dstStx
    let w := op1W.1
    let op2 ← elabAnyReg srcStx w
    if op1W.2.isSp then
      throwErrorAt dstStx "SP/WSP is not allowed as destination of {instrName}"
    else if op2.isSp then
      let dstZr ← anyToRegOrZr dstStx op1W.2
      let src1Sp ← anyToRegOrSp srcStx op2
      let op3 ← elabExtOrImmTail stx rest w
      pure ⟨w, mkE dstZr src1Sp op3⟩
    else if op2.isXzr then
      let dstZr ← anyToRegOrZr dstStx op1W.2
      let src1Zr ← anyToRegOrZr srcStx op2
      let shiftOp ← elabShiftRegTail stx rest w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩
    else
      match ← tryShiftRegTail? stx rest w with
      | some shiftOp =>
        let dstZr ← anyToRegOrZr dstStx op1W.2
        let src1Zr ← anyToRegOrZr srcStx op2
        pure ⟨w, mkS dstZr src1Zr shiftOp⟩
      | none =>
        let dstZr ← anyToRegOrZr dstStx op1W.2
        let src1Sp ← anyToRegOrSp srcStx op2
        let extOp ← elabExtOrImmTail stx rest w
        pure ⟨w, mkE dstZr src1Sp extOp⟩
  | _ => throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"

def elabCompare (stx : Syntax) (ops : Array OperandStx)
    (mkE : {w : RegWidth} → RegOrZr w → RegOrSp w → ExtOrImmReg → Operation w)
    (mkS : {w : RegWidth} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | srcStx :: rest =>
    if rest.isEmpty || rest.length > 2 then
      throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"
    let op1W ← elabAnyRegW srcStx
    let w := op1W.1
    let dstZr : RegOrZr w := .low .XZR w
    if op1W.2.isSp then
      let src1Sp ← anyToRegOrSp srcStx op1W.2
      let op2 ← elabExtOrImmTail stx rest w
      pure ⟨w, mkE dstZr src1Sp op2⟩
    else if op1W.2.isXzr then
      let src1Zr ← anyToRegOrZr srcStx op1W.2
      let shiftOp ← elabShiftRegTail stx rest w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩
    else
      match ← tryShiftRegTail? stx rest w with
      | some shiftOp =>
        let src1Zr ← anyToRegOrZr srcStx op1W.2
        pure ⟨w, mkS dstZr src1Zr shiftOp⟩
      | none =>
        let src1Sp ← anyToRegOrSp srcStx op1W.2
        let extOp ← elabExtOrImmTail stx rest w
        pure ⟨w, mkE dstZr src1Sp extOp⟩
  | _ => throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"

def elabLogicalNoFlags (stx : Syntax) (ops : Array OperandStx)
    (mkI : {w : RegWidth} → RegOrSp w → RegOrZr w → ConstExpr → Operation w)
    (mkS : {w : RegWidth} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | dstStx :: srcStx :: third :: extra =>
    let dstW ← elabAnyRegW dstStx
    let w := dstW.1
    let src1 ← elabRegOrZr srcStx w
    if isConstOrReloc third then
      if !extra.isEmpty then
        throwErrorAt stx "expected 3 operands, got {ops.size}"
      let dstSp ← anyToRegOrSp dstStx dstW.2
      let imm ← elabConstExpr third
      if let .int64 val := imm then
        liftCheck third (checkLogicalImmediate w val)
      pure ⟨w, mkI dstSp src1 imm⟩
    else
      let dstZr ← anyToRegOrZr dstStx dstW.2
      let shiftOp ← elabShiftRegTail stx (third :: extra) w true
      pure ⟨w, mkS dstZr src1 shiftOp⟩
  | _ => throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"

def elabLogicalFlags (stx : Syntax) (ops : Array OperandStx)
    (mkI : {w : RegWidth} → RegOrZr w → RegOrZr w → ConstExpr → Operation w)
    (mkS : {w : RegWidth} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | dstStx :: srcStx :: third :: extra =>
    let dstW ← elabRegOrZrW dstStx
    let w := dstW.w
    let src1 ← elabRegOrZr srcStx w
    if isConstOrReloc third then
      if !extra.isEmpty then
        throwErrorAt stx "expected 3 operands, got {ops.size}"
      let imm ← elabConstExpr third
      if let .int64 val := imm then
        liftCheck third (checkLogicalImmediate w val)
      pure ⟨w, mkI dstW.reg src1 imm⟩
    else
      let shiftOp ← elabShiftRegTail stx (third :: extra) w true
      pure ⟨w, mkS dstW.reg src1 shiftOp⟩
  | _ => throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"

def elabMov (stx : Syntax) (ops : Array OperandStx) : TermElabM Instr := do
  match ops with
  | #[dstStx, srcStx] =>
    let dstW ← elabAnyRegW dstStx
    let w := dstW.1
    if isConstOrReloc srcStx then
      let imm ← elabConstExpr srcStx
      if let .int64 val := imm then
        if !dstW.2.isSp then
          let dstZr ← anyToRegOrZr dstStx dstW.2
          let valBitVec := BitVec.ofInt w.bits val.toInt
          match tryMovzOrMovn w valBitVec with
          | some (false, imm16, shift) => pure ⟨w, .MOVZ dstZr (.int64 imm16) shift⟩
          | some (true, imm16, shift)  => pure ⟨w, .MOVN dstZr (.int64 imm16) shift⟩
          | none =>
            match checkLogicalImmediate w val with
            | .ok _ =>
              let dstSp ← anyToRegOrSp dstStx dstW.2
              pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
            | .error _ =>
              throwErrorAt srcStx "immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence)"
        else
          let dstSp ← anyToRegOrSp dstStx dstW.2
          liftCheck srcStx (checkLogicalImmediate w val)
          pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
      else
        let dstSp ← anyToRegOrSp dstStx dstW.2
        pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
    else
      let srcAny ← elabAnyReg srcStx w
      if dstW.2.isSp || srcAny.isSp then
        let dstSp ← anyToRegOrSp dstStx dstW.2
        let srcSp ← anyToRegOrSp srcStx srcAny
        pure ⟨w, .ADD_e dstSp srcSp (.imm { imm := 0, shift := .S0 })⟩
      else
        let dstZr ← anyToRegOrZr dstStx dstW.2
        let srcZr ← anyToRegOrZr srcStx srcAny
        pure ⟨w, .ORR_s dstZr (.low .XZR w) { reg := srcZr, amount := 0, shift := .LSL }⟩
  | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"

def elabMoveWide (stx : Syntax) (ops : Array OperandStx)
    (mk : {w : RegWidth} → RegOrZr w → ConstExpr → MovShift w → Operation w) : TermElabM Instr := do
  match ops.toList with
  | dstStx :: immStx :: extra =>
    if extra.length > 1 then
      throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"
    let dstW ← elabRegOrZrW dstStx
    let w := dstW.w
    let imm ← elabConstExpr immStx
    if let .int64 val := imm then
      if val.toInt < 0 || val.toInt > UInt16.maxValue.toInt then
        throwErrorAt immStx "move wide immediate {val.toInt} out of range [0, 65535]"
    let shift ← match extra with
      | [] => liftCheck stx (getMovShift w 0)
      | [modStx] =>
        match modStx with
        | `(aarch64_operand| $shiftId:aarch64_ident $amtStx:aarch64_const) =>
          let name ← getAsmIdent shiftId
          if name.toLower != "lsl" then
            throwErrorAt shiftId "only lsl shift supported for move wide"
          let amt ← elabConstNode amtStx
          match amt with
          | .int64 n => liftCheck amtStx (getMovShift w n.toBitVec.toNat)
          | _        => liftCheck amtStx (getMovShift w 0)
        | _ => throwErrorAt modStx "only lsl shift supported for move wide"
      | _ => throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"
    pure ⟨w, mk dstW.reg imm shift⟩
  | _ => throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"

-- ============================================================================
-- Top-Level AArch64 Instruction Dispatcher
-- ============================================================================

/-- Elaborate an `aarch64_instr` syntax node into an AArch64 `Instr` expression. -/
def elabInstrExpr (stx : TSyntax `aarch64_instr) : TermElabM Expr :=
  match stx with
  | `(aarch64_instr| ${ $t:term }) =>
    elabTerm t (some (mkConst ``Instr))
  | `(aarch64_instr| $mnStx:aarch64_ident $opSep:aarch64_operand,*) => do
    let mnemonic ← getAsmIdent mnStx
    let mn := mnemonic.toLower
    let ops : Array OperandStx := opSep.getElems
    let instr : Instr ← match mn with
    | "ldr" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let w := dstW.w
        let src ← elabAddrOrLit op2 w true
        if let .addr mem := src then
          liftCheck op2 (checkLdrStrRegisters dstW.reg mem)
        if addrOrLitNeedsUnscaled src w.bytes then
          match addrOrLitToUnscaled src with
          | some uoff => pure ⟨w, .LDUR dstW.reg uoff⟩
          | none      => throwErrorAt op2 "unscaled load cannot be literal or register offset"
        else
          pure ⟨w, .LDR dstW.reg src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "str" => do
      match ops with
      | #[op1, op2] =>
        let srcW ← elabRegOrZrW op1
        let w := srcW.w
        let dst ← elabAddr op2 w true
        liftCheck op2 (checkLdrStrRegisters srcW.reg dst)
        if addrExprNeedsUnscaled dst w.bytes then
          match addrExprToUnscaled dst with
          | some uoff => pure ⟨w, .STUR srcW.reg uoff⟩
          | none      => throwErrorAt op2 "unscaled store cannot be register offset"
        else
          pure ⟨w, .STR srcW.reg dst⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldur" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabUnscaledAddr op2
        pure ⟨dstW.w, .LDUR dstW.reg src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "stur" => do
      match ops with
      | #[op1, op2] =>
        let srcW ← elabRegOrZrW op1
        let dst ← elabUnscaledAddr op2
        pure ⟨srcW.w, .STUR srcW.reg dst⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldp" | "stp" => do
      match ops with
      | #[op1, op2, op3] =>
        let isLdp := mn == "ldp"
        let reg1W ← elabRegOrZrW op1
        let reg2 ← elabRegOrZr op2 reg1W.w
        let mem ← elabPairAddr op3 reg1W.w
        liftCheck stx (checkLdpStpRegisters isLdp reg1W.reg reg2 mem)
        pure ⟨reg1W.w, if isLdp then .LDP reg1W.reg reg2 mem else .STP reg1W.reg reg2 mem⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"
    | "ldrb" | "ldrh" => do
      match ops with
      | #[op1, op2] =>
        let scale := if mn == "ldrb" then 1 else 2
        let dstW ← elabRegOrZrW op1
        let dst ← checkRegWidthM op1 .W32 dstW.w dstW.reg
        let src ← elabAddr op2 .W32 true scale
        liftCheck op2 (checkLdrStrRegisters dst src)
        if addrExprNeedsUnscaled src scale then
          match addrExprToUnscaled src with
          | some uoff => pure ⟨.W32, if mn == "ldrb" then .LDURB dst uoff else .LDURH dst uoff⟩
          | none      => throwErrorAt op2 "unscaled load cannot be register offset"
        else
          pure ⟨.W32, if mn == "ldrb" then .LDRB dst src else .LDRH dst src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldurb" | "ldurh" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let dst ← checkRegWidthM op1 .W32 dstW.w dstW.reg
        let src ← elabUnscaledAddr op2
        pure ⟨.W32, if mn == "ldurb" then .LDURB dst src else .LDURH dst src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "strb" | "strh" => do
      match ops with
      | #[op1, op2] =>
        let scale := if mn == "strb" then 1 else 2
        let srcW ← elabRegOrZrW op1
        let src ← checkRegWidthM op1 .W32 srcW.w srcW.reg
        let dst ← elabAddr op2 .W32 true scale
        liftCheck op2 (checkLdrStrRegisters src dst)
        if addrExprNeedsUnscaled dst scale then
          match addrExprToUnscaled dst with
          | some uoff => pure ⟨.W32, if mn == "strb" then .STURB src uoff else .STURH src uoff⟩
          | none      => throwErrorAt op2 "unscaled store cannot be register offset"
        else
          pure ⟨.W32, if mn == "strb" then .STRB src dst else .STRH src dst⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "sturb" | "sturh" => do
      match ops with
      | #[op1, op2] =>
        let srcW ← elabRegOrZrW op1
        let src ← checkRegWidthM op1 .W32 srcW.w srcW.reg
        let dst ← elabUnscaledAddr op2
        pure ⟨.W32, if mn == "sturb" then .STURB src dst else .STURH src dst⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldrsb" | "ldrsh" => do
      match ops with
      | #[op1, op2] =>
        let scale := if mn == "ldrsb" then 1 else 2
        let dstW ← elabRegOrZrW op1
        let src ← elabAddr op2 dstW.w true scale
        liftCheck op2 (checkLdrStrRegisters dstW.reg src)
        if addrExprNeedsUnscaled src scale then
          match addrExprToUnscaled src with
          | some uoff => pure ⟨dstW.w, if mn == "ldrsb" then .LDURSB dstW.reg uoff else .LDURSH dstW.reg uoff⟩
          | none      => throwErrorAt op2 "unscaled load cannot be register offset"
        else
          pure ⟨dstW.w, if mn == "ldrsb" then .LDRSB dstW.reg src else .LDRSH dstW.reg src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldursb" | "ldursh" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabUnscaledAddr op2
        pure ⟨dstW.w, if mn == "ldursb" then .LDURSB dstW.reg src else .LDURSH dstW.reg src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldrsw" => do
      match ops with
      | #[op1, op2] =>
        let dst ← elabRegOrZr op1 .W64
        let src ← elabAddrOrLit op2 .W32 true 4 false
        if let .addr mem := src then
          liftCheck op2 (checkLdrStrRegisters dst mem)
        if addrOrLitNeedsUnscaled src 4 then
          match addrOrLitToUnscaled src with
          | some uoff => pure ⟨.W64, .LDURSW dst uoff⟩
          | none      => throwErrorAt op2 "unscaled load cannot be literal or register offset"
        else
          pure ⟨.W64, .LDRSW dst src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldursw" => do
      match ops with
      | #[op1, op2] =>
        let dst ← elabRegOrZr op1 .W64
        let src ← elabUnscaledAddr op2
        pure ⟨.W64, .LDURSW dst src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "ldpsw" => do
      match ops with
      | #[op1, op2, op3] =>
        let reg1 ← elabRegOrZr op1 .W64
        let reg2 ← elabRegOrZr op2 .W64
        let mem ← elabPairAddr op3 .W32
        liftCheck stx (checkLdpStpRegisters true reg1 reg2 mem)
        pure ⟨.W64, .LDPSW reg1 reg2 mem⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "add"  => elabArithNoFlags stx ops .ADD_e .ADD_s
    | "adds" => elabArithFlags stx "adds" ops .ADDS_e .ADDS_s
    | "cmn"  => elabCompare stx ops .ADDS_e .ADDS_s
    | "sub"  => elabArithNoFlags stx ops .SUB_e .SUB_s
    | "subs" => elabArithFlags stx "subs" ops .SUBS_e .SUBS_s
    | "cmp"  => elabCompare stx ops .SUBS_e .SUBS_s

    | "adc" | "adcs" | "sbc" | "sbcs" | "sdiv" | "udiv" | "lslv" | "lsrv" | "asrv" | "rorv" => do
      match ops with
      | #[op1, op2, op3] =>
        let dstW ← elabRegOrZrW op1
        let src1 ← elabRegOrZr op2 dstW.w
        let src2 ← elabRegOrZr op3 dstW.w
        let op : Operation dstW.w := match mn with
          | "adc"  => .ADC dstW.reg src1 src2
          | "adcs" => .ADCS dstW.reg src1 src2
          | "sbc"  => .SBC dstW.reg src1 src2
          | "sbcs" => .SBCS dstW.reg src1 src2
          | "sdiv" => .SDIV dstW.reg src1 src2
          | "udiv" => .UDIV dstW.reg src1 src2
          | "lslv" => .LSLV dstW.reg src1 src2
          | "lsrv" => .LSRV dstW.reg src1 src2
          | "asrv" => .ASRV dstW.reg src1 src2
          | _      => .RORV dstW.reg src1 src2
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "madd" | "msub" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src1 ← elabRegOrZr op2 dstW.w
        let src2 ← elabRegOrZr op3 dstW.w
        let src3 ← elabRegOrZr op4 dstW.w
        pure ⟨dstW.w, if mn == "madd" then .MADD dstW.reg src1 src2 src3 else .MSUB dstW.reg src1 src2 src3⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "mneg" | "mul" => do
      match ops with
      | #[op1, op2, op3] =>
        let dstW ← elabRegOrZrW op1
        let src1 ← elabRegOrZr op2 dstW.w
        let src2 ← elabRegOrZr op3 dstW.w
        let zr : RegOrZr dstW.w := .low .XZR dstW.w
        pure ⟨dstW.w, if mn == "mul" then .MADD dstW.reg src1 src2 zr else .MSUB dstW.reg src1 src2 zr⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"
    | "neg" | "negs" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let sh : ShiftRegExpr dstW.w := { reg := src, amount := 0, shift := .LSL }
        let zr : RegOrZr dstW.w := .low .XZR dstW.w
        pure ⟨dstW.w, if mn == "neg" then .SUB_s dstW.reg zr sh else .SUBS_s dstW.reg zr sh⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"

    | "smulh" | "umulh" => do
      match ops with
      | #[op1, op2, op3] =>
        let dst ← elabRegOrZr op1 .W64
        let src1 ← elabRegOrZr op2 .W64
        let src2 ← elabRegOrZr op3 .W64
        pure ⟨.W64, if mn == "smulh" then .SMULH dst src1 src2 else .UMULH dst src1 src2⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"
    | "smaddl" | "umaddl" | "smsubl" | "umsubl" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dst ← elabRegOrZr op1 .W64
        let src1 ← elabRegOrZr op2 .W32
        let src2 ← elabRegOrZr op3 .W32
        let src3 ← elabRegOrZr op4 .W64
        let op : Operation .W64 := match mn with
          | "smaddl" => .SMADDL dst src1 src2 src3
          | "umaddl" => .UMADDL dst src1 src2 src3
          | "smsubl" => .SMSUBL dst src1 src2 src3
          | _        => .UMSUBL dst src1 src2 src3
        pure ⟨.W64, op⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "smull" | "umull" | "smnegl" | "umnegl" => do
      match ops with
      | #[op1, op2, op3] =>
        let dst ← elabRegOrZr op1 .W64
        let src1 ← elabRegOrZr op2 .W32
        let src2 ← elabRegOrZr op3 .W32
        let zr : RegOrZr .W64 := .low .XZR .W64
        let op : Operation .W64 := match mn with
          | "smull"  => .SMADDL dst src1 src2 zr
          | "umull"  => .UMADDL dst src1 src2 zr
          | "smnegl" => .SMSUBL dst src1 src2 zr
          | _        => .UMSUBL dst src1 src2 zr
        pure ⟨.W64, op⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "and"  => elabLogicalNoFlags stx ops .AND_i .AND_s
    | "ands" => elabLogicalFlags stx ops .ANDS_i .ANDS_s
    | "orr"  => elabLogicalNoFlags stx ops .ORR_i .ORR_s
    | "eor"  => elabLogicalNoFlags stx ops .EOR_i .EOR_s
    | "orn" | "bic" | "eon" | "bics" => do
      match ops.toList with
      | dstStx :: srcStx :: rest =>
        if rest.isEmpty || rest.length > 2 then
          throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"
        let dstW ← elabRegOrZrW dstStx
        let src1 ← elabRegOrZr srcStx dstW.w
        let shiftOp ← elabShiftRegTail stx rest dstW.w true
        let op : Operation dstW.w := match mn with
          | "orn"  => .ORN_s dstW.reg src1 shiftOp
          | "bic"  => .BIC_s dstW.reg src1 shiftOp
          | "eon"  => .EON_s dstW.reg src1 shiftOp
          | _      => .BICS_s dstW.reg src1 shiftOp
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 3 or 4 operands, got {ops.size}"
    | "tst" => do
      match ops.toList with
      | srcStx :: second :: extra =>
        let src1W ← elabRegOrZrW srcStx
        let w := src1W.w
        if isConstOrReloc second then
          if !extra.isEmpty then
            throwErrorAt stx "expected 2 operands, got {ops.size}"
          let imm ← elabConstExpr second
          if let .int64 val := imm then
            liftCheck second (checkLogicalImmediate w val)
          pure ⟨w, .ANDS_i (.low .XZR w) src1W.reg imm⟩
        else
          let src2 ← elabShiftRegTail stx (second :: extra) w true
          pure ⟨w, .ANDS_s (.low .XZR w) src1W.reg src2⟩
      | _ => throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"

    | "bfm" | "sbfm" | "ubfm" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let immr ← elabImmNat op3
        let imms ← elabImmNat op4
        liftCheck op3 (checkBitWidthBound "bitfield" dstW.w immr)
        liftCheck op4 (checkBitWidthBound "bitfield" dstW.w imms)
        let op : Operation dstW.w := match mn with
          | "bfm"  => .BFM dstW.reg src immr imms
          | "sbfm" => .SBFM dstW.reg src immr imms
          | _      => .UBFM dstW.reg src immr imms
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "sbfx" | "ubfx" | "bfxil" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let lsb ← elabImmNat op3
        let width ← elabImmNat op4
        liftCheck stx (checkBitfieldBounds "bitfield extract" dstW.w lsb width)
        let immr := lsb
        let imms := lsb + width - 1
        let op : Operation dstW.w := match mn with
          | "sbfx" => .SBFM dstW.reg src immr imms
          | "ubfx" => .UBFM dstW.reg src immr imms
          | _      => .BFM dstW.reg src immr imms
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "bfi" | "sbfiz" | "ubfiz" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let lsb ← elabImmNat op3
        let width ← elabImmNat op4
        liftCheck stx (checkBitfieldBounds "bitfield insert" dstW.w lsb width)
        let immr := (dstW.w.bits - lsb) % dstW.w.bits
        let imms := width - 1
        let op : Operation dstW.w := match mn with
          | "bfi"   => .BFM dstW.reg src immr imms
          | "sbfiz" => .SBFM dstW.reg src immr imms
          | _       => .UBFM dstW.reg src immr imms
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "sxtb" | "sxth" | "sxtw" | "uxtb" | "uxth" | "uxtw" => do
      match ops with
      | #[op1, op2] =>
        let imms := match mn with
          | "sxtb" | "uxtb" => 7
          | "sxth" | "uxth" => 15
          | _               => 31
        let dstW ← elabRegOrZrW op1
        if imms == 31 && dstW.w != .W64 then
          throwErrorAt op1 "expected w64 register, got w32"
        let src32 ← elabRegOrZr op2 .W32
        let src : RegOrZr dstW.w := match src32 with | .low r _ => .low r dstW.w
        let isSigned := mn.startsWith "s"
        pure ⟨dstW.w, if isSigned then .SBFM dstW.reg src 0 imms else .UBFM dstW.reg src 0 imms⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"

    | "clz" | "cls" | "rbit" | "rev" | "rev16" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let op : Operation dstW.w := match mn with
          | "clz"  => .CLZ dstW.reg src
          | "cls"  => .CLS dstW.reg src
          | "rbit" => .RBIT dstW.reg src
          | "rev"  => .REV dstW.reg src
          | _      => .REV16 dstW.reg src
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "rev32" | "rev64" => do
      match ops with
      | #[op1, op2] =>
        let dst ← elabRegOrZr op1 .W64
        let src ← elabRegOrZr op2 .W64
        pure ⟨.W64, if mn == "rev32" then .REV32 dst src else .REV dst src⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "extr" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src1 ← elabRegOrZr op2 dstW.w
        let src2 ← elabRegOrZr op3 dstW.w
        let lsb ← elabImmNat op4
        liftCheck op4 (checkBitWidthBound "extr" dstW.w lsb)
        pure ⟨dstW.w, .EXTR dstW.reg src1 src2 lsb⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"

    | "lsl" | "lsr" | "asr" | "ror" => do
      match ops with
      | #[op1, op2, op3] =>
        let dstW ← elabRegOrZrW op1
        let w := dstW.w
        let src1 ← elabRegOrZr op2 w
        if isConstOrReloc op3 then
          let imm ← elabImmNat op3
          liftCheck op3 (checkBitWidthBound "shift" w imm)
          let op : Operation w := match mn with
            | "lsl" => .UBFM dstW.reg src1 ((w.bits - imm) % w.bits) (w.bits - 1 - imm)
            | "lsr" => .UBFM dstW.reg src1 imm (w.bits - 1)
            | "asr" => .SBFM dstW.reg src1 imm (w.bits - 1)
            | _     => .EXTR dstW.reg src1 src1 imm
          pure ⟨w, op⟩
        else
          let src2 ← elabRegOrZr op3 w
          let op : Operation w := match mn with
            | "lsl" => .LSLV dstW.reg src1 src2
            | "lsr" => .LSRV dstW.reg src1 src2
            | "asr" => .ASRV dstW.reg src1 src2
            | _     => .RORV dstW.reg src1 src2
          pure ⟨w, op⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "ccmp" | "ccmn" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let src1W ← elabRegOrZrW op1
        let w := src1W.w
        let nzcv ← elabImmNat op3
        liftCheck op3 (checkNzcvFlags nzcv)
        let cond ← elabCondArg op4
        if isConstOrReloc op2 then
          let imm ← elabImmNat op2
          liftCheck op2 (checkCcmpImmediate imm)
          pure ⟨w, if mn == "ccmp" then .CCMP_imm src1W.reg imm nzcv cond else .CCMN_imm src1W.reg imm nzcv cond⟩
        else
          let src2 ← elabRegOrZr op2 w
          pure ⟨w, if mn == "ccmp" then .CCMP_reg src1W.reg src2 nzcv cond else .CCMN_reg src1W.reg src2 nzcv cond⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"

    | "csel" | "csinc" | "csinv" | "csneg" => do
      match ops with
      | #[op1, op2, op3, op4] =>
        let dstW ← elabRegOrZrW op1
        let src1 ← elabRegOrZr op2 dstW.w
        let src2 ← elabRegOrZr op3 dstW.w
        let cond ← elabCondArg op4
        let op : Operation dstW.w := match mn with
          | "csel"  => .CSEL dstW.reg src1 src2 cond
          | "csinc" => .CSINC dstW.reg src1 src2 cond
          | "csinv" => .CSINV dstW.reg src1 src2 cond
          | _       => .CSNEG dstW.reg src1 src2 cond
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 4 operands, got {ops.size}"
    | "cset" | "csetm" => do
      match ops with
      | #[op1, op2] =>
        let dstW ← elabRegOrZrW op1
        let zr : RegOrZr dstW.w := .low .XZR dstW.w
        let cond ← elabCondArg op2
        pure ⟨dstW.w, if mn == "cset" then .CSINC dstW.reg zr zr cond.invert else .CSINV dstW.reg zr zr cond.invert⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "cinc" | "cinv" | "cneg" => do
      match ops with
      | #[op1, op2, op3] =>
        let dstW ← elabRegOrZrW op1
        let src ← elabRegOrZr op2 dstW.w
        let cond ← elabCondArg op3
        let op : Operation dstW.w := match mn with
          | "cinc" => .CSINC dstW.reg src src cond.invert
          | "cinv" => .CSINV dstW.reg src src cond.invert
          | _      => .CSNEG dstW.reg src src cond.invert
        pure ⟨dstW.w, op⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "mov"  => elabMov stx ops
    | "mvn"  => do
      match ops.toList with
      | dstStx :: rest =>
        if rest.isEmpty || rest.length > 2 then
          throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"
        let dstW ← elabRegOrZrW dstStx
        let shiftOp ← elabShiftRegTail stx rest dstW.w true
        pure ⟨dstW.w, .ORN_s dstW.reg (.low .XZR dstW.w) shiftOp⟩
      | _ => throwErrorAt stx "expected 2 or 3 operands, got {ops.size}"
    | "movz" => elabMoveWide stx ops .MOVZ
    | "movk" => elabMoveWide stx ops .MOVK
    | "movn" => elabMoveWide stx ops .MOVN

    | "adr" | "adrp" => do
      match ops with
      | #[op1, op2] =>
        let dst ← elabRegOrZr op1 .W64
        let target ← elabConstExpr op2
        if let .int64 imm := target then
          liftCheck op2 (if mn == "adr" then checkAdrOffset imm else checkAdrpOffset imm)
        pure ⟨.W64, if mn == "adr" then .ADR dst target else .ADRP dst target⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"

    | "b" | "bl" => do
      match ops with
      | #[op1] =>
        let target ← elabConstExpr op1
        if let .int64 imm := target then
          liftCheck op1 (checkBOffset imm)
        pure ⟨.W64, if mn == "b" then .B target else .BL target⟩
      | _ => throwErrorAt stx "expected 1 operand, got {ops.size}"
    | "blr" | "br" => do
      match ops with
      | #[op1] =>
        let target ← elabRegOrZr op1 .W64
        pure ⟨.W64, if mn == "blr" then .BLR target else .BR target⟩
      | _ => throwErrorAt stx "expected 1 operand, got {ops.size}"
    | "ret" => do
      match ops with
      | #[] => pure ⟨.W64, .RET RegOrZr.X30⟩
      | #[op1] =>
        let target ← elabRegOrZr op1 .W64
        pure ⟨.W64, .RET target⟩
      | _ => throwErrorAt stx "expected 0 or 1 operands, got {ops.size}"

    | "cbz" | "cbnz" => do
      match ops with
      | #[op1, op2] =>
        let regW ← elabRegOrZrW op1
        let target ← elabConstExpr op2
        if let .int64 imm := target then
          liftCheck op2 (checkCbzOffset mn imm)
        pure ⟨regW.w, if mn == "cbz" then .CBZ regW.reg target else .CBNZ regW.reg target⟩
      | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"
    | "tbz" | "tbnz" => do
      match ops with
      | #[op1, op2, op3] =>
        let regW ← elabRegOrZrW op1
        let bit ← elabImmNat op2
        liftCheck op2 (checkTbzBitPosition mn regW.w bit)
        let target ← elabConstExpr op3
        if let .int64 imm := target then
          liftCheck op3 (checkTbzOffset mn imm)
        pure ⟨regW.w, if mn == "tbz" then .TBZ regW.reg bit target else .TBNZ regW.reg bit target⟩
      | _ => throwErrorAt stx "expected 3 operands, got {ops.size}"

    | "nop" => do
      match ops with
      | #[] => pure ⟨.W64, .NOP⟩
      | _ => throwErrorAt stx "expected 0 operands, got {ops.size}"

    | _ => do
      let condStr? :=
        if mn.startsWith "b." then some (mn.drop 2).toString
        else if mn.startsWith "b" && mn.length == 3 then some (mn.drop 1).toString
        else none
      match condStr?.bind parseCondCode with
      | some cond =>
        match ops with
        | #[op1] =>
          let target ← elabConstExpr op1
          if let .int64 imm := target then
            liftCheck op1 (checkBCondOffset imm)
          pure ⟨.W64, .B_cond cond target⟩
        | _ => throwErrorAt stx "expected 1 operand, got {ops.size}"
      | none =>
        if mn.startsWith "b." then
          throwErrorAt mnStx "unknown condition code in branch instruction: {mnemonic}"
        else
          throwErrorAt mnStx "unsupported instruction: {mnemonic}"
    return toExpr instr
  | _ => throwErrorAt stx "invalid AArch64 instruction syntax"

-- ============================================================================
-- Directive, Program, runParserCategory, and Elaborator Entrypoints
-- ============================================================================

/-- Elaborate an `aarch64_directive` syntax node into a `Directive` expression. -/
def elabDirective (stx : TSyntax `aarch64_directive) : TermElabM Expr := do
  match stx with
  | `(aarch64_directive| $lbl:aarch64_ident :) =>
    let name ← getAsmIdent lbl
    return toExpr (Directive.label name)
  | `(aarch64_directive| $ins:aarch64_instr) =>
    let instrExpr ← elabInstrExpr ins
    mkAppM ``Directive.instr #[instrExpr]
  | `(aarch64_directive| ${ $t:term }) =>
    elabTerm t (some (mkConst ``Directive))
  | _ => throwErrorAt stx "invalid AArch64 directive"

/-- Elaborate a parsed `aarch64_prog` syntax tree into a `Program` (`List Directive`) expression. -/
def elabProgSyntax (stx : TSyntax `aarch64_prog) : TermElabM Expr := do
  match stx with
  | `(aarch64_prog| $dirs:aarch64_directive*) =>
    let dirExprs ← dirs.toList.mapM elabDirective
    mkListLit (mkConst ``Directive) dirExprs
  | _ => throwErrorAt stx "invalid AArch64 assembly program"

/-- Replace AArch64 inline `// ...` and line-leading `# ...` comments with Lean `-- ...` comments
    so comments remain attached in `Lean.Syntax` trivia. -/
private def replaceAArch64Comments (input : String) : String :=
  String.intercalate "\n" <| input.splitOn "\n" |>.map fun line =>
    let line :=
      match line.splitOn "//" with
      | [] => ""
      | code :: rest =>
        if rest.isEmpty then code
        else code ++ "--" ++ String.intercalate "//" rest
    let trimmed := line.trimAsciiStart.toString
    if trimmed.startsWith "#" then
      let wsPrefixLen := line.length - trimmed.length
      (line.take wsPrefixLen).toString ++ "--" ++ (trimmed.drop 1).toString
    else
      line

/-- Parse an AArch64 assembly string via `Lean.Parser.runParserCategory` (`aarch64_prog`)
    and elaborate the resulting syntax into a `Lean.Expr` of type `Program`. -/
def elabAArch64 (input : String) : TermElabM Lean.Expr := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `aarch64_prog (replaceAArch64Comments input) with
  | .ok stx => elabProgSyntax ⟨stx⟩
  | .error err => throwError err

/-- Inline quasiquotation syntax for AArch64 assembly programs using the `aarch64_prog` syntax category. -/
elab "[aarch64|" p:aarch64_prog "]" : term =>
  elabProgSyntax p

/-- Read an AArch64 assembly file at elaboration time, strip directives, parse via `elabAArch64`,
    and elaborate the resulting syntax into a Kraken `Program`. -/
elab "include_aarch64 " path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path (elabAArch64 (stripDirectives content))

/-- Function-call style `include_aarch64("path")` macro alias. -/
elab "include_aarch64(" path:str ")" : term => do
  let content ← IO.FS.readFile path.getString
  withRef path (elabAArch64 (stripDirectives content))

end

end Kraken.AArch64.Parser
