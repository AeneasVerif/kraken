module

public import LeanQbe.T.Arm64.IselCore

/-!
# AArch64 Wave 6.2-B `CCMP`/`CCMN` & `CSNEG` Lowering (`Arm64.IselCcmp`)

Implements the opt-in `GprIsa` hooks for Wave 6.2-B (`OPT-8`):
* `armCcmp`: short-circuit conditional compare (`CCMP`/`CCMN` reg or 5-bit imm) at widths
  `32` and `64` with exact NZCV fallbacks (`armNzcvTrue` / `armNzcvFalse`).
* `armSelectNeg`: conditional negation (`CSNEG wd, wx, wx, cond`) for dynamic
  `select pc x (-x)` / `select pc (-x) x` at `[8, 16, 32, 64]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `CCMP` / `CCMN` Conditional Compare (`armCcmp`) -/

/-- Minimal 4-bit `NZCV` immediate (`< 16`) making `c.interp (StatusFlags.ofNat nzcv) = true`. -/
def armNzcvTrue : ArmCond → Nat
  | .eq => 4 | .ne => 0 | .cs => 2 | .cc => 0
  | .mi => 8 | .pl => 0 | .vs => 1 | .vc => 0
  | .hi => 2 | .ls => 0 | .ge => 0 | .lt => 1
  | .gt => 0 | .le => 1

/-- Minimal 4-bit `NZCV` immediate (`< 16`) making `c.interp (StatusFlags.ofNat nzcv) = false`. -/
def armNzcvFalse (c : ArmCond) : Nat :=
  armNzcvTrue (armNegCond c)

/-- Single-instruction `CCMP_imm` (`imm < 32`) or `CCMN_imm` (`imm ≠ 0 ∧ (-imm) < 32`). -/
def armCcmpImm5? {n : Nat} (w : RegWidth) (rx : XReg) (imm : BitVec n)
    (nzcv : Nat) (ccExec : ArmCond) : Option Instr :=
  if Nat.blt imm.toNat 32 then
    some (armIselInsI (.CCMP_imm (zr rx w) imm.toNat nzcv ccExec.toKraken))
  else if imm != 0#n && Nat.blt (-imm).toNat 32 then
    some (armIselInsI (.CCMN_imm (zr rx w) (-imm).toNat nzcv ccExec.toKraken))
  else none

/-- Conditional compare `CCMP`/`CCMN` (`Instr` builder) at widths `32` and `64`. -/
def armCcmpIns (prevCond : ArmCond) (isOr : Bool) (co : CmpOp) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) : Option (ArmCond × List Instr × FlagMask) :=
  if !(n == 32 || n == 64) then none
  else
    let w := armWidthOf n
    let ccExec := if isOr then armNegCond prevCond else prevCond
    match pa, pb with
    | .gpr (.reg ra), .gpr (.reg rb) =>
      let dstCond := armCmpCond co
      let nzcv := if isOr then armNzcvTrue dstCond else armNzcvFalse dstCond
      some (dstCond, [armIselInsI (.CCMP_reg (zr ra w) (zr rb w) nzcv ccExec.toKraken)], maskNZCV)
    | .gpr (.reg ra), .imm cb =>
      let dstCond := armCmpCond co
      let nzcv := if isOr then armNzcvTrue dstCond else armNzcvFalse dstCond
      (armCcmpImm5? w ra cb nzcv ccExec).map fun ins => (dstCond, [ins], maskNZCV)
    | .imm ca, .gpr (.reg rb) =>
      let dstCond := armCmpCond co.swap
      let nzcv := if isOr then armNzcvTrue dstCond else armNzcvFalse dstCond
      (armCcmpImm5? w rb ca nzcv ccExec).map fun ins => (dstCond, [ins], maskNZCV)
    | _, _ => none

/-- Conditional compare `CCMP`/`CCMN` returning clean directives and `maskNZCV`. -/
def armCcmp (prevCond : ArmCond) (isOr : Bool) (co : CmpOp) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) :
    Option (ArmCond × List Directive × FlagMask) :=
  (armCcmpIns prevCond isOr co n pa pb).map fun (dstCond, c, cl) =>
    (dstCond, emitClean c, cl)

/-! ## 2. Dynamic Conditional Negation `CSNEG` (`armSelectNeg`) -/

/-- Dynamic conditional negation `select pc x (-x)` / `select pc (-x) x` (`Instr` builder). -/
def armSelectNegIns (n : Nat) (pc : PArg Reg Empty ArmCond .bool) (rx : Reg)
    (negFirst : Bool) (rd : Reg) : Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let x ← match rx with | .reg x => some x | .SP => none
    let d ← match rd with | .reg d => some d | .SP => none
    let w := armWidthOf n
    let mkCsneg (cond : ArmCond) : Instr :=
      let c := if negFirst then armNegCond cond else cond
      armIselInsI (.CSNEG (zr d w) (zr x w) (zr x w) c.toKraken)
    match pc with
    | .imm b =>
      if (if b then negFirst else !negFirst) then
        some ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh x))], maskNone)
      else
        some ([armIselInsI (.ORR_s (zr d w) (xzr w) (sh x))], maskNone)
    | .flag cond => some ([mkCsneg cond], maskNone)
    | .gpr (.reg rc) =>
      some ([armIselInsI (.ANDS_i (xzr .W32) (zr rc .W32) (.int64 1)), mkCsneg .ne], maskNZCV)
    | .gpr .SP => none

/-- Dynamic conditional negation (`CSNEG`) returning clean directives and `FlagMask`. -/
def armSelectNeg (n : Nat) (pc : PArg Reg Empty ArmCond .bool) (rx : Reg)
    (negFirst : Bool) (rd : Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armSelectNegIns n pc rx negFirst rd)

end LeanQbe.T.Arm64
