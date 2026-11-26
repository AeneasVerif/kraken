module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr

/-!
# AArch64 Flag-Reuse and Branch-Inversion `GprIsa` Hooks (`Arm64.IselFlagHooks`)

Implements the 5 `GprIsa` flag-reuse and `.gpr` branch-inversion hooks wired into
`LeanQbe.T.Arm64.armGpr` without introducing cyclic imports between `Arm64.Isel` and proof modules:

* `armJnzGprInv` / `armJnzGpr`: bit-0 `TBZ`/`TBNZ` branch on `.bool` GPR (routing `.SP` via `.X16`)
  preserving NZCV (`maskNone`).
* `armCmpCond`: total `CmpOp → ArmCond` mapping after `SUBS`.
* `armCmpFlagsOut`: exact operand-order oracle (`some true` for lhs-rhs `SUBS`, `some false` for
  swapped rhs-lhs `SUBS`/`ADDS`, `none` when `armZeroCmpIns?` handles the compare without full
  NZCV flags or when 8/16-bit zero-extension breaks signed comparisons).
* `armBoolFlagOut`: `.copy .bool` and `.not .bool` flag-source preservation across flag-preserving
  `CSET`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Shared Low-Level Builders and Compare Primitives -/

/-- Low-level AArch64 `Instr` constructor matching `ins`. -/
abbrev armIselInsI {w : RegWidth} (op : Operation w) : Instr :=
  { operation_size := w, operation := op }

/-- Move `s : Reg` (possibly `.SP`) to `d : XReg` (`Instr`). -/
abbrev armIselMovToXI (d : XReg) (s : Reg) : Instr :=
  armIselInsI (.ADD_e (.low (.reg d) .W64) (.low s .W64) imm0)

/-- Register width (`W64` for 64-bit operations, `W32` for 8/16/32-bit operations). -/
abbrev armWidthOf (n : Nat) : RegWidth :=
  if n == 64 then .W64 else .W32

/-- Materialize condition `c` as `0/1` into `x_d` without clobbering flags (`Instr`). -/
abbrev armCset64I (d : XReg) (c : ArmCond) : Instr :=
  armIselInsI (.CSINC (zr d .W64) (xzr .W64) (xzr .W64) (armNegCond c).toKraken)

/-- 12-bit unsigned arithmetic immediate (`S0` or `S12`). -/
@[expose] def armImm12? {n : Nat} (c : BitVec n) : Option ExtOrImmReg :=
  if Nat.blt c.toNat 4096 then
    some (.imm { imm := .int64 (Int64.ofNat c.toNat), shift := .S0 })
  else if Nat.blt c.toNat 16777216 && (c.toNat % 4096 == 0) then
    some (.imm { imm := .int64 (Int64.ofNat (c.toNat / 4096)), shift := .S12 })
  else none

/-- `ArmCond` corresponding to integer comparison `o` after `cmp a, b` (`SUBS`). -/
@[expose] def armCmpCond : CmpOp → ArmCond
  | .eq => .eq | .ne => .ne | .ult => .cc | .ule => .ls | .ugt => .hi
  | .uge => .cs | .slt => .lt | .sle => .le | .sgt => .gt | .sge => .ge

/-- True iff `o` is a signed integer comparison (`slt`/`sle`/`sgt`/`sge`). -/
@[expose] def armIsSignedCmp : CmpOp → Bool
  | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- Immediate `cmp`/`cmn` instruction on `rx` vs `imm` (`SUBS_e` for 12-bit `imm`,
`ADDS_e` (`CMN`) for non-zero negated 12-bit immediates, or `none` if literal load is needed). -/
@[expose] def armCmpImmIns? {m : Nat} (w : RegWidth) (rx : XReg) (imm : BitVec m) :
    Option (List Instr) :=
  match armImm12? imm with
  | some ei => some [armIselInsI (.SUBS_e (xzr w) (.low (.reg rx) w) ei)]
  | none =>
    if imm == 0#m then none
    else match armImm12? (-imm) with
      | some ei => some [armIselInsI (.ADDS_e (xzr w) (.low (.reg rx) w) ei)]
      | none => none

/-- Specialized compare-against-zero lowering for `o` on `rx : XReg` (`UBFM` sign-bit test for
`.slt`/`.sge` into `.gpr`, and 1-insn `ANDS_i` `#0xFF`/`#0xFFFF` for narrow `8`/`16`-bit equality
or `.gpr` `.ule`/`.ugt`). -/
@[expose] def armZeroCmpIns? (o : CmpOp) (n : Nat) (rx : XReg)
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  let w := armWidthOf n
  match o, dst with
  | .slt, .gpr (.reg d) =>
    some ([armIselInsI (.UBFM (zr d w) (zr rx w) (n - 1) (n - 1))], maskNone)
  | .sge, .gpr (.reg d) =>
    if n == 8 || n == 16 then
      some ([armIselInsI (.UBFM (zr d .W32) (zr rx .W32) (n - 1) (n - 1)),
             armIselInsI (.EOR_i (.low (.reg d) .W32) (zr d .W32) (.int64 1))], maskNone)
    else none
  | .eq, _ | .ne, _ =>
    if n == 8 || n == 16 then
      let ands := armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
        (.int64 (if n == 8 then 0xFF else 0xFFFF)))
      let cond := armCmpCond o
      match dst with
      | .flag cf => if cf == cond then some ([ands], maskNZCV) else none
      | .gpr (.reg d) => some ([ands, armCset64I d cond], maskNZCV)
      | .gpr .SP | .vec _ => none
    else none
  | .ule, .gpr (.reg d) | .ugt, .gpr (.reg d) =>
    if n == 8 || n == 16 then
      let ands := armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
        (.int64 (if n == 8 then 0xFF else 0xFFFF)))
      some ([ands, armCset64I d (if o == .ule then .eq else .ne)], maskNZCV)
    else none
  | _, _ => none

/-! ## 2. Exported `GprIsa` Flag-Reuse & `jnzGprInv?` Hooks -/

/-- Bit-0 branch instruction `TBZ`/`TBNZ w_x, #0, l`. -/
abbrev armJnzBit0I (inv : Bool) (x : XReg) (l : Sym) : Instr :=
  match inv with
  | true => armIselInsI (w := .W32) (.TBZ (zr x .W32) 0 (.label l))
  | false => armIselInsI (w := .W32) (.TBNZ (zr x .W32) 0 (.label l))

/-- Test low bit `0` of `.bool` register `r` via `tbz` (`inv = true`) or `tbnz` (`inv = false`),
routing `.SP` via `.X16` (`Instr` builder). -/
abbrev armJnzGprInvIns (r : Reg) (inv : Bool) (l : Sym) : List Instr × FlagMask :=
  match r with
  | .reg x => ([armJnzBit0I inv x l], maskNone)
  | .SP => ([armIselMovToXI .X16 .SP, armJnzBit0I inv .X16 l], maskNone)

/-- Test low bit `0` of `.bool` register `r` via `tbz`/`tbnz` (routing `.SP` via `.X16`),
preserving flags. -/
@[expose] def armJnzGprInv (r : Reg) (inv : Bool) (l : Sym) : List Directive × FlagMask :=
  let p := armJnzGprInvIns r inv l
  (emitClean p.1, p.2)

/-- Non-inverted `armJnzGprIns` (`TBNZ w_r, #0, l`). -/
abbrev armJnzGprIns (r : Reg) (l : Sym) : List Instr × FlagMask :=
  armJnzGprInvIns r false l

/-- Non-inverted `armJnzGpr` (`TBNZ w_r, #0, l`), preserving flags. -/
@[expose] def armJnzGpr (r : Reg) (l : Sym) : List Directive × FlagMask :=
  let p := armJnzGprIns r l
  (emitClean p.1, p.2)

/-- Flag condition preserved in NZCV after flag-preserving boolean `.copy`/`.not` from `.flag`. -/
@[expose] def armBoolFlagOut {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg Empty ArmCond) sig)
    (pd : PDst Reg Empty ArmCond .bool) : Option ArmCond :=
  match pd with
  | .gpr (.reg _) =>
    match code, pas with
    | .copy .bool, (.flag c, ()) => some c
    | .not .bool, (.flag c, ()) => some (armNegCond c)
    | _, _ => none
  | _ => none

/-- Comparison operand order (`some true` = `va - vb`, `some false` = `vb - va`, `none` = full
comparison flags not guaranteed) matching `armCmpOpIns` unconditionally. -/
@[expose] def armCmpFlagsOut (o : CmpOp) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n))
    (pd : PDst Reg Empty ArmCond .bool) : Option Bool :=
  if ![8, 16, 32, 64].contains n then none
  else if (n == 8 || n == 16) && !armIsSignedCmp o then none
  else
    let lf? : Option Bool :=
      match pa, pb with
      | .gpr (.reg ra), .imm cb =>
        if cb == 0#n && (armZeroCmpIns? o n ra pd).isSome then none else some true
      | .imm ca, .gpr (.reg rb) =>
        if ca == 0#n then
          if (armZeroCmpIns? o.swap n rb pd).isSome then none else some false
        else if n == 32 || n == 64 then
          some (!(armCmpImmIns? (armWidthOf n) rb ca).isSome)
        else some false
      | .gpr (.reg _), .gpr (.reg _) => some true
      | _, _ => none
    lf?.bind fun lf =>
      let ok := match pd with
        | .gpr (.reg _) => true
        | .flag cf => cf == armCmpCond (if lf then o else o.swap)
        | .gpr .SP | .vec _ => false
      if ok then some lf else none

end LeanQbe.T.Arm64
