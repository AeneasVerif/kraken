module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Driver
public import LeanQbe.T.MainInline
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbeTest.T.Arm64DirPreds
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.MainLemmas
meta import LeanQbe.T.Driver
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbeTest.T.RegaTestKit
public meta import Kraken.AArch64.Print

/-!
# Arm64 Wave-6 `W6-A + W6-B` (`w6ab`) Activation Tests

End-to-end `Live` -> `Spill` -> `Rega` -> `Arm64.Isel` activation `#guard`s for the verified
Arm64 `w6ab` bundle, each checked against the same compiler with the bundle switched off
(`armIsaNoW6ab`):

* **W6-B** (`GprIsa.addrCse`): in-block address CSE (`[p, #c]` shares one `add xP, xB, xI, lsl #k`
  instead of per-access `add x16`).
* **W6-A** zero-extension drop (`GprIsa.widenZextCmp`): `CBZ`/`CBNZ` and narrow `cmp` vs imm/reg
  of `.gprZ` values emit without `UBFM #0, #7`/`#15`.
* **W6-A** `ldrsb`/`ldrsh` fusion (`GprIsa.cmpMem := armCmpMem`): single-use narrow loads feeding
  signed compares fuse into `LDRSB`/`LDRSH` + `CMP` (no `SBFM`).
* **W6-A** shifted-register ALU & CMP (`GprIsa.shiftAlu`, `GprIsa.shiftCmp`): `lsl`/`lsr`/`asr`
  feeding `add`/`sub`/`and`/`or`/`xor` or `cmp` fuse into shifted-operand instructions.
* Real `Kissat.Plain` hot functions (`plain_watch_push`, `plain_prop_lit`, ...)
  emit strictly fewer instructions with the bundle on.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Arm64W6ABTest

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit LeanQbeTest.T.Arm64DirPreds

/-! ## 1. Compilation helpers (bundle on / off) -/

/-- `armTarget.toIsa` with every `w6ab` hook switched off (the pre-`w6ab` Arm64 backend). -/
@[expose] meta def armIsaNoW6ab : Isa :=
  { armTarget.toIsa with
    gpr :=
      { armGpr with
        addrCse := false
        widenZextCmp := false
        shiftAlu := fun _ _ _ _ _ _ _ => none
        zeroUpper32ShiftAlu := false
        deferShiftAlu := false
        shiftCmp := fun _ _ _ _ _ _ _ _ => none
        shiftCmpFlagsOut? := fun _ _ _ _ => none
        cmpMem := fun _ _ _ _ _ => none }
    supportsCmpMem := fun _ => false }

meta def armChk (fs : List Fn) : Bool :=
  chk armTarget armLayout armLegalTarget fs

meta def armCode (fs : List Fn) : List armTarget.toIsa.Directive :=
  codeOf armTarget armLegalTarget fs

/-- Emitted code of `fs` with the `w6ab` bundle off. -/
meta def armCodeOff (fs : List Fn) : List Directive :=
  extractCode (compileModule armIsaNoW6ab armLegalTarget 0 [] [] 0 fs
    (fs.map (Fn.computeHints armIsaNoW6ab armLegalTarget)))

/-- Non-label directive count. -/
meta def insnCount (ds : List Directive) : Nat :=
  countDirs (fun d => match d with | .instr _ => true | _ => false) ds

/-- `add x16, xB, xI, lsl/uxtw #k` (per-access scratch address recomputation). -/
meta def isAddrX16Dir : Directive → Bool
  | .instr { operation := .ADD_s (.low (.reg .X16) .W64) _ _, .. }
  | .instr { operation := .ADD_e (.low (.reg .X16) .W64) _ (.ext _), .. } => true
  | _ => false

/-- Any non-zero shifted-register `add` (`add xD, xB, xI, lsl #k`). -/
meta def isAddShiftedDir : Directive → Bool
  | .instr { operation := .ADD_s _ _ sr, .. } => sr.amount != 0
  | _ => false

meta def isLdrsbOrLdrshDir : Directive → Bool
  | .instr { operation := .LDRSB .., .. }
  | .instr { operation := .LDRSH .., .. } => true
  | _ => false

meta def isSbfmExtDir : Directive → Bool
  | .instr { operation := .SBFM _ _ 0 7, .. }
  | .instr { operation := .SBFM _ _ 0 15, .. } => true
  | _ => false

meta def isCbzOrCbnzDir (d : Directive) : Bool :=
  isCbzDir d || isCbnzDir d

meta def isShiftedAluNonZeroDir : Directive → Bool
  | .instr { operation := .ADD_s _ _ sr, .. }
  | .instr { operation := .SUB_s _ _ sr, .. }
  | .instr { operation := .AND_s _ _ sr, .. }
  | .instr { operation := .ORR_s _ _ sr, .. }
  | .instr { operation := .EOR_s _ _ sr, .. } => sr.amount != 0
  | _ => false

meta def isShiftedSubsDir : Directive → Bool
  | .instr { operation := .SUBS_s (.low .XZR _) _ sr, .. } => sr.amount != 0
  | _ => false

meta def isShiftStandaloneDir : Directive → Bool
  | .instr { operation := .UBFM _ _ r s, .. } => !(r == 0 && (s == 7 || s == 15 || s == 31))
  | .instr { operation := .SBFM _ _ r s, .. } => !(r == 0 && (s == 7 || s == 15 || s == 31))
  | _ => false

/-! ## 2. W6-B litmus: repeated `[base + idx << k + c]` accesses share one address `add` -/

/-- Four `i32` stores at `[b + (i << 2) + {4, 8, 12, 16}]`. -/
meta def cseStoresFn : Fn :=
  ⟨"w6b_cse_stores", [i64, i64, i32], [i64], fun _ _ (b, i, v, ()) =>
    .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var s)) fun (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 4)) fun (p4, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8)) fun (p8, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 12)) fun (p12, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 16)) fun (p16, ()) =>
    .store (.var v) (.var p4) (.store (.var v) (.var p8)
      (.store (.var v) (.var p12) (.store (.var v) (.var p16) (.ret (.imm 0, ())))))⟩

/-- Four `i32` loads at `[b + (i << 3) + {4, 8, 12, 16}]`, summed. -/
meta def cseLoadsFn : Fn :=
  ⟨"w6b_cse_loads", [i64, i64], [i32], fun _ _ (b, i, ()) =>
    .let_ (op2 (.shl i64) (.var i) (.imm 3)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var s)) fun (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 4)) fun (p4, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8)) fun (p8, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 12)) fun (p12, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 16)) fun (p16, ()) =>
    .load i32 (.var p4) fun x =>
    .load i32 (.var p8) fun y =>
    .load i32 (.var p12) fun z =>
    .load i32 (.var p16) fun w =>
    .let_ (op2 (.add i32) (.var x) (.var y)) fun (xy, ()) =>
    .let_ (op2 (.add i32) (.var xy) (.var z)) fun (xyz, ()) =>
    .let_ (op2 (.add i32) (.var xyz) (.var w)) fun (r, ()) => .ret (.var r, ())⟩

/-- Single access `[b + (i << 2) + 4]`: policy keeps the scratch form (no extra register). -/
meta def cseSingleFn : Fn :=
  ⟨"w6b_cse_single", [i64, i64], [i32], fun _ _ (b, i, ()) =>
    .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var s)) fun (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 4)) fun (p4, ()) =>
    .load i32 (.var p4) fun x => .ret (.var x, ())⟩

#guard armChk [cseStoresFn, cseLoadsFn, cseSingleFn]

#guard countDirs isAddrX16Dir (armCodeOff [cseStoresFn]) == 4
#guard countDirs isAddrX16Dir (armCode [cseStoresFn]) == 0 &&
  countDirs isAddShiftedDir (armCode [cseStoresFn]) == 1
#guard insnCount (armCode [cseStoresFn]) < insnCount (armCodeOff [cseStoresFn])

#guard countDirs isAddrX16Dir (armCodeOff [cseLoadsFn]) == 4
#guard countDirs isAddrX16Dir (armCode [cseLoadsFn]) == 0 &&
  countDirs isAddShiftedDir (armCode [cseLoadsFn]) == 1
#guard insnCount (armCode [cseLoadsFn]) < insnCount (armCodeOff [cseLoadsFn])

#guard insnCount (armCode [cseSingleFn]) == insnCount (armCodeOff [cseSingleFn])

/-! ## 3. W6-A litmus: zero-extension drop (`CBZ`/`CBNZ` and narrow `cmp` vs imm) -/

/-- `ldrb v; if v != 0 ...` with `v` also stored (prevents if-conversion, emits `CBZ`). -/
meta def zextCbnzFn : Fn :=
  ⟨"w6a_zext_cbnz", [i64, i64, i64], [i64], fun _ _ (b, a, dst, ()) =>
    .load i8 (.var b) fun v =>
    .let_ (op1 (.zext 8 64) (.var v)) fun (w, ()) =>
    .let_ (op2 (.cmp .ne i8) (.var v) (.imm 0)) fun (c, ()) =>
    .jnz (.var c) (.store (.var w) (.var dst) (.ret (.var w, ()))) (.ret (.var a, ()))⟩

/-- `ldrh v; if v == 0 ...` (16-bit, `CBNZ`). -/
meta def zextCbz16Fn : Fn :=
  ⟨"w6a_zext_cbz16", [i64, i64, i64], [i64], fun _ _ (b, a, dst, ()) =>
    .load i16 (.var b) fun v =>
    .let_ (op1 (.zext 16 64) (.var v)) fun (w, ()) =>
    .let_ (op2 (.cmp .eq i16) (.var v) (.imm 0)) fun (c, ()) =>
    .jnz (.var c) (.store (.var w) (.var dst) (.ret (.var w, ()))) (.ret (.var a, ()))⟩

/-- `ldrb v; if (zext 8 32 v) == 32 ...` (white-space check with `v` kept alive). -/
meta def zextCmpImmFn : Fn :=
  ⟨"w6a_zext_cmp_imm", [i64, i64], [i64], fun _ _ (b, a, ()) =>
    .load i8 (.var b) fun v =>
    .let_ (op1 (.zext 8 32) (.var v)) fun (vz, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var vz) (.imm 32)) fun (c, ()) =>
    .let_ (op1 (.zext 8 64) (.var v)) fun (w, ()) =>
    .jnz (.var c) (.ret (.var w, ())) (.ret (.var a, ()))⟩

#guard armChk [zextCbnzFn, zextCbz16Fn, zextCmpImmFn]

#guard countDirs isExtDir (armCodeOff [zextCbnzFn]) == 1 &&
  countDirs isCbzOrCbnzDir (armCodeOff [zextCbnzFn]) == 1
#guard countDirs isExtDir (armCode [zextCbnzFn]) == 0 &&
  countDirs isCbzOrCbnzDir (armCode [zextCbnzFn]) == 1
#guard insnCount (armCode [zextCbnzFn]) + 1 == insnCount (armCodeOff [zextCbnzFn])

#guard countDirs isExtDir (armCode [zextCbz16Fn]) == 0 &&
  countDirs isCbzOrCbnzDir (armCode [zextCbz16Fn]) == 1
#guard insnCount (armCode [zextCbz16Fn]) + 1 == insnCount (armCodeOff [zextCbz16Fn])

#guard countDirs isExtDir (armCodeOff [zextCmpImmFn]) == 1
#guard countDirs isExtDir (armCode [zextCmpImmFn]) == 0 &&
  countDirs isSubsImmDir (armCode [zextCmpImmFn]) == 1
#guard insnCount (armCode [zextCmpImmFn]) + 1 == insnCount (armCodeOff [zextCmpImmFn])

/-! ## 4. W6-A litmus: `ldrb` + `sxtb` + `cmp` -> `ldrsb` + `cmp` (`cmpMem`) -/

/-- Kissat `value > 0` on a signed byte: `(sext 8 32 (load i8 [b])) >s 0`. -/
meta def ldrsbCmpFn : Fn :=
  ⟨"w6a_ldrsb_cmp", [i64, i64, i64], [i64], fun _ _ (b, x, y, ()) =>
    .load i8 (.var b) fun v =>
    .let_ (op1 (.sext 8 32) (.var v)) fun (sv, ()) =>
    .let_ (op2 (.cmp .sgt i32) (.var sv) (.imm 0)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ())) (.ret (.var y, ()))⟩

/-- `(sext 16 32 (load i16 [b])) <s 7`. -/
meta def ldrshCmpFn : Fn :=
  ⟨"w6a_ldrsh_cmp", [i64, i64, i64], [i64], fun _ _ (b, x, y, ()) =>
    .load i16 (.var b) fun v =>
    .let_ (op1 (.sext 16 32) (.var v)) fun (sv, ()) =>
    .let_ (op2 (.cmp .slt i32) (.var sv) (.imm 7)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ())) (.ret (.var y, ()))⟩

#guard armChk [ldrsbCmpFn, ldrshCmpFn]

#guard countDirs isSbfmExtDir (armCodeOff [ldrsbCmpFn]) == 1 &&
  countDirs isLdrsbOrLdrshDir (armCodeOff [ldrsbCmpFn]) == 0
#guard countDirs isSbfmExtDir (armCode [ldrsbCmpFn]) == 0 &&
  countDirs isLdrsbOrLdrshDir (armCode [ldrsbCmpFn]) == 1
#guard insnCount (armCode [ldrsbCmpFn]) + 1 == insnCount (armCodeOff [ldrsbCmpFn])

#guard countDirs isSbfmExtDir (armCode [ldrshCmpFn]) == 0 &&
  countDirs isLdrsbOrLdrshDir (armCode [ldrshCmpFn]) == 1
#guard insnCount (armCode [ldrshCmpFn]) + 1 == insnCount (armCodeOff [ldrshCmpFn])

/-! ## 5. W6-A litmus: shifted-register ALU and shifted-register CMP fusion -/

/-- `a + (b >>> 5)` (`add x0, x0, x1, lsr #5`). -/
meta def shiftAluLsrFn : Fn :=
  ⟨"w6a_shift_alu_lsr", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.lshr i64) (.var b) (.imm 5)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var s)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(b <<< 3) ^ a` (32-bit commutative `eor w0, w0, w1, lsl #3`). -/
meta def shiftAlu32XorFn : Fn :=
  ⟨"w6a_shift_alu32_xor", [i32, i32], [i32], fun _ _ (a, b, ()) =>
    .let_ (op2 (.shl i32) (.var b) (.imm 3)) fun (s, ()) =>
    .let_ (op2 (.xor i32) (.var s) (.var a)) fun (r, ()) => .ret (.var r, ())⟩

/-- `a <u (b >>> 2)` (`subs xzr, x0, x1, lsr #2` + `b.lo`). -/
meta def shiftCmpLsrFn : Fn :=
  ⟨"w6a_shift_cmp_lsr", [i64, i64, i64, i64], [i64], fun _ _ (a, b, x, y, ()) =>
    .let_ (op2 (.lshr i64) (.var b) (.imm 2)) fun (s, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var a) (.var s)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ())) (.ret (.var y, ()))⟩

/-- `(a >>>a 4) <=s b` (`lhsShift = true`, `subs xzr, x1, x0, asr #4` + `b.ge`). -/
meta def shiftCmpLhsAsrFn : Fn :=
  ⟨"w6a_shift_cmp_lhs_asr", [i64, i64, i64, i64], [i64], fun _ _ (a, b, x, y, ()) =>
    .let_ (op2 (.ashr i64) (.var a) (.imm 4)) fun (s, ()) =>
    .let_ (op2 (.cmp .sle i64) (.var s) (.var b)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ())) (.ret (.var y, ()))⟩

#guard armChk [shiftAluLsrFn, shiftAlu32XorFn, shiftCmpLsrFn, shiftCmpLhsAsrFn]

#guard countDirs isShiftStandaloneDir (armCodeOff [shiftAluLsrFn]) == 1
#guard countDirs isShiftStandaloneDir (armCode [shiftAluLsrFn]) == 0 &&
  countDirs isShiftedAluNonZeroDir (armCode [shiftAluLsrFn]) == 1
#guard insnCount (armCode [shiftAluLsrFn]) + 1 == insnCount (armCodeOff [shiftAluLsrFn])

#guard countDirs isShiftStandaloneDir (armCode [shiftAlu32XorFn]) == 0 &&
  countDirs isShiftedAluNonZeroDir (armCode [shiftAlu32XorFn]) == 1
#guard insnCount (armCode [shiftAlu32XorFn]) + 1 == insnCount (armCodeOff [shiftAlu32XorFn])

#guard countDirs isShiftStandaloneDir (armCodeOff [shiftCmpLsrFn]) == 1
#guard countDirs isShiftStandaloneDir (armCode [shiftCmpLsrFn]) == 0 &&
  countDirs isShiftedSubsDir (armCode [shiftCmpLsrFn]) == 1
#guard insnCount (armCode [shiftCmpLsrFn]) + 1 == insnCount (armCodeOff [shiftCmpLsrFn])

#guard countDirs isShiftStandaloneDir (armCode [shiftCmpLhsAsrFn]) == 0 &&
  countDirs isShiftedSubsDir (armCode [shiftCmpLhsAsrFn]) == 1
#guard insnCount (armCode [shiftCmpLhsAsrFn]) + 1 == insnCount (armCodeOff [shiftCmpLhsAsrFn])

/-! ## 6. Real `Kissat.Plain` hot-function activation (not dead code) -/

/-- `Kissat.Plain` functions after the default inline policy. -/
meta def plainPolFns : List Fn :=
  (LeanQbe.T.Examples.Kissat.Plain.plainModule.optInlinePolicy {}).fns

meta def isInstrDir : Directive → Bool
  | .instr _ => true
  | _ => false

meta def okInsns : Except String (List Directive) → Nat
  | .ok ds => countDirs isInstrDir ds
  | .error _ => 0

meta def plainPolFn? (nm : Sym) : Option Fn :=
  plainPolFns.find? (·.name == nm)

/-- `(on, off)` production (`Driver.compileFnFlat`) instruction counts of `Plain` function `nm`. -/
meta def hotPair (nm : Sym) : Nat × Nat :=
  match plainPolFn? nm with
  | some f =>
    (okInsns (Driver.compileFnFlat armTarget.toIsa armLegalTarget f),
      okInsns (Driver.compileFnFlat armIsaNoW6ab armLegalTarget f))
  | none => (0, 0)

meta def hotWins (nm : Sym) : Bool :=
  let (on, off) := hotPair nm
  0 < on && on < off

#guard hotWins "plain_watch_push"
#guard hotWins "plain_prop_lit"
#guard hotWins "plain_zero_tables"
#guard hotWins "plain_sweep"
#guard hotWins "plain_shrink_blk"
#guard hotWins "plain_decide"
#guard hotWins "plain_ema_update"
#guard hotWins "plain_rephase"
#guard hotWins "plain_analyze"

/-! ## 7. Axiom audit (`std3` only) -/

#print axioms LeanQbe.T.Arm64.armTarget
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.Arm64W6ABTest
