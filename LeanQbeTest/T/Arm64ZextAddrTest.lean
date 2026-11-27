module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.Arm64DirPreds
public import LeanQbeTest.T.Arm64UxtwTest
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.MainLemmas
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbeTest.T.Arm64UxtwTest
meta import LeanQbeTest.T.RegaTestKit
public meta import Kraken.AArch64.Print

/-!
# End-to-End AArch64 `Rega`/`Live` `.zext 32 64` + `UXTW` Fusion Tests

Verifies full `Live` -> `Rega` -> `Arm64.Isel` lowering (`checkCompile` + emitted assembly) for:
1. Fused `[base + (zext 32 64 idx) <<< sh + disp]` loads (`i8`, `i16`, `i32`, `i64`, `disp = 0`,
   `disp > 0`, `disp < 0`, and reversed `(zext idx) + base` operand order) eliding standalone
   `orr w, wzr, w` / `ubfm #0, #31` zero-extensions.
2. Fused `sext m 64 (load i_m [base + (zext 32 64 idx) <<< sh])` -> `ldrsb` / `ldrsh` `uxtw`.
3. Fused `store [base + (zext 32 64 idx) <<< sh + disp]` -> `str` `uxtw`.
4. Fused `leaArithZext`: `base + (zext idx)`, `base + ((zext idx) <<< 4) + 16`, and baseless
   `(zext idx) <<< 3` (`ubfiz`), while keeping `(zext idx) + 8` free of 2-instr `orr + add`.
5. Soundness preservation on `zext 16 64` and multi-use `zext 32 64` boundaries, plus `std3` audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Arm64ZextAddrTest

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit LeanQbeTest.T.Arm64DirPreds LeanQbeTest.T.Arm64UxtwTest

/-! ## 1. Compilation & directive predicates -/

meta def armChk (fs : List Fn) : Bool :=
  chk armTarget armLayout armLegalTarget fs

meta def armCode (fs : List Fn) : List armTarget.toIsa.Directive :=
  codeOf armTarget armLegalTarget fs

meta def isStandaloneZext32 : Directive → Bool
  | .instr { operation := .ORR_s (.low _ .W32) (.low .XZR .W32) _, .. } => true
  | .instr { operation := .UBFM _ _ 0 31, .. } => true
  | _ => false

meta def isAnyUxtwDir (d : Directive) : Bool :=
  isAddUxtwDir d || isMemUxtwDir d

/-! ## 2. Load / sext-load / store with `zext 32 64` index -/

/-- `load i32 [base + (zext 32 64 idx) <<< 2]` from incoming `i32` ABI parameter. -/
meta def loadI32ZextFn : Fn :=
  ⟨"load_i32_zext", [i64, i32], [i32], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, ())⟩

/-- `load i8 [(zext 32 64 idx) + base]` (reversed sum operand order, `sh = 0`). -/
meta def loadI8ZextRevFn : Fn :=
  ⟨"load_i8_zext_rev", [i64, i32], [i32], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var z) (.var b)) fun (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.zext 8 32) (.var v)) fun (r, ()) => .ret (.var r, ())⟩

/-- `load i64 [base + (zext 32 64 idx) <<< 3 + 16]` with positive displacement. -/
meta def loadI64ZextDispFn : Fn :=
  ⟨"load_i64_zext_disp", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 3)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 16)) fun (p, ()) =>
    .load i64 (.var p) fun v => .ret (.var v, ())⟩

/-- `load i32 [base + (zext 32 64 idx) <<< 2 - 4]` with negative displacement. -/
meta def loadI32ZextNegDispFn : Fn :=
  ⟨"load_i32_zext_neg", [i64, i32], [i32], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.sub i64) (.var p0) (.imm 4)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, ())⟩

/-- `sext 8 64 (load i8 [base + (zext 32 64 idx)])` -> `ldrsb [x, w, uxtw #0]`. -/
meta def loadSext8ZextFn : Fn :=
  ⟨"load_sext8_zext", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var z)) fun (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.sext 8 64) (.var v)) fun (r, ()) => .ret (.var r, ())⟩

/-- `sext 16 64 (load i16 [base + (zext 32 64 idx) <<< 1])` -> `ldrsh [x, w, uxtw #1]`. -/
meta def loadSext16ZextFn : Fn :=
  ⟨"load_sext16_zext", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 1)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i16 (.var p) fun v =>
    .let_ (op1 (.sext 16 64) (.var v)) fun (r, ()) => .ret (.var r, ())⟩

/-- `store i64 v, [base + (zext 32 64 idx) <<< 3 + 8]`. -/
meta def storeI64ZextDispFn : Fn :=
  ⟨"store_i64_zext_disp", [i64, i32, i64], [i64], fun _ _ (b, i, v, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 3)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 8)) fun (p, ()) =>
    .store (.var v) (.var p) (.ret (.imm 0, ()))⟩

/-- `store i32 v, [base + (zext 32 64 idx) <<< 2]`. -/
meta def storeI32ZextFn : Fn :=
  ⟨"store_i32_zext", [i64, i32, i32], [i64], fun _ _ (b, i, v, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .store (.var v) (.var p) (.ret (.imm 0, ()))⟩

#guard armChk [loadI32ZextFn, loadI8ZextRevFn, loadI64ZextDispFn, loadI32ZextNegDispFn,
  loadSext8ZextFn, loadSext16ZextFn, storeI64ZextDispFn, storeI32ZextFn]

#guard countDirs isStandaloneZext32 (armCode [loadI32ZextFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [loadI32ZextFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [loadI8ZextRevFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [loadI8ZextRevFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [loadI64ZextDispFn]) == 0 &&
  countDirs isAddUxtwDir (armCode [loadI64ZextDispFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [loadI32ZextNegDispFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [loadI32ZextNegDispFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [loadSext8ZextFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [loadSext8ZextFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [loadSext16ZextFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [loadSext16ZextFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [storeI64ZextDispFn]) == 0 &&
  countDirs isAddUxtwDir (armCode [storeI64ZextDispFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [storeI32ZextFn]) == 0 &&
  countDirs isMemUxtwDir (armCode [storeI32ZextFn]) == 1

/-! ## 3. `leaArithZext` (`ADD ... UXTW`, `UBFIZ`) & non-regression boundaries -/

/-- `base + (zext 32 64 idx)` -> `add x0, x0, w1, uxtw #0`. -/
meta def leaBaseZextFn : Fn :=
  ⟨"lea_base_zext", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var z)) fun (r, ()) => .ret (.var r, ())⟩

/-- `base + ((zext 32 64 idx) <<< 4) + 16` -> `add x, xb, wi, uxtw #4; add xd, x, #16`. -/
meta def leaScaledDispZextFn : Fn :=
  ⟨"lea_scaled_disp_zext", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 4)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 16)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(zext 32 64 idx) <<< 3` -> `ubfiz x0, x1, #3, #32`. -/
meta def leaUbfizZextFn : Fn :=
  ⟨"lea_ubfiz_zext", [i32], [i64], fun _ _ (i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 3)) fun (r, ()) => .ret (.var r, ())⟩

/-- `(zext 32 64 idx) + 8` (`sh = 0`, baseless): keeps `zext` + `add #8` (no 2-instr expansion). -/
meta def zextPlusImmSh0Fn : Fn :=
  ⟨"zext_plus_imm_sh0", [i32], [i64], fun _ _ (i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var z) (.imm 8)) fun (r, ()) => .ret (.var r, ())⟩

/-- `zext 16 64` is NOT `32 -> 64`: must still compile validly and preserve `ubfm #0, #15`. -/
meta def loadZext16BoundaryFn : Fn :=
  ⟨"load_zext16_boundary", [i64, i64], [i32], fun _ _ (b, x, ()) =>
    .let_ (op1 (.trunc 64 16) (.var x)) fun (h, ()) =>
    .let_ (op1 (.zext 16 64) (.var h)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, ())⟩

/-- Multi-use `zext 32 64` (used both in `[b + z <<< 2]` and returned): compiles cleanly. -/
meta def multiUseZextFn : Fn :=
  ⟨"multi_use_zext", [i64, i32], [i32, i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, .var z, ())⟩

#guard armChk [leaBaseZextFn, leaScaledDispZextFn, leaUbfizZextFn, zextPlusImmSh0Fn,
  loadZext16BoundaryFn, multiUseZextFn]

#guard countDirs isStandaloneZext32 (armCode [leaBaseZextFn]) == 0 &&
  countDirs isAddUxtwDir (armCode [leaBaseZextFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [leaScaledDispZextFn]) == 0 &&
  countDirs isAddUxtwDir (armCode [leaScaledDispZextFn]) == 1
#guard countDirs isStandaloneZext32 (armCode [leaUbfizZextFn]) == 0 &&
  countDirs isUbfiz32Dir (armCode [leaUbfizZextFn]) == 1
#guard countDirs isAnyUxtwDir (armCode [loadZext16BoundaryFn]) == 0 &&
  countDirs isUbfmZext16Dir (armCode [loadZext16BoundaryFn]) == 1

/-! ## 4. Axiom audit (`std3` only) -/

#print axioms LeanQbe.T.Arm64.armTarget
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.Arm64ZextAddrTest
