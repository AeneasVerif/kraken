module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.MainLemmas
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit

/-!
# SysV x86-64 Non-Regression Tests for `.zext 32 64` Addressing (`X64ZextAddrRegressTest`)

Verifies that adding Arm64 `UXTW` index-extension fusion preserves `x64Target` soundness and
code quality:
1. `x64Target.toIsa.supportsAddrZextIdx` defaults to `false`, preserving `movl` 32->64 zero
   extension on `x64Target` without unsound elision.
2. Programs with `zext 32 64` + scaled index compile cleanly (`checkCompile = true`) and still
   fold `[base + zext <<< sc + disp]` / `base + (zext <<< sc)` via x64 SIB addressing.
3. Axiom audit (`std3` only) on `x64Target`, `x64LabelClean`, and `compile_sound`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.X64ZextAddrRegressTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbeTest.T.RegaTestKit

theorem x64_supportsAddrZextIdx_rfl :
    x64Target.toIsa.supportsAddrZextIdx i64 .s1 0#64 = false ∧
    x64Target.toIsa.supportsAddrZextIdx i32 .s4 0#64 = false :=
  ⟨rfl, rfl⟩

meta def x64Chk (fs : List Fn) : Bool :=
  chk x64Target x64Layout x64LegalTarget fs

meta def x64Code (fs : List Fn) : List x64Target.toIsa.Directive :=
  codeOf x64Target x64LegalTarget fs

meta def isSelfMov32 : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) =>
    a == b
  | _ => false

meta def isLeaDir : Directive → Bool
  | .instr (.regular _ .W64 (.lea _ _)) => true
  | _ => false

/-- Non-canonical `add 64` -> `trunc 64 32` -> `zext 32 64`: x64 MUST still emit `movl`! -/
meta def truncAddZextLoadX64Fn : Fn :=
  ⟨"trunc_add_zext_load_x64", [i64, i64], [i32], fun _ _ (b, y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.imm 1)) fun (y1, ()) =>
    .let_ (op1 (.trunc 64 32) (.var y1)) fun (w, ()) =>
    .let_ (op1 (.zext 32 64) (.var w)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, ())⟩

meta def loadI32ZextX64Fn : Fn :=
  ⟨"load_i32_zext_x64", [i64, i32], [i32], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .load i32 (.var p) fun v => .ret (.var v, ())⟩

meta def loadI64ZextDispX64Fn : Fn :=
  ⟨"load_i64_zext_disp_x64", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 3)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 16)) fun (p, ()) =>
    .load i64 (.var p) fun v => .ret (.var v, ())⟩

meta def storeI32ZextX64Fn : Fn :=
  ⟨"store_i32_zext_x64", [i64, i32, i32], [i64], fun _ _ (b, i, v, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 2)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p, ()) =>
    .store (.var v) (.var p) (.ret (.imm 0, ()))⟩

meta def leaScaledZextX64Fn : Fn :=
  ⟨"lea_scaled_zext_x64", [i64, i32], [i64], fun _ _ (b, i, ()) =>
    .let_ (op1 (.zext 32 64) (.var i)) fun (z, ()) =>
    .let_ (op2 (.shl i64) (.var z) (.imm 3)) fun (sc, ()) =>
    .let_ (op2 (.add i64) (.var b) (.var sc)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 8)) fun (r, ()) => .ret (.var r, ())⟩

#guard x64Chk [truncAddZextLoadX64Fn, loadI32ZextX64Fn, loadI64ZextDispX64Fn,
  storeI32ZextX64Fn, leaScaledZextX64Fn]
#guard countDirs isSelfMov32 (x64Code [truncAddZextLoadX64Fn]) >= 1
#guard countDirs isSelfMov32 (x64Code [loadI32ZextX64Fn]) == 0
#guard countDirs isSelfMov32 (x64Code [loadI64ZextDispX64Fn]) == 0
#guard countDirs isSelfMov32 (x64Code [storeI32ZextX64Fn]) == 0
#guard countDirs isLeaDir (x64Code [leaScaledZextX64Fn]) == 1

#print axioms LeanQbe.T.Amd64.x64Target
#print axioms LeanQbe.T.Amd64.x64LabelClean
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.X64ZextAddrRegressTest
