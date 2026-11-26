module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
public import LeanQbeTest.T.Arm64DirPreds
public import LeanQbeTest.T.MainFlatParityArm64Test
meta import Lean
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.IselFlagHooks
meta import LeanQbe.T.Arm64.IselFlagHooksLemmas
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbeTest.T.MainFlatParityArm64Test

/-!
# AArch64 `GprIsa` Flag-Reuse & `jnzGprInv?` Regression Suite (`ArmFlagReuseTest`)

Verifies all 5 Wave-5 `W5-1a` hooks wired on `armGpr` (`T/Arm64/Isel.lean`):
1. Multi-branch `cmp` flag reuse (`condOfCmp?` + `cmpFlagsOut?`), including swapped `.imm, .gpr`.
2. Zero-compare flag reuse (`x >s 0` / `x <s 0` / `x == 0`) with fewer compares and zero `cset`.
3. Bit-test `ANDS` flag reuse (`hasTestFlags` + `armTestOp`) across multiple consumers.
4. `.bool` `copy`/`not` flag preservation (`boolFlagOut?`) without duplicate comparisons.
5. `.gpr` `TBZ`/`TBNZ` branch inversion (`jnzGprInv?`) on hot loops and cold branches.
6. `MainFlatParityArm64Test` 0-diff parity reference, Arm64/x64 MetaM isolation, and `<= std3`
   axiom audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.ArmFlagReuseTest

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbeTest.T.Arm64DirPreds

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  RegaTestKit.hintsOf armTarget armLegalTarget fs

meta def chk (fs : List Fn) : Bool :=
  RegaTestKit.chk armTarget armLayout armLegalTarget fs

meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  RegaTestKit.codeOf armTarget armLegalTarget fs

/-! ## 1. Multi-Branch Flag Reuse (`condOfCmp?` + `cmpFlagsOut?`) -/

/-- `(x <s y)` then `(x == y)` emits only `1` `SUBS`, `0` `CSET`, and `2` `B.cond`. -/
meta def seqCmpReuseArmFn : Fn :=
  ⟨"seqCmpReuseArm", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, p, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c1, ()) =>
    .jnz (.var c1)
      (.store (t := i64) (.var a) (.var p) (.ret (.var a, ())))
      (.let_ (op2 (.cmp .eq i64) (.var x) (.var y)) fun (c2, ()) =>
       .jnz (.var c2)
         (.store (t := i64) (.var x) (.var p) (.ret (.var x, ())))
         (.ret (.imm 0#64, ())))⟩

/-- Multi-branch `x >s 0` / `x <s 0` emits `1` `SUBS`, `0` `CSET`, and `2` `B.cond`. -/
meta def valsZeroMultiArmFn : Fn :=
  ⟨"valsZeroMultiArm", [i64, i64, i64, i64], [i64], fun _ _ (x, posV, negV, p, ()) =>
    .let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (cPos, ()) =>
    .jnz (.var cPos)
      (.store (t := i64) (.var posV) (.var p) (.ret (.var posV, ())))
      (.let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (cNeg, ()) =>
       .jnz (.var cNeg)
         (.store (t := i64) (.var negV) (.var p) (.ret (.var negV, ())))
         (.ret (.imm 0#64, ())))⟩

/-- Swapped `5 <=s x` then `5 == x` emits `1` `SUBS`, `0` `CSET`, and `2` `B.cond`. -/
meta def swappedImmReuseArmFn : Fn :=
  ⟨"swappedImmReuseArm", [i64, i64, i64], [i64], fun _ _ (x, a, p, ()) =>
    .let_ (op2 (.cmp .sle i64) (.imm 5#64) (.var x)) fun (c1, ()) =>
    .jnz (.var c1)
      (.let_ (op2 (.cmp .eq i64) (.imm 5#64) (.var x)) fun (c2, ()) =>
       .jnz (.var c2)
         (.store (t := i64) (.var a) (.var p) (.ret (.var a, ())))
         (.store (t := i64) (.var x) (.var p) (.ret (.var x, ()))))
      (.ret (.imm 0#64, ()))⟩

#guard chk [seqCmpReuseArmFn] &&
  countDirs isSubsDir (codeOf [seqCmpReuseArmFn]) == 1 &&
  countDirs isCsetDir (codeOf [seqCmpReuseArmFn]) == 0 &&
  countDirs isBcondDir (codeOf [seqCmpReuseArmFn]) == 2
#guard chk [valsZeroMultiArmFn] &&
  countDirs isSubsDir (codeOf [valsZeroMultiArmFn]) == 1 &&
  countDirs isCsetDir (codeOf [valsZeroMultiArmFn]) == 0 &&
  countDirs isBcondDir (codeOf [valsZeroMultiArmFn]) == 2
#guard chk [swappedImmReuseArmFn] &&
  countDirs isSubsDir (codeOf [swappedImmReuseArmFn]) == 1 &&
  countDirs isCsetDir (codeOf [swappedImmReuseArmFn]) == 0 &&
  countDirs isBcondDir (codeOf [swappedImmReuseArmFn]) == 2
#guard armCmpFlagsOut .slt 64 (.imm 5#64) (.gpr (.reg .X0)) (.flag .gt) == some false
#guard armCmpFlagsOut .slt 64 (.imm 5000#64) (.gpr (.reg .X0)) (.flag .lt) == some true
#guard armCmpFlagsOut .eq 64 (.gpr (.reg .X0)) (.imm 0#64) (.gpr (.reg .X1)) == some true

/-! ## 2. Bit-Test `ANDS` Flag Reuse (`hasTestFlags`) & `.bool` `copy`/`not` (`boolFlagOut?`) -/

/-- `(x &&& 0xff) != 0` reused in `jnz` and `select`: `1` `ANDS`, `0` `AND`, `0` `CSET`. -/
meta def bitTestReuseArmFn : Fn :=
  ⟨"bitTestReuseArm", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 0xff#64)) fun (t, ()) =>
    .let_ (op2 (.cmp .ne i64) (.var t) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (r, ()) => .ret (.var r, ()))
      (.ret (.var b, ()))⟩

/-- `not .bool` preserves `NZCV` flags across `CSET` (`1` `SUBS`, `0` `ANDS`/`TST`). -/
meta def boolNotReuseArmFn : Fn :=
  ⟨"boolNotReuseArm", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c1, ()) =>
    .let_ (op1 (.not .bool) (.var c1)) fun (c2, ()) =>
    .jnz (.var c1)
      (.let_ (op3 (.select i64) (.var c2) (.var a) (.var b)) fun (r, ()) => .ret (.var r, ()))
      (.ret (.var b, ()))⟩

#guard chk [bitTestReuseArmFn] &&
  countDirs isAndsDir (codeOf [bitTestReuseArmFn]) == 1 &&
  countDirs isAndDir (codeOf [bitTestReuseArmFn]) == 0 &&
  countDirs isCsetDir (codeOf [bitTestReuseArmFn]) == 0
#guard chk [boolNotReuseArmFn] &&
  countDirs isSubsDir (codeOf [boolNotReuseArmFn]) == 1 &&
  countDirs isAndsDir (codeOf [boolNotReuseArmFn]) == 0

/-! ## 3. `.gpr` `TBZ`/`TBNZ` Branch Inversion (`jnzGprInv?`) -/

/-- `.bool` parameter in GPR inside hot loop: `invertJnz` inverts `.gpr` branch to `TBZ`. -/
meta def gprBoolHotLoopArmFn : Fn :=
  ⟨"gprBoolHotLoopArm", [.bool, i64], [i64], fun _ _ (cond, n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .jnz (.var cond)
          (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 0#64)) fun (done, ()) =>
           .jnz (.var done)
             (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1#64)) fun (i', ()) =>
              .jump loopLbl (.var i', .var acc', ())))
          (.ret (.var acc, ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .imm 0#64, ()))⟩

/-- Non-inverted `.bool` loop in GPR emits `TBNZ`. -/
meta def gprBoolColdThenArmFn : Fn :=
  ⟨"gprBoolColdThenArm", [.bool, i64], [i64], fun _ _ (cond, n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .jnz (.var cond)
          (.ret (.var acc, ()))
          (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 0#64)) fun (done, ()) =>
           .jnz (.var done)
             (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1#64)) fun (i', ()) =>
              .jump loopLbl (.var i', .var acc', ())))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .imm 0#64, ()))⟩

#guard chk [gprBoolHotLoopArmFn] && (codeOf [gprBoolHotLoopArmFn]).any isTbzDir
#guard chk [gprBoolColdThenArmFn] && (codeOf [gprBoolColdThenArmFn]).any isTbnzDir

/-! ## 4. Parity Reference, Isolation & Single-Line Axiom Checks -/

theorem armFlagReuse_mainFlatParity_check :
    MainFlatParityArm64Test.compileModuleFlat_ok_implies_compileModule_arm =
      MainFlatParityArm64Test.compileModuleFlat_ok_implies_compileModule_arm := rfl

theorem armFlagReuse_gprSpec_check : GprTarget armMach armGpr armScratch :=
  arm_gprSpec

theorem armFlagReuse_labelClean_check : Rega.LabelClean armTarget.toIsa :=
  armLabelClean

#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armJnzGprInv_spec
#print axioms LeanQbe.T.Arm64.armBoolFlagOut_spec
#print axioms LeanQbe.T.Arm64.armCmpFlagsOut_spec
#print axioms LeanQbe.T.Arm64.armTestOp_boolFlag_spec
#print axioms LeanQbe.T.Arm64.armJnzGprInv_noLab
#print axioms LeanQbe.T.Arm64.arm_gprSpec
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.Arm64.arm64_of_call
#print axioms armFlagReuse_mainFlatParity_check
#print axioms armFlagReuse_gprSpec_check
#print axioms armFlagReuse_labelClean_check

open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenX64Mod (m : Name) : Bool :=
  (m.toString.splitOn "Amd64").length > 1 || m.toString.startsWith "Kraken.X64"
private def isForbiddenVllMod (m : Name) : Bool :=
  (m.toString.splitOn "Vll").length > 1

#eval show MetaM Unit from do
  let testBad := (← getEnv).header.moduleNames.filter fun m =>
    isForbiddenX64Mod m || isForbiddenVllMod m
  if !testBad.isEmpty then throwError "ArmFlagReuseTest imports Amd64/X64/Vll: {testBad.toList}"
  let env ← getEnv
  for nm in [``LeanQbe.T.Arm64.armGprSpec, ``LeanQbe.T.Arm64.armJnzGprInv_spec,
      ``LeanQbe.T.Arm64.armBoolFlagOut_spec, ``LeanQbe.T.Arm64.armCmpFlagsOut_spec,
      ``LeanQbe.T.Arm64.armTestOp_boolFlag_spec, ``LeanQbe.T.Arm64.armJnzGprInv_noLab,
      ``LeanQbe.T.Arm64.arm_gprSpec, ``LeanQbe.T.Arm64.armLabelClean,
      ``LeanQbe.T.Arm64.arm64_of_call,
      ``LeanQbeTest.T.MainFlatParityArm64Test.compileModuleFlat_ok_implies_compileModule_arm] do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    let some ci := env.find? nm | throwError "Missing {nm}"
    if ci.isUnsafe then throwError "{nm} is unsafe"

end LeanQbeTest.T.ArmFlagReuseTest
