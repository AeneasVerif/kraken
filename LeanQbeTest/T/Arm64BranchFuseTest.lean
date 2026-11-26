module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.LratBytes
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.FullM4Bcp
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
public import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Arm64.LratBytes
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.FullM4Bcp
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit
meta import LeanQbeTest.T.Arm64DirPreds

/-!
# AArch64 `CBZ`/`CBNZ` & `TBZ`/`TBNZ` Branch Fusion Tests

Verifies compare-against-zero and single-bit test branch fusion through
`armGpr`, `armTarget`, `Rega.lowerFn`, `FullM4Bcp`, and `Arm64.LratBytes`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Arm64BranchFuseTest

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbeTest.T.Arm64DirPreds

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  RegaTestKit.hintsOf armTarget armLegalTarget fs

meta def chk (fs : List Fn) (exs : List (SigEntry × Nat) := []) : Bool :=
  RegaTestKit.chk armTarget armLayout armLegalTarget fs exs

meta def codeOf (fs : List Fn) (exs : List (SigEntry × Nat) := []) : List Directive :=
  RegaTestKit.codeOf armTarget armLegalTarget fs exs

/-! ## 1. ISA `cmpZeroJcc` and `testJcc` unit checks -/

theorem armSingleBit_checks :
    armSingleBit? 32 (1#32 <<< 31) = some 31 ∧
    armSingleBit? 8 0x80#8 = some 7 ∧
    armSingleBit? 64 0x40#64 = some 6 ∧
    armSingleBit? 32 6#32 = none ∧
    armSingleBit? 64 0#64 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#guard match armGpr.cmpZeroJcc .eq 64 (.reg .X1) "L" with
  | some ([d], m) => isCbzDir d && m == maskNone
  | _ => false

#guard match armGpr.cmpZeroJcc .ne 32 (.reg .X2) "L" with
  | some ([d], m) => isCbnzDir d && m == maskNone
  | _ => false

#guard match armGpr.cmpZeroJcc .ule 64 (.reg .X3) "L" with
  | some ([d], _) => isCbzDir d
  | _ => false

#guard match armGpr.cmpZeroJcc .ugt 32 (.reg .X4) "L" with
  | some ([d], _) => isCbnzDir d
  | _ => false

#guard match armGpr.cmpZeroJcc .slt 64 (.reg .X5) "L" with
  | some ([.instr { operation := .TBNZ _ 63 _, .. }], _) => true
  | _ => false

#guard match armGpr.cmpZeroJcc .sge 8 (.reg .X6) "L" with
  | some ([.instr { operation := .TBZ _ 7 _, .. }], _) => true
  | _ => false

#guard match armGpr.cmpZeroJcc .eq 8 (.reg .X1) "L" with
  | some ([_, d2], _) => isCbzDir d2
  | _ => false

#guard (armGpr.cmpZeroJcc .sle 64 (.reg .X1) "L").isNone
#guard (armGpr.cmpZeroJcc .eq 64 .SP "L").isNone
#guard (armGpr.cmpZeroJcc .eq 128 (.reg .X1) "L").isNone

#guard match armGpr.testJcc true 32 (.reg .X1) (1#32 <<< 17) "L" with
  | some ([.instr { operation := .TBNZ _ 17 _, .. }], m) => m == maskNone
  | _ => false

#guard match armGpr.testJcc false 8 (.reg .X1) 0x80#8 "L" with
  | some ([.instr { operation := .TBZ _ 7 _, .. }], m) => m == maskNone
  | _ => false

#guard (armGpr.testJcc true 32 (.reg .X1) 0x6#32 "L").isNone
#guard (armGpr.testJcc false 64 .SP 1#64 "L").isNone

/-! ## 2. End-to-end verified lowering regressions -/

/-- `x == 0` at `i64` emits `CBZ` (0 `SUBS`, 0 `B.cond`). -/
meta def cbz64Fn : Fn :=
  ⟨"cbz64", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var x) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- `0 != x` (commutative zero) at `i32` emits `CBNZ`. -/
meta def cbnz32CommFn : Fn :=
  ⟨"cbnz32Comm", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .ne i32) (.imm 0) (.var x)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Narrow `i8` `x == 0` uses `UBFM` + `CBZ`, 0 `SUBS`. -/
meta def cbz8Fn : Fn :=
  ⟨"cbz8", [i8, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .eq i8) (.var x) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Signed `x < 0` at `i32` emits `TBNZ w, #31` (0 `SUBS`/`B.LT`). -/
meta def sltZero32Fn : Fn :=
  ⟨"sltZero32", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .slt i32) (.var x) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Unsigned `x > 0` (`ugt 0`) emits `CBNZ`. -/
meta def ugtZero64Fn : Fn :=
  ⟨"ugtZero64", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .ugt i64) (.var x) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Single-bit test `(x & (1 << 5)) == 0` at `i64` emits `TBZ x, #5`. -/
meta def tbz64Bit5Fn : Fn :=
  ⟨"tbz64Bit5", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.and i64) (.var x) (.imm 32)) fun (t, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var t) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- `sext 8 64` + `<s 0` narrows through `sextVar` and emits `TBNZ w, #7`. -/
meta def sextSltZeroFn : Fn :=
  ⟨"sextSltZero", [i8, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op1 (.sext 8 64) (.var x)) fun (sx, ()) =>
        .let_ (op2 (.cmp .slt i64) (.var sx) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Branch inversion: threading `true` arm (`jump j0`) flips `== 0` (`CBZ`) to `CBNZ`. -/
meta def cbzFlipThreadFn : Fn :=
  ⟨"cbzFlipThread", [i64, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var x) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j0 ()) (.jump j1 ())⟩

/-- Multi-use condition `c` still materializes when used again inside a branch body. -/
meta def cmpZeroReuseFn : Fn :=
  ⟨"cmpZeroReuse", [i64, i64], [.bool], fun _ _ (x, _y, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var c, ())) (.ret (.imm false, ()))⟩

#guard chk [cbz64Fn]
#guard countDirs isCbnzDir (codeOf [cbz64Fn]) == 1
#guard countDirs isSubsDir (codeOf [cbz64Fn]) == 0
#guard countDirs isBcondDir (codeOf [cbz64Fn]) == 0

#guard chk [cbnz32CommFn]
#guard countDirs isCbzDir (codeOf [cbnz32CommFn]) == 1
#guard countDirs isSubsDir (codeOf [cbnz32CommFn]) == 0
#guard countDirs isBcondDir (codeOf [cbnz32CommFn]) == 0

#guard chk [cbz8Fn]
#guard countDirs isCbnzDir (codeOf [cbz8Fn]) == 1
#guard countDirs isSubsDir (codeOf [cbz8Fn]) == 0

#guard chk [sltZero32Fn]
#guard countDirs isTbzDir (codeOf [sltZero32Fn]) == 1
#guard countDirs isSubsDir (codeOf [sltZero32Fn]) == 0

#guard chk [ugtZero64Fn]
#guard countDirs isCbzDir (codeOf [ugtZero64Fn]) == 1
#guard countDirs isSubsDir (codeOf [ugtZero64Fn]) == 0

#guard chk [tbz64Bit5Fn]
#guard countDirs isTbnzDir (codeOf [tbz64Bit5Fn]) == 1
#guard countDirs isAndsDir (codeOf [tbz64Bit5Fn]) == 0

#guard chk [sextSltZeroFn]
#guard countDirs isTbzDir (codeOf [sextSltZeroFn]) == 1
#guard countDirs isSubsDir (codeOf [sextSltZeroFn]) == 0

#guard chk [cbzFlipThreadFn]
#guard countDirs isCbzDir (codeOf [cbzFlipThreadFn]) == 1
#guard countDirs isCbnzDir (codeOf [cbzFlipThreadFn]) == 0

#guard chk [cmpZeroReuseFn]

/-! ## 3. `FullM4Bcp` & `LratBytes` fusion counts -/

meta def m4BcpEx : List (SigEntry × Nat) :=
  Examples.Kissat.FullM4Bcp.m4BcpExterns.map fun e => (⟨e.name, e.as, e.rs⟩, 0)

#guard chk Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx
#guard countDirs (fun d => isCbzDir d || isCbnzDir d)
  (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) ≥ 1
#guard countDirs (fun d => isTbzDir d || isTbnzDir d)
  (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) ≥ 1

#guard chk Examples.LratBytes.lratBytesFns
#guard countDirs (fun d => isCbzDir d || isCbnzDir d)
  (codeOf Examples.LratBytes.lratBytesFns) ≥ 20
-- Rank-2 `SimplifyGroupPlan` splicing eliminates 1 raw `tbnz #0` bool branch (`25 -> 24`).
#guard countDirs (fun d => isTbzDir d || isTbnzDir d)
  (codeOf Examples.LratBytes.lratBytesFns) ≥ 24

theorem lratBytes_compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      Examples.LratBytes.lratBytesFns Arm64.LratBytes.lratBytesHints 2048 = true :=
  Arm64.LratBytes.compiled_check

/-! ## 4. Axiom audit -/

#print axioms LeanQbe.T.Arm64.armCmpZeroJcc_spec
#print axioms LeanQbe.T.Arm64.armTestJcc_spec
#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.Arm64.LratBytes.lrat_check_bytes_arm64_correct

end LeanQbeTest.T.Arm64BranchFuseTest
