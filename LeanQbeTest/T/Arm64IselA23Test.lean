module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.LratBytes
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.FullM4Bcp
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Arm64.LratBytes
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.FullM4Bcp
meta import LeanQbe.T.Spill

/-!
# AArch64 `armTestOp` (`supportsTestFuse`) + `baseIdxDisp` Regression Tests

Verifies test-fusion and base-index-displacement addressing through `armTarget` and
`Rega.lowerFn`:
1. Test fusion (`armTestOp` + `armIsa.supportsTestFuse := true`):
   - `ANDS_i` for bitmask immediates (`0x80000000`, `0x80`, `1`), `ANDS_s` for register/all-ones;
   - `8`/`16`-bit `(gpr, imm)` without `UBFM`, `(gpr, gpr)` with 1 `UBFM` + `ANDS_s`;
   - `Rega.tryExtCmp` fusing `sext`/`zext` + `cmp` at narrow width.
2. Base-index-displacement addressing (`armSupportsAddrIdx` + `armSetupAddrIns` for `.baseIdxDisp`
   with `disp != 0`):
   - `ADD_s x16, rb, ri, lsl #s` + `[x16, #disp]` for scaled offsets (`4`, `4100`, unaligned `sc`);
   - `ADD_e`/`SUB_e x16, rb, #imm` + `[x16, ri, lsl #amt]` for negative/unaligned 12-bit disps.
3. End-to-end checks on `FullM4Bcp`, `LratBytes`, and standard `#print axioms`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64IselA23Test

open LeanQbe.T LeanQbe.T.Arm64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

meta def chk (fs : List Fn) (exs : List (SigEntry × Nat) := []) : Bool :=
  checkCompile armTarget armLayout armLegalTarget exs [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) (exs : List (SigEntry × Nat) := []) : List Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes exs [] 0 fs
    (hintsOf fs))

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat :=
  (ds.filter p).length

meta def isAndsImmDir : Directive → Bool
  | .instr { operation := .ANDS_i .., .. } => true
  | _ => false

meta def isAndsRegDir : Directive → Bool
  | .instr { operation := .ANDS_s .., .. } => true
  | _ => false

meta def isAndsDir (d : Directive) : Bool :=
  isAndsImmDir d || isAndsRegDir d

meta def isAndDir : Directive → Bool
  | .instr { operation := .AND_i .., .. }
  | .instr { operation := .AND_s .., .. } => true
  | _ => false

meta def isSubsDir : Directive → Bool
  | .instr { operation := .SUBS_e .., .. }
  | .instr { operation := .SUBS_s .., .. } => true
  | _ => false

meta def isTbzOrTbnzDir : Directive → Bool
  | .instr { operation := .TBZ .., .. }
  | .instr { operation := .TBNZ .., .. } => true
  | _ => false

meta def isAddScaledDir : Directive → Bool
  | .instr { operation := .ADD_s (.low (.reg .X16) .W64) _ _, .. } => true
  | _ => false

meta def isSubImmX16Dir : Directive → Bool
  | .instr { operation := .SUB_e (.low (.reg .X16) .W64) _ _, .. } => true
  | _ => false

meta def isLslDir : Directive → Bool
  | .instr { operation := .UBFM _ _ 62 61, .. }
  | .instr { operation := .UBFM _ _ 61 60, .. }
  | .instr { operation := .LSLV .., .. } => true
  | _ => false

meta def isExtDir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. }
  | .instr { operation := .SBFM _ _ 0 7, .. }
  | .instr { operation := .UBFM _ _ 0 15, .. }
  | .instr { operation := .SBFM _ _ 0 15, .. } => true
  | _ => false

/-! ## 1. Test-fusion & `baseIdxDisp` Isa & Isel unit checks -/

theorem armIsa_a2_a3_rfl :
    armTarget.toIsa.supportsTestFuse = true ∧
    armTarget.toIsa.supportsAddrIdx i32 .s4 4#64 = true ∧
    armTarget.toIsa.supportsAddrIdx i32 .s4 (-4#64) = true ∧
    armTarget.toIsa.supportsAddrIdx i8 .s4 4#64 = true ∧
    armTarget.toIsa.supportsAddrIdx i64 .s8 4104#64 = true ∧
    armTarget.toIsa.supportsAddrIdx i64 .s8 0x123456#64 = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#guard match armGpr.testOp 32 true (.gpr (.reg .X1)) (.imm 0x80000000#32) (.flag .ne) with
  | some ([d], _) => isAndsImmDir d
  | _ => false

#guard match armGpr.testOp 64 false (.gpr (.reg .X1)) (.gpr (.reg .X2)) (.flag .eq) with
  | some ([d], _) => isAndsRegDir d
  | _ => false

#guard match armGpr.testOp 64 true (.gpr (.reg .X1)) (.imm (~~~0#64)) (.flag .ne) with
  | some ([d], _) => isAndsRegDir d
  | _ => false

#guard match armGpr.testOp 8 true (.gpr (.reg .X1)) (.imm 0x80#8) (.flag .ne) with
  | some ([d], _) => isAndsImmDir d
  | _ => false

#guard match armGpr.testOp 8 false (.gpr (.reg .X1)) (.gpr (.reg .X2)) (.flag .eq) with
  | some ([d1, d2], _) => isExtDir d1 && isAndsRegDir d2
  | _ => false

#guard match armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 4) with
  | some ([d1, _], _) => isAddScaledDir d1
  | _ => false

#guard match armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 (-4)) with
  | some ([d1, _], _) => isSubImmX16Dir d1
  | _ => false

#guard match armGpr.store i8 (.gpr (.reg .X0)) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 4) with
  | some ([d1, _], _) => isAddScaledDir d1
  | _ => false

/-! ## 2. End-to-end verified lowering regressions -/

/-- `full_prop_lit_raw`-style bitmask test `(x & 0x80000000) != 0` emits 1 `ANDS_i`. -/
meta def bitTestImm32Fn : Fn :=
  ⟨"bitTestImm32", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.and i32) (.var x) (.imm 0x80000000)) fun (t, ()) =>
        .let_ (op2 (.cmp .ne i32) (.var t) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- Register bit-test `(x & y) == 0` emits 1 `ANDS_s`, 0 `AND`/`CMP`. -/
meta def bitTestReg64Fn : Fn :=
  ⟨"bitTestReg64", [i64, i64, i64, i64], [i64], fun _ _ (x, y, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.and i64) (.var x) (.var y)) fun (t, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var t) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- `LratBytes` LEB128 bit-7 test `((load i8 p) & 0x80) != 0` emits `ANDS_i`, 0 `UBFM`/`CMP`. -/
meta def leb128Bit7Fn : Fn :=
  ⟨"leb128Bit7", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .load i8 (.var p) fun v =>
        .let_ (op2 (.and i8) (.var v) (.imm 0x80)) fun (t, ()) =>
        .let_ (op2 (.cmp .ne i8) (.var t) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- `Rega.tryExtCmp`: `sext 8 64` + `cmp .slt (-1)` folds without widening. -/
meta def extCmpSext8Fn : Fn :=
  ⟨"extCmpSext8", [i8, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op1 (.sext 8 64) (.var x)) fun (sx, ()) =>
        .let_ (op2 (.cmp .slt i64) (.var sx) (.imm (-1))) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

/-- `wdata[i + 1]` load & store (`base + (i << 2) + 4`) fuse into `ADD_s x16` + `[x16, #4]`. -/
meta def baseIdxDisp4Fn : Fn :=
  ⟨"baseIdxDisp4", [i64, i64], [i32], fun _ _ (base, idx, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm 4)) fun (p1, ()) =>
    .load i32 (.var p1) fun v =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off2, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off2)) fun (q0, ()) =>
    .let_ (op2 (.add i64) (.var q0) (.imm 8)) fun (q1, ()) =>
    .store (t := i32) (.var v) (.var q1) <|
    .ret (.var v, ())⟩

/-- Negative offset `arr[i - 1]` uses `SUB_e x16, base, #4` + `[x16, i, lsl #2]`. -/
meta def baseIdxNegDispFn : Fn :=
  ⟨"baseIdxNegDisp", [i64, i64], [i32], fun _ _ (base, idx, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var base) (.var off)) fun (p0, ()) =>
    .let_ (op2 (.add i64) (.var p0) (.imm (-4))) fun (p1, ()) =>
    .load i32 (.var p1) fun v =>
    .ret (.var v, ())⟩

/-- Multi-bit mask test `(x & 0x6) != 0` emits 1 `ANDS_i` (not single-bit `TBZ`/`TBNZ`). -/
meta def bitTestMultiImm32Fn : Fn :=
  ⟨"bitTestMultiImm32", [i32, i64, i64], [i64], fun _ _ (x, a, b, ()) =>
    .group (sig := [[], []])
      (fun _ => Blocks.cons (fun () => .ret (.var a, ()))
        (Blocks.cons (fun () =>
          .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ()))
          Blocks.nil))
      fun (j0, j1, ()) =>
        .let_ (op2 (.and i32) (.var x) (.imm 0x6)) fun (t, ()) =>
        .let_ (op2 (.cmp .ne i32) (.var t) (.imm 0)) fun (c, ()) =>
        .jnz (.var c) (.jump j1 ()) (.jump j0 ())⟩

#guard chk [bitTestImm32Fn]
#guard countDirs isTbzOrTbnzDir (codeOf [bitTestImm32Fn]) == 1
#guard countDirs isAndsImmDir (codeOf [bitTestImm32Fn]) == 0
#guard countDirs isAndDir (codeOf [bitTestImm32Fn]) == 0
#guard countDirs isSubsDir (codeOf [bitTestImm32Fn]) == 0

#guard chk [bitTestMultiImm32Fn]
#guard countDirs isAndsImmDir (codeOf [bitTestMultiImm32Fn]) == 1
#guard countDirs isTbzOrTbnzDir (codeOf [bitTestMultiImm32Fn]) == 0
#guard countDirs isAndDir (codeOf [bitTestMultiImm32Fn]) == 0
#guard countDirs isSubsDir (codeOf [bitTestMultiImm32Fn]) == 0

#guard chk [bitTestReg64Fn]
#guard countDirs isAndsRegDir (codeOf [bitTestReg64Fn]) == 1
#guard countDirs isAndDir (codeOf [bitTestReg64Fn]) == 0
#guard countDirs isSubsDir (codeOf [bitTestReg64Fn]) == 0

#guard chk [leb128Bit7Fn]
#guard countDirs isTbzOrTbnzDir (codeOf [leb128Bit7Fn]) == 1
#guard countDirs isAndsImmDir (codeOf [leb128Bit7Fn]) == 0
#guard countDirs isExtDir (codeOf [leb128Bit7Fn]) == 0
#guard countDirs isSubsDir (codeOf [leb128Bit7Fn]) == 0

#guard chk [extCmpSext8Fn]
#guard countDirs isSubsDir (codeOf [extCmpSext8Fn]) == 0

#guard chk [baseIdxDisp4Fn]
#guard countDirs isAddScaledDir (codeOf [baseIdxDisp4Fn]) == 2
#guard countDirs isLslDir (codeOf [baseIdxDisp4Fn]) == 0

#guard chk [baseIdxNegDispFn]
#guard countDirs isSubImmX16Dir (codeOf [baseIdxNegDispFn]) == 1
#guard countDirs isLslDir (codeOf [baseIdxNegDispFn]) == 0

/-! ## 3. `FullM4Bcp` & `LratBytes` codegen -/

meta def m4BcpEx : List (SigEntry × Nat) :=
  Examples.Kissat.FullM4Bcp.m4BcpExterns.map fun e => (⟨e.name, e.as, e.rs⟩, 0)

#guard chk Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx
#guard countDirs isAndsDir (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) ≥ 1
#guard countDirs isAddScaledDir (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) ≥ 1

#guard chk Examples.LratBytes.lratBytesFns
#guard countDirs isTbzOrTbnzDir (codeOf Examples.LratBytes.lratBytesFns) ≥ 14

/-! ## 4. Axiom audit -/

#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armTestOp_wp
#print axioms LeanQbe.T.Arm64.armSetupAddr_wp
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.Arm64.LratBytes.lrat_check_bytes_arm64_correct

end LeanQbeTest.T.Arm64IselA23Test
