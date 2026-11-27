module

public import LeanQbe.T.Arm64.IselShiftLemmas
public import LeanQbe.T.Arm64.IselNarrowLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Driver
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbeTest.T.RegaTestKit
public import LeanQbeTest.T.Arm64DirPreds
import Kraken.AArch64.Parser
meta import LeanQbe.T.Arm64.IselShift
meta import LeanQbe.T.Arm64.IselNarrow
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbeTest.T.RegaTestKit
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbe.T.Logic.ProofKit

/-!
# Arm64 Wave-5 & Rank-9 Instruction Selection Test Suite (`Arm64W5IselTest`)

Verifies all Wave-5 (`W5-1c`) shifted/extended ISel helpers and Rank-9 load/sign/compare helpers:
1. Kernel `rfl` / `#guard` positive and negative bounds for `armShiftedCmp?`, `armExtAlu?`,
   `armExtCmp?`, `armCmpZextOp`, `armCmpZeroZextJcc`, `armCmpMem`, widened `armGpr.loadSext 32 64`,
   and widened `armGpr.leaArith`.
2. End-to-end `RegaTestKit.chk`/`codeOf` regressions for `LDRSW`, displaced `leaArith`, and
   `FullM4` compilation (`Driver.compileFns`).
3. Concrete `Host.ofLayout` execution witnesses via `armShiftedCmp_spec`, `armExtAlu_zero32`,
   `armExtCmp_spec`, `armCmpZextOp_spec`, `armCmpZeroZextJcc_spec`, and `armCmpMem_flags_spec`.
4. Standard-axiom verification (`ProofKit.check_std_axioms!`) across all new theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Arm64W5IselTest

open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbeTest.T.Arm64DirPreds
open Kraken.AArch64.Parser

/-! ## 1. Unit & Negative Boundary Checks (`rfl` / `#guard`) -/

example :
    armShiftedCmp? .eq 64 (.reg .X1) (.reg .X2) .lsl 3 false (.flag .eq) =
      some (⸨prog| subs xzr, x1, x2, lsl #3 ⸩, maskNZCV) ∧
    armShiftedCmp? .ult 32 (.reg .X3) (.reg .X4) .lsr 31 false (.flag .cc) =
      some (⸨prog| subs wzr, w3, w4, lsr #31 ⸩, maskNZCV) ∧
    armShiftedCmp? .slt 64 (.reg .X5) (.reg .X6) .asr 17 true (.gpr (.reg .X0)) =
      some (⸨prog|
        subs xzr, x6, x5, asr #17
        csinc x0, xzr, xzr, le
      ⸩, maskNZCV) ∧
    armShiftedCmpFlagsOut .slt 64 true (.gpr (.reg .X0)) = some false ∧
    armShiftedCmpFlagsOut .slt 64 true (.flag .gt) = some false ∧
    armShiftedCmpFlagsOut .slt 64 true (.flag .lt) = none ∧
    (armShiftedCmp? .eq 32 (.reg .X1) (.reg .X2) .lsl 32 false (.flag .eq)) = none ∧
    (armShiftedCmp? .eq 16 (.reg .X1) (.reg .X2) .lsl 1 false (.flag .eq)) = none ∧
    (armShiftedCmp? .eq 64 .SP (.reg .X2) .lsl 1 false (.flag .eq)) = none ∧
    (armShiftedCmp? .slt 64 (.reg .X1) (.reg .X2) .lsl 1 true (.flag .lt)) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    armExtAlu? 64 (.add _) (.reg .X1) (.reg .X2) .uxtw 2 (.reg .X0) =
      some (⸨prog| add x0, x1, w2, uxtw #2 ⸩, maskNone) ∧
    armExtAlu? 64 (.sub _) (.reg .X3) (.reg .X4) .sxtw 4 (.reg .X5) =
      some (⸨prog| sub x5, x3, w4, sxtw #4 ⸩, maskNone) ∧
    armExtAlu? 32 (.add _) (.reg .X1) (.reg .X2) .uxtb 0 (.reg .X0) =
      some (⸨prog| add w0, w1, w2, uxtb #0 ⸩, maskNone) ∧
    armExtAlu? 32 (.sub _) (.reg .X1) (.reg .X2) .sxth 3 (.reg .X0) =
      some (⸨prog| sub w0, w1, w2, sxth #3 ⸩, maskNone) ∧
    (armExtAlu? 64 (.add _) (.reg .X1) (.reg .X2) .uxtw 5 (.reg .X0)) = none ∧
    (armExtAlu? 16 (.add _) (.reg .X1) (.reg .X2) .uxtb 0 (.reg .X0)) = none ∧
    (armExtAlu? 64 (.mul _) (.reg .X1) (.reg .X2) .uxtw 0 (.reg .X0)) = none ∧
    (armExtAlu? 64 (.add _) .SP (.reg .X2) .uxtw 0 (.reg .X0)) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    armExtCmp? .sgt 64 (.reg .X1) (.reg .X2) .sxtw 3 false (.flag .gt) =
      some (⸨prog| subs xzr, x1, w2, sxtw #3 ⸩, maskNZCV) ∧
    armExtCmp? .ne 32 (.reg .X3) (.reg .X4) .uxtb 1 true (.gpr (.reg .X0)) =
      some (⸨prog|
        subs wzr, w4, w3, uxtb #1
        csinc x0, xzr, xzr, eq
      ⸩, maskNZCV) ∧
    armExtCmpFlagsOut .sgt 64 true (.flag .lt) = some false ∧
    armExtCmpFlagsOut .sgt 64 true (.flag .gt) = none ∧
    (armExtCmp? .eq 64 (.reg .X1) (.reg .X2) .sxtw 5 false (.flag .eq)) = none ∧
    (armExtCmp? .eq 32 (.reg .X1) .SP .uxtw 0 false (.flag .eq)) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    armCmpZextOp .ult 8 true true (.gpr (.reg .X1)) (.gpr (.reg .X2)) (.flag .cc) =
      some (⸨prog| subs wzr, w1, w2 ⸩, maskNZCV) ∧
    armCmpZextOp .eq 16 true false (.gpr (.reg .X1)) (.imm 7#16) (.flag .eq) =
      some (⸨prog| subs wzr, w1, #7 ⸩, maskNZCV) ∧
    armCmpZextOp .ult 8 false true (.imm 5#8) (.gpr (.reg .X2)) (.flag .hi) =
      some (⸨prog| subs wzr, w2, #5 ⸩, maskNZCV) ∧
    armCmpZextOp .ult 8 false false (.gpr (.reg .X1)) (.gpr (.reg .X2)) (.flag .cc) =
      some (⸨prog|
        ubfm w16, w1, #0, #7
        ubfm w17, w2, #0, #7
        subs wzr, w16, w17
      ⸩, maskNZCV) ∧
    armCmpZeroZextJcc true .eq 8 (.reg .X1) "L_z" =
      some (⸨prog| cbz w1, L_z ⸩, maskNone) ∧
    armCmpZeroZextJcc true .ugt 16 (.reg .X2) "L_nz" =
      some (⸨prog| cbnz w2, L_nz ⸩, maskNone) ∧
    armCmpZeroZextJcc false .eq 8 (.reg .X1) "L_z" =
      some (⸨prog|
        ubfm w16, w1, #0, #7
        cbz w16, L_z
      ⸩, maskNone) ∧
    armCmpMem .slt 8 (.baseDisp (.reg .X1) 0) (.imm 0#8) (.flag .lt) =
      some (⸨prog|
        ldrsb x17, [x1]
        subs wzr, w17, #0
      ⸩, maskNZCV) ∧
    armCmpMem .eq 8 (.baseDisp (.reg .X1) 4) (.imm 42#8) (.flag .eq) =
      some (⸨prog|
        ldrb w17, [x1, #4]
        subs wzr, w17, #42
      ⸩, maskNZCV) ∧
    armCmpMem .sge 16 (.baseIdxDisp (.reg .X1) (.reg .X2) .s2 0) (.gpr (.reg .X3))
        (.gpr (.reg .X0)) =
      some (⸨prog|
        ldrsh x17, [x1, x2, lsl #1]
        sbfm w16, w3, #0, #15
        subs wzr, w17, w16
        csinc x0, xzr, xzr, lt
      ⸩, maskNZCV) ∧
    armCmpMemFlagsOut .slt 8 (.imm 0#8) (.flag .lt) = some true ∧
    armCmpMemFlagsOut .slt 8 (.imm 0#8) (.flag .gt) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    armGpr.loadSext 32 64 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0) =
      some (⸨prog| ldrsw x0, [x1, x2, lsl #2] ⸩, maskNone) ∧
    (armGpr.loadSext 32 64 (.reg .X0) (.baseIdxDisp .SP (.reg .X2) .s4 0)) = none ∧
    (armGpr.loadSext 32 32 (.reg .X0) (.baseDisp (.reg .X1) 0)) = none ∧
    armGpr.leaArith 64 (some (.reg .X1)) (.reg .X2) .s8 (-16) (.reg .X0) =
      some (⸨prog|
        add x16, x1, x2, lsl #3
        sub x0, x16, #16
      ⸩, maskNone) ∧
    armGpr.leaArith 64 none (.reg .X1) .s4 8 (.reg .X0) =
      some (⸨prog|
        ubfm x16, x1, #62, #61
        add x0, x16, #8
      ⸩, maskNone) ∧
    (armGpr.leaArith 64 (some (.reg .X1)) (.reg .X2) .s4 5000 (.reg .X0)) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. End-to-End Lowering Regressions & `FullM4` Check -/

meta def isLdrswDir : armTarget.toIsa.Directive → Bool
  | .instr { operation := .LDRSW .., .. } => true
  | _ => false

meta def hasAddScaledX16 (d : armTarget.toIsa.Directive) : Bool :=
  (Kraken.AArch64.Print.directive d).startsWith "add x16, x"

meta def sext32To64LoadFn : Fn :=
  ⟨"sext32To64Load", [i64], [i64], fun _ _ (p, ()) =>
    .load i32 (.var p) fun v =>
    .let_ (op1 (.sext 32 64) (.var v)) fun (sx, ()) =>
    .ret (.var sx, ())⟩

meta def leaDispFn : Fn :=
  ⟨"leaDisp", [i64, i64], [i64], fun _ _ (p, idx, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var s)) fun (q, ()) =>
    .let_ (op2 (.add i64) (.var q) (.imm 8)) fun (r, ()) =>
    .ret (.var r, ())⟩

meta def leaNoBaseScaledDispFn : Fn :=
  ⟨"leaNoBaseScaledDisp", [i64], [i64], fun _ _ (idx, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (s, ()) =>
    .let_ (op2 (.add i64) (.var s) (.imm 12)) fun (r, ()) =>
    .ret (.var r, ())⟩

#guard chk armTarget armLayout armLegalTarget [sext32To64LoadFn]
#guard countDirs isLdrswDir
    (codeOf armTarget armLegalTarget [sext32To64LoadFn]) == 1
#guard countDirs isArmSext32Dir
    (codeOf armTarget armLegalTarget [sext32To64LoadFn]) == 0

#guard chk armTarget armLayout armLegalTarget [leaDispFn]
#guard countDirs hasAddScaledX16
    (codeOf armTarget armLegalTarget [leaDispFn]) ≥ 1

#guard chk armTarget armLayout armLegalTarget [leaNoBaseScaledDispFn]

#guard match Driver.compileFns armIsa armLegalTarget Examples.Kissat.FullM4.m4Module.fns with
  | .ok code => code.length > 20000
  | .error _ => false

/-! ## 3. Concrete `Host.ofLayout` Execution Witnesses -/

@[instance_reducible] def w5Layout : Layout where
  start := 0x50000
  instrSize _ := 4
  instrSize_pos _ := by decide

/-- Witness for `armShiftedCmp?` with `lhsShift = true` (flag reuse via `o.swap`). -/
theorem witness_shifted_cmp_lhs_swap (h : Host) (s : MachineData)
    (hx1 : armMach.getGpr s (.reg .X1) = 0x0000_0000_0000_0001#64)
    (hx2 : armMach.getGpr s (.reg .X2) = 0x0000_0000_0000_0010#64)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      ⸨prog| subs xzr, x2, x1, lsl #3 ⸩
      armScratch [] maskNZCV s
      (fun s' =>
        armMach.PDstHolds s' .bool (.flag .gt) true ∧
        FlagCmpOk armMach armGpr s' 16#64 8#64 false ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hc := armShiftedCmp_spec h (steps := 1) (o := .slt) (w := 64)
    (.reg .X1) (.reg .X2) .lsl 3 true (.flag .gt)
    ⸨prog| subs xzr, x2, x1, lsl #3 ⸩ maskNZCV (by rfl) s 1#64 16#64
    (by rw [hx1]; simp [GprHolds]) (by rw [hx2]; simp [GprHolds]) post
  have hcmps : CmpOp.slt.evalBits (ArmShiftOp.lsl.eval 1#64 3) 16#64 = true := by decide
  intro hinfix hcont
  refine hc hinfix (fun s' ⟨hpd, hfc, hmem⟩ hfr => hcont s' ⟨?_, ?_, hmem⟩ hfr)
  · simpa [hcmps] using hpd
  · exact hfc (lf := false) rfl

/-- Witness that 32-bit `armExtAlu?` with `.sxtw` sign-extends and clears upper 32 bits of `rd`. -/
theorem witness_ext_alu_sxtw_zero32 (h : Host) (s : MachineData)
    (ha : armMach.getGpr s (.reg .X1) = 0xffff_ffff_0000_0100#64)
    (hb : armMach.getGpr s (.reg .X2) = 0x1234_5678_ffff_fffe#64)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      ⸨prog| add w0, w1, w2, sxtw #2 ⸩
      (.reg .X0 :: armScratch) [] maskNone s
      (fun s' =>
        armMach.getGpr s' (.reg .X0) = 0x0000_0000_0000_00f8#64 ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hc := armExtAlu_zero32 h (steps := 1) (.add _) (.reg .X1) (.reg .X2) .sxtw 2 (.reg .X0)
    ⸨prog| add w0, w1, w2, sxtw #2 ⸩ maskNone (by rfl) s 0x0000_0100#32 0xffff_fffe#32
    (by rw [ha]; simp [GprHolds]) (by rw [hb]; simp [GprHolds, ArmExtType.srcBits]) post
  intro hinfix hcont
  refine hc hinfix (fun s' ⟨hw, hmem, _⟩ hfr => hcont s' ⟨?_, hmem⟩ hfr)
  simpa [OpCode.wp, lift2, ArmExtType.eval, ArmExtType.isSigned] using hw

/-- Witness for `armExtCmp?` (`uxth #1`, `lhsExt = true`, `.gpr`). -/
theorem witness_ext_cmp_uxth (h : Host) (s : MachineData)
    (ha : armMach.getGpr s (.reg .X1) = 0xffff_ffff_ffff_0010#64)
    (hb : armMach.getGpr s (.reg .X2) = 0x0000_0000_0000_001f#64)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      ⸨prog|
        subs xzr, x2, w1, uxth #1
        csinc x0, xzr, xzr, ge
      ⸩
      (.reg .X0 :: armScratch) [] maskNZCV s
      (fun s' =>
        armMach.PDstHolds s' .bool (.gpr (.reg .X0)) true ∧
        FlagCmpOk armMach armGpr s' 31#64 32#64 false ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hhb : GprHolds (armMach.getGpr s (if true then .reg .X2 else .reg .X1))
      (.bits 64) 31#64 := by
    simpa [GprHolds] using hb
  have hha : GprHolds (armMach.getGpr s (if true then .reg .X1 else .reg .X2))
      (.bits ArmExtType.uxth.srcBits) 0x0010#16 := by
    refine ⟨by decide, ?_⟩
    change (armMach.getGpr s (.reg .X1)).setWidth 16 = 0x0010#16
    rw [ha]
    rfl
  have hc := armExtCmp_spec h (steps := 1) (o := .sgt) (w := 64)
    (.reg .X1) (.reg .X2) .uxth 1 true (.gpr (.reg .X0))
    ⸨prog|
      subs xzr, x2, w1, uxth #1
      csinc x0, xzr, xzr, ge
    ⸩ maskNZCV (by rfl) s 31#64 0x0010#16 hhb hha post
  have hcmp : CmpOp.sgt.evalBits (ArmExtType.uxth.eval (w := 64) 0x0010#16 1) 31#64 = true := by
    decide
  intro hinfix hcont
  refine hc hinfix (fun s' ⟨hpd, hfc, hmem⟩ hfr => hcont s' ⟨?_, ?_, hmem⟩ hfr)
  · simpa [hcmp] using hpd
  · exact hfc (lf := false) rfl

/-- Witness that `armCmpZextOp` elides `UBFM #0, #7` when `AbiGprHolds` holds (`az = bz = true`). -/
theorem witness_cmp_zext_op_elide (h : Host) (s : MachineData)
    (ha : AbiGprHolds (armMach.getGpr s (.reg .X1)) i8 0x05#8)
    (hb : AbiGprHolds (armMach.getGpr s (.reg .X2)) i8 0xfe#8)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      ⸨prog| subs wzr, w1, w2 ⸩
      armScratch [] maskNZCV s
      (fun s' =>
        armMach.PDstHolds s' .bool (.flag .cc) true ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hc := armCmpZextOp_spec (h := h) (k := 1) (o := .ult) (n := 8) (az := true) (bz := true)
    (pa := .gpr (.reg .X1)) (pb := .gpr (.reg .X2)) (dst := .flag .cc)
    (c := ⸨prog| subs wzr, w1, w2 ⸩) (clob := maskNZCV) (va := 0x05#8) (vb := 0xfe#8)
    (s := s) (post := post) rfl (by simp [armScratch]) (by simp [armScratch])
    ⟨.reg .X1, rfl, ha⟩ ⟨.reg .X2, rfl, hb⟩
  have heval : CmpOp.ult.evalBits 0x05#8 0xfe#8 = true := by decide
  simpa [heval] using hc

/-- Witness that `armCmpZeroZextJcc` branches via 1-insn `CBZ w1` when `AbiGprHolds` holds. -/
def cbzZextProg : List Directive :=
  ⸨prog|
    cbz w1, L_zero
    nop
  L_zero:
    nop
  ⸩

theorem cbzZextProg_small :
    (Kraken.Layout.apply w5Layout cbzZextProg).sizeBefore cbzZextProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply w5Layout cbzZextProg).sizeBefore cbzZextProg.length = 12 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
    decide
  omega

@[instance_reducible] def cbzZextHost : Host := Host.ofLayout cbzZextProg w5Layout cbzZextProg_small

theorem witness_cmp_zero_zext_jcc_cbz {s : MachineData}
    (ha : AbiGprHolds (armMach.getGpr s (.reg .X1)) i8 0#8) :
    armMach.Run cbzZextHost 0 s fun st => st.pc = armMach.addrOf cbzZextHost 2 := by
  letI := cbzZextHost
  have hc : ⸨prog| cbz w1, L_zero ⸩.IsInfixAt (armMach.prog cbzZextHost) 0 :=
    ⟨⸨prog|
      nop
    L_zero:
      nop
    ⸩, rfl⟩
  have hl : armMach.labelAddr cbzZextHost "L_zero" = armMach.addrOf cbzZextHost 2 :=
    letI := cbzZextHost
    Host.label_eq_addrOf rfl ((Host.labelsUnique_of_nodup (by decide)).first rfl)
  refine armCmpZeroZextJcc_spec (h := cbzZextHost) (k := 0) (j := 2) (isZext := true) (co := .ule)
    (n := 8) (r := .reg .X1) (l := "L_zero") (v := 0#8) rfl hc hl
    (by simp [armScratch]) ha ?_
  intro s' _ _
  refine ⟨fun _ => Eventually.done _ rfl, fun hf => by simp [CmpOp.evalBits] at hf⟩

/-- Witness that `armCmpMem` fuses signed `LDRSB` + `CMP` and exports `FlagCmpOk`. -/
theorem witness_cmp_mem_ldrsb_flags (h : Host) (s : MachineData)
    (hload : loadVal (armMach.mem s) i8 (AddrArg.eval (armMach.getGpr s) (.baseDisp (.reg .X1) 0)) =
      some 0xfb#8)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      ⸨prog|
        ldrsb x17, [x1]
        subs wzr, w17, #1
      ⸩
      armScratch [] maskNZCV s
      (fun s' =>
        armMach.PDstHolds s' .bool (.flag .lt) true ∧
        FlagCmpOk armMach armGpr s' 0xfb#8 1#8 false ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hc := armCmpMem_flags_spec (h := h) (k := 1) (co := .slt) (w := 8)
    (a := .baseDisp (.reg .X1) 0) (pb := .imm 1#8) (pd := .flag .lt) (lhsFirst := true)
    (c := ⸨prog|
      ldrsb x17, [x1]
      subs wzr, w17, #1
    ⸩) (clob := maskNZCV)
    (va := 0xfb#8) (vb := 1#8) (s := s) (post := post) rfl rfl
    (by simp [AddrArg.regs, armScratch]) (by simp [armScratch]) hload rfl
  have heval : CmpOp.slt.evalBits 0xfb#8 1#8 = true := by decide
  simpa [heval] using hc

/-! ## 4. Standard-Axiom Verification -/

open LeanQbe.T.ProofKit in
check_std_axioms!
  LeanQbe.T.Arm64.armShiftedCmp_noLab
  LeanQbe.T.Arm64.armShiftedCmp_wp
  LeanQbe.T.Arm64.armShiftedCmp_spec
  LeanQbe.T.Arm64.armExtAlu_noLab
  LeanQbe.T.Arm64.armExtAlu_wp
  LeanQbe.T.Arm64.armExtAlu_spec
  LeanQbe.T.Arm64.armExtAlu_zero32
  LeanQbe.T.Arm64.armExtCmp_noLab
  LeanQbe.T.Arm64.armExtCmp_wp
  LeanQbe.T.Arm64.armExtCmp_spec
  LeanQbe.T.Arm64.armCmpZextOp_noLab
  LeanQbe.T.Arm64.armCmpZextOp_spec
  LeanQbe.T.Arm64.armCmpZeroZextJcc_noLab
  LeanQbe.T.Arm64.armCmpZeroZextJcc_spec
  LeanQbe.T.Arm64.armCmpMem_noLab
  LeanQbe.T.Arm64.armCmpMem_spec
  LeanQbe.T.Arm64.armCmpMem_flags_spec
  LeanQbeTest.T.Arm64W5IselTest.witness_shifted_cmp_lhs_swap
  LeanQbeTest.T.Arm64W5IselTest.witness_ext_alu_sxtw_zero32
  LeanQbeTest.T.Arm64W5IselTest.witness_ext_cmp_uxth
  LeanQbeTest.T.Arm64W5IselTest.witness_cmp_zext_op_elide
  LeanQbeTest.T.Arm64W5IselTest.witness_cmp_zero_zext_jcc_cbz
  LeanQbeTest.T.Arm64W5IselTest.witness_cmp_mem_ldrsb_flags

end LeanQbeTest.T.Arm64W5IselTest
