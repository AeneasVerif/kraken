module

public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.FrameLemmas
public import LeanQbe.T.Legal

/-!
# AAPCS64 Arm64 `Target` Assembly & Legalization Parity (`T12i`)

Assembles `armTarget : Target` from the verified AArch64 ISA components (`armMach`, `armGpr`,
`VecIsa.empty`, `armFrame`, `armGprSpec`, `VecTarget.empty`, `armFrameSpec`) and defines
`armLegalTarget := LegalTarget.aarch64` alongside capability parity theorems and kernel check suites
documenting the exact scalar/width boundary (`popcnt := false`, `[32, 64]` for
`clz`/`cls`/`rbit`/`ctz`/`fshl`/`fshr`/`addc`/`subb`/`umulw`/`smulw`, `[16, 32, 64]` for
`bswap`, and `[8, 16, 32, 64]` otherwise; `#323`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Target Assembly (`armTarget`) and Legalization Profile (`armLegalTarget`) -/

/-- Verified AAPCS64 Arm64 scalar `Target` (`VecIsa.empty` / `VecTarget.empty`, `raBytes = 0`). -/
@[reducible] def armTarget : Target where
  Reg := Reg
  VReg := Empty
  Cond := ArmCond
  Directive := Directive
  gpr := armGpr
  vec := VecIsa.empty Reg ArmCond Directive
  frame := armFrame
  mach := armMach
  gprSpec := armGprSpec
  frameSpec := armFrameSpec
  vecSpec := VecTarget.empty armMach armCondReads armFrame.sp armScratch armFrameSpec.spOk

theorem armTarget_toIsa :
    armTarget.toIsa =
      { Reg := Reg, VReg := Empty, Cond := ArmCond, Directive := Directive,
        gpr := armGpr, vec := VecIsa.empty Reg ArmCond Directive, frame := armFrame } :=
  rfl

/-- AArch64 scalar legalization capability record (`LegalTarget.aarch64`, no vectors/floats). -/
def armLegalTarget : LegalTarget := LegalTarget.aarch64

theorem armLegalTarget_valid : armLegalTarget.valid = true := by
  decide

/-! ## 2. Parity Theorems (`armLegalTarget` ↔ `armTarget.toIsa`) & Kernel Checks -/

private theorem arm_w3264_imp (n : Nat) :
    [32, 64].contains n = true → [8, 16, 32, 64].contains n = true := by
  intro h
  simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl <;> simp

private theorem arm_w163264_imp (n : Nat) :
    [16, 32, 64].contains n = true → [8, 16, 32, 64].contains n = true := by
  intro h
  simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl <;> simp

/-- Parity theorem aligning `armLegalTarget` and `armTarget.toIsa` across scalar-only vector/float
rejection, `popcnt := false`, `[32, 64]`-restricted ops, `bswap`, and `[8, 16, 32, 64]` ops. -/
theorem armSupportsOp_parity (t : Ty) (f : Fmt) (n : Nat)
    (u1n : Tup (Arg (fun _ => Unit)) [.bits n])
    (u2n : Tup (Arg (fun _ => Unit)) [.bits n, .bits n])
    (uc3 : Tup (Arg (fun _ => Unit)) [.bits n, .bits n, .bool])
    (uf3 : Tup (Arg (fun _ => Unit)) [.bits n, .bits n, .bits n])
    (u164 : Tup (Arg (fun _ => Unit)) [i64])
    (u264 : Tup (Arg (fun _ => Unit)) [i64, i64])
    (u216 : Tup (Arg (fun _ => Unit)) [i16, i16])
    {sig rs : List Ty} (vcode : OpCode sig rs) (vargs : Tup (Arg (fun _ => Unit)) sig) :
    (armLegalTarget.keepsPacked t = false ∧
      armLegalTarget.supportsTy (.float f) = false ∧
      armTarget.toIsa.hasBank (.float f) = false ∧
      armTarget.toIsa.vec.supportsVecOp vcode vargs = false) ∧
    (armTarget.toIsa.supportsOp (.popcnt n) u1n = false) ∧
    (armTarget.toIsa.supportsOp (.clz n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.cls n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.rbit n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.ctz n) u1n = ([32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.fshl n) uf3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.fshr n) uf3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.addc n) uc3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.subb n) uc3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.umulw n) u2n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.smulw n) u2n = ([32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.bswap (.bits n)) u1n = ([16, 32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.add (.bits n)) u2n = ([8, 16, 32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.udiv0 n) u2n = ([8, 16, 32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.sdiv0 n) u2n = ([8, 16, 32, 64].contains n)) ∧
    (armLegalTarget.isLegalOp (.clz 64) false = true ∧
      armTarget.toIsa.supportsOp (.clz 64) u164 = true ∧
      armLegalTarget.isLegalOp (.udiv0 64) false = true ∧
      armTarget.toIsa.supportsOp (.udiv0 64) u264 = true ∧
      armLegalTarget.isLegalOp (.add i16) false = true ∧
      armTarget.toIsa.supportsOp (.add i16) u216 = true) := by
  have hkeep : armLegalTarget.keepsPacked t = false := by
    simp [LegalTarget.keepsPacked, armLegalTarget, LegalTarget.aarch64]
  have hfl : armLegalTarget.supportsTy (.float f) = false := by
    simp [LegalTarget.supportsTy, armLegalTarget, LegalTarget.aarch64]
  have hbankBits : armTarget.toIsa.hasBank (.bits n) = [8, 16, 32, 64].contains n := rfl
  have hbankBool : armTarget.toIsa.hasBank .bool = true := rfl
  refine ⟨⟨hkeep, hfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ([.bits n].all armTarget.toIsa.hasBank &&
        [.bits n].all armTarget.toIsa.hasBank && (false || false)) = false
    simp only [Bool.or_self, Bool.and_false]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · change ([.bits n].all armTarget.toIsa.hasBank &&
            [.bits n].all armTarget.toIsa.hasBank &&
            ([32, 64].contains n || false)) = [32, 64].contains n
        simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
        cases h : [32, 64].contains n
        · simp only [Bool.and_false]
        · simp only [arm_w3264_imp n h, Bool.and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ([.bits n, .bits n, .bits n].all armTarget.toIsa.hasBank &&
          [.bits n].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
    · change ([.bits n, .bits n, .bits n].all armTarget.toIsa.hasBank &&
          [.bits n].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
    · change ([.bits n, .bits n, .bool].all armTarget.toIsa.hasBank &&
          [.bits n, .bool].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, hbankBool, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
    · change ([.bits n, .bits n, .bool].all armTarget.toIsa.hasBank &&
          [.bits n, .bool].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, hbankBool, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
    · change ([.bits n, .bits n].all armTarget.toIsa.hasBank &&
          [.bits n, .bits n].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
    · change ([.bits n, .bits n].all armTarget.toIsa.hasBank &&
          [.bits n, .bits n].all armTarget.toIsa.hasBank &&
          ([32, 64].contains n || false)) = [32, 64].contains n
      simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
      cases h : [32, 64].contains n <;>
        simp only [Bool.and_false, arm_w3264_imp n, h, Bool.and_self]
  · change ([.bits n].all armTarget.toIsa.hasBank &&
        [.bits n].all armTarget.toIsa.hasBank &&
        ([16, 32, 64].contains n || false)) = [16, 32, 64].contains n
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
    cases h : [16, 32, 64].contains n <;>
      simp only [Bool.and_false, arm_w163264_imp n, h, Bool.and_self]
  · refine ⟨?_, ?_, ?_⟩ <;>
      · change ([.bits n, .bits n].all armTarget.toIsa.hasBank &&
            [.bits n].all armTarget.toIsa.hasBank &&
            ([8, 16, 32, 64].contains n || false)) = [8, 16, 32, 64].contains n
        simp only [List.all_cons, List.all_nil, Bool.and_true, hbankBits, Bool.or_false]
        cases h : [8, 16, 32, 64].contains n
        · simp only [Bool.and_false]
        · simp only [Bool.and_self]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Kernel `rfl` check suite aligning `armLegalTarget` and `armTarget.toIsa` (`popcnt = false`,
`[32, 64]` bit-counts/funnel/carry/wide-mul, `[16, 32, 64]` `bswap`, `[8, 16, 32, 64]` scalar). -/
theorem armSupportsOp_checks :
    armLegalTarget.valid = true ∧
    armLegalTarget.oracle.isPackedPair v4i32 = false ∧
    armLegalTarget.supportsTy (.float .s) = false ∧
    armLegalTarget.supportsTy (.float .d) = false ∧
    armTarget.toIsa.vec.supportsVecOp (.add v4i32) (.var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.popcnt 8) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.popcnt 16) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.popcnt 32) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.popcnt 64) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.clz 8) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.clz 16) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.clz 32) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.clz 64) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.cls 16) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.cls 32) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.rbit 16) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.rbit 64) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.ctz 8) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.ctz 32) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.fshl 16) (.var (), .var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.fshl 32) (.var (), .var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.fshr 16) (.var (), .var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.fshr 64) (.var (), .var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.addc 16) (.var (), .var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.addc 64) (.var (), .var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.subb 8) (.var (), .var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.subb 32) (.var (), .var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.umulw 16) (.var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.umulw 64) (.var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.smulw 16) (.var (), .var (), ()) = false ∧
    armGpr.supportsScalarOp (.smulw 64) (.var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.bswap i8) (.var (), ()) = false ∧
    armGpr.supportsScalarOp (.bswap i16) (.var (), ()) = true ∧
    armGpr.supportsScalarOp (.add i8) (.var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.udiv0 8) (.var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.sdiv0 64) (.var (), .var (), ()) = true ∧
    armGpr.supportsScalarOp (.fadd (.float .s)) (.var (), .var (), ()) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

end LeanQbe.T.Arm64
