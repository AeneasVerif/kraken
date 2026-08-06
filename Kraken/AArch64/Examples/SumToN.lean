import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.Examples.SumToN

/-!
A compiler-produced AArch64 counterpart to the x86-64 `sum_to_n` proof.

The theorem verifies the parsed, checked-in assembly. Regeneration establishes
artifact provenance, not compiler correctness.

Run `python3 Kraken/Examples/check_sum_to_n.py --arch aarch64` to regenerate
the assembly and check its encoded instructions and Lean layout.
-/

open Kraken.AArch64.Parser
open Kraken.Examples

def compiledSumToNAArch64 : Program :=
  parseFileAArch64("Kraken/AArch64/Examples/sum_to_n.S")

def compiledSumToNAArch64Sizes : List Nat :=
  [0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 0]

@[reducible] def compiledSumToNAArch64Layout : Layout where
  start := 0
  size i := compiledSumToNAArch64Sizes.getD i 0

def compiledSumToNAArch64Executable : Executable :=
  (0, compiledSumToNAArch64.zip compiledSumToNAArch64Sizes)

local instance : Layout := compiledSumToNAArch64Layout

/-- info: true -/
#guard_msgs in
#eval
  let exe := compiledSumToNAArch64Executable
  exe.labels.label "sum_to_n" == 0 &&
    exe.labels.label ".LBB0_1" == 8 &&
    exe.labels.label ".LBB0_2" == 20 &&
    exe.labels.label ".Lfunc_end0" == 28 &&
    compiledSumToNAArch64Sizes.length == compiledSumToNAArch64.length &&
    exe.locatedDirectives.length == compiledSumToNAArch64.length

macro "sum_to_n_aarch64_step" : tactic =>
  `(tactic|
    (simp only [step1]
     dsimp [compiledSumToNAArch64Executable, compiledSumToNAArch64Layout,
       compiledSumToNAArch64Sizes, compiledSumToNAArch64, Layout.apply,
       List.mapIdx, List.mapIdx.go, Executable.step, Executable.fetch?,
       Executable.locatedDirectives, Executable.LocatedDirective.ofDirectives,
       List.find?]
     simp [Executable.LocatedDirective.stop, Executable.labels,
       Directive.interp, Instr.interp, Operation.interp, ShiftRegExpr.interp,
       ExtOrImmReg.interp, ConstExpr.interp, ConstExpr.evalBranchTarget,
       MachineData.setRegOrSp, MachineData.setRegOrZr,
       Reg64s.getRegOrSp, Reg64s.getRegOrZr, Reg64s.getRegOrSp64,
       Reg64s.getRegOrZr64, Reg64s.getXReg, RegOrSp.base, RegOrZr.base,
       Reg64s.setRegOrSp, Reg64s.setRegOrZr, Reg64s.setRegOrSp64,
       Reg64s.setRegOrZr64, Reg64s.setXReg, Width.type, Width.bits,
       BitVec.drop, BitVec.take, BitVec.extractLsb', BitVec.shiftLeft_zero,
       StatusFlags.from_result, StatusFlags.subs, Effects.All]))

private theorem compiledSumToNAArch64_zero_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 0)
      (fun s' =>
        s'.2 = 4 ∧ s'.1.regs.X8 = 0 ∧ s'.1.regs.X0 = s.regs.X0) := by
  sum_to_n_aarch64_step

private theorem compiledSumToNAArch64_cbz_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 4)
      (fun s' =>
        s'.1 = s ∧ s'.2 = if s.regs.X0 == 0 then 20 else 8) := by
  sum_to_n_aarch64_step
  by_cases h : s.regs.X0 = 0
  · simp [h, Effects.All]
    decide
  · have hb : s.regs.X0.toBitVec ≠ 0#64 := by
      intro hb
      apply h
      exact UInt64.toBitVec_inj.mp (by simpa using hb)
    simp [h, hb, Effects.All]

private theorem compiledSumToNAArch64_add_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 8)
      (fun s' =>
        s'.2 = 12 ∧ s'.1.regs.X8 = s.regs.X8 + s.regs.X0 ∧
        s'.1.regs.X0 = s.regs.X0) := by
  sum_to_n_aarch64_step
  apply UInt64.toBitVec_inj.mp
  change s.regs.X8.toBitVec + (s.regs.X0.toBitVec <<< 0) =
    s.regs.X8.toBitVec + s.regs.X0.toBitVec
  rw [BitVec.shiftLeft_zero]

private theorem compiledSumToNAArch64_subs_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 12)
      (fun s' =>
        s'.2 = 16 ∧ s'.1.regs.X8 = s.regs.X8 ∧
        s'.1.regs.X0 = s.regs.X0 - 1 ∧
        s'.1.status.z = (s'.1.regs.X0 == 0)) := by
  sum_to_n_aarch64_step
  constructor
  · apply UInt64.toBitVec_inj.mp
    rfl
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, UInt64.eq_iff_toBitVec_eq]
    rfl

private theorem compiledSumToNAArch64_bne_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 16)
      (fun s' =>
        s'.1 = s ∧ s'.2 = if !s.status.z then 8 else 20) := by
  sum_to_n_aarch64_step
  cases h : s.status.z
  · simp [h, CondCode.interp, Effects.All]
    decide
  · simp [h, CondCode.interp, Effects.All]

private theorem compiledSumToNAArch64_result_step (s : MachineData) :
    step1 compiledSumToNAArch64Executable (s, 20)
      (fun s' =>
        s'.2 = 24 ∧ s'.1.regs.X0 = s.regs.X8 ∧
        s'.1.regs.X8 = s.regs.X8) := by
  sum_to_n_aarch64_step
  apply UInt64.toBitVec_inj.mp
  change 0#64 ||| (s.regs.X8.toBitVec <<< 0) = s.regs.X8.toBitVec
  rw [BitVec.shiftLeft_zero, BitVec.zero_or]

private theorem compiledSumToNAArch64_finish
    (target : UInt64) (s : MachineData) (hresult : s.regs.X8 = target) :
    Eventually (step1 compiledSumToNAArch64Executable)
      (fun s' => s'.2 = 24 ∧ s'.1.regs.X0 = target)
      (s, 20) := by
  refine .step (s, 20) _ (compiledSumToNAArch64_result_step s) ?_
  rintro ⟨s', pc'⟩ ⟨hpc, hx0, _⟩
  change pc' = 24 at hpc
  subst pc'
  apply Eventually.done
  exact ⟨rfl, hx0.trans hresult⟩

private theorem compiledSumToNAArch64_loop
    (target : UInt64) (n : Nat) (s : MachineData)
    (hbound : n + 1 < 2 ^ 64)
    (hx0 : s.regs.X0 = UInt64.ofNat (n + 1))
    (hinv : sumToN (n + 1) + s.regs.X8 = target) :
    Eventually (step1 compiledSumToNAArch64Executable)
      (fun s' => s'.2 = 24 ∧ s'.1.regs.X0 = target)
      (s, 8) := by
  induction n generalizing s with
  | zero =>
      refine .step (s, 8) _ (compiledSumToNAArch64_add_step s) ?_
      rintro ⟨s₁, _⟩ ⟨rfl, hx8₁, hx0₁⟩
      refine .step (s₁, 12) _ (compiledSumToNAArch64_subs_step s₁) ?_
      rintro ⟨s₂, _⟩ ⟨rfl, hx8₂, hx0₂, hz₂⟩
      have hx0₂_zero : s₂.regs.X0 = 0 := by
        rw [hx0₂, hx0₁, hx0]
        decide
      have hz₂_true : s₂.status.z = true := by
        simpa [hx0₂_zero] using hz₂
      have hx8₂_target : s₂.regs.X8 = target := by
        rw [hx8₂, hx8₁, hx0]
        simpa [sumToN, UInt64.add_comm] using hinv
      refine .step (s₂, 16) _ (compiledSumToNAArch64_bne_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hz₂_true] at hpc₃
      subst pc₃
      exact compiledSumToNAArch64_finish target s₂ hx8₂_target
  | succ n ih =>
      refine .step (s, 8) _ (compiledSumToNAArch64_add_step s) ?_
      rintro ⟨s₁, _⟩ ⟨rfl, hx8₁, hx0₁⟩
      refine .step (s₁, 12) _ (compiledSumToNAArch64_subs_step s₁) ?_
      rintro ⟨s₂, _⟩ ⟨rfl, hx8₂, hx0₂, hz₂⟩
      have hbound' : n + 1 < 2 ^ 64 := by omega
      have hx0₂' : s₂.regs.X0 = UInt64.ofNat (n + 1) := by
        rw [hx0₂, hx0₁, hx0]
        simpa [Nat.add_assoc] using uint64_ofNat_succ_sub_one (n + 1) hbound
      have hz₂_false : s₂.status.z = false := by
        rw [hz₂, hx0₂']
        exact uint64_ofNat_succ_beq_zero n hbound'
      have hinv' : sumToN (n + 1) + s₂.regs.X8 = target := by
        calc
          sumToN (n + 1) + s₂.regs.X8 =
              sumToN (n + 1) + (s.regs.X8 + UInt64.ofNat (n + 2)) := by
                rw [hx8₂, hx8₁, hx0]
          _ = (UInt64.ofNat (n + 2) + sumToN (n + 1)) + s.regs.X8 := by
                ac_rfl
          _ = sumToN (n + 2) + s.regs.X8 := by rfl
          _ = target := by simpa [Nat.add_assoc] using hinv
      refine .step (s₂, 16) _ (compiledSumToNAArch64_bne_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hz₂_false] at hpc₃
      subst pc₃
      exact ih s₂ hbound' hx0₂' hinv'

private theorem compiledSumToNAArch64_entryAddress :
    compiledSumToNAArch64Executable.labels.label "sum_to_n" = 0 := by
  decide

private theorem compiledSumToNAArch64_returnAddress :
    compiledSumToNAArch64Executable.labels.label ".Lfunc_end0" - 4 = 24 := by
  decide

/--
The compiled function receives `n` in `x0` and has the unsigned sum in `x0`
when execution reaches its `ret` instruction.
-/
theorem compiledSumToNAArch64_correct (s₀ : MachineData) :
    Eventually (step1 compiledSumToNAArch64Executable)
      (fun s =>
        s.2 = compiledSumToNAArch64Executable.labels.label ".Lfunc_end0" - 4 ∧
        s.1.regs.X0 = sumToN s₀.regs.X0.toNat)
      (s₀, compiledSumToNAArch64Executable.labels.label "sum_to_n") := by
  rw [compiledSumToNAArch64_returnAddress, compiledSumToNAArch64_entryAddress]
  refine .step (s₀, 0) _ (compiledSumToNAArch64_zero_step s₀) ?_
  rintro ⟨s₁, pc₁⟩ ⟨hpc₁, hx8₁, hx0₁⟩
  change pc₁ = 4 at hpc₁
  subst pc₁
  cases hn : s₀.regs.X0.toNat with
  | zero =>
      have hx0₀ : s₀.regs.X0 = 0 := by
        rw [← UInt64.ofNat_toNat (x := s₀.regs.X0), hn]
        rfl
      refine .step (s₁, 4) _ (compiledSumToNAArch64_cbz_step s₁) ?_
      rintro ⟨s₂, pc₂⟩ ⟨hs₂, hpc₂⟩
      change s₂ = s₁ at hs₂
      subst s₂
      change pc₂ = _ at hpc₂
      have hx0₁_zero : s₁.regs.X0 = 0 := by
        rw [hx0₁, hx0₀]
      simp [hx0₁_zero] at hpc₂
      subst pc₂
      exact compiledSumToNAArch64_finish (sumToN 0) s₁ (by
        simpa [sumToN] using hx8₁)
  | succ n =>
      have hbound : n + 1 < 2 ^ 64 := by
        simpa [hn] using s₀.regs.X0.toNat_lt
      have hx0₀ : s₀.regs.X0 = UInt64.ofNat (n + 1) := by
        rw [← UInt64.ofNat_toNat (x := s₀.regs.X0), hn]
      have hx0₁' : s₁.regs.X0 = UInt64.ofNat (n + 1) := by
        rw [hx0₁, hx0₀]
      have hinv : sumToN (n + 1) + s₁.regs.X8 = sumToN (n + 1) := by
        rw [hx8₁]
        simp
      refine .step (s₁, 4) _ (compiledSumToNAArch64_cbz_step s₁) ?_
      rintro ⟨s₂, pc₂⟩ ⟨hs₂, hpc₂⟩
      change s₂ = s₁ at hs₂
      subst s₂
      change pc₂ = _ at hpc₂
      have hx0_ne : s₁.regs.X0 ≠ 0 := by
        rw [hx0₁']
        exact beq_eq_false_iff_ne.mp (uint64_ofNat_succ_beq_zero n hbound)
      simp [hx0_ne] at hpc₂
      subst pc₂
      exact compiledSumToNAArch64_loop (sumToN (n + 1)) n s₁
        hbound hx0₁' hinv
