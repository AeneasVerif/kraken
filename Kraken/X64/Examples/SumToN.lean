import Kraken.X64.Tactics
import Kraken.X64.Parser
import Kraken.Examples.SumToN

/-!
A vertical example connecting compiler-produced x86-64 assembly to a
register-level functional-correctness theorem.

`python3 Kraken/Examples/check_sum_to_n.py --arch x64` regenerates the assembly,
compares its encoded instructions with the checked-in artifact, and checks that
the assembler's instruction sizes match `compiledSumToNSizes` below.

The Lean theorem verifies the parsed, checked-in assembly. The regeneration
check records its compiler provenance; it is not a proof of Clang correctness.
-/

open Kraken.X64.Parser
open Kraken.Examples

/-- Clang's assembly output for `sum_to_n.c`, parsed at elaboration time. -/
def compiledSumToN : Program :=
  parseFile("Kraken/X64/Examples/sum_to_n.S")

/-- Encoded sizes from the assembled `.text` section, including zero-sized labels. -/
def compiledSumToNSizes : List Nat := [0, 2, 3, 2, 0, 3, 3, 2, 0, 1, 0]

/-- The actual relative layout reported by the assembler for `sum_to_n`. -/
@[reducible] def compiledSumToNLayout : Layout where
  start := 0
  size i := compiledSumToNSizes.getD i 0

def compiledSumToNExecutable : Executable :=
  (0, compiledSumToN.zip compiledSumToNSizes)

local instance : Layout := compiledSumToNLayout

/-- info: true -/
#guard_msgs in
#eval
  let exe := compiledSumToNExecutable
  exe.labels.label "sum_to_n" == 0 &&
    exe.labels.label ".LBB0_1" == 7 &&
    exe.labels.label ".LBB0_2" == 15 &&
    compiledSumToNSizes.length == compiledSumToN.length &&
    exe.locatedDirectives.length == compiledSumToN.length

macro "sum_to_n_step" : tactic =>
  `(tactic|
    (simp only [step1]
     dsimp [compiledSumToNExecutable, compiledSumToNLayout,
       compiledSumToNSizes, compiledSumToN, Layout.apply,
       List.mapIdx, List.mapIdx.go, Executable.step, Executable.fetch?,
       Executable.locatedDirectives, Executable.LocatedDirective.ofDirectives,
       List.find?]
     simp [Executable.LocatedDirective.stop, Executable.labels,
       Directive.interp, Instr.interp, Operation.interp, Operand.interp,
       RegOrMem.interp, Reg64s.get, Reg.base, Reg.offset, MachineData.set,
       MachineData.setReg, Reg64s.set, Reg64s.get64, Reg64s.set64,
       Width.type, Width.bits, BitVec.drop, BitVec.take,
       BitVec.extractLsb', StatusFlags.from_result, Effects.All]))

private theorem compiledSumToN_zero_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 0)
      (fun s' =>
        s'.2 = 2 ∧ s'.1.regs.rax = 0 ∧ s'.1.regs.rdi = s.regs.rdi) := by
  sum_to_n_step

private theorem compiledSumToN_test_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 2)
      (fun s' =>
        s'.2 = 5 ∧ s'.1.regs.rax = s.regs.rax ∧
        s'.1.regs.rdi = s.regs.rdi ∧
        s'.1.status.zf = (s'.1.regs.rdi == 0)) := by
  sum_to_n_step
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt64.eq_iff_toBitVec_eq,
    UInt64.toBitVec_ofNat]

private theorem compiledSumToN_je_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 5)
      (fun s' => s'.1 = s ∧ s'.2 = if s.status.zf then 15 else 7) := by
  sum_to_n_step
  cases h : s.status.zf
  · simp [h, CondCode.interp, Effects.All]
  · simp only [h, CondCode.interp, ↓reduceIte, Effects.All]
    exact ⟨trivial, by decide⟩

private theorem compiledSumToN_add_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 7)
      (fun s' =>
        s'.2 = 10 ∧ s'.1.regs.rax = s.regs.rdi + s.regs.rax ∧
        s'.1.regs.rdi = s.regs.rdi) := by
  sum_to_n_step

private theorem compiledSumToN_dec_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 10)
      (fun s' =>
        s'.2 = 13 ∧ s'.1.regs.rax = s.regs.rax ∧
        s'.1.regs.rdi = s.regs.rdi - 1 ∧
        s'.1.status.zf = (s'.1.regs.rdi == 0)) := by
  sum_to_n_step
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt64.eq_iff_toBitVec_eq,
    UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]

private theorem compiledSumToN_jne_step (s : MachineData) :
    step1 compiledSumToNExecutable (s, 13)
      (fun s' => s'.1 = s ∧ s'.2 = if !s.status.zf then 7 else 15) := by
  sum_to_n_step
  cases h : s.status.zf
  · simp only [h, CondCode.interp, Bool.not_false, ↓reduceIte, Effects.All]
    exact ⟨trivial, by decide⟩
  · simp [h, CondCode.interp, Effects.All]

private theorem compiledSumToN_loop
    (target : UInt64) (n : Nat) (s : MachineData)
    (hbound : n + 1 < 2 ^ 64)
    (hrdi : s.regs.rdi = UInt64.ofNat (n + 1))
    (hinv : sumToN (n + 1) + s.regs.rax = target) :
    Eventually (step1 compiledSumToNExecutable)
      (fun s' => s'.2 = 15 ∧ s'.1.regs.rax = target)
      (s, 7) := by
  induction n generalizing s with
  | zero =>
      refine .step (s, 7) _ (compiledSumToN_add_step s) ?_
      rintro ⟨s₁, _⟩ ⟨rfl, hrax₁, hrdi₁⟩
      refine .step (s₁, 10) _ (compiledSumToN_dec_step s₁) ?_
      rintro ⟨s₂, _⟩ ⟨rfl, hrax₂, hrdi₂, hzf₂⟩
      have hrdi₂_zero : s₂.regs.rdi = 0 := by
        rw [hrdi₂, hrdi₁, hrdi]
        decide
      have hzf₂_true : s₂.status.zf = true := by
        simpa [hrdi₂_zero] using hzf₂
      refine .step (s₂, 13) _ (compiledSumToN_jne_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hzf₂_true] at hpc₃
      subst pc₃
      apply Eventually.done
      constructor
      · rfl
      · rw [hrax₂, hrax₁, hrdi]
        simpa [sumToN] using hinv
  | succ n ih =>
      refine .step (s, 7) _ (compiledSumToN_add_step s) ?_
      rintro ⟨s₁, _⟩ ⟨rfl, hrax₁, hrdi₁⟩
      refine .step (s₁, 10) _ (compiledSumToN_dec_step s₁) ?_
      rintro ⟨s₂, _⟩ ⟨rfl, hrax₂, hrdi₂, hzf₂⟩
      have hbound' : n + 1 < 2 ^ 64 := by omega
      have hrdi₂' : s₂.regs.rdi = UInt64.ofNat (n + 1) := by
        rw [hrdi₂, hrdi₁, hrdi]
        simpa [Nat.add_assoc] using uint64_ofNat_succ_sub_one (n + 1) hbound
      have hzf₂_false : s₂.status.zf = false := by
        rw [hzf₂, hrdi₂']
        exact uint64_ofNat_succ_beq_zero n hbound'
      have hinv' : sumToN (n + 1) + s₂.regs.rax = target := by
        calc
          sumToN (n + 1) + s₂.regs.rax =
              sumToN (n + 1) + (UInt64.ofNat (n + 2) + s.regs.rax) := by
                rw [hrax₂, hrax₁, hrdi]
          _ = (UInt64.ofNat (n + 2) + sumToN (n + 1)) + s.regs.rax := by
                ac_rfl
          _ = sumToN (n + 2) + s.regs.rax := by rfl
          _ = target := by simpa [Nat.add_assoc] using hinv
      refine .step (s₂, 13) _ (compiledSumToN_jne_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hzf₂_false] at hpc₃
      subst pc₃
      exact ih s₂ hbound' hrdi₂' hinv'

private theorem compiledSumToN_returnAddress :
    compiledSumToNExecutable.labels.label ".LBB0_2" = 15 := by
  decide

private theorem compiledSumToN_entryAddress :
    compiledSumToNExecutable.labels.label "sum_to_n" = 0 := by
  decide

/--
The compiled function receives `n` in `%rdi` and has the specified result in
`%rax` when it reaches its return block.
-/
theorem compiledSumToN_correct (s₀ : MachineData) :
    Eventually (step1 compiledSumToNExecutable)
      (fun s =>
        s.2 = compiledSumToNExecutable.labels.label ".LBB0_2" ∧
        s.1.regs.rax = sumToN s₀.regs.rdi.toNat)
      (s₀, compiledSumToNExecutable.labels.label "sum_to_n") := by
  rw [compiledSumToN_returnAddress, compiledSumToN_entryAddress]
  refine .step (s₀, 0) _ (compiledSumToN_zero_step s₀) ?_
  rintro ⟨s₁, pc₁⟩ ⟨hpc₁, hrax₁, hrdi₁⟩
  change pc₁ = 2 at hpc₁
  subst pc₁
  refine .step (s₁, 2) _ (compiledSumToN_test_step s₁) ?_
  rintro ⟨s₂, pc₂⟩ ⟨hpc₂, hrax₂, hrdi₂, hzf₂⟩
  change pc₂ = 5 at hpc₂
  subst pc₂
  cases hn : s₀.regs.rdi.toNat with
  | zero =>
      have hrdi₀ : s₀.regs.rdi = 0 := by
        rw [← UInt64.ofNat_toNat (x := s₀.regs.rdi), hn]
        rfl
      have hzf₂_true : s₂.status.zf = true := by
        rw [hzf₂, hrdi₂, hrdi₁, hrdi₀]
        rfl
      refine .step (s₂, 5) _ (compiledSumToN_je_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hzf₂_true] at hpc₃
      subst pc₃
      apply Eventually.done
      constructor
      · rfl
      · rw [hrax₂, hrax₁]
        simp [sumToN]
  | succ n =>
      have hbound : n + 1 < 2 ^ 64 := by
        simpa [hn] using s₀.regs.rdi.toNat_lt
      have hrdi₀ : s₀.regs.rdi = UInt64.ofNat (n + 1) := by
        rw [← UInt64.ofNat_toNat (x := s₀.regs.rdi), hn]
      have hrdi₂' : s₂.regs.rdi = UInt64.ofNat (n + 1) := by
        rw [hrdi₂, hrdi₁, hrdi₀]
      have hzf₂_false : s₂.status.zf = false := by
        rw [hzf₂, hrdi₂']
        exact uint64_ofNat_succ_beq_zero n hbound
      have hinv : sumToN (n + 1) + s₂.regs.rax = sumToN (n + 1) := by
        rw [hrax₂, hrax₁]
        simp
      refine .step (s₂, 5) _ (compiledSumToN_je_step s₂) ?_
      rintro ⟨s₃, pc₃⟩ ⟨hs₃, hpc₃⟩
      change s₃ = s₂ at hs₃
      subst s₃
      change pc₃ = _ at hpc₃
      simp [hzf₂_false] at hpc₃
      subst pc₃
      exact compiledSumToN_loop (sumToN (n + 1)) n s₂
        hbound hrdi₂' hinv
