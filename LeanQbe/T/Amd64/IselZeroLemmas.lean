module

public import LeanQbe.T.Amd64.Isel
public import LeanQbe.T.Amd64.IselLemmas1

/-!
# Typed x64 Scalar Zero-Idiom Proofs (`Amd64.IselZeroLemmas`)

Label-cleanliness and `x64Mach.FallsTo` specification proofs for `x64MoviDeadFlags`
(`xorl %ed, %ed` with `maskAll` when `c == 0#64`, `moviI` with `maskNone` otherwise).
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T

public section

theorem x64Gpr_moviDeadFlags_noLab (rd : Reg64) (c : BitVec 64) :
    ∀ l, Kraken.Directive.label l ∉ (x64MoviDeadFlags rd c).1 := by
  dsimp only [x64MoviDeadFlags]
  split <;> exact emitClean_noLab _

theorem fallsTo_xorl_zero (s : MachineData) (r : Reg64) :
    Directive.FallsTo (ins32 (.xor (.reg (d r)) (.reg (d r)))) s (fun s' =>
      ∃ status, s' = { s with regs := s.regs.set64 r 0#64, status }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Effects.All]
  intro af
  have hzero : ((s.regs.get64 r).setWidth 32 ^^^ (s.regs.get64 r).setWidth 32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
  rw [hzero, BitVec.zeroExtend_eq_setWidth]
  exact hk _ ⟨_, rfl⟩

theorem x64Gpr_moviDeadFlags_spec {h : Host} {k : Nat} {rd : Reg64} {c0 : BitVec 64}
    {s : MachineData} {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k (x64MoviDeadFlags rd c0).1 (rd :: x64Scratch) []
      (x64MoviDeadFlags rd c0).2 s
      (fun s' => s'.regs.get64 rd = c0 ∧ s'.dmem = s.dmem) post := by
  dsimp only [x64MoviDeadFlags]
  split
  · rename_i hc
    have hc0 : c0 = 0#64 := beq_iff_eq.mp hc
    subst hc0
    refine dir_to_x64FallsTo (fallsTo_xorl_zero s rd) ?_
    rintro s' ⟨st, rfl⟩
    refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩,
      x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
    intro r hr
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
  · exact x64Gpr_movi_spec

end

end LeanQbe.T.Amd64
