module

public import LeanQbe.Examples.LitmusProgs
public import LeanQbe.Wf
public import LeanQbe.WPLemmas

/-!
# Litmus programs: well-formedness and source-level contracts (generic)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

theorem tracer_wf : Func.Wf tracer.body := by unfold tracer; wf_tac

theorem ifelse_wf : Func.Wf ifelse.body := by unfold ifelse; wf_tac

theorem sumto_wf : Func.Wf sumto.body := by unfold sumto; wf_tac

theorem evenodd_wf : Func.Wf evenodd.body := by unfold evenodd; wf_tac

theorem nested_wf : Func.Wf nested.body := by unfold nested; wf_tac

theorem swap_wf : Func.Wf swap.body := by unfold swap; wf_tac

/-- `1 + 2 + … + i` in 64-bit arithmetic. -/
def tri : Nat → Val
  | 0 => 0
  | i + 1 => tri i + BitVec.ofNat 64 (i + 1)

/-- The source-level contract of `sumto`, by induction over the loop counter (the join point is
universally quantified and constrained only by its closure hypothesis `hloop`). -/
theorem sumto_spec (Γ : Env) (n : Val) (hn : n.toNat < 2 ^ 32) (m : Mem 64) :
    Func.spec Γ sumto.body [n] m (fun r m' => r = [tri n.toNat] ∧ m' = m) (fun _ _ _ => False) := by
  simp only [Func.spec, sumto, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map,
    closed_param, forall_args_nil, List.nil_append, true_and, Option.some.injEq,
    exists_eq_left']
  intro loop hloop
  suffices h : ∀ k, k ≤ n.toNat → ∀ s, s + tri k = tri n.toNat → loop [BitVec.ofNat 64 k, s] m by
    simpa using h n.toNat (Nat.le_refl _) 0 (by simp)
  intro k
  induction k with
  | zero =>
    intro _ s hs
    refine hloop _ _ _ ⟨fun ht => absurd ht (by decide), fun _ => ⟨?_, rfl⟩⟩
    simpa [tri] using hs
  | succ k ih =>
    intro hk s hs
    have hk32 : k + 1 < 2 ^ 32 := by omega
    have ht : Truthy (BitVec.ofNat 64 (k + 1)) := by
      simp only [Truthy, lo32, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp [BitVec.toNat_ofNat] at this
      omega
    refine hloop _ _ _ ⟨fun _ => ?_, fun hnt => absurd ht hnt⟩
    have hsub : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsub]
    refine ih (by omega) _ ?_
    rw [← hs]; simp only [tri]; ac_rfl

end LeanQbe.Litmus
