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
theorem inc_wf : Func.Wf inc.body := by unfold inc; wf_tac
theorem callinc_wf : Func.Wf callinc.body := by unfold callinc; wf_tac
theorem check_wf : Func.Wf check.body := by unfold check; wf_tac
theorem twice_wf : Func.Wf twice.body := by unfold twice; wf_tac
theorem spill10_wf : Func.Wf spill10.body := by unfold spill10; wf_tac
theorem sumcall_wf : Func.Wf sumcall.body := by unfold sumcall; wf_tac

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

/-- Source contract of `inc`. -/
def incContract : Spec := fun args m Q _ =>
  ∃ a, args = [a] ∧ Q [a + 1] m

theorem inc_spec (Γ : Env) :
    ∀ args m Q X, incContract args m Q X → Func.spec Γ inc.body args m Q X := by
  rintro _ m Q X ⟨a, rfl, hQ⟩
  simp only [Func.spec, inc, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map, true_and,
    Option.some.injEq, exists_eq_left']
  exact hQ

/-- Source contract of `callinc`. -/
def callincContract : Spec := fun args m Q _ =>
  ∃ a b, args = [a, b] ∧ Q [a + 1 + b] m

theorem callinc_spec (Γ : Env) (hinc : Γ "inc" = incContract) :
    ∀ args m Q X, callincContract args m Q X → Func.spec Γ callinc.body args m Q X := by
  rintro _ m Q X ⟨a, b, rfl, hQ⟩
  simp only [Func.spec, callinc, wp, Arg.val, List.map, true_and]
  refine ⟨fun rs m' => rs = [a + 1] ∧ m' = m, fun _ _ _ => False, ?_, ?_, fun _ _ _ h => h.elim⟩
  · rw [hinc]; exact ⟨a, rfl, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, a + 1 + b, rfl, rfl, hQ⟩

/-- Source contract of `check`. -/
def checkContract : Spec := fun args m Q X =>
  ∃ a, args = [a] ∧ (Truthy a → Q [a] m) ∧ (¬Truthy a → X "fail" [a] m)

theorem check_spec (Γ : Env) :
    ∀ args m Q X, checkContract args m Q X → Func.spec Γ check.body args m Q X := by
  rintro _ m Q X ⟨a, rfl, hQ, hX⟩
  simp only [Func.spec, check, wp, Arg.val, List.map, true_and]
  exact ⟨hQ, hX⟩

/-- Source contract of `twice`: returns `[a + b]` if both are truthy, else exits to `"fail"`. -/
def twiceContract : Spec := fun args m Q X =>
  ∃ a b, args = [a, b] ∧
    (Truthy a → Truthy b → Q [a + b] m) ∧
    (¬Truthy a → X "fail" [a] m) ∧
    (Truthy a → ¬Truthy b → X "fail" [b] m)

theorem twice_spec (Γ : Env) (hcheck : Γ "check" = checkContract) :
    ∀ args m Q X, twiceContract args m Q X → Func.spec Γ twice.body args m Q X := by
  rintro _ m Q X ⟨a, b, rfl, hQ, hXa, hXb⟩
  simp only [Func.spec, twice, wp, Arg.val, List.map, true_and]
  refine ⟨fun rs m' => Truthy a ∧ rs = [a] ∧ m' = m,
    fun g xs m' => ¬Truthy a ∧ g = "fail" ∧ xs = [a] ∧ m' = m, ?_, ?_, ?_⟩
  · rw [hcheck]; exact ⟨a, rfl, fun ha => ⟨ha, rfl, rfl⟩, fun hna => ⟨hna, rfl, rfl, rfl⟩⟩
  · rintro _ m1 ⟨ha, rfl, rfl⟩
    refine ⟨rfl, fun rs m' => Truthy b ∧ rs = [b] ∧ m' = m1,
      fun g xs m' => ¬Truthy b ∧ g = "fail" ∧ xs = [b] ∧ m' = m1, ?_, ?_, ?_⟩
    · rw [hcheck]; exact ⟨b, rfl, fun hb => ⟨hb, rfl, rfl⟩, fun hnb => ⟨hnb, rfl, rfl, rfl⟩⟩
    · rintro _ _ ⟨hb, rfl, rfl⟩
      exact ⟨rfl, a + b, rfl, rfl, hQ ha hb⟩
    · rintro _ _ _ ⟨hnb, rfl, rfl, rfl⟩
      exact hXb ha hnb
  · rintro _ _ _ ⟨hna, rfl, rfl, rfl⟩
    exact hXa hna

/-- Expected value of `spill10(a, b)`. -/
def spill10Val (a b : Val) : Val :=
  (a + 1) ^^^ (a + 2) ^^^ (a + 3) ^^^ (a + 4) ^^^ (a + 5) ^^^
  (a + 6) ^^^ (a + 7) ^^^ (a + 8) ^^^ (a + 9) ^^^ (a + 10) ^^^ b

theorem spill10_spec (Γ : Env) (a b : Val) (m : Mem 64) :
    Func.spec Γ spill10.body [a, b] m (fun r m' => r = [spill10Val a b] ∧ m' = m)
      (fun _ _ _ => False) := by
  simp [Func.spec, spill10, spill10Val, wp, Op.wp, Op.eval, BinOp.eval, Arg.val]

end LeanQbe.Litmus
