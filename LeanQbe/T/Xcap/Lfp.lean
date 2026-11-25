module

/-!
# Generic Knaster–Tarski Least Closed Predicate (`Xcap.Lfp`)

Shared impredicative least-fixed-point combinator `Lfp.lfp` over predicate transformers
`(α → Prop) → (α → Prop)` with zero step-indexing:

* `Lfp.le`, `Lfp.mono`, `Lfp.Closed`, `Lfp.lfp`.
* `Lfp.lfp_le`, `Lfp.lfp_closed`, `Lfp.lfp_pre`, `Lfp.lfp_post`, `Lfp.lfp_fix`, `Lfp.lfp_mono`.
* `Lfp.lfp_of_wf` (well-founded induction along arbitrary `(ι, lt)`), and `Lfp.lfp_of_ranked`
  (`Nat`-ranked total-correctness introduction for loops and cyclic SCCs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Xcap.Lfp

universe u v

/-- Predicates over a state/configuration space `α`. -/
abbrev Pred (α : Type u) : Type u := α → Prop

/-- Pointwise implication ordering on `Pred α`. -/
@[expose] def le {α : Type u} (P Q : Pred α) : Prop :=
  ∀ x, P x → Q x

theorem le_refl {α : Type u} (P : Pred α) : le P P :=
  fun _ h => h

theorem le_trans {α : Type u} {P Q R : Pred α} (h₁ : le P Q) (h₂ : le Q R) : le P R :=
  fun x h => h₂ x (h₁ x h)

/-- Monotonicity of a predicate transformer `F : Pred α → Pred α` under `Lfp.le`. -/
@[expose] def mono {α : Type u} (F : Pred α → Pred α) : Prop :=
  ∀ ⦃P Q : Pred α⦄, le P Q → le (F P) (F Q)

/-- Pre-fixed point predicate: `P` is closed under one step of `F` (`F P ≤ P`). -/
@[expose] def Closed {α : Type u} (F : Pred α → Pred α) (P : Pred α) : Prop :=
  le (F P) P

/-- Impredicative Knaster–Tarski least closed predicate (`F P ≤ P → P x`). -/
@[expose] def lfp {α : Type u} (F : Pred α → Pred α) : Pred α :=
  fun x => ∀ P, Closed F P → P x

/-- `lfp F` lies below every `F`-closed predicate `P`. -/
theorem lfp_le {α : Type u} {F : Pred α → Pred α} {P : Pred α} (h : Closed F P) :
    le (lfp F) P :=
  fun _ hlfp => hlfp P h

/-- `lfp F` is itself `F`-closed whenever `F` is monotone (`F (lfp F) ≤ lfp F`). -/
theorem lfp_closed {α : Type u} {F : Pred α → Pred α} (hm : mono F) : Closed F (lfp F) :=
  fun x hx _P hP => hP x (hm (lfp_le hP) x hx)

/-- Pre-fixed point direction (`F (lfp F) ≤ lfp F`) for monotone `F`. -/
theorem lfp_pre {α : Type u} {F : Pred α → Pred α} (hm : mono F) :
    le (F (lfp F)) (lfp F) :=
  lfp_closed hm

/-- Post-fixed point direction (`lfp F ≤ F (lfp F)`) for monotone `F`. -/
theorem lfp_post {α : Type u} {F : Pred α → Pred α} (hm : mono F) :
    le (lfp F) (F (lfp F)) :=
  lfp_le (hm (lfp_closed hm))

/-- Fixed-point equation `lfp F = F (lfp F)` for monotone `F`. -/
theorem lfp_fix {α : Type u} {F : Pred α → Pred α} (hm : mono F) :
    lfp F = F (lfp F) := by
  funext x
  exact propext ⟨fun h => lfp_post hm x h, fun h => lfp_pre hm x h⟩

/-- Monotonicity of `lfp` in the transformer `F`. -/
theorem lfp_mono {α : Type u} {F₁ F₂ : Pred α → Pred α} (h : ∀ P x, F₁ P x → F₂ P x) :
    le (lfp F₁) (lfp F₂) :=
  fun _x h₁ P hP => h₁ P (fun y hy => hP y (h P y hy))

/-- Indexed supremum strictly below `i` along relation `lt`. -/
@[expose] def supBelow {α : Type u} {ι : Type v} (lt : ι → ι → Prop) (I : ι → Pred α)
    (i : ι) : Pred α :=
  fun x => ∃ j, lt j i ∧ I j x

/-- Well-founded `(ι, lt)` introduction into `lfp F`. -/
theorem lfp_of_wf {α : Type u} {ι : Type v} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    {F : Pred α → Pred α} (hm : mono F) (I : ι → Pred α)
    (hI : ∀ i, le (I i) (F (supBelow lt I i))) :
    ∀ i, le (I i) (lfp F) := by
  intro i
  induction i using (WellFounded.induction hwf) with
  | h i ih =>
    have hsup : le (supBelow lt I i) (lfp F) := by
      rintro x ⟨j, hlt, hj⟩
      exact ih j hlt x hj
    exact le_trans (hI i) (le_trans (hm hsup) (lfp_pre hm))

/-- `Nat`-ranked introduction into `lfp F` for loops and cyclic SCCs under total correctness. -/
theorem lfp_of_ranked {α : Type u} {F : Pred α → Pred α} (hm : mono F) (I : Nat → Pred α)
    (hI : ∀ n x, I n x → F (fun y => ∃ k, k < n ∧ I k y) x) :
    ∀ n x, I n x → lfp F x :=
  lfp_of_wf Nat.lt_wfRel.wf hm I hI

end LeanQbe.T.Xcap.Lfp
