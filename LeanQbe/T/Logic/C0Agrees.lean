module

public import LeanQbe.T.Logic.C0Step

/-!
# Compositional `AgreesExcept` Algebra and `SafetySlice` Combinators

Proof-acceleration combinators for multi-field, multi-array C0 state structures:

1. **Compositional `AgreesExcept` algebra.** Equivalence laws (`agreesExcept_refl`,
   `agreesExcept_symm`, `agreesExcept_trans`), mask widening (`agreesExcept_mono`,
   `AgreesExcept.trans_mono`, `AgreesExcept.comp_left`/`comp_right`), record-update chaining,
   field/sub-struct/predicate projection preservation, and unmasked list-slice preservation.
2. **Array prefix/slice agreement.** `PrefixAgrees`, `SliceAgrees`, and `OutsideSliceAgrees` with
   `List.set` and `getD` lemmas for loops mutating one slice of an array while preserving another.
3. **Framed loop and join rules.** `wp_loop_agreesExcept` (wrapping `C0Step.wp_loop_inv`),
   `wp_loop_agreesExcept_mem`, state-measure variants `wp_loop_agreesExcept_state{,_mem}`,
   `wp_loop_break_agreesExcept`, and `wp_join_agreesExcept{,_mem}` so multi-field struct loop
   invariants never enumerate unchanged fields manually.
4. **Safety-only slice combinator (`PreservesCoreSlice`, `SafetySlice`, `wp_safety_slice`).**
   Reusable framing wrapper for C0 functions and loops that only mutate heuristic, phase, WalkSAT,
   queue/heap, or witness-reconstruction scratch buffers while leaving the core soundness state
   untouched or read-only, transporting arbitrary predicates `Inv (coreProj s)` across calls,
   loops, and expressions in one step.
5. **Scoped simp/grind lemmas (`LeanQbe.T.C0Agrees`).** Strictly `scoped` attributes (`[simp]`,
   `[grind =]`, `[grind →]`) with zero global `@[grind]` pollution.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std.ExtHashMap

/-! ## 1. Compositional `AgreesExcept` algebra -/

theorem agreesExcept_iff {σ : Type} (mask : σ → σ) (s s' : σ) :
    AgreesExcept mask s s' ↔ mask s' = mask s :=
  Iff.rfl

theorem agreesExcept_refl {σ : Type} (mask : σ → σ) (s : σ) : AgreesExcept mask s s :=
  AgreesExcept.refl mask s

theorem agreesExcept_of_eq {σ : Type} (mask : σ → σ) {s s' : σ} (h : s' = s) :
    AgreesExcept mask s s' :=
  h ▸ AgreesExcept.refl mask s

theorem agreesExcept_id {σ : Type} (s s' : σ) : AgreesExcept id s s' ↔ s' = s :=
  Iff.rfl

theorem agreesExcept_const {σ : Type} (c s s' : σ) : AgreesExcept (fun _ => c) s s' :=
  rfl

namespace AgreesExcept

variable {σ : Type} {mask mask₁ mask₂ : σ → σ} {s s' s'' : σ}

/-- Symmetry of `AgreesExcept`. -/
theorem symm (h : AgreesExcept mask s s') : AgreesExcept mask s' s :=
  Eq.symm h

/-- Construct `AgreesExcept` from a state equality. -/
theorem of_eq (mask : σ → σ) (h : s' = s) : AgreesExcept mask s s' :=
  h ▸ rfl

/-- Mask widening: if `mask₂` overwrites at least every field overwritten by `mask₁`
(so `mask₂ (mask₁ t) = mask₂ t`, closing by `rfl` on record masks), agreement modulo `mask₁`
implies agreement modulo `mask₂`. -/
theorem mono (h : AgreesExcept mask₁ s s')
    (hsub : ∀ t, mask₂ (mask₁ t) = mask₂ t := by intro; rfl) :
    AgreesExcept mask₂ s s' := by
  change mask₂ s' = mask₂ s
  rw [← hsub s', ← hsub s, h]

/-- Mask widening via an explicit factoring function `mask₂ = f ∘ mask₁`. -/
theorem mono_of_factor (h : AgreesExcept mask₁ s s') (f : σ → σ)
    (hfac : ∀ t, mask₂ t = f (mask₁ t)) : AgreesExcept mask₂ s s' := by
  change mask₂ s' = mask₂ s
  rw [hfac s', hfac s, h]

/-- Composing an extra mask on the outside widens agreement unconditionally. -/
theorem comp_left (mask₂ : σ → σ) (h : AgreesExcept mask₁ s s') :
    AgreesExcept (fun t => mask₂ (mask₁ t)) s s' :=
  congrArg mask₂ h

/-- Composing a commuting mask on the inside widens agreement (`hcomm` closes by `rfl` for
disjoint record masks). -/
theorem comp_right (mask₁ : σ → σ) (h : AgreesExcept mask₂ s s')
    (hcomm : ∀ t, mask₂ (mask₁ t) = mask₁ (mask₂ t) := by intro; rfl) :
    AgreesExcept (fun t => mask₂ (mask₁ t)) s s' := by
  change mask₂ (mask₁ s') = mask₂ (mask₁ s)
  rw [hcomm s', hcomm s, h]

/-- Compose two agreements with smaller masks into one agreement with a wider mask. -/
theorem trans_mono (h₁ : AgreesExcept mask₁ s s') (h₂ : AgreesExcept mask₂ s' s'')
    (hsub₁ : ∀ t, mask (mask₁ t) = mask t := by intro; rfl)
    (hsub₂ : ∀ t, mask (mask₂ t) = mask t := by intro; rfl) :
    AgreesExcept mask s s'' :=
  (h₁.mono hsub₁).trans (h₂.mono hsub₂)

/-- Compose two agreements into their composed mask (for commuting masks). -/
theorem trans_comp (h₁ : AgreesExcept mask₁ s s') (h₂ : AgreesExcept mask₂ s' s'')
    (hcomm : ∀ t, mask₂ (mask₁ t) = mask₁ (mask₂ t) := by intro; rfl) :
    AgreesExcept (fun t => mask₂ (mask₁ t)) s s'' :=
  (h₁.comp_left mask₂).trans (h₂.comp_right mask₁ hcomm)

/-- Single masked update from `s` agrees with `s` modulo `mask`. -/
theorem update_self (mask : σ → σ) (s : σ) (upd : σ → σ)
    (hu : ∀ t, mask (upd t) = mask t := by intro; rfl) :
    AgreesExcept mask s (upd s) :=
  hu s

/-- A masked update on the left state can be stripped. -/
theorem update_left {upd : σ → σ} (h : AgreesExcept mask (upd s) s')
    (hu : ∀ t, mask (upd t) = mask t := by intro; rfl) :
    AgreesExcept mask s s' :=
  Eq.trans h (hu s)

/-- Masked updates on both sides preserve agreement. -/
theorem update_both (h : AgreesExcept mask s s') (upd₁ upd₂ : σ → σ)
    (hu₁ : ∀ t, mask (upd₁ t) = mask t := by intro; rfl)
    (hu₂ : ∀ t, mask (upd₂ t) = mask t := by intro; rfl) :
    AgreesExcept mask (upd₁ s) (upd₂ s') := by
  change mask (upd₂ s') = mask (upd₁ s)
  rw [hu₂ s', hu₁ s, h]

/-- An idempotent mask agrees with `s` on `mask s`. -/
theorem idem (mask : σ → σ) (s : σ) (hi : ∀ t, mask (mask t) = mask t := by intro; rfl) :
    AgreesExcept mask s (mask s) :=
  hi s

/-- Project `AgreesExcept` onto a sub-structure `τ` with sub-mask `maskSub`. -/
theorem proj {τ : Type} (h : AgreesExcept mask s s') (p : σ → τ) (maskSub : τ → τ)
    (hp : ∀ t, maskSub (p (mask t)) = maskSub (p t) := by intro; rfl) :
    AgreesExcept maskSub (p s) (p s') := by
  change maskSub (p s') = maskSub (p s)
  rw [← hp s', ← hp s, h]

/-- Any predicate invariant under `mask` is preserved across `AgreesExcept`. -/
theorem preserves (h : AgreesExcept mask s s') (P : σ → Prop)
    (hP : ∀ t, P (mask t) ↔ P t) : P s' ↔ P s := by
  rw [← hP s', ← hP s, h]

/-- Transport a mask-invariant predicate forward along `AgreesExcept`. -/
theorem transport (h : AgreesExcept mask s s') (P : σ → Prop)
    (hP : ∀ t, P (mask t) ↔ P t) (hs : P s) : P s' :=
  (h.preserves P hP).mpr hs

/-- Any predicate over an unmasked projection `p : σ → α` is preserved across `AgreesExcept`. -/
theorem preserves_proj {α : Type} (h : AgreesExcept mask s s') (p : σ → α) (P : α → Prop)
    (hp : ∀ t, p (mask t) = p t := by intro; rfl) : P (p s') ↔ P (p s) := by
  rw [h.get p hp]

/-- Transport `P (p s)` to `P (p s')` for any unmasked projection `p : σ → α`. -/
theorem transport_proj {α : Type} (h : AgreesExcept mask s s') (p : σ → α) (P : α → Prop)
    (hs : P (p s)) (hp : ∀ t, p (mask t) = p t := by intro; rfl) : P (p s') :=
  (h.preserves_proj p P hp).mpr hs

/-- Unmasked array length preservation. -/
theorem arr_length {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s').length = (arr s).length :=
  congrArg List.length (h.get arr hf)

/-- Unmasked array `getElem?` preservation. -/
theorem arr_getElem? {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (i : Nat)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s')[i]? = (arr s)[i]? := by
  rw [h.get arr hf]

/-- Unmasked array `getElem` preservation. -/
theorem arr_getElem {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (i : Nat)
    (hi : i < (arr s).length) (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s')[i]'(by rw [h.arr_length arr hf]; exact hi) = (arr s)[i]'hi := by
  have h1 := h.arr_getElem? arr i hf
  rw [List.getElem?_eq_getElem (by rw [h.arr_length arr hf]; exact hi),
    List.getElem?_eq_getElem hi] at h1
  exact Option.some.inj h1

/-- Unmasked array `getElem?.getD` preservation. -/
theorem arr_getD {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (i : Nat) (d : α)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s')[i]?.getD d = (arr s)[i]?.getD d := by
  rw [h.get arr hf]

/-- Unmasked array prefix preservation (`List.take`). -/
theorem arr_take {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (n : Nat)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s').take n = (arr s).take n := by
  rw [h.get arr hf]

/-- Unmasked array suffix preservation (`List.drop`). -/
theorem arr_drop {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (n : Nat)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    (arr s').drop n = (arr s).drop n := by
  rw [h.get arr hf]

/-- Unmasked array sub-slice preservation (`(arr.drop off).take len`). -/
theorem arr_slice {α : Type} (h : AgreesExcept mask s s') (arr : σ → List α) (off len : Nat)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    ((arr s').drop off).take len = ((arr s).drop off).take len := by
  rw [h.get arr hf]

end AgreesExcept

/-! ### Top-level aliases matching `agreesExcept_*` naming -/

theorem agreesExcept_symm {σ : Type} {mask : σ → σ} {s s' : σ} (h : AgreesExcept mask s s') :
    AgreesExcept mask s' s :=
  h.symm

theorem agreesExcept_trans {σ : Type} {mask : σ → σ} {s s' s'' : σ}
    (h₁ : AgreesExcept mask s s') (h₂ : AgreesExcept mask s' s'') :
    AgreesExcept mask s s'' :=
  h₁.trans h₂

theorem agreesExcept_mono {σ : Type} {mask₁ mask₂ : σ → σ} {s s' : σ}
    (h : AgreesExcept mask₁ s s')
    (hsub : ∀ t, mask₂ (mask₁ t) = mask₂ t := by intro; rfl) :
    AgreesExcept mask₂ s s' :=
  h.mono hsub

theorem agreesExcept_get {σ α : Type} {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s') (f : σ → α)
    (hf : ∀ t, f (mask t) = f t := by intro; rfl) : f s' = f s :=
  h.get f hf

theorem agreesExcept_proj {σ τ : Type} {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s') (p : σ → τ) (maskSub : τ → τ)
    (hp : ∀ t, maskSub (p (mask t)) = maskSub (p t) := by intro; rfl) :
    AgreesExcept maskSub (p s) (p s') :=
  h.proj p maskSub hp

theorem agreesExcept_preserves {σ : Type} {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s') (P : σ → Prop) (hP : ∀ t, P (mask t) ↔ P t) :
    P s' ↔ P s :=
  h.preserves P hP

theorem agreesExcept_preserves_proj {σ α : Type} {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s') (p : σ → α) (P : α → Prop)
    (hp : ∀ t, p (mask t) = p t := by intro; rfl) : P (p s') ↔ P (p s) :=
  h.preserves_proj p P hp

/-! ## 2. List `getD`, prefix, and slice agreement algebra -/

theorem getElem?_getD_of_lt {α : Type} {xs : List α} {i : Nat} (d : α) (hi : i < xs.length) :
    xs[i]?.getD d = xs[i] := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem getElem?_getD_set_eq {α : Type} (xs : List α) {i : Nat} (v d : α)
    (hi : i < xs.length) : (xs.set i v)[i]?.getD d = v := by
  rw [List.getElem?_set_self hi, Option.getD_some]

theorem getElem?_getD_set_ne {α : Type} (xs : List α) {i j : Nat} (v d : α) (hne : i ≠ j) :
    (xs.set i v)[j]?.getD d = xs[j]?.getD d := by
  rw [List.getElem?_set_ne hne]

theorem getElem?_getD_set {α : Type} (xs : List α) (i j : Nat) (v d : α) :
    (xs.set i v)[j]?.getD d = if i = j ∧ i < xs.length then v else xs[j]?.getD d := by
  rw [List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hi : i < xs.length <;> simp [hi]
  · simp [h]

/-- `ys` agrees with `xs` on the prefix `[0, n)`. -/
def PrefixAgrees {α : Type} (n : Nat) (xs ys : List α) : Prop :=
  ∀ i < n, ys[i]? = xs[i]?

namespace PrefixAgrees

variable {α : Type} {n n' : Nat} {xs ys zs : List α}

theorem refl (n : Nat) (xs : List α) : PrefixAgrees n xs xs := fun _ _ => rfl

theorem symm (h : PrefixAgrees n xs ys) : PrefixAgrees n ys xs :=
  fun i hi => (h i hi).symm

theorem trans (h₁ : PrefixAgrees n xs ys) (h₂ : PrefixAgrees n ys zs) :
    PrefixAgrees n xs zs :=
  fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem mono (h : PrefixAgrees n xs ys) (hle : n' ≤ n) : PrefixAgrees n' xs ys :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hle)

theorem zero (xs ys : List α) : PrefixAgrees 0 xs ys := fun _ h => absurd h (Nat.not_lt_zero _)

theorem of_eq (n : Nat) (h : ys = xs) : PrefixAgrees n xs ys := h ▸ refl n xs

theorem getElem?_eq (h : PrefixAgrees n xs ys) {i : Nat} (hi : i < n) : ys[i]? = xs[i]? :=
  h i hi

theorem getD_eq (h : PrefixAgrees n xs ys) {i : Nat} (d : α) (hi : i < n) :
    ys[i]?.getD d = xs[i]?.getD d := by
  rw [h i hi]

theorem getElem_eq (h : PrefixAgrees n xs ys) {i : Nat} (hi : i < n)
    (hx : i < xs.length) (hy : i < ys.length) : ys[i]'hy = xs[i]'hx := by
  have heq := h i hi
  rw [List.getElem?_eq_getElem hy, List.getElem?_eq_getElem hx] at heq
  exact Option.some.inj heq

theorem set_of_ge (xs : List α) {k : Nat} (v : α) (hk : n ≤ k) :
    PrefixAgrees n xs (xs.set k v) :=
  fun _ hi => List.getElem?_set_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hi hk))

theorem update_set (h : PrefixAgrees n xs ys) {k : Nat} (v : α) (hk : n ≤ k) :
    PrefixAgrees n xs (ys.set k v) :=
  h.trans (set_of_ge ys v hk)

theorem take_eq (h : PrefixAgrees n xs ys) : ys.take n = xs.take n := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rename_i hi; exact h i hi
  · rfl

theorem of_take_eq (h : ys.take n = xs.take n) : PrefixAgrees n xs ys := by
  intro i hi
  have hget := congrArg (fun l => l[i]?) h
  simpa [List.getElem?_take, hi] using hget

theorem of_agreesExcept {σ : Type} {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s') (arr : σ → List α) (n : Nat)
    (hf : ∀ t, arr (mask t) = arr t := by intro; rfl) :
    PrefixAgrees n (arr s) (arr s') :=
  of_eq n (h.get arr hf)

end PrefixAgrees

/-- `ys` agrees with `xs` on the half-open slice `[lo, hi)`. -/
def SliceAgrees {α : Type} (lo hi : Nat) (xs ys : List α) : Prop :=
  ∀ i, lo ≤ i → i < hi → ys[i]? = xs[i]?

namespace SliceAgrees

variable {α : Type} {lo hi lo' hi' : Nat} {xs ys zs : List α}

theorem refl (lo hi : Nat) (xs : List α) : SliceAgrees lo hi xs xs := fun _ _ _ => rfl

theorem symm (h : SliceAgrees lo hi xs ys) : SliceAgrees lo hi ys xs :=
  fun i h1 h2 => (h i h1 h2).symm

theorem trans (h₁ : SliceAgrees lo hi xs ys) (h₂ : SliceAgrees lo hi ys zs) :
    SliceAgrees lo hi xs zs :=
  fun i h1 h2 => (h₂ i h1 h2).trans (h₁ i h1 h2)

theorem mono (h : SliceAgrees lo hi xs ys) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    SliceAgrees lo' hi' xs ys :=
  fun i h1 h2 => h i (Nat.le_trans hlo h1) (Nat.lt_of_lt_of_le h2 hhi)

theorem of_eq (lo hi : Nat) (h : ys = xs) : SliceAgrees lo hi xs ys := h ▸ refl lo hi xs

theorem getElem?_eq (h : SliceAgrees lo hi xs ys) {i : Nat} (h1 : lo ≤ i) (h2 : i < hi) :
    ys[i]? = xs[i]? :=
  h i h1 h2

theorem getD_eq (h : SliceAgrees lo hi xs ys) {i : Nat} (d : α) (h1 : lo ≤ i) (h2 : i < hi) :
    ys[i]?.getD d = xs[i]?.getD d := by
  rw [h i h1 h2]

theorem set_of_outside (xs : List α) {k : Nat} (v : α) (hk : k < lo ∨ hi ≤ k) :
    SliceAgrees lo hi xs (xs.set k v) :=
  fun i h1 h2 => List.getElem?_set_ne (by omega)

theorem update_set (h : SliceAgrees lo hi xs ys) {k : Nat} (v : α) (hk : k < lo ∨ hi ≤ k) :
    SliceAgrees lo hi xs (ys.set k v) :=
  h.trans (set_of_outside ys v hk)

theorem drop_take_eq {len : Nat} (h : SliceAgrees lo (lo + len) xs ys) :
    (ys.drop lo).take len = (xs.drop lo).take len := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rename_i hi
    rw [List.getElem?_drop, List.getElem?_drop]
    exact h (lo + i) (Nat.le_add_right lo i) (Nat.add_lt_add_left hi lo)
  · rfl

theorem of_prefix {n : Nat} (h : PrefixAgrees n xs ys) (hhi : hi ≤ n) :
    SliceAgrees lo hi xs ys :=
  fun i _ h2 => h i (Nat.lt_of_lt_of_le h2 hhi)

theorem to_prefix (h : SliceAgrees 0 hi xs ys) : PrefixAgrees hi xs ys :=
  fun i h2 => h i (Nat.zero_le i) h2

end SliceAgrees

/-- `ys` agrees with `xs` everywhere outside `[lo, hi)`. -/
def OutsideSliceAgrees {α : Type} (lo hi : Nat) (xs ys : List α) : Prop :=
  ∀ i, (i < lo ∨ hi ≤ i) → ys[i]? = xs[i]?

namespace OutsideSliceAgrees

variable {α : Type} {lo hi lo' hi' : Nat} {xs ys zs : List α}

theorem refl (lo hi : Nat) (xs : List α) : OutsideSliceAgrees lo hi xs xs := fun _ _ => rfl

theorem symm (h : OutsideSliceAgrees lo hi xs ys) : OutsideSliceAgrees lo hi ys xs :=
  fun i hne => (h i hne).symm

theorem trans (h₁ : OutsideSliceAgrees lo hi xs ys) (h₂ : OutsideSliceAgrees lo hi ys zs) :
    OutsideSliceAgrees lo hi xs zs :=
  fun i hne => (h₂ i hne).trans (h₁ i hne)

theorem mono (h : OutsideSliceAgrees lo hi xs ys) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    OutsideSliceAgrees lo' hi' xs ys :=
  fun i hor => h i (hor.elim (fun h1 => Or.inl (Nat.lt_of_lt_of_le h1 hlo))
    (fun h2 => Or.inr (Nat.le_trans hhi h2)))

theorem of_eq (lo hi : Nat) (h : ys = xs) : OutsideSliceAgrees lo hi xs ys :=
  h ▸ refl lo hi xs

theorem getElem?_lt (h : OutsideSliceAgrees lo hi xs ys) {i : Nat} (h1 : i < lo) :
    ys[i]? = xs[i]? :=
  h i (Or.inl h1)

theorem getElem?_ge (h : OutsideSliceAgrees lo hi xs ys) {i : Nat} (h2 : hi ≤ i) :
    ys[i]? = xs[i]? :=
  h i (Or.inr h2)

theorem getD_lt (h : OutsideSliceAgrees lo hi xs ys) {i : Nat} (d : α) (h1 : i < lo) :
    ys[i]?.getD d = xs[i]?.getD d := by
  rw [h.getElem?_lt h1]

theorem getD_ge (h : OutsideSliceAgrees lo hi xs ys) {i : Nat} (d : α) (h2 : hi ≤ i) :
    ys[i]?.getD d = xs[i]?.getD d := by
  rw [h.getElem?_ge h2]

theorem set_of_mem (xs : List α) {k : Nat} (v : α) (h1 : lo ≤ k) (h2 : k < hi) :
    OutsideSliceAgrees lo hi xs (xs.set k v) :=
  fun i hor => List.getElem?_set_ne (by omega)

theorem update_set (h : OutsideSliceAgrees lo hi xs ys) {k : Nat} (v : α)
    (h1 : lo ≤ k) (h2 : k < hi) : OutsideSliceAgrees lo hi xs (ys.set k v) :=
  h.trans (set_of_mem ys v h1 h2)

theorem to_prefix (h : OutsideSliceAgrees lo hi xs ys) : PrefixAgrees lo xs ys :=
  fun _ h1 => h.getElem?_lt h1

theorem take_eq (h : OutsideSliceAgrees lo hi xs ys) : ys.take lo = xs.take lo :=
  h.to_prefix.take_eq

theorem drop_eq (h : OutsideSliceAgrees lo hi xs ys) : ys.drop hi = xs.drop hi := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_drop]
  exact h.getElem?_ge (Nat.le_add_right hi i)

end OutsideSliceAgrees

/-! ## 3. Framed loop and join rules (`wp_loop_agreesExcept`) -/

section LoopAgrees

variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}

/-- Measure-based loop rule wrapping `C0Step.wp_loop_inv` with automatic `AgreesExcept mask s₀ s'`
framing: multi-field struct loop invariants never enumerate unchanged fields manually. On each
back-edge, supply only the step-local `AgreesExcept mask s' s''` (which closes by `rfl` on any
sequence of masked record updates or `hcall.mono` after a callee). -/
theorem wp_loop_agreesExcept {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : σ → Tup Val ts → Mem 64 → Prop)
    (μ : Tup Val ts → Mem 64 → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, AgreesExcept mask s₀ s' → Inv s' xs ml → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      AgreesExcept mask s₀ s' → Inv s' xs ml →
      (∀ s'' ys ml', μ ys ml' < μ xs ml → AgreesExcept mask s' s'' →
        Inv s'' ys ml' → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_inv (fun xs ml => ∃ s', AgreesExcept mask s₀ s' ∧ Inv s' xs ml) μ
    (fun J hJ => hentry J fun s' xs ml hag hi => hJ xs ml ⟨s', hag, hi⟩)
    (fun J xs ml ⟨s', hag, hi⟩ hJ =>
      hbody J s' xs ml hag hi fun s'' ys ml' hlt hstep hi' =>
        hJ ys ml' hlt ⟨s'', hag.trans hstep, hi'⟩)

/-- `wp_loop_agreesExcept` specialized to a separation-logic state footprint `(MemPred s' ⋆ R)`
and a pure SSA-driven measure `μ : Tup Val ts → Nat`. Memory precedes `AgreesExcept` on the
back-edge so `c0_frame` instantiates `s''` before `rfl` closes `AgreesExcept`. -/
theorem wp_loop_agreesExcept_mem {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ) (MemPred : σ → Mem 64 → Prop) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : σ → Tup Val ts → Prop)
    (μ : Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (MemPred s' ⋆ R) ml → AgreesExcept mask s₀ s' → Inv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      AgreesExcept mask s₀ s' → Inv s' xs → (MemPred s' ⋆ R) ml →
      (∀ s'' ys ml', (MemPred s'' ⋆ R) ml' → μ ys < μ xs → AgreesExcept mask s' s'' →
        Inv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_agreesExcept mask s₀ (fun s' xs ml => Inv s' xs ∧ (MemPred s' ⋆ R) ml) (fun xs _ => μ xs)
    (fun J hJ => hentry J fun s' xs ml hml hag hi => hJ s' xs ml hag ⟨hi, hml⟩)
    (fun J s' xs ml hag ⟨hi, hml⟩ hJ =>
      hbody J s' xs ml hag hi hml fun s'' ys ml' hml' hlt hstep hi' =>
        hJ s'' ys ml' hlt hstep ⟨hi', hml'⟩)

/-- State-measure variant of `wp_loop_agreesExcept` where the decreasing variant `μ : σ → Tup Val
ts → Nat` may depend on struct fields in memory (e.g. `s'.trail_end`, `s'.fuel`, `s'.heap_len`). -/
theorem wp_loop_agreesExcept_state {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : σ → Tup Val ts → Mem 64 → Prop)
    (μ : σ → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, AgreesExcept mask s₀ s' → Inv s' xs ml → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      AgreesExcept mask s₀ s' → Inv s' xs ml →
      (∀ s'' ys ml', μ s'' ys < μ s' xs → AgreesExcept mask s' s'' →
        Inv s'' ys ml' → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group (fun n xs ml => ∃ s', AgreesExcept mask s₀ s' ∧ Inv s' xs ml ∧ μ s' xs = n)
    (fun J _ xs ml hJ ⟨s', hag, hi, hμ⟩ =>
      hbody J s' xs ml hag hi fun s'' ys ml' hlt hstep hi' =>
        hJ _ ys ml' (hμ ▸ hlt) ⟨s'', hag.trans hstep, hi', rfl⟩)
    (fun J hJ => hentry J fun s' xs ml hag hi => hJ _ xs ml ⟨s', hag, hi, rfl⟩)

/-- State-measure `wp_loop_agreesExcept_state` with a separation-logic state footprint
`(MemPred s' ⋆ R)` baked into the invariant (memory precedes `μ`/`AgreesExcept` on back-edges so
`c0_frame` instantiates `s''` first). -/
theorem wp_loop_agreesExcept_state_mem {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ) (MemPred : σ → Mem 64 → Prop) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : σ → Tup Val ts → Prop)
    (μ : σ → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (MemPred s' ⋆ R) ml → AgreesExcept mask s₀ s' → Inv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      AgreesExcept mask s₀ s' → Inv s' xs → (MemPred s' ⋆ R) ml →
      (∀ s'' ys ml', (MemPred s'' ⋆ R) ml' → μ s'' ys < μ s' xs → AgreesExcept mask s' s'' →
        Inv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_agreesExcept_state mask s₀ (fun s' xs ml => Inv s' xs ∧ (MemPred s' ⋆ R) ml) μ
    (fun J hJ => hentry J fun s' xs ml hml hag hi => hJ s' xs ml hag ⟨hi, hml⟩)
    (fun J s' xs ml hag ⟨hi, hml⟩ hJ =>
      hbody J s' xs ml hag hi hml fun s'' ys ml' hml' hlt hstep hi' =>
        hJ s'' ys ml' hlt hstep ⟨hi', hml'⟩)

/-- Loop-with-break rule (`wp_loop_break_group`) with automatic `AgreesExcept mask s₀ s'`
framing in both the loop invariant and the break continuation `hafter`. -/
theorem wp_loop_break_agreesExcept {brkTs lpTs : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ)
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    (BrkPost : σ → Tup Val brkTs → Mem 64 → Prop)
    (Inv : σ → Tup Val lpTs → Mem 64 → Prop)
    (μ : σ → Tup Val lpTs → Nat)
    (hafter : ∀ (B : Cont brkTs) s' xs ml,
      AgreesExcept mask s₀ s' → BrkPost s' xs ml →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here xs) ml)
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) s' xs ml,
      AgreesExcept mask s₀ s' → Inv s' xs ml →
      (∀ s'' r ml', AgreesExcept mask s' s'' → BrkPost s'' r ml' → B r ml') →
      (∀ s'' ys ml', μ s'' ys < μ s' xs → AgreesExcept mask s' s'' →
        Inv s'' ys ml' → L ys ml') →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here xs) ml)
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ s' r ml, AgreesExcept mask s₀ s' → BrkPost s' r ml → B r ml) →
      (∀ s' xs ml, AgreesExcept mask s₀ s' → Inv s' xs ml → L xs ml) →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_loop_break_group
    (fun xs ml => ∃ s', AgreesExcept mask s₀ s' ∧ BrkPost s' xs ml)
    (fun n xs ml => ∃ s', AgreesExcept mask s₀ s' ∧ Inv s' xs ml ∧ μ s' xs = n)
    (fun B xs ml ⟨s', hag, hb⟩ => hafter B s' xs ml hag hb)
    (fun B L _ xs ml hB hL ⟨s', hag, hi, hμ⟩ =>
      hbody B L s' xs ml hag hi
        (fun s'' r ml' hstep hb' => hB r ml' ⟨s'', hag.trans hstep, hb'⟩)
        (fun s'' ys ml' hlt hstep hi' => hL _ ys ml' (hμ ▸ hlt) ⟨s'', hag.trans hstep, hi', rfl⟩))
    (fun B L hB hL =>
      hentry B L
        (fun s' r ml hag hb => hB r ml ⟨s', hag, hb⟩)
        (fun s' xs ml hag hi => hL _ xs ml ⟨s', hag, hi, rfl⟩))

/-- Forward join-point rule (`wp_join_group`) with automatic `AgreesExcept mask s₀ s'` framing. -/
theorem wp_join_agreesExcept {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : σ → Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) s' xs ml, AgreesExcept mask s₀ s' → P s' xs ml →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, AgreesExcept mask s₀ s' → P s' xs ml → J xs ml) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun xs ml => ∃ s', AgreesExcept mask s₀ s' ∧ P s' xs ml)
    (fun J xs ml ⟨s', hag, hp⟩ => hbody J s' xs ml hag hp)
    (fun J hJ => hentry J fun s' xs ml hag hp => hJ xs ml ⟨s', hag, hp⟩)

/-- `wp_join_agreesExcept` with a separation-logic footprint `(MemPred s' ⋆ R)` baked in. -/
theorem wp_join_agreesExcept_mem {ts : List Ty} {m : Mem 64} {σ : Type}
    (mask : σ → σ) (s₀ : σ) (MemPred : σ → Mem 64 → Prop) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : σ → Tup Val ts → Prop)
    (hbody : ∀ (J : Cont ts) s' xs ml, AgreesExcept mask s₀ s' → P s' xs →
      (MemPred s' ⋆ R) ml → wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, AgreesExcept mask s₀ s' → P s' xs → (MemPred s' ⋆ R) ml → J xs ml) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_agreesExcept mask s₀ (fun s' xs ml => P s' xs ∧ (MemPred s' ⋆ R) ml)
    (fun J s' xs ml hag ⟨hp, hml⟩ => hbody J s' xs ml hag hp hml)
    (fun J hJ => hentry J fun s' xs ml hag hp hml => hJ s' xs ml hag ⟨hp, hml⟩)

end LoopAgrees

/-! ## 4. Safety-only slice combinator (`PreservesCoreSlice`, `SafetySlice`, `wp_safety_slice`) -/

/-- `s'` preserves the core soundness projection `coreProj` of `s`.
Functions that only mutate heuristic, phase, WalkSAT, queue/heap, or witness-reconstruction
scratch buffers satisfy `PreservesCoreSlice coreProj s s'`, allowing any core soundness invariant
`Inv (coreProj s)` to be transported across the transition in one step. -/
def PreservesCoreSlice {σ κ : Type} (coreProj : σ → κ) (s s' : σ) : Prop :=
  coreProj s' = coreProj s

theorem preservesCoreSlice_iff {σ κ : Type} (coreProj : σ → κ) (s s' : σ) :
    PreservesCoreSlice coreProj s s' ↔ coreProj s' = coreProj s :=
  Iff.rfl

theorem preservesCoreSlice_refl {σ κ : Type} (coreProj : σ → κ) (s : σ) :
    PreservesCoreSlice coreProj s s :=
  rfl

namespace PreservesCoreSlice

variable {σ κ : Type} {coreProj : σ → κ} {s s' s'' : σ}

theorem refl (coreProj : σ → κ) (s : σ) : PreservesCoreSlice coreProj s s := rfl

theorem symm (h : PreservesCoreSlice coreProj s s') : PreservesCoreSlice coreProj s' s :=
  Eq.symm h

theorem trans (h₁ : PreservesCoreSlice coreProj s s')
    (h₂ : PreservesCoreSlice coreProj s' s'') : PreservesCoreSlice coreProj s s'' :=
  Eq.trans h₂ h₁

theorem of_eq (coreProj : σ → κ) (h : s' = s) : PreservesCoreSlice coreProj s s' :=
  h ▸ rfl

/-- Any `AgreesExcept mask` whose mask leaves `coreProj` unchanged implies `PreservesCoreSlice`. -/
theorem of_agreesExcept {mask : σ → σ} (h : AgreesExcept mask s s')
    (hp : ∀ t, coreProj (mask t) = coreProj t := by intro; rfl) :
    PreservesCoreSlice coreProj s s' :=
  h.get coreProj hp

/-- Direct equivalence when `coreProj` itself is used as an `AgreesExcept` mask. -/
theorem agreesExcept_iff (mask : σ → σ) (s s' : σ) :
    AgreesExcept mask s s' ↔ PreservesCoreSlice mask s s' :=
  Iff.rfl

/-- A scratch-only update from `s` preserves `coreProj` (`hu` closes by `rfl`). -/
theorem of_update (coreProj : σ → κ) (s : σ) (upd : σ → σ)
    (hu : ∀ t, coreProj (upd t) = coreProj t := by intro; rfl) :
    PreservesCoreSlice coreProj s (upd s) :=
  hu s

/-- Chaining a scratch-only update preserves `coreProj`. -/
theorem update (h : PreservesCoreSlice coreProj s s') (upd : σ → σ)
    (hu : ∀ t, coreProj (upd t) = coreProj t := by intro; rfl) :
    PreservesCoreSlice coreProj s (upd s') :=
  (hu s').trans h

/-- Stripping a scratch-only update on the left state preserves `coreProj`. -/
theorem update_left {upd : σ → σ} (h : PreservesCoreSlice coreProj (upd s) s')
    (hu : ∀ t, coreProj (upd t) = coreProj t := by intro; rfl) :
    PreservesCoreSlice coreProj s s' :=
  Eq.trans h (hu s)

/-- Coarsen a core projection by composing with `f : κ → κ'`. -/
theorem comp {κ' : Type} (f : κ → κ') (h : PreservesCoreSlice coreProj s s') :
    PreservesCoreSlice (fun t => f (coreProj t)) s s' :=
  congrArg f h

/-- Combine two core-slice preservations into a paired projection. -/
theorem pair {κ₁ κ₂ : Type} {p₁ : σ → κ₁} {p₂ : σ → κ₂}
    (h₁ : PreservesCoreSlice p₁ s s') (h₂ : PreservesCoreSlice p₂ s s') :
    PreservesCoreSlice (fun t => (p₁ t, p₂ t)) s s' :=
  Prod.ext h₁ h₂

/-- Transport an arbitrary core soundness invariant `Inv : κ → Prop` in one step. -/
theorem transport (h : PreservesCoreSlice coreProj s s') (Inv : κ → Prop)
    (hInv : Inv (coreProj s)) : Inv (coreProj s') :=
  h.symm ▸ hInv

/-- Bidirectional transport of `Inv (coreProj ·)`. -/
theorem transport_iff (h : PreservesCoreSlice coreProj s s') (Inv : κ → Prop) :
    Inv (coreProj s') ↔ Inv (coreProj s) := by
  rw [h]

/-- Project any derived core observable `f : κ → α`. -/
theorem get {α : Type} (h : PreservesCoreSlice coreProj s s') (f : κ → α) :
    f (coreProj s') = f (coreProj s) :=
  congrArg f h

/-- Unchanged core array slice via `coreProj`. -/
theorem arr_slice {α : Type} (h : PreservesCoreSlice coreProj s s')
    (arr : κ → List α) (off len : Nat) :
    ((arr (coreProj s')).drop off).take len = ((arr (coreProj s)).drop off).take len := by
  rw [h]

end PreservesCoreSlice

/-- A full-state invariant `FullInv : σ → Prop` (such as a CDCL solver invariant bundling
UNSAT soundness with buffer lengths) factors through `(coreProj, Safe)` when preserving the core
slice and memory safety suffices to preserve `FullInv`. -/
def DependsOnCoreAndSafe {σ κ : Type} (coreProj : σ → κ) (Safe : σ → Prop)
    (FullInv : σ → Prop) : Prop :=
  ∀ s s', PreservesCoreSlice coreProj s s' → Safe s' → FullInv s → FullInv s'

theorem dependsOnCoreAndSafe_proj_and_safe {σ κ : Type} (coreProj : σ → κ) (Safe : σ → Prop)
    (Inv : κ → Prop) :
    DependsOnCoreAndSafe coreProj Safe (fun s => Inv (coreProj s) ∧ Safe s) :=
  fun _ _ hcore hsafe ⟨hInv, _⟩ => ⟨hcore.transport Inv hInv, hsafe⟩

theorem dependsOnCoreAndSafe_proj {σ κ : Type} (coreProj : σ → κ) (Safe : σ → Prop)
    (Inv : κ → Prop) :
    DependsOnCoreAndSafe coreProj Safe (fun s => Inv (coreProj s)) :=
  fun _ _ hcore _ hInv => hcore.transport Inv hInv

theorem dependsOnCoreAndSafe_and {σ κ : Type} {coreProj : σ → κ} {Safe : σ → Prop}
    {P₁ P₂ : σ → Prop} (h₁ : DependsOnCoreAndSafe coreProj Safe P₁)
    (h₂ : DependsOnCoreAndSafe coreProj Safe P₂) :
    DependsOnCoreAndSafe coreProj Safe (fun s => P₁ s ∧ P₂ s) :=
  fun s s' hcore hsafe ⟨hp1, hp2⟩ => ⟨h₁ s s' hcore hsafe hp1, h₂ s s' hcore hsafe hp2⟩

/-- A *safety slice* packages a C0 state footprint `mem`, a core soundness projection `coreProj`
(read-only / untouched by scratch helpers), and a memory-safety invariant `safe`. -/
structure SafetySlice (σ κ : Type) where
  mem : σ → Mem 64 → Prop
  coreProj : σ → κ
  safe : σ → Prop

namespace SafetySlice

/-- Build a `SafetySlice` directly from an `AgreesExcept` mask `mask : σ → σ` (so
`PreservesCoreSlice coreProj` is definitionally `AgreesExcept mask`). -/
def ofMask {σ : Type} (mem : σ → Mem 64 → Prop) (mask : σ → σ) (safe : σ → Prop) :
    SafetySlice σ σ :=
  ⟨mem, mask, safe⟩

theorem ofMask_mem {σ : Type} (mem : σ → Mem 64 → Prop) (mask : σ → σ) (safe : σ → Prop) :
    (ofMask mem mask safe).mem = mem := rfl

theorem ofMask_coreProj {σ : Type} (mem : σ → Mem 64 → Prop) (mask : σ → σ) (safe : σ → Prop) :
    (ofMask mem mask safe).coreProj = mask := rfl

theorem ofMask_safe {σ : Type} (mem : σ → Mem 64 → Prop) (mask : σ → σ) (safe : σ → Prop) :
    (ofMask mem mask safe).safe = safe := rfl

/-- Build a `SafetySlice` for a state already split into disjoint `(core, scratch)` memory. -/
def ofPair {κ τ : Type} (coreMem : κ → Mem 64 → Prop) (scratchMem : τ → Mem 64 → Prop)
    (scratchSafe : τ → Prop) : SafetySlice (κ × τ) κ where
  mem := fun (k, t) => coreMem k ⋆ scratchMem t
  coreProj := Prod.fst
  safe := fun (_, t) => scratchSafe t

theorem ofPair_mem {κ τ : Type} (coreMem : κ → Mem 64 → Prop) (scratchMem : τ → Mem 64 → Prop)
    (scratchSafe : τ → Prop) (k : κ) (t : τ) :
    (ofPair coreMem scratchMem scratchSafe).mem (k, t) = (coreMem k ⋆ scratchMem t) := rfl

theorem ofPair_coreProj {κ τ : Type} (coreMem : κ → Mem 64 → Prop)
    (scratchMem : τ → Mem 64 → Prop) (scratchSafe : τ → Prop) (p : κ × τ) :
    (ofPair coreMem scratchMem scratchSafe).coreProj p = p.1 := rfl

theorem ofPair_safe {κ τ : Type} (coreMem : κ → Mem 64 → Prop) (scratchMem : τ → Mem 64 → Prop)
    (scratchSafe : τ → Prop) (p : κ × τ) :
    (ofPair coreMem scratchMem scratchSafe).safe p = scratchSafe p.2 := rfl

/-- Reusable safety-only contract for a config-indexed `SafetySlice`:
functions implementing `SafetySlice.spec` prove only memory safety (`safe`), core-projection
preservation (`PreservesCoreSlice`), optional `Post`, and frame preservation `R`. Callers
transport arbitrary core soundness predicates `Inv ((sl c).coreProj s)` in one step via
`wp_safety_slice_call` / `wp_safety_slice_func`. -/
def spec {ι σ κ : Type} {as rs : List Ty}
    (sl : ι → SafetySlice σ κ)
    (Pre : ι → Tup Val as → σ → Prop)
    (Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop := fun _ _ _ _ _ => True) :
    Spec as rs :=
  fun xs m Q _ =>
    ∃ (c : ι) (s : σ) (R : Mem 64 → Prop),
      Pre c xs s ∧ (sl c).safe s ∧ ((sl c).mem s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (s' : σ) (m' : Mem 64),
        PreservesCoreSlice (sl c).coreProj s s' →
        (sl c).safe s' →
        Post c xs r s s' →
        ((sl c).mem s' ⋆ R) m' →
        Q r m'

/-- Unindexed shorthand for `SafetySlice.spec` when no static config `ι` is needed. -/
abbrev spec0 {σ κ : Type} {as rs : List Ty}
    (sl : SafetySlice σ κ)
    (Pre : Tup Val as → σ → Prop)
    (Post : Tup Val as → Tup Val rs → σ → σ → Prop := fun _ _ _ _ => True) :
    Spec as rs :=
  spec (ι := Unit) (fun _ => sl) (fun _ => Pre) (fun _ => Post)

/-- Every `SafetySlice.spec` is monotone in both postconditions. -/
theorem spec_mono {ι σ κ : Type} {as rs : List Ty}
    (sl : ι → SafetySlice σ κ)
    (Pre : ι → Tup Val as → σ → Prop)
    (Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop) :
    (spec sl Pre Post).Mono := by
  rintro xs m Q Q' X X' hQ _ ⟨c, s, R, hPre, hSafe, hm, hk⟩
  exact ⟨c, s, R, hPre, hSafe, hm, fun r s' m' hcore hs' hp hm' =>
    hQ r m' (hk r s' m' hcore hs' hp hm')⟩

/-- Every `SafetySlice.spec` ignores exit continuations (`Compiled.fnSpec_noExit_id`). -/
theorem spec_noExit {ι σ κ : Type} {as rs : List Ty}
    {sl : ι → SafetySlice σ κ} {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X X' : XPost}
    (h : spec sl Pre Post xs m Q X) : spec sl Pre Post xs m Q X' :=
  h

/-- Separation-logic frame closure of `SafetySlice.spec`. -/
theorem spec_frame {ι σ κ : Type} {as rs : List Ty}
    {sl : ι → SafetySlice σ κ} {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost} {F : Mem 64 → Prop}
    (h : ((fun m₁ => spec sl Pre Post xs m₁ Q X) ⋆ F) m) :
    spec sl Pre Post xs m (fun r m' => (Q r ⋆ F) m') X := by
  unfold spec at h ⊢
  obtain ⟨c, h⟩ := sep_ex_l.mp h
  obtain ⟨s, h⟩ := sep_ex_l.mp h
  obtain ⟨R, h⟩ := sep_ex_l.mp h
  obtain ⟨hPre, h⟩ := sep_pure_l.mp h
  obtain ⟨hSafe, h⟩ := sep_pure_l.mp h
  obtain ⟨hk, hmF⟩ := sep_pure_l.mp (sep_mono (fun _ hx => ⟨hx.2, hx.1⟩) h)
  rw [sep_assoc] at hmF
  refine ⟨c, s, R ⋆ F, hPre, hSafe, hmF, fun r s' m' hcore hs' hp hm' => ?_⟩
  rw [← sep_assoc] at hm'
  exact sep_mono (fun _ hsm' => hk r s' _ hcore hs' hp hsm') hm'

/-- Strengthen preconditions / weaken postconditions of a `SafetySlice.spec`. -/
theorem spec_weaken {ι σ κ : Type} {as rs : List Ty}
    {sl : ι → SafetySlice σ κ}
    {Pre₁ Pre₂ : ι → Tup Val as → σ → Prop}
    {Post₁ Post₂ : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    (hPre : ∀ c xs s, Pre₁ c xs s → Pre₂ c xs s)
    (hPost : ∀ c xs r s s', Pre₁ c xs s → PreservesCoreSlice (sl c).coreProj s s' →
      (sl c).safe s' → Post₂ c xs r s s' → Post₁ c xs r s s')
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : spec sl Pre₁ Post₁ xs m Q X) : spec sl Pre₂ Post₂ xs m Q X := by
  rcases h with ⟨c, s, R, hp1, hs, hm, hk⟩
  exact ⟨c, s, R, hPre c xs s hp1, hs, hm, fun r s' m' hcore hs' hp2 hm' =>
    hk r s' m' hcore hs' (hPost c xs r s s' hp1 hcore hs' hp2) hm'⟩

/-- Bridge: any function proved with `AgreesExcept (mask c)` (where `mask c` leaves
`(sl c).coreProj` untouched) satisfies `SafetySlice.spec sl`. -/
theorem spec_of_agreesExcept {ι σ κ : Type} {as rs : List Ty}
    {sl : ι → SafetySlice σ κ} {mask : ι → σ → σ}
    {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    (hproj : ∀ c t, (sl c).coreProj (mask c t) = (sl c).coreProj t := by intro _ _; rfl)
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : spec sl Pre Post xs m Q X) :
    ∃ (c : ι) (s : σ) (R : Mem 64 → Prop),
      Pre c xs s ∧ (sl c).safe s ∧ ((sl c).mem s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (s' : σ) (m' : Mem 64),
        AgreesExcept (mask c) s s' →
        (sl c).safe s' →
        Post c xs r s s' →
        ((sl c).mem s' ⋆ R) m' →
        Q r m' := by
  rcases h with ⟨c, s, R, hPre, hSafe, hm, hk⟩
  exact ⟨c, s, R, hPre, hSafe, hm, fun r s' m' hag hs' hp hm' =>
    hk r s' m' (PreservesCoreSlice.of_agreesExcept hag (hproj c)) hs' hp hm'⟩

/-- Lift a scratch-only function contract (touching only `scratchMem`) into a `SafetySlice.ofPair`
contract over `coreMem ⋆ scratchMem`, framing `coreMem` automatically into `R`. -/
theorem lift_scratchOnly {ι κ τ : Type} {as rs : List Ty}
    {coreMem : ι → κ → Mem 64 → Prop} {scratchMem : ι → τ → Mem 64 → Prop}
    {scratchSafe : ι → τ → Prop}
    {Pre : ι → Tup Val as → τ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → τ → τ → Prop}
    {Γ : Env} {body : Func as rs}
    (hScratch : ∀ xs m Q X,
      (∃ (c : ι) (t : τ) (R : Mem 64 → Prop),
        Pre c xs t ∧ scratchSafe c t ∧ (scratchMem c t ⋆ R) m ∧
        ∀ r t' m', scratchSafe c t' → Post c xs r t t' →
          (scratchMem c t' ⋆ R) m' → Q r m') →
      Func.wp Γ body xs m Q X) :
    ∀ xs m Q X,
      spec (fun c => ofPair (coreMem c) (scratchMem c) (scratchSafe c))
        (fun c xs p => Pre c xs p.2) (fun c xs r p p' => Post c xs r p.2 p'.2) xs m Q X →
      Func.wp Γ body xs m Q X := by
  rintro xs m Q X ⟨c, ⟨k, t⟩, R, hPre, hSafe, hm, hk⟩
  apply hScratch xs m Q X
  refine ⟨c, t, coreMem c k ⋆ R, hPre, hSafe, by dsimp [ofPair] at hm; ecancel,
    fun r t' m' hSafe' hPost hm' => ?_⟩
  exact hk r (k, t') m' rfl hSafe' hPost (by dsimp [ofPair]; ecancel)

end SafetySlice

/-! ### One-step `wp` / `Func.wp` / `call` / `loop` / `join` safety-slice combinators -/

section SafetySliceWP

variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}

/-- Transport an arbitrary core soundness invariant `Inv (sl.coreProj s)` across any expression
`e` proved against safety-only postcondition `Post` and core-slice preservation. -/
theorem wp_safety_slice {σ κ : Type} (sl : SafetySlice σ κ)
    {s : σ} {R : Mem 64 → Prop} {m : Mem 64} {e : Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s))
    (Post : Tup Val rs → σ → Prop := fun _ _ => True)
    (hsafe : wp Γ (fun r m' => ∃ s', PreservesCoreSlice sl.coreProj s s' ∧
        sl.safe s' ∧ Post r s' ∧ (sl.mem s' ⋆ R) m') X e m)
    (hQ : ∀ r s' m', PreservesCoreSlice sl.coreProj s s' → sl.safe s' →
        Inv (sl.coreProj s') → Post r s' → (sl.mem s' ⋆ R) m' → Q r m') :
    wp Γ Q X e m :=
  wp_mono
    (fun r m' ⟨s', hcore, hs', hp, hm'⟩ =>
      hQ r s' m' hcore hs' (hcore.transport Inv hInv) hp hm')
    (fun _ _ _ _ hx => hx) e m hsafe

/-- Full-state variant of `wp_safety_slice` for invariants `FullInv : σ → Prop` satisfying
`DependsOnCoreAndSafe sl.coreProj sl.safe FullInv`. -/
theorem wp_safety_slice_full {σ κ : Type} (sl : SafetySlice σ κ)
    {s : σ} {R : Mem 64 → Prop} {m : Mem 64} {e : Expr Val Cont rs}
    {FullInv : σ → Prop}
    (hDep : DependsOnCoreAndSafe sl.coreProj sl.safe FullInv)
    (hFull : FullInv s)
    (Post : Tup Val rs → σ → Prop := fun _ _ => True)
    (hsafe : wp Γ (fun r m' => ∃ s', PreservesCoreSlice sl.coreProj s s' ∧
        sl.safe s' ∧ Post r s' ∧ (sl.mem s' ⋆ R) m') X e m)
    (hQ : ∀ r s' m', PreservesCoreSlice sl.coreProj s s' → sl.safe s' →
        FullInv s' → Post r s' → (sl.mem s' ⋆ R) m' → Q r m') :
    wp Γ Q X e m :=
  wp_mono
    (fun r m' ⟨s', hcore, hs', hp, hm'⟩ =>
      hQ r s' m' hcore hs' (hDep s s' hcore hs' hFull) hp hm')
    (fun _ _ _ _ hx => hx) e m hsafe

/-- Transport an arbitrary core soundness invariant `Inv ((sl c).coreProj s)` across any function
proved against `SafetySlice.spec`. -/
theorem wp_safety_slice_func {as : List Ty} {body : Func as rs}
    {ι σ κ : Type} {sl : ι → SafetySlice σ κ}
    {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    (hf : ∀ xs m Q X, SafetySlice.spec sl Pre Post xs m Q X → Func.wp Γ body xs m Q X)
    {c : ι} {xs : Tup Val as} {s : σ} {R : Mem 64 → Prop} {m : Mem 64}
    (Inv : κ → Prop) (hInv : Inv ((sl c).coreProj s))
    (hPre : Pre c xs s) (hSafe : (sl c).safe s) (hm : ((sl c).mem s ⋆ R) m)
    (hQ : ∀ r s' m', PreservesCoreSlice (sl c).coreProj s s' → (sl c).safe s' →
        Inv ((sl c).coreProj s') → Post c xs r s s' → ((sl c).mem s' ⋆ R) m' → Q r m') :
    Func.wp Γ body xs m Q X :=
  hf xs m Q X ⟨c, s, R, hPre, hSafe, hm, fun r s' m' hcore hs' hp hm' =>
    hQ r s' m' hcore hs' (hcore.transport Inv hInv) hp hm'⟩

/-- Full-state variant of `wp_safety_slice_func`. -/
theorem wp_safety_slice_func_full {as : List Ty} {body : Func as rs}
    {ι σ κ : Type} {sl : ι → SafetySlice σ κ}
    {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → σ → σ → Prop}
    (hf : ∀ xs m Q X, SafetySlice.spec sl Pre Post xs m Q X → Func.wp Γ body xs m Q X)
    {c : ι} {xs : Tup Val as} {s : σ} {R : Mem 64 → Prop} {m : Mem 64}
    {FullInv : σ → Prop}
    (hDep : DependsOnCoreAndSafe (sl c).coreProj (sl c).safe FullInv)
    (hFull : FullInv s)
    (hPre : Pre c xs s) (hSafe : (sl c).safe s) (hm : ((sl c).mem s ⋆ R) m)
    (hQ : ∀ r s' m', PreservesCoreSlice (sl c).coreProj s s' → (sl c).safe s' →
        FullInv s' → Post c xs r s s' → ((sl c).mem s' ⋆ R) m' → Q r m') :
    Func.wp Γ body xs m Q X :=
  hf xs m Q X ⟨c, s, R, hPre, hSafe, hm, fun r s' m' hcore hs' hp hm' =>
    hQ r s' m' hcore hs' (hDep s s' hcore hs' hFull) hp hm'⟩

/-- Discharge an `Expr.call` to a `SafetySlice.spec` callee and transport any core soundness
predicate `Inv ((sl c).coreProj s)` across the call in one step. -/
theorem wp_safety_slice_call {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {ι σ κ : Type} {sl : ι → SafetySlice σ κ}
    {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val bs → σ → σ → Prop}
    (hCallee : ∀ xs m Q X, SafetySlice.spec sl Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : ι} {s : σ} {R : Mem 64 → Prop}
    (Inv : κ → Prop) (hInv : Inv ((sl c).coreProj s))
    (hPre : Pre c (vals args) s) (hSafe : (sl c).safe s) (hm : ((sl c).mem s ⋆ R) m)
    (hk : ∀ r s' m', PreservesCoreSlice (sl c).coreProj s s' → (sl c).safe s' →
        Inv ((sl c).coreProj s') → Post c (vals args) r s s' → ((sl c).mem s' ⋆ R) m' →
        wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X ⟨c, s, R, hPre, hSafe, hm,
    fun r s' m' hcore hs' hp hm' =>
      hk r s' m' hcore hs' (hcore.transport Inv hInv) hp hm'⟩)

/-- Full-state variant of `wp_safety_slice_call` for `FullInv : σ → Prop` factoring through
`DependsOnCoreAndSafe`. -/
theorem wp_safety_slice_call_full {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {ι σ κ : Type} {sl : ι → SafetySlice σ κ}
    {Pre : ι → Tup Val as → σ → Prop}
    {Post : ι → Tup Val as → Tup Val bs → σ → σ → Prop}
    (hCallee : ∀ xs m Q X, SafetySlice.spec sl Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : ι} {s : σ} {R : Mem 64 → Prop}
    {FullInv : σ → Prop}
    (hDep : DependsOnCoreAndSafe (sl c).coreProj (sl c).safe FullInv)
    (hFull : FullInv s)
    (hPre : Pre c (vals args) s) (hSafe : (sl c).safe s) (hm : ((sl c).mem s ⋆ R) m)
    (hk : ∀ r s' m', PreservesCoreSlice (sl c).coreProj s s' → (sl c).safe s' →
        FullInv s' → Post c (vals args) r s s' → ((sl c).mem s' ⋆ R) m' →
        wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X ⟨c, s, R, hPre, hSafe, hm,
    fun r s' m' hcore hs' hp hm' =>
      hk r s' m' hcore hs' (hDep s s' hcore hs' hFull) hp hm'⟩)

/-- Unindexed shorthand for `wp_safety_slice_call` over `SafetySlice.spec0`. -/
theorem wp_safety_slice_call0 {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {σ κ : Type} {sl : SafetySlice σ κ}
    {Pre : Tup Val as → σ → Prop}
    {Post : Tup Val as → Tup Val bs → σ → σ → Prop}
    (hCallee : ∀ xs m Q X, SafetySlice.spec0 sl Pre Post xs m Q X → Γ f as bs xs m Q X)
    {s : σ} {R : Mem 64 → Prop}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s))
    (hPre : Pre (vals args) s) (hSafe : sl.safe s) (hm : (sl.mem s ⋆ R) m)
    (hk : ∀ r s' m', PreservesCoreSlice sl.coreProj s s' → sl.safe s' →
        Inv (sl.coreProj s') → Post (vals args) r s s' → (sl.mem s' ⋆ R) m' →
        wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_safety_slice_call (c := ()) hCallee Inv hInv hPre hSafe hm hk

/-- Loop rule over a `SafetySlice` (wrapping `C0Step.wp_loop_inv`): automatically maintains
`PreservesCoreSlice sl.coreProj s₀ s'`, `sl.safe s'`, and `(sl.mem s' ⋆ R) ml`, and delivers
`Inv (sl.coreProj s')` into every iteration without ever re-proving `Inv` on back-edges.
Memory precedes `μ`/`PreservesCoreSlice` on back-edges so `c0_frame` instantiates `s''` first. -/
theorem wp_loop_safety_slice {ts : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s₀))
    (LoopInv : σ → Tup Val ts → Prop)
    (μ : Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ s'' ys ml', (sl.mem s'' ⋆ R) ml' → μ ys < μ xs →
        PreservesCoreSlice sl.coreProj s' s'' → sl.safe s'' → LoopInv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_inv
    (fun xs ml => ∃ s', PreservesCoreSlice sl.coreProj s₀ s' ∧ sl.safe s' ∧
      LoopInv s' xs ∧ (sl.mem s' ⋆ R) ml)
    (fun xs _ => μ xs)
    (fun J hJ => hentry J fun s' xs ml hml hcore hs hli => hJ xs ml ⟨s', hcore, hs, hli, hml⟩)
    (fun J xs ml ⟨s', hcore, hs, hli, hml⟩ hJ =>
      hbody J s' xs ml hcore hs (hcore.transport Inv hInv) hli hml
        fun s'' ys ml' hml' hlt hstep hs' hli' =>
          hJ ys ml' hlt ⟨s'', hcore.trans hstep, hs', hli', hml'⟩)

/-- Pure safety-only loop rule over a `SafetySlice` (no external `Inv` needed inside the body). -/
theorem wp_loop_safety_slice_pure {ts : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (LoopInv : σ → Tup Val ts → Prop)
    (μ : Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ s'' ys ml', (sl.mem s'' ⋆ R) ml' → μ ys < μ xs →
        PreservesCoreSlice sl.coreProj s' s'' → sl.safe s'' → LoopInv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_safety_slice sl s₀ R (fun _ => True) trivial LoopInv μ hentry
    (fun J s' xs ml hcore hs _ hli hml hJ => hbody J s' xs ml hcore hs hli hml hJ)

/-- State-measure variant of `wp_loop_safety_slice` where `μ : σ → Tup Val ts → Nat` may depend
on struct fields (e.g. `s'.heap_len`, `s'.walk_flips`, `s'.fuel`). -/
theorem wp_loop_safety_slice_state {ts : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s₀))
    (LoopInv : σ → Tup Val ts → Prop)
    (μ : σ → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ s'' ys ml', (sl.mem s'' ⋆ R) ml' → μ s'' ys < μ s' xs →
        PreservesCoreSlice sl.coreProj s' s'' → sl.safe s'' → LoopInv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group
    (fun n xs ml => ∃ s', PreservesCoreSlice sl.coreProj s₀ s' ∧ sl.safe s' ∧
      LoopInv s' xs ∧ (sl.mem s' ⋆ R) ml ∧ μ s' xs = n)
    (fun J _ xs ml hJ ⟨s', hcore, hs, hli, hml, hμ⟩ =>
      hbody J s' xs ml hcore hs (hcore.transport Inv hInv) hli hml
        fun s'' ys ml' hml' hlt hstep hs' hli' =>
          hJ _ ys ml' (hμ ▸ hlt) ⟨s'', hcore.trans hstep, hs', hli', hml', rfl⟩)
    (fun J hJ => hentry J fun s' xs ml hml hcore hs hli =>
      hJ _ xs ml ⟨s', hcore, hs, hli, hml, rfl⟩)

/-- Pure state-measure safety-only loop rule over a `SafetySlice`. -/
theorem wp_loop_safety_slice_state_pure {ts : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (LoopInv : σ → Tup Val ts → Prop)
    (μ : σ → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ s'' ys ml', (sl.mem s'' ⋆ R) ml' → μ s'' ys < μ s' xs →
        PreservesCoreSlice sl.coreProj s' s'' → sl.safe s'' → LoopInv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_safety_slice_state sl s₀ R (fun _ => True) trivial LoopInv μ hentry
    (fun J s' xs ml hcore hs _ hli hml hJ => hbody J s' xs ml hcore hs hli hml hJ)

/-- Loop-with-break rule over a `SafetySlice`: transports `Inv (sl.coreProj s₀)` automatically
into both the loop body and the post-break continuation `hafter`. -/
theorem wp_loop_safety_slice_break {brkTs lpTs : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s₀))
    (BrkPost : σ → Tup Val brkTs → Prop)
    (LoopInv : σ → Tup Val lpTs → Prop)
    (μ : σ → Tup Val lpTs → Nat)
    (hafter : ∀ (B : Cont brkTs) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      BrkPost s' xs → (sl.mem s' ⋆ R) ml →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here xs) ml)
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ s'' r ml', (sl.mem s'' ⋆ R) ml' → PreservesCoreSlice sl.coreProj s' s'' →
        sl.safe s'' → BrkPost s'' r → B r ml') →
      (∀ s'' ys ml', (sl.mem s'' ⋆ R) ml' → μ s'' ys < μ s' xs →
        PreservesCoreSlice sl.coreProj s' s'' → sl.safe s'' → LoopInv s'' ys → L ys ml') →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here xs) ml)
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ s' r ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → BrkPost s' r → B r ml) →
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → L xs ml) →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_loop_break_group
    (fun xs ml => ∃ s', PreservesCoreSlice sl.coreProj s₀ s' ∧ sl.safe s' ∧
      BrkPost s' xs ∧ (sl.mem s' ⋆ R) ml)
    (fun n xs ml => ∃ s', PreservesCoreSlice sl.coreProj s₀ s' ∧ sl.safe s' ∧
      LoopInv s' xs ∧ (sl.mem s' ⋆ R) ml ∧ μ s' xs = n)
    (fun B xs ml ⟨s', hcore, hs, hb, hml⟩ =>
      hafter B s' xs ml hcore hs (hcore.transport Inv hInv) hb hml)
    (fun B L _ xs ml hB hL ⟨s', hcore, hs, hli, hml, hμ⟩ =>
      hbody B L s' xs ml hcore hs (hcore.transport Inv hInv) hli hml
        (fun s'' r ml' hml' hstep hs' hb' => hB r ml' ⟨s'', hcore.trans hstep, hs', hb', hml'⟩)
        (fun s'' ys ml' hml' hlt hstep hs' hli' =>
          hL _ ys ml' (hμ ▸ hlt) ⟨s'', hcore.trans hstep, hs', hli', hml', rfl⟩))
    (fun B L hB hL =>
      hentry B L
        (fun s' r ml hml hcore hs hb => hB r ml ⟨s', hcore, hs, hb, hml⟩)
        (fun s' xs ml hml hcore hs hli => hL _ xs ml ⟨s', hcore, hs, hli, hml, rfl⟩))

/-- Forward join-point rule over a `SafetySlice`, transporting `Inv (sl.coreProj s₀)` across
control-flow merges. -/
theorem wp_join_safety_slice {ts : List Ty} {m : Mem 64} {σ κ : Type}
    (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s₀))
    (P : σ → Tup Val ts → Prop)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      P s' xs → (sl.mem s' ⋆ R) ml →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → P s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group
    (fun xs ml => ∃ s', PreservesCoreSlice sl.coreProj s₀ s' ∧ sl.safe s' ∧
      P s' xs ∧ (sl.mem s' ⋆ R) ml)
    (fun J xs ml ⟨s', hcore, hs, hp, hml⟩ =>
      hbody J s' xs ml hcore hs (hcore.transport Inv hInv) hp hml)
    (fun J hJ => hentry J fun s' xs ml hml hcore hs hp => hJ xs ml ⟨s', hcore, hs, hp, hml⟩)

end SafetySliceWP

/-! ## 5. Scoped `simp` / `grind` bundle (`LeanQbe.T.C0Agrees`) -/

namespace C0Agrees

attribute [scoped simp]
  agreesExcept_refl
  preservesCoreSlice_refl
  PrefixAgrees.refl
  SliceAgrees.refl
  OutsideSliceAgrees.refl
  SafetySlice.ofMask_mem
  SafetySlice.ofMask_coreProj
  SafetySlice.ofMask_safe
  SafetySlice.ofPair_mem
  SafetySlice.ofPair_coreProj
  SafetySlice.ofPair_safe
  getElem?_getD_set_eq
  getElem?_getD_set_ne

attribute [scoped grind =]
  agreesExcept_iff
  preservesCoreSlice_iff
  getElem?_getD_set_eq
  getElem?_getD_set_ne
  SafetySlice.ofMask_mem
  SafetySlice.ofMask_coreProj
  SafetySlice.ofMask_safe
  SafetySlice.ofPair_mem
  SafetySlice.ofPair_coreProj
  SafetySlice.ofPair_safe

scoped grind_pattern PrefixAgrees.getElem?_eq => PrefixAgrees n xs ys, ys[i]?
scoped grind_pattern PrefixAgrees.getElem?_eq => PrefixAgrees n xs ys, xs[i]?
scoped grind_pattern SliceAgrees.getElem?_eq => SliceAgrees lo hi xs ys, ys[i]?
scoped grind_pattern SliceAgrees.getElem?_eq => SliceAgrees lo hi xs ys, xs[i]?
scoped grind_pattern OutsideSliceAgrees.getElem?_lt => OutsideSliceAgrees lo hi xs ys, ys[i]?
scoped grind_pattern OutsideSliceAgrees.getElem?_lt => OutsideSliceAgrees lo hi xs ys, xs[i]?
scoped grind_pattern OutsideSliceAgrees.getElem?_ge => OutsideSliceAgrees lo hi xs ys, ys[i]?
scoped grind_pattern OutsideSliceAgrees.getElem?_ge => OutsideSliceAgrees lo hi xs ys, xs[i]?

/-- Strip wrapper `mdata` from a `Func.wp` / `wp` goal (e.g. after `unfold`/`dsimp at h`) so
`c0_steps` recognizes the head symbol without prematurely unfolding `Func.wp`. -/
scoped macro "c0_strip_mdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _ | skip)

/-- `c0_steps` after stripping any `mdata` wrapper left by `unfold`/`dsimp at h`. -/
scoped macro "c0_agrees_steps" : tactic =>
  `(tactic| (c0_strip_mdata; c0_steps))

/-- Strict `c0_steps!` after stripping any `mdata` wrapper left by `unfold`/`dsimp at h`. -/
scoped macro "c0_agrees_steps!" : tactic =>
  `(tactic| (c0_strip_mdata; c0_steps!))

end C0Agrees

end LeanQbe.T
