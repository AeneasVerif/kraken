/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Minimize
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Cdcl

/-!
# Soundness Proofs for `Minimize`

Extracted pure-Lean proofs for `Minimize` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Lazy-level filtering backtrack -/

private def filterIdxMap {α : Type} (p : α → Bool) : List α → Nat → Nat
  | [], _ => 0
  | x :: xs, i' =>
    if p x then
      match i' with
      | 0 => 0
      | k + 1 => filterIdxMap p xs k + 1
    else
      filterIdxMap p xs i' + 1

private theorem filterIdxMap_props {α : Type} (p : α → Bool) (xs : List α) :
    ∀ i' (hi' : i' < (xs.filter p).length),
      ∃ (hi : filterIdxMap p xs i' < xs.length),
        (xs.filter p)[i'] = xs[filterIdxMap p xs i'] ∧ p xs[filterIdxMap p xs i'] = true := by
  induction xs with
  | nil => intro i' hi'; simp at hi'
  | cons x xs ih =>
    intro i' hi'
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, ↓reduceIte] at hi' ⊢
      cases i' with
      | zero =>
        have hlt : filterIdxMap p (x :: xs) 0 < (x :: xs).length := by simp [filterIdxMap, hpx]
        exact ⟨hlt, by simp [filterIdxMap, hpx], by simp [filterIdxMap, hpx]⟩
      | succ k =>
        obtain ⟨hk, heq, hp⟩ := ih k (by simpa using hi')
        have hlt : filterIdxMap p (x :: xs) (k + 1) < (x :: xs).length := by
          simp [filterIdxMap, hpx]; omega
        refine ⟨hlt, ?_, ?_⟩
        · simpa [filterIdxMap, hpx] using heq
        · simpa [filterIdxMap, hpx] using hp
    · have hpf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ↓reduceIte] at hi' ⊢
      obtain ⟨hi, heq, hp⟩ := ih i' hi'
      have hlt : filterIdxMap p (x :: xs) i' < (x :: xs).length := by
        simp [filterIdxMap, hpf]; omega
      refine ⟨hlt, ?_, ?_⟩
      · simpa [filterIdxMap, hpf] using heq
      · simpa [filterIdxMap, hpf] using hp

private theorem filterIdxMap_strictMono {α : Type} (p : α → Bool) (xs : List α) :
    ∀ i' j', i' < j' → j' < (xs.filter p).length →
      filterIdxMap p xs i' < filterIdxMap p xs j' := by
  induction xs with
  | nil => intro _ _ _ hj'; simp at hj'
  | cons x xs ih =>
    intro i' j' hij hj'
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, ↓reduceIte] at hj'
      cases i' with
      | zero =>
        cases j' with
        | zero => omega
        | succ m => simp [filterIdxMap, hpx]
      | succ k =>
        cases j' with
        | zero => omega
        | succ m =>
          simp only [filterIdxMap, hpx, ↓reduceIte]
          exact Nat.succ_lt_succ (ih k m (by omega) (by simpa using hj'))
    · have hpf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ↓reduceIte] at hj'
      simp only [filterIdxMap, hpf, Bool.false_eq_true, ↓reduceIte]
      exact Nat.succ_lt_succ (ih i' j' hij hj')

private theorem filterIdxMap_surj_lt {α : Type} (p : α → Bool) (xs : List α) :
    ∀ i' (hi' : i' < (xs.filter p).length) (j : Nat) (hj : j < filterIdxMap p xs i'),
      p (xs[j]'(Nat.lt_trans hj (filterIdxMap_props p xs i' hi').1)) = true →
      ∃ (j' : Nat) (_hj' : j' < i'), filterIdxMap p xs j' = j := by
  induction xs with
  | nil => intro _ hi'; simp at hi'
  | cons x xs ih =>
    intro i' hi' j hj hjp
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, ↓reduceIte] at hi'
      cases i' with
      | zero => simp [filterIdxMap, hpx] at hj
      | succ k =>
        simp only [filterIdxMap, hpx, ↓reduceIte] at hj
        cases j with
        | zero => exact ⟨0, Nat.zero_lt_succ k, by simp [filterIdxMap, hpx]⟩
        | succ m =>
          obtain ⟨j', hj'lt, hj'eq⟩ := ih k (by simpa using hi') m (by omega) hjp
          exact ⟨j' + 1, Nat.succ_lt_succ hj'lt, by simp [filterIdxMap, hpx, hj'eq]⟩
    · have hpf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ↓reduceIte] at hi'
      simp only [filterIdxMap, hpf, Bool.false_eq_true, ↓reduceIte] at hj
      cases j with
      | zero => exact absurd hjp (by simpa using hpx)
      | succ m =>
        obtain ⟨j', hj'lt, hj'eq⟩ := ih i' hi' m (by omega) hjp
        exact ⟨j', hj'lt, by simp [filterIdxMap, hpf, hj'eq]⟩

/-- Filtering backtrack preserves `LazyTrailInv` and `f0` under lazy assignment levels. -/
theorem backtrackFilter_preserves_lazyInv {s : CdclState} (hinv : LazyTrailInv s)
    (targetLevel : Nat) :
    LazyTrailInv (backtrackFilter s targetLevel) ∧
      (backtrackFilter s targetLevel).f0 = s.f0 := by
  let p : Nat → Bool := fun l => decide (stateLevel s l ≤ targetLevel)
  have hlen : (backtrackFilter s targetLevel).trail.size = (s.trail.toList.filter p).length := by
    simp [backtrackFilter, p]
  have hget : ∀ i' (hi' : i' < (backtrackFilter s targetLevel).trail.size),
      (backtrackFilter s targetLevel).trail[i'] = s.trail[filterIdxMap p s.trail.toList i']'(by
        have h1 := (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).1
        simpa using h1) := by
    intro i' hi'
    have hp := (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).2.1
    simpa [backtrackFilter, p] using hp
  refine ⟨⟨?_, ?_, ?_, hinv.db_sound, hinv.units_sound, ?_, hinv.inconsistent_sound⟩, rfl⟩
  · intro i' j' hi' hj' hvar
    rw [hget i' hi', hget j' hj'] at hvar
    have heq := hinv.vars_nodup _ _ _ _ hvar
    rcases Nat.lt_trichotomy i' j' with hlt | rfl | hgt
    · have hfm := filterIdxMap_strictMono p s.trail.toList i' j' hlt (hlen ▸ hj')
      omega
    · rfl
    · have hfm := filterIdxMap_strictMono p s.trail.toList j' i' hgt (hlen ▸ hi')
      omega
  · intro i' hi'
    change stateLevel s (backtrackFilter s targetLevel).trail[i'] ≤ Nat.min s.level targetLevel
    rw [hget i' hi']
    have hi_sz : filterIdxMap p s.trail.toList i' < s.trail.size := by
      have := (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).1; simpa using this
    have h1 := hinv.levels_le _ hi_sz
    have h2 : p (s.trail.toList[filterIdxMap p s.trail.toList i']'(filterIdxMap_props p
        s.trail.toList i' (hlen ▸ hi')).1) = true :=
      (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).2.2
    have h2' : stateLevel s s.trail[filterIdxMap p s.trail.toList i'] ≤ targetLevel := by
      simpa [p] using h2
    exact Nat.le_min.mpr ⟨h1, h2'⟩
  · intro i' j' hi' hj' hleq hrsn
    change stateLevel s (backtrackFilter s targetLevel).trail[i'] =
      stateLevel s (backtrackFilter s targetLevel).trail[j'] at hleq
    change stateReason s (backtrackFilter s targetLevel).trail[j'] = .decision at hrsn
    rw [hget i' hi', hget j' hj'] at hleq
    rw [hget j' hj'] at hrsn
    have hle := hinv.dec_earliest _ _ _ _ hleq hrsn
    exact Classical.byContradiction fun hnot => by
      have hgt : i' < j' := Nat.lt_of_not_le hnot
      have hfm := filterIdxMap_strictMono p s.trail.toList i' j' hgt (hlen ▸ hj')
      omega
  · intro i' hi'
    let i := filterIdxMap p s.trail.toList i'
    have hi_list : i < s.trail.toList.length :=
      (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).1
    have hi : i < s.trail.size := by simpa using hi_list
    have hrd := hinv.reason_dag i hi; dsimp only at hrd
    have hst_r : stateReason (backtrackFilter s targetLevel)
        (backtrackFilter s targetLevel).trail[i'] = stateReason s s.trail[i] := by
      change stateReason s (backtrackFilter s targetLevel).trail[i'] = stateReason s s.trail[i]
      rw [hget i' hi']
    change match stateReason (backtrackFilter s targetLevel)
        (backtrackFilter s targetLevel).trail[i'] with | _ => _
    rw [hst_r]
    generalize hrsn : stateReason s s.trail[i] = rsn; rw [hrsn] at hrd
    cases rsn with
    | decision =>
      change 0 < stateLevel s (backtrackFilter s targetLevel).trail[i']
      rw [hget i' hi']; exact hrd
    | unit =>
      change stateLevel s (backtrackFilter s targetLevel).trail[i'] = 0 ∧
        s.f0.EntailsClause (cnfClause [(backtrackFilter s targetLevel).trail[i']])
      rw [hget i' hi']; exact hrd
    | binary other =>
      obtain ⟨hbin, j, hj, hjlt, hjeq, hle, hlex⟩ := hrd
      have hpj : p (s.trail.toList[j]'(by simpa using hj)) = true := by
        simp only [p, Array.getElem_toList, decide_eq_true_eq]
        have heq_other : stateLevel s s.trail[j] = stateLevel s other := by
          rw [hjeq, stateLevel_litNeg]
        have hp_i : stateLevel s s.trail[i] ≤ targetLevel := by
          have hp := (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).2.2
          simpa [p] using hp
        omega
      obtain ⟨j', hj'lt, hj'eq⟩ :=
        filterIdxMap_surj_lt p s.trail.toList i' (hlen ▸ hi') j hjlt hpj
      have hj'sz : j' < (backtrackFilter s targetLevel).trail.size := Nat.lt_trans hj'lt hi'
      refine ⟨?_, j', hj'sz, hj'lt, ?_, ?_, ?_⟩
      · change s.f0.EntailsClause (cnfClause [(backtrackFilter s targetLevel).trail[i'], other])
        rw [hget i' hi']; exact hbin
      · rw [hget j' hj'sz]; simpa [hj'eq] using hjeq
      · change stateLevel s other ≤ stateLevel s (backtrackFilter s targetLevel).trail[i']
        rw [hget i' hi']; exact hle
      · change lexLt (stateLevel s other) j'
          (stateLevel s (backtrackFilter s targetLevel).trail[i']) i'
        rw [hget i' hi']
        rcases hlex with hlt | ⟨heql, _⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨heql, hj'lt⟩
    | large cid =>
      obtain ⟨c, hget_c, hng, hlmem, hall⟩ := hrd
      refine ⟨c, hget_c, hng, ?_, fun x hx hne => ?_⟩
      · rw [hget i' hi']; exact hlmem
      · have hne' : x ≠ s.trail[i] := by rw [← hget i' hi']; exact hne
        obtain ⟨j, hj, hjlt, hjeq, hle, hlex⟩ := hall x hx hne'
        have hpj : p (s.trail.toList[j]'(by simpa using hj)) = true := by
          simp only [p, Array.getElem_toList, decide_eq_true_eq]
          have heq_x : stateLevel s s.trail[j] = stateLevel s x := by
            rw [hjeq, stateLevel_litNeg]
          have hp_i : stateLevel s s.trail[i] ≤ targetLevel := by
            have hp := (filterIdxMap_props p s.trail.toList i' (hlen ▸ hi')).2.2
            simpa [p] using hp
          omega
        obtain ⟨j', hj'lt, hj'eq⟩ :=
          filterIdxMap_surj_lt p s.trail.toList i' (hlen ▸ hi') j hjlt hpj
        have hj'sz : j' < (backtrackFilter s targetLevel).trail.size := Nat.lt_trans hj'lt hi'
        refine ⟨j', hj'sz, hj'lt, ?_, ?_, ?_⟩
        · rw [hget j' hj'sz]; simpa [hj'eq] using hjeq
        · change stateLevel s x ≤ stateLevel s (backtrackFilter s targetLevel).trail[i']
          rw [hget i' hi']; exact hle
        · change lexLt (stateLevel s x) j'
            (stateLevel s (backtrackFilter s targetLevel).trail[i']) i'
          rw [hget i' hi']
          rcases hlex with hlt | ⟨heql, _⟩
          · exact Or.inl hlt
          · exact Or.inr ⟨heql, hj'lt⟩

/-! ## 2. Trail-indexed `MinState` and lexicographic `(level, trailPos)` preorder -/

@[simp] theorem MinState.cdcl_setRemovable (s : MinState) (v : Nat) (b : Bool) :
    (s.setRemovable v b).cdcl = s.cdcl := rfl

@[simp] theorem MinState.trailPos_setRemovable (s : MinState) (v : Nat) (b : Nat → Bool) :
    (s.setRemovable v (b v)).trailPos = s.trailPos := rfl

@[simp] theorem MinState.varLevel_setRemovable (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setRemovable v b).varLevel w = s.varLevel w := rfl

@[simp] theorem MinState.litLevel_setRemovable (s : MinState) (v : Nat) (b : Bool) (l : Nat) :
    (s.setRemovable v b).litLevel l = s.litLevel l := rfl

@[simp] theorem MinState.varTrailPos_setRemovable (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setRemovable v b).varTrailPos w = s.varTrailPos w := rfl

@[simp] theorem MinState.isRemovable_setRemovable (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setRemovable v b).isRemovable w = if w = v then b else s.isRemovable w :=
  arraySetPad_getD s.removable v b false w

@[simp] theorem MinState.cdcl_setPoisoned (s : MinState) (v : Nat) (b : Bool) :
    (s.setPoisoned v b).cdcl = s.cdcl := rfl

@[simp] theorem MinState.trailPos_setPoisoned (s : MinState) (v : Nat) (b : Bool) :
    (s.setPoisoned v b).trailPos = s.trailPos := rfl

@[simp] theorem MinState.removable_setPoisoned (s : MinState) (v : Nat) (b : Bool) :
    (s.setPoisoned v b).removable = s.removable := rfl

@[simp] theorem MinState.isRemovable_setPoisoned (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setPoisoned v b).isRemovable w = s.isRemovable w := rfl

@[simp] theorem MinState.isPoisoned_setPoisoned (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setPoisoned v b).isPoisoned w = if w = v then b else s.isPoisoned w :=
  arraySetPad_getD s.poisoned v b false w

@[simp] theorem MinState.cdcl_setShrinkable (s : MinState) (v : Nat) (b : Bool) :
    (s.setShrinkable v b).cdcl = s.cdcl := rfl

@[simp] theorem MinState.trailPos_setShrinkable (s : MinState) (v : Nat) (b : Bool) :
    (s.setShrinkable v b).trailPos = s.trailPos := rfl

@[simp] theorem MinState.removable_setShrinkable (s : MinState) (v : Nat) (b : Bool) :
    (s.setShrinkable v b).removable = s.removable := rfl

@[simp] theorem MinState.isRemovable_setShrinkable (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setShrinkable v b).isRemovable w = s.isRemovable w := rfl

@[simp] theorem MinState.isShrinkable_setShrinkable (s : MinState) (v : Nat) (b : Bool) (w : Nat) :
    (s.setShrinkable v b).isShrinkable w = if w = v then b else s.isShrinkable w :=
  arraySetPad_getD s.shrinkable v b false w

@[simp] theorem MinState.cdcl_resetPoisoned (s : MinState) : s.resetPoisoned.cdcl = s.cdcl := rfl

@[simp] theorem MinState.trailPos_resetPoisoned (s : MinState) :
    s.resetPoisoned.trailPos = s.trailPos := rfl

@[simp] theorem MinState.isRemovable_resetPoisoned (s : MinState) (w : Nat) :
    s.resetPoisoned.isRemovable w = s.isRemovable w := rfl

@[simp] theorem MinState.isPoisoned_resetPoisoned (s : MinState) (w : Nat) :
    s.resetPoisoned.isPoisoned w = false := by
  simp only [MinState.isPoisoned, MinState.resetPoisoned, Array.getD_eq_getD_getElem?]
  cases h : (Array.replicate s.poisoned.size false)[w]? with
  | none => rfl
  | some b =>
    simp only [Array.getElem?_replicate] at h
    split at h <;> simp_all

@[simp] theorem MinState.cdcl_resetShrinkable (s : MinState) :
    s.resetShrinkable.cdcl = s.cdcl := rfl

@[simp] theorem MinState.trailPos_resetShrinkable (s : MinState) :
    s.resetShrinkable.trailPos = s.trailPos := rfl

@[simp] theorem MinState.isRemovable_resetShrinkable (s : MinState) (w : Nat) :
    s.resetShrinkable.isRemovable w = s.isRemovable w := rfl

@[simp] theorem MinState.isShrinkable_resetShrinkable (s : MinState) (w : Nat) :
    s.resetShrinkable.isShrinkable w = false := by
  simp only [MinState.isShrinkable, MinState.resetShrinkable, Array.getD_eq_getD_getElem?]
  cases h : (Array.replicate s.shrinkable.size false)[w]? with
  | none => rfl
  | some b =>
    simp only [Array.getElem?_replicate] at h
    split at h <;> simp_all

@[simp] theorem MinState.isRemovable_resetRemovable (s : MinState) (w : Nat) :
    s.resetRemovable.isRemovable w = false := by
  simp only [MinState.isRemovable, MinState.resetRemovable, Array.getD_eq_getD_getElem?]
  cases h : (Array.replicate s.removable.size false)[w]? with
  | none => rfl
  | some b =>
    simp only [Array.getElem?_replicate] at h
    split at h <;> simp_all

private theorem buildTrailPos_go_inv (trail : Array Nat)
    (hnodup : ∀ i j, (hi : i < trail.size) → (hj : j < trail.size) →
      litVar trail[i] = litVar trail[j] → i = j) :
    ∀ i acc, (∀ k (_hk : k < i) (_hkt : k < trail.size), acc.getD (litVar trail[k]) 0 = k) →
      ∀ j (hj : j < trail.size), (buildTrailPos.go trail i acc).getD (litVar trail[j]) 0 = j := by
  intro i
  have hsub : ∀ n i acc, trail.size - i ≤ n →
      (∀ k (hk : k < i) (_hkt : k < trail.size), acc.getD (litVar trail[k]) 0 = k) →
      ∀ j (hj : j < trail.size), (buildTrailPos.go trail i acc).getD (litVar trail[j]) 0 = j := by
    intro n
    induction n with
    | zero =>
      intro i acc hle hinv j hj
      unfold buildTrailPos.go
      rw [dite_eq_right (by omega : ¬ i < trail.size)]
      exact hinv j (by omega) hj
    | succ n ih =>
      intro i acc hle hinv j hj
      unfold buildTrailPos.go
      by_cases hlt : i < trail.size
      · rw [dite_eq_left hlt]
        refine ih (i + 1) _ (by omega) (fun k hk hkt => ?_) j hj
        rw [arraySetPad_getD]
        by_cases hki : k = i
        · subst hki; simp
        · have hne : litVar trail[k] ≠ litVar trail[i] := fun heq =>
            hki (hnodup k i hkt hlt heq)
          simp [hne, hinv k (by omega) hkt]
      · rw [dite_eq_right hlt]
        exact hinv j (by omega) hj
  exact fun acc hinv j hj => hsub (trail.size - i) i acc (Nat.le_refl _) hinv j hj

theorem trailPosInv_ofCdcl {cdcl : CdclState}
    (hnodup : ∀ i j, (hi : i < cdcl.trail.size) → (hj : j < cdcl.trail.size) →
      litVar cdcl.trail[i] = litVar cdcl.trail[j] → i = j)
    (frameUsed : Array Nat := #[]) :
    TrailPosInv cdcl (MinState.ofCdcl cdcl frameUsed).trailPos :=
  buildTrailPos_go_inv cdcl.trail hnodup 0 #[] (fun _ hk => by omega)

theorem MinBaseInv.ofCdcl {cdcl : CdclState} (hinv : LazyTrailInv cdcl)
    (frameUsed : Array Nat := #[]) :
    MinBaseInv (MinState.ofCdcl cdcl frameUsed) :=
  ⟨hinv, trailPosInv_ofCdcl hinv.vars_nodup frameUsed⟩

theorem MinBaseInv.setRemovable {s : MinState} (h : MinBaseInv s) (v : Nat) (b : Bool) :
    MinBaseInv (s.setRemovable v b) := ⟨h.trail_inv, h.pos_inv⟩

theorem MinBaseInv.setPoisoned {s : MinState} (h : MinBaseInv s) (v : Nat) (b : Bool) :
    MinBaseInv (s.setPoisoned v b) := ⟨h.trail_inv, h.pos_inv⟩

theorem MinBaseInv.setShrinkable {s : MinState} (h : MinBaseInv s) (v : Nat) (b : Bool) :
    MinBaseInv (s.setShrinkable v b) := ⟨h.trail_inv, h.pos_inv⟩

theorem MinBaseInv.resetPoisoned {s : MinState} (h : MinBaseInv s) :
    MinBaseInv s.resetPoisoned := ⟨h.trail_inv, h.pos_inv⟩

theorem MinBaseInv.resetShrinkable {s : MinState} (h : MinBaseInv s) :
    MinBaseInv s.resetShrinkable := ⟨h.trail_inv, h.pos_inv⟩

theorem varLe_refl (s : MinState) (v : Nat) : varLe s v v :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

theorem varLe_trans {s : MinState} {u v w : Nat}
    (h1 : varLe s u v) (h2 : varLe s v w) : varLe s u w := by
  rcases h1 with h1l | ⟨h1e, h1p⟩ <;> rcases h2 with h2l | ⟨h2e, h2p⟩
  · exact Or.inl (Nat.lt_trans h1l h2l)
  · exact Or.inl (h2e ▸ h1l)
  · exact Or.inl (h1e ▸ h2l)
  · exact Or.inr ⟨h1e.trans h2e, Nat.le_trans h1p h2p⟩

theorem varLt_of_varLe_varLt {s : MinState} {u v w : Nat}
    (h1 : varLe s u v) (h2 : varLt s v w) : varLt s u w := by
  rcases h1 with h1l | ⟨h1e, h1p⟩ <;> rcases h2 with h2l | ⟨h2e, h2p⟩
  · exact Or.inl (Nat.lt_trans h1l h2l)
  · exact Or.inl (h2e ▸ h1l)
  · exact Or.inl (h1e ▸ h2l)
  · exact Or.inr ⟨h1e.trans h2e, Nat.lt_of_le_of_lt h1p h2p⟩

theorem varLt_trans {s : MinState} {u v w : Nat}
    (h1 : varLt s u v) (h2 : varLt s v w) : varLt s u w :=
  varLt_of_varLe_varLt (Or.imp_right (fun ⟨e, p⟩ => ⟨e, Nat.le_of_lt p⟩) h1) h2

theorem varLt.to_varLe {s : MinState} {u v : Nat} (h : varLt s u v) : varLe s u v :=
  Or.imp_right (fun ⟨e, p⟩ => ⟨e, Nat.le_of_lt p⟩) h

theorem varLt_irrefl {s : MinState} {v : Nat} : ¬ varLt s v v := by
  intro h; rcases h with h | ⟨_, h⟩ <;> omega

theorem not_varLe_of_varLt {s : MinState} {u v : Nat}
    (h : varLt s u v) : ¬ varLe s v u := by
  intro hle
  rcases h with h1 | ⟨he1, hp1⟩ <;> rcases hle with h2 | ⟨he2, hp2⟩ <;> omega

theorem varLtLit_iff {s : MinState} {l1 l2 : Nat} :
    varLtLit s l1 l2 = true ↔ varLt s (litVar l1) (litVar l2) := by
  by_cases h1 : s.varLevel (litVar l1) < s.varLevel (litVar l2) <;>
    by_cases h2 : s.varLevel (litVar l1) = s.varLevel (litVar l2) <;>
    by_cases h3 : s.varTrailPos (litVar l1) < s.varTrailPos (litVar l2) <;>
    simp [varLtLit, varLt, MinState.litLevel, MinState.litTrailPos, h1, h2, h3]

@[simp] theorem varLe_setRemovable (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLe (s.setRemovable v b) u w ↔ varLe s u w := Iff.rfl

@[simp] theorem varLt_setRemovable (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLt (s.setRemovable v b) u w ↔ varLt s u w := Iff.rfl

@[simp] theorem varLe_setPoisoned (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLe (s.setPoisoned v b) u w ↔ varLe s u w := Iff.rfl

@[simp] theorem varLt_setPoisoned (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLt (s.setPoisoned v b) u w ↔ varLt s u w := Iff.rfl

@[simp] theorem varLe_resetPoisoned (s : MinState) (u w : Nat) :
    varLe s.resetPoisoned u w ↔ varLe s u w := Iff.rfl

@[simp] theorem varLt_resetPoisoned (s : MinState) (u w : Nat) :
    varLt s.resetPoisoned u w ↔ varLt s u w := Iff.rfl

@[simp] theorem varLe_setShrinkable (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLe (s.setShrinkable v b) u w ↔ varLe s u w := Iff.rfl

@[simp] theorem varLt_setShrinkable (s : MinState) (v : Nat) (b : Bool) (u w : Nat) :
    varLt (s.setShrinkable v b) u w ↔ varLt s u w := Iff.rfl

theorem trailPos_eq_of_mem {s : MinState} (h : MinBaseInv s) {i : Nat}
    (hi : i < s.cdcl.trail.size) :
    s.varTrailPos (litVar s.cdcl.trail[i]) = i :=
  h.pos_inv i hi

theorem trail_idx_unique_of_var {s : MinState} (h : MinBaseInv s) {i j : Nat}
    (hi : i < s.cdcl.trail.size) (hj : j < s.cdcl.trail.size)
    (heq : litVar s.cdcl.trail[i] = litVar s.cdcl.trail[j]) : i = j :=
  h.trail_inv.vars_nodup i j hi hj heq

/-- Under `MinBaseInv` (with lazy levels), `ReasonDagInv` forces every antecedent `x` to have
`s.litLevel x ≤ s.litLevel t`, `litTrailPos x < litTrailPos t`, and `varLt` order. -/
theorem reason_antecedent_varLt {s : MinState} (h : MinBaseInv s) {i : Nat}
    (hi : i < s.cdcl.trail.size) :
    match stateReason s.cdcl s.cdcl.trail[i] with
    | .decision => 0 < s.litLevel s.cdcl.trail[i]
    | .unit =>
      s.litLevel s.cdcl.trail[i] = 0 ∧ s.cdcl.f0.EntailsClause (cnfClause [s.cdcl.trail[i]])
    | .binary other =>
      s.cdcl.f0.EntailsClause (cnfClause [s.cdcl.trail[i], other]) ∧
      ∃ (j : Nat) (hj : j < s.cdcl.trail.size), j < i ∧
        s.cdcl.trail[j] = litNeg other ∧ s.litLevel other ≤ s.litLevel s.cdcl.trail[i] ∧
        varLt s (litVar other) (litVar s.cdcl.trail[i])
    | .large cid =>
      ∃ c : Clause, s.cdcl.clauses[cid]? = some (some c) ∧ !c.garbage = true ∧
        s.cdcl.trail[i] ∈ c.lits ∧
        ∀ x ∈ c.lits, x ≠ s.cdcl.trail[i] →
          ∃ (j : Nat) (hj : j < s.cdcl.trail.size), j < i ∧
            s.cdcl.trail[j] = litNeg x ∧ s.litLevel x ≤ s.litLevel s.cdcl.trail[i] ∧
            varLt s (litVar x) (litVar s.cdcl.trail[i]) := by
  have hrd := h.trail_inv.reason_dag i hi; dsimp only at hrd
  have hpi : s.varTrailPos (litVar s.cdcl.trail[i]) = i := h.pos_inv i hi
  generalize hrsn : stateReason s.cdcl s.cdcl.trail[i] = rsn; rw [hrsn] at hrd
  cases rsn with
  | decision | unit => exact hrd
  | binary other =>
    obtain ⟨hbin, j, hj, hjlt, hjeq, hle, _⟩ := hrd
    have hpj : s.varTrailPos (litVar other) = j := by
      have := h.pos_inv j hj
      simpa [MinState.varTrailPos, hjeq, litVar_litNeg] using this
    refine ⟨hbin, j, hj, hjlt, hjeq, hle, ?_⟩
    by_cases hlt : s.litLevel other < s.litLevel s.cdcl.trail[i]
    · exact Or.inl hlt
    · have heql : s.varLevel (litVar other) = s.varLevel (litVar s.cdcl.trail[i]) := by
        simp only [MinState.litLevel, MinState.varLevel, stateLevel] at hlt hle ⊢; omega
      exact Or.inr ⟨heql, by rw [hpj, hpi]; exact hjlt⟩
  | large cid =>
    obtain ⟨c, hget, hng, hlmem, hall⟩ := hrd
    refine ⟨c, hget, hng, hlmem, fun x hx hne => ?_⟩
    obtain ⟨j, hj, hjlt, hjeq, hle, _⟩ := hall x hx hne
    have hpj : s.varTrailPos (litVar x) = j := by
      have := h.pos_inv j hj
      simpa [MinState.varTrailPos, hjeq, litVar_litNeg] using this
    refine ⟨j, hj, hjlt, hjeq, hle, ?_⟩
    by_cases hlt : s.litLevel x < s.litLevel s.cdcl.trail[i]
    · exact Or.inl hlt
    · have heql : s.varLevel (litVar x) = s.varLevel (litVar s.cdcl.trail[i]) := by
        simp only [MinState.litLevel, MinState.varLevel, stateLevel] at hlt hle ⊢; omega
      exact Or.inr ⟨heql, by rw [hpj, hpi]; exact hjlt⟩

/-! ## 3. Lexicographic `RemovableInv`, seeding, poison/depth safety, caching, and cut deletion -/

theorem removableInv_of_all_false {s : MinState} (h : ∀ v, s.isRemovable v = false)
    (C : List Nat) : s.RemovableInv C := fun v hv => by simp [h v] at hv

theorem removableInv_of_ofCdcl (cdcl : CdclState) (frameUsed : Array Nat := #[])
    (C : List Nat) : (MinState.ofCdcl cdcl frameUsed).RemovableInv C :=
  removableInv_of_all_false (fun v => by
    simp only [MinState.isRemovable, MinState.ofCdcl, Array.getD_eq_getD_getElem?]
    cases h : (Array.replicate cdcl.numVars false)[v]? with
    | none => rfl
    | some b =>
      simp only [Array.getElem?_replicate] at h
      split at h <;> simp_all) C

/-- (b) Poisoned, shrinkable, and depth-limit failure invariance: modifying `poisoned` or
`shrinkable`, or resetting them, never violates `RemovableInv`. -/
theorem removableInv_setPoisoned {s : MinState} {C : List Nat} {v : Nat} {b : Bool} :
    (s.setPoisoned v b).RemovableInv C ↔ s.RemovableInv C := Iff.rfl

theorem removableInv_resetPoisoned {s : MinState} {C : List Nat} :
    s.resetPoisoned.RemovableInv C ↔ s.RemovableInv C := by
  simp [MinState.RemovableInv, MinState.varLevel, MinState.varTrailPos, varLe]

theorem removableInv_setShrinkable {s : MinState} {C : List Nat} {v : Nat} {b : Bool} :
    (s.setShrinkable v b).RemovableInv C ↔ s.RemovableInv C := Iff.rfl

theorem removableInv_resetShrinkable {s : MinState} {C : List Nat} :
    s.resetShrinkable.RemovableInv C ↔ s.RemovableInv C := by
  simp [MinState.RemovableInv, MinState.varLevel, MinState.varTrailPos, varLe]

/-- Monotonicity wrt enlarging the retained clause `C ⊆ C'`. -/
theorem removableInv_mono_clause {s : MinState} {C C' : List Nat}
    (hsub : ∀ l ∈ C, l ∈ C') (hinv : s.RemovableInv C) : s.RemovableInv C' := by
  intro v hrem hl0
  obtain ⟨i, hi, hveq, himp⟩ := hinv v hrem hl0
  exact ⟨i, hi, hveq, fun α hα hC' => himp α hα fun l hlC hle => hC' l (hsub l hlC) hle⟩

theorem seedRemovable_cdcl (s : MinState) (C : List Nat) :
    (seedRemovable s C).cdcl = s.cdcl := by
  unfold seedRemovable
  induction C generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem seedRemovable_trailPos (s : MinState) (C : List Nat) :
    (seedRemovable s C).trailPos = s.trailPos := by
  unfold seedRemovable
  induction C generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih]; rfl

theorem MinBaseInv.seedRemovable {s : MinState} (h : MinBaseInv s) (C : List Nat) :
    MinBaseInv (seedRemovable s C) :=
  ⟨by rw [seedRemovable_cdcl]; exact h.trail_inv,
   by rw [seedRemovable_cdcl, seedRemovable_trailPos]; exact h.pos_inv⟩

theorem seedRemovable_isRemovable (s : MinState) (C : List Nat) (v : Nat) :
    (seedRemovable s C).isRemovable v = true ↔
      s.isRemovable v = true ∨ ∃ l ∈ C, litVar l = v := by
  unfold seedRemovable
  induction C generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, MinState.isRemovable_setRemovable, List.mem_cons]
    by_cases hv : v = litVar x
    · subst hv; simp [exists_eq_or_imp]
    · have hne : litVar x ≠ v := Ne.symm hv
      simp [hv, hne]

theorem trail_getElem_of_eq {c1 c2 : CdclState} (hc : c1 = c2) {i : Nat}
    (h1 : i < c1.trail.size) (_h2 : i < c2.trail.size) :
    c1.trail[i] = c2.trail[i] := by
  subst hc; rfl

/-- (a) Initial clause-literal seeding lemma (`minimize.c:172-173`): pushing all clause literals
onto `removable` establishes `RemovableInv` for `C`. -/
theorem seedRemovable_preserves {s : MinState} {C : List Nat}
    (hrem : s.RemovableInv C)
    (hfals : ∀ l ∈ C, litNeg l ∈ s.cdcl.trail.toList) :
    (seedRemovable s C).RemovableInv C := by
  intro v hv hl0
  rw [seedRemovable_isRemovable] at hv
  rcases hv with hfold | ⟨l, hlC, hlv⟩
  · have hl0' : 0 < s.varLevel v := by
      simpa [MinState.varLevel, seedRemovable_cdcl] using hl0
    obtain ⟨i, hi, hveq, himp⟩ := hrem v hfold hl0'
    have hi' : i < (seedRemovable s C).cdcl.trail.size := by
      simpa [seedRemovable_cdcl] using hi
    have htr : (seedRemovable s C).cdcl.trail[i] = s.cdcl.trail[i] :=
      trail_getElem_of_eq (seedRemovable_cdcl s C) hi' hi
    refine ⟨i, hi', ?_, fun α hα hC => ?_⟩
    · rw [htr, hveq]
    · rw [htr]
      apply himp α (by simpa [seedRemovable_cdcl] using hα)
      intro x hx hle
      exact hC x hx (by simpa [varLe, MinState.varLevel, MinState.varTrailPos,
        seedRemovable_cdcl, seedRemovable_trailPos] using hle)
  · obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp (hfals l hlC)
    have hi' : i < (seedRemovable s C).cdcl.trail.size := by
      simpa [seedRemovable_cdcl] using hi
    have htr : (seedRemovable s C).cdcl.trail[i] = s.cdcl.trail[i] :=
      trail_getElem_of_eq (seedRemovable_cdcl s C) hi' hi
    refine ⟨i, hi', ?_, fun α _ hC => ?_⟩
    · rw [htr, hieq, litVar_litNeg, hlv]
    · rw [htr, hieq]
      exact (sat_cnfClause_litNeg_iff α l).mpr (hC l hlC (by rw [hlv]; exact varLe_refl _ _))

/-- Helper: given `RemovableInv s C`, any falsified literal `x` on the trail whose variable is
level-0 or `removable` (with all smaller `C` literals falsified) must be falsified under `α`. -/
theorem antecedent_falsified {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) {x : Nat}
    (hx_trail : ∃ (j : Nat) (_hj : j < s.cdcl.trail.size), s.cdcl.trail[j] = litNeg x)
    (hok : s.litLevel x = 0 ∨ s.isRemovable (litVar x) = true)
    {α : Nat → Bool} (hα : s.cdcl.f0.Sat α)
    (hC : 0 < s.varLevel (litVar x) →
      ∀ l ∈ C, varLe s (litVar l) (litVar x) → ¬ (cnfClause [l]).Sat α) :
    ¬ (cnfClause [x]).Sat α := by
  obtain ⟨j, hj, hjeq⟩ := hx_trail
  rcases hok with hl0 | hrx
  · have hl0' : stateLevel s.cdcl s.cdcl.trail[j] = 0 := by
      simpa [hjeq, stateLevel_litNeg, MinState.litLevel, MinState.varLevel, stateLevel] using hl0
    have hent := lazyTrailEntailment_level0 h.trail_inv hj hl0'
    rw [hjeq] at hent
    exact (sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent α hα)
  · by_cases hpos : 0 < s.varLevel (litVar x)
    · obtain ⟨j', hj', hj'var, himp⟩ := hrem (litVar x) hrx hpos
      have hj'eq : j' = j := trail_idx_unique_of_var h hj' hj (by rw [hj'var, hjeq, litVar_litNeg])
      subst hj'eq
      have hsat : (cnfClause [litNeg x]).Sat α := by
        rw [← hjeq]; exact himp α hα (hC hpos)
      exact (sat_cnfClause_litNeg_iff α x).mp hsat
    · have hl0' : stateLevel s.cdcl s.cdcl.trail[j] = 0 := by
        simp only [MinState.varLevel] at hpos
        rw [hjeq, stateLevel_litNeg]; unfold stateLevel; omega
      have hent := lazyTrailEntailment_level0 h.trail_inv hj hl0'
      rw [hjeq] at hent
      exact (sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent α hα)

/-- Core semantic step: if `t = trail[i]` has `AntecedentsRemovable`, then `(cnfClause [t]).Sat α`
follows from `F₀.Sat α` and falsification of `{ l ∈ C | var l ≺ var t }` (strict `<_lex`). -/
theorem trailLit_entailed_of_antecedents {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) {i : Nat} (hi : i < s.cdcl.trail.size)
    (hant : AntecedentsRemovable s s.cdcl.trail[i])
    {α : Nat → Bool} (hα : s.cdcl.f0.Sat α)
    (hC : ∀ l ∈ C, varLt s (litVar l) (litVar s.cdcl.trail[i]) → ¬ (cnfClause [l]).Sat α) :
    (cnfClause [s.cdcl.trail[i]]).Sat α := by
  have hrd := reason_antecedent_varLt h hi
  unfold AntecedentsRemovable at hant
  generalize hrsn : stateReason s.cdcl s.cdcl.trail[i] = rsn
  rw [hrsn] at hrd hant
  cases rsn with
  | decision => exact False.elim hant
  | unit =>
    have hl0 : stateLevel s.cdcl s.cdcl.trail[i] = 0 := by
      simpa [MinState.litLevel, MinState.varLevel, stateLevel] using hant
    have hent := lazyTrailEntailment_level0 h.trail_inv hi hl0
    exact CNF.entails_clause_def.mp hent α hα
  | binary other =>
    obtain ⟨hbin, j, hj, _, hjeq, _, hlt⟩ := hrd
    have hnf : ¬ (cnfClause [other]).Sat α :=
      antecedent_falsified h hrem ⟨j, hj, hjeq⟩ hant hα
        (fun _ l hl hle => hC l hl (varLt_of_varLe_varLt hle hlt))
    obtain ⟨y, hy, hsat⟩ :=
      (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hbin α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with heq | heq
    · rw [heq] at hsat; exact (sat_cnfClause_singleton α _).mpr hsat
    · rw [heq] at hsat; exact absurd ((sat_cnfClause_singleton α _).mpr hsat) hnf
  | large cid =>
    obtain ⟨c, hget, _, _, hall⟩ := hrd
    obtain ⟨cl, hget_cl, _, _, hall_ant⟩ := hant
    rw [hget] at hget_cl; cases hget_cl
    obtain ⟨x, hx, hsat⟩ :=
      (clause_sat_cnfClause_iff α c.lits).mp
        (CNF.entails_clause_def.mp (h.trail_inv.db_sound cid c hget) α hα)
    by_cases hxeq : x = s.cdcl.trail[i]
    · rw [hxeq] at hsat; exact (sat_cnfClause_singleton α _).mpr hsat
    · obtain ⟨j, hj, _, hjeq, _, hlt⟩ := hall x hx hxeq
      have hnf : ¬ (cnfClause [x]).Sat α :=
        antecedent_falsified h hrem ⟨j, hj, hjeq⟩ (hall_ant x hx hxeq) hα
          (fun _ l hl hle => hC l hl (varLt_of_varLe_varLt hle hlt))
      exact absurd ((sat_cnfClause_singleton α _).mpr hsat) hnf

/-- (c) Single-step `removable` caching preserves `RemovableInv` whenever antecedents are
already level-0 or `removable`. -/
theorem setRemovable_of_justified {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) {i : Nat} (hi : i < s.cdcl.trail.size)
    (hant : s.litLevel s.cdcl.trail[i] = 0 ∨ AntecedentsRemovable s s.cdcl.trail[i]) :
    (s.setRemovable (litVar s.cdcl.trail[i]) true).RemovableInv C := by
  intro w hw hl0
  simp only [MinState.isRemovable_setRemovable] at hw
  by_cases hweq : w = litVar s.cdcl.trail[i]
  · subst hweq
    rcases hant with h0 | hant'
    · simp [MinState.varLevel, MinState.litLevel] at hl0 h0; omega
    · refine ⟨i, hi, rfl, fun α hα hC => ?_⟩
      exact trailLit_entailed_of_antecedents h hrem hi hant' hα
        (fun x hx hlt => hC x hx hlt.to_varLe)
  · simp only [hweq, ↓reduceIte] at hw
    exact hrem w hw hl0

theorem setRemovableList_cdcl (s : MinState) (vs : List Nat) :
    (setRemovableList s vs).cdcl = s.cdcl := by
  unfold setRemovableList
  induction vs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem setRemovableList_trailPos (s : MinState) (vs : List Nat) :
    (setRemovableList s vs).trailPos = s.trailPos := by
  unfold setRemovableList
  induction vs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih]; rfl

theorem MinBaseInv.setRemovableList {s : MinState} (h : MinBaseInv s) (vs : List Nat) :
    MinBaseInv (setRemovableList s vs) :=
  ⟨by rw [setRemovableList_cdcl]; exact h.trail_inv,
   by rw [setRemovableList_cdcl, setRemovableList_trailPos]; exact h.pos_inv⟩

theorem setRemovableList_isRemovable (s : MinState) (vs : List Nat) (w : Nat) :
    (setRemovableList s vs).isRemovable w = true ↔ s.isRemovable w = true ∨ w ∈ vs := by
  unfold setRemovableList
  induction vs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, MinState.isRemovable_setRemovable, List.mem_cons]
    by_cases hw : w = x <;> simp [hw]

theorem setRemovableList_ext_reverse (s : MinState) (vs : List Nat) :
    ∀ w, (setRemovableList s vs).isRemovable w = (setRemovableList s vs.reverse).isRemovable w := by
  intro w
  rw [Bool.eq_iff_iff, setRemovableList_isRemovable, setRemovableList_isRemovable, List.mem_reverse]

/-- Rewriting `RemovableInv` when two states agree on `cdcl`, `trailPos`, and `isRemovable`. -/
theorem removableInv_congr {s1 s2 : MinState} {C : List Nat}
    (hcdcl : s1.cdcl = s2.cdcl) (htp : s1.trailPos = s2.trailPos)
    (hrem : ∀ w, s1.isRemovable w = s2.isRemovable w) :
    s1.RemovableInv C ↔ s2.RemovableInv C := by
  simp only [MinState.RemovableInv, MinState.varLevel, MinState.varTrailPos, varLe, hcdcl, htp]
  constructor
  · intro H w hw hl0; rw [← hrem w] at hw; exact H w hw hl0
  · intro H w hw hl0; rw [hrem w] at hw; exact H w hw hl0

theorem varLexMeasure_lt {s : MinState} (h : MinBaseInv s) {u v : Nat}
    (hu_trl : ∃ (j : Nat) (_hj : j < s.cdcl.trail.size), litVar s.cdcl.trail[j] = u)
    (hlt : varLt s u v) :
    varLexMeasure s u < varLexMeasure s v := by
  obtain ⟨j, hj, hjeq⟩ := hu_trl
  have hpos_u : s.varTrailPos u = j := by
    unfold MinState.varTrailPos; rw [← hjeq]; exact h.pos_inv j hj
  unfold varLexMeasure
  rcases hlt with hl | ⟨heq, hp⟩
  · have hmul : (s.varLevel u + 1) * (s.cdcl.trail.size + 1) ≤
        s.varLevel v * (s.cdcl.trail.size + 1) := Nat.mul_le_mul_right _ hl
    have hsucc : (s.varLevel u + 1) * (s.cdcl.trail.size + 1) =
        s.varLevel u * (s.cdcl.trail.size + 1) + (s.cdcl.trail.size + 1) := Nat.succ_mul _ _
    omega
  · rw [heq]; omega

/-- Simultaneous closed-set caching lemma: marking any list `vs` of variables as `removable`
preserves `RemovableInv C` whenever each `v ∈ vs` (`varLevel v > 0`) is on the trail with
all reason antecedents already level-0, previously `removable`, or in `vs`. -/
theorem setRemovableList_of_closed_justified {s : MinState} (h : MinBaseInv s) {C : List Nat}
    (hrem : s.RemovableInv C) (vs : List Nat)
    (hclosed : ∀ v ∈ vs, 0 < s.varLevel v →
      ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
        litVar s.cdcl.trail[i] = v ∧
        AntecedentsRemovable (setRemovableList s vs) s.cdcl.trail[i]) :
    (setRemovableList s vs).RemovableInv C := by
  let s' := setRemovableList s vs
  have hs'_base : MinBaseInv s' := h.setRemovableList vs
  have hstrong : ∀ (m v : Nat), varLexMeasure s v = m →
      s'.isRemovable v = true → 0 < s.varLevel v →
      ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
        litVar s.cdcl.trail[i] = v ∧
        ∀ α : Nat → Bool, s.cdcl.f0.Sat α →
          (∀ l ∈ C, varLe s (litVar l) v → ¬ (cnfClause [l]).Sat α) →
          (cnfClause [s.cdcl.trail[i]]).Sat α := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro v hm hv hl0
      rw [show s'.isRemovable v = true ↔ s.isRemovable v = true ∨ v ∈ vs from
        setRemovableList_isRemovable s vs v] at hv
      rcases hv with hprev | hmem
      · exact hrem v hprev hl0
      · obtain ⟨i, hi, hveq, hant⟩ := hclosed v hmem hl0
        refine ⟨i, hi, hveq, fun α hα hC => ?_⟩
        have hrd := reason_antecedent_varLt h hi
        have hant' : AntecedentsRemovable s' s.cdcl.trail[i] := by
          simpa [setRemovableList_cdcl] using hant
        unfold AntecedentsRemovable at hant'
        have hsr : stateReason s'.cdcl s.cdcl.trail[i] = stateReason s.cdcl s.cdcl.trail[i] := by
          rw [setRemovableList_cdcl]
        generalize hrsn : stateReason s.cdcl s.cdcl.trail[i] = rsn
        rw [hsr, hrsn] at hant'
        rw [hrsn] at hrd
        have hant_fals : ∀ x j (hj : j < s.cdcl.trail.size),
            s.cdcl.trail[j] = litNeg x → varLt s (litVar x) v →
            (s'.litLevel x = 0 ∨ s'.isRemovable (litVar x) = true) →
            ¬ (cnfClause [x]).Sat α := by
          intro x j hj hjeq hxlt hok
          rcases hok with hxl0 | hxrem
          · have hjl0 : stateLevel s.cdcl s.cdcl.trail[j] = 0 := by
              rw [hjeq, stateLevel_litNeg]
              simpa [s', MinState.litLevel, MinState.varLevel, setRemovableList_cdcl, stateLevel]
                using hxl0
            have hent_j := lazyTrailEntailment_level0 h.trail_inv hj hjl0
            rw [hjeq] at hent_j
            exact (sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent_j α hα)
          · by_cases hpos : 0 < s.varLevel (litVar x)
            · have hmx : varLexMeasure s (litVar x) < m := by
                rw [← hm]
                exact varLexMeasure_lt h ⟨j, hj, by rw [hjeq, litVar_litNeg]⟩ hxlt
              obtain ⟨j', hj', hj'var, himp⟩ := ih _ hmx (litVar x) rfl hxrem hpos
              have hj'eq : j' = j :=
                trail_idx_unique_of_var h hj' hj (by rw [hj'var, hjeq, litVar_litNeg])
              subst hj'eq
              have hsat : (cnfClause [litNeg x]).Sat α := by
                rw [← hjeq]
                exact himp α hα fun l hlC hle =>
                  hC l hlC (varLt_of_varLe_varLt hle hxlt).to_varLe
              exact (sat_cnfClause_litNeg_iff α x).mp hsat
            · have hjl0 : stateLevel s.cdcl s.cdcl.trail[j] = 0 := by
                simp only [MinState.varLevel] at hpos
                rw [hjeq, stateLevel_litNeg]; unfold stateLevel; omega
              have hent_j := lazyTrailEntailment_level0 h.trail_inv hj hjl0
              rw [hjeq] at hent_j
              exact (sat_cnfClause_litNeg_iff α x).mp (CNF.entails_clause_def.mp hent_j α hα)
        cases rsn with
        | decision => exact False.elim hant'
        | unit =>
          have hl0' : stateLevel s.cdcl s.cdcl.trail[i] = 0 := by
            simpa [s', MinState.litLevel, MinState.varLevel, setRemovableList_cdcl, stateLevel]
              using hant'
          exact CNF.entails_clause_def.mp (lazyTrailEntailment_level0 h.trail_inv hi hl0') α hα
        | binary other =>
          obtain ⟨hbin, j, hj, _, hjeq, _, hxlt⟩ := hrd
          have hnf := hant_fals other j hj hjeq (hveq ▸ hxlt) hant'
          obtain ⟨y, hy, hsat⟩ :=
            (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hbin α hα)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with heq | heq
          · rw [heq] at hsat; exact (sat_cnfClause_singleton α _).mpr hsat
          · rw [heq] at hsat; exact absurd ((sat_cnfClause_singleton α _).mpr hsat) hnf
        | large cid =>
          obtain ⟨c, hget, _, _, hall⟩ := hrd
          obtain ⟨cl, hget_cl, _, _, hall_ant⟩ := hant'
          rw [show s'.cdcl.clauses = s.cdcl.clauses from
            congrArg CdclState.clauses (setRemovableList_cdcl s vs), hget] at hget_cl
          cases hget_cl
          obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α c.lits).mp
            (CNF.entails_clause_def.mp (h.trail_inv.db_sound cid c hget) α hα)
          by_cases hxeq : x = s.cdcl.trail[i]
          · rw [hxeq] at hsat; exact (sat_cnfClause_singleton α _).mpr hsat
          · obtain ⟨j, hj, _, hjeq, _, hxlt⟩ := hall x hx hxeq
            have hnf := hant_fals x j hj hjeq (hveq ▸ hxlt) (hall_ant x hx hxeq)
            exact absurd ((sat_cnfClause_singleton α _).mpr hsat) hnf
  intro v hv hl0
  simp only [setRemovableList_cdcl, setRemovableList_trailPos, MinState.varLevel,
    MinState.varTrailPos, varLe] at hl0 ⊢
  exact hstrong (varLexMeasure s v) v rfl hv hl0

/-- (d) Cut-deletion theorem (`minimize.c:19,127-128,185-188`): depth-0 justification of `l`
(without consulting `l`'s own `removable` flag) justifies deleting `l` from `C` while preserving
both `F₀.EntailsClause (C \ {l})` and `RemovableInv F₀ (C \ {l})`. -/
theorem cut_delete_sound {s : MinState} (h : MinBaseInv s) {C : List Nat} {l : Nat}
    (hent : s.cdcl.f0.EntailsClause (cnfClause C))
    (hrem : s.RemovableInv C)
    (hl_trl : litNeg l ∈ s.cdcl.trail.toList)
    (hjust : s.litLevel l = 0 ∨ AntecedentsRemovable s (litNeg l)) :
    let C' := C.filter (· != l)
    s.cdcl.f0.EntailsClause (cnfClause C') ∧ s.RemovableInv C' := by
  have hcut : ∀ α : Nat → Bool, s.cdcl.f0.Sat α →
      (∀ x ∈ C, x ≠ l → varLe s (litVar x) (litVar l) → ¬ (cnfClause [x]).Sat α) →
      ¬ (cnfClause [l]).Sat α := by
    intro α hα hx_lt
    obtain ⟨i, hi, hieq⟩ := trail_mem_iff_exists.mp hl_trl
    rcases hjust with hl0 | hant
    · have hl0' : stateLevel s.cdcl s.cdcl.trail[i] = 0 := by
        rw [hieq, stateLevel_litNeg]
        simpa [MinState.litLevel, MinState.varLevel, stateLevel] using hl0
      have hent_l := lazyTrailEntailment_level0 h.trail_inv hi hl0'
      rw [hieq] at hent_l
      exact (sat_cnfClause_litNeg_iff α l).mp (CNF.entails_clause_def.mp hent_l α hα)
    · have hant' : AntecedentsRemovable s s.cdcl.trail[i] := by rwa [hieq]
      have htr_sat : (cnfClause [s.cdcl.trail[i]]).Sat α := by
        apply trailLit_entailed_of_antecedents h hrem hi hant' hα
        intro x hxC hlt
        rw [hieq, litVar_litNeg] at hlt
        have hxne : x ≠ l := fun hxl => varLt_irrefl (hxl ▸ hlt)
        exact hx_lt x hxC hxne hlt.to_varLe
      rw [hieq] at htr_sat
      exact (sat_cnfClause_litNeg_iff α l).mp htr_sat
  refine ⟨?_, ?_⟩
  · rw [CNF.entails_clause_def]
    intro α hα
    exact Classical.byContradiction fun hnot => by
      have hC' : ∀ x ∈ C.filter (· != l), ¬ (cnfClause [x]).Sat α := fun x hx hxs =>
        hnot ((clause_sat_cnfClause_iff α _).mpr ⟨x, hx, (sat_cnfClause_singleton α x).mp hxs⟩)
      obtain ⟨x, hxC, hxsat⟩ :=
        (clause_sat_cnfClause_iff α C).mp (CNF.entails_clause_def.mp hent α hα)
      have hxs : (cnfClause [x]).Sat α := (sat_cnfClause_singleton α x).mpr hxsat
      by_cases hxl : x = l
      · subst hxl
        exact hcut α hα (fun y hy hyne _ => hC' y (List.mem_filter.mpr ⟨hy, by simp [hyne]⟩)) hxs
      · exact hC' x (List.mem_filter.mpr ⟨hxC, by simp [hxl]⟩) hxs
  · intro v hv hl0
    obtain ⟨i, hi, hveq, himp⟩ := hrem v hv hl0
    refine ⟨i, hi, hveq, fun α hα hC' => ?_⟩
    apply himp α hα
    intro x hxC hle
    by_cases hxl : x = l
    · subst hxl
      exact hcut α hα fun y hy hyne hyle =>
        hC' y (List.mem_filter.mpr ⟨hy, by simp [hyne]⟩) (varLe_trans hyle hle)
    · exact hC' x (List.mem_filter.mpr ⟨hxC, by simp [hxl]⟩) hle

end LeanQbe.T.Examples.Kissat.Ref
