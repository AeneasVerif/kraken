module

@[expose] public section

/-!
`List.IsInfixAt l₁ l₂ k` refines `List.IsInfix l₁ l₂` by the index `k` at which `l₁` starts in `l₂`.
-/

universe u

namespace List

/-- `l₁` occurs in `l₂` starting at index `k`. -/
def IsInfixAt {α : Type u} (l₁ l₂ : List α) (k : Nat) : Prop := l₁ <+: l₂.drop k

variable {α : Type u} {l₁ l₂ a b : List α} {d : α} {k : Nat}

theorem isInfixAt_iff_getElem? :
    l₁.IsInfixAt l₂ k ↔ ∀ i (h : i < l₁.length), l₂[k + i]? = some l₁[i] := by
  simp [IsInfixAt, prefix_iff_getElem?, getElem?_drop]

theorem IsInfixAt.isInfix (h : l₁.IsInfixAt l₂ k) : l₁ <:+: l₂ :=
  IsInfix.trans (IsPrefix.isInfix (show l₁ <+: l₂.drop k from h)) (drop_suffix k l₂).isInfix

theorem isInfix_iff_exists_isInfixAt : l₁ <:+: l₂ ↔ ∃ k, l₁.IsInfixAt l₂ k := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => h.isInfix⟩
  obtain ⟨k, -, h⟩ := infix_iff_getElem?.mp h
  exact ⟨k, isInfixAt_iff_getElem?.mpr fun i hi => by rw [Nat.add_comm]; exact h i hi⟩

theorem nil_isInfixAt (l : List α) (k : Nat) : ([] : List α).IsInfixAt l k := nil_prefix

theorem IsInfixAt.cons (h : (d :: l₁).IsInfixAt l₂ k) : l₂[k]? = some d ∧ l₁.IsInfixAt l₂ (k + 1) := by
  have hk : k < l₂.length := by
    have := h.length_le; grind
  unfold IsInfixAt at h ⊢
  rw [drop_eq_getElem_cons hk, cons_prefix_iff] at h
  grind

theorem IsInfixAt.append (h : (a ++ b).IsInfixAt l₂ k) :
    a.IsInfixAt l₂ k ∧ b.IsInfixAt l₂ (k + a.length) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨b ++ t, by rw [← ht, append_assoc]⟩, ⟨t, ?_⟩⟩
  rw [← drop_drop, ← ht, append_assoc, drop_left]

theorem IsInfixAt.drop (h : l₁.IsInfixAt l₂ k) (m : Nat) : (l₁.drop m).IsInfixAt l₂ (k + m) := by
  by_cases hm : m ≤ l₁.length
  · have h' := (IsInfixAt.append (a := l₁.take m) (b := l₁.drop m) (by rwa [take_append_drop])).2
    rwa [length_take_of_le hm] at h'
  · rw [drop_eq_nil_of_le (show l₁.length ≤ m by omega)]
    exact nil_isInfixAt _ _

theorem exists_isPrefixOf_drop [DecidableEq α] (h : l₁ <:+: l₂) :
    ∃ k, k ∈ range (l₂.length + 1) ∧ l₁.isPrefixOf (l₂.drop k) := by
  obtain ⟨k, hk⟩ := isInfix_iff_exists_isInfixAt.mp h
  replace hk : l₁ <+: l₂.drop k := hk
  refine ⟨min k l₂.length, mem_range.mpr (by omega), isPrefixOf_iff_prefix.mpr ?_⟩
  by_cases hkl : k ≤ l₂.length
  · rw [Nat.min_eq_left hkl]
    exact hk
  · have hnil : l₁ = [] := prefix_nil.mp (by rwa [drop_eq_nil_of_le (by omega)] at hk)
    rw [hnil]
    exact nil_prefix

/-- The first index at which `l₁` occurs in `l₂`. -/
def infixIdx [DecidableEq α] (l₁ l₂ : List α) (h : l₁ <:+: l₂) : Nat :=
  ((range (l₂.length + 1)).find? fun k => l₁.isPrefixOf (l₂.drop k)).get
    (find?_isSome.mpr (exists_isPrefixOf_drop h))

theorem isInfixAt_infixIdx [DecidableEq α] (h : l₁ <:+: l₂) : l₁.IsInfixAt l₂ (l₁.infixIdx l₂ h) := by
  have hp := find?_some (p := fun k => l₁.isPrefixOf (l₂.drop k))
    (Option.some_get (find?_isSome.mpr (exists_isPrefixOf_drop h))).symm
  exact isPrefixOf_iff_prefix.mp hp

end List
