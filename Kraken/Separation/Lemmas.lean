import Kraken.Separation

open Std
open Std.ExtHashMap

namespace Std.ExtHashMap

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]

omit [LawfulBEq key] in
theorem disjoint_symm {m1 m2 : ExtHashMap key value} (h : m1.inter m2 = ∅) :
    m2.inter m1 = ∅ := by
  rw [eq_empty_iff_forall_not_mem] at *
  intro k
  have h_not := h k
  rw [inter_eq] at *
  rw [mem_inter_iff] at *
  intro h_mem
  apply h_not
  exact ⟨h_mem.2, h_mem.1⟩

omit [LawfulBEq key] in
private theorem disjoint_symm_iff {m1 m2 : ExtHashMap key value} :
    (m1.inter m2 = ∅) = (m2.inter m1 = ∅) :=
  propext ⟨disjoint_symm, disjoint_symm⟩

private theorem union_comm_of_disjoint (m1 m2 : ExtHashMap key value) (h_disj : m1.inter m2 = ∅) :
    m1.union m2 = m2.union m1 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union]
  cases h1 : m1[k]?
  · cases h2 : m2[k]?
    · rfl
    · rfl
  · have h_not_mem1 : k ∈ m1 := by
      rw [mem_iff_isSome_getElem?]
      rw [h1]
      rfl
    have h_not_mem2 : ¬ k ∈ m2 := fun h_mem2 => by
      have h_empty := eq_empty_iff_forall_not_mem.mp h_disj k
      rw [inter_eq, mem_inter_iff] at h_empty
      exact h_empty ⟨h_not_mem1, h_mem2⟩
    have h2 : m2[k]? = none := getElem?_eq_none h_not_mem2
    rw [h2]
    rfl

private theorem union_assoc (m1 m2 m3 : ExtHashMap key value) :
    (m1.union m2).union m3 = m1.union (m2.union m3) := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union, getElem?_union]
  cases m3[k]?
  · rfl
  · rfl

omit [LawfulBEq key] in
private theorem disjoint_union_l (a b c : ExtHashMap key value) :
    ((a.union b).inter c = ∅) = (a.inter c = ∅ ∧ b.inter c = ∅) := by
  apply propext
  constructor
  · intro h
    rw [eq_empty_iff_forall_not_mem] at h
    constructor
    · rw [eq_empty_iff_forall_not_mem]
      intro k
      have h_not := h k
      intro h_ac
      apply h_not
      rw [inter_eq] at h_ac
      rw [mem_inter_iff] at h_ac
      have ⟨ha, hc⟩ := h_ac
      rw [inter_eq]
      rw [mem_inter_iff]
      refine ⟨?_, hc⟩
      rw [union_eq]
      rw [mem_union_iff]
      left
      exact ha
    · rw [eq_empty_iff_forall_not_mem]
      intro k
      have h_not := h k
      intro h_bc
      apply h_not
      rw [inter_eq] at h_bc
      rw [mem_inter_iff] at h_bc
      have ⟨hb, hc⟩ := h_bc
      rw [inter_eq]
      rw [mem_inter_iff]
      refine ⟨?_, hc⟩
      rw [union_eq]
      rw [mem_union_iff]
      right
      exact hb
  · intro ⟨ha, hb⟩
    rw [eq_empty_iff_forall_not_mem] at *
    intro k
    intro h_mem
    rw [inter_eq] at h_mem
    rw [mem_inter_iff] at h_mem
    have ⟨h_ab, hc⟩ := h_mem
    rw [union_eq] at h_ab
    rw [mem_union_iff] at h_ab
    cases h_ab with
    | inl ha' =>
      apply ha k
      rw [inter_eq]
      rw [mem_inter_iff]
      exact ⟨ha', hc⟩
    | inr hb' =>
      apply hb k
      rw [inter_eq]
      rw [mem_inter_iff]
      exact ⟨hb', hc⟩

omit [LawfulBEq key] in
private theorem disjoint_union_r (a b c : ExtHashMap key value) :
    (a.inter (b.union c) = ∅) = (a.inter b = ∅ ∧ a.inter c = ∅) := by
  rw [disjoint_symm_iff]
  rw [disjoint_union_l]
  rw [disjoint_symm_iff (m1:=b), disjoint_symm_iff (m1:=c)]

theorem sep_comm (p q : SepPred key value) : p ⋆ q = q ⋆ p := by
  have h (p q : SepPred key value) (m) (h : (p ⋆ q) m) : (q ⋆ p) m := by
    have ⟨a, b, h_union, h_inter, hp, hq⟩ := h
    refine ⟨b, a, by rw [← h_union, union_comm_of_disjoint a b h_inter], disjoint_symm h_inter, hq, hp⟩
  funext m
  exact propext ⟨h p q m, h q p m⟩

theorem sep_assoc (p q r : SepPred key value) : p ⋆ q ⋆ r = p ⋆ (q ⋆ r) := by
  funext m
  apply propext
  constructor
  · intro h
    have ⟨ab, c, habc_union, habc_inter, ⟨a, b, hab_union, hab_inter, hp, hq⟩, hr⟩ := h
    subst hab_union
    refine ⟨a, b.union c, (union_assoc a b c).symm.trans habc_union, ?_, hp, ⟨b, c, rfl, ?_, hq, hr⟩⟩
    · have ⟨hac, hbc⟩ := (disjoint_union_l a b c).mp habc_inter
      exact (disjoint_union_r a b c).mpr ⟨hab_inter, hac⟩
    · exact ((disjoint_union_l a b c).mp habc_inter).2
  · intro h
    have ⟨a, bc, habc_union, habc_inter, hp, ⟨b, c, hbc_union, hbc_inter, hq, hr⟩⟩ := h
    subst hbc_union
    refine ⟨a.union b, c, (union_assoc a b c).trans habc_union, ?_, ⟨a, b, rfl, ?_, hp, hq⟩, hr⟩
    · have ⟨hab, hac⟩ := (disjoint_union_r a b c).mp habc_inter
      exact (disjoint_union_l a b c).mpr ⟨hac, hbc_inter⟩
    · exact ((disjoint_union_r a b c).mp habc_inter).1

instance : Std.Commutative (sep : SepPred key value → _) := ⟨sep_comm⟩
instance : Std.Associative (sep : SepPred key value → _) := ⟨sep_assoc⟩

end Std.ExtHashMap

