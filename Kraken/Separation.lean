import Std
namespace Std.ExtHashMap

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]

def sep (p q : ExtHashMap key value → Prop) (m : ExtHashMap key value) : Prop :=
 ∃ a b, a.union b = m ∧ a.inter b = ∅ ∧ p a ∧ q b

infixl:60 " ⋆ " => sep
notation:70 m " =⋆ " P => P m

omit [LawfulBEq key] in
theorem disjoint_symm {m1 m2 : ExtHashMap key value} (h : m1.inter m2 = ∅) :
    m2.inter m1 = ∅ := by
  simpa only [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff, and_comm] using h

omit [LawfulBEq key] in
private theorem disjoint_symm_iff {m1 m2 : ExtHashMap key value} :
    (m1.inter m2 = ∅) = (m2.inter m1 = ∅) :=
  propext ⟨disjoint_symm, disjoint_symm⟩

theorem union_comm_of_disjoint (m1 m2 : ExtHashMap key value) (h_disj : m1.inter m2 = ∅) :
    m1.union m2 = m2.union m1 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union]
  have hd := eq_empty_iff_forall_not_mem.mp h_disj k
  simp only [inter_eq, mem_inter_iff] at hd
  cases h1 : m1[k]? <;> cases h2 : m2[k]? <;> simp <;>
    simp_all [mem_iff_isSome_getElem?]

private theorem union_assoc (m1 m2 m3 : ExtHashMap key value) :
    (m1.union m2).union m3 = m1.union (m2.union m3) := by
  apply ExtHashMap.ext_getElem?
  intro k
  simpa only [union_eq, getElem?_union] using (Option.or_assoc).symm

omit [LawfulBEq key] in
private theorem disjoint_union_l (a b c : ExtHashMap key value) :
    ((a.union b).inter c = ∅) = (a.inter c = ∅ ∧ b.inter c = ∅) := by
  apply propext
  simp only [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff, union_eq, mem_union_iff]
  grind

omit [LawfulBEq key] in
private theorem disjoint_union_r (a b c : ExtHashMap key value) :
    (a.inter (b.union c) = ∅) = (a.inter b = ∅ ∧ a.inter c = ∅) := by
  rw [disjoint_symm_iff]
  rw [disjoint_union_l]
  rw [disjoint_symm_iff (m1:=b), disjoint_symm_iff (m1:=c)]

theorem sep_comm (p q : ExtHashMap key value → Prop) : p ⋆ q = q ⋆ p := by
  have h (p q : ExtHashMap key value → Prop) (m) (h : (p ⋆ q) m) : (q ⋆ p) m := by
    have ⟨a, b, h_union, h_inter, hp, hq⟩ := h
    refine ⟨b, a, by rw [← h_union, union_comm_of_disjoint a b h_inter], disjoint_symm h_inter, hq, hp⟩
  funext m
  exact propext ⟨h p q m, h q p m⟩

theorem sep_assoc (p q r : ExtHashMap key value → Prop) : p ⋆ q ⋆ r = p ⋆ (q ⋆ r) := by
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

instance : Std.Commutative (sep : (ExtHashMap key value → Prop) → _) := ⟨sep_comm⟩
instance : Std.Associative (sep : (ExtHashMap key value → Prop) → _) := ⟨sep_assoc⟩

end Std.ExtHashMap
