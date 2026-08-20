import Kraken.Mem
import Kraken.Separation

/-!
# Separation-logic interface to Kraken memory-access operations
-/

open Std
open Std.ExtHashMap
open List

private theorem Std.ExtHashMap.get_union_l_disjoint {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 : ExtHashMap key value) (k : key) (v : value) (h_disj : m1.inter m2 = ∅) (h : m1.get? k = some v) :
    (m1.union m2).get? k = some v := by
  rw [get?_eq_getElem?] at h
  rw [get?_eq_getElem?, union_comm_of_disjoint m1 m2 h_disj]
  simp only [union_eq, getElem?_union, h, Option.some_or]

private theorem Std.ExtHashMap.union_union_override {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 m3 : ExtHashMap key value) (h_sub : ∀ k, k ∈ m1 → k ∈ m3) :
    (m1.union m2).union m3 = m2.union m3 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union]
  cases h3 : m3[k]?
  · have h_not_mem3 : ¬ k ∈ m3 := by
      intro h_mem
      have h_some := getElem?_eq_some_getElem h_mem
      rw [h3] at h_some
      contradiction
    have h_not_mem1 : ¬ k ∈ m1 := fun h => h_not_mem3 (h_sub k h)
    have h1 := getElem?_eq_none h_not_mem1
    rw [h1]
    cases h2 : m2[k]?
    · rfl
    · rfl
  · rfl

private theorem List.mapM_loop_id_some {α : Type} (xs : List α) (acc : List α) :
    List.mapM.loop id (xs.map some) acc = some (acc.reverse ++ xs) := by
  induction xs generalizing acc <;> simp_all [List.mapM.loop]

private theorem List.allSome_map_some {α : Type} (l : List α) : List.allSome (l.map some) = some l := by
  exact List.mapM_loop_id_some l []

private theorem List.range_get_eq_map_some {α : Type} (l : List α) :
    (List.range l.length).map (fun i => if h : i < l.length then some (l.get ⟨i, h⟩) else none) = l.map some := by
  apply List.ext_get <;> simp

private theorem mem_At_samerange {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (h_len : _bs.length = bs.length) (k : BitVec w) :
    (k ∈ bs.At a) = (k ∈ _bs.At a) := by
  exact propext (by simp [mem_At_iff, h_len])

private theorem disjoint_Atsame_l_same_r {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (m2 : Mem w)
    (h_disj : (_bs.At a).inter m2 = ∅) (h_len : _bs.length = bs.length) :
    (bs.At a).inter m2 = ∅ := by
  simpa [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff,
    mem_At_samerange _bs bs a h_len] using h_disj

namespace Mem

theorem loadBytes_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadBytes a n = some bs := by
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  rw [← h_union]
  have h_get : ∀ i (h : i < n), ((bs.At a).union m2).get? (a + BitVec.ofNat w i) = some (bs.get ⟨i, Hl ▸ h⟩) := by
    intro i hi
    apply get_union_l_disjoint
    · exact h_inter
    · rw [get?_At_idx _ _ _ (by omega) (Hl.symm ▸ Hlw)]
      exact getElem?_eq_getElem (Hl ▸ hi)
  rw [Mem.loadBytes]
  rw [show (List.range n).map (fun i => ((bs.At a).union m2).get? (a + BitVec.ofNat w i)) =
           (List.range n).map (fun i => if h : i < n then some (bs.get ⟨i, Hl ▸ h⟩) else none) by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; rw [dif_pos hi]; exact h_get i hi]
  cases Hl
  rw [List.range_get_eq_map_some]
  rw [List.allSome_map_some]

theorem storeBytes_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n ∧ bs.length = n) :
    (m.storeBytes a bs) =⋆ Eq (bs.At a) ⋆ R := by
  have ⟨Hsep, h_len1, h_len2⟩ := H
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  dsimp [storeBytes]
  rw [← h_union]
  rw [union_union_override (_bs.At a) m2 (bs.At a) (by
    intro k hk; rw [mem_At_samerange _bs bs a (by omega)]; exact hk)]
  rw [sep_comm]
  exact ⟨m2, bs.At a, rfl, disjoint_symm (disjoint_Atsame_l_same_r _bs bs a m2 h_inter (by omega)), hR, rfl⟩

theorem loadBV_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadBV a n = some (BitVec.ofBytes (8 * n) bs) := by
  simp [loadBV, loadBytes_sep bs a n R m Hsep Hl Hlw]

theorem storeBV_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n) {bits : Nat} (v : BitVec bits) :
    m.storeBV a n v =⋆ Eq ((BitVec.toBytes n v).At a) ⋆ R := by
  simpa only [storeBV] using
    storeBytes_sep a n _bs (BitVec.toBytes n v) R m ⟨H.1, H.2, BitVec.toBytes_length n v⟩

theorem At_append_sep {w : Nat} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    Eq ((bs1 ++ bs2).At a) = Eq (bs1.At a) ⋆ Eq (bs2.At (a + .ofNat _ bs1.length)) := by
  funext m
  apply propext
  constructor
  · rintro rfl
    rw [List.At_append _ _ _ h_len]
    exact ⟨bs1.At a, bs2.At (a + BitVec.ofNat w bs1.length), rfl, List.disjoint_At_append _ _ _ h_len, rfl, rfl⟩
  · rintro ⟨m1, m2, h_union, h_disj, rfl, rfl⟩
    rw [← h_union]
    rw [← List.At_append _ _ _ h_len]

end Mem
