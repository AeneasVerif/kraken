module

public import Kraken.Mem
import all Kraken.Mem
public import Kraken.Separation
import all Kraken.Separation

public section

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

theorem loadInt_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  simp [loadInt, loadBytes_sep bs a n R m Hsep Hl Hlw]

theorem storeInt_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ Eq ((Int.toBytes n v).At a) ⋆ R := by
  simpa only [storeInt] using
    storeBytes_sep a n _bs (Int.toBytes n v) R m ⟨H.1, H.2, Int.toBytes_length n v⟩

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


/-! ## Slices of a region

An access of `n` bytes at `addr` inside a region `bs.At a` touches the bytes at
offset `(addr - a).toNat`. The region splits around them, which reduces the
access to `loadInt_sep` or `storeInt_sep` with the rest of the region in the
frame. -/

/-- A region in three parts, split with the middle part first. -/
theorem At_append3_sep {w : Nat} (pre mid post : List UInt8) (a : BitVec w)
    (hlen : pre.length + mid.length + post.length ≤ 2 ^ w) :
    Eq ((pre ++ mid ++ post).At a)
      = Eq (mid.At (a + .ofNat w pre.length))
        ⋆ (Eq (pre.At a) ⋆ Eq (post.At (a + .ofNat w (pre.length + mid.length)))) := by
  rw [At_append_sep (pre ++ mid) post a (by simp; omega),
    At_append_sep pre mid a (by omega), sep_assoc, sep_comm_l]
  simp only [List.length_append]

private theorem add_ofNat_toNat_sub {w : Nat} (a addr : BitVec w) :
    a + BitVec.ofNat w (addr - a).toNat = addr := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- A region split around the `n` bytes at `addr` inside it: those bytes first,
then the bytes before and after them. -/
theorem At_slice_sep {w : Nat} (bs : List UInt8) (a addr : BitVec w) (n : Nat)
    (hin : (addr - a).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    Eq (bs.At a)
      = Eq (((bs.drop (addr - a).toNat).take n).At addr)
        ⋆ (Eq ((bs.take (addr - a).toNat).At a)
          ⋆ Eq ((bs.drop ((addr - a).toNat + n)).At (addr + .ofNat w n))) := by
  have hsplit : bs = bs.take (addr - a).toNat ++ (bs.drop (addr - a).toNat).take n
      ++ bs.drop ((addr - a).toNat + n) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  conv => lhs; rw [hsplit]
  rw [At_append3_sep _ _ _ a (by simp only [List.length_take, List.length_drop]; omega), h1, h2,
    add_ofNat_toNat_sub, BitVec.ofNat_add, ← BitVec.add_assoc, add_ofNat_toNat_sub]

/-- A load inside a region reads the region's bytes there. -/
theorem loadInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) :
    m.loadInt addr n = some (Int.ofBytes ((bs.drop (addr - a).toNat).take n)) := by
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  exact loadInt_sep _ addr n _ m h (by simp only [List.length_take, List.length_drop]; omega)
    (by omega)

/-- A store inside a region writes its bytes into the region, which keeps its
length. -/
theorem storeInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) (v : Int) :
    m.storeInt addr n v =⋆
      Eq ((bs.take (addr - a).toNat ++ Int.toBytes n v ++ bs.drop ((addr - a).toNat + n)).At a)
        ⋆ F := by
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  have hst := storeInt_sep addr n _ _ m ⟨h, h2⟩ v
  rw [At_append3_sep _ _ _ a
      (by simp only [List.length_take, List.length_drop, Int.toBytes_length]; omega),
    sep_assoc, h1, Int.toBytes_length, add_ofNat_toNat_sub, BitVec.ofNat_add,
    ← BitVec.add_assoc, add_ofNat_toNat_sub]
  exact hst

/-! ## Blocks: owned regions with untracked contents

A program that moves data around without inspecting it (a copy, an in-place
update) needs to know which regions it owns, not what they hold. `Block a len`
owns the `len` bytes at `a`, whatever they are, and `Blocks` lists several,
separated from each other. A load or store inside a listed block is safe and
keeps the list, so an invariant says `s.dmem =⋆ Mem.Blocks [...] ⋆ R` and needs
nothing else about memory.

The load and store lemmas fire in `grind` on such a fact and an access.
Their side condition `Blocks.Inside` has one introduction rule per usual
address shape: the block's base, the base plus an offset, and the base plus
two offsets (a pointer into the block plus an index), with the base as the
first or the second term. `grind` applies a rule only when the address is
computed from that block's base, so it never has to rule out the other blocks.
A pointer that moves through a block, as in a loop, is not computed from the
base; its rule applies when the pointer's offset from the base is among the
terms, as it is when a loop invariant bounds it. -/

/-- An owned region of `len` bytes at `a`, whose contents are not tracked. -/
def Block {w : Nat} (a : BitVec w) (len : Nat) (h : Mem w) : Prop :=
  len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ bs.At a = h

/-- A block is a region with some contents of its length. -/
theorem Block.sep_elim {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Block a len ⋆ F) :
    len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ m =⋆ Eq (bs.At a) ⋆ F := by
  obtain ⟨m1, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩ := h
  exact ⟨hw, bs, hlen, _, m2, hu, hi, rfl, hF⟩

/-- A region is a block of its length, forgetting the contents. -/
theorem Block.sep_intro {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    {bs : List UInt8} (hlen : bs.length = len) (hw : len ≤ 2 ^ w)
    (h : m =⋆ Eq (bs.At a) ⋆ F) : m =⋆ Block a len ⋆ F := by
  obtain ⟨m1, m2, hu, hi, rfl, hF⟩ := h
  exact ⟨_, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩

/-- A load inside a block succeeds. -/
theorem Block.loadInt_isSome {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) :
    (m.loadInt addr n).isSome = true := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  rw [loadInt_slice h' hin hw]
  rfl

/-- A store inside a block keeps the block. -/
theorem Block.storeInt {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) (v : Int) :
    m.storeInt addr n v =⋆ Block a len ⋆ F := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  exact Block.sep_intro
    (by simp only [List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
        omega)
    hw (storeInt_slice h' hin hw v)

/-- Blocks separated from each other, as `(base, length)` pairs:
`Blocks [(a₁, l₁), (a₂, l₂)]` is `Block a₁ l₁ ⋆ Block a₂ l₂`. -/
def Blocks {w : Nat} : List (BitVec w × Nat) → Mem w → Prop
  | [] => emp
  | [(a, len)] => Block a len
  | (a, len) :: b :: bs => Block a len ⋆ Blocks (b :: bs)

/-- The `n` bytes at `addr` lie inside one of the blocks. -/
def Blocks.Inside {w : Nat} (addr : BitVec w) (n : Nat) : List (BitVec w × Nat) → Prop
  | [] => False
  | (a, len) :: bs => (addr - a).toNat + n ≤ len ∨ Blocks.Inside addr n bs

/-- An access inside a later block is inside the list. -/
theorem Blocks.Inside.tail {w : Nat} {addr : BitVec w} {n : Nat} {p : BitVec w × Nat}
    {bs : List (BitVec w × Nat)} (h : Blocks.Inside addr n bs) :
    Blocks.Inside addr n (p :: bs) := by
  obtain ⟨a, len⟩ := p
  exact Or.inr h

/-- An access at a block's base. -/
theorem Blocks.Inside.base {w : Nat} {a : BitVec w} {n len : Nat} {bs : List (BitVec w × Nat)}
    (h : n ≤ len) : Blocks.Inside a n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- An access at an offset `x` from a block's base. -/
theorem Blocks.Inside.base_add {w : Nat} {a x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : x.toNat + n ≤ len) :
    Blocks.Inside (a + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

theorem Blocks.Inside.base_add_sub {w : Nat} {a x y : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (x - y).toNat + n ≤ len) :
    Blocks.Inside (a + x - y) n ((a, len) :: bs) :=
  Or.inl (by rw [show a + x - y - a = x - y by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_comm a,
      BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (-y), ← BitVec.add_assoc a,
      ← BitVec.sub_eq_add_neg a a, BitVec.sub_self, BitVec.zero_add]]; exact h)

/-- An access at two offsets `c` and `x` from a block's base, such as a pointer
into the block plus an index. -/
theorem Blocks.Inside.base_add_add {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x).toNat + n ≤ len) :
    Blocks.Inside (a + c + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

/-- An access at offsets `c` and `x` around a block's base, as `c + a + x`: an
operand whose index register holds the pointer to the block, such as
`16(%rcx,%rsi,1)` for the block at `rsi`. -/
theorem Blocks.Inside.add_base_add {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x).toNat + n ≤ len) :
    Blocks.Inside (c + a + x) n ((a, len) :: bs) :=
  Or.inl (by
    rw [BitVec.add_comm c a, BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]
    exact h)

/-- An access at an offset `x` from a pointer `p` into a block, given the
pointer's offset `p - a` from the base: the form in which a loop invariant
tracks a moving pointer. -/
theorem Blocks.Inside.ptr_add {w : Nat} {a p x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p - a).toNat + x.toNat + n ≤ len) :
    Blocks.Inside (p + x) n ((a, len) :: bs) := by
  refine Or.inl ?_
  have hsum : p + x - a = (p - a) + x := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm x,
      ← BitVec.add_assoc]
  rw [hsum, BitVec.toNat_add]
  have := Nat.mod_le ((p - a).toNat + x.toNat) (2 ^ w)
  omega

/-- A load inside one of the blocks succeeds. -/
theorem Blocks.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h hin
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h' hin
      · rw [sep_comm_l] at h'
        exact ih h' hin

/-- A store inside one of the blocks keeps all of them. -/
theorem Blocks.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) (v : Int) :
    m.storeInt addr n v =⋆ Blocks bs ⋆ F := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.storeInt h hin v
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      show (Block a len ⋆ Blocks (q :: bs) ⋆ F) (m.storeInt addr n v)
      rw [sep_assoc]
      rcases hin with hin | hin
      · exact Block.storeInt h' hin v
      · rw [sep_comm_l] at h' ⊢
        exact ih h' hin

grind_pattern Blocks.Inside.tail => Blocks.Inside addr n (p :: bs)
grind_pattern Blocks.Inside.base => Blocks.Inside a n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add => Blocks.Inside (a + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_sub => Blocks.Inside (a + x - y) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_add => Blocks.Inside (a + c + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.add_base_add => Blocks.Inside (c + a + x) n ((a, len) :: bs)
-- The pointer rule also needs the offset `p - a` among the terms, which an
-- invariant about the pointer puts there. Otherwise any pointer into any block
-- would match, and ruling out the wrong blocks swamps the arithmetic.
grind_pattern Blocks.Inside.ptr_add => Blocks.Inside (p + x) n ((a, len) :: bs), p - a
grind_pattern Blocks.loadInt_isSome => sep (Blocks bs) F m, Mem.loadInt m addr n
grind_pattern Blocks.storeInt => sep (Blocks bs) F m, Mem.storeInt m addr n v



/-! ## Copying into a block: `Blocks` owns the destination, `Contains` tracks contents -/

@[grind =] theorem _root_.List.getElem!_drop' (l : List UInt8) (k i : Nat) :
    (l.drop k)[i]! = l[k + i]! := by
  simp only [getElem!_def, List.getElem?_drop]

@[grind =] theorem _root_.List.getElem!_take' (l : List UInt8) (r i : Nat) (h : i < r) :
    (l.take r)[i]! = l[i]! := by
  simp only [getElem!_def, List.getElem?_take, ite_eq_left h]

@[grind =] theorem _root_.Int.toBytes_one_byte (b : UInt8) :
    Int.toBytes 1 (BitVec.ofInt 8 (b.toNat : Int)).toInt = [b] := by
  have hb := b.toNat_lt
  have h : (BitVec.ofInt 8 (b.toNat : Int)).toInt.take 8 = b.toNat := by
    rw [Int.take, BitVec.toInt_ofInt, show ((2 : Int) ^ 8) = ((2 ^ 8 : Nat) : Int) by norm_cast,
      Int.bmod_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Int.toBytes, h, Int.toNat_natCast, List.cons.injEq, and_true]
  simp

/-- The owned bytes `bs` at `a`. -/
def Bytes {w : Nat} (a : BitVec w) (bs : List UInt8) : Mem w → Prop := Eq (bs.At a)

/-- `m` holds the bytes `bs` at `a`. -/
def Contains {w : Nat} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Prop :=
  ∀ i (h : i < bs.length), m.get? (a + .ofNat w i) = some bs[i]

private theorem Blocks_cons_sep {w : Nat} (a : BitVec w) (len : Nat) (l : List (BitVec w × Nat))
    (F : Mem w → Prop) : Blocks ((a, len) :: l) ⋆ F = Block a len ⋆ (Blocks l ⋆ F) := by
  cases l with
  | nil => rw [Blocks, Blocks, emp_sep]
  | cons b l => rw [Blocks, sep_assoc]

theorem Blocks.storeInt_head {w : Nat} {a : BitVec w} {n : Nat} {l : List (BitVec w × Nat)}
    {F : Mem w → Prop} {m : Mem w} (h : m =⋆ Blocks ((a, n) :: l) ⋆ F) (v : Int) :
    m.storeInt a n v =⋆ Bytes a (Int.toBytes n v) ⋆ Blocks l ⋆ F := by
  rw [Blocks_cons_sep] at h
  obtain ⟨-, ys, hys, h⟩ := Block.sep_elim h
  rw [Bytes, sep_assoc]
  exact storeInt_sep a n ys _ m ⟨h, hys⟩ v

theorem Blocks.storeInt₂ {w : Nat} {P F : Mem w → Prop} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : m =⋆ P ⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs)
    (v : Int) : m.storeInt addr n v =⋆ P ⋆ Blocks bs ⋆ F := by
  rw [sep_assoc, sep_comm_l] at h ⊢
  exact Blocks.storeInt h hin v

theorem Blocks.loadInt_isSome₂ {w : Nat} {P F : Mem w → Prop} {bs : List (BitVec w × Nat)}
    {m : Mem w} {addr : BitVec w} {n : Nat} (h : m =⋆ P ⋆ Blocks bs ⋆ F)
    (hin : Blocks.Inside addr n bs) : (m.loadInt addr n).isSome = true := by
  rw [sep_assoc, sep_comm_l] at h
  exact Blocks.loadInt_isSome h hin

theorem Bytes.loadInt₂ {w : Nat} {a : BitVec w} {bs : List UInt8} {n : Nat} {G F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Bytes a bs ⋆ G ⋆ F) (hn : bs.length = n) (hw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  rw [Bytes, sep_assoc] at h
  exact loadInt_sep bs a n _ m h hn hw

theorem Contains.of_sep {w : Nat} {bs : List UInt8} {a : BitVec w} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Eq (bs.At a) ⋆ F) (hw : bs.length ≤ 2 ^ w) : Contains m a bs := by
  obtain ⟨m1, m2, rfl, hi, rfl, -⟩ := h
  intro i hi'
  exact Std.ExtHashMap.get_union_l_disjoint _ _ _ _ hi
    (by rw [get?_At_idx _ _ _ (by omega) hw, List.getElem?_eq_getElem hi'])

theorem Contains.of_sep₂ {w : Nat} {bs : List UInt8} {a : BitVec w} {G F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Bytes a bs ⋆ G ⋆ F) (hw : bs.length ≤ 2 ^ w) : Contains m a bs := by
  rw [Bytes, sep_assoc] at h
  exact Contains.of_sep h hw

theorem Contains.of_length {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : bs.length = 0) : Contains m a bs := fun i hi => by omega

theorem Contains.loadInt {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hi : (addr - a).toNat < bs.length) :
    m.loadInt addr 1 = some (bs[(addr - a).toNat]!.toNat : Int) := by
  have := h _ hi
  rw [add_ofNat_toNat_sub] at this
  rw [Mem.loadInt_one, this, getElem!_pos bs _ hi]
  rfl

theorem Contains.loadInt_take {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {r : Nat} (h : Contains m a (bs.take r)) (hi : (addr - a).toNat < r) (hr : r ≤ bs.length) :
    m.loadInt addr 1 = some (bs[(addr - a).toNat]!.toNat : Int) := by
  rw [h.loadInt (by simp only [List.length_take]; omega), List.getElem!_take' _ _ _ hi]

theorem Contains.loadInt_head {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hi : 0 < bs.length) : m.loadInt a 1 = some (bs[0]!.toNat : Int) := by
  have := h.loadInt (addr := a) (by rw [BitVec.sub_self, BitVec.toNat_zero]; exact hi)
  rwa [BitVec.sub_self, BitVec.toNat_zero] at this

theorem Contains.storeInt {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hd : bs.length ≤ (addr - a).toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a bs := fun i hi => by
  rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => ?_]
  · exact h i hi
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [BitVec.add_zero] at he
    rw [← he, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at hd
    have := Nat.mod_le i (2 ^ w)
    omega

theorem Contains.consume {w : Nat} {m : Mem w} {a a' addr : BitVec w} {bs : List UInt8}
    {k k' : Nat} (h : Contains m a (bs.drop k)) (hk : k' = k + 1) (ha : a' = a + 1)
    (hd : bs.length - k' ≤ (addr - a').toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a' (bs.drop k') := by
  refine Contains.storeInt (fun i hi => ?_) (by simpa using hd) v
  have hi' : i + 1 < (bs.drop k).length := by simp only [List.length_drop] at hi ⊢; omega
  have := h (i + 1) hi'
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat w i), ← BitVec.add_assoc] at this
  subst hk ha
  have e : k + (i + 1) = k + 1 + i := by omega
  simp only [List.getElem_drop, e] at this ⊢
  exact this

theorem Contains.consume_back {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {r r' : Nat} (h : Contains m a (bs.take r)) (hr : r' + 1 = r)
    (hd : r' ≤ (addr - a).toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a (bs.take r') := by
  refine Contains.storeInt (fun i hi => ?_) (by simp only [List.length_take]; omega) v
  have hi' : i < (bs.take r).length := by simp only [List.length_take] at hi ⊢; omega
  simpa only [List.getElem_take] using h i hi'

theorem Contains.extend {w : Nat} {m : Mem w} {a p : BitVec w} {bs : List UInt8} {k k' : Nat}
    (h : Contains m a (bs.take k)) (hk : k' = k + 1) (hp : p = a + .ofNat w k)
    (hkl : k < bs.length) (hw : bs.length ≤ 2 ^ w) {v : Int} (hv : Int.toBytes 1 v = [bs[k]!]) :
    Contains (m.storeInt p 1 v) a (bs.take k') := fun i hi => by
  subst hk
  have hi' : i < k + 1 := by simp only [List.length_take] at hi; omega
  rw [Mem.get?_storeInt_one]
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_left hp.symm]
    have h1 : ((Int.toBytes 1 v)[0]'(by rw [Int.toBytes_length]; omega)) = (v.take 8).toNat.toUInt8 := rfl
    simp only [hv, List.getElem_cons_zero, List.getElem_take] at h1 ⊢
    rw [← h1, getElem!_pos bs _ hkl]
  · have hne : a + BitVec.ofNat w i ≠ p := fun he => hik (by
      rw [hp] at he
      have h2 := congrArg (fun x => BitVec.toNat (x - a)) he
      simp only [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at h2
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2)
    rw [ite_eq_right hne]
    have := h i (by simp only [List.length_take]; omega)
    simpa only [List.getElem_take] using this

theorem Contains.extend_back {w : Nat} {m : Mem w} {b q : BitVec w} {bs : List UInt8} {r r' : Nat}
    (h : Contains m b (bs.drop r)) (hr : r' + 1 = r) (hb : b = q + 1) (hrl : r ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) {v : Int} (hv : Int.toBytes 1 v = [bs[r']!]) :
    Contains (m.storeInt q 1 v) q (bs.drop r') := fun i hi => by
  subst hr hb
  rw [Mem.get?_storeInt_one]
  by_cases hi0 : i = 0
  · subst hi0
    rw [BitVec.add_zero, ite_eq_left rfl]
    have h1 : ((Int.toBytes 1 v)[0]'(by rw [Int.toBytes_length]; omega)) = (v.take 8).toNat.toUInt8 := rfl
    simp only [hv, List.getElem_cons_zero] at h1
    simp only [List.getElem_drop, Nat.add_zero]
    rw [← getElem!_pos bs r' (by omega), h1]
  · have hne : q + BitVec.ofNat w i ≠ q := fun he => hi0 (by
      have h2 := congrArg (fun x => BitVec.toNat (x - q)) he
      simp only [BitVec.add_comm q, BitVec.add_sub_cancel, BitVec.sub_self, BitVec.toNat_ofNat] at h2
      simp only [List.length_drop] at hi
      rwa [Nat.mod_eq_of_lt (by omega)] at h2)
    rw [ite_eq_right hne]
    have := h (i - 1) (by simp only [List.length_drop] at hi ⊢; omega)
    rw [show q + 1 + BitVec.ofNat w (i - 1) = q + BitVec.ofNat w i by
      rw [BitVec.add_assoc, show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, ← BitVec.ofNat_add,
        show 1 + (i - 1) = i by omega]] at this
    simpa only [List.getElem_drop, show r' + 1 + (i - 1) = r' + i by omega] using this

theorem Blocks.of_contains {w : Nat} {p a : BitVec w} {ys bs : List UInt8} {n : Nat}
    {F : Mem w → Prop} {m : Mem w} (h : m =⋆ Bytes p ys ⋆ Blocks [(a, n)] ⋆ F)
    (hc : Contains m a bs) (hn : bs.length = n) (hyw : ys.length ≤ 2 ^ w) :
    m =⋆ Blocks [(p, ys.length)] ⋆ Bytes a bs ⋆ F := by
  have hB : ∀ (a : BitVec w) (n : Nat), Blocks [(a, n)] = Block a n := fun _ _ => rfl
  rw [Bytes, hB, sep_assoc, sep_comm_l] at h
  obtain ⟨hw, zs, hzs, h'⟩ := Block.sep_elim h
  have hz : zs = bs := by
    have hcz := Contains.of_sep h' (by omega)
    apply List.ext_getElem (by omega)
    intro i h1 h2
    have := (hcz i h1).symm.trans (hc i h2)
    simpa using this
  subst hz
  rw [sep_comm_l] at h'
  have := Block.sep_intro (len := ys.length) rfl hyw h'
  rw [hB, Bytes, sep_assoc]
  exact this

attribute [grind =] Int.toBytes_length

grind_pattern Blocks.storeInt_head => sep (Blocks ((a, n) :: l)) F m, Mem.storeInt m a n v
grind_pattern Blocks.loadInt_isSome₂ => sep (sep P (Blocks bs)) F m, Mem.loadInt m addr n
grind_pattern Blocks.storeInt₂ => sep (sep P (Blocks bs)) F m, Mem.storeInt m addr n v
grind_pattern Bytes.loadInt₂ => sep (sep (Bytes a bs) G) F m, Mem.loadInt m a n
grind_pattern Contains.of_sep₂ => sep (sep (Bytes a bs) G) F m
grind_pattern Contains.of_length => Contains m a bs
grind_pattern Contains.loadInt_take => Contains m a (List.take r bs), Mem.loadInt m addr 1
grind_pattern Contains.loadInt_head => Contains m a bs, Mem.loadInt m a 1
grind_pattern Contains.consume => Contains m a (List.drop k bs),
  Contains (Mem.storeInt m addr 1 v) a' (List.drop k' bs)
grind_pattern Contains.consume_back => Contains m a (List.take r bs),
  Contains (Mem.storeInt m addr 1 v) a (List.take r' bs)
grind_pattern Contains.extend => Contains m a (List.take k bs),
  Contains (Mem.storeInt m p 1 v) a (List.take k' bs)
grind_pattern Contains.extend_back => Contains m b (List.drop r bs),
  Contains (Mem.storeInt m q 1 v) q (List.drop r' bs)
grind_pattern Blocks.of_contains => sep (sep (Bytes p ys) (Blocks [(a, n)])) F m, Contains m a bs

def UnchangedOutside {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) : Prop :=
  ∀ b, ¬ Blocks.Inside b 1 bs → m'.get? b = m.get? b

@[grind =] theorem unchangedOutside_iff {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) :
    UnchangedOutside bs m m' ↔ ∀ b, ¬ Blocks.Inside b 1 bs → m'.get? b = m.get? b := Iff.rfl

def Mapped {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → (m.get? b).isSome

def Blocks.Disjoint {w : Nat} (bs bs' : List (BitVec w × Nat)) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → ¬ Blocks.Inside b 1 bs'

theorem Blocks.Inside.add_ofNat {w : Nat} {bs : List (BitVec w × Nat)} {addr : BitVec w}
    {n i : Nat} (hin : Blocks.Inside addr n bs) (hi : i < n) :
    Blocks.Inside (addr + BitVec.ofNat w i) 1 bs := by
  induction bs with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    rcases hin with h | h
    · left
      rw [show addr + BitVec.ofNat w i - a = (addr - a) + BitVec.ofNat w i by
        rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm _ (-a),
          ← BitVec.add_assoc]]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := Nat.mod_le ((addr - a).toNat + i % 2 ^ w) (2 ^ w)
      have := Nat.mod_le i (2 ^ w)
      omega
    · exact Or.inr (ih h)

theorem Blocks.Inside.get?_storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr b : BitVec w} {n : Nat} (hin : Blocks.Inside addr n bs) (hb : ¬ Blocks.Inside b 1 bs)
    (v : Int) : (m.storeInt addr n v).get? b = m.get? b :=
  Mem.get?_storeInt_of_ne _ _ _ _ _ fun _ hi he => hb (he ▸ hin.add_ofNat hi)

theorem Mapped.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true := by
  have hl : ∀ l : List Nat, (∀ i ∈ l, i < n) →
      ((l.map fun i => m.get? (addr + BitVec.ofNat w i)).mapM id).isSome = true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h _ (hin.add_ofNat (hl i (List.mem_cons_self ..))))
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp
        (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons, List.mapM_cons, id, hx, hxs]
      rfl
  simpa only [Mem.loadInt, Mem.loadBytes, List.allSome, Option.isSome_map] using
    hl (List.range n) fun i hi => List.mem_range.mp hi

theorem Mapped.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w} (h : Mapped bs m)
    (a : BitVec w) (n : Nat) (v : Int) : Mapped bs (m.storeInt a n v) := fun b hb => by
  have hm := h b hb
  rw [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union]
  rw [get?_eq_getElem?] at hm
  cases ((Int.toBytes n v).At a)[b]? <;> simp_all

theorem Contains.loadInt_eq {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8} {n : Nat}
    (h : Contains m a bs) (hn : bs.length = n) : m.loadInt a n = some (Int.ofBytes bs) := by
  subst hn
  have hb : m.loadBytes a bs.length = some bs := by
    rw [Mem.loadBytes, List.map_congr_left (fun i hi => (h i (List.mem_range.mp hi)).trans
      (List.getElem?_eq_getElem (List.mem_range.mp hi)).symm), List.map_range_getElem?,
      List.allSome_map_some]
  simp only [Mem.loadInt, hb, Option.map_some]

theorem Contains.storeInt_self {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int)
    (hw : n ≤ 2 ^ w) : Contains (m.storeInt a n v) a (Int.toBytes n v) := fun i hi => by
  have hl := Int.toBytes_length n v
  rw [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, ExtHashMap.union_eq,
    ExtHashMap.getElem?_union, ← get?_eq_getElem?, get?_At_idx _ a i (by omega) (by omega),
    List.getElem?_eq_getElem hi]
  rfl

theorem Contains.storeInt_of_disjoint {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {n : Nat} {bs₁ bs₂ : List (BitVec w × Nat)} (h : Contains m a bs)
    (hin : Blocks.Inside addr n bs₁) (hd : Blocks.Disjoint bs₁ bs₂)
    (ha : Blocks.Inside a bs.length bs₂) (v : Int) : Contains (m.storeInt addr n v) a bs :=
  fun i hi => by
    rw [hin.get?_storeInt (fun hb => hd _ hb (ha.add_ofNat hi)) v]
    exact h i hi

theorem Contains.storeInt_of_disjoint' {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {n : Nat} {bs₁ bs₂ : List (BitVec w × Nat)} (h : Contains m a bs)
    (hin : Blocks.Inside addr n bs₁) (hd : Blocks.Disjoint bs₂ bs₁)
    (ha : Blocks.Inside a bs.length bs₂) (v : Int) : Contains (m.storeInt addr n v) a bs :=
  fun i hi => by
    rw [hin.get?_storeInt (fun hb => hd _ (ha.add_ofNat hi) hb) v]
    exact h i hi

grind_pattern Blocks.Inside.get?_storeInt => Std.ExtHashMap.get? (Mem.storeInt m addr n v) b, Blocks.Inside b 1 bs
grind_pattern Mapped.loadInt_isSome => Mapped bs m, Mem.loadInt m addr n
grind_pattern Mapped.storeInt => Mapped bs m, Mem.storeInt m a n v
grind_pattern Contains.loadInt_eq => Contains m a bs, Mem.loadInt m a n
grind_pattern Contains.storeInt_self => Mem.storeInt m a n v
grind_pattern Contains.storeInt_of_disjoint => Contains m a bs, Mem.storeInt m addr n v, Blocks.Disjoint bs₁ bs₂
grind_pattern Contains.storeInt_of_disjoint' => Contains m a bs, Mem.storeInt m addr n v, Blocks.Disjoint bs₂ bs₁

end Mem
