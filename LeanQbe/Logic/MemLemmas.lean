module

public import LeanQbe.Logic.Mem
public import Kraken.SeparationMem
import all Kraken.Separation
import all Kraken.Mem

/-!
# Lemmas about the memory predicates

* Separation glue missing from Kraken: pulling `∃` and pure facts out of `⋆`, and transporting a fact
  along an equation of predicates (`sep_cast`; `sep_ac h` proves the equation by `ac_rfl`, after
  `open ProofUtil`).
* `loadVal` / `storeOk` / `storeMem` on `cell64` and `array64`, in the form `wp` asks for.
* `array64` focusing (`array64_focus`, `array64_set`), as in Kraken's `LratTrimSpec.word8Array`.
* Satisfiability: `array64_bytes` (non-vacuity of every spec built on `array64`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

open Std Std.ExtHashMap

/-! ## Separation glue -/

theorem sep_ex_l {α : Type} {P : α → Mem 64 → Prop} {R : Mem 64 → Prop} {m : Mem 64} :
    ((fun m => ∃ x, P x m) ⋆ R) m ↔ ∃ x, (P x ⋆ R) m := by
  constructor
  · rintro ⟨a, b, hu, hi, ⟨x, hp⟩, hr⟩; exact ⟨x, a, b, hu, hi, hp, hr⟩
  · rintro ⟨x, a, b, hu, hi, hp, hr⟩; exact ⟨a, b, hu, hi, ⟨x, hp⟩, hr⟩

theorem sep_pure_l {φ : Prop} {P R : Mem 64 → Prop} {m : Mem 64} :
    ((fun m => φ ∧ P m) ⋆ R) m ↔ φ ∧ (P ⋆ R) m := by
  constructor
  · rintro ⟨a, b, hu, hi, ⟨h, hp⟩, hr⟩; exact ⟨h, a, b, hu, hi, hp, hr⟩
  · rintro ⟨h, a, b, hu, hi, hp, hr⟩; exact ⟨a, b, hu, hi, ⟨h, hp⟩, hr⟩

theorem sep_cast {P P' : Mem 64 → Prop} {m : Mem 64} (h : P m) (e : P = P') : P' m := e ▸ h

namespace ProofUtil
scoped macro "sep_ac" h:term : term => `(sep_cast $h (by ac_rfl))
end ProofUtil

/-! ## Words -/

theorem loadVal_cell64 {a v : Val} {sg : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v ⋆ R) m) : loadVal m .l .l sg a = some v := by
  simp only [loadVal, Sz.bytes, Mem.loadInt_sep _ a 8 R m h (Int.toBytes_length 8 _) (by decide),
    Option.map_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

theorem store_cell64 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v0 ⋆ R) m) : storeOk m .l a ∧ (cell64 a v ⋆ R) (storeMem m .l a v) :=
  ⟨⟨_, Mem.loadInt_sep _ a 8 R m h (Int.toBytes_length 8 _) (by decide)⟩,
    Mem.storeInt_sep a 8 _ R m ⟨h, Int.toBytes_length 8 _⟩ v.toInt⟩

/-! ## Arrays -/

@[simp] theorem array64_nil (a : Val) : array64 a [] = emp := rfl
@[simp] theorem array64_cons (a v : Val) (vs : List Val) :
    array64 a (v :: vs) = (cell64 a v ⋆ array64 (a + 8) vs) := rfl

theorem array64_append (a : Val) (xs ys : List Val) :
    array64 a (xs ++ ys) = (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, array64_cons, array64_cons, ih, ← sep_assoc, List.length_cons]
    congr 2; exact BitVec.eq_of_toNat_eq (by grind)

/-- Element `i` of an array, and the rest. -/
theorem array64_focus (a : Val) (xs : List Val) {i : Nat} (hi : i < xs.length) :
    array64 a xs = (cell64 (a + BitVec.ofNat 64 (8 * i)) xs[i] ⋆
      (array64 a (xs.take i) ⋆ array64 (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi]
  rw [array64_append, array64_cons, List.length_take_of_le (Nat.le_of_lt hi),
    ← sep_assoc, sep_comm (array64 a (xs.take i)), sep_assoc]

theorem array64_set (a : Val) (xs : List Val) {i : Nat} (hi : i < xs.length) (v : Val) :
    array64 a (xs.set i v) = (cell64 (a + BitVec.ofNat 64 (8 * i)) v ⋆
      (array64 a (xs.take i) ⋆ array64 (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  rw [array64_focus a (xs.set i v) (i := i) (by simp [hi])]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

/-- `loadl` of element `i`. -/
theorem loadVal_array64 {a : Val} {xs : List Val} {i : Nat} {sg : Bool} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ R) m) :
    loadVal m .l .l sg (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [array64_focus a xs hi, sep_assoc] at h
  exact loadVal_cell64 h

/-- `storel` to element `i`. -/
theorem store_array64 {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ R) m) :
    storeOk m .l (a + BitVec.ofNat 64 (8 * i)) ∧
      (array64 a (xs.set i v) ⋆ R) (storeMem m .l (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [array64_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_cell64 v h
  exact ⟨h1, by rwa [array64_set a xs hi, sep_assoc]⟩

/-! ## Any width: `Int.toBytes n x` cells (Kraken's `byte1` / `int4` / `word8` are instances) -/

theorem setWidth_toInt_take (v : Val) (w : Nat) :
    (v.setWidth w).toInt.take w = (v.toNat : Int).take w := by
  simp only [Int.take, BitVec.toInt_emod_two_pow, BitVec.toNat_setWidth]
  push_cast; rfl

/-- The value `storeMem` writes, as Kraken's `storeInt` argument. -/
theorem storeMem_eq (m : Mem 64) (s : Sz) (a v : Val) :
    ∃ y : Int, storeMem m s a v = m.storeInt a s.bytes y ∧
      y.take (8 * s.bytes) = (v.toNat : Int).take (8 * s.bytes) := by
  cases s
  · exact ⟨_, rfl, setWidth_toInt_take v 8⟩
  · exact ⟨_, rfl, setWidth_toInt_take v 16⟩
  · exact ⟨_, rfl, setWidth_toInt_take v 32⟩
  · refine ⟨_, rfl, ?_⟩
    simp only [Sz.bytes, Int.take, BitVec.toInt_emod_two_pow]
    grind

theorem loadVal_toBytes {s : Sz} {a : Val} {x : Int} {k : Cls} {sg : Bool} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (Eq ((Int.toBytes s.bytes x).At a) ⋆ R) m) :
    loadVal m k s sg a = some (k.trunc (s.extend sg (BitVec.ofInt 64 (x.take (8 * s.bytes))))) := by
  have hb : s.bytes ≤ 2 ^ 64 := by cases s <;> decide
  simp only [loadVal, Mem.loadInt_sep _ a _ R m h (Int.toBytes_length _ _) hb, Option.map_some,
    ofBytes_toBytes]

theorem store_toBytes {s : Sz} {a : Val} {x : Int} (v : Val) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (Eq ((Int.toBytes s.bytes x).At a) ⋆ R) m) :
    storeOk m s a ∧ (Eq ((Int.toBytes s.bytes v.toNat).At a) ⋆ R) (storeMem m s a v) := by
  have hb : s.bytes ≤ 2 ^ 64 := by cases s <;> decide
  obtain ⟨y, hy, ht⟩ := storeMem_eq m s a v
  refine ⟨⟨_, Mem.loadInt_sep _ a _ R m h (Int.toBytes_length _ _) hb⟩, ?_⟩
  rw [hy, ← Int.toBytes_emod, ← ht, Int.toBytes_emod]
  exact Mem.storeInt_sep a _ _ R m ⟨h, Int.toBytes_length _ _⟩ y

/-! ## Satisfiability -/

/-- The bytes of `xs`, 8 per word, little-endian. -/
def bytes64 (xs : List Val) : List UInt8 := xs.flatMap fun v => Int.toBytes 8 v.toInt

theorem bytes64_length (xs : List Val) : (bytes64 xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [bytes64, List.flatMap_cons, List.length_append, Int.toBytes_length] at ih ⊢
    rw [ih, List.length_cons]; omega

/-- Every array that fits in the address space is satisfied by its bytes. -/
theorem array64_bytes (a : Val) (xs : List Val) (h : 8 * xs.length ≤ 2 ^ 64) :
    array64 a xs ((bytes64 xs).At a) := by
  induction xs generalizing a with
  | nil =>
    show _ = ∅
    apply ExtHashMap.ext_getElem?; intro k
    simp [bytes64, List.At]
  | cons x xs ih =>
    have hl : (Int.toBytes 8 x.toInt).length + (bytes64 xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytes64_length]; simp at h; omega
    have : bytes64 (x :: xs) = Int.toBytes 8 x.toInt ++ bytes64 xs := rfl
    have hd := List.disjoint_At_append _ _ a hl
    rw [array64_cons, this, List.At_append _ _ _ hl]
    rw [Int.toBytes_length] at hd ⊢
    exact ⟨_, _, rfl, hd, rfl, ih _ (by simp at h; omega)⟩

end LeanQbe
