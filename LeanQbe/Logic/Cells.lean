module

public import LeanQbe.Logic.MemLemmas
public import LeanQbe.Logic.BitVec
public import Kraken.Bedrock2.Test.LratTrimSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kraken's `byte1` / `int4` / `word8` cells and arrays, read and written by QBE loads and stores

The predicates (`byte1`, `int4`, `word8`, `byte1Array`, `int4Array`, `word8Array`, `IsInt8`, `IsInt32`)
and their focusing lemmas are Kraken's (`Kraken.Bedrock2.Test.LratTrimSpec`); here is what `wp` asks of
them, on top of `loadVal_toBytes` / `store_toBytes` of `MemLemmas.lean`.

* Sign extension and `Truthy` on values that fit (`sext8`, `sext32`, `truthy_iff`).
* One cell: `loadsb_byte1`, `loadsw_int4`, `loaduw_int4`, `loadl_word8`, `loadsw_word8`, `store_byte1`,
  `store_int4`, `store_word8`.
* Element `i` of an array: `loadsb_byte1Array`, `loadsw_int4Array`, `loadl_word8Array`,
  `storeb_byte1Array`, `storew_int4Array`, `storel_word8Array`.
* The same with the address as a separate equation, for concrete addresses (`loadsw_at`, `loadl_at`,
  `loadsb_at`, `storeb_at`), and as the goal `wp_unfold` leaves at a load (`ld_w_step`, `ld_l_step`,
  `ld_b_step`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## Values that fit in 8 or 32 bits -/

theorem sext8 (v : Val) (h : IsInt8 v) :
    (BitVec.setWidth 8 (BitVec.ofInt 64 ((v.toNat : Int).take 8))).signExtend 64 = v := by
  rw [ofInt_take_toNat v]; unfold IsInt8 at h; grind

theorem sext32 (v : Val) (h : IsInt32 v) :
    (BitVec.setWidth 32 (BitVec.ofInt 64 ((v.toNat : Int).take 32))).signExtend 64 = v := by
  rw [ofInt_take_toNat v]; unfold IsInt32 at h; grind

theorem truthy_iff (v : Val) (h : IsInt32 v) : Truthy v ↔ v ≠ 0 := by
  unfold Truthy IsInt32 at *; constructor <;> intro h1 h2 <;> apply h1 <;> grind

/-! ## Cells -/

theorem loadsb_byte1 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (byte1 a v ⋆ R) m)
    (hv : IsInt8 v) : loadVal m .l .b true a = some v := by
  rw [loadVal_toBytes (s := .b) h]; exact congrArg some (sext8 v hv)

theorem loadsw_int4 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v ⋆ R) m)
    (hv : IsInt32 v) : loadVal m .l .w true a = some v := by
  rw [loadVal_toBytes (s := .w) h]; exact congrArg some (sext32 v hv)

theorem loadl_word8 {a v : Val} {sg : Bool} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v ⋆ R) m) :
    loadVal m .l .l sg a = some v := by
  rw [loadVal_toBytes (s := .l) h]
  simp only [Sz.bytes, Int.take, Cls.trunc, Sz.extend]
  rw [Int.emod_eq_of_lt (by omega) (by have := v.isLt; omega)]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simp))

theorem store_byte1 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (byte1 a v0 ⋆ R) m) :
    storeOk m .b a ∧ (byte1 a v ⋆ R) (storeMem m .b a v) := store_toBytes (s := .b) v h

theorem store_int4 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v0 ⋆ R) m) :
    storeOk m .w a ∧ (int4 a v ⋆ R) (storeMem m .w a v) := store_toBytes (s := .w) v h

theorem store_word8 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v0 ⋆ R) m) :
    storeOk m .l a ∧ (word8 a v ⋆ R) (storeMem m .l a v) := store_toBytes (s := .l) v h

theorem loaduw_int4 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v ⋆ R) m) :
    loadVal m .l .w false a = some (v &&& 0xffffffff#64) := by
  rw [loadVal_toBytes (s := .w) h]
  simp only [Cls.trunc, Sz.extend, Sz.bytes]; rw [ofInt_take_toNat v]; congr 1; grind

theorem word8_eq_int4_sep (a v : Val) :
    word8 a v = (int4 a v ⋆ Eq (((Int.toBytes 8 v.toNat).drop 4).At (a + 4))) := by
  unfold word8 int4
  conv => lhs; rw [← List.take_append_drop 4 (Int.toBytes 8 v.toNat)]
  exact Mem.At_append_sep (Int.toBytes 4 v.toNat) ((Int.toBytes 8 v.toNat).drop 4) a
    (by simp [Int.toBytes_length])

theorem loadsw_word8 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v ⋆ R) m)
    (hv : IsInt32 v) : loadVal m .l .w true a = some v := by
  rw [word8_eq_int4_sep, sep_assoc] at h
  exact loadsw_int4 h hv

/-! ## Arrays -/

theorem loadsb_byte1Array {a : Val} {xs : List Val} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt8 xs[i]) (h : (byte1Array a xs ⋆ R) m) :
    loadVal m .l .b true (a + BitVec.ofNat 64 i) = some xs[i] := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h; exact loadsb_byte1 h hv

theorem storeb_byte1Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    storeOk m .b (a + BitVec.ofNat 64 i) ∧
      (byte1Array a (xs.set i v) ⋆ R) (storeMem m .b (a + BitVec.ofNat 64 i) v) := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_byte1 v h
  exact ⟨h1, by rwa [byte1Array_set a xs hi, sep_assoc]⟩

theorem storew_int4Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m) :
    storeOk m .w (a + BitVec.ofNat 64 (4 * i)) ∧
      (int4Array a (xs.set i v) ⋆ R) (storeMem m .w (a + BitVec.ofNat 64 (4 * i)) v) := by
  rw [int4Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_int4 v h
  exact ⟨h1, by rwa [int4Array_set a xs hi, sep_assoc]⟩

theorem loadl_word8Array {a : Val} {xs : List Val} {i : Nat} {sg : Bool} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    loadVal m .l .l sg (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [word8Array_focus a xs hi, sep_assoc] at h; exact loadl_word8 h

theorem storel_word8Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    storeOk m .l (a + BitVec.ofNat 64 (8 * i)) ∧
      (word8Array a (xs.set i v) ⋆ R) (storeMem m .l (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [word8Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_word8 v h
  exact ⟨h1, by rwa [word8Array_set a xs hi, sep_assoc]⟩

theorem loadsw_int4Array {a : Val} {xs : List Val} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (h32 : IsInt32 xs[i]) (h : (int4Array a xs ⋆ R) m) :
    loadVal m .l .w true (a + BitVec.ofNat 64 (4 * i)) = some xs[i] := by
  rw [int4Array_focus a xs hi, sep_assoc] at h; exact loadsw_int4 h h32

/-! ## Arrays at a concrete address -/

theorem loadsw_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt32 xs[i]) (h : (int4Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (4 * i) := by rfl) :
    loadVal m .l .w true p = some xs[i] := heq ▸ loadsw_int4Array hi hv h

theorem loadl_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (8 * i) := by rfl) :
    loadVal m .l .l true p = some xs[i] := heq ▸ loadl_word8Array hi h

theorem loadsb_at {a p : Val} {xs : List Val} (i : Nat) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt8 xs[i]) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    loadVal m .l .b true p = some xs[i] := heq ▸ loadsb_byte1Array hi hv h

theorem storeb_at {a : Val} {xs : List Val} (i : Nat) (p v : Val) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    storeOk m .b p ∧ (byte1Array a (xs.set i v) ⋆ R) (storeMem m .b p v) :=
  heq ▸ storeb_byte1Array v hi h

theorem ld_w_step {m : Mem 64} {p : Val} {Q : Val → Prop} (a : Val) (i : Nat)
    {xs : List Val} {R : Mem 64 → Prop} {v : Val}
    (h : (int4Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 (4 * i))
    (hi : xs[i]? = some v) (hv : IsInt32 v) (hk : Q v) :
    ∃ x, loadVal m .l .w true p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v, hget ▸ loadsw_at i hlt (hget ▸ hv) h heq, hk⟩

theorem ld_l_step {m : Mem 64} {p : Val} {Q : Val → Prop} (a : Val) (i : Nat)
    {xs : List Val} {R : Mem 64 → Prop} {v : Val}
    (h : (word8Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 (8 * i))
    (hi : xs[i]? = some v) (hk : Q v) :
    ∃ x, loadVal m .l .l true p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v, hget ▸ loadl_at i hlt h heq, hk⟩

theorem ld_b_step {m : Mem 64} {p : Val} {Q : Val → Prop} (a : Val) (i : Nat)
    {xs : List Val} {R : Mem 64 → Prop} {v : Val}
    (h : (byte1Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 i)
    (hi : xs[i]? = some v) (hv : IsInt8 v) (hk : Q v) :
    ∃ x, loadVal m .l .b true p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v, hget ▸ loadsb_at i hlt (hget ▸ hv) h heq, hk⟩

end LeanQbe
