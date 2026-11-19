module

public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.BitVec
public import Kraken.Bedrock2.Test.LratTrimSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kraken's `byte1` / `int4` / `word8` cells and arrays for `LeanQbe.T` (`T4`)

Typed-IR counterpart of `LeanQbe/Logic/Cells.lean` using `LeanQbe.T.loadVal` at types
`i8` / `i32` / `i64` (so widths are exact in the IR, and extensions happen via `zext`/`sext`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## Values that fit in 8 or 32 bits -/

theorem sext8 (v : BitVec 64) (h : IsInt8 v) : (v.setWidth 8).signExtend 64 = v := by
  unfold IsInt8 at h; grind

theorem sext32 (v : BitVec 64) (h : IsInt32 v) : (v.setWidth 32).signExtend 64 = v := by
  unfold IsInt32 at h; grind

theorem zext8 (v : BitVec 64) : (v.setWidth 8).setWidth 64 = v &&& 0xff#64 := by
  grind

theorem zext32 (v : BitVec 64) : (v.setWidth 32).setWidth 64 = v &&& 0xffffffff#64 := by
  grind

private theorem setWidth_of_ofInt {n : Nat} (v : BitVec 64) :
    BitVec.ofInt n (v.toNat : Int) = v.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

private theorem setWidth64_toNat_mod {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    Int.toBytes ((Ty.bits n).bytes) ((v.setWidth 64).toNat : Int) =
      Int.toBytes ((Ty.bits n).bytes) (v.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  have hpow : (2 : Int) ^ (8 * (Ty.bits n).bytes) = ((2 ^ (8 * (Ty.bits n).bytes) : Nat) : Int) := by
    push_cast; rfl
  have hsw : (v.setWidth 64).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hn))
  rw [hsw]

/-! ## Cells -/

theorem load_byte1 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (byte1 a v ⋆ R) m) : loadVal m i8 a = some (v.setWidth 8) := by
  rw [loadVal_toBytes_bits (n := 8) (by decide) h, setWidth_of_ofInt]

theorem load_int4 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (int4 a v ⋆ R) m) : loadVal m i32 a = some (v.setWidth 32) := by
  rw [loadVal_toBytes_bits (n := 32) (by decide) h, setWidth_of_ofInt]

theorem load_word8 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8 a v ⋆ R) m) : loadVal m i64 a = some v := by
  rw [loadVal_toBytes_bits (n := 64) (by decide) h]
  simp only [Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, ← Int.natCast_emod, Nat.mod_eq_of_lt v.isLt, Int.toNat_natCast]

theorem store_byte1 {a v0 : BitVec 64} (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (byte1 a v0 ⋆ R) m) :
    storeOk m i8 a ∧ (byte1 a (v.setWidth 64) ⋆ R) (storeMem m i8 a v) := by
  obtain ⟨hok, hmem⟩ := store_toBytes_bits (n := 8) v rfl (by decide) h
  refine ⟨hok, ?_⟩
  unfold byte1
  have hsw : Int.toBytes 1 (v.setWidth 64).toNat = Int.toBytes (Ty.bits 8).bytes v.toNat :=
    setWidth64_toNat_mod (n := 8) (by decide) v
  rw [hsw]; exact hmem

theorem store_int4 {a v0 : BitVec 64} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (int4 a v0 ⋆ R) m) :
    storeOk m i32 a ∧ (int4 a (v.setWidth 64) ⋆ R) (storeMem m i32 a v) := by
  obtain ⟨hok, hmem⟩ := store_toBytes_bits (n := 32) v rfl (by decide) h
  refine ⟨hok, ?_⟩
  unfold int4
  have hsw : Int.toBytes 4 (v.setWidth 64).toNat = Int.toBytes (Ty.bits 32).bytes v.toNat :=
    setWidth64_toNat_mod (n := 32) (by decide) v
  rw [hsw]; exact hmem

theorem store_word8 {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8 a v0 ⋆ R) m) :
    storeOk m i64 a ∧ (word8 a v ⋆ R) (storeMem m i64 a v) :=
  store_toBytes_bits (n := 64) v rfl (by decide) h

theorem word8_eq_int4_sep (a v : BitVec 64) :
    word8 a v = (int4 a v ⋆ Eq (((Int.toBytes 8 v.toNat).drop 4).At (a + 4))) := by
  unfold word8 int4
  conv => lhs; rw [← List.take_append_drop 4 (Int.toBytes 8 v.toNat)]
  exact Mem.At_append_sep (Int.toBytes 4 v.toNat) ((Int.toBytes 8 v.toNat).drop 4) a
    (by simp [Int.toBytes_length])

theorem load_int4_of_word8 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8 a v ⋆ R) m) : loadVal m i32 a = some (v.setWidth 32) := by
  rw [word8_eq_int4_sep, sep_assoc] at h
  exact load_int4 h

/-! ## Arrays -/

theorem load_byte1Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some (xs[i].setWidth 8) := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h; exact load_byte1 h

theorem store_byte1Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (byte1Array a (xs.set i (v.setWidth 64)) ⋆ R)
        (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_byte1 v h
  exact ⟨h1, by rwa [byte1Array_set a xs hi, sep_assoc]⟩

theorem load_int4Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some (xs[i].setWidth 32) := by
  rw [int4Array_focus a xs hi, sep_assoc] at h; exact load_int4 h

theorem store_int4Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (int4Array a (xs.set i (v.setWidth 64)) ⋆ R)
        (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) := by
  rw [int4Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_int4 v h
  exact ⟨h1, by rwa [int4Array_set a xs hi, sep_assoc]⟩

theorem load_word8Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [word8Array_focus a xs hi, sep_assoc] at h; exact load_word8 h

theorem store_word8Array {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (word8Array a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [word8Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_word8 v h
  exact ⟨h1, by rwa [word8Array_set a xs hi, sep_assoc]⟩

/-! ## Arrays at a concrete address -/

theorem loadw_at {a p : BitVec 64} {xs : List (BitVec 64)} (i : Nat) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (4 * i) := by rfl) :
    loadVal m i32 p = some (xs[i].setWidth 32) := heq ▸ load_int4Array hi h

theorem loadl_at {a p : BitVec 64} {xs : List (BitVec 64)} (i : Nat) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (8 * i) := by rfl) :
    loadVal m i64 p = some xs[i] := heq ▸ load_word8Array hi h

theorem loadb_at {a p : BitVec 64} {xs : List (BitVec 64)} (i : Nat) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    loadVal m i8 p = some (xs[i].setWidth 8) := heq ▸ load_byte1Array hi h

theorem storeb_at {a : BitVec 64} {xs : List (BitVec 64)} (i : Nat) (p : BitVec 64) (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 i := by rfl) :
    storeOk m i8 p ∧ (byte1Array a (xs.set i (v.setWidth 64)) ⋆ R) (storeMem m i8 p v) :=
  heq ▸ store_byte1Array v hi h

theorem ld_w_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 32 → Prop} (a : BitVec 64) (i : Nat)
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {v : BitVec 64}
    (h : (int4Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 (4 * i))
    (hi : xs[i]? = some v) (hk : Q (v.setWidth 32)) :
    ∃ x, loadVal m i32 p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v.setWidth 32, hget ▸ loadw_at i hlt h heq, hk⟩

theorem ld_l_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 64 → Prop} (a : BitVec 64) (i : Nat)
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {v : BitVec 64}
    (h : (word8Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 (8 * i))
    (hi : xs[i]? = some v) (hk : Q v) :
    ∃ x, loadVal m i64 p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v, hget ▸ loadl_at i hlt h heq, hk⟩

theorem ld_b_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 8 → Prop} (a : BitVec 64) (i : Nat)
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {v : BitVec 64}
    (h : (byte1Array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 i)
    (hi : xs[i]? = some v) (hk : Q (v.setWidth 8)) :
    ∃ x, loadVal m i8 p = some x ∧ Q x := by
  have hlt : i < xs.length := Nat.lt_of_not_le fun hge => by
    simp [List.getElem?_eq_none hge] at hi
  have hget : xs[i] = v := Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hi)
  exact ⟨v.setWidth 8, hget ▸ loadb_at i hlt h heq, hk⟩

/-! ## Truncating `BitVec 64` stores into `byte1` / `int4` arrays -/

theorem byte1_setWidth8 (a v : BitVec 64) :
    byte1 a ((v.setWidth 8).setWidth 64) = byte1 a v := by
  unfold byte1
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  simp only [Int.take, BitVec.toNat_setWidth]
  have h1 : v.toNat % 2 ^ 8 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt h1]
  exact_mod_cast (Nat.mod_mod_of_dvd v.toNat (Nat.dvd_refl (2 ^ 8)))

theorem int4_setWidth32 (a v : BitVec 64) :
    int4 a ((v.setWidth 32).setWidth 64) = int4 a v := by
  unfold int4
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  simp only [Int.take, BitVec.toNat_setWidth]
  have h1 : v.toNat % 2 ^ 32 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt h1]
  exact_mod_cast (Nat.mod_mod_of_dvd v.toNat (Nat.dvd_refl (2 ^ 32)))

theorem store_byte1Array64 {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (byte1Array a (xs.set i v) ⋆ R) (storeMem m i8 (a + BitVec.ofNat 64 i) (v.setWidth 8)) := by
  obtain ⟨hok, hm'⟩ := store_byte1Array (v.setWidth 8) hi h
  refine ⟨hok, ?_⟩
  rw [byte1Array_set a xs hi, byte1_setWidth8] at hm'
  rwa [byte1Array_set a xs hi]

theorem store_int4Array64 {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (int4Array a (xs.set i v) ⋆ R)
        (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) (v.setWidth 32)) := by
  obtain ⟨hok, hm'⟩ := store_int4Array (v.setWidth 32) hi h
  refine ⟨hok, ?_⟩
  rw [int4Array_set a xs hi, int4_setWidth32] at hm'
  rwa [int4Array_set a xs hi]

end LeanQbe.T
