module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0BigNum` Core Helpers (`Milestone R1`, Part 1)

Proves `Func.wp rtR1Env` contracts for the 16 leaf, allocation, RC, scratch, load/store,
normalization, and comparison functions of `rtR1Mod`:
- `rt_scratch`, `rt_scratch_cap`, `lcnf_nat_alloc`, `bn_dec_nat`, `bn_require_scratch`
- `bn_trim`, `bn_copy`, `bn_zero`, `bn_nat_from_limbs`, `bn_int_from_limbs`
- `bn_nat_len`, `bn_int_len`, `bn_load_nat`, `bn_load_int`, `bn_cmp_fixed`, `bn_cmp`

Also provides shared `@[c0_load]` / `@[c0_store]` lemmas, `array64` slice-splitting helpers, and
`mpzTag` / `LcnfObj` footprint packing lemmas used by `LcnfC0BigNumProof2` and `LcnfC0BigNumProof`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.LeanLCNF.BigNumRt

/-! ## 1. BitVec, Alignment, and `limbsVal` / `array64` Slice Helpers -/

theorem ptr_add_nat_bn (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bv64_and1_eq_zero_of_mod8 {p : BitVec 64} (h : p.toNat % 8 = 0) :
    (p &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (p.toNat &&& (2 ^ 1 - 1)) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
  omega

theorem bv64_shl3_eq_mul8 (i : BitVec 64) : i <<< 3#64 = i * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mul_comm]

theorem bv64_mul8_eq_ofNat (i : BitVec 64) : i * 8#64 = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem bv64_shl3_eq_ofNat (i : BitVec 64) : i <<< 3#64 = BitVec.ofNat 64 (8 * i.toNat) := by
  rw [bv64_shl3_eq_mul8, bv64_mul8_eq_ofNat]

theorem bv64_add_mul8_eq (off k : BitVec 64) :
    (off + k) * 8#64 = BitVec.ofNat 64 (8 * (off.toNat + k.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add, Nat.mul_mod_mod, Nat.mul_comm]

theorem bv64_add_shl3_eq (off k : BitVec 64) :
    (off + k) <<< 3#64 = BitVec.ofNat 64 (8 * (off.toNat + k.toNat)) := by
  rw [bv64_shl3_eq_mul8, bv64_add_mul8_eq]

theorem align8_of_mul8_add16 (n : Nat) : align8 (16 + 8 * n) = 16 + 8 * n := by
  unfold align8
  omega

/-- Split `array64 a xs` at prefix length `k` (`k ≤ xs.length`). -/
theorem array64_split2 (a : BitVec 64) (xs : List (BitVec 64)) (k : Nat) (hk : k ≤ xs.length) :
    array64 a xs =
      (array64 a (xs.take k) ⋆ array64 (a + BitVec.ofNat 64 (8 * k)) (xs.drop k)) := by
  conv => lhs; rw [← List.take_append_drop k xs]
  rw [array64_append, List.length_take_of_le hk]

/-- Split `array64 a xs` into 3 contiguous slices of lengths `k1`, `k2`, and tail. -/
theorem array64_split3 (a : BitVec 64) (xs : List (BitVec 64)) (k1 k2 : Nat)
    (hk : k1 + k2 ≤ xs.length) :
    array64 a xs =
      (array64 a (xs.take k1) ⋆
        array64 (a + BitVec.ofNat 64 (8 * k1)) ((xs.drop k1).take k2) ⋆
        array64 (a + BitVec.ofNat 64 (8 * (k1 + k2))) (xs.drop (k1 + k2))) := by
  rw [array64_split2 a xs k1 (by omega)]
  have hk2 : k2 ≤ (xs.drop k1).length := by simp; omega
  rw [array64_split2 (a + BitVec.ofNat 64 (8 * k1)) (xs.drop k1) k2 hk2,
    ptr_add_nat_bn, List.drop_drop]
  have heq : 8 * k1 + 8 * k2 = 8 * (k1 + k2) := by omega
  rw [heq, ← sep_assoc]

/-- Reassemble a 3-slice `array64` partition when only slices were replaced with equal-length ones.
  -/
theorem array64_join3 (a : BitVec 64) (s1 s2 s3 : List (BitVec 64)) (k1 k2 : Nat)
    (h1 : s1.length = k1) (h2 : s2.length = k2) :
    (array64 a s1 ⋆
      array64 (a + BitVec.ofNat 64 (8 * k1)) s2 ⋆
      array64 (a + BitVec.ofNat 64 (8 * (k1 + k2))) s3) =
      array64 a (s1 ++ s2 ++ s3) := by
  rw [array64_append, array64_append, List.length_append, h1, h2, sep_assoc]

/-- Prefix replacement lemma for `bn_copy` loop steps. -/
theorem replacePrefix_set {src dst : List (BitVec 64)} {i : Nat}
    (his : i < src.length) (hid : i < dst.length) :
    (src.take i ++ dst.drop i).set i src[i] = src.take (i + 1) ++ dst.drop (i + 1) := by
  have hlen : (src.take i).length = i := List.length_take_of_le (Nat.le_of_lt his)
  rw [List.set_append, hlen]
  simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
  have hdrop : dst.drop i = dst[i] :: dst.drop (i + 1) := List.drop_eq_getElem_cons hid
  rw [hdrop, List.set_cons_zero]
  rw [List.take_add_one, List.getElem?_eq_getElem his, Option.toList_some, List.append_assoc]
  rfl

/-- Prefix zeroing lemma for `bn_zero` loop steps. -/
theorem zeroPrefix_set {dst : List (BitVec 64)} {i : Nat} (hid : i < dst.length) :
    (List.replicate i 0#64 ++ dst.drop i).set i 0#64 =
      List.replicate (i + 1) 0#64 ++ dst.drop (i + 1) := by
  have hlen : (List.replicate i 0#64).length = i := List.length_replicate
  rw [List.set_append, hlen]
  simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
  have hdrop : dst.drop i = dst[i] :: dst.drop (i + 1) := List.drop_eq_getElem_cons hid
  rw [hdrop, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

/-! ## 2. Footprint-Indexed `@[c0_load]` / `@[c0_store]` Lemmas -/

@[c0_load] theorem c0_load_cell64_var {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v ⋆ R) m) : loadVal m i64 a = some v :=
  loadVal_cell64 h

theorem c0_store_cell64_var {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 a v0 ⋆ R) m) :
    storeOk m i64 a ∧ (cell64 a v ⋆ R) (storeMem m i64 a v) :=
  store_cell64 v h

@[c0_load] theorem c0_load_cell64_add33672 {rt v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (rt + 33672#64) v ⋆ R) m) : loadVal m i64 (rt + 33672) = some v :=
  loadVal_cell64 h

@[c0_load] theorem c0_load_cell64_add33680 {rt v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (rt + 33680#64) v ⋆ R) m) : loadVal m i64 (rt + 33680) = some v :=
  loadVal_cell64 h

@[c0_load] theorem bn_c0_load_cell64_add8_imm {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8) = some v :=
  loadVal_cell64 h

@[c0_store] theorem bn_c0_store_cell64_add8_imm {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 8) ∧ (cell64 (a + 8#64) v ⋆ R) (storeMem m i64 (a + 8) v) :=
  store_cell64 v h

@[c0_load] theorem c0_load_array64_zero {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (h0 : 0 < xs.length) :
    loadVal m i64 a = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 h

@[c0_store] theorem c0_store_array64_zero {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (h0 : 0 < xs.length) :
    storeOk m i64 a ∧ (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 a v) := by
  simpa using store_array64 (i := 0) v h0 h

@[c0_load] theorem bn_c0_load_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + (i <<< 3)) = some xs[i.toNat] := by
  rw [show (i <<< 3) = i <<< 3#64 from rfl, bv64_shl3_eq_ofNat]; exact loadVal_array64 hi h

@[c0_store] theorem bn_c0_store_array64_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + (i <<< 3)) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + (i <<< 3)) v) := by
  rw [show (i <<< 3) = i <<< 3#64 from rfl, bv64_shl3_eq_ofNat]; exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_mul8_r {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8 * i) = some xs[i.toNat] := by
  rw [show (8 * i : BitVec 64) = 8#64 * i from rfl, BitVec.mul_comm 8#64 i, bv64_mul8_eq_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_mul8_r {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 8 * i) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8 * i) v) := by
  rw [show (8 * i : BitVec 64) = 8#64 * i from rfl, BitVec.mul_comm 8#64 i, bv64_mul8_eq_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_mul8_l {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i * 8) = some xs[i.toNat] := by
  rw [show (i * 8 : BitVec 64) = i * 8#64 from rfl, bv64_mul8_eq_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_mul8_l {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + i * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i * 8) v) := by
  rw [show (i * 8 : BitVec 64) = i * 8#64 from rfl, bv64_mul8_eq_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_sub1_mul8 {a n : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    loadVal m i64 (a + (n - 1) * 8) = some (xs[n.toNat - 1]'(by omega)) := by
  have hsub : (n - 1#64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]; rfl
  rw [show ((n - 1) * 8 : BitVec 64) = (n - 1#64) * 8#64 from rfl, bv64_mul8_eq_ofNat, hsub]
  exact loadVal_array64 (by omega) h

@[c0_store] theorem c0_store_array64_sub1_mul8 {a n : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    storeOk m i64 (a + (n - 1) * 8) ∧
      (array64 a (xs.set (n.toNat - 1) v) ⋆ R)
        (storeMem m i64 (a + (n - 1) * 8) v) := by
  have hsub : (n - 1#64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]; rfl
  rw [show ((n - 1) * 8 : BitVec 64) = (n - 1#64) * 8#64 from rfl, bv64_mul8_eq_ofNat, hsub]
  exact store_array64 v (by omega) h

@[c0_load] theorem c0_load_array64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + ((off + k) <<< 3)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show ((off + k) <<< 3) = (off + k) <<< 3#64 from rfl, bv64_add_shl3_eq]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + ((off + k) <<< 3)) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + ((off + k) <<< 3)) v) := by
  rw [show ((off + k) <<< 3) = (off + k) <<< 3#64 from rfl, bv64_add_shl3_eq]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_off_mul8 {a off k : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + 8 * (off + k)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 * (off + k) : BitVec 64) = 8#64 * (off + k) from rfl,
    BitVec.mul_comm 8#64 (off + k), bv64_add_mul8_eq]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_off_mul8 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + 8 * (off + k)) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + 8 * (off + k)) v) := by
  rw [show (8 * (off + k) : BitVec 64) = 8#64 * (off + k) from rfl,
    BitVec.mul_comm 8#64 (off + k), bv64_add_mul8_eq]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_sub1_shl3 {a n : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    loadVal m i64 (a + ((n - 1) <<< 3)) = some (xs[n.toNat - 1]'(by omega)) := by
  have hsub : (n - 1#64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]
    rfl
  rw [show ((n - 1) <<< 3) = (n - 1#64) <<< 3#64 from rfl, bv64_shl3_eq_ofNat, hsub]
  exact loadVal_array64 (by omega) h

@[c0_store] theorem c0_store_array64_sub1_shl3 {a n : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    storeOk m i64 (a + ((n - 1) <<< 3)) ∧
      (array64 a (xs.set (n.toNat - 1) v) ⋆ R)
        (storeMem m i64 (a + ((n - 1) <<< 3)) v) := by
  have hsub : (n - 1#64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]
    rfl
  rw [show ((n - 1) <<< 3) = (n - 1#64) <<< 3#64 from rfl, bv64_shl3_eq_ofNat, hsub]
  exact store_array64 v (by omega) h

@[c0_load] theorem c0_load_array64_obj2_imm {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m) (h0 : 0 < xs.length) :
    loadVal m i64 (a + 16) = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 h

@[c0_store] theorem c0_store_array64_obj2_imm {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (h0 : 0 < xs.length) :
    storeOk m i64 (a + 16) ∧
      (array64 (a + 16#64) (xs.set 0 v) ⋆ R) (storeMem m i64 (a + 16) v) := by
  simpa using store_array64 (i := 0) v h0 h

@[c0_load] theorem c0_load_array64_obj2_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    loadVal m i64 (a + ((2 + i) <<< 3)) = some xs[i.toNat] := by
  have heq : a + ((2 + i) <<< 3) = (a + 16#64) + BitVec.ofNat 64 (8 * i.toNat) := by
    rw [show ((2 + i) <<< 3) = (2#64 + i) <<< 3#64 from rfl, bv64_add_shl3_eq, ptr_add_nat_bn]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mul_add]
  rw [heq]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_obj2_shl3 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + ((2 + i) <<< 3)) ∧
      (array64 (a + 16#64) (xs.set i.toNat v) ⋆ R)
        (storeMem m i64 (a + ((2 + i) <<< 3)) v) := by
  have heq : a + ((2 + i) <<< 3) = (a + 16#64) + BitVec.ofNat 64 (8 * i.toNat) := by
    rw [show ((2 + i) <<< 3) = (2#64 + i) <<< 3#64 from rfl, bv64_add_shl3_eq, ptr_add_nat_bn]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mul_add]
  rw [heq]
  exact store_array64 v hi h

@[c0_store] theorem c0_store_array64_obj2_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + (2 + i) * 8) ∧
      (array64 (a + 16#64) (xs.set i.toNat v) ⋆ R)
        (storeMem m i64 (a + (2 + i) * 8) v) := by
  rw [show ((2 + i) * 8 : BitVec 64) = (2 + i) <<< 3 from (bv64_shl3_eq_mul8 (2 + i)).symm]
  exact c0_store_array64_obj2_shl3 v h hi

@[c0_store] theorem c0_store_array64_obj2_shl3_comm {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (a + ((i + 2) <<< 3)) ∧
      (array64 (a + 16#64) (xs.set i.toNat v) ⋆ R)
        (storeMem m i64 (a + ((i + 2) <<< 3)) v) := by
  rw [BitVec.add_comm i 2]
  exact c0_store_array64_obj2_shl3 v h hi

/-! ## 3. `LcnfObj` Header & MPZ Region Packing Lemmas -/

private theorem header_getLsbD_bn (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (i : Nat) :
    o.header.getLsbD i =
      if i < 32 then o.rc.toNat.testBit i
      else if i < 48 then o.csSz.testBit (i - 32)
      else if i < 56 then o.other.testBit (i - 48)
      else if i < 64 then o.tag.testBit (i - 56)
      else false := by
  by_cases hi : i < 64
  · simp only [LcnfObj.header, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    by_cases h32 : i < 32
    · simp [h32, show i < 48 by omega, show i < 56 by omega]
    · have hrcf : o.rc.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le o.rc.isLt
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
      by_cases h48 : i < 48
      · simp [h32, h48, show i < 56 by omega, show i - 32 < 64 by omega, hrcf]
      · have hcsf : o.csSz.testBit (i - 32) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show o.csSz < 2 ^ 16 from hcs)
            (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
        by_cases h56 : i < 56
        · simp [h32, h48, h56, show i - 32 < 64 by omega, show i - 48 < 64 by omega, hrcf, hcsf]
        · have hothf : o.other.testBit (i - 48) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show o.other < 2 ^ 8 from hoth)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
          simp [h32, h48, h56, show i - 32 < 64 by omega, show i - 48 < 64 by omega,
            show i - 56 < 64 by omega, hrcf, hcsf, hothf]
  · have hge : ¬(i < 32) ∧ ¬(i < 48) ∧ ¬(i < 56) ∧ ¬(i < 64) := by omega
    have hfalse : o.header.getLsbD i = false := by
      rw [BitVec.getLsbD]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le o.header.isLt
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    simp [hfalse, hge]

theorem LcnfObj.header_setWidth32 (o : LcnfObj) (hwf : o.Wf) :
    o.header.setWidth 32 = o.rc := by
  rcases hwf with ⟨_, _, _, hcs, hoth, _⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth, header_getLsbD_bn o hcs hoth]
  by_cases hi : i < 32
  · simp [hi, BitVec.getLsbD]
  · have hrcf : o.rc.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le o.rc.isLt
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    simp [hi, BitVec.getLsbD, hrcf]

theorem LcnfObj.header_other_byte (o : LcnfObj) (hwf : o.Wf) :
    ((o.header >>> 48#64) &&& 0xff#64) = BitVec.ofNat 64 o.other := by
  rcases hwf with ⟨_, _, _, hcs, hoth, _⟩
  rw [show (o.header >>> 48#64) = (o.header >>> 48) from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    header_getLsbD_bn o hcs hoth]
  have hff : (0xff : Nat) = 2 ^ 8 - 1 := rfl
  rw [hff, Nat.testBit_two_pow_sub_one]
  by_cases hi8 : i < 8
  · simp [show i < 64 by omega, hi8, show ¬(48 + i < 32) by omega,
      show ¬(48 + i < 48) by omega, show 48 + i < 56 by omega]
  · have hof : o.other.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show o.other < 2 ^ 8 from hoth)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
    by_cases hi64 : i < 64 <;> simp [hi8, hi64, hof]

theorem LcnfObj.header_dec_rc (o : LcnfObj) (hwf : o.Wf) (hrc : 1 < o.rc.toInt) :
    ((o.header &&& 0xffffffff00000000#64) |||
        ((BitVec.ofNat 32 (o.rc.toNat - 1)).setWidth 64)) =
      (o.withRc (o.rc - 1#32)).header := by
  rcases hwf with ⟨_, _, _, hcs, hoth, _⟩
  have hrcSub : (o.rc - 1#32).toNat = o.rc.toNat - 1 := by
    have h1 : 1 ≤ o.rc.toNat := by
      have hmsb := BitVec.toInt_eq_msb_cond o.rc
      cases hms : o.rc.msb <;> rw [hms] at hmsb <;> simp at hmsb <;> omega
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h1)]
    rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofNat, header_getLsbD_bn o hcs hoth,
    header_getLsbD_bn (o.withRc (o.rc - 1#32)) hcs hoth]
  have hmask : (0xffffffff00000000 : Nat).testBit i = decide (32 ≤ i ∧ i < 64) := by
    have heq : (0xffffffff00000000 : Nat) = (2 ^ 32 - 1) <<< 32 := by decide
    rw [heq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : 32 ≤ i <;> by_cases h2 : i < 64 <;> simp [h1, h2] <;> omega
  rw [hmask]
  by_cases hi64 : i < 64
  · by_cases hi32 : i < 32
    · simp [hi64, hi32, show ¬(32 ≤ i) by omega, LcnfObj.withRc, hrcSub]
    · have hrf1 : (o.rc.toNat - 1).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) o.rc.isLt)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
      by_cases h48 : i < 48 <;> by_cases h56 : i < 56 <;>
        simp [hi64, hi32, h48, h56, show 32 ≤ i by omega, LcnfObj.withRc, hrf1]
  · simp [hi64]

theorem LcnfObj.mpzMeta_arrSize (o : LcnfObj) (hcap : o.cap < 2 ^ 32) (harr : o.arrSize < 2 ^ 32) :
    o.mpzMeta >>> 32#64 = BitVec.ofNat 64 o.arrSize := by
  rw [show o.mpzMeta >>> 32#64 = o.mpzMeta >>> 32 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hm : (o.mpzMeta) = BitVec.ofNat 64 o.cap ||| (BitVec.ofNat 64 o.arrSize <<< 32) := rfl
  rw [hm]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  by_cases hi32 : i < 32
  · have hcf : o.cap.testBit (32 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcap (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [show i < 64 by omega, show 32 + i < 64 by omega, hcf]
  · have haf : o.arrSize.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le harr (Nat.pow_le_pow_right (by decide) (by omega)))
    have hnot : ¬(32 + i < 64) := by omega
    by_cases hi64 : i < 64 <;> simp [hi64, haf, hnot]

theorem LcnfObj.header_or_other_one (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other = 0) :
    (o.header ||| (1#64 <<< 48#64)) = { o with other := 1 }.header := by
  rw [show (1#64 <<< 48#64) = (1#64 <<< 48) from rfl]
  have hoth1 : ({ o with other := 1 } : LcnfObj).other < 256 := by dsimp; decide
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    header_getLsbD_bn o hcs (by omega),
    header_getLsbD_bn { o with other := 1 } hcs hoth1]
  simp only [BitVec.getLsbD_ofNat]
  by_cases hi64 : i < 64
  · by_cases hi48 : i = 48
    · subst hi48; simp [hoth]
    · by_cases h48 : i < 48
      · by_cases h32 : i < 32 <;> simp [hi64, h48, h32]
      · have hzero : (1 : Nat).testBit (i - 48) = false := by
          cases h : i - 48 with
          | zero => omega
          | succ k => simp [Nat.testBit, Nat.shiftRight_succ_inside]
        by_cases h56 : i < 56 <;>
          simp [hi64, h48, show ¬(i < 32) by omega, h56, hoth, hzero]
  · simp [hi64, show ¬(i < 32) by omega, show ¬(i < 48) by omega, show ¬(i < 56) by omega]

theorem LcnfObj.withRc_wf {o : LcnfObj} (hwf : o.Wf) {rc' : BitVec 32} (hnn : 0 ≤ rc'.toInt) :
    (o.withRc rc').Wf := by
  rcases hwf with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, hnn, h4, h5, h6, h7, h8, h9, h10⟩

@[simp] theorem LcnfObj.withRc_cloMeta (o : LcnfObj) (rc' : BitVec 32) :
    (o.withRc rc').cloMeta = o.cloMeta := rfl

@[simp] theorem LcnfObj.withRc_mpzMeta (o : LcnfObj) (rc' : BitVec 32) :
    (o.withRc rc').mpzMeta = o.mpzMeta := rfl

@[simp] theorem LcnfObj.withRc_totalBytes (o : LcnfObj) (rc' : BitVec 32) :
    (o.withRc rc').totalBytes = o.totalBytes := rfl

private def lcnfObjMemTail (o : LcnfObj) : Mem 64 → Prop :=
  if o.tag = closureTag then
    cell64 (o.addr + 8#64) o.funId ⋆
    cell64 (o.addr + 16#64) o.cloMeta ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (o.csSz - (24 + 8 * o.fields.length))
  else if o.tag = arrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (8 * (o.cap - o.fields.length))
  else if o.tag = sarrayTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    bytes (o.addr + 24#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
      (o.totalBytes - (24 + o.scalarData.length))
  else if o.tag = stringTag then
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
    bytes (o.addr + 32#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
      (o.totalBytes - (32 + o.scalarData.length))
  else if o.tag = mpzTag then
    cell64 (o.addr + 8#64) o.mpzMeta ⋆
    array64 (o.addr + 16#64) o.limbs
  else
    let soff := 8 + 8 * o.fields.length
    array64 (o.addr + 8#64) o.fields ⋆
    bytes (o.addr + BitVec.ofNat 64 soff) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (soff + o.scalarData.length))
      (o.csSz - (soff + o.scalarData.length))

private theorem lcnfObjMem_eq_header_tail (o : LcnfObj) :
    lcnfObjMem o = (cell64 o.addr o.header ⋆ lcnfObjMemTail o) := by
  unfold lcnfObjMem lcnfObjMemTail closureTag arrayTag sarrayTag stringTag mpzTag
  by_cases h1 : o.tag = 245; · simp [h1, sep_assoc]
  by_cases h2 : o.tag = 246; · simp [h2, sep_assoc]
  by_cases h3 : o.tag = 248; · simp [h3, sep_assoc]
  by_cases h4 : o.tag = 249; · simp [h4, sep_assoc]
  by_cases h5 : o.tag = 250; · simp [h5, sep_assoc]
  simp [h1, h2, h3, h4, h5, sep_assoc]

theorem lcnfObjMem_load_header {o : LcnfObj} (_hwf : o.Wf) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) : loadVal m i64 o.addr = some o.header := by
  rw [lcnfObjMem_eq_header_tail, sep_assoc] at hm
  exact loadVal_cell64 hm

theorem lcnfObjMem_store_header {o : LcnfObj} (_hwf : o.Wf) (rc' : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    storeOk m i64 o.addr ∧
      (lcnfObjMem (o.withRc rc') ⋆ R) (storeMem m i64 o.addr (o.withRc rc').header) := by
  rw [lcnfObjMem_eq_header_tail, sep_assoc] at hm
  obtain ⟨hok, hs⟩ := store_cell64 (o.withRc rc').header hm
  rw [lcnfObjMem_eq_header_tail, show lcnfObjMemTail (o.withRc rc') = lcnfObjMemTail o from rfl,
    sep_assoc]
  exact ⟨hok, hs⟩

theorem lcnfObjMem_mpz_eq {o : LcnfObj} (htag : o.tag = mpzTag) :
    lcnfObjMem o = (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
      array64 (o.addr + 16#64) o.limbs) := by
  simp [lcnfObjMem, htag, mpzTag, closureTag, arrayTag, sarrayTag, stringTag]

theorem lcnfObjMem_mpz_elim {o : LcnfObj} (htag : o.tag = mpzTag) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
      array64 (o.addr + 16#64) o.limbs ⋆ R) m := by
  rw [lcnfObjMem_mpz_eq htag] at hm
  exact sep_ac hm

theorem lcnfObjMem_mpz_intro {o : LcnfObj} (htag : o.tag = mpzTag) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
      array64 (o.addr + 16#64) o.limbs ⋆ R) m) :
    (lcnfObjMem o ⋆ R) m := by
  rw [lcnfObjMem_mpz_eq htag]
  exact sep_ac hm

theorem region_to_cell64_bn {a : BitVec 64} {m : Mem 64} (h : region a 8 m) :
    ∃ v : BitVec 64, cell64 a v m := by
  obtain ⟨xs, hlen, harr⟩ := bn_region_to_array64 1 (by decide) h
  rcases xs with _ | ⟨v, _ | _⟩ <;> simp at hlen
  rw [array64_cons, array64_nil, sep_emp] at harr
  exact ⟨v, harr⟩

theorem region_to_mpz_parts {p : BitVec 64} {n : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hn1 : 1 ≤ n) (hnmax : n ≤ mpzMaxLimbs)
    (hm : (region p (16 + 8 * n) ⋆ R) m) :
    ∃ (w0 w1 : BitVec 64) (limbs : List (BitVec 64)),
      limbs.length = n ∧
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ array64 (p + 16#64) limbs ⋆ R) m := by
  have hlt64 : 16 + 8 * n ≤ 2 ^ 64 := by unfold mpzMaxLimbs at hnmax; omega
  have h16 : region p (16 + 8 * n) = (region p 16 ⋆ region (p + 16#64) (8 * n)) := by
    simpa [ptr_add_nat_bn] using region_split (a := p) (n1 := 16) (n2 := 8 * n) hlt64
  have h8 : region p 16 = (region p 8 ⋆ region (p + 8#64) 8) :=
    region_split (a := p) (n1 := 8) (n2 := 8) (by decide)
  rw [h16, h8] at hm
  have hm1 : (region p 8 ⋆ (region (p + 8#64) 8 ⋆ (region (p + 16#64) (8 * n) ⋆ R))) m :=
    sep_ac hm
  obtain ⟨m0, mRest, rfl, hd0, hr0, hRest⟩ := hm1
  obtain ⟨w0, hc0⟩ := region_to_cell64_bn hr0
  obtain ⟨m1, mRest2, rfl, hd1, hr1, hRest2⟩ := hRest
  obtain ⟨w1, hc1⟩ := region_to_cell64_bn hr1
  obtain ⟨m2, mR, rfl, hd2, hr2, hR⟩ := hRest2
  obtain ⟨limbs, hlen, harr⟩ := bn_region_to_array64 n (by omega) hr2
  refine ⟨w0, w1, limbs, hlen, ?_⟩
  have htmp : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ (array64 (p + 16#64) limbs ⋆ R)))
      (m0.union (m1.union (m2.union mR))) :=
    ⟨m0, m1.union (m2.union mR), rfl, hd0, hc0,
      ⟨m1, m2.union mR, rfl, hd1, hc1, ⟨m2, mR, rfl, hd2, harr, hR⟩⟩⟩
  exact sep_ac htmp

theorem intSmallEnc_sshiftRight1 {z : Int} (hlo : -(2 ^ 62 : Int) ≤ z) (hhi : z < (2 ^ 62 : Int)) :
    let w := BitVec.ofInt 64 (2 * z + 1)
    (w &&& 1#64) = 1#64 ∧ w.sshiftRight 1 = BitVec.ofInt 64 z := by
  obtain ⟨h1, h2⟩ := intSmallEnc_toInt hlo hhi
  refine ⟨h1, ?_⟩
  apply BitVec.eq_of_toInt_eq
  rw [h2]
  have hmod : (z : Int).bmod (2 ^ 64) = z := by
    by_cases hz : 0 ≤ z
    · rw [Int.bmod_def, Int.emod_eq_of_lt (by omega) (by omega)]
      split <;> omega
    · have h1 := Int.add_mul_emod_self_right z 1 (↑(2 ^ 64 : Nat) : Int)
      rw [Int.one_mul] at h1
      rw [Int.bmod_def, ← h1, Int.emod_eq_of_lt (by omega) (by omega)]
      split <;> omega
  simpa [BitVec.toInt_ofInt] using hmod.symm

theorem bv64_ne_of_and1 {w : BitVec 64} (h : (w &&& 1#64) = 1#64) : w ≠ 0#64 := by
  intro hw; rw [hw] at h; simp at h

theorem wp_call_of {Γ : Env} {rs as bs : List Ty} {f : Sym} {args : Tup (Arg Val) as}
    {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Γ f as bs (vals args) m (fun res m' => wp Γ Q X (k res) m') X) :
    wp Γ Q X (Expr.call f args k) m := by
  unfold wp
  exact ⟨_, X, h, fun _ _ hp => hp, fun _ _ _ _ hx => hx⟩

/-! ## 4. Proofs of Core Helpers (`rt_scratch` .. `bn_cmp`) -/

theorem rt_scratch_wp :
    ∀ xs m Q X, rtScratchSpec xs m Q X → Func.wp rtR1Env rt_scratch.body xs m Q X := by
  intro ⟨rt, ⟨⟩⟩ m Q X ⟨scr, R, hm, hQ⟩
  dsimp only [Func.wp, rt_scratch, rt_scratch_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps!
  exact hQ

theorem rt_scratch_cap_wp :
    ∀ xs m Q X, rtScratchCapSpec xs m Q X → Func.wp rtR1Env rt_scratch_cap.body xs m Q X := by
  intro ⟨rt, ⟨⟩⟩ m Q X ⟨cap, R, hm, hQ⟩
  dsimp only [Func.wp, rt_scratch_cap, rt_scratch_cap_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps!
  exact hQ

theorem lcnf_nat_alloc_wp :
    ∀ xs m Q X, lcnfNatAllocSpec xs m Q X → Func.wp rtR1Env lcnf_nat_alloc.body xs m Q X := by
  intro ⟨rt, nlimbs, ⟨⟩⟩ m Q X hspec
  rcases hspec with ⟨st, R, hmax, hbd, havail, hm, hQ⟩
  dsimp only at havail hm hQ
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  have hn1 : 1 ≤ n' := Nat.le_max_left 1 _
  have hnMax : n' ≤ mpzMaxLimbs := by
    dsimp [n']; exact Nat.max_le.mpr ⟨by unfold mpzMaxLimbs; omega, hmax⟩
  have hn'lt : n' < 2 ^ 64 := by unfold mpzMaxLimbs at hnMax; omega
  have hbytesLo : rtMinObjBytes ≤ bytes := by unfold rtMinObjBytes; omega
  have hbytesMax : bytes < rtMaxObjBytes := by
    dsimp [bytes]; unfold mpzMaxLimbs rtMaxObjBytes at *; omega
  have hbytesMod : bytes % 8 = 0 := by dsimp [bytes]; omega
  have hn'bv : (BitVec.ofNat 64 n').toNat = n' := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn'lt]
  have hbytesBv : (16 + 8 * BitVec.ofNat 64 n' : BitVec 64) = BitVec.ofNat 64 bytes := by
    apply BitVec.eq_of_toNat_eq
    dsimp [bytes]
    simp only [hn'bv, BitVec.toNat_ofNat]
    omega
  have hbytesToNat : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnMax; dsimp [bytes]; omega)]
  have hAllocTail : ∀ csVal : BitVec 64,
      csVal = (if bytes < 65536 then BitVec.ofNat 64 bytes else 0#64) →
      wp rtR1Env Q X
        (Expr.call (V := Val) (L := Cont) (rs := [i64]) (as := [i64,
          i64]) (bs := [i64]) "lcnf_alloc"
          (Arg.var rt, Arg.var (BitVec.ofNat 64 bytes), ())
          fun (p : Tup Val [i64]) =>
          Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) }
            fun (p_1 : Tup Val [i64]) =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var csVal, Arg.var p_1.fst,
                ()) }
              fun (p_2 : Tup Val [i64]) =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.or i64, args := (Arg.imm 1, Arg.var p_2.fst,
                  ()) }
                fun (p_3 : Tup Val [i64]) =>
                Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 56, ()) }
                  fun (p_4 : Tup Val [i64]) =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.imm 250,
                      Arg.var p_4.fst, ()) }
                    fun (p_5 : Tup Val [i64]) =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p_3.fst,
                        Arg.var p_5.fst, ()) }
                      fun (p_6 : Tup Val [i64]) =>
                      Expr.store (Arg.var p_6.fst) (Arg.var p.fst)
                        (Expr.let_
                          { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst,
                            Arg.imm 8, ()) }
                          fun (p_7 : Tup Val [i64]) =>
                          Expr.let_
                            { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) }
                            fun (p_8 : Tup Val [i64]) =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.shl i64,
                                args := (Arg.var (BitVec.ofNat 64 n'), Arg.var p_8.fst, ()) }
                              fun (p_9 : Tup Val [i64]) =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.or i64,
                                  args := (Arg.var (BitVec.ofNat 64 n'), Arg.var p_9.fst, ()) }
                                fun (p_10 : Tup Val [i64]) =>
                                Expr.store (Arg.var p_10.fst) (Arg.var p_7.fst)
                                  (Expr.group
                                    (fun (Js : Tup Cont [[i64]]) =>
                                      Blocks.cons
                                        (fun (p_11 : Tup Val [i64]) =>
                                          Expr.let_
                                            { sig := [i64, i64],
                                              code := OpCode.cmp CmpOp.ult i64 Ty.bool (by rfl),
                                              args := (Arg.var p_11.fst,
                                                Arg.var (BitVec.ofNat 64 n'), ()) }
                                            fun (p_12 : Tup Val [Ty.bool]) =>
                                            Expr.jnz (Arg.var p_12.fst)
                                              (Expr.let_
                                                { sig := [i64, i64], code := OpCode.add i64,
                                                  args := (Arg.imm 2, Arg.var p_11.fst, ()) }
                                                fun (p_13 : Tup Val [i64]) =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.mul i64,
                                                    args := (Arg.var p_13.fst, Arg.imm 8, ()) }
                                                  fun (p_14 : Tup Val [i64]) =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.add i64,
                                                      args := (Arg.var p.fst, Arg.var p_14.fst,
                                                        ()) }
                                                    fun (p_15 : Tup Val [i64]) =>
                                                    Expr.store (@Arg.imm Val i64 0#64)
                                                      (Arg.var p_15.fst)
                                                      (Expr.let_
                                                        { sig := [i64, i64], code := OpCode.add i64,
                                                          args := (Arg.var p_11.fst, Arg.imm 1,
                                                            ()) }
                                                        fun (p_16 : Tup Val [i64]) =>
                                                        Expr.jump Js.fst (Arg.var p_16.fst, ())))
                                              (Expr.ret (Arg.var p.fst, ())))
                                        Blocks.nil)
                                    fun (Js : Tup Cont [[i64]]) =>
                                      Expr.jump Js.fst (@Arg.imm Val i64 0#64, ()))))
        m := by
    intro csVal hcs
    subst hcs
    apply wp_call_of
    apply rtR1Env_lcnf_alloc
    dsimp only [BigNumRt.lcnfAllocSpec, vals, Tup.map, Arg.val]
    refine ⟨st, R, ?_, ?_, ?_, ?_, hm, ?_⟩
    · rw [hbytesToNat]; unfold mpzMaxLimbs at hnMax; dsimp [bytes]; omega
    · rw [hbytesToNat, align8_of_mul8_add16]; exact hbytesLo
    · rw [hbytesToNat, align8_of_mul8_add16]; exact hbytesMax
    · rw [hbytesToNat, align8_of_mul8_add16]; exact havail
    ·
        intro p st' mAlloc hpNz hpMod hpres hrem hmAlloc
        rw [hbytesToNat, align8_of_mul8_add16] at hmAlloc
        obtain ⟨w0, w1, limbs, hlen, hpParts⟩ :=
          region_to_mpz_parts hn1 hnMax (by
            have hmReg : (region p (16 + 8 * n') ⋆ (rtC0Inv rt st' ⋆ R)) mAlloc := sep_ac hmAlloc
            simpa [bytes, Nat.mul_comm] using hmReg)
        let obj : LcnfObj :=
          { addr := p
            rc := 1#32
            csSz := if bytes < 65536 then bytes else 0
            other := 0
            tag := mpzTag
            cap := n'
            arrSize := n'
            limbs := List.replicate n' 0#64 }
        have hobjWf : obj.Wf := by
          refine ⟨hpNz, hpMod, by dsimp [obj]; decide, ?_, by dsimp [obj]; decide,
            by dsimp [obj, mpzTag]; decide, ?_, ?_, ?_, ?_⟩
          · dsimp [obj]; split <;> omega
          · dsimp [obj, LcnfObj.totalBytes]; simp only [mpzTag, arrayTag, sarrayTag, stringTag]
            exact hbytesLo
          · dsimp [obj, LcnfObj.totalBytes]; simp only [mpzTag, arrayTag, sarrayTag, stringTag]
            exact hbytesMax
          · dsimp [obj, LcnfObj.totalBytes]; simp only [mpzTag, arrayTag, sarrayTag, stringTag]
            exact hbytesMod
          · dsimp [obj]
            simp [mpzTag, closureTag, arrayTag, sarrayTag, stringTag, List.length_replicate]
            unfold mpzMaxLimbs at hnMax; constructor <;> omega
        have hhdr : ((1#64 ||| ((if bytes <
          65536 then BitVec.ofNat 64 bytes else 0#64) <<< 32#64)) |||
            (250#64 <<< 56#64)) = obj.header := by
          dsimp only [obj, LcnfObj.header, mpzTag]
          rw [show (1#32 : BitVec 32).toNat = 1 from rfl,
            show (BitVec.ofNat 64 0 <<< 48 : BitVec 64) = 0#64 from rfl, BitVec.or_zero,
            show (BitVec.ofNat 64 250 <<< 56 : BitVec 64) = (250#64 <<< 56#64) from rfl,
            show ∀ x : BitVec 64, x <<< 32#64 = x <<< 32 from fun _ => rfl]
          by_cases hb : bytes < 65536
          · simp only [hb, ↓reduceIte]
          · simp only [hb, ↓reduceIte]
        have hmeta : (BitVec.ofNat 64 n' ||| BitVec.ofNat 64 n' <<< 32#64) = obj.mpzMeta := rfl
        have hpParts' : (cell64 p w0 ⋆
            (cell64 (p + 8#64) w1 ⋆ (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) mAlloc :=
          sep_ac hpParts
        have swap12 : ∀ {A B C : Mem 64 → Prop} {mx : Mem 64},
            (A ⋆ (B ⋆ C)) mx → (B ⋆ (A ⋆ C)) mx := fun h => sep_ac h
        have pack3 : ∀ {A B C D : Mem 64 → Prop} {mx : Mem 64},
            (B ⋆ (A ⋆ (C ⋆ D))) mx → (A ⋆ B ⋆ C ⋆ D) mx := fun h => sep_ac h
        clear hpParts hmAlloc
        change LeanQbe.T.wp _ _ _ _ _
        apply wp_sext (by decide); intro p_1 hp_1
        apply wp_shl; intro p_2 hp_2
        apply wp_or; intro p_3 hp_3
        apply wp_sext (by decide); intro p_4 hp_4
        apply wp_shl; intro p_5 hp_5
        apply wp_or; intro p_6 hp_6
        dsimp only [Arg.val] at hp_1 hp_2 hp_3 hp_4 hp_5 hp_6
        have hp6_eq : p_6 = obj.header := by
          rw [hp_6, hp_5, hp_4, hp_3, hp_2, hp_1,
            show (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 from rfl,
            show (BitVec.signExtend 64 (56 : BitVec 32)).toNat % 64 = 56 from rfl, ← hhdr,
            show ∀ x : BitVec 64, x <<< 32#64 = x <<< 32 from fun _ => rfl,
            show (250#64 <<< 56#64 : BitVec 64) = (250 : BitVec 64) <<< 56 from rfl]
          rfl
        apply wp_store_sep
        · exact store_cell64 _ hpParts'
        · intro m1 hm1
          dsimp only [Arg.val] at hm1
          rw [hp6_eq] at hm1
          have hm1' := swap12 hm1
          clear hm1 hpParts'
          change LeanQbe.T.wp _ _ _ _ _
          apply wp_add; intro p_7 hp_7
          apply wp_sext (by decide); intro p_8 hp_8
          apply wp_shl; intro p_9 hp_9
          apply wp_or; intro p_10 hp_10
          dsimp only [Arg.val] at hp_7 hp_8 hp_9 hp_10
          rw [hp_7]
          apply wp_store_sep
          · exact store_cell64 _ hm1'
          · intro m2 hm2
            dsimp only [Arg.val] at hm2
            have hm2_eq : p_10 = obj.mpzMeta := by
              rw [hp_10, hp_9, hp_8, ← hmeta,
                show (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 from rfl,
                show ∀ x : BitVec 64, x <<< 32#64 = x <<< 32 from fun _ => rfl]
            rw [hm2_eq] at hm2
            clear hm1'
            have exposeArr : ∀ {A B C D : Mem 64 → Prop} {mx : Mem 64},
                (A ⋆ B ⋆ C ⋆ D) mx → (C ⋆ (A ⋆ B ⋆ D)) mx := fun h => sep_ac h
            have packArr : ∀ {A B C D : Mem 64 → Prop} {mx : Mem 64},
                (C ⋆ (A ⋆ B ⋆ D)) mx → (A ⋆ B ⋆ C ⋆ D) mx := fun h => sep_ac h
            have swapOut : ∀ {A B C : Mem 64 → Prop} {mx : Mem 64},
                (A ⋆ (B ⋆ C)) mx → ((B ⋆ A) ⋆ C) mx := fun h => sep_ac h
            change LeanQbe.T.wp _ _ _ _ _
            refine wp_loop_inv
              (fun (xs : Tup Val [i64]) mL =>
                ∃ iNat : Nat, iNat ≤ n' ∧ xs.1 = BitVec.ofNat 64 iNat ∧
                  (cell64 p obj.header ⋆ cell64 (p + 8#64) obj.mpzMeta ⋆
                    array64 (p + 16#64) (List.replicate iNat 0#64 ++ limbs.drop iNat) ⋆
                    (rtC0Inv rt st' ⋆ R)) mL)
              (fun (xs : Tup Val [i64]) _ => n' - xs.1.toNat)
              ?_ ?_
            · intro Js hJs
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              refine hJs (0#64, ()) _ ⟨0, Nat.zero_le _, rfl, ?_⟩
              dsimp only [List.replicate, List.nil_append, List.drop_zero]
              exact pack3 hm2
            · intro Js ⟨i, ⟨⟩⟩ mL ⟨iNat, hiLe, hiEq, hmL⟩ hRec
              dsimp only at hiEq
              subst hiEq
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              · have hlt : iNat < n' := by
                  have hc : (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 n').toNat := by
                    assumption
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn'lt] at hc
                  exact hc
                have hiLen : (BitVec.ofNat 64 iNat).toNat <
                    (List.replicate iNat 0#64 ++ limbs.drop iNat).length := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.length_append,
                    List.length_replicate, List.length_drop, hlen]
                  omega
                apply wp_store_sep
                · exact c0_store_array64_obj2_mul8 0#64 (exposeArr hmL) hiLen
                · intro mL' hmL'
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), zeroPrefix_set
                    (by omega)] at hmL'
                  change LeanQbe.T.wp _ _ _ _ _
                  c0_steps
                  have heq : BitVec.ofNat 64 iNat + (1 : BitVec 64) = BitVec.ofNat 64 (iNat + 1) :=
                    by
                    apply BitVec.eq_of_toNat_eq; simp
                  rw [heq]
                  refine hRec (BitVec.ofNat 64 (iNat + 1), ()) mL' ?_ ⟨iNat + 1, by omega, rfl, ?_⟩
                  · change n' - (BitVec.ofNat 64 (iNat + 1)).toNat <
                    n' - (BitVec.ofNat 64 iNat).toNat
                    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    omega
                  · exact packArr hmL'
              · have hge : n' ≤ iNat := by
                  have hc : ¬ (BitVec.ofNat 64 iNat).toNat < (BitVec.ofNat 64 n').toNat := by
                    assumption
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn'lt] at hc
                  omega
                have hiEqN : iNat = n' := by omega
                subst hiEqN
                rw [show limbs.drop n' = [] from List.drop_of_length_le
                  (by omega), List.append_nil] at hmL
                refine hQ p st' mL hobjWf (bv64_and1_eq_zero_of_mod8 hpMod) hpres hrem
                  (RtC0State.bounded48_of_preserves hbd hpres) ?_
                exact swapOut (lcnfObjMem_mpz_intro rfl hmL)
  dsimp only [Func.wp, lcnf_nat_alloc, lcnf_nat_alloc_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_join_group (fun (xs : Tup Val [i64]) m' => xs.1 = BitVec.ofNat 64 n' ∧ m' = m) ?_ ?_
  · intro J_n ⟨nCur, ⟨⟩⟩ m' ⟨hnCur, hm'⟩
    dsimp only at hnCur
    subst hnCur hm'
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · exfalso
      have hc : (33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 n').toNat := by assumption
      have hn'toNat : (BitVec.ofNat 64 n').toNat = n' := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn'lt]
      have h335 : (33554429#64 : BitVec 64).toNat = 33554429 := rfl
      rw [h335, hn'toNat] at hc
      unfold mpzMaxLimbs at hnMax
      omega
    · have hlt : (BitVec.toNat (16#64 : BitVec 64) +
          BitVec.toNat (8#64 : BitVec 64) * (n' % 2 ^ 64)) % 2 ^ 64 <
          BitVec.toNat (65536#64 : BitVec 64) := by assumption
      have hsz : (BitVec.toNat (16#64 : BitVec 64) +
          BitVec.toNat (8#64 : BitVec 64) * (n' % 2 ^ 64)) % 2 ^ 64 = bytes := by
        dsimp [bytes]
        rw [Nat.mod_eq_of_lt hn'lt]
        change (16 + 8 * n') % 2 ^ 64 = 16 + 8 * n'
        rw [Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnMax; omega)]
      have hlt' : bytes < 65536 := by
        rw [hsz, show BitVec.toNat (65536#64 : BitVec 64) = 65536 from rfl] at hlt
        exact hlt
      rw [hbytesBv]
      exact hAllocTail (BitVec.ofNat 64 bytes) (by simp only [hlt', ↓reduceIte])
    · have hge : ¬ (BitVec.toNat (16#64 : BitVec 64) +
          BitVec.toNat (8#64 : BitVec 64) * (n' % 2 ^ 64)) % 2 ^ 64 <
          BitVec.toNat (65536#64 : BitVec 64) := by assumption
      have hsz : (BitVec.toNat (16#64 : BitVec 64) +
          BitVec.toNat (8#64 : BitVec 64) * (n' % 2 ^ 64)) % 2 ^ 64 = bytes := by
        dsimp [bytes]
        rw [Nat.mod_eq_of_lt hn'lt]
        change (16 + 8 * n') % 2 ^ 64 = 16 + 8 * n'
        rw [Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnMax; omega)]
      have hge' : ¬ bytes < 65536 := by
        rw [hsz, show BitVec.toNat (65536#64 : BitVec 64) = 65536 from rfl] at hge
        exact hge
      rw [hbytesBv]
      exact hAllocTail 0#64 (by simp only [hge', ↓reduceIte])
  · intro J_n hJ_n
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · refine hJ_n _ _ ⟨?_, rfl⟩
      have hn0 : nlimbs = 0#64 := by assumption
      simp [n', hn0]
    · refine hJ_n _ _ ⟨?_, rfl⟩
      have hn0 : nlimbs ≠ 0#64 := by assumption
      have hpos : 0 < nlimbs.toNat := Nat.pos_of_ne_zero fun h => hn0 (BitVec.eq_of_toNat_eq h)
      have hmaxEq : n' = nlimbs.toNat := by dsimp [n']; omega
      rw [hmaxEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem bn_require_scratch_wp :
    ∀ xs m Q X, bnRequireScratchSpec xs m Q X →
      Func.wp rtR1Env bn_require_scratch.body xs m Q X := by
  intro ⟨rt, need, ⟨⟩⟩ m Q X ⟨scr, cap, R, hscr, hneed, hm, hQ⟩
  dsimp only [Func.wp, bn_require_scratch, bn_require_scratch_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  exact hQ

theorem bn_dec_nat_wp :
    ∀ xs m Q X, bnDecNatSpec xs m Q X → Func.wp rtR1Env bn_dec_nat.body xs m Q X := by
  intro ⟨rt, a, ⟨⟩⟩ m Q X hspec
  dsimp only [Func.wp, bn_dec_nat, bn_dec_nat_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_join_group (fun (_ : Tup Val []) m' => Q () m') ?_ ?_
  · intro J_ret ⟨⟩ m' hQ'
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hQ'
  · intro J_ret hJ_ret
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hscalar : (a &&& 1#64) ≠ 0#64
    · dsimp only [bnDecNatSpec] at hspec
      split at hspec
      · c0_steps
        exact hJ_ret () m hspec
      · exact absurd hscalar ‹_›
    · have ha0 : (a &&& 1#64) = 0#64 := Classical.not_not.mp hscalar
      dsimp only [bnDecNatSpec] at hspec
      have hspec' : ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
          objs.length ≤ st.workCap ∧
          (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
          (∃ obj ∈ objs, obj.addr = a) ∧
          (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
          (∀ obj ∈ objs, obj.addr = a → obj.rc = 1#32 → RcSound a objs) ∧
          ∀ st' objs' m',
            DecNatRel a st st' objs objs' →
            (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m' := by
        split at hspec
        · exact absurd ‹_› hscalar
        · exact hspec
      rcases hspec' with ⟨st, objs, R, hcap, hm, ⟨obj0, hmem0, had0⟩, hwfAll, hclosed, hrcS, hQ⟩
      obtain ⟨idx, hidxLt, hidxEq⟩ := List.getElem_of_mem hmem0
      have hobjAddr : objs[idx].addr = a := by rw [hidxEq]; exact had0
      have hobjWf : objs[idx].Wf := hwfAll _ (List.getElem_mem hidxLt)
      have hfocus : lcnfHeap objs =
          (lcnfObjMem objs[idx] ⋆ (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)))) :=
        lcnfHeap_focus objs hidxLt
      have hmFocus : (cell64 a objs[idx].header ⋆ (lcnfObjMemTail objs[idx] ⋆ rtC0Inv rt st ⋆
          (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ R)) m := by
        rw [hfocus, lcnfObjMem_eq_header_tail, hobjAddr] at hm
        exact sep_ac hm
      have hrc32 : objs[idx].header.setWidth 32 = objs[idx].rc :=
        LcnfObj.header_setWidth32 objs[idx] hobjWf
      have hrcSext : ((objs[idx].header.setWidth 32).signExtend 64).toInt = objs[idx].rc.toInt := by
        rw [hrc32]; exact BitVec.toInt_signExtend_of_le (by decide)
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      · have hrcGt1 : 1 < objs[idx].rc.toInt := by
          have hc : (1#64).slt ((objs[idx].header.setWidth 32).signExtend 64) = true := by
            assumption
          simp only [BitVec.slt, decide_eq_true_eq] at hc
          have h1i : (1#64 : BitVec 64).toInt = 1 := rfl
          omega
        have hmsb : objs[idx].rc.msb = false := by
          have h := BitVec.toInt_eq_msb_cond objs[idx].rc
          have hnn := hobjWf.2.2.1
          cases hm0 : objs[idx].rc.msb <;> rw [hm0] at h <;> simp at h <;> omega
        have hsxtNat : (objs[idx].rc.signExtend 64).toNat = objs[idx].rc.toNat := by
          have hlt64 : objs[idx].rc.toNat < 2 ^ 64 :=
            Nat.lt_of_lt_of_le objs[idx].rc.isLt (by decide : 2 ^ 32 ≤ 2 ^ 64)
          simp [BitVec.signExtend_eq_setWidth_of_msb_false, hmsb, Nat.mod_eq_of_lt hlt64]
        have hsub32 :
          (((objs[idx].header.setWidth 32).signExtend 64 - 1#64).setWidth 32).setWidth 64 =
            (BitVec.ofNat 32 (objs[idx].rc.toNat - 1)).setWidth 64 := by
          rw [hrc32]
          congr 1
          apply BitVec.eq_of_toNat_eq
          have h1lt := objs[idx].rc.isLt
          have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
          have hle64 : (BitVec.ofNat 64 1) ≤ objs[idx].rc.signExtend 64 := by
            rw [BitVec.le_def, hsxtNat, h1n]
            have hrcToNat : objs[idx].rc.toInt = (objs[idx].rc.toNat : Int) := by
              rw [BitVec.toInt_eq_msb_cond, hmsb]; simp
            omega
          have hsubLt32 : objs[idx].rc.toNat - 1 < 2 ^ 32 :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) h1lt
          have hsubMod64 : (objs[idx].rc.toNat - 1) % 2 ^ 32 = objs[idx].rc.toNat - 1 :=
            Nat.mod_eq_of_lt hsubLt32
          rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle64, hsxtNat, h1n,
            BitVec.toNat_ofNat, hsubMod64]
        have hhdrEq := LcnfObj.header_dec_rc objs[idx] hobjWf hrcGt1
        apply wp_store_sep
        · exact store_cell64 _ hmFocus
        · intro m' hm'
          change LeanQbe.T.wp _ _ _ _ _
          c0_steps
          apply hJ_ret () m'
          refine hQ st (objs.set idx (objs[idx].withRc (objs[idx].rc - 1#32))) m'
            (Or.inr (Or.inr (Or.inl ⟨ha0, idx, hidxLt, hobjAddr, hrcGt1, rfl, rfl⟩))) ?_
          have hstMem : (cell64 a ((objs[idx].header &&& 18446744069414584320#64) |||
              (BitVec.ofNat 32 (objs[idx].rc.toNat - 1)).setWidth 64) ⋆
              (lcnfObjMemTail objs[idx] ⋆ rtC0Inv rt st ⋆
                (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ R)) m' := by
            rw [← hsub32]; exact hm'
          rw [show (18446744069414584320#64 : BitVec 64) = 0xffffffff00000000#64 from rfl,
            hhdrEq] at hstMem
          rw [lcnfHeap_set objs hidxLt, lcnfObjMem_eq_header_tail,
            show lcnfObjMemTail (objs[idx].withRc (objs[idx].rc - 1#32)) =
              lcnfObjMemTail objs[idx] from rfl,
            show (objs[idx].withRc (objs[idx].rc - 1#32)).addr = a from hobjAddr]
          exact sep_ac hstMem
      · have hrc1 : objs[idx].rc = 1#32 := by
          have heq : (objs[idx].header.setWidth 32).signExtend 64 = 1#64 := by assumption
          have h2 := congrArg BitVec.toInt heq
          rw [hrcSext] at h2
          apply BitVec.eq_of_toInt_eq
          simpa using h2
        apply wp_call_of
        apply rtR1Env_lcnf_dec_ref_cold
        dsimp only [BigNumRt.lcnfDecRefColdSpec, vals, Tup.map, Arg.val]
        refine ⟨ha0, st, objs, R, hcap, hm,
          ⟨objs[idx], List.getElem_mem hidxLt, hobjAddr, hrc1⟩,
          hwfAll, hclosed, hrcS _ (List.getElem_mem hidxLt) hobjAddr hrc1,
          fun st' objs' m' hp hr hc hm' => ?_⟩
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        exact hJ_ret () m' (hQ st' objs' m' (Or.inr (Or.inr (Or.inr ⟨ha0, hp, hr, hc⟩))) hm')
      · have hrc0 : objs[idx].rc = 0#32 := by
          have hle : ((1#64).slt ((objs[idx].header.setWidth 32).signExtend 64)) = false := by
            assumption
          have hne : (objs[idx].header.setWidth 32).signExtend 64 ≠ 1#64 := by assumption
          simp only [BitVec.slt, decide_eq_false_iff_not] at hle
          have h1i : (1#64 : BitVec 64).toInt = 1 := rfl
          have hnn := hobjWf.2.2.1
          have hlt1 : objs[idx].rc.toInt < 1 := by
            by_cases hlt1' : objs[idx].rc.toInt < 1
            · exact hlt1'
            · have hge1 : 1 ≤ objs[idx].rc.toInt := by omega
              by_cases heq1 : objs[idx].rc.toInt = 1
              · have heqs : (objs[idx].header.setWidth 32).signExtend 64 = 1#64 := by
                  apply BitVec.eq_of_toInt_eq; omega
                exact absurd heqs hne
              · exact absurd (by omega) hle
          apply BitVec.eq_of_toInt_eq
          have h0i : (0#32 : BitVec 32).toInt = 0 := rfl
          omega
        exact hJ_ret () m (hQ st objs m (Or.inr (Or.inl ⟨ha0, objs[idx], List.getElem_mem hidxLt,
          hobjAddr, hrc0, rfl, rfl⟩)) hm)

theorem bn_copy_wp :
    ∀ xs m Q X, bnCopySpec xs m Q X → Func.wp rtR1Env bn_copy.body xs m Q X := by
  intro ⟨dst, src, n, ⟨⟩⟩ m Q X ⟨dstXs, srcXs, R, hndst, hnsrc, hm, hQ⟩
  dsimp only [Func.wp, bn_copy, bn_copy_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ iNat : Nat, iNat ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 iNat ∧
        (array64 dst (srcXs.take iNat ++ dstXs.drop iNat) ⋆ (array64 src srcXs ⋆ R)) mL)
    (fun (xs : Tup Val [i64]) _ => n.toNat - xs.1.toNat)
    ?_ ?_
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    refine hJs (0#64, ()) m ⟨0, Nat.zero_le _, rfl, ?_⟩
    simpa [sep_assoc] using hm
  · intro Js ⟨i, ⟨⟩⟩ mL ⟨iNat, hiLe, hiEq, hmL⟩ hRec
    dsimp only at hiEq; subst hiEq
    have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe n.isLt
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hlt : iNat < n.toNat := by
        have hc : (BitVec.ofNat 64 iNat).toNat < n.toNat := by assumption
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64] at hc
        exact hc
      have hsrcIdx : (BitVec.ofNat 64 iNat).toNat < srcXs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]; omega
      have hdstIdx : (BitVec.ofNat 64 iNat).toNat < (srcXs.take iNat ++ dstXs.drop iNat).length :=
        by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64, List.length_append,
          List.length_take_of_le (by omega), List.length_drop]
        omega
      c0_steps
      apply wp_store_sep
      · exact c0_store_array64_mul8_l srcXs[(BitVec.ofNat 64 iNat).toNat] hmL hdstIdx
      · intro mL' hmL'
        have heq2 : (BitVec.ofNat 64 iNat).toNat = iNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64]
        simp only [heq2] at hmL'
        rw [replacePrefix_set (by omega) (by omega)] at hmL'
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        have heq1 : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [heq1]
        refine hRec (BitVec.ofNat 64 (iNat + 1), ()) mL' ?_ ⟨iNat + 1, by omega, rfl, hmL'⟩
        change n.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat < n.toNat - (BitVec.ofNat 64 iNat).toNat
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hilt64]
        omega
    · have hge : n.toNat ≤ iNat := by
        have hc : ¬ (BitVec.ofNat 64 iNat).toNat < n.toNat := by assumption
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64] at hc
        omega
      have hiEqN : iNat = n.toNat := by omega
      subst hiEqN
      exact hQ mL (sep_ac hmL)

theorem bn_zero_wp :
    ∀ xs m Q X, bnZeroSpec xs m Q X → Func.wp rtR1Env bn_zero.body xs m Q X := by
  intro ⟨dst, n, ⟨⟩⟩ m Q X ⟨xsArr, R, hnle, hm, hQ⟩
  dsimp only [Func.wp, bn_zero, bn_zero_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ iNat : Nat, iNat ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 iNat ∧
        (array64 dst (List.replicate iNat 0#64 ++ xsArr.drop iNat) ⋆ R) mL)
    (fun (xs : Tup Val [i64]) _ => n.toNat - xs.1.toNat)
    ?_ ?_
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    refine hJs (0#64, ()) m ⟨0, Nat.zero_le _, rfl, ?_⟩
    simpa using hm
  · intro Js ⟨i, ⟨⟩⟩ mL ⟨iNat, hiLe, hiEq, hmL⟩ hRec
    dsimp only at hiEq; subst hiEq
    have hilt64 : iNat < 2 ^ 64 := Nat.lt_of_le_of_lt hiLe n.isLt
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hlt : iNat < n.toNat := by
        have hc : (BitVec.ofNat 64 iNat).toNat < n.toNat := by assumption
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64] at hc
        exact hc
      have hdstIdx : (BitVec.ofNat 64 iNat).toNat <
          (List.replicate iNat 0#64 ++ xsArr.drop iNat).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64, List.length_append,
          List.length_replicate, List.length_drop]
        omega
      apply wp_store_sep
      · exact c0_store_array64_mul8_l 0#64 hmL hdstIdx
      · intro mL' hmL'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64, zeroPrefix_set (by omega)] at hmL'
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        have heq1 : BitVec.ofNat 64 iNat + 1 = BitVec.ofNat 64 (iNat + 1) := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [heq1]
        refine hRec (BitVec.ofNat 64 (iNat + 1), ()) mL' ?_ ⟨iNat + 1, by omega, rfl, hmL'⟩
        change n.toNat - (BitVec.ofNat 64 (iNat + 1)).toNat < n.toNat - (BitVec.ofNat 64 iNat).toNat
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hilt64]
        omega
    · have hge : n.toNat ≤ iNat := by
        have hc : ¬ (BitVec.ofNat 64 iNat).toNat < n.toNat := by assumption
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt64] at hc
        omega
      have hiEqN : iNat = n.toNat := by omega
      subst hiEqN
      exact hQ mL hmL

/-! ### Reusable Polymorphic Separation-Logic & Heap Helpers -/

theorem sep_comm2 {A B : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B) m) : (B ⋆ A) m := sep_ac h
theorem sep_swap12 {A B C : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ (B ⋆ C)) m) : (B ⋆ (A ⋆
  C)) m := sep_ac h
theorem sep_swap12l {A B C : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C) m) : (B ⋆ A ⋆
  C) m := sep_ac h
theorem sep_assoc_r {A B C : Mem 64 → Prop} {m : Mem 64} (h : ((A ⋆ B) ⋆ C) m) : (A ⋆ (B ⋆
  C)) m := sep_ac h
theorem sep_assoc_l {A B C : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ (B ⋆ C)) m) : ((A ⋆ B) ⋆
  C) m := sep_ac h

theorem sep_mpz_swap2 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D) m) : (B ⋆ (A ⋆ C ⋆ D)) m := sep_ac h
theorem sep_mpz_unswap2 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ C ⋆ D)) m) : (A ⋆ B ⋆ C ⋆ D) m := sep_ac h
theorem sep_mpz_swap3 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D) m) : (C ⋆ (A ⋆ B ⋆ D)) m := sep_ac h
theorem sep_mpz_unswap3 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ D)) m) : (A ⋆ B ⋆ C ⋆ D) m := sep_ac h

theorem sep_mpz_to_list4 {H1 H2 H3 A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (H1 ⋆ (H2 ⋆ (H3 ⋆ (A ⋆ (B ⋆ C ⋆ D))))) m) :
    (H1 ⋆ H2 ⋆ H3 ⋆ (A ⋆ B ⋆ C ⋆ D)) m := sep_ac h

theorem sep_pick2_3r {A B C1 C2 C3 : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ (C1 ⋆ C2 ⋆ C3)) m) : (B ⋆ (A ⋆ C1 ⋆ C2 ⋆ C3)) m := sep_ac h

theorem sep_pick2_3 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C) m) : (B ⋆ (A ⋆ C)) m := sep_ac h
theorem sep_unpick2_3 {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ C)) m) : (A ⋆ B ⋆ C) m := sep_ac h

theorem sep_pick2_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D) m) : (B ⋆ (A ⋆ C ⋆ D)) m := sep_ac h
theorem sep_unpick2_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ C ⋆ D)) m) : (A ⋆ B ⋆ C ⋆ D) m := sep_ac h

theorem sep_pick1_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D) m) : (A ⋆ (B ⋆ C ⋆ D)) m := sep_ac h
theorem sep_unpick1_4 {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D)) m) : (A ⋆ B ⋆ C ⋆ D) m := sep_ac h

theorem lcnfHeap_cons_eq (o : LcnfObj) (os : List LcnfObj) :
    BigNumRt.lcnfHeap (o :: os) = (BigNumRt.lcnfObjMem o ⋆ BigNumRt.lcnfHeap os) := rfl

theorem lcnfHeap_mpz_focus {objs : List LcnfObj} {obj : LcnfObj}
    (hIn : obj ∈ objs) (htag : obj.tag = mpzTag) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (BigNumRt.lcnfHeap objs ⋆ R) m) :
    ∃ idx : Nat, ∃ hlt : idx < objs.length, objs[idx] = obj ∧
      (cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
        array64 (obj.addr + 16#64) obj.limbs ⋆
        ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆ R)) m := by
  obtain ⟨idx, hlt, heq⟩ := List.mem_iff_getElem.mp hIn
  refine ⟨idx, hlt, heq, ?_⟩
  rw [BigNumRt.lcnfHeap_focus objs hlt, heq] at hm
  exact lcnfObjMem_mpz_elim htag (sep_assoc_r hm)

theorem lcnfHeap_mpz_restore {objs : List LcnfObj} {obj : LcnfObj} {idx : Nat}
    (hlt : idx < objs.length) (heq : objs[idx] = obj) (htag : obj.tag = mpzTag)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
      array64 (obj.addr + 16#64) obj.limbs ⋆
      ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆ R)) m) :
    (BigNumRt.lcnfHeap objs ⋆ R) m := by
  rw [BigNumRt.lcnfHeap_focus objs hlt, heq]
  exact sep_assoc_l (lcnfObjMem_mpz_intro htag hm)

/-! ### BitVec & Limb Length Helpers -/

theorem nat_lor_two_mul_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    have h2 : (2 * k + 1).testBit (i + 1) = (2 * k).testBit (i + 1) := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ]
      have hd : (2 * k + 1) / (2 ^ i * 2) = (2 * k) / (2 ^ i * 2) := by
        rw [Nat.mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        congr 1; omega
      rw [hd]
    have h1 : (1 : Nat).testBit (i + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero _) (by decide : 1 < 2))]
    rw [h1, h2, Bool.or_false]

theorem bv64_shl1_or1 (x : BitVec 64) :
    (x <<< 1 ||| 1#64) = BitVec.ofNat 64 (2 * (x.toNat % 2 ^ 63) + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x <<< 1).toNat = 2 * (x.toNat % 2 ^ 63) := by
    rw [BitVec.toNat_shiftLeft, show (1 : Nat) = 1 from rfl, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mul_comm x.toNat 2, show (2 ^ 64 : Nat) = 2 * 2 ^ 63 from rfl, Nat.mul_mod_mul_left]
  have hlt : 2 * (x.toNat % 2 ^ 63) + 1 < 2 ^ 64 := by
    have := Nat.mod_lt x.toNat (by decide : 0 < 2 ^ 63); omega
  rw [BitVec.toNat_or, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    nat_lor_two_mul_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem bv64_ofNat_small_enc {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< 1 ||| 1#64) = BitVec.ofNat 64 (2 * x.toNat + 1) := by
  rw [bv64_shl1_or1, Nat.mod_eq_of_lt hx]

theorem bv64_ofInt_pos_enc {x : BitVec 64} (hx : x.toNat < 2 ^ 62) :
    (x <<< 1 ||| 1#64) = BitVec.ofInt 64 (2 * (x.toNat : Int) + 1) := by
  rw [bv64_ofNat_small_enc (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have hlt : 2 * x.toNat + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

theorem bv64_ofInt_neg_enc {x : BitVec 64} (hx : x.toNat ≤ 2 ^ 62) :
    ((0#64 - x) <<< 1 ||| 1#64) = BitVec.ofInt 64 (2 * (-(x.toNat : Int)) + 1) := by
  by_cases hx0 : x.toNat = 0
  · have : x = 0#64 := BitVec.eq_of_toNat_eq hx0
    subst this; decide
  · apply BitVec.eq_of_toNat_eq
    rw [bv64_shl1_or1]
    have hsub : (0#64 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (0#64 : BitVec 64).toNat = 0 from rfl]; omega
    have hmod : (2 ^ 64 - x.toNat) % 2 ^ 63 = 2 ^ 63 - x.toNat := by omega
    rw [hsub, hmod, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have hlt : 2 * (2 ^ 63 - x.toNat) + 1 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

theorem natSmallEnc_ushiftRight1 {v : Nat} (hv : v < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * v + 1)) >>> 1 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have hlt : 2 * v + 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

theorem natSmallEnc_and1 {v : Nat} (hv : v < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * v + 1) &&& 1#64) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2 ^ 64),
    show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem limbLenNat_eq_one {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) : limbLenNat n = 1 := by
  unfold limbLenNat
  have hnz : n ≠ 0 := by omega
  simp only [hnz, ↓reduceIte]
  have hlog : n.log2 < 64 := (Nat.log2_lt hnz).mpr hlt
  have hdiv : n.log2 / 64 = 0 := Nat.div_eq_of_lt hlog
  omega

/-! ### Remaining Helper Proofs (9 / 16) -/

theorem bv64_sub1_idx {k' : Nat} (hk : k' + 1 < 2 ^ 64) :
    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 = k' := by
  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    show 2 ^ 64 - 1 + (k' + 1) = 2 ^ 64 + k' from by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem bn_trim_wp :
    ∀ xs m Q X, bnTrimSpec xs m Q X → Func.wp rtR1Env bn_trim.body xs m Q X := by
  intro ⟨buf, n, ⟨⟩⟩ m Q X ⟨xsArr, R, hnle, hm, hQ⟩
  dsimp only [Func.wp, bn_trim, bn_trim_body]
  change LeanQbe.T.wp _ _ _ _ _
  refine wp_loop_break_group
    (fun (xs : Tup Val [i64]) m' =>
      xs.1 = BitVec.ofNat 64 (trimLenLoop xsArr n.toNat) ∧ m' = m)
    (fun k (xs : Tup Val [i64]) m' =>
      k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
        trimLenLoop xsArr k = trimLenLoop xsArr n.toNat ∧ m' = m)
    ?_ ?_ ?_
  · intro B ⟨res, ⟨⟩⟩ m' ⟨hres, hm'⟩
    subst hres hm'
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hQ
  · intro B L k ⟨cur, ⟨⟩⟩ m' hB hL ⟨hkLe, hcur, htrim, hm'⟩
    dsimp only at hcur
    subst hcur hm'
    have hklt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hkLe n.isLt
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hkPos : 0 < k := by
        have hc : BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        exact hc
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxLt : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < xsArr.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hne0 : xsArr[k'] ≠ 0#64 := by
        have hc : ¬ xsArr[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64] = 0 := by
          assumption
        simp only [bv64_sub1_idx hklt64] at hc
        exact hc
      have hstep : trimLenLoop xsArr (k' + 1) = k' + 1 := by
        rw [trimLenLoop.eq_2]
        simp [getElem!_pos xsArr k' (by omega), hne0]
      apply hB (BitVec.ofNat 64 (k' + 1), ()) m'
      exact ⟨by rw [← htrim, hstep], rfl⟩
    · have hkPos : 0 < k := by
        have hc : BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        exact hc
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxLt : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < xsArr.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have heq0 : xsArr[k'] = 0#64 := by
        have hc : xsArr[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64] = 0 := by
          assumption
        simp only [bv64_sub1_idx hklt64] at hc
        exact hc
      have hstep : trimLenLoop xsArr (k' + 1) = trimLenLoop xsArr k' := by
        rw [trimLenLoop.eq_2]
        simp [getElem!_pos xsArr k' (by omega), heq0]
      have hsub : BitVec.ofNat 64 (k' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k' := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt64];
              exact Nat.succ_le_succ (Nat.zero_le k'))]
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt64, Nat.mod_eq_of_lt
          (by omega)]
        simp
      rw [hsub]
      exact hL k' (BitVec.ofNat 64 k', ()) m'
        (by omega) ⟨by omega, rfl, by rw [← htrim, hstep], rfl⟩
    · have hk0 : k = 0 := by
        have hc : ¬ BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        omega
      subst hk0
      have htrim0 : trimLenLoop xsArr 0 = 0 := trimLenLoop.eq_1 xsArr
      apply hB (0#64, ()) m'
      refine ⟨?_, rfl⟩
      rw [← htrim, htrim0]
  · intro B L hB hL
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hL n.toNat (n, ()) m ⟨Nat.le_refl _, BitVec.eq_of_toNat_eq (by simp), rfl, rfl⟩

private theorem mpz_wf_bounds {o : BigNumRt.LcnfObj} (hwf : o.Wf) (htag : o.tag = mpzTag) :
    o.cap < 2 ^ 32 ∧ o.arrSize < 2 ^ 32 := by
  rcases hwf with ⟨_, _, _, _, _, _, _, _, _, h10⟩
  rw [htag] at h10
  simp only [mpzTag, closureTag, arrayTag, sarrayTag, stringTag] at h10
  have hmpz : o.limbs.length = o.cap ∧ o.cap ≤ 33554429 ∧ o.arrSize < 2 ^ 32 := by
    revert h10; simp
  omega

private theorem preservesMeta_refl (st : BigNumRt.RtC0State) : st.PreservesMeta st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem getLast_eq_getLast! {α : Type} [Inhabited α] (l : List α) (h : l ≠ []) :
    l.getLast h = l.getLast! := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    induction xs generalizing x with
    | nil => rfl
    | cons y ys ih => exact ih y (by simp)

private theorem totalBytes_mpz {o : BigNumRt.LcnfObj} (h : o.tag = mpzTag) :
    o.totalBytes = 16 + 8 * o.cap := by
  simp [BigNumRt.LcnfObj.totalBytes, h, mpzTag, arrayTag, sarrayTag, stringTag]

private theorem mpz_wf_of_limbs {o o' : BigNumRt.LcnfObj} (hwf : o.Wf)
    (htag : o.tag = mpzTag) (htag' : o'.tag = mpzTag)
    (h1 : o'.addr = o.addr) (h2 : o'.rc = o.rc) (h3 : o'.csSz = o.csSz)
    (h4 : o'.other < 256) (h5 : o'.cap = o.cap) (h6 : o'.arrSize = o.arrSize)
    (h7 : o'.limbs.length = o'.cap) : o'.Wf := by
  have hb := mpz_wf_bounds hwf htag
  rcases hwf with ⟨w1, w2, w3, w4, _, w6, w7, w8, w9, w10⟩
  have hcap : o.cap ≤ 33554429 := by
    rw [htag] at w10
    have hmpz : o.limbs.length = o.cap ∧ o.cap ≤ 33554429 ∧ o.arrSize < 2 ^ 32 := by
      revert w10; simp [mpzTag, closureTag, arrayTag, sarrayTag, stringTag]
    exact hmpz.2.1
  refine ⟨by rw [h1]; exact w1, by rw [h1]; exact w2, by rw [h2]; exact w3,
    by rw [h3]; exact w4, h4, by rw [htag']; rw [htag] at w6; exact w6, ?_, ?_, ?_, ?_⟩
  · rw [totalBytes_mpz htag] at w7; rw [totalBytes_mpz htag', h5]; exact w7
  · rw [totalBytes_mpz htag] at w8; rw [totalBytes_mpz htag', h5]; exact w8
  · rw [totalBytes_mpz htag] at w9; rw [totalBytes_mpz htag', h5]; exact w9
  · rw [htag']
    have hres : o'.limbs.length = o'.cap ∧ o'.cap ≤ 33554429 ∧ o'.arrSize < 2 ^ 32 :=
      ⟨h7, by rw [h5]; exact hcap, by rw [h6]; exact hb.2⟩
    simpa [mpzTag, closureTag, arrayTag, sarrayTag, stringTag] using hres

theorem bn_nat_len_wp :
    ∀ xs m Q X, bnNatLenSpec xs m Q X → Func.wp rtR1Env bn_nat_len.body xs m Q X := by
  intro ⟨a, ⟨⟩⟩ m Q X ⟨val, objs, R, hrep, hm, hQ⟩
  dsimp only [Func.wp, bn_nat_len, bn_nat_len_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : val < 2 ^ 63 := Classical.byContradiction fun hge => by
      unfold natRep at hrep
      simp only [hge, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold natRep at hrep
    simp only [hsmall, ↓reduceIte] at hrep
    subst hrep
    have hv0bv : BitVec.ofNat 64 (2 * val + 1) >>> 1 = 0#64 := by assumption
    rw [natSmallEnc_ushiftRight1 hsmall] at hv0bv
    have hv0 : val = 0 := by
      have := congrArg BitVec.toNat hv0bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : val < 2 ^ 64)] at this
      simpa using this
    subst hv0
    rw [limbLenNat_zero] at hQ
    exact hQ
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : val < 2 ^ 63 := Classical.byContradiction fun hge => by
      unfold natRep at hrep
      simp only [hge, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold natRep at hrep
    simp only [hsmall, ↓reduceIte] at hrep
    subst hrep
    have hvnz : BitVec.ofNat 64 (2 * val + 1) >>> 1 ≠ 0#64 := by assumption
    rw [natSmallEnc_ushiftRight1 hsmall] at hvnz
    have hvpos : 0 < val := Classical.byContradiction fun hle0 => by
      have hv0 : val = 0 := by omega
      subst hv0
      exact hvnz rfl
    rw [limbLenNat_eq_one hvpos (by omega : val < 2 ^ 64)] at hQ
    exact hQ
  · have ha0 : a &&& (1 : BitVec 64) = 0#64 := by assumption
    have hbig : 2 ^ 63 ≤ val := Classical.byContradiction fun hlt => by
      have hsm : val < 2 ^ 63 := by omega
      unfold natRep at hrep
      simp only [hsm, ↓reduceIte] at hrep
      subst hrep
      rw [show (1 : BitVec 64) = 1#64 from rfl, natSmallEnc_and1 hsm] at ha0
      contradiction
    have hnsm : ¬ val < 2 ^ 63 := by omega
    unfold natRep at hrep
    simp only [hnsm, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn hcanon.2.1 hm
    rw [haddr] at hmObj
    have hmMeta := sep_mpz_swap2 hmObj
    rw [wp_load]
    refine ⟨obj.mpzMeta, loadVal_cell64 hmMeta, ?_⟩
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    have hbounds := mpz_wf_bounds hcanon.1 hcanon.2.1
    rw [show (obj.mpzMeta >>> 32 : BitVec 64) = obj.mpzMeta >>> 32#64 from rfl,
      LcnfObj.mpzMeta_arrSize obj hbounds.1 hbounds.2]
    have hne : obj.limbs ≠ [] := by
      intro hempty
      have h1 := hcanon.2.2.2.2.1
      rw [hempty, List.length_nil] at h1
      omega
    have hlen : limbLenNat val = obj.arrSize := by
      rw [← hcanon.2.2.2.2.2.2.2.1, hcanon.2.2.2.1]
      exact limbLenNat_eq_length_of_trimmed hne hcanon.2.2.2.2.2.2.1
    rw [hlen] at hQ
    exact hQ

theorem bn_int_len_wp :
    ∀ xs m Q X, bnIntLenSpec xs m Q X → Func.wp rtR1Env bn_int_len.body xs m Q X := by
  intro ⟨a, ⟨⟩⟩ m Q X ⟨val, objs, R, hrep, hm, hQ⟩
  dsimp only [Func.wp, bn_int_len, bn_int_len_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
      unfold intRep at hrep
      simp only [hnb, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold intRep at hrep
    simp only [hsmall] at hrep
    subst hrep
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsmall.1 hsmall.2
    have hzero : (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 = 0#64 := by assumption
    have hval0 : val = 0 := by rw [← htoInt, hzero]; rfl
    subst hval0
    rw [Int.natAbs_zero, limbLenNat_zero] at hQ
    exact hQ
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
      unfold intRep at hrep
      simp only [hnb, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold intRep at hrep
    simp only [hsmall] at hrep
    subst hrep
    have ⟨_, hshr⟩ := intSmallEnc_sshiftRight1 hsmall.1 hsmall.2
    have hnz : (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 ≠ 0#64 := by assumption
    have hvalnz : val ≠ 0 := by
      intro hv0; subst hv0
      apply hnz; rw [hshr]; rfl
    have hpos : 0 < val.natAbs := Int.natAbs_pos.mpr hvalnz
    have hlt64 : val.natAbs < 2 ^ 64 := by omega
    rw [limbLenNat_eq_one hpos hlt64] at hQ
    exact hQ
  · have ha0 : a &&& (1 : BitVec 64) = 0#64 := by assumption
    have hbig : ¬ (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) := by
      intro hsm
      unfold intRep at hrep
      simp only [hsm] at hrep
      subst hrep
      have ⟨hand, _⟩ := intSmallEnc_toInt hsm.1 hsm.2
      exact absurd ha0 (by rw [show (1 : BitVec 64) = 1#64 from rfl, hand]; decide)
    unfold intRep at hrep
    simp only [hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn hcanon.2.1 hm
    rw [haddr] at hmObj
    have hmMeta := sep_mpz_swap2 hmObj
    rw [wp_load]
    refine ⟨obj.mpzMeta, loadVal_cell64 hmMeta, ?_⟩
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    have hbounds := mpz_wf_bounds hcanon.1 hcanon.2.1
    rw [show (obj.mpzMeta >>> 32 : BitVec 64) = obj.mpzMeta >>> 32#64 from rfl,
      LcnfObj.mpzMeta_arrSize obj hbounds.1 hbounds.2]
    have hne : obj.limbs ≠ [] := by
      intro hempty
      have h1 := hcanon.2.2.2.2.1
      rw [hempty, List.length_nil] at h1
      omega
    have hlen : limbLenNat val.natAbs = obj.arrSize := by
      rw [← hcanon.2.2.2.2.2.2.2.1, hcanon.2.2.2.1]
      exact limbLenNat_eq_length_of_trimmed hne hcanon.2.2.2.2.2.2.1
    rw [hlen] at hQ
    exact hQ

theorem bn_load_nat_wp :
    ∀ xs m Q X, bnLoadNatSpec xs m Q X → Func.wp rtR1Env bn_load_nat.body xs m Q X := by
  intro ⟨a, dst, ⟨⟩⟩ m Q X ⟨val, objs, dstXs, R, hrep, hlenDst, hm, hQ⟩
  dsimp only [Func.wp, bn_load_nat, bn_load_nat_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : val < 2 ^ 63 := Classical.byContradiction fun hge => by
      unfold natRep at hrep
      simp only [hge, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold natRep at hrep
    simp only [hsmall, ↓reduceIte] at hrep
    subst hrep
    have hv0bv : BitVec.ofNat 64 (2 * val + 1) >>> 1 = 0#64 := by assumption
    rw [natSmallEnc_ushiftRight1 hsmall] at hv0bv
    have hv0 : val = 0 := by
      have := congrArg BitVec.toNat hv0bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : val < 2 ^ 64)] at this
      simpa using this
    subst hv0
    rw [limbLenNat_zero] at hQ
    exact hQ dstXs m rfl rfl rfl hm
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : val < 2 ^ 63 := Classical.byContradiction fun hge => by
      unfold natRep at hrep
      simp only [hge, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold natRep at hrep
    simp only [hsmall, ↓reduceIte] at hrep
    subst hrep
    have hvnz : BitVec.ofNat 64 (2 * val + 1) >>> 1 ≠ 0#64 := by assumption
    rw [natSmallEnc_ushiftRight1 hsmall] at hvnz
    have hvpos : 0 < val := Classical.byContradiction fun hle0 => by
      have hv0 : val = 0 := by omega
      subst hv0
      exact hvnz rfl
    have hlen1 : limbLenNat val = 1 := limbLenNat_eq_one hvpos (by omega : val < 2 ^ 64)
    have hdstPos : 0 < dstXs.length := by rw [hlen1] at hlenDst; omega
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    rw [BitVec.add_zero]
    apply wp_store_sep
    · exact c0_store_array64_zero _ hmDst hdstPos
    · intro m' hm'
      dsimp only [Arg.val] at hm'
      rw [natSmallEnc_ushiftRight1 hsmall] at hm'
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      rw [hlen1] at hQ
      have hm'' := sep_unpick2_3 hm'
      refine hQ (dstXs.set 0 (BitVec.ofNat 64 val)) m' (List.length_set ..) ?_ ?_ hm''
      · cases dstXs with
        | nil => simp at hdstPos
        | cons d ds =>
          simp only [List.set_cons_zero, List.take_succ_cons, List.take_zero, limbsVal_cons,
            limbsVal_nil, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by omega : val < 2 ^ 64)
      · exact List.drop_set_of_lt (by decide : 0 < 1)
  · have ha0 : a &&& (1 : BitVec 64) = 0#64 := by assumption
    have hbig : 2 ^ 63 ≤ val := Classical.byContradiction fun hlt => by
      have hsm : val < 2 ^ 63 := by omega
      unfold natRep at hrep
      simp only [hsm, ↓reduceIte] at hrep
      subst hrep
      rw [show (1 : BitVec 64) = 1#64 from rfl, natSmallEnc_and1 hsm] at ha0
      contradiction
    have hnsm : ¬ val < 2 ^ 63 := by omega
    unfold natRep at hrep
    simp only [hnsm, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    have hm1 : (BigNumRt.lcnfHeap objs ⋆ (array64 dst dstXs ⋆ R)) m := sep_assoc_r hm
    obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn hcanon.2.1 hm1
    rw [haddr] at hmObj
    have hmMeta := sep_mpz_swap2 hmObj
    rw [wp_load]
    refine ⟨obj.mpzMeta, loadVal_cell64 hmMeta, ?_⟩
    change LeanQbe.T.wp _ _ _ _ _
    apply wp_sext (by decide); intro p_4 hp_4
    apply wp_lshr; intro p_5 hp_5
    apply wp_add; intro p_6 hp_6
    dsimp only [Arg.val] at hp_4 hp_5 hp_6
    have hbounds := mpz_wf_bounds hcanon.1 hcanon.2.1
    have hp5_eq : p_5 = BitVec.ofNat 64 obj.arrSize := by
      rw [hp_5, hp_4, show (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 from rfl]
      exact LcnfObj.mpzMeta_arrSize obj hbounds.1 hbounds.2
    have hne : obj.limbs ≠ [] := by
      intro hempty; have h1 := hcanon.2.2.2.2.1; rw [hempty, List.length_nil] at h1; omega
    have hlen : limbLenNat val = obj.arrSize := by
      rw [← hcanon.2.2.2.2.2.2.2.1, hcanon.2.2.2.1]
      exact limbLenNat_eq_length_of_trimmed hne hcanon.2.2.2.2.2.2.1
    have harrLt64 : obj.arrSize < 2 ^ 64 := by omega
    have harrToNat : (BitVec.ofNat 64 obj.arrSize).toNat = obj.arrSize := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt harrLt64]
    have hmArr : (array64 dst dstXs ⋆ array64 (a + 16#64) obj.limbs ⋆
        (cell64 (a + 8#64) obj.mpzMeta ⋆ cell64 a obj.header ⋆
          ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆ R))) m :=
      sep_ac hmMeta
    apply wp_call_of
    apply rtR1Env_bn_copy
    dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
    rw [hp_6, hp5_eq]
    refine ⟨dstXs, obj.limbs, _, ?_, ?_, hmArr, ?_⟩
    · rw [harrToNat, ← hlen]; exact hlenDst
    · rw [harrToNat, hcanon.2.2.2.1]; exact le_refl _
    · intro m' hmCopy
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      rw [harrToNat] at hmCopy
      have htakeSelf : obj.limbs.take obj.arrSize = obj.limbs := by
        rw [hcanon.2.2.2.1, List.take_length]
      let dstXs' := obj.limbs.take obj.arrSize ++ dstXs.drop obj.arrSize
      have hdstEq : dstXs' = obj.limbs ++ dstXs.drop obj.arrSize := by
        dsimp [dstXs']; rw [htakeSelf]
      have hmRest : (cell64 a obj.header ⋆ cell64 (a + 8#64) obj.mpzMeta ⋆
        array64 (a + 16#64) obj.limbs ⋆
          ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆
            (array64 dst dstXs' ⋆ R))) m' := sep_ac hmCopy
      have hmHeap := sep_assoc_l (lcnfHeap_mpz_restore hlt heq hcanon.2.1
        (by rw [haddr]; exact hmRest))
      have hlen' : dstXs'.length = dstXs.length := by
        rw [hdstEq]
        have hleDst : obj.arrSize ≤ dstXs.length := by rw [← hlen]; exact hlenDst
        rw [List.length_append, List.length_drop, ← hcanon.2.2.2.1]
        omega
      have htake' : dstXs'.take (limbLenNat val) = obj.limbs := by
        rw [hdstEq, hlen, hcanon.2.2.2.1, List.take_left]
      have hdrop' : dstXs'.drop (limbLenNat val) = dstXs.drop (limbLenNat val) := by
        rw [hdstEq, hlen, hcanon.2.2.2.1, List.drop_left]
      rw [← hlen]
      exact hQ dstXs' m' hlen' (by rw [htake', hcanon.2.2.2.2.2.2.2.1]) hdrop' hmHeap

theorem bn_load_int_wp :
    ∀ xs m Q X, bnLoadIntSpec xs m Q X → Func.wp rtR1Env bn_load_int.body xs m Q X := by
  intro ⟨a, dst, ⟨⟩⟩ m Q X ⟨val, objs, dstXs, R, hrep, hlenDst, hm, hQ⟩
  dsimp only [Func.wp, bn_load_int, bn_load_int_body]
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
      unfold intRep at hrep
      simp only [hnb, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold intRep at hrep
    simp only [hsmall] at hrep
    subst hrep
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsmall.1 hsmall.2
    have hzero : (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 = 0#64 := by assumption
    have hval0 : val = 0 := by rw [← htoInt, hzero]; rfl
    subst hval0
    have hinfo0 : BitVec.ofNat 64 (limbLenNat (0 : Int).natAbs) <<< 1 |||
        (if (0 : Int) < 0 then 1#64 else 0#64) = 0#64 := by decide
    rw [hinfo0, Int.natAbs_zero, limbLenNat_zero] at hQ
    exact hQ dstXs m rfl rfl rfl hm
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
      unfold intRep at hrep
      simp only [hnb, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold intRep at hrep
    simp only [hsmall] at hrep
    subst hrep
    have ⟨_, hshr⟩ := intSmallEnc_sshiftRight1 hsmall.1 hsmall.2
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsmall.1 hsmall.2
    have hsgt : (0#64 : BitVec 64).slt ((BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1) = true := by
      assumption
    rw [BitVec.slt, decide_eq_true_eq, htoInt, show (0#64 : BitVec 64).toInt = 0 from rfl] at hsgt
    have hlen1 : limbLenNat val.natAbs = 1 := limbLenNat_eq_one (by omega) (by omega)
    have hdstPos : 0 < dstXs.length := by rw [hlen1] at hlenDst; omega
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    rw [BitVec.add_zero]
    apply wp_store_sep
    · exact c0_store_array64_zero _ hmDst hdstPos
    · intro m' hm'
      dsimp only [Arg.val] at hm'
      rw [hshr] at hm'
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      have hm'' := sep_unpick2_3 hm'
      have hnotNeg : ¬ val < 0 := by omega
      have hinfo : BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1 ||| (if val <
        0 then 1#64 else 0#64) = 2#64 := by
        rw [hlen1]; simp only [hnotNeg, ↓reduceIte]; decide
      rw [hinfo] at hQ
      refine hQ (dstXs.set 0 (BitVec.ofInt 64 val)) m' (List.length_set ..) ?_ ?_ hm''
      · rw [hlen1]
        cases dstXs with
        | nil => simp at hdstPos
        | cons d ds =>
          simp only [List.set_cons_zero, List.take_succ_cons, List.take_zero, limbsVal_cons,
            limbsVal_nil, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofInt]
          omega
      · rw [hlen1]; exact List.drop_set_of_lt (by decide : 0 < 1)
  · have ha1 : a &&& (1 : BitVec 64) ≠ 0#64 := by assumption
    have hsmall : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
      unfold intRep at hrep
      simp only [hnb, ↓reduceIte] at hrep
      exact ha1 hrep.1
    unfold intRep at hrep
    simp only [hsmall] at hrep
    subst hrep
    have ⟨_, hshr⟩ := intSmallEnc_sshiftRight1 hsmall.1 hsmall.2
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsmall.1 hsmall.2
    have hnz : (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 ≠ 0#64 := by assumption
    have hnlt : (0#64 : BitVec 64).slt ((BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1) = false := by
      assumption
    simp only [BitVec.slt, decide_eq_false_iff_not, htoInt,
      show (0#64 : BitVec 64).toInt = 0 from rfl] at hnlt
    have hvalNeg : val < 0 := Classical.byContradiction fun hge0 => by
      have hval0 : val = 0 := by omega
      subst hval0; apply hnz; rw [hshr]; rfl
    have hlen1 : limbLenNat val.natAbs = 1 := limbLenNat_eq_one (by omega) (by omega)
    have hdstPos : 0 < dstXs.length := by rw [hlen1] at hlenDst; omega
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    rw [BitVec.add_zero]
    apply wp_store_sep
    · exact c0_store_array64_zero _ hmDst hdstPos
    · intro m' hm'
      dsimp only [Arg.val] at hm'
      rw [hshr] at hm'
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      have hm'' := sep_unpick2_3 hm'
      have hinfo : BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1 ||| (if val <
        0 then 1#64 else 0#64) = 3#64 := by
        rw [hlen1]; simp only [hvalNeg, ↓reduceIte]; decide
      have hnegEq : (0 : BitVec 64) - BitVec.ofInt 64 val = BitVec.ofNat 64 val.natAbs := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl, BitVec.toNat_ofInt,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : val.natAbs < 2 ^ 64)]
        omega
      rw [hnegEq] at hm''
      rw [hinfo] at hQ
      refine hQ (dstXs.set 0 (BitVec.ofNat 64 val.natAbs)) m' (List.length_set ..) ?_ ?_ hm''
      · rw [hlen1]
        cases dstXs with
        | nil => simp at hdstPos
        | cons d ds =>
          simp only [List.set_cons_zero, List.take_succ_cons, List.take_zero, limbsVal_cons,
            limbsVal_nil, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by omega)
      · rw [hlen1]; exact List.drop_set_of_lt (by decide : 0 < 1)
  · have ha0 : a &&& (1 : BitVec 64) = 0#64 := by assumption
    have hbig : ¬ (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) := by
      intro hsm
      unfold intRep at hrep
      simp only [hsm] at hrep
      subst hrep
      have ⟨hand, _⟩ := intSmallEnc_toInt hsm.1 hsm.2
      exact absurd ha0 (by rw [show (1 : BitVec 64) = 1#64 from rfl, hand]; decide)
    unfold intRep at hrep
    simp only [hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    have hm1 : (BigNumRt.lcnfHeap objs ⋆ (array64 dst dstXs ⋆ R)) m := sep_assoc_r hm
    obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn hcanon.2.1 hm1
    rw [haddr] at hmObj
    rw [wp_load]
    refine ⟨obj.header,
      by dsimp only [Arg.val]; exact loadVal_cell64 (sep_assoc_r (sep_assoc_r hmObj)), ?_⟩
    change LeanQbe.T.wp _ _ _ _ _
    have hne : obj.limbs ≠ [] := by
      intro hempty; have h1 := hcanon.2.2.2.2.1; rw [hempty, List.length_nil] at h1; omega
    have hlen : limbLenNat val.natAbs = obj.arrSize := by
      rw [← hcanon.2.2.2.2.2.2.2.1, hcanon.2.2.2.1]
      exact limbLenNat_eq_length_of_trimmed hne hcanon.2.2.2.2.2.2.1
    refine wp_join_group (fun (xs : Tup Val [i64]) m' =>
        xs.1 = (if val < 0 then 1#64 else 0#64) ∧ m' = m) ?_ ?_
    · intro J ⟨negBit, ⟨⟩⟩ m' ⟨hneg, hm'⟩
      subst hneg hm'
      change LeanQbe.T.wp _ _ _ _ _
      simp only [Blocks.get]
      apply wp_add; intro p_add hp_add
      have hmMeta := sep_mpz_swap2 hmObj
      rw [wp_load]
      refine ⟨obj.mpzMeta, by dsimp only [Arg.val]; rw [hp_add]; exact loadVal_cell64 hmMeta, ?_⟩
      change LeanQbe.T.wp _ _ _ _ _
      apply wp_sext (by decide); intro p_5 hp_5
      apply wp_lshr; intro p_6 hp_6
      apply wp_add; intro p_7 hp_7
      dsimp only [Arg.val] at hp_5 hp_6 hp_7
      have hbounds := mpz_wf_bounds hcanon.1 hcanon.2.1
      have hp6_eq : p_6 = BitVec.ofNat 64 obj.arrSize := by
        rw [hp_6, hp_5, show (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 from rfl]
        exact LcnfObj.mpzMeta_arrSize obj hbounds.1 hbounds.2
      have harrLt64 : obj.arrSize < 2 ^ 64 := by omega
      have harrToNat : (BitVec.ofNat 64 obj.arrSize).toNat = obj.arrSize := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt harrLt64]
      have hmArr : (array64 dst dstXs ⋆ array64 (a + 16#64) obj.limbs ⋆
          (cell64 (a + 8#64) obj.mpzMeta ⋆ cell64 a obj.header ⋆
            ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆
              R))) m' :=
        sep_ac hmMeta
      apply wp_call_of
      apply rtR1Env_bn_copy
      dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
      rw [hp_7, hp6_eq]
      refine ⟨dstXs, obj.limbs, _, ?_, ?_, hmArr, ?_⟩
      · rw [harrToNat, ← hlen]; exact hlenDst
      · rw [harrToNat, hcanon.2.2.2.1]; exact le_refl _
      · intro m'' hmCopy
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        rw [harrToNat] at hmCopy
        have htakeSelf : obj.limbs.take obj.arrSize = obj.limbs := by
          rw [hcanon.2.2.2.1, List.take_length]
        let dstXs' := obj.limbs.take obj.arrSize ++ dstXs.drop obj.arrSize
        have hdstEq : dstXs' = obj.limbs ++ dstXs.drop obj.arrSize := by
          dsimp [dstXs']; rw [htakeSelf]
        have hmRest : (cell64 a obj.header ⋆ cell64 (a + 8#64) obj.mpzMeta ⋆
          array64 (a + 16#64) obj.limbs ⋆
            ((BigNumRt.lcnfHeap (objs.take idx) ⋆ BigNumRt.lcnfHeap (objs.drop (idx + 1))) ⋆
              (array64 dst dstXs' ⋆ R))) m'' := sep_ac hmCopy
        have hmHeap := sep_assoc_l (lcnfHeap_mpz_restore hlt heq hcanon.2.1
          (by rw [haddr]; exact hmRest))
        have hlen' : dstXs'.length = dstXs.length := by
          rw [hdstEq]
          have hleDst : obj.arrSize ≤ dstXs.length := by rw [← hlen]; exact hlenDst
          rw [List.length_append, List.length_drop, ← hcanon.2.2.2.1]
          omega
        have htake' : dstXs'.take (limbLenNat val.natAbs) = obj.limbs := by
          rw [hdstEq, hlen, hcanon.2.2.2.1, List.take_left]
        have hdrop' : dstXs'.drop (limbLenNat val.natAbs) = dstXs.drop (limbLenNat val.natAbs) := by
          rw [hdstEq, hlen, hcanon.2.2.2.1, List.drop_left]
        rw [← hlen]
        exact hQ dstXs' m'' hlen' (by rw [htake', hcanon.2.2.2.2.2.2.2.1]) hdrop' hmHeap
    · intro J hJ
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      · have hne0 : (obj.header >>> 48) &&& (255 : BitVec 64) ≠ 0#64 := by assumption
        rw [show (obj.header >>> 48 : BitVec 64) = obj.header >>> 48#64 from rfl,
          show (255 : BitVec 64) = 0xff#64 from rfl,
          LcnfObj.header_other_byte obj hcanon.1] at hne0
        have hoth1 : obj.other = 1 := by
          rcases hcanon.2.2.1 with h0 | h1
          · rw [h0] at hne0; exact absurd rfl hne0
          · exact h1
        have hvNeg : val < 0 := hcanon.2.2.2.2.2.2.2.2.1.mp hoth1
        exact hJ (1#64, ()) m ⟨by simp only [hvNeg, ↓reduceIte], rfl⟩
      · have heq0 : (obj.header >>> 48) &&& (255 : BitVec 64) = 0#64 := by assumption
        rw [show (obj.header >>> 48 : BitVec 64) = obj.header >>> 48#64 from rfl,
          show (255 : BitVec 64) = 0xff#64 from rfl,
          LcnfObj.header_other_byte obj hcanon.1] at heq0
        have hoth0 : obj.other = 0 := by
          rcases hcanon.2.2.1 with h0 | h1
          · exact h0
          · rw [h1] at heq0; exact absurd heq0 (by decide)
        have hnotNeg : ¬ val < 0 := fun hv => by
          have h1 := hcanon.2.2.2.2.2.2.2.2.1.mpr hv; omega
        exact hJ (0#64, ()) m ⟨by simp only [hnotNeg, ↓reduceIte], rfl⟩

theorem bn_nat_from_limbs_wp :
    ∀ xs m Q X, bnNatFromLimbsSpec xs m Q X → Func.wp rtR1Env bn_nat_from_limbs.body xs m Q X := by
  intro ⟨rt, buf, n, ⟨⟩⟩ m Q X ⟨st, bufXs, objs, R, hnle, hnMax, hbd, havail, hm, hQ⟩
  dsimp only [Func.wp, bn_nat_from_limbs, bn_nat_from_limbs_body]
  change LeanQbe.T.wp _ _ _ _ _
  let tn := trimLenLoop bufXs n.toNat
  let val := limbsVal (bufXs.take n.toNat)
  have htnLe : tn ≤ n.toNat := trimLenLoop_le bufXs n.toNat
  have htnMax : tn ≤ mpzMaxLimbs := le_trans htnLe hnMax
  have htnLt64 : tn < 2 ^ 64 := by unfold mpzMaxLimbs at htnMax; omega
  have hvalEq : val = limbsVal (bufXs.take tn) := (limbsVal_trimLenLoop bufXs n.toNat hnle).symm
  have hmTrim : (array64 buf bufXs ⋆ (BigNumRt.rtC0Inv rt st ⋆ BigNumRt.lcnfHeap objs ⋆
    R)) m := sep_pick2_4 hm
  have hBoxed : ∀ (htnPos : 0 < tn), 2 ^ 63 ≤ val →
      LeanQbe.T.wp rtR1Env Q X
        (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc"
          (Arg.var rt, @Arg.var Val i64 (BitVec.ofNat 64 tn), ()) fun (p : Tup Val [i64]) =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.1, Arg.imm 16#64,
              ()) } fun (p_1 : Tup Val [i64]) =>
            Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
              (Arg.var p_1.1, Arg.var buf, @Arg.var Val i64 (BitVec.ofNat 64 tn), ())
              fun (_ : Tup Val []) =>
              Expr.ret (Arg.var p.1, ())) m := by
    intro htnPos hbig
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    have hmAlloc : (BigNumRt.rtC0Inv rt st ⋆ (array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) m :=
      sep_pick1_4 (sep_unpick2_4 hmTrim)
    apply wp_call_of
    apply rtR1Env_lcnf_nat_alloc
    dsimp only [lcnfNatAllocSpec, vals, Tup.map, Arg.val]
    refine ⟨st, _, ?_, hbd, ?_, hmAlloc, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; exact htnMax
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos]; exact havail hbig
    · intro p st' mAlloc hwf0 hand0 hpres0 hrem0 hbd0 hmObj0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos] at hwf0 hmObj0
      let bytes := 16 + 8 * tn
      let newObj0 : BigNumRt.LcnfObj :=
        { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
          tag := mpzTag,
          cap := tn, arrSize := tn, limbs := List.replicate tn 0#64 }
      change LeanQbe.T.wp _ _ _ _ _
      apply wp_add; intro p_5 hp_5
      dsimp only [Arg.val] at hp_5
      have hobj0Elim := lcnfObjMem_mpz_elim (o := newObj0) rfl (sep_assoc_r (sep_swap12l hmObj0))
      have hmCopyIn : (array64 (p + 16#64) newObj0.limbs ⋆ array64 buf bufXs ⋆
          (cell64 (p + 8#64) newObj0.mpzMeta ⋆ cell64 p newObj0.header ⋆
            (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfHeap objs ⋆ R))) mAlloc := sep_ac hobj0Elim
      apply wp_call_of
      apply rtR1Env_bn_copy
      dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
      rw [hp_5]
      refine ⟨newObj0.limbs, bufXs, _, ?_, ?_, hmCopyIn, ?_⟩
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; dsimp [newObj0]
        rw [List.length_replicate]; exact le_refl _
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; omega
      · intro mCopy hmCopyOut
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at hmCopyOut
        have hdrop0 : List.drop tn newObj0.limbs = [] := by
          dsimp [newObj0]
          rw [List.drop_of_length_le (by rw [List.length_replicate]; exact le_refl _)]
        have hmCopyClean : (array64 (p + 16#64) (bufXs.take tn) ⋆ array64 buf bufXs ⋆
            (cell64 (p + 8#64) newObj0.mpzMeta ⋆ cell64 p newObj0.header ⋆
              (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfHeap objs ⋆ R))) mCopy := by
          rw [hdrop0, List.append_nil] at hmCopyOut; exact hmCopyOut
        let newObj : BigNumRt.LcnfObj :=
          { newObj0 with limbs := bufXs.take tn }
        have hnewObjWf : newObj.Wf :=
          mpz_wf_of_limbs hwf0 rfl rfl rfl rfl rfl hwf0.2.2.2.2.1 rfl rfl
            (by dsimp [newObj, newObj0]; exact htakeLen)
        have hcanon : mpzNatCanon newObj val :=
          ⟨hnewObjWf, rfl, rfl, htakeLen.symm, by rw [htakeLen]; exact htnPos,
            by rw [htakeLen]; exact htnMax, hlastNe, hvalEq.symm, hbig⟩
        have hmPacked : (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆
            BigNumRt.lcnfHeap (newObj :: objs) ⋆ R) mCopy := by
          have h1 : (cell64 p newObj.header ⋆ cell64 (p + 8#64) newObj.mpzMeta ⋆
              array64 (p + 16#64) newObj.limbs ⋆
              (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) mCopy :=
            sep_ac hmCopyClean
          have h2 := lcnfObjMem_mpz_intro (o := newObj) rfl h1
          rw [lcnfHeap_cons_eq]
          exact sep_ac h2
        have hnotSm : ¬ val < 2 ^ 63 := by omega
        refine hQ p st' (newObj :: objs) mCopy hpres0 hrem0 hbd0 ?_
          (fun h => absurd h hnotSm) (fun _ => ⟨newObj, rfl, hcanon, rfl⟩) hmPacked
        change natRep p val (newObj :: objs)
        unfold natRep
        simp only [show ¬ val < 2 ^ 63 from by omega, ↓reduceIte]
        exact ⟨hand0, newObj, List.mem_cons_self .., rfl, hcanon⟩
  apply wp_call_of
  apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bufXs, _, hnle, hmTrim, ?_⟩
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have htn0bv : BitVec.ofNat 64 tn = 0#64 := by assumption
    have htn0 : tn = 0 := by
      have := congrArg BitVec.toNat htn0bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hval0 : val = 0 := by rw [hvalEq, htn0, List.take_zero, limbsVal_nil]
    have hQ' := hQ 1#64 st objs m (preservesMeta_refl st) (le_refl _) hbd
    dsimp only [val] at hval0
    rw [hval0] at hQ'
    refine hQ' ?_ (fun _ => rfl) (fun h => absurd h (by decide)) (sep_unpick2_4 hmTrim)
    unfold natRep; simp
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hval1 : val = bufXs[0].toNat := by
      rw [hvalEq, htn1, htake1, limbsVal_cons, limbsVal_nil]; omega
    have hult : bufXs[0].toNat < ((1 : BitVec 64) <<< 63).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 63).toNat = 2 ^ 63 from rfl] at hult
    have hvalSm : val < 2 ^ 63 := by rw [hval1]; exact hult
    have henc : bufXs[0] <<< 1 ||| (1 : BitVec 64) = BitVec.ofNat 64 (2 * val + 1) := by
      rw [show (1 : BitVec 64) = 1#64 from rfl, bv64_ofNat_small_enc hult, ← hval1]
    rw [henc]
    have hnotBig : ¬ (2 ^ 63 ≤ val) := by omega
    refine hQ (BitVec.ofNat 64 (2 * val + 1)) st objs m
      (preservesMeta_refl st) (le_refl _) hbd ?_
      (fun _ => rfl) (fun h => absurd h hnotBig) (sep_unpick2_4 hmTrim)
    change natRep (BitVec.ofNat 64 (2 * val + 1)) val objs
    unfold natRep; simp only [hvalSm, ↓reduceIte]
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hval1 : val = bufXs[0].toNat := by
      rw [hvalEq, htn1, htake1, limbsVal_cons, limbsVal_nil]; omega
    have huge : ¬ bufXs[0].toNat < ((1 : BitVec 64) <<< 63).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 63).toNat = 2 ^ 63 from rfl] at huge
    exact hBoxed (by omega) (by rw [hval1]; omega)
  · have htnNzBv : BitVec.ofNat 64 tn ≠ 0#64 := by assumption
    have htnNe1 : BitVec.ofNat 64 tn ≠ 1#64 := by assumption
    have htnPos : 0 < tn := Classical.byContradiction fun hle0 => by
      have h0 : tn = 0 := by omega
      apply htnNzBv; rw [h0]
    have htnGe2 : 2 ≤ tn := Classical.byContradiction fun hlt2 => by
      have h1 : tn = 1 := by omega
      apply htnNe1; rw [h1]
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    have htakeNe : bufXs.take tn ≠ [] := by intro h; rw [h, List.length_nil] at htakeLen; omega
    have hpow : 2 ^ 64 ≤ val := by
      rw [hvalEq]
      have hge := limbsVal_ge_pow_of_nonzero_last htakeNe
        (by rw [getLast_eq_getLast! _ htakeNe]; exact hlastNe)
      rw [htakeLen] at hge
      have hpow1 : 2 ^ 64 ≤ 2 ^ (64 * (tn - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    exact hBoxed htnPos (by omega)

theorem bn_int_from_limbs_wp :
    ∀ xs m Q X, bnIntFromLimbsSpec xs m Q X → Func.wp rtR1Env bn_int_from_limbs.body xs m Q X := by
  intro ⟨rt, neg, buf, n, ⟨⟩⟩ m Q X ⟨st, bufXs, objs, R, hnle, hnMax, hbd, havail, hm, hQ⟩
  dsimp only [Func.wp, bn_int_from_limbs, bn_int_from_limbs_body]
  change LeanQbe.T.wp _ _ _ _ _
  let tn := trimLenLoop bufXs n.toNat
  let mag := limbsVal (bufXs.take n.toNat)
  let val : Int := if tn = 0 then 0 else if neg = 0#64 then (mag : Int) else -(mag : Int)
  have htnLe : tn ≤ n.toNat := trimLenLoop_le bufXs n.toNat
  have htnMax : tn ≤ mpzMaxLimbs := le_trans htnLe hnMax
  have htnLt64 : tn < 2 ^ 64 := by unfold mpzMaxLimbs at htnMax; omega
  have hmagEq : mag = limbsVal (bufXs.take tn) := (limbsVal_trimLenLoop bufXs n.toNat hnle).symm
  have hmTrim : (array64 buf bufXs ⋆ (BigNumRt.rtC0Inv rt st ⋆ BigNumRt.lcnfHeap objs ⋆
    R)) m := sep_pick2_4 hm
  have hBoxed : ∀ (htnPos : 0 < tn), (val < -2 ^ 62 ∨ 2 ^ 62 ≤ val) →
      LeanQbe.T.wp rtR1Env Q X
        (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc"
          (Arg.var rt, @Arg.var Val i64 (BitVec.ofNat 64 tn), ()) fun (p : Tup Val [i64]) =>
          Expr.group
            (fun (_ : Tup Cont [[]]) =>
              Blocks.cons
                (fun (_ : Tup Val []) =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.1,
                      Arg.imm 16#64, ()) } fun (p_2 : Tup Val [i64]) =>
                    Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
                      (Arg.var p_2.1, Arg.var buf, @Arg.var Val i64 (BitVec.ofNat 64 tn), ())
                      fun (_ : Tup Val []) =>
                      Expr.ret (Arg.var p.1, ()))
                Blocks.nil)
            fun (Js : Tup Cont [[]]) =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (by decide),
                args := (Arg.var neg, Arg.imm 0#64, ()) } fun (p_1 : Tup Val [Ty.bool]) =>
              Expr.jnz (Arg.var p_1.1)
                (Expr.load i64 (Arg.var p.1) fun (ld : Val i64) =>
                  Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm (48 : BitVec 32),
                      ()) } fun (p_2 : Tup Val [i64]) =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.imm 1#64,
                        Arg.var p_2.1, ()) } fun (p_3 : Tup Val [i64]) =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var ld,
                          Arg.var p_3.1, ()) } fun (p_4 : Tup Val [i64]) =>
                        Expr.store (Arg.var p_4.1) (Arg.var p.1) (Expr.jump Js.1 (PUnit.unit : Tup
                          (Arg Val) [])))
                (Expr.jump Js.1 (PUnit.unit : Tup (Arg Val) []))) m := by
    intro htnPos hbig
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    have htakeNe : bufXs.take tn ≠ [] := by intro h; rw [h, List.length_nil] at htakeLen; omega
    have hvalNz : val = if neg = 0#64 then (mag : Int) else -(mag : Int) := by
      dsimp [val]; simp [show tn ≠ 0 from by omega]
    have hmAlloc : (BigNumRt.rtC0Inv rt st ⋆ (array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) m :=
      sep_pick1_4 (sep_unpick2_4 hmTrim)
    apply wp_call_of
    apply rtR1Env_lcnf_nat_alloc
    dsimp only [lcnfNatAllocSpec, vals, Tup.map, Arg.val]
    refine ⟨st, _, ?_, hbd, ?_, hmAlloc, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; exact htnMax
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos]; exact havail hbig
    · intro p st' mAlloc hwf0 hand0 hpres0 hrem0 hbd0 hmObj0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos] at hwf0 hmObj0
      let bytes := 16 + 8 * tn
      let newObj0 : BigNumRt.LcnfObj :=
        { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
          tag := mpzTag,
          cap := tn, arrSize := tn, limbs := List.replicate tn 0#64 }
      let newObj1 : BigNumRt.LcnfObj :=
        { newObj0 with other := if neg = 0#64 then 0 else 1 }
      have hobj1Wf : newObj1.Wf :=
        mpz_wf_of_limbs hwf0 rfl rfl rfl rfl rfl (by dsimp [newObj1]; split <;> decide) rfl rfl
          (by dsimp [newObj1, newObj0]; rw [List.length_replicate])
      change LeanQbe.T.wp _ _ _ _ _
      refine wp_join_group (fun (_ : Tup Val []) m1 =>
          (BigNumRt.lcnfObjMem newObj1 ⋆
            (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) m1) ?_ ?_
      · intro Js1 _ m1 hm1
        change LeanQbe.T.wp _ _ _ _ _
        apply wp_add; intro p_6 hp_6
        dsimp only [Arg.val] at hp_6
        have hobj1Elim := lcnfObjMem_mpz_elim (o := newObj1) rfl hm1
        have hmCopyIn : (array64 (p + 16#64) newObj1.limbs ⋆ array64 buf bufXs ⋆
            (cell64 (p + 8#64) newObj1.mpzMeta ⋆ cell64 p newObj1.header ⋆
              (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfHeap objs ⋆ R))) m1 := sep_ac hobj1Elim
        apply wp_call_of
        apply rtR1Env_bn_copy
        dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
        rw [hp_6]
        refine ⟨newObj1.limbs, bufXs, _, ?_, ?_, hmCopyIn, ?_⟩
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; dsimp [newObj1, newObj0]
          rw [List.length_replicate]; exact le_refl _
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; omega
        · intro mCopy hmCopyOut
          change LeanQbe.T.wp _ _ _ _ _
          c0_steps
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at hmCopyOut
          have hdrop0 : List.drop tn newObj1.limbs = [] := by
            dsimp [newObj1, newObj0]
            rw [List.drop_of_length_le (by rw [List.length_replicate]; exact le_refl _)]
          have hmCopyClean : (array64 (p + 16#64) (bufXs.take tn) ⋆ array64 buf bufXs ⋆
              (cell64 (p + 8#64) newObj1.mpzMeta ⋆ cell64 p newObj1.header ⋆
                (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfHeap objs ⋆ R))) mCopy := by
            rw [hdrop0, List.append_nil] at hmCopyOut; exact hmCopyOut
          let newObj : BigNumRt.LcnfObj :=
            { newObj1 with limbs := bufXs.take tn }
          have hmagPos : 0 < mag := by
            rw [hmagEq]
            have hge := limbsVal_ge_pow_of_nonzero_last htakeNe
              (by rw [getLast_eq_getLast! _ htakeNe]; exact hlastNe)
            have h1 := Nat.one_le_pow (64 * ((bufXs.take tn).length - 1)) 2 (by decide)
            omega
          have hnatAbs : val.natAbs = mag := by
            rw [hvalNz]; split <;> simp [Int.natAbs_natCast]
          have hothDisj : newObj.other = 0 ∨ newObj.other = 1 := by
            dsimp [newObj, newObj1]; split <;> simp
          have hothNeg : newObj.other = 1 ↔ val < 0 := by
            dsimp [newObj, newObj1]
            rw [hvalNz]
            by_cases hn0 : neg = 0#64
            · simp [hn0]
            · simp [hn0]; omega
          have hnewObjWf : newObj.Wf :=
            mpz_wf_of_limbs hobj1Wf rfl rfl rfl rfl rfl hobj1Wf.2.2.2.2.1 rfl rfl
              (by dsimp [newObj, newObj1, newObj0]; exact htakeLen)
          have hcanon : mpzIntCanon newObj val :=
            ⟨hnewObjWf, rfl, hothDisj, htakeLen.symm, by rw [htakeLen]; exact htnPos,
              by rw [htakeLen]; exact htnMax, hlastNe, hmagEq.symm.trans hnatAbs.symm, hothNeg,
              hbig⟩
          have hmPacked : (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆
              BigNumRt.lcnfHeap (newObj :: objs) ⋆ R) mCopy := by
            have h1 : (cell64 p newObj.header ⋆ cell64 (p + 8#64) newObj.mpzMeta ⋆
                array64 (p + 16#64) newObj.limbs ⋆
                (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) mCopy :=
              sep_ac hmCopyClean
            have h2 := lcnfObjMem_mpz_intro (o := newObj) rfl h1
            rw [lcnfHeap_cons_eq]
            exact sep_ac h2
          have hnotSm : ¬ (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) := by omega
          refine hQ p st' (newObj :: objs) mCopy hpres0 hrem0 hbd0 ?_
            (fun h => absurd h hnotSm) (fun _ => ⟨newObj, rfl, hcanon, rfl⟩) hmPacked
          change intRep p val (newObj :: objs)
          unfold intRep
          simp only [hnotSm, ↓reduceIte]
          exact ⟨hand0, newObj, List.mem_cons_self .., rfl, hcanon⟩
      · intro Js1 hJs1
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · have hnegNz : neg ≠ 0#64 := by assumption
          have hmObj0_elim := sep_assoc_r (sep_assoc_r
            (lcnfObjMem_mpz_elim (o := newObj0) rfl (sep_assoc_r (sep_swap12l hmObj0))))
          rw [wp_load]
          refine ⟨newObj0.header,
            by
              dsimp only [Arg.val]
              change loadVal mAlloc i64 newObj0.addr = some newObj0.header
              exact loadVal_cell64 hmObj0_elim,
            ?_⟩
          change LeanQbe.T.wp _ _ _ _ _
          apply wp_sext (by decide); intro p_s hp_s
          apply wp_shl; intro p_sh hp_sh
          apply wp_or; intro p_or hp_or
          dsimp only [Arg.val] at hp_s hp_sh hp_or
          apply wp_store_sep
          · dsimp only [Arg.val]
            change storeOk mAlloc i64 newObj0.addr ∧ _
            exact store_cell64 p_or hmObj0_elim
          · intro m1 hm1
            have hpOrEq : p_or = newObj1.header := by
              rw [hp_or, hp_sh, hp_s,
                show (BitVec.signExtend 64 (48 : BitVec 32)).toNat % 64 = 48 from rfl]
              have hhdr1 := LcnfObj.header_or_other_one newObj0 hwf0.2.2.2.1 rfl
              rw [show (1#64 : BitVec 64) <<< 48 = 1#64 <<< 48#64 from rfl, hhdr1]
              dsimp [newObj1]
              simp only [hnegNz, ↓reduceIte]
            rw [hpOrEq] at hm1
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            have hm1' : (cell64 newObj1.addr newObj1.header ⋆
              cell64 (newObj1.addr + 8#64) newObj1.mpzMeta ⋆
                array64 (newObj1.addr + 16#64) newObj1.limbs ⋆
                (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) m1 :=
              sep_mpz_to_list4 hm1
            exact hJs1 () m1 (lcnfObjMem_mpz_intro (o := newObj1) rfl hm1')
        · have hneg0 : neg = 0#64 := by assumption
          have hEq01 : newObj1 = newObj0 := by dsimp [newObj1]; simp [hneg0]; rfl
          have hm1 : (BigNumRt.lcnfObjMem newObj0 ⋆
              (BigNumRt.rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ BigNumRt.lcnfHeap objs ⋆ R)) mAlloc :=
            sep_pick2_3r hmObj0
          rw [← hEq01] at hm1
          exact hJs1 () mAlloc hm1
  apply wp_call_of
  apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bufXs, _, hnle, hmTrim, ?_⟩
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have htn0bv : BitVec.ofNat 64 tn = 0#64 := by assumption
    have htn0 : tn = 0 := by
      have := congrArg BitVec.toNat htn0bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hval0 : (if trimLenLoop bufXs (BitVec.toNat n) = 0 then (0 : Int)
        else if neg = 0#64 then ↑(limbsVal (List.take (BitVec.toNat n) bufXs))
        else -↑(limbsVal (List.take (BitVec.toNat n) bufXs))) = 0 := by
      rw [show trimLenLoop bufXs (BitVec.toNat n) = 0 from htn0]; rfl
    have hQ' := hQ 1#64 st objs m (preservesMeta_refl st) (le_refl _) hbd
    rw [hval0] at hQ'
    refine hQ' ?_ (fun _ => rfl) (fun h => absurd h (by decide)) (sep_unpick2_4 hmTrim)
    unfold intRep; simp
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hneg0 : neg = 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hvalPos : val = (bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hneg0, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hult : bufXs[0].toNat < ((1 : BitVec 64) <<< 62).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 62).toNat = 2 ^ 62 from rfl] at hult
    have hvalSm : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := by rw [hvalPos]; omega
    have henc : bufXs[0] <<< 1 ||| (1 : BitVec 64) = BitVec.ofInt 64 (2 * val + 1) := by
      rw [show (1 : BitVec 64) = 1#64 from rfl, bv64_ofInt_pos_enc hult, ← hvalPos]
    rw [henc]
    have hnotBig : ¬ (val < -2 ^ 62 ∨ 2 ^ 62 ≤ val) := by omega
    refine hQ (BitVec.ofInt 64 (2 * val + 1)) st objs m
      (preservesMeta_refl st) (le_refl _) hbd ?_
      (fun _ => rfl) (fun h => absurd h hnotBig) (sep_unpick2_4 hmTrim)
    change intRep (BitVec.ofInt 64 (2 * val + 1)) val objs
    unfold intRep; simp only [hvalSm.1, hvalSm.2, and_self, ↓reduceIte]
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hneg0 : neg = 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hvalPos : val = (bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hneg0, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have huge : ¬ bufXs[0].toNat < ((1 : BitVec 64) <<< 62).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 62).toNat = 2 ^ 62 from rfl] at huge
    exact hBoxed (by omega) (Or.inr (by rw [hvalPos]; omega))
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hnegNz : neg ≠ 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hvalNeg : val = -(bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hnegNz, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hule : bufXs[0].toNat ≤ ((1 : BitVec 64) <<< 62).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 62).toNat = 2 ^ 62 from rfl] at hule
    have hvalSm : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := by rw [hvalNeg]; omega
    have henc : ((0 : BitVec 64) - bufXs[0]) <<< 1 ||| (1 : BitVec 64) = BitVec.ofInt 64 (2 * val +
      1) := by
      rw [show (0 : BitVec 64) = 0#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
        bv64_ofInt_neg_enc hule, ← hvalNeg]
    rw [henc]
    have hnotBig : ¬ (val < -2 ^ 62 ∨ 2 ^ 62 ≤ val) := by omega
    refine hQ (BitVec.ofInt 64 (2 * val + 1)) st objs m
      (preservesMeta_refl st) (le_refl _) hbd ?_
      (fun _ => rfl) (fun h => absurd h hnotBig) (sep_unpick2_4 hmTrim)
    change intRep (BitVec.ofInt 64 (2 * val + 1)) val objs
    unfold intRep; simp only [hvalSm.1, hvalSm.2, and_self, ↓reduceIte]
  · have htn1bv : BitVec.ofNat 64 tn = 1#64 := by assumption
    have htn1 : tn = 1 := by
      have := congrArg BitVec.toNat htn1bv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at this; exact this
    have hnegNz : neg ≠ 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with
      | nil => simp at hnle; omega
      | cons b bs => rfl
    have hvalNeg : val = -(bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hnegNz, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hugt : ¬ bufXs[0].toNat ≤ ((1 : BitVec 64) <<< 62).toNat := by assumption
    rw [show ((1 : BitVec 64) <<< 62).toNat = 2 ^ 62 from rfl] at hugt
    exact hBoxed (by omega) (Or.inl (by rw [hvalNeg]; omega))
  · have htnNzBv : BitVec.ofNat 64 tn ≠ 0#64 := by assumption
    have htnNe1 : BitVec.ofNat 64 tn ≠ 1#64 := by assumption
    have htnPos : 0 < tn := Classical.byContradiction fun hle0 => by
      have h0 : tn = 0 := by omega
      apply htnNzBv; rw [h0]
    have htnGe2 : 2 ≤ tn := Classical.byContradiction fun hlt2 => by
      have h1 : tn = 1 := by omega
      apply htnNe1; rw [h1]
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    have htakeNe : bufXs.take tn ≠ [] := by intro h; rw [h, List.length_nil] at htakeLen; omega
    have hpow : 2 ^ 64 ≤ mag := by
      rw [hmagEq]
      have hge := limbsVal_ge_pow_of_nonzero_last htakeNe
        (by rw [getLast_eq_getLast! _ htakeNe]; exact hlastNe)
      rw [htakeLen] at hge
      have hpow1 : 2 ^ 64 ≤ 2 ^ (64 * (tn - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hbig : val < -2 ^ 62 ∨ 2 ^ 62 ≤ val := by
      dsimp [val]
      simp only [show tn ≠ 0 from by omega, ↓reduceIte]
      by_cases hn0 : neg = 0#64
      · right; simp [hn0]; omega
      · left; simp [hn0]; omega
    exact hBoxed htnPos hbig

theorem bn_cmp_fixed_wp :
    ∀ xs m Q X, bnCmpFixedSpec xs m Q X → Func.wp rtR1Env bn_cmp_fixed.body xs m Q X := by
  intro ⟨a, b, n, ⟨⟩⟩ m Q X ⟨aXs, bXs, R, hna, hnb, hm, hQ⟩
  dsimp only [Func.wp, bn_cmp_fixed, bn_cmp_fixed_body]
  change LeanQbe.T.wp _ _ _ _ _
  have hspec := cmpLimbsFixed_spec aXs bXs n.toNat hna hnb
  have hgoalEq : ∀ (r : Int),
      ((r = -1 ↔ limbsVal (aXs.take n.toNat) < limbsVal (bXs.take n.toNat)) ∧
       (r = 0 ↔ limbsVal (aXs.take n.toNat) = limbsVal (bXs.take n.toNat)) ∧
       (r = 1 ↔ limbsVal (bXs.take n.toNat) < limbsVal (aXs.take n.toNat))) →
      (r = -1 → -1#64 = cmpResult64 (limbsVal (aXs.take n.toNat)) (limbsVal (bXs.take n.toNat))) ∧
      (r = 1 → 1#64 = cmpResult64 (limbsVal (aXs.take n.toNat)) (limbsVal (bXs.take n.toNat))) ∧
      (r = 0 → 0#64 = cmpResult64 (limbsVal (aXs.take n.toNat)) (limbsVal (bXs.take n.toNat))) := by
    intro r ⟨hm1, hz, hp1⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hr; have hlt := hm1.mp hr; unfold cmpResult64; simp [hlt]
    · intro hr; have hgt := hp1.mp hr; unfold cmpResult64
      have hnlt : ¬ limbsVal (aXs.take n.toNat) < limbsVal (bXs.take n.toNat) := by omega
      simp [hnlt, hgt]
    · intro hr; have heq := hz.mp hr; unfold cmpResult64; simp [heq]
  have ⟨hresM1, hresP1, hres0⟩ := hgoalEq (cmpLimbsFixed aXs bXs n.toNat) hspec
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ k : Nat, k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
        cmpLimbsFixed aXs bXs k = cmpLimbsFixed aXs bXs n.toNat ∧ mL = m)
    (fun (xs : Tup Val [i64]) _ => xs.1.toNat)
    ?_ ?_
  · intro Js hJs
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    exact hJs (n, ()) m ⟨n.toNat, le_refl _, BitVec.eq_of_toNat_eq (by simp), rfl, rfl⟩
  · intro Js ⟨i, ⟨⟩⟩ mL ⟨k, hkLe, hkEq, hcmpEq, hmL⟩ hRec
    dsimp only at hkEq; subst hkEq hmL
    have hklt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hkLe n.isLt
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · have hkPos : 0 < k := by
        have hc : BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        exact hc
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxA : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < aXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hidxB : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < bXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hlt : aXs[k'] < bXs[k'] := by
        have hc : aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat := by assumption
        simp only [bv64_sub1_idx hklt64] at hc
        rw [BitVec.lt_def]; exact hc
      have hstep : cmpLimbsFixed aXs bXs (k' + 1) = -1 := by
        rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
        simp [hlt]
      rw [show (BitVec.signExtend 64 (-1 : BitVec 32) : BitVec 64) = -1#64 from rfl]
      rw [← hresM1 (by rw [← hcmpEq, hstep])] at hQ
      exact hQ
    · have hkPos : 0 < k := by
        have hc : BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        exact hc
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxA : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < aXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hidxB : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < bXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hnlt : ¬ aXs[k'] < bXs[k'] := by
        have hc : ¬ aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat := by assumption
        simp only [bv64_sub1_idx hklt64] at hc
        rw [BitVec.lt_def]; exact hc
      have hgt : bXs[k'] < aXs[k'] := by
        have hc : bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat := by assumption
        simp only [bv64_sub1_idx hklt64] at hc
        rw [BitVec.lt_def]; exact hc
      have hstep : cmpLimbsFixed aXs bXs (k' + 1) = 1 := by
        rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
        simp [hnlt, hgt]
      rw [← hresP1 (by rw [← hcmpEq, hstep])] at hQ
      exact hQ
    · have hkPos : 0 < k := by
        have hc : BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        exact hc
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxA : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < aXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hidxB : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < bXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hnlt : ¬ aXs[k'] < bXs[k'] := by
        have hc : ¬ aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat := by assumption
        simp only [bv64_sub1_idx hklt64] at hc
        rw [BitVec.lt_def]; exact hc
      have hngt : ¬ bXs[k'] < aXs[k'] := by
        have hc : ¬ bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat := by assumption
        simp only [bv64_sub1_idx hklt64] at hc
        rw [BitVec.lt_def]; exact hc
      have hstep : cmpLimbsFixed aXs bXs (k' + 1) = cmpLimbsFixed aXs bXs k' := by
        rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
        simp [hnlt, hngt]
      have hsub : BitVec.ofNat 64 (k' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k' := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt64];
              exact Nat.succ_le_succ (Nat.zero_le k'))]
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt64, Nat.mod_eq_of_lt
          (by omega)]
        simp
      have hmeas : (BitVec.ofNat 64 (k' + 1) - (1 : BitVec 64)).toNat < (BitVec.ofNat 64 (k' +
        1)).toNat := by
        rw [hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hklt64]
        omega
      exact hRec _ mL hmeas ⟨k', by omega, hsub, by rw [← hcmpEq, hstep], rfl⟩
    · have hk0 : k = 0 := by
        have hc : ¬ BitVec.toNat (0 : BitVec 64) < k % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hklt64, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
        omega
      subst hk0
      have hstep : cmpLimbsFixed aXs bXs 0 = 0 := cmpLimbsFixed.eq_1 aXs bXs
      rw [← hres0 (by rw [← hcmpEq, hstep])] at hQ
      exact hQ

theorem bn_cmp_wp :
    ∀ xs m Q X, bnCmpSpec xs m Q X → Func.wp rtR1Env bn_cmp.body xs m Q X := by
  intro ⟨a, na, b, nb, ⟨⟩⟩ m Q X ⟨aXs, bXs, R, hna, hnb, hm, hQ⟩
  dsimp only [Func.wp, bn_cmp, bn_cmp_body]
  change LeanQbe.T.wp _ _ _ _ _
  let ta := trimLenLoop aXs na.toNat
  let tb := trimLenLoop bXs nb.toNat
  have htaLe : ta ≤ na.toNat := trimLenLoop_le aXs na.toNat
  have htbLe : tb ≤ nb.toNat := trimLenLoop_le bXs nb.toNat
  have htaLt64 : ta < 2 ^ 64 := Nat.lt_of_le_of_lt htaLe na.isLt
  have htbLt64 : tb < 2 ^ 64 := Nat.lt_of_le_of_lt htbLe nb.isLt
  have hspec := cmpLimbs_spec aXs na.toNat bXs nb.toNat hna hnb
  have hcmpEq : cmpLimbs aXs na.toNat bXs nb.toNat =
      if ta < tb then -1 else if tb < ta then 1 else cmpLimbsFixed aXs bXs ta := cmpLimbs.eq_1 ..
  apply wp_call_of
  apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨aXs, (array64 b bXs ⋆ R), hna, sep_assoc_r hm, ?_⟩
  apply wp_call_of
  apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bXs, (array64 a aXs ⋆ R), hnb, sep_swap12 (sep_assoc_r hm), ?_⟩
  change LeanQbe.T.wp _ _ _ _ _
  c0_steps
  · have hlt : ta % 2 ^ 64 < tb % 2 ^ 64 := by assumption
    rw [Nat.mod_eq_of_lt htaLt64, Nat.mod_eq_of_lt htbLt64] at hlt
    have hm1 : cmpLimbs aXs na.toNat bXs nb.toNat = -1 := by rw [hcmpEq]; simp [hlt]
    have hltVal := hspec.1.mp hm1
    have hcEq : cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)) = -1#64 :=
      by
      unfold cmpResult64; simp [hltVal]
    rw [show (BitVec.signExtend 64 (-1 : BitVec 32) : BitVec 64) = -1#64 from rfl]
    rw [hcEq] at hQ
    exact hQ
  · have hgt : tb % 2 ^ 64 < ta % 2 ^ 64 := by assumption
    rw [Nat.mod_eq_of_lt htbLt64, Nat.mod_eq_of_lt htaLt64] at hgt
    have hnlt : ¬ ta < tb := by omega
    have hp1 : cmpLimbs aXs na.toNat bXs nb.toNat = 1 := by rw [hcmpEq]; simp [hnlt, hgt]
    have hgtVal := hspec.2.2.mp hp1
    have hcEq : cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)) = 1#64 :=
      by
      unfold cmpResult64
      have hnltV : ¬ limbsVal (aXs.take na.toNat) < limbsVal (bXs.take nb.toNat) := by omega
      simp [hnltV, hgtVal]
    rw [hcEq] at hQ
    exact hQ
  · have hnlt : ¬ ta % 2 ^ 64 < tb % 2 ^ 64 := by assumption
    have hngt : ¬ tb % 2 ^ 64 < ta % 2 ^ 64 := by assumption
    rw [Nat.mod_eq_of_lt htaLt64, Nat.mod_eq_of_lt htbLt64] at hnlt hngt
    have hteq : ta = tb := by omega
    apply wp_call_of
    apply rtR1Env_bn_cmp_fixed
    dsimp only [bnCmpFixedSpec, vals, Tup.map, Arg.val]
    refine ⟨aXs, bXs, R, ?_, ?_, sep_assoc_l (sep_swap12 (sep_swap12 (sep_assoc_r hm))), ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htaLt64]; exact le_trans htaLe hna
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htaLt64, hteq]; exact le_trans htbLe hnb
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htaLt64]
      have hvalA := (limbsVal_trimLenLoop aXs na.toNat hna).symm
      have hvalB := (limbsVal_trimLenLoop bXs nb.toNat hnb).symm
      rw [show limbsVal (aXs.take ta) = limbsVal (aXs.take na.toNat) from hvalA.symm,
        show limbsVal (bXs.take ta) =
          limbsVal (bXs.take nb.toNat) from by rw [hteq]; exact hvalB.symm]
      exact hQ

end LeanQbe.T.LeanLCNF
