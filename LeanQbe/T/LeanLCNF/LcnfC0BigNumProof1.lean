module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumSpec
import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
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

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
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

private theorem lcnf_nat_alloc_zero_wp
    {Q : Post [i64]} {X : XPost} (p : Val i64) (n' : Nat) (obj : LcnfObj)
    (limbs : List (BitVec 64)) (rt : Val i64) (st' : RtC0State) (R : Mem 64 → Prop)
    (m2 : Mem 64) (hn'lt : n' < 2 ^ 64) (hlen : limbs.length = n')
    (hobjAddr : obj.addr = p) (hobjTag : obj.tag = mpzTag)
    (hobjLimbs : obj.limbs = List.replicate n' 0#64)
    (hm2h : (cell64 (p + 8#64) obj.mpzMeta ⋆ (cell64 p obj.header ⋆
      (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) m2)
    (hQ : ∀ mL, (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) mL → Q (p, ()) mL) :
    wp rtR1Env Q X
      (Expr.group
        (fun (Js : Tup Cont [[i64]]) =>
          Blocks.cons
            (fun (p_11 : Tup Val [i64]) =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (by rfl),
                  args := (Arg.var p_11.fst, Arg.var (BitVec.ofNat 64 n'), ()) }
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
                          args := (Arg.var p, Arg.var p_14.fst, ()) }
                        fun (p_15 : Tup Val [i64]) =>
                        Expr.store (@Arg.imm Val i64 0#64) (Arg.var p_15.fst)
                          (Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var p_11.fst, Arg.imm 1, ()) }
                            fun (p_16 : Tup Val [i64]) =>
                            Expr.jump Js.fst (Arg.var p_16.fst, ())))
                  (Expr.ret (Arg.var p, ())))
            Blocks.nil)
        fun (Js : Tup Cont [[i64]]) =>
          Expr.jump Js.fst (@Arg.imm Val i64 0#64, ())) m2 := by
  refine wp_while_mut_cursor64 (tsRest := []) 0 n' limbs (fun (_ : Unit) => ())
    (fun i xs _ => xs = List.replicate i 0#64 ++ limbs.drop i)
    (fun _ xs _ => cell64 p obj.header ⋆ cell64 (p + 8#64) obj.mpzMeta ⋆
      array64 (p + 16#64) xs) (rtC0Inv rt st' ⋆ R) ?_ ?_
  · intro J hJ
    c0_hsteps
    exact hJ 0 limbs () _ (.init (Nat.zero_le _) (Nat.le_of_eq hlen.symm) rfl) (sep_ac hm2h)
  · intro J idx xs ⟨⟩ mL hinv hmL hRec
    have hlt64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt hinv.idx_le hn'lt
    c0_hsteps
    · have hiLt : idx < n' := by c0_bv_omega
      have hxsLen : (BitVec.ofNat 64 idx).toNat < xs.length := by
        rw [ArrayCursorInv.toNat_ofNat_lt hlt64]; exact hinv.idx_lt_length hiLt
      c0_hsteps
      rw [ArrayCursorInv.ofNat_add_one]
      refine hRec (idx + 1) _ () _ (by omega)
        (hinv.step_set hiLt 0#64 (by rw [hinv.inv, zeroPrefix_set (by omega)])) ?_
      try rw [ArrayCursorInv.toNat_ofNat_lt hlt64] at hm
      exact sep_ac hm
    · obtain ⟨rfl, _, _, rfl⟩ := hinv.done (by c0_bv_omega)
      rw [List.drop_of_length_le (Nat.le_of_eq hlen), List.append_nil] at hmL
      have hmL1 : (cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
          array64 (obj.addr + 16#64) obj.limbs ⋆ (rtC0Inv rt st' ⋆ R)) mL := by
        rw [hobjAddr, hobjLimbs]
        exact sep_ac hmL
      exact hQ mL (sep_ac (lcnfObjMem_mpz_intro hobjTag hmL1))

private theorem lcnf_nat_alloc_hdr_wp
    {Q : Post [i64]} {X : XPost} (p csVal : Val i64) (n' bytes : Nat) (obj : LcnfObj)
    (w0 w1 : BitVec 64) (limbs : List (BitVec 64)) (rt : Val i64) (st' : RtC0State)
    (R : Mem 64 → Prop) (mAlloc : Mem 64)
    (hn'lt : n' < 2 ^ 64) (hlen : limbs.length = n') (hobjAddr : obj.addr = p)
    (hobjHeader : obj.header = (((1 : BitVec 64) |||
        ((if bytes < 65536 then BitVec.ofNat 64 bytes else 0#64) <<< (32 : Nat))) |||
        ((250 : BitVec 64) <<< (56 : Nat))))
    (hobjMeta : obj.mpzMeta = (BitVec.ofNat 64 n' ||| (BitVec.ofNat 64 n' <<< (32 : Nat))))
    (hobjTag : obj.tag = mpzTag) (hobjLimbs : obj.limbs = List.replicate n' 0#64)
    (hcs : csVal = (if bytes < 65536 then BitVec.ofNat 64 bytes else 0#64))
    (hpParts : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆
      (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) mAlloc)
    (hQ : ∀ mL, (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) mL → Q (p, ()) mL) :
    wp rtR1Env Q X
      (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) }
        fun (p_1 : Tup Val [i64]) =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.shl i64,
            args := (Arg.var csVal, Arg.var p_1.fst, ()) } fun (p_2 : Tup Val [i64]) =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.or i64,
              args := (Arg.imm 1, Arg.var p_2.fst, ()) } fun (p_3 : Tup Val [i64]) =>
            Expr.let_
              { sig := [i32], code := OpCode.sext 32 64,
                args := (Arg.imm 56, ()) } fun (p_4 : Tup Val [i64]) =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.shl i64,
                  args := (Arg.imm 250, Arg.var p_4.fst, ()) } fun (p_5 : Tup Val [i64]) =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.or i64,
                    args := (Arg.var p_3.fst, Arg.var p_5.fst, ()) }
                  fun (p_6 : Tup Val [i64]) =>
                  Expr.store (Arg.var p_6.fst) (Arg.var p)
                    (Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p, Arg.imm 8, ()) } fun (p_7 : Tup Val [i64]) =>
                      Expr.let_
                        { sig := [i32], code := OpCode.sext 32 64,
                          args := (Arg.imm 32, ()) } fun (p_8 : Tup Val [i64]) =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.shl i64,
                            args := (Arg.var (BitVec.ofNat 64 n'),
                              Arg.var p_8.fst, ()) } fun (p_9 : Tup Val [i64]) =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.or i64,
                              args := (Arg.var (BitVec.ofNat 64 n'),
                                Arg.var p_9.fst, ()) } fun (p_10 : Tup Val [i64]) =>
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
                                            { sig := [i64, i64],
                                              code := OpCode.add i64,
                                              args := (Arg.imm 2, Arg.var p_11.fst, ()) }
                                            fun (p_13 : Tup Val [i64]) =>
                                            Expr.let_
                                              { sig := [i64, i64],
                                                code := OpCode.mul i64,
                                                args := (Arg.var p_13.fst, Arg.imm 8, ()) }
                                              fun (p_14 : Tup Val [i64]) =>
                                              Expr.let_
                                                { sig := [i64, i64],
                                                  code := OpCode.add i64,
                                                  args := (Arg.var p, Arg.var p_14.fst, ()) }
                                                fun (p_15 : Tup Val [i64]) =>
                                                Expr.store (@Arg.imm Val i64 0#64)
                                                  (Arg.var p_15.fst)
                                                  (Expr.let_
                                                    { sig := [i64, i64],
                                                      code := OpCode.add i64,
                                                      args := (Arg.var p_11.fst, Arg.imm 1, ()) }
                                                    fun (p_16 : Tup Val [i64]) =>
                                                    Expr.jump Js.fst (Arg.var p_16.fst, ())))
                                          (Expr.ret (Arg.var p, ())))
                                    Blocks.nil)
                                fun (Js : Tup Cont [[i64]]) =>
                                  Expr.jump Js.fst (@Arg.imm Val i64 0#64, ())))) mAlloc := by
  subst hcs
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine wp_store_sep (store_cell64 _ hpParts) fun m1 hm1 => ?_
  dsimp only [Arg.val] at hm1
  have hm1h : (cell64 p (((1 : BitVec 64) |||
      ((if bytes < 65536 then BitVec.ofNat 64 bytes else 0#64) <<< (32 : Nat))) |||
      ((250 : BitVec 64) <<< (56 : Nat))) ⋆ (cell64 (p + 8#64) w1 ⋆
      (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) m1 := hm1
  rw [← hobjHeader] at hm1h
  clear hpParts hm1
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  have hm1' : (cell64 (p + 8#64) w1 ⋆ (cell64 p obj.header ⋆
      (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) m1 := sep_ac hm1h
  refine wp_store_sep (store_cell64 _ hm1') fun m2 hm2 => ?_
  dsimp only [Arg.val] at hm2
  have hm2h : (cell64 (p + 8#64) (BitVec.ofNat 64 n' |||
      (BitVec.ofNat 64 n' <<< (32 : Nat))) ⋆ (cell64 p obj.header ⋆
      (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) m2 := hm2
  rw [← hobjMeta] at hm2h
  clear hm1' hm2
  exact lcnf_nat_alloc_zero_wp p n' obj limbs rt st' R m2 hn'lt hlen
    hobjAddr hobjTag hobjLimbs hm2h hQ

private theorem lcnf_nat_alloc_tail_wp
    {Q : Post [i64]} {X : XPost} (rt nlimbs csVal : Val i64) (st : RtC0State)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hmax : nlimbs.toNat ≤ mpzMaxLimbs) (hbd : st.Bounded48)
    (havail : st.hasFree (16 + 8 * max 1 nlimbs.toNat) ∨
      16 + 8 * max 1 nlimbs.toNat ≤ st.rem)
    (hm : (rtC0Inv rt st ⋆ R) m)
    (hcs : csVal = (if 16 + 8 * max 1 nlimbs.toNat < 65536 then
      BitVec.ofNat 64 (16 + 8 * max 1 nlimbs.toNat) else 0#64))
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : ExtHashMap (BitVec 64) UInt8),
      have obj :=
        { addr := p, rc := 1#32,
          csSz := if 16 + 8 * max 1 nlimbs.toNat < 65536 then
            16 + 8 * max 1 nlimbs.toNat else 0,
          other := 0, tag := mpzTag, cap := max 1 nlimbs.toNat, arrSize := max 1 nlimbs.toNat,
          limbs := List.replicate (max 1 nlimbs.toNat) 0#64 };
      obj.Wf → p &&& 1#64 = 0#64 → st'.PreservesMeta st → st'.rem ≤ st.rem →
        st'.Bounded48 → (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) m' → Q (p, ()) m') :
    wp rtR1Env Q X
      (Expr.call (V := Val) (L := Cont) (rs := [i64]) (as := [i64, i64]) (bs := [i64])
        "lcnf_alloc" (Arg.var rt, Arg.var (BitVec.ofNat 64 (16 + 8 * max 1 nlimbs.toNat)), ())
        fun (p : Tup Val [i64]) =>
        Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) }
          fun (p_1 : Tup Val [i64]) =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.shl i64,
              args := (Arg.var csVal, Arg.var p_1.fst, ()) } fun (p_2 : Tup Val [i64]) =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.or i64,
                args := (Arg.imm 1, Arg.var p_2.fst, ()) } fun (p_3 : Tup Val [i64]) =>
              Expr.let_
                { sig := [i32], code := OpCode.sext 32 64,
                  args := (Arg.imm 56, ()) } fun (p_4 : Tup Val [i64]) =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.shl i64,
                    args := (Arg.imm 250, Arg.var p_4.fst, ()) } fun (p_5 : Tup Val [i64]) =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.or i64,
                      args := (Arg.var p_3.fst, Arg.var p_5.fst, ()) }
                    fun (p_6 : Tup Val [i64]) =>
                    Expr.store (Arg.var p_6.fst) (Arg.var p.fst)
                      (Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p.fst, Arg.imm 8, ()) } fun (p_7 : Tup Val [i64]) =>
                        Expr.let_
                          { sig := [i32], code := OpCode.sext 32 64,
                            args := (Arg.imm 32, ()) } fun (p_8 : Tup Val [i64]) =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.shl i64,
                              args := (Arg.var (BitVec.ofNat 64 (max 1 nlimbs.toNat)),
                                Arg.var p_8.fst, ()) } fun (p_9 : Tup Val [i64]) =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.or i64,
                                args := (Arg.var (BitVec.ofNat 64 (max 1 nlimbs.toNat)),
                                  Arg.var p_9.fst, ()) } fun (p_10 : Tup Val [i64]) =>
                              Expr.store (Arg.var p_10.fst) (Arg.var p_7.fst)
                                (Expr.group
                                  (fun (Js : Tup Cont [[i64]]) =>
                                    Blocks.cons
                                      (fun (p_11 : Tup Val [i64]) =>
                                        Expr.let_
                                          { sig := [i64, i64],
                                            code := OpCode.cmp CmpOp.ult i64 Ty.bool (by rfl),
                                            args := (Arg.var p_11.fst,
                                              Arg.var (BitVec.ofNat 64 (max 1 nlimbs.toNat)), ()) }
                                          fun (p_12 : Tup Val [Ty.bool]) =>
                                          Expr.jnz (Arg.var p_12.fst)
                                            (Expr.let_
                                              { sig := [i64, i64],
                                                code := OpCode.add i64,
                                                args := (Arg.imm 2, Arg.var p_11.fst, ()) }
                                              fun (p_13 : Tup Val [i64]) =>
                                              Expr.let_
                                                { sig := [i64, i64],
                                                  code := OpCode.mul i64,
                                                  args := (Arg.var p_13.fst, Arg.imm 8, ()) }
                                                fun (p_14 : Tup Val [i64]) =>
                                                Expr.let_
                                                  { sig := [i64, i64],
                                                    code := OpCode.add i64,
                                                    args := (Arg.var p.fst, Arg.var p_14.fst, ()) }
                                                  fun (p_15 : Tup Val [i64]) =>
                                                  Expr.store (@Arg.imm Val i64 0#64)
                                                    (Arg.var p_15.fst)
                                                    (Expr.let_
                                                      { sig := [i64, i64],
                                                        code := OpCode.add i64,
                                                        args := (Arg.var p_11.fst, Arg.imm 1, ()) }
                                                      fun (p_16 : Tup Val [i64]) =>
                                                      Expr.jump Js.fst (Arg.var p_16.fst, ())))
                                            (Expr.ret (Arg.var p.fst, ())))
                                      Blocks.nil)
                                  fun (Js : Tup Cont [[i64]]) =>
                                    Expr.jump Js.fst (@Arg.imm Val i64 0#64, ())))) m := by
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  have hn1 : 1 ≤ n' := Nat.le_max_left 1 _
  have hnMax : n' ≤ mpzMaxLimbs := Nat.max_le.mpr ⟨by unfold mpzMaxLimbs; omega, hmax⟩
  have hn'lt : n' < 2 ^ 64 := by unfold mpzMaxLimbs at hnMax; omega
  have hbytesLo : rtMinObjBytes ≤ bytes := by unfold rtMinObjBytes; omega
  have hbytesMax : bytes < rtMaxObjBytes := by unfold mpzMaxLimbs rtMaxObjBytes at *; omega
  have hbytesEq : align8 (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnMax; omega),
      align8_of_mul8_add16]
  apply wp_call_of; apply rtR1Env_lcnf_alloc
  dsimp only [BigNumRt.lcnfAllocSpec, vals, Tup.map, Arg.val]
  refine ⟨st, R, ?_, by rw [hbytesEq]; exact hbytesLo, by rw [hbytesEq]; exact hbytesMax,
    by rw [hbytesEq]; exact havail, hm, ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold mpzMaxLimbs at hnMax; omega)]
    unfold mpzMaxLimbs at hnMax; omega
  · intro p st' mAlloc hpNz hpMod hpres hrem hmAlloc
    rw [hbytesEq] at hmAlloc
    dsimp only [bytes] at hmAlloc
    obtain ⟨w0, w1, limbs, hlen, hpParts⟩ :=
      region_to_mpz_parts (R := rtC0Inv rt st' ⋆ R) hn1 hnMax (sep_ac hmAlloc)
    let obj : LcnfObj :=
      { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
        tag := mpzTag, cap := n', arrSize := n', limbs := List.replicate n' 0#64 }
    have hobjWf : obj.Wf := by
      unfold mpzMaxLimbs rtMinObjBytes rtMaxObjBytes at *
      refine ⟨hpNz, hpMod, by dsimp [obj]; decide, ?_,
        by dsimp [obj]; decide, by dsimp [obj, mpzTag]; decide, ?_, ?_, ?_, ?_⟩
      · dsimp [obj]; split <;> omega
      · simp [obj, LcnfObj.totalBytes, mpzTag, arrayTag, sarrayTag, stringTag, rtMinObjBytes]
      · simp [obj, LcnfObj.totalBytes, mpzTag, arrayTag, sarrayTag, stringTag, rtMaxObjBytes]
        omega
      · simp [obj, LcnfObj.totalBytes, mpzTag, arrayTag, sarrayTag, stringTag]
      · simp [obj, mpzTag, closureTag, arrayTag, sarrayTag, stringTag, List.length_replicate]
        omega
    have hhdr : obj.header = (((1 : BitVec 64) |||
        ((if bytes < 65536 then BitVec.ofNat 64 bytes else 0#64) <<< (32 : Nat))) |||
        ((250 : BitVec 64) <<< (56 : Nat))) := by
      dsimp only [obj, LcnfObj.header, mpzTag]
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl,
        show (BitVec.ofNat 64 1 : BitVec 64) = (1 : BitVec 64) from rfl,
        show (BitVec.ofNat 64 0 <<< 48 : BitVec 64) = 0#64 from rfl, BitVec.or_zero,
        show (BitVec.ofNat 64 250 <<< 56 : BitVec 64) =
          ((250 : BitVec 64) <<< (56 : Nat)) from rfl]
      by_cases hb : bytes < 65536 <;> simp [hb]
    have hmeta : obj.mpzMeta = (BitVec.ofNat 64 n' |||
        (BitVec.ofNat 64 n' <<< (32 : Nat))) := rfl
    have hpParts' : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆
        (array64 (p + 16#64) limbs ⋆ (rtC0Inv rt st' ⋆ R)))) mAlloc := sep_ac hpParts
    exact lcnf_nat_alloc_hdr_wp p csVal n' bytes obj w0 w1 limbs rt st' R mAlloc
      hn'lt hlen rfl hhdr hmeta rfl rfl hcs hpParts'
      fun mL hmOut => hQ p st' mL hobjWf (bv64_and1_eq_zero_of_mod8 hpMod) hpres hrem
        (RtC0State.bounded48_of_preserves hbd hpres) hmOut

theorem lcnf_nat_alloc_wp :
    ∀ xs m Q X, lcnfNatAllocSpec xs m Q X → Func.wp rtR1Env lcnf_nat_alloc.body xs m Q X := by
  intro ⟨rt, nlimbs, ⟨⟩⟩ m Q X ⟨st, R, hmax, hbd, havail, hm, hQ⟩
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  have hnMax : n' ≤ mpzMaxLimbs := Nat.max_le.mpr ⟨by unfold mpzMaxLimbs; omega, hmax⟩
  have hbytesBv : (16 + 8 * BitVec.ofNat 64 n' : BitVec 64) = BitVec.ofNat 64 bytes := by
    apply BitVec.eq_of_toNat_eq; c0_bv_omega
  dsimp only [Func.wp, lcnf_nat_alloc, lcnf_nat_alloc_body]
  refine wp_join_group (fun (xs : Tup Val [i64]) m' => xs.1 = BitVec.ofNat 64 n' ∧ m' = m) ?_ ?_
  · intro J_n ⟨nCur, ⟨⟩⟩ m' ⟨hnCur, hm'⟩
    rw [hm']; subst hnCur
    c0_hsteps
    · exfalso; unfold mpzMaxLimbs at hnMax; c0_bv_omega
    · rw [hbytesBv]
      exact lcnf_nat_alloc_tail_wp rt nlimbs _ st R m hmax hbd havail hm
        (by
          have hb : 16 + 8 * max 1 nlimbs.toNat < 65536 := by
            change bytes < 65536; dsimp [bytes]; c0_bv_omega
          simp [hb]; rfl) hQ
    · rw [hbytesBv]
      exact lcnf_nat_alloc_tail_wp rt nlimbs 0#64 st R m hmax hbd havail hm
        (by
          have hnb : ¬(16 + 8 * max 1 nlimbs.toNat < 65536) := by
            change ¬bytes < 65536; dsimp [bytes]; c0_bv_omega
          simp [hnb]) hQ
  · intro J_n hJ_n
    c0_hsteps
    · refine hJ_n _ _ ⟨by simp [n', ‹nlimbs = 0#64›], rfl⟩
    · have hpos : 0 < nlimbs.toNat :=
        Nat.pos_of_ne_zero fun h => ‹nlimbs ≠ 0#64› (BitVec.eq_of_toNat_eq h)
      refine hJ_n _ _ ⟨by simp [n', Nat.max_eq_right hpos], rfl⟩

theorem bn_require_scratch_wp :
    ∀ xs m Q X, bnRequireScratchSpec xs m Q X →
      Func.wp rtR1Env bn_require_scratch.body xs m Q X := by
  intro ⟨rt, need, ⟨⟩⟩ m Q X ⟨scr, cap, R, hscr, hneed, hm, hQ⟩
  dsimp only [Func.wp, bn_require_scratch, bn_require_scratch_body]
  c0_hsteps; exact hQ

theorem bn_dec_nat_wp :
    ∀ xs m Q X, bnDecNatSpec xs m Q X → Func.wp rtR1Env bn_dec_nat.body xs m Q X := by
  intro ⟨rt, a, ⟨⟩⟩ m Q X hspec
  dsimp only [Func.wp, bn_dec_nat, bn_dec_nat_body]
  refine wp_join_group (fun (_ : Tup Val []) m' => Q () m')
    (fun _ _ _ h => by c0_hsteps; exact h) ?_
  intro J_ret hJ_ret
  dsimp only [bnDecNatSpec] at hspec
  split at hspec
  · c0_hsteps; exact hJ_ret () m hspec
  · rename_i hscalar
    have ha0 : (a &&& 1#64) = 0#64 := Classical.not_not.mp hscalar
    rcases hspec with ⟨st, objs, R, hcap, hm, ⟨obj0, hmem0, had0⟩, hwfAll, hclosed, hrcS, hQ⟩
    obtain ⟨idx, hidxLt, hidxEq⟩ := List.getElem_of_mem hmem0
    have hobjAddr : objs[idx].addr = a := hidxEq ▸ had0
    have hobjWf : objs[idx].Wf := hwfAll _ (List.getElem_mem hidxLt)
    have hmFocus : (cell64 a objs[idx].header ⋆ (lcnfObjMemTail objs[idx] ⋆ rtC0Inv rt st ⋆
        (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ R)) m := by
      rw [lcnfHeap_focus objs hidxLt, lcnfObjMem_eq_header_tail, hobjAddr] at hm
      exact sep_ac hm
    have hrc32 : objs[idx].header.setWidth 32 = objs[idx].rc := LcnfObj.header_setWidth32 _ hobjWf
    have hrcSext : ((objs[idx].header.setWidth 32).signExtend 64).toInt = objs[idx].rc.toInt :=
      hrc32 ▸ BitVec.toInt_signExtend_of_le (by decide)
    c0_hsteps
    · have hrcGt1 : 1 < objs[idx].rc.toInt := by
        have hc : (1#64).slt ((objs[idx].header.setWidth 32).signExtend 64) = true := by assumption
        rw [BitVec.slt, decide_eq_true_eq, hrcSext] at hc; exact hc
      have hmsb : objs[idx].rc.msb = false := by
        cases hm' : objs[idx].rc.msb
        · rfl
        · have hneg := BitVec.toInt_eq_msb_cond objs[idx].rc
          have := objs[idx].rc.isLt; simp [hm'] at hneg; omega
      have hsext : objs[idx].rc.signExtend 64 = objs[idx].rc.setWidth 64 :=
        BitVec.signExtend_eq_setWidth_of_msb_false hmsb
      have hrcLt : objs[idx].rc.toNat < 2 ^ 31 := by
        rw [BitVec.msb_eq_false_iff_two_mul_lt] at hmsb; omega
      have hrcGe2 : 2 ≤ objs[idx].rc.toNat := by
        have := BitVec.toInt_eq_toNat_of_lt (by omega : 2 * objs[idx].rc.toNat < 2 ^ 32); omega
      have hsub32 :
          (((objs[idx].header.setWidth 32).signExtend 64 - 1#64).setWidth 32).setWidth 64 =
            (BitVec.ofNat 32 (objs[idx].rc.toNat - 1)).setWidth 64 := by
        rw [hrc32, hsext]; congr 1; apply BitVec.eq_of_toNat_eq
        have hle1 : (1#64 : BitVec 64) ≤ objs[idx].rc.setWidth 64 := by
          rw [BitVec.le_def, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by omega : objs[idx].rc.toNat < 2 ^ 64)]
          exact Nat.le_trans (by decide : (1#64 : BitVec 64).toNat ≤ 2) hrcGe2
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle1, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : objs[idx].rc.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : objs[idx].rc.toNat - 1 < 2 ^ 32)]
      have hhdrEq := LcnfObj.header_dec_rc objs[idx] hobjWf hrcGt1
      refine wp_store_sep (store_cell64 _ hmFocus) fun m' hm' => ?_
      c0_hsteps
      dsimp only [Arg.val] at hm'
      rw [hsub32, show (18446744069414584320 : BitVec 64) = 18446744069414584320#64 from rfl,
        hhdrEq] at hm'
      apply hJ_ret () m'
      refine hQ st (objs.set idx (objs[idx].withRc (objs[idx].rc - 1#32))) m'
        (Or.inr (Or.inr (Or.inl ⟨ha0, idx, hidxLt, hobjAddr, hrcGt1, rfl, rfl⟩))) ?_
      rw [lcnfHeap_set objs hidxLt, lcnfObjMem_eq_header_tail,
        show lcnfObjMemTail (objs[idx].withRc (objs[idx].rc - 1#32)) =
          lcnfObjMemTail objs[idx] from rfl,
        show (objs[idx].withRc (objs[idx].rc - 1#32)).addr = a from hobjAddr]
      exact sep_ac hm'
    · have hrc1 : objs[idx].rc = 1#32 := BitVec.eq_of_toInt_eq <| by
        have h := congrArg BitVec.toInt (‹(objs[idx].header.setWidth 32).signExtend 64 = 1#64›)
        rwa [hrcSext] at h
      apply wp_call_of; apply rtR1Env_lcnf_dec_ref_cold
      refine ⟨ha0, st, objs, R, hcap, hm, ⟨objs[idx], List.getElem_mem hidxLt, hobjAddr, hrc1⟩,
        hwfAll, hclosed, hrcS _ (List.getElem_mem hidxLt) hobjAddr hrc1,
        fun st' objs' m' hp hr hc hm' => ?_⟩
      c0_hsteps
      exact hJ_ret () m' (hQ st' objs' m' (Or.inr (Or.inr (Or.inr ⟨ha0, hp, hr, hc⟩))) hm')
    · have hrc0 : objs[idx].rc = 0#32 := BitVec.eq_of_toInt_eq <| by
        have hnn := hobjWf.2.2.1
        have hle := ‹((1#64).slt ((objs[idx].header.setWidth 32).signExtend 64)) = false›
        have hne := ‹(objs[idx].header.setWidth 32).signExtend 64 ≠ 1#64›
        rw [BitVec.slt, decide_eq_false_iff_not, hrcSext] at hle
        have hne1 : objs[idx].rc.toInt ≠ 1 :=
          fun h => hne (BitVec.eq_of_toInt_eq (by simpa [hrcSext]))
        have : (1#64 : BitVec 64).toInt = 1 := rfl
        have : (0#32 : BitVec 32).toInt = 0 := rfl
        omega
      exact hJ_ret () m (hQ st objs m (Or.inr (Or.inl ⟨ha0, objs[idx], List.getElem_mem hidxLt,
        hobjAddr, hrc0, rfl, rfl⟩)) hm)

theorem bn_copy_wp :
    ∀ xs m Q X, bnCopySpec xs m Q X → Func.wp rtR1Env bn_copy.body xs m Q X := by
  intro ⟨dst, src, n, ⟨⟩⟩ m Q X ⟨dstXs, srcXs, R, hndst, hnsrc, hm, hQ⟩
  dsimp only [Func.wp, bn_copy, bn_copy_body]
  refine wp_while_mut_cursor64 0 n.toNat dstXs (fun (_ : Unit) => ())
    (fun i xs _ => xs = srcXs.take i ++ dstXs.drop i)
    (fun _ xs _ => array64 dst xs) (array64 src srcXs ⋆ R) ?_ ?_
  · intro Js hJs
    c0_hsteps
    exact hJs 0 dstXs () m (.init (Nat.zero_le _) hndst rfl) (sep_ac hm)
  · intro Js idx xs ⟨⟩ mL hinv hmL hRec
    have hlt64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt hinv.idx_le n.isLt
    c0_hsteps
    · have hiLt : idx < n.toNat := by c0_bv_omega
      have hsrc : (BitVec.ofNat 64 idx).toNat < srcXs.length := by
        rw [ArrayCursorInv.toNat_ofNat_lt hlt64]; omega
      have hdst : (BitVec.ofNat 64 idx).toNat < xs.length := by
        rw [ArrayCursorInv.toNat_ofNat_lt hlt64]; exact hinv.idx_lt_length hiLt
      c0_hsteps
      have hmS : (array64 dst (xs.set (BitVec.ofNat 64 idx).toNat
          srcXs[(BitVec.ofNat 64 idx).toNat]) ⋆ (array64 src srcXs ⋆ R)) _ := ‹_›
      simp only [ArrayCursorInv.toNat_ofNat_lt hlt64] at hmS
      rw [ArrayCursorInv.ofNat_add_one]
      exact hRec (idx + 1) _ () _ (by omega)
        (hinv.step_set hiLt srcXs[idx] (by rw [hinv.inv, replacePrefix_set (by omega) (by omega)]))
        hmS
    · obtain ⟨rfl, _, _, rfl⟩ := hinv.done (by c0_bv_omega)
      exact hQ mL (sep_ac hmL)

theorem bn_zero_wp :
    ∀ xs m Q X, bnZeroSpec xs m Q X → Func.wp rtR1Env bn_zero.body xs m Q X := by
  intro ⟨dst, n, ⟨⟩⟩ m Q X ⟨xsArr, R, hnle, hm, hQ⟩
  dsimp only [Func.wp, bn_zero, bn_zero_body]
  refine wp_while_mut_cursor64 0 n.toNat xsArr (fun (_ : Unit) => ())
    (fun i xs _ => xs = List.replicate i 0#64 ++ xsArr.drop i)
    (fun _ xs _ => array64 dst xs) R ?_ ?_
  · intro Js hJs
    c0_hsteps
    exact hJs 0 xsArr () m (.init (Nat.zero_le _) hnle rfl) (sep_ac hm)
  · intro Js idx xs ⟨⟩ mL hinv hmL hRec
    have hlt64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt hinv.idx_le n.isLt
    c0_hsteps
    · have hiLt : idx < n.toNat := by c0_bv_omega
      have hdst : (BitVec.ofNat 64 idx).toNat < xs.length := by
        rw [ArrayCursorInv.toNat_ofNat_lt hlt64]; exact hinv.idx_lt_length hiLt
      c0_hsteps
      have hmS : (array64 dst (xs.set (BitVec.ofNat 64 idx).toNat 0#64) ⋆ R) _ := ‹_›
      rw [ArrayCursorInv.toNat_ofNat_lt hlt64] at hmS
      rw [ArrayCursorInv.ofNat_add_one]
      exact hRec (idx + 1) _ () _ (by omega)
        (hinv.step_set hiLt 0#64 (by rw [hinv.inv, zeroPrefix_set (by omega)])) hmS
    · obtain ⟨rfl, _, _, rfl⟩ := hinv.done (by c0_bv_omega)
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
  refine wp_loop_break_group
    (fun (xs : Tup Val [i64]) m' =>
      xs.1 = BitVec.ofNat 64 (trimLenLoop xsArr n.toNat) ∧ m' = m)
    (fun k (xs : Tup Val [i64]) m' =>
      k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
        trimLenLoop xsArr k = trimLenLoop xsArr n.toNat ∧ m' = m)
    (fun _ ⟨_, ⟨⟩⟩ _ ⟨hres, hm'⟩ => by subst hres hm'; c0_hsteps; exact hQ) ?_
    (fun B L hB hL => by
      c0_hsteps
      exact hL n.toNat (n, ()) m ⟨Nat.le_refl _, BitVec.eq_of_toNat_eq (by simp), rfl, rfl⟩)
  intro B L k ⟨cur, ⟨⟩⟩ m' hB hL ⟨hkLe, hcur, htrim, hm'⟩
  subst hcur hm'
  have hklt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hkLe n.isLt
  c0_hsplit
  · have hkPos : 0 < k := by c0_bv_omega
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hidx : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 = k' :=
      bv64_sub1_idx hklt64
    have hsub1 : (BitVec.ofNat 64 (k' + 1) - 1#64).toNat = k' := by c0_bv_omega
    have hk'Lt : k' < xsArr.length := by omega
    have hsubLt : (BitVec.ofNat 64 (k' + 1) - 1#64).toNat < xsArr.length := by omega
    c0_hsteps
    · have hne0 : xsArr[k'] ≠ 0#64 := by simp only [hidx] at *; c0_bv_omega
      have hstep : trimLenLoop xsArr (k' + 1) = k' + 1 := by
        rw [trimLenLoop.eq_2]; simp [getElem!_pos xsArr k' hk'Lt, hne0]
      exact hB (BitVec.ofNat 64 (k' + 1), ()) m' ⟨by rw [← htrim, hstep], rfl⟩
    · have heq0 : xsArr[k'] = 0#64 := by simp only [hidx] at *; c0_bv_omega
      have hstep : trimLenLoop xsArr (k' + 1) = trimLenLoop xsArr k' := by
        rw [trimLenLoop.eq_2]; simp [getElem!_pos xsArr k' hk'Lt, heq0]
      have hsub : BitVec.ofNat 64 (k' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k' := by
        apply BitVec.eq_of_toNat_eq; c0_bv_omega
      rw [hsub]
      exact hL k' (BitVec.ofNat 64 k', ()) m' (by omega)
        ⟨by omega, rfl, by rw [← htrim, hstep], rfl⟩
  · have hk0 : k = 0 := by c0_bv_omega
    subst hk0
    c0_hsteps
    exact hB (0#64, ()) m' ⟨by rw [← htrim, trimLenLoop.eq_1], rfl⟩

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

theorem natRep_small_of_odd {a : BitVec 64} {val : Nat} {objs : List LcnfObj}
    (hrep : natRep a val objs) (ha : (a &&& 1#64) ≠ 0#64) :
    val < 2 ^ 63 ∧ a = BitVec.ofNat 64 (2 * val + 1) := by
  have hsm : val < 2 ^ 63 := Classical.byContradiction fun hge => by
    simp only [natRep, hge, ↓reduceIte] at hrep; exact ha hrep.1
  simp only [natRep, hsm, ↓reduceIte] at hrep
  exact ⟨hsm, hrep⟩

theorem natRep_big_of_even {a : BitVec 64} {val : Nat} {objs : List LcnfObj}
    (hrep : natRep a val objs) (ha : (a &&& 1#64) = 0#64) : ¬ val < 2 ^ 63 := by
  intro hsm; simp only [natRep, hsm, ↓reduceIte] at hrep; subst hrep
  exact absurd (natSmallEnc_and1 hsm) (by rw [ha]; decide)

theorem intRep_small_of_odd {a : BitVec 64} {val : Int} {objs : List LcnfObj}
    (hrep : intRep a val objs) (ha : (a &&& 1#64) ≠ 0#64) :
    (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) ∧ a = BitVec.ofInt 64 (2 * val + 1) := by
  have hsm : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := Classical.byContradiction fun hnb => by
    simp only [intRep, hnb, ↓reduceIte] at hrep; exact ha hrep.1
  simp only [intRep, hsm] at hrep
  exact ⟨hsm, hrep⟩

theorem intRep_big_of_even {a : BitVec 64} {val : Int} {objs : List LcnfObj}
    (hrep : intRep a val objs) (ha : (a &&& 1#64) = 0#64) :
    ¬ (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) := by
  intro hsm; simp only [intRep, hsm] at hrep; subst hrep
  exact absurd ha (by rw [(intSmallEnc_toInt hsm.1 hsm.2).1]; decide)

private theorem mpz_focus_meta {objs : List LcnfObj} {obj : LcnfObj} {a : BitVec 64} {mag : Nat}
    {R' : Mem 64 → Prop} {m : Mem 64}
    (hIn : obj ∈ objs) (haddr : obj.addr = a) (hwf : obj.Wf) (htag : obj.tag = mpzTag)
    (hsz : obj.limbs.length = obj.arrSize) (hpos : 0 < obj.arrSize)
    (htrim : obj.limbs.getLast! ≠ 0#64) (hval : limbsVal obj.limbs = mag)
    (hm : (lcnfHeap objs ⋆ R') m) :
    ∃ idx, ∃ hlt : idx < objs.length, objs[idx] = obj ∧
      limbLenNat mag = obj.arrSize ∧ obj.arrSize < 2 ^ 64 ∧
      obj.mpzMeta >>> 32#64 = BitVec.ofNat 64 obj.arrSize ∧
      (cell64 (a + 8#64) obj.mpzMeta ⋆ cell64 a obj.header ⋆ array64 (a + 16#64) obj.limbs ⋆
        ((lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ R')) m := by
  obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn htag hm
  rw [haddr] at hmObj
  have hbounds := mpz_wf_bounds hwf htag
  have hne : obj.limbs ≠ [] := by intro he; rw [he, List.length_nil] at hsz; omega
  have hlen : limbLenNat mag = obj.arrSize := by
    rw [← hval, ← hsz]; exact limbLenNat_eq_length_of_trimmed hne htrim
  exact ⟨idx, hlt, heq, hlen, by omega,
    LcnfObj.mpzMeta_arrSize obj hbounds.1 hbounds.2, sep_ac hmObj⟩

private theorem bn_load_mpz_copy_wp {Q : Post [i64]} {X : XPost}
    {a dst : BitVec 64} {mag : Nat} {objs : List LcnfObj} {dstXs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (tail : Val i64 → Expr Val Cont [i64]) (obj : LcnfObj)
    (hIn : obj ∈ objs) (haddr : obj.addr = a) (hwf : obj.Wf) (htag : obj.tag = mpzTag)
    (hsz : obj.limbs.length = obj.arrSize) (hpos : 0 < obj.arrSize)
    (htrim : obj.limbs.getLast! ≠ 0#64) (hval : limbsVal obj.limbs = mag)
    (hlenDst : limbLenNat mag ≤ dstXs.length)
    (hm : (lcnfHeap objs ⋆ array64 dst dstXs ⋆ R) m)
    (hQ : ∀ (dstXs' : List (BitVec 64)) (m' : Mem 64),
      dstXs'.length = dstXs.length → limbsVal (dstXs'.take (limbLenNat mag)) = mag →
      dstXs'.drop (limbLenNat mag) = dstXs.drop (limbLenNat mag) →
      (lcnfHeap objs ⋆ array64 dst dstXs' ⋆ R) m' →
      wp rtR1Env Q X (tail (BitVec.ofNat 64 (limbLenNat mag))) m') :
    wp rtR1Env Q X
      (Expr.load i64 (Arg.var (a + 8#64)) fun (p_4 : Val i64) =>
        Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) }
          fun (p_5 : Tup Val [i64]) =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.lshr i64,
              args := (Arg.var p_4, Arg.var p_5.fst, ()) }
            fun (p_6 : Tup Val [i64]) =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var a, Arg.imm 16, ()) }
              fun (p_7 : Tup Val [i64]) =>
              Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
                (Arg.var dst, Arg.var p_7.fst, Arg.var p_6.fst, ()) fun (_ : Tup Val []) =>
                tail p_6.fst) m := by
  obtain ⟨idx, hlt, heq, hlen, harrLt64, hmeta, hmFocus⟩ :=
    mpz_focus_meta hIn haddr hwf htag hsz hpos htrim hval (sep_assoc_r hm)
  have harrToNat : (BitVec.ofNat 64 obj.arrSize).toNat = obj.arrSize := by c0_bv_omega
  c0_hsteps_nogrp
  rw [show obj.mpzMeta >>> 32 = obj.mpzMeta >>> 32#64 from rfl, hmeta]
  apply wp_call_of; apply rtR1Env_bn_copy
  dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
  rw [show (a + 16 : BitVec 64) = a + 16#64 from rfl]
  refine ⟨dstXs, obj.limbs, cell64 a obj.header ⋆ cell64 (a + 8#64) obj.mpzMeta ⋆
      ((lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆ R),
    harrToNat.symm ▸ hlen ▸ hlenDst, harrToNat.symm ▸ Nat.le_of_eq hsz.symm,
    sep_ac hmFocus, fun m' hmCopy => ?_⟩
  rw [harrToNat] at hmCopy
  let dstXs' := obj.limbs.take obj.arrSize ++ dstXs.drop obj.arrSize
  have hdstEq : dstXs' = obj.limbs ++ dstXs.drop obj.arrSize := by
    dsimp [dstXs']; rw [← hsz, List.take_length]
  have hmBack : (cell64 obj.addr obj.header ⋆ cell64 (obj.addr + 8#64) obj.mpzMeta ⋆
      array64 (obj.addr + 16#64) obj.limbs ⋆
      ((lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆
        (array64 dst dstXs' ⋆ R))) m' := by
    rw [haddr]; exact sep_ac hmCopy
  have hmHeap := sep_assoc_l (lcnfHeap_mpz_restore hlt heq htag hmBack)
  have hlen' : dstXs'.length = dstXs.length := by
    rw [hdstEq, List.length_append, List.length_drop, hsz]; omega
  rw [← hlen]
  exact hQ dstXs' m' hlen' (by rw [hdstEq, hlen, ← hsz, List.take_left, hval])
    (by rw [hdstEq, hlen, ← hsz, List.drop_left]) hmHeap

theorem bn_nat_len_wp :
    ∀ xs m Q X, bnNatLenSpec xs m Q X → Func.wp rtR1Env bn_nat_len.body xs m Q X := by
  intro ⟨a, ⟨⟩⟩ m Q X ⟨val, objs, R, hrep, hm, hQ⟩
  dsimp only [Func.wp, bn_nat_len, bn_nat_len_body]
  c0_hsteps
  · obtain ⟨hsm, hrep⟩ := natRep_small_of_odd hrep ‹_›
    subst hrep; rw [natSmallEnc_ushiftRight1 hsm] at *
    have : val = 0 := by c0_bv_omega
    subst this; rwa [limbLenNat_zero] at hQ
  · obtain ⟨hsm, hrep⟩ := natRep_small_of_odd hrep ‹_›
    subst hrep; rw [natSmallEnc_ushiftRight1 hsm] at *
    have hvpos : 0 < val := by c0_bv_omega
    rwa [limbLenNat_eq_one hvpos (by omega : val < 2 ^ 64)] at hQ
  · have hnsm := natRep_big_of_even hrep ‹_›
    simp only [natRep, hnsm, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    obtain ⟨idx, hlt, heq, hlen, _, hmeta, hmFocus⟩ :=
      mpz_focus_meta hIn haddr hcanon.1 hcanon.2.1 hcanon.2.2.2.1.symm
        (by rw [hcanon.2.2.2.1]; exact hcanon.2.2.2.2.1)
        hcanon.2.2.2.2.2.2.1 hcanon.2.2.2.2.2.2.2.1 hm
    c0_hsteps
    rw [show obj.mpzMeta >>> 32 = obj.mpzMeta >>> 32#64 from rfl, hmeta, ← hlen]
    exact hQ

theorem bn_int_len_wp :
    ∀ xs m Q X, bnIntLenSpec xs m Q X → Func.wp rtR1Env bn_int_len.body xs m Q X := by
  intro ⟨a, ⟨⟩⟩ m Q X ⟨val, objs, R, hrep, hm, hQ⟩
  dsimp only [Func.wp, bn_int_len, bn_int_len_body]
  c0_hsteps
  · obtain ⟨hsm, hrep⟩ := intRep_small_of_odd hrep ‹_›
    subst hrep
    have hz := ‹(BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 = 0#64›
    have hval0 : val = 0 := by rw [← (intSmallEnc_toInt hsm.1 hsm.2).2, hz]; rfl
    subst hval0; rwa [Int.natAbs_zero, limbLenNat_zero] at hQ
  · obtain ⟨hsm, hrep⟩ := intRep_small_of_odd hrep ‹_›
    subst hrep
    have hne := ‹(BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 ≠ 0#64›
    have hnz : val ≠ 0 := fun hv => by
      subst hv; exact hne (intSmallEnc_sshiftRight1 hsm.1 hsm.2).2
    rwa [limbLenNat_eq_one (Int.natAbs_pos.mpr hnz) (by omega : val.natAbs < 2 ^ 64)] at hQ
  · have hnbig := intRep_big_of_even hrep ‹_›
    simp only [intRep, hnbig, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    obtain ⟨idx, hlt, heq, hlen, _, hmeta, hmFocus⟩ :=
      mpz_focus_meta hIn haddr hcanon.1 hcanon.2.1 hcanon.2.2.2.1.symm
        (by rw [hcanon.2.2.2.1]; exact hcanon.2.2.2.2.1)
        hcanon.2.2.2.2.2.2.1 hcanon.2.2.2.2.2.2.2.1 hm
    c0_hsteps
    rw [show obj.mpzMeta >>> 32 = obj.mpzMeta >>> 32#64 from rfl, hmeta, ← hlen]
    exact hQ

theorem bn_load_nat_wp :
    ∀ xs m Q X, bnLoadNatSpec xs m Q X → Func.wp rtR1Env bn_load_nat.body xs m Q X := by
  intro ⟨a, dst, ⟨⟩⟩ m Q X ⟨val, objs, dstXs, R, hrep, hlenDst, hm, hQ⟩
  dsimp only [Func.wp, bn_load_nat, bn_load_nat_body]
  c0_hsteps
  · obtain ⟨hsm, hrep⟩ := natRep_small_of_odd hrep ‹_›
    subst hrep; rw [natSmallEnc_ushiftRight1 hsm] at *
    have : val = 0 := by c0_bv_omega
    subst this; rw [limbLenNat_zero] at hQ
    exact hQ dstXs m rfl rfl rfl hm
  · obtain ⟨hsm, hrep⟩ := natRep_small_of_odd hrep ‹_›
    subst hrep; rw [natSmallEnc_ushiftRight1 hsm] at *
    have hvpos : 0 < val := by c0_bv_omega
    have hlen1 := limbLenNat_eq_one hvpos (by omega : val < 2 ^ 64)
    have hdstPos : 0 < dstXs.length := Nat.lt_of_lt_of_le (by rw [hlen1]; decide) hlenDst
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    c0_hsteps
    rw [hlen1] at hQ
    refine hQ (dstXs.set 0 (BitVec.ofNat 64 val)) _ (List.length_set ..) ?_
      (List.drop_set_of_lt (by decide)) (sep_unpick2_3 ‹_›)
    cases dstXs with
    | nil => simp at hdstPos
    | cons d ds => simp [limbsVal_cons, limbsVal_nil]
  · have hnsm := natRep_big_of_even hrep ‹_›
    simp only [natRep, hnsm, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    refine bn_load_mpz_copy_wp (fun p => Expr.ret (Arg.var p, ()))
      obj hIn haddr hcanon.1 hcanon.2.1 hcanon.2.2.2.1.symm
      (by rw [hcanon.2.2.2.1]; exact hcanon.2.2.2.2.1)
      hcanon.2.2.2.2.2.2.1 hcanon.2.2.2.2.2.2.2.1 hlenDst hm
      fun dstXs' m' hlen' hval' hdrop' hm' => ?_
    c0_hsteps
    exact hQ dstXs' m' hlen' hval' hdrop' hm'

theorem bn_load_int_wp :
    ∀ xs m Q X, bnLoadIntSpec xs m Q X → Func.wp rtR1Env bn_load_int.body xs m Q X := by
  intro ⟨a, dst, ⟨⟩⟩ m Q X ⟨val, objs, dstXs, R, hrep, hlenDst, hm, hQ⟩
  dsimp only [Func.wp, bn_load_int, bn_load_int_body]
  c0_hsteps
  · obtain ⟨hsm, hrep⟩ := intRep_small_of_odd hrep ‹_›
    subst hrep
    have hz := ‹(BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 = 0#64›
    have hval0 : val = 0 := by rw [← (intSmallEnc_toInt hsm.1 hsm.2).2, hz]; rfl
    subst hval0
    have hinfo0 : BitVec.ofNat 64 (limbLenNat (0 : Int).natAbs) <<< 1 |||
        (if (0 : Int) < 0 then 1#64 else 0#64) = 0#64 := by decide
    rw [hinfo0, Int.natAbs_zero, limbLenNat_zero] at hQ
    exact hQ dstXs m rfl rfl rfl hm
  · obtain ⟨hsm, hrep⟩ := intRep_small_of_odd hrep ‹_›
    subst hrep
    have ⟨_, hshr⟩ := intSmallEnc_sshiftRight1 hsm.1 hsm.2
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsm.1 hsm.2
    have hsgt := ‹(0#64 : BitVec 64).slt ((BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1) = true›
    rw [BitVec.slt, decide_eq_true_eq, htoInt, show (0#64 : BitVec 64).toInt = 0 from rfl] at hsgt
    have hlen1 := limbLenNat_eq_one (by omega : 0 < val.natAbs) (by omega)
    have hdstPos : 0 < dstXs.length := Nat.lt_of_lt_of_le (by rw [hlen1]; decide) hlenDst
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    c0_hsteps
    rw [hlen1, show BitVec.ofNat 64 1 <<< 1 ||| (if val < 0 then 1#64 else 0#64) = 2#64 by
      simp [show ¬val < 0 by omega]] at hQ
    have hmRaw := ‹(array64 dst (dstXs.set (BitVec.toNat 0)
        ((BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1)) ⋆
        (BigNumRt.lcnfHeap objs ⋆ R)) _›
    rw [hshr] at hmRaw
    refine hQ (dstXs.set 0 (BitVec.ofInt 64 val)) _ (List.length_set ..) ?_
      (List.drop_set_of_lt (by decide)) (sep_unpick2_3 hmRaw)
    cases dstXs with
    | nil => simp at hdstPos
    | cons d ds => simp [limbsVal_cons, limbsVal_nil, BitVec.toNat_ofInt]; omega
  · obtain ⟨hsm, hrep⟩ := intRep_small_of_odd hrep ‹_›
    subst hrep
    have ⟨_, hshr⟩ := intSmallEnc_sshiftRight1 hsm.1 hsm.2
    have ⟨_, htoInt⟩ := intSmallEnc_toInt hsm.1 hsm.2
    have hne0 := ‹(BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 ≠ 0#64›
    have hvalNeg : val < 0 := by
      have hnlt :=
        ‹(0#64 : BitVec 64).slt ((BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1) = false›
      rw [BitVec.slt, decide_eq_false_iff_not, htoInt,
        show (0#64 : BitVec 64).toInt = 0 from rfl] at hnlt
      exact Classical.byContradiction fun hge0 =>
        hne0 (by rw [hshr, show val = 0 by omega]; rfl)
    have hlen1 := limbLenNat_eq_one (by omega : 0 < val.natAbs) (by omega)
    have hdstPos : 0 < dstXs.length := Nat.lt_of_lt_of_le (by rw [hlen1]; decide) hlenDst
    have hmDst : (array64 dst dstXs ⋆ (BigNumRt.lcnfHeap objs ⋆ R)) m := sep_pick2_3 hm
    c0_hsteps
    have hnegEq : (0#64 - (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1) =
        BitVec.ofNat 64 val.natAbs := by
      rw [hshr]; apply BitVec.eq_of_toNat_eq
      have hv0 : (0#64 : BitVec 64).toNat = 0 := rfl
      have hvi : (BitVec.ofInt 64 val).toNat = 2 ^ 64 - val.natAbs := by
        rw [BitVec.toNat_ofInt]; omega
      have hva : (BitVec.ofNat 64 val.natAbs).toNat = val.natAbs :=
        Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_sub, hv0, hvi, hva]; omega
    rw [hlen1, show BitVec.ofNat 64 1 <<< 1 ||| (if val < 0 then 1#64 else 0#64) = 3#64 by
      simp [hvalNeg]] at hQ
    have hmRaw := ‹(array64 dst (dstXs.set (BitVec.toNat 0)
        (0 - (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1)) ⋆
        (BigNumRt.lcnfHeap objs ⋆ R)) _›
    rw [show (0 : BitVec 64) - (BitVec.ofInt 64 (2 * val + 1)).sshiftRight 1 =
        BitVec.ofNat 64 val.natAbs from hnegEq] at hmRaw
    refine hQ (dstXs.set 0 (BitVec.ofNat 64 val.natAbs)) _ (List.length_set ..) ?_
      (List.drop_set_of_lt (by decide)) (sep_unpick2_3 hmRaw)
    cases dstXs with
    | nil => simp at hdstPos
    | cons d ds =>
      simp [limbsVal_cons, limbsVal_nil]
  · have hnbig := intRep_big_of_even hrep ‹_›
    simp only [intRep, hnbig, ↓reduceIte] at hrep
    rcases hrep with ⟨_, obj, hIn, haddr, hcanon⟩
    have hm1 : (BigNumRt.lcnfHeap objs ⋆ (array64 dst dstXs ⋆ R)) m := sep_assoc_r hm
    obtain ⟨idx, hlt, heq, hmObj⟩ := lcnfHeap_mpz_focus hIn hcanon.2.1 hm1
    rw [haddr] at hmObj
    have hmHdr := sep_assoc_r (sep_assoc_r hmObj)
    have hne : obj.limbs ≠ [] := by
      intro he; have := hcanon.2.2.2.2.1; rw [he, List.length_nil] at this; omega
    have hlen : limbLenNat val.natAbs = obj.arrSize := by
      rw [← hcanon.2.2.2.2.2.2.2.1, hcanon.2.2.2.1]
      exact limbLenNat_eq_length_of_trimmed hne hcanon.2.2.2.2.2.2.1
    rw [wp_load]; refine ⟨obj.header, loadVal_cell64 hmHdr, ?_⟩
    refine wp_join_group (fun (xs : Tup Val [i64]) m' =>
        xs.1 = (if val < 0 then 1#64 else 0#64) ∧ m' = m) ?_ ?_
    · intro J ⟨negBit, ⟨⟩⟩ m' ⟨hneg, hm'⟩; subst hneg hm'; simp only [Blocks.get]
      c0_hstep
      refine bn_load_mpz_copy_wp
        (fun p => Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
          fun p_3 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.shl i64,
              args := (Arg.var p, Arg.var p_3.1, ()) }
            fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.or i64,
                args := (Arg.var p.1, Arg.var (if val < 0 then 1#64 else 0#64), ()) }
              fun p => Expr.ret (Arg.var p.1, ()))
        obj hIn haddr hcanon.1 hcanon.2.1 hcanon.2.2.2.1.symm
        (by rw [hcanon.2.2.2.1]; exact hcanon.2.2.2.2.1)
        hcanon.2.2.2.2.2.2.1 hcanon.2.2.2.2.2.2.2.1 hlenDst hm
        fun dstXs' m' hlen' hval' hdrop' hm' => ?_
      c0_hsteps
      exact hQ dstXs' m' hlen' hval' hdrop' hm'
    · intro J hJ
      c0_hsteps
      · have hne0 : (obj.header >>> 48) &&& 255#64 ≠ 0#64 := by assumption
        rw [show (obj.header >>> 48 : BitVec 64) = obj.header >>> 48#64 from rfl,
          LcnfObj.header_other_byte obj hcanon.1] at hne0
        have hoth1 : obj.other = 1 := by
          rcases hcanon.2.2.1 with h0 | h1
          · rw [h0] at hne0; exact absurd rfl hne0
          · exact h1
        exact hJ (1#64, ()) m ⟨by simp [hcanon.2.2.2.2.2.2.2.2.1.mp hoth1], rfl⟩
      · have heq0 : (obj.header >>> 48) &&& 255#64 = 0#64 := by assumption
        rw [show (obj.header >>> 48 : BitVec 64) = obj.header >>> 48#64 from rfl,
          LcnfObj.header_other_byte obj hcanon.1] at heq0
        have hoth0 : obj.other = 0 := by
          rcases hcanon.2.2.1 with h0 | h1
          · exact h0
          · rw [h1] at heq0; exact absurd heq0 (by decide)
        have hnotNeg : ¬ val < 0 := fun hv => by
          have := hcanon.2.2.2.2.2.2.2.2.1.mpr hv; omega
        exact hJ (0#64, ()) m ⟨by simp [hnotNeg], rfl⟩

private theorem limbsVal_take_ge_pow64 {bufXs : List (BitVec 64)} {n tn : Nat}
    (hnle : n ≤ bufXs.length) (htn : tn = trimLenLoop bufXs n) (hge2 : 2 ≤ tn) :
    2 ^ 64 ≤ limbsVal (bufXs.take tn) := by
  have htnLe : tn ≤ n := htn ▸ trimLenLoop_le bufXs n
  have hlastNe := getLast_take_ne_zero bufXs n (by omega) hnle
  have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
  have htakeNe : bufXs.take tn ≠ [] := by intro h; rw [h, List.length_nil] at htakeLen; omega
  have hge := limbsVal_ge_pow_of_nonzero_last htakeNe
    (by rw [getLast_eq_getLast! _ htakeNe, htn]; exact hlastNe)
  have hpow1 : 2 ^ 64 ≤ 2 ^ (64 * (tn - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [htakeLen] at hge; omega

private theorem bn_from_limbs_copy_ret {Q : Post [i64]} {X : XPost}
    {rt buf : BitVec 64} {st' : RtC0State} {bufXs : List (BitVec 64)}
    {objs : List LcnfObj} {R : Mem 64 → Prop} {m1 : Mem 64}
    (newObj1 : LcnfObj) (n tn : Nat)
    (htag : newObj1.tag = mpzTag) (hcap : newObj1.cap = tn) (harr : newObj1.arrSize = tn)
    (hlimbs : newObj1.limbs = List.replicate tn 0#64) (hwf1 : newObj1.Wf)
    (htnLt64 : tn < 2 ^ 64) (htnLe : tn ≤ n) (hnle : n ≤ bufXs.length)
    (hm1 : (lcnfObjMem newObj1 ⋆ (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) m1)
    (hPost : ∀ mCopy,
      let newObj : LcnfObj := { newObj1 with limbs := bufXs.take tn }
      newObj.Wf →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap (newObj :: objs) ⋆ R) mCopy →
      Q (newObj1.addr, ()) mCopy) :
    wp rtR1Env Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var newObj1.addr, Arg.imm 16#64, ()) }
        fun (p_1 : Tup Val [i64]) =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
          (Arg.var p_1.1, Arg.var buf, @Arg.var Val i64 (BitVec.ofNat 64 tn), ())
          fun (_ : Tup Val []) => Expr.ret (Arg.var newObj1.addr, ())) m1 := by
  have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
  have hmIn : (array64 (newObj1.addr + 16#64) newObj1.limbs ⋆ array64 buf bufXs ⋆
      (cell64 (newObj1.addr + 8#64) newObj1.mpzMeta ⋆ cell64 newObj1.addr newObj1.header ⋆
        (rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R))) m1 := sep_ac (lcnfObjMem_mpz_elim htag hm1)
  c0_hsteps_nogrp
  apply wp_call_of; apply rtR1Env_bn_copy
  dsimp only [bnCopySpec, vals, Tup.map, Arg.val]
  refine ⟨newObj1.limbs, bufXs, cell64 (newObj1.addr + 8#64) newObj1.mpzMeta ⋆
      cell64 newObj1.addr newObj1.header ⋆ (rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R),
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, hlimbs, List.length_replicate]
       exact Nat.le_refl _,
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; omega, hmIn, fun mCopy hmCopyOut => ?_⟩
  c0_hsteps
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64] at hmCopyOut
  have hdrop0 : newObj1.limbs.drop tn = [] := by
    rw [hlimbs, List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_refl _)]
  rw [hdrop0, List.append_nil] at hmCopyOut
  let newObj : LcnfObj := { newObj1 with limbs := bufXs.take tn }
  have hnewWf : newObj.Wf :=
    mpz_wf_of_limbs hwf1 htag htag rfl rfl rfl hwf1.2.2.2.2.1 rfl rfl
      (by dsimp [newObj]; rw [htakeLen, hcap])
  have hmMem : (cell64 newObj.addr newObj.header ⋆ cell64 (newObj.addr + 8#64) newObj.mpzMeta ⋆
      array64 (newObj.addr + 16#64) newObj.limbs ⋆
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) mCopy := sep_ac hmCopyOut
  have hmPacked : (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap (newObj :: objs) ⋆ R) mCopy := by
    rw [lcnfHeap_cons_eq]
    exact sep_ac (lcnfObjMem_mpz_intro (o := newObj) htag hmMem)
  exact hPost mCopy hnewWf hmPacked

theorem bn_nat_from_limbs_wp :
    ∀ xs m Q X, bnNatFromLimbsSpec xs m Q X → Func.wp rtR1Env bn_nat_from_limbs.body xs m Q X := by
  intro ⟨rt, buf, n, ⟨⟩⟩ m Q X ⟨st, bufXs, objs, R, hnle, hnMax, hbd, havail, hm, hQ⟩
  dsimp only [Func.wp, bn_nat_from_limbs, bn_nat_from_limbs_body]
  let tn := trimLenLoop bufXs n.toNat
  let val := limbsVal (bufXs.take n.toNat)
  have htnLe : tn ≤ n.toNat := trimLenLoop_le bufXs n.toNat
  have htnMax : tn ≤ mpzMaxLimbs := le_trans htnLe hnMax
  have htnLt64 : tn < 2 ^ 64 := by unfold mpzMaxLimbs at htnMax; omega
  have hvalEq : val = limbsVal (bufXs.take tn) := (limbsVal_trimLenLoop bufXs n.toNat hnle).symm
  have hmTrim : (array64 buf bufXs ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_pick2_4 hm
  have hBoxed : ∀ (htnPos : 0 < tn), 2 ^ 63 ≤ val →
      wp rtR1Env Q X
        (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc"
          (Arg.var rt, @Arg.var Val i64 (BitVec.ofNat 64 tn), ()) fun (p : Tup Val [i64]) =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var p.1, Arg.imm 16#64, ()) }
            fun (p_1 : Tup Val [i64]) =>
            Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
              (Arg.var p_1.1, Arg.var buf, @Arg.var Val i64 (BitVec.ofNat 64 tn), ())
              fun (_ : Tup Val []) => Expr.ret (Arg.var p.1, ())) m := by
    intro htnPos hbig
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    apply wp_call_of; apply rtR1Env_lcnf_nat_alloc
    dsimp only [lcnfNatAllocSpec, vals, Tup.map, Arg.val]
    refine ⟨st, array64 buf bufXs ⋆ lcnfHeap objs ⋆ R,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; exact htnMax, hbd,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos]
         exact havail hbig,
      sep_pick1_4 (sep_unpick2_4 hmTrim),
      fun p st' mAlloc hwf0 hand0 hpres0 hrem0 hbd0 hmObj0 => ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos] at hwf0 hmObj0
    let bytes := 16 + 8 * tn
    let newObj0 : LcnfObj :=
      { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
        tag := mpzTag, cap := tn, arrSize := tn, limbs := List.replicate tn 0#64 }
    have hmObj0' : (lcnfObjMem newObj0 ⋆
        (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) mAlloc := by
      dsimp [newObj0, bytes]; simpa [Nat.mul_comm 8 tn] using sep_ac hmObj0
    refine bn_from_limbs_copy_ret newObj0 n.toNat tn rfl rfl rfl rfl hwf0 htnLt64 htnLe hnle
      hmObj0' fun mCopy hnewWf hmPacked => ?_
    let newObj : LcnfObj := { newObj0 with limbs := bufXs.take tn }
    have hcanon : mpzNatCanon newObj val :=
      ⟨hnewWf, rfl, rfl, htakeLen.symm, by rw [htakeLen]; exact htnPos,
        by rw [htakeLen]; exact htnMax, hlastNe, hvalEq.symm, hbig⟩
    have hnotSm : ¬ val < 2 ^ 63 := by omega
    refine hQ p st' (newObj :: objs) mCopy hpres0 hrem0 hbd0 ?_
      (fun h => absurd h hnotSm) (fun _ => ⟨newObj, rfl, hcanon, rfl⟩) hmPacked
    unfold natRep; dsimp only [val] at hnotSm
    simp only [hnotSm, ↓reduceIte]
    exact ⟨hand0, newObj, List.mem_cons_self .., rfl, hcanon⟩
  apply wp_call_of; apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bufXs, rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R, hnle, hmTrim, ?_⟩
  c0_hsteps
  · have htn0 : tn = 0 := by c0_bv_omega
    have hval0 : val = 0 := by rw [hvalEq, htn0, List.take_zero, limbsVal_nil]
    have hQ' := hQ 1#64 st objs m (preservesMeta_refl st) (Nat.le_refl _) hbd
    rw [show limbsVal (bufXs.take n.toNat) = 0 from hval0] at hQ'
    refine hQ' ?_ (fun _ => rfl) (fun h => absurd h (by decide)) (sep_unpick2_4 hmTrim)
    simp [natRep]
  · have htn1 : tn = 1 := by c0_bv_omega
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hval1 : val = bufXs[0].toNat := by
      rw [hvalEq, htn1, htake1, limbsVal_cons, limbsVal_nil]; omega
    have hult : bufXs[0].toNat < 2 ^ 63 := by assumption
    have hvalSm : val < 2 ^ 63 := hval1 ▸ hult
    have h0lt : (0 : BitVec 64).toNat < bufXs.length := by
      have : (0 : BitVec 64).toNat = 0 := rfl; omega
    have h0eq : bufXs[(0 : BitVec 64).toNat]'h0lt = bufXs[0] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hret : (bufXs[(0 : BitVec 64).toNat]'h0lt <<< (1 : Nat) ||| 1#64) =
        BitVec.ofNat 64 (2 * val + 1) := by
      rw [h0eq, bv64_ofNat_small_enc hult, ← hval1]
    have hQ' := hQ (BitVec.ofNat 64 (2 * val + 1)) st objs m (preservesMeta_refl st)
      (Nat.le_refl _) hbd (by dsimp only [val] at *; simp [natRep, hvalSm])
      (fun _ => rfl) (fun h => absurd h (by omega)) (sep_unpick2_4 hmTrim)
    exact hret ▸ hQ'
  · have htn1 : tn = 1 := by c0_bv_omega
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hval1 : val = bufXs[0].toNat := by
      rw [hvalEq, htn1, htake1, limbsVal_cons, limbsVal_nil]; omega
    have huge : ¬ bufXs[0].toNat < 2 ^ 63 := by assumption
    exact hBoxed (by omega) (by rw [hval1]; omega)
  · have htnGe2 : 2 ≤ tn := by c0_bv_omega
    have hpow := hvalEq ▸ limbsVal_take_ge_pow64 hnle rfl htnGe2
    exact hBoxed (by omega) (by omega)

theorem bn_int_from_limbs_wp :
    ∀ xs m Q X, bnIntFromLimbsSpec xs m Q X → Func.wp rtR1Env bn_int_from_limbs.body xs m Q X := by
  intro ⟨rt, neg, buf, n, ⟨⟩⟩ m Q X ⟨st, bufXs, objs, R, hnle, hnMax, hbd, havail, hm, hQ⟩
  dsimp only [Func.wp, bn_int_from_limbs, bn_int_from_limbs_body]
  let tn := trimLenLoop bufXs n.toNat
  let mag := limbsVal (bufXs.take n.toNat)
  let val : Int := if tn = 0 then 0 else if neg = 0#64 then (mag : Int) else -(mag : Int)
  have htnLe : tn ≤ n.toNat := trimLenLoop_le bufXs n.toNat
  have htnMax : tn ≤ mpzMaxLimbs := le_trans htnLe hnMax
  have htnLt64 : tn < 2 ^ 64 := by unfold mpzMaxLimbs at htnMax; omega
  have hmagEq : mag = limbsVal (bufXs.take tn) := (limbsVal_trimLenLoop bufXs n.toNat hnle).symm
  have hmTrim : (array64 buf bufXs ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_pick2_4 hm
  have hBoxed : ∀ (htnPos : 0 < tn), (val < -2 ^ 62 ∨ 2 ^ 62 ≤ val) →
      wp rtR1Env Q X
        (Expr.call (as := [i64, i64]) (bs := [i64]) "lcnf_nat_alloc"
          (Arg.var rt, @Arg.var Val i64 (BitVec.ofNat 64 tn), ()) fun (p : Tup Val [i64]) =>
          Expr.group
            (fun (_ : Tup Cont [[]]) =>
              Blocks.cons
                (fun (_ : Tup Val []) =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p.1, Arg.imm 16#64, ()) }
                    fun (p_2 : Tup Val [i64]) =>
                    Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
                      (Arg.var p_2.1, Arg.var buf, @Arg.var Val i64 (BitVec.ofNat 64 tn), ())
                      fun (_ : Tup Val []) => Expr.ret (Arg.var p.1, ()))
                Blocks.nil)
            fun (Js : Tup Cont [[]]) =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (by decide),
                args := (Arg.var neg, Arg.imm 0#64, ()) } fun (p_1 : Tup Val [Ty.bool]) =>
              Expr.jnz (Arg.var p_1.1)
                (Expr.load i64 (Arg.var p.1) fun (ld : Val i64) =>
                  Expr.let_
                    { sig := [i32], code := OpCode.sext 32 64,
                      args := (Arg.imm (48 : BitVec 32), ()) } fun (p_2 : Tup Val [i64]) =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.shl i64,
                        args := (Arg.imm 1#64, Arg.var p_2.1, ()) } fun (p_3 : Tup Val [i64]) =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.or i64,
                          args := (Arg.var ld, Arg.var p_3.1, ()) } fun (p_4 : Tup Val [i64]) =>
                        Expr.store (Arg.var p_4.1) (Arg.var p.1) (Expr.jump Js.1 ()))
                (Expr.jump Js.1 ())) m := by
    intro htnPos hbig
    have hlastNe : (bufXs.take tn).getLast! ≠ 0#64 := getLast_take_ne_zero bufXs n.toNat htnPos hnle
    have htakeLen : (bufXs.take tn).length = tn := List.length_take_of_le (le_trans htnLe hnle)
    have htakeNe : bufXs.take tn ≠ [] := by intro h; rw [h, List.length_nil] at htakeLen; omega
    have hvalNz : val = if neg = 0#64 then (mag : Int) else -(mag : Int) := by
      dsimp [val]; simp [show tn ≠ 0 from by omega]
    apply wp_call_of; apply rtR1Env_lcnf_nat_alloc
    dsimp only [lcnfNatAllocSpec, vals, Tup.map, Arg.val]
    refine ⟨st, array64 buf bufXs ⋆ lcnfHeap objs ⋆ R,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64]; exact htnMax, hbd,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos]
         exact havail hbig,
      sep_pick1_4 (sep_unpick2_4 hmTrim),
      fun p st' mAlloc hwf0 hand0 hpres0 hrem0 hbd0 hmObj0 => ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htnLt64, Nat.max_eq_right htnPos] at hwf0 hmObj0
    let bytes := 16 + 8 * tn
    let newObj0 : LcnfObj :=
      { addr := p, rc := 1#32, csSz := if bytes < 65536 then bytes else 0, other := 0,
        tag := mpzTag, cap := tn, arrSize := tn, limbs := List.replicate tn 0#64 }
    let newObj1 : LcnfObj := { newObj0 with other := if neg = 0#64 then 0 else 1 }
    have hobj1Wf : newObj1.Wf :=
      mpz_wf_of_limbs hwf0 rfl rfl rfl rfl rfl (by dsimp [newObj1]; split <;> decide) rfl rfl
        (by dsimp [newObj1, newObj0]; rw [List.length_replicate])
    refine wp_join_group (fun (_ : Tup Val []) m1 =>
        (lcnfObjMem newObj1 ⋆
          (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) m1) ?_ ?_
    · intro Js1 _ m1 hm1; simp only [Blocks.get]
      refine bn_from_limbs_copy_ret newObj1 n.toNat tn rfl rfl rfl rfl hobj1Wf htnLt64 htnLe hnle
        hm1 fun mCopy hnewWf hmPacked => ?_
      let newObj : LcnfObj := { newObj1 with limbs := bufXs.take tn }
      have hmagPos : 0 < mag := by
        rw [hmagEq]
        have hge := limbsVal_ge_pow_of_nonzero_last htakeNe
          (by rw [getLast_eq_getLast! _ htakeNe]; exact hlastNe)
        have h1 := Nat.one_le_pow (64 * ((bufXs.take tn).length - 1)) 2 (by decide)
        omega
      have hnatAbs : val.natAbs = mag := by rw [hvalNz]; split <;> simp [Int.natAbs_natCast]
      have hothDisj : newObj.other = 0 ∨ newObj.other = 1 := by
        dsimp [newObj, newObj1]; split <;> simp
      have hothNeg : newObj.other = 1 ↔ val < 0 := by
        dsimp [newObj, newObj1]; rw [hvalNz]
        by_cases hn0 : neg = 0#64
        · simp [hn0]
        · simp [hn0]; omega
      have hcanon : mpzIntCanon newObj val :=
        ⟨hnewWf, rfl, hothDisj, htakeLen.symm, by rw [htakeLen]; exact htnPos,
          by rw [htakeLen]; exact htnMax, hlastNe, hmagEq.symm.trans hnatAbs.symm, hothNeg, hbig⟩
      have hnotSm : ¬ (-2 ^ 62 ≤ val ∧ val < 2 ^ 62) := by omega
      refine hQ p st' (newObj :: objs) mCopy hpres0 hrem0 hbd0 ?_
        (fun h => absurd h hnotSm) (fun _ => ⟨newObj, rfl, hcanon, rfl⟩) hmPacked
      unfold intRep; dsimp only [val, tn, mag] at hnotSm
      simp only [hnotSm, ↓reduceIte]
      exact ⟨hand0, newObj, List.mem_cons_self .., rfl, hcanon⟩
    · intro Js1 hJs1
      c0_hstep
      c0_hsplit
      · have hnegNz : neg ≠ 0#64 := by assumption
        have hm0 : (lcnfObjMem newObj0 ⋆
            (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) mAlloc := by
          dsimp [newObj0, bytes]; simpa [Nat.mul_comm 8 tn] using sep_ac hmObj0
        have hmHdr := sep_assoc_r (sep_assoc_r (lcnfObjMem_mpz_elim (o := newObj0) rfl hm0))
        clear hmObj0 hm0
        c0_hstep; c0_hstep; c0_hstep; c0_hstep
        have hmHdr' := hmHdr
        rw [show newObj0.addr = p from rfl] at hmHdr'
        refine wp_store_sep (by
          dsimp only [Arg.val]
          exact store_cell64 _ hmHdr') fun mS hmS => ?_
        c0_hsteps
        try dsimp only [Arg.val] at hmS
        have hhdrEq : (newObj0.header ||| (1#64 : BitVec 64) <<< (48 : Nat)) =
            newObj1.header := by
          rw [show (1#64 : BitVec 64) <<< (48 : Nat) = 1#64 <<< 48#64 from rfl,
            LcnfObj.header_or_other_one newObj0 hwf0.2.2.2.1 rfl]
          dsimp [newObj1]; simp [hnegNz]
        rw [hhdrEq] at hmS
        have haddr1 : p = newObj1.addr := rfl
        have hmeta01 : newObj0.mpzMeta = newObj1.mpzMeta := rfl
        have hlimbs01 : newObj0.limbs = newObj1.limbs := rfl
        rw [haddr1, hmeta01, hlimbs01] at hmS
        exact hJs1 () mS (lcnfObjMem_mpz_intro (o := newObj1) rfl (sep_ac hmS))
      · have hneg0 : neg = 0#64 := by assumption
        have hm0 : (lcnfObjMem newObj0 ⋆
            (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R)) mAlloc := by
          dsimp [newObj0, bytes]; simpa [Nat.mul_comm 8 tn] using sep_ac hmObj0
        have hEq01 : newObj1 = newObj0 := by dsimp [newObj1]; simp [hneg0]; rfl
        rw [← hEq01] at hm0
        exact hJs1 () mAlloc hm0
  apply wp_call_of; apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bufXs, rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R, hnle, hmTrim, ?_⟩
  c0_hsteps
  · have htn0 : tn = 0 := by c0_bv_omega
    have hval0 : val = 0 := by dsimp [val]; rw [htn0]; rfl
    have hQ' := hQ 1#64 st objs m (preservesMeta_refl st) (Nat.le_refl _) hbd
    dsimp [val] at hval0; rw [hval0] at hQ'
    refine hQ' ?_ (fun _ => rfl) (fun h => absurd h (by decide)) (sep_unpick2_4 hmTrim)
    simp [intRep]
  · have htn1 : tn = 1 := by c0_bv_omega
    have hneg0 : neg = 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hvalPos : val = (bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hneg0, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hult : bufXs[0].toNat < 2 ^ 62 := by assumption
    have hvalSm : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := by rw [hvalPos]; omega
    have h0lt : (0 : BitVec 64).toNat < bufXs.length := by
      have : (0 : BitVec 64).toNat = 0 := rfl; omega
    have h0eq : bufXs[(0 : BitVec 64).toNat]'h0lt = bufXs[0] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hret : (bufXs[(0 : BitVec 64).toNat]'h0lt <<< (1 : Nat) ||| 1#64) =
        BitVec.ofInt 64 (2 * val + 1) := by
      rw [h0eq, bv64_ofInt_pos_enc hult, ← hvalPos]
    dsimp only [val, tn, mag] at hvalSm
    have hQ' := hQ (BitVec.ofInt 64 (2 * val + 1)) st objs m (preservesMeta_refl st)
      (Nat.le_refl _) hbd (by dsimp only [val, tn, mag]; simp [intRep]; omega)
      (fun _ => rfl) (fun h => absurd h (by omega)) (sep_unpick2_4 hmTrim)
    exact hret ▸ hQ'
  · have htn1 : tn = 1 := by c0_bv_omega
    have hneg0 : neg = 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hvalPos : val = (bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hneg0, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have huge : ¬ bufXs[0].toNat < 2 ^ 62 := by assumption
    exact hBoxed (by omega) (Or.inr (by rw [hvalPos]; omega))
  · have htn1 : tn = 1 := by c0_bv_omega
    have hnegNz : neg ≠ 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hvalNeg : val = -(bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hnegNz, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hule : bufXs[0].toNat ≤ 2 ^ 62 := by assumption
    have hvalSm : -2 ^ 62 ≤ val ∧ val < 2 ^ 62 := by rw [hvalNeg]; omega
    have h0lt : (0 : BitVec 64).toNat < bufXs.length := by
      have : (0 : BitVec 64).toNat = 0 := rfl; omega
    have h0eq : bufXs[(0 : BitVec 64).toNat]'h0lt = bufXs[0] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hret : (((0 : BitVec 64) - bufXs[(0 : BitVec 64).toNat]'h0lt) <<< (1 : Nat) ||| 1#64) =
        BitVec.ofInt 64 (2 * val + 1) := by
      rw [h0eq, show (0 : BitVec 64) = 0#64 from rfl, bv64_ofInt_neg_enc hule, ← hvalNeg]
    dsimp only [val, tn, mag] at hvalSm
    have hQ' := hQ (BitVec.ofInt 64 (2 * val + 1)) st objs m (preservesMeta_refl st)
      (Nat.le_refl _) hbd (by dsimp only [val, tn, mag]; simp [intRep]; omega)
      (fun _ => rfl) (fun h => absurd h (by omega)) (sep_unpick2_4 hmTrim)
    exact hret ▸ hQ'
  · have htn1 : tn = 1 := by c0_bv_omega
    have hnegNz : neg ≠ 0#64 := by assumption
    have htake1 : bufXs.take 1 = [bufXs[0]] := by
      cases bufXs with | nil => simp at hnle; omega | cons _ _ => rfl
    have hvalNeg : val = -(bufXs[0].toNat : Int) := by
      dsimp [val]; simp [htn1, hnegNz, hmagEq, htake1, limbsVal_cons, limbsVal_nil]
    have hugt : ¬ bufXs[0].toNat ≤ 2 ^ 62 := by assumption
    exact hBoxed (by omega) (Or.inl (by rw [hvalNeg]; omega))
  · have htnGe2 : 2 ≤ tn := by c0_bv_omega
    have hpow := hmagEq ▸ limbsVal_take_ge_pow64 hnle rfl htnGe2
    have hbig : val < -2 ^ 62 ∨ 2 ^ 62 ≤ val := by
      dsimp [val]; simp only [show tn ≠ 0 from by omega, ↓reduceIte]
      by_cases hn0 : neg = 0#64
      · right; simp [hn0]; omega
      · left; simp [hn0]; omega
    exact hBoxed (by omega) hbig

private theorem cmpResult64_cases {a b : Nat} {r : Int}
    (hm1 : r = -1 ↔ a < b) (hz : r = 0 ↔ a = b) (hp1 : r = 1 ↔ b < a) :
    (r = -1 → -1#64 = cmpResult64 a b) ∧
    (r = 1 → 1#64 = cmpResult64 a b) ∧
    (r = 0 → 0#64 = cmpResult64 a b) := by
  refine ⟨fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
  · simp [cmpResult64, hm1.mp hr]
  · have hgt := hp1.mp hr
    simp [cmpResult64, show ¬a < b by omega, hgt]
  · simp [cmpResult64, hz.mp hr]

theorem bn_cmp_fixed_wp :
    ∀ xs m Q X, bnCmpFixedSpec xs m Q X → Func.wp rtR1Env bn_cmp_fixed.body xs m Q X := by
  intro ⟨a, b, n, ⟨⟩⟩ m Q X ⟨aXs, bXs, R, hna, hnb, hm, hQ⟩
  dsimp only [Func.wp, bn_cmp_fixed, bn_cmp_fixed_body]
  have hspec := cmpLimbsFixed_spec aXs bXs n.toNat hna hnb
  have ⟨hresM1, hresP1, hres0⟩ := cmpResult64_cases hspec.1 hspec.2.1 hspec.2.2
  refine wp_loop_inv
    (fun (xs : Tup Val [i64]) mL =>
      ∃ k : Nat, k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
        cmpLimbsFixed aXs bXs k = cmpLimbsFixed aXs bXs n.toNat ∧ mL = m)
    (fun (xs : Tup Val [i64]) _ => xs.1.toNat) ?_ ?_
  · intro Js hJs
    c0_hsteps
    exact hJs (n, ()) m ⟨n.toNat, Nat.le_refl _, BitVec.eq_of_toNat_eq (by simp), rfl, rfl⟩
  · intro Js ⟨i, ⟨⟩⟩ mL ⟨k, hkLe, hkEq, hcmpEq, hmL⟩ hRec
    subst hkEq hmL
    have hklt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hkLe n.isLt
    c0_hsplit
    · have hkPos : 0 < k := by c0_bv_omega
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hidxA : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < aXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hidxB : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64 < bXs.length := by
        rw [bv64_sub1_idx hklt64]; omega
      have hsubA : (BitVec.ofNat 64 (k' + 1) - 1#64).toNat < aXs.length := by c0_bv_omega
      have hsubB : (BitVec.ofNat 64 (k' + 1) - 1#64).toNat < bXs.length := by c0_bv_omega
      have hk'A : k' < aXs.length := by omega
      have hk'B : k' < bXs.length := by omega
      c0_hsteps
      · have hlt : aXs[k'] < bXs[k'] := by
          have hc := ‹aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat›
          simp only [bv64_sub1_idx hklt64] at hc
          rwa [BitVec.lt_def]
        have hstep : cmpLimbsFixed aXs bXs (k' + 1) = -1 := by
          rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
          simp [hlt]
        rw [show (BitVec.signExtend 64 (-1 : BitVec 32) : BitVec 64) = -1#64 from rfl]
        rw [← hresM1 (by rw [← hcmpEq, hstep])] at hQ
        exact hQ
      · have hnlt : ¬ aXs[k'] < bXs[k'] := by
          have hc := ‹¬ aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat›
          simp only [bv64_sub1_idx hklt64] at hc; rwa [BitVec.lt_def]
        have hgt : bXs[k'] < aXs[k'] := by
          have hc := ‹bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat›
          simp only [bv64_sub1_idx hklt64] at hc; rwa [BitVec.lt_def]
        have hstep : cmpLimbsFixed aXs bXs (k' + 1) = 1 := by
          rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
          simp [hnlt, hgt]
        rw [← hresP1 (by rw [← hcmpEq, hstep])] at hQ; exact hQ
      · have hnlt : ¬ aXs[k'] < bXs[k'] := by
          have hc := ‹¬ aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat›
          simp only [bv64_sub1_idx hklt64] at hc; rwa [BitVec.lt_def]
        have hngt : ¬ bXs[k'] < aXs[k'] := by
          have hc := ‹¬ bXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat <
            aXs[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (k' + 1)) % 2 ^ 64].toNat›
          simp only [bv64_sub1_idx hklt64] at hc; rwa [BitVec.lt_def]
        have hstep : cmpLimbsFixed aXs bXs (k' + 1) = cmpLimbsFixed aXs bXs k' := by
          rw [cmpLimbsFixed.eq_2, getElem!_pos aXs k' (by omega), getElem!_pos bXs k' (by omega)]
          simp [hnlt, hngt]
        have hsub : BitVec.ofNat 64 (k' + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k' := by
          apply BitVec.eq_of_toNat_eq; c0_bv_omega
        exact hRec _ mL (by rw [hsub]; c0_bv_omega)
          ⟨k', by omega, hsub, by rw [← hcmpEq, hstep], rfl⟩
    · have hk0 : k = 0 := by c0_bv_omega
      subst hk0
      c0_hsteps
      rw [← hres0 (by rw [← hcmpEq, cmpLimbsFixed.eq_1])] at hQ; exact hQ

theorem bn_cmp_wp :
    ∀ xs m Q X, bnCmpSpec xs m Q X → Func.wp rtR1Env bn_cmp.body xs m Q X := by
  intro ⟨a, na, b, nb, ⟨⟩⟩ m Q X ⟨aXs, bXs, R, hna, hnb, hm, hQ⟩
  dsimp only [Func.wp, bn_cmp, bn_cmp_body]
  let ta := trimLenLoop aXs na.toNat
  let tb := trimLenLoop bXs nb.toNat
  have htaLe : ta ≤ na.toNat := trimLenLoop_le aXs na.toNat
  have htbLe : tb ≤ nb.toNat := trimLenLoop_le bXs nb.toNat
  have htaLt64 : ta < 2 ^ 64 := Nat.lt_of_le_of_lt htaLe na.isLt
  have htbLt64 : tb < 2 ^ 64 := Nat.lt_of_le_of_lt htbLe nb.isLt
  have hspec := cmpLimbs_spec aXs na.toNat bXs nb.toNat hna hnb
  have hcmpEq : cmpLimbs aXs na.toNat bXs nb.toNat =
      if ta < tb then -1 else if tb < ta then 1 else cmpLimbsFixed aXs bXs ta := cmpLimbs.eq_1 ..
  apply wp_call_of; apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨aXs, (array64 b bXs ⋆ R), hna, sep_assoc_r hm, ?_⟩
  apply wp_call_of; apply rtR1Env_bn_trim
  dsimp only [bnTrimSpec, vals, Tup.map, Arg.val]
  refine ⟨bXs, (array64 a aXs ⋆ R), hnb, sep_swap12 (sep_assoc_r hm), ?_⟩
  c0_hsteps
  · have hlt : ta < tb := by c0_bv_omega
    have hm1 : cmpLimbs aXs na.toNat bXs nb.toNat = -1 := by rw [hcmpEq]; simp [hlt]
    have hltVal := hspec.1.mp hm1
    rw [show (BitVec.signExtend 64 (-1 : BitVec 32) : BitVec 64) = -1#64 from rfl]
    rw [show cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)) = -1#64 by
      simp [cmpResult64, hltVal]] at hQ
    exact hQ
  · have hgt : tb < ta := by c0_bv_omega
    have hnlt : ¬ ta < tb := by omega
    have hp1 : cmpLimbs aXs na.toNat bXs nb.toNat = 1 := by rw [hcmpEq]; simp [hnlt, hgt]
    have hgtVal := hspec.2.2.mp hp1
    rw [show cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)) = 1#64 by
      simp [cmpResult64,
        show ¬ limbsVal (aXs.take na.toNat) < limbsVal (bXs.take nb.toNat) by omega, hgtVal]]
      at hQ
    exact hQ
  · have hteq : ta = tb := by c0_bv_omega
    apply wp_call_of; apply rtR1Env_bn_cmp_fixed
    dsimp only [bnCmpFixedSpec, vals, Tup.map, Arg.val]
    refine ⟨aXs, bXs, R, by c0_bv_omega, by c0_bv_omega,
      sep_assoc_l (sep_swap12 (sep_swap12 (sep_assoc_r hm))), ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htaLt64]
    have hvalA := (limbsVal_trimLenLoop aXs na.toNat hna).symm
    have hvalB := (limbsVal_trimLenLoop bXs nb.toNat hnb).symm
    rw [show limbsVal (aXs.take ta) = limbsVal (aXs.take na.toNat) from hvalA.symm,
      show limbsVal (bXs.take ta) = limbsVal (bXs.take nb.toNat) from
        by rw [hteq]; exact hvalB.symm]
    exact hQ

end LeanQbe.T.LeanLCNF
