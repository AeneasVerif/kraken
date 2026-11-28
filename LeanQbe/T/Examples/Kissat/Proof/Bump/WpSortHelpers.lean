/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.MemLemmas
import Kraken.ToBytes

/-!
# Sorting, Packing, Radix & Memory-Focus Helpers for `Proof.Bump` (`Proof.Bump.WpSortHelpers`)

1. `packPair64` / `packPairs64` / `unpackPairs32` bit-packing lemmas and
   `array64` ↔ `array (t := i32)` separation-logic equivalences.
2. `FullMem` array focus/unfocus combinators (`FullScrSortRest`, `FullCoreReprRest`).
3. List swap/take permutation lemmas and LSD radix-pass counting/permutation invariants.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. 64-Bit `(hi, lo)` Pair Packing & Array Bridges -/

@[expose] def packPair64 (lo hi : BitVec 32) : BitVec 64 :=
  (BitVec.setWidth 64 hi <<< 32) ||| BitVec.setWidth 64 lo

@[expose] def packPairs64 : List (BitVec 32) → List (BitVec 64)
  | lo :: hi :: rest => packPair64 lo hi :: packPairs64 rest
  | _ => []

@[expose] def unpackPairs32 (xs : List (BitVec 64)) : List (BitVec 32) :=
  List.flatMap (fun (x : BitVec 64) => [x.setWidth 32, (x >>> 32).setWidth 32]) xs

private theorem bv32_getLsbD_ge (v : BitVec 32) {k : Nat} (hk : 32 ≤ k) :
    v.getLsbD k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hk))

private theorem setWidth64_getLsbD_hi (lo : BitVec 32) {k : Nat} (hk : 32 ≤ k) :
    (BitVec.setWidth 64 lo).getLsbD k = false := by
  rw [BitVec.getLsbD_setWidth]
  by_cases hlt : k < 64
  · simp [hlt, bv32_getLsbD_ge lo hk]
  · simp [hlt]

theorem packPair64_shr32 (lo hi : BitVec 32) :
    (packPair64 lo hi) >>> 32 = BitVec.setWidth 64 hi := by
  unfold packPair64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, setWidth64_getLsbD_hi lo (by omega)]
  by_cases hi32 : i < 32
  · simp [hi32, hi_lt, show 32 + i < 64 by omega, show ¬ (32 + i < 32) by omega]
  · simp [show ¬ (32 + i < 64) by omega, hi_lt, bv32_getLsbD_ge hi (k := i) (by omega)]

theorem packPair64_lo (lo hi : BitVec 32) : (packPair64 lo hi).setWidth 32 = lo := by
  unfold packPair64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [hi_lt]

theorem packPair64_hi (lo hi : BitVec 32) : ((packPair64 lo hi) >>> 32).setWidth 32 = hi := by
  rw [packPair64_shr32]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [hi_lt]

theorem packPair64_hi_toNat (lo hi : BitVec 32) :
    ((packPair64 lo hi) >>> 32).toNat = hi.toNat := by
  rw [packPair64_shr32, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans hi.isLt (by decide))]

theorem packPairs64_length (xs : List (BitVec 32)) :
    (packPairs64 xs).length = xs.length / 2 := by
  match xs with
  | [] => simp [packPairs64]
  | [_] => simp [packPairs64]
  | _ :: _ :: rest =>
    simp only [packPairs64, List.length_cons]
    rw [packPairs64_length rest]; omega

theorem unpackPairs32_length (xs : List (BitVec 64)) :
    (unpackPairs32 xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [unpackPairs32]
  | cons x xs ih =>
    simp only [unpackPairs32, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons] at ih ⊢
    omega

theorem unpackPairs32_packPairs64 (xs : List (BitVec 32)) (heven : xs.length % 2 = 0) :
    unpackPairs32 (packPairs64 xs) = xs := by
  match xs with
  | [] => simp [packPairs64, unpackPairs32]
  | [_] => simp at heven
  | lo :: hi :: rest =>
    simp only [packPairs64, unpackPairs32, List.flatMap_cons, List.cons_append,
      List.nil_append, packPair64_lo, packPair64_hi]
    exact congrArg (lo :: hi :: ·) (unpackPairs32_packPairs64 rest (by simp at heven; omega))

theorem packPairs64_unpackPairs32 (xs : List (BitVec 64)) :
    packPairs64 (unpackPairs32 xs) = xs := by
  induction xs with
  | nil => simp [unpackPairs32, packPairs64]
  | cons x xs ih =>
    have hx : packPair64 (x.setWidth 32) ((x >>> 32).setWidth 32) = x := by
      unfold packPair64
      apply BitVec.eq_of_getLsbD_eq
      intro i hi_lt
      by_cases hi32 : i < 32
      · simp [hi32, hi_lt]
      · simp [hi32, show 32 ≤ i by omega, show i - 32 < 32 by omega, hi_lt]
    have hu : unpackPairs32 (x :: xs) =
        [x.setWidth 32, (x >>> 32).setWidth 32] ++ unpackPairs32 xs := rfl
    rw [hu]
    simp only [List.cons_append, List.nil_append, packPairs64, hx, ih]

private theorem int_take32_toInt (x : BitVec 64) :
    Int.take x.toInt 32 = Int.take (x.setWidth 32).toInt 32 := by
  dsimp only [Int.take]
  have h1 : x.toInt % (2 : Int) ^ 32 = ((x.toNat % 2 ^ 32 : Nat) : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  have h2 : (x.setWidth 32).toInt % (2 : Int) ^ 32 = ((x.toNat % 2 ^ 32 : Nat) : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth]
    split <;> omega
  rw [h1, h2]

private theorem int_div4_take32_toInt (x : BitVec 64) :
    Int.take ((((x.toInt / 256) / 256) / 256) / 256) 32 =
      Int.take ((x >>> 32).setWidth 32).toInt 32 := by
  dsimp only [Int.take]
  have hdiv : (((x.toInt / 256) / 256) / 256) / 256 = x.toInt / (2 : Int) ^ 32 := by omega
  rw [hdiv]
  have hx : x.toInt / (2 : Int) ^ 32 % (2 : Int) ^ 32 =
      ((x.toNat / 2 ^ 32 % 2 ^ 32 : Nat) : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  have hy : ((x >>> 32).setWidth 32).toInt % (2 : Int) ^ 32 =
      ((x.toNat / 2 ^ 32 % 2 ^ 32 : Nat) : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    have hlt : x.toNat / 2 ^ 32 < 2 ^ 32 := by have := x.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]
    split <;> omega
  rw [hx, hy]

private theorem int_toBytes_8_split (v : Int) :
    Int.toBytes 8 v = Int.toBytes 4 v ++ Int.toBytes 4 ((((v / 256) / 256) / 256) / 256) := by
  rfl

private theorem toBits_i64_eq (x : BitVec 64) : toBits (t := i64) x = x := by
  simp [toBits]

private theorem toBits_i32_eq (x : BitVec 32) : toBits (t := i32) x = x := by
  simp [toBits]

private theorem sw_toBits_i64_eq (x : BitVec 64) :
    BitVec.setWidth (8 * i64.bytes) (toBits i64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toBits_i64_eq, BitVec.toNat_setWidth]
  have hx : x.toNat < 2 ^ (8 * i64.bytes) := by
    rw [show i64.bytes = 8 from rfl]; exact x.isLt
  exact Nat.mod_eq_of_lt hx

private theorem sw_toBits_i32_eq (x : BitVec 32) :
    BitVec.setWidth (8 * i32.bytes) (toBits i32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toBits_i32_eq, BitVec.toNat_setWidth]
  have hx : x.toNat < 2 ^ (8 * i32.bytes) := by
    rw [show i32.bytes = 4 from rfl]; exact x.isLt
  exact Nat.mod_eq_of_lt hx

private theorem bytesOf_i64_cons (x : BitVec 64) (xs : List (BitVec 64)) :
    bytesOf (t := i64) (x :: xs) = Int.toBytes 8 x.toInt ++ bytesOf (t := i64) xs := by
  conv => lhs; unfold bytesOf
  first
  | rw [List.map_cons, List.flatten_cons, sw_toBits_i64_eq, show i64.bytes = 8 from rfl]; rfl
  | rw [List.flatMap_cons, toBits_i64_eq, show i64.bytes = 8 from rfl]; rfl

private theorem bytesOf_i32_cons (x : BitVec 32) (xs : List (BitVec 32)) :
    bytesOf (t := i32) (x :: xs) = Int.toBytes 4 x.toInt ++ bytesOf (t := i32) xs := by
  conv => lhs; unfold bytesOf
  first
  | rw [List.map_cons, List.flatten_cons, sw_toBits_i32_eq, show i32.bytes = 4 from rfl]; rfl
  | rw [List.flatMap_cons, toBits_i32_eq, show i32.bytes = 4 from rfl]; rfl

private theorem bytesOf_i64_eq_i32_unpackPairs32 (xs : List (BitVec 64)) :
    bytesOf (t := i64) xs = bytesOf (t := i32) (unpackPairs32 xs) := by
  induction xs with
  | nil => simp [bytesOf, unpackPairs32]
  | cons x xs ih =>
    have hu : unpackPairs32 (x :: xs) =
        x.setWidth 32 :: (x >>> 32).setWidth 32 :: unpackPairs32 xs := rfl
    rw [bytesOf_i64_cons, hu, bytesOf_i32_cons, bytesOf_i32_cons, ← List.append_assoc, ih]
    congr 1
    rw [int_toBytes_8_split x.toInt]
    have hlo : Int.toBytes 4 x.toInt = Int.toBytes 4 (x.setWidth 32).toInt := by
      rw [← Int.toBytes_emod 4 x.toInt, ← Int.toBytes_emod 4 (x.setWidth 32).toInt]
      exact congrArg (Int.toBytes 4) (int_take32_toInt x)
    have hhi : Int.toBytes 4 ((((x.toInt / 256) / 256) / 256) / 256) =
        Int.toBytes 4 ((x >>> 32).setWidth 32).toInt := by
      rw [← Int.toBytes_emod 4 _, ← Int.toBytes_emod 4 ((x >>> 32).setWidth 32).toInt]
      exact congrArg (Int.toBytes 4) (int_div4_take32_toInt x)
    rw [hlo, hhi]

theorem array64_eq_array32_unpack (a : BitVec 64) (xs : List (BitVec 64))
    (h : 8 * xs.length ≤ 2 ^ 64) :
    array64 a xs = array (t := i32) a (unpackPairs32 xs) := by
  have h64 : Ty.bytes i64 * xs.length ≤ 2 ^ 64 := by
    simpa only [show Ty.bytes i64 = 8 from rfl] using h
  have h32 : Ty.bytes i32 * (unpackPairs32 xs).length ≤ 2 ^ 64 := by
    rw [unpackPairs32_length, show Ty.bytes i32 = 4 from rfl]; omega
  funext m
  apply propext
  constructor
  · intro hm
    rw [array64_eq_array a xs] at hm
    have hm_eq := array_eq_bytesOf (t := i64) a xs h64 hm
    rw [hm_eq, bytesOf_i64_eq_i32_unpackPairs32 xs]
    exact array_bytes (t := i32) a (unpackPairs32 xs) h32
  · intro hm
    have hm_eq := array_eq_bytesOf (t := i32) a (unpackPairs32 xs) h32 hm
    rw [array64_eq_array a xs, hm_eq, ← bytesOf_i64_eq_i32_unpackPairs32 xs]
    exact array_bytes (t := i64) a xs h64

theorem array32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
    (heven : xs.length % 2 = 0) (h : 4 * xs.length ≤ 2 ^ 64) :
    array (t := i32) a xs = array64 a (packPairs64 xs) := by
  have h64 : 8 * (packPairs64 xs).length ≤ 2 ^ 64 := by
    rw [packPairs64_length]; omega
  rw [array64_eq_array32_unpack a (packPairs64 xs) h64, unpackPairs32_packPairs64 xs heven]

private theorem array32_nil_eq_emp (a : BitVec 64) : array (t := i32) a [] = emp := by
  first | rw [array_nil] | (funext m; apply propext; rw [array_nil])

theorem array32_prefix256_focus (a : BitVec 64) (sbuf : List (BitVec 32))
    (hge : 512 ≤ sbuf.length) (_hle : 4 * sbuf.length ≤ 2 ^ 64) :
    array (t := i32) a sbuf =
      (array64 a (packPairs64 (sbuf.take 512)) ⋆
        array (t := i32) (a + 2048#64) (sbuf.drop 512)) := by
  have hsplit := array_slice_focus (t := i32) a sbuf (off := 0) (len := 512) (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero, List.drop_zero, List.take_zero, Nat.zero_add,
    show Ty.bytes i32 * 512 = 2048 from rfl] at hsplit
  rw [array32_nil_eq_emp, sep_comm emp, sep_emp] at hsplit
  rw [hsplit, array32_eq_array64_pack a (sbuf.take 512)
    (by rw [List.length_take_of_le hge])
    (by rw [List.length_take_of_le hge]; omega)]

theorem array32_prefix256_replace (a : BitVec 64) (sbuf : List (BitVec 32))
    (cnt : List (BitVec 64)) (hge : 512 ≤ sbuf.length) (hcnt : cnt.length = 256)
    (_hle : 4 * sbuf.length ≤ 2 ^ 64) :
    (array64 a cnt ⋆ array (t := i32) (a + 2048#64) (sbuf.drop 512)) =
      array (t := i32) a (unpackPairs32 cnt ++ sbuf.drop 512) := by
  have hlen_u : (unpackPairs32 cnt).length = 512 := by
    rw [unpackPairs32_length, hcnt]
  have h64 : 8 * cnt.length ≤ 2 ^ 64 := by rw [hcnt]; decide
  rw [array64_eq_array32_unpack a cnt h64]
  have hrep := array_slice_replace (t := i32) a sbuf (unpackPairs32 cnt) (off := 0) (len := 512)
    (by omega) hlen_u
  simp only [List.take_zero, List.nil_append, Nat.mul_zero, BitVec.add_zero, Nat.zero_add,
    show Ty.bytes i32 * 512 = 2048 from rfl] at hrep
  rw [array32_nil_eq_emp, sep_comm emp, sep_emp] at hrep
  exact hrep.symm

/-! ## 2. `FullMem` Focus & Reconstruction Helpers -/

@[expose] def FullCoreReprRest (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  FullCoreByteArrs c k ⋆ FullCoreU32A c k ⋆ FullCoreDynArrs c k ⋆
  array (t := i32) c.pFrameTrail k.frame_trail ⋆ array (t := i32) c.pFrameDec k.frame_dec ⋆
  array (t := i32) c.pWvec k.wvec ⋆ array (t := i32) c.pMinStk k.min_stk

theorem fullCoreArrays_focus_repr (c : FullCfg) (k : FullCoreState) :
    FullCoreArrays c k = (array (t := i32) c.pRepr k.repr ⋆ FullCoreReprRest c k) := by
  simp only [FullCoreArrays, FullCoreU32B, FullCoreReprRest]; ac_rfl

@[expose] def FullScrSortRest (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  FullScrByteArrs c sc ⋆
  array (t := i32) c.pHeap sc.heap ⋆ array (t := i32) c.pPos sc.pos ⋆
  array (t := i32) c.pShrinkStk sc.shrink_stk ⋆ array (t := i32) c.pQPrev sc.q_prev ⋆
  array (t := i32) c.pQNext sc.q_next ⋆
  array (t := i32) c.pWorkStk2 sc.work_stk2 ⋆ array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach ⋆
  FullScrMetaArrs c sc ⋆
  array (t := i32) c.pDelayed sc.delayed ⋆ array (t := i32) c.pRedRefs sc.red_refs ⋆
  array (t := i32) c.pExtendStk sc.extend_stk

theorem fullScratchArrays_focus_sort (c : FullCfg) (sc : FullScratch) :
    FullScratchArrays c sc =
      (array (t := i32) c.pQStamp sc.q_stamp ⋆
        array (t := i32) c.pWorkStk1 sc.work_stk1 ⋆
        array (t := i32) c.pWsort sc.wsort ⋆
        array (t := i32) c.pScratchBuf sc.scratch_buf ⋆
        FullScrSortRest c sc) := by
  simp only [FullScratchArrays, FullScrU32A, FullScrWksArrs, FullScrDynArrs, FullScrSortRest]
  ac_rfl

/-! ## 3. List Swap & Permutation Lemmas -/

@[expose] def listSwap {α : Type} (xs : List α) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) : List α :=
  (xs.set i xs[j]).set j xs[i]

theorem listSwap_length {α : Type} (xs : List α) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (listSwap xs i j hi hj).length = xs.length := by
  simp [listSwap]

theorem listSwap_getElem_ge {α : Type} (xs : List α) (i j k : Nat)
    (hi : i < xs.length) (hj : j < xs.length) (hki : i ≠ k) (hkj : j ≠ k) :
    (listSwap xs i j hi hj)[k]? = xs[k]? := by
  simp only [listSwap, List.getElem?_set_ne hkj, List.getElem?_set_ne hki]

private theorem list_count_set {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {k : Nat}
    (hk : k < xs.length) (v a : α) :
    (xs.set k v).count a + (if xs[k] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing k with
  | nil => contradiction
  | cons x xs ih =>
    cases k with
    | zero => simp [List.count_cons]; omega
    | succ k' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have h1 := ih (by simp at hk; omega)
      omega

theorem listSwap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    (listSwap xs i j hi hj).Perm xs := by
  by_cases hij : i = j
  · subst hij
    rw [List.perm_iff_count]; intro a
    simp only [listSwap]
    have h1 := list_count_set (xs.set i xs[i]) (by simp; omega) xs[i] a
    have h2 := list_count_set xs hi xs[i] a
    rw [List.getElem_set_self (by rw [List.length_set]; exact hi)] at h1
    omega
  · rw [List.perm_iff_count]; intro a
    simp only [listSwap]
    have h1 := list_count_set (xs.set i xs[j]) (by simp; omega) xs[i] a
    have h2 := list_count_set xs hi xs[j] a
    rw [List.getElem_set_ne hij] at h1
    omega

theorem list_take_set_perm_swap {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j n : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ xs.length) :
    ((listSwap xs i j (by omega) (by omega)).take n).Perm (xs.take n) := by
  have ht : (listSwap xs i j (by omega) (by omega)).take n =
      listSwap (xs.take n) i j (by rw [List.length_take_of_le hn]; omega)
        (by rw [List.length_take_of_le hn]; omega) := by
    apply List.ext_getElem?
    intro k
    have hlt_n : (xs.take n).length = n := List.length_take_of_le hn
    by_cases hk : k < n
    · simp only [List.getElem?_take_of_lt hk, listSwap]
      by_cases hkj : k = j
      · subst hkj
        rw [List.getElem?_set_self (by simp; omega),
          List.getElem?_set_self (by simp [hlt_n]; omega)]
        simp [List.getElem_take]
      · by_cases hki : k = i
        · subst hki
          rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_self (by omega),
            List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_self (by rw [hlt_n]; omega)]
          simp [List.getElem_take]
        · simp [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hki),
            List.getElem?_take_of_lt hk]
    · rw [List.getElem?_take]; simp only [hk, ↓reduceIte]
      rw [List.getElem?_eq_none]
      rw [listSwap_length, hlt_n]; omega
  rw [ht]
  exact listSwap_perm (xs.take n) _ _

/-! ## 4. LSD Radix-Pass Counting & Permutation Lemmas -/

@[expose] def rdxBkt (shift : Nat) (x : BitVec 64) : Nat :=
  ((x >>> shift) &&& 255#64).toNat

theorem rdxBkt_lt (shift : Nat) (x : BitVec 64) : rdxBkt shift x < 256 := by
  unfold rdxBkt
  have h1 : (((x >>> shift) &&& 255#64).toNat) ≤ 255 := by
    rw [BitVec.toNat_and, show (255#64 : BitVec 64).toNat = 255 from rfl]
    exact Nat.le_trans (Nat.and_le_right) (by decide)
  omega

@[expose] def rdxSeen (shift : Nat) (s_arr : List (BitVec 64)) (k b : Nat) : Nat :=
  ((s_arr.take k).filter (fun x => rdxBkt shift x == b)).length

theorem rdxSeen_zero (shift : Nat) (s_arr : List (BitVec 64)) (b : Nat) :
    rdxSeen shift s_arr 0 b = 0 := by
  simp [rdxSeen]

private theorem list_take_succ {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < xs.length := by simp at hi; omega
      change x :: xs.take (i + 1) = x :: (xs.take i ++ [xs[i]'hi'])
      rw [ih hi']

theorem rdxSeen_succ (shift : Nat) (s_arr : List (BitVec 64)) {i : Nat}
    (hi : i < s_arr.length) (b : Nat) :
    rdxSeen shift s_arr (i + 1) b =
      rdxSeen shift s_arr i b + (if rdxBkt shift s_arr[i] = b then 1 else 0) := by
  simp only [rdxSeen, list_take_succ s_arr hi, List.filter_append, List.length_append]
  by_cases hb : rdxBkt shift s_arr[i] = b <;> simp [hb]

theorem rdxSeen_mono (shift : Nat) (s_arr : List (BitVec 64)) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ s_arr.length) (b : Nat) :
    rdxSeen shift s_arr i b ≤ rdxSeen shift s_arr j b := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hle : i ≤ j
    · have := ih hle (by omega)
      rw [rdxSeen_succ shift s_arr (by omega) b]; omega
    · have : i = j + 1 := by omega
      subst this
      exact Nat.le_refl _

theorem rdxSeen_le_self (shift : Nat) (s_arr : List (BitVec 64)) (i b : Nat) :
    rdxSeen shift s_arr i b ≤ i := by
  unfold rdxSeen
  have h1 := List.length_filter_le (fun x => rdxBkt shift x == b) (s_arr.take i)
  simp only [List.length_take] at h1
  omega

@[expose] def rdxStart (tot : Nat → Nat) (b : Nat) : Nat :=
  ((List.range b).map tot).sum

theorem rdxStart_zero (tot : Nat → Nat) : rdxStart tot 0 = 0 := rfl

theorem rdxStart_succ (tot : Nat → Nat) (b : Nat) :
    rdxStart tot (b + 1) = rdxStart tot b + tot b := by
  simp [rdxStart, List.range_succ, List.sum_append]

theorem rdxStart_mono (tot : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    rdxStart tot a ≤ rdxStart tot b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a ≤ b
    · rw [rdxStart_succ]; exact Nat.le_trans (ih h) (Nat.le_add_right _ _)
    · have : a = b + 1 := by omega
      subst this
      exact Nat.le_refl _

private theorem list_filter_lt_succ (shift k : Nat) (l : List (BitVec 64)) :
    (l.filter (fun x => decide (rdxBkt shift x < k + 1))).length =
      (l.filter (fun x => decide (rdxBkt shift x < k))).length +
      (l.filter (fun x => rdxBkt shift x == k)).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    by_cases h1 : rdxBkt shift x < k
    · have h2 : rdxBkt shift x < k + 1 := by omega
      have h3 : (rdxBkt shift x == k) = false := by simp; omega
      simp [h1, h2, h3, ih]; omega
    · by_cases h2 : rdxBkt shift x = k
      · simp [h2, ih]; omega
      · have h3 : ¬ (rdxBkt shift x < k + 1) := by omega
        have h4 : (rdxBkt shift x == k) = false := by simp [h2]
        simp [h1, h3, h4, ih]

private theorem filter_false_nil {α : Type} (xs : List α) : xs.filter (fun _ => false) = [] := by
  induction xs <;> simp [*]

theorem rdxStart_sum_all (shift : Nat) (s_arr : List (BitVec 64)) {n : Nat}
    (hn : n ≤ s_arr.length) :
    rdxStart (fun b => rdxSeen shift s_arr n b) 256 = n := by
  have hgen : ∀ k : Nat, rdxStart (fun b => rdxSeen shift s_arr n b) k =
      ((s_arr.take n).filter (fun x => decide (rdxBkt shift x < k))).length := by
    intro k
    induction k with
    | zero => simp [rdxStart_zero, filter_false_nil]
    | succ k ih =>
      rw [rdxStart_succ, ih, list_filter_lt_succ]
      simp [rdxSeen]
  rw [hgen 256]
  have hall : (s_arr.take n).filter (fun x => decide (rdxBkt shift x < 256)) = s_arr.take n := by
    rw [List.filter_eq_self]
    intro x _; simp [rdxBkt_lt shift x]
  rw [hall, List.length_take_of_le hn]

private theorem list_take_add {α : Type} (xs : List α) (s t : Nat) :
    xs.take (s + t) = xs.take s ++ (xs.drop s).take t := by
  rw [← List.take_append_drop s (xs.take (s + t)), List.take_take,
    Nat.min_eq_left (Nat.le_add_right s t), List.drop_take, Nat.add_sub_cancel_left]

theorem rdx_flatMap_range_full (tot : Nat → Nat) (d_arr : List (BitVec 64)) (m : Nat)
    (hle : rdxStart tot m ≤ d_arr.length) :
    (List.range m).flatMap (fun b => (d_arr.drop (rdxStart tot b)).take (tot b)) =
      d_arr.take (rdxStart tot m) := by
  induction m with
  | zero => simp [rdxStart_zero]
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih (Nat.le_trans (rdxStart_mono tot (Nat.le_succ m)) hle),
      rdxStart_succ, list_take_add]

theorem rdx_slice_set_ne (d_arr : List (BitVec 64)) (x : BitVec 64) {p s k : Nat}
    (hdisj : p < s ∨ s + k ≤ p) :
    ((d_arr.set p x).drop s).take k = (d_arr.drop s).take k := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < k
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_drop,
      List.getElem?_drop, List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_take, List.getElem?_take]; simp [hi]

theorem rdx_slice_set_append (d_arr : List (BitVec 64)) (x : BitVec 64) {s k : Nat}
    (hp : s + k < d_arr.length) :
    ((d_arr.set (s + k) x).drop s).take (k + 1) = (d_arr.drop s).take k ++ [x] := by
  have hkd : k ≤ (d_arr.drop s).length := by simp [List.length_drop]; omega
  apply List.ext_getElem?; intro i
  by_cases hi : i < k
  · rw [List.getElem?_take_of_lt (by omega : i < k + 1), List.getElem?_drop,
      List.getElem?_set_ne (by omega)]
    rw [List.getElem?_append_left (by rw [List.length_take_of_le hkd]; exact hi),
      List.getElem?_take_of_lt hi, List.getElem?_drop]
  · by_cases hieq : i = k
    · subst hieq
      rw [List.getElem?_take_of_lt (Nat.lt_succ_self _), List.getElem?_drop,
        List.getElem?_set_self hp]
      rw [List.getElem?_append_right (by rw [List.length_take_of_le hkd]; exact Nat.le_refl _),
        List.length_take_of_le hkd, Nat.sub_self, List.getElem?_singleton]
      simp
    · rw [List.getElem?_take]; simp only [show ¬ (i < k + 1) by omega, ↓reduceIte]
      rw [List.getElem?_append_right (by rw [List.length_take_of_le hkd]; omega),
        List.length_take_of_le hkd]
      have hne0 : i - k ≠ 0 := by omega
      simp [hne0]

theorem rdx_flatMap_zero_count (shift : Nat) (s_arr d_arr : List (BitVec 64)) (n : Nat)
    (y : BitVec 64) :
    ((List.range 256).flatMap fun b =>
        (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take
          (rdxSeen shift s_arr 0 b)).count y =
      (s_arr.take 0).count y := by
  have hall : (List.range 256).flatMap (fun b =>
      (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take
        (rdxSeen shift s_arr 0 b)) = [] := by
    induction (List.range 256) with
    | nil => rfl
    | cons _ _ _ => simp [rdxSeen_zero]
  simp [hall]

theorem rdx_flatMap_count_step (shift : Nat) (s_arr d_arr : List (BitVec 64))
    {i n : Nat} (hi : i < n) (hn : n ≤ s_arr.length) (hd : n ≤ d_arr.length) (y : BitVec 64) :
    let tot := fun b => rdxSeen shift s_arr n b
    let x := s_arr[i]'(by omega)
    let bv := rdxBkt shift x
    let p := rdxStart tot bv + rdxSeen shift s_arr i bv
    let d' := d_arr.set p x
    ((List.range 256).flatMap fun b =>
        (d'.drop (rdxStart tot b)).take (rdxSeen shift s_arr (i + 1) b)).count y =
      ((List.range 256).flatMap fun b =>
        (d_arr.drop (rdxStart tot b)).take (rdxSeen shift s_arr i b)).count y +
        (if x == y then 1 else 0) := by
  intro tot x bv p d'
  have hbv_lt : bv < 256 := rdxBkt_lt shift x
  have hseen_lt : rdxSeen shift s_arr i bv < tot bv := by
    have h1 := rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv
    have h2 := rdxSeen_mono shift s_arr (by omega : i + 1 ≤ n) hn bv
    have hbv_eq : rdxBkt shift (s_arr[i]'(by omega)) = bv := rfl
    simp only [hbv_eq, ↓reduceIte] at h1; dsimp only [tot]; omega
  have hp_lt_next : p < rdxStart tot (bv + 1) := by simp only [rdxStart_succ, p]; omega
  have hp_lt_n : p < n := by
    have hle := rdxStart_mono tot (by omega : bv + 1 ≤ 256)
    rw [rdxStart_sum_all shift s_arr hn] at hle; omega
  have hgen : ∀ m, m ≤ 256 →
      ((List.range m).flatMap fun b =>
          (d'.drop (rdxStart tot b)).take (rdxSeen shift s_arr (i + 1) b)).count y =
        ((List.range m).flatMap fun b =>
          (d_arr.drop (rdxStart tot b)).take (rdxSeen shift s_arr i b)).count y +
          (if bv < m then (if x == y then 1 else 0) else 0) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.count_append,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append, ih (by omega)]
      by_cases hbm : bv = m'
      · subst hbm
        have hsucc : rdxSeen shift s_arr (i + 1) bv = rdxSeen shift s_arr i bv + 1 := by
          rw [rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv]
          simp [show rdxBkt shift s_arr[i] = bv from rfl]
        rw [hsucc, rdx_slice_set_append d_arr x (by dsimp only [p] at hp_lt_n; omega),
          List.count_append, List.count_singleton]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]; omega
      · have hsucc : rdxSeen shift s_arr (i + 1) m' = rdxSeen shift s_arr i m' := by
          rw [rdxSeen_succ shift s_arr (by omega : i < s_arr.length) m']
          simp [show rdxBkt shift s_arr[i] = bv from rfl, hbm]
        have hdisj : p < rdxStart tot m' ∨ rdxStart tot m' + rdxSeen shift s_arr i m' ≤ p := by
          by_cases hlt : bv < m'
          · left; have := rdxStart_mono tot (by omega : bv + 1 ≤ m'); omega
          · right
            have hle1 := rdxStart_mono tot (by omega : m' + 1 ≤ bv)
            have hle2 := rdxSeen_mono shift s_arr (by omega : i ≤ n) hn m'
            rw [rdxStart_succ] at hle1; dsimp only [p, tot] at *; omega
        rw [hsucc, rdx_slice_set_ne d_arr x hdisj]
        have hiff : (bv < m' + 1) ↔ (bv < m') := by omega
        by_cases hlt : bv < m'
        · simp [hlt, hiff.mpr hlt]; omega
        · simp [hlt, mt hiff.mp hlt]
  have h256 := hgen 256 (Nat.le_refl _)
  simpa [hbv_lt] using h256

theorem radix_pass_perm (shift : Nat) (s_arr d_arr : List (BitVec 64)) {n : Nat}
    (hn : n ≤ s_arr.length) (hd : n ≤ d_arr.length)
    (hcnt : ∀ y, ((List.range 256).flatMap fun b =>
        (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take
          (rdxSeen shift s_arr n b)).count y = (s_arr.take n).count y) :
    (d_arr.take n).Perm (s_arr.take n) := by
  rw [List.perm_iff_count]; intro y
  have hfull := rdx_flatMap_range_full (fun b => rdxSeen shift s_arr n b) d_arr 256
    (by rw [rdxStart_sum_all shift s_arr hn]; exact hd)
  rw [rdxStart_sum_all shift s_arr hn] at hfull
  rw [← hfull]; exact hcnt y

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
