/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.C0Agrees

import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Helpers, `u64`-in-`array32` Memory Rules & Upstream Bridges (`Proof.Walk.Helpers`)

Shared infrastructure for `LeanQbe.T.Examples.Kissat.Proof.Walk.Wp0`–`Wp3`:
1. `WalkMemTactics`: `@[scoped c0_load]` / `@[scoped c0_store]` rules for 64-bit reads and
   writes inside `scratch_buf` (`array32`), built on self-contained 32-bit pair-packing
   separation lemmas.
2. `WalkTblExpsOk`, `WalkScrPrefixPres`, `FullExtScratchPres`, and state-abstraction lemmas.
3. Clean `FullSparseInv` / `FullM6HdrInv` bridges for calling upstream verified specs
   (`arena_next`, `dense_bin_roundtrip_fid`, `watch_large_clauses_fid`, `next_dec_var`,
   `assign`, `propagate_beyond_m7`, `backtrack`, `walk_m7`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open Std.Sat
open Std.ExtHashMap
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
open LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open scoped FullArenaTactics
open scoped M6HdrTactics

/-! ## 1. `u64`-in-`array32` Separation Bridges & `WalkMemTactics` -/

private theorem pack64_toNat (x y : BitVec 32) :
    (pack64 x y).toNat = x.toNat + 2 ^ 32 * y.toNat := by
  unfold pack64
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : y.toNat * 2 ^ 32 < 2 ^ 64)]
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_or]
  by_cases hi : i < 32
  · have h1 : (y.toNat * 2 ^ 32).testBit i = false := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp; omega
    have h2 : (x.toNat + 2 ^ 32 * y.toNat).testBit i = x.toNat.testBit i := by
      rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx]; simp [hi]
    simp [h1, h2]
  · have h1 : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : (x.toNat + 2 ^ 32 * y.toNat).testBit i = y.toNat.testBit (i - 32) := by
      rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx]; simp [hi]
    have h3 : (y.toNat * 2 ^ 32).testBit i = y.toNat.testBit (i - 32) := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.not_lt.mp hi]
    simp [h1, h2, h3]

theorem pack64_lo_hi (v : BitVec 64) : pack64 (v.setWidth 32) ((v >>> 32).setWidth 32) = v := by
  apply BitVec.eq_of_toNat_eq; rw [pack64_toNat]
  have hv := v.isLt
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

private theorem bitvec_toBytes_byte {w : Nat} (b : BitVec w) (k : Nat) (hk : 8 * (k + 1) ≤ w) :
    ((b.toInt / ((256 : Int) ^ k)).take 8).toNat = (b.toNat / 256 ^ k) % 256 := by
  have hdiv : (2 : Int) ^ w = (2 : Int) ^ (w - 8 * k) * (256 : Int) ^ k := by
    rw [show (256 : Int) = (2 : Int) ^ 8 by decide, ← Int.pow_mul, ← Int.pow_add]; congr 1; omega
  have hpow : (2 : Int) ^ (w - 8 * k) = (2 : Int) ^ (w - 8 * k - 8) * 256 := by
    rw [show (256 : Int) = (2 : Int) ^ 8 by decide, ← Int.pow_add]; congr 1; omega
  have hbi : b.toInt = ↑b.toNat ∨ b.toInt = ↑b.toNat - (2 : Int) ^ w := by
    unfold BitVec.toInt; by_cases h : 2 * b.toNat < 2 ^ w <;> simp [h]
  have hpk : (256 : Int) ^ k ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have haux : (↑b.toNat / (256 : Int) ^ k % 256).toNat = b.toNat / 256 ^ k % 256 := by
    have hp : (256 : Int) ^ k = ↑(256 ^ k : Nat) := by simp
    have hm : (256 : Int) = ↑(256 : Nat) := rfl
    rw [hp, ← Int.natCast_ediv, hm, ← Int.natCast_emod, Int.toNat_natCast]
  simp only [Int.take, show (2 : Int) ^ 8 = 256 by decide]
  rcases hbi with heq | heq <;> rw [heq]
  · exact haux
  · have hmul : (↑b.toNat - (2 : Int) ^ w) / (256 : Int) ^ k =
        ↑b.toNat / (256 : Int) ^ k - (2 : Int) ^ (w - 8 * k) := by
      rw [hdiv]; exact Int.sub_mul_ediv_right _ _ hpk
    rw [hmul, hpow]
    have hmod : (↑b.toNat / (256 : Int) ^ k - (2 : Int) ^ (w - 8 * k - 8) * 256) % 256 =
        (↑b.toNat / (256 : Int) ^ k) % 256 := by
      have : (2 : Int) ^ (w - 8 * k - 8) * 256 = 256 * (2 : Int) ^ (w - 8 * k - 8) :=
        Int.mul_comm _ _
      omega
    rw [hmod]; exact haux

private theorem cell32_pair_eq_cell64 (a : BitVec 64) (x y : Val i32) :
    (cell a x ⋆ cell (a + 4) y) = cell64 a (pack64 x y) := by
  have hpxy := pack64_toNat x y
  have hdiv_step : ∀ (z : Int) (m : Nat),
      (z / (256 : Int) ^ m) / 256 = z / (256 : Int) ^ (m + 1) := by
    intro z m
    rw [Int.ediv_ediv]
    have hnn : 0 ≤ (256 : Int) ^ m := Int.pow_nonneg (by decide)
    have hnl : ¬ (256 : Int) ^ m < 0 := Int.not_lt.mpr hnn
    simp [hnl, Int.pow_succ]
  have hd2 : ∀ z : Int, z / 256 / 256 = z / (256 : Int) ^ 2 := fun z => by
    have h := hdiv_step z 1; rwa [Int.pow_one] at h
  have hd3 : ∀ z : Int, z / 256 / 256 / 256 = z / (256 : Int) ^ 3 := fun z => by
    rw [hd2 z]; exact hdiv_step z 2
  have hd4 : ∀ z : Int, z / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 4 := fun z => by
    rw [hd3 z]; exact hdiv_step z 3
  have hd5 : ∀ z : Int, z / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 5 := fun z => by
    rw [hd4 z]; exact hdiv_step z 4
  have hd6 : ∀ z : Int, z / 256 / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 6 :=
    fun z => by rw [hd5 z]; exact hdiv_step z 5
  have hd7 : ∀ z : Int, z / 256 / 256 / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 7 :=
    fun z => by rw [hd6 z]; exact hdiv_step z 6
  have hbytes : Int.toBytes 4 x.toInt ++ Int.toBytes 4 y.toInt =
      Int.toBytes 8 (pack64 x y).toInt := by
    simp only [Int.toBytes.eq_2, Int.toBytes.eq_1, List.cons_append, List.nil_append,
      List.cons.injEq, and_true]
    rw [hd7 (pack64 x y).toInt, hd6 (pack64 x y).toInt, hd5 (pack64 x y).toInt,
      hd4 (pack64 x y).toInt, hd3 (pack64 x y).toInt, hd2 (pack64 x y).toInt,
      hd3 x.toInt, hd2 x.toInt, hd3 y.toInt, hd2 y.toInt]
    have h0 := bitvec_toBytes_byte x 0 (by decide)
    have h1 := bitvec_toBytes_byte x 1 (by decide)
    have h2 := bitvec_toBytes_byte x 2 (by decide)
    have h3 := bitvec_toBytes_byte x 3 (by decide)
    have g0 := bitvec_toBytes_byte y 0 (by decide)
    have g1 := bitvec_toBytes_byte y 1 (by decide)
    have g2 := bitvec_toBytes_byte y 2 (by decide)
    have g3 := bitvec_toBytes_byte y 3 (by decide)
    have p0 := bitvec_toBytes_byte (pack64 x y) 0 (by decide)
    have p1 := bitvec_toBytes_byte (pack64 x y) 1 (by decide)
    have p2 := bitvec_toBytes_byte (pack64 x y) 2 (by decide)
    have p3 := bitvec_toBytes_byte (pack64 x y) 3 (by decide)
    have p4 := bitvec_toBytes_byte (pack64 x y) 4 (by decide)
    have p5 := bitvec_toBytes_byte (pack64 x y) 5 (by decide)
    have p6 := bitvec_toBytes_byte (pack64 x y) 6 (by decide)
    have p7 := bitvec_toBytes_byte (pack64 x y) 7 (by decide)
    rw [Int.pow_zero, Int.ediv_one, Nat.pow_zero, Nat.div_one] at h0 g0 p0
    rw [Int.pow_one, Nat.pow_one] at h1 g1 p1
    rw [hpxy] at p0 p1 p2 p3 p4 p5 p6 p7
    have hx := x.isLt; have hy := y.isLt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply congrArg Nat.toUInt8
    · rw [h0, p0]; omega
    · rw [h1, p1]; omega
    · rw [h2, p2]; omega
    · rw [h3, p3]; omega
    · rw [g0, p4]; omega
    · rw [g1, p5]; omega
    · rw [g2, p6]; omega
    · rw [g3, p7]; omega
  have heq1 : cell (t := i32) a x = Eq ((Int.toBytes 4 x.toInt).At a) := rfl
  have heq2 : cell (t := i32) (a + 4) y = Eq ((Int.toBytes 4 y.toInt).At (a + 4)) := rfl
  have heq3 : cell64 a (pack64 x y) = Eq ((Int.toBytes 8 (pack64 x y).toInt).At a) := rfl
  rw [heq1, heq2, heq3, ← hbytes, Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
  simp [Int.toBytes_length]

private theorem array32_focus_pair_any (a : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (4 * i)) (pack64 xs[i] xs[i + 1]) ⋆
        (array (t := i32) a (xs.take i) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2)))) := by
  have hf := LeanQbe.T.array_slice_focus (t := i32) a xs (off := i) (len := 2) (by omega)
  have htd : List.take 2 (List.drop i xs) = [xs[i], xs[i + 1]] := by
    apply List.ext_getElem
    · simp; omega
    · intro k hk1 hk2
      rcases (by simp at hk1; omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp
  have hmul : i32.bytes = 4 := rfl
  have h8 : BitVec.ofNat 64 (4 * (i + 2)) = BitVec.ofNat 64 (4 * i) + 8 := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [hmul, htd, h8] at hf
  simp only [array, sep_emp, hmul] at hf
  rw [show (BitVec.ofNat 64 4 : BitVec 64) = 4 from rfl, ← sep_assoc,
    cell32_pair_eq_cell64] at hf
  simpa [BitVec.add_assoc, sep_assoc] using hf

private theorem array32_set_pair_any (a : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) (x y : Val i32) :
    array (t := i32) a ((xs.set i x).set (i + 1) y) =
      (cell64 (a + BitVec.ofNat 64 (4 * i)) (pack64 x y) ⋆
        (array (t := i32) a (xs.take i) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2)))) := by
  have hi_len : i + 1 < ((xs.set i x).set (i + 1) y).length := by simp [hi]
  have hf := array32_focus_pair_any a ((xs.set i x).set (i + 1) y) hi_len
  have htake : ((xs.set i x).set (i + 1) y).take i = xs.take i := by
    rw [List.take_set_of_le (by omega), List.take_set_of_le (Nat.le_refl _)]
  have hdrop : ((xs.set i x).set (i + 1) y).drop (i + 2) = xs.drop (i + 2) := by
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have hx : ((xs.set i x).set (i + 1) y)[i]'(by omega) = x := by
    rw [List.getElem_set_ne (by omega), List.getElem_set_self]
  have hy : ((xs.set i x).set (i + 1) y)[i + 1]'hi_len = y := List.getElem_set_self (by simp [hi])
  rw [hf, hx, hy, htake, hdrop]

private theorem array32_focus_pair_ptr (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr) (hp8 : ptr + 8 = ptr8) :
    array (t := i32) a xs =
      (cell64 ptr (pack64 xs[i] xs[i + 1]) ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hp; subst hp8; exact array32_focus_pair_any a xs hi

private theorem array32_set_pair_ptr (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr) (hp8 : ptr + 8 = ptr8)
    (x y : Val i32) :
    array (t := i32) a ((xs.set i x).set (i + 1) y) =
      (cell64 ptr (pack64 x y) ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hp; subst hp8; exact array32_set_pair_any a xs hi x y

private theorem array32_set_pair_pack (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i j : Nat}
    (hj : j = i + 1) (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr)
    (hp8 : ptr + 8 = ptr8) (v : BitVec 64) :
    array (t := i32) a ((xs.set i (v.setWidth 32)).set j ((v >>> 32).setWidth 32)) =
      (cell64 ptr v ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hj
  rw [array32_set_pair_ptr a ptr ptr8 xs hi hp hp8, pack64_lo_hi v]

theorem mem_array32_load64 {p ptr : BitVec 64} {xs : List (BitVec 32)}
    {rest : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i + 1 < xs.length) (hp : p + BitVec.ofNat 64 (4 * i) = ptr)
    (hm : (array (t := i32) p xs ⋆ rest) m) :
    loadVal m i64 ptr = some (pack64 xs[i] xs[i + 1]) := by
  rw [array32_focus_pair_ptr p ptr (ptr + 8) xs hi hp rfl, sep_assoc] at hm
  exact loadVal_cell64 hm

theorem mem_array32_store64 {p ptr : BitVec 64} {xs : List (BitVec 32)}
    {rest : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i + 1 < xs.length) (hp : p + BitVec.ofNat 64 (4 * i) = ptr)
    (hm : (array (t := i32) p xs ⋆ rest) m) :
    storeOk m i64 ptr ∧
      (array (t := i32) p ((xs.set i (v.setWidth 32)).set (i + 1) ((v >>> 32).setWidth 32))
        ⋆ rest) (storeMem m i64 ptr v) := by
  rw [array32_focus_pair_ptr p ptr (ptr + 8) xs hi hp rfl, sep_assoc] at hm
  obtain ⟨hok, hst⟩ := store_cell64 v hm
  rw [← sep_assoc, ← array32_set_pair_pack p ptr (ptr + 8) xs rfl hi hp rfl v] at hst
  exact ⟨hok, hst⟩

theorem full_sb_load64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} {ptr : BitVec 64} (hi : i + 1 < s.scratch.scratch_buf.length)
    (hp : c.pScratchBuf + BitVec.ofNat 64 (4 * i) = ptr) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 ptr = some (pack64 s.scratch.scratch_buf[i] s.scratch.scratch_buf[i + 1]) :=
  mem_array32_load64 hi hp (ArrayField.focus .scratch_buf hm)

theorem full_sb_store64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} {ptr : BitVec 64} (v : BitVec 64)
    (hi : i + 1 < s.scratch.scratch_buf.length)
    (hp : c.pScratchBuf + BitVec.ofNat 64 (4 * i) = ptr) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 ptr ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set i (v.setWidth 32)).set (i + 1)
          ((v >>> 32).setWidth 32) } } ⋆ R) (storeMem m i64 ptr v) := by
  obtain ⟨hok, hst⟩ := mem_array32_store64 v hi hp (ArrayField.focus .scratch_buf hm)
  exact ⟨hok, ArrayField.unfocus .scratch_buf hst⟩

theorem full_wk2_load64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} {ptr : BitVec 64} (hi : i + 1 < s.scratch.work_stk2.length)
    (hp : c.pWorkStk2 + BitVec.ofNat 64 (4 * i) = ptr) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 ptr = some (pack64 s.scratch.work_stk2[i] s.scratch.work_stk2[i + 1]) :=
  mem_array32_load64 hi hp (ArrayField.focus .work_stk2 hm)

theorem full_wk2_store64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} {ptr : BitVec 64} (v : BitVec 64)
    (hi : i + 1 < s.scratch.work_stk2.length)
    (hp : c.pWorkStk2 + BitVec.ofNat 64 (4 * i) = ptr) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 ptr ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := (s.scratch.work_stk2.set i (v.setWidth 32)).set (i + 1)
          ((v >>> 32).setWidth 32) } } ⋆ R) (storeMem m i64 ptr v) := by
  obtain ⟨hok, hst⟩ := mem_array32_store64 v hi hp (ArrayField.focus .work_stk2 hm)
  exact ⟨hok, ArrayField.unfocus .work_stk2 hst⟩

namespace WalkMemTactics

@[scoped c0_load low] theorem c0_load_full_scratch_buf64_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : BitVec 64} (hd : d.toNat % 4 = 0)
    (hi : d.toNat / 4 + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + d) =
      some (pack64 s.scratch.scratch_buf[d.toNat / 4]
        s.scratch.scratch_buf[d.toNat / 4 + 1]) :=
  full_sb_load64 hi (by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load] theorem c0_load_full_scratch_buf64_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 c.pScratchBuf =
      some (pack64 s.scratch.scratch_buf[0] s.scratch.scratch_buf[1]) :=
  full_sb_load64 hi (by simp) hm

@[scoped c0_load] theorem c0_load_full_scratch_buf64_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + i * 8) =
      some (pack64 s.scratch.scratch_buf[2 * i.toNat] s.scratch.scratch_buf[2 * i.toNat + 1]) :=
  full_sb_load64 hi (by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load] theorem c0_load_full_scratch_buf64_shl3 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + (i <<< (3 : Nat))) =
      some (pack64 s.scratch.scratch_buf[2 * i.toNat] s.scratch.scratch_buf[2 * i.toNat + 1]) :=
  full_sb_load64 hi (by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load] theorem c0_load_full_scratch_buf64_add8 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 3 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pScratchBuf + i * 8 + 8) =
      some (pack64 s.scratch.scratch_buf[2 * i.toNat + 2]
        s.scratch.scratch_buf[2 * i.toNat + 3]) :=
  full_sb_load64 hi (by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store low] theorem c0_store_full_scratch_buf64_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : BitVec 64} (v : BitVec 64)
    (hd : d.toNat % 4 = 0) (hi : d.toNat / 4 + 1 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + d) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set (d.toNat / 4) (v.setWidth 32)).set
          (d.toNat / 4 + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + d) v) :=
  full_sb_store64 v hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store] theorem c0_store_full_scratch_buf64_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 c.pScratchBuf ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set 0 (v.setWidth 32)).set 1
          ((v >>> 32).setWidth 32) } } ⋆ R) (storeMem m i64 c.pScratchBuf v) :=
  full_sb_store64 v hi (by simp) hm

@[scoped c0_store] theorem c0_store_full_scratch_buf64_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + i * 8) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set (2 * i.toNat) (v.setWidth 32)).set
          (2 * i.toNat + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + i * 8) v) :=
  full_sb_store64 v hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store] theorem c0_store_full_scratch_buf64_shl3 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + (i <<< (3 : Nat))) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set (2 * i.toNat) (v.setWidth 32)).set
          (2 * i.toNat + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + (i <<< (3 : Nat))) v) :=
  full_sb_store64 v hi (by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store] theorem c0_store_full_scratch_buf64_add8 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 3 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pScratchBuf + i * 8 + 8) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set (2 * i.toNat + 2) (v.setWidth 32)).set
          (2 * i.toNat + 3) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pScratchBuf + i * 8 + 8) v) :=
  full_sb_store64 v hi (by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load low] theorem c0_load_full_work_stk264_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : BitVec 64} (hd : d.toNat % 4 = 0)
    (hi : d.toNat / 4 + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWorkStk2 + d) =
      some (pack64 s.scratch.work_stk2[d.toNat / 4] s.scratch.work_stk2[d.toNat / 4 + 1]) :=
  full_wk2_load64 hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load] theorem c0_load_full_work_stk264_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 c.pWorkStk2 =
      some (pack64 s.scratch.work_stk2[0] s.scratch.work_stk2[1]) :=
  full_wk2_load64 hi (by simp) hm

@[scoped c0_load] theorem c0_load_full_work_stk264_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWorkStk2 + i * 8) =
      some (pack64 s.scratch.work_stk2[2 * i.toNat] s.scratch.work_stk2[2 * i.toNat + 1]) :=
  full_wk2_load64 hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_load] theorem c0_load_full_work_stk264_shl3 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWorkStk2 + (i <<< (3 : Nat))) =
      some (pack64 s.scratch.work_stk2[2 * i.toNat] s.scratch.work_stk2[2 * i.toNat + 1]) :=
  full_wk2_load64 hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store low] theorem c0_store_full_work_stk264_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : BitVec 64} (v : BitVec 64)
    (hd : d.toNat % 4 = 0) (hi : d.toNat / 4 + 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWorkStk2 + d) ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := (s.scratch.work_stk2.set (d.toNat / 4) (v.setWidth 32)).set
          (d.toNat / 4 + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWorkStk2 + d) v) :=
  full_wk2_store64 v hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store] theorem c0_store_full_work_stk264_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 c.pWorkStk2 ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := (s.scratch.work_stk2.set 0 (v.setWidth 32)).set 1
          ((v >>> 32).setWidth 32) } } ⋆ R) (storeMem m i64 c.pWorkStk2 v) :=
  full_wk2_store64 v hi (by simp) hm

@[scoped c0_store] theorem c0_store_full_work_stk264_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWorkStk2 + i * 8) ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := (s.scratch.work_stk2.set (2 * i.toNat) (v.setWidth 32)).set
          (2 * i.toNat + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWorkStk2 + i * 8) v) :=
  full_wk2_store64 v hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

@[scoped c0_store] theorem c0_store_full_work_stk264_shl3 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : 2 * i.toNat + 1 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWorkStk2 + (i <<< (3 : Nat))) ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk2 := (s.scratch.work_stk2.set (2 * i.toNat) (v.setWidth 32)).set
          (2 * i.toNat + 1) ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWorkStk2 + (i <<< (3 : Nat))) v) :=
  full_wk2_store64 v hi (by congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) hm

end WalkMemTactics

/-! ## 2. `WalkTblExpsOk`, `WalkScrPrefixPres`, Lengths & State Abstraction -/

theorem walkTblExpsOk_iff (s : FullState) :
    WalkTblExpsOk s ↔
      (pack64 (s.scratch.scratch_buf[2160]?.getD 0#32)
        (s.scratch.scratch_buf[2161]?.getD 0#32)).toNat ≤ 1080 :=
  Iff.rfl

theorem walkScrPrefixPres_refl (s : FullState) : WalkScrPrefixPres s s :=
  fun _ _ => rfl

theorem walkScrPrefixPres_trans {s1 s2 s3 : FullState}
    (h1 : WalkScrPrefixPres s1 s2) (h2 : WalkScrPrefixPres s2 s3) :
    WalkScrPrefixPres s1 s3 :=
  fun j hj => (h2 j hj).trans (h1 j hj)

theorem walkScrPrefixPres_set_ge {s : FullState} {k : Nat} (hk : 2200 ≤ k) (v : BitVec 32) :
    WalkScrPrefixPres s
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set k v } } :=
  fun j hj => List.getElem?_set_ne (by omega)

theorem walkScrPrefixPres_tblExpsOk {s s' : FullState}
    (hpre : WalkScrPrefixPres s s') (hok : WalkTblExpsOk s) : WalkTblExpsOk s' := by
  unfold WalkTblExpsOk at hok ⊢
  rw [hpre 2160 (by decide), hpre 2161 (by decide)]
  exact hok

theorem walkTblExpsOk_of_store1080 {s : FullState} {v : BitVec 64}
    (h2161 : 2161 < s.scratch.scratch_buf.length) (hv : v.toNat ≤ 1080) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := (s.scratch.scratch_buf.set 2160 (v.setWidth 32)).set 2161
        ((v >>> 32).setWidth 32) } } := by
  rw [walkTblExpsOk_iff]
  have hlen1 : 2161 < (s.scratch.scratch_buf.set 2160 (v.setWidth 32)).length := by
    simp; exact h2161
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self hlen1, Option.getD_some, Option.getD_some, pack64_lo_hi]
  exact hv

theorem walkTblExpsOk_store_ne1080 {s : FullState} {k : Nat} (v : BitVec 64)
    (hne : k + 1 < 2160 ∨ 2161 < k) (hok : WalkTblExpsOk s) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := (s.scratch.scratch_buf.set k (v.setWidth 32)).set (k + 1)
        ((v >>> 32).setWidth 32) } } := by
  unfold WalkTblExpsOk at hok ⊢
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hok

theorem walkTblExpsOk_of_sb {s : FullState}
    (h : (pack64 (s.scratch.scratch_buf[2160]?.getD 0#32)
      (s.scratch.scratch_buf[2161]?.getD 0#32)).toNat ≤ 1080) : WalkTblExpsOk s := h

theorem walkTblExps_sb_set_ne {sb : List (BitVec 32)} {k : Nat} (w : BitVec 32)
    (hk0 : k ≠ 2160) (hk1 : k ≠ 2161)
    (h : (pack64 (sb[2160]?.getD 0#32) (sb[2161]?.getD 0#32)).toNat ≤ 1080) :
    (pack64 ((sb.set k w)[2160]?.getD 0#32) ((sb.set k w)[2161]?.getD 0#32)).toNat ≤
      1080 := by
  rwa [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem walkTblExps_sb_set64_1080 (sb : List (BitVec 32)) {v : BitVec 64}
    (h2161 : 2161 < sb.length) (hv : v.toNat ≤ 1080) :
    (pack64
      (((sb.set 2160 (v.setWidth 32)).set 2161 ((v >>> 32).setWidth 32))[2160]?.getD 0#32)
      (((sb.set 2160 (v.setWidth 32)).set 2161 ((v >>> 32).setWidth 32))[2161]?.getD 0#32)).toNat ≤
      1080 := by
  have hlen1 : 2161 < (sb.set 2160 (v.setWidth 32)).length := by simp; exact h2161
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self hlen1, Option.getD_some, Option.getD_some, pack64_lo_hi]
  exact hv

theorem walkTblExps_sb_set64_imm (sb : List (BitVec 32)) {d v : BitVec 64}
    (hd : d.toNat / 4 = 2160) (h2161 : 2161 < sb.length) (hv : v.toNat ≤ 1080) :
    (pack64
      (((sb.set (d.toNat / 4) (v.setWidth 32)).set (d.toNat / 4 + 1)
        ((v >>> 32).setWidth 32))[2160]?.getD 0#32)
      (((sb.set (d.toNat / 4) (v.setWidth 32)).set (d.toNat / 4 + 1)
        ((v >>> 32).setWidth 32))[2161]?.getD 0#32)).toNat ≤ 1080 := by
  rw [hd, show (2160 : Nat) + 1 = 2161 from rfl]
  exact walkTblExps_sb_set64_1080 sb h2161 hv

theorem walkTblExpsOk_cb_tbl {s : FullState} {sb0 : List (BitVec 32)}
    {k0 k1 k2 k3 k4 k5 : Nat} {w0 w1 w2 w3 w4 w5 : BitVec 32}
    (hsb : s.scratch.scratch_buf =
      (((((sb0.set k0 w0).set k1 w1).set k2 w2).set k3 w3).set k4 w4).set k5 w5)
    (hk0 : k0 = 2160) (hk1 : k1 = 2161)
    (hne : k2 ≠ 2160 ∧ k2 ≠ 2161 ∧ k3 ≠ 2160 ∧ k3 ≠ 2161 ∧
      k4 ≠ 2160 ∧ k4 ≠ 2161 ∧ k5 ≠ 2160 ∧ k5 ≠ 2161)
    (hlen : 2161 < sb0.length) (hle : (pack64 w0 w1).toNat ≤ 1080) :
    WalkTblExpsOk s := by
  rw [walkTblExpsOk_iff, hsb, hk0, hk1]
  obtain ⟨h20, h21, h30, h31, h40, h41, h50, h51⟩ := hne
  rw [List.getElem?_set_ne h50, List.getElem?_set_ne h40,
    List.getElem?_set_ne h30, List.getElem?_set_ne h20,
    List.getElem?_set_ne h51, List.getElem?_set_ne h41,
    List.getElem?_set_ne h31, List.getElem?_set_ne h21]
  have hl0 : 2161 < (sb0.set 2160 w0).length := by simp; exact hlen
  rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega),
    List.getElem?_set_self hl0, Option.getD_some, Option.getD_some]
  exact hle

theorem walkTblExpsOk_to_lt1080 {s : FullState} (hok : WalkTblExpsOk s)
    {hi_len : 2161 < s.scratch.scratch_buf.length} :
    (pack64 s.scratch.scratch_buf[2160] s.scratch.scratch_buf[2161]).toNat ≤ 1080 := by
  rw [walkTblExpsOk_iff] at hok
  simpa [hi_len, show 2160 < s.scratch.scratch_buf.length by omega] using hok

theorem walk_state_abs {c : FullCfg} {s₀ s₁ s_next : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s₁ ⋆ R) m) (heq : s₁ = s_next)
    (hcore : s_next.core = s₀.core) (hlen : s_next.LengthsOk c)
    (hext : FullExtScratchPres s₀ s_next) (hpre : WalkScrPrefixPres s₀ s_next) :
    ∃ st : FullState, st.core = s₀.core ∧ st.LengthsOk c ∧
      FullExtScratchPres s₀ st ∧ WalkScrPrefixPres s₀ st ∧ (FullMem c st ⋆ R) m :=
  ⟨s_next, hcore, hlen, hext, hpre, heq ▸ hm⟩

theorem bv64_shl1_toNat_lt {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt h]

theorem bv32_lit_toNat_mod64 (lit : BitVec 32) : (lit.setWidth 64).toNat = lit.toNat := by
  have h := lit.isLt
  simp [BitVec.toNat_setWidth]; omega

theorem fullExtScratchPres_of_eq {s s' : FullState}
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len) : FullExtScratchPres s s' :=
  ⟨hll, hel⟩

/-! ## 3. Cross-Segment Call & `FullSparseInv` / `FullM6HdrInv` Bridges -/

theorem fullSparseInv_of_fields {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hnd' : FullArenaVarsNodup s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlmk : s'.core.lit_mark = s.core.lit_mark)
    (hdm' : s'.core.dense_mode = 0#64) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len)
    (hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullSparseInv c F0 s' := by
  obtain ⟨_, ⟨hm, hlm⟩, _, ⟨hll0, hel0⟩, _⟩ := hsp
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨fun v hv => by rw [hmrk]; exact hm v hv,
    fun l hl => by rw [hlmk]; exact hlm l hl⟩, hnd', ⟨?_, by rw [hel]; exact hel0⟩, hdm'⟩
  intro i hi; dsimp only; unfold FullLastLearnedWf at hll0; rw [hll]
  exact (hll0 i hi).imp id (hrefs _)

theorem fullArenaVarsNodup_of_permEq {s s' : FullState}
    (hnd : FullArenaVarsNodup s) (hap : FullArenaPermEq s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  have hr0 : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1] at hr
  obtain ⟨_, hgb, hpm⟩ := hap.2.2 r hr0
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
  unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hnd r hr0 hng0)

theorem walk_call_arena_next {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32]} {k : Tup Val [i32] → Expr Val Cont rs}
    (hAn : Γ.Has "full_arena_next" fullArenaNextSpec)
    {c : FullCfg} {s : FullState} {cref : BitVec 32} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, cref, ())) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : wp Γ Q X (k (BitVec.ofNat 32
      (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ())) m) :
    wp Γ Q X (.call "full_arena_next" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hAn _ _ _ _ ⟨c, s, R, rfl, hlen, hm, hk⟩

theorem walk_call_bin_roundtrip {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hBin : Γ.Has "full_dense_bin_roundtrip_fid" fullDenseBinRoundtripFidSpec)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_dense_bin_roundtrip_fid" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  obtain ⟨F_cur, hlen, hw, hlm, hnd, hext, hdm⟩ := hsp.exists_witness
  exact hBin _ _ _ _
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, fun s' m'
      hlen' hw' hlm' hnd' hext' hcv' hcl' hdm' _ _ _ _ _ hfu' _ _ _ _ _ _ _ hpr' hap'
      hel' _ _ hll' hm' =>
    hk s' m' ⟨⟨hlen', F_cur, hw'⟩, hlm', hnd', hext', hdm'.trans hdm⟩
      hap' hcv' hcl' hfu' hpr' ⟨hll', hel'⟩ hm'⟩

theorem walk_call_watch_large {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hLarge : Γ.Has "full_watch_large_clauses_fid" fullWatchLargeClausesSpec)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_watch_large_clauses_fid" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  obtain ⟨F_cur, hlen, hw, hlm, hnd, hext, hdm⟩ := hsp.exists_witness
  exact hLarge _ _ _ _
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm, fun s' m'
      hlen' hw' hlm' hnd' hext' hcv' hcl' hdm' _ _ _ _ hfu' _ _ _ hpr' hap'
      hel' _ _ hll' hm' =>
    hk s' m' ⟨⟨hlen', F_cur, hw'⟩, hlm', hnd', hext', hdm'.trans hdm⟩
      hap' hcv' hcl' hfu' hpr' ⟨hll', hel'⟩ hm'⟩

theorem walk_fullContract_of_safetySlice {extraArgs rs : List Ty}
    {K : FullContract extraArgs rs PUnit} {xs : Tup Val (i64 :: extraArgs)}
    {m : Mem 64} {Q : Post rs} {X : XPost} (h : K.toSpec xs m Q X)
    (pre : FullCfg → Tup Val (i64 :: extraArgs) → FullState → Prop)
    (post : FullCfg → Tup Val (i64 :: extraArgs) → Tup Val rs → FullState → FullState → Prop)
    (hPre : ∀ c h a s, K.pre c s a PUnit.unit → h = c.hdr → pre c (h, a) s)
    (hPost : ∀ c h a r s s', s'.core = s.core → s'.LengthsOk c →
      post c (h, a) r s s' → K.post c s a PUnit.unit r s') :
    SafetySlice.spec fullSafetySlice pre post xs m Q X := by
  rcases xs with ⟨h0, args⟩
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, hp, hm, hQ⟩ := FullContract.elim h
  exact ⟨c, s, R, hPre c c.hdr args s hp rfl, hlen, hm,
    fun r s' m' hc hl hpo hm' => hQ r s' m' hl (hPost c c.hdr args r s s' hc hl hpo) hm'⟩

theorem walk_m6_frame_walk_m7 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hWm7 : Γ.Has "full_walk_m7" walkCoreSpec)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hinv : FullM6HdrInv c F0 ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m',
      FullM6HdrInv c F0 ext s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hWm7 _ _ _ _ ?_
  dsimp only [walkCoreSpec]
  refine FullContract.intro hinv.sparse.lengths hinv.sparse (fullM6HdrMem_focus_full hm)
    fun () s' m' _ ⟨hsp', hap, hcv, hcl, hfu, hpr, hext⟩ hm' => ?_
  exact hk s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hap hcv hcl hfu hpr hext
    (fullM6HdrMem_unfocus_full hm')

theorem walk_call_next_dec_var_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hNdv : Γ.Has "full_next_dec_var" nextDecVarSpec)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hinv : FullM6HdrInv c F0 ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) s' m',
      FullM6HdrInv c F0 ext s' → s'.core = s.core → FullExtScratchPres s s' →
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_next_dec_var" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hNdv _ _ _ _ ?_
  dsimp only [nextDecVarSpec]
  refine FullContract.intro (w := ()) hinv.sparse.lengths trivial (fullM6HdrMem_focus_full hm) ?_
  rintro ⟨r, ⟨⟩⟩ s' m' hs' ⟨hc', hext', hr⟩ hm'
  have hextOk := FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 hext'
    (fun _ ha => by unfold fullArenaClauseRefs fullArenaClauseRefsCore at ha ⊢; rwa [hc'])
  have hinv' := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk (hinv.sparse.with_scratch hs' hc' hextOk)
  exact hk r s' m' hinv' hc' hext' hr (fullM6HdrMem_unfocus_full hm')

theorem fullArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

theorem fullArenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr => ?_⟩
  have hr2 : r ∈ fullArenaClauseRefsCore k2 := by rwa [h1.2.1]
  obtain ⟨hsz1, hgb1, hpm1⟩ := h1.2.2 r hr
  obtain ⟨hsz2, hgb2, hpm2⟩ := h2.2.2 r hr2
  exact ⟨hsz2.trans hsz1, hgb2.trans hgb1, hpm2.trans hpm1⟩

theorem walk_call_backtrack_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {tlvl : BitVec 64} (hargs : vals args = (c.hdr, tlvl, ()))
    (hinv : FullM6HdrInv c F0 ext s) (htlvl : tlvl.toNat ≤ s.core.cur_level)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m',
      FullM6HdrInv c F0 ext s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = min s.core.cur_level tlvl.toNat →
      s'.core.trail_end ≤ s.core.trail_end → s'.core.fuel = s.core.fuel →
      s'.core.probing = s.core.probing → FullExtScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_backtrack" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have hmxc := c.hmaxv; unfold dimacsBound at hmxc
    have hcl_le := hw.cur_level_le; have hte_le := hsp.lengths.core_ok.trail_end_le
    have hcv := hsp.lengths.core_ok.cur_vars_le; omega
  have htlvl_lt : tlvl.toNat < s.core.cur_level → tlvl.toNat < c.max_vars := fun hlt => by
    have hcl_le := hw.cur_level_le; have hte_le := hsp.lengths.core_ok.trail_end_le
    have hcv := hsp.lengths.core_ok.cur_vars_le; omega
  refine hBt _ _ _ _
    ⟨c, s, _, rfl, hsp.lengths, hcl_lt, htlvl_lt, hw.trail_lits_lt,
      fullM6HdrMem_focus_full hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
        hlen' hte' _ hcl' hpr' _ _ _ hw' _ hm' => ?_⟩
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' }
      scratch := sc' }
  have hsp' : FullSparseInv c F0 s' :=
    fullSparseInv_of_fields hsp hlen' (hw' F0 F_cur hw htlvl) hsp.2.2.1 rfl rfl
      hsp.2.2.2.2 hpr'.1.1 hpr'.1.2 (fun _ hr => hr)
  exact hk s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') (fullArenaPermEq_refl _)
    rfl hcl' hte' rfl rfl hpr'.1 (fullM6HdrMem_unfocus_full hm')

theorem walk_call_propagate_beyond_m7_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hProp : Γ.Has "full_propagate_beyond_m7" propagateBeyondM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hinv : FullM6HdrInv c F0 ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) ext' s' m',
      FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.probing = s.core.probing → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate_beyond_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  exact hProp _ _ _ _
    ⟨c, F0, F_cur, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hsp.lengths, hw, hsp.2.2.2.2, hm,
      fun r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
        wlen' wu' fuel' oom' sc' m' hext' _ hlen' hw' _ _ hap' hpr' _ _ _ _ hfu' hdom' hr0
        _ _ hm' =>
    let s' : FullState :=
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', oom := oom' }
        scratch := sc' }
    have hnd' : FullArenaVarsNodup s' := fullArenaVarsNodup_of_permEq hsp.2.2.1 hap'
    have hextPres : FullExtScratchPres s s' := hpr'.1
    have hsp' : FullSparseInv c F0 s' :=
      fullSparseInv_of_fields hsp hlen' hw' hnd' rfl rfl hsp.2.2.2.2 hextPres.1 hextPres.2
        (fun ref href => by unfold fullArenaClauseRefs at href ⊢; rwa [hap'.2.1])
    hk r ext' s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hext' hsp') hap' rfl rfl rfl hfu' hdom'
      (fun heq => ⟨(hr0 heq).1, (hr0 heq).2.2⟩) hextPres hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Walk
