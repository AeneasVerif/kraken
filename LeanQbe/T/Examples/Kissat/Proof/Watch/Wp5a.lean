/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0HeadStep

/-! # Watch WP Helpers Part 5a: 64-bit `wstk` Bridges, Layout & Slice Deletion

Reusable 64-bit `wstk` `c0_load`/`c0_store` bridges (`pack64`), `WatchStackLayout` shrinking,
and entry-boundary deletion lemmas for `WatchSliceOk` / `DenseWatchSliceOk` used by `Wp5` and `Wp6`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

theorem pack64_toNat (x y : BitVec 32) :
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

theorem cell32_pair_eq_cell64 (a : BitVec 64) (x y : Val i32) :
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

theorem array32_focus_pair_any (a : BitVec 64) (xs : List (Val i32)) {i : Nat}
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

theorem array32_set_pair_any (a : BitVec 64) (xs : List (Val i32)) {i : Nat}
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

theorem array32_focus_pair_ptr (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr) (hp8 : ptr + 8 = ptr8) :
    array (t := i32) a xs =
      (cell64 ptr (pack64 xs[i] xs[i + 1]) ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hp; subst hp8; exact array32_focus_pair_any a xs hi

theorem array32_set_pair_ptr (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i : Nat}
    (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr) (hp8 : ptr + 8 = ptr8)
    (x y : Val i32) :
    array (t := i32) a ((xs.set i x).set (i + 1) y) =
      (cell64 ptr (pack64 x y) ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hp; subst hp8; exact array32_set_pair_any a xs hi x y

theorem array32_set_pair_pack (a ptr ptr8 : BitVec 64) (xs : List (Val i32)) {i j : Nat}
    (hj : j = i + 1) (hi : i + 1 < xs.length) (hp : a + BitVec.ofNat 64 (4 * i) = ptr)
    (hp8 : ptr + 8 = ptr8) (v : BitVec 64) :
    array (t := i32) a ((xs.set i (v.setWidth 32)).set j ((v >>> 32).setWidth 32)) =
      (cell64 ptr v ⋆
        (array (t := i32) a (xs.take i) ⋆ array (t := i32) ptr8 (xs.drop (i + 2)))) := by
  subst hj
  rw [array32_set_pair_ptr a ptr ptr8 xs hi hp hp8, pack64_lo_hi v]

namespace WatchMemTactics

@[scoped c0_load] theorem c0_load_full_wstk64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat + 1 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWstk + i * 4) =
      some (pack64 s.core.wstk[i.toNat] s.core.wstk[i.toNat + 1]) := by
  have h1 := ArrayField.focus .wstk hm
  dsimp only [ArrayField.elemTy, ArrayField.ptr, ArrayField.get] at h1
  have hp : c.pWstk + BitVec.ofNat 64 (4 * i.toNat) = c.pWstk + i * 4 := by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [array32_focus_pair_ptr c.pWstk _ _ s.core.wstk hi hp rfl, sep_assoc] at h1
  exact loadVal_cell64 h1

@[scoped c0_load] theorem c0_load_full_wstk64_add8 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat + 3 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWstk + i * 4 + 8) =
      some (pack64 s.core.wstk[i.toNat + 2] s.core.wstk[i.toNat + 3]) := by
  have h1 := ArrayField.focus .wstk hm
  dsimp only [ArrayField.elemTy, ArrayField.ptr, ArrayField.get] at h1
  have hp : c.pWstk + BitVec.ofNat 64 (4 * (i.toNat + 2)) = c.pWstk + i * 4 + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [array32_focus_pair_ptr c.pWstk _ _ s.core.wstk (by omega) hp rfl, sep_assoc] at h1
  exact loadVal_cell64 h1

@[scoped c0_store] theorem c0_store_full_wstk64 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat + 1 < s.core.wstk.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + i * 4) ∧
      (FullMem c { s with core := { s.core with
        wstk := (s.core.wstk.set i.toNat (v.setWidth 32)).set (i.toNat + 1)
          ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + i * 4) v) := by
  have h1 := ArrayField.focus .wstk hm
  dsimp only [ArrayField.elemTy, ArrayField.ptr, ArrayField.get] at h1
  have hp : c.pWstk + BitVec.ofNat 64 (4 * i.toNat) = c.pWstk + i * 4 := by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [array32_focus_pair_ptr c.pWstk _ _ s.core.wstk hi hp rfl, sep_assoc] at h1
  obtain ⟨hok, hst⟩ := store_cell64 v h1
  rw [← sep_assoc,
    ← array32_set_pair_pack c.pWstk _ _ s.core.wstk rfl hi hp rfl v] at hst
  exact ⟨hok, ArrayField.unfocus .wstk hst⟩

@[scoped c0_store] theorem c0_store_full_wstk64_add8 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat + 3 < s.core.wstk.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + i * 4 + 8) ∧
      (FullMem c { s with core := { s.core with
        wstk := (s.core.wstk.set (i.toNat + 2) (v.setWidth 32)).set (i.toNat + 3)
          ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + i * 4 + 8) v) := by
  have h1 := ArrayField.focus .wstk hm
  dsimp only [ArrayField.elemTy, ArrayField.ptr, ArrayField.get] at h1
  have hp : c.pWstk + BitVec.ofNat 64 (4 * (i.toNat + 2)) = c.pWstk + i * 4 + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [array32_focus_pair_ptr c.pWstk _ _ s.core.wstk (by omega) hp rfl, sep_assoc] at h1
  obtain ⟨hok, hst⟩ := store_cell64 v h1
  rw [← sep_assoc,
    ← array32_set_pair_pack c.pWstk _ _ s.core.wstk (Nat.add_assoc i.toNat 2 1) (by omega) hp rfl
      v] at hst
  exact ⟨hok, ArrayField.unfocus .wstk hst⟩

end WatchMemTactics

theorem wvec_set_size_off_self {wvec : List (BitVec 32)} {lit : Nat}
    (_h1 : 2 * lit + 1 < wvec.length) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * lit]?.getD 0#32 = wvec[2 * lit]?.getD 0#32 := by
  rw [List.getElem?_set_ne (by omega)]

theorem wvec_set_size_sz_self {wvec : List (BitVec 32)} {lit : Nat}
    (h1 : 2 * lit + 1 < wvec.length) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * lit + 1]?.getD 0#32 = sz' := by
  rw [List.getElem?_set_self h1, Option.getD_some]

theorem wvec_set_size_other {wvec : List (BitVec 32)} {lit l : Nat}
    (hne : l ≠ lit) (sz' : BitVec 32) :
    (wvec.set (2 * lit + 1) sz')[2 * l]?.getD 0#32 = wvec[2 * l]?.getD 0#32 ∧
    (wvec.set (2 * lit + 1) sz')[2 * l + 1]?.getD 0#32 = wvec[2 * l + 1]?.getD 0#32 := by
  exact ⟨by rw [List.getElem?_set_ne (by omega)], by rw [List.getElem?_set_ne (by omega)]⟩

theorem watchStackLayout_shrink {c : FullCfg} {k : FullCoreState} (hlay : WatchStackLayout k)
    (hlen : k.LengthsOk c) {lit cnt : Nat} (hlit : lit < 2 * k.cur_vars)
    (hcnt : cnt ≤ fullWatchSizeCore k lit) {wstk' : List (BitVec 32)}
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit → ∀ idx < fullWatchSizeCore k l,
      wstk'[fullWatchOffCore k l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hnosent : ∀ idx < fullWatchSizeCore k lit - cnt,
      wstk'[fullWatchOffCore k lit + idx]? ≠ some 0xFFFFFFFF#32)
    {wlen' : Nat} {wusable' nb' : BitVec 64} (hwlen : k.wlen ≤ wlen') :
    let k' : FullCoreState := { k with
      wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 (fullWatchSizeCore k lit - cnt))
      wstk := wstk', wlen := wlen', wusable := wusable', num_binary := nb' }
    WatchStackLayout k' := by
  intro k'
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have := c.hmaxv
  unfold dimacsBound at *
  have hwv1 : 2 * lit + 1 < k.wvec.length := by omega
  have hsz_lt : fullWatchSizeCore k lit - cnt < 2 ^ 32 := by
    have := (k.wvec[2 * lit + 1]?.getD 0#32).isLt
    change (k.wvec[2 * lit + 1]?.getD 0#32).toNat - cnt < 2 ^ 32
    omega
  have hoff_lit : fullWatchOffCore k' lit = fullWatchOffCore k lit := by
    simp only [fullWatchOffCore, k']
    exact congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)
  have hsz_lit : fullWatchSizeCore k' lit = fullWatchSizeCore k lit - cnt := by
    simp only [fullWatchSizeCore, k', wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz_lt
  have hoth : ∀ l, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne
    have h := wvec_set_size_other (wvec := k.wvec) hne
      (BitVec.ofNat 32 (fullWatchSizeCore k lit - cnt))
    exact ⟨by dsimp only [fullWatchOffCore, k']; exact congrArg BitVec.toNat h.1,
      by dsimp only [fullWatchSizeCore, k']; exact congrArg BitVec.toNat h.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    by_cases hll : l = lit
    · subst hll; rw [hoff_lit, hsz_lit]; have := hlay.bounds l hl; change _ ≤ wlen'; omega
    · obtain ⟨ho, hs⟩ := hoth l hll; rw [ho, hs]; have := hlay.bounds l hl
      change fullWatchOffCore k l + fullWatchSizeCore k l ≤ wlen'; omega
  · intro l hl hpos
    by_cases hll : l = lit
    · subst hll; rw [hoff_lit]; rw [hsz_lit] at hpos; exact hlay.pos_off l hl (by omega)
    · obtain ⟨ho, hs⟩ := hoth l hll; rw [ho]; rw [hs] at hpos; exact hlay.pos_off l hl hpos
  · intro l1 l2 hl1 hl2 hne hp1 hp2
    by_cases h1 : l1 = lit
    · subst h1
      obtain ⟨ho2, hs2⟩ := hoth l2 hne.symm
      rw [hoff_lit, hsz_lit, ho2, hs2]
      rw [hsz_lit] at hp1; rw [hs2] at hp2
      rcases hlay.disjoint l1 l2 hl1 hl2 hne (by omega) hp2 with h | h <;> omega
    · by_cases h2 : l2 = lit
      · subst h2
        obtain ⟨ho1, hs1⟩ := hoth l1 hne
        rw [ho1, hs1, hoff_lit, hsz_lit]
        rw [hs1] at hp1; rw [hsz_lit] at hp2
        rcases hlay.disjoint l1 l2 hl1 hl2 hne hp1 (by omega) with h | h <;> omega
      · obtain ⟨ho1, hs1⟩ := hoth l1 h1; obtain ⟨ho2, hs2⟩ := hoth l2 h2
        rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
        exact hlay.disjoint l1 l2 hl1 hl2 hne hp1 hp2
  · intro l hl idx hidx
    by_cases hll : l = lit
    · subst hll; rw [hoff_lit]; rw [hsz_lit] at hidx; exact hnosent idx hidx
    · obtain ⟨ho, hs⟩ := hoth l hll; rw [ho]
      rw [hs] at hidx
      change wstk'[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
      rw [hother l hl hll idx hidx]
      exact hlay.no_sentinel l hl idx hidx

inductive WatchBoundary (wstk : List (BitVec 32)) : Nat → Nat → Nat → Prop where
  | here (p rem : Nat) : WatchBoundary wstk p rem p
  | bin {p rem q : Nat} {w0 : BitVec 32} :
      wstk[p]? = some w0 → w0 &&& 0x80000000#32 ≠ 0#32 →
      WatchBoundary wstk (p + 1) rem q → WatchBoundary wstk p (rem + 1) q
  | large {p rem q : Nat} {w0 cref : BitVec 32} :
      wstk[p]? = some w0 → wstk[p + 1]? = some cref →
      w0 &&& 0x80000000#32 = 0#32 → cref.toNat < 2147483648 →
      WatchBoundary wstk (p + 2) rem q → WatchBoundary wstk p (rem + 2) q

theorem watchSliceOk_boundary_end {F : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (hs : WatchSliceOk F k lit p rem) : WatchBoundary k.wstk p rem (p + rem) := by
  induction hs with
  | empty => simp; exact WatchBoundary.here _ 0
  | @bin p rem _ hw hbin _ _ _ _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm 1 rem] using WatchBoundary.bin hw hbin ih
  | @large p rem _ _ hw0 hw1 hlg hlt _ _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm 2 rem] using WatchBoundary.large hw0 hw1 hlg hlt ih

theorem denseWatchSliceOk_boundary_end {F : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (hs : DenseWatchSliceOk F k lit p rem) : WatchBoundary k.wstk p rem (p + rem) :=
  watchSliceOk_boundary_end hs.toWatchSliceOk

theorem watchBoundary_le {wstk : List (BitVec 32)} {p rem q : Nat}
    (hb : WatchBoundary wstk p rem q) : p ≤ q ∧ q ≤ p + rem := by
  induction hb with
  | here _ _ => omega
  | bin _ _ _ ih => omega
  | large _ _ _ _ _ ih => omega

theorem watchBoundary_prev {wstk : List (BitVec 32)} {p rem q : Nat}
    (hb : WatchBoundary wstk p rem q) (hpq : p < q) :
    (∃ w0, wstk[q - 1]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32 ∧
      WatchBoundary wstk p rem (q - 1)) ∨
    (∃ w0 cref, p + 2 ≤ q ∧ wstk[q - 2]? = some w0 ∧ wstk[q - 1]? = some cref ∧
      w0 &&& 0x80000000#32 = 0#32 ∧ cref.toNat < 2147483648 ∧
      WatchBoundary wstk p rem (q - 2)) := by
  induction hb with
  | here _ _ => omega
  | @bin p rem q w0 hw hbin rest ih =>
    cases rest with
    | here =>
      left; exact ⟨w0, by simpa using hw, hbin, by simpa using WatchBoundary.here p (rem + 1)⟩
    | bin _ _ _ | large _ _ _ _ _ =>
      have hgt : p + 1 < q := by have := watchBoundary_le ‹WatchBoundary _ _ _ _›; omega
      rcases ih hgt with
        ⟨w', hw', hb', hr'⟩ | ⟨w', c', hle, hw0', hw1', hlg', hlt', hr'⟩
      · left; exact ⟨w', hw', hb', WatchBoundary.bin hw hbin hr'⟩
      · right; exact ⟨w', c', by omega, hw0', hw1', hlg', hlt', WatchBoundary.bin hw hbin hr'⟩
  | @large p rem q w0 cref hw0 hw1 hlg hlt rest ih =>
    cases rest with
    | here =>
      right; exact ⟨w0, cref, by omega, by simpa using hw0, by simpa using hw1, hlg, hlt,
        by simpa using WatchBoundary.here p (rem + 2)⟩
    | bin _ _ _ | large _ _ _ _ _ =>
      have hgt : p + 2 < q := by have := watchBoundary_le ‹WatchBoundary _ _ _ _›; omega
      rcases ih hgt with
        ⟨w', hw', hb', hr'⟩ | ⟨w', c', hle, hw0', hw1', hlg', hlt', hr'⟩
      · left; exact ⟨w', hw', hb', WatchBoundary.large hw0 hw1 hlg hlt hr'⟩
      · right; exact ⟨w', c', by omega, hw0', hw1', hlg', hlt',
          WatchBoundary.large hw0 hw1 hlg hlt hr'⟩

theorem watchBoundary_append_bin {wstk : List (BitVec 32)} {p rem q : Nat} {w0 : BitVec 32}
    (hb : WatchBoundary wstk p rem q) (hrem : q + 1 ≤ p + rem)
    (hw : wstk[q]? = some w0) (hbin : w0 &&& 0x80000000#32 ≠ 0#32) :
    WatchBoundary wstk p rem (q + 1) := by
  induction hb with
  | @here p0 r0 =>
    cases r0 with
    | zero => omega
    | succ r' => exact WatchBoundary.bin hw hbin (WatchBoundary.here (p0 + 1) r')
  | @bin p0 r0 q0 w' hw' hbin' rest ih =>
    exact WatchBoundary.bin hw' hbin' (ih (by omega) hw)
  | @large p0 r0 q0 w' c' hw0' hw1' hlg' hlt' rest ih =>
    exact WatchBoundary.large hw0' hw1' hlg' hlt' (ih (by omega) hw)

theorem watchBoundary_append_large {wstk : List (BitVec 32)} {p rem q : Nat} {w0 cref : BitVec 32}
    (hb : WatchBoundary wstk p rem q) (hrem : q + 2 ≤ p + rem)
    (hw0 : wstk[q]? = some w0) (hw1 : wstk[q + 1]? = some cref)
    (hlg : w0 &&& 0x80000000#32 = 0#32) (hlt : cref.toNat < 2147483648) :
    WatchBoundary wstk p rem (q + 2) := by
  induction hb with
  | @here p0 r0 =>
    have hr' : r0 = (r0 - 2) + 2 := by omega
    rw [hr']
    exact WatchBoundary.large hw0 hw1 hlg hlt (WatchBoundary.here (p0 + 2) (r0 - 2))
  | @bin p0 r0 q0 w' hw' hbin' rest ih =>
    exact WatchBoundary.bin hw' hbin' (ih (by omega) hw0 hw1)
  | @large p0 r0 q0 w' c' hw0' hw1' hlg' hlt' rest ih =>
    exact WatchBoundary.large hw0' hw1' hlg' hlt' (ih (by omega) hw0 hw1)

theorem watchSliceOk_erase {F : List (List Nat)} {k k' : FullCoreState} {lit p rem q d : Nat}
    (hcur : k.cur_vars ≤ k'.cur_vars)
    (hare : ∀ r, r ∈ fullArenaClauseRefsCore k → r ∈ fullArenaClauseRefsCore k')
    (hslice : WatchSliceOk F k lit p rem) (hbd : WatchBoundary k.wstk p rem q)
    (hle : q + d ≤ p + rem)
    (hd_match : (d = 1 ∧ ∃ w0, k.wstk[q]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32) ∨
      (d = 2 ∧ ∃ w0 cref, k.wstk[q]? = some w0 ∧ k.wstk[q + 1]? = some cref ∧
        w0 &&& 0x80000000#32 = 0#32 ∧ cref.toNat < 2147483648))
    (hpre : ∀ idx, p ≤ idx → idx < q → k'.wstk[idx]? = k.wstk[idx]?)
    (hsh : ∀ idx, q ≤ idx → idx < p + rem - d → k'.wstk[idx]? = k.wstk[idx + d]?) :
    WatchSliceOk F k' lit p (rem - d) := by
  induction hslice with
  | empty =>
    have := watchBoundary_le hbd
    rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  | @bin p rem' w0 hw hbin hns hlt hent hrest ih =>
    have hq_le : p ≤ q := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hq_le with rfl | hpq
    · rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, w', c', hw', _, hlg, _⟩
      · simpa using fullWatchSlice_relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using
              hsh (p + idx) (by omega) (by omega))
          hrest
      · rw [hw] at hw'; cases hw'; exact absurd hlg hbin
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ hw' _ rest => exact rest
        | @large _ _ _ _ _ hw0' _ hlg' _ _ =>
          rw [hw] at hw0'; cases hw0'; contradiction
      have hbd_le := watchBoundary_le hbd'
      have hw' : k'.wstk[p]? = some w0 := by rw [hpre p (Nat.le_refl p) hpq, hw]
      have hrest' := ih hbd' (by omega)
        (fun idx h1 h2 => hpre idx (by omega) h2)
        (fun idx h1 h2 => hsh idx h1 (by omega))
      have hsub : rem' + 1 - d = (rem' - d) + 1 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact WatchSliceOk.bin hw' hbin hns (Nat.lt_of_lt_of_le hlt (by omega)) hent hrest'
  | @large p rem' w0 cref hw0 hw1 hlg hlt haref hrest ih =>
    have hq_le : p ≤ q := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hq_le with rfl | hpq
    · rcases hd_match with ⟨rfl, w', hw', hbin'⟩ | ⟨rfl, _⟩
      · rw [hw0] at hw'; cases hw'; contradiction
      · simpa using fullWatchSlice_relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 2 idx] using
              hsh (p + idx) (by omega) (by omega))
          hrest
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ hw' hbin' _ => rw [hw0] at hw'; cases hw'; contradiction
        | @large _ _ _ _ _ _ _ _ _ rest => exact rest
      have hbd_le := watchBoundary_le hbd'
      have hw0' : k'.wstk[p]? = some w0 := by rw [hpre p (Nat.le_refl p) (by omega), hw0]
      have hw1' : k'.wstk[p + 1]? = some cref := by
        rw [hpre (p + 1) (by omega) (by omega), hw1]
      have hrest' := ih hbd' (by omega)
        (fun idx h1 h2 => hpre idx (by omega) h2)
        (fun idx h1 h2 => hsh idx h1 (by omega))
      have hsub : rem' + 2 - d = (rem' - d) + 2 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact WatchSliceOk.large hw0' hw1' hlg hlt (hare _ haref) hrest'

theorem denseWatchSliceOk_erase {F : List (List Nat)} {k k' : FullCoreState} {lit p rem q d : Nat}
    (hcur : k.cur_vars ≤ k'.cur_vars)
    (hare : ∀ r, r ∈ fullArenaClauseRefsCore k → r ∈ fullArenaClauseRefsCore k')
    (hslice : DenseWatchSliceOk F k lit p rem) (hbd : WatchBoundary k.wstk p rem q)
    (hle : q + d ≤ p + rem)
    (hd_match : (d = 1 ∧ ∃ w0, k.wstk[q]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32) ∨
      (d = 2 ∧ ∃ w0 cref, k.wstk[q]? = some w0 ∧ k.wstk[q + 1]? = some cref ∧
        w0 &&& 0x80000000#32 = 0#32 ∧ cref.toNat < 2147483648))
    (hpre : ∀ idx, p ≤ idx → idx < q → k'.wstk[idx]? = k.wstk[idx]?)
    (hsh : ∀ idx, q ≤ idx → idx < p + rem - d → k'.wstk[idx]? = k.wstk[idx + d]?) :
    DenseWatchSliceOk F k' lit p (rem - d) := by
  induction hslice with
  | empty =>
    have := watchBoundary_le hbd
    rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  | @bin p rem' w0 hw hbin hns hlt hent hrest ih =>
    have hq_le : p ≤ q := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hq_le with rfl | hpq
    · rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, w', c', hw', _, hlg, _⟩
      · simpa using DenseWatchSliceOk.relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur
          hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using
              hsh (p + idx) (by omega) (by omega))
          hrest
      · rw [hw] at hw'; cases hw'; exact absurd hlg hbin
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ hw' _ rest => exact rest
        | @large _ _ _ _ _ hw0' _ hlg' _ _ =>
          rw [hw] at hw0'; cases hw0'; contradiction
      have hbd_le := watchBoundary_le hbd'
      have hw' : k'.wstk[p]? = some w0 := by rw [hpre p (Nat.le_refl p) hpq, hw]
      have hrest' := ih hbd' (by omega)
        (fun idx h1 h2 => hpre idx (by omega) h2)
        (fun idx h1 h2 => hsh idx h1 (by omega))
      have hsub : rem' + 1 - d = (rem' - d) + 1 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact DenseWatchSliceOk.bin hw' hbin hns (Nat.lt_of_lt_of_le hlt (by omega)) hent hrest'
  | @occ p rem' w0 cref hw0 hw1 hlg hge3 hlt haref hrest ih =>
    have hq_le : p ≤ q := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hq_le with rfl | hpq
    · rcases hd_match with ⟨rfl, w', hw', hbin'⟩ | ⟨rfl, _⟩
      · rw [hw0] at hw'; cases hw'; contradiction
      · simpa using DenseWatchSliceOk.relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur
          hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 2 idx] using
              hsh (p + idx) (by omega) (by omega))
          hrest
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ hw' hbin' _ => rw [hw0] at hw'; cases hw'; contradiction
        | @large _ _ _ _ _ _ _ _ _ rest => exact rest
      have hbd_le := watchBoundary_le hbd'
      have hw0' : k'.wstk[p]? = some w0 := by rw [hpre p (Nat.le_refl p) (by omega), hw0]
      have hw1' : k'.wstk[p + 1]? = some cref := by
        rw [hpre (p + 1) (by omega) (by omega), hw1]
      have hrest' := ih hbd' (by omega)
        (fun idx h1 h2 => hpre idx (by omega) h2)
        (fun idx h1 h2 => hsh idx h1 (by omega))
      have hsub : rem' + 2 - d = (rem' - d) + 2 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact DenseWatchSliceOk.occ hw0' hw1' hlg hge3 hlt (hare _ haref) hrest'

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
