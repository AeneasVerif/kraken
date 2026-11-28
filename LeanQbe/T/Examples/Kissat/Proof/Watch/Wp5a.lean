/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
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
  have hd (n : Nat) (z : Int) :
      (z / (256 : Int) ^ n) / 256 = z / (256 : Int) ^ (n + 1) := by
    rw [Int.ediv_ediv]
    simp [Int.not_lt.mpr (Int.pow_nonneg (by decide : (0 : Int) ≤ 256)), Int.pow_succ]
  have hd2 (z : Int) : z / 256 / 256 = z / (256 : Int) ^ 2 := by
    simpa only [Int.pow_one] using hd 1 z
  have hd3 (z : Int) : z / 256 / 256 / 256 = z / (256 : Int) ^ 3 := hd2 z ▸ hd 2 z
  have hd4 (z : Int) : z / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 4 := hd3 z ▸ hd 3 z
  have hd5 (z : Int) : z / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 5 := hd4 z ▸ hd 4 z
  have hd6 (z : Int) : z / 256 / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 6 :=
    hd5 z ▸ hd 5 z
  have hd7 (z : Int) : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 = z / (256 : Int) ^ 7 :=
    hd6 z ▸ hd 6 z
  have hb32_0 (b : BitVec 32) : (b.toInt.take 8).toNat = b.toNat % 256 := by
    simpa using bitvec_toBytes_byte b 0 (by decide)
  have hb32_1 (b : BitVec 32) : ((b.toInt / 256).take 8).toNat = (b.toNat / 256) % 256 := by
    simpa using bitvec_toBytes_byte b 1 (by decide)
  have hb64_0 : ((pack64 x y).toInt.take 8).toNat = (x.toNat + 2 ^ 32 * y.toNat) % 256 := by
    simpa [hpxy] using bitvec_toBytes_byte (pack64 x y) 0 (by decide)
  have hb64_1 :
      (((pack64 x y).toInt / 256).take 8).toNat = ((x.toNat + 2 ^ 32 * y.toNat) / 256) % 256 := by
    simpa [hpxy] using bitvec_toBytes_byte (pack64 x y) 1 (by decide)
  have hb64 (k : Nat) (hk : 8 * (k + 1) ≤ 64) :
      (((pack64 x y).toInt / ((256 : Int) ^ k)).take 8).toNat =
        ((x.toNat + 2 ^ 32 * y.toNat) / 256 ^ k) % 256 := by
    simpa [hpxy] using bitvec_toBytes_byte (pack64 x y) k hk
  have hbytes : Int.toBytes 4 x.toInt ++ Int.toBytes 4 y.toInt =
      Int.toBytes 8 (pack64 x y).toInt := by
    simp only [Int.toBytes.eq_2, Int.toBytes.eq_1, List.cons_append, List.nil_append,
      List.cons.injEq, and_true]
    rw [hd7, hd6, hd5, hd4, hd3, hd2, hd3, hd2, hd3, hd2]
    have hx := x.isLt; have hy := y.isLt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply congrArg Nat.toUInt8 <;>
      simp only [hb32_0, hb32_1, bitvec_toBytes_byte x 2 (by decide),
        bitvec_toBytes_byte x 3 (by decide), bitvec_toBytes_byte y 2 (by decide),
        bitvec_toBytes_byte y 3 (by decide), hb64_0, hb64_1, hb64 2 (by decide),
        hb64 3 (by decide), hb64 4 (by decide), hb64 5 (by decide), hb64 6 (by decide),
        hb64 7 (by decide)] <;> omega
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
  | empty => have := watchBoundary_le hbd; rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  | @bin p rem' w0 hw hbin hns hlt hent hrest ih =>
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, w', _, hw', _, hlg, _⟩
      · simpa using fullWatchSlice_relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using hsh (p + idx) (by omega) (by omega))
          hrest
      · rw [hw] at hw'; cases hw'; exact absurd hlg hbin
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | bin _ _ rest => exact rest
        | large hw0' _ _ _ _ => rw [hw] at hw0'; cases hw0'; contradiction
      have hbd_le := watchBoundary_le hbd'
      have hsub : rem' + 1 - d = (rem' - d) + 1 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact WatchSliceOk.bin (by rw [hpre p (Nat.le_refl p) hpq, hw]) hbin hns
        (Nat.lt_of_lt_of_le hlt (by omega)) hent (ih hbd' (by omega)
          (fun idx h1 h2 => hpre idx (by omega) h2) (fun idx h1 h2 => hsh idx h1 (by omega)))
  | @large p rem' w0 cref hw0 hw1 hlg hlt haref hrest ih =>
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · rcases hd_match with ⟨rfl, w', hw', _⟩ | ⟨rfl, _⟩
      · rw [hw0] at hw'; cases hw'; contradiction
      · simpa using fullWatchSlice_relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur hare
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 2 idx] using hsh (p + idx) (by omega) (by omega))
          hrest
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | bin hw' _ _ => rw [hw0] at hw'; cases hw'; contradiction
        | large _ _ _ _ rest => exact rest
      have hbd_le := watchBoundary_le hbd'
      have hsub : rem' + 2 - d = (rem' - d) + 2 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact WatchSliceOk.large (by rw [hpre p (Nat.le_refl p) (by omega), hw0])
        (by rw [hpre (p + 1) (by omega) (by omega), hw1]) hlg hlt (hare _ haref)
        (ih hbd' (by omega) (fun idx h1 h2 => hpre idx (by omega) h2)
          (fun idx h1 h2 => hsh idx h1 (by omega)))

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
  | empty => have := watchBoundary_le hbd; rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  | @bin p rem' w0 hw hbin hns hlt hent hrest ih =>
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, w', _, hw', _, hlg, _⟩
      · simpa using DenseWatchSliceOk.relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur
          hare (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using hsh (p + idx) (by omega) (by omega))
          hrest
      · rw [hw] at hw'; cases hw'; exact absurd hlg hbin
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | bin _ _ rest => exact rest
        | large hw0' _ _ _ _ => rw [hw] at hw0'; cases hw0'; contradiction
      have hbd_le := watchBoundary_le hbd'
      have hsub : rem' + 1 - d = (rem' - d) + 1 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact DenseWatchSliceOk.bin (by rw [hpre p (Nat.le_refl p) hpq, hw]) hbin hns
        (Nat.lt_of_lt_of_le hlt (by omega)) hent (ih hbd' (by omega)
          (fun idx h1 h2 => hpre idx (by omega) h2) (fun idx h1 h2 => hsh idx h1 (by omega)))
  | @occ p rem' w0 cref hw0 hw1 hlg hge3 hlt haref hrest ih =>
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · rcases hd_match with ⟨rfl, w', hw', _⟩ | ⟨rfl, _⟩
      · rw [hw0] at hw'; cases hw'; contradiction
      · simpa using DenseWatchSliceOk.relocate (Std.Sat.CNF.entails_refl (cnfOfClauses F)) hcur
          hare (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 2 idx] using hsh (p + idx) (by omega) (by omega))
          hrest
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | bin hw' _ _ => rw [hw0] at hw'; cases hw'; contradiction
        | large _ _ _ _ rest => exact rest
      have hbd_le := watchBoundary_le hbd'
      have hsub : rem' + 2 - d = (rem' - d) + 2 := by
        rcases hd_match with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hsub]
      exact DenseWatchSliceOk.occ (by rw [hpre p (Nat.le_refl p) (by omega), hw0])
        (by rw [hpre (p + 1) (by omega) (by omega), hw1]) hlg hge3 hlt (hare _ haref)
        (ih hbd' (by omega) (fun idx h1 h2 => hpre idx (by omega) h2)
          (fun idx h1 h2 => hsh idx h1 (by omega)))

theorem bv32_ushr31_of_bin {w0 : BitVec 32} (hb : w0 &&& 0x80000000#32 ≠ 0#32) :
    w0 >>> 31 = 1#32 := by
  have hlt := w0.isLt
  have hge : 0x80000000 ≤ w0.toNat := by
    refine Classical.byContradiction fun hlt' => hb ?_
    apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro k
    rw [BitVec.toNat_and, Nat.testBit_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
      show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_testBit]
    by_cases hk : k = 31
    · subst hk
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [show w0.toNat / 2 ^ 31 = 0 by omega]
    · rw [Nat.testBit_two_pow, decide_eq_false (Ne.symm hk)]; simp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (1#32 : BitVec 32).toNat = 1 from rfl]
  omega

theorem bv32_ushr31_of_lt {w0 : BitVec 32} (hlt : w0.toNat < 2147483648) :
    w0 >>> 31 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0#32 : BitVec 32).toNat = 0 from rfl]
  omega

theorem bv64_ofNat_add_const (x k : Nat) (hx : x + k < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 k = BitVec.ofNat 64 (x + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hx]

theorem pop_tail_fin {c : FullCfg} {s : FullState} {lit cnt : Val i32}
    {wstk' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hcnt_le : cnt.toNat ≤ fullWatchSize s lit.toNat)
    (hwlen' : wstk'.length = s.core.wstk.length)
    (hpre : ∀ idx,
      idx < fullWatchOffCore s.core lit.toNat + (fullWatchSizeCore s.core lit.toNat - cnt.toNat) →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hpost : ∀ idx, fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ≤ idx →
      idx < s.core.wstk.length → wstk'[idx]? = s.core.wstk[idx]?)
    (hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length)
    (hsz_lt : fullWatchSizeCore s.core lit.toNat - cnt.toNat < 2 ^ 32)
    (hm : (FullMem c { s with core := { s.core with
      wvec := s.core.wvec.set (2 * lit.toNat + 1)
        (BitVec.ofNat 32 (fullWatchSizeCore s.core lit.toNat - cnt.toNat))
      wstk := wstk', wusable := s.core.wusable + BitVec.zeroExtend 64 cnt } } ⋆ R) m)
    (hQ : ∀ (wvec' wstk' : List (BitVec 32)) (wusable' : BitVec 64) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        fullWatchOff s' l = fullWatchOff s l ∧ fullWatchSize s' l = fullWatchSize s l ∧
        ∀ idx < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + idx]? = s.core.wstk[fullWatchOff s l + idx]?) →
      fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat →
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat - cnt.toNat →
      (∀ idx < fullWatchSize s lit.toNat - cnt.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + idx]? =
          s.core.wstk[fullWatchOff s lit.toNat + idx]?) →
      (FullMem c s' ⋆ R) m' → Q () m') : Q () m := by
  let off := fullWatchOffCore s.core lit.toNat
  let sz := fullWatchSizeCore s.core lit.toNat
  have hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat → ∀ idx < fullWatchSizeCore s.core l,
      wstk'[fullWatchOffCore s.core l + idx]? = s.core.wstk[fullWatchOffCore s.core l + idx]? := by
    intro l hl hne idx hidx
    by_cases hsz0 : sz = 0
    · have hbd_l := hlay.bounds l hl
      have hwl_le := hlen.core_ok.wlen_le
      have hws_len := hlen.core_ok.wstk_len_arr
      by_cases hlt_off : fullWatchOffCore s.core l + idx < off + (sz - cnt.toNat)
      · exact hpre _ hlt_off
      · exact hpost _ (by omega) (by omega)
    · rcases hlay.disjoint l lit.toNat hl hlit hne
          (Nat.lt_of_le_of_lt (Nat.zero_le _) hidx) (by omega) with hle_l | hle_r
      · exact hpre _ (by omega)
      · have hbd_l := hlay.bounds l hl
        have hwl_le := hlen.core_ok.wlen_le
        have hws_len := hlen.core_ok.wstk_len_arr
        exact hpost _ (by omega) (by omega)
  have hnosent : ∀ idx < sz - cnt.toNat, wstk'[off + idx]? ≠ some 0xFFFFFFFF#32 :=
    fun idx hidx => by
      rw [hpre (off + idx) (by omega)]; exact hlay.no_sentinel lit.toNat hlit idx (by omega)
  let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz - cnt.toNat))
  let k' : FullCoreState := { s.core with
    wvec := wvec', wstk := wstk', wusable := s.core.wusable + BitVec.zeroExtend 64 cnt }
  have hlay' := watchStackLayout_shrink hlay hlen.core_ok hlit hcnt_le hother hnosent
    (wlen' := s.core.wlen) (wusable' := s.core.wusable + BitVec.zeroExtend 64 cnt)
    (nb' := s.core.num_binary) (Nat.le_refl _)
  have hlen_core' : k'.LengthsOk c :=
    { hlen.core_ok with wvec_len := by rw [List.length_set, hlen.core_ok.wvec_len]
                        wstk_len_arr := by rw [hwlen', hlen.core_ok.wstk_len_arr] }
  have hoff_lit : fullWatchOffCore k' lit.toNat = off :=
    congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)
  have hsz_lit : fullWatchSizeCore k' lit.toNat = sz - cnt.toNat := by
    dsimp only [fullWatchSizeCore, k', wvec']
    rw [wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  refine hQ wvec' wstk' (s.core.wusable + BitVec.zeroExtend 64 cnt) m
    ⟨hlen_core', hlen.scratch_ok⟩ hlay' (fun l hl hne => ?_) hoff_lit hsz_lit
    (fun idx hidx => by
      change idx < sz - cnt.toNat at hidx
      change wstk'[fullWatchOffCore k' lit.toNat + idx]? = _
      rw [hoff_lit]; exact hpre (off + idx) (by omega)) hm
  have hw' := wvec_set_size_other (wvec := s.core.wvec) hne (BitVec.ofNat 32 (sz - cnt.toNat))
  have hoff_eq : fullWatchOff { s with core := k' } l = fullWatchOff s l :=
    congrArg BitVec.toNat hw'.1
  have hsz_eq : fullWatchSize { s with core := k' } l = fullWatchSize s l :=
    congrArg BitVec.toNat hw'.2
  exact ⟨hoff_eq, hsz_eq, fun idx hidx => by rw [hoff_eq]; exact hother l hl hne idx hidx⟩

theorem unwatch_tail_bv {c : FullCfg} {k : FullCoreState} (hlen : k.LengthsOk c) {lit : Val i32}
    (hlit : lit.toNat < 2 * k.cur_vars)
    (hbounds : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat ≤ k.wlen)
    (hsz2 : 2 ≤ fullWatchSizeCore k lit.toNat) {wstk_len : Nat}
    (hwl : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat ≤ wstk_len) :
    let off := fullWatchOffCore k lit.toNat
    let sz := fullWatchSizeCore k lit.toNat
    let h0 : (BitVec.setWidth 64 lit <<< 1).toNat < k.wvec.length := (wvec_shl1_lt hlen hlit).2.2.1
    let h1 : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < k.wvec.length :=
      (wvec_shl1_lt hlen hlit).2.2.2.1
    (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 2).toNat =
      off + sz - 2 ∧
    (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 1).toNat =
      off + sz - 1 ∧
    BitVec.setWidth 32
      (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 2) =
      BitVec.ofNat 32 (sz - 2) ∧
    (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 2).toNat <
      wstk_len ∧
    (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 1).toNat <
      wstk_len := by
  intro off sz h0 h1
  have hlt := wvec_shl1_lt hlen hlit
  have hwv0 := hlt.1; have hwv1 := hlt.2.1
  have hwl_le := hlen.wlen_le; have hwc := c.hwcap; unfold dimacsBound at hwc
  have hend := wvec_end_add_eq hlen hlit h0 h1
  have hg1 : k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1 = k.wvec[2 * lit.toNat + 1]'hwv1 :=
    list_getElem_congr h1 (bv64_shl1_add1_lit lit)
  have hsz_lt : sz < 2 ^ 32 := (k.wvec[2 * lit.toNat + 1]?.getD 0#32).isLt
  have h64 : off + sz < 2 ^ 64 := by omega
  have hm2 : (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 2).toNat =
      off + sz - 2 := by
    rw [BitVec.toNat_sub, hend, show (2 : BitVec 64).toNat = 2 from rfl]
    dsimp only [off, sz] at *; simp only [Nat.reducePow] at *; omega
  have hm1 : (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0) +
      BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 1).toNat =
      off + sz - 1 := by
    rw [BitVec.toNat_sub, hend, show (1 : BitVec 64).toNat = 1 from rfl]
    dsimp only [off, sz] at *; simp only [Nat.reducePow] at *; omega
  have hw1_val : BitVec.setWidth 32
      (BitVec.setWidth 64 (k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1) - 2) =
      BitVec.ofNat 32 (sz - 2) := by
    rw [hg1]; apply BitVec.eq_of_toNat_eq
    have hlt_v0 := (k.wvec[2 * lit.toNat + 1]'hwv1).isLt
    have hge2 : 2 ≤ (k.wvec[2 * lit.toNat + 1]'hwv1).toNat := by
      simpa [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some] using hsz2
    simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some,
      BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow,
      show (2 : BitVec 64).toNat = 2 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : (k.wvec[2 * lit.toNat + 1]'hwv1).toNat < 18446744073709551616)]
    omega
  exact ⟨hm2, hm1, hw1_val, by rw [hm2]; omega, by rw [hm1]; omega⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
