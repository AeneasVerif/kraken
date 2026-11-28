/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly0Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Monomial Union & Pool Compaction WPs (`Arisca.Proof.Poly0`)

`XPost`-polymorphic `Mem 64` WP proofs for `ar_munion` and `ar_compact`, re-exporting all specs
and primitive WPs from `Poly0Base`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

public section

/-! ## 1. `ar_munion_wp` -/

private def slicePref (xs : List (BitVec 32)) (k : Nat) : List Nat :=
  (List.range (k - 1)).map (fun t => (xs.getD (1 + t) 0#32).toNat)

private def sliceSuf (xs : List (BitVec 32)) (off len i : Nat) : List Nat :=
  (List.range (len + 1 - i)).map (fun t => (xs.getD (off + i + t) 0#32).toNat)

private theorem slicePref_set_eq {xs : List (BitVec 32)} {k : Nat} {x : BitVec 32}
    (hk1 : 1 ≤ k) (hklt : k < xs.length) :
    slicePref (xs.set k x) (k + 1) = slicePref xs k ++ [x.toNat] := by
  have hk_succ : k = (k - 1) + 1 := by omega
  have hhead : ((xs.set k x).getD (1 + (k - 1)) 0#32).toNat = x.toNat := by
    rw [show 1 + (k - 1) = k by omega, getD_set_eq xs 0#32 x hklt]; simp
  have htail : (List.range (k - 1)).map (fun t => ((xs.set k x).getD (1 + t) 0#32).toNat) =
      (List.range (k - 1)).map (fun t => (xs.getD (1 + t) 0#32).toNat) := by
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    rw [getD_set_eq xs 0#32 x hklt]
    simp [show 1 + t ≠ k by omega]
  dsimp only [slicePref]
  rw [Nat.add_sub_cancel]
  conv => lhs; rhs; rw [hk_succ]
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, hhead, htail]

private theorem mem_slicePref_set {xs : List (BitVec 32)} {k : Nat} {x : BitVec 32}
    (hk1 : 1 ≤ k) (hklt : k < xs.length) (z : Nat) :
    z ∈ slicePref (xs.set k x) (k + 1) ↔ z = x.toNat ∨ z ∈ slicePref xs k := by
  rw [slicePref_set_eq hk1 hklt, List.mem_append, List.mem_singleton, or_comm]

private theorem mem_sliceSuf_succ {xs : List (BitVec 32)} {off len i : Nat} (hi : i ≤ len) :
    ∀ z, z ∈ sliceSuf xs off len i ↔
      z = (xs.getD (off + i) 0#32).toNat ∨ z ∈ sliceSuf xs off len (i + 1) := by
  intro z
  simp only [sliceSuf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | zero => left; simp
    | succ t' => right; refine ⟨t', by omega, by congr 2; omega⟩
  · rintro (rfl | ⟨t', ht', rfl⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨t' + 1, by omega, by congr 2; omega⟩

private theorem sliceSuf_head_lt {xs : List (BitVec 32)} {off i : Nat}
    (hs : MonoSorted xs off) (hi1 : 1 ≤ i) (hle : i ≤ (xs.getD off 0#32).toNat) :
    ∀ y ∈ sliceSuf xs off (xs.getD off 0#32).toNat (i + 1),
      (xs.getD (off + i) 0#32).toNat < y := by
  intro y hy
  simp only [sliceSuf, List.mem_map, List.mem_range] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have hlt := (monoSorted_iff xs off).mp hs (i - 1) (i + t) (by omega) (by omega)
  rwa [show off + 1 + (i - 1) = off + i by omega,
    show off + 1 + (i + t) = off + (i + 1) + t by omega] at hlt

private theorem sliceSuf_gt_eq_nil {xs : List (BitVec 32)} {off len i : Nat} (hi : len < i) :
    sliceSuf xs off len i = [] := by
  simp [sliceSuf, show len + 1 - i = 0 by omega]

private def MunionInv (outPtr aBase bBase : BitVec 64)
    (out0 aArr bArr : List (BitVec 32)) (aOff bOff idx0 la lb : Nat)
    (sym : BitVec 32) (R : Mem 64 → Prop)
    (rem : Nat) (args : Tup Val [i32, i32, i32, i64]) (m' : Mem 64) : Prop :=
  let ⟨i, j, k, g, _⟩ := args
  ∃ outCur : List (BitVec 32),
    outCur.length = out0.length ∧
    1 ≤ i.toNat ∧ i.toNat ≤ la + 1 ∧
    1 ≤ j.toNat ∧ j.toNat ≤ lb + 1 ∧
    1 ≤ k.toNat ∧
    k.toNat ≤ (i.toNat - 1) + (j.toNat - 1) + 1 - (if idx0 < i.toNat then 1 else 0) ∧
    rem = (la + 1 - i.toNat) + (lb + 1 - j.toNat) ∧
    (∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32) ∧
    (∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff)) ∧
    (∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64) ∧
    (MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y)) ∧
    (array (t := i32) outPtr outCur ⋆ array (t := i32) aBase aArr ⋆
      array (t := i32) bBase bArr ⋆ R) m'

private theorem munion_step_write {out0 aArr bArr outCur : List (BitVec 32)}
    {aOff bOff la lb : Nat} {sym i j k : BitVec 32} {g : BitVec 64}
    (hk1 : 1 ≤ k.toNat) (hk_cur : k.toNat < outCur.length)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (x i' j' : BitVec 32)
    (hmem_step : ∀ z, (z = x.toNat ∨ z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i'.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j'.toNat) ↔
      (z ∈ slicePref outCur k.toNat ∨
        (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
        z ∈ sliceSuf bArr bOff lb j.toNat)) :
    (∀ idx, idx < 1 ∨ k.toNat + 1 ≤ idx →
      (outCur.set k.toNat x).getD idx 0#32 = out0.getD idx 0#32) ∧
    (∀ z, (z ∈ slicePref (outCur.set k.toNat x) (k.toNat + 1) ∨
      (z ∈ sliceSuf aArr aOff la i'.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j'.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff)) ∧
    (∀ z ∈ slicePref (outCur.set k.toNat x) (k.toNat + 1),
      ((g ||| sigBit x) &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64) := by
  refine ⟨fun idx hidx => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [getD_set_eq outCur 0#32 x hk_cur]
    simp only [show idx ≠ k.toNat by omega, ↓reduceIte]
    exact hpres idx (by
      rcases hidx with h | h
      · left; omega
      · right; omega)
  · rw [mem_slicePref_set hk1 hk_cur, or_assoc]
    exact (hmem_step z).trans (hmem_inv z)
  · rw [mem_slicePref_set hk1 hk_cur] at hz
    rcases hz with rfl | hz
    · rw [BitVec.ofNat_toNat]; exact or_and_sigBit_ne_zero g x
    · have ho := hsig_inv z hz
      rw [BitVec.or_comm]
      exact and_sigBit_or_left ho |> fun h => by rwa [BitVec.or_comm] at h

private theorem munion_step_sort {aArr bArr outCur : List (BitVec 32)}
    {aOff bOff la lb : Nat} {i j k : BitVec 32}
    (hk1 : 1 ≤ k.toNat) (hk_cur : k.toNat < outCur.length)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (x i' j' : BitVec 32)
    (hxy : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (∀ z ∈ slicePref outCur k.toNat, z < x.toNat) ∧
      (∀ y ∈ sliceSuf aArr aOff la i'.toNat, x.toNat < y) ∧
      (∀ y ∈ sliceSuf bArr bOff lb j'.toNat, x.toNat < y)) :
    MonoSorted aArr aOff → MonoSorted bArr bOff →
    (slicePref (outCur.set k.toNat x) (k.toNat + 1)).Pairwise (· < ·) ∧
    (∀ z ∈ slicePref (outCur.set k.toNat x) (k.toNat + 1),
      ∀ y ∈ sliceSuf aArr aOff la i'.toNat, z < y) ∧
    (∀ z ∈ slicePref (outCur.set k.toNat x) (k.toNat + 1),
      ∀ y ∈ sliceSuf bArr bOff lb j'.toNat, z < y) := by
  intro hmsA hmsB
  obtain ⟨hpw, _, _⟩ := hsort_inv hmsA hmsB
  obtain ⟨hzx, hxyA, hxyB⟩ := hxy hmsA hmsB
  rw [slicePref_set_eq hk1 hk_cur]
  refine ⟨List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _,
      fun a ha _ hb => by simp only [List.mem_singleton] at hb; rw [hb]; exact hzx a ha⟩,
    fun z hz y hy => ?_, fun z hz y hy => ?_⟩
  · rw [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact Nat.lt_trans (hzx z hz) (hxyA y hy)
    · exact hxyA y hy
  · rw [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact Nat.lt_trans (hzx z hz) (hxyB y hy)
    · exact hxyB y hy

private theorem munion_skip_inv {outPtr aBase bBase : BitVec 64}
    {out0 aArr bArr outCur : List (BitVec 32)} {aOff bOff idx0 la lb : Nat}
    {sym i j k : BitVec 32} {g : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    (hla32 : la + 1 < 2 ^ 32) (hi1 : 1 ≤ i.toNat) (hi_le_la : i.toNat ≤ la)
    (hj1 : 1 ≤ j.toNat) (hjle : j.toNat ≤ lb + 1) (hk1 : 1 ≤ k.toNat)
    (hk_bd : k.toNat ≤ (i.toNat - 1) + (j.toNat - 1) + 1 - (if idx0 < i.toNat then 1 else 0))
    (hout_cur_len : outCur.length = out0.length)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (ha_eq : aArr.getD (aOff + i.toNat) 0#32 = sym)
    (hm' : (array (t := i32) outPtr outCur ⋆ array (t := i32) aBase aArr ⋆
      array (t := i32) bBase bArr ⋆ R) m') :
    MunionInv outPtr aBase bBase out0 aArr bArr aOff bOff idx0 la lb sym R
      ((la + 1 - (i + 1#32).toNat) + (lb + 1 - j.toNat)) (i + 1#32, j, k, g, ⟨⟩) m' := by
  have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
  have hskip_bd : k.toNat ≤ (i.toNat + 1 - 1) + (j.toNat - 1) + 1 -
      (if idx0 < i.toNat + 1 then 1 else 0) := by
    by_cases heq : i.toNat = idx0
    · have h1 : ¬ idx0 < i.toNat := by omega
      have h2 : idx0 < i.toNat + 1 := by omega
      simp only [h1, h2, ↓reduceIte] at hk_bd ⊢; omega
    · by_cases hlt : idx0 < i.toNat
      · have h2 : idx0 < i.toNat + 1 := by omega
        simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega
      · have h2 : ¬ idx0 < i.toNat + 1 := by omega
        simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega
  refine ⟨outCur, hout_cur_len, by omega, by omega, hj1, hjle, hk1,
    by rw [hip1]; exact hskip_bd, rfl, hpres, fun z => ?_, hsig_inv, fun hmsA hmsB => ?_, hm'⟩
  · rw [← hmem_inv z, hip1, mem_sliceSuf_succ hi_le_la z, ha_eq]
    by_cases hz : z = sym.toNat <;> simp [hz]
  · obtain ⟨hpw, hsa, hsb⟩ := hsort_inv hmsA hmsB
    refine ⟨hpw, fun z hz y hy => hsa z hz y ?_, hsb⟩
    rw [hip1] at hy; rw [mem_sliceSuf_succ hi_le_la]; exact Or.inr hy

private theorem munion_push_a_inv {outPtr aBase bBase : BitVec 64}
    {out0 aArr bArr outCur : List (BitVec 32)} {aOff bOff idx0 la lb : Nat}
    {sym i j k : BitVec 32} {g sig : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    (hla32 : la + 1 < 2 ^ 32) (hsum32 : la + lb < 2 ^ 32)
    (hi1 : 1 ≤ i.toNat) (hi_le_la : i.toNat ≤ la) (hj1 : 1 ≤ j.toNat) (hjle : j.toNat ≤ lb + 1)
    (hk1 : 1 ≤ k.toNat) (hk_lt_len : k.toNat < la + lb)
    (hk_bd : k.toNat ≤ (i.toNat - 1) + (j.toNat - 1) + 1 - (if idx0 < i.toNat then 1 else 0))
    (hout_cur_len : outCur.length = out0.length) (hk_lt_out : k.toNat < outCur.length)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (hlt_a : aOff + i.toNat < aArr.length)
    (hla_eq : la = (aArr.getD aOff 0#32).toNat)
    (hne_s : aArr.getD (aOff + i.toNat) 0#32 ≠ sym)
    (hne_idx : i.toNat ≠ idx0)
    (hsig : sig = sigBit (aArr[aOff + i.toNat]'hlt_a))
    (hb_lt : MonoSorted bArr bOff →
      ∀ y ∈ sliceSuf bArr bOff lb j.toNat, (aArr[aOff + i.toNat]'hlt_a).toNat < y)
    (hm' : (array (t := i32) outPtr (outCur.set k.toNat (aArr[aOff + i.toNat]'hlt_a)) ⋆
      array (t := i32) aBase aArr ⋆ array (t := i32) bBase bArr ⋆ R) m') :
    MunionInv outPtr aBase bBase out0 aArr bArr aOff bOff idx0 la lb sym R
      ((la + 1 - (i + 1#32).toNat) + (lb + 1 - j.toNat))
      (i + 1#32, j, k + 1#32, g ||| sig, ⟨⟩) m' := by
  have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 32)]
  have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
  have hst := munion_step_write hk1 hk_lt_out hpres hmem_inv hsig_inv
    (aArr[aOff + i.toNat]'hlt_a) (i + 1#32) j (fun z => by
      have hsuf := mem_sliceSuf_succ (xs := aArr) (off := aOff) hi_le_la z
      rw [hip1, hsuf, getD_eq_getElem aArr 0#32 hlt_a]
      have hne_nat : (aArr[aOff + i.toNat]'hlt_a).toNat ≠ sym.toNat :=
        fun he => hne_s (by rw [getD_eq_getElem aArr 0#32 hlt_a]; exact BitVec.eq_of_toNat_eq he)
      by_cases hz : z = (aArr[aOff + i.toNat]'hlt_a).toNat <;> simp [hz, hne_nat])
  have hsr := munion_step_sort hk1 hk_lt_out hsort_inv (aArr[aOff + i.toNat]'hlt_a) (i + 1#32) j
    (fun hmsA hmsB => by
      obtain ⟨_, hsa, _⟩ := hsort_inv hmsA hmsB
      have hx_mem : (aArr[aOff + i.toNat]'hlt_a).toNat ∈ sliceSuf aArr aOff la i.toNat := by
        rw [mem_sliceSuf_succ hi_le_la]; exact Or.inl (by rw [getD_eq_getElem aArr 0#32 hlt_a])
      refine ⟨fun z hz => hsa z hz _ hx_mem, fun y hy => ?_, hb_lt hmsB⟩
      rw [hip1] at hy; rw [hla_eq] at hy
      have := sliceSuf_head_lt hmsA hi1 (by rw [← hla_eq]; exact hi_le_la) y hy
      rwa [← getD_eq_getElem aArr 0#32 hlt_a])
  refine ⟨outCur.set k.toNat (aArr[aOff + i.toNat]'hlt_a), by simp [hout_cur_len],
    by omega, by omega, hj1, hjle, by omega, ?_, rfl, by rw [hkp1]; exact hst.1,
    by rw [hkp1]; exact hst.2.1, by rw [hkp1, hsig]; exact hst.2.2, by rw [hkp1]; exact hsr, hm'⟩
  rw [hkp1, hip1]
  by_cases hlt : idx0 < i.toNat
  · have h2 : idx0 < i.toNat + 1 := by omega
    simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega
  · have hlt' : i.toNat < idx0 := by omega
    have h2 : ¬ idx0 < i.toNat + 1 := by omega
    simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega

private theorem munion_push_b_inv {outPtr aBase bBase : BitVec 64}
    {out0 aArr bArr outCur : List (BitVec 32)} {aOff bOff idx0 la lb : Nat}
    {sym i j k : BitVec 32} {g sig : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    (hlb32 : lb + 1 < 2 ^ 32) (hsum32 : la + lb < 2 ^ 32)
    (hi1 : 1 ≤ i.toNat) (hile : i.toNat ≤ la + 1) (hj1 : 1 ≤ j.toNat) (hj_le_lb : j.toNat ≤ lb)
    (hk1 : 1 ≤ k.toNat) (hk_lt_len : k.toNat < la + lb)
    (hk_bd' : k.toNat + 1 ≤ (i.toNat - 1) + (j.toNat + 1 - 1) + 1 -
      (if idx0 < i.toNat then 1 else 0))
    (hout_cur_len : outCur.length = out0.length) (hk_lt_out : k.toNat < outCur.length)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (hlt_b : bOff + j.toNat < bArr.length)
    (hlb_eq : lb = (bArr.getD bOff 0#32).toNat)
    (hsig : sig = sigBit (bArr[bOff + j.toNat]'hlt_b))
    (ha_lt : MonoSorted aArr aOff →
      ∀ y ∈ sliceSuf aArr aOff la i.toNat, (bArr[bOff + j.toNat]'hlt_b).toNat < y)
    (hm' : (array (t := i32) outPtr (outCur.set k.toNat (bArr[bOff + j.toNat]'hlt_b)) ⋆
      array (t := i32) aBase aArr ⋆ array (t := i32) bBase bArr ⋆ R) m') :
    MunionInv outPtr aBase bBase out0 aArr bArr aOff bOff idx0 la lb sym R
      ((la + 1 - i.toNat) + (lb + 1 - (j + 1#32).toNat))
      (i, j + 1#32, k + 1#32, g ||| sig, ⟨⟩) m' := by
  have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 32)]
  have hjp1 : (j + 1#32).toNat = j.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
  have hst := munion_step_write hk1 hk_lt_out hpres hmem_inv hsig_inv
    (bArr[bOff + j.toNat]'hlt_b) i (j + 1#32) (fun z => by
      have hsufB := mem_sliceSuf_succ (xs := bArr) (off := bOff) hj_le_lb z
      rw [hjp1, hsufB, getD_eq_getElem bArr 0#32 hlt_b]
      by_cases hz : z = (bArr[bOff + j.toNat]'hlt_b).toNat <;> simp [hz])
  have hsr := munion_step_sort hk1 hk_lt_out hsort_inv (bArr[bOff + j.toNat]'hlt_b) i (j + 1#32)
    (fun hmsA hmsB => by
      obtain ⟨_, _, hsb⟩ := hsort_inv hmsA hmsB
      have hx_mem : (bArr[bOff + j.toNat]'hlt_b).toNat ∈ sliceSuf bArr bOff lb j.toNat := by
        rw [mem_sliceSuf_succ hj_le_lb]; exact Or.inl (by rw [getD_eq_getElem bArr 0#32 hlt_b])
      refine ⟨fun z hz => hsb z hz _ hx_mem, ha_lt hmsA, fun y hy => ?_⟩
      rw [hjp1] at hy; rw [hlb_eq] at hy
      have := sliceSuf_head_lt hmsB hj1 (by rw [← hlb_eq]; exact hj_le_lb) y hy
      rwa [← getD_eq_getElem bArr 0#32 hlt_b])
  exact ⟨outCur.set k.toNat (bArr[bOff + j.toNat]'hlt_b), by simp [hout_cur_len],
    hi1, hile, by omega, by omega, by omega, by rw [hkp1, hjp1]; exact hk_bd', rfl,
    by rw [hkp1]; exact hst.1, by rw [hkp1]; exact hst.2.1,
    by rw [hkp1, hsig]; exact hst.2.2, by rw [hkp1]; exact hsr, hm'⟩

private theorem munion_push_ab_inv {outPtr aBase bBase : BitVec 64}
    {out0 aArr bArr outCur : List (BitVec 32)} {aOff bOff idx0 la lb : Nat}
    {sym i j k : BitVec 32} {g sig : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    (hla32 : la + 1 < 2 ^ 32) (hlb32 : lb + 1 < 2 ^ 32) (hsum32 : la + lb < 2 ^ 32)
    (hi1 : 1 ≤ i.toNat) (hi_le_la : i.toNat ≤ la) (hj1 : 1 ≤ j.toNat) (hj_le_lb : j.toNat ≤ lb)
    (hk1 : 1 ≤ k.toNat) (hk_lt_len : k.toNat < la + lb)
    (hk_bd : k.toNat ≤ (i.toNat - 1) + (j.toNat - 1) + 1 - (if idx0 < i.toNat then 1 else 0))
    (hout_cur_len : outCur.length = out0.length) (hk_lt_out : k.toNat < outCur.length)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (hlt_a : aOff + i.toNat < aArr.length) (hlt_b : bOff + j.toNat < bArr.length)
    (hla_eq : la = (aArr.getD aOff 0#32).toNat) (hlb_eq : lb = (bArr.getD bOff 0#32).toNat)
    (hne_s : aArr.getD (aOff + i.toNat) 0#32 ≠ sym)
    (hne_idx : i.toNat ≠ idx0)
    (heq_ab : aArr[aOff + i.toNat]'hlt_a = bArr[bOff + j.toNat]'hlt_b)
    (hsig : sig = sigBit (aArr[aOff + i.toNat]'hlt_a))
    (hm' : (array (t := i32) outPtr (outCur.set k.toNat (aArr[aOff + i.toNat]'hlt_a)) ⋆
      array (t := i32) aBase aArr ⋆ array (t := i32) bBase bArr ⋆ R) m') :
    MunionInv outPtr aBase bBase out0 aArr bArr aOff bOff idx0 la lb sym R
      ((la + 1 - (i + 1#32).toNat) + (lb + 1 - (j + 1#32).toNat))
      (i + 1#32, j + 1#32, k + 1#32, g ||| sig, ⟨⟩) m' := by
  have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 32)]
  have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
  have hjp1 : (j + 1#32).toNat = j.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
  have hst := munion_step_write hk1 hk_lt_out hpres hmem_inv hsig_inv
    (aArr[aOff + i.toNat]'hlt_a) (i + 1#32) (j + 1#32) (fun z => by
      have hsufA := mem_sliceSuf_succ (xs := aArr) (off := aOff) hi_le_la z
      have hsufB := mem_sliceSuf_succ (xs := bArr) (off := bOff) hj_le_lb z
      rw [hip1, hjp1, hsufA, hsufB, getD_eq_getElem aArr 0#32 hlt_a,
        getD_eq_getElem bArr 0#32 hlt_b, ← heq_ab]
      have hne_nat : (aArr[aOff + i.toNat]'hlt_a).toNat ≠ sym.toNat :=
        fun he => hne_s (by rw [getD_eq_getElem aArr 0#32 hlt_a]; exact BitVec.eq_of_toNat_eq he)
      by_cases hz : z = (aArr[aOff + i.toNat]'hlt_a).toNat <;> simp [hz, hne_nat])
  have hsr := munion_step_sort hk1 hk_lt_out hsort_inv (aArr[aOff + i.toNat]'hlt_a)
    (i + 1#32) (j + 1#32) (fun hmsA hmsB => by
      obtain ⟨_, hsa, _⟩ := hsort_inv hmsA hmsB
      have hx_mem : (aArr[aOff + i.toNat]'hlt_a).toNat ∈ sliceSuf aArr aOff la i.toNat := by
        rw [mem_sliceSuf_succ hi_le_la]; exact Or.inl (by rw [getD_eq_getElem aArr 0#32 hlt_a])
      refine ⟨fun z hz => hsa z hz _ hx_mem, fun y hy => ?_, fun y hy => ?_⟩
      · rw [hip1, hla_eq] at hy
        have := sliceSuf_head_lt hmsA hi1 (by rw [← hla_eq]; exact hi_le_la) y hy
        rwa [← getD_eq_getElem aArr 0#32 hlt_a]
      · rw [hjp1, hlb_eq] at hy
        have := sliceSuf_head_lt hmsB hj1 (by rw [← hlb_eq]; exact hj_le_lb) y hy
        rw [getD_eq_getElem bArr 0#32 hlt_b, ← heq_ab] at this; exact this)
  refine ⟨outCur.set k.toNat (aArr[aOff + i.toNat]'hlt_a), by simp [hout_cur_len],
    by omega, by omega, by omega, by omega, by omega, ?_, rfl, by rw [hkp1]; exact hst.1,
    by rw [hkp1]; exact hst.2.1, by rw [hkp1, hsig]; exact hst.2.2, by rw [hkp1]; exact hsr, hm'⟩
  rw [hkp1, hip1, hjp1]
  by_cases hlt : idx0 < i.toNat
  · have h2 : idx0 < i.toNat + 1 := by omega
    simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega
  · have hlt' : i.toNat < idx0 := by omega
    have h2 : ¬ idx0 < i.toNat + 1 := by omega
    simp only [hlt, h2, ↓reduceIte] at hk_bd ⊢; omega

private theorem munion_exit_post {outPtr aBase bBase : BitVec 64}
    {out0 aArr bArr outCur : List (BitVec 32)} {aOff bOff la lb : Nat}
    {sym i j k : BitVec 32} {g : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]}
    (hk1 : 1 ≤ k.toNat) (hkl : k.toNat ≤ la + lb) (h0_lt : 0 < outCur.length)
    (hout_cur_len : outCur.length = out0.length)
    (hi_done : i.toNat = la + 1) (hj_done : j.toNat = lb + 1)
    (hpres : ∀ idx, idx < 1 ∨ k.toNat ≤ idx → outCur.getD idx 0#32 = out0.getD idx 0#32)
    (hmem_inv : ∀ z, (z ∈ slicePref outCur k.toNat ∨
      (z ∈ sliceSuf aArr aOff la i.toNat ∧ z ≠ sym.toNat) ∨
      z ∈ sliceSuf bArr bOff lb j.toNat) ↔
      ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff))
    (hsig_inv : ∀ z ∈ slicePref outCur k.toNat, (g &&& sigBit (BitVec.ofNat 32 z)) ≠ 0#64)
    (hsort_inv : MonoSorted aArr aOff → MonoSorted bArr bOff →
      (slicePref outCur k.toNat).Pairwise (· < ·) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf aArr aOff la i.toNat, z < y) ∧
      (∀ z ∈ slicePref outCur k.toNat, ∀ y ∈ sliceSuf bArr bOff lb j.toNat, z < y))
    (hm : (array (t := i32) outPtr (outCur.set 0 (k - 1#32)) ⋆ array (t := i32) aBase aArr ⋆
      array (t := i32) bBase bArr ⋆ R) m)
    (hQ : ∀ (g : BitVec 64) (out' : List (BitVec 32)) (m' : Mem 64),
      out'.length = out0.length →
      (out'.getD 0 0#32).toNat + 1 ≤ la + lb →
      (∀ z, z ∈ symListAt out' 0 ↔
        ((z ∈ symListAt aArr aOff ∧ z ≠ sym.toNat) ∨ z ∈ symListAt bArr bOff)) →
      (MonoSorted aArr aOff → MonoSorted bArr bOff → MonoSorted out' 0) →
      (∀ x ∈ symListAt out' 0, (g &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64) →
      (∀ idx, la + lb ≤ idx → out'.getD idx 0#32 = out0.getD idx 0#32) →
      (array (t := i32) outPtr out' ⋆ array (t := i32) aBase aArr ⋆
        array (t := i32) bBase bArr ⋆ R) m' →
      Q (g, ⟨⟩) m') :
    Q (g, ⟨⟩) m := by
  have hksub : (k - 1#32).toNat = k.toNat - 1 := by
    have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; exact hk1)), h1]
  have hsym_eq : symListAt (outCur.set 0 (k - 1#32)) 0 = slicePref outCur k.toNat := by
    rw [symListAt_set_zero outCur (k - 1#32) h0_lt, hksub]; rfl
  refine hQ g (outCur.set 0 (k - 1#32)) m (by simp [hout_cur_len]) ?_ ?_ ?_ ?_ ?_ hm
  · rw [getD_set_eq outCur 0#32 (k - 1#32) h0_lt]; simp only [↓reduceIte]; omega
  · intro z
    have hsA : sliceSuf aArr aOff la i.toNat = [] := by simp [sliceSuf, hi_done]
    have hsB : sliceSuf bArr bOff lb j.toNat = [] := by simp [sliceSuf, hj_done]
    rw [hsym_eq, ← hmem_inv z, hsA, hsB]; simp
  · intro hmsA hmsB; rw [MonoSorted, hsym_eq]; exact (hsort_inv hmsA hmsB).1
  · intro x hx; rw [hsym_eq] at hx; exact hsig_inv x hx
  · intro idx hidx
    rw [getD_set_eq outCur 0#32 (k - 1#32) h0_lt]
    simp only [show idx ≠ 0 by omega, ↓reduceIte]; exact hpres idx (by right; omega)

theorem ar_munion_wp (Γ : T.Env)
    (hSig : ∀ xs m Q X, arSigbitSpec xs m Q X → Γ "ar_sigbit" [i32] [i64] xs m Q X) :
    ∀ xs m Q X, arMunionSpec xs m Q X → Func.wp Γ ar_munion_body xs m Q X := by
  rintro ⟨outPtr, aPtr, sym, bPtr, ⟨⟩⟩ m Q X
    ⟨out0, aBase, aArr, aOff, bBase, bArr, bOff, R, haPtr, hbPtr, hA, hB, hla32, hlb32,
      ⟨idx0, hidx1, hidx_le, hidx_eq⟩, hout_len, hsum32, hm, hQ⟩
  subst haPtr; subst hbPtr
  let la := (aArr.getD aOff 0#32).toNat
  let lb := (bArr.getD bOff 0#32).toNat
  let Ra := array (t := i32) outPtr out0 ⋆ array (t := i32) bBase bArr ⋆ R
  let Rb := array (t := i32) outPtr out0 ⋆ array (t := i32) aBase aArr ⋆ R
  try c0_hsteps
  · exact wp_load_arr32 (base := aBase) (off := aOff) (i := 0) (R := Ra) (by simp) hA.1
      (sep_cast hm (by dsimp only [Ra]; ac_rfl)) (by
      try c0_hsteps
      · exact wp_load_arr32 (base := bBase) (off := bOff) (i := 0) (R := Rb) (by simp) hB.1
          (sep_cast hm (by dsimp only [Rb]; ac_rfl)) (by
          c0_hsteps
          refine wp_loop_group
            (MunionInv outPtr aBase bBase out0 aArr bArr aOff bOff idx0 la lb sym R) ?_ ?_
          · intro J rem ⟨i, j, k, g, ⟨⟩⟩ m' hrec
              ⟨outCur, hout_cur_len, hi1, hile, hj1, hjle, hk1, hk_bd, hrem, hpres, hmem_inv,
                hsig_inv, hsort_inv, hm'⟩
            let Ra' := array (t := i32) outPtr outCur ⋆ array (t := i32) bBase bArr ⋆ R
            let Rb' := array (t := i32) outPtr outCur ⋆ array (t := i32) aBase aArr ⋆ R
            have hk_w64 : (BitVec.setWidth 64 k).toNat = k.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
            c0_hsteps
            · -- `i <= la`, check `a[i] == s`
              have hi_le_la : i.toNat ≤ la := by
                have h0 : aArr[aOff + 0]'hA.1 = aArr[aOff]'hA.1 := rfl
                have hle' := hc
                rw [h0, ← getD_eq_getElem aArr 0#32 hA.1] at hle'
                exact hle'
              have hlt_a : aOff + i.toNat < aArr.length := by
                have := hA.2; omega
              try c0_hsteps
              · exact wp_load_arr32_idx (base := aBase) (off := aOff) (i := i) (R := Ra')
                  rfl hlt_a (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                    c0_hsteps
                    · -- `a[i] == sym`: skip `i`
                      have ha_eq : aArr.getD (aOff + i.toNat) 0#32 = sym := by
                        rw [getD_eq_getElem aArr 0#32 hlt_a]
                        exact ‹aArr[aOff + i.toNat]'hlt_a = sym›
                      exact hrec ((la + 1 - (i + 1#32).toNat) + (lb + 1 - j.toNat))
                        (i + 1#32, j, k, g, ⟨⟩) m' (by
                          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]; omega)
                        (munion_skip_inv hla32 hi1 hi_le_la hj1 hjle hk1 hk_bd hout_cur_len hpres
                          hmem_inv hsig_inv hsort_inv ha_eq hm')
                    · -- `a[i] != sym`, `j > lb`: `x = a[i]`, `i' = i+1`, `j' = j`
                      have hne_s : aArr.getD (aOff + i.toNat) 0#32 ≠ sym := by
                        rw [getD_eq_getElem aArr 0#32 hlt_a]
                        exact ‹aArr[aOff + i.toNat]'hlt_a ≠ sym›
                      have hk_lt_len : k.toNat < la + lb := by
                        by_cases hlt : idx0 < i.toNat
                        · simp only [hlt, ↓reduceIte] at hk_bd; omega
                        · have hne_i : i.toNat ≠ idx0 := fun h => hne_s (by rw [h, hidx_eq])
                          simp only [hlt, ↓reduceIte] at hk_bd; omega
                      have hk_lt_out : k.toNat < outCur.length := by omega
                      have hj_gt_lb : lb < j.toNat := by
                        have hlt_nat : (bArr[bOff + 0]'hB.1).toNat < j.toNat := hc
                        have h0 : (bArr[bOff + 0]'hB.1).toNat = (bArr.getD bOff 0#32).toNat :=
                          (congrArg BitVec.toNat (getD_eq_getElem bArr 0#32 hB.1)).symm
                        omega
                      exact wp_load_arr32_idx (base := aBase) (off := aOff) (i := i) (R := Ra')
                        rfl hlt_a (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                        try c0_hsteps
                        refine wp_call_of_spec _ _ (hSig _ _ _ _ (fun sig hsig => ?_))
                        c0_hsteps
                        dsimp only [Arg.val] at hsig
                        refine hrec ((la + 1 - (i + 1#32).toNat) + (lb + 1 - j.toNat))
                          (i + 1#32, j, k + 1#32, g ||| sig, ⟨⟩) _ (by
                            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]; omega)
                          (munion_push_a_inv hla32 hsum32 hi1 hi_le_la hj1 hjle hk1 hk_lt_len hk_bd
                            hout_cur_len hk_lt_out hpres hmem_inv hsig_inv hsort_inv hlt_a rfl hne_s
                            (fun h => hne_s (by rw [h, hidx_eq])) hsig
                            (fun _ y hy => by rw [sliceSuf_gt_eq_nil hj_gt_lb] at hy; simp at hy)
                            (by
                              have hstore := ‹(array outPtr _ ⋆ _) _›
                              rw [hk_w64] at hstore; exact sep_cast hstore (by ac_rfl))))
                    · -- `a[i] != sym`, `j <= lb` -> load `a[i]`, load `b[j]`, compare
                      have hne_s : aArr.getD (aOff + i.toNat) 0#32 ≠ sym := by
                        rw [getD_eq_getElem aArr 0#32 hlt_a]
                        exact ‹aArr[aOff + i.toNat]'hlt_a ≠ sym›
                      have hk_lt_len : k.toNat < la + lb := by
                        by_cases hlt : idx0 < i.toNat
                        · simp only [hlt, ↓reduceIte] at hk_bd; omega
                        · have hne_i : i.toNat ≠ idx0 := fun h => hne_s (by rw [h, hidx_eq])
                          simp only [hlt, ↓reduceIte] at hk_bd; omega
                      have hk_lt_out : k.toNat < outCur.length := by omega
                      have hj_le_lb : j.toNat ≤ lb := by
                        have hnot : ¬ (bArr[bOff + 0]'hB.1).toNat < j.toNat := ‹_›
                        have h0 : (bArr[bOff + 0]'hB.1).toNat = (bArr.getD bOff 0#32).toNat := by
                          symm; exact congrArg BitVec.toNat (getD_eq_getElem bArr 0#32 hB.1)
                        omega
                      have hlt_b : bOff + j.toNat < bArr.length := by
                        have := hB.2; omega
                      exact wp_load_arr32_idx (base := aBase) (off := aOff) (i := i) (R := Ra')
                        rfl hlt_a (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                        try c0_hsteps
                        · exact wp_load_arr32_idx (base := bBase) (off := bOff) (i := j) (R := Rb')
                            rfl hlt_b (sep_cast hm' (by dsimp only [Rb']; ac_rfl)) (by
                            c0_hsteps
                            · -- `a[i] < b[j]`: x = a[i], i' = i+1, j' = j
                              have hab_lt : (aArr[aOff + i.toNat]'hlt_a).toNat <
                                  (bArr[bOff + j.toNat]'hlt_b).toNat := hc
                              try c0_hsteps
                              exact wp_load_arr32_idx (base := aBase) (off := aOff) (i := i)
                                (R := Ra') rfl hlt_a
                                (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                                try c0_hsteps
                                refine wp_call_of_spec _ _ (hSig _ _ _ _ (fun sig hsig => ?_))
                                c0_hsteps
                                dsimp only [Arg.val] at hsig
                                refine hrec ((la + 1 - (i + 1#32).toNat) + (lb + 1 - j.toNat))
                                  (i + 1#32, j, k + 1#32, g ||| sig, ⟨⟩) _ (by
                                    rw [BitVec.toNat_add,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]; omega)
                                  (munion_push_a_inv hla32 hsum32 hi1 hi_le_la hj1 hjle hk1
                                    hk_lt_len hk_bd hout_cur_len hk_lt_out hpres hmem_inv hsig_inv
                                    hsort_inv hlt_a rfl hne_s (fun h => hne_s (by rw [h, hidx_eq]))
                                    hsig (fun hmsB y hy => by
                                      rw [mem_sliceSuf_succ hj_le_lb] at hy
                                      rcases hy with rfl | hy'
                                      · rwa [getD_eq_getElem bArr 0#32 hlt_b]
                                      · have := sliceSuf_head_lt hmsB hj1 hj_le_lb y hy'
                                        rw [getD_eq_getElem bArr 0#32 hlt_b] at this; omega)
                                    (by
                                      have hs := ‹(array outPtr _ ⋆ _) _›; rw [hk_w64] at hs
                                      exact sep_cast hs (by ac_rfl))))
                            · -- `¬ (a[i] < b[j])`: reload `a[i]`, `b[j]`
                              try c0_hsteps
                              · exact wp_load_arr32_idx (base := aBase) (off := aOff) (i := i)
                                  (R := Ra') rfl hlt_a
                                  (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                                  try c0_hsteps
                                  · exact wp_load_arr32_idx (base := bBase) (off := bOff) (i := j)
                                      (R := Rb') rfl hlt_b
                                      (sep_cast hm' (by dsimp only [Rb']; ac_rfl)) (by
                                      c0_hsteps
                                      · -- `a[i] > b[j]`: `x = b[j]`, `i' = i`, `j' = j+1`
                                        have hba_lt : (bArr[bOff + j.toNat]'hlt_b).toNat <
                                            (aArr[aOff + i.toNat]'hlt_a).toNat := hc
                                        try c0_hsteps
                                        exact wp_load_arr32_idx (base := bBase) (off := bOff)
                                          (i := j) (R := Rb') rfl hlt_b
                                          (sep_cast hm' (by dsimp only [Rb']; ac_rfl)) (by
                                          try c0_hsteps
                                          refine wp_call_of_spec _ _
                                            (hSig _ _ _ _ (fun sig hsig => ?_))
                                          c0_hsteps
                                          dsimp only [Arg.val] at hsig
                                          refine hrec
                                            ((la + 1 - i.toNat) + (lb + 1 - (j + 1#32).toNat))
                                            (i, j + 1#32, k + 1#32, g ||| sig, ⟨⟩) _ (by
                                              rw [BitVec.toNat_add,
                                                show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
                                              omega)
                                            (munion_push_b_inv hlb32 hsum32 hi1 hile hj1
                                              hj_le_lb hk1
                                              hk_lt_len (by
                                                by_cases hlt : idx0 < i.toNat
                                                · simp only [hlt, ↓reduceIte] at hk_bd ⊢; omega
                                                · have hne_i : i.toNat ≠ idx0 := fun h =>
                                                    hne_s (by rw [h, hidx_eq])
                                                  simp only [hlt, ↓reduceIte] at hk_bd ⊢; omega)
                                              hout_cur_len hk_lt_out
                                              hpres hmem_inv hsig_inv hsort_inv hlt_b rfl hsig
                                              (fun hmsA y hy => by
                                                rw [mem_sliceSuf_succ hi_le_la] at hy
                                                rcases hy with rfl | hy'
                                                · rwa [getD_eq_getElem aArr 0#32 hlt_a]
                                                · have := sliceSuf_head_lt hmsA hi1 hi_le_la y hy'
                                                  rw [getD_eq_getElem aArr 0#32 hlt_a] at this
                                                  omega)
                                              (by
                                                have hs := ‹(array outPtr _ ⋆ _) _›
                                                rw [hk_w64] at hs; exact sep_cast hs (by ac_rfl))))
                                      · -- `a[i] == b[j]`: `x = a[i]`, `i' = i+1`, `j' = j+1`
                                        try c0_hsteps
                                        exact wp_load_arr32_idx (base := aBase) (off := aOff)
                                          (i := i) (R := Ra') rfl hlt_a
                                          (sep_cast hm' (by dsimp only [Ra']; ac_rfl)) (by
                                          try c0_hsteps
                                          refine wp_call_of_spec _ _
                                            (hSig _ _ _ _ (fun sig hsig => ?_))
                                          c0_hsteps
                                          dsimp only [Arg.val] at hsig
                                          have heq_ab :
                                              (aArr[aOff + i.toNat]'hlt_a) =
                                                (bArr[bOff + j.toNat]'hlt_b) :=
                                            bv32_eq_of_ult_false ‹_› ‹_›
                                          refine hrec ((la + 1 - (i + 1#32).toNat) +
                                                (lb + 1 - (j + 1#32).toNat))
                                              (i + 1#32, j + 1#32, k + 1#32, g ||| sig, ⟨⟩) _
                                              (by
                                                rw [BitVec.toNat_add, BitVec.toNat_add,
                                                  show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                  Nat.mod_eq_of_lt
                                                    (by omega : i.toNat + 1 < 2 ^ 32),
                                                  Nat.mod_eq_of_lt
                                                    (by omega : j.toNat + 1 < 2 ^ 32)]
                                                omega)
                                              (munion_push_ab_inv hla32 hlb32 hsum32 hi1 hi_le_la
                                                hj1 hj_le_lb hk1 hk_lt_len hk_bd hout_cur_len
                                                hk_lt_out hpres hmem_inv hsig_inv hsort_inv
                                                hlt_a hlt_b rfl rfl hne_s
                                                (fun h => hne_s (by rw [h, hidx_eq])) heq_ab hsig
                                                (by
                                                  have hs := ‹(array outPtr _ ⋆ _) _›
                                                  rw [hk_w64] at hs
                                                  exact sep_cast hs (by ac_rfl)))))))))
            · -- `i > la`, `j <= lb` -> `x = b[j]`, `i' = i`, `j' = j+1`
              have hi_eq : i.toNat = la + 1 := by
                have hlt_nat : (aArr[aOff + 0]'hA.1).toNat < i.toNat := ‹_›
                have h0 : (aArr[aOff + 0]'hA.1).toNat = (aArr.getD aOff 0#32).toNat :=
                  (congrArg BitVec.toNat (getD_eq_getElem aArr 0#32 hA.1)).symm
                omega
              have hj_le_lb : j.toNat ≤ lb := by
                have h0 : bArr[bOff + 0]'hB.1 = bArr[bOff]'hB.1 := rfl
                have hle' : j ≤ bArr[bOff + 0]'hB.1 := ‹_›
                rw [h0, ← getD_eq_getElem bArr 0#32 hB.1] at hle'
                exact hle'
              have hk_lt_len : k.toNat < la + lb := by
                have hif : idx0 < i.toNat := by omega
                simp only [hif, ↓reduceIte] at hk_bd; omega
              have hk_lt_out : k.toNat < outCur.length := by omega
              have hlt_b : bOff + j.toNat < bArr.length := by have := hB.2; omega
              try c0_hsteps
              · exact wp_load_arr32_idx (base := bBase) (off := bOff) (i := j) (R := Rb')
                  rfl hlt_b (sep_cast hm' (by dsimp only [Rb']; ac_rfl)) (by
                  try c0_hsteps
                  refine wp_call_of_spec _ _ (hSig _ _ _ _ (fun sig hsig => ?_))
                  c0_hsteps
                  dsimp only [Arg.val] at hsig
                  exact hrec ((la + 1 - i.toNat) + (lb + 1 - (j + 1#32).toNat))
                    (i, j + 1#32, k + 1#32, g ||| sig, ⟨⟩) _ (by
                      rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]; omega)
                    (munion_push_b_inv hlb32 hsum32 hi1 hile hj1 hj_le_lb hk1 hk_lt_len
                      (by have hif : idx0 < i.toNat := by omega
                          simp only [hif, ↓reduceIte] at hk_bd ⊢; omega)
                      hout_cur_len hk_lt_out hpres hmem_inv hsig_inv hsort_inv hlt_b rfl hsig
                      (fun _ y hy => by
                        rw [sliceSuf_gt_eq_nil (by omega : la < i.toNat)] at hy; simp at hy)
                      (by
                        have hstore := ‹(array outPtr _ ⋆ _) _›
                        rw [hk_w64] at hstore; exact sep_cast hstore (by ac_rfl))))
            · -- `i > la` and `j > lb`: exit loop, store `out[0] = k - 1`, return `g`
              have hi_done : i.toNat = la + 1 := by
                have hlt_nat : (aArr[aOff + 0]'hA.1).toNat < i.toNat :=
                  Nat.lt_of_not_le ‹¬ i.toNat ≤ (aArr[aOff + 0]'hA.1).toNat›
                have h0 : (aArr[aOff + 0]'hA.1).toNat = (aArr.getD aOff 0#32).toNat :=
                  (congrArg BitVec.toNat (getD_eq_getElem aArr 0#32 hA.1)).symm
                omega
              have hj_done : j.toNat = lb + 1 := by
                have hlt_nat : (bArr[bOff + 0]'hB.1).toNat < j.toNat :=
                  Nat.lt_of_not_le ‹¬ j.toNat ≤ (bArr[bOff + 0]'hB.1).toNat›
                have h0 : (bArr[bOff + 0]'hB.1).toNat = (bArr.getD bOff 0#32).toNat :=
                  (congrArg BitVec.toNat (getD_eq_getElem bArr 0#32 hB.1)).symm
                omega
              have hkl : k.toNat ≤ la + lb := by
                have hif : idx0 < i.toNat := by omega
                simp only [hif, ↓reduceIte] at hk_bd; omega
              have h0_lt : 0 < outCur.length := by omega
              try c0_hsteps
              have hstore := ‹(array outPtr _ ⋆ _) _›
              simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hstore
              refine munion_exit_post (outPtr := outPtr) (aBase := aBase) (bBase := bBase)
                (R := R) hk1 hkl h0_lt hout_cur_len hi_done hj_done hpres
                hmem_inv hsig_inv hsort_inv ?_ hQ
              rw [show (1 : BitVec 32) = 1#32 from rfl] at hstore
              exact sep_cast hstore (by ac_rfl)
          · intro J hJ; c0_hsteps
            have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
            have hnot1 : ¬ idx0 < 1 := by omega
            refine hJ ((la + 1 - 1) + (lb + 1 - 1)) (1#32, 1#32, 1#32, 0#64, ⟨⟩) m
              ⟨out0, rfl, by decide, by rw [h1_32]; omega, by decide, by rw [h1_32]; omega,
                by decide, by rw [h1_32]; simp only [hnot1, ↓reduceIte]; omega, rfl,
                fun idx _ => rfl, ?_, ?_, ?_, hm⟩
            · intro z; simp [slicePref, sliceSuf, symListAt, la, lb]
            · intro z hz; simp [slicePref] at hz
            · intro _ _; simp [slicePref]))

/-! ## 2. `ar_compact_wp` -/

def u32PadTail (p : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  region (p + BitVec.ofNat 64 (4 * n)) (align8 (4 * n) - 4 * n)

theorem arrayPad_u32_unfold (p : BitVec 64) (xs : List (BitVec 32)) :
    arrayPad i32 p xs = (array (t := i32) p xs ⋆ u32PadTail p xs.length) := by
  simp only [arrayPad, u32PadTail, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size]

theorem bv32_lt2_cases {x : BitVec 32} (hx : x.toNat < 2) : x = 0#32 ∨ x = 1#32 := by
  have hx' : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases hx' with h | h
  · left; exact BitVec.eq_of_toNat_eq h
  · right; exact BitVec.eq_of_toNat_eq h

theorem tMem_focus_eq (s : ArCtxState)
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 : List (BitVec 32)) :
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
          array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64)
            (if s.pc.toNat = 0 then pool1 else pool0) ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0 else tm1) ⋆
          rest)) ∧
      (∀ (s' : ArCtxState), s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl →
          s'.th = s.th → s'.pool = s.pool →
        ∀ (tmAct' poolDst' : List (BitVec 32)),
          tmAct'.length = (if s.tc.toNat = 0 then tm0 else tm1).length →
          poolDst'.length = (if s.pc.toNat = 0 then pool1 else pool0).length →
          tMem s' (if s.tc.toNat = 0 then tmAct' else tm0)
              (if s.tc.toNat = 0 then tm1 else tmAct') ts0 tl0 th0 ts1 tl1 th1
              (if s.pc.toNat = 0 then pool0 else poolDst')
              (if s.pc.toNat = 0 then poolDst' else pool1) =
            (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
                (if s.pc.toNat = 0 then pool0 else pool1) ⋆
              array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) poolDst' ⋆
              array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmAct' ⋆
              rest)) := by
  rcases bv32_lt2_cases hpc with hpc0 | hpc1 <;> rcases bv32_lt2_cases htc with htc0 | htc1
  · simp only [hpc0, htc0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.sub_zero, ↓reduceIte]
    refine ⟨array64 (s.ts.getD 0 0#64) ts0 ⋆ array64 (s.tl.getD 0 0#64) tl0 ⋆
      array64 (s.th.getD 0 0#64) th0 ⋆ arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆
      array64 (s.ts.getD 1 0#64) ts1 ⋆ array64 (s.tl.getD 1 0#64) tl1 ⋆
      array64 (s.th.getD 1 0#64) th1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length,
      by simp only [tMem, arrayPad_u32_unfold]; ac_rfl, fun _ hm hs hl hh hp _ _ h1 h2 => by
        simp only [tMem, hm, hs, hl, hh, hp, arrayPad_u32_unfold]; rw [h1, h2]; ac_rfl⟩
  · simp only [hpc0, htc1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      show ¬ (1 : Nat) = 0 by decide, Nat.sub_zero, ↓reduceIte]
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      array64 (s.ts.getD 1 0#64) ts1 ⋆ array64 (s.tl.getD 1 0#64) tl1 ⋆
      array64 (s.th.getD 1 0#64) th1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length,
      by simp only [tMem, arrayPad_u32_unfold]; ac_rfl, fun _ hm hs hl hh hp _ _ h1 h2 => by
        simp only [tMem, hm, hs, hl, hh, hp, arrayPad_u32_unfold]; rw [h1, h2]; ac_rfl⟩
  · simp only [hpc1, htc0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      show ¬ (1 : Nat) = 0 by decide, Nat.sub_self, ↓reduceIte]
    refine ⟨array64 (s.ts.getD 0 0#64) ts0 ⋆ array64 (s.tl.getD 0 0#64) tl0 ⋆
      array64 (s.th.getD 0 0#64) th0 ⋆ arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆
      array64 (s.ts.getD 1 0#64) ts1 ⋆ array64 (s.tl.getD 1 0#64) tl1 ⋆
      array64 (s.th.getD 1 0#64) th1 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length,
      by simp only [tMem, arrayPad_u32_unfold]; ac_rfl, fun _ hm hs hl hh hp _ _ h1 h2 => by
        simp only [tMem, hm, hs, hl, hh, hp, arrayPad_u32_unfold]; rw [h1, h2]; ac_rfl⟩
  · simp only [hpc1, htc1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      show ¬ (1 : Nat) = 0 by decide, Nat.sub_self, ↓reduceIte]
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      array64 (s.ts.getD 1 0#64) ts1 ⋆ array64 (s.tl.getD 1 0#64) tl1 ⋆
      array64 (s.th.getD 1 0#64) th1 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length,
      by simp only [tMem, arrayPad_u32_unfold]; ac_rfl, fun _ hm hs hl hh hp _ _ h1 h2 => by
        simp only [tMem, hm, hs, hl, hh, hp, arrayPad_u32_unfold]; rw [h1, h2]; ac_rfl⟩

private theorem monoTotalWords_congr {pool1 tm1 pool2 tm2 : List (BitVec 32)} {n : Nat}
    (h : ∀ p < n,
      (pool1.getD (tm1.getD p 0#32).toNat 0#32).toNat =
        (pool2.getD (tm2.getD p 0#32).toNat 0#32).toNat) :
    monoTotalWords pool1 tm1 n = monoTotalWords pool2 tm2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [monoTotalWords_succ, monoTotalWords_succ, ih (fun p hp => h p (Nat.lt_succ_of_lt hp)),
      h n (Nat.lt_succ_self n)]

theorem ar_compact_wp (Γ : T.Env) :
    ∀ xs m Q X, arCompactSpec xs m Q X → Func.wp Γ ar_compact_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, σ, R,
      hpc, htc, htn_le, htm0_len, htm1_len, hptop_le, hpcap32, hpool0_len, hpool1_len,
      hSlices, hTot, hm, hQ⟩
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let dstPool0 := if s.pc.toNat = 0 then pool1 else pool0
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  have hpc_xor : (s.pc ^^^ 1#32).toNat = 1 - s.pc.toNat := by
    rcases bv32_lt2_cases hpc with h | h <;> rw [h] <;> decide
  have hsrcTm_len : s.tcap.toNat ≤ srcTm.length := by dsimp only [srcTm]; split <;> assumption
  have hsrcPool_len : s.pcap.toNat ≤ srcPool.length := by
    dsimp only [srcPool]; split <;> assumption
  have hdstPool_len : s.pcap.toNat ≤ dstPool0.length := by
    dsimp only [dstPool0]; split <;> assumption
  obtain ⟨restT, hm_split, hfoc_all⟩ := tMem_focus_eq s hpc htc tm0 tm1
    ts0 tl0 th0 ts1 tl1 th1 pool0 pool1
  let Rt0 := array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstPool0 ⋆
    array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆ restT ⋆ R
  have hm_arr : (arCtxMem cx s ⋆ Rt0) m := by
    rw [hm_split] at hm; exact sep_cast hm (by dsimp only [Rt0]; ac_rfl)
  have hl_s : ArCtxLengthsOk s := (sep_pure_l.mp hm_arr).1
  have hpool_pc : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) =
      s.pool.getD s.pc.toNat 0#64 :=
    (getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hpc)).symm
  have hlt_xor : (s.pc ^^^ 1#32).toNat < 2 := by rw [hpc_xor]; omega
  have hpool_xor : s.pool[(s.pc ^^^ 1#32).toNat]'(by rw [hl_s.pool]; exact hlt_xor) =
      s.pool.getD (1 - s.pc.toNat) 0#64 := by
    rw [← getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hlt_xor), hpc_xor]
  have htm_tc : s.tm[s.tc.toNat]'(by rw [hl_s.tm]; exact htc) =
      s.tm.getD s.tc.toNat 0#64 := (getD_eq_getElem s.tm 0#64 (by rw [hl_s.tm]; exact htc)).symm
  c0_hsteps
  refine wp_loop_group (fun rem ⟨k, i, ⟨⟩⟩ m' => ∃ (tmCur dstCur : List (BitVec 32)),
      tmCur.length = srcTm.length ∧ dstCur.length = dstPool0.length ∧
      i.toNat ≤ s.tn.toNat ∧
      k.toNat = monoTotalWords srcPool srcTm i.toNat ∧
      k.toNat ≤ s.pcap.toNat ∧
      rem = s.tn.toNat - i.toNat ∧
      (∀ p < i.toNat,
        symListAt dstCur (tmCur.getD p 0#32).toNat = symListAt srcPool (srcTm.getD p 0#32).toNat ∧
        MonoSliceOk dstCur (tmCur.getD p 0#32).toNat k.toNat ∧
        (dstCur.getD (tmCur.getD p 0#32).toNat 0#32).toNat =
          (srcPool.getD (srcTm.getD p 0#32).toNat 0#32).toNat) ∧
      (∀ p, i.toNat ≤ p → tmCur.getD p 0#32 = srcTm.getD p 0#32) ∧
      (arCtxMem cx s ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstCur ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmCur ⋆ restT ⋆ R) m')
    ?_ ?_
  · intro J rem ⟨k, i, ⟨⟩⟩ m' hrec ⟨tmCur, dstCur, htmL, hdstL, hi_le, hk_eq, hk_cap, hrem,
      hPref, hTail, hm'⟩
    let Rtm := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstCur ⋆ restT ⋆ R
    c0_hsteps
    · -- Loop body: `i < s.tn`
      have hi_lt : i.toNat < s.tn.toNat := hc
      have hi_tm : i.toNat < tmCur.length := by omega
      have hsrcTm_i : srcTm.getD i.toNat 0#32 = tmCur[i.toNat]'hi_tm := by
        rw [← getD_eq_getElem tmCur 0#32 hi_tm, hTail i.toNat (le_refl _)]
      let mOff := (srcTm.getD i.toNat 0#32).toNat
      have hmSlice := hSlices i.toNat hi_lt
      have hm0_lt : mOff < srcPool.length := hmSlice.1
      have hmSlice_tot : monoTotalWords srcPool srcTm (i.toNat + 1) ≤ s.pcap.toNat := by
        have hmono : ∀ n, i.toNat + 1 ≤ n → monoTotalWords srcPool srcTm (i.toNat + 1) ≤
            monoTotalWords srcPool srcTm n := by
          intro n hn
          induction n with
          | zero => omega
          | succ n ih =>
            by_cases he : i.toNat + 1 = n + 1
            · rw [he]; exact le_refl _
            · rw [monoTotalWords_succ (n := n)]
              exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
        exact Nat.le_trans (hmono s.tn.toNat hi_lt) hTot
      have hk_len_cap : k.toNat + ((srcPool.getD mOff 0#32).toNat + 1) ≤ s.pcap.toNat := by
        rw [hk_eq, ← monoTotalWords_succ]; exact hmSlice_tot
      let Rsrc := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstCur ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmCur ⋆ restT ⋆ R
      try c0_hsteps
      · exact wp_load_arr32_idx (base := s.tm.getD s.tc.toNat 0#64) (off := 0) (i := i)
          (R := Rtm) (by rw [htm_tc]; simp) (by simpa using hi_tm)
          (sep_cast hm' (by dsimp only [Rtm]; ac_rfl)) (by
          rw [show tmCur[0 + i.toNat]'(by simpa using hi_tm) = srcTm.getD i.toNat 0#32 from by
            simp [← hsrcTm_i]]
          have hm0_nat : (BitVec.setWidth 64 (srcTm.getD i.toNat 0#32)).toNat = mOff := by
            have hlt64 : (srcTm.getD i.toNat 0#32).toNat < 2 ^ 64 := by
              have := (srcTm.getD i.toNat 0#32).isLt; omega
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt64]
          try c0_hsteps
          · exact wp_load_arr32_abs (base := s.pool.getD s.pc.toNat 0#64) (xs := srcPool)
              (i := BitVec.setWidth 64 (srcTm.getD i.toNat 0#32)) (R := Rsrc)
              (by rw [hpool_pc]; simp) (by rw [hm0_nat]; exact hm0_lt)
              (sep_cast hm' (by dsimp only [Rsrc]; ac_rfl)) (by
              let len := srcPool[(BitVec.setWidth 64 (srcTm.getD i.toNat 0#32)).toNat]'(by
                rw [hm0_nat]; exact hm0_lt)
              have hlen_eq : len.toNat = (srcPool.getD mOff 0#32).toNat := by
                dsimp only [len]
                simp only [hm0_nat]
                exact congrArg BitVec.toNat (getD_eq_getElem srcPool 0#32 hm0_lt).symm
              c0_hsteps
              refine wp_loop_group (fun jrem ⟨j, ⟨⟩⟩ m'' => ∃ dstIn : List (BitVec 32),
                  dstIn.length = dstCur.length ∧
                  j.toNat ≤ len.toNat + 1 ∧
                  jrem = len.toNat + 1 - j.toNat ∧
                  (∀ q < k.toNat, dstIn.getD q 0#32 = dstCur.getD q 0#32) ∧
                  (∀ t < j.toNat, dstIn.getD (k.toNat + t) 0#32 = srcPool.getD (mOff + t) 0#32) ∧
                  (arCtxMem cx s ⋆
                    array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                    array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstIn ⋆
                    array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmCur ⋆ restT ⋆ R) m'')
                ?_ ?_
              · intro J2 jrem ⟨j, ⟨⟩⟩ m'' hrec2
                  ⟨dstIn, hdstIn_len, hj_le, hjrem, hOld, hCopied, hm''⟩
                let Rsrc2 := arCtxMem cx s ⋆
                  array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstIn ⋆
                  array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmCur ⋆ restT ⋆ R
                let Rdst2 := arCtxMem cx s ⋆
                  array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                  array (t := i32) (s.tm.getD s.tc.toNat 0#64) tmCur ⋆ restT ⋆ R
                let Rtm2 := arCtxMem cx s ⋆
                  array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                  array (t := i32) (s.pool.getD (1 - s.pc.toNat) 0#64) dstIn ⋆ restT ⋆ R
                c0_hsteps
                · -- Inner loop step: `j <= len`
                  have hj_le_len : j.toNat ≤ len.toNat := hc
                  have hm_j : mOff + j.toNat < srcPool.length := by
                    have hm2 : mOff + 1 + (srcPool.getD mOff 0#32).toNat ≤ srcPool.length :=
                      hmSlice.2
                    rw [← hlen_eq] at hm2
                    omega
                  have hd_kj : k.toNat + j.toNat < dstIn.length := by omega
                  have hkj_nat : (k + BitVec.setWidth 64 j).toNat = k.toNat + j.toNat := by
                    have h2 : (2 ^ 32 : Nat) ≤ 2 ^ 64 := by decide
                    rw [BitVec.toNat_add, BitVec.toNat_setWidth,
                      Nat.mod_eq_of_lt (by have := j.isLt; omega), Nat.mod_eq_of_lt (by omega)]
                  have hjp1 : (j + 1#32).toNat = j.toNat + 1 := by
                    have := len.isLt
                    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
                  try c0_hsteps
                  · exact wp_load_arr32_idx (base := s.pool.getD s.pc.toNat 0#64) (off := mOff)
                      (i := j) (R := Rsrc2)
                      (by
                        rw [hpool_pc]
                        apply BitVec.eq_of_toNat_eq
                        simp [mOff, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
                          BitVec.toNat_ofNat, Nat.mul_comm _ 4])
                      hm_j (sep_cast hm'' (by dsimp only [Rsrc2]; ac_rfl)) (by
                      try c0_hsteps
                      refine wp_store_arr32_abs (base := s.pool.getD (1 - s.pc.toNat) 0#64)
                        (idx := k + BitVec.setWidth 64 j) (R := Rdst2)
                        (val := srcPool[mOff + j.toNat]'hm_j)
                        rfl (by
                          rw [show s.pool[(s.pc ^^^ 1).toNat]'(by rw [hl_s.pool]; exact hlt_xor) =
                            s.pool.getD (1 - s.pc.toNat) 0#64 from hpool_xor]; rfl)
                        (by rw [hkj_nat]; exact hd_kj)
                        (sep_cast hm'' (by dsimp only [Rdst2]; ac_rfl)) (fun m3 hm3 => ?_)
                      c0_hsteps
                      refine hrec2 (len.toNat + 1 - (j + 1#32).toNat)
                        (j + 1#32, ⟨⟩) m3 (by omega)
                        ⟨dstIn.set (k + BitVec.setWidth 64 j).toNat (srcPool[mOff + j.toNat]'hm_j),
                          by simp [hdstIn_len], by omega, rfl, fun q hq => ?_, fun t ht => ?_,
                          sep_cast hm3 (by dsimp only [Rdst2]; ac_rfl)⟩
                      · rw [getD_set_eq dstIn 0#32 _ (by rw [hkj_nat]; exact hd_kj)]
                        simp only [hkj_nat, show q ≠ k.toNat + j.toNat by omega, ↓reduceIte]
                        exact hOld q hq
                      · rw [getD_set_eq dstIn 0#32 _ (by rw [hkj_nat]; exact hd_kj), hkj_nat]
                        by_cases htj : t = j.toNat
                        · subst htj; simp only [↓reduceIte]
                          exact (getD_eq_getElem srcPool 0#32 hm_j).symm
                        · simp only [show k.toNat + t ≠ k.toNat + j.toNat by omega, ↓reduceIte]
                          exact hCopied t (by omega))
                · -- Inner loop done: `j = len + 1`
                  have hj_eq : j.toNat = len.toNat + 1 := by
                    have hlt : (srcPool.getD mOff 0#32).toNat < j.toNat := by
                      rw [getD_eq_getElem srcPool 0#32 hm0_lt]; dsimp only [mOff]; omega
                    omega
                  have hk32 : (k.setWidth 32).toNat = k.toNat := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hk_cap hpcap32)]
                  have hkn_add : (k + BitVec.setWidth 64 len + 1#64).toNat =
                      k.toNat + len.toNat + 1 := by
                    have hb : k.toNat + len.toNat + 1 ≤ s.pcap.toNat := by
                      have hkl := hk_len_cap; rw [← hlen_eq] at hkl; omega
                    have := len.isLt; have := s.pcap.isLt
                    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                      show (1#64 : BitVec 64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : len.toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : k.toNat + len.toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : k.toNat + len.toNat + 1 < 2 ^ 64)]
                  have hip1 : (i + 1#32).toNat = i.toNat + 1 := by
                    have := s.tn.isLt
                    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                  try c0_hsteps
                  refine wp_store_arr32_idx (base := s.tm.getD s.tc.toNat 0#64) (idx := i)
                    (R := Rtm2) (val := k.setWidth 32) rfl
                    (by rw [htm_tc]; simp) hi_tm
                    (sep_cast hm'' (by dsimp only [Rtm2]; ac_rfl)) (fun m3 hm3 => ?_)
                  c0_hsteps
                  refine hrec (s.tn.toNat - (i + 1#32).toNat)
                    (k + BitVec.setWidth 64 len + 1#64, i + 1#32, ⟨⟩) m3 (by omega)
                    ⟨tmCur.set i.toNat (k.setWidth 32), dstIn, by simp [htmL],
                      hdstIn_len.trans hdstL, by omega,
                      by rw [hip1, monoTotalWords_succ, hkn_add, hk_eq, ← hlen_eq, Nat.add_assoc],
                      by omega, rfl, fun p hp => ?_, fun p hp => ?_,
                      sep_cast hm3 (by dsimp only [Rtm2]; ac_rfl)⟩
                  · rw [getD_set_eq tmCur 0#32 (k.setWidth 32) hi_tm]
                    by_cases hpi : p = i.toNat
                    · subst hpi; simp only [↓reduceIte, hk32]
                      have hdst_k : dstIn.getD k.toNat 0#32 = len := by
                        have h0 := hCopied 0 (by omega)
                        simp only [Nat.add_zero] at h0
                        rw [h0, getD_eq_getElem srcPool 0#32 hm0_lt]
                        dsimp only [len]; simp only [hm0_nat]
                      refine ⟨?_, ⟨by omega, by rw [hdst_k, hkn_add]; omega⟩,
                        by rw [hdst_k, hlen_eq]⟩
                      simp only [symListAt, hdst_k, hlen_eq]
                      apply List.map_congr_left
                      intro t ht; rw [List.mem_range] at ht
                      rw [show k.toNat + 1 + t = k.toNat + (1 + t) by omega,
                        hCopied (1 + t) (by omega), show mOff + (1 + t) = mOff + 1 + t by omega]
                    · simp only [hpi, ↓reduceIte]
                      obtain ⟨hsym, ⟨hpm1, hpm2⟩, hlenp⟩ := hPref p (by omega)
                      have hkeep : ∀ t ≤ (dstCur.getD (tmCur.getD p 0#32).toNat 0#32).toNat,
                          dstIn.getD ((tmCur.getD p 0#32).toNat + t) 0#32 =
                            dstCur.getD ((tmCur.getD p 0#32).toNat + t) 0#32 :=
                        fun t ht => hOld _ (by omega)
                      have hkeep0 := hkeep 0 (Nat.zero_le _); rw [Nat.add_zero] at hkeep0
                      refine ⟨?_, ⟨by omega, by rw [hkeep0]; omega⟩, by rw [hkeep0]; exact hlenp⟩
                      rw [← hsym]; simp only [symListAt, hkeep0]
                      apply List.map_congr_left
                      intro t ht; rw [List.mem_range] at ht
                      rw [show (tmCur.getD p 0#32).toNat + 1 + t =
                        (tmCur.getD p 0#32).toNat + (1 + t) by omega, hkeep (1 + t) (by omega)]
                  · rw [getD_set_eq tmCur 0#32 (k.setWidth 32) hi_tm]
                    simp only [show p ≠ i.toNat by omega, ↓reduceIte]
                    exact hTail p (by omega)
              · intro J2 hJ2
                c0_hsteps
                exact hJ2 (len.toNat + 1 - 0) (0#32, ⟨⟩) m'
                  ⟨dstCur, rfl, Nat.zero_le _, by simp, fun q hq => rfl,
                    fun t ht => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at ht; omega,
                    hm'⟩))
    · -- Exit loop: `i == tn`
      have hi_eq : i.toNat = s.tn.toNat := by
        have := BitVec.not_lt.mp hc; omega
      c0_hsteps
      let s' : ArCtxState := { s with pc := s.pc ^^^ 1#32, ptop := k }
      have hfoc2 := hfoc_all s' rfl rfl rfl rfl rfl tmCur dstCur htmL hdstL
      let tm0' := if s.tc.toNat = 0 then tmCur else tm0
      let tm1' := if s.tc.toNat = 0 then tm1 else tmCur
      let pool0' := if s.pc.toNat = 0 then pool0 else dstCur
      let pool1' := if s.pc.toNat = 0 then dstCur else pool1
      have hdst_eq : (if s.pc.toNat = 0 then pool1' else pool0') = dstCur := by
        dsimp only [pool0', pool1']; by_cases h : s.pc.toNat = 0 <;> simp [h]
      have htm_eq : (if s.tc.toNat = 0 then tm0' else tm1') = tmCur := by
        dsimp only [tm0', tm1']; by_cases h : s.tc.toNat = 0 <;> simp [h]
      refine hQ s' tm0' tm1' pool0' pool1' _ hpc_xor rfl (by rw [hk_eq, hi_eq]) hk_cap
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp only [tm0', srcTm] at htmL ⊢; by_cases h : s.tc.toNat = 0 <;> simp [h, htmL]
      · dsimp only [tm1', srcTm] at htmL ⊢; by_cases h : s.tc.toNat = 0 <;> simp [h, htmL]
      · dsimp only [pool0', dstPool0] at hdstL ⊢; by_cases h : s.pc.toNat = 0 <;> simp [h, hdstL]
      · dsimp only [pool1', dstPool0] at hdstL ⊢; by_cases h : s.pc.toNat = 0 <;> simp [h, hdstL]
      · dsimp only [pool0', pool1']; by_cases h : s.pc.toNat = 0 <;> simp [h]
      · dsimp only [tm0', tm1']; by_cases h : s.tc.toNat = 0 <;> simp [h]
      · intro p hp
        rw [hdst_eq, htm_eq]
        obtain ⟨hsym, hok, _⟩ := hPref p (by omega)
        exact ⟨hsym, hok.1, by simpa [s'] using hok.2⟩
      · rw [hdst_eq, htm_eq,
          monoTotalWords_congr (pool1 := dstCur) (tm1 := tmCur) (pool2 := srcPool) (tm2 := srcTm)
            (n := s.tn.toNat) (fun p hp => (hPref p (by omega)).2.2),
          ← hi_eq, ← hk_eq]
      · rw [hdst_eq, htm_eq]
        exact polyEval_congr_symListAt s.n_out.toNat σ dstCur tmCur srcPool srcTm _ _ s.tn.toNat
          (fun p hp => (hPref p (by omega)).1)
      · dsimp only [tm0', tm1', pool0', pool1']
        rw [hfoc2]; exact sep_cast ‹_› (by ac_rfl)
  · intro J hJ
    c0_hsteps
    exact hJ s.tn.toNat (0#64, 0#32, ⟨⟩) m
      ⟨srcTm, dstPool0, rfl, rfl, Nat.zero_le _, rfl, Nat.zero_le _, by simp,
        fun p hp => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hp; omega,
        fun p _ => rfl, sep_cast hm_arr (by dsimp only [Rt0]; ac_rfl)⟩

end

end LeanQbe.T.Examples.Arisca.Proof
