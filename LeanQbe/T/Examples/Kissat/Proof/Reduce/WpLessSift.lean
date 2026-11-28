/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `full_red_less` and `full_red_sift` (`Proof.Reduce.WpLessSift`)

Canonical `Func.wp` proofs for `full_red_less` (`fullRedLessSpec`) and `full_red_sift`
(`fullRedSiftSpec`) over raw `array (t := i32)` separation predicates.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open Std
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Src.Reduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

section LocalArrayTactics

private theorem arr32_bytes_le : (i32 : Ty).bytes ≤ 2 ^ 64 := by decide

private theorem arr32_elem_addr (p : BitVec 64) (i : BitVec 64) :
    p + i * 4#64 = p + BitVec.ofNat 64 ((i32 : Ty).bytes * i.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [Ty.bytes, Ty.size, BitVec.toNat_mul, Nat.mul_comm]

private theorem arr32_zext_addr (p : BitVec 64) (i : BitVec 32) :
    p + i.setWidth 64 * 4#64 = p + BitVec.ofNat 64 ((i32 : Ty).bytes * i.toNat) := by
  rw [arr32_elem_addr, zext_toNat i (by decide)]

private theorem arr32_zext_add_addr (p : BitVec 64) (i : BitVec 32) (k : Nat)
    (hk : i.toNat + k < 2 ^ 64) :
    p + (i.setWidth 64 + BitVec.ofNat 64 k) * 4#64 =
      p + BitVec.ofNat 64 ((i32 : Ty).bytes * (i.toNat + k)) := by
  rw [arr32_elem_addr, BitVec.toNat_add, zext_toNat i (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]

@[scoped c0_load] private theorem load_arr32_bv {p : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < xs.length) (hm : (array (t := i32) p xs ⋆ R) m) :
    loadVal m i32 (p + i * 4#64) = some xs[i.toNat] := by
  rw [arr32_elem_addr]; exact loadVal_array arr32_bytes_le hi hm

@[scoped c0_load] private theorem load_arr32_zext {p : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 32}
    (hi : i.toNat < xs.length) (hm : (array (t := i32) p xs ⋆ R) m) :
    loadVal m i32 (p + i.setWidth 64 * 4#64) = some xs[i.toNat] := by
  rw [arr32_zext_addr]; exact loadVal_array arr32_bytes_le hi hm

@[scoped c0_load] private theorem load_arr32_zext_add {p : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 32} {k : Nat}
    (hk : i.toNat + k < 2 ^ 64) (hi : i.toNat + k < xs.length)
    (hm : (array (t := i32) p xs ⋆ R) m) :
    loadVal m i32 (p + (i.setWidth 64 + BitVec.ofNat 64 k) * 4#64) = some xs[i.toNat + k] := by
  rw [arr32_zext_add_addr p i k hk]; exact loadVal_array arr32_bytes_le hi hm

@[scoped c0_store] private theorem store_arr32_bv {p : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < xs.length) (hm : (array (t := i32) p xs ⋆ R) m) :
    storeOk m i32 (p + i * 4#64) ∧
      (array (t := i32) p (xs.set i.toNat v) ⋆ R) (storeMem m i32 (p + i * 4#64) v) := by
  rw [arr32_elem_addr]; exact store_array v arr32_bytes_le hi hm

end LocalArrayTactics

private theorem bv64_shl1_plus_eq (x : BitVec 64) (k : Nat) (hx : 2 * x.toNat + k < 2 ^ 64) :
    ((x <<< (1 : Nat)) + BitVec.ofNat 64 k).toNat = 2 * x.toNat + k := by
  rw [BitVec.toNat_add, FullArenaTactics.bv64_shl1_nat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hx]

private theorem list_swap_mem {α : Type} {xs : List α} {n a b : Nat}
    (hlen : a < xs.length) (hlenb : b < xs.length) (ha : a < n) (hb : b < n)
    (hmem : ∀ k < n, ∃ j < n, xs[k]? = xs[j]?) :
    let xs' := (xs.set a (xs[b]'hlenb)).set b (xs[a]'hlen)
    (∀ k, n ≤ k → xs'[k]? = xs[k]?) ∧
    (∀ k < n, ∃ j < n, xs'[k]? = xs[j]?) := by
  intro xs'
  constructor
  · intro k hk
    dsimp only [xs']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · intro k hk
    by_cases hkb : k = b
    · subst hkb; refine ⟨a, ha, ?_⟩
      dsimp only [xs']
      rw [List.getElem?_set_self (by simp; omega), List.getElem?_eq_getElem hlen]
    · by_cases hka : k = a
      · subst hka; refine ⟨b, hb, ?_⟩
        dsimp only [xs']
        rw [List.getElem?_set_ne (Ne.symm hkb), List.getElem?_set_self hlen,
          List.getElem?_eq_getElem hlenb]
      · dsimp only [xs']
        rw [List.getElem?_set_ne (Ne.symm hkb), List.getElem?_set_ne (Ne.symm hka)]
        exact hmem k hk

theorem full_red_less_wp (Γ : Env) :
    ∀ a m Q X, fullRedLessSpec a m Q X → Func.wp Γ full_red_less_body a m Q X := by
  rintro ⟨ar_ptr, a, b, ⟨⟩⟩ m Q X ⟨ar, R, ha, hb, hm, hQ⟩
  unfold Func.wp full_red_less_body
  have ha0 : a.toNat < ar.length := by omega
  have hb0 : b.toNat < ar.length := by omega
  have ha1 : a.toNat + 1 < ar.length := by omega
  have hb1 : b.toNat + 1 < ar.length := by omega
  have ha2 : a.toNat + 2 < ar.length := ha
  have hb2 : b.toNat + 2 < ar.length := hb
  have ha1_64 : a.toNat + 1 < 2 ^ 64 := by have := a.isLt; omega
  have hb1_64 : b.toNat + 1 < 2 ^ 64 := by have := b.isLt; omega
  have ha2_64 : a.toNat + 2 < 2 ^ 64 := by have := a.isLt; omega
  have hb2_64 : b.toNat + 2 < 2 ^ 64 := by have := b.isLt; omega
  c0_hsteps <;> exact hQ _

theorem full_red_sift_wp (Γ : Env)
    (hLess : Γ.Has "full_red_less" fullRedLessSpec) :
    ∀ a m Q X, fullRedSiftSpec a m Q X → Func.wp Γ full_red_sift_body a m Q X := by
  rintro ⟨ar_ptr, rr_ptr, start, n, ⟨⟩⟩ m Q X ⟨ar, rr, R, hst, hn_rr, hn62, hrefs, hm, hQ⟩
  unfold Func.wp full_red_sift_body
  c0_hsteps_nogrp
  let Inv : BitVec 64 → Mem 64 → Prop := fun idx m1 =>
    idx.toNat ≤ n.toNat ∧ ∃ rr1 : List (BitVec 32),
      rr1.length = rr.length ∧
      (∀ k, n.toNat ≤ k → rr1[k]? = rr[k]?) ∧
      (∀ k < n.toNat, ∃ j < n.toNat, rr1[k]? = rr[j]?) ∧
      (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr1 ⋆ R) m1
  refine wp_while_break_state (fun idx : BitVec 64 => (idx, ())) Inv
    (fun idx : BitVec 64 => (idx, ())) (fun idx => n.toNat - idx.toNat) Inv
    (fun _ idx m' ⟨_, rr1, hlen1, hout1, hmem1, hm1⟩ => by
      c0_hsteps
      exact hQ rr1 m' hlen1 hout1 hmem1 hm1)
    (fun B L idx m1 hB hL ⟨hidx_le, rr1, hlen1, hout1, hmem1, hm1⟩ => by
      c0_hsplit
      · clear hc
        have hidx64 : 2 * idx.toNat + 2 < 2 ^ 64 := by omega
        have hch1_eq : ((idx <<< (1 : Nat)) + 1#64).toNat = 2 * idx.toNat + 1 :=
          bv64_shl1_plus_eq idx 1 (by omega)
        c0_hstraight; rw [wp_jnz]; constructor <;> intro hge
        · c0_hsteps
          exact hB idx m1 ⟨hidx_le, rr1, hlen1, hout1, hmem1, hm1⟩
        · have hch1_lt : 2 * idx.toNat + 1 < n.toNat := by
            simp only [BitVec.ule] at hge
            have h1 : ¬ n.toNat ≤ ((idx <<< (1 : Nat)) + 1#64).toNat := by
              intro hle; apply Bool.false_ne_true; rw [← hge]; exact decide_eq_true hle
            omega
          let ch1 : BitVec 64 := (idx <<< (1 : Nat)) + 1#64
          have hch1_toNat : ch1.toNat = 2 * idx.toNat + 1 := hch1_eq
          refine wp_join_group (ts := [i64])
            (fun (best, ()) mb => mb = m1 ∧ idx.toNat < best.toNat ∧ best.toNat < n.toNat)
            (fun _ (best, ()) mb ⟨hmb, hbi, hbn⟩ => by
              rcases hmb with rfl
              have hbest_rr : best.toNat < rr1.length := by omega
              have hidx_rr : idx.toNat < rr1.length := by omega
              have href_best : (rr1[best.toNat]'hbest_rr).toNat + 2 < ar.length := by
                obtain ⟨j, hj, heq⟩ := hmem1 best.toNat hbn
                rw [List.getElem?_eq_getElem hbest_rr] at heq
                have := hrefs j hj; rw [← heq, Option.getD_some] at this; exact this
              have href_idx : (rr1[idx.toNat]'hidx_rr).toNat + 2 < ar.length := by
                obtain ⟨j, hj, heq⟩ := hmem1 idx.toNat (by omega)
                rw [List.getElem?_eq_getElem hidx_rr] at heq
                have := hrefs j hj; rw [← heq, Option.getD_some] at this; exact this
              c0_hstraight
              refine wp_call_of_spec _ _ (hLess _ _ _ _
                ⟨ar, array (t := i32) rr_ptr rr1 ⋆ R,
                  by dsimp only [Arg.val]; exact href_idx,
                  by dsimp only [Arg.val]; exact href_best,
                  by dsimp only [Arg.val]; exact sep_ac hm1,
                  fun res => ?_⟩)
              c0_hstraight; rw [wp_jnz]; constructor <;> intro hres
              · have hrr_idx : idx.toNat < rr1.length := hidx_rr
                have hrr_best : best.toNat < rr1.length := hbest_rr
                have hrr_best2 :
                    best.toNat < (rr1.set idx.toNat (rr1[best.toNat]'hrr_best)).length := by
                  simp [hrr_best]
                c0_hsteps
                have hsw := list_swap_mem (n := n.toNat) hrr_idx hrr_best (by omega) hbn
                  (fun k hk => ⟨k, hk, rfl⟩)
                refine hL best _ (by omega)
                  ⟨Nat.le_of_lt hbn,
                   (rr1.set idx.toNat (rr1[best.toNat]'hrr_best)).set best.toNat
                     (rr1[idx.toNat]'hrr_idx),
                   by simp [hlen1], fun k hk => (hsw.1 k hk).trans (hout1 k hk),
                   fun k hk => by
                     obtain ⟨j, hj, heq⟩ := hsw.2 k hk
                     obtain ⟨j0, hj0, heq0⟩ := hmem1 j hj
                     exact ⟨j0, hj0, heq.trans heq0⟩,
                   sep_ac (by assumption)⟩
              · c0_hsteps
                exact hB idx mb ⟨hidx_le, rr1, hlen1, hout1, hmem1, hm1⟩)
            (fun _ hJ => by
              have hch2_eq : (ch1 + 1#64).toNat = 2 * idx.toNat + 2 := by
                rw [BitVec.toNat_add, hch1_toNat, show (1#64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hstraight; rw [wp_jnz]; constructor <;> intro hch2
              · have hch2_lt : 2 * idx.toNat + 2 < n.toNat := by
                  rw [show (Arg.var _).val = (ch1 + 1#64).ult n from rfl,
                    BitVec.ult, hch2_eq] at hch2
                  exact decide_eq_true_eq.mp hch2
                have hch2_rr : (ch1 + 1#64).toNat < rr1.length := by omega
                have hch1_rr : ch1.toNat < rr1.length := by omega
                have href_ch2 : (rr1[(ch1 + 1#64).toNat]'hch2_rr).toNat + 2 < ar.length := by
                  obtain ⟨j, hj, heq⟩ := hmem1 (ch1 + 1#64).toNat (by omega)
                  rw [List.getElem?_eq_getElem hch2_rr] at heq
                  have := hrefs j hj; rw [← heq, Option.getD_some] at this; exact this
                have href_ch1 : (rr1[ch1.toNat]'hch1_rr).toNat + 2 < ar.length := by
                  obtain ⟨j, hj, heq⟩ := hmem1 ch1.toNat (by omega)
                  rw [List.getElem?_eq_getElem hch1_rr] at heq
                  have := hrefs j hj; rw [← heq, Option.getD_some] at this; exact this
                c0_hstraight
                refine wp_call_of_spec _ _ (hLess _ _ _ _
                  ⟨ar, array (t := i32) rr_ptr rr1 ⋆ R,
                    by dsimp only [Arg.val]; exact href_ch2,
                    by dsimp only [Arg.val]; exact href_ch1,
                    by dsimp only [Arg.val]; exact sep_ac hm1,
                    fun res => ?_⟩)
                c0_hsteps
                · exact hJ (ch1, ()) m1 ⟨rfl, by omega, by omega⟩
                · exact hJ (ch1 + 1#64, ()) m1 ⟨rfl, by omega, by omega⟩
              · c0_hsteps
                exact hJ (ch1, ()) m1 ⟨rfl, by omega, by omega⟩)
      · exact hB idx m1 ⟨hidx_le, rr1, hlen1, hout1, hmem1, hm1⟩)
    (fun _ L _ hL => by
      c0_hsteps
      exact hL start m ⟨hst, rr, rfl, fun _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩, hm⟩)
