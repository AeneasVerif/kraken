/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Examples.Kissat.Src.Internal
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat M6 `FullM6Hdr` Group-A Init Proofs (`Proof.Spec.Header1`)

Live `Func.wp` proofs for `Src.Tiers` / `Src.Internal`:
1. `m6_hdr_init_wp` (`Src.Tiers.m6_hdr_init_body`)
2. `m6_ext_ensure_init_wp` (`Src.Tiers.m6_ext_ensure_init_body`)
3. `full_m6_mem_init_wp` (`Src.Internal.full_m6_mem_init_body`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open scoped FullArenaTactics
open scoped M6HdrTactics
open Kraken.Bedrock2.Test

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

theorem m6_hdr_init_wp (Γ : Env) :
    ∀ a m Q X, m6HdrInitSpec a m Q X → Func.wp Γ Src.Tiers.m6_hdr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp Src.Tiers.m6_hdr_init_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (i, ()) m1 => i.toNat ≤ 288 ∧ ∃ ext1 : List (BitVec 64),
      ext1.length = 288 ∧ (FullMem c s ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m1)
    (fun (i, ()) _ => 288 - i.toNat)
    (fun L hL => by c0_hsteps; exact hL (0#64, ()) m ⟨by simp, ext, hext.len, hm⟩)
    (fun L (i, ()) m1 ⟨hi_le, ext1, hl1, hm1⟩ ih => ?_)
  c0_hsteps
  · have hi_lt : i.toNat < 288 := by c0_bound
    have hi_len : i.toNat < ext1.length := by rw [hl1]; exact hi_lt
    c0_hsteps
    exact ih _ _ (by c0_bound) ⟨by c0_bound, ext1.set i.toNat 0, by simp [hl1], by assumption⟩
  · have h288 : ext1.length = 288 := hl1
    c0_hsteps
    refine hQ _ _ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    refine ⟨by simp only [List.length_set, h288, fullM6ExtWords], ?_⟩
    rw [show (0 : BitVec 64).toNat = 0 from rfl,
      List.getElem?_set_self (by simp only [List.length_set, h288]; omega)]
    rfl


theorem m6_ext_ensure_init_wp (Γ : Env)
    (hInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Func.wp Γ Src.Tiers.m6_ext_ensure_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  have h0 : 0 < ext.length := by rw [hext.len]; omega
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp Src.Tiers.m6_ext_ensure_init_body
  c0_hsteps
  · have hne : ext[0]'h0 ≠ fullM6HdrMagic := by
      intro heq; apply hc; simpa [fullM6HdrMagic] using heq
    have hnot : ¬ M6HdrExtInitOk ext := fun hi => by
      have hm0 := hi.2; rw [List.getElem?_eq_getElem h0, Option.some.injEq] at hm0; exact hne hm0
    m6h_call hInit
    refine ⟨c, ext, s, R, rfl, hcfg, hext, hlen, (fullM6HdrMem_iff ..).mpr hm,
      fun ext' m1 hinit1 hm1 => ?_⟩
    c0_hsteps
    exact hQ ext' m1 hinit1 (fun hi => absurd hi hnot) hm1
  · have heq : ext[0]'h0 = fullM6HdrMagic := by simpa [fullM6HdrMagic] using hc
    have hinit : M6HdrExtInitOk ext := ⟨hext.len, by rw [List.getElem?_eq_getElem h0, heq]⟩
    exact hQ ext m hinit (fun _ => rfl) ((fullM6HdrMem_iff ..).mpr hm)


private theorem sep_swap_l {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ (Q ⋆ R)) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [← sep_assoc, sep_comm P Q, sep_assoc] at h; exact h

private theorem sep_init_split {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C) ⋆ R) m) : (A ⋆ C ⋆ (B ⋆ R)) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => by rwa [sep_assoc] at x) m h
  exact sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h1

private theorem sep_init_merge {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ C ⋆ (B ⋆ R)) m) : (A ⋆ (B ⋆ C) ⋆ R) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h
  rw [← sep_assoc B C R] at h1
  exact h1

private theorem sep_init_pull_ext {A F E R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ F ⋆ (E ⋆ R)) m) : (E ⋆ (A ⋆ F ⋆ R)) m := by
  rw [sep_assoc] at h
  have h1 : (A ⋆ (E ⋆ (F ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h
  have h2 := sep_swap_l h1
  rwa [← sep_assoc A F R] at h2

private theorem sep_init_pack {E A F R : Mem 64 → Prop} {m : Mem 64}
    (h : (E ⋆ (A ⋆ F ⋆ R)) m) : ((E ⋆ F) ⋆ (A ⋆ R)) m := by
  have h1 : (E ⋆ (A ⋆ (F ⋆ R))) m := by rwa [sep_assoc A F R] at h
  have h2 := sep_swap_l h1
  have h3 : (A ⋆ ((E ⋆ F) ⋆ R)) m :=
    sep_mono2 (fun _ x => x) (fun _ x => (congrFun (sep_assoc E F R) _).mpr x) m h2
  exact sep_swap_l h3

private theorem sep_init_unpack {H A R : Mem 64 → Prop} {m : Mem 64}
    (h : (H ⋆ (A ⋆ R)) m) : (A ⋆ H ⋆ R) m := by
  have h1 := sep_swap_l h
  rwa [← sep_assoc A H R] at h1

private theorem bv64_max_sub_ult_false {wb av : BitVec 64}
    (hfit : wb.toNat + av.toNat < 2 ^ 64) :
    (((18446744073709551615 : BitVec 64) - av).ult wb) = false := by
  have hav := av.isLt
  have hmax : (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : ((18446744073709551615 : BitVec 64) - av).toNat = 2 ^ 64 - 1 - av.toNat := by
    rw [BitVec.toNat_sub, hmax]
    have h1 : 2 ^ 64 - av.toNat + (2 ^ 64 - 1) = (2 ^ 64 - 1 - av.toNat) + 2 ^ 64 := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ult, hsub, decide_eq_false_iff_not]; omega

private theorem mem_init_sub_eq {av : BitVec 64} (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (av - 2304).toNat = av.toNat - fullM6ExtBytes := by
  rw [BitVec.toNat_sub, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *; omega

private theorem mem_init_hdr_toNat {wb av : BitVec 64} (hfit : wb.toNat + av.toNat < 2 ^ 64)
    (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (wb + 2304).toNat = wb.toNat + fullM6ExtBytes := by
  rw [BitVec.toNat_add, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem mem_init_ext_fit : 8 * fullM6ExtWords ≤ 2 ^ 64 := by
  unfold fullM6ExtWords; decide


theorem full_m6_mem_init_wp (Γ : Env)
    (hInitState : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hHdrInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, fullM6MemInitSpec a m Q X →
      Func.wp Γ Src.Internal.full_m6_mem_init_body a m Q X := by
  rintro ⟨cnf_ptr, cend, work_base, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, hcend, hfit, hwfit, hm, hFail, hOk⟩
  unfold Func.wp Src.Internal.full_m6_mem_init_body; wp_unfold
  have hult_av : avail.ult 3456 = decide (avail.toNat < fullM6HdrTotalBytes) := by
    rw [BitVec.ult, show (3456 : BitVec 64).toNat = fullM6HdrTotalBytes from rfl]
  rw [hult_av]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hlt => hFail m hm (Or.inl hlt), fun hnot_lt => ?_⟩
  have hge3456 : fullM6HdrTotalBytes ≤ avail.toNat := Nat.le_of_not_lt hnot_lt
  rw [bv64_max_sub_ult_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := Nat.le_of_lt avail.isLt
  have hsub_eq : (avail - 2304).toNat = avail.toNat - fullM6ExtBytes :=
    mem_init_sub_eq hge3456
  have hhdr_to : (work_base + 2304).toNat = work_base.toNat + fullM6ExtBytes :=
    mem_init_hdr_toNat hwfit hge3456
  have hhdr_bv : work_base + (2304 : BitVec 64) =
      work_base + BitVec.ofNat 64 fullM6ExtBytes := by
    unfold fullM6ExtBytes; rfl
  have hsum_av : fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) = avail.toNat :=
    Nat.add_sub_of_le (Nat.le_trans (by decide : fullM6ExtBytes ≤ fullM6HdrTotalBytes) hge3456)
  have hrem_fit :
      work_base.toNat + fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) < 2 ^ 64 := by
    rw [Nat.add_assoc, hsum_av]; exact hwfit
  have hrem_ge : 1152 ≤ avail.toNat - fullM6ExtBytes :=
    Nat.le_sub_of_add_le (by exact hge3456)
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region (work_base + 2304) (avail - 2304).toNat ⋆
      (region work_base fullM6ExtBytes ⋆ R)) m := by
    have hm1 : (bytes cnf_ptr cnfBytes ⋆
        (region work_base fullM6ExtBytes ⋆
          region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
            (avail.toNat - fullM6ExtBytes)) ⋆ R) m := by
      rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
        (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le]
      exact hm
    rw [hsub_eq, hhdr_bv]; exact sep_init_split hm1
  c0_call hInitState
  refine ⟨cnfBytes, region work_base fullM6ExtBytes ⋆ R, hcend, hfit,
    by rw [hhdr_to, hsub_eq]; exact hrem_fit,
    by rw [hsub_eq]; exact hrem_ge, hsplit, ?_, ?_⟩
  · intro m1 hm1 hfail1
    wp_unfold
    have hre : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m1 := by
      have hm2 : (bytes cnf_ptr cnfBytes ⋆
          (region work_base fullM6ExtBytes ⋆
            region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
              (avail.toNat - fullM6ExtBytes)) ⋆ R) m1 := by
        rw [hsub_eq, hhdr_bv] at hm1; exact sep_init_merge hm1
      rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
        (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le] at hm2
      exact hm2
    exact hFail m1 hre (Or.inr fun mv nc rest hp => by
      have := hfail1 mv nc rest hp; rwa [hsub_eq] at this)
  · intro c s j rest m1 hchdr hcavail hparse hj hdrop hsp hcv hdcur hal hwl hte hpr hcl
      hfu _ _ _ _ hoom hinc _ _ _ _ _ hm1
    have hcfg : FullM6HdrCfgOk c := by
      unfold FullM6HdrCfgOk; rw [hchdr, hhdr_to]; exact Nat.le_add_left ..
    have hwa : m6ExtAddr c.hdr = work_base := by
      rw [hchdr]; exact m6ExtAddr_of_add_imm work_base
    have hm1' : (region work_base (8 * fullM6ExtWords) ⋆
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R)) m1 := by
      have h0 := sep_init_pull_ext hm1
      simpa only [show fullM6ExtBytes = 8 * fullM6ExtWords from rfl] using h0
    have hm2 := sep_mono (fun _ (hr : region work_base (8 * fullM6ExtWords) _) =>
      region_to_array64 fullM6ExtWords mem_init_ext_fit hr) hm1'
    obtain ⟨ext0, hm3⟩ := sep_ex_l.mp hm2
    obtain ⟨hext0_len, hm4⟩ := sep_pure_l.mp hm3
    have hm_ext : (FullM6HdrMem c ext0 s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m1 := by
      have h1 : (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆
          (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R)) m1 := by
        rw [hwa]; exact hm4
      unfold FullM6HdrMem; exact sep_init_pack h1
    c0_hsteps_nogrp
    · c0_call hHdrInit
      refine ⟨c, ext0, s, bytes cnf_ptr cnfBytes ⋆ R, hchdr.symm, hcfg, hext0_len,
        hsp.lengths, hm_ext, fun ext1 m2 hinit1 hm2 => ?_⟩
      c0_hsteps
      rw [← hchdr]
      exact hOk c ext1 s j rest m2 (hchdr.trans hhdr_bv) (by rwa [hsub_eq] at hcavail) hcfg
        hinit1 hparse hj hdrop ⟨hcfg, hinit1.toOk, hsp⟩ hcv hdcur hal hwl hte hpr hcl hfu
        hoom hinc (sep_init_unpack hm2)
    · cases hc


end LeanQbe.T.Examples.Kissat.Proof.Spec
