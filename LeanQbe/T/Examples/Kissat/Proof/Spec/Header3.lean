/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat M6 `FullM6Hdr` Decision-Rate Helper Proofs (`Proof.Spec.Header3`)

Live `Func.wp` proofs for the `3` `Src.Tiers` decision-rate functions (`m6_hdr_dr_init`,
`m6_hdr_dr_update`, `m6_hdr_dr_allow`).
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
open LeanQbe.T.Examples.Kissat.Src
open FullArenaTactics
open scoped FullArenaTactics
open scoped M6HdrTactics
open Kraken.Bedrock2.Test

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv64_add_small2 {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

private theorem w2b_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6ExtW2aPres ext1 ext') :
    M6HdrExtInitOk ext → M6ExtW2aPres ext ext' :=
  fun hi => (h1 hi) ▸ h2


/-! ## 1. `FullM6Hdr` `decision_rate` Helpers (`3` Functions) -/

theorem m6_hdr_dr_init_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ Src.Tiers.m6_hdr_dr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_dr_init_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps
  · exact hQ ext1 m1 hinit1 (w2b_pres_of_init hpres1 (M6ExtW2aPres.refl ext1))
      ((fullM6HdrMem_iff ..).mpr hm1)
  · refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact ((((((hinit1.set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)
    · refine w2b_pres_of_init hpres1 ?_
      exact (((((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        ((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
          (M6ExtW2aPres.set_w2b _ (by decide) (by decide)))

theorem m6_hdr_dr_update_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ Src.Tiers.m6_hdr_dr_update_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_dr_update_body
  c0_hsteps_nogrp
  m6h_call hDrInit
  refine m6HdrDrMutSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hw1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  have hp_eq : ((2 : BitVec 64) + mode).toNat = 2 + mode.toNat :=
    bv64_add_small2 (n := 2) rfl (by omega)
  have hsb_eq : ((4 : BitVec 64) + mode).toNat = 4 + mode.toNat :=
    bv64_add_small2 (n := 4) rfl (by omega)
  have hse_eq : ((6 : BitVec 64) + mode).toNat = 6 + mode.toNat :=
    bv64_add_small2 (n := 6) rfl (by omega)
  have hp_lt : ((2 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hp_eq]; omega
  have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hsb_eq]; omega
  have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hse_eq]; omega
  c0_hsteps_nogrp
  · c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (((hinit1.set_pos _ (by decide)).set_pos _ (by rw [hp_eq]; omega)).set_pos _
        (by rw [hsb_eq]; omega)).set_pos _ (by rw [hse_eq]; omega)
    · intro hi
      exact (hw1 hi).trans (((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega))).trans
        ((M6ExtW2aPres.set_w2b _ (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b _ (by rw [hse_eq]; omega) (by rw [hse_eq]; omega))))
  · obtain ⟨ext2, hm2, hl2, hinit2, hw12⟩ :
        ∃ ext2 : List (BitVec 64), (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m ∧
          ext2.length = 288 ∧ M6HdrExtInitOk ext2 ∧ M6ExtW2aPres ext1 ext2 :=
      ⟨_, hm, by simp [hl1], hinit1.set_pos _ (by rw [hp_eq]; omega),
        M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega)⟩
    have hsb2_lt : ((4 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hsb_eq]; omega
    have hse2_lt : ((6 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hse_eq]; omega
    let m2 := m
    have hm2' : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm2
    clear hm hm2
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (_d, ()) m3 hm3 => ?_) (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (_dc, ()) m3 hm3 => ?_) (fun _ hJc => by c0_hsteps <;> exact hJc (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (sb, ()) m3 hm3 => ?_) (fun _ hJsb => by c0_hsteps <;> exact hJsb (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (se, ()) m3 hm3 => ?_)
      (fun _ hJse => by
        c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m2)
            (fun _ (se1, ()) m4 hm4 => by subst m4; exact hJse (se1, ()) m2 rfl)
            (fun _ hJse1 => by c0_hsteps <;> exact hJse1 (_, ()) m2 rfl)
        · exact hJse (_, ()) m2 rfl)
    subst m3
    c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos sb (by rw [hsb_eq]; omega)).set_pos se (by rw [hse_eq]; omega)
    · intro hi
      exact ((hw1 hi).trans hw12).trans
        ((M6ExtW2aPres.set_w2b sb (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b se (by rw [hse_eq]; omega) (by rw [hse_eq]; omega)))

theorem m6_hdr_dr_allow_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrAllowSpec a m Q X → Func.wp Γ Src.Tiers.m6_hdr_dr_allow_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrAllowSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_dr_allow_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
  · refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
      (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
      (fun _ hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
        · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
    subst m2
    have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
    have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small2 (n := 4) rfl (by omega)]; omega
    have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small2 (n := 6) rfl (by omega)]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
      (fun _ (_sd, ()) m2 hm2 => by
        subst m2; c0_hsteps
        · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
        · exact hQ _ ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1))
      (fun _ hJsd => by c0_hsteps <;> exact hJsd (_, ()) m1 rfl)


end LeanQbe.T.Examples.Kissat.Proof.Spec
