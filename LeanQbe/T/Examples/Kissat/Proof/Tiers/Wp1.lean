/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat/Src/Tiers.lean` Part 1 (`Wp1`)

Self-contained `CanonicalEnv` `Func.wp` proofs for the remaining `10` functions of `Src.Tiers.fns`:
`m6_hdr_get_tier1`, `m6_hdr_get_tier2`, `m6_hdr_delaying`, `m6_hdr_bump_delay`,
`m6_hdr_reduce_delay`, `m6_hdr_get_watermark`, `m6_hdr_set_watermark`,
`m6_hdr_dr_init`, `m6_hdr_dr_update`, `m6_hdr_dr_allow` (`0` legacy `Full*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Tiers

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Tiers
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

/-! ## 1. Tier Getters (`2` Functions) -/

theorem m6_hdr_get_tier1_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ m6_hdr_get_tier1_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_get_tier1_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
    (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_)
    (fun _ hJs => by
      c0_hsteps
      · exact hJs (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJs (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJs (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hst_le : st.toNat ≤ 1 := by rcases hst with rfl | rfl <;> decide
  have hidx : ((8 : BitVec 64) + st).toNat < ext1.length := by
    rw [hl1, bv64_add_small (n := 8) rfl (by omega)]; omega
  c0_hsteps
  exact hQ (_, ()) ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) hinit1.toOk
    (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1)) ((fullM6HdrMem_iff ..).mpr hm1)

theorem m6_hdr_get_tier2_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ m6_hdr_get_tier2_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_get_tier2_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
    (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_)
    (fun _ hJs => by
      c0_hsteps
      · exact hJs (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJs (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hst_le : st.toNat ≤ 1 := by rcases hst with rfl | rfl <;> decide
  have hidx : ((10 : BitVec 64) + st).toNat < ext1.length := by
    rw [hl1, bv64_add_small (n := 10) rfl (by omega)]; omega
  c0_hsteps
  all_goals
    exact hQ (_, ()) ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) hinit1.toOk
      (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1)) ((fullM6HdrMem_iff ..).mpr hm1)

/-! ## 2. `delay[4]` Backoff (`3` Functions) -/

theorem m6_hdr_delaying_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Func.wp Γ m6_hdr_delaying_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_delaying_body
  c0_hsteps_nogrp
  · exact hQ (false, ()) ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid4 : id.toNat < 4 := by
      have h4 : (4 : BitVec 64).toNat = 4 := rfl; omega
    m6h_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    have hidx_eq : ((16 : BitVec 64) + id).toNat = 16 + id.toNat :=
      bv64_add_small (n := 16) rfl (by omega)
    have hidx : ((16 : BitVec 64) + id).toNat < ext1.length := by rw [hl1, hidx_eq]; omega
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps
    · refine hQ (true, ()) _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
        ((fullM6HdrMem_iff ..).mpr (by assumption))
      · exact (hinit1.set_pos _ (by rw [hidx_eq]; omega)).toOk
      · exact w2a_pres_of_init hpres1 (hinit1.set_pos _ (by rw [hidx_eq]; omega))
          (M6ExtW2bPres.set_ge8 _ (by rw [hidx_eq]; omega))
    · exact hQ (false, ()) ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) hinit1.toOk
        (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1))
        ((fullM6HdrMem_iff ..).mpr hm1)

theorem m6_hdr_bump_delay_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_bump_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_bump_delay_body
  c0_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid4 : id.toNat < 4 := by
      have h4 : (4 : BitVec 64).toNat = 4 := rfl; omega
    m6h_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    have hicur_eq : ((20 : BitVec 64) + id).toNat = 20 + id.toNat :=
      bv64_add_small (n := 20) rfl (by omega)
    have hicnt_eq : ((16 : BitVec 64) + id).toNat = 16 + id.toNat :=
      bv64_add_small (n := 16) rfl (by omega)
    have hicur : ((20 : BitVec 64) + id).toNat < ext1.length := by rw [hl1, hicur_eq]; omega
    have hicnt : ((16 : BitVec 64) + id).toNat < ext1.length := by rw [hl1, hicnt_eq]; omega
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
      (fun _ (cur, ()) m2 hm2 => ?_)
      (fun _ hJc => by c0_hsteps <;> exact hJc (_, ()) m1 rfl)
    subst m2
    have hicnt2 : ((16 : BitVec 64) + id).toNat <
        (ext1.set ((20 : BitVec 64) + id).toNat cur).length := by
      rw [List.length_set]; exact hicnt
    c0_hsteps
    let ext2 :=
      (ext1.set ((20 : BitVec 64) + id).toNat cur).set ((16 : BitVec 64) + id).toNat cur
    have hinit2 : M6HdrExtInitOk ext2 :=
      (hinit1.set_pos cur (by rw [hicur_eq]; omega)).set_pos cur (by rw [hicnt_eq]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 :=
      (M6ExtW2bPres.set_ge8 cur (by rw [hicur_eq]; omega)).trans
        (M6ExtW2bPres.set_ge8 cur (by rw [hicnt_eq]; omega))
    exact hQ () ext2 s _ rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
      (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr (by assumption))

theorem m6_hdr_reduce_delay_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_reduce_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_reduce_delay_body
  c0_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid4 : id.toNat < 4 := by
      have h4 : (4 : BitVec 64).toNat = 4 := rfl; omega
    m6h_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    have hicur_eq : ((20 : BitVec 64) + id).toNat = 20 + id.toNat :=
      bv64_add_small (n := 20) rfl (by omega)
    have hicnt_eq : ((16 : BitVec 64) + id).toNat = 16 + id.toNat :=
      bv64_add_small (n := 16) rfl (by omega)
    have hicur : ((20 : BitVec 64) + id).toNat < ext1.length := by rw [hl1, hicur_eq]; omega
    have hicnt : ((16 : BitVec 64) + id).toNat < ext1.length := by rw [hl1, hicnt_eq]; omega
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps
    refine hQ () _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
      ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact ((hinit1.set_pos _ (by rw [hicur_eq]; omega)).set_pos _
        (by rw [hicnt_eq]; omega)).toOk
    · exact w2a_pres_of_init hpres1
        ((hinit1.set_pos _ (by rw [hicur_eq]; omega)).set_pos _ (by rw [hicnt_eq]; omega))
        ((M6ExtW2bPres.set_ge8 _ (by rw [hicur_eq]; omega)).trans
          (M6ExtW2bPres.set_ge8 _ (by rw [hicnt_eq]; omega)))

/-! ## 3. Watermarks (`2` Functions) -/

theorem m6_hdr_get_watermark_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrGetWatermarkSpec a m Q X →
      Func.wp Γ m6_hdr_get_watermark_body a m Q X := by
  rintro ⟨h, kind, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  unfold Func.wp m6_hdr_get_watermark_body
  c0_hsteps_nogrp
  · exact hQ 0#64 ext s m rfl hlen (M6HdrScratchPres.refl s) rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hk8 : kind.toNat < 8 := by
      have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
    m6h_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    have hidx : ((24 : BitVec 64) + kind).toNat < ext1.length := by
      rw [hl1, bv64_add_small (n := 24) rfl (by omega)]; omega
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps
    exact hQ _ ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) rfl hinit1.toOk
      (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1))
      ((fullM6HdrMem_iff ..).mpr hm1)

theorem m6_hdr_set_watermark_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Func.wp Γ m6_hdr_set_watermark_body a m Q X := by
  rintro ⟨h, kind, val, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_set_watermark_body
  c0_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hk8 : kind.toNat < 8 := by
      have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
    m6h_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    have hidx_eq : ((24 : BitVec 64) + kind).toNat = 24 + kind.toNat :=
      bv64_add_small (n := 24) rfl (by omega)
    have hidx : ((24 : BitVec 64) + kind).toNat < ext1.length := by rw [hl1, hidx_eq]; omega
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps
    let ext2 := ext1.set ((24 : BitVec 64) + kind).toNat val
    have hinit2 : M6HdrExtInitOk ext2 := hinit1.set_pos val (by rw [hidx_eq]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 := M6ExtW2bPres.set_ge8 val (by rw [hidx_eq]; omega)
    exact hQ () ext2 s _ rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
      (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr (by assumption))

/-! ## 4. Decision-Rate Helpers (`3` Functions) -/

theorem m6_hdr_dr_init_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp m6_hdr_dr_init_body
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
    (hDrInit : Γ.Has "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_update_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp m6_hdr_dr_update_body
  c0_hsteps_nogrp
  m6h_call hDrInit
  refine m6HdrDrMutSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hw1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (mode, ()) m2 => m1 = m2 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  rcases hm2 with rfl
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  have hp_eq : ((2 : BitVec 64) + mode).toNat = 2 + mode.toNat :=
    bv64_add_small (n := 2) rfl (by omega)
  have hsb_eq : ((4 : BitVec 64) + mode).toNat = 4 + mode.toNat :=
    bv64_add_small (n := 4) rfl (by omega)
  have hse_eq : ((6 : BitVec 64) + mode).toNat = 6 + mode.toNat :=
    bv64_add_small (n := 6) rfl (by omega)
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
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (_d, ()) m3 hm3 => ?_) (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hFrom _ _ _ _ fun _ => ?_)
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (sb, ()) m3 hm3 => ?_)
      (fun _ hJsb => by
        c0_hsplit
        · c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hMul _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun _ => ?_)
          c0_hsteps; exact hJsb (_, ()) m2 rfl
        · c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hMul _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_)
          c0_hsteps; exact hJsb (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (se, ()) m3 hm3 => ?_)
      (fun _ hJse => by
        c0_hsplit
        · c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hMul _ _ _ _ fun _ => ?_)
          refine wp_join_group (ts := [i64]) (fun _ m4 => m2 = m4)
            (fun _ (se1, ()) m4 hm4 => by rcases hm4 with rfl; exact hJse (se1, ()) m2 rfl)
            (fun _ hJse1 => by c0_hsteps <;> exact hJse1 (_, ()) m2 rfl)
        · c0_hsteps; exact hJse (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos sb (by rw [hsb_eq]; omega)).set_pos se (by rw [hse_eq]; omega)
    · intro hi
      exact ((hw1 hi).trans hw12).trans
        ((M6ExtW2aPres.set_w2b sb (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b se (by rw [hse_eq]; omega) (by rw [hse_eq]; omega)))

theorem m6_hdr_dr_allow_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hDiv : Γ.Has "f64u_div" f64uPure2Spec) :
    ∀ a m Q X, m6HdrDrAllowSpec a m Q X → Func.wp Γ m6_hdr_dr_allow_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrAllowSpec_elim hs
  unfold Func.wp m6_hdr_dr_allow_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
  · refine wp_join_group (ts := [i64])
      (fun (mode, ()) m2 => m1 = m2 ∧ (mode = 0#64 ∨ mode = 1#64))
      (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
      (fun _ hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
        · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
    rcases hm2 with rfl
    have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
    have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small (n := 4) rfl (by omega)]; omega
    have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small (n := 6) rfl (by omega)]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m1 = m2)
      (fun _ _ m2 hm2 => by
        rcases hm2 with rfl; c0_hsteps
        exact hQ _ ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1))
      (fun _ hJval => by
        c0_hsplit
        · c0_hsteps_nogrp; refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp
          · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
          · refine wp_call_of_spec _ _ (hDiv _ _ _ _ fun _ => ?_)
            c0_hsteps; exact hJval (_, ()) m1 rfl
        · c0_hsteps; exact hJval (_, ()) m1 rfl)

end LeanQbe.T.Examples.Kissat.Proof.Tiers
