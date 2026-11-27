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
# Kissat M6 `FullM6Hdr` Tier, Glue-Histogram, Delay & Watermark Proofs (`Proof.Tiers.Header2`)

Live `Func.wp` proofs for all `12` non-DR `Src.Tiers` functions (`m6_hdr_sync_legacy_tiers` ..
`m6_hdr_set_watermark`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Tiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Spec
open FullArenaTactics
open scoped FullArenaTactics
open scoped M6HdrTactics
open Kraken.Bedrock2.Test

private theorem w2a_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6HdrExtInitOk ext')
    (h3 : M6ExtW2bPres ext1 ext') :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext' :=
  fun hi => ⟨h2, (h1 hi) ▸ h3⟩

/-! ## 1. Tier Sync & Mode-Split Tier Recomputation (`4` Functions) -/

theorem m6_hdr_sync_legacy_tiers_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_sync_legacy_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_sync_legacy_tiers_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps
  all_goals
    refine hQ () ext1 _ _ ?_ ?_ ?_ hinit1.toOk
      (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1))
      ((fullM6HdrMem_iff ..).mpr (by assumption))
    · rfl
    · exact hlen.with_scratch
        { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
    · exact M6HdrScratchPres.of_tier _ _

theorem m6_hdr_recompute_tiers_mode_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_recompute_tiers_mode_body a m Q X := by
  rintro ⟨h, st, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_recompute_tiers_mode_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (base, ()) m2 => m2 = m1 ∧ (base = 32#64 ∨ base = 160#64))
    (fun _ (base, ()) m2 ⟨hm2, hbase⟩ => ?_)
    (fun _ hJb => by
      c0_hsteps
      · exact hJb (32#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJb (160#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hbase_le : base.toNat ≤ 160 := by rcases hbase with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (_tot, g, ()) mL => g.toNat ≤ 128 ∧ mL = m1)
    (fun (_, g, ()) _ => 128 - g.toNat)
    (fun Jl hJl => by c0_hsteps; exact hJl (0#64, 0#64, ()) m1 ⟨by decide, rfl⟩)
    (fun Jl (tot, g, ()) mL ⟨hg128, hmL⟩ ih => ?_)
  subst mL
  c0_hsteps_nogrp
  · have hg_lt : g.toNat < 128 := by
      have h128 : (128 : BitVec 64).toNat = 128 := rfl; omega
    have hidx : (base + g).toNat < ext1.length := by
      rw [hl1, bv64_add_small_eq (by omega)]; omega
    have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat_lt (by omega)
    c0_hsteps
    all_goals exact ih (_, g + 1, ()) m1 (by dsimp only; omega) ⟨by omega, rfl⟩
  · have htu_idx : ((14 : BitVec 64) + mode).toNat = 14 + mode.toNat :=
      bv64_add_small (n := 14) rfl (by omega)
    have htu_lt : ((14 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, htu_idx]; omega
    c0_hsteps_nogrp
    let ext2 := ext1.set ((14 : BitVec 64) + mode).toNat tot
    have hl2 : ext2.length = 288 := by simp [ext2, hl1]
    have hinit2 : M6HdrExtInitOk ext2 := hinit1.set_pos tot (by rw [htu_idx]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 := M6ExtW2bPres.set_ge8 tot (by rw [htu_idx]; omega)
    let m2 := m
    have hm2 : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm
    refine wp_join_group (ts := [i64, i64, i64]) (fun _ m3 => m3 = m2)
      (fun _ (_g', t1, t2, ()) m3 hm3 => ?_) ?_
    · subst m3
      refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
        (fun _ (t2c, ()) m3 hm3 => ?_) ?_
      · subst m3
        have ht1_idx : ((8 : BitVec 64) + mode).toNat = 8 + mode.toNat :=
          bv64_add_small (n := 8) rfl (by omega)
        have ht2_idx : ((10 : BitVec 64) + mode).toNat = 10 + mode.toNat :=
          bv64_add_small (n := 10) rfl (by omega)
        have ht1_lt : ((8 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, ht1_idx]; omega
        have ht2_lt : ((10 : BitVec 64) + mode).toNat <
            (ext2.set ((8 : BitVec 64) + mode).toNat t1).length := by
          rw [List.length_set, hl2, ht2_idx]; omega
        c0_hsteps_nogrp
        let ext3 := (ext2.set ((8 : BitVec 64) + mode).toNat t1).set
          ((10 : BitVec 64) + mode).toNat t2c
        have hinit3 : M6HdrExtInitOk ext3 :=
          (hinit2.set_pos t1 (by rw [ht1_idx]; omega)).set_pos t2c (by rw [ht2_idx]; omega)
        have hw3 : M6ExtW2bPres ext1 ext3 :=
          hw2.trans ((M6ExtW2bPres.set_ge8 t1 (by rw [ht1_idx]; omega)).trans
            (M6ExtW2bPres.set_ge8 t2c (by rw [ht2_idx]; omega)))
        m6h_call hSync
        refine m6HdrW2aSpec_of rfl hcfg hinit3.toOk hlen
          ((fullM6HdrMem_iff ..).mpr (by assumption))
          fun () ext4 s4 m4 hcore4 hlen4 hpres4 hok4 hw4 hm4 => ?_
        have ⟨hinit4, hw34⟩ := hw4 hinit3
        exact hQ () ext4 s4 m4 hcore4 hlen4 hpres4 hok4
          (w2a_pres_of_init hpres1 hinit4 (hw3.trans hw34)) hm4
      · intro _ hJt2c; c0_hsteps <;> exact hJt2c (_, ()) m2 rfl
    · intro _ hJt; c0_hsteps_nogrp
      · refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
          (fun _ (_lim1, ()) m3 hm3 => ?_) ?_
        · subst m3
          refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m2)
            (fun _ (_lim2, ()) m4 hm4 => ?_) ?_
          · subst m4
            refine wp_join_group (ts := [i64, i64, i64, i64, .bool, .bool])
              (fun _ m5 => m5 = m2)
              (fun _ (_g', _t1, _t2, _acc, _g1, _g2, ()) m5 hm5 => by
                subst m5; c0_hsteps <;> exact hJt (_, _, _, ()) m2 rfl)
              ?_
            · intro _ hJb
              c0_hsteps_nogrp
              refine wp_loop_inv (ts := [i64, i64, i64, .bool])
                (fun (g, _t1, _acc, _g1, ()) mL => g.toNat ≤ 128 ∧ mL = m2)
                (fun (g, _, _, _, ()) _ => 128 - g.toNat)
                (fun Ja hJa => by c0_hsteps; exact hJa (0#64, _, _, _, ()) m2 ⟨by decide, rfl⟩)
                (fun Ja (g, t1, acc, g1, ()) mL ⟨hg128', hmL⟩ ih2 => ?_)
              subst mL
              c0_hsteps_nogrp
              · have hg_lt : g.toNat < 128 := by
                  have h128 : (128 : BitVec 64).toNat = 128 := rfl; omega
                have hidx2 : (base + g).toNat < ext2.length := by
                  rw [hl2, bv64_add_small_eq (by omega)]; omega
                have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat_lt (by omega)
                c0_hsteps
                all_goals
                  try exact ih2 (g + 1, _, _, _, ()) m2 (by dsimp only; omega) ⟨by omega, rfl⟩
                all_goals (c0_hsteps; exact hJb (_, _, _, _, _, _, ()) m2 rfl)
              · c0_hsteps <;> exact hJb (_, _, _, _, _, _, ()) m2 rfl
          · intro _ hJ2; c0_hsteps <;> exact hJ2 (_, ()) m2 rfl
        · intro _ hJ1; c0_hsteps <;> exact hJ1 (_, ()) m2 rfl
      · exact hJt (_, _, _, ()) m2 rfl

theorem m6_hdr_recompute_tiers_wp (Γ : Env)
    (hMode : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_recompute_tiers_mode" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_recompute_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp Src.Tiers.m6_hdr_recompute_tiers_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = m)
    (fun _ (st, ()) m1 hm1 => by
      subst m1; m6h_call hMode
      exact m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm) hQ)
    (fun _ hJs => by c0_hsteps <;> exact hJs (_, ()) m rfl)

theorem m6_hdr_update_tier_limits_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_update_tier_limits_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_update_tier_limits_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () mJ => ∃ extJ sJ, sJ.core = s.core ∧ sJ.LengthsOk c ∧ M6HdrScratchPres s sJ ∧
      M6HdrExtInitOk extJ ∧ M6ExtW2bPres ext1 extJ ∧ (FullM6HdrMem c extJ sJ ⋆ R) mJ)
    (fun _ () mJ ⟨extJ, sJ, hcoreJ, hlenJ, hscJ, hinitJ, hwJ, hmJ⟩ => by
      c0_hsteps
      exact hQ () extJ sJ mJ hcoreJ hlenJ hscJ hinitJ.toOk
        (w2a_pres_of_init hpres1 hinitJ hwJ) hmJ)
    (fun _ hJ => by
      c0_hsteps_nogrp
      · m6h_call hRecomp
        refine m6HdrW2aSpec_of rfl hcfg hinit1.toOk hlen ((fullM6HdrMem_iff ..).mpr hm1)
          fun () ext2 s2 m2 hcore2 hlen2 hsc2 _ hw2 hm2 => ?_
        have ⟨hinit2, hw12⟩ := hw2 hinit1
        have hl2 : ext2.length = 288 := hinit2.toOk.len
        rw [fullM6HdrMem_iff] at hm2
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
          (fun _ (iv, ()) m3 hm3 => ?_)
          (fun _ hJiv => by c0_hsteps <;> exact hJiv (_, ()) m2 rfl)
        subst m3
        c0_hsteps
        refine hJ () _ ⟨_, s2, hcore2, hlen2, hsc2, ?_, ?_,
          (fullM6HdrMem_iff ..).mpr (by assumption)⟩
        · exact (hinit2.set_pos _ (by decide)).set_pos _ (by decide)
        · exact hw12.trans
            ((M6ExtW2bPres.set_ge8 _ (by decide)).trans (M6ExtW2bPres.set_ge8 _ (by decide)))
      · exact hJ () m1 ⟨ext1, s, rfl, hlen, M6HdrScratchPres.refl s, hinit1,
          M6ExtW2bPres.refl ext1, (fullM6HdrMem_iff ..).mpr hm1⟩)

/-! ## 2. Glue Histogram & Tier Getters (`3` Functions) -/

theorem m6_hdr_record_used_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_record_used_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_record_used_body
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
      · exact hJs (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJs (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hst_le : st.toNat ≤ 1 := by rcases hst with rfl | rfl <;> decide
  refine wp_join_group (ts := [i64]) (fun (gi, ()) m2 => m2 = m1 ∧ gi.toNat < 128)
    (fun _ (gi, ()) m2 ⟨hm2, hgi⟩ => ?_)
    (fun _ hJg => by
      c0_hsteps
      · exact hJg (_, ()) m1 ⟨rfl, by decide⟩
      · exact hJg (glue, ()) m1 ⟨rfl, by
          have h128 : (128 : BitVec 64).toNat = 128 := rfl; omega⟩)
  subst m2
  refine wp_join_group (ts := [i64])
    (fun (base, ()) m2 => m2 = m1 ∧ (base = 32#64 ∨ base = 160#64))
    (fun _ (base, ()) m2 ⟨hm2, hbase⟩ => ?_)
    (fun _ hJb => by
      c0_hsteps
      · exact hJb (32#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJb (160#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hbase_ge : 32 ≤ base.toNat := by rcases hbase with rfl | rfl <;> decide
  have hbase_le : base.toNat ≤ 160 := by rcases hbase with rfl | rfl <;> decide
  have hbg_eq : (base + gi).toNat = base.toNat + gi.toNat :=
    bv64_add_small_eq (by omega)
  have hbg_lt : (base + gi).toNat < ext1.length := by rw [hl1, hbg_eq]; omega
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m2 => ∃ ext2, M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2 ∧
      (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2)
    (fun _ () m2 ⟨ext2, hinit2, hw2, hm2⟩ => ?_)
    (fun _ hJu => by
      c0_hsteps
      · refine hJu () _ ⟨ext1.set (base + gi).toNat _,
          hinit1.set_pos _ (by rw [hbg_eq]; omega),
          M6ExtW2bPres.set_ge8 _ (by rw [hbg_eq]; omega), by assumption⟩
      · exact hJu () m1 ⟨ext1, hinit1, M6ExtW2bPres.refl ext1, hm1⟩)
  have hl2 : ext2.length = 288 := hinit2.toOk.len
  have htu_eq : ((14 : BitVec 64) + st).toNat = 14 + st.toNat :=
    bv64_add_small (n := 14) rfl (by omega)
  have htu_lt : ((14 : BitVec 64) + st).toNat < ext2.length := by rw [hl2, htu_eq]; omega
  c0_hsteps
  · refine hQ () _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
      ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos _ (by rw [htu_eq]; omega)).toOk
    · exact w2a_pres_of_init hpres1 (hinit2.set_pos _ (by rw [htu_eq]; omega))
        (hw2.trans (M6ExtW2bPres.set_ge8 _ (by rw [htu_eq]; omega)))
  · exact hQ () ext2 s m2 rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
      (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr hm2)

theorem m6_hdr_get_tier1_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_get_tier1_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_get_tier1_body
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
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_get_tier2_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_get_tier2_body
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

/-! ## 3. `delay[4]` Backoff (`4` Functions) -/

theorem m6_hdr_delaying_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_delaying_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_delaying_body
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
        (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1)) ((fullM6HdrMem_iff ..).mpr hm1)

theorem m6_hdr_bump_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_bump_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_bump_delay_body
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
    let ext2 := (ext1.set ((20 : BitVec 64) + id).toNat cur).set ((16 : BitVec 64) + id).toNat cur
    have hinit2 : M6HdrExtInitOk ext2 :=
      (hinit1.set_pos cur (by rw [hicur_eq]; omega)).set_pos cur (by rw [hicnt_eq]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 :=
      (M6ExtW2bPres.set_ge8 cur (by rw [hicur_eq]; omega)).trans
        (M6ExtW2bPres.set_ge8 cur (by rw [hicnt_eq]; omega))
    exact hQ () ext2 s _ rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
      (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr (by assumption))

theorem m6_hdr_reduce_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_reduce_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_reduce_delay_body
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


/-! ## 4. Watermarks & Tick Routing (`3` Functions) -/

theorem m6_hdr_get_watermark_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_get_watermark_body a m Q X := by
  rintro ⟨h, kind, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_get_watermark_body
  c0_hsteps_nogrp
  · exact hQ (0#64, ()) ext s m rfl hlen (M6HdrScratchPres.refl s) hext
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
    exact hQ (_, ()) ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) hinit1.toOk
      (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1)) ((fullM6HdrMem_iff ..).mpr hm1)

theorem m6_hdr_set_watermark_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Func.wp Γ Src.Tiers.m6_hdr_set_watermark_body a m Q X := by
  rintro ⟨h, kind, val, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp Src.Tiers.m6_hdr_set_watermark_body
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


end LeanQbe.T.Examples.Kissat.Proof.Tiers
