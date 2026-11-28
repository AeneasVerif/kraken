/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dense.Helpers

/-!
# Kissat Dense Watch Rebuild WP Proofs (`Proof.Dense.WpRebuild`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on
theorems/lemmas/sections, `0` legacy imports, `<= 100` cols) for:
1. `full_rebuild_watches_nosort_fid` (`Spec.fullRebuildWatchesM6Spec`)
2. `full_rebuild_watches` (`Spec.fullRebuildWatchesM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dense
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "dr_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem rebuild_dense_to_sparse {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hdense : FullDenseInv c F0 s) :
    let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
    FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧ s0.core.dense_mode = 0#64 :=
  ⟨hdense.toSparse_clear_dense, hdense.2.2.2.2.1, rfl⟩

/-- `full_rebuild_watches_nosort_fid` WP proof (`Spec.fullRebuildWatchesM6Spec`). -/
theorem full_rebuild_watches_nosort_fid_wp (Γ : Env)
    (hSweep : Γ.Has "full_arena_sweep" Proof.Spec.fullArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec) :
    ∀ a m Q X, Spec.fullRebuildWatchesM6Spec a m Q X →
      Func.wp Γ full_rebuild_watches_nosort_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdense, hm, hQ⟩
  unfold full_rebuild_watches_nosort_fid_body Func.wp
  have hm_f : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m :=
    fullM6HdrMem_focus_full hm
  c0_hsteps_nogrp
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have ⟨hsp0, hl0_0, _⟩ := rebuild_dense_to_sparse hdense
  have hm0 : (FullM6HdrMem c ext s0 ⋆ R) _ :=
    fullM6HdrMem_unfocus_full (by assumption)
  refine wp_join0 (P := fun mj => ∃ ext' s' m',
      m' = mj ∧ FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0 ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext' s' ⋆ R) m')
    (fun _ mj ⟨ext', s', m', hm_eq, hinv', hl0', hfl', hm'⟩ => by
      subst hm_eq; c0_hsteps_nogrp
      exact hQ 1#64 ext' s' m' hinv' hl0' hfl' (Or.inr (Or.inl rfl))
        (fun h => absurd h (by decide)) hm')
    (fun Js hJs => ?_)
  c0_hsteps_nogrp
  refine wp_while_state0
    (α := Σ' (extL : List (BitVec 64)) (sL : FullState),
      M6HdrExtOk extL ∧ FullSparseInv c F0 sL ∧ sL.core.cur_level = 0 ∧
      sL.core.fuel.toNat ≤ s.core.fuel.toNat)
    (fun st => c.max_vars - st.2.1.core.trail_end)
    (fun st mL => (FullM6HdrMem c st.1 st.2.1 ⋆ R) mL)
    (fun J hLoop => by
      c0_hsteps_nogrp
      exact hLoop ⟨ext, s0, hext, hsp0, hl0_0, Nat.le_refl _⟩ m hm0)
    (fun J ⟨extL, sL, hextL, hspL, hl0L, hflL⟩ mL hmL hStep => ?_)
  c0_hsteps_nogrp
  c0_hsplit
  · obtain ⟨F_curL, hwL⟩ := hspL.exists_witness
    dr_call hSweep
    refine ⟨c, F0, F_curL, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl, hspL.lengths, hwL.2.1,
      hspL.2.2.1, hspL.2.2.2.2, fun hgt => absurd hgt (by omega),
      fullM6HdrMem_focus_full hmL, ?_⟩
    rintro sr vals1 flags1 lvl1 rsns1 trl1 tp1 te1 unass1 unfl1 wvec1 wstk1 arena1 alen1
      wlen1 wu1 fred1 ni1 nr1 nb1 oom1 sc1 m1 s1 hlen1 hdom_sr hext1 hws1 hll1 hw1 hnd1 _
      _ hsr1 hsr2 _ hm1
    have hsp1 : FullSparseInv c F0 s1 :=
      ⟨⟨hlen1, ⟨F_curL, hw1⟩⟩, hspL.2.1, hnd1, ⟨hll1, hext1 ▸ hspL.2.2.2.1.2⟩, hspL.2.2.2.2⟩
    have hl0_1 : s1.core.cur_level = 0 := hl0L
    have hm1_u : (FullM6HdrMem c extL s1 ⋆ R) m1 := fullM6HdrMem_unfocus_full hm1
    c0_hsteps_nogrp
    · c0_hsteps_nogrp
      exact hQ 20#64 extL s1 m1 (FullM6HdrInv.mk_inv hcfg hextL hsp1) hl0_1 hflL
        (Or.inr (Or.inr rfl)) (fun _ => (hsr2 (by simpa using hc)).2) hm1_u
    · c0_hsteps_nogrp
      exact hQ 0#64 extL s1 m1 (FullM6HdrInv.mk_inv hcfg hextL hsp1) hl0_1 hflL
        (Or.inl rfl) (fun h => absurd h (by decide)) hm1_u
    · have h01 : sr = 0#64 ∨ sr = 1#64 := by
        rcases hdom_sr with rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (by contradiction)
      refine wp_join0 (P := fun m2 => ∃ ext2 s2,
            M6HdrExtOk ext2 ∧ FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
            s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (sr = 1#64 → sL.core.trail_end < s2.core.trail_end) ∧
            (FullM6HdrMem c ext2 s2 ⋆ R) m2)
          (fun _ m2 ⟨ext2, s2, hext2, hsp2, hl0_2, hfl2, hgrow, hm2⟩ => by
            c0_hsteps_nogrp
            obtain ⟨F_cur2, hw2⟩ := hsp2.exists_witness
            dr_call hProp
            refine ⟨c, F0, F_cur2, ext2, s2, R, rfl, hcfg, hext2, hsp2.lengths, hw2.2.1,
              hsp2.2.2.2.2, hm2, ?_⟩
            rintro pr ext3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 unass3 unfl3 wvec3
              arena3 wstk3 wlen3 wu3 fuel3 ctype3 cref3 c0_3 c1_3 oom3 sc3 m3 s3
              hext3 _ hlen3 hw3 hte3 _ hap3 hprobe3 _ _ _ _ hfl3 _ _ hpr1 _ _ hm3
            have hnd3 : FullArenaVarsNodup s3 := fun r hr hng => by
              change r ∈ fullArenaClauseRefsCore s3.core at hr
              have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core :=
                hap3.2.1
              rw [hrefs] at hr
              have hp := hap3.2.2 r hr
              change fullArenaClauseGarbCore s3.core r = false at hng
              rw [hp.2.1] at hng
              change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
              exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp2.2.2.1 r hr hng)
            have hll3 : FullLastLearnedWf s3 :=
              hsp2.2.2.2.1.1.of_refs_subset hprobe3.1.1 (fun r hr => by
                change r ∈ fullArenaClauseRefsCore s3.core; rw [hap3.2.1]; exact hr)
            have hsp3 : FullSparseInv c F0 s3 :=
              ⟨⟨hlen3, ⟨F_cur2, hw3⟩⟩, hsp2.2.1, hnd3, ⟨hll3, hprobe3.1.2 ▸ hsp2.2.2.2.1.2⟩,
                hsp2.2.2.2.2⟩
            c0_hsteps_nogrp
            · have huns : F0.Unsat :=
                level0_unsat_of_conflict_okW hw3 hl0_2 (hpr1 hc).2.2
              c0_hsteps_nogrp
              exact hQ 20#64 ext3 s3 m3 (FullM6HdrInv.mk_inv hcfg hext3 hsp3) hl0_2
                (Nat.le_trans hfl3 hfl2) (Or.inr (Or.inr rfl)) (fun _ => huns) hm3
            · c0_hsteps_nogrp
              exact hJs _ ⟨ext3, s3, _, rfl, FullM6HdrInv.mk_inv hcfg hext3 hsp3, hl0_2,
                Nat.le_trans hfl3 hfl2, hm3⟩
            · have hsr1_eq : sr = 1#64 := by
                rcases h01 with rfl | rfl
                · exfalso; simp at hc
                · rfl
              have hlt_m : c.max_vars - s3.core.trail_end < c.max_vars - sL.core.trail_end := by
                have := Nat.lt_of_lt_of_le (hgrow hsr1_eq) hte3.1
                have := hsp3.lengths.core_ok.trail_end_le
                have := hsp3.lengths.core_ok.cur_vars_le
                omega
              c0_hsteps_nogrp
              exact hStep ⟨ext3, s3, hext3, hsp3, hl0_2, Nat.le_trans hfl3 hfl2⟩ m3 hlt_m hm3)
          (fun Js2 hJs2 => ?_)
      c0_hsteps_nogrp
      · let s2 : FullState := { s1 with core := { s1.core with unflushed := 0#64 } }
        have hw2 : FullWitnessInv c F0 F_curL s2.core :=
          fullWitnessInv_with_unflushed hw1 0#64
        have hsp2 : FullSparseInv c F0 s2 :=
          ⟨⟨⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len }, hlen1.scratch_ok⟩,
            ⟨F_curL, hw2⟩⟩, hsp1.2.1, hnd1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
        exact hJs2 _ ⟨extL, s2, hextL, hsp2, hl0_1, hflL,
          fun h => absurd (hc.symm.trans h) (by decide),
          fullM6HdrMem_unfocus_full (by assumption)⟩
      · exact hJs2 m1 ⟨extL, s1, hextL, hsp1, hl0_1, hflL,
          fun hsr1_eq => (hsr1 hsr1_eq).2, hm1_u⟩
  · c0_hsteps_nogrp
    exact hJs mL ⟨extL, sL, mL, rfl, FullM6HdrInv.mk_inv hcfg hextL hspL, hl0L, hflL, hmL⟩

/-- `full_rebuild_watches` WP proof (`Spec.fullRebuildWatchesM6Spec`). -/
theorem full_rebuild_watches_wp (Γ : Env)
    (hNosort : Γ.Has "full_rebuild_watches_nosort_fid" Spec.fullRebuildWatchesM6Spec)
    (hSort : Γ.Has "full_sort_bin_watches_fid" Watch.Spec.fullSortBinWatchesSpec) :
    ∀ a m Q X, Spec.fullRebuildWatchesM6Spec a m Q X →
      Func.wp Γ full_rebuild_watches_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdense, hm, hQ⟩
  unfold full_rebuild_watches_body Func.wp
  c0_hsteps_nogrp
  dr_call hNosort
  refine ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdense, hm, ?_⟩
  intro r ext' s' m' hinv' hl0' hfl' hdom' huns' hm'
  c0_hsteps_nogrp
  refine wp_join0 (P := fun m'' => ∃ s'',
      FullM6HdrInv c F0 ext' s'' ∧ s''.core.cur_level = 0 ∧
      s''.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext' s'' ⋆ R) m'')
    (fun _ m'' ⟨s'', hinv'', hl0'', hfl'', hm''⟩ => by
      c0_hsteps_nogrp
      exact hQ r ext' s'' m'' hinv'' hl0'' hfl'' hdom' huns' hm'')
    (fun Js hJs => ?_)
  c0_hsteps_nogrp
  c0_hsplit
  · obtain ⟨F_cur', hw'⟩ := hinv'.sparse.exists_witness
    dr_call hSort
    refine ⟨c, F0, F_cur', s', m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R, rfl, hw',
      fullM6HdrMem_focus_full hm', ?_⟩
    intro wstk'' m'' s'' _ hspw'' _ hm''
    c0_hsteps_nogrp
    exact hJs m'' ⟨s'', FullM6HdrInv.mk_inv hinv'.cfgOk hinv'.extOk hspw''.toSparse,
      hl0', hfl', fullM6HdrMem_unfocus_full hm''⟩
  · c0_hsteps_nogrp
    exact hJs m' ⟨s', hinv', hl0', hfl', hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Dense
