/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2d
import all LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
import all LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1

/-!
# Kissat Fidelity Delayed-Watch BCP Outer Proof (`FullFidelityBcpProof2`)

Plain `public section` (`0` `@[expose]`, `0` `public` `import all`, `std3` axioms only;
private `import all` of `FullFidelityBcpProof0` and `FullM6BcpS15Proof1`).
Proves `full_propagate_ignore_fid_wp` certifying `full_propagate_ignore_fid_body` against
`FullM6BcpS15.fullPropagateIgnoreS15Spec`:
1. `fid_compact_post_wp`: watch compaction, sentinel fill, final `full_prop_flush_del_fid`,
   chrono repair, and exit / outer-loop continue.
2. `fid_post_lp_ovf_wp`: post-scan overflow handler (delayed-watch flush, cold
   `full_prop_lit_ovf_hot` push, `wvec[nl64]` rebase, arena swap or keep + `brk = 2`).
3. `full_propagate_ignore_fid_wp`: outer propagation loop (`while (prop < tend)`), hoisted scalar
   fields (`wvec`, `del`, `dlim`, `fuel`, `nl_lvl`), and `FidOuterInv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fid_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "fid_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "fid_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Compaction + Final Flush + Chrono + Exit/Continue (`fid_compact_post_wp`) -/

private theorem fid_compact_post_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b off_b p_b q_b end_b di_b brk_b
      t0_v nl64 : BitVec 64}
    {not_lit : BitVec 32} {dlen_b : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 →
      sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b →
      sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      sem_next.core.confl_type = s.core.confl_type →
      sem_next.core.dense_mode = 0#64 →
      sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level →
      sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated →
      te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc →
      FidScr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R)
        mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hwc : c.wcap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : FidScr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat))
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hpi_b : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
      sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat)
    (hdi_b : di_b.toNat = 3 * dlen_b) (hdlen_b : dlen_b ≤ c.delayed_cap)
    (hdok_b : DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat)
    (hd0_b : c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
    (hmb : (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) :
    wp Γ Q X (fidCompactAndPostExpr J_out c.hdr c.pWstk c.pWvec nl64 prop_v fuel1 te_b un_b
      uf_b tk_b off_b p_b q_b end_b di_b brk_b t0_v) mb := by
  subst nl64
  obtain ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ := hs_disk
  have hnot_b : not_lit.toNat < 2 * sem_b.core.cur_vars := by
    rw [hpi_b.cur_vars_eq, hs_base]; exact hnot_lt
  have hend_b_le : end_b.toNat ≤ c.wcap := by
    have := hpi_b.end_lt_wcap hnot_b; omega
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge_b := hpi_b.sw.q_ge
  have hq_le_b := hpi_b.sw.q_le_p
  have hp_le_b := hpi_b.sw.p_le_end
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b.tr.te_ge; subst hs_base; exact this
  have hsd_len : s_disk.LengthsOk c := by
    subst hs_disk_eq
    exact ⟨{ hlen0.core_ok with
        trail_end_le := Nat.le_trans htem_le
          (Nat.le_trans hte_sem_le (by
            rw [← hcv_o]
            have hcv_b : sem_b.core.cur_vars = sem.core.cur_vars := by
              rw [hpi_b.cur_vars_eq, hs_base]
            rw [← hcv_b]
            exact hpi_b.len.core_ok.trail_end_le))
        propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hnot_b_mv : not_lit.toNat < 2 * c.max_vars := by
    have := hpi_b.len.core_ok.cur_vars_le; omega
  have hnl64_1_idx : ((BitVec.setWidth 64 not_lit <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * not_lit.toNat + 1 := by
    simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_add1_nat not_lit
  let s_pi_b : FullState :=
    { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
  have hscr_spi : FidScr s s_pi_b := by
    unfold FidScr at hsc_o ⊢; dsimp only [s_pi_b]; rw [hs_base]; dsimp only; rw [hsc_o]
  have hscr_b : FidScr s sem_b := fid_scr_of_pi hpi_b.sc_eq hscr_spi
  unfold fidCompactAndPostExpr
  refine wp_loop_group (fun rem_c (pc_v, qc_v, ()) mc =>
    ∃ wstk_c : List (BitVec 32),
      rem_c = end_b.toNat - pc_v.toNat ∧
      wstk_c.length = c.wcap ∧
      p_b.toNat ≤ pc_v.toNat ∧ pc_v.toNat ≤ end_b.toNat ∧
      qc_v.toNat = q_b.toNat + (pc_v.toNat - p_b.toNat) ∧
      (∀ k, off_b.toNat ≤ k → k < q_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k < pc_v.toNat - p_b.toNat, wstk_c[q_b.toNat + k]? = sem_b.core.wstk[p_b.toNat + k]?) ∧
      (∀ k, pc_v.toNat ≤ k → k < end_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k, (k < off_b.toNat ∨ end_b.toNat ≤ k) → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s_disk { sem_b with core :=
        { sem_b.core with wstk := wstk_c } }) ⋆ R) mc) ?_ ?_
  · rintro Jc rem_c ⟨pc_v, qc_v, ⟨⟩⟩ mc ih_c ⟨wstk_c, rfl, hwc_len, hp_pc, hpc_end,
        hqc_n, hpre_c, hsuf_c, hrem_c, hout_c, hmc⟩
    have hmem_c_len : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len
        (sem := { sem_b with core := { sem_b.core with wstk := wstk_c } })
        ⟨{ hpi_b.len.core_ok with wstk_len_arr := hwc_len }, hpi_b.len.scratch_ok⟩
        (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
        (by rw [hs_disk_eq]; dsimp only; rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
        rfl
    have hwc_mem : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).core.wstk.length =
        c.wcap := by rw [fastPropMem_wstk]; exact hwc_len
    fid_hsplit
    · have hpc_lt : pc_v.toNat < end_b.toNat := hc
      have hpc_lt_w : pc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hqc_lt_w : qc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hpc1_n : (pc_v + 1#64).toNat = pc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      have hqc1_n : (qc_v + 1#64).toNat = qc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      let v_p := wstk_c[pc_v.toNat]'hpc_lt_w
      let wstk_c' := wstk_c.set qc_v.toNat v_p
      have hstep := propLit_loop2_step hq_ge_b hq_le_b hp_pc hpc_lt hpc_lt_w
        (by rw [← hqc_n]; exact hqc_lt_w) hpre_c hsuf_c hrem_c hout_c
      rw [← hqc_n] at hstep
      fid_hsteps
      exact ih_c _ (pc_v + 1#64, qc_v + 1#64, ()) m (by rw [hpc1_n]; omega)
        ⟨wstk_c', rfl, by simp [wstk_c', hwc_len], by rw [hpc1_n]; omega,
          by rw [hpc1_n]; omega, by rw [hqc1_n, hpc1_n]; omega,
          hstep.1, fun k hk => by rw [hpc1_n] at hk; exact hstep.2.1 k hk,
          fun k hk1 hk2 => by rw [hpc1_n] at hk1; exact hstep.2.2.1 k hk1 hk2,
          hstep.2.2.2, by
            simpa only [wstk_c', v_p, fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
    · have hpc_eq : pc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
      rw [hpc_eq] at hqc_n hsuf_c
      fid_hsteps_nogrp
      refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
        (BitVec.setWidth 32 (qc_v - off_b)) ?_ hmc) ?_
      next =>
        dsimp only
        erw [hnl64_1_idx]
        rw [fastPropMem_wvec, hpi_b.len.core_ok.wvec_len]
        change 2 * not_lit.toNat + 1 < 4 * c.max_vars; omega
      intro m hm
      dsimp only at hm
      erw [hnl64_1_idx] at hm
      rw [fastPropMem_wvec] at hm
      replace hm : (FullMem c (fastPropMem s_disk
          { sem_b with core :=
            { sem_b.core with
              wstk := wstk_c
              wvec := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
                ((qc_v - off_b).setWidth 32) } }) ⋆ R) m := by
        simpa only [fastPropMem] using hm
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ st_fin : FullState,
            st_fin.LengthsOk c ∧
            FullWitnessInv c F0 F_cur st_fin.core ∧
            AgreesExcept propLitCoreMask s_base.core st_fin.core ∧
            FullPropDecSpecs.FullTrailExt s_base.core st_fin.core ∧
            FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core ∧
            st_fin.core.oom = sem_b.core.oom ∧
            st_fin.core.confl_type = sem_b.core.confl_type ∧
            st_fin.core.confl_ref = sem_b.core.confl_ref ∧
            st_fin.core.confl_lit0 = sem_b.core.confl_lit0 ∧
            st_fin.core.confl_lit1 = sem_b.core.confl_lit1 ∧
            st_fin.core.cur_vars = sem_b.core.cur_vars ∧
            st_fin.core.vals = sem_b.core.vals ∧
            st_fin.core.trail_end = sem_b.core.trail_end ∧
            st_fin.core.unassigned = sem_b.core.unassigned ∧
            st_fin.core.unflushed = sem_b.core.unflushed ∧
            st_fin.core.arena_len = sem_b.core.arena_len ∧
            st_fin.core.cur_level = sem_b.core.cur_level ∧
            st_fin.core.arena = sem_b.core.arena ∧
            FidScr s st_fin ∧
            (c.delayed_cap = 0 → st_fin.scratch.delayed = s.scratch.delayed) ∧
            DelayedWatchesOk s_base.core st_fin.scratch.delayed dlen_b not_lit.toNat ∧
            (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) ?_ ?_
      · rintro _ ⟨⟩ mf ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f,
            har_f, hscr_f, hd0_f, hdok_f, hmf⟩
        exact fid_post_flush_wp hChrono hFlush hQ hJ_out hlen0 hpr_lt hs_base hfuel1
          ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ htr_o hperm_o hag_o hcv_o hcl_o hprob_o
          halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge hpi_b.len hpi_b.cur_vars_eq
          hpi_b.tr hdense_b hte_b hun_b huf_b hbr0 hbr1 hbr_cases hdi_b hdlen_b hdok_f
          hlen_f hwf_f hag_f htr_f hperm_f hoom_f hct_f hcr_f hc0_f hc1_f hcv_f hvals_f hte_f
          hun_f huf_f halen_f hcl_f har_f hscr_f hd0_f hmf
      · intro Jfn hJfn
        have hqc_v_eq : qc_v.toNat = q_b.toNat + (end_b.toNat - p_b.toNat) := hqc_n
        have hqc_le_end : qc_v.toNat ≤ end_b.toNat := by omega
        have hidx1_lt : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
            sem_b.core.wvec.length := by
          rw [hpi_b.len.core_ok.wvec_len, m7_bv64_shl1_add1_nat]; omega
        let wvec_f := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
          ((qc_v - off_b).setWidth 32)
        let wu_f := sem_b.core.wusable + (end_b - qc_v)
        fid_hsplit
        · fid_hsteps
          refine wp_loop_group (fun rem_k (k_v, ()) mk =>
            ∃ wstk_k : List (BitVec 32),
              rem_k = end_b.toNat - k_v.toNat ∧
              wstk_k.length = c.wcap ∧
              qc_v.toNat ≤ k_v.toNat ∧ k_v.toNat ≤ end_b.toNat ∧
              (∀ i, (i < qc_v.toNat ∨ end_b.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
              (FullMem c (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }) ⋆ R) mk) ?_ ?_
          · rintro Jk rem_k ⟨k_v, ⟨⟩⟩ mk ih_k ⟨wstk_k, rfl, hwk_len, hq_k, hk_end,
                hk_keep, hmk⟩
            have hmem_k_len : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).LengthsOk c :=
              fastPropMem_lengthsOk hsd_len
                (sem := { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } })
                ⟨{ hpi_b.len.core_ok with
                    wvec_len := by simp [wvec_f, hpi_b.len.core_ok.wvec_len]
                    wstk_len_arr := hwk_len },
                 hpi_b.len.scratch_ok⟩
                (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
                (by rw [hs_disk_eq]; dsimp only
                    rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
                rfl
            have hwk_mem : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).core.wstk.length =
                c.wcap := by rw [fastPropMem_wstk]; exact hwk_len
            fid_hsplit
            · have hk_lt : k_v.toNat < end_b.toNat := hc
              have hk_lt_w : k_v.toNat < wstk_k.length := by rw [hwk_len]; omega
              have hk1_n : (k_v + 1#64).toNat = k_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
              have hk_dec : end_b.toNat - (k_v + 1#64).toNat < end_b.toNat - k_v.toNat := by
                omega
              have hq_k1 : qc_v.toNat ≤ (k_v + 1#64).toNat := by omega
              have hk1_end : (k_v + 1#64).toNat ≤ end_b.toNat := by omega
              refine wp_store_sep
                (FullArenaTactics.c0_store_full_wstk 0xFFFFFFFF#32
                  (by rw [hwk_mem]; exact Nat.lt_of_lt_of_eq hk_lt_w hwk_len) hmk) ?_
              intro m hm
              clear hmk hwk_mem
              fid_hsteps
              dsimp only [Arg.val] at hm
              exact ih_k (end_b.toNat - (k_v + 1#64).toNat) (k_v + 1#64, ()) m hk_dec
                ⟨wstk_k.set k_v.toNat 0xFFFFFFFF#32, rfl,
                  by rw [List.length_set, hwk_len], hq_k1, hk1_end,
                  propLit_loop3_step hq_k hk_lt hk_keep,
                  by simpa only [fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
            · fid_hsteps
              have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwk_len
                hqc_v_eq hpre_c hsuf_c hout_c hk_keep
              let st_fin_k : FullState :=
                { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }
              exact hJfn () mk ⟨st_fin_k, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, rfl,
                hscr_b, hd0_b, hdok_b, hmk⟩
          · intro Jk hJk
            exact hJk _ (qc_v, ()) m
              ⟨wstk_c, rfl, hwc_len, Nat.le_refl _, hqc_le_end,
                fun _ _ => rfl,
                by simpa only [wvec_f, wu_f, fastPropMem_wusable, fastPropMem] using hm⟩
        · have hqc_eq_end : qc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
          have hsub0 : end_b - qc_v = 0#64 := by rw [hqc_eq_end]; simp
          have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwc_len
            hqc_v_eq hpre_c hsuf_c hout_c (fun _ _ => rfl)
          have hwu0 : sem_b.core.wusable + (end_b - qc_v) = sem_b.core.wusable := by
            rw [hsub0]; simp
          let st_fin_0 : FullState :=
            { sem_b with core :=
              { sem_b.core with
                wstk := wstk_c, wvec := wvec_f,
                wusable := sem_b.core.wusable + (end_b - qc_v) } }
          exact hJfn () m ⟨st_fin_0, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, rfl,
            hscr_b, hd0_b, hdok_b,
            by simpa only [st_fin_0, wvec_f, hwu0] using hm⟩
  · intro Jc hJc
    exact hJc _ (p_b, q_b, ()) mb
      ⟨sem_b.core.wstk, rfl, hpi_b.len.core_ok.wstk_len_arr, Nat.le_refl _,
        hp_le_b, by simp, fun _ _ _ => rfl, fun _ hk => absurd hk (by omega),
        fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩

/-! ## 2. Post-Scan Overflow Handler (`fid_post_lp_ovf_wp`) -/

private theorem fid_post_lp_ovf_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_base s_disk sem_o sem_p : FullState}
    {ignore_ref t0_v off_o p_o end_o te_p un_p uf_p tk_p p_p q_p di_p brk_p : BitVec 64}
    {ovf_p : Bool} {not_lit not_lit_v ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32}
    {ovf_ri_p nl64 : BitVec 64} {dlen_p : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mbp : Mem 64}
    {Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    (hOvf : ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hBo : ∀ xs m,
      (match xs with
        | (te_b, un_b, uf_b, _tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, _ovf_b, ()) =>
          ∃ (sem_b : FullState) (dlen_b : Nat),
            PropLitInv c F0 F_cur
              { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
              sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat ∧
            di_b.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
            DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
            (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
            te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
            uf_b = sem_b.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
            (brk_b = 0#64 →
              sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
              p_b = end_b) ∧
            (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
              sem_b.core.oom = 0#64) ∧
            (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
            (FullMem c (fastPropMem s_disk sem_b) ⋆ R) m) → Bo xs m)
    (ih_o : ∀ rem' xs m,
      rem' < (end_o.toNat - p_o.toNat) + 1 →
      (match xs with
        | (te_o', un_o', uf_o', _tk_o', off_o', p_o', q_o', end_o', di_o', brk_o', ovf_o', ()) =>
          ∃ (sem_o' : FullState) (dlen_o' : Nat),
            rem' = (end_o'.toNat - p_o'.toNat) + (if ovf_o' then 1 else 0) ∧
            PropLitInv c F0 F_cur
              { s_base with scratch := { s_base.scratch with delayed := sem_o'.scratch.delayed } }
              sem_o' not_lit.toNat off_o'.toNat q_o'.toNat p_o'.toNat end_o'.toNat ∧
            di_o'.toNat = 3 * dlen_o' ∧ dlen_o' ≤ c.delayed_cap ∧
            DelayedWatchesOk s_base.core sem_o'.scratch.delayed dlen_o' not_lit.toNat ∧
            (c.delayed_cap = 0 → sem_o'.scratch.delayed = s.scratch.delayed) ∧
            te_o'.toNat = sem_o'.core.trail_end ∧ un_o' = sem_o'.core.unassigned ∧
            uf_o' = sem_o'.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o'.core.trail_end) ∧
            (ovf_o' = true → brk_o' = 0#64 ∧ sem_o'.core.oom = 0#64 ∧
              sem_o'.core.confl_type = s.core.confl_type) ∧
            (ovf_o' = false →
              (brk_o' = 0#64 →
                sem_o'.core.oom = 0#64 ∧ sem_o'.core.confl_type = s.core.confl_type ∧
                p_o' = end_o') ∧
              (brk_o' = 1#64 → PropLitConfl F_cur ignore_ref sem_o'.core ∧
                sem_o'.core.oom = 0#64) ∧
              (brk_o' = 0#64 ∨ brk_o' = 1#64)) ∧
            (FullMem c (fastPropMem s_disk sem_o') ⋆ R) m) → Lo xs m)
    (har : c.arena_cap < 2 * 2 ^ 28) (hwc : c.wcap < 2 * 2 ^ 28)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem_p.core.cur_vars)
    (hsd_pr : s_disk.core.propagated = sem_p.core.propagated)
    (hnot_lt : not_lit.toNat < 2 * sem_p.core.cur_vars)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat))
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hct_o2 : sem_o.core.confl_type = s.core.confl_type)
    (ht0_p : t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end)
    (hnl_eq : not_lit_v = not_lit)
    (hpi_p : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
      sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat)
    (hdi_p : di_p.toNat = 3 * dlen_p) (hdlen_p : dlen_p ≤ c.delayed_cap)
    (hdok_p : DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat)
    (hd0_p : c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed)
    (_hpo_le_pp : p_o.toNat ≤ p_p.toNat)
    (hte_p : te_p.toNat = sem_p.core.trail_end) (hun_p : un_p = sem_p.core.unassigned)
    (huf_p : uf_p = sem_p.core.unflushed) (hoom_p : sem_p.core.oom = 0#64)
    (hnoov : ovf_p = false →
      (brk_p = 0#64 → p_p = end_o ∧ sem_p.core.confl_type = sem_o.core.confl_type) ∧
      (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
      (brk_p = 0#64 ∨ brk_p = 1#64))
    (hov_yes : ovf_p = true →
      brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
      2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
      end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
      ovf_cr_p.toNat < 0x80000000 ∧
      ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
      ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
        sem_p.core.arena_len ∧
      ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat ≠ not_lit.toNat ∧
      2 ≤ ovf_ri_p.toNat ∧
      ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
      sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hmbp : (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) :
    wp Γ Q X (fidPostLpOvfExpr c nl64 not_lit_v off_o end_o Bo Lo
      te_p un_p uf_p tk_p p_p q_p di_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p)
      mbp := by
  have hmaxv := c.hmaxv
  unfold dimacsBound at hmaxv
  rw [hnl_eq, hnl64]
  unfold fidPostLpOvfExpr
  refine wp_unroll_group fun _Js0 _hJs0 => ?_
  fid_hsplit
  · have hovf_true : ovf_p = true := hc
    have hov_y := hov_yes hovf_true
    subst hovf_true
    obtain ⟨rfl, hct_p, hp_off2, hq_pp2, hrem_dec, hcr_lt, hcr_ref, hcr_fit,
      hoth_lt, hovf_lt, hovf_ne, hri2, hri_lt, har3, har4, har_ri⟩ := hov_y
    have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
    have hcv_p := hpi_p.len.core_ok.cur_vars_le
    have hnot_c : not_lit.toNat < 2 * c.max_vars := by omega
    let s_pi_p : FullState :=
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
    have hsd_cv_b : s_disk.core.cur_vars = s_base.core.cur_vars := by
      rw [hsd_cv, hpi_p.cur_vars_eq]
    have hsd_pr_b : s_disk.core.propagated = s_base.core.propagated := by
      rw [hsd_pr, hpi_p.ag.get FullCoreState.propagated]
    let P_jf : BitVec 64 × Bool → Mem 64 → Prop := fun (di_f, fok) mf =>
      ∃ sem_f : FullState,
        di_f = 0#64 ∧
        sem_f.LengthsOk c ∧ WatchStackLayout sem_f.core ∧
        FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem_f.core) ∧
        AgreesExcept propLitCoreMask s_base.core sem_f.core ∧
        FullPropDecSpecs.FullTrailExt s_base.core sem_f.core ∧
        FullPropDecSpecs.FullArenaPermEq s_base.core sem_f.core ∧
        sem_f.core.cur_vars = sem_p.core.cur_vars ∧
        sem_f.core.vals = sem_p.core.vals ∧
        sem_f.core.arena = sem_p.core.arena ∧
        sem_f.core.arena_len = sem_p.core.arena_len ∧
        sem_f.core.trail_end = sem_p.core.trail_end ∧
        sem_f.core.unassigned = sem_p.core.unassigned ∧
        sem_f.core.unflushed = sem_p.core.unflushed ∧
        sem_f.core.oom = sem_p.core.oom ∧
        sem_f.core.confl_type = sem_p.core.confl_type ∧
        sem_f.scratch = { s_pi_p.scratch with
          search_ticks := sem_f.scratch.search_ticks,
          wsort := sem_f.scratch.wsort, phases := sem_f.scratch.phases } ∧
        sem_f.scratch.delayed = sem_p.scratch.delayed ∧
        (let off_f := fullWatchOffCore sem_f.core not_lit.toNat
         SplitWatchesInv F_cur sem_f.core not_lit.toNat off_f
           (off_f + (q_p.toNat - off_o.toNat))
           (off_f + (p_p.toNat - off_o.toNat))
           (off_f + (end_o.toNat - off_o.toNat))) ∧
        (FullMem c (fastPropMem s_disk sem_f) ⋆ R) mf
    refine wp_join_group (fun (di_f, fok, ()) mf => P_jf (di_f, fok) mf) ?_ ?_
    · rintro _ ⟨di_f, fok, ⟨⟩⟩ mf
        ⟨sem_f, rfl, hlen_f, hlay_f, hnw_f, hag_f, htr_f, hperm_f, hcv_f, hvals_f, har_f,
          halen_f, hte_f, hun_f, huf_f, hoom_f, hct_f, hsc_f, hdel_f, hsw_f, hmf⟩
      let P_jp : Bool → Mem 64 → Prop := fun pk m4 =>
        ∃ st4 : FullState,
          st4.LengthsOk c ∧ WatchStackLayout st4.core ∧
          FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) ∧
          AgreesExcept propLitCoreMask s_base.core st4.core ∧
          FullPropDecSpecs.FullTrailExt s_base.core st4.core ∧
          FullPropDecSpecs.FullArenaPermEq sem_f.core st4.core ∧
          st4.core.cur_vars = sem_f.core.cur_vars ∧
          st4.core.vals = sem_f.core.vals ∧
          st4.core.arena = sem_f.core.arena ∧
          st4.core.arena_len = sem_f.core.arena_len ∧
          st4.core.trail_end = sem_p.core.trail_end ∧
          st4.core.unassigned = sem_p.core.unassigned ∧
          st4.core.unflushed = sem_p.core.unflushed ∧
          st4.core.oom = sem_p.core.oom ∧
          st4.core.confl_type = sem_p.core.confl_type ∧
          st4.scratch = { s_pi_p.scratch with
            search_ticks := st4.scratch.search_ticks,
            wsort := st4.scratch.wsort, phases := st4.scratch.phases } ∧
          st4.scratch.delayed = sem_p.scratch.delayed ∧
          (∀ l < 2 * sem_f.core.cur_vars, l ≠ ovf_rw_p.toNat →
            fullWatchSizeCore st4.core l = fullWatchSizeCore sem_f.core l ∧
            ∀ k < fullWatchSizeCore sem_f.core l,
              st4.core.wstk[fullWatchOffCore st4.core l + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core l + k]?) ∧
          (pk = true →
            fullWatchSizeCore st4.core ovf_rw_p.toNat =
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 2 ∧
            (∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
              st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?) ∧
            st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat]? =
                some (ovf_oth_p &&& 0x7FFFFFFF#32) ∧
            st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 1]? = some ovf_cr_p) ∧
          (pk = false →
            fullWatchSizeCore st4.core ovf_rw_p.toNat =
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat ∧
            ∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
              st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?) ∧
          (FullMem c (fastPropMem s_disk st4) ⋆ R) m4
      refine wp_join_group (fun (pk, ()) m4 => P_jp pk m4) ?_ ?_
      · rintro _ ⟨pk, ⟨⟩⟩ m4
          ⟨st4, hlen4, hlay4, hnw4, hag4, htr4, hperm24,
            hcv4, hvals4, har4_eq, hal4, hte4, hun4, huf4, hoom4, hct4,
            hsc4, hdel4, hoth_pr, hpok_t_pr, hpok_f_pr, hmo'⟩
        have hnot_f : not_lit.toNat < 2 * sem_f.core.cur_vars := hcv_f.symm ▸ hnot_lt
        have hcv4_p : st4.core.cur_vars = sem_p.core.cur_vars := hcv4.trans hcv_f
        have hnot4 : not_lit.toNat < 2 * st4.core.cur_vars := hcv4.symm ▸ hnot_f
        have hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals4, hvals_f]; exact hpi_p.not_f
        have hpi_f : PropLitInv c F0 F_cur s_pi_p sem_f not_lit.toNat
            (fullWatchOffCore sem_f.core not_lit.toNat)
            (fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat)) := by
          exact { len := hlen_f, nw := hnw_f, sw := hsw_f
                  ag := hag_f, tr := htr_f, perm := hperm_f
                  sc_eq := hsc_f, not_f := by rw [hvals_f]; exact hpi_p.not_f }
        have hoff_f_lt64 : fullWatchOffCore sem_f.core not_lit.toNat < 2 ^ 64 := by
          have := hsw_f.layout.bounds not_lit.toNat hnot_f
          have := hlen_f.core_ok.wlen_le; omega
        have hend_f_le : fullWatchOffCore sem_f.core not_lit.toNat +
            (end_o.toNat - off_o.toNat) ≤ c.wcap := by
          have := hsw_f.layout.bounds not_lit.toNat hnot_f
          rw [hsw_f.off_eq, hsw_f.sz_eq] at this
          have := hlen_f.core_ok.wlen_le
          have := hsw_f.q_ge; have := hsw_f.q_le_p; have := hsw_f.p_le_end
          omega
        let off_f_v := BitVec.ofNat 64 (fullWatchOffCore sem_f.core not_lit.toNat)
        let q_f_v := off_f_v + (q_p - off_o)
        let p_f_v := off_f_v + (p_p - off_o)
        let end_f_v := off_f_v + (end_o - off_o)
        have hq_ge_o := hpi_p.sw.q_ge
        have hq_le_o := hpi_p.sw.q_le_p
        have hp_le_o := hpi_p.sw.p_le_end
        have hend_o_le := hpi_p.end_lt_wcap hnot_lt
        have hoff_fv_n : off_f_v.toNat = fullWatchOffCore sem_f.core not_lit.toNat :=
          m7_bv64_ofNat_toNat_lt hoff_f_lt64
        have hqf_n : q_f_v.toNat =
            fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat) := by
          dsimp only [q_f_v]
          rw [BitVec.toNat_add, hoff_fv_n, m7_bv64_sub_toNat hq_ge_o, Nat.mod_eq_of_lt (by omega)]
        have hpf_n : p_f_v.toNat =
            fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat) := by
          dsimp only [p_f_v]
          rw [BitVec.toNat_add, hoff_fv_n, m7_bv64_sub_toNat (Nat.le_trans hq_ge_o hq_le_o),
            Nat.mod_eq_of_lt (by omega)]
        have hendf_n : end_f_v.toNat =
            fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat) := by
          dsimp only [end_f_v]
          rw [BitVec.toNat_add, hoff_fv_n,
            m7_bv64_sub_toNat (Nat.le_trans (Nat.le_trans hq_ge_o hq_le_o) hp_le_o),
            Nat.mod_eq_of_lt (by omega)]
        have hpf_ge2 : (2#64 : BitVec 64).toNat ≤ p_f_v.toNat := by
          change 2 ≤ p_f_v.toNat; omega
        have h2_64 : (2#64 : BitVec 64).toNat = 2 := rfl
        have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
        have hpv_sub2 : ((p_f_v - 2#64).toNat + 2) = p_f_v.toNat := by
          rw [m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
        have hpf_back : (p_f_v - 2#64) + 1#64 + 1#64 = p_f_v := by
          apply BitVec.eq_of_toNat_eq
          have h1 : (p_f_v - 2#64).toNat + 1 < 2 ^ 64 := by
            rw [m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
          rw [BitVec.toNat_add, BitVec.toNat_add, m7_bv64_sub_toNat hpf_ge2, h2_64, h1_64,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hpf_back_nat : ((p_f_v - 2#64) + 1#64 + 1#64).toNat = (p_f_v - 2#64).toNat + 2 := by
          rw [hpf_back, m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
        have hpi_f' : PropLitInv c F0 F_cur s_pi_p sem_f not_lit.toNat off_f_v.toNat
            q_f_v.toNat ((p_f_v - 2#64).toNat + 2) end_f_v.toNat := by
          rw [hoff_fv_n, hqf_n, hendf_n, hpv_sub2, hpf_n]
          exact hpi_f
        have hq_le_pf : q_f_v.toNat ≤ (p_f_v - 2#64).toNat := by
          rw [m7_bv64_sub_toNat hpf_ge2, h2_64, hqf_n, hpf_n]; omega
        have hsub_q : q_f_v - off_f_v = q_p - off_o := by
          dsimp only [q_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
        have hsub_p : (p_f_v - 2#64) + 1#64 + 1#64 - off_f_v = p_p - off_o := by
          rw [hpf_back]; dsimp only [p_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
        have hsub_e : end_f_v - off_f_v = end_o - off_o := by
          dsimp only [end_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
        have hoth_mask : (ovf_oth_p &&& 0x7FFFFFFF#32) = ovf_oth_p :=
          m7_bv32_mask7f_eq (by omega)
        have hcr_ref_f : ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_f.core :=
          hperm_f.1 ▸ (hpi_p.perm.1 ▸ hcr_ref)
        have hcsz_fp :
            fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat =
              fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat :=
          (hperm_f.2 ovf_cr_p.toNat (hpi_p.perm.1 ▸ hcr_ref)).1.trans
            (hpi_p.perm.2 ovf_cr_p.toNat (hpi_p.perm.1 ▸ hcr_ref)).1.symm
        have hcr_fit_f : ovf_cr_p.toNat + 3 +
            fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat ≤ sem_f.core.arena_len := by
          rw [halen_f, hcsz_fp]; exact hcr_fit
        have hri_lt_f : ovf_ri_p.toNat < fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat := by
          rw [hcsz_fp]; exact hri_lt
        have har3_f : sem_f.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p := by
          rw [har_f]; exact har3
        have har4_f : sem_f.core.arena[ovf_cr_p.toNat + 4]? = some not_lit := by
          rw [har_f]; exact har4
        have har_ri_f : sem_f.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p := by
          rw [har_f]; exact har_ri
        have hwvc4 := hlen4.core_ok.wvec_len
        have hoff4_lt_wv : 2 * not_lit.toNat < st4.core.wvec.length := by
          rw [hwvc4]; omega
        have hoff4_lt_m : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
            (fastPropMem s_disk st4).core.wvec.length := by
          rw [fastPropMem_wvec, hnl64_idx]; exact hoff4_lt_wv
        have h2n_lt64 : 2 * not_lit.toNat < 2 ^ 64 := by omega
        have hoff4_mod : 2 * not_lit.toNat % 2 ^ 64 = 2 * not_lit.toNat :=
          Nat.mod_eq_of_lt h2n_lt64
        have hmem_wvec_get : ∀ {i : Nat} (hi : i = 2 * not_lit.toNat)
            (pf : i < (fastPropMem s_disk st4).core.wvec.length),
            ((fastPropMem s_disk st4).core.wvec[i]'pf).setWidth 64 =
            (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 := by
          intro i hi pf
          have hg : (fastPropMem s_disk st4).core.wvec[i]? =
              st4.core.wvec[2 * not_lit.toNat]? := by rw [fastPropMem_wvec, hi]
          rw [List.getElem?_eq_getElem pf, List.getElem?_eq_getElem hoff4_lt_wv,
            Option.some.injEq] at hg
          exact congrArg (BitVec.setWidth 64) hg
        have hsc4_pi : st4.scratch = { s_pi_p.scratch with
            search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
            phases := st4.scratch.phases } := hsc4
        fid_hsteps_nogrp
        refine wp_join_group (fun ((off_n, p_n, q_n, end_n, ()) :
            Tup Val [i64, i64, i64, i64]) mj =>
            mj = m4 ∧
            off_n = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 ∧
            q_n = off_n + (q_p - off_o) ∧
            p_n = off_n + (p_p - off_o) ∧
            end_n = off_n + (end_o - off_o)) ?_ ?_
        · rintro _ ⟨off_n, p_n, q_n, end_n, ⟨⟩⟩ mj ⟨rfl, hoff_n_def, hqn_d, hpn_d, hen_d⟩
          have hoff_n_eq : off_n = BitVec.setWidth 64
              (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
            rw [hoff_n_def, List.getElem?_eq_getElem hoff4_lt_wv, Option.getD_some]
          have hqn_d' : q_n = off_n + (q_f_v - off_f_v) := by rw [hqn_d, hsub_q]
          have hpn_d' : p_n = off_n + ((p_f_v - 2#64) + 1#64 + 1#64 - off_f_v) := by
            rw [hpn_d, hsub_p]
          have hen_d' : end_n = off_n + (end_f_v - off_f_v) := by rw [hen_d, hsub_e]
          clear hoff_n_def hqn_d hpn_d hen_d
          subst hqn_d' hen_d' hpn_d' hoff_n_eq
          fid_hsplit
          · have hpok_t : pk = true := hc
            have hok := m7_ovf_ok_step hpi_f' hlen4 hcv4 hnot_f hlay4 hperm24 hnw4
              hag4 htr4 hsc4_pi hnot_f4 har4_eq hcr_fit_f hal4 har3_f har4_f hri2 hri_lt_f
              har_ri_f (hcv_f.symm ▸ hovf_lt) hovf_ne hcr_lt hcr_ref_f hpf_back_nat hq_le_pf
              hoth_mask hoth_pr (hpok_t_pr hpok_t)
            have hcr_u64 : ovf_cr_p.toNat + 3 +
                fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat < 2 ^ 64 := by
              have := hpi_p.len.core_ok.arena_len_le
              exact Nat.lt_of_le_of_lt (Nat.le_trans hcr_fit this) (Nat.lt_trans har (by decide))
            have har_m4 : (fastPropMem s_disk st4).core.arena.length =
                sem_p.core.arena.length := by
              rw [fastPropMem_arena, har4_eq, har_f]
            have h3_idx : (BitVec.setWidth 64 ovf_cr_p + 3).toNat = ovf_cr_p.toNat + 3 := by
              rw [BitVec.toNat_add, bv_c0_zext32_64, show (3 : BitVec 64).toNat = 3 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have h31_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat =
                ovf_cr_p.toNat + 4 := by
              rw [BitVec.toNat_add, h3_idx, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have hri_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat =
                ovf_cr_p.toNat + 3 + ovf_ri_p.toNat := by
              rw [BitVec.toNat_add, h3_idx, Nat.mod_eq_of_lt (by omega)]
            have har3_m : (BitVec.setWidth 64 ovf_cr_p + 3).toNat <
                (fastPropMem s_disk st4).core.arena.length := by
              rw [h3_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har3).1
            have har31_m : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat <
                (fastPropMem s_disk st4).core.arena.length := by
              rw [h31_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har4).1
            have har_ri_m : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat <
                (fastPropMem s_disk st4).core.arena.length := by
              rw [hri_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har_ri).1
            have har4_pf : st4.core.arena = sem_p.core.arena := har4_eq.trans har_f
            fid_hsteps
            let sem_n : FullState :=
              { st4 with core := { st4.core with
                arena := ((st4.core.arena.set (ovf_cr_p.toNat + 3) ovf_oth_p).set
                  (ovf_cr_p.toNat + 4) ovf_rw_p).set (ovf_cr_p.toNat + 3 + ovf_ri_p.toNat)
                  not_lit } }
            have hdel_sn : sem_n.scratch.delayed = sem_p.scratch.delayed := hdel4
            have hpi_n := hok.2.2.2.2.2
            exact ih_o _ (te_p, un_p, uf_p, tk_p, _, _, _, _, 0#64, 0#64, true, ()) _
              (by
                simp only [↓reduceIte]
                rw [hok.2.2.2.2.1, hpv_sub2, hpf_n, hendf_n]
                have := hpi_p.sw.q_ge; have := hpi_p.sw.q_le_p; have := hpi_p.sw.p_le_end
                omega)
              ⟨sem_n, 0, rfl, by simpa only [sem_n, s_pi_p, hdel4, har4_pf] using hpi_n,
                rfl, Nat.zero_le _,
                fun _ hj => absurd hj (Nat.not_lt_zero _),
                fun h0 => hdel_sn.trans (hd0_p h0),
                hte_p.trans hte4.symm, hun_p.trans hun4.symm, huf_p.trans huf4.symm,
                ht0_p.imp_right (fun h => hte4 ▸ h),
                fun _ => ⟨rfl, hoom4.trans hoom_p, hct4.trans (hct_p.trans hct_o2)⟩,
                fun h => absurd h (by decide),
                by
                  simpa only [sem_n, fastPropMem_arena, fastPropMem_with_arena,
                    h3_idx, h31_idx, hri_idx] using hm⟩
          · have hpok_f : pk = false := hc
            have hfail := m7_ovf_fail_step hpi_f' hlen4 hcv4 hnot_f hlay4 hperm24 hnw4
              hag4 htr4 hsc4_pi hnot_f4 (hcv_f.symm ▸ hovf_lt) hovf_ne hcr_lt hcr_ref_f
              hpf_back_nat hq_le_pf hoth_mask hoth_pr (hpok_f_pr hpok_f)
            let wv_n0 := (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64
            have hq_wlen : (wv_n0 + (q_f_v - off_f_v)).toNat <
                (fastPropMem s_disk st4).core.wstk.length := by
              rw [fastPropMem_wstk]; exact hfail.1
            have hq1_wlen : (wv_n0 + (q_f_v - off_f_v) + 1#64).toNat <
                (fastPropMem s_disk st4).core.wstk.length := by
              rw [fastPropMem_wstk, hfail.2.2.1]; exact hfail.2.1
            refine fc_let_mul rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            refine wp_store_sep (FullArenaTactics.c0_store_full_wstk ovf_oth_p
              (by dsimp only [Arg.val]; exact hq_wlen) hmo') ?_
            intro m5a hm5a; clear hmo'; dsimp only [Arg.val] at hm5a
            rw [fastPropMem_wstk, fastPropMem_with_wstk] at hm5a
            refine fc_let_add rfl rfl ?_
            refine fc_let_mul rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            let st4a : FullState := { st4 with core := { st4.core with
              wstk := st4.core.wstk.set (wv_n0 + (q_f_v - off_f_v)).toNat ovf_oth_p } }
            have hq1_wlen_a : (wv_n0 + (q_f_v - off_f_v) + 1#64).toNat <
                (fastPropMem s_disk st4a).core.wstk.length := by
              rw [fastPropMem_wstk, List.length_set, ← fastPropMem_wstk]; exact hq1_wlen
            refine wp_store_sep (FullArenaTactics.c0_store_full_wstk ovf_cr_p
              (by dsimp only [Arg.val]; exact hq1_wlen_a) hm5a) ?_
            intro m_fin hm_fin; clear hm5a; dsimp only [Arg.val] at hm_fin
            refine fc_let_add rfl rfl ?_
            refine fc_wp_jump_head ?_
            dsimp only [vals, Arg.val]
            let st5 : FullState :=
              { st4 with core := { st4.core with
                wstk := (st4.core.wstk.set
                  (wv_n0 + (q_f_v - off_f_v)).toNat ovf_oth_p).set
                  ((wv_n0 + (q_f_v - off_f_v)).toNat + 1) ovf_cr_p } }
            have hdel5 : st5.scratch.delayed = sem_p.scratch.delayed := hdel4
            refine hBo _ _ ⟨st5, 0,
              by
                dsimp only [st5, s_pi_p] at hfail ⊢
                rw [hdel5]
                exact hfail.2.2.2.2.2.2.2,
              rfl, Nat.zero_le _, fun _ hj => absurd hj (Nat.not_lt_zero _),
              fun h0 => hdel5.trans (hd0_p h0),
              hte_p.trans hte4.symm, hun_p.trans hun4.symm, huf_p.trans huf4.symm,
              ht0_p.imp_right (fun h => hte4 ▸ h),
              fun h => absurd h (by decide), fun h => absurd h (by decide), Or.inr (Or.inr rfl),
              by
                have h1_idx : (BitVec.setWidth 64
                    (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
                    (q_f_v - off_f_v) + 1).toNat =
                    (wv_n0 + (q_f_v - off_f_v)).toNat + 1 := hfail.2.2.1
                rw [fastPropMem_wstk, fastPropMem_with_wstk, h1_idx] at hm_fin
                exact hm_fin⟩
        · intro Jn hJn
          fid_hsplit
          · fid_hsteps
            have hnoff := hmem_wvec_get hnl64_idx hoff4_lt_m
            exact hJn _ m4 ⟨rfl, hnoff, rfl, rfl, rfl⟩
          · fid_hsteps
            have hnoff_eq := hmem_wvec_get hoff4_mod
              (by rw [hoff4_mod, fastPropMem_wvec]; exact hoff4_lt_wv)
            have hoff_eq :
                off_o = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 :=
              hc.symm.trans hnoff_eq
            have had_sub : ∀ {x : BitVec 64}, off_o.toNat ≤ x.toNat →
                x.toNat < 2 ^ 64 → x = off_o + (x - off_o) := by
              intro x hle hlt
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, m7_bv64_sub_toNat hle, Nat.mod_eq_of_lt (by omega)]
              omega
            have hend_lt : end_o.toNat < 2 ^ 64 :=
              Nat.lt_of_le_of_lt
                (Nat.le_trans (hpi_p.end_lt_wcap hnot_lt).1 (hpi_p.end_lt_wcap hnot_lt).2)
                (Nat.lt_trans hwc (by decide))
            have hq_ge := hpi_p.sw.q_ge
            have hq_le := hpi_p.sw.q_le_p
            have hp_le := hpi_p.sw.p_le_end
            exact hJn _ m4 ⟨rfl, hoff_eq,
              had_sub hq_ge (by omega),
              had_sub (Nat.le_trans hq_ge hq_le) (by omega),
              had_sub (Nat.le_trans hq_ge (Nat.le_trans hq_le hp_le)) hend_lt⟩
      · intro Jp hJp
        have hnot_f : not_lit.toNat < 2 * sem_f.core.cur_vars := hcv_f.symm ▸ hnot_lt
        have hsw_f' := hsw_f
        fid_hsplit
        · have hfok_t : fok = true := hc
          have hlay_mf : WatchStackLayout (fastPropMem s_disk sem_f).core :=
            fastPropMem_watchLayout hlay_f rfl
          have hlen_mf : (fastPropMem s_disk sem_f).LengthsOk c :=
            fastPropMem_lengthsOk hsd_len hlen_f
              (by rw [hsd_cv, hcv_f])
              (by rw [hsd_pr_b, hag_f.get FullCoreState.propagated]) rfl
          c0_call hOvf
          refine ⟨c, fastPropMem s_disk sem_f, R, rfl, hlen_mf, hlay_mf,
            fun h => absurd h (by decide),
            fun _ => ⟨by
                intro h; rw [h] at hoth_lt
                have h42 : (4294967295#32 : BitVec 32).toNat = 4294967295 := rfl
                rw [h42] at hoth_lt; omega,
              by intro h; rw [h] at hcr_lt; revert hcr_lt; decide⟩,
            hmf,
            fun pok wv' ws' wl' wu' wsrt' mo' hlen' hlay' hoth_pr hnew_pr hfail_pr hmo' => ?_⟩
          let st4 : FullState :=
            { sem_f with
              core := { sem_f.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
              scratch := { sem_f.scratch with wsort := wsrt' } }
          have hlen4 : st4.LengthsOk c := by
            simp only [fastPropMem_def] at hlen'
            have hso := hlen'.scratch_ok
            have hscr4 : st4.scratch.LengthsOk c :=
              ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8,
               hso.9, hso.10, hso.11, hso.12, hso.13, hso.14, hso.15, hso.16,
               hso.17, hso.18, hso.19, hso.20, hso.21, hso.22, hso.23, hso.24⟩
            exact ⟨{ hlen'.core_ok with
                trail_end_le := hlen_f.core_ok.trail_end_le
                propagated_le := hlen_f.core_ok.propagated_le }, hscr4⟩
          have hlay4 : WatchStackLayout st4.core := by
            simp only [fastPropMem_def] at hlay'
            exact { bounds := hlay'.bounds, pos_off := hlay'.pos_off,
                    disjoint := hlay'.disjoint, no_sentinel := hlay'.no_sentinel }
          have hperm24 : FullPropDecSpecs.FullArenaPermEq sem_f.core st4.core :=
            ⟨rfl, fun r _ => ⟨rfl, rfl, .refl _⟩⟩
          have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
            fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw_f rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hag4 : AgreesExcept propLitCoreMask s_base.core st4.core :=
            hag_f.update (fun k =>
              { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
          have htr4 : FullPropDecSpecs.FullTrailExt s_base.core st4.core :=
            ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩
          have hsc4 : st4.scratch = { s_pi_p.scratch with
              search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
              phases := st4.scratch.phases } := by
            dsimp only [st4]; rw [hsc_f]
          have hmo4 : (FullMem c (fastPropMem s_disk st4) ⋆ R) mo' := by
            simpa only [st4, fastPropMem_def] using hmo'
          exact hJp (pok, ()) mo' ⟨st4, hlen4, hlay4, hnw4, hag4, htr4, hperm24,
            rfl, rfl, rfl, rfl, hte_f, hun_f, huf_f,
            hoom_f, hct_f, hsc4, hdel_f,
            fun l hl hne => by
              have h := hoth_pr l (by simpa only [fastPropMem_def] using hl) hne
              simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
                fullWatchOff, fullWatchOffCore] at h
              simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h,
            fun ht => by
              have h := (hnew_pr ht).2.2
              simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
                fullWatchOff, fullWatchOffCore] at h
              simpa only [st4, fullWatchSizeCore, fullWatchOffCore,
                m7_bv32_mask7f_eq (by omega : ovf_oth_p.toNat < 2 ^ 31)] using
                ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 rfl⟩,
            fun hf => by
              have h := (hfail_pr hf).1
                (by simpa only [fastPropMem_def, hcv_f] using hovf_lt)
              simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
                fullWatchOff, fullWatchOffCore] at h
              simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h,
            hmo4⟩
        · have hfok_f : fok = false := by revert hc; cases fok <;> simp
          fid_hsteps
          exact hJp (false, ()) mf ⟨sem_f, hlen_f, hlay_f, hnw_f, hag_f, htr_f,
            .refl _, rfl, rfl, rfl, rfl, hte_f,
            hun_f, huf_f, hoom_f, hct_f, hsc_f, hdel_f,
            fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩,
            fun h => absurd h (by decide),
            fun _ => ⟨rfl, fun _ _ => rfl⟩,
            hmf⟩
    · intro Jf hJf
      have hlay_p : WatchStackLayout sem_p.core := hpi_p.sw.layout
      fid_hsplit
      · have hdi_pos : 0 < di_p.toNat := hc
        have hlay_mp : WatchStackLayout (fastPropMem s_disk sem_p).core :=
          fastPropMem_watchLayout hlay_p rfl
        have hlen_mp : (fastPropMem s_disk sem_p).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hpi_p.len hsd_cv.symm hsd_pr.symm rfl
        have hdok_mp : DelayedWatchesOk (fastPropMem s_disk sem_p).core
            (fastPropMem s_disk sem_p).scratch.delayed dlen_p not_lit.toNat := by
          rw [fastPropMem_delayed]
          exact delayedWatchesOk_congr (k1 := s_base.core)
            (by rw [fastPropMem_def, hpi_p.cur_vars_eq])
            (by rw [fastPropMem_def]; exact hpi_p.perm.1) hdok_p
        c0_call hFlush
        refine ⟨c, F_cur, fastPropMem s_disk sem_p, R, dlen_p, not_lit.toNat, rfl, hlen_mp,
          hlay_mp, hdi_p, hdlen_p, hdok_mp, hmbp,
          fun fok wv' ws' wl' wu' wsrt' mf1 hlen' hlay' _hwat' hsw' hmf1 => ?_⟩
        let sem_f : FullState :=
          { sem_p with
            core := { sem_p.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
            scratch := { sem_p.scratch with wsort := wsrt' } }
        have hlen_f : sem_f.LengthsOk c := by
          simp only [fastPropMem_def] at hlen'
          have hso := hlen'.scratch_ok
          have hscr4 : sem_f.scratch.LengthsOk c :=
            ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8,
             hso.9, hso.10, hso.11, hso.12, hso.13, hso.14, hso.15, hso.16,
             hso.17, hso.18, hso.19, hso.20, hso.21, hso.22, hso.23, hso.24⟩
          exact ⟨{ hlen'.core_ok with
              trail_end_le := hpi_p.len.core_ok.trail_end_le
              propagated_le := hpi_p.len.core_ok.propagated_le }, hscr4⟩
        have hlay_f : WatchStackLayout sem_f.core := by
          simp only [fastPropMem_def] at hlay'
          exact { bounds := hlay'.bounds, pos_off := hlay'.pos_off,
                  disjoint := hlay'.disjoint, no_sentinel := hlay'.no_sentinel }
        have hsw_mp : SplitWatchesInv F_cur (fastPropMem s_disk sem_p).core not_lit.toNat
            off_o.toNat q_p.toNat p_p.toNat end_o.toNat :=
          hpi_p.sw.with_nonwatch (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hsw_f_raw := hsw' (by rw [fastPropMem_def]; exact hnot_lt)
          off_o.toNat q_p.toNat p_p.toNat end_o.toNat hsw_mp
        have hsw_f : SplitWatchesInv F_cur sem_f.core not_lit.toNat
            (fullWatchOffCore sem_f.core not_lit.toNat)
            (fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat)) := by
          have hoff_eq : fullWatchOffCore sem_f.core not_lit.toNat =
              fullWatchOffCore { (fastPropMem s_disk sem_p).core with
                wvec := wv', wstk := ws', wlen := wl', wusable := wu' } not_lit.toNat := by
            unfold fullWatchOffCore; rfl
          rw [hoff_eq]
          exact hsw_f_raw.with_nonwatch (by rw [fastPropMem_def]) rfl rfl rfl
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hnw_f : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem_f.core) :=
          fullWitnessInv_nw_congr hlen_f.core_ok.cur_vars_le hpi_p.nw
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hag_f : AgreesExcept propLitCoreMask s_base.core sem_f.core :=
          hpi_p.ag.update (fun k =>
            { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
        have htr_f : FullPropDecSpecs.FullTrailExt s_base.core sem_f.core :=
          ⟨hpi_p.tr.te_ge, hpi_p.tr.trl_pref, hpi_p.tr.lvl_pres⟩
        have hsc_f : sem_f.scratch = { s_pi_p.scratch with
            search_ticks := sem_f.scratch.search_ticks, wsort := sem_f.scratch.wsort,
            phases := sem_f.scratch.phases } := by
          dsimp only [sem_f]; rw [hpi_p.sc_eq]
        have hmf1' : (FullMem c (fastPropMem s_disk sem_f) ⋆ R) mf1 := by
          simpa only [sem_f, fastPropMem_def] using hmf1
        exact hJf (0#64, fok, ()) mf1 ⟨sem_f, rfl, hlen_f, hlay_f, hnw_f, hag_f, htr_f,
          hpi_p.perm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsc_f, rfl, hsw_f, hmf1'⟩
      · have hdi0 : di_p = 0#64 := BitVec.eq_of_toNat_eq (by
          have hc' : ¬ (0 : BitVec 64).toNat < di_p.toNat := hc
          rw [show (0 : BitVec 64).toNat = 0 from rfl] at hc'
          show di_p.toNat = (0#64).toNat
          rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; omega)
        have hoff_o_eq : fullWatchOffCore sem_p.core not_lit.toNat = off_o.toNat :=
          hpi_p.sw.off_eq
        have hsw_p' : SplitWatchesInv F_cur sem_p.core not_lit.toNat
            (fullWatchOffCore sem_p.core not_lit.toNat)
            (fullWatchOffCore sem_p.core not_lit.toNat + (q_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_p.core not_lit.toNat + (p_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_p.core not_lit.toNat + (end_o.toNat - off_o.toNat)) := by
          rw [hoff_o_eq]
          have hq_ge := hpi_p.sw.q_ge
          have hq_le := hpi_p.sw.q_le_p
          have hp_le := hpi_p.sw.p_le_end
          rw [Nat.add_sub_cancel' hq_ge, Nat.add_sub_cancel' (Nat.le_trans hq_ge hq_le),
            Nat.add_sub_cancel' (Nat.le_trans (Nat.le_trans hq_ge hq_le) hp_le)]
          exact hpi_p.sw
        fid_hsteps
        rw [hdi0]
        exact hJf (0#64, true, ()) mbp ⟨sem_p, rfl, hpi_p.len, hlay_p, hpi_p.nw, hpi_p.ag,
          ⟨hpi_p.tr.te_ge, hpi_p.tr.trl_pref, hpi_p.tr.lvl_pres⟩, hpi_p.perm,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpi_p.sc_eq, rfl, hsw_p', hmbp⟩
  · have hovf_false : ovf_p = false := hc
    subst hovf_false
    have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
    fid_hsteps
    exact ih_o _ (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, di_p, brk_p, false, ()) mbp
      (by simp only [Bool.false_eq_true, ↓reduceIte]; have := _hpo_le_pp; omega)
      ⟨sem_p, dlen_p, rfl, hpi_p, hdi_p, hdlen_p, hdok_p, hd0_p, hte_p, hun_p, huf_p, ht0_p,
        fun h => absurd h (by decide),
        fun _ => ⟨fun h0 => ⟨hoom_p, (hbrk0_fn h0).2.trans hct_o2, (hbrk0_fn h0).1⟩,
          fun h1 => ⟨hbrk1_fn h1, hoom_p⟩, by rcases hbrk_disj with rfl | rfl <;> simp⟩,
        hmbp⟩

/-! ## 3. Outer Propagation Loop \& Headline Theorem (`full_propagate_ignore_fid_wp`) -/

private def FidOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (rem : Nat)
    (prop_v tend_v fuel_v unass_v unfl_v _ticks_v : BitVec 64) (m : Mem 64) : Prop :=
  ∃ (sem : FullState) (te_mem : Nat),
    rem = sem.core.fuel.toNat ∧
    sem.LengthsOk c ∧
    FullWitnessInv c F0 F_cur sem.core ∧
    FullPropDecSpecs.FullTrailExt s.core sem.core ∧
    FullPropDecSpecs.FullArenaPermEq s.core sem.core ∧
    AgreesExcept fidCoreMask s.core sem.core ∧
    sem.core.propagated = prop_v.toNat ∧
    sem.core.trail_end = tend_v.toNat ∧
    sem.core.fuel = fuel_v ∧
    sem.core.unassigned = unass_v ∧
    sem.core.unflushed = unfl_v ∧
    sem.core.oom = 0#64 ∧
    sem.core.confl_type = s.core.confl_type ∧
    sem.core.dense_mode = 0#64 ∧
    sem.core.cur_vars = s.core.cur_vars ∧
    sem.core.cur_level = s.core.cur_level ∧
    sem.core.probing = s.core.probing ∧
    sem.core.arena_len = s.core.arena_len ∧
    sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
    s.core.propagated ≤ prop_v.toNat ∧
    te_mem ≤ sem.core.trail_end ∧
    s.core.propagated ≤ te_mem ∧
    FidScr s sem ∧
    (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
    (FullMem c
      (fastPropMem
        { s with core := { s.core with trail_end := te_mem } }
        { sem with
          core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R)
      m

/-- `full_propagate_ignore_fid` satisfies `FullM6BcpS15.fullPropagateIgnoreS15Spec`: delayed-watch
buffering, hoisted outer scalar fields, and delayed `h->fuel` memory writeback. -/
theorem full_propagate_ignore_fid_wp (Γ : Env)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hChrono : ∀ args m Q X, FullM7BcpHot.fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec args m Q X →
      Func.wp Γ full_propagate_ignore_fid_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  have hQ_fid : FidHQ c F0 F_cur s ignore_ref R Q := by
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen'
      wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
      hlen' hw' htr' hperm' hd0' hfl' hr hr0 hr1 hr2 hnoop hm'
    exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen'
      wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' ⟨htr'.te_ge, htr'.trl_pref, htr'.lvl_pres⟩ ⟨rfl, hperm'⟩ hd0' hfl'
      hr hr0 hr1 hr2 hnoop hm'
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have har := c.harena; unfold dimacsBound at har
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hdelc := c.hdel; unfold dimacsBound at hdelc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have h2cv_lt31 : 2 * s.core.cur_vars < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.trail_end_le hcv_lt64
  have hpr0_lt64 : s.core.propagated < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.propagated_le hte0_lt64
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hclv_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
  have hal0_lt64 : s.core.arena_len < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.arena_len_le (Nat.lt_trans har (by decide))
  have hdelc_lt64 : c.delayed_cap < 2 ^ 64 := Nat.lt_trans hdelc (by decide)
  have hdlim_toNat : (BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap := by
    rw [BitVec.toNat_mul, m7_bv64_ofNat_toNat_lt hdelc_lt64,
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold Func.wp full_propagate_ignore_fid_body
  fid_hsplit
  · have hge : s.core.trail_end ≤ s.core.propagated := by
      have hh : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64] at hh
    have hpe : s.core.propagated = s.core.trail_end :=
      Nat.le_antisymm hlen0.core_ok.propagated_le hge
    exact fid_exit_hQ c F0 F_cur s ignore_ref R Q hQ_fid 0#64 s m (.refl _ _) rfl hlen0 hw0
      (.refl _) (.refl _) (fun _ => rfl) (Nat.le_refl _) (Or.inl rfl)
      (fun _ => ⟨hpe, rfl, fun h => h,
        fun hlt => absurd hlt (Nat.not_lt_of_ge (Nat.le_of_eq hpe.symm))⟩)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl⟩) hm0
  · have hpr_lt : s.core.propagated < s.core.trail_end := by
      have hh : ¬ s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64, Nat.not_le] at hh
    fid_hsplit
    · exact fid_exit_hQ c F0 F_cur s ignore_ref R Q hQ_fid 2#64 s m (.refl _ _) rfl hlen0 hw0
        (.refl _) (.refl _) (fun _ => rfl) (Nat.le_refl _) (Or.inr (Or.inr rfl))
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => Or.inl hc) (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm0
    · have hoom0 : s.core.oom = 0#64 := hc
      fid_hsteps_nogrp
      refine wp_loop_group
        (fun rem (prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ()) ml =>
          FidOuterInv c F0 F_cur s R rem prop_v tend_v fuel_v unass_v unfl_v ticks_v ml) ?_ ?_
      · rintro J rem ⟨prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ⟨⟩⟩ ml ih
          ⟨sem, te_mem, rfl, hlen_o, hw_o, htr_o, hperm_o, hag_o, hprop_eq, htend_eq,
           hfuel_eq, hunass_eq, hunfl_eq, hoom_o, hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
           hfuel_le, hfuel_lt, hpr_ge, htem_le, hpr_tem, hsc_o, hd0_sem, hml⟩
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let sem_d : FullState :=
          { sem with core :=
            { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
        have hsd_len : s_disk.LengthsOk c :=
          ⟨{ hlen0.core_ok with
              trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
              propagated_le := hpr_tem },
           hlen0.scratch_ok⟩
        have hsemd_len : sem_d.LengthsOk c :=
          ⟨{ hlen_o.core_ok with
              propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
           hlen_o.scratch_ok⟩
        have hmem_len : (fastPropMem s_disk sem_d).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hsemd_len (by simp [s_disk, sem_d, hcv_o]) rfl rfl
        have hte_lt64 : sem.core.trail_end < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.trail_end_le (hcv_o ▸ hcv_lt64)
        have hpr_o_lt64 : sem.core.propagated < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.propagated_le hte_lt64
        fid_hsplit
        · have hp_lt_o : prop_v.toNat < tend_v.toNat := hc
          have hp_lt_sem : sem.core.propagated < sem.core.trail_end := by
            rw [hprop_eq, htend_eq]; exact hp_lt_o
          fid_hsplit
          · have hfl0 : sem.core.fuel = 0#64 := hfuel_eq.trans hc
            clear ih
            fid_hsteps
            exact fid_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
              hQ_fid hlen_o hw_o htr_o hperm_o hag_o hsc_o hd0_sem
              hprop_eq htend_eq hfl0 hunass_eq hunfl_eq hfuel_le hpr_lt
              (Or.inr (Or.inr rfl)) (fun h => absurd h (by decide)) (by decide)
              (fun _ => Or.inr hfl0)
              (by
                simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                  hunass_eq, hunfl_eq, hfl0, BitVec.ofNat_eq_ofNat] using hm)
          · have hfl_ne : sem.core.fuel ≠ 0#64 := fun h => hc (hfuel_eq ▸ h)
            have hfl_pos : 0 < sem.core.fuel.toNat := by
              by_cases h0 : sem.core.fuel.toNat = 0
              · exact absurd (BitVec.eq_of_toNat_eq h0) hfl_ne
              · omega
            have hfl_dec : (sem.core.fuel - 1#64).toNat = sem.core.fuel.toNat - 1 :=
              m7_bv64_sub_toNat (by simp; omega)
            have hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by omega
            have hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length := by
              rw [fastPropMem_trl, hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            let lit := (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl
            have hlit_eq : lit = sem.core.trl[sem.core.propagated]'(by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega) := by
              simp only [lit, fc_getElem_trl]
              exact (fc_getElem_eq_of_idx hprop_eq _ _).symm
            have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
              have := hw_o.trail_lits_lt sem.core.propagated hp_lt_sem
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              rwa [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq] at this
            let not_lit := lit ^^^ 1#32
            have hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars := by
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [fc_nat_xor_one]; split <;> omega
            have hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              refine (hw_o.vals_false_iff not_lit.toNat hnot_lt).mpr
                ⟨sem.core.propagated, hp_lt_sem, ?_⟩
              rw [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq]
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rcases Nat.mod_two_eq_zero_or_one lit.toNat with h | h
              · have h2 : (lit.toNat + 1) % 2 = 1 := by omega
                simp only [fc_nat_xor_one, h, ↓reduceIte, h2, Nat.one_ne_zero]; omega
              · have h2 : (lit.toNat - 1) % 2 = 0 := by omega
                simp only [fc_nat_xor_one, h, Nat.one_ne_zero, ↓reduceIte, h2]; omega
            have hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
              m7_bv64_shl1_u32_nat not_lit
            have hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                2 * not_lit.toNat + 1 := m7_bv64_shl1_add1_nat not_lit
            have hwv_o_len := hlen_o.core_ok.wvec_len
            have hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
              m7_bv64_add1_toNat (by have := hte_lt64; omega)
            have hnl64_lt_wv0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_1_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_lt_wv : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_lt_wv0
            have hnl64_1_lt_wv : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_1_lt_wv0
            have h_wvec_len_mem : (fastPropMem s_disk sem_d).core.wvec.length =
                4 * c.max_vars := by
              rw [fastPropMem_wvec, hwv_o_len]
            have hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length := by
              rw [hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            have hsz_hc_idx :
                ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                  (2 * ((sem.core.trl[prop_v.toNat]'hp_sem_lt_trl).toNat ^^^ 1) + 1) %
                    2 ^ 64 := by
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                simp only [lit, fc_getElem_trl, sem_d]
              have hnot_toNat : not_lit.toNat = lit.toNat ^^^ 1 := by
                dsimp only [not_lit]; rw [BitVec.toNat_xor]
                simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [hnl64_1_idx, hlit_trl, ← hnot_toNat,
                Nat.mod_eq_of_lt (by have := hlen_o.core_ok.cur_vars_le; omega)]
            fid_hsplit
            · have hsz0 : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 = 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              fid_hsteps
              let sem_n : FullState :=
                { sem with
                  core :=
                    { sem.core with
                      propagated := prop_v.toNat + 1
                      fuel := sem.core.fuel - 1#64 } }
              have hlen_n : sem_n.LengthsOk c :=
                ⟨{ hlen_o.core_ok with propagated_le := by rw [htend_eq]; exact hp_lt_o },
                 hlen_o.scratch_ok⟩
              have hwat_n : WatchesInv F_cur sem_n.core := by
                have hw_sp : ModeWatchesInv F_cur sem_n.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_n : sem_n.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_n, ↓reduceIte] using hw_sp
              have hw_n : FullWitnessInv c F0 F_cur sem_n.core :=
                fullWitnessInv_of_nw
                  (fullWitnessInv_nw_congr hlen_n.core_ok.cur_vars_le
                    (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl)
                  (show sem_n.core.dense_mode = 0#64 from hdm_o) hwat_n
              exact ih (sem_n.core.fuel.toNat)
                (prop_v + 1#64, tend_v, fuel_v - 1#64, unass_v, unfl_v, ticks_v, ()) ml
                hfl_rem_dec
                ⟨sem_n, te_mem, rfl, hlen_n, hw_n,
                  ⟨htr_o.te_ge, htr_o.trl_pref, htr_o.lvl_pres⟩,
                  hperm_o, fid_agrees_upd_prop_fuel hag_o, by simp [sem_n, hp1_prop], htend_eq,
                  by simp [sem_n, hfuel_eq], hunass_eq, hunfl_eq, hoom_o,
                  hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
                  Nat.le_trans (Nat.le_of_lt hfl_rem_dec) hfuel_le,
                  fun _ => Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le,
                  by rw [hp1_prop]; omega, htem_le, hpr_tem, hsc_o, hd0_sem, hml⟩
            · have hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              let s_base : FullState :=
                { sem with core := { sem.core with
                  propagated := s.core.propagated, fuel := s.core.fuel } }
              have hbase_len : s_base.LengthsOk c :=
                ⟨{ hlen_o.core_ok with
                    propagated_le :=
                      Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
                 hlen_o.scratch_ok⟩
              have hbase_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s_base.core) :=
                fullWitnessInv_nw_congr hbase_len.core_ok.cur_vars_le
                  (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl
              have hwat_base : WatchesInv F_cur s_base.core := by
                have hw_sp : ModeWatchesInv F_cur s_base.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_b : s_base.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_b, ↓reduceIte] using hw_sp
              have hoff0_nat : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                  hnl64_lt_wv0).setWidth 64).toNat =
                  fullWatchOffCore s_base.core not_lit.toNat := by
                unfold fullWatchOffCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_idx _)
              have hsz0_nat : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
                  fullWatchSizeCore s_base.core not_lit.toNat := by
                unfold fullWatchSizeCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_1_idx _)
              have hsz0_pos : 0 < fullWatchSizeCore s_base.core not_lit.toNat := by
                rw [← hsz0_nat]
                by_cases h0 : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                    1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat = 0
                · exact absurd (BitVec.eq_of_toNat_eq h0) hsz_ne
                · omega
              have hpi0 : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat) :=
                { len := hbase_len, nw := hbase_nw
                  sw := SplitWatchesInv.init (hcv_o ▸ hnot_lt) hwat_base hsz0_pos
                  ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl
                  not_f := by simpa [s_base] using hnot_f0 }
              have hnl_div : (((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^
                  1#32) >>> 1#32).setWidth 64)).toNat = not_lit.toNat / 2 := by
                change ((not_lit >>> (1 : Nat)).setWidth 64).toNat = not_lit.toNat / 2
                rw [bv_c0_zext32_64, bv32_lshr_1]
              have hlvl_d_len : (fastPropMem s_disk sem_d).core.lvl.length = c.max_vars := by
                rw [fastPropMem_lvl]; exact hlen_o.core_ok.lvl_len
              have hnl_idx_lt :
                  (((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^
                    1#32) >>> 1#32).setWidth 64)).toNat <
                    (fastPropMem s_disk sem_d).core.lvl.length := by
                rw [hlvl_d_len, hnl_div]; have := hlen_o.core_ok.cur_vars_le; omega
              fid_hsteps_nogrp
              have hm_base : (FullMem c (fastPropMem s_disk s_base) ⋆ R) ml := hml
              clear hml
              refine wp_join_group (fun (t0_v, ()) mt =>
                  mt = ml ∧
                  (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem.core.trail_end))
                ?_ ?_
              · rintro _ ⟨t0_v, ⟨⟩⟩ mt ⟨rfl, ht0_bound⟩
                have hend0_lt64 : fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 := by
                  have := hpi0.end_lt_wcap hnot_lt
                  exact Nat.lt_of_le_of_lt (Nat.le_trans this.1 this.2)
                    (Nat.lt_trans hwc (by decide))
                fid_hsteps_nogrp
                refine wp_loop_break_group
                  (fun (te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, _ovf_b, ())
                      mb =>
                    ∃ (sem_b : FullState) (dlen_b : Nat),
                      PropLitInv c F0 F_cur
                        { s_base with scratch :=
                          { s_base.scratch with delayed := sem_b.scratch.delayed } }
                        sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat ∧
                      di_b.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
                      DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
                      (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
                      te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
                      uf_b = sem_b.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
                      (brk_b = 0#64 →
                        sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
                        p_b = end_b) ∧
                      (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
                        sem_b.core.oom = 0#64) ∧
                      (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
                      (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb)
                  (fun rem_o (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o, ovf_o,
                      ()) mo =>
                    ∃ (sem_o : FullState) (dlen_o : Nat),
                      rem_o = (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) ∧
                      PropLitInv c F0 F_cur
                        { s_base with scratch :=
                          { s_base.scratch with delayed := sem_o.scratch.delayed } }
                        sem_o not_lit.toNat off_o.toNat q_o.toNat p_o.toNat end_o.toNat ∧
                      di_o.toNat = 3 * dlen_o ∧ dlen_o ≤ c.delayed_cap ∧
                      DelayedWatchesOk s_base.core sem_o.scratch.delayed dlen_o not_lit.toNat ∧
                      (c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed) ∧
                      te_o.toNat = sem_o.core.trail_end ∧ un_o = sem_o.core.unassigned ∧
                      uf_o = sem_o.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o.core.trail_end) ∧
                      (ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
                        sem_o.core.confl_type = s.core.confl_type) ∧
                      (ovf_o = false →
                        (brk_o = 0#64 →
                          sem_o.core.oom = 0#64 ∧ sem_o.core.confl_type = s.core.confl_type ∧
                          p_o = end_o) ∧
                        (brk_o = 1#64 → PropLitConfl F_cur ignore_ref sem_o.core ∧
                          sem_o.core.oom = 0#64) ∧
                        (brk_o = 0#64 ∨ brk_o = 1#64)) ∧
                      (FullMem c (fastPropMem s_disk sem_o) ⋆ R) mo)
                  ?_ ?_ ?_
                · rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, ovf_b,
                      ⟨⟩⟩ mb
                    ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                      _ht0_b, hbr0, hbr1, hbr_cases, hmb⟩
                  exact fid_compact_post_wp hChrono hFlush hQ_fid
                    (fun sem_next te_mc mc0 hlen_n hw_n htr_n hperm_n hag_n hpr_n hfl_n
                      hte_n hun_n huf_n hoom_n hct_n hdm_n hcv_n hcl_n hprob_n halen_n hfl_sem_lt
                      hfl_s_lt hfl_le hpr_ge_n htemc_le hpr_temc hsc_n hd0_n hm_mc =>
                      ih sem_next.core.fuel.toNat
                        (prop_v + 1#64, te_b, fuel_v - 1#64, un_b, uf_b, tk_b, ()) mc0 hfl_sem_lt
                        ⟨sem_next, te_mc, rfl, hlen_n, hw_n, htr_n, hperm_n, hag_n, hpr_n,
                          hte_n, (by rw [hfl_n]; rfl), hun_n, huf_n, hoom_n, hct_n, hdm_n,
                          hcv_n, hcl_n, hprob_n, halen_n, hfl_le, fun _ => hfl_s_lt,
                          (hpr_n ▸ hpr_ge_n), htemc_le, hpr_temc, hsc_n, hd0_n, hm_mc⟩)
                    hwc hmaxv hlen0 hpr_lt rfl (by rw [hfuel_eq]; rfl)
                    ⟨te_mem, rfl, htem_le, hpr_tem⟩
                    htr_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hfl_rem_dec hfuel_le
                    hp1_prop (htend_eq ▸ hp_lt_o) hpr_ge rfl hnot_lt hdm_o hpi_b hdi_b hdl_b
                    hdok_b hd0_b hte_b hun_b huf_b (fun h => let x := hbr0 h; ⟨x.1, x.2.1⟩)
                    hbr1 hbr_cases hmb
                · rintro Bo Lo rem_o ⟨te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o,
                      ovf_o, ⟨⟩⟩ mo hBo ih_o
                    ⟨sem_o, dlen_o, rfl, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o, hte_o, hun_o, huf_o,
                      ht0_o, hov_t, hov_f, hmo⟩
                  fid_hsplit
                  · have hov_t_eq : ovf_o = true := hc
                    have ⟨hbr0_o, hoom_o2, hct_o2⟩ := hov_t hov_t_eq
                    clear hov_t hov_f hc
                    fid_hsteps_nogrp
                    refine wp_join_group
                      (fun (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ()) mbp =>
                        ∃ (sem_p : FullState) (dlen_p : Nat),
                          PropLitInv c F0 F_cur
                            { s_base with scratch :=
                              { s_base.scratch with delayed := sem_p.scratch.delayed } }
                            sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat ∧
                          di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
                          DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
                          (c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed) ∧
                          p_o.toNat ≤ p_p.toNat ∧ sem_o.core.trail_end ≤ sem_p.core.trail_end ∧
                          te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
                          uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
                          (ovf_p = false →
                            (brk_p = 0#64 → p_p = end_o ∧
                              sem_p.core.confl_type = sem_o.core.confl_type) ∧
                            (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
                            (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
                          (ovf_p = true →
                            brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
                            2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
                            end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
                            ovf_cr_p.toNat < 0x80000000 ∧
                            ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
                            ovf_cr_p.toNat + 3 +
                              fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
                              sem_p.core.arena_len ∧
                            ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat ≠ not_lit.toNat ∧
                            2 ≤ ovf_ri_p.toNat ∧
                            ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? =
                              some ovf_rw_p) ∧
                          (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) ?_ ?_
                    · rintro _ ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ⟨⟩⟩ mbp
                        ⟨sem_p, dlen_p, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, _hpo_le_pp, hte_ge_p,
                          hte_p, hun_p, huf_p, hoom_p, hnoov, hov_yes, hmbp⟩
                      have ht0_p :
                          t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end :=
                        ht0_o.imp_right (fun h => Nat.le_trans h hte_ge_p)
                      dsimp only [Blocks.get]
                      exact fid_post_lp_ovf_wp hOvf hFlush hBo
                        (fun n' xs m hlt => ih_o n' xs m
                          (by simpa only [hov_t_eq, ↓reduceIte] using hlt))
                        har hwc hsd_len
                        (by dsimp only [s_disk, s_base]; rw [hpi_p.cur_vars_eq, hcv_o])
                        (by simp [s_disk, s_base, hpi_p.ag.get FullCoreState.propagated])
                        (hpi_p.cur_vars_eq.symm ▸ hnot_lt)
                        rfl hnl64_idx hct_o2 ht0_p
                        (by
                          simp only [not_lit, lit, fastPropMem_trl, fc_getElem_trl,
                            sem_d, BitVec.ofNat_eq_ofNat])
                        hpi_p hdi_p hdl_p hdok_p hd0_p _hpo_le_pp hte_p hun_p huf_p hoom_p
                        hnoov hov_yes hmbp
                    · intro J_ovf hJ_ovf
                      have hnot_o : not_lit.toNat < 2 * sem_o.core.cur_vars :=
                        hpi_o.cur_vars_eq.symm ▸ hnot_lt
                      have hcl32_o : sem_o.core.cur_level < 2 ^ 32 := by
                        rw [hpi_o.ag.get FullCoreState.cur_level]
                        change sem.core.cur_level < 2 ^ 32
                        rw [hcl_o]; exact hclv_lt32
                      have hnl_sbase : ∀ k : FullCoreState,
                          FullPropDecSpecs.FullTrailExt s_base.core k →
                          k.lvl[not_lit.toNat / 2]?.getD 0#32 =
                            (fastPropMem s_disk sem_d).core.lvl[(((((fastPropMem
                              s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^
                              1#32) >>> 1#32).setWidth 64)).toNat]'hnl_idx_lt := by
                        intro k htr
                        have hnot_div2 :
                            not_lit.toNat / 2 =
                              (s_base.core.trl[prop_v.toNat]?.getD 0#32).toNat / 2 := by
                          have hlt_eq : s_base.core.trl[prop_v.toNat]?.getD 0#32 = lit := by
                            dsimp only [s_base]
                            rw [List.getElem?_eq_getElem hp_sem_lt_trl, Option.getD_some]
                            simp only [lit, fc_getElem_trl, sem_d]
                          rw [hlt_eq]; dsimp only [not_lit]; rw [BitVec.toNat_xor]
                          simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
                            fc_nat_xor_one]
                          split <;> omega
                        have hp_lt_sb : prop_v.toNat < s_base.core.trail_end := by
                          dsimp only [s_base]; rw [← hprop_eq]; exact hp_lt_sem
                        have hlp := htr.lvl_pres prop_v.toNat hp_lt_sb
                        rw [← hnot_div2] at hlp
                        rw [hlp]
                        have hsb_lt : not_lit.toNat / 2 < s_base.core.lvl.length := by
                          dsimp only [s_base]; rw [hlen_o.core_ok.lvl_len]
                          have := hlen_o.core_ok.cur_vars_le; omega
                        have hget : some (s_base.core.lvl[not_lit.toNat / 2]'hsb_lt) =
                            some ((fastPropMem s_disk sem_d).core.lvl[(((((fastPropMem
                              s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
                              1#32).setWidth 64)).toNat]'hnl_idx_lt) := by
                          rw [← List.getElem?_eq_getElem hsb_lt,
                            ← List.getElem?_eq_getElem hnl_idx_lt, fastPropMem_lvl, hnl_div]
                        rw [List.getElem?_eq_getElem hsb_lt, Option.getD_some]
                        exact Option.some.inj hget
                      refine fid_lp_loop_wp (ignore_ref := ignore_ref)
                        c.hmaxv c.harena c.hwcap hpi_o hnot_o
                        (by
                          rw [hpi_o.cur_vars_eq]; dsimp only [s_base]; rw [hcv_o]
                          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
                          rw [Nat.mod_eq_of_lt hcv_lt64,
                            show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                            Nat.shiftLeft_eq, Nat.pow_one,
                            Nat.mul_comm s.core.cur_vars 2, Nat.mod_eq_of_lt h2cv_lt64])
                        (by
                          apply BitVec.eq_of_toNat_eq
                          rw [hpi_o.ag.get FullCoreState.cur_level]; dsimp only [s_base]
                          rw [hcl_o]
                          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hclv_lt32, Nat.mod_eq_of_lt hclv_lt64])
                        hcl32_o hte_o hun_o huf_o hoom_o2 hbr0_o hnl_sbase
                        hdi_o hdl_o hdlim_toNat hdok_o
                        (fun h0 => (hd0_o h0).trans (hd0_sem h0).symm)
                        hmo ?_
                      intro sem' te' un' uf' tk' p' q' di' brk' ovf' ovf_rw' ovf_oth' ovf_cr'
                        ovf_ri' dlen' m' hpi' hdi' hdl' hdok' hd0' hp' hte_ge' hte' hun' huf'
                        hoom' hno' hyes' hm'
                      fid_hsteps
                      exact hJ_ovf _ m' ⟨sem', dlen', hpi', hdi', hdl', hdok',
                        fun h0 => (hd0' h0).trans (hd0_sem h0),
                        hp', hte_ge', hte', hun', huf', hoom', hno', hyes', hm'⟩
                  · have hov_f_eq : ovf_o = false := by revert hc; cases ovf_o <;> simp
                    have ⟨h0, h1, hcs⟩ := hov_f hov_f_eq
                    exact hBo _ mo ⟨sem_o, dlen_o, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o,
                      hte_o, hun_o, huf_o, ht0_o, h0, h1,
                      hcs.elim Or.inl (fun h => Or.inr (Or.inl h)), hmo⟩
                · intro Bo Lo hBo hLo
                  fid_hsteps
                  have hsz_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[((BitVec.setWidth 64
                          (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_add1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[((BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                        (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'
                          hnl64_1_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_1_idx.symm) pf2
                        hnl64_1_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hsz0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[(BitVec.setWidth 64 (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[(BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat]'
                        pf2).setWidth 64 =
                        (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                          hnl64_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_idx.symm) pf2
                        hnl64_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hoff0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff0_lt64 : fullWatchOffCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hend0_lt64
                  have hsz0_lt64 : fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hend0_lt64
                  have hof0_eq := m7_bv64_ofNat_toNat_lt hoff0_lt64
                  have hsz0_eq := m7_bv64_ofNat_toNat_lt hsz0_lt64
                  have hadd0_eq : (BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) +
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat)).toNat =
                      fullWatchOffCore s_base.core not_lit.toNat +
                      fullWatchSizeCore s_base.core not_lit.toNat := by
                    rw [BitVec.toNat_add, hof0_eq, hsz0_eq, Nat.mod_eq_of_lt hend0_lt64]
                  simp only [fastPropMem_wvec]
                  refine hLo (fullWatchSizeCore s_base.core not_lit.toNat + 1) _ mt ?_
                  refine ⟨s_base, 0, ?_, ?_, rfl, Nat.zero_le _,
                    fun _ h => absurd h (Nat.not_lt_zero _), hd0_sem,
                    htend_eq.symm, hunass_eq.symm, hunfl_eq.symm,
                    ht0_bound, fun _ => ⟨rfl, hoom_o, hct_o⟩,
                    fun h => absurd h (by decide), hm_base⟩
                  · simp only [fastPropMem_trl]
                    erw [hoff_trl sem.core.trl rfl _ _, hsz_trl sem.core.trl rfl _ _]
                    rw [hadd0_eq, hof0_eq]
                    simp only [↓reduceIte]
                    exact congrArg (· + 1)
                      (Nat.add_sub_cancel_left (fullWatchOffCore s_base.core not_lit.toNat)
                        (fullWatchSizeCore s_base.core not_lit.toNat)).symm
                  · simp only [fastPropMem_trl]
                    erw [hoff_trl sem.core.trl rfl _ _, hsz_trl sem.core.trl rfl _ _]
                    rw [hof0_eq, hadd0_eq]
                    exact hpi0
              · intro Jt0 hJt0
                fid_hsplit
                · fid_hsplit
                  · fid_hsteps
                    exact hJt0 (tend_v, ()) ml ⟨rfl, Or.inr (htend_eq ▸ Nat.le_refl _)⟩
                  · fid_hsteps; exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨rfl, Or.inl rfl⟩
                · fid_hsteps; exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨rfl, Or.inl rfl⟩
        · have hpe_o : sem.core.propagated = sem.core.trail_end := by
            have hh : tend_v.toNat ≤ prop_v.toNat := Nat.le_of_not_lt hc
            rw [← htend_eq, ← hprop_eq] at hh
            exact Nat.le_antisymm hlen_o.core_ok.propagated_le hh
          have hprop_gt : s.core.propagated < prop_v.toNat := by
            rw [← hprop_eq, hpe_o]
            exact Nat.lt_of_lt_of_le hpr_lt htr_o.te_ge
          have hfuel_dec := hfuel_lt hprop_gt
          clear ih
          fid_hsteps
          exact fid_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
            hQ_fid hlen_o hw_o htr_o hperm_o hag_o hsc_o hd0_sem
            hprop_eq htend_eq hfuel_eq hunass_eq hunfl_eq hfuel_le hpr_lt
            (Or.inl rfl)
            (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o,
              fun _ => hfuel_dec⟩)
            (by decide) (fun h => absurd h (by decide))
            (by
              simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                hunass_eq, hunfl_eq, hfuel_eq] using hm)
      · intro J hJ
        exact hJ s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated,
            BitVec.ofNat 64 s.core.trail_end, s.core.fuel, s.core.unassigned, s.core.unflushed,
            0#64, ()) m
          ⟨s, s.core.trail_end, rfl, hlen0, hw0, .refl _, .refl _, .refl _ _,
            (m7_bv64_ofNat_toNat_lt hpr0_lt64).symm, (m7_bv64_ofNat_toNat_lt hte0_lt64).symm,
            rfl, rfl, rfl, hoom0, rfl, hdense0, rfl, rfl, rfl, rfl, Nat.le_refl _,
            fun hlt => absurd (m7_bv64_ofNat_toNat_lt hpr0_lt64 ▸ hlt) (Nat.lt_irrefl _),
            by rw [m7_bv64_ofNat_toNat_lt hpr0_lt64]; exact Nat.le_refl _,
            Nat.le_refl _, hlen0.core_ok.propagated_le,
            rfl, fun _ => rfl, by simpa only [fastPropMem_self] using hm0⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
