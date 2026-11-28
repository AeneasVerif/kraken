/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Backbone WP Proofs — Top Driver (`Proof.Backbone.WpTop`)

Canonical `(Γ : Env)` `Func.wp` proof (`0` `@[expose]` on theorems/lemmas) for
`full_backbone_m6_wp` (`fullBackboneM6Spec`, `FullM6HdrMem`-threaded Step-13 contract).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Backbone
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

local macro "bb_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `FullM6HdrMem` Extension & BCP Transport Helpers -/

private theorem bb_ext_pres_trans {ext0 ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

private theorem bb_sparse_core_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hc : s'.core = s.core)
    (hext : FullExtScratchPres s s') (hlen : s'.LengthsOk c) :
    FullSparseInvW c F0 F_cur s' :=
  ⟨hlen, hc ▸ hsp.2.1,
    ⟨fun v hv => by change s'.core.mrk[v]?.getD 0#8 = 0#8; rw [hc]; exact hsp.2.2.1.1 v hv,
     fun l hl => by
       change s'.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hc]; exact hsp.2.2.1.2 l hl⟩,
    fun r hr hng => by
      have hr' : r ∈ fullArenaClauseRefs s := by unfold fullArenaClauseRefs at hr ⊢; rwa [← hc]
      have hg' : fullArenaClauseGarb s r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [← hc]
      have hl : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hc]
      rw [hl]; exact hsp.2.2.2.1 r hr' hg',
    ⟨fun i hi => by
      change s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨ _
      rw [hext.1]; unfold fullArenaClauseRefs at *; rw [hc]; exact hsp.2.2.2.2.1.1 i hi,
     by change s'.scratch.extend_len ≤ c.extend_cap; rw [hext.2]; exact hsp.2.2.2.2.1.2⟩,
    by change s'.core.dense_mode = 0#64; rw [hc]; exact hsp.2.2.2.2.2⟩

private theorem bb_sparse_of_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hsp : FullSparseInvW c F0 F_cur s)
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := sc' })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core)
    (hpr : FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed } } s') :
    FullSparseInvW c F0 F_cur s' := by
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm'.2.2 r hr0
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
    unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r hr0 hng0)
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1]
  subst hs'
  exact fullSparseInvW_of_prop_state hsp hlen' hw' hnd' hpr hrefs

/-! ## 2. `full_backbone_m6_wp` (`fullBackboneM6Spec`) -/

theorem full_backbone_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, propagateM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hPrio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (hSched : ∀ a m Q X, fullBackboneSchedM6Spec a m Q X →
      Γ "full_backbone_sched_m6" [i64] [i64] a m Q X)
    (hRound : ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Γ "full_backbone_round_m6" [i64, i64, .bool] [i64] a m Q X)
    (hKeep : ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Γ "full_backbone_keep_m6" [i64, i64] [] a m Q X)
    (hWm4Get : ∀ a m Q X, m6HdrW2aSpec [] [i64] a m Q X →
      Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hWm4Set : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_wm4_set" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullBackboneM6Spec a m Q X →
      Func.wp Γ full_backbone_m6_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, ext0, s, R, rfl, hcfg, hext0, hsp, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_backbone_m6_body
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ (F_cur : List (List Nat)) (s1 : FullState),
      FullSparseInvW c F0 F_cur s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.probing = s.core.probing ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext0 s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨F_cur, s1, hsp1, hl0_1, hpr_1, hfu1, hm1⟩
    rw [Blocks.get_here]
    have hcv1_le := hsp1.1.core_ok.cur_vars_le
    rw [fullM6HdrMem_iff] at hm1
    have hret := hQ 1#64 ext0 s1 m1 ⟨hext0, fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩⟩
      ⟨⟨hsp1.1, ⟨F_cur, hsp1.2.1⟩⟩, hsp1.2.2⟩ (fun _ => hl0_1) hpr_1
      ⟨hl0_1, hpr_1⟩ hfu1 (Or.inl rfl) (fun h => by cases h)
      ((fullM6HdrMem_iff ..).mpr hm1)
    c0_hsteps_nogrp
    all_goals try exact hret
    let s1p : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp1p : FullSparseInvW c F0 F_cur s1p := bb_sparseW_with_probing hsp1 1#64
    c0_hsteps_nogrp; bb_call hProp
    refine ⟨c, F0, F_cur, ext0, s1p, R, rfl, hcfg, hext0, hsp1p.1, hsp1p.2.1,
      hsp1p.2.2.2.2.2, (fullM6HdrMem_iff ..).mpr (by assumption),
      fun pr0 ext2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2 wvec2
        arena2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 sc2 m2 hext2 hw2
        hlen2 hw_w2 _ _ hperm2 hpr_sc2 _ _ _ _ hfu2 _ _ hpr0 _ _ hm2 => ?_⟩
    let s2 : FullState := { s1p with scratch := sc2, core := { s1p.core with
      vals := vals2, flags := flags2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_pos := tp2,
      trail_end := te2, propagated := prop2, unassigned := unass2, unflushed := unfl2,
      wvec := wvec2, arena := arena2, wstk := wstk2, wlen := wlen2, wusable := wu2,
      fuel := fuel2, confl_type := ctype2, confl_ref := cref2, confl_lit0 := c0_2,
      confl_lit1 := c1_2, oom := oom2 } }
    have hsp2 := bb_sparse_of_bcp hsp1p rfl hlen2 hw_w2 hperm2 hpr_sc2
    have hfu2' : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu2 hfu1
    rw [fullM6HdrMem_iff] at hm2
    c0_hsplit
    · c0_hsteps
      have hsp_u := bb_sparseW_with_probing hsp2 s1.core.probing
      exact hQ 20#64 ext2 _ _ ⟨hext2, hw2⟩ ⟨⟨hsp_u.1, ⟨F_cur, hsp_u.2.1⟩⟩, hsp_u.2.2⟩
        (fun _ => hl0_1) hpr_1 ⟨hl0_1, hpr_1⟩ hfu2' (Or.inr rfl)
        (fun _ => level0_unsat_of_conflict_okW hw_w2 hl0_1 (hpr0 hc).2.2)
        ((fullM6HdrMem_iff ..).mpr (by assumption))
    c0_hsplit
    · c0_hsteps
      have hsp_o := bb_sparseW_with_probing hsp2 s1.core.probing
      exact hQ 1#64 ext2 _ _ ⟨hext2, hw2⟩ ⟨⟨hsp_o.1, ⟨F_cur, hsp_o.2.1⟩⟩, hsp_o.2.2⟩
        (fun _ => hl0_1) hpr_1 ⟨hl0_1, hpr_1⟩ hfu2' (Or.inl rfl)
        (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr (by assumption))
    bb_call hPrio
    refine ⟨c, F0, F_cur, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hsp2,
      fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr hm2),
      fun _stop_early wstk3 scr3 m3 hsp3 hm3 => ?_⟩
    bb_call hSched
    refine ⟨c, F0, F_cur, _, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hsp3, hm3,
      fun cand_n0 fl4 ws1_4 m4 hsp4 hcn0_le hlt0 hm4 => ?_⟩
    c0_hsteps_nogrp
    have hsp4a := bb_sparseW_with_ant_sz hsp4 tick_lim
    bb_call hWm4Get
    refine m6HdrW2aSpec_of rfl hcfg hext2 hsp4a.1
      (fullM6HdrMem_unfocus_full (by assumption))
      fun ⟨wm4, ⟨⟩⟩ ext_g sg mg hcg hleng hscg hext_g hw_g hm_g => ?_
    have hw_eg := bb_ext_pres_trans hw2 hw_g
    c0_hsteps_nogrp; bb_call hWm4Set
    refine m6HdrW2aSpec_of rfl hcfg hext_g hleng hm_g
      fun () ext_w sw mw hcw hlenw hscw hext_w hw_w hm_w => ?_
    have hw_ew := bb_ext_pres_trans hw_eg hw_w
    have hsp_w := bb_sparse_core_eq hsp4a (hcw.trans hcg)
      ⟨hscw.extPres.1.trans hscg.extPres.1, hscw.extPres.2.trans hscg.extPres.2⟩ hlenw
    have hws1_w : sw.scratch.work_stk1 = ws1_4 := hscw.ws1.trans hscg.ws1
    let bbOut (cn_o res_o : BitVec 64) (mo : Mem 64) : Prop :=
      ∃ ext_o so, M6HdrExtOk ext_o ∧
        (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext_o ∧ M6ExtW2bPres ext0 ext_o) ∧
        FullSparseInvW c F0 F_cur so ∧ so.core.cur_level = 0 ∧
        so.core.cur_vars = s1.core.cur_vars ∧ so.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        cn_o.toNat ≤ 2 * so.core.cur_vars ∧
        (∀ i < cn_o.toNat,
          (so.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * so.core.cur_vars) ∧
        (res_o = 1#64 ∨ res_o = 20#64) ∧ (res_o = 20#64 → F0.Unsat) ∧
        (FullM6HdrMem c ext_o so ⋆ R) mo
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (mr, ()) mm => mr.toNat ≤ 1000 ∧ mm = mw) ?_ ?_
    · rintro _ ⟨max_rounds, ⟨⟩⟩ mm ⟨hmr_le, hmm⟩
      subst hmm; rw [Blocks.get_here]
      refine wp_join_group (ts := [i64, i64, i64])
        (fun (cn_f, res_f, _, ()) mf => bbOut cn_f res_f mf) ?_ ?_
      · rintro _ ⟨cn_f, res_f, _, ⟨⟩⟩ mf ⟨ext_f, sf, hext_f, hw_ef, hspf, hclf, _hcvf,
            hfuf, hcnf_le, hltf, hdom, huns, hmf⟩
        rw [Blocks.get_here]; bb_call hKeep
        refine ⟨c, F0, F_cur, sf, m6ExtMem (m6ExtAddr c.hdr) ext_f ⋆ R, rfl, hspf,
          hcnf_le, hltf, fullM6HdrMem_focus_full hmf, fun fl_k mk hspk hmk => ?_⟩
        have hmk' := fullM6HdrMem_unfocus_full hmk; rw [fullM6HdrMem_iff] at hmk'
        c0_hsteps
        have hsp_end := bb_sparseW_with_probing hspk s1.core.probing
        exact hQ res_f ext_f _ _ ⟨hext_f, hw_ef⟩
          ⟨⟨hsp_end.1, ⟨F_cur, hsp_end.2.1⟩⟩, hsp_end.2.2⟩ (fun _ => hclf) hpr_1
          ⟨hclf, hpr_1⟩ hfuf hdom huns ((fullM6HdrMem_iff ..).mpr (by assumption))
      · intro Jbr hJbr
        refine wp_loop_inv (ts := [i64, i64, i64])
          (fun (cn_r, res_r, rnd, ()) mr => rnd.toNat ≤ 1000 ∧ bbOut cn_r res_r mr)
          (fun (_, _, rnd, ()) _ => 1000 - rnd.toNat)
          (fun Jr hJr => by
            c0_hsteps
            exact hJr (cand_n0, 1#64, 0#64, ()) _
              ⟨Nat.zero_le _, ext_w, sw, hext_w, hw_ew, hsp_w, by rw [hcw, hcg]; exact hl0_1,
               by rw [hcw, hcg], by rw [hcw, hcg]; exact hfu2',
               by rw [hcw, hcg]; exact hcn0_le,
               by rw [hcw, hcg, hws1_w]; exact hlt0, Or.inl rfl, (fun h => by cases h), hm_w⟩)
          (fun Jr ⟨cn_r, res_r, rnd, ⟨⟩⟩ mr ⟨hrnd_le, ext_r, sr, hext_r, hw_er, hspr, hclr,
              hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩ ihr => ?_)
        have hmr_f := fullM6HdrMem_focus_full hmr
        have hbrk := hJbr (cn_r, res_r, rnd, ()) mr ⟨ext_r, sr, hext_r, hw_er, hspr, hclr,
          hcvr, hfur, hcnr_le, hltr, hdomr, hunsr, hmr⟩
        c0_hsplit
        · have hrnd_lt : rnd.toNat < 1000 := by
            have h1 : rnd.toNat < max_rounds.toNat := by c0_bound
            omega
          have hrnd1 : (rnd + 1#64).toNat = rnd.toNat + 1 := by bv_omega
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · c0_hsteps_nogrp; bb_call hRound
                  refine ⟨c, F0, F_cur, sr, m6ExtMem (m6ExtAddr c.hdr) ext_r ⋆ R, rfl,
                    hspr, hclr, hcnr_le, hltr, fullM6HdrMem_focus_full hmr,
                    fun cn_n sn mn hspn hcln hcvn hfun hcnn_le hltn huc_le huc_ok hmn => ?_⟩
                  have hmn' := fullM6HdrMem_unfocus_full hmn
                  have hcvn' : sn.core.cur_vars = s1.core.cur_vars := hcvn.trans hcvr
                  have hfun' : sn.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [hfun]; exact hfur
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun (res_n, ()) m_n => bbOut cn_n res_n m_n) ?_ ?_
                  · rintro _ ⟨res_n, ⟨⟩⟩ m_n ⟨ext_n, s_n, hext_n, hw_en, hsp_n, hcl_n, hcv_n,
                        hfu_n, hcn_n', hlt_n', hdom_n, huns_n, hm_n⟩
                    rw [Blocks.get_here]; c0_hsplit
                    · c0_hsteps; exact hJbr (cn_n, res_n, rnd, ()) m_n ⟨ext_n, s_n, hext_n,
                        hw_en, hsp_n, hcl_n, hcv_n, hfu_n, hcn_n', hlt_n', hdom_n, huns_n, hm_n⟩
                    · c0_hsteps; exact ihr (cn_n, res_n, rnd + 1#64, ()) m_n (by dsimp; omega)
                        ⟨by omega, ext_n, s_n, hext_n, hw_en, hsp_n, hcl_n, hcv_n, hfu_n,
                         hcn_n', hlt_n', hdom_n, huns_n, hm_n⟩
                  · intro Jn hJn; c0_hsplit
                    · refine wp_join_group (ts := [i64, i64])
                        (fun (res_u, _, ()) mu => ∃ su, FullSparseInvW c F0 F_cur su ∧
                          su.core.cur_level = 0 ∧ su.core.cur_vars = s1.core.cur_vars ∧
                          su.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          su.scratch.work_stk1 = sn.scratch.work_stk1 ∧ (res_u = 1#64 ∨
                            res_u = 20#64) ∧ (res_u = 20#64 → F0.Unsat) ∧
                          (FullM6HdrMem c ext_r su ⋆ R) mu) ?_ ?_
                      · rintro _ ⟨res_u, _, ⟨⟩⟩ mu ⟨su, hspu, hclu, hcvu, hfuu, hws1u, hdomu,
                            hunsu, hmu⟩
                        rw [Blocks.get_here]; c0_hsplit
                        · c0_hsteps; exact hJbr (cn_n, res_u, rnd, ()) mu ⟨ext_r, su, hext_r,
                            hw_er, hspu, hclu, hcvu, hfuu, by rw [hcvu, ← hcvr]; exact hcnn_le,
                            by rw [hws1u, hcvu, ← hcvr]; exact hltn, hdomu, hunsu, hmu⟩
                        · c0_hsteps_nogrp; bb_call hProp
                          refine ⟨c, F0, F_cur, ext_r, su, R, rfl, hcfg, hext_r, hspu.1,
                            hspu.2.1, hspu.2.2.2.2.2, hmu,
                            fun pr1 ext_p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel_p _ _ _ _ _ sc_p
                              mp hext_p hw_p hlenp hwp _ _ hpermp hpr_scp _ _ _ _ hfup _ _ hpr1
                              _ _ hmp => ?_⟩
                          have hspp := bb_sparse_of_bcp hspu rfl hlenp hwp hpermp hpr_scp
                          have hfup' : fuel_p.toNat ≤ s.core.fuel.toNat :=
                            Nat.le_trans hfup hfuu
                          have hw_ep := bb_ext_pres_trans hw_er hw_p
                          have hws1p : sc_p.work_stk1 = su.scratch.work_stk1 := hpr_scp.2.1
                          c0_hsplit
                          · c0_hsteps; exact hJbr (cn_n, 20#64, rnd, ()) mp ⟨ext_p, _, hext_p,
                              hw_ep, hspp, hclu, hcvu, hfup',
                              by rw [hcvu, ← hcvr]; exact hcnn_le,
                              by rw [hws1p, hws1u, hcvu, ← hcvr]; exact hltn, Or.inr rfl,
                              fun _ => level0_unsat_of_conflict_okW hwp hclu
                                (hpr1 (by c0_bound)).2.2, hmp⟩
                          · c0_hsplit
                            · c0_hsteps; exact hJbr (cn_n, res_u, rnd, ()) mp ⟨ext_p, _, hext_p,
                                hw_ep, hspp, hclu, hcvu, hfup',
                                by rw [hcvu, ← hcvr]; exact hcnn_le,
                                by rw [hws1p, hws1u, hcvu, ← hcvr]; exact hltn,
                                hdomu, hunsu, hmp⟩
                            · c0_hsteps; exact hJn (res_u, ()) mp ⟨ext_p, _, hext_p, hw_ep,
                                hspp, hclu, hcvu, hfup', by rw [hcvu, ← hcvr]; exact hcnn_le,
                                by rw [hws1p, hws1u, hcvu, ← hcvr]; exact hltn,
                                hdomu, hunsu, hmp⟩
                      · intro Ju hJu
                        refine wp_loop_inv (ts := [i64]) (fun (ui, ()) mui => ∃ sui :
                          FullState, FullSparseInvW c F0 F_cur sui ∧ sui.core.cur_level = 0 ∧
                          sui.core.cur_vars = s1.core.cur_vars ∧
                          sui.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          ui.toNat ≤ (sn.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat ∧
                          sui.scratch.work_stk1 = sn.scratch.work_stk1 ∧
                          sui.scratch.work_stk2 = sn.scratch.work_stk2 ∧
                          (FullM6HdrMem c ext_r sui ⋆ R) mui) (fun (ui, ()) _ =>
                            (sn.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat - ui.toNat) ?_ ?_
                        · intro Jui hJui; c0_hsteps; exact hJui (0#64, ()) mn
                            ⟨sn, hspn, hcln, hcvn', hfun', Nat.zero_le _, rfl, rfl, hmn'⟩
                        · rintro Jui ⟨ui, ⟨⟩⟩ mui ⟨sui, hspui, hclui, hcvui, hfuui, hui_le,
                            hws1ui, hws2ui, hmui⟩ ihui
                          c0_hsplit
                          · have hui_lt : ui.toNat <
                                (sn.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat := by c0_bound
                            have hui1 : (ui + 1#64).toNat = ui.toNat + 1 := by bv_omega
                            have hui_ws2 : ui.toNat < sui.scratch.work_stk2.length := by
                              have := hspui.1.scratch_ok.work_stk2_len
                              have := hspui.1.core_ok.cur_vars_le; omega
                            let ul := sui.scratch.work_stk2[ui.toNat]'hui_ws2
                            have hul_ok : ul.toNat < 2 * sui.core.cur_vars ∧
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
                              have h1 := huc_ok ui.toNat hui_lt
                              rw [← hws2ui, List.getElem?_eq_getElem hui_ws2,
                                Option.getD_some] at h1
                              rw [hcvui, ← hcvr]; exact h1
                            have hmui_f := fullM6HdrMem_focus_full hmui
                            c0_hsteps_nogrp; bb_call hAddUnit
                            refine ⟨c, F0, F_cur, sui, m6ExtMem (m6ExtAddr c.hdr) ext_r ⋆ R,
                              rfl, hspui.1, hspui.2.1, fun _ => hul_ok.2,
                              fullM6HdrMem_focus_full hmui, fun ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                _ _ _ _ _ _ _ m_a hlen_a hw_a hcl_a hlt_a _ hm_a => ?_⟩
                            have hsp_a : FullSparseInvW c F0 F_cur _ := ⟨hlen_a, hw_a,
                              hspui.2.2.1, hspui.2.2.2.1, hspui.2.2.2.2.1, hspui.2.2.2.2.2⟩
                            c0_hsplit
                            · c0_hsteps; exact ihui (ui + 1#64, ()) _
                                (show (sn.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat -
                                    (ui + 1#64).toNat <
                                    (sn.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat -
                                      ui.toNat by rw [hui1]; omega)
                                ⟨_, bb_sparseW_with_delayed hsp_a _, hcl_a, hcvui, hfuui,
                                 by rw [hui1]; omega, hws1ui, hws2ui,
                                 fullM6HdrMem_unfocus_full (by assumption)⟩
                            · c0_hsteps; exact hJu (20#64, ui, ()) m_a ⟨_, hsp_a, hcl_a, hcvui,
                                hfuui, hws1ui, Or.inr rfl,
                                fun _ => (hlt_a hul_ok.1 (by c0_bound)).1,
                                fullM6HdrMem_unfocus_full (by assumption)⟩
                          · c0_hsteps; exact hJu (res_r, ui, ()) mui ⟨sui, hspui, hclui, hcvui,
                              hfuui, hws1ui, hdomr, hunsr, hmui⟩
                    · c0_hsteps; exact hJn (res_r, ()) mn ⟨ext_r, sn, hext_r, hw_er, hspn,
                        hcln, hcvn', hfun', by rw [hcvn]; exact hcnn_le,
                        by rw [hcvn]; exact hltn, hdomr, hunsr, hmn'⟩
                · c0_hsteps; exact hbrk
              · c0_hsteps; exact hbrk
            · c0_hsteps; exact hbrk
          · c0_hsteps; exact hbrk
        · c0_hsteps; exact hbrk
    · intro _ hJm
      c0_hsplit
      · c0_hsteps; exact hJm (1000#64, ()) mw ⟨by decide, rfl⟩
      · c0_hsteps; refine hJm (_, ()) mw ⟨?_, rfl⟩
        have h2 : (((wm4 >>> 2#64) &&& 0xFFFF#64) + 1#64).toNat < 10 := by
          have h1 : ¬ 10#64 ≤ (((wm4 >>> 2#64) &&& 0xFFFF#64) + 1#64) := by c0_bound
          bv_omega
        change ((wm4 >>> (2 : Nat) &&& 65535#64) + 1#64).toNat < 10 at h2
        change (100#64 * ((wm4 >>> (2 : Nat) &&& 65535#64) + 1#64)).toNat ≤ 1000
        rw [BitVec.toNat_mul, show (100#64 : BitVec 64).toNat = 100 from rfl,
          Nat.mod_eq_of_lt (by omega)]
        omega
  · intro Jbt hJbt
    obtain ⟨F_cur, hw⟩ := hsp.1.witness; have hlen := hsp.1.lengths
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
      have := hlen.core_ok.cur_vars_le; omega
    rw [fullM6HdrMem_iff] at hm0; c0_hsteps_nogrp; c0_hsplit
    · bb_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hlen, hcl_lt, (fun hpos => by
          have h0 : (Arg.imm (t := i64) 0).val.toNat = 0 := rfl
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [h0] at hpos; omega),
        hw.trail_lits_lt, fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr hm0),
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => ?_⟩
      have hsp1 := fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1
      obtain ⟨F_c1, hw1'⟩ := hsp1.1.witness
      exact hJbt () _ ⟨F_c1, _, ⟨hsp1.1.lengths, hw1', hsp1.2⟩, by rw [hcl1]; simp, rfl,
        Nat.le_refl _, fullM6HdrMem_unfocus_full hm1⟩
    · have hcl0' : s.core.cur_level = 0 := by
        have h1 : s.core.cur_level % 2 ^ 64 = 0 := by c0_bound
        rwa [Nat.mod_eq_of_lt hcl_lt] at h1
      exact hJbt () m0 ⟨F_cur, s, ⟨hlen, hw, hsp.2⟩, hcl0', rfl, Nat.le_refl _,
        (fullM6HdrMem_iff ..).mpr hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Backbone
