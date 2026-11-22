module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3b
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B` Proof Shard 3 (`full_analyze_m6`)

Proves `full_analyze_m6_wp` certifying `full_analyze_m6_body` against canonical
`Full.fullAnalyzeSpec`:
1. Level-0 early exit (`20`, UNSAT via `Full.level0_unsat_of_conflict_okW`).
2. `decision_rate` EMA update on non-probing conflicts (`full_dr_update_m6`).
3. Level-1 multi-UIP failed-literal loop (`full_ana_failed_lit_m6`).
4. 1UIP/OTFS retry (`dst = 2`): `conflicts += 1`, conditional `tmp[0]` restore of root conflict
   literal, and `full_restore_bump_ana_m6` (sorted VMTF bumping gated by `full_dr_allow_m6` +
   mark clear).
5. `dst = 1`: `full_min_shrink_m6`, conditional `full_restore_bump_ana_m6` + `full_tick_rel`,
   glue calculation, conditional `full_ema_update`, and tail `full_learn_clause`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding full_analyze_body full_analyze_wf
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

section LocalHelpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem m6_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

private theorem m6_bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

attribute [local bv_c0] m6_bv32_lshr_1 m6_bv32_setWidth64_toNat

private theorem m6_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem m6_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem m6_arenaVarsNodup_congr_core {s1 s2 : FullState}
    (hnd : Full.FullArenaVarsNodup s1)
    (ha : s2.core.arena = s1.core.arena) (hl : s2.core.arena_len = s1.core.arena_len) :
    Full.FullArenaVarsNodup s2 := by
  unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore
    Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaClauseLits
    Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore Full.fullArenaHdrCore at hnd ⊢
  rw [ha, hl]; exact hnd

private theorem m6_otfs_of_safetySlice {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : Full.FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : Full.FullExtScratchPres s s') : Full.FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold Full.FullLitMarksClear Full.FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseGarb
      Full.fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact Full.FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold Full.fullArenaClauseRefs; rwa [heq]

private theorem m6_cut_with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : Full.FullCutInvW c F0 F_cur cut s) (k' : BitVec 64) :
    Full.FullCutInvW c F0 F_cur cut { s with scratch := { s.scratch with conflicts := k' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩,
   Full.deduce_same_core_cut h.2.1 s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len
     s.core.min_clr_len,
   h.2.2.1, m6_arenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
   Full.FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩

private theorem m6_cut_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : Full.FullCutInvW c F0 F_cur cut s)
    {tmp' : List (BitVec 32)} {tl' : Nat} (htarr : tmp'.length = c.max_vars)
    (htle : tl' ≤ c.max_vars) :
    Full.FullCutInvW c F0 F_cur cut
      { s with core := { s.core with tmp := tmp', tmp_len := tl' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htarr, tmp_len_le := htle }, h.1.scratch_ok⟩,
   Full.deduce_same_core_cut h.2.1 s.core.mrk tmp' s.core.tmp_cnt tl' s.core.min_clr_len,
   h.2.2.1, m6_arenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
   Full.FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩

private theorem m6_cut_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : Full.FullCutInvW c F0 F_cur cut s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : Full.FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    Full.FullCutInvW c F0 F_cur cut
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen', Full.deduce_same_core_cut h.2.1 mrk' s.core.tmp s.core.tmp_cnt s.core.tmp_len mcl',
   ⟨hmrk0', h.2.2.1.2⟩, m6_arenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
   Full.FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩

private theorem m6_otfs_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : Full.FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : Full.FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    Full.FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } := by
  let s' : FullState :=
    { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
  have hwt : Full.FullOtfsWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨hlen', hwt, ⟨hmrk0', h.2.2.1.2⟩, m6_arenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
    Full.FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩

end LocalHelpers

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_analyze_m6` `Func.wp` certification against `Full.fullAnalyzeSpec` -/

/-- Certifies `full_analyze_m6_body` against canonical `Full.fullAnalyzeSpec`:
- `decision_rate` update (`full_dr_update_m6`),
- level-1 multi-UIP failed-literal analysis (`full_ana_failed_lit_m6`),
- OTFS retry with root-literal fallback bump (`full_restore_bump_ana_m6`), and
- cohesive block minimization/shrinking + conditional bumping, glue/EMA, and clause learning. -/
theorem full_analyze_m6_wp (Γ : Env)
    (hDrUpdate : ∀ a m Q X, m6DrUpdateSpec a m Q X →
      Γ "full_dr_update_m6" [i64] [] a m Q X)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailedLit : ∀ a m Q X, m6AnaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip_m6" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, m6RestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m6" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, Full.fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs, hconfl, hm, hQ⟩
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcl := hs.1.core_ok
  have hcv_le := hcl.cur_vars_le
  have hcur_le := hs.2.1.cur_level_le
  have hte_le := hcl.trail_end_le
  unfold Func.wp full_analyze_m6_body
  dsimp only
  c0_hsplit
  · -- Level 0 conflict (`cur_level == 0`) -> UNSAT (`20`)
    have hcl0 : s.core.cur_level = 0 := by bv_omega
    c0_hsteps
    exact hQ 20#64 s m hs.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hs.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => Full.level0_unsat_of_conflict_okW hs.2.1 hcl0 hconfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · have hcur_pos : 0 < s.core.cur_level := by bv_omega
    have hlim_nat : (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = s.core.cur_vars + 64 := by
      bv_omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ m_dr =>
      ∃ s_dr : FullState,
        Full.FullSparseInvW c F0 F_cur s_dr ∧ Full.FullConflictOkW F_cur s_dr ∧
        s_dr.core.cur_level = s.core.cur_level ∧ s_dr.core.cur_vars = s.core.cur_vars ∧
        s_dr.core.fuel = s.core.fuel ∧ s_dr.core.dense_mode = s.core.dense_mode ∧
        s_dr.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s_dr ⋆ R) m_dr) ?_ ?_
    · rintro _ ⟨⟩ m_dr
        ⟨s_dr, hsp_dr, hcf_dr, hcl_dr, hcv_dr, hfu_dr, hdm_dr, hws2_dr, hm_dr⟩
      rw [Blocks.get_here]; try dsimp only
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun rem (iter_v, ()) m_i =>
          ∃ iter cut s_i,
            iter ≤ s.core.cur_vars + 64 ∧ rem = s.core.cur_vars + 64 - iter ∧
            iter_v = BitVec.ofNat 64 iter ∧ cut ≤ s_i.core.trail_end ∧
            Full.FullCutInvW c F0 F_cur cut s_i ∧ 0 < s_i.core.cur_level ∧
            s_i.core.cur_level ≤ s.core.cur_level ∧ Full.FullConflictOkCut F_cur cut s_i ∧
            s_i.core.cur_vars = s.core.cur_vars ∧
            s_i.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            s_i.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s_i ⋆ R) m_i) ?_ ?_
      · rintro L rem ⟨iter_v, ⟨⟩⟩ m_i ih
          ⟨iter, cut, s_i, hiter_le, rfl, rfl, hcut_le, hcut_inv, hcl_pos_i, hcl_le_i,
            hconfl_i, hcv_i, hfu_i, hws2_i, hm_i⟩
        c0_hsplit
        · have hiter_lt : iter < s.core.cur_vars + 64 := by
            have hlt : iter % 2 ^ 64 <
                (s.core.cur_vars + (64#64 : BitVec 64).toNat) % 2 ^ 64 := by
              simpa only [← hcv_dr,
                show (64#64 : BitVec 64).toNat = BitVec.toNat 64 from rfl] using
                (by assumption : _)
            rw [Nat.mod_eq_of_lt (by omega : iter < 2 ^ 64),
              show (64#64 : BitVec 64).toNat = 64 from rfl,
              Nat.mod_eq_of_lt (by omega : s.core.cur_vars + 64 < 2 ^ 64)] at hlt
            exact hlt
          have hiter1_eq : (BitVec.ofNat 64 iter + 1#64).toNat = iter + 1 := by
            rw [m6_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega)]
          have hiter1_bv : BitVec.ofNat 64 iter + 1#64 = BitVec.ofNat 64 (iter + 1) :=
            BitVec.eq_of_toNat_eq (by rw [hiter1_eq, bv64_ofNat_toNat (by omega)])
          c0_hsteps_nogrp; c0_hcall hOneLit
          refine ⟨c, F0, F_cur, cut, s_i, R, rfl, hcut_inv, hconfl_i, hm_i, ?_⟩
          intro ol s1 m1 h1_len hol_dom h1_cv h1_fu h1_ws2 h1_20 h1_1 h1_2 h1_0 hm1
          have h1_cv' : s1.core.cur_vars = s.core.cur_vars := h1_cv.trans hcv_i
          have h1_fu' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by
            rw [h1_fu]; exact hfu_i
          have h1_ws2' : s1.scratch.work_stk2 = s.scratch.work_stk2 := h1_ws2.trans hws2_i
          c0_hsplit
          · c0_hsteps
            obtain ⟨hu1, ho1, hcl1, hdm1⟩ := h1_20 (by assumption)
            exact hQ 20#64 s1 m1 h1_len (Or.inr (Or.inr rfl)) h1_cv' h1_fu'
              ⟨h1_ws2', fun _ => ⟨ho1, Nat.le_trans hcl1 hcl_le_i,
                hdm1.trans (hcut_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
              (fun _ => hu1) (fun h => by cases h) (fun h => by cases h) hm1
          · c0_hsplit
            · obtain ⟨h1_sp, h1_cl_lt⟩ := h1_1 (by assumption)
              c0_hsteps
              exact hQ 1#64 s1 m1 h1_len (Or.inr (Or.inl rfl)) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩
                (fun h => by cases h) (fun h => by cases h)
                (fun _ => ⟨h1_sp, by omega⟩) hm1
            · c0_hsplit
              · c0_hsteps
                exact hQ 0#64 s1 m1 h1_len (Or.inl rfl) h1_cv' h1_fu'
                  ⟨h1_ws2', fun h => by cases h⟩
                  (fun h => by cases h) (fun _ => h1_2 (by assumption))
                  (fun h => by cases h) hm1
              · have hol_0 : ol = 0#64 := by
                  rcases hol_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                obtain ⟨cut1, hcut1_le, hcut1_inv, hcl1_pos, hcl1_le, hconfl1⟩ := h1_0 hol_0
                have hcl1_le' : s1.core.cur_level ≤ s.core.cur_level :=
                  Nat.le_trans hcl1_le hcl_le_i
                c0_hsplit
                · -- `cur_level == 1`: failed-literal multi-UIP (`full_ana_failed_lit_m6`)
                  c0_hsteps_nogrp; c0_hcall hFailedLit
                  refine m6AnaFailedLitSpec_of hcut1_inv hcl1_pos hconfl1 hm1 ?_
                  intro r s_fl m_fl hfl_len hfl_dom hfl_cv hfl_fu hfl_ws2
                    hfl_20 hfl_0 hfl_1 hm_fl
                  have hfl_cv' : s_fl.core.cur_vars = s.core.cur_vars := hfl_cv.trans h1_cv'
                  have hfl_fu' : s_fl.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [hfl_fu]; exact h1_fu'
                  have hfl_ws2' : s_fl.scratch.work_stk2 = s.scratch.work_stk2 :=
                    hfl_ws2.trans h1_ws2'
                  c0_hsteps
                  exact hQ r s_fl m_fl hfl_len hfl_dom hfl_cv' hfl_fu'
                    ⟨hfl_ws2', fun h20 => let ⟨_, ho, hcl, hdm⟩ := hfl_20 h20
                      ⟨ho, Nat.le_trans hcl hcl1_le',
                        hdm.trans (hcut1_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
                    (fun h20 => (hfl_20 h20).1) hfl_0
                    (fun h1 => let ⟨hsp, hcl⟩ := hfl_1 h1
                      ⟨hsp, Nat.lt_of_lt_of_le hcl hcl1_le'⟩)
                    hm_fl
                · c0_hsteps_nogrp; c0_hcall hDeduce
                  refine ⟨c, F0, F_cur, cut1, s1, R, rfl, hcut1_inv, hcl1_pos, hconfl1, hm1, ?_⟩
                  intro dst s2 m2 h2_len hdst_dom h2_cv h2_fu h2_ws2 h2_20 h2_0 h2_1 h2_2 hm2
                  have h2_cv' : s2.core.cur_vars = s.core.cur_vars := h2_cv.trans h1_cv'
                  have h2_fu' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
                    rw [h2_fu]; exact h1_fu'
                  have h2_ws2' : s2.scratch.work_stk2 = s.scratch.work_stk2 :=
                    h2_ws2.trans h1_ws2'
                  c0_hsplit
                  · c0_hsteps
                    obtain ⟨hu2, ho2, hcl2, hdm2⟩ := h2_20 (by assumption)
                    exact hQ 20#64 s2 m2 h2_len (Or.inr (Or.inr rfl)) h2_cv' h2_fu'
                      ⟨h2_ws2', fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1_le',
                        hdm2.trans (hcut1_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
                      (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2
                  · c0_hsplit
                    · c0_hsteps
                      exact hQ 0#64 s2 m2 h2_len (Or.inl rfl) h2_cv' h2_fu'
                        ⟨h2_ws2', fun h => by cases h⟩
                        (fun h => by cases h) (fun _ => h2_0 (by assumption))
                        (fun h => by cases h) hm2
                    · c0_hsplit
                      · -- `dst == 2`: increment `conflicts`, conditional `tmp[0]` + bump, retry
                        obtain ⟨cut2, hcut2_le, hcut2_inv, hcl2_eq, hconfl2⟩ :=
                          h2_2 (by assumption)
                        c0_hsteps_nogrp
                        let s2c : FullState :=
                          { s2 with
                            scratch := { s2.scratch with
                              conflicts := s2.scratch.conflicts + 1#64 } }
                        have h2c_inv : Full.FullCutInvW c F0 F_cur cut2 s2c :=
                          m6_cut_with_conflicts hcut2_inv (s2.scratch.conflicts + 1#64)
                        refine wp_join_group (ts := []) (fun _ m_rb =>
                          ∃ s_rb : FullState,
                            cut2 ≤ s_rb.core.trail_end ∧
                            Full.FullCutInvW c F0 F_cur cut2 s_rb ∧
                            s_rb.core.cur_level = s2.core.cur_level ∧
                            Full.FullConflictOkCut F_cur cut2 s_rb ∧
                            s_rb.core.cur_vars = s2.core.cur_vars ∧
                            s_rb.core.fuel = s2.core.fuel ∧
                            s_rb.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                            (FullMem c s_rb ⋆ R) m_rb) ?_ ?_
                        · rintro _ ⟨⟩ m_rb
                            ⟨s_rb, hrb_cut, hrb_inv, hrb_cl, hrb_cf, hrb_cv, hrb_fu, hrb_ws2,
                              hm_rb⟩
                          rw [Blocks.get_here]; try dsimp only
                          c0_hsteps
                          rw [show (1 : BitVec 64) = 1#64 from rfl, hiter1_bv]
                          exact ih (s.core.cur_vars + 64 - (iter + 1))
                            (BitVec.ofNat 64 (iter + 1), ()) m_rb (by omega)
                            ⟨iter + 1, cut2, s_rb, by omega, rfl, rfl, hrb_cut, hrb_inv,
                              by rw [hrb_cl, hcl2_eq]; exact hcl1_pos,
                              by rw [hrb_cl, hcl2_eq]; exact hcl1_le',
                              hrb_cf, hrb_cv.trans h2_cv', by rw [hrb_fu]; exact h2_fu',
                              hrb_ws2.trans h2_ws2', hm_rb⟩
                        · intro Jrb hJrb
                          c0_hsplit
                          · -- `probing == 0`: conditional `tmp[0]` + `full_restore_bump_ana_m6`
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := []) (fun _ m_t =>
                              ∃ s_t : FullState,
                                cut2 ≤ s_t.core.trail_end ∧
                                Full.FullCutInvW c F0 F_cur cut2 s_t ∧
                                s_t.core.cur_level = s2.core.cur_level ∧
                                Full.FullConflictOkCut F_cur cut2 s_t ∧
                                s_t.core.cur_vars = s2.core.cur_vars ∧
                                s_t.core.fuel = s2.core.fuel ∧
                                s_t.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                                (FullMem c s_t ⋆ R) m_t) ?_ ?_
                            · rintro _ ⟨⟩ m_t
                                ⟨s_t, ht_cut, ht_inv, ht_cl, ht_cf, ht_cv, ht_fu, ht_ws2, hm_t⟩
                              rw [Blocks.get_here]; try dsimp only
                              c0_hsteps_nogrp; c0_hcall hRestoreBump
                              refine m6RestoreBumpAnaSpec_of ht_inv.1 ht_inv.2.2.1.1 hm_t
                                fun mrk_r mcl_r sc_r m_r hlen_r hmrk_r _ _ hpres_r hws2_r hm_r => ?_
                              let s_rb : FullState :=
                                { core := { s_t.core with mrk := mrk_r, min_clr_len := mcl_r }
                                  scratch := sc_r }
                              c0_hsteps
                              exact hJrb () m_r
                                ⟨s_rb, ht_cut,
                                 m6_cut_of_restoreBump ht_inv hlen_r hmrk_r hpres_r,
                                 ht_cl, ht_cf, ht_cv, ht_fu, hws2_r.trans ht_ws2, hm_r⟩
                            · intro Jt hJt
                              c0_hsplit
                              · have hcv_pos2 : 0 < s2.core.cur_vars := by bv_omega
                                have htmp_pos : 0 < s2c.core.tmp.length := by
                                  rw [h2_len.core_ok.tmp_len_arr]
                                  have := h2_len.core_ok.cur_vars_le; omega
                                have htl1_le : 1 ≤ c.max_vars := by
                                  have := h2_len.core_ok.cur_vars_le; omega
                                c0_hsteps_nogrp
                                refine wp_unroll_group fun _ _ => ?_
                                c0_hsplit
                                · let lit0_32 := s2c.core.confl_lit0.setWidth 32
                                  let s_t : FullState :=
                                    { s2c with core :=
                                      { s2c.core with
                                        tmp := s2c.core.tmp.set 0 lit0_32, tmp_len := 1 } }
                                  c0_hsteps
                                  exact hJt () m
                                    ⟨s_t, hcut2_le, m6_cut_with_tmp h2c_inv
                                      (by simp [s2c, h2_len.core_ok.tmp_len_arr]) htl1_le,
                                     rfl, hconfl2, rfl, rfl, rfl,
                                     by simpa only [s_t, s2c, lit0_32,
                                       show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                                       show (1#64 : BitVec 64) = 1 from rfl,
                                       show (1 : BitVec 64).toNat = 1 from rfl] using hm⟩
                                · c0_hsteps
                                  all_goals first
                                  | exact hJt () m ⟨s2c, hcut2_le, h2c_inv, rfl, hconfl2,
                                      rfl, rfl, rfl, hm⟩
                                  | (have haca := c.harena; unfold dimacsBound at haca
                                     have hal_le := h2_len.core_ok.arena_len_le
                                     have hc3_lt : (s2c.core.confl_ref + 3#64).toNat <
                                         s2c.core.arena.length := by
                                       dsimp only [s2c]
                                       rw [h2_len.core_ok.arena_len_arr]; bv_omega
                                     let l_ar :=
                                       s2c.core.arena[(s2c.core.confl_ref + 3#64).toNat]'hc3_lt
                                     let s_t : FullState :=
                                       { s2c with core :=
                                         { s2c.core with
                                           tmp := s2c.core.tmp.set 0 l_ar, tmp_len := 1 } }
                                     c0_hsteps
                                     exact hJt () m
                                       ⟨s_t, hcut2_le, m6_cut_with_tmp h2c_inv
                                         (by simp [s2c, h2_len.core_ok.tmp_len_arr]) htl1_le,
                                        rfl, hconfl2, rfl, rfl, rfl,
                                        by simpa only [s_t, s2c, l_ar,
                                          show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                                          show (1#64 : BitVec 64) = 1 from rfl,
                                          show (3#64 : BitVec 64) = 3 from rfl,
                                          show (1 : BitVec 64).toNat = 1 from rfl] using hm⟩)
                              · c0_hsteps
                                exact hJt () m ⟨s2c, hcut2_le, h2c_inv, rfl, hconfl2,
                                  rfl, rfl, rfl, hm⟩
                          · c0_hsteps
                            exact hJrb () m ⟨s2c, hcut2_le, h2c_inv, rfl, hconfl2,
                              rfl, rfl, rfl, hm⟩
                      · -- `dst == 1`: minimize, conditional bump+tick, glue loop, EMA, learn
                        have hdst_1 : dst = 1#64 := by
                          rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                        obtain ⟨h2_otfs, h2_cl, h2_tl1, h2_tl_cv, h2_nd, h2_vals, h2_lvls,
                          h2_lvl0, h2_ent⟩ := h2_1 hdst_1
                        clear ih L
                        c0_hsteps_nogrp; c0_hcall hMinShrink
                        refine ⟨c, F0, F_cur, s2, R, rfl, h2_len, h2_otfs.2.1, h2_otfs.2.2.1,
                          h2_tl1, h2_tl_cv, h2_nd, h2_ent, h2_vals, h2_lvls, h2_lvl0, hm2, ?_⟩
                        intro tmp_ms tl_ms mrk_ms mstk_ms mclr_ms mcl_ms mcf_ms conf_ms llits_ms
                          mrem_ms sstk_ms m_ms _ hms_len hms_w hms_clr hms_tl1 hms_tl_le hms_0
                          hms_nd hms_post hms_ent hm_ms
                        let s_ms : FullState :=
                          { s2 with
                            core := { s2.core with
                              tmp := tmp_ms, tmp_len := tl_ms, mrk := mrk_ms, min_stk := mstk_ms,
                              min_clr := mclr_ms, min_clr_len := mcl_ms, min_clr_full := mcf_ms }
                            scratch := { s2.scratch with
                              conflicts := conf_ms, learned_lits := llits_ms,
                              min_removed := mrem_ms, shrink_stk := sstk_ms } }
                        have hms_otfs : Full.FullOtfsInvW c F0 F_cur s_ms :=
                          ⟨hms_len, hms_w, hms_clr,
                            m6_arenaVarsNodup_congr_core h2_otfs.2.2.2.1 rfl rfl,
                            Full.FullExtScratchOk.of_pres h2_otfs.2.2.2.2.1 ⟨rfl, rfl⟩
                              (fun _ r => r),
                            h2_otfs.2.2.2.2.2⟩
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ m_tr =>
                          ∃ s_tr : FullState,
                            Full.FullOtfsInvW c F0 F_cur s_tr ∧
                            s_tr.core.tmp = tmp_ms ∧ s_tr.core.tmp_len = tl_ms ∧
                            s_tr.core.lvl = s2.core.lvl ∧ s_tr.core.vals = s2.core.vals ∧
                            s_tr.core.cur_level = s2.core.cur_level ∧
                            s_tr.core.cur_vars = s2.core.cur_vars ∧
                            s_tr.core.fuel = s2.core.fuel ∧
                            s_tr.core.dense_mode = s2.core.dense_mode ∧
                            s_tr.scratch.work_stk2 = s.scratch.work_stk2 ∧
                            (FullMem c s_tr ⋆ R) m_tr) ?_ ?_
                        · rintro _ ⟨⟩ m_tr
                            ⟨s_tr, htr_otfs, htr_tmp, htr_tl, htr_lvl, htr_vals, htr_cl, htr_cv,
                              htr_fu, htr_dm, htr_ws2, hm_tr⟩
                          rw [Blocks.get_here]; try dsimp only
                          have htr_len := htr_otfs.1
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64, i32, i64])
                            (fun r_gi (glue_v, last_v, gi_v, ()) m_gi =>
                              ∃ gi, 1 ≤ gi ∧ gi ≤ tl_ms ∧ r_gi = tl_ms - gi ∧
                                gi_v = BitVec.ofNat 64 gi ∧ (FullMem c s_tr ⋆ R) m_gi) ?_ ?_
                          · rintro Lgi _ ⟨glue_v, last_v, gi_v, ⟨⟩⟩ m_gi ih_gi
                              ⟨gi, hgi1, hgile, rfl, rfl, hm_gi⟩
                            have htr_tl_bd : tl_ms < 2 ^ 64 := by
                              have := h2_len.core_ok.cur_vars_le; omega
                            c0_hsplit
                            · have hgi_bv : (BitVec.ofNat 64 gi).toNat = gi :=
                                bv64_ofNat_toNat (by omega)
                              have hgilt : gi < tl_ms := by
                                have hlt : (BitVec.ofNat 64 gi).toNat <
                                    (BitVec.ofNat 64 s_tr.core.tmp_len).toNat := by assumption
                                rw [htr_tl, hgi_bv, bv64_ofNat_toNat htr_tl_bd] at hlt
                                exact hlt
                              have htr_tmp_len : s_tr.core.tmp.length = c.max_vars :=
                                htr_len.core_ok.tmp_len_arr
                              have hgi_idx :
                                  (BitVec.ofNat 64 gi).toNat < s_tr.core.tmp.length := by
                                rw [hgi_bv, htr_tmp_len]
                                have := h2_len.core_ok.cur_vars_le; omega
                              have hgi_post := hms_post gi hgi1 hgilt
                              have htr_tmp_gi_lt : gi < tmp_ms.length := by
                                rw [← htr_tmp, htr_tmp_len]
                                have := h2_len.core_ok.cur_vars_le; omega
                              have hgi_t_eq :
                                  s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx =
                                    tmp_ms[gi]'htr_tmp_gi_lt :=
                                m6_getElem_congr_list htr_tmp hgi_bv
                              have hgi_l_eq : (tmp_ms[gi]'htr_tmp_gi_lt).toNat / 2 =
                                  ((tmp_ms[gi]?.getD 0#32).toNat / 2) := by
                                rw [List.getElem?_eq_getElem htr_tmp_gi_lt, Option.getD_some]
                              have hgi_lvl_lt : ((s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx
                                  >>> 1#32).setWidth 64).toNat < s_tr.core.lvl.length := by
                                rw [m6_bv32_setWidth64_toNat, m6_bv32_lshr_1, hgi_t_eq, hgi_l_eq,
                                  htr_lvl, h2_len.core_ok.lvl_len]
                                have := h2_len.core_ok.cur_vars_le; have := hgi_post.1; omega
                              have hgi1_nat : (BitVec.ofNat 64 gi + 1#64).toNat = gi + 1 := by
                                rw [m6_bv64_add1_toNat (by rw [hgi_bv]; omega), hgi_bv]
                              c0_hsteps
                              all_goals exact (ih_gi (tl_ms - (gi + 1)) _ m_gi (by omega)
                                ⟨gi + 1, by omega, by omega, rfl,
                                  BitVec.eq_of_toNat_eq (by
                                    rw [show (1 : BitVec 64) = 1#64 from rfl, hgi1_nat,
                                      bv64_ofNat_toNat (by omega)]),
                                  hm_gi⟩)
                            · -- Post-glue: conditional `full_ema_update`, then `full_learn_clause`
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := []) (fun _ m_em =>
                                ∃ s_em : FullState,
                                  Full.FullOtfsInvW c F0 F_cur s_em ∧
                                  s_em.core = s_tr.core ∧
                                  s_em.scratch.work_stk2 = s.scratch.work_stk2 ∧
                                  (FullMem c s_em ⋆ R) m_em) ?_ ?_
                              · rintro _ ⟨⟩ m_em ⟨s_em, hem_otfs, hem_core, hem_ws2, hm_em⟩
                                rw [Blocks.get_here]; try dsimp only
                                c0_hsteps_nogrp; c0_hcall hLearnCl
                                refine ⟨c, F0, F_cur, s_em, R, rfl, hem_otfs,
                                  ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm_em, ?_⟩
                                · rw [hem_core, htr_cl, h2_cl]; exact hcl1_pos
                                · rw [hem_core, htr_tl]; exact hms_tl1
                                · rw [hem_core, htr_tl, htr_cv]; omega
                                · rw [hem_core, htr_tmp, htr_tl]; exact hms_nd
                                · intro k hk; rw [hem_core, htr_tl] at hk
                                  rw [hem_core, htr_tmp, htr_vals, htr_cv]
                                  cases k with
                                  | zero =>
                                    have h0_s2 := h2_vals 0 h2_tl1
                                    have h0_eq : tmp_ms[0]? = s2.core.tmp[0]? := hms_0
                                    rw [h0_eq]; exact h0_s2
                                  | succ k' =>
                                    have hk_p := hms_post (k' + 1) (by omega) hk
                                    exact ⟨hk_p.1, hk_p.2.1⟩
                                · intro k hk1 hk2
                                  rw [hem_core, htr_tl] at hk2
                                  rw [hem_core, htr_lvl, htr_tmp, htr_tl, htr_cl]
                                  have hk_p := hms_post k hk1 hk2
                                  exact ⟨hk_p.2.2.1, hk_p.2.2.2.1, hk_p.2.2.2.2⟩
                                · rw [hem_core, htr_tmp, htr_tl]; exact hms_ent
                                · intro rl s_lc m_lc hlc_len hlc_dom hlc_cv hlc_fu hlc_ws2
                                    hlc_20 hlc_0 hlc_1 hm_lc
                                  have hlc_cv' : s_lc.core.cur_vars = s.core.cur_vars := by
                                    rw [hlc_cv, hem_core, htr_cv]; exact h2_cv'
                                  have hlc_fu' : s_lc.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                    rw [hem_core, htr_fu] at hlc_fu
                                    exact Nat.le_trans hlc_fu h2_fu'
                                  have hlc_ws2' : s_lc.scratch.work_stk2 = s.scratch.work_stk2 :=
                                    hlc_ws2.trans hem_ws2
                                  have hcl_tr : s_em.core.cur_level = s2.core.cur_level := by
                                    rw [hem_core, htr_cl]
                                  have hdm_tr : s_em.core.dense_mode = s2.core.dense_mode := by
                                    rw [hem_core, htr_dm]
                                  c0_hsteps
                                  exact hQ rl s_lc m_lc hlc_len hlc_dom hlc_cv' hlc_fu'
                                    ⟨hlc_ws2', fun h20 => let ⟨_, hsp, hcl⟩ := hlc_20 h20
                                      ⟨hsp.toOtfs, by rw [hcl_tr] at hcl; omega,
                                        hsp.2.2.2.2.2.trans hs.2.2.2.2.2.symm⟩⟩
                                    (fun h20 => (hlc_20 h20).1)
                                    (fun h0 => (hlc_0 h0).toOtfs)
                                    (fun h1 => let ⟨hs1, hcl1⟩ := hlc_1 h1
                                      ⟨hs1, by rw [hcl_tr] at hcl1; omega⟩)
                                    hm_lc
                              · intro Jem hJem
                                c0_hsplit
                                · c0_hsteps_nogrp; c0_hcall hEma
                                  refine ⟨c, s_tr, R, rfl, htr_len, hm_gi,
                                    fun _ s_em m_em hem_core hem_len hem_pres hm_em => ?_⟩
                                  have hem_otfs :=
                                    m6_otfs_of_safetySlice htr_otfs hem_len hem_core hem_pres.1
                                  have hem_core_eq : s_em.core = s_tr.core :=
                                    fullCoreState_agrees_with_scratch hem_core
                                  have hem_ws2 : s_em.scratch.work_stk2 = s.scratch.work_stk2 :=
                                    hem_pres.2.2.1.trans htr_ws2
                                  c0_hsteps
                                  exact hJem () m_em ⟨s_em, hem_otfs, hem_core_eq, hem_ws2, hm_em⟩
                                · c0_hsteps
                                  exact hJem () m_gi ⟨s_tr, htr_otfs, rfl, htr_ws2, hm_gi⟩
                          · intro Jgl hJgl; c0_hsteps
                            exact hJgl (tl_ms - 1) (1#64, 0#32, 1#64, ()) m_tr
                              ⟨1, Nat.le_refl _, hms_tl1, rfl, rfl, hm_tr⟩
                        · intro Jtr hJtr
                          c0_hsplit
                          · c0_hsteps_nogrp; c0_hcall hRestoreBump
                            refine m6RestoreBumpAnaSpec_of hms_len hms_clr.1 hm_ms
                              fun mrk_r mcl_r sc_r m_r hlen_r hmrk_r _ _ hpres_r hws2_r hm_r => ?_
                            let s_rb : FullState :=
                              { core := { s_ms.core with mrk := mrk_r, min_clr_len := mcl_r }
                                scratch := sc_r }
                            have hrb_otfs := m6_otfs_of_restoreBump hms_otfs hlen_r hmrk_r hpres_r
                            c0_hsteps_nogrp; c0_hcall hTickRel
                            refine ⟨c, s_rb, R, rfl, hlen_r, hm_r,
                              fun _ s_tr m_tr htr_core htr_len htr_pres hm_tr => ?_⟩
                            have htr_otfs :=
                              m6_otfs_of_safetySlice hrb_otfs htr_len htr_core htr_pres.1
                            have htr_core_eq : s_tr.core = s_rb.core :=
                              fullCoreState_agrees_with_scratch htr_core
                            have htr_ws2 : s_tr.scratch.work_stk2 = s.scratch.work_stk2 :=
                              htr_pres.2.2.1.trans (hws2_r.trans h2_ws2')
                            c0_hsteps
                            exact hJtr () m_tr
                              ⟨s_tr, htr_otfs, by rw [htr_core_eq], by rw [htr_core_eq],
                               by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                               by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                               htr_ws2, hm_tr⟩
                          · c0_hsteps
                            exact hJtr () m_ms
                              ⟨s_ms, hms_otfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                               h2_ws2', hm_ms⟩
        · -- Loop exit (`iter = cur_vars + 64`) -> return `0`
          c0_hsteps
          exact hQ 0#64 s_i m_i hcut_inv.1 (Or.inl rfl) hcv_i hfu_i
            ⟨hws2_i, fun h => by cases h⟩
            (fun h => by cases h) (fun _ => hcut_inv.toOtfs) (fun h => by cases h) hm_i
      · intro L hL; c0_hsteps
        exact hL (s.core.cur_vars + 64) (0#64, ()) m_dr
          ⟨0, s_dr.core.trail_end, s_dr, Nat.zero_le _, rfl, rfl, Nat.le_refl _,
            hsp_dr.toCut, by rw [hcl_dr]; exact hcur_pos, by rw [hcl_dr]; exact Nat.le_refl _,
            hcf_dr.toCut hsp_dr.2.1, hcv_dr, by rw [hfu_dr]; exact Nat.le_refl _,
            hws2_dr, hm_dr⟩
    · intro Jdr hJdr
      c0_hsplit
      · c0_hsteps_nogrp; c0_hcall hDrUpdate
        refine m6DrUpdateSpec_of hs.1 hm fun dl' del' m_dr hlen_dr hm_dr => ?_
        let s_dr : FullState :=
          { s with scratch := { s.scratch with delayed_len := dl', delayed := del' } }
        have hsp_dr : Full.FullSparseInvW c F0 F_cur s_dr :=
          ⟨hlen_dr, hs.2.1, hs.2.2.1, m6_arenaVarsNodup_congr_core hs.2.2.2.1 rfl rfl,
            Full.FullExtScratchOk.of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
            hs.2.2.2.2.2⟩
        c0_hsteps
        exact hJdr () m_dr ⟨s_dr, hsp_dr, hconfl, rfl, rfl, rfl, rfl, rfl, hm_dr⟩
      · c0_hsteps
        exact hJdr () m ⟨s, hs, hconfl, rfl, rfl, rfl, rfl, rfl, hm⟩

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
