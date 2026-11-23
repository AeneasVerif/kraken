/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7SpecBridges0
public import LeanQbe.T.Examples.Kissat.FullM7SpecBridges1
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Wf
import LeanQbe.T.WfLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` `M7` Spec Bridges — Gap B Wrapper, `full_analyze_m5`, and Non-Vacuity

Unified additive bridge entry point re-exporting `FullM7SpecBridges0` (`Gap A`) and
`FullM7SpecBridges1` (`m7MinShrinkSpec`, `full_min_shrink_m6_m7sort_wp`), plus:
1. `full_min_shrink_m7_wp`: certifies forwarding wrapper `FullM6Orch.full_min_shrink_body`
   under `"full_min_shrink_m6" ↦ m7MinShrinkSpec`.
2. `full_analyze_m5_m7_wp`: certifies `FullM5HeurCore.full_analyze_m5_body` against canonical
   `Full.fullAnalyzeSpec` under `"full_min_shrink" ↦ m7MinShrinkSpec` (`wsort` is idle
   scratch in `full_analyze_m5` and `FullM6Orch.full_analyze_core_m6`).
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`): `nv_m7_min_shrink_m6`,
   `nv_m7_min_shrink`, and `nv_m7_analyze`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7SpecBridges

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open scoped LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

/-! ## 1. `full_min_shrink` Wrapper Bridge (`full_min_shrink_m7_wp`) -/

theorem full_min_shrink_m7_wp (Γ : Env)
    (hMs : ∀ args m Q X, m7MinShrinkSpec args m Q X →
      Γ "full_min_shrink_m6" [i64] [] args m Q X) :
    ∀ args m Q X, m7MinShrinkSpec args m Q X →
      Func.wp Γ FullM6Orch.full_min_shrink_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, ha, hlen, hw, hlm, htl1, htl_cv, hnd, hEnt, hvals, hlvls,
    h0_lvl, hm, hQ⟩ := m7MinShrinkSpec_elim hspec
  obtain rfl : h = c.hdr := congrArg Prod.fst ha
  unfold Func.wp FullM6Orch.full_min_shrink_body
  dsimp only
  c0_hsteps_nogrp
  c0_call hMs
  exact m7MinShrinkSpec_of hlen hw hlm htl1 htl_cv hnd hEnt hvals hlvls h0_lvl hm
    fun tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' wsort' m'
        hlen' hw' hlm' htl1' htl_le h0' hnd' hpost' hEnt' hw16' hm' => by
      c0_hsteps
      exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' wsort' m'
        hlen' hw' hlm' htl1' htl_le h0' hnd' hpost' hEnt' hw16' hm'

/-! ## 2. Canonical `full_analyze_m5` Gap-B Closure (`full_analyze_m5_m7_wp`) -/

section AnalyzeHelpers

private theorem br_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

private theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem br_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem br_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem br_fullArenaVarsNodup_congr_core {s s' : FullState}
    (h : FullArenaVarsNodup s) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) : FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    fullArenaHdrCore
  rw [har, hal]; exact h

private theorem br_fullOtfsWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem br_fullOtfsWitnessInv_with_tmp_tl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) (tl' : Nat) :
    FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp', tmp_len := tl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem br_fullOtfsInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · exact br_fullArenaVarsNodup_congr_core h.2.2.2.1 (congrArg FullCoreState.arena heq)
      (congrArg FullCoreState.arena_len heq)
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

private theorem br_fullCutInvW_with_conflicts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (k' : BitVec 64) :
    FullCutInvW c F0 F_cur cut { s with scratch := { s.scratch with conflicts := k' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩, h.2.1, h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r), h.2.2.2.2.2⟩

private theorem br_fullCutInvW_with_tmp_tl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (tmp' : List (BitVec 32)) (tl' : Nat)
    (htmp_len : tmp'.length = c.max_vars) (htl_le : tl' ≤ c.max_vars) :
    FullCutInvW c F0 F_cur cut
      { s with core := { s.core with tmp := tmp', tmp_len := tl' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htmp_len, tmp_len_le := htl_le }, h.1.scratch_ok⟩,
    ⟨br_fullOtfsWitnessInv_with_tmp_tl h.2.1.toFullOtfsWitnessInv tmp' tl', h.2.1.cut_le,
      h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩,
    h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r), h.2.2.2.2.2⟩

private theorem br_fullCutInvW_of_restoreBump {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullCutInvW c F0 F_cur cut
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen',
    ⟨{ h.2.1.toFullOtfsWitnessInv with
        arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
        watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
      h.2.1.cut_le, h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩,
    ⟨hmrk0', h.2.2.1.2⟩,
    br_fullArenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r),
    h.2.2.2.2.2⟩

private theorem br_fullOtfsInvW_of_restoreBump {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (h : FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen',
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hmrk0', h.2.2.1.2⟩,
    br_fullArenaVarsNodup_congr_core h.2.2.2.1 rfl rfl,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r),
    h.2.2.2.2.2⟩

end AnalyzeHelpers

/-- Discharges `FullM5HeurCore.full_analyze_m5_body` against canonical `Full.fullAnalyzeSpec`
when `"full_min_shrink"` uses `M7` `m7MinShrinkSpec` (permitting `wsort` scratch mutation for
`16 < tmp_len`). `full_analyze_m5` never reads or relies on `wsort` across `full_min_shrink`. -/
private def restrictOneLitSpec (P : BitVec 64 → Prop) : Spec [i64] [i64] :=
  fun a m Q X => Full.fullOneLitConflSpec a m (fun (r, ()) m' => P r → Q (r, ()) m') X

private def restrictDeduceSpec (P : BitVec 64 → Prop) : Spec [i64] [i64] :=
  fun a m Q X => Full.fullDeduce1uipSpec a m (fun (r, ()) m' => P r → Q (r, ()) m') X

private def restrictLearnSpec (P : BitVec 64 → Prop) : Spec [i64, i64] [i64] :=
  fun a m Q X => Full.fullLearnClauseSpec a m (fun (r, ()) m' => P r → Q (r, ()) m') X

private theorem oneLit_unrestrict {a m Q X}
    (h : restrictOneLitSpec (fun _ => True) a m Q X) : Full.fullOneLitConflSpec a m Q X := by
  rcases a with ⟨hdr, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, cut, s, R, rfl, h1, h2, hm, hq⟩
  exact ⟨c, F0, F_cur, cut, s, R, rfl, h1, h2, hm,
    fun r s' m' a1 a2 a3 a4 a5 a6 a7 a8 a9 hm' =>
      hq r s' m' a1 a2 a3 a4 a5 a6 a7 a8 a9 hm' trivial⟩

private theorem deduce_unrestrict {a m Q X}
    (h : restrictDeduceSpec (fun _ => True) a m Q X) : Full.fullDeduce1uipSpec a m Q X := by
  rcases a with ⟨hdr, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, cut, s, R, rfl, h1, h2, h3, hm, hq⟩
  exact ⟨c, F0, F_cur, cut, s, R, rfl, h1, h2, h3, hm,
    fun r s' m' a1 a2 a3 a4 a5 a6 a7 a8 a9 hm' =>
      hq r s' m' a1 a2 a3 a4 a5 a6 a7 a8 a9 hm' trivial⟩

private theorem learn_unrestrict {a m Q X}
    (h : restrictLearnSpec (fun _ => True) a m Q X) : Full.fullLearnClauseSpec a m Q X := by
  rcases a with ⟨hdr, glue, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, h1, h2, h3, h4, h5, h6, h7, h8, hm, hq⟩
  exact ⟨c, F0, F_cur, s, R, rfl, h1, h2, h3, h4, h5, h6, h7, h8, hm,
    fun r s' m' a1 a2 a3 a4 a5 a6 a7 a8 hm' =>
      hq r s' m' a1 a2 a3 a4 a5 a6 a7 a8 hm' trivial⟩

private theorem full_analyze_m5_m7_core_wp (Γ : Env)
    (olAllow dedAllow lcAllow retAllow : BitVec 64 → Prop) (noRetry : Prop)
    (hRet20 : retAllow 20#64)
    (hOl20 : olAllow 20#64 → retAllow 20#64) (hOl1 : olAllow 1#64 → retAllow 1#64)
    (hOl2 : olAllow 2#64 → retAllow 0#64)
    (hDed20 : dedAllow 20#64 → retAllow 20#64) (hDed0 : dedAllow 0#64 → retAllow 0#64)
    (hNoRetry : noRetry → ¬ dedAllow 2#64)
    (hLcRet : ∀ r, lcAllow r → retAllow r)
    (hLoopExit : ¬ noRetry → retAllow 0#64)
    (hOneLit : ∀ a m Q X, restrictOneLitSpec olAllow a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, restrictDeduceSpec dedAllow a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m7MinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, restrictLearnSpec lcAllow a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
         (R : Mem 64 → Prop),
        args = (c.hdr, ()) ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ r s' m', s'.LengthsOk c → retAllow r → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
            (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
              s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
          (r = 20#64 → F0.Unsat) → (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
          (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m') →
      Func.wp Γ full_analyze_m5_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, ha, hs, hconfl, hm, hQ⟩
  obtain rfl : h = c.hdr := congrArg Prod.fst ha
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcl := hs.1.core_ok
  have hcv_le := hcl.cur_vars_le
  have hcur_le := hs.2.1.cur_level_le
  have hte_le := hcl.trail_end_le
  unfold Func.wp full_analyze_m5_body
  dsimp only
  c0_hsplit
  · have hcl0 : s.core.cur_level = 0 := by bv_omega
    c0_hsteps
    exact hQ 20#64 s m hs.1 hRet20 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hs.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => Full.level0_unsat_of_conflict_okW hs.2.1 hcl0 hconfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · have hcur_pos : 0 < s.core.cur_level := by bv_omega
    have hlim_nat : (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = s.core.cur_vars + 64 := by
      bv_omega
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64])
      (fun rem (iter_v, ()) m_i =>
        ∃ iter cut s_i,
          iter ≤ s.core.cur_vars + 64 ∧ (noRetry → iter = 0) ∧
          rem = s.core.cur_vars + 64 - iter ∧
          iter_v = BitVec.ofNat 64 iter ∧ cut ≤ s_i.core.trail_end ∧
          FullCutInvW c F0 F_cur cut s_i ∧ 0 < s_i.core.cur_level ∧
          s_i.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut s_i ∧
          s_i.core.cur_vars = s.core.cur_vars ∧ s_i.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          s_i.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s_i ⋆ R) m_i) ?_ ?_
    · rintro L rem ⟨iter_v, ⟨⟩⟩ m_i ih
        ⟨iter, cut, s_i, hiter_le, hiter0, rfl, rfl, hcut_le, hcut_inv, hcl_pos_i, hcl_le_i,
          hconfl_i, hcv_i, hfu_i, hws2_i, hm_i⟩
      c0_hsplit
      · have hiter_lt : iter < s.core.cur_vars + 64 := by
          have hlt : iter % 2 ^ 64 < (s.core.cur_vars + (64#64 : BitVec 64).toNat) % 2 ^ 64 := by
            assumption
          rw [Nat.mod_eq_of_lt (by omega : iter < 2 ^ 64),
            show (64#64 : BitVec 64).toNat = 64 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars + 64 < 2 ^ 64)] at hlt
          exact hlt
        have hiter1_eq : (BitVec.ofNat 64 iter + 1#64).toNat = iter + 1 := by
          rw [br_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
            bv64_ofNat_toNat (by omega)]
        have hiter1_bv : BitVec.ofNat 64 iter + 1#64 = BitVec.ofNat 64 (iter + 1) :=
          BitVec.eq_of_toNat_eq (by rw [hiter1_eq, bv64_ofNat_toNat (by omega)])
        c0_hsteps_nogrp; c0_call hOneLit
        refine ⟨c, F0, F_cur, cut, s_i, R, rfl, hcut_inv, hconfl_i, hm_i, ?_⟩
        intro ol s1 m1 h1_len hol_dom h1_cv h1_fu h1_ws2 h1_20 h1_1 h1_2 h1_0 hm1 hol_allow
        have h1_cv' : s1.core.cur_vars = s.core.cur_vars := h1_cv.trans hcv_i
        have h1_fu' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h1_fu]; exact hfu_i
        have h1_ws2' : s1.scratch.work_stk2 = s.scratch.work_stk2 := h1_ws2.trans hws2_i
        c0_hsplit
        · c0_hsteps
          obtain ⟨hu1, ho1, hcl1, hdm1⟩ := h1_20 (by assumption)
          exact hQ 20#64 s1 m1 h1_len
            (hOl20 (by simpa [show ol = 20#64 by assumption] using hol_allow))
            (Or.inr (Or.inr rfl)) h1_cv' h1_fu'
            ⟨h1_ws2', fun _ => ⟨ho1, Nat.le_trans hcl1 hcl_le_i,
              hdm1.trans (hcut_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
            (fun _ => hu1) (fun h => by cases h) (fun h => by cases h) hm1
        · c0_hsplit
          · obtain ⟨h1_sp, h1_cl_lt⟩ := h1_1 (by assumption)
            c0_hsteps
            exact hQ 1#64 s1 m1 h1_len
              (hOl1 (by simpa [show ol = 1#64 by assumption] using hol_allow))
              (Or.inr (Or.inl rfl)) h1_cv' h1_fu'
              ⟨h1_ws2', fun h => by cases h⟩
              (fun h => by cases h) (fun h => by cases h)
              (fun _ => ⟨h1_sp, by omega⟩) hm1
          · c0_hsplit
            · c0_hsteps
              exact hQ 0#64 s1 m1 h1_len
                (hOl2 (by simpa [show ol = 2#64 by assumption] using hol_allow))
                (Or.inl rfl) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩
                (fun h => by cases h) (fun _ => h1_2 (by assumption))
                (fun h => by cases h) hm1
            · have hol_0 : ol = 0#64 := by
                rcases hol_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨cut1, hcut1_le, hcut1_inv, hcl1_pos, hcl1_le, hconfl1⟩ := h1_0 hol_0
              have hcl1_le' : s1.core.cur_level ≤ s.core.cur_level := Nat.le_trans hcl1_le hcl_le_i
              c0_hsteps_nogrp; c0_call hDeduce
              refine ⟨c, F0, F_cur, cut1, s1, R, rfl, hcut1_inv, hcl1_pos, hconfl1, hm1, ?_⟩
              intro dst s2 m2 h2_len hdst_dom h2_cv h2_fu h2_ws2 h2_20 h2_0 h2_1 h2_2 hm2 hdst_allow
              have h2_cv' : s2.core.cur_vars = s.core.cur_vars := h2_cv.trans h1_cv'
              have h2_fu' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h2_fu]; exact h1_fu'
              have h2_ws2' : s2.scratch.work_stk2 = s.scratch.work_stk2 := h2_ws2.trans h1_ws2'
              c0_hsplit
              · c0_hsteps
                obtain ⟨hu2, ho2, hcl2, hdm2⟩ := h2_20 (by assumption)
                exact hQ 20#64 s2 m2 h2_len
                  (hDed20 (by simpa [show dst = 20#64 by assumption] using hdst_allow))
                  (Or.inr (Or.inr rfl)) h2_cv' h2_fu'
                  ⟨h2_ws2', fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1_le',
                    hdm2.trans (hcut1_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
                  (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2
              · c0_hsplit
                · c0_hsteps
                  exact hQ 0#64 s2 m2 h2_len
                    (hDed0 (by simpa [show dst = 0#64 by assumption] using hdst_allow))
                    (Or.inl rfl) h2_cv' h2_fu'
                    ⟨h2_ws2', fun h => by cases h⟩
                    (fun h => by cases h) (fun _ => h2_0 (by assumption))
                    (fun h => by cases h) hm2
                · c0_hsplit
                  · -- `dst == 2`: increment `conflicts`, conditional restore+bump, retry
                    have hdst_2 : dst = 2#64 := by
                      rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨cut2, hcut2_le, hcut2_inv, hcl2_eq, hconfl2⟩ := h2_2 hdst_2
                    c0_hsteps_nogrp
                    let s2c : FullState :=
                      { s2 with
                        scratch := { s2.scratch with conflicts := s2.scratch.conflicts + 1#64 } }
                    have h2c_inv :=
                      br_fullCutInvW_with_conflicts hcut2_inv (s2.scratch.conflicts + 1#64)
                    refine wp_join_group (ts := []) (fun _ m_rb =>
                      ∃ s_rb : FullState,
                        s_rb.core.trail_end ≥ cut2 ∧ FullCutInvW c F0 F_cur cut2 s_rb ∧
                        s_rb.core.cur_level = s2c.core.cur_level ∧
                        FullConflictOkCut F_cur cut2 s_rb ∧
                        s_rb.core.cur_vars = s2.core.cur_vars ∧
                        s_rb.core.fuel = s2.core.fuel ∧
                        s_rb.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                        (FullMem c s_rb ⋆ R) m_rb) ?_ ?_
                    · rintro _ ⟨⟩ m_rb
                        ⟨s_rb, hrb_cut, hrb_inv, hrb_cl, hrb_cf, hrb_cv, hrb_fu, hrb_ws2, hm_rb⟩
                      rw [Blocks.get_here]; try dsimp only
                      c0_hsteps
                      rw [show (1 : BitVec 64) = 1#64 from rfl, hiter1_bv]
                      exact ih (s.core.cur_vars + 64 - (iter + 1)) (BitVec.ofNat 64 (iter + 1), ())
                        m_rb (by omega)
                        ⟨iter + 1, cut2, s_rb, by omega,
                          fun hnr => absurd (hdst_2 ▸ hdst_allow) (hNoRetry hnr),
                          rfl, rfl, hrb_cut, hrb_inv,
                          by rw [hrb_cl, hcl2_eq]; exact hcl1_pos,
                          by rw [hrb_cl, hcl2_eq]; exact hcl1_le',
                          hrb_cf, hrb_cv.trans h2_cv', by rw [hrb_fu]; exact h2_fu',
                          hrb_ws2.trans h2_ws2', hm_rb⟩
                    · intro Jrb hJrb
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ m_t =>
                          ∃ s_t : FullState,
                            cut2 ≤ s_t.core.trail_end ∧
                            FullCutInvW c F0 F_cur cut2 s_t ∧
                            s_t.core.cur_level = s2.core.cur_level ∧
                            FullConflictOkCut F_cur cut2 s_t ∧
                            s_t.core.cur_vars = s2.core.cur_vars ∧
                            s_t.core.fuel = s2.core.fuel ∧
                            s_t.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                            (FullMem c s_t ⋆ R) m_t) ?_ ?_
                        · rintro _ ⟨⟩ m_t
                            ⟨s_t, ht_cut, ht_inv, ht_cl, ht_cf, ht_cv, ht_fu, ht_ws2, hm_t⟩
                          rw [Blocks.get_here]; try dsimp only
                          c0_hsteps_nogrp; c0_call hRestoreBump
                          refine ⟨c, s_t, R, rfl, ht_inv.1, ht_inv.2.2.1.1, hm_t, ?_⟩
                          intro mrk_r mcl_r sc_r m_r _ hlen_r hmrk_r hpres_r hws2_r hm_r
                          let s_rb : FullState :=
                            { core := { s_t.core with mrk := mrk_r, min_clr_len := mcl_r }
                              scratch := sc_r }
                          c0_hsteps
                          exact hJrb () m_r
                            ⟨s_rb, ht_cut,
                              br_fullCutInvW_of_restoreBump ht_inv hlen_r hmrk_r hpres_r,
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
                                ⟨s_t, hcut2_le, br_fullCutInvW_with_tmp_tl h2c_inv _ 1
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
                                   ⟨s_t, hcut2_le, br_fullCutInvW_with_tmp_tl h2c_inv _ 1
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
                  · -- `dst == 1`: `m7MinShrinkSpec`, conditional restore+bump, tick/glue/ema/learn
                    have hdst_1 : dst = 1#64 := by
                      rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨h2_otfs, h2_cl, h2_tl1, h2_tl_cv, h2_nd, h2_vals, h2_lvls, h2_lvl0,
                      h2_ent⟩ := h2_1 hdst_1
                    clear ih L
                    c0_hsteps_nogrp; c0_call hMinShrink
                    refine m7MinShrinkSpec_of h2_len h2_otfs.2.1 h2_otfs.2.2.1 h2_tl1 h2_tl_cv
                      h2_nd h2_ent h2_vals h2_lvls h2_lvl0 hm2 ?_
                    intro tmp_ms tl_ms mrk_ms mstk_ms mclr_ms mcl_ms mcf_ms conf_ms llits_ms
                      mrem_ms sstk_ms wsort_ms m_ms _ hms_len hms_w hms_clr hms_tl1 hms_tl_le hms_0
                      hms_nd hms_post hms_ent _ hm_ms
                    let s_ms : FullState :=
                      { core := { s2.core with
                          tmp := tmp_ms, tmp_len := tl_ms, mrk := mrk_ms, min_stk := mstk_ms,
                          min_clr := mclr_ms, min_clr_len := mcl_ms, min_clr_full := mcf_ms }
                        scratch := { s2.scratch with
                          conflicts := conf_ms, learned_lits := llits_ms,
                          min_removed := mrem_ms, shrink_stk := sstk_ms, wsort := wsort_ms } }
                    have hms_otfs : FullOtfsInvW c F0 F_cur s_ms :=
                      ⟨hms_len, hms_w, hms_clr,
                        br_fullArenaVarsNodup_congr_core h2_otfs.2.2.2.1 rfl rfl,
                        FullExtScratchOk.of_pres h2_otfs.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                        h2_otfs.2.2.2.2.2⟩
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ m_r1 =>
                      ∃ s_r1 : FullState,
                        FullOtfsInvW c F0 F_cur s_r1 ∧
                        s_r1.core.tmp = tmp_ms ∧ s_r1.core.tmp_len = tl_ms ∧
                        s_r1.core.lvl = s2.core.lvl ∧ s_r1.core.vals = s2.core.vals ∧
                        s_r1.core.cur_level = s2.core.cur_level ∧
                        s_r1.core.cur_vars = s2.core.cur_vars ∧
                        s_r1.core.fuel = s2.core.fuel ∧
                        s_r1.core.dense_mode = s2.core.dense_mode ∧
                        s_r1.core.probing = s2.core.probing ∧
                        s_r1.scratch.work_stk2 = s.scratch.work_stk2 ∧
                        (FullMem c s_r1 ⋆ R) m_r1) ?_ ?_
                    · rintro _ ⟨⟩ m_tr
                        ⟨s_tr, htr_otfs, hr1_tmp, hr1_tl, hr1_lvl, hr1_vals, hr1_cl, hr1_cv,
                          hr1_fu, hr1_dm, hr1_pr, htr_ws2, hm_tr⟩
                      have htr_len := htr_otfs.1
                      have htr_core_eq : s_tr.core = s_tr.core := rfl
                      have hm_gi : (FullMem c s_tr ⋆ R) m_tr := hm_tr
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
                            rw [htr_core_eq, hr1_tl, hgi_bv, bv64_ofNat_toNat htr_tl_bd] at hlt
                            exact hlt
                          have htr_tmp_len : s_tr.core.tmp.length = c.max_vars :=
                            htr_len.core_ok.tmp_len_arr
                          have hgi_idx : (BitVec.ofNat 64 gi).toNat < s_tr.core.tmp.length := by
                            rw [hgi_bv, htr_tmp_len]
                            have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_post := hms_post gi hgi1 hgilt
                          have htr_tmp_gi_lt : gi < tmp_ms.length := by
                            rw [← hr1_tmp, ← htr_core_eq, htr_tmp_len]
                            have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_t_eq : s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx =
                              tmp_ms[gi]'htr_tmp_gi_lt :=
                            br_getElem_congr_list (by rw [htr_core_eq, hr1_tmp]) hgi_bv
                          have hgi_l_eq : (tmp_ms[gi]'htr_tmp_gi_lt).toNat / 2 =
                              ((tmp_ms[gi]?.getD 0#32).toNat / 2) := by
                            rw [List.getElem?_eq_getElem htr_tmp_gi_lt, Option.getD_some]
                          have hgi_lvl_lt : ((s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx
                              >>> 1#32).setWidth 64).toNat < s_tr.core.lvl.length := by
                            rw [bv32_setWidth64_toNat, br_bv32_lshr_1, hgi_t_eq, hgi_l_eq,
                              htr_core_eq, hr1_lvl, h2_len.core_ok.lvl_len]
                            have := h2_len.core_ok.cur_vars_le; have := hgi_post.1; omega
                          have hgi1_nat : (BitVec.ofNat 64 gi + 1#64).toNat = gi + 1 := by
                            rw [br_bv64_add1_toNat (by rw [hgi_bv]; omega), hgi_bv]
                          c0_hsteps
                          all_goals exact (ih_gi (tl_ms - (gi + 1)) _ m_gi (by omega)
                            ⟨gi + 1, by omega, by omega, rfl,
                              BitVec.eq_of_toNat_eq (by
                                rw [show (1 : BitVec 64) = 1#64 from rfl, hgi1_nat,
                                  bv64_ofNat_toNat (by omega)]),
                              hm_gi⟩)
                        · c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ m_em =>
                            ∃ s_em : FullState,
                              FullOtfsInvW c F0 F_cur s_em ∧ s_em.core = s_tr.core ∧
                              s_em.scratch.work_stk2 = s.scratch.work_stk2 ∧
                              (FullMem c s_em ⋆ R) m_em) ?_ ?_
                          · rintro _ ⟨⟩ m_em ⟨s_em, hem_otfs, hem_core, hem_ws2, hm_em⟩
                            rw [Blocks.get_here]; try dsimp only
                            c0_hsteps_nogrp; c0_call hLearnCl
                            refine ⟨c, F0, F_cur, s_em, R, rfl, hem_otfs,
                              ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm_em, ?_⟩
                            · rw [hem_core, htr_core_eq, hr1_cl, h2_cl]; exact hcl1_pos
                            · rw [hem_core, htr_core_eq, hr1_tl]; exact hms_tl1
                            · rw [hem_core, htr_core_eq, hr1_tl, hr1_cv]; omega
                            · rw [hem_core, htr_core_eq, hr1_tmp, hr1_tl]; exact hms_nd
                            · intro k hk
                              rw [hem_core, htr_core_eq, hr1_tl] at hk
                              rw [hem_core, htr_core_eq, hr1_tmp, hr1_vals, hr1_cv]
                              cases k with
                              | zero =>
                                have h0_s2 := h2_vals 0 h2_tl1
                                have h0_eq : tmp_ms[0]? = s2.core.tmp[0]? := hms_0
                                rw [h0_eq]; exact h0_s2
                              | succ k' =>
                                have hk_p := hms_post (k' + 1) (by omega) hk
                                exact ⟨hk_p.1, hk_p.2.1⟩
                            · intro k hk1 hk2
                              rw [hem_core, htr_core_eq, hr1_tl] at hk2
                              rw [hem_core, htr_core_eq, hr1_lvl, hr1_tmp, hr1_tl, hr1_cl]
                              have hk_p := hms_post k hk1 hk2
                              exact ⟨hk_p.2.2.1, hk_p.2.2.2.1, hk_p.2.2.2.2⟩
                            · rw [hem_core, htr_core_eq, hr1_tmp, hr1_tl]; exact hms_ent
                            · intro rl s_lc m_lc hlc_len hlc_dom hlc_cv hlc_fu hlc_ws2
                                hlc_20 hlc_0 hlc_1 hm_lc hlc_allow
                              have hlc_cv' : s_lc.core.cur_vars = s.core.cur_vars := by
                                rw [hlc_cv, hem_core, htr_core_eq, hr1_cv]; exact h2_cv'
                              have hlc_fu' : s_lc.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                rw [hem_core, htr_core_eq, hr1_fu] at hlc_fu
                                exact Nat.le_trans hlc_fu h2_fu'
                              have hlc_ws2' : s_lc.scratch.work_stk2 = s.scratch.work_stk2 :=
                                hlc_ws2.trans hem_ws2
                              have hcl_tr : s_em.core.cur_level = s2.core.cur_level := by
                                rw [hem_core, htr_core_eq, hr1_cl]
                              have hdm_tr : s_em.core.dense_mode = s2.core.dense_mode := by
                                rw [hem_core, htr_core_eq, hr1_dm]
                              c0_hsteps
                              exact hQ rl s_lc m_lc hlc_len (hLcRet rl hlc_allow) hlc_dom hlc_cv'
                                hlc_fu'
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
                            · c0_hsteps_nogrp; c0_call hEma
                              refine ⟨c, s_tr, R, rfl, htr_len, hm_gi,
                                fun _ s_em m_em hem_core hem_len hem_pres hm_em => ?_⟩
                              have hem_otfs :=
                                br_fullOtfsInvW_of_safetySlice htr_otfs hem_len hem_core hem_pres.1
                              have hem_core_eq : s_em.core = s_tr.core :=
                                fullCoreState_agrees_with_scratch hem_core
                              have hem_ws2 : s_em.scratch.work_stk2 = s.scratch.work_stk2 :=
                                hem_pres.2.2.1.trans htr_ws2
                              c0_hsteps
                              exact hJem () m_em ⟨s_em, hem_otfs, hem_core_eq, hem_ws2, hm_em⟩
                            · c0_hsteps
                              exact hJem () m_gi ⟨s_tr, htr_otfs, rfl, htr_ws2, hm_gi⟩
                      · intro Jgl hJgl
                        c0_hsteps
                        exact hJgl (tl_ms - 1) (1#64, 0#32, 1#64, ()) m_tr
                          ⟨1, Nat.le_refl _, hms_tl1, rfl, rfl, hm_tr⟩
                    · intro Jr1 hJr1
                      c0_hsplit
                      · c0_hsteps_nogrp; c0_call hRestoreBump
                        refine ⟨c, s_ms, R, rfl, hms_len, hms_clr.1, hm_ms, ?_⟩
                        intro mrk_r mcl_r sc_r m_r _ hlen_r hmrk_r hpres_r hws2_r hm_r
                        let s_r1 : FullState :=
                          { core := { s_ms.core with mrk := mrk_r, min_clr_len := mcl_r }
                            scratch := sc_r }
                        have hr1_otfs :=
                          br_fullOtfsInvW_of_restoreBump hms_otfs hlen_r hmrk_r hpres_r
                        have hr1_ws2 : s_r1.scratch.work_stk2 = s.scratch.work_stk2 :=
                          hws2_r.trans h2_ws2'
                        c0_hsteps_nogrp; c0_call hTickRel
                        refine ⟨c, s_r1, R, rfl, hlen_r, hm_r,
                          fun _ s_tr m_tr htr_core htr_len htr_pres hm_tr => ?_⟩
                        have htr_otfs :=
                          br_fullOtfsInvW_of_safetySlice hr1_otfs htr_len htr_core htr_pres.1
                        have htr_core_eq : s_tr.core = s_r1.core :=
                          fullCoreState_agrees_with_scratch htr_core
                        have htr_ws2 : s_tr.scratch.work_stk2 = s.scratch.work_stk2 :=
                          htr_pres.2.2.1.trans hr1_ws2
                        c0_hsteps
                        exact hJr1 () m_tr
                          ⟨s_tr, htr_otfs, by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], htr_ws2, hm_tr⟩
                      · c0_hsteps
                        exact hJr1 () m_ms
                          ⟨s_ms, hms_otfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                            h2_ws2', hm_ms⟩
      · c0_hsteps
        have hnr_f : ¬ noRetry := fun hnr => by
          have hiter_z := hiter0 hnr; subst hiter_z
          have hlt0 : 0 % 2 ^ 64 < (s.core.cur_vars + (64 : BitVec 64).toNat) % 2 ^ 64 := by
            rw [Nat.mod_eq_of_lt (by decide), show (64 : BitVec 64).toNat = 64 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega
          contradiction
        exact hQ 0#64 s_i m_i hcut_inv.1 (hLoopExit hnr_f) (Or.inl rfl) hcv_i hfu_i
          ⟨hws2_i, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => hcut_inv.toOtfs) (fun h => by cases h) hm_i
    · intro L hL; c0_hsteps
      exact hL (s.core.cur_vars + 64) (0#64, ()) m
        ⟨0, s.core.trail_end, s, Nat.zero_le _, fun _ => rfl, rfl, rfl, Nat.le_refl _,
          hs.toCut, hcur_pos, Nat.le_refl _, hconfl.toCut hs.2.1, rfl, Nat.le_refl _, rfl, hm⟩

/-- Canonical `Full.fullAnalyzeSpec` theorem for `FullM5HeurCore.full_analyze_m5_body` even
when `"full_min_shrink"` uses `M7` `m7MinShrinkSpec` (permitting `wsort` scratch mutation for
`16 < tmp_len`). `full_analyze_m5` never reads or relies on `wsort` across `full_min_shrink`. -/
theorem full_analyze_m5_m7_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m7MinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, Full.fullAnalyzeSpec args m Q X →
      Func.wp Γ full_analyze_m5_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs, hconfl, hm, hQ⟩
  exact full_analyze_m5_m7_core_wp Γ
    (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) False
    trivial (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ => trivial) (fun _ => trivial) (fun h => False.elim h) (fun _ _ => trivial)
    (fun _ => trivial)
    (fun a m Q X hs => hOneLit a m Q X (oneLit_unrestrict hs))
    (fun a m Q X hs => hDeduce a m Q X (deduce_unrestrict hs))
    hRestoreBump hMinShrink hTickRel hEma
    (fun a m Q X hs => hLearnCl a m Q X (learn_unrestrict hs))
    (c.hdr, ()) m Q X
    ⟨c, F0, F_cur, s, R, rfl, hs, hconfl, hm, fun r s' m' a1 _ a2 a3 a4 a5 a6 a7 a8 hm' =>
      hQ r s' m' a1 a2 a3 a4 a5 a6 a7 a8 hm'⟩

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvBrF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvBr_entails_1 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvBr_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvBr_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvBr_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvBr_marksClear : FullLitMarksClear nvOneLitCfg nvOneLitState :=
  ⟨fun v hv => by
      have hmv : nvOneLitCfg.max_vars = 1 := rfl
      rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl,
   fun l hl => by
      have hmv : nvOneLitCfg.max_vars = 1 := rfl
      rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl⟩

private theorem nvBr_nodup : FullArenaVarsNodup nvOneLitState := fun r hr => by
  have : fullArenaClauseRefs nvOneLitState = [] := rfl
  simp [this] at hr

private theorem nvBr_extOk : FullExtScratchOk nvOneLitCfg nvOneLitState :=
  ⟨FullLastLearnedWf.of_cleared fun i hi => by
    simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
      ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

private theorem nvBr_sparse :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState :=
  ⟨nvOneLit_lengths, nvBr_witness, nvBr_marksClear, nvBr_nodup, nvBr_extOk, rfl⟩

/-- Closed `12`-row concrete `SpecEntry` table wiring all Gap-B callees (with `m7SortTmpSpec`
and `m7MinShrinkSpec`) for non-vacuity checks. -/
def m7GapBNvTable : List SpecEntry :=
  [ ⟨"full_sort_tmp", [i64], [], m7SortTmpSpec, true⟩
  , ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩
  , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool], m6MinLitDfsSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool], m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], m7MinShrinkSpec, true⟩
  , ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_restore_bump_ana_m5", [i64], [], fullRestoreBumpAnaSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], m7MinShrinkSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩ ]

theorem m7GapBNvTable_nodup : (m7GapBNvTable.map SpecEntry.name).Nodup := by decide

private theorem nv_gapb_row {i : Nat} {e : SpecEntry} (hi : m7GapBNvTable[i]? = some e)
    (hX : ∀ xs m Q X, e.spec xs m Q X → ∀ X', e.spec xs m Q X') :
    ∀ xs m Q X', e.spec xs m Q X' →
      Env.ofTable m7GapBNvTable e.name e.as e.rs xs m Q X' :=
  fun xs m Q X' h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7GapBNvTable_nodup (hX xs m Q X' h _)

private theorem nv_arr_p {t : Ty} (a : BitVec 64) (xs : List (Val t)) (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf (t := t) xs).length = n ∧ array (t := t) a xs ((bytesOf (t := t) xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem nv_arr64_p (a : BitVec 64) (xs : List (BitVec 64)) (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem nv_pad_p (a : BitVec 64) (p : Nat) :
    (List.replicate p (0 : UInt8)).length = p ∧
      region a p ((List.replicate p (0 : UInt8)).At a) :=
  ⟨List.length_replicate .., ⟨List.replicate p 0, List.length_replicate .., rfl⟩⟩

private theorem nv_join_pair {a1 a2 : BitVec 64} {n1 n2 : Nat} {bs1 bs2 : List UInt8}
    {P Q : Mem 64 → Prop} (h1 : bs1.length = n1 ∧ P (bs1.At a1))
    (h2 : bs2.length = n2 ∧ Q (bs2.At a2))
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a1) := by
  have hl : bs1.length + bs2.length ≤ 2 ^ 64 := by rw [h1.1, h2.1]; exact hfit
  have heq : (Eq (bs1.At a1) ⋆ Eq (bs2.At (a1 + BitVec.ofNat 64 bs1.length)))
      ((bs1 ++ bs2).At a1) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a1 hl) ((bs1 ++ bs2).At a1)).mp rfl
  rw [h1.1, ← hadd] at heq
  exact ⟨by rw [List.length_append, h1.1, h2.1],
    sep_mono2 (fun _ hx => hx ▸ h1.2) (fun _ hy => hy ▸ h2.2) _ heq⟩

private theorem nv_arr_pad_p {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (n p : Nat) (hn : t.bytes * xs.length = n) (hbd : n + p ≤ 2 ^ 64) :
    (bytesOf (t := t) xs ++ List.replicate p (0 : UInt8)).length = n + p ∧
      (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) p)
        ((bytesOf (t := t) xs ++ List.replicate p (0 : UInt8)).At a) :=
  nv_join_pair (nv_arr_p a xs n hn (by omega))
    (nv_pad_p (a + BitVec.ofNat 64 n) p) rfl hbd

private theorem nv_sep_reorg {bs : List UInt8} {a : BitVec 64} {n : Nat}
    {P Q : Mem 64 → Prop} (h : bs.length = n ∧ P (bs.At a)) (hPQ : ∀ f, P f → Q f) :
    bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, hPQ _ h.2⟩

/-- `18`-variable `FullCfg` (`tmp_len = 18 > 16`) exercising `full_sort_tmp` (`m7SortTmpSpec`),
`full_min_mark`, `dfs`, `shrink_blk`, and `wsort` mutation in `nv_m7_min_shrink*`. -/
def nv18MinCfg : FullCfg :=
  { hdr := 0x1000#64
    avail := 4508
    mv := 18
    max_vars := 18
    bva_cap := 0
    nc := 1
    arena_cap := 0
    wcap := 1
    delayed_cap := 0
    red_cap := 0
    extend_cap := 0
    scratch_cap := 0
    hbva := rfl
    hmv := by decide
    hmaxv := by decide
    hnc := by decide
    harena := by decide
    hwcap := by decide
    hdel := by decide
    hred := by decide
    hext := by decide
    hscr := by decide
    havail_fit := by decide
    hsize := by decide }

def nv18MinVals : List (BitVec 8) :=
  [ 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8,
    1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8,
    1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8 ]

def nv18MinLvl : List (BitVec 32) :=
  [ 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32, 9#32,
    10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32, 18#32 ]

def nv18MinTrl : List (BitVec 32) :=
  [ 0#32, 2#32, 4#32, 6#32, 8#32, 10#32, 12#32, 14#32, 16#32,
    18#32, 20#32, 22#32, 24#32, 26#32, 28#32, 30#32, 32#32, 34#32 ]

def nv18MinTpos : List (BitVec 32) :=
  [ 0#32, 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32,
    9#32, 10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32 ]

def nv18MinFTrl : List (BitVec 32) :=
  [ 0#32, 0#32, 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32,
    9#32, 10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32 ]

def nv18MinFDec : List (BitVec 32) :=
  [ 0#32, 0#32, 2#32, 4#32, 6#32, 8#32, 10#32, 12#32, 14#32, 16#32,
    18#32, 20#32, 22#32, 24#32, 26#32, 28#32, 30#32, 32#32, 34#32 ]

def nv18MinTmp : List (BitVec 32) :=
  [ 35#32, 33#32, 31#32, 29#32, 27#32, 25#32, 23#32, 21#32, 19#32,
    17#32, 15#32, 13#32, 11#32, 9#32, 7#32, 5#32, 3#32, 1#32 ]

def nv18MinScratch : FullScratch :=
  { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
    rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
    learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := 0#64
    switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
    mode_saved_ticks := 0#64, search_ticks := 0#64, q_first := 0#64, q_last := 0#64
    q_search_idx := 0#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
    target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 0#64
    rephased := 0#64, reduce_limit := 0#64, reductions := 0#64, tier1 := 0#64
    tier2 := 0#64, restarts := 0#64, restart_limit := 0#64, ema_fast_biased := 0#64
    ema_fast_exp := 0#64, ema_slow_biased := 0#64, ema_slow_exp := 0#64, extend_len := 0
    rng_state := 0#64, chrono_levels := 0#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64
    probe_limit := 0#64, probings := 0#64, elim_limit := 0#64, eliminations := 0#64
    elim_bound := 0#64, iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64
    viv_cnt := 0#64, subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64
    bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64
    fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64
    walk_vals := List.replicate 36 0#8, phases := List.replicate 18 0#8
    phases_target := List.replicate 18 0#8, phases_best := List.replicate 18 0#8
    walk_best := List.replicate 18 0#8, heap := List.replicate 18 0#32
    pos := List.replicate 18 0#32, shrink_stk := List.replicate 18 0#32
    q_prev := List.replicate 18 0#32, q_next := List.replicate 18 0#32
    q_stamp := List.replicate 18 0#32, wsort := List.replicate 36 0#32
    work_stk1 := List.replicate 36 0#32, work_stk2 := List.replicate 36 0#32
    tarjan_mark := List.replicate 36 0#32, tarjan_reach := List.replicate 36 0#32
    score := List.replicate 18 0#64, sim_sig := List.replicate 18 0#64
    glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0#32
    delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] }

/-- `18`-variable state (`tmp_len = 18 > 16`, `cur_level = 18`) for non-bailout min/shrink NV. -/
def nv18MinState : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := 18, unassigned := 0#64
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64
        trail_end := 18, propagated := 0, cur_level := 18, fuel := 0#64
        confl_ref := 0#64, confl_type := 1#64, confl_lit0 := 1#64, confl_lit1 := 1#64
        tmp_cnt := 0, tmp_len := 18, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := nv18MinVals, lit_mark := List.replicate 36 0#8
        mrk := List.replicate 18 0#8, flags := List.replicate 18 0#32
        lvl := nv18MinLvl, rsns := List.replicate 18 0xFFFFFFFF#32
        trl := nv18MinTrl, trail_pos := nv18MinTpos
        tmp := nv18MinTmp, min_clr := List.replicate 18 0#32
        frame_trail := nv18MinFTrl, frame_dec := nv18MinFDec
        wvec := List.replicate 72 0#32, repr := List.replicate 36 0#32
        min_stk := List.replicate 38 0#32, arena := [], wstk := [0#32] }
    scratch := nv18MinScratch }

private def nv18BlkHdr : List UInt8 :=
  let c := nv18MinCfg; let s := nv18MinState
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nv18BlkBytes : List UInt8 :=
  let sc := nv18MinState.scratch; let k := nv18MinState.core
  (bytesOf (t := i8) k.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 6 0)

private def nv18BlkU32A : List UInt8 :=
  let k := nv18MinState.core
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nv18BlkU32B : List UInt8 :=
  let k := nv18MinState.core; let sc := nv18MinState.scratch
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nv18BlkU32C : List UInt8 :=
  let k := nv18MinState.core; let sc := nv18MinState.scratch
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nv18BlkWvec : List UInt8 :=
  let k := nv18MinState.core; let sc := nv18MinState.scratch
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++
  bytes64 sc.score ++ bytes64 sc.sim_sig

private def nv18BlkTail : List UInt8 :=
  let k := nv18MinState.core; let sc := nv18MinState.scratch
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

def nv18MinMem : Mem 64 :=
  (nv18BlkHdr ++ nv18BlkBytes ++ nv18BlkU32A ++ nv18BlkU32B ++
    nv18BlkU32C ++ nv18BlkWvec ++ nv18BlkTail).At nv18MinCfg.hdr

private theorem nv18Min_lengths : nv18MinState.LengthsOk nv18MinCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nv18MinMem_ok : (FullMem nv18MinCfg nv18MinState ⋆ emp) nv18MinMem := by
  let c := nv18MinCfg; let s := nv18MinState
  have hv4 : valsBytes c.max_vars - 2 * c.max_vars = 4 := by decide
  have h2m : 2 * c.max_vars = 36 := by decide
  have hm6 : markBytes c.max_vars - c.max_vars = 6 := by decide
  have hm18 : c.max_vars = 18 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 72 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 76 := by decide
  have hsl : c.slack = 0 := by decide
  have hHdr : nv18BlkHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s)) (nv18BlkHdr.At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (c.hdr + 32) (Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by decide)
  have hBytes : nv18BlkBytes.length = 240 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes) (nv18BlkBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) c.pVals s.core.vals 36 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) c.pWalkVals s.scratch.walk_vals 36 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i8) c.pLitMark s.core.lit_mark 36 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i8) c.pMark s.core.mrk 18 6 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) c.pPhases s.scratch.phases 18 6 rfl (by decide)
    have h6 := nv_arr_pad_p (t := i8) c.pPhasesTarget s.scratch.phases_target 18 6 rfl
      (by decide)
    have h7 := nv_arr_pad_p (t := i8) c.pPhasesBest s.scratch.phases_best 18 6 rfl (by decide)
    have h8 := nv_arr_pad_p (t := i8) c.pWalkBest s.scratch.walk_best 18 6 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234567 h8 (by decide) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hv4, h2m, hm6, hm18]; exact pB hm
  have hU32A : nv18BlkU32A.length = 400 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nv18BlkU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) c.pFlags s.core.flags 72 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) c.pLevel s.core.lvl 72 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) c.pReason s.core.rsns 72 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) c.pTrail s.core.trl 72 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) c.pTrailPos s.core.trail_pos 72 8 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : nv18BlkU32B.length = 400 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nv18BlkU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) c.pTmp s.core.tmp 72 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) c.pHeap s.scratch.heap 72 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) c.pPos s.scratch.pos 72 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) c.pMinClr s.core.min_clr 72 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) c.pShrinkStk s.scratch.shrink_stk 72 8 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : nv18BlkU32C.length = 400 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nv18BlkU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) c.pQPrev s.scratch.q_prev 72 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) c.pQNext s.scratch.q_next 72 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) c.pQStamp s.scratch.q_stamp 72 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) c.pFrameTrail s.core.frame_trail 76 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) c.pFrameDec s.core.frame_dec 76 4 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : nv18BlkWvec.length = 1440 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nv18BlkWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) c.pWvec s.core.wvec 288 rfl (by decide)
    have h2 := nv_arr_p (t := i32) c.pRepr s.core.repr 144 rfl (by decide)
    have h3 := nv_arr_p (t := i32) c.pWsort s.scratch.wsort 144 rfl (by decide)
    have h4 := nv_arr_p (t := i32) c.pWorkStk1 s.scratch.work_stk1 144 rfl (by decide)
    have h5 := nv_arr_p (t := i32) c.pWorkStk2 s.scratch.work_stk2 144 rfl (by decide)
    have h6 := nv_arr_p (t := i32) c.pTarjanMark s.scratch.tarjan_mark 144 rfl (by decide)
    have h7 := nv_arr_p (t := i32) c.pTarjanReach s.scratch.tarjan_reach 144 rfl (by decide)
    have h8 := nv_arr64_p c.pScore s.scratch.score 144 rfl (by decide)
    have h9 := nv_arr64_p c.pSimSig s.scratch.sim_sig 144 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := nv_join_pair j1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nv18BlkTail.length = 476 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nv18BlkTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) c.pMinStk s.core.min_stk 152 rfl (by decide)
    have h2 := nv_arr_p (t := i32) c.pGlueUsed s.scratch.glue_used 256 rfl (by decide)
    have h3 := nv_arr_p (t := i32) c.pLastLearned s.scratch.last_learned 64 rfl (by decide)
    have h4 := nv_arr_p (t := i32) c.pArena s.core.arena 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) c.pWstk s.core.wstk 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) c.pDelayed s.scratch.delayed 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) c.pRedRefs s.scratch.red_refs 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) c.pExtendStk s.scratch.extend_stk 0 rfl (by decide)
    have h9 := nv_arr_p (t := i32) c.pScratchBuf s.scratch.scratch_buf 0 rfl (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      rw [hsl]; exact nv_pad_p c.pSlack 0
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := nv_join_pair j1234567 h8 (by decide) (by decide)
    have j123456789 := nv_join_pair j12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_sep_reorg (nv_join_pair h02 hU32B (by decide) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := nv_sep_reorg (nv_join_pair h03 hU32C (by decide) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆
          ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k :=
      fun x => sep_ac x
    exact p2 hm
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  have h06 : (nv18BlkHdr ++ nv18BlkBytes ++ nv18BlkU32A ++ nv18BlkU32B ++
      nv18BlkU32C ++ nv18BlkWvec ++ nv18BlkTail).length = 4508 ∧
      FullMem c s ((nv18BlkHdr ++ nv18BlkBytes ++ nv18BlkU32A ++ nv18BlkU32B ++
        nv18BlkU32C ++ nv18BlkWvec ++ nv18BlkTail).At c.hdr) := by
    refine nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => ?_
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆
          (P2 ⋆ SL)) k :=
      fun x => sep_ac x
    have p4 : ∀ {D H CB UA_T_Mc FTr FDec Wv Re MS CD Scr Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ (((CB ⋆ UA_T_Mc ⋆ FTr ⋆ FDec) ⋆ Wv ⋆ Re ⋆ MS ⋆ CD)) ⋆ Scr ⋆ Pad) k →
        (D ⋆ H ⋆ (CB ⋆ UA_T_Mc ⋆ (FTr ⋆ FDec ⋆ Wv ⋆ Re ⋆ MS) ⋆ CD) ⋆ Scr ⋆ Pad) k :=
      fun x => sep_ac x
    have p5 : ∀ {D H Core SB HpPsSh QpQnQs SW Sc Ss Gu Ll SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (((SB ⋆ HpPsSh) ⋆ QpQnQs) ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (HpPsSh ⋆ QpQnQs) ⋆ SW ⋆ (Sc ⋆ Ss ⋆ Gu ⋆ Ll) ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    have p6 : ∀ {D H Core Scr PB PA PB2 PC SL : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (((PB ⋆ PA ⋆ PB2) ⋆ PC) ⋆ SL)) k →
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) k :=
      fun x => sep_ac x
    have p7 : ∀ {D H Core SB Hp Ps Sh Qp Qn Qs SW Meta SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ ((Hp ⋆ Ps ⋆ Sh) ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B
      FullScratchArrays FullScrU32A FullScrMetaArrs FullCfg.pad
    exact p7 (p6 (p5 (p4 (p3 hm))))
  rw [sep_emp]
  exact h06.2

private theorem nv18Min_witness :
    FullWitnessInv nv18MinCfg nvOneLitF0 [[0], [1]] nv18MinState.core := by
  have hrefs : fullArenaClauseRefsCore nv18MinState.core = [] := rfl
  have hcv : nv18MinState.core.cur_vars = 18 := rfl
  have hte : nv18MinState.core.trail_end = 18 := rfl
  have hcl : nv18MinState.core.cur_level = 18 := rfl
  have hdm : nv18MinState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nv18MinState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices
      (fun l hl => (by decide : ∀ q : Fin 36,
        fullWatchOffCore nv18MinState.core q.1 + fullWatchSizeCore nv18MinState.core q.1 ≤
          nv18MinState.core.wlen) ⟨l, by omega⟩)
      (fun l hl hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nv18MinState.core q.1 = 0) ⟨l, by omega⟩
        dsimp only at hz; omega))
      (fun l1 _ h1 _ _ hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nv18MinState.core q.1 = 0) ⟨l1, by omega⟩
        dsimp only at hz; omega))
      (fun l hl => by
        have hws : fullWatchSizeCore nv18MinState.core l = 0 := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nv18MinState.core q.1 = 0) ⟨l, by omega⟩
        have hwo : fullWatchOffCore nv18MinState.core l = 0 := (by decide : ∀ q : Fin 36,
          fullWatchOffCore nv18MinState.core q.1 = 0) ⟨l, by omega⟩
        rw [hwo, hws]; exact WatchSliceOk.empty)
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 18 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.le_refl _
      trail_lits_lt := fun i hi => (by decide : ∀ q : Fin 18,
        (nv18MinState.core.trl[q.1]?.getD 0#32).toNat < 36) ⟨i, by omega⟩
      trail_vars_nodup := fun i j hi hj heq => congrArg Fin.val ((by decide : ∀ a b : Fin 18,
        (nv18MinState.core.trl[a.1]?.getD 0#32).toNat / 2 =
        (nv18MinState.core.trl[b.1]?.getD 0#32).toNat / 2 → a = b) ⟨i, by omega⟩ ⟨j, by omega⟩ heq)
      vals_domain := fun l hl => (by decide : ∀ q : Fin 36,
        let v := nv18MinState.core.vals[q.1]?.getD 0#8
        v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) ⟨l, by omega⟩
      vals_true_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 36,
            nv18MinState.core.vals[q.1]?.getD 0#8 = 1#8 →
            q.1 / 2 < 18 ∧ (nv18MinState.core.trl[q.1 / 2]?.getD 0#32).toNat = q.1)
            ⟨l, by omega⟩ hv
          exact ⟨l / 2, by omega, hc.2⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 18,
            nv18MinState.core.vals[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat]?.getD 0#8 =
              1#8) ⟨i, by omega⟩
          rw [← htr]; exact hc
      vals_false_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 36,
            nv18MinState.core.vals[q.1]?.getD 0#8 = 0xFF#8 →
            q.1 / 2 < 18 ∧ (nv18MinState.core.trl[q.1 / 2]?.getD 0#32).toNat = q.1 ^^^ 1)
            ⟨l, by omega⟩ hv
          exact ⟨l / 2, by omega, hc.2⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 18,
            nv18MinState.core.vals[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat ^^^ 1]?.getD
              0#8 = 0xFF#8) ⟨i, by omega⟩
          have hl1 : l < 36 := by omega
          have hl_eq : l = (nv18MinState.core.trl[i]?.getD 0#32).toNat ^^^ 1 := by
            rw [htr, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          rw [hl_eq]; exact hc
      lvl_le := fun i hi => (by decide : ∀ q : Fin 18,
        (nv18MinState.core.lvl[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≤ 18) ⟨i, by omega⟩
      dec_earliest := fun i j hi hj hlv _ => by
        have heq := (by decide : ∀ a b : Fin 18,
          (nv18MinState.core.lvl[(nv18MinState.core.trl[a.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat =
          (nv18MinState.core.lvl[(nv18MinState.core.trl[b.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat → a.1 = b.1) ⟨i, by omega⟩ ⟨j, by omega⟩ hlv
        dsimp only at heq; omega
      levels_inhabited := fun L h1 h2 =>
        ⟨L - 1, by omega, (by decide : ∀ q : Fin 19, 1 ≤ q.1 → q.1 ≤ 18 →
          (nv18MinState.core.lvl[(nv18MinState.core.trl[q.1 - 1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat = q.1) ⟨L, by omega⟩ h1 (by omega)⟩
      level0_sound := fun i hi hlv => absurd hlv ((by decide : ∀ q : Fin 18,
        (nv18MinState.core.lvl[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≠ 0) ⟨i, by omega⟩)
      trail_pos_inv := fun i hi => (by decide : ∀ q : Fin 18,
        (nv18MinState.core.trail_pos[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat = q.1) ⟨i, by omega⟩
      level0_rsn_none := fun i hi _ => (by decide : ∀ q : Fin 18,
        nv18MinState.core.rsns[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩
      frame_trail_lt := fun L hL => (by decide : ∀ q : Fin 19,
        (nv18MinState.core.frame_trail[q.1]?.getD 0#32).toNat ≤ 18) ⟨L, by omega⟩
      frame_trail_mono := fun L1 L2 h12 hL2 => (by decide : ∀ a b : Fin 19, a.1 ≤ b.1 →
        (nv18MinState.core.frame_trail[a.1]?.getD 0#32).toNat ≤
        (nv18MinState.core.frame_trail[b.1]?.getD 0#32).toNat) ⟨L1, by omega⟩ ⟨L2, by omega⟩ h12
      frame_trail_before_lt := fun L h1 h2 i hi =>
        (by decide : ∀ q : Fin 19, 1 ≤ q.1 → ∀ j : Fin 18,
          j.1 < (nv18MinState.core.frame_trail[q.1]?.getD 0#32).toNat →
          (nv18MinState.core.lvl[(nv18MinState.core.trl[j.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat < q.1)
          ⟨L, by omega⟩ h1 ⟨i, by
            have hb := (by decide : ∀ q : Fin 19,
              (nv18MinState.core.frame_trail[q.1]?.getD 0#32).toNat ≤ 18) ⟨L, by omega⟩
            dsimp only at hb; omega⟩ hi
      frame_dec_lt := fun L h1 h2 => (by decide : ∀ q : Fin 19, 1 ≤ q.1 →
        (nv18MinState.core.frame_dec[q.1]?.getD 0#32).toNat < 36) ⟨L, by omega⟩ h1
      reason_inv := fun i hi hne => absurd ((by decide : ∀ q : Fin 18,
        nv18MinState.core.rsns[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩) hne
      reason_lit_mem := fun i hi hne => absurd ((by decide : ∀ q : Fin 18,
        nv18MinState.core.rsns[(nv18MinState.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩) hne }

private theorem nv18Min_marksClear : FullLitMarksClear nv18MinCfg nv18MinState :=
  ⟨fun v hv => (by decide : ∀ q : Fin 18, nv18MinState.core.mrk[q.1]?.getD 0#8 = 0#8) ⟨v, hv⟩,
   fun l hl =>
     (by decide : ∀ q : Fin 36, nv18MinState.core.lit_mark[q.1]?.getD 0#8 = 0#8) ⟨l, hl⟩⟩

private theorem nv18Min_spec_inst {X : XPost} :
    m7MinShrinkSpec (nv18MinCfg.hdr, ()) nv18MinMem
      (fun () m' => ∃ s' : FullState, s'.LengthsOk nv18MinCfg ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ nvOneLitF0.Unsat ∧ FullMem nv18MinCfg s' m')
      X := by
  have hent : (cnfOfClauses [[0], [1]]).EntailsClause
      (cnfClause ((nv18MinState.core.tmp.take nv18MinState.core.tmp_len).map BitVec.toNat)) := by
    rw [CNF.entails_clause_def]; intro α hα; exfalso
    exact CNF.unsat_iff_not_sat.mp nvBrF0_unsat α (by simpa [nvOneLitF0] using hα)
  refine m7MinShrinkSpec_of nv18Min_lengths nv18Min_witness.toOtfs nv18Min_marksClear
    (by decide) (by decide) (by decide) hent
    (fun k hk => (by decide : ∀ q : Fin 18,
      let l := (nv18MinState.core.tmp[q.1]?.getD 0#32).toNat
      l < 36 ∧ nv18MinState.core.vals[l]?.getD 0#8 = 0xFF#8) ⟨k, hk⟩)
    (fun k hk1 hk2 => (by decide : ∀ q : Fin 18, 1 ≤ q.1 →
      let lv := (nv18MinState.core.lvl[(nv18MinState.core.tmp[q.1]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat
      0 < lv ∧ lv < 18) ⟨k, hk2⟩ hk1)
    rfl nv18MinMem_ok ?_
  intro tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' wsort' m' _
    hlen' _ _ h1' hle' h0' _ _ _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨_, hlen', h1', hle', h0', nvBrF0_unsat, hm'⟩

/-- Concrete `Mem 64` non-bailout UNSAT NV (`tmp_len = 18 > 16`, exercising `full_sort_tmp`
`m7SortTmpSpec`, `wsort` mutation, `full_min_mark`, `dfs`, `shrink_blk`, `XPost := False`) for
`full_min_shrink_m6_m7sort_wp`. -/
theorem nv_m7_min_shrink_m6 :
    Func.wp (Env.ofTable m7GapBNvTable) full_min_shrink_m6_body
      (nv18MinCfg.hdr, ()) nv18MinMem
      (fun () m' => ∃ s' : FullState, s'.LengthsOk nv18MinCfg ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ nvOneLitF0.Unsat ∧ FullMem nv18MinCfg s' m')
      (fun _ _ _ _ => False) :=
  full_min_shrink_m6_m7sort_wp (Env.ofTable m7GapBNvTable)
    (nv_gapb_row (i := 0) rfl fun _ _ _ _ h _ => m7SortTmpSpec_monoX h)
    (nv_gapb_row (i := 1) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 2) rfl fun _ _ _ _ h _ => m6MinLitDfsSpec_monoX h)
    (nv_gapb_row (i := 3) rfl fun _ _ _ _ h _ => m6ShrinkBlkBoolSpec_monoX h)
    _ _ _ _ nv18Min_spec_inst

/-- Concrete `Mem 64` non-bailout UNSAT NV (`tmp_len = 18 > 16`, `XPost := False`) for
`full_min_shrink_m7_wp`. -/
theorem nv_m7_min_shrink :
    Func.wp (Env.ofTable m7GapBNvTable) FullM6Orch.full_min_shrink_body
      (nv18MinCfg.hdr, ()) nv18MinMem
      (fun () m' => ∃ s' : FullState, s'.LengthsOk nv18MinCfg ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ nvOneLitF0.Unsat ∧ FullMem nv18MinCfg s' m')
      (fun _ _ _ _ => False) :=
  full_min_shrink_m7_wp (Env.ofTable m7GapBNvTable)
    (nv_gapb_row (i := 4) rfl fun _ _ _ _ h _ => m7MinShrinkSpec_monoX h)
    _ _ _ _ nv18Min_spec_inst

/-- Non-bailout `cur_level = 1` state on `nvOneLitCfg` for `full_analyze_m5` NV. -/
def nvAnalyzeState : FullState :=
  { nvOneLitState with core := { nvOneLitState.core with cur_level := 1, lvl := [1#32] } }

def nvAnalyzeMem : Mem 64 :=
  storeMem (storeMem nvOneLitMem i64 (nvOneLitCfg.hdr + 160) 1#64) i32 nvOneLitCfg.pLevel 1#32

private theorem nvAnalyze_lengths : nvAnalyzeState.LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with lvl_len := rfl }, nvOneLit_lengths.scratch_ok⟩

private theorem nvAnalyzeMem_ok : (FullMem nvOneLitCfg nvAnalyzeState ⋆ emp) nvAnalyzeMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have h1 := (store_full_cur_level (c := nvOneLitCfg) 1 (by decide) hm0).2
  have h2 := (store_full_lvl (c := nvOneLitCfg) (i := 0) 1#32 (by decide) h1).2
  simpa [nvAnalyzeMem, nvAnalyzeState, nvOneLitState] using h2

private theorem nvAnalyze_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvAnalyzeState.core := by
  have hrefs : fullArenaClauseRefsCore nvAnalyzeState.core = [] := rfl
  have hcv : nvAnalyzeState.core.cur_vars = 1 := rfl
  have hte : nvAnalyzeState.core.trail_end = 1 := rfl
  have hcl : nvAnalyzeState.core.cur_level = 1 := rfl
  have hdm : nvAnalyzeState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvAnalyzeState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvAnalyzeState, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvAnalyzeState, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.le_refl 1
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvAnalyzeState, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 1
      dec_earliest := fun i j hi hj _ _ => by rw [hte] at hi hj; omega
      levels_inhabited := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega); exact ⟨0, Nat.zero_lt_one, rfl⟩
      level0_sound := fun i hi hlv => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases hlv
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi hlv => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases hlv
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; rcases (by omega : L = 0 ∨ L = 1) with rfl | rfl <;> decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2
        rcases (by omega : L1 = 0 ∨ L1 = 1) with rfl | rfl <;>
          rcases (by omega : L2 = 0 ∨ L2 = 1) with rfl | rfl <;> first | exact Nat.le_refl _ | omega
      frame_trail_before_lt := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega); decide
      frame_dec_lt := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega); decide
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvAnalyze_sparse :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvAnalyzeState :=
  ⟨nvAnalyze_lengths, nvAnalyze_witness, nvBr_marksClear, nvBr_nodup, nvBr_extOk, rfl⟩

/-- Non-bailout `7`-row callee table forcing `full_analyze_m5` through `full_one_lit_confl`
(`0#64`), `full_deduce_1uip` (`1#64`), `full_min_shrink` (`m7MinShrinkSpec`), `restore_bump`,
`tick_rel`, `ema_update`, and `full_learn_clause` (`20#64`). -/
def m7GapBNvAnaTable : List SpecEntry :=
  [ ⟨"full_one_lit_confl", [i64], [i64], restrictOneLitSpec (· = 0#64), true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], restrictDeduceSpec (· = 1#64), true⟩
  , ⟨"full_restore_bump_ana_m5", [i64], [], fullRestoreBumpAnaSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], m7MinShrinkSpec, true⟩
  , ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], restrictLearnSpec (· = 20#64), true⟩ ]

theorem m7GapBNvAnaTable_nodup : (m7GapBNvAnaTable.map SpecEntry.name).Nodup := by decide

private theorem nv_gapb_ana_row {i : Nat} {e : SpecEntry} (hi : m7GapBNvAnaTable[i]? = some e)
    (hX : ∀ xs m Q X, e.spec xs m Q X → ∀ X', e.spec xs m Q X') :
    ∀ xs m Q X', e.spec xs m Q X' →
      Env.ofTable m7GapBNvAnaTable e.name e.as e.rs xs m Q X' :=
  fun xs m Q X' h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7GapBNvAnaTable_nodup (hX xs m Q X' h _)

/-- Concrete non-bailout `Mem 64` UNSAT NV (`cur_level = 1`, deterministic `r = 20#64`, exercising
`m7MinShrinkSpec` on `"full_min_shrink"` and all `7` callees, `XPost := False`). -/
theorem nv_m7_analyze :
    Func.wp (Env.ofTable m7GapBNvAnaTable) full_analyze_m5_body
      (nvOneLitCfg.hdr, ()) nvAnalyzeMem
      (fun (r, ()) m' => ∃ s' : FullState, r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  refine full_analyze_m5_m7_core_wp (Env.ofTable m7GapBNvAnaTable)
    (· = 0#64) (· = 1#64) (· = 20#64) (· = 20#64) True
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ h => h) (fun h => absurd trivial h)
    (nv_gapb_ana_row (i := 0) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_ana_row (i := 1) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_ana_row (i := 2) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_ana_row (i := 3) rfl fun _ _ _ _ h _ => m7MinShrinkSpec_monoX h)
    (nv_gapb_ana_row (i := 4) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_ana_row (i := 5) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_ana_row (i := 6) rfl fun _ _ _ _ h _ => h)
    (nvOneLitCfg.hdr, ()) nvAnalyzeMem _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvAnalyzeState, emp, rfl, nvAnalyze_sparse,
      Or.inl ⟨rfl, by decide, by decide, rfl, rfl,
        entails_of_mem_or_false nvBr_entails_1 fun _ hl => by
          simp only [List.mem_singleton] at hl; subst hl
          exact Or.inl (by dsimp [nvAnalyzeState, nvOneLitState]; exact List.mem_cons_self)⟩,
      nvAnalyzeMem_ok,
      fun r s' m' _ hr _ _ _ _ hu _ _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', hr, hu hr, hm'⟩⟩

/-- Direct instantiation of exported `full_analyze_m5_m7_wp` at `cur_level = 1` (`nvAnalyzeMem`). -/
theorem nv_m7_analyze_wp :
    Func.wp (Env.ofTable m7GapBNvTable) full_analyze_m5_body
      (nvOneLitCfg.hdr, ()) nvAnalyzeMem
      (fun (r, ()) m' => ∃ s' : FullState, (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  refine full_analyze_m5_m7_wp (Env.ofTable m7GapBNvTable)
    (nv_gapb_row (i := 5) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 6) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 7) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 8) rfl fun _ _ _ _ h _ => m7MinShrinkSpec_monoX h)
    (nv_gapb_row (i := 9) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 10) rfl fun _ _ _ _ h _ => h)
    (nv_gapb_row (i := 11) rfl fun _ _ _ _ h _ => h)
    (nvOneLitCfg.hdr, ()) nvAnalyzeMem _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvAnalyzeState, emp, rfl, nvAnalyze_sparse,
      Or.inl ⟨rfl, by decide, by decide, rfl, rfl,
        entails_of_mem_or_false nvBr_entails_1 fun _ hl => by
          simp only [List.mem_singleton] at hl; subst hl
          exact Or.inl (by dsimp [nvAnalyzeState, nvOneLitState]; exact List.mem_cons_self)⟩,
      nvAnalyzeMem_ok,
      fun r s' m' _ hr _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', hr, nvBrF0_unsat, hm'⟩⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7SpecBridges
