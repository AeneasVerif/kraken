module

public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat M5 Wave 1 (`PR-W1A`) `Func.wp` Proofs — Part 0 (`FullM5HeurCoreProof0`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for the first
`6` functions of `FullM5HeurCore`:
1. `full_save_target_best_m5_wp` against canonical `Full.fullSaveTargetBestSpec` (`RC-12`).
2. `fullBacktrackRawSpec` + `full_backtrack_raw_m5_wp` (`rfl`-bridged from
   `FullIngestLemmas2.full_backtrack_wp`).
3. `full_backtrack_m5_wp` against canonical `Full.fullBacktrackSpec` (`RC-12`).
4. `full_warmup_m5_wp` against canonical `Full.fullWarmupSpec` (`RC-12`).
5. `full_analyze_rsn_m5_wp` against canonical `Full.fullAnalyzeRsnSpec` (`RC-09`).
6. `full_otfs_subsume_m5_wp` against canonical `Full.fullOtfsSubsumeSpec` (`RC-09`).
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullM5HeurCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `full_save_target_best_m5` (`Full.fullSaveTargetBestSpec`) -/

section SaveTargetBestProof

open scoped FullArenaTactics FullHeurWalkTactics
open FullBridgeHelpers

/-- Zero-guarded `full_save_target_best_m5` satisfies canonical `Full.fullSaveTargetBestSpec`. -/
theorem full_save_target_best_m5_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Func.wp Γ full_save_target_best_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le; obtain hvl := hok.vals_len
  c0_to_group
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧
        (∃ ta' ba' pt' pb', s1.scratch = { s.scratch with
          target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb' }) ∧
        (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, ⟨ta1, ba1, pt1, pb1, hsc1⟩, hm1⟩ => ?_) ?_
    · rw [Blocks.get_here]
      have hceq1 : s1.core = s.core := hcore1
      obtain hsok1 := hlen1.scratch_ok; obtain hpbl1 := hsok1.phases_best_len
      c0_clean; c0_steps
      · refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s1 R
          (fun s2 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s1 s2 ∧
            ∃ ba' pb', s2.scratch = { s1.scratch with best_assigned := ba', phases_best := pb' })
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s2 (k, ()) m2 hcore2 hlen2 ⟨hk2, hpres2, ba2, pb2, hsc2⟩ hm2 hLoop2 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_
            ⟨by simp, probePres_refl s1, _, s1.scratch.phases_best, rfl⟩
          exact hlen_upd_phases hlen1 hsok1.phases_target_len hpbl1
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
          have hceq2 : s2.core = s1.core := hcore2
          obtain hsok2 := hlen2.scratch_ok; obtain hpbl2 := hsok2.phases_best_len
          c0_clean; c0_steps
          · have hk_lt : k.toNat < s.core.cur_vars := by
              have h1 : k.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                rw [hceq2, hceq1] at *; c0_bound
              rw [bv64_ofNat_toNat (by omega)] at h1; exact h1
            have hk2_lt : (k <<< (1 : Nat)).toNat < s2.core.vals.length := by
              have hsh : (k <<< (1 : Nat)).toNat = 2 * k.toNat := by c0_bound
              rw [hsh, hceq2, hceq1, hvl]; omega
            have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
            c0_clean; c0_steps
            · refine hLoop2 _ (k + 1, ()) m hm (by dsimp only; omega) rfl ?_
                ⟨by dsimp only; omega, hpres2, ba2, _, by dsimp only; rw [hsc2]⟩
              exact hlen_upd_phases hlen2 hsok2.phases_target_len (by simp [hpbl2])
            · exact hLoop2 _ (k + 1, ()) m2 hm2 (by dsimp only; omega) rfl hlen2
                ⟨by dsimp only; omega, hpres2, ba2, pb2, hsc2⟩
          · exact hQ () s2 m2 (hcore1.trans hcore2) hlen2
              ⟨probePres_trans hpres1 hpres2, ta1, ba2, pt1, pb2, by rw [hsc2, hsc1]⟩ hm2
      · exact hQ () s1 m1 hcore1 hlen1 ⟨hpres1, ta1, ba1, pt1, pb1, hsc1⟩ hm1
    · intro J1 hJ1; c0_steps
      · obtain hsok := hlen.scratch_ok; obtain hptl := hsok.phases_target_len
        refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
          (fun s1 (k, ()) => k.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1 ∧
            ∃ ta' pt', s1.scratch = { s.scratch with target_assigned := ta', phases_target := pt' })
          (fun (k, ()) => s.core.cur_vars - k.toNat)
          (fun J hLoop => ?_)
          (fun J s1 (k, ()) m1 hcore1 hlen1 ⟨hk1, hpres1, ta1, pt1, hsc1⟩ hm1 hLoop1 => ?_)
        · c0_steps
          refine hLoop _ (0#64, ()) m hm rfl ?_
            ⟨by simp, probePres_refl s, _, s.scratch.phases_target, rfl⟩
          exact hlen_upd_phases hlen hptl hsok.phases_best_len
        · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
          have hceq1 : s1.core = s.core := hcore1
          obtain hsok1 := hlen1.scratch_ok; obtain hptl1 := hsok1.phases_target_len
          c0_clean; c0_steps
          · have hk_lt : k.toNat < s.core.cur_vars := by
              have h1 : k.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                rw [hceq1] at *; c0_bound
              rw [bv64_ofNat_toNat (by omega)] at h1; exact h1
            have hk2_lt : (k <<< (1 : Nat)).toNat < s1.core.vals.length := by
              have hsh : (k <<< (1 : Nat)).toNat = 2 * k.toNat := by c0_bound
              rw [hsh, hceq1, hvl]; omega
            have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
            c0_clean; c0_steps
            · refine hLoop1 _ (k + 1, ()) m hm (by dsimp only; omega) rfl ?_
                ⟨by dsimp only; omega, hpres1, ta1, _, by dsimp only; rw [hsc1]⟩
              exact hlen_upd_phases hlen1 (by simp [hptl1]) hsok1.phases_best_len
            · exact hLoop1 _ (k + 1, ()) m1 hm1 (by dsimp only; omega) rfl hlen1
                ⟨by dsimp only; omega, hpres1, ta1, pt1, hsc1⟩
          · exact hJ1 () m1 ⟨s1, hcore1, hlen1, hpres1,
              ⟨ta1, s.scratch.best_assigned, pt1, s.scratch.phases_best, hsc1⟩, hm1⟩
      · exact hJ1 () m ⟨s, rfl, hlen, probePres_refl s,
          ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
            s.scratch.phases_best, rfl⟩, hm⟩

end SaveTargetBestProof

/-! ## 2. `full_backtrack_raw_m5` & `full_backtrack_m5` (`Full.fullBacktrackSpec`) -/

/-- Internal backtrack helper contract: identical to canonical `Full.fullBacktrackSpec` plus
pointwise preservation of `lvl[v]` for all variables with `lvl[v] ≤ target_lvl` (needed for
composing 1-level unwind + target/best phase save + remaining unwind in `full_backtrack_m5`). -/
@[expose] def fullBacktrackRawSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc' = { s.scratch with
        target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
        heap := hp', pos := ps', heap_len := hl',
        q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ v < s.core.cur_vars, (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
        lvl'[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
          if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 = if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

section BacktrackProof

open scoped FullArenaTactics FullIngestTactics
open FullBridgeHelpers

private theorem m5_canonOtfs_to_ingest {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullIngestSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m5_backtrack_raw_body_eq :
    full_backtrack_raw_m5_body = Full.full_backtrack_body := rfl

/-- `full_backtrack_raw_m5` satisfies `fullBacktrackRawSpec` via `Full.full_backtrack_wp`. -/
theorem full_backtrack_raw_m5_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Func.wp Γ full_backtrack_raw_m5_body a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  rw [m5_backtrack_raw_body_eq]
  refine full_backtrack_wp Γ
    (fun a' m' Q' X' ⟨c', s', R', hh', hl', hm', hQ'⟩ =>
      hSave a' m' Q' X' ⟨c', s', R', hh', hl', hm', fun r' s'' m'' hc' hl'' hp' hm'' =>
        hQ' r' s'' m'' hc' hl''
          ⟨⟨hp'.1.1, hp'.1.2.1, hp'.1.2.2.1, hp'.1.2.2.2.1, hp'.1.2.2.2.2.1, hp'.1.2.2.2.2.2.1,
            hp'.1.2.2.2.2.2.2.1, hp'.1.2.2.2.2.2.2.2⟩, hp'.2⟩ hm''⟩)
    (fun a' m' Q' X' ⟨c', s', R', hh', hl', hm', hQ'⟩ =>
      hHeapPush a' m' Q' X' ⟨c', s', R', hh', hl', hm', fun r' s'' m'' hc' hl'' hp' hm'' =>
        hQ' r' s'' m'' hc' hl''
          ⟨⟨hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2.1, hp'.2.2.2.2.1, hp'.2.2.2.2.2.1,
            hp'.2.2.2.2.2.2.1, hp'.2.2.2.2.2.2.2.1⟩, hp'.2.2.2.2.2.2.2.2⟩ hm''⟩)
    _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, ?_⟩
  dsimp only
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hprop hcl hfr htrl' _ hlvl_low hclr hw_w hw_o hm'
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hprop hcl hfr.1 hfr.2 htrl' hlvl_low
    (fun ⟨F0, Fc, hw⟩ => hclr ⟨F0, Fc, hw.elim Or.inl (Or.inr ∘ m5_canonOtfs_to_ingest)⟩)
    hw_w (fun F0 Fc ho => hw_o F0 Fc (m5_canonOtfs_to_ingest ho)) hm'

private theorem m5_witness_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (p : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hw.cur_level_le
    trail_lits_lt := hw.trail_lits_lt, trail_vars_nodup := hw.trail_vars_nodup
    vals_domain := hw.vals_domain, vals_true_iff := hw.vals_true_iff
    vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt
    reason_inv := hw.reason_inv, reason_lit_mem := hw.reason_lit_mem }

private theorem m5_otfs_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (p : BitVec 64) :
    FullOtfsWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hw.cur_level_le
    trail_lits_lt := hw.trail_lits_lt, trail_vars_nodup := hw.trail_vars_nodup
    vals_domain := hw.vals_domain, vals_true_iff := hw.vals_true_iff
    vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt
    reason_inv_below := hw.reason_inv_below, reason_lit_mem_below := hw.reason_lit_mem_below }

private theorem m5_lengths_with_probing {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (p : BitVec 64) :
    ({ s with core := { s.core with probing := p } } : FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with cur_vars_le := hlen.core_ok.cur_vars_le }, hlen.scratch_ok⟩

private theorem m5_bt_noop_clear {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {tgt : Nat} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (hle : k.cur_level ≤ tgt) :
    (∀ l < 2 * k.cur_vars, k.vals[l]?.getD 0#8 =
      if (k.lvl[l / 2]?.getD 0#32).toNat ≤ tgt then k.vals[l]?.getD 0#8 else 0#8) ∧
    (∀ i < k.trail_end, let v := (k.trl[i]?.getD 0#32).toNat / 2
      k.lvl[v]?.getD 0#32 =
        if (k.lvl[v]?.getD 0#32).toNat ≤ tgt then k.lvl[v]?.getD 0#32 else 0#32) := by
  refine ⟨fun l hl => ?_, fun i hi => ?_⟩
  · rcases hw.vals_domain l hl with hv | hv | hv
    · rw [hv]; split <;> rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp hv
      have hli := hw.lvl_le i hi
      rw [heq] at hli; rw [ite_eq_left (by omega)]
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hv
      have hli := hw.lvl_le i hi
      rw [heq, fullInv_var_xor1] at hli; rw [ite_eq_left (by omega)]
  · have hli := hw.lvl_le i hi
    dsimp only; rw [ite_eq_left (by omega)]

private theorem m5_bt_scr_trans {sc sc1 sc2 : FullScratch}
    (h1 : ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc1 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' })
    (h2 : ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc2 = { sc1 with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }) :
    ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc2 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsc1⟩ := h1
  obtain ⟨ta2, ba2, pt2, pb2, hp2, ps2, hl2, qsi2, qss2, hsc2⟩ := h2
  exact ⟨ta2, ba2, pt2, pb2, hp2, ps2, hl2, qsi2, qss2, by rw [hsc2, hsc1]⟩

private theorem m5_bt_scr_save {sc sc1 : FullScratch}
    (h : ∃ ta' ba' pt' pb', sc1 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb' }) :
    ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc1 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } := by
  obtain ⟨ta, ba, pt, pb, hsc⟩ := h
  exact ⟨ta, ba, pt, pb, sc.heap, sc.pos, sc.heap_len, sc.q_search_idx, sc.q_search_stamp, hsc⟩

private theorem m5_bt_compose_clear {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k1 k2 : FullCoreState} {back tgt : Nat} (htgt_lt : tgt < back)
    (hcv1 : k1.cur_vars = k.cur_vars)
    (hwo : FullOtfsWitnessInv c F0 F_cur k) (hw1 : FullWitnessInv c F0 F_cur k1)
    (hvals1 : ∀ l < 2 * k.cur_vars, k1.vals[l]?.getD 0#8 =
      if (k.lvl[l / 2]?.getD 0#32).toNat ≤ back then k.vals[l]?.getD 0#8 else 0#8)
    (hlvl1 : ∀ i < k.trail_end, let v := (k.trl[i]?.getD 0#32).toNat / 2
      k1.lvl[v]?.getD 0#32 =
        if (k.lvl[v]?.getD 0#32).toNat ≤ back then k.lvl[v]?.getD 0#32 else 0#32)
    (hlvl2_low : ∀ v < k1.cur_vars, (k1.lvl[v]?.getD 0#32).toNat ≤ tgt →
      k2.lvl[v]?.getD 0#32 = k1.lvl[v]?.getD 0#32)
    (hvals2 : ∀ l < 2 * k1.cur_vars, k2.vals[l]?.getD 0#8 =
      if (k1.lvl[l / 2]?.getD 0#32).toNat ≤ tgt then k1.vals[l]?.getD 0#8 else 0#8)
    (hlvl2 : ∀ i < k1.trail_end, let v := (k1.trl[i]?.getD 0#32).toNat / 2
      k2.lvl[v]?.getD 0#32 =
        if (k1.lvl[v]?.getD 0#32).toNat ≤ tgt then k1.lvl[v]?.getD 0#32 else 0#32) :
    (∀ l < 2 * k.cur_vars, k2.vals[l]?.getD 0#8 =
      if (k.lvl[l / 2]?.getD 0#32).toNat ≤ tgt then k.vals[l]?.getD 0#8 else 0#8) ∧
    (∀ i < k.trail_end, let v := (k.trl[i]?.getD 0#32).toNat / 2
      k2.lvl[v]?.getD 0#32 =
        if (k.lvl[v]?.getD 0#32).toNat ≤ tgt then k.lvl[v]?.getD 0#32 else 0#32) := by
  refine ⟨fun l hl => ?_, fun i hi => ?_⟩
  · rw [hvals2 l (by omega), hvals1 l hl]
    rcases hwo.vals_domain l hl with hv | hv | hv
    · rw [hv]; simp only [ite_self]
    · obtain ⟨i, hi, heq⟩ := (hwo.vals_true_iff l hl).mp hv
      have hl1 := hlvl1 i hi; dsimp only at hl1; rw [heq] at hl1; rw [hl1]
      by_cases h1 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ tgt
      · have h2 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ back := by omega
        simp [h1, h2]
      · by_cases h2 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ back
        · simp [h1, h2]
        · simp [h1, h2]
    · obtain ⟨i, hi, heq⟩ := (hwo.vals_false_iff l hl).mp hv
      have hl1 := hlvl1 i hi; dsimp only at hl1; rw [heq, fullInv_var_xor1] at hl1; rw [hl1]
      by_cases h1 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ tgt
      · have h2 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ back := by omega
        simp [h1, h2]
      · by_cases h2 : (k.lvl[l / 2]?.getD 0#32).toNat ≤ back
        · simp [h1, h2]
        · simp [h1, h2]
  · dsimp only
    let l := (k.trl[i]?.getD 0#32).toNat
    let v := l / 2
    have hl_lt : l < 2 * k.cur_vars := hwo.trail_lits_lt i hi
    have hv_lt : v < k.cur_vars := Nat.div_lt_of_lt_mul hl_lt
    have hl1 := hlvl1 i hi; dsimp only at hl1
    by_cases h1 : (k.lvl[v]?.getD 0#32).toNat ≤ tgt
    · have h2 : (k.lvl[v]?.getD 0#32).toNat ≤ back := by omega
      have hl1' : k1.lvl[v]?.getD 0#32 = k.lvl[v]?.getD 0#32 := by
        simpa [v, l, h2] using hl1
      rw [ite_eq_left h1, hlvl2_low v (by omega) (by rw [hl1']; exact h1), hl1']
    · by_cases h2 : (k.lvl[v]?.getD 0#32).toNat ≤ back
      · have hl1' : k1.lvl[v]?.getD 0#32 = k.lvl[v]?.getD 0#32 := by
          simpa [v, l, h2] using hl1
        have hval_l : k.vals[l]?.getD 0#8 = 1#8 := (hwo.vals_true_iff l hl_lt).mpr ⟨i, hi, rfl⟩
        have hval1_l : k1.vals[l]?.getD 0#8 = 1#8 := by
          rw [hvals1 l hl_lt, ite_eq_left h2]; exact hval_l
        obtain ⟨i1, hi1, hi1_eq⟩ := (hw1.vals_true_iff l (by omega)).mp hval1_l
        have hl2 := hlvl2 i1 hi1; dsimp only at hl2
        rw [hi1_eq] at hl2
        rw [ite_eq_right h1, hl2, hl1', ite_eq_right h1]
      · have hl1' : k1.lvl[v]?.getD 0#32 = 0#32 := by simpa [v, l, h2] using hl1
        rw [ite_eq_right h1, hlvl2_low v (by omega) (by rw [hl1']; simp), hl1']

/-- `full_backtrack_m5` unwinds 1 level before saving target/best phases in stable non-probing mode
and satisfies canonical `Full.fullBacktrackSpec`. -/
theorem full_backtrack_m5_wp (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X → Func.wp Γ full_backtrack_m5_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt_mx, htrl_lits, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_backtrack_m5_body
  c0_split
  · full_steps
    have hle : s.core.cur_level ≤ target_lvl.toNat := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; exact hc
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos s.core.trail_end
      s.core.propagated s.core.cur_level s.core.unassigned s.scratch m hlen (le_refl _)
      hlen.core_ok.propagated_le (Nat.min_eq_left hle).symm (probePres_refl s)
      (m5_bt_scr_save ⟨_, _, _, _, rfl⟩) htrl_lits
      (fun ⟨_, _, hw⟩ => m5_bt_noop_clear (hw.elim FullWitnessInv.toOtfs id) hle)
      (fun _ _ hw _ => hw) (fun _ _ _ hlt => False.elim (by omega)) hm
  · have htgt_lt : target_lvl.toNat < s.core.cur_level := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; omega
    have htgt_cmax : target_lvl.toNat < c.max_vars := htgt_mx htgt_lt
    clear hc
    c0_to_group
    refine wp_join_group (ts := [])
      (fun _ m0 => ∃ s0 : FullState, s0.core = s.core ∧ s0.LengthsOk c ∧
        FullProbeScratchPres s s0 ∧
        (∃ ta' ba' pt' pb', s0.scratch = { s.scratch with
          target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb' }) ∧
        (FullMem c s0 ⋆ R) m0) ?_ ?_
    · -- Shared fallthrough: `saved_prob = probing; probing = 1; raw_bt(tgt); probing = saved_prob;`
      rintro _ _ m0 ⟨s0, hc0, hlen0, hpres0, hscr0, hm0⟩
      rcases s0 with ⟨c0, sc0⟩; dsimp only at hc0; subst hc0
      full_steps
      let s0p : FullState := { core := { s.core with probing := 1#64 }, scratch := sc0 }
      have hm0p : (FullMem c s0p ⋆ R) m := hm
      c0_call hBtRaw
      refine ⟨c, s0p, R, rfl, m5_lengths_with_probing hlen0 1#64, hcl64, htgt_mx, htrl_lits,
        hm0p, ?_⟩
      intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1 s0_bt
        hlen1 hte1 hprop1 hcl1 hpres1 hscr1 htrl1 _ hclr1 hw_w1 hw_o1 hm1
      full_steps
      let s_fin : FullState :=
        { s with
          core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      have hlen_fin : s_fin.LengthsOk c :=
        m5_lengths_with_probing hlen1 s.core.probing
      exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m hlen_fin hte1 hprop1 hcl1
        (probePres_trans hpres0 hpres1) (m5_bt_scr_trans (m5_bt_scr_save hscr0) hscr1) htrl1
        (fun ⟨F0, Fc, hw⟩ =>
          hclr1 ⟨F0, Fc, hw.elim (fun w => Or.inl (m5_witness_with_probing w 1#64))
            (fun o => Or.inr (m5_otfs_with_probing o 1#64))⟩)
        (fun F0 Fc hw hle => m5_witness_with_probing
          (hw_w1 F0 Fc (m5_witness_with_probing hw 1#64) hle) s.core.probing)
        (fun F0 Fc ho hlt => m5_witness_with_probing
          (hw_o1 F0 Fc (m5_otfs_with_probing ho 1#64) hlt) s.core.probing)
        hm
    · intro Jfall hJfall
      c0_split
      · have hprob0 : s.core.probing = 0#64 := ‹_›
        c0_split
        · have hback_mod : (2 ^ 64 - 1 + s.core.cur_level) % 2 ^ 64 = s.core.cur_level - 1 := by
            omega
          have hback_nat : (BitVec.ofNat 64 s.core.cur_level - (1 : BitVec 64)).toNat =
              s.core.cur_level - 1 := by
            rw [BitVec.toNat_sub, bv64_ofNat_toNat hcl64]
            simpa only [show (1 : BitVec 64).toNat = 1 from rfl] using hback_mod
          c0_split
          · have hback_lt_mx : s.core.cur_level - 1 < c.max_vars := by
              rw [hback_mod, Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64)] at hc; exact hc
            full_steps
            let s_p1 : FullState := { s with core := { s.core with probing := 1#64 } }
            have hm_p1 : (FullMem c s_p1 ⋆ R) m := hm
            c0_call hBtRaw
            refine ⟨c, s_p1, R, rfl, m5_lengths_with_probing hlen 1#64, hcl64,
              fun _ => by rw [hback_nat]; exact hback_lt_mx, htrl_lits, hm_p1, ?_⟩
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 s1_bt
              hlen1 hte1 hprop1 hcl1 hpres1 hscr1 htrl1 hlvl1_low hclr1 hw_w1 hw_o1 hm1
            have hcl1_eq : cl1 = s.core.cur_level - 1 := by
              dsimp only [s_p1] at hcl1; rw [hcl1, hback_nat]; exact Nat.min_eq_right (by omega)
            full_steps
            let s1 : FullState :=
              { core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                      trail_pos := tp1, trail_end := te1, propagated := prop1,
                                      cur_level := cl1, unassigned := unass1 }
                scratch := sc1 }
            have hlen1' : s1.LengthsOk c := by
              simpa only [s1, s1_bt, s_p1, hprob0] using m5_lengths_with_probing hlen1 0#64
            have hm1' : (FullMem c s1 ⋆ R) m := by
              simpa only [s1, s1_bt, s_p1, hprob0, show (0 : BitVec 64) = 0#64 from rfl] using hm
            c0_call hSave
            refine ⟨c, s1, R, rfl, hlen1', hm1', ?_⟩
            intro _ s2 m2 hcore2 hlen2 ⟨hpres2, hscr2⟩ hm2
            have hc2_eq : s2.core = s1.core := hcore2
            rcases s2 with ⟨c2, sc2⟩; dsimp only at hc2_eq; subst hc2_eq
            change (FullMem c { core := s1.core, scratch := sc2 } ⋆ R) m2 at hm2
            have hpres12 : FullProbeScratchPres s { core := s1.core, scratch := sc2 } :=
              probePres_trans hpres1 hpres2
            have hscr12 := m5_bt_scr_trans hscr1 (m5_bt_scr_save hscr2)
            have hback_lt_cl :
                (BitVec.ofNat 64 s.core.cur_level - (1 : BitVec 64)).toNat < s.core.cur_level := by
              rw [hback_nat]; omega
            have hw_of_s1 : ∀ F0 Fc,
                (FullWitnessInv c F0 Fc s.core ∨ FullOtfsWitnessInv c F0 Fc s.core) →
                FullWitnessInv c F0 Fc s1.core := fun F0 Fc hw =>
              hw.elim
                (fun w => by
                  have := m5_witness_with_probing
                    (hw_w1 F0 Fc (m5_witness_with_probing w 1#64) (le_of_lt hback_lt_cl)) 0#64
                  simpa only [s1, s1_bt, s_p1, hprob0] using this)
                (fun o => by
                  have := m5_witness_with_probing
                    (hw_o1 F0 Fc (m5_otfs_with_probing o 1#64) hback_lt_cl) 0#64
                  simpa only [s1, s1_bt, s_p1, hprob0] using this)
            c0_to_group
            refine wp_join_group (ts := []) (fun _ mf => Q () mf)
              (fun _ _ mf hmf => by full_steps; exact hmf) (fun Jr hJr => ?_)
            c0_split
            · have htgt_lt_back : target_lvl.toNat < s.core.cur_level - 1 := by
                rw [hback_mod] at hc; exact hc
              full_steps
              let s2p : FullState := { core := { s1.core with probing := 1#64 }, scratch := sc2 }
              have hm2p : (FullMem c s2p ⋆ R) m := hm
              c0_call hBtRaw
              refine ⟨c, s2p, R, rfl, m5_lengths_with_probing hlen2 1#64,
                by dsimp only [s2p, s1]; omega, fun _ => htgt_cmax, htrl1, hm2p, ?_⟩
              intro vals3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 sc3 m3 s3_bt
                hlen3 hte3 hprop3 hcl3 hpres3 hscr3 htrl3 hlvl3_low hclr3 hw_w3 _ hm3
              full_steps
              have hcl3_eq : cl3 = min s.core.cur_level target_lvl.toNat := by
                dsimp only [s2p, s1] at hcl3; rw [hcl3, hcl1_eq]; omega
              let s3 : FullState :=
                { s with
                  core := { s.core with vals := vals3, lvl := lvl3, rsns := rsns3, trl := trl3,
                                        trail_pos := tp3, trail_end := te3, propagated := prop3,
                                        cur_level := cl3, unassigned := unass3 }
                  scratch := sc3 }
              have hlen3' : s3.LengthsOk c := by
                simpa only [s3, s3_bt, s2p, s1, hprob0] using m5_lengths_with_probing hlen3 0#64
              have hm3' : (FullMem c s3 ⋆ R) m := by
                simpa only [s3, s3_bt, s2p, s1, hprob0,
                  show (0 : BitVec 64) = 0#64 from rfl] using hm
              refine hJr () m (hQ vals3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 sc3 m hlen3'
                (le_trans hte3 hte1) hprop3 hcl3_eq (probePres_trans hpres12 hpres3)
                (m5_bt_scr_trans hscr12 hscr3) htrl3 ?_ ?_ ?_ hm3')
              · rintro ⟨F0, Fc, hw⟩
                have hw1 := hw_of_s1 F0 Fc hw
                have hclr1' := hclr1 ⟨F0, Fc, hw.elim
                  (fun w => Or.inl (m5_witness_with_probing w 1#64))
                  (fun o => Or.inr (m5_otfs_with_probing o 1#64))⟩
                have hclr3' := hclr3 ⟨F0, Fc, Or.inl (m5_witness_with_probing hw1 1#64)⟩
                rw [hback_nat] at hclr1'
                exact m5_bt_compose_clear (k := s.core) (k1 := s1.core) (k2 := s3.core)
                  htgt_lt_back rfl (hw.elim FullWitnessInv.toOtfs id) hw1 hclr1'.1 hclr1'.2
                  hlvl3_low hclr3'.1 hclr3'.2
              · intro F0 Fc hw _
                have := m5_witness_with_probing
                  (hw_w3 F0 Fc (m5_witness_with_probing (hw_of_s1 F0 Fc (Or.inl hw)) 1#64)
                    (by dsimp only [s2p, s1]; omega)) 0#64
                simpa only [s3, s3_bt, s2p, s1, hprob0] using this
              · intro F0 Fc ho _
                have := m5_witness_with_probing
                  (hw_w3 F0 Fc (m5_witness_with_probing (hw_of_s1 F0 Fc (Or.inr ho)) 1#64)
                    (by dsimp only [s2p, s1]; omega)) 0#64
                simpa only [s3, s3_bt, s2p, s1, hprob0] using this
            · have htgt_eq_back : target_lvl.toNat = s.core.cur_level - 1 := by
                rw [hback_mod] at hc; omega
              full_steps
              refine hJr () m2 (hQ vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc2 m2 hlen2 hte1
                hprop1 (by omega) hpres12 hscr12 htrl1 ?_ ?_ ?_ hm2)
              · rintro ⟨F0, Fc, hw⟩
                have hclr1' := hclr1 ⟨F0, Fc, hw.elim
                  (fun w => Or.inl (m5_witness_with_probing w 1#64))
                  (fun o => Or.inr (m5_otfs_with_probing o 1#64))⟩
                rwa [hback_nat, ← htgt_eq_back] at hclr1'
              · intro F0 Fc hw _; exact hw_of_s1 F0 Fc (Or.inl hw)
              · intro F0 Fc ho _; exact hw_of_s1 F0 Fc (Or.inr ho)
          · full_steps
            c0_call hSave
            refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
            intro _ s0 m0 hcore0 hlen0 ⟨hpres0, hscr0⟩ hm0
            full_steps
            exact hJfall () m0 ⟨s0, hcore0, hlen0, hpres0, hscr0, hm0⟩
        · full_steps; exact hJfall () m ⟨s, rfl, hlen, probePres_refl s, ⟨_, _, _, _, rfl⟩, hm⟩
      · full_steps; exact hJfall () m ⟨s, rfl, hlen, probePres_refl s, ⟨_, _, _, _, rfl⟩, hm⟩

end BacktrackProof

/-! ## 3. `full_warmup_m5` (`Full.fullWarmupSpec`) -/

section WarmupProof

open scoped FullArenaTactics FullPropDecTactics

local macro "fp_nojoin_m5" : tactic =>
  `(tactic| repeat (any_goals ((fail_if_success (apply wp_unroll_group)); fp_step)))

private theorem m5_warmup_bv32_dec_even {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 32)]
  omega

private theorem m5_warmup_bv32_dec_odd {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hev := m5_warmup_bv32_dec_even hv
  rw [show (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat =
      ((v <<< (1 : Nat)).setWidth 32).toNat ||| 1 from by simp [BitVec.toNat_or], hev]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have h0 : Nat.testBit 1 (k + 1) = false := by rw [Nat.testBit_succ]; simp
    rw [h0, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]; congr 1; omega

private def m5WarmupMask (k : FullCoreState) : FullCoreState :=
  { k with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    frame_trail := [], frame_dec := [], trail_end := 0, propagated := 0, cur_level := 0,
    probing := 0#64, unassigned := 0#64, unflushed := 0#64, wvec := [], arena := [],
    wstk := [], wlen := 0, wusable := 0#64, fuel := 0#64, confl_type := 0#64,
    confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64, oom := 0#64 }

private theorem m5Warmup_eq_upd {s st : FullState}
    (h : AgreesExcept m5WarmupMask s.core st.core)
    (hcl : st.core.cur_level = s.core.cur_level) :
    st =
      { core := { s.core with
          vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
          trl := st.core.trl, trail_pos := st.core.trail_pos, frame_trail := st.core.frame_trail,
          frame_dec := st.core.frame_dec, trail_end := st.core.trail_end,
          propagated := st.core.propagated, probing := st.core.probing,
          unassigned := st.core.unassigned, unflushed := st.core.unflushed, wvec := st.core.wvec,
          arena := st.core.arena, wstk := st.core.wstk, wlen := st.core.wlen,
          wusable := st.core.wusable, fuel := st.core.fuel, confl_type := st.core.confl_type,
          confl_ref := st.core.confl_ref, confl_lit0 := st.core.confl_lit0,
          confl_lit1 := st.core.confl_lit1, oom := st.core.oom }
        scratch := st.scratch } := by
  have h1 := h.get FullCoreState.d_cur; have h2 := h.get FullCoreState.d_val
  have h3 := h.get FullCoreState.cur_vars; have h4 := h.get FullCoreState.arena_len
  have h5 := h.get FullCoreState.arena_garbage; have h6 := h.get FullCoreState.first_reducible
  have h7 := h.get FullCoreState.num_irred; have h8 := h.get FullCoreState.num_redundant
  have h9 := h.get FullCoreState.num_binary; have h10 := h.get FullCoreState.tmp_cnt
  have h11 := h.get FullCoreState.tmp_len; have h12 := h.get FullCoreState.min_clr_len
  have h13 := h.get FullCoreState.min_clr_full; have h14 := h.get FullCoreState.dense_mode
  have h15 := h.get FullCoreState.inconsistent; have h16 := h.get FullCoreState.lit_mark
  have h17 := h.get FullCoreState.mrk; have h18 := h.get FullCoreState.tmp
  have h19 := h.get FullCoreState.min_clr; have h20 := h.get FullCoreState.repr
  have h21 := h.get FullCoreState.min_stk
  cases st with | mk stc stsc =>
  cases s with | mk sc ssc =>
  cases stc; cases sc; simp only at *; subst_vars; rfl

private theorem m5_arenaPerm_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem m5_arenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h12 : FullArenaPermEq k1 k2) (h23 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h12.2.2 r hr
    let ⟨s2, g2, p2⟩ := h23.2.2 r (h12.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

/-- `full_warmup_m5` preserves phase saving (`probing` unchanged during warmup), propagates beyond
conflicts, unwinds via `full_backtrack_raw_m5` with `probing = 1` (protecting `ptgt`/`pbst`), and
restores `search_ticks`, satisfying canonical `Full.fullWarmupSpec`. -/
theorem full_warmup_m5_del_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_warmup_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_noop : Q () m :=
    hQ s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.propagated s.core.probing
      s.core.unassigned s.core.unflushed s.core.wvec s.core.arena s.core.wstk s.core.wlen
      s.core.wusable s.core.fuel s.core.confl_type s.core.confl_ref s.core.confl_lit0
      s.core.confl_lit1 s.core.oom s.scratch m hinv (m5_arenaPerm_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) hm
  have hcv0 := hinv.lengths.core_ok.cur_vars_le
  have hte0 := hinv.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hinv.witness
  have hcl0_le := hw0.cur_level_le
  fp_nojoin_m5
  · exact hret_noop
  · exact hret_noop
  · have hcl0 : s.core.cur_level = 0 := by c0_bound
    refine wp_loop_break_group
      (fun (_steps, ()) mb => ∃ st : FullState,
        FullCoreInv c F0 st ∧ AgreesExcept m5WarmupMask s.core st.core ∧
        st.core.probing = s.core.probing ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) mb)
      (fun rem (steps, ()) ml => ∃ st : FullState,
        rem = s.core.cur_vars - steps.toNat ∧ steps.toNat ≤ s.core.cur_vars ∧
        FullCoreInv c F0 st ∧ AgreesExcept m5WarmupMask s.core st.core ∧
        st.core.probing = s.core.probing ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) ml) ?_ ?_ ?_
    · -- Post-loop `B`: `saved_prob = probing; probing = 1; raw_bt(0); probing = saved_prob; ticks`
      rintro _ ⟨_steps, ⟨⟩⟩ mb ⟨st, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hmb⟩
      obtain ⟨Fc_b, hwb⟩ := hst_inv.witness
      have hcb := hst_inv.lengths.core_ok
      have hcl_lt64 : st.core.cur_level < 2 ^ 64 := by
        have := hwb.cur_level_le; have := hcb.trail_end_le; have := hcb.cur_vars_le; omega
      have hmaxv_pos : (0 : BitVec 64).toNat < st.core.cur_level →
          (0 : BitVec 64).toNat < c.max_vars := by
        intro _; have := hwb.cur_level_le; have := hcb.trail_end_le; have := hcb.cur_vars_le; omega
      fp_steps
      let stp : FullState := { st with core := { st.core with probing := 1#64 } }
      have hinvp : FullCoreInv c F0 stp := hst_inv.with_probing 1#64
      have hmbp : (FullMem c stp ⋆ R) m := hm
      c0_call hBtRaw
      refine ⟨c, stp, R, rfl, hinvp.lengths, hcl_lt64, hmaxv_pos, hwb.trail_lits_lt, hmbp,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc' m1
          hlen1 _ _ hcl' hpres1 _ _ _ _ hwinv1 _ hm1 => ?_⟩
      have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
      subst hcl'0
      let st1 : FullState :=
        { core := { stp.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unas' }
          scratch := sc' }
      have hwbp : FullWitnessInv c F0 Fc_b stp.core := m5_witness_with_probing hwb 1#64
      have hinv1 : FullCoreInv c F0 st1 := ⟨hlen1, Fc_b, hwinv1 F0 Fc_b hwbp (Nat.zero_le _)⟩
      fp_steps
      let st2 : FullState :=
        { core := { st1.core with probing := st.core.probing }
          scratch := { sc' with search_ticks := s.scratch.search_ticks } }
      have hinv2_p : FullCoreInv c F0
          { st1 with core := { st1.core with probing := st.core.probing } } :=
        hinv1.with_probing st.core.probing
      have hsc2_ok : ({ sc' with search_ticks := s.scratch.search_ticks } :
          FullScratch).LengthsOk c :=
        { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
      have hinv2 : FullCoreInv c F0 st2 := hinv2_p.with_fuel_scratch hsc2_ok
      have hag2 : AgreesExcept m5WarmupMask s.core st2.core :=
        hag.update (fun k => { k with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0,
          unassigned := unas', probing := st.core.probing })
      have hst2_eq := m5Warmup_eq_upd hag2 (by dsimp only [st2, st1]; omega)
      have hinv2' := hinv2; have hm2' : (FullMem c st2 ⋆ R) m := hm
      have hperm' : FullArenaPermEq s.core st2.core := hperm
      rw [hst2_eq] at hinv2' hm2' hperm'
      exact hQ st2.core.vals st2.core.flags st2.core.lvl st2.core.rsns st2.core.trl
        st2.core.trail_pos st2.core.frame_trail st2.core.frame_dec st2.core.trail_end
        st2.core.propagated st2.core.probing st2.core.unassigned st2.core.unflushed
        st2.core.wvec st2.core.arena st2.core.wstk st2.core.wlen st2.core.wusable
        st2.core.fuel st2.core.confl_type st2.core.confl_ref st2.core.confl_lit0
        st2.core.confl_lit1 st2.core.oom st2.scratch m hinv2' hperm' hfl
        ⟨hpres1.1.1.trans hll, hpres1.1.2.trans hext⟩
        (fun h0 => by dsimp only [st2]; rw [hprob_eq]; exact h0) hm2'
    · -- Outer loop body `L`
      rintro B L rem ⟨steps, ⟨⟩⟩ ml hB ih
        ⟨st, rfl, hst_le, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hml⟩
      have hcv_eq : st.core.cur_vars = s.core.cur_vars := hag.get FullCoreState.cur_vars
      have hdm_st : st.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
      have hcv_le := hst_inv.lengths.core_ok.cur_vars_le
      fp_steps
      · have hst_lt : steps.toNat < s.core.cur_vars := by
          have h1 : steps.toNat < st.core.cur_vars % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt (by omega : st.core.cur_vars < 2 ^ 64)] at h1; omega
        have hst1_nat : (steps + (1 : BitVec 64)).toNat = steps.toNat + 1 := bv64_add1_toNat
          (by omega)
        c0_call hNextDec
        refine ⟨c, st, R, rfl, hst_inv.lengths, hml,
          fun ⟨v, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hp1, hv⟩ hm1 => ?_⟩
        rcases s1 with ⟨c1, sc1⟩; dsimp only [fullSafetySlice] at hcore1; cases hcore1
        let st1 : FullState := { st with scratch := sc1 }
        change (FullMem c { st with scratch := sc1 } ⋆ R) m1 at hm1
        have hinv1 : FullCoreInv c F0 st1 := hst_inv.with_fuel_scratch hlen1.scratch_ok
        have hcl1 := hinv1.lengths.core_ok
        have hph1 : sc1.phases.length = c.max_vars := hlen1.scratch_ok.phases_len
        have hptgt1 : sc1.phases_target.length = c.max_vars := hlen1.scratch_ok.phases_target_len
        have hftrl1 : st.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
        have hfdec1 : st.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
        fp_nojoin_m5
        · exact hB (steps + (1 : BitVec 64), ()) m1
            ⟨st1, hinv1, hag, hprob_eq, hperm, hfl, hp1.1.trans hll, hp1.2.trans hext, hm1⟩
        · obtain ⟨hv_lt, hval0⟩ := hv.resolve_left hc
          have hv_lt_max : v.toNat < c.max_vars := by omega
          have hv_lt30 : v.toNat < 2 ^ 30 := by omega
          refine wp_join_group (ts := [i8]) (fun (_dph, ()) md => m1 = md) ?_ ?_
          · rintro _ ⟨dph, ⟨⟩⟩ _ rfl
            refine wp_join_group (fun (lit, ()) m2 =>
              m1 = m2 ∧ (lit.toNat = 2 * v.toNat ∨ lit.toNat = 2 * v.toNat + 1)) ?_ ?_
            · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
              have hte1 : st.core.trail_end ≤ st.core.cur_vars := hcl1.trail_end_le
              obtain ⟨_, hw1⟩ := hinv1.witness
              have hcl1_le : st.core.cur_level ≤ st.core.trail_end := hw1.cur_level_le
              have hcl1_lt : st.core.cur_level < 2 ^ 63 := by omega
              have hnlvl_nat : (BitVec.ofNat 64 st.core.cur_level + (1 : BitVec 64)).toNat =
                  st.core.cur_level + 1 := by bv_omega
              fp_steps
              · exact hB (steps + (1 : BitVec 64), ()) m1
                  ⟨st1, hinv1, hag, hprob_eq, hperm, hfl, hp1.1.trans hll, hp1.2.trans hext, hm1⟩
              · have hnlvl_le : st.core.cur_level + 1 ≤ c.max_vars := by c0_bound
                have ⟨_, hun, hte_lt, _⟩ := full_decide_preserves_fullCore hinv1 hlen1.scratch_ok
                  hcl1.flags_len hv_lt hval0 hlit_eq (flags' := st.core.flags)
                  (unas' := st.core.unassigned) (unfl' := st.core.unflushed)
                have hte_lt' : st.core.trail_end < st.core.cur_vars := hte_lt
                let nlvl := st.core.cur_level + 1
                let ftrl' := st.core.frame_trail.set nlvl (BitVec.ofNat 32 st.core.trail_end)
                let fdec' := st.core.frame_dec.set nlvl lit
                let st2 : FullState :=
                  { core := { st.core with
                      frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
                    scratch := sc1 }
                have hlen2 : st2.LengthsOk c :=
                  ⟨{ hcl1 with frame_trail_len := by simp [st2, ftrl', hftrl1]
                               frame_dec_len := by simp [st2, fdec', hfdec1] }, hlen1.scratch_ok⟩
                have hm2 : (FullMem c st2 ⋆ R) m := by
                  have hte_bv : (BitVec.ofNat 64 st.core.trail_end).setWidth 32 =
                      BitVec.ofNat 32 st.core.trail_end := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 32)]
                  simpa only [st2, ftrl', fdec', nlvl, hnlvl_nat, hte_bv] using hm
                have hng : ¬ (st2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st2.core.trail_end ∨
                    st2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                  change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st1.core.trail_end ∨
                    st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                  simp only [hun, ne_eq, not_true_eq_false, or_false]
                  change ¬ (st.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st.core.trail_end)
                  omega
                c0_call hAssign
                refine ⟨c, st2, R, rfl, hlen2, by dsimp only [st2, nlvl]; omega, hm2, ?_⟩
                simp only [hng, ↓reduceIte]
                intro flags' unas' phases' m3 hfl_l hph_l hm3
                have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
                  { hlen1.scratch_ok with phases_len := hph_l }
                have ⟨hinv3, _, _, _⟩ := full_decide_preserves_fullCore hinv1 hsc3 hfl_l hv_lt hval0
                  hlit_eq (flags' := flags') (unas' := unas') (unfl' := st.core.unflushed)
                have hnl_ne0 : nlvl ≠ 0 := by dsimp only [nlvl]; omega
                have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                let st3 : FullState :=
                  { core := { st.core with
                      vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                      flags := flags',
                      lvl := st.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                      rsns := st.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                      trl := st.core.trl.set st.core.trail_end lit,
                      trail_pos := st.core.trail_pos.set (lit.toNat / 2)
                        (BitVec.ofNat 32 st.core.trail_end),
                      frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                      cur_level := nlvl, unassigned := unas' }
                    scratch := { sc1 with phases := phases' } }
                have hm3' : (FullMem c st3 ⋆ R) m3 := by
                  simpa only [st3, st2, hnl_ne0, ↓reduceIte, hff] using hm3
                have hag3 : AgreesExcept m5WarmupMask s.core st3.core :=
                  hag.update (fun k => { k with
                    vals := st3.core.vals, flags := flags', lvl := st3.core.lvl,
                    rsns := st3.core.rsns, trl := st3.core.trl, trail_pos := st3.core.trail_pos,
                    frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                    cur_level := nlvl, unassigned := unas' })
                -- Inner propagate-beyond-conflicts loop (`fuel.toNat` strictly decreases on `pr=1`)
                have hll3 : st3.scratch.last_learned = s.scratch.last_learned := hp1.1.trans hll
                have hext3 : st3.scratch.extend_len = s.scratch.extend_len := hp1.2.trans hext
                clear hNextDec hAssign hBtRaw hret_noop hcv0 hte0 hcl0_le hcl0 hB hst_inv hag hml
                  hinv1 hcl1 hph1 hptgt1 hftrl1 hfdec1 hlen2 hm2 hng hsc3 hm3 hfl_l hph_l
                  hnl_ne0 hff hp1 hv hv_lt hval0 hv_lt_max hv_lt30 hte1 hcl1_le hcl1_lt hnlvl_nat
                  hnlvl_le hte_lt hte_lt' hll hext
                refine wp_loop_break_group
                  (fun () m_out => ∃ st_o : FullState,
                    FullCoreInv c F0 st_o ∧ AgreesExcept m5WarmupMask s.core st_o.core ∧
                    st_o.core.probing = s.core.probing ∧
                    FullArenaPermEq s.core st_o.core ∧ st_o.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    st_o.scratch.last_learned = s.scratch.last_learned ∧
                    st_o.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st_o ⋆ R) m_out)
                  (fun rem_f () m_in => ∃ st_i : FullState,
                    rem_f = st_i.core.fuel.toNat ∧
                    FullCoreInv c F0 st_i ∧ AgreesExcept m5WarmupMask s.core st_i.core ∧
                    st_i.core.probing = s.core.probing ∧
                    FullArenaPermEq s.core st_i.core ∧ st_i.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    st_i.scratch.last_learned = s.scratch.last_learned ∧
                    st_i.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st_i ⋆ R) m_in)
                  ?_ ?_ ?_
                · rintro _ ⟨⟩ m_out ⟨st_o, hinv_o, hag_o, hpr_o, hperm_o, hfl_o, hll_o, hext_o,
                    hm_o⟩
                  c0_steps
                  exact ih (s.core.cur_vars - (steps + (1 : BitVec 64)).toNat)
                    (steps + (1 : BitVec 64), ()) m_out (by omega)
                    ⟨st_o, rfl, by omega, hinv_o, hag_o, hpr_o, hperm_o, hfl_o, hll_o, hext_o, hm_o⟩
                · rintro Bin Lin rem_f ⟨⟩ m_in hBin ih_in
                    ⟨st_i, rfl, hinv_i, hag_i, hpr_i, hperm_i, hfl_i, hll_i, hext_i, hm_i⟩
                  have hdm_i : st_i.core.dense_mode = 0#64 :=
                    (hag_i.get FullCoreState.dense_mode).trans hdense0
                  fp_steps
                  · obtain ⟨F_cur_i, hw_i⟩ := hinv_i.witness
                    c0_call hProp
                    refine ⟨c, F0, F_cur_i, st_i, R, rfl, hinv_i.lengths, hw_i, hdm_i, hm_i, ?_⟩
                    dsimp only
                    intro r vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop'' unas'' unfl''
                      wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype'' cref'' c0'' c1'' oom''
                      ticks'' wsort'' phases'' delayed'' m4 hlen4 hw4 _ hperm4 hfl4 hr_dom _
                      hr1 _ _ hm4
                    let st4 : FullState :=
                      { core := { st_i.core with
                          vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'',
                          trl := trl'', trail_pos := tp'', trail_end := te'', propagated := prop'',
                          unassigned := unas'', unflushed := unfl'', wvec := wvec'',
                          arena := arena'', wstk := wstk'', wlen := wlen'', wusable := wu'',
                          fuel := fuel'', confl_type := ctype'', confl_ref := cref'',
                          confl_lit0 := c0'', confl_lit1 := c1'', oom := oom'' }
                        scratch := { st_i.scratch with
                          search_ticks := ticks'', wsort := wsort'', phases := phases'',
                          delayed := delayed'' } }
                    have hinv4 : FullCoreInv c F0 st4 := ⟨hlen4, F_cur_i, hw4⟩
                    have hag4 : AgreesExcept m5WarmupMask s.core st4.core :=
                      hag_i.update (fun k => { k with
                        vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'',
                        trl := trl'', trail_pos := tp'', trail_end := te'', propagated := prop'',
                        unassigned := unas'', unflushed := unfl'', wvec := wvec'',
                        arena := arena'', wstk := wstk'', wlen := wlen'', wusable := wu'',
                        fuel := fuel'', confl_type := ctype'', confl_ref := cref'',
                        confl_lit0 := c0'', confl_lit1 := c1'', oom := oom'' })
                    have hperm4' : FullArenaPermEq s.core st4.core :=
                      m5_arenaPerm_trans hperm_i hperm4
                    have hfl4' : st4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl4 hfl_i
                    refine wp_jnz_of (fun _ => ?_) (fun hne0 => ?_)
                    · exact hBin () m4 ⟨st4, hinv4, hag4, hpr_i, hperm4', hfl4', hll_i, hext_i, hm4⟩
                    · c0_steps
                      · exact hBin () m4
                          ⟨st4, hinv4, hag4, hpr_i, hperm4', hfl4', hll_i, hext_i, hm4⟩
                      · have hr_is1 : r = 1#64 := by
                          rcases hr_dom with rfl | rfl | rfl
                          · simp at hne0
                          · rfl
                          · contradiction
                        have hfl_lt : fuel''.toNat < st_i.core.fuel.toNat := (hr1 hr_is1).1
                        exact ih_in fuel''.toNat () m4 hfl_lt
                          ⟨st4, rfl, hinv4, hag4, hpr_i, hperm4', hfl4', hll_i, hext_i, hm4⟩
                  · exact hBin () m_in ⟨st_i, hinv_i, hag_i, hpr_i, hperm_i, hfl_i, hll_i, hext_i,
                      hm_i⟩
                  · exact hBin () m_in ⟨st_i, hinv_i, hag_i, hpr_i, hperm_i, hfl_i, hll_i, hext_i,
                      hm_i⟩
                  · exact hBin () m_in ⟨st_i, hinv_i, hag_i, hpr_i, hperm_i, hfl_i, hll_i, hext_i,
                      hm_i⟩
                · intro _ Lin _ hLin; c0_steps
                  exact hLin st3.core.fuel.toNat () m3
                    ⟨st3, rfl, hinv3, hag3, hprob_eq, hperm, hfl, hll3, hext3, hm3'⟩
            · intro Jlit hJlit; fp_steps
              · exact hJlit ((v <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
                  ⟨rfl, Or.inr (m5_warmup_bv32_dec_odd hv_lt30)⟩
              · exact hJlit ((v <<< (1 : Nat)).setWidth 32, ()) m1
                  ⟨rfl, Or.inl (m5_warmup_bv32_dec_even hv_lt30)⟩
          · intro Jdph hJdph; fp_steps
            · exact hJdph _ m1 rfl
            · exact hJdph _ m1 rfl
            · exact hJdph _ m1 rfl
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hprob_eq, hperm, hfl, hll, hext, hml⟩
    · intro _ L _ hL; fp_steps
      exact hL s.core.cur_vars (0#64, ()) m
        ⟨s, by simp, Nat.zero_le _, hinv, AgreesExcept.refl m5WarmupMask s.core, rfl,
          m5_arenaPerm_refl _, Nat.le_refl _, rfl, rfl, hm⟩

theorem full_warmup_m5_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_warmup_m5_body a m Q X :=
  full_warmup_m5_del_wp Γ hNextDec hAssign
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h)) hBtRaw

end WarmupProof

/-! ## 4. `full_analyze_rsn_m5` & `full_otfs_subsume_m5` (`RC-09`) -/

section AnalyzeRsnAndOtfsProof

open FullAnalyzeTactics FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

private theorem m5_canonCut_to_anaCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hcond hne =>
      hcond.elim (fun hc => h.reason_inv_cut idx hc hne)
        (fun hlt => h.reason_inv_below idx hi hlt hne),
    fun idx hi hcond hne hlg =>
      hcond.elim (fun hc => h.reason_lit_mem_cut idx hc hne hlg)
        (fun hlt => h.reason_lit_mem_below idx hi hlt hne hlg)⟩

private theorem m5_anaCut_to_canonCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    (hcut : cut ≤ k.trail_end) : FullWitnessCutInv c F0 F_cur cut k :=
  ⟨⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hlt hne => h.reason_inv idx hi (Or.inr hlt) hne,
    fun idx hi hlt hne hlg => h.reason_lit_mem idx hi (Or.inr hlt) hne hlg⟩,
    hcut,
    fun idx hc hne => h.reason_inv idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne,
    fun idx hc hne hlg => h.reason_lit_mem idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne hlg⟩

private theorem m5_fullMem_arena_gu_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {ar1 ar2 gu1 gu2 : List (BitVec 32)} (ha : ar1 = ar2) (hg : gu1 = gu2)
    (hm : (FullMem c ⟨{ s.core with arena := ar1 },
      { s.scratch with glue_used := gu1 }⟩ ⋆ R) m) :
    (FullMem c ⟨{ s.core with arena := ar2 },
      { s.scratch with glue_used := gu2 }⟩ ⋆ R) m := by
  subst ha hg; exact hm

private theorem m5_bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · have hq : Q := h.mp hp; simp [hp, hq]
  · have hnq : ¬Q := mt h.mpr hp; simp [hp, hnq]

private theorem m5_res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

private abbrev M5CanonRsnPre (c : FullCfg) (s : FullState) (rsn_lits : List Nat)
    (skip_var : BitVec 32) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
    (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
  (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ rsn_lits ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
    (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) ∧
  (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) ∧
  (res' = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)

private theorem m5_canon_rsn_step {c : FullCfg} {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (htl_ge : s.core.tmp_len ≤ tl')
    (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : M5CanonRsnPre c s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 ≠ 0#8 →
      mrk2[v]?.getD 0#8 = mrk'[v]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hnt2 : ∀ j, tl' ≤ j → j < tl2 → (tmp2[j]?.getD 0#32).toNat = l_bv.toNat ∧
      l_bv.toNat / 2 < s.core.cur_vars ∧ l_bv.toNat / 2 ≠ skip_var.toNat ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres2 : res2 = res' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64)
    (htc2_eq : tc2 = tc' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) :
    M5CanonRsnPre c s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun v hv hnz => by have h1 := hmp v hv hnz; rw [hmp2 v hv (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun v hv hs0 hmnz => ?_,
    fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[v]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnm2 v hv hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hlt, hne', hpos, hle⟩
    · exact hnm v hv hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by
          rw [hmp _ (by omega) hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact m5_res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) hres_l hres2

private abbrev m5CanonRsnState (s : FullState) (mrk' : List (BitVec 8))
    (tmp' ws1' arena' gu' : List (BitVec 32)) (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) :
    FullState :=
  { s with core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                 min_clr_len := mcl', arena := arena' }
           scratch := { s.scratch with work_stk1 := ws1', glue_used := gu',
                                       ant_sz := ant', res_sz := res' } }

private theorem m5_maskNGlue_bit :
    ∀ i : Fin 32, (~~~0x0007FFFF#32)[i.val] = decide (19 ≤ i.val) := by decide

private theorem m5_mask19_bit :
    ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) := by decide

private theorem m5_mask23_bit :
    ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by decide

private theorem m5_bv32_bit_false_of_lt {ng : BitVec 32} (hng : ng.toNat < 2 ^ 19)
    {i : Nat} (hi19 : 19 ≤ i) (hi32 : i < 32) : ng[i] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hng (Nat.pow_le_pow_right (by decide) hi19))

private theorem m5_bv32_setGlue_garb (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, m5_maskNGlue_bit ⟨i, hi⟩,
    m5_mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19
  · subst h19
    have hb : ng[19] = false := m5_bv32_bit_false_of_lt hng (Nat.le_refl 19) (by omega)
    simp [hb]
  · simp [h19]

private theorem m5_bv32_setGlue_shrk (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, m5_maskNGlue_bit ⟨i, hi⟩,
    m5_mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23
  · subst h23
    have hb : ng[23] = false := m5_bv32_bit_false_of_lt hng (by decide) (by omega)
    simp [hb]
  · simp [h23]

private theorem m5_arenaSetGlue_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (ng : BitVec 32)
    (hng : ng.toNat < 2 ^ 19) (ni' nr' : BitVec 64) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref ((hdr &&& ~~~0x0007FFFF#32) ||| ng)
               num_irred := ni', num_redundant := nr' }
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref
    (fun x => (x &&& ~~~0x0007FFFF#32) ||| ng) k.arena_garbage ni' nr'
    (m5_bv32_setGlue_garb _ ng hng) (m5_bv32_setGlue_shrk _ ng hng)

/-- `full_analyze_rsn_m5` unconditionally sets `used = 31u` for all redundant reasons (`RC-09`,
`deduce.c:14-27`) and satisfies canonical `Full.fullAnalyzeRsnSpec`. -/
theorem full_analyze_rsn_m5_wp (Γ : Env)
    (hLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X → Func.wp Γ full_analyze_rsn_m5_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hcov, htl_cv, htc_fit, hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hgu_len := hlen.scratch_ok.glue_used_len
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena
      s.scratch m hlen hw hcov ⟨rfl, rfl⟩ rfl (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl
      (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ h0 h => absurd h0 h) (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro _ _; simp)
      (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  fa_unmdata; c0_step; c0_step
  · exact hret_false_same
  · c0_step
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := ‹_›
      c0_hsteps_np
      refine wp_call_of_spec _ _ (hLit (c.hdr, rsn &&& 0x7FFFFFFF#32, skip_var, ()) _ _ _
        ⟨c, s, R, rfl, hlen, hcur32, htl_cv, by omega, hcov, hm, ?_⟩)
      intro ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' _ hlen' hcov' htl_ge _ htl_le htc_ge
        hant_eq hres_eq htc_eq hmpres htpres hnewm hnewt hok hm'
      c0_hsteps_np
      have hw' : FullWitnessCutInv c F0 F_cur cut
          (m5CanonRsnState s mrk' tmp' ws1' s.core.arena s.scratch.glue_used
            mcl' tc' tl' ant' res').core :=
        m5_anaCut_to_canonCut (same_core_fullWitnessCut (m5_canonCut_to_anaCut hw)
          hlen'.core_ok.mrk_len hlen'.core_ok.tmp_len_arr hlen'.core_ok.min_clr_len_le htl_le
          (tc' := tc')) hw.cut_le
      have htc_f := filter_step_of_lit
        (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
        (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
        (fun w hw_lt => hmpres w (by omega)) (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (Nat.le_refl _) (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl)
        (by simpa only [decide_eq_true_eq] using htc_eq)
      have hres_f := m5_res_step_of_lit (mv := s.core.cur_vars)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
        (r1 := s.scratch.res_sz) (fun _ _ _ => rfl) (fun w hw_lt => hmpres w (by omega))
        (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) hres_eq
      refine hQ ok mrk' tmp' tc' tl' mcl' s.core.arena
        { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } m'
        hlen' hw' hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
        hmpres htpres ?_ ?_ (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ hm'
      · intro v hv h0 hnz; obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnewm v hv h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (mem_fullRsnLits_bin hne hbin).mpr rfl,
          rfl, hlt, hne', hpos, hle⟩
      · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
        exact ⟨(mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega, by rwa [heq],
          by rwa [heq], by rwa [heq], by rwa [heq]⟩
      · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'
        refine ⟨hne, ?_, fun l hl => ?_⟩
        · rw [hant_eq, fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.countP_cons, List.countP_nil, Nat.zero_add]
          exact congrArg (s.scratch.ant_sz + ·)
            (m5_bv64_ite_iff (by simp only [decide_eq_true_eq]))
        · simp only [fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.mem_singleton] at hl
          subst hl; refine ⟨hvlt, fun hne' => ?_⟩
          obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
          obtain ⟨hle, _, hlow⟩ := h0r h0
          exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
            ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hlarge : (rsn &&& 0x80000000#32) = 0#32 := ‹_›
      have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
      obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
      have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSize s rsn.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hhdr_get : s.core.arena[rsn.toNat]'(by omega) = s.core.arena[rsn.toNat]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      fa_unmdata; (try c0_let_simp)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; all_goals (try exact hret_false_same)
      refine wp_join_group (ts := [i32]) (fun (_hdr_r, ()) m1 => ∃ arena1 gu1,
          let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                         scratch := { s.scratch with glue_used := gu1 } }
          FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
          fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
          (∀ k < fullArenaClauseSize s rsn.toNat,
            arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
          (FullMem c s1 ⋆ R) m1) ?_ ?_
      · rintro _ ⟨_hdr_r, ⟨⟩⟩ m1 ⟨arena1, gu1, hw1, hlen1, hrefs1, hcl1, har1_eq, hm1⟩
        c0_hsteps_nogrp
        let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                       scratch := { s.scratch with glue_used := gu1 } }
        have har1_len : arena1.length = c.arena_cap := hlen1.core_ok.arena_len_arr
        have har1_le : s.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
        let sz : Nat := fullArenaClauseSize s rsn.toNat
        let antPred : Nat → Bool := fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
        let LoopInv : Nat → List (BitVec 8) → List (BitVec 32) → List (BitVec 32) →
            Nat → Nat → Nat → BitVec 64 → BitVec 64 → Prop :=
          fun i mrk' tmp' ws1' mcl' tc' tl' ant' res' =>
            i ≤ sz ∧ mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧
            ws1'.length = 2 * c.max_vars ∧ mcl' ≤ c.max_vars ∧
            s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
            FullAnaMarksCov c (m5CanonRsnState s1 mrk' tmp' ws1' arena1 gu1
              mcl' tc' tl' ant' res') ∧
            M5CanonRsnPre c s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
            (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
              (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
            ant' = s.scratch.ant_sz +
              BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
            ∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
              l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
                (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
                (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
                  (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                  (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                    ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                      (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))
        refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk' tmp' ws1' mcl' tc' tl' ant' res',
          r = sz - i ∧ iv = BitVec.ofNat 32 i ∧ LoopInv i mrk' tmp' ws1' mcl' tc' tl' ant' res' ∧
          (FullMem c (m5CanonRsnState s mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res') ⋆ R) ml)
          ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', ws1', mcl', tc', tl', ant', res', rfl, rfl,
            ⟨hile, hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hcov', hpre,
              hnewlow, hant_l, hdone⟩, hml⟩
          have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
          have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
            change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
          have hidx_eq : s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
              s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
          rw [Blocks.get_here]; c0_hsplit
          · have hi32 : i < 2 ^ 32 := by omega
            have hilt : i < sz := by
              have hlt_bv : i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hlt_bv; exact hlt_bv
            have hidx_l : ((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat =
                rsn.toNat + 3 + i := by simp only [bv_c0, BitVec.reduceToNat]; omega
            have hilt_core : i < fullArenaClauseSizeCore s.core rsn.toNat := hilt
            have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
                arena1.length := by rw [hidx_l, har1_len]; omega
            c0_hsteps_np
            have htc_le_cv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
              rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
            let st := m5CanonRsnState s1 mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res'
            have hst_len : st.LengthsOk c :=
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp only [st]; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
            let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
            have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
              have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv :=
                List.getElem?_eq_getElem (by omega)
              rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
              exact (Option.some.inj h1).symm
            have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
            have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
              (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
            rw [getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
            refine wp_call_of_spec _ _ (hLit (c.hdr, l_bv, skip_var, ()) _ _ _
              ⟨c, st, R, rfl, hst_len, hcur32, htl_le, by dsimp only [st]; omega, hcov', hml, ?_⟩)
            intro ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 _ hlen2 hcov2 htl2_ge htl2_inc
              htl2_le htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2
            dsimp only [st, s1] at *
            have hpre2 := m5_canon_rsn_step hcv_le htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre
              hmpres2 htpres2 hnewm2 hnewt2 hres2 htc2_eq
            cases ok2 with
            | false =>
              wp_unfold; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
              exact hQ false mrk2 tmp2 tc2 tl2 mcl2 arena1
                { s.scratch with work_stk1 := ws2, glue_used := gu1,
                                 ant_sz := ant2, res_sz := res2 } m2
                hlen2
                (m5_anaCut_to_canonCut (same_core_fullWitnessCut (m5_canonCut_to_anaCut hw1)
                  hlen2.core_ok.mrk_len hlen2.core_ok.tmp_len_arr hlen2.core_ok.min_clr_len_le
                  htl2_le (tc' := tc2)) hw1.cut_le)
                hcov2 ⟨rfl, rfl⟩ rfl (by omega) htl2_le (by omega) hrefs1 hcl1 h1 h2
                (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := h3 v hv hs0 hmnz
                  ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
                (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
                  ⟨(mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
                h5 h6 h7 (fun hc => by cases hc) hm2
            | true =>
              wp_unfold; obtain ⟨hvlt, hrest⟩ := hok2 rfl
              have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
                  (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
                have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz,
                    fullArenaClauseSize]; omega
                rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
                congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
                simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
              have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
                  (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
                rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
                  Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
                exact congrArg (s.scratch.ant_sz + ·) (congrArg _
                  (m5_bv64_ite_iff (by simp only [antPred, decide_eq_true_eq])))
              rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
                BitVec.eq_of_toNat_eq (by
                  have h1n : (1 : BitVec 32).toNat = 1 := rfl
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1n,
                    Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega),
                    Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)])]
              refine ih (sz - (i + 1)) _ _ (by omega)
                ⟨i + 1, mrk2, tmp2, ws2, mcl2, tc2, tl2, ant2, res2, rfl, rfl,
                  ⟨by omega, hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr,
                    hlen2.scratch_ok.work_stk1_len, hlen2.core_ok.min_clr_len_le,
                    by omega, htl2_le, by omega, hcov2, hpre2, ?_, hant2_eq, ?_⟩, hm2⟩
              · intro w hw_lt hs0 hmnz2 hltcl
                by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
                · obtain ⟨rfl, _, hne', hpos, _⟩ := hnewm2 w (by omega) hm1_w hmnz2
                  obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
                  exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
                · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
                  exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
              · intro k hk; by_cases hki : k = i
                · subst hki; dsimp only; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
                  obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
                  by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
                  · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                    exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                      ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
                  · obtain ⟨_, _, _, _, _, _, hle⟩ := hnewm _ (by omega) hs0 hm1_w
                    exact ⟨hle, fun _ hltcl =>
                      let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                      ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
                · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                  refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
                  refine ⟨fun hp => by rw [hmpres2 _ (by omega) (h1 hp)]; exact h1 hp, ?_⟩
                  intro hs0
                  obtain ⟨hle, hlow⟩ := h2 hs0
                  exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                    ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
          · c0_hsteps_nogrp
            have hi32 : i < 2 ^ 32 := by omega
            have hieq : i = sz := by
              have hge_bv : ¬ i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hge_bv; omega
            refine hQ true mrk' tmp' tc' tl' mcl' arena1
              { s.scratch with work_stk1 := ws1', glue_used := gu1,
                               ant_sz := ant', res_sz := res' } ml
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp only; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
              (m5_anaCut_to_canonCut (same_core_fullWitnessCut (m5_canonCut_to_anaCut hw1)
                hml_l htl_l hmcl_le htl_le (tc' := tc')) hw1.cut_le)
              hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge hrefs1 hcl1 hmpres htpres
              (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := hnewm v hv hs0 hmnz
                ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
              (fun j hj1 hj2 => let ⟨h1, hr⟩ := hnewt j hj1 hj2
                ⟨(mem_fullRsnLits_large hne hlarge).mpr h1, hr⟩)
              hnd_t hcnt hres_l (fun _ => ⟨hne, ?_, fun l hl => by
                simp only [fullRsnLits, hne, hlarge, ↓reduceIte] at hl
                obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
                have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
                have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd⟩) hml
            · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
                  List.length_map, List.length_take, List.length_drop]; have := har_len; omega
              rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
              simp [fullRsnLits, hne, hlarge, antPred]
        · intro L hL; c0_hsteps_nogrp
          refine hL sz _ m1 ⟨0, s.core.mrk, s.core.tmp, s.scratch.work_stk1, s.core.min_clr_len,
            s.core.tmp_cnt, s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, by omega, rfl,
            ⟨Nat.zero_le _, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
              hlen1.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _,
              htl_cv, Nat.le_refl _, hcov, ⟨fun _ _ _ => rfl, fun _ _ => rfl,
                fun _ _ h0 hnz => absurd h0 hnz, fun _ h1 h2 => by omega,
                fun _ _ _ h1 h2 => by omega,
                by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
                   intro _ _; simp,
                by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp⟩,
              fun _ _ h0 hnz _ => absurd h0 hnz, (by simp), fun _ hk => by omega⟩, hm1⟩
      · intro Jred hJred
        clear hLit hQ htl_cv htc_fit hcov hrsn_ref hret_false_same skip_var
        c0_let_simp; c0_step
        · refine wp_join_group (ts := [i32, i64])
            (fun (hdr0, glue0, ()) m0 => ∃ arena0,
              let s0 : FullState := { s with core := { s.core with arena := arena0 } }
              FullWitnessCutInv c F0 F_cur cut s0.core ∧ s0.LengthsOk c ∧
              fullArenaClauseRefs s0 = fullArenaClauseRefs s ∧
              (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s0 r = fullArenaClauseSize s r ∧
                fullArenaClauseGarb s0 r = fullArenaClauseGarb s r ∧
                fullArenaClauseLits s0 r = fullArenaClauseLits s r) ∧
              (∀ k < fullArenaClauseSize s rsn.toNat,
                arena0[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
              fullArenaHdrCore s0.core rsn.toNat = hdr0 ∧
              (FullMem c s0 ⋆ R) m0) ?_ ?_
          · rintro _ ⟨hdr0, glue0, ⟨⟩⟩ m0 ⟨arena0, hw0, hlen0, hrefs0, hcl0, har0_eq, hhdr0, hm0⟩
            let s0 : FullState := { s with core := { s.core with arena := arena0 } }
            have har0_len : arena0.length = c.arena_cap := hlen0.core_ok.arena_len_arr
            have href0 : rsn.toNat ∈ fullArenaClauseRefs s0 := by rw [hrefs0]; exact href
            dsimp only [s0] at hm0
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (gi, ()) m_gi => gi.toNat < 64 ∧ (FullMem c s0 ⋆ R) m_gi) ?_ ?_
            · rintro _ ⟨gi, ⟨⟩⟩ m_gi ⟨hgi_lt, hm_gi⟩; c0_let_simp
              refine wp_join_group (ts := []) (fun () m_gu => ∃ gu1, gu1.length = 64 ∧
                (FullMem c ⟨s0.core, { s.scratch with glue_used := gu1 }⟩ ⋆ R) m_gu) ?_ ?_
              · rintro _ ⟨⟩ m_gu ⟨gu1, hgu1, hm_gu⟩; clear hm_gi
                dsimp only [s0] at hm_gu
                c0_hsteps
                · obtain ⟨hw', hr', hcl'⟩ := arenaBumpUsage_preserves_fullWitnessCut hlen0.core_ok
                    (m5_canonCut_to_anaCut hw0) href0 31#32
                  have har_u_eq : arena0.set (rsn.setWidth 64).toNat
                      ((hdr0 &&& 134217727#32) ||| (31#32 <<< (27 : BitVec 32))) =
                      arena0.set rsn.toNat ((fullArenaHdrCore s0.core rsn.toNat &&&
                        0x07FFFFFF#32) ||| (31#32 <<< 27)) := by
                    rw [bv_c0_zext32_64, hhdr0]; rfl
                  let arena_u := arena0.set rsn.toNat
                    ((fullArenaHdrCore s0.core rsn.toNat &&& 0x07FFFFFF#32) ||| (31#32 <<< 27))
                  refine hJred (hdr0, ()) _ ⟨arena_u, gu1, m5_anaCut_to_canonCut hw' hw0.cut_le,
                    ⟨{ hlen0.core_ok with arena_len_arr := by simp [arena_u, har0_len] },
                     { hlen0.scratch_ok with glue_used_len := hgu1 }⟩,
                    hr'.trans hrefs0,
                    fun r hr =>
                      let ⟨s_a, g_a, l_a⟩ :=
                        hcl' r (by change r ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hr)
                      let ⟨s_b, g_b, l_b⟩ := hcl0 r hr
                      ⟨s_a.trans s_b, g_a.trans g_b, l_a.trans l_b⟩,
                    fun k hk => (List.getElem?_set_ne (by omega)).trans (har0_eq k hk), ?_⟩
                  refine m5_fullMem_arena_gu_eq har_u_eq rfl ?_
                  assumption
                · exact hJred (hdr0, ()) _ ⟨arena0, gu1, hw0,
                    ⟨hlen0.core_ok, { hlen0.scratch_ok with glue_used_len := hgu1 }⟩,
                    hrefs0, hcl0, har0_eq, hm_gu⟩
              · intro Jgu hJgu; dsimp only [s0] at hm_gi; c0_hsteps_np
                · exact hJgu () _ ⟨s.scratch.glue_used.set gi.toNat
                    (s.scratch.glue_used[gi.toNat]'(by omega) + 1), by simp [hgu_len],
                    by assumption⟩
                · exact hJgu () _ ⟨s.scratch.glue_used, hgu_len, hm_gi⟩
            · intro Jgi hJgi; c0_hsteps_np
              · exact hJgi _ _ ⟨by decide, hm0⟩
              · refine hJgi _ _ ⟨?_, hm0⟩
                rw [show (63 : BitVec 64).toNat = 63 from rfl] at hc; omega
          · intro Jpromo hJpromo
            have hJpromo_same : ∀ hdr0 glue0 m0, fullArenaHdrCore s.core rsn.toNat = hdr0 →
                (FullMem c s ⋆ R) m0 → Jpromo (hdr0, glue0, ()) m0 :=
              fun hdr0 glue0 m0 hh hm0 =>
                hJpromo (hdr0, glue0, ()) m0 ⟨s.core.arena, hw, hlen, rfl,
                  fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hh,
                  by change (FullMem c s ⋆ R) m0; exact hm0⟩
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun (_lim0, ()) ml1 => (FullMem c s ⋆ R) ml1) ?_ ?_
              · rintro _ ⟨lim0, ⟨⟩⟩ ml1 hm1
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (lim, ()) ml2 => lim.toNat ≤ 32 ∧ (FullMem c s ⋆ R) ml2) ?_ ?_
                · rintro _ ⟨lim, ⟨⟩⟩ ml2 ⟨hlim_le, hm2⟩
                  have hlvl_ge_cv : s.core.cur_vars ≤ s.core.lvl.length := by
                    rw [hlen.core_ok.lvl_len]; exact hcv_le
                  c0_hsteps_nogrp
                  refine wp_loop_inv (ts := [i64, i64, .bool])
                    (fun (ng, lo, more, ()) mo =>
                      ng.toNat ≤ 33 ∧ (more = true → ng.toNat ≤ lim.toNat + 1) ∧
                      (FullMem c s ⋆ R) mo)
                    (fun (ng, _lo, more, ()) _ =>
                      2 * (33 - ng.toNat) + (if more then 1 else 0)) ?_ ?_
                  · intro Jout hJout; fa_fast_steps
                    exact hJout (0#64, 0#64, true, ()) ml2
                      ⟨by decide, fun _ => Nat.zero_le _, hm2⟩
                  · intro Jout (ng, lo, more, ⟨⟩) mo ⟨hng_le, hng_lim, hmo⟩ ih_out
                    cases more with
                    | false =>
                      fa_fast_steps <;> try contradiction
                      · have hng_lt : ng.toNat < 2 ^ 19 := by omega
                        have hng32_lt : (ng.setWidth 32).toNat < 2 ^ 19 := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hng_lt
                        obtain ⟨hw0, hr0, hcl0⟩ := m5_arenaSetGlue_preserves_fullWitnessCut
                          hlen.core_ok (m5_canonCut_to_anaCut hw) href (ng.setWidth 32) hng32_lt
                          s.core.num_irred s.core.num_redundant
                        have hhdr_eq : s.core.arena.set (rsn.setWidth 64).toNat
                            (((s.core.arena[rsn.toNat]'(by omega)) &&& ~~~0x0007FFFF#32) |||
                              ng.setWidth 32) =
                            s.core.arena.set rsn.toNat ((fullArenaHdrCore s.core rsn.toNat &&&
                              ~~~0x0007FFFF#32) ||| ng.setWidth 32) := by
                          rw [bv_c0_zext32_64, hhdr_get]; rfl
                        let hdr_p :=
                          ((s.core.arena[rsn.toNat]'(by omega)) &&& ~~~0x0007FFFF#32) |||
                          ng.setWidth 32
                        let arena_p := s.core.arena.set rsn.toNat
                          ((fullArenaHdrCore s.core rsn.toNat &&& ~~~0x0007FFFF#32) |||
                            ng.setWidth 32)
                        have hhdr_self : fullArenaHdrCore
                            ({ s.core with arena := arena_p } : FullCoreState) rsn.toNat =
                            hdr_p := by
                          unfold fullArenaHdrCore; dsimp only [arena_p, hdr_p]
                          rw [List.getElem?_set_self (by omega), Option.getD_some]
                          exact congrArg (· ||| ng.setWidth 32)
                            (congrArg (· &&& ~~~0x0007FFFF#32) hhdr_get.symm)
                        refine hJpromo (hdr_p, ng, ()) _
                          ⟨arena_p, m5_anaCut_to_canonCut hw0 hw.cut_le,
                           ⟨{ hlen.core_ok with arena_len_arr := by simp [arena_p, har_len] },
                            hlen.scratch_ok⟩,
                           hr0, hcl0, fun k _ => List.getElem?_set_ne (by omega), hhdr_self, ?_⟩
                        dsimp only [arena_p]; rw [← hhdr_eq]; assumption
                      · exact hJpromo_same _ _ mo hhdr_get.symm hmo
                      · exact hJpromo_same _ _ mo hhdr_get.symm hmo
                    | true =>
                      dsimp only
                      refine wp_unroll_group fun Jex hJex => ?_
                      c0_hsteps_nogrp <;> try (first | contradiction | exact absurd rfl ‹_›)
                      · have hng_le_lim : ng.toNat ≤ lim.toNat := by omega
                        refine wp_loop_inv (ts := [i64, i32])
                          (fun (best, k, ()) mk => k.toNat ≤ fullArenaClauseSize s rsn.toNat ∧
                            (FullMem c s ⋆ R) mk)
                          (fun (_best, k, ()) _ =>
                            fullArenaClauseSize s rsn.toNat - k.toNat) ?_ ?_
                        · intro Jin hJin; c0_hsteps_np
                          exact hJin (0xFFFFFFFFFFFFFFFF#64, 0#32, ()) mo ⟨Nat.zero_le _, hmo⟩
                        · intro Jin (best, k, ⟨⟩) mk ⟨hk_le, hmk⟩ ih_in
                          have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
                            change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
                          have hidx_eq :
                              s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
                              s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
                          c0_hsplit
                          · have hk_lt : k.toNat < fullArenaClauseSize s rsn.toNat := by
                              have h1 : k.toNat < (s.core.arena[(rsn.toNat +
                                  (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
                              rwa [hidx_eq, hsz_get] at h1
                            have hk_core : k.toNat < fullArenaClauseSizeCore s.core rsn.toNat :=
                              hk_lt
                            have hk_idx : ((rsn.setWidth 64 + 3#64) + k.setWidth 64).toNat =
                                rsn.toNat + 3 + k.toNat := by
                              simp only [bv_c0]; omega
                            have hk_lt_ar : ((rsn.setWidth 64 + 3#64) + k.setWidth 64).toNat <
                                s.core.arena.length := by rw [hk_idx, har_len]; omega
                            have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
                              rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32)]
                              exact Nat.mod_eq_of_lt (by have := BitVec.isLt k; omega)
                            c0_hsteps_nogrp_np
                            refine wp_join_group (ts := [i64])
                              (fun (_best', ()) mb => (FullMem c s ⋆ R) mb) ?_ ?_
                            · rintro _ ⟨best', ⟨⟩⟩ mb hmb
                              c0_hsteps_np
                              exact ih_in (best', k + 1#32, ()) mb
                                (by dsimp only; rw [hkp1]; omega)
                                ⟨by rw [hkp1]; omega, hmb⟩
                            · intro Jbest hJbest; c0_hsteps_np <;> exact hJbest _ mk hmk
                          · have hk_eq : k.toNat = fullArenaClauseSize s rsn.toNat := by
                              have hge : ¬ k.toNat < (s.core.arena[(rsn.toNat +
                                  (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
                              rw [hidx_eq, hsz_get] at hge; omega
                            c0_hsteps_np
                            · have hdec : 2 * (33 - ng.toNat) + 0 <
                                  2 * (33 - ng.toNat) + 1 := by omega
                              exact ih_out (ng, lo, false, ()) mk hdec
                                ⟨hng_le, (fun hf => False.elim (Bool.noConfusion hf)), hmk⟩
                            · have hngp1 : (ng + 1#64).toNat = ng.toNat + 1 := by
                                rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
                                exact Nat.mod_eq_of_lt (by omega)
                              have hdec : 2 * (33 - (ng + 1#64).toNat) + 1 <
                                  2 * (33 - ng.toNat) + 1 := by
                                rw [hngp1]; omega
                              exact ih_out (ng + 1#64, _ , true, ()) mk hdec
                                ⟨by rw [hngp1]; omega, fun _ => by rw [hngp1]; omega, hmk⟩
                      · c0_hsteps <;> try (first | contradiction | exact absurd rfl ‹_›)
                        exact hJpromo_same _ _ mo hhdr_get.symm hmo
                · intro Jlim2 hJlim2
                  c0_hsplit
                  · c0_hsteps_np; exact hJlim2 (32#64, ()) ml1 ⟨by decide, hm1⟩
                  · c0_hsteps_np
                    refine hJlim2 (lim0, ()) ml1 ⟨?_, hm1⟩
                    rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc; omega
              · intro Jlim hJlim
                c0_hsplit
                · c0_hsteps_np; exact hJlim _ m hm
                · c0_hsteps_np; exact hJlim _ m hm
            · c0_hsteps_np
              exact hJpromo_same _ _ m hhdr_get.symm hm
        · c0_hsteps_np
          simp only [bv_c0_zext32_64]
          exact hJred (s.core.arena[rsn.toNat]'(by omega), ()) _
            ⟨s.core.arena, s.scratch.glue_used, hw, hlen, rfl,
             fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm⟩

private theorem m5_bv32_and_glue_lt (x : BitVec 32) : (x &&& 0x0007FFFF#32).toNat < 2 ^ 19 := by
  have h : (x &&& 0x0007FFFF#32).toNat ≤ (0x0007FFFF#32 : BitVec 32).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  exact Nat.lt_of_le_of_lt h (by decide)

private theorem m5_fullWitnessCut_with_counts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k) (ni' nr' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut { k with num_irred := ni', num_redundant := nr' } :=
  ⟨⟨hw.ext_sound, hw.inconsistent_sound,
    { hw.arena with len_ok := hw.arena.len_ok },
    hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
    hw.cur_level_le, hw.trail_lits_lt,
    hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le,
    hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv, hw.level0_rsn_none,
    hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt, hw.frame_dec_lt,
    hw.reason_inv_below, hw.reason_lit_mem_below⟩,
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

/-- `full_otfs_subsume_m5` clamps surviving redundant glue (`min(cg, dg)`) and updates
`num_redundant`/`num_irred` on `PH_GARB`, satisfying canonical `Full.fullOtfsSubsumeSpec`. -/
theorem full_otfs_subsume_m5_wp (Γ : Env) :
    ∀ args m Q X, fullOtfsSubsumeSpec args m Q X →
      Func.wp Γ full_otfs_subsume_m5_body args m Q X := by
  rintro ⟨h, new_confl, old_ctype, old_cref, to_bin, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hnd, hpre, hm, hQ⟩
  have hsame : Q () m := hQ s.core.arena s.core.arena_garbage s.core.num_irred
    s.core.num_redundant m hlen hw hnd rfl (fun _ _ => ⟨rfl, fun _ => rfl⟩) hm
  by_cases hct : old_ctype = 2#64
  · subst old_ctype
    by_cases hcr : old_cref = 0xFFFFFFFF#64
    · subst old_cref; fa_fast_steps; exact hsame
    · obtain ⟨hold_ref, hnew_ref, hnonact⟩ := hpre rfl hcr
      have hwf := hw.arena.refs_wf old_cref.toNat hold_ref
      have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
      have hcap31 := c.harena; unfold dimacsBound at hcap31
      have hcr_bd : old_cref.toNat + 2 < s.core.arena.length := by omega
      have hcr2 : (old_cref + 2#64).toNat = old_cref.toNat + 2 := by
        rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
      have hd_eq : fullArenaHdrCore s.core old_cref.toNat =
          s.core.arena[old_cref.toNat]'(by omega) := by
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      obtain ⟨arena1, h_arena1⟩ : ∃ xs, xs = s.core.arena.set old_cref.toNat
          (fullArenaHdrCore s.core old_cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
      have har1_len : arena1.length = c.arena_cap := by rw [h_arena1]; simp [har_len]
      obtain ⟨ag1, h_ag1⟩ : ∃ x, x = s.core.arena_garbage + 3#64 +
          (arena1[old_cref.toNat + 2]'(by rw [har1_len]; omega)).setWidth 64 := ⟨_, rfl⟩
      let s1 : FullState :=
        { s with core := { s.core with arena := arena1, arena_garbage := ag1 } }
      have hmg1 := markGarb_preserves_fullWitnessCut hlen.core_ok (m5_canonCut_to_anaCut hw)
        (Nat.le_refl cut) hold_ref ag1 (fun idx hidx hcond hne hlg =>
          hnonact idx hidx hcond hne hlg)
      rw [← h_arena1] at hmg1
      obtain ⟨hw1a, hrefs1, hprops1⟩ := hmg1
      have hw1 : FullWitnessCutInv c F0 F_cur cut s1.core := m5_anaCut_to_canonCut hw1a hw.cut_le
      have hgarb_c : fullArenaClauseGarbCore s1.core old_cref.toNat = true := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        dsimp only [s1]; rw [h_arena1, List.getElem?_set_self (by omega), Option.getD_some]
        simp [bv32_or_garb_garb]
      have hlen1 : s1.LengthsOk c :=
        ⟨{ hlen.core_ok with arena_len_arr := har1_len }, hlen.scratch_ok⟩
      have hnd1 : FullArenaVarsNodup s1 := fullArenaVarsNodup_markGarb hnd hrefs1 hgarb_c
        fun r hr hne => ⟨(hprops1 r hr).2.1, (hprops1 r hr).2.2 hne⟩
      have ha1_eq : s.core.arena.set old_cref.toNat
          (s.core.arena[old_cref.toNat]'(by omega) ||| 0x00080000#32) = arena1 := by
        rw [← hd_eq]; exact h_arena1.symm
      have hget_ag {xs : List (BitVec 32)} (hx : xs = arena1)
          (h1 : (old_cref + 2#64).toNat < xs.length) :
          s.core.arena_garbage + 3#64 + (xs[(old_cref + 2#64).toNat]'h1).setWidth 64 = ag1 := by
        subst hx; rw [h_ag1]; congr 1; congr 1; exact getElem_eq_of_idx hcr2
      have hdone_counts (ni1 nr1 : BitVec 64) (ml : Mem 64)
          (hml : (FullMem c { s1 with core :=
            { s1.core with num_irred := ni1, num_redundant := nr1 } } ⋆ R) ml) : Q () ml :=
        hQ arena1 ag1 ni1 nr1 ml
          ⟨{ hlen1.core_ok with arena_len_arr := har1_len }, hlen.scratch_ok⟩
          (m5_fullWitnessCut_with_counts hw1 ni1 nr1) hnd1 hrefs1
          (fun r hr => ⟨(hprops1 r hr).2.1, fun hne => (hprops1 r hr).2.2 (hne rfl)⟩) hml
      have hnc_z : (new_confl.setWidth 64).toNat = new_confl.toNat :=
        zext_toNat new_confl (by decide)
      have hcore1_eq {ml : Mem 64} {a' : List (BitVec 32)} {g' : BitVec 64}
          (ha : a' = arena1) (hg : g' = ag1)
          (hm' : (FullMem c { s with core := { s.core with arena := a', arena_garbage := g' } }
            ⋆ R) ml) : (FullMem c s1 ⋆ R) ml := by
        subst ha hg; exact hm'
      c0_hsteps_nogrp
      · exact hsame
      · refine wp_unroll_group fun Jtop hJtop => ?_
        have hm_s1 : (FullMem c s1 ⋆ R) _ := hcore1_eq ha1_eq (hget_ag ha1_eq _) ‹_›
        c0_hsteps_nogrp
        · -- `(dhdr & PH_RED) != 0`: decrement `num_redundant`, clamp `ar[new_confl]` glue
          refine wp_join_group (ts := [])
            (fun _ mnr => ∃ nr1 : BitVec 64,
              (FullMem c { s1 with core := { s1.core with num_redundant := nr1 } } ⋆ R) mnr) ?_ ?_
          · rintro _ ⟨⟩ mnr ⟨nr1, hmnr⟩
            refine wp_unroll_group fun Jred_out hJred_out => ?_
            c0_hsteps_nogrp
            · exact hdone_counts s.core.num_irred nr1 mnr hmnr
            · have hnc_ref := hnew_ref (by assumption)
              have hnc_wf := hw.arena.refs_wf new_confl.toNat hnc_ref
              have hnc_bd : new_confl.toNat < arena1.length := by rw [har1_len]; omega
              have hnc_ref1 : new_confl.toNat ∈ fullArenaClauseRefsCore s1.core := by
                rw [hrefs1]; exact hnc_ref
              have har_nc : fullArenaHdrCore s1.core new_confl.toNat =
                  arena1[new_confl.toNat]'hnc_bd := by
                unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hnc_bd, Option.getD_some]
              fa_fast_steps
              · let dg : BitVec 32 := (s.core.arena[old_cref.toNat]'(by omega)) &&& 0x0007FFFF#32
                let arena2 := s1.core.arena.set new_confl.toNat
                  ((fullArenaHdrCore s1.core new_confl.toNat &&& ~~~0x0007FFFF#32) ||| dg)
                obtain ⟨hw2a, hrefs2, hprops2⟩ := m5_arenaSetGlue_preserves_fullWitnessCut
                  hlen1.core_ok hw1a hnc_ref1 dg (m5_bv32_and_glue_lt _) s.core.num_irred nr1
                have hlen2 : ({ s1 with core := { s1.core with
                    arena := arena2, num_redundant := nr1 } } : FullState).LengthsOk c :=
                  ⟨{ hlen1.core_ok with arena_len_arr := by simp [arena2, s1, har1_len] },
                    hlen.scratch_ok⟩
                have hnd2 : FullArenaVarsNodup { s1 with core :=
                    { s1.core with arena := arena2, num_redundant := nr1 } } := fun r hr hng2 => by
                  change r ∈ fullArenaClauseRefsCore _ at hr; rw [hrefs2] at hr
                  obtain ⟨_, hgarb2, hlits2⟩ := hprops2 r hr
                  change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup
                  rw [hlits2]; refine hnd1 r hr ?_
                  change fullArenaClauseGarbCore s1.core r = false; rw [← hgarb2]; exact hng2
                let ar2_g := s1.core.arena.set (new_confl.setWidth 64).toNat
                  ((s1.core.arena[(new_confl.setWidth 64).toNat]'(by rw [hnc_z]; exact hnc_bd)
                    &&& ~~~0x0007FFFF#32) ||| dg)
                have har2_eq : ar2_g = arena2 := by
                  dsimp only [ar2_g, arena2, s1]
                  exact list_set_congr hnc_z
                    (by rw [getElem_eq_of_idx (hj := hnc_bd) hnc_z, har_nc])
                refine hQ arena2 ag1 s.core.num_irred nr1 _ hlen2
                  (m5_anaCut_to_canonCut hw2a hw.cut_le) hnd2 (hrefs2.trans hrefs1) (fun r hr => by
                    have hr1 : r ∈ fullArenaClauseRefsCore s1.core := by rw [hrefs1]; exact hr
                    refine ⟨(hprops2 r hr1).2.2.trans (hprops1 r hr).2.1, fun hne => ?_⟩
                    exact (hprops2 r hr1).2.1.trans ((hprops1 r hr).2.2 (hne rfl))) ?_
                exact fullMem_of_eq (s1 := { s1 with core :=
                  { s1.core with arena := ar2_g, num_redundant := nr1 } })
                  ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl
              · exact hdone_counts s.core.num_irred nr1 mnr hmnr
              · exact hdone_counts s.core.num_irred nr1 mnr hmnr
          · intro Jnr hJnr; c0_hsteps_nogrp
            · exact hJnr () _ ⟨s.core.num_redundant - 1#64, ‹_›⟩
            · exact hJnr () _ ⟨s.core.num_redundant, hm_s1⟩
        · -- `(dhdr & PH_RED) == 0`: decrement `num_irred`, optionally clear `PH_RED` on `new_confl`
          refine wp_join_group (ts := [])
            (fun _ mni => ∃ ni1 : BitVec 64,
              (FullMem c { s1 with core := { s1.core with num_irred := ni1 } } ⋆ R) mni) ?_ ?_
          · rintro _ ⟨⟩ mni ⟨ni1, hmni⟩
            refine wp_unroll_group fun Jir_out hJir_out => ?_
            c0_hsteps_nogrp
            · exact hdone_counts ni1 s.core.num_redundant mni hmni
            · have hnc_ref := hnew_ref (by assumption)
              have hnc_wf := hw.arena.refs_wf new_confl.toNat hnc_ref
              have hnc_bd : new_confl.toNat < arena1.length := by rw [har1_len]; omega
              have hnc_ref1 : new_confl.toNat ∈ fullArenaClauseRefsCore s1.core := by
                rw [hrefs1]; exact hnc_ref
              have har_nc : fullArenaHdrCore s1.core new_confl.toNat =
                  arena1[new_confl.toNat]'hnc_bd := by
                unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hnc_bd, Option.getD_some]
              let arena2 := s1.core.arena.set new_confl.toNat
                (fullArenaHdrCore s1.core new_confl.toNat &&& 0xFFBFFFFF#32)
              have hstep_red (ni2 nr2 : BitVec 64) (ml : Mem 64)
                  (hm2 : (FullMem c { s1 with core :=
                    { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } ⋆ R)
                    ml) : Q () ml := by
                obtain ⟨hw2a, hrefs2, hprops2⟩ :=
                  clearRed_preserves_fullWitnessCut hlen1.core_ok hw1a hnc_ref1 ni2 nr2
                have hlen2 : ({ s1 with core := { s1.core with
                    arena := arena2, num_irred := ni2, num_redundant := nr2 } } :
                    FullState).LengthsOk c :=
                  ⟨{ hlen1.core_ok with arena_len_arr := by simp [arena2, s1, har1_len] },
                    hlen.scratch_ok⟩
                have hnd2 : FullArenaVarsNodup { s1 with core :=
                    { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } :=
                  fun r hr hng2 => by
                    change r ∈ fullArenaClauseRefsCore _ at hr; rw [hrefs2] at hr
                    obtain ⟨_, hgarb2, hlits2⟩ := hprops2 r hr
                    change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup
                    rw [hlits2]; refine hnd1 r hr ?_
                    change fullArenaClauseGarbCore s1.core r = false; rw [← hgarb2]; exact hng2
                exact hQ arena2 ag1 ni2 nr2 ml hlen2 (m5_anaCut_to_canonCut hw2a hw.cut_le) hnd2
                  (hrefs2.trans hrefs1) (fun r hr => by
                    have hr1 : r ∈ fullArenaClauseRefsCore s1.core := by rw [hrefs1]; exact hr
                    refine ⟨(hprops2 r hr1).2.2.trans (hprops1 r hr).2.1, fun hne => ?_⟩
                    exact (hprops2 r hr1).2.1.trans ((hprops1 r hr).2.2 (hne rfl))) hm2
              have hnot_ff : ~~~(4194304#32 : BitVec 32) = 0xFFBFFFFF#32 := by decide
              let ar2_c0 := s1.core.arena.set (new_confl.setWidth 64).toNat
                (s1.core.arena[(new_confl.setWidth 64).toNat]'(by rw [hnc_z]; exact hnc_bd) &&&
                  ~~~(4194304#32 : BitVec 32))
              have har2_eq : ar2_c0 = arena2 := by
                dsimp only [ar2_c0, arena2, s1]
                exact list_set_congr hnc_z
                  (by rw [getElem_eq_of_idx (hj := hnc_bd) hnc_z, har_nc, hnot_ff])
              fa_fast_steps
              · exact hstep_red (ni1 + 1#64) (s.core.num_redundant - 1#64) _
                  (fullMem_of_eq (s1 := { s1 with core := { s1.core with
                    num_irred := ni1 + 1#64, num_redundant := s.core.num_redundant - 1#64,
                    arena := ar2_c0 } }) ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
              · exact hstep_red (ni1 + 1#64) s.core.num_redundant _
                  (fullMem_of_eq (s1 := { s1 with core := { s1.core with
                    num_irred := ni1 + 1#64, arena := ar2_c0 } })
                    ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
              · exact hdone_counts ni1 s.core.num_redundant mni hmni
          · intro Jni hJni; c0_hsteps_nogrp
            · exact hJni () _ ⟨s.core.num_irred - 1#64, ‹_›⟩
            · exact hJni () _ ⟨s.core.num_irred, hm_s1⟩
  · fa_fast_steps
    · exact hsame
    all_goals (exfalso; exact hct ‹_›)

end AnalyzeRsnAndOtfsProof

end LeanQbe.T.Examples.Kissat.FullM5HeurCore
