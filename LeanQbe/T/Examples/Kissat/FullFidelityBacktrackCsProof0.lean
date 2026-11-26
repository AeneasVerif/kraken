/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof0
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas4b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0b
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-11 `S11-7` Consistent-State Backtrack & Conflict Caller Proofs — Part 0
(`FullFidelityBacktrackCsProof0`)

Plain `public section` (`0` `@[expose]`, `0` new `import all`, `std3`, `XPost`-polymorphic):
1. `fid11_save_target_best_wp`: `fid11_save_target_best` (`assigned = cur_vars - unassigned`)
   against canonical `Full.fullSaveTargetBestSpec`.
2. `fid11_backtrack_cs_wp`: default consistent-state `fid11_backtrack_cs` against canonical
   `Full.fullBacktrackSpec`.
3. `fid11_backtrack_ac_wp`: `fid11BacktrackAcFn` (`full_backtrack_ac_fid`) against canonical
   `Full.fullBacktrackSpec`.
4. `fid11_one_lit_confl_wp`, `fid11_learn_clause_wp`, `fid11_learn_clause_m6_wp`: transported
   parametrically from Step-5 / Step-7 / Step-10 proofs via `Func.Wf`-driven callee renaming.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep10
open scoped FullArenaTactics FullHeurWalkTactics
open FullBridgeHelpers

/-! ## 1. `fid11_save_target_best_wp` (`Full.fullSaveTargetBestSpec`) -/

theorem fid11_save_target_best_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Func.wp Γ fid11SaveTargetBestFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hcv_le := hok.cur_vars_le; obtain hvl := hok.vals_len
  unfold Func.wp fid11SaveTargetBestFn fid11_save_target_best_body
  dsimp only
  c0_to_group
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨probePres_refl s, s.scratch.target_assigned,
      s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, rfl⟩ hm
  · refine wp_join_group (ts := [i64]) (fun _ m_a => m_a = m)
      (fun _ _ m_a hm_a => ?_) (fun _ hJa => by
        c0_steps
        · exact hJa (_, ()) m rfl
        · exact hJa (0#64, ()) m rfl)
    subst m_a
    c0_to_group
    refine wp_join_group
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

/-! ## 2. `fid11_backtrack_cs_wp` & `fid11_backtrack_ac_wp` (`Full.fullBacktrackSpec`) -/

private theorem cs_witness_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (p : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt
    trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain
    vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff
    lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt
    reason_inv := hw.reason_inv, reason_lit_mem := hw.reason_lit_mem }

private theorem cs_otfs_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) (p : BitVec 64) :
    FullOtfsWitnessInv c F0 F_cur { k with probing := p } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt
    trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain
    vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff
    lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest
    levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound
    trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none
    frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt
    reason_inv_below := hw.reason_inv_below, reason_lit_mem_below := hw.reason_lit_mem_below }

private theorem cs_lengths_with_probing {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (p : BitVec 64) :
    ({ s with core := { s.core with probing := p } } : FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with cur_vars_le := hlen.core_ok.cur_vars_le }, hlen.scratch_ok⟩

private theorem cs_bt_noop_clear {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem cs_bt_scr_trans {sc sc1 sc2 : FullScratch}
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

private theorem cs_bt_scr_save {sc sc1 : FullScratch}
    (h : ∃ ta' ba' pt' pb', sc1 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb' }) :
    ∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc1 = { sc with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
      heap := hp', pos := ps', heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } := by
  obtain ⟨ta, ba, pt, pb, hsc⟩ := h
  exact ⟨ta, ba, pt, pb, sc.heap, sc.pos, sc.heap_len, sc.q_search_idx, sc.q_search_stamp, hsc⟩

/-- Default consistent-state `full_backtrack` (`fid11_backtrack_cs`) saves target/best phases
from the current consistent trail before backtracking and satisfies `Full.fullBacktrackSpec`. -/
theorem fid11_backtrack_cs_wp (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X → Func.wp Γ fid11BacktrackFn.body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt_mx, htrl_lits, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp fid11BacktrackFn fid11_backtrack_cs_body
  dsimp only
  c0_split
  · c0_hsteps
    have hle : s.core.cur_level ≤ target_lvl.toNat := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; exact hc
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos s.core.trail_end
      s.core.propagated s.core.cur_level s.core.unassigned s.scratch m hlen (le_refl _)
      hlen.core_ok.propagated_le (Nat.min_eq_left hle).symm (probePres_refl s)
      (cs_bt_scr_save ⟨_, _, _, _, rfl⟩) htrl_lits
      (fun ⟨_, _, hw⟩ => cs_bt_noop_clear (hw.elim FullWitnessInv.toOtfs id) hle)
      (fun _ _ hw _ => hw) (fun _ _ _ hlt => False.elim (by omega)) hm
  · have htgt_lt : target_lvl.toNat < s.core.cur_level := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; omega
    clear hc
    c0_call hSave
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    intro _ s0 m0 hc0 hlen0 hpres0 hm0
    rcases s0 with ⟨c0, sc0⟩; obtain ⟨hpres0, hscr0⟩ := hpres0
    subst hc0
    change (FullMem c { core := s.core, scratch := sc0 } ⋆ R) m0 at hm0
    clear hm
    c0_hsteps
    let s0p : FullState := { core := { s.core with probing := 1#64 }, scratch := sc0 }
    have hm0p : (FullMem c s0p ⋆ R) m := hm
    c0_call hBtRaw
    refine ⟨c, s0p, R, rfl, cs_lengths_with_probing hlen0 1#64, hcl64, htgt_mx, htrl_lits,
      hm0p, ?_⟩
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1 s0_bt
      hlen1 hte1 hprop1 hcl1 hpres1 hscr1 htrl1 _ hclr1 hw_w1 hw_o1 hm1
    clear hm
    c0_hsteps
    let s_fin : FullState :=
      { s with
        core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass' }
        scratch := sc' }
    have hlen_fin : s_fin.LengthsOk c := cs_lengths_with_probing hlen1 s.core.probing
    exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m hlen_fin hte1 hprop1 hcl1
      (probePres_trans hpres0 hpres1) (cs_bt_scr_trans (cs_bt_scr_save hscr0) hscr1) htrl1
      (fun ⟨F0, Fc, hw⟩ =>
        hclr1 ⟨F0, Fc, hw.elim (fun w => Or.inl (cs_witness_with_probing w 1#64))
          (fun o => Or.inr (cs_otfs_with_probing o 1#64))⟩)
      (fun F0 Fc hw hle => cs_witness_with_probing
        (hw_w1 F0 Fc (cs_witness_with_probing hw 1#64) hle) s.core.probing)
      (fun F0 Fc ho hlt => cs_witness_with_probing
        (hw_o1 F0 Fc (cs_otfs_with_probing ho 1#64) hlt) s.core.probing)
      hm

/-- After-conflict `full_backtrack_ac_fid` equals `FullM5HeurCore.full_backtrack_m5_body` and
satisfies canonical `Full.fullBacktrackSpec`. -/
theorem fid11_backtrack_ac_wp (Γ : Env)
    (hBtRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X → Func.wp Γ fid11BacktrackAcFn.body a m Q X :=
  fun a m Q X hs => full_backtrack_m5_wp Γ hBtRaw hSave a m Q X hs

/-! ## 3. `Wf`-Driven Callee-Rename Transport & Conflict Caller Proofs -/

private def DiagV (G : Ctx Val Val) : Prop :=
  ∀ (t : Ty) (v₁ v₂ : Val t), ⟨t, v₁, v₂⟩ ∈ G → v₁ = v₂

private def DiagL (D : Ctx Cont Cont) : Prop :=
  ∀ (ts : List Ty) (j₁ j₂ : Cont ts), ⟨ts, j₁, j₂⟩ ∈ D → j₁ = j₂

private theorem diagV_cons {G : Ctx Val Val} (hG : DiagV G) (t : Ty) (v : Val t) :
    DiagV (⟨t, v, v⟩ :: G) := by
  intro u a b hm
  rcases List.mem_cons.mp hm with h | h
  · cases h; rfl
  · exact hG u a b h

private theorem diagV_tupZip :
    ∀ {ts : List Ty} (xs : Tup Val ts) {G : Ctx Val Val}, DiagV G →
      DiagV (Tup.zip xs xs ++ G)
  | [], (), _, hG => hG
  | t :: _, (x, xs), _, hG => by
    rw [Tup.zip, List.cons_append]
    exact diagV_cons (diagV_tupZip xs hG) t x

private theorem diagL_cons {D : Ctx Cont Cont} (hD : DiagL D) (ts : List Ty) (j : Cont ts) :
    DiagL (⟨ts, j, j⟩ :: D) := by
  intro us a b hm
  rcases List.mem_cons.mp hm with h | h
  · cases h; rfl
  · exact hD us a b h

private theorem diagL_tupZip :
    ∀ {sig : List (List Ty)} (Js : Tup Cont sig) {D : Ctx Cont Cont}, DiagL D →
      DiagL (Tup.zip Js Js ++ D)
  | [], (), _, hD => hD
  | ts :: _, (J, Js), _, hD => by
    rw [Tup.zip, List.cons_append]
    exact diagL_cons (diagL_tupZip Js hD) ts J

private theorem arg_eq_of_rel {G : Ctx Val Val} (hG : DiagV G) {t : Ty}
    {a₁ a₂ : Arg Val t} (hr : ArgRel G t a₁ a₂) : a₁ = a₂ := by
  cases hr with
  | var hm => rw [hG _ _ _ hm]
  | imm _ => rfl

private theorem trel_eq_of_rel {G : Ctx Val Val} (hG : DiagV G) :
    ∀ {ts : List Ty} {xs₁ xs₂ : Tup (Arg Val) ts}, TRel (ArgRel G) xs₁ xs₂ → xs₁ = xs₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha hxs => by
    rw [arg_eq_of_rel hG ha, trel_eq_of_rel hG hxs]

private theorem op_eq_of_rel {G : Ctx Val Val} (hG : DiagV G) {ts : List Ty}
    {op₁ op₂ : Op Val ts} (hr : OpRel G op₁ op₂) : op₁ = op₂ := by
  cases hr with | mk _ h => rw [trel_eq_of_rel hG h]

private theorem op_wp_iff {ts : List Ty} (op : Op Val ts) {P₁ P₂ : Tup Val ts → Prop}
    (h : ∀ r, P₁ r ↔ P₂ r) : op.wp P₁ ↔ op.wp P₂ :=
  ⟨fun h1 => Op.wp_mono (fun r hr => (h r).mp hr) h1,
   fun h2 => Op.wp_mono (fun r hr => (h r).mpr hr) h2⟩

mutual
private theorem wf_wp_renameExpr (σ : Sym → Sym) (Γ : Env) {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ {G : Ctx Val Val} {D : Ctx Cont Cont} {e₁ e₂ : Expr Val Cont rs},
      _root_.LeanQbe.T.Wf G D e₁ e₂ → DiagV G → DiagL D →
      ∀ m, wp (fun f as bs => Γ (σ f) as bs) Q X e₁ m ↔
        wp Γ Q X (renameExprCalls σ e₂) m
  | _, _, _, _, .let_ hop hk, hG, hD, m => by
    rw [op_eq_of_rel hG hop]
    exact op_wp_iff _ fun r =>
      wf_wp_renameExpr σ Γ (hk r r) (diagV_tupZip r hG) hD m
  | _, _, _, _, .load t ha hk, hG, hD, m => by
    rw [arg_eq_of_rel hG ha]; dsimp only [wp, renameExprCalls]
    exact exists_congr fun v => and_congr_right fun _ =>
      wf_wp_renameExpr σ Γ (hk v v) (diagV_cons hG t v) hD m
  | _, _, _, _, .store hv ha hk, hG, hD, m => by
    rw [arg_eq_of_rel hG hv, arg_eq_of_rel hG ha]; dsimp only [wp, renameExprCalls]
    exact and_congr_right fun _ => wf_wp_renameExpr σ Γ hk hG hD _
  | _, _, _, _, .call f hargs hk, hG, hD, m => by
    rw [trel_eq_of_rel hG hargs]; dsimp only [wp, renameExprCalls]
    exact exists_congr fun P => exists_congr fun E =>
      and_congr_right fun _ => and_congr_left fun _ =>
        forall_congr' fun r => forall_congr' fun m' =>
          imp_congr_right fun _ => wf_wp_renameExpr σ Γ (hk r r) (diagV_tupZip r hG) hD m'
  | _, _, _, _, .jnz hc ht he, hG, hD, m => by
    rw [arg_eq_of_rel hG hc]; dsimp only [wp, renameExprCalls]
    exact and_congr (imp_congr_right fun _ => wf_wp_renameExpr σ Γ ht hG hD m)
      (imp_congr_right fun _ => wf_wp_renameExpr σ Γ he hG hD m)
  | _, _, _, _, .jump hj hargs, hG, hD, _ => by
    rw [hD _ _ _ hj, trel_eq_of_rel hG hargs]; exact Iff.rfl
  | _, _, _, _, .ret hvs, hG, _, _ => by
    rw [trel_eq_of_rel hG hvs]; exact Iff.rfl
  | _, _, _, _, .exit _ hargs, hG, _, _ => by
    rw [trel_eq_of_rel hG hargs]; exact Iff.rfl
  | _, _, _, _, .hlt, _, _, _ => Iff.rfl
  | _, _, _, _, .group hb hk, hG, hD, m => by
    dsimp only [wp, renameExprCalls]
    refine forall_congr' fun Js => imp_congr ?_ ?_
    · exact wfB_closed_renameBlocks σ Γ (hb Js Js) hG (diagL_tupZip Js hD) Js
    · exact wf_wp_renameExpr σ Γ (hk Js Js) hG (diagL_tupZip Js hD) m

private theorem wfB_closed_renameBlocks (σ : Sym → Sym) (Γ : Env) {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ {G : Ctx Val Val} {D : Ctx Cont Cont} {sig : List (List Ty)}
      {bs₁ bs₂ : Blocks Val Cont rs sig},
      _root_.LeanQbe.T.WfB G D bs₁ bs₂ → DiagV G → DiagL D → ∀ Js,
      Closed (fun f as bs => Γ (σ f) as bs) Q X bs₁ Js ↔
        Closed Γ Q X (renameBlocksCalls σ bs₂) Js
  | _, _, _, _, _, .nil, _, _, () => Iff.rfl
  | _, _, _, _, _, .cons hb hbs, hG, hD, (J, Js) => by
    unfold Closed renameBlocksCalls
    exact and_congr
      (forall_congr' fun xs => forall_congr' fun m =>
        imp_congr_left (wf_wp_renameExpr σ Γ (hb xs xs) (diagV_tupZip xs hG) hD m))
      (wfB_closed_renameBlocks σ Γ hbs hG hD Js)
end

private theorem diagV_tupZip_nil :
    ∀ {ts : List Ty} (xs : Tup Val ts), DiagV (Tup.zip xs xs) := by
  intro ts xs
  have h := diagV_tupZip xs (G := []) (fun _ _ _ h => by cases h)
  rwa [List.append_nil] at h

private theorem func_wp_of_renameFuncCalls {as rs : List Ty} (σ : Sym → Sym) (f : Func as rs)
    (hwf : Func.Wf f) (Γ : Env) {spec : Spec as rs}
    (hwp : ∀ a m Q X, spec a m Q X → Func.wp (fun fn as' bs' => Γ (σ fn) as' bs') f a m Q X) :
    ∀ a m Q X, spec a m Q X → Func.wp Γ (renameFuncCalls σ f) a m Q X :=
  fun a m Q X hs =>
    (wf_wp_renameExpr σ Γ (hwf Val Val Cont Cont a a) (diagV_tupZip_nil a)
      (fun _ _ _ h => by cases h) m).mp (hwp a m Q X hs)

/-- Rebound `"full_one_lit_confl"` routing `"full_backtrack"` to `"full_backtrack_ac_fid"`. -/
theorem fid11_one_lit_confl_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAss : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullOneLitConflSpec a m Q X → Func.wp Γ fid11OneLitConflFn.body a m Q X :=
  func_wp_of_renameFuncCalls pr3BtAcMap full_one_lit_confl_m5_body full_one_lit_confl_m5_wf Γ
    (full_one_lit_confl_m5_wp _ hDefrag hDet hBtAc hAss hUnw hPush)

/-- Rebound `"full_learn_clause"` routing `"full_backtrack"` to `"full_backtrack_ac_fid"`. -/
theorem fid11_learn_clause_wp (Γ : Env)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullLearnClauseSpec a m Q X → Func.wp Γ fid11LearnClauseFn.body a m Q X :=
  func_wp_of_renameFuncCalls pr3BtAcMap FullFidelityStep7.full_learn_clause_body
    full_learn_clause_step7_wf Γ
    (full_learn_clause_step7_wp _ hBtAc hAsgn hDnl hDefrag hRed hAddCl hEsub)

/-- Rebound `"full_learn_clause_m6"` routing `"full_backtrack"` to `"full_backtrack_ac_fid"`. -/
theorem fid11_learn_clause_m6_wp (Γ : Env)
    (hBtAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, FullM6Orch.m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ a m Q X, step10LearnClauseM6Spec a m Q X → Func.wp Γ fid11LearnClauseM6Fn.body a m Q X :=
  func_wp_of_renameFuncCalls pr3BtAcMap FullFidelityStep10.full_learn_clause_m6_body
    full_learn_clause_m6_step10_wf Γ
    (full_learn_clause_m6_step10_wp _ hBtAc hAsgn hDnl hDefrag hRedM6 hAddCl hEsub)

end LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
