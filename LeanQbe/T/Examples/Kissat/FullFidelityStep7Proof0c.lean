/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof2
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofAnalyze
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof1
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3b1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 7 Proofs — `full_bump_analyzed_m6_hdr` (`FullFidelityStep7Proof0c`)

Proves the Step-7 `full_bump_analyzed_m6_hdr` (`M6_DELAY_BUMPREASONS` gating, `search_ticks`
accounting, split `stable` bump) against `m6aBumpAnalyzedSpecP M6ExtW2bPres`, and rewires the
Stage-0 generic (`Pext`-parameterized) adapter lemmas at `Pext := M6ExtW2bPres`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0c

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

/-! ## Rewires at `Pext := M6ExtW2bPres` -/

theorem full_restore_bump_ana_m6_hdr_step7_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ full_restore_bump_ana_m6_hdr_body a m Q X :=
  full_restore_bump_ana_m6_hdr_wp_gen M6ExtW2bPres M6ExtW2bPres.refl Γ hBumpAna hClearAna

theorem full_ana_failed_lit_m6_hdr_step7_wp (Γ : Env)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ full_ana_failed_lit_m6_hdr_body a m Q X :=
  full_ana_failed_lit_m6_hdr_wp_gen M6ExtW2bPres M6ExtW2bPres.refl Γ hClear hBumpAna hBacktrack
    hAssignLvl

theorem full_analyze_core_m6_step7_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, FullM7Proof.m7Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, FullM8CoreParity.m8MinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearn : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ FullM8FidV12.m8_analyze_core_m6_body a m Q X :=
  FullM8CoreParity.m8_analyze_core_m6_m8_wp_gen M6ExtW2bPres Γ hOneLit hFailed hDeduce hRestore
    hMinShrink hTick hEma hLearn

/-! ## Helpers (adapted from `FullM6OrchAdaptersProof3`) -/

section Helpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem s7b_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem s7b_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem s7b_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

private theorem s7b_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

attribute [local bv_c0] s7b_bv32_lshr1 s7b_bv32_setWidth64 s7b_sext32_64_1 s7b_bv32_lshr_nat1

private theorem s7b_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem s7b_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem s7b_nodup_of_getElem_ne {α : Type} :
    ∀ (xs : List α),
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, s7b_nodup_of_getElem_ne _ fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

private theorem s7b_nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hmiss : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  refine s7b_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take, List.length_set] at hi hj
  simp only [List.getElem_map, List.getElem_take]
  have hi_n : i < n := by omega
  rw [List.getElem_set_ne (by omega)]
  by_cases hj_n : j = n
  · subst hj_n; rw [List.getElem_set_self (by rw [List.length_set]; exact hn)]
    have hm := hmiss i hi_n
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hm
  · rw [List.getElem_set_ne (by omega)]
    have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    intro heq
    have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
    simp only [List.getElem_map, List.getElem_take] at hne
    exact hne heq

private theorem s7b_nodup_take_pred {xs : List (BitVec 32)} {n : Nat}
    (hpos : 0 < n) (hnd : ((xs.take n).map BitVec.toNat).Nodup) :
    ((xs.take (n - 1)).map BitVec.toNat).Nodup := by
  refine s7b_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take] at hi hj
  have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
  simpa only [List.getElem_map, List.getElem_take] using hne

/-- Post-state shape of `m6aBumpAnalyzedSpecP`: `mrk`/`min_clr_len` and the whole scratch. -/
private abbrev bumpSt2 (s : FullState) (sc : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat) :
    FullState :=
  { s with core := { s.core with mrk := mrk, min_clr_len := mcl }, scratch := sc }

/-- Scan-loop state over base scratch `sc0`: `mrk`, `min_clr_len`, `work_stk1`, `search_ticks`. -/
private abbrev mkBumpState (s : FullState) (sc0 : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat)
    (ws1 : List (BitVec 32)) (tk : BitVec 64) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { sc0 with work_stk1 := ws1, search_ticks := tk } }

private theorem mkBumpState_lengths {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    (hlen : ({ s with scratch := sc0 } : FullState).LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (mkBumpState s sc0 mrk mcl ws1 tk).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem bump_push_marksCov {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws1 tk))
    (hov_cv : ov.toNat < s.core.cur_vars) (hmcl_cv : mcl < s.core.cur_vars)
    (hmrk0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c
      (mkBumpState s sc0 (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov) tk) := by
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hnd hfwd hbak
  have hmcl_ws : mcl < ws1.length := by rw [hws1]; omega
  refine ⟨hmcl_cv, s7b_nodup_map_take_append hmcl_ws hnd (fun k hk heq => ?_),
    fun k hk => ?_, fun v hv hnz => ?_⟩
  · exact (hfwd k hk).2 (by simpa [heq] using hmrk0)
  · dsimp only [mkBumpState] at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · have hk_cov := hfwd k hlt
      have hne : (ws1[k]?.getD 0#32).toNat ≠ ov.toNat := fun heq => by
        rw [heq] at hk_cov; exact hk_cov.2 hmrk0
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hne.symm]
      exact hk_cov
    · rw [List.getElem?_set_self hmcl_ws, Option.getD_some,
        List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some]
      exact ⟨hov_cv, by decide⟩
  · dsimp only [mkBumpState] at hnz ⊢
    by_cases hveq : v = ov.toNat
    · refine ⟨mcl, Nat.lt_succ_self _, ?_⟩
      subst hveq
      rw [List.getElem?_set_self hmcl_ws, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      rwa [List.getElem?_set_ne (by omega)]

private theorem bump_pop_marksCov {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws1 tk)) (hpos : 0 < mcl) :
    let hmcl_ws : mcl - 1 < ws1.length := by
      have hm1 := hcov.1; dsimp only [mkBumpState] at hm1; rw [hws1]; omega
    let rv := ws1[mcl - 1]'hmcl_ws
    FullAnaMarksCov c (mkBumpState s sc0 (mrk.set rv.toNat 0#8) (mcl - 1) ws1 tk) := by
  intro hmcl_ws rv
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hmcl_cv0 hnd hfwd hbak
  have hrv_lt : rv.toNat < s.core.cur_vars := by
    have := (hfwd (mcl - 1) (by omega)).1
    simpa [rv, List.getElem?_eq_getElem hmcl_ws] using this
  dsimp only [FullAnaMarksCov, mkBumpState]
  refine ⟨by omega, s7b_nodup_take_pred hpos hnd, fun k hk => ?_, fun v hv hnz => ?_⟩
  · have hk_cov := hfwd k (by omega)
    have hne : (ws1[k]?.getD 0#32).toNat ≠ rv.toNat := by
      have hk_t : k < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hr_t : mcl - 1 < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hdiff := List.pairwise_iff_getElem.mp hnd k (mcl - 1) hk_t hr_t (by omega)
      simp only [List.getElem_map, List.getElem_take] at hdiff
      rw [List.getElem?_eq_getElem (by omega : k < ws1.length), Option.getD_some]
      exact hdiff
    rw [List.getElem?_set_ne hne.symm]
    exact hk_cov
  · have hvne : v ≠ rv.toNat := fun hveq => by
      subst hveq
      rw [List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some] at hnz
      exact hnz rfl
    rw [List.getElem?_set_ne hvne.symm] at hnz
    obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
    rcases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt hi) with hlt | rfl
    · exact ⟨i, hlt, hieq⟩
    · exfalso; apply hvne; rw [← hieq]
      simp [rv, List.getElem?_eq_getElem hmcl_ws]

private theorem bump_perm_marksCov {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {mrk : List (BitVec 8)} {cnt : Nat} {ws1 ws' : List (BitVec 32)} {tk : BitVec 64}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hws1 : ws1.length = 2 * c.max_vars) (hws' : ws'.length = 2 * c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk cnt ws1 tk))
    (hperm : (ws'.take cnt).Perm (ws1.take cnt)) :
    FullAnaMarksCov c (mkBumpState s sc0 mrk cnt ws' tk) := by
  obtain ⟨hcnt_cv, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hcnt_cv hnd hfwd hbak
  have hcnt_ws1 : cnt ≤ ws1.length := by rw [hws1]; omega
  have hcnt_ws' : cnt ≤ ws'.length := by rw [hws']; omega
  refine ⟨hcnt_cv, (hperm.map BitVec.toNat).nodup_iff.mpr hnd, fun k hk => ?_,
    fun v hv hnz => ?_⟩
  · dsimp only [mkBumpState] at hk ⊢
    have hmem : ws'[k]'(by omega) ∈ ws1.take cnt := by
      rw [← hperm.mem_iff]
      have hk_t : k < (ws'.take cnt).length := by rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hk_t
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hj
    have hj_lt : j < cnt := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    rw [List.getElem_take] at hjeq
    have hcov_j := hfwd j hj_lt
    rw [List.getElem?_eq_getElem (by omega : k < ws'.length), Option.getD_some, ← hjeq]
    rwa [List.getElem?_eq_getElem (by omega : j < ws1.length), Option.getD_some] at hcov_j
  · dsimp only [mkBumpState] at hnz ⊢
    obtain ⟨j, hj, hjeq⟩ := hbak v hv hnz
    have hmem : ws1[j]'(by omega) ∈ ws'.take cnt := by
      rw [hperm.mem_iff]
      have hj_t : j < (ws1.take cnt).length := by rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hj_t
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hi
    have hi_lt : i < cnt := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    rw [List.getElem_take] at hieq
    refine ⟨i, hi_lt, ?_⟩
    rw [List.getElem?_eq_getElem (by omega : i < ws'.length), Option.getD_some, hieq]
    rwa [List.getElem?_eq_getElem (by omega : j < ws1.length), Option.getD_some] at hjeq

private theorem s7b_cov_of_core_eq {c : FullCfg} {s s' : FullState}
    (hcov : FullAnaMarksCov c s) (hc : s'.core = s.core)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) :
    FullAnaMarksCov c s' := by
  unfold FullAnaMarksCov at hcov ⊢; rw [hc, hws1]; exact hcov

end Helpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev BumpSt := List (BitVec 8) × Nat × List (BitVec 32) × BitVec 64

private abbrev bumpAllowInv (c : FullCfg) (s : FullState) (sc0 : FullScratch)
    (R_hdr : Mem 64 → Prop) (st : BumpSt) (m : Mem 64) : Prop :=
  st.1.length = c.max_vars ∧ st.2.2.1.length = 2 * c.max_vars ∧
  FullAnaMarksCov c (mkBumpState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ∧
  (FullMem c (mkBumpState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ⋆ R_hdr) m

/-- Join invariant after the gated reason-bumping block (`M6ExtW2bPres`-monotone `ext`). -/
private abbrev bumpPostInv (c : FullCfg) (s : FullState) (ext : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  ∃ (ext1 : List (BitVec 64)) (sc : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat),
    M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1) ∧
    (bumpSt2 s sc mrk mcl).LengthsOk c ∧ FullAnaMarksCov c (bumpSt2 s sc mrk mcl) ∧
    FullExtScratchPres s (bumpSt2 s sc mrk mcl) ∧ sc.work_stk2 = s.scratch.work_stk2 ∧
    (FullMem c (bumpSt2 s sc mrk mcl) ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m

private theorem bumpPostInv_of_w2a {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {ext ext1 ext2 : List (BitVec 64)} {R : Mem 64 → Prop}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws : List (BitVec 32)} {tk : BitVec 64}
    {s' : FullState} {m' : Mem 64}
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws tk))
    (hcore' : s'.core = (mkBumpState s sc0 mrk mcl ws tk).core) (hlen' : s'.LengthsOk c)
    (hsc' : M6HdrScratchPres (mkBumpState s sc0 mrk mcl ws tk) s')
    (hext2 : M6HdrExtOk ext2)
    (hw2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2)
    (hm' : (FullMem c s' ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m') :
    bumpPostInv c s ext R m' := by
  obtain ⟨core', sc'⟩ := s'
  dsimp only at hcore'
  subst hcore'
  refine ⟨ext2, sc', mrk, mcl, hext2, fun hi =>
    ⟨(hw2 (hinit1 hi).1).1, (hinit1 hi).2.trans (hw2 (hinit1 hi).1).2⟩, hlen',
    s7b_cov_of_core_eq hcov rfl hsc'.ws1,
    ⟨hsc'.extPres.1.trans hpre0.1, hsc'.extPres.2.trans hpre0.2⟩, hsc'.ws2.trans hws20, hm'⟩

/-! ## `full_bump_analyzed_m6_hdr` (Step 7, `m6aBumpAnalyzedSpecP M6ExtW2bPres`) -/

theorem full_bump_analyzed_m6_hdr_step7_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSortAna : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, m6aBumpAnalyzedSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ FullFidelityStep7.fidStep7BumpAnalyzedM6HdrFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hcov, hm, hQ⟩ := m6aBumpAnalyzedSpecP_elimP hs
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok
  have hcv_le := hco.cur_vars_le
  have hmrk0_len := hco.mrk_len
  change Func.wp Γ FullFidelityStep7.full_bump_analyzed_m6_hdr_body _ m Q X
  unfold Func.wp FullFidelityStep7.full_bump_analyzed_m6_hdr_body
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch ext m hlen hcov ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · let saved : Nat := s.core.min_clr_len
    have hsaved_le : saved ≤ s.core.cur_vars := hcov.1
    have hlim_lt : saved * 10 < 2 ^ 64 := by dsimp [saved]; omega
    have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
    have hlim_bv : (BitVec.ofNat 64 saved * 10#64).toNat = saved * 10 := by
      rw [BitVec.toNat_mul, bv64_ofNat_toNat (by omega),
        show (10#64 : BitVec 64).toNat = 10 from rfl, Nat.mod_eq_of_lt hlim_lt]
    have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
      bv64_ofNat_toNat hcv_lt64
    refine wp_join_group (ts := [])
      (fun () m2 => bumpPostInv c s ext R m2)
      (fun _ () m2 ⟨ext1, sc2, mrk2, mcl2, hext1, hinit1, hlen2, hcov2, hpre2, hws22, hm2⟩ => ?_)
      (fun Jallow hJallow => ?_)
    · -- after the gated block: `cnt`, then the split `stable` bump
      let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
      have hmcl2_cv : mcl2 ≤ s.core.cur_vars := hcov2.1
      have hmrk2 : mrk2.length = c.max_vars := hlen2.core_ok.mrk_len
      have hws2 : sc2.work_stk1.length = 2 * c.max_vars := hlen2.scratch_ok.work_stk1_len
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mf => Q () mf)
        (fun _ () mf hf => by rw [Blocks.get_here]; c0_hsteps <;> exact hf)
        (fun Jfin hJfin => ?_)
      c0_hsteps_nogrp
      · -- `stable == 0`: optional sort, then `full_queue_mtf` loop
        refine wp_join_group (ts := [])
          (fun () m3 => ∃ ws3, ws3.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkBumpState s sc2 mrk2 mcl2 ws3 sc2.search_ticks) ∧
            (FullMem c (mkBumpState s sc2 mrk2 mcl2 ws3 sc2.search_ticks) ⋆ R_hdr) m3)
          (fun _ () m3 ⟨ws3, hws3, hcov3, hm3⟩ => ?_)
          (fun Jsrt hJsrt => ?_)
        · let s3 := mkBumpState s sc2 mrk2 mcl2 ws3 sc2.search_ticks
          have hlen3 : s3.LengthsOk c :=
            ⟨hlen2.core_ok, { hlen2.scratch_ok with work_stk1_len := hws3 }⟩
          c0_hsteps_nogrp
          refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
            (proj := fun st => BitVec.ofNat 64 st.1)
            (μ := fun st => mcl2 - st.1)
            (Inv := fun st mk => st.1 ≤ mcl2 ∧
              let sk : FullState := { s3 with scratch := st.2 }
              sk.LengthsOk c ∧ FullAnaMarksCov c sk ∧ FullExtScratchPres s3 sk ∧
              st.2.work_stk1 = ws3 ∧ st.2.work_stk2 = s3.scratch.work_stk2 ∧
              (FullMem c sk ⋆ R_hdr) mk)
            (fun Jk hJk => by
              c0_hsteps; exact hJk (0, s3.scratch) m3 ⟨Nat.zero_le _, hlen3, hcov3,
                ⟨rfl, rfl⟩, rfl, rfl, hm3⟩)
            (fun Jk (k, sck) mk ⟨hk_le, hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
          dsimp only at hk_le hlenk hcovk hprek hws1k hws2k hmk ihk
          rw [Blocks.get_here]; dsimp only
          let sk : FullState := { s3 with scratch := sck }
          c0_hsteps_nogrp
          · have hk_lt : k < mcl2 := by
              have hk_lt_bd : mcl2 < 2 ^ 64 := by omega
              have hlt : k % 2 ^ 64 < mcl2 % 2 ^ 64 := by
                simpa [BitVec.toNat_ofNat] using (by assumption : _)
              rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk_lt_bd] at hlt
            have hk_ws1 : k < sck.work_stk1.length := by
              rw [hlenk.scratch_ok.work_stk1_len]; omega
            let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
              (by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)
            have hbv_eq : bv = ws3[k]'(by rw [hws3]; omega) := by
              dsimp only [bv]
              exact s7b_getElem_congr_list hws1k (bv64_ofNat_toNat (by omega))
            have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
              have hcov_k := hcovk.2.2.1 k hk_lt
              dsimp only [sk, s3, mkBumpState] at hcov_k
              rw [hws1k, List.getElem?_eq_getElem (by rw [hws3]; omega),
                Option.getD_some] at hcov_k
              simpa [hbv_eq] using hcov_k.1
            have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
              BitVec.eq_of_toNat_eq (by
                rw [show (1 : BitVec 64) = 1#64 from rfl,
                  fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                  bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
            have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
              rw [s7b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullScratch)
              (Inv := fun sc' m' =>
                let sk' : FullState := { s3 with scratch := sc' }
                sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s3 sk' ∧
                sc'.work_stk1 = ws3 ∧ sc'.work_stk2 = s3.scratch.work_stk2 ∧
                (FullMem c sk' ⋆ R_hdr) m')
              (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
                rw [Blocks.get_here]
                c0_hsteps; rw [hk1_bv]
                exact ihk (k + 1, sc') m' (by dsimp only; omega)
                  ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
              (fun Jstep hJstep => ?_)
            c0_hsteps_nogrp
            · c0_hcall hQueueMtf
              refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
              dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
                Full.fullSafetySlice_safe] at hc1 hs1 hm1
              have hcs1 : sk1.core = sk.core :=
                @Full.fullCoreState_agrees_with_scratch c sk sk1 hc1
              have hsk1_eq : sk1 = { s3 with scratch := sk1.scratch } := by
                cases sk1; simp only [sk] at hcs1; congr 1
              rw [hsk1_eq] at hs1 hm1
              c0_hsteps
              exact hJstep sk1.scratch mk1 ⟨hs1, s7b_cov_of_core_eq hcovk rfl hp1.2.1,
                ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
                hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1⟩
            · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
            · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
          · c0_hsteps
            exact hJfin () mk (hQ mrk2 mcl2 sck ext1 mk hlenk hcovk
              ⟨hprek.1.trans hpre2.1, hprek.2.trans hpre2.2⟩ (hws2k.trans hws22) hext1
              hinit1 ((fullM6HdrMem_iff ..).mpr hmk))
        · -- `if (cnt <= cv)` sort producer (`Jsrt`)
          c0_hsteps_nogrp
          · c0_hcall hSortAna
            refine m6SortAnaQsSpec_of hlen2
              (by simpa [bumpSt2, bv64_ofNat_toNat (by omega : mcl2 < 2 ^ 64)] using hmcl2_cv)
              (fun k hk => by
                simp only [Arg.val_var,
                  bv64_ofNat_toNat (show mcl2 < 2 ^ 64 by omega)] at hk
                exact (hcov2.2.2.1 k hk).1)
              hm2 fun ws3 m3 hws3 hperm _ _ hm3 => ?_
            simp only [Arg.val_var,
              bv64_ofNat_toNat (show mcl2 < 2 ^ 64 by omega)] at hperm
            c0_hsteps
            exact hJsrt () m3 ⟨ws3, hws3,
              bump_perm_marksCov (sc0 := sc2) (tk := sc2.search_ticks) hcv_le hws2 hws3 hcov2
                hperm, hm3⟩
      · -- `stable != 0`: `full_bump_var` loop, then `full_bump_decay`
        let s3 := bumpSt2 s sc2 mrk2 mcl2
        let ws3 := sc2.work_stk1
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
          (proj := fun st => BitVec.ofNat 64 st.1)
          (μ := fun st => mcl2 - st.1)
          (Inv := fun st mk => st.1 ≤ mcl2 ∧
            let sk : FullState := { s3 with scratch := st.2 }
            sk.LengthsOk c ∧ FullAnaMarksCov c sk ∧ FullExtScratchPres s3 sk ∧
            st.2.work_stk1 = ws3 ∧ st.2.work_stk2 = s3.scratch.work_stk2 ∧
            (FullMem c sk ⋆ R_hdr) mk)
          (fun Jk hJk => by
            c0_hsteps; exact hJk (0, s3.scratch) m2 ⟨Nat.zero_le _, hlen2, hcov2,
              ⟨rfl, rfl⟩, rfl, rfl, hm2⟩)
          (fun Jk (k, sck) mk ⟨hk_le, hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
        dsimp only at hk_le hlenk hcovk hprek hws1k hws2k hmk ihk
        rw [Blocks.get_here]; dsimp only
        let sk : FullState := { s3 with scratch := sck }
        c0_hsteps_nogrp
        · have hk_lt : k < mcl2 := by
            have hk_lt_bd : mcl2 < 2 ^ 64 := by omega
            have hlt : k % 2 ^ 64 < mcl2 % 2 ^ 64 := by
              simpa [BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk_lt_bd] at hlt
          have hk_ws1 : k < sck.work_stk1.length := by
            rw [hlenk.scratch_ok.work_stk1_len]; omega
          let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
            (by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)
          have hbv_eq : bv = ws3[k]'(by rw [hws2]; omega) := by
            dsimp only [bv]
            exact s7b_getElem_congr_list hws1k (bv64_ofNat_toNat (by omega))
          have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
            have hcov_k := hcovk.2.2.1 k hk_lt
            dsimp only [sk, s3, bumpSt2] at hcov_k
            rw [hws1k, List.getElem?_eq_getElem (by rw [hws2]; omega),
              Option.getD_some] at hcov_k
            simpa [hbv_eq] using hcov_k.1
          have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
            BitVec.eq_of_toNat_eq (by
              rw [show (1 : BitVec 64) = 1#64 from rfl,
                fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
          have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
            rw [s7b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullScratch)
            (Inv := fun sc' m' =>
              let sk' : FullState := { s3 with scratch := sc' }
              sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s3 sk' ∧
              sc'.work_stk1 = ws3 ∧ sc'.work_stk2 = s3.scratch.work_stk2 ∧
              (FullMem c sk' ⋆ R_hdr) m')
            (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
              rw [Blocks.get_here]
              c0_hsteps; rw [hk1_bv]
              exact ihk (k + 1, sc') m' (by dsimp only; omega)
                ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
            (fun Jstep hJstep => ?_)
          c0_hsteps_nogrp
          · c0_hcall hBumpVar
            refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
            dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
              Full.fullSafetySlice_safe] at hc1 hs1 hm1
            have hcs1 : sk1.core = sk.core :=
              @Full.fullCoreState_agrees_with_scratch c sk sk1 hc1
            have hsk1_eq : sk1 = { s3 with scratch := sk1.scratch } := by
              cases sk1; simp only [sk] at hcs1; congr 1
            rw [hsk1_eq] at hs1 hm1
            c0_hsteps
            exact hJstep sk1.scratch mk1 ⟨hs1, s7b_cov_of_core_eq hcovk rfl hp1.2.1,
              ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
              hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1⟩
          · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
          · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
        · c0_hsteps_nogrp
          c0_hcall hBumpDecay
          refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk' m' hcore' hsafe' hpres' hm' => ?_⟩
          dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
            Full.fullSafetySlice_safe] at hcore' hsafe' hm'
          have hcs' : sk'.core = sk.core :=
            @Full.fullCoreState_agrees_with_scratch c sk sk' hcore'
          have hsf_eq : sk' = { s3 with scratch := sk'.scratch } := by
            cases sk'; simp only [sk] at hcs'; congr 1
          rw [hsf_eq] at hsafe' hm'
          c0_hsteps
          exact hJfin () m' (hQ mrk2 mcl2 sk'.scratch ext1 m' hsafe'
            (s7b_cov_of_core_eq hcovk rfl hpres'.2.1)
            ⟨hpres'.1.1.trans (hprek.1.trans hpre2.1), hpres'.1.2.trans (hprek.2.trans hpre2.2)⟩
            (hpres'.2.2.1.trans (hws2k.trans hws22)) hext1 hinit1
            ((fullM6HdrMem_iff ..).mpr hm'))
    · -- gated block producer (`Jallow`): `!m6_hdr_delaying(h, 0) && m6_hdr_dr_allow(h)`
      m6h_call hDelaying
      refine m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
        fun ⟨dl, ⟨⟩⟩ ext0 s0 m0 hcore0 hlen0 hsc0 hext0 hw0 hm0 => ?_
      obtain ⟨sc0, rfl⟩ : ∃ sc0 : FullScratch, s0 = { s with scratch := sc0 } := by
        obtain ⟨core0, sc0⟩ := s0
        dsimp only at hcore0
        subst hcore0
        exact ⟨sc0, rfl⟩
      have hcov0 : FullAnaMarksCov c { s with scratch := sc0 } :=
        s7b_cov_of_core_eq hcov rfl hsc0.ws1
      have hpre0 : FullExtScratchPres s { s with scratch := sc0 } := hsc0.extPres
      have hws20 : sc0.work_stk2 = s.scratch.work_stk2 := hsc0.ws2
      have hws10_len : sc0.work_stk1.length = 2 * c.max_vars := hlen0.scratch_ok.work_stk1_len
      rw [fullM6HdrMem_iff] at hm0
      c0_hsteps_nogrp
      · exact hJallow () m0 ⟨ext0, sc0, s.core.mrk, s.core.min_clr_len, hext0, hw0, hlen0,
          hcov0, hpre0, hws20, hm0⟩
      m6h_call hDrAllow
      refine m6HdrDrAllowSpec_of hcfg hext0 hlen0 ((fullM6HdrMem_iff ..).mpr hm0)
        fun allow ext1 m1 hinit1 hext_eq hm1 => ?_
      have hext1 : M6HdrExtOk ext1 := hinit1.toOk
      have hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1 :=
        fun hi => ⟨hinit1, by rw [hext_eq (hw0 hi).1]; exact (hw0 hi).2⟩
      rw [fullM6HdrMem_iff] at hm1
      let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
      c0_hsteps_nogrp
      · -- `allow = true`: clamp `tlen`, scan `tmp[0..tlen)`, rollback/bump or reduce delay
        refine wp_join_state1 (t := i64) (α := Nat)
          (proj := BitVec.ofNat 64)
          (Inv := fun tlen mt => tlen ≤ s.core.cur_vars ∧ mt = m1)
          (fun Jt tlen mt ⟨htlen_le, hmt⟩ => ?_) (fun Jt hJt => ?_)
        · rcases hmt with rfl; rw [Blocks.get_here]; dsimp only
          have htlen_bv : (BitVec.ofNat 64 tlen).toNat = tlen := bv64_ofNat_toNat (by omega)
          c0_hsteps_nogrp
          refine wp_while_state1 (t := i64) (α := Nat × BumpSt)
            (proj := fun st => BitVec.ofNat 64 st.1)
            (μ := fun st => tlen - st.1)
            (Inv := fun st mi => st.1 ≤ tlen ∧ bumpAllowInv c s sc0 R_hdr st.2 mi)
            (fun Ji hJi => by
              c0_hsteps
              exact hJi (0, s.core.mrk, saved, sc0.work_stk1, sc0.search_ticks) mt
                ⟨Nat.zero_le _, hmrk0_len, hws10_len, hcov0, hm1⟩)
            (fun Ji (i, mrk_i, mcl_i, ws_i, tk_i) mi ⟨hi_le, hmrk_i, hws_i, hcov_i, hmi⟩ ihi =>
              ?_)
          dsimp only at hi_le hmrk_i hws_i hcov_i hmi ihi
          rw [Blocks.get_here]; dsimp only
          let si := mkBumpState s sc0 mrk_i mcl_i ws_i tk_i
          refine wp_join_group (ts := [])
            (fun () mr => ∃ st_a : BumpSt, bumpAllowInv c s sc0 R_hdr st_a mr)
            (fun _ () mr ⟨⟨mrk_a, mcl_a, ws_a, tk_a⟩, hmrk_a, hws_a, hcov_a, hmr⟩ => by
              rw [Blocks.get_here]
              refine wp_join_group (ts := [])
                (fun () m_out => bumpPostInv c s ext R m_out)
                (fun _ () m_out hpost => by
                  rw [Blocks.get_here]; c0_hsteps
                  exact hJallow () m_out hpost)
                (fun Jrb hJrb => ?_)
              c0_hsteps_nogrp
              · refine wp_while_state0 (α := BumpSt)
                  (μ := fun st => st.2.1)
                  (Inv := fun st mr' => bumpAllowInv c s sc0 R_hdr st mr')
                  (fun Jr hJr => ?_)
                  (fun Jr (mrk_r, mcl_r, ws_r, tk_r) mr' ⟨hmrk_r, hws_r, hcov_r, hmr'⟩ ihr => ?_)
                · c0_hsteps
                  exact hJr (mrk_a, mcl_a, ws_a, tk_a) mr ⟨hmrk_a, hws_a, hcov_a, hmr⟩
                · dsimp only at hmrk_r hws_r hcov_r hmr' ihr
                  rw [Blocks.get_here]; dsimp only
                  let sr := mkBumpState s sc0 mrk_r mcl_r ws_r tk_r
                  have hmcl_r_cv : mcl_r ≤ s.core.cur_vars := hcov_r.1
                  c0_hsteps_nogrp
                  · have hmcl_r_pos : 0 < mcl_r := by
                      have hgt : saved % 2 ^ 64 < mcl_r % 2 ^ 64 := by assumption
                      rw [Nat.mod_eq_of_lt (by omega : saved < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : mcl_r < 2 ^ 64)] at hgt
                      omega
                    have hmcl_m1_bv : (BitVec.ofNat 64 mcl_r - 1#64).toNat = mcl_r - 1 := by
                      rw [fl_bv64_sub1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                        bv64_ofNat_toNat (by omega)]
                    have hmcl_ws :
                        (BitVec.ofNat 64 mcl_r - 1#64).toNat < sr.scratch.work_stk1.length := by
                      rw [hmcl_m1_bv, hws_r]; omega
                    let rv := sr.scratch.work_stk1[(BitVec.ofNat 64 mcl_r - 1#64).toNat]'hmcl_ws
                    have hmcl_ws' : mcl_r - 1 < ws_r.length := by rw [hws_r]; omega
                    have hrv_eq : rv = ws_r[mcl_r - 1]'hmcl_ws' :=
                      s7b_getElem_congr_list rfl hmcl_m1_bv
                    have hrv_lt : rv.toNat < s.core.cur_vars := by
                      have hcov_prev :=
                        (hcov_r.2.2.1 (mcl_r - 1) (by dsimp only [mkBumpState]; omega)).1
                      dsimp only [sr, mkBumpState] at hcov_prev
                      rw [List.getElem?_eq_getElem hmcl_ws', Option.getD_some] at hcov_prev
                      simpa [hrv_eq] using hcov_prev
                    have hrv_mrk : (rv.setWidth 64).toNat < mrk_r.length := by
                      rw [s7b_bv32_setWidth64, hmrk_r]; omega
                    refine wp_join_state0 (α := BumpSt)
                      (Inv := fun st mr'' => st.2.1 < mcl_r ∧ bumpAllowInv c s sc0 R_hdr st mr'')
                      (fun _ st mr'' ⟨hm_lt, hinv⟩ => by
                        rw [Blocks.get_here]; c0_hsteps; exact ihr st mr'' hm_lt hinv)
                      (fun Js2 hJs2 => ?_)
                    c0_hsteps_nogrp
                    · have hcov_pop := bump_pop_marksCov hmrk_r hws_r hcv_le hcov_r hmcl_r_pos
                      c0_hsteps
                      have hmod32 :
                          ∀ (b : BitVec 32), b.toNat % 18446744073709551616 = b.toNat :=
                        fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                      exact hJs2 (mrk_r.set rv.toNat 0#8, mcl_r - 1, ws_r, tk_r) _
                        ⟨by dsimp only; omega, by simp [hmrk_r], hws_r,
                          by simpa [hrv_eq] using hcov_pop, by
                          simpa [sr, mkBumpState, rv, hmcl_m1_bv, s7b_bv32_setWidth64, hmod32,
                            show BitVec.ofNat 8 0 = 0#8 from rfl,
                            Nat.mod_eq_of_lt (by omega : mcl_r - 1 < 2 ^ 64)] using hm⟩
                    · exfalso
                      have hge_idx :
                          (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 % 2 ^ 64 =
                            mcl_r - 1 := by
                        simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
                      have hrv_hc :
                          ws_r[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 %
                            2 ^ 64]'(by rw [hge_idx]; exact hmcl_ws') = rv :=
                        (s7b_getElem_congr_list rfl hge_idx).trans hrv_eq.symm
                      have hge := hc
                      rw [hrv_hc, Nat.mod_eq_of_lt hcv_lt64] at hge
                      omega
                  · -- rollback done: `m6_hdr_bump_delay(h, 0)`
                    have hlen_r : (mkBumpState s sc0 mrk_r mcl_r ws_r tk_r).LengthsOk c :=
                      mkBumpState_lengths hlen0 hmrk_r hws_r (by omega)
                    m6h_call hBumpDelay
                    refine m6HdrW2aSpec_of rfl hcfg hext1 hlen_r ((fullM6HdrMem_iff ..).mpr hmr')
                      fun () ext2 s' m' hcore' hlen' hsc' hext2 hw2 hm' => ?_
                    rw [fullM6HdrMem_iff] at hm'
                    c0_hsteps
                    exact hJrb () m' (bumpPostInv_of_w2a hpre0 hws20 hinit_pres hcov_r hcore'
                      hlen' hsc' hext2 hw2 hm')
              · -- `m6_hdr_reduce_delay(h, 0)`
                have hlen_a : (mkBumpState s sc0 mrk_a mcl_a ws_a tk_a).LengthsOk c :=
                  mkBumpState_lengths hlen0 hmrk_a hws_a
                    (by have := hcov_a.1; dsimp only [mkBumpState] at this; omega)
                m6h_call hReduceDelay
                refine m6HdrW2aSpec_of rfl hcfg hext1 hlen_a ((fullM6HdrMem_iff ..).mpr hmr)
                  fun () ext2 s' m' hcore' hlen' hsc' hext2 hw2 hm' => ?_
                rw [fullM6HdrMem_iff] at hm'
                c0_hsteps
                exact hJrb () m' (bumpPostInv_of_w2a hpre0 hws20 hinit_pres hcov_a hcore'
                  hlen' hsc' hext2 hw2 hm'))
            (fun Jafter hJafter => ?_)
          c0_hsteps_nogrp
          · have hi_lt : i < tlen := by
              have hlt : i % 2 ^ 64 < tlen % 2 ^ 64 := by
                simpa [BitVec.toNat_ofNat] using (by assumption : _)
              rwa [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : tlen < 2 ^ 64)] at hlt
            have hi_tmp : i < si.core.tmp.length := by
              rw [show si.core.tmp = s.core.tmp from rfl, hco.tmp_len_arr]; omega
            have hi_tmp_bv : (BitVec.ofNat 64 i).toNat <
                (mkBumpState s sc0 mrk_i mcl_i ws_i tk_i).core.tmp.length := by
              rw [bv64_ofNat_toNat (by omega)]; exact hi_tmp
            have hi1_bv : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) :=
              BitVec.eq_of_toNat_eq (by
                rw [show (1 : BitVec 64) = 1#64 from rfl,
                  fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                  bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
            let uv32 := (si.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp_bv) >>> 1#32
            c0_hsteps_nogrp
            refine wp_join_state1 (t := i32) (α := BitVec 32)
              (proj := fun x => x) (Inv := fun _ mr => mr = mi)
              (fun Jr rsn mr hmr => ?_) (fun Jr hJr => ?_)
            · rw [hmr] at *; clear mr hmr; rw [Blocks.get_here]; dsimp only
              c0_hsteps_nogrp
              refine wp_join_state0 (α := BumpSt)
                (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                (fun _ st' mi' hst' => by
                  rw [Blocks.get_here]; try dsimp only
                  c0_hsteps; rw [hi1_bv]
                  exact ihi (i + 1, st') mi' (by dsimp only; omega) ⟨by omega, hst'⟩)
                (fun Jstep hJstep => ?_)
              refine wp_join_group (ts := []) (fun () m' => m' = mi)
                (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
              · rw [hm'] at *; clear m' hm'; rw [Blocks.get_here]; dsimp only
                refine wp_join_state0 (α := BumpSt)
                  (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                  (fun _ st' mi' hst' => by
                    rw [Blocks.get_here]; c0_hsteps; exact hJstep st' mi' hst')
                  (fun Js hJs => ?_)
                have hal_le := hco.arena_len_le
                have har_len := hco.arena_len_arr
                have har_cap := c.harena; unfold LratBytes.dimacsBound at har_cap
                c0_hsteps_nogrp
                · have hrsn_3 : rsn.toNat + 3 ≤ s.core.arena_len := by
                    have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                    have hrsn64 : rsn.toNat + 3 < 2 ^ 64 := by have := rsn.isLt; omega
                    have hge :
                        (rsn.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
                      simpa [show BitVec.toNat (3 : BitVec 64) = 3 from rfl] using hc
                    rw [Nat.mod_eq_of_lt hal64, Nat.mod_eq_of_lt hrsn64] at hge; omega
                  have hrsn2 : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                    bv_omega
                  have hrsn2_eq : (rsn.setWidth 64 + 2#64).toNat = (rsn.toNat + 2) % 2 ^ 64 := by
                    bv_omega
                  let sz := s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn2
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := BumpSt)
                    (Inv := fun st' mj' => bumpAllowInv c s sc0 R_hdr st' mj')
                    (fun _ st' mj' hst' => by
                      rw [Blocks.get_here]; c0_hsteps; exact hJs st' mj' hst')
                    (fun Jsz hJsz => ?_)
                  c0_hsteps_nogrp
                  · have hsz_lt64 : rsn.toNat + 3 + sz.toNat < 2 ^ 64 := by
                      have := rsn.isLt; have := sz.isLt; omega
                    have hsz_ar : rsn.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
                      have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                      have hge :
                          (rsn.toNat + 3 + sz.toNat) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
                        dsimp only [sz]
                        simpa [hrsn2_eq, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                          show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc
                      rw [Nat.mod_eq_of_lt hal64, Nat.mod_eq_of_lt hsz_lt64] at hge; omega
                    refine wp_while_state1 (t := i32) (α := BitVec 32 × BumpSt)
                      (proj := fun st => st.1) (μ := fun st => sz.toNat - st.1.toNat)
                      (Inv := fun st mj =>
                        st.1.toNat ≤ sz.toNat ∧ bumpAllowInv c s sc0 R_hdr st.2 mj)
                      (fun Jj hJj => by
                        c0_hsteps
                        exact hJj (0#32, mrk_i, mcl_i, ws_i, tk_i + 1) _
                          ⟨Nat.zero_le _, hmrk_i, hws_i, hcov_i, hm⟩)
                      (fun Jj (j, mrk_j, mcl_j, ws_j, tk_j) mj
                        ⟨hj_le, hmrk_j, hws_j, hcov_j, hmj⟩ ihj => ?_)
                    dsimp only at hj_le hmrk_j hws_j hcov_j hmj ihj
                    rw [Blocks.get_here]; dsimp only
                    let sj := mkBumpState s sc0 mrk_j mcl_j ws_j tk_j
                    c0_hsteps_nogrp
                    · have hj_lt : j.toNat < sz.toNat := by
                        have hj_hc :
                            j.toNat <
                              (s.core.arena[(rsn.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(
                                by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hrsn2_eq]
                                   exact hrsn2)).toNat := by assumption
                        simpa [sz, hrsn2_eq, show BitVec.toNat (2 : BitVec 64) = 2 from rfl]
                          using hj_hc
                      have har_j : (rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                          sj.core.arena.length := by
                        dsimp only [sj, mkBumpState]; bv_omega
                      let ov : BitVec 32 :=
                        (sj.core.arena[(rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat]'har_j) >>>
                          (1 : Nat)
                      have hj1_bv : (j + 1#32).toNat = j.toNat + 1 :=
                        fl_bv32_add1_toNat (by have := sz.isLt; omega)
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := BumpSt)
                        (Inv := fun st' mj' => bumpAllowInv c s sc0 R_hdr st' mj')
                        (fun _ st' mj' hst' => by
                          rw [Blocks.get_here]; try dsimp only
                          c0_hsteps
                          exact ihj (j + 1#32, st') mj' (by dsimp only; rw [hj1_bv]; omega)
                            ⟨by rw [hj1_bv]; omega, hst'⟩)
                        (fun Jjs hJjs => ?_)
                      c0_hsplit
                      · have hov_cv : ov.toNat < s.core.cur_vars := by
                          have h1 : ov.toNat < s.core.cur_vars % 2 ^ 64 := by
                            simpa [ov] using (by assumption : _)
                          rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                        have hov_lvl : (ov.setWidth 64).toNat < s.core.lvl.length := by
                          rw [s7b_bv32_setWidth64, hco.lvl_len]; omega
                        have hov_mrk : (ov.setWidth 64).toNat < mrk_j.length := by
                          rw [s7b_bv32_setWidth64, hmrk_j]; omega
                        c0_hsplit
                        · c0_hsplit
                          · have hmrk_hc := hc
                            c0_hsplit
                            · have hmcl_cv : mcl_j < s.core.cur_vars := by
                                have hmcl64 : mcl_j < 2 ^ 64 := by
                                  have := hcov_j.1; dsimp [mkBumpState] at this; omega
                                have h1 : mcl_j % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by
                                  assumption
                                rwa [Nat.mod_eq_of_lt hmcl64, Nat.mod_eq_of_lt hcv_lt64] at h1
                              have hmrk_z : mrk_j[ov.toNat]?.getD 0#8 = 0#8 := by
                                rw [List.getElem?_eq_getElem (by rw [hmrk_j]; omega),
                                  Option.getD_some]
                                exact s7b_bv8_zext32_eq0_iff.mp (by
                                  have hmod32 :
                                      ∀ (b : BitVec 32), b.toNat % 18446744073709551616 =
                                        b.toNat :=
                                    fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                                  simpa [ov, sj, mkBumpState, BitVec.toNat_ushiftRight, hmod32,
                                    Nat.shiftRight_eq_div_pow,
                                    show BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32
                                      from rfl] using hmrk_hc)
                              have hcov' :=
                                bump_push_marksCov hmrk_j hws_j hcv_le hcov_j hov_cv hmcl_cv
                                  hmrk_z
                              have hmcl1_bv :
                                  (BitVec.ofNat 64 mcl_j + 1).toNat = mcl_j + 1 := by
                                rw [show (1 : BitVec 64) = 1#64 from rfl,
                                  fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                  bv64_ofNat_toNat (by omega)]
                              c0_hsteps
                              have hmod32 :
                                  ∀ (b : BitVec 32), b.toNat % 18446744073709551616 = b.toNat :=
                                fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                              exact hJjs
                                (mrk_j.set ov.toNat 1#8, mcl_j + 1, ws_j.set mcl_j ov, tk_j) _
                                ⟨by simp [hmrk_j], by simp [hws_j], hcov', by
                                  simpa [sj, mkBumpState, ov, hmcl1_bv, hmod32,
                                    BitVec.toNat_ushiftRight,
                                    bv64_ofNat_toNat (by omega : mcl_j < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by omega : mcl_j + 1 < 2 ^ 64),
                                    show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                            · exact hJjs (mrk_j, mcl_j, ws_j, tk_j) mj
                                ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                          · exact hJjs (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                        · exact hJjs (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                      · exact hJjs (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                    · exact hJsz (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                    · exact hJsz (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                  · exact hJsz (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                  · exact hJsz (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJs (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJs (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
              · -- binary reason branch (`Jelse` producer)
                c0_hsteps_nogrp
                · refine wp_join_state0 (α := BumpSt)
                    (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                    (fun _ st' mi' hst' => by
                      rw [Blocks.get_here]; c0_hsteps; exact hJstep st' mi' hst')
                    (fun Jbin hJbin => ?_)
                  let ov : BitVec 32 := (rsn &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                  c0_hsplit
                  · have hov_cv : ov.toNat < s.core.cur_vars := by
                      have h1 : ov.toNat < s.core.cur_vars % 2 ^ 64 := by
                        simpa [ov, BitVec.toNat_ushiftRight, BitVec.toNat_and] using
                          (by assumption : _)
                      rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                    have hov_lvl : (ov.setWidth 64).toNat < s.core.lvl.length := by
                      rw [s7b_bv32_setWidth64, hco.lvl_len]; omega
                    have hov_mrk : (ov.setWidth 64).toNat < mrk_i.length := by
                      rw [s7b_bv32_setWidth64, hmrk_i]; omega
                    c0_hsplit
                    · c0_hsplit
                      · have hmrk_hc := hc
                        c0_hsplit
                        · have hmcl_cv : mcl_i < s.core.cur_vars := by
                            have hmcl64 : mcl_i < 2 ^ 64 := by
                              have := hcov_i.1; dsimp [mkBumpState] at this; omega
                            have h1 : mcl_i % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by assumption
                            rwa [Nat.mod_eq_of_lt hmcl64, Nat.mod_eq_of_lt hcv_lt64] at h1
                          have hmod_rsn : rsn.toNat % 18446744073709551616 = rsn.toNat :=
                            Nat.mod_eq_of_lt (Nat.lt_trans rsn.isLt (by decide))
                          have hmrk_z : mrk_i[ov.toNat]?.getD 0#8 = 0#8 := by
                            rw [List.getElem?_eq_getElem (by rw [hmrk_i]; omega), Option.getD_some]
                            exact s7b_bv8_zext32_eq0_iff.mp (by
                              simpa [ov, BitVec.toNat_ushiftRight, BitVec.toNat_and, hmod_rsn,
                                Nat.shiftRight_eq_div_pow,
                                show BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32
                                  from rfl] using hmrk_hc)
                          have hcov' :=
                            bump_push_marksCov hmrk_i hws_i hcv_le hcov_i hov_cv hmcl_cv hmrk_z
                          have hmcl1_bv : (BitVec.ofNat 64 mcl_i + 1).toNat = mcl_i + 1 := by
                            rw [show (1 : BitVec 64) = 1#64 from rfl,
                              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                              bv64_ofNat_toNat (by omega)]
                          c0_hsteps
                          exact hJbin (mrk_i.set ov.toNat 1#8, mcl_i + 1, ws_i.set mcl_i ov, tk_i) _
                            ⟨by simp [hmrk_i], by simp [hws_i], hcov', by
                              simpa [mkBumpState, ov, hmcl1_bv, hmod_rsn,
                                BitVec.toNat_ushiftRight, BitVec.toNat_and,
                                bv64_ofNat_toNat (by omega : mcl_i < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : mcl_i + 1 < 2 ^ 64),
                                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                        · exact hJbin (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                      · exact hJbin (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                    · exact hJbin (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                  · exact hJbin (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJelse () mi rfl
                · exact hJelse () mi rfl
            · c0_hsteps_nogrp
              · have huv_lt : uv32.toNat < s.core.cur_vars := by
                  have h1 : uv32.toNat < s.core.cur_vars % 2 ^ 64 := by
                    simpa [uv32, si, mkBumpState, s7b_bv32_setWidth64] using (by assumption : _)
                  rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                have huv_cv : (uv32.setWidth 64).toNat < si.core.rsns.length := by
                  rw [s7b_bv32_setWidth64, hco.rsns_len]; omega
                c0_hsteps; exact hJr _ mi rfl
              · c0_hsteps; exact hJr _ mi rfl
          · exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩
          · exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩
        · c0_hsteps
          · exact hJt s.core.cur_vars m1 ⟨Nat.le_refl _, rfl⟩
          · have htlen_le : s.core.tmp_len ≤ s.core.cur_vars := by
              have hcv64 : s.core.cur_vars < 2 ^ 64 := hcv_lt64
              have htl_le := hco.tmp_len_le
              have htl64 : s.core.tmp_len < 2 ^ 64 := by omega
              have hle : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by assumption
              rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt htl64] at hle; omega
            exact hJt s.core.tmp_len m1 ⟨htlen_le, rfl⟩
      · exact hJallow () m1 ⟨ext1, sc0, s.core.mrk, saved, hext1, hinit_pres, hlen0, hcov0,
          hpre0, hws20, hm1⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0c
