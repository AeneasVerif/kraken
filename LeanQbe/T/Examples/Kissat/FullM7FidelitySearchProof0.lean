/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
public import LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 High-Fidelity Search, Randec & Bumping Proofs (`FullM7FidelitySearchProof`)

M1-clean, UNSAT-only proof module (`public section`, `0` `@[expose]`, `0` `@[local]`,
`0` `import all`, `XPost := False`, `0` SAT model-finding proofs, `std3` axioms):
1. `full_bump_analyzed_fid_wp` (`FullM6OrchAdapters.m6aBumpAnalyzedSpec`, focused vs stable split).
2. `full_switch_mode_fid_wp` (`FullM7Search.m7SwitchModeSpec`, `randec` reset `[56..63]`).
3. `m6_hdr_decide_fid_wp` (`FullM6Hdr.m6HdrDecideSpec`, calling `full_decide_m7`).
4. `full_search_fid_wp` (`FullM6Orch.fullM6SearchSpec`, `search.c:195-223` loop).
5. Closed `26`-row `fidSearchSpecTable`, `fidSearchEnv`, `fidSearch_tableImpl`,
   `fidSearch_moduleOk`, plus `fidSearchPatchRows` / `fidSearchPatch_tableImpl_of`.
6. Spliced `411`-fn `FullM7 + FullM7FidelitySearch` integration over `FullM7.m7Module`:
   `fidSearchSpliced_acyclic`, `fidSearchSpliced_moduleOk`, `fidSearchSpliced_solve_bytes_sound`,
   and `fidSearchSpliced_unsat_nv` (`XPost := False`).
7. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for all `4` functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySearch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

local macro "fs_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "fs_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

local elab "fs_nojnz" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local elab "fs_nojnz_grp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

/-! ## 1. Shared BV & State-Preservation Helpers -/

private theorem fs_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem fs_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fs_bv64_sub1 {x : BitVec 64} (hx : x ≠ 0#64) : (x - 1#64).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 =>
    hx (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

private theorem fs_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fs_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem fs_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

private theorem fs_bv64_lshr1_le (x : BitVec 64) : (x >>> 1#64).toNat ≤ x.toNat := by
  change (x >>> (1 : Nat)).toNat ≤ _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega

private theorem fs_getElem_congr {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem fs_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem fid_len_scalars {c : FullCfg} {s s' : FullState} (h : s.LengthsOk c)
    (hc : s'.core = s.core := by rfl)
    (h1 : s'.scratch.walk_vals = s.scratch.walk_vals := by rfl)
    (h2 : s'.scratch.phases = s.scratch.phases := by rfl)
    (h3 : s'.scratch.phases_target = s.scratch.phases_target := by rfl)
    (h4 : s'.scratch.phases_best = s.scratch.phases_best := by rfl)
    (h5 : s'.scratch.walk_best = s.scratch.walk_best := by rfl)
    (h6 : s'.scratch.heap = s.scratch.heap := by rfl)
    (h7 : s'.scratch.pos = s.scratch.pos := by rfl)
    (h8 : s'.scratch.shrink_stk = s.scratch.shrink_stk := by rfl)
    (h9 : s'.scratch.q_prev = s.scratch.q_prev := by rfl)
    (h10 : s'.scratch.q_next = s.scratch.q_next := by rfl)
    (h11 : s'.scratch.q_stamp = s.scratch.q_stamp := by rfl)
    (h12 : s'.scratch.wsort = s.scratch.wsort := by rfl)
    (h13 : s'.scratch.work_stk1 = s.scratch.work_stk1 := by rfl)
    (h14 : s'.scratch.work_stk2 = s.scratch.work_stk2 := by rfl)
    (h15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark := by rfl)
    (h16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach := by rfl)
    (h17 : s'.scratch.score = s.scratch.score := by rfl)
    (h18 : s'.scratch.sim_sig = s.scratch.sim_sig := by rfl)
    (h19 : s'.scratch.glue_used = s.scratch.glue_used := by rfl)
    (h20 : s'.scratch.last_learned = s.scratch.last_learned := by rfl)
    (h21 : s'.scratch.delayed = s.scratch.delayed := by rfl)
    (h22 : s'.scratch.red_refs = s.scratch.red_refs := by rfl)
    (h23 : s'.scratch.extend_stk = s.scratch.extend_stk := by rfl)
    (h24 : s'.scratch.scratch_buf = s.scratch.scratch_buf := by rfl) : s'.LengthsOk c :=
  ⟨hc ▸ h.core_ok, ⟨h1 ▸ h.scratch_ok.walk_vals_len, h2 ▸ h.scratch_ok.phases_len,
    h3 ▸ h.scratch_ok.phases_target_len, h4 ▸ h.scratch_ok.phases_best_len,
    h5 ▸ h.scratch_ok.walk_best_len, h6 ▸ h.scratch_ok.heap_len_arr, h7 ▸ h.scratch_ok.pos_len,
    h8 ▸ h.scratch_ok.shrink_stk_len, h9 ▸ h.scratch_ok.q_prev_len, h10 ▸ h.scratch_ok.q_next_len,
    h11 ▸ h.scratch_ok.q_stamp_len, h12 ▸ h.scratch_ok.wsort_len, h13 ▸ h.scratch_ok.work_stk1_len,
    h14 ▸ h.scratch_ok.work_stk2_len, h15 ▸ h.scratch_ok.tarjan_mark_len,
    h16 ▸ h.scratch_ok.tarjan_reach_len, h17 ▸ h.scratch_ok.score_len,
    h18 ▸ h.scratch_ok.sim_sig_len, h19 ▸ h.scratch_ok.glue_used_len,
    h20 ▸ h.scratch_ok.last_learned_len, h21 ▸ h.scratch_ok.delayed_len_arr,
    h22 ▸ h.scratch_ok.red_refs_len, h23 ▸ h.scratch_ok.extend_stk_len,
    h24 ▸ h.scratch_ok.scratch_buf_len⟩⟩


/-! ## 2. `full_bump_analyzed_fid_wp` (`m6aBumpAnalyzedSpec`) -/

section BumpAnalyzedProof

private abbrev FidBumpSt := List (BitVec 8) × Nat × List (BitVec 32)

private abbrev fidMkBumpState (s : FullState) (mrk : List (BitVec 8)) (mcl : Nat)
    (ws1 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { s.scratch with work_stk1 := ws1 } }

private abbrev fidBumpAllowInv (c : FullCfg) (s : FullState) (R_hdr : Mem 64 → Prop)
    (st : FidBumpSt) (m : Mem 64) : Prop :=
  st.1.length = c.max_vars ∧ st.2.2.length = 2 * c.max_vars ∧
  FullAnaMarksCov c (fidMkBumpState s st.1 st.2.1 st.2.2) ∧
  (FullMem c (fidMkBumpState s st.1 st.2.1 st.2.2) ⋆ R_hdr) m

private theorem fid_nodup_of_getElem_ne {α : Type} :
    ∀ (xs : List α),
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, fid_nodup_of_getElem_ne _ fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

private theorem fid_nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hmiss : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  refine fid_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
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

private theorem fid_nodup_take_pred {xs : List (BitVec 32)} {n : Nat}
    (hpos : 0 < n) (hnd : ((xs.take n).map BitVec.toNat).Nodup) :
    ((xs.take (n - 1)).map BitVec.toNat).Nodup := by
  refine fid_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take] at hi hj
  have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
  simpa only [List.getElem_map, List.getElem_take] using hne

private theorem fid_mkBumpState_lengths {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (fidMkBumpState s mrk mcl ws1).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem fid_bump_push_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (fidMkBumpState s mrk mcl ws1))
    (hov_cv : ov.toNat < s.core.cur_vars) (hmcl_cv : mcl < s.core.cur_vars)
    (hmrk0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (fidMkBumpState s (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov)) := by
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [fidMkBumpState] at hnd hfwd hbak
  have hmcl_ws : mcl < ws1.length := by rw [hws1]; omega
  refine ⟨hmcl_cv, fid_nodup_map_take_append hmcl_ws hnd (fun k hk heq => ?_),
    fun k hk => ?_, fun v hv hnz => ?_⟩
  · exact (hfwd k hk).2 (by simpa [heq] using hmrk0)
  · dsimp only [fidMkBumpState] at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · have hk_cov := hfwd k hlt
      have hne : (ws1[k]?.getD 0#32).toNat ≠ ov.toNat := fun heq => by
        rw [heq] at hk_cov; exact hk_cov.2 hmrk0
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hne.symm]
      exact hk_cov
    · rw [List.getElem?_set_self hmcl_ws, Option.getD_some,
        List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some]
      exact ⟨hov_cv, by decide⟩
  · dsimp only [fidMkBumpState] at hnz ⊢
    by_cases hveq : v = ov.toNat
    · refine ⟨mcl, Nat.lt_succ_self _, ?_⟩
      subst hveq
      rw [List.getElem?_set_self hmcl_ws, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      rwa [List.getElem?_set_ne (by omega)]

private theorem fid_bump_pop_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (fidMkBumpState s mrk mcl ws1)) (hpos : 0 < mcl) :
    let hmcl_ws : mcl - 1 < ws1.length := by
      have hm1 := hcov.1; dsimp only [fidMkBumpState] at hm1; rw [hws1]; omega
    let rv := ws1[mcl - 1]'hmcl_ws
    FullAnaMarksCov c (fidMkBumpState s (mrk.set rv.toNat 0#8) (mcl - 1) ws1) := by
  intro hmcl_ws rv
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [fidMkBumpState] at hmcl_cv0 hnd hfwd hbak
  have hrv_lt : rv.toNat < s.core.cur_vars := by
    have := (hfwd (mcl - 1) (by omega)).1
    simpa [rv, List.getElem?_eq_getElem hmcl_ws] using this
  dsimp only [FullAnaMarksCov, fidMkBumpState]
  refine ⟨by omega, fid_nodup_take_pred hpos hnd, fun k hk => ?_, fun v hv hnz => ?_⟩
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

private theorem fid_bump_perm_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {cnt : Nat} {ws1 ws' : List (BitVec 32)}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hws1 : ws1.length = 2 * c.max_vars) (hws' : ws'.length = 2 * c.max_vars)
    (hcov : FullAnaMarksCov c (fidMkBumpState s mrk cnt ws1))
    (hperm : (ws'.take cnt).Perm (ws1.take cnt)) :
    FullAnaMarksCov c (fidMkBumpState s mrk cnt ws') := by
  obtain ⟨hcnt_cv, hnd, hfwd, hbak⟩ := hcov
  dsimp only [fidMkBumpState] at hcnt_cv hnd hfwd hbak
  have hcnt_ws1 : cnt ≤ ws1.length := by rw [hws1]; omega
  have hcnt_ws' : cnt ≤ ws'.length := by rw [hws']; omega
  refine ⟨hcnt_cv, (hperm.map BitVec.toNat).nodup_iff.mpr hnd, fun k hk => ?_,
    fun v hv hnz => ?_⟩
  · dsimp only [fidMkBumpState] at hk ⊢
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
  · dsimp only [fidMkBumpState] at hnz ⊢
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

private theorem fid_anaMarksCov_of_core_eq {c : FullCfg} {s s' : FullState}
    (hcov : FullAnaMarksCov c s) (hc : s'.core = s.core)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) : FullAnaMarksCov c s' := by
  unfold FullAnaMarksCov at hcov ⊢; rw [hc, hws1]; exact hcov

private theorem fid_bump_pass_step {Γ : Env} {ret : List Ty} {callee : Sym}
    {args : Tup (Arg Val) [i64, i32]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {s3 sk : FullState} {ws1 ws2 : List (BitVec 32)}
    {R_hdr : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, (vals args).2.1, ()))
    (hCall : ∀ a m Q X,
      SafetySlice.spec fullSafetySlice (fun c (a : Tup Val [i64, i32]) _ => a.1 = c.hdr)
        (fun _ _ _ s s' => FullProbeScratchPres s s') a m Q X →
      Γ callee [i64, i32] [] a m Q X)
    (hlenk : sk.LengthsOk c) (hcovk : FullAnaMarksCov c sk)
    (hprek : FullExtScratchPres s3 sk) (hws1k : sk.scratch.work_stk1 = ws1)
    (hws2k : sk.scratch.work_stk2 = ws2) (hmk : (FullMem c sk ⋆ R_hdr) m) (hskc : sk.core = s3.core)
    (hk : ∀ sc' m',
      let sk' : FullState := { s3 with scratch := sc' }
      sk'.LengthsOk c → FullAnaMarksCov c sk' → FullExtScratchPres s3 sk' →
      sc'.work_stk1 = ws1 → sc'.work_stk2 = ws2 → (FullMem c sk' ⋆ R_hdr) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (.call callee args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hCall _ _ _ _ ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hc1 hs1 hm1
  have hcs1 : sk1.core = s3.core :=
    (@Full.fullCoreState_agrees_with_scratch c sk sk1 hc1).trans hskc
  have hsk1_eq : sk1 = { s3 with scratch := sk1.scratch } := by
    cases sk1; dsimp only at hcs1; congr 1
  rw [hsk1_eq] at hs1 hm1
  exact hk sk1.scratch mk1 hs1 (fid_anaMarksCov_of_core_eq hcovk hskc.symm hp1.2.1)
    ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩ (hp1.2.1.trans hws1k)
    (hp1.2.2.1.trans hws2k) hm1

private theorem fid_bump_push_ok {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_lt64 : s.core.cur_vars < 2 ^ 64)
    (hcov : FullAnaMarksCov c (fidMkBumpState s mrk mcl ws1))
    (hov_cv : ov.toNat < s.core.cur_vars)
    (hmcl_hc : mcl % 2 ^ 64 < s.core.cur_vars % 2 ^ 64)
    (hmrk_z : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (fidMkBumpState s (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov)) ∧
      (BitVec.ofNat 64 mcl + 1).toNat = mcl + 1 := by
  have hmcl_cv : mcl < s.core.cur_vars := by
    have hm64 : mcl < 2 ^ 64 := by
      have := hcov.1; dsimp only [fidMkBumpState] at this; omega
    rwa [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hcv_lt64] at hmcl_hc
  refine ⟨fid_bump_push_marksCov hmrk hws1 hcv_le hcov hov_cv hmcl_cv hmrk_z, ?_⟩
  rw [show (1 : BitVec 64) = 1#64 from rfl,
    fs_bv64_add1 (by rw [fs_bv64_ofNat (by omega)]; omega), fs_bv64_ofNat (by omega)]

/-- WP proof for `full_bump_analyzed_fid` (`m6aBumpAnalyzedSpec`), splitting focused
(`full_queue_mtf` only) vs stable (`full_bump_var` + `full_bump_decay` only). -/
theorem full_bump_analyzed_fid_wp (Γ : Env)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hSortAna : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hcov, hm, hQ⟩ := m6aBumpAnalyzedSpec_elim hs
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hcv_le := hco.cur_vars_le
  have hmrk0_len := hco.mrk_len
  have hws10_len := hso.work_stk1_len
  unfold Func.wp full_bump_analyzed_fid_body
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch ext m hlen hcov ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, rfl⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · let saved : Nat := s.core.min_clr_len
    have hsaved_le : saved ≤ s.core.cur_vars := hcov.1
    have hlim_lt : saved * 10 < 2 ^ 64 := by dsimp only [saved]; omega
    have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
    have hlim_bv : (BitVec.ofNat 64 saved * 10#64).toNat = saved * 10 := by
      rw [BitVec.toNat_mul, fs_bv64_ofNat (by omega),
        show (10#64 : BitVec 64).toNat = 10 from rfl, Nat.mod_eq_of_lt hlim_lt]
    have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
      fs_bv64_ofNat hcv_lt64
    refine wp_join_group (ts := [])
      (fun () m2 => ∃ (ext1 : List (BitVec 64)) (st2 : FidBumpSt), M6HdrExtOk ext1 ∧
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ ext1 = ext) ∧
        fidBumpAllowInv c s (array64 (c.hdr - 2304) ext1 ⋆ R) st2 m2)
      (fun _ () m2 ⟨ext1, ⟨mrk2, mcl2, ws2⟩, hext1, hinit_pres, hmrk2, hws2, hcov2, hm2⟩ => ?_)
      (fun Jallow hJallow => ?_)
    · let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
      let s2 := fidMkBumpState s mrk2 mcl2 ws2
      have hmcl2_cv : mcl2 ≤ s.core.cur_vars := hcov2.1
      have hlen2 : s2.LengthsOk c := fid_mkBumpState_lengths hlen hmrk2 hws2 (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () mf => ∃ scf : FullScratch,
          let sf : FullState :=
            { s with core := { s.core with mrk := mrk2, min_clr_len := mcl2 }, scratch := scf }
          sf.LengthsOk c ∧ FullAnaMarksCov c sf ∧ FullExtScratchPres s sf ∧
          scf.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c sf ⋆ R_hdr) mf)
        (fun _ () mf ⟨scf, hlenf, hcovf, hpref, hws2f, hmf⟩ => by
          rw [Blocks.get_here]; c0_hsteps
          exact hQ mrk2 mcl2 scf ext1 mf hlenf hcovf hpref hws2f hext1
            hinit_pres ((fullM6HdrMem_iff ..).mpr hmf))
        (fun Jmode hJmode => ?_)
      fs_nojnz
      fs_jnz hstab
      · -- Focused branch (`h->stable == 0ULL`): sort + `full_queue_mtf` only
        fs_nojnz
        refine wp_join_group (ts := [])
          (fun () m3 => ∃ ws3, ws3.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (fidMkBumpState s mrk2 mcl2 ws3) ∧
            (FullMem c (fidMkBumpState s mrk2 mcl2 ws3) ⋆ R_hdr) m3)
          (fun _ () m3 ⟨ws3, hws3, hcov3, hm3⟩ => ?_)
          (fun Jsrt hJsrt => ?_)
        · let s3 := fidMkBumpState s mrk2 mcl2 ws3
          have hlen3 : s3.LengthsOk c := fid_mkBumpState_lengths hlen hmrk2 hws3 (by omega)
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
              have hlt : k % 2 ^ 64 < mcl2 % 2 ^ 64 := by
                simpa [BitVec.toNat_ofNat] using (by assumption : _)
              rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : mcl2 < 2 ^ 64)] at hlt
            have hk_ws1 : k < sck.work_stk1.length := by
              rw [hlenk.scratch_ok.work_stk1_len]; omega
            let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
              (by rw [fs_bv64_ofNat (by omega)]; exact hk_ws1)
            have hbv_eq : bv = ws3[k]'(by rw [hws3]; omega) := by
              dsimp only [bv]; exact fs_getElem_congr hws1k (fs_bv64_ofNat (by omega))
            have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
              have hcov_k := hcovk.2.2.1 k hk_lt
              dsimp only [sk, s3, fidMkBumpState] at hcov_k
              rw [hws1k, List.getElem?_eq_getElem (by rw [hws3]; omega),
                Option.getD_some] at hcov_k
              simpa [hbv_eq] using hcov_k.1
            have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
              BitVec.eq_of_toNat_eq (by
                rw [show (1 : BitVec 64) = 1#64 from rfl,
                  fs_bv64_add1 (by rw [fs_bv64_ofNat (by omega)]; omega),
                  fs_bv64_ofNat (by omega), fs_bv64_ofNat (by omega)])
            have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
              rw [fs_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullScratch)
              (Inv := fun sc' m' =>
                let sk' : FullState := { s3 with scratch := sc' }
                sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s3 sk' ∧
                sc'.work_stk1 = ws3 ∧ sc'.work_stk2 = s3.scratch.work_stk2 ∧
                (FullMem c sk' ⋆ R_hdr) m')
              (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
                rw [Blocks.get_here]; c0_hsteps; rw [hk1_bv]
                exact ihk (k + 1, sc') m' (by dsimp only; omega)
                  ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
              (fun Jstep hJstep => ?_)
            c0_hsteps_nogrp
            · exact fid_bump_pass_step rfl (hQueueMtf · · · ·) hlenk hcovk hprek hws1k hws2k
                hmk rfl fun sc' m' h1 h2 h3 h4 h5 h6 => hJstep sc' m' ⟨h1, h2, h3, h4, h5, h6⟩
            · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
            · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
          · c0_hsteps; exact hJmode () mk ⟨sck, hlenk, hcovk, hprek, hws2k, hmk⟩
        · fs_nojnz
          fs_jnz hcnt
          · c0_hsteps_nogrp
            fs_call hSortAna
            refine m6SortAnaQsSpec_of hlen2
              (by simpa [s2, fidMkBumpState, fs_bv64_ofNat (by omega : mcl2 < 2 ^ 64)] using
                hmcl2_cv)
              (fun k hk => by
                rw [Arg.val_var, fs_bv64_ofNat (by omega)] at hk
                exact (hcov2.2.2.1 k hk).1)
              hm2 fun ws3 m3 hws3 hperm _ _ hm3 => ?_
            rw [Arg.val_var, fs_bv64_ofNat (by omega)] at hperm
            c0_hsteps
            exact hJsrt () m3 ⟨ws3, hws3, fid_bump_perm_marksCov hcv_le hws2 hws3 hcov2 hperm, hm3⟩
          · c0_hsteps; exact hJsrt () m2 ⟨ws2, hws2, hcov2, hm2⟩
      · -- Stable branch (`h->stable != 0ULL`): `full_bump_var` + `full_bump_decay` only
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
          (proj := fun st => BitVec.ofNat 64 st.1)
          (μ := fun st => mcl2 - st.1)
          (Inv := fun st mk => st.1 ≤ mcl2 ∧
            let sk : FullState := { s2 with scratch := st.2 }
            sk.LengthsOk c ∧ FullAnaMarksCov c sk ∧ FullExtScratchPres s2 sk ∧
            st.2.work_stk1 = ws2 ∧ st.2.work_stk2 = s2.scratch.work_stk2 ∧
            (FullMem c sk ⋆ R_hdr) mk)
          (fun Jk hJk => by
            c0_hsteps; exact hJk (0, s2.scratch) m2 ⟨Nat.zero_le _, hlen2, hcov2,
              ⟨rfl, rfl⟩, rfl, rfl, hm2⟩)
          (fun Jk (k, sck) mk ⟨hk_le, hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
        dsimp only at hk_le hlenk hcovk hprek hws1k hws2k hmk ihk
        rw [Blocks.get_here]; dsimp only
        let sk : FullState := { s2 with scratch := sck }
        c0_hsteps_nogrp
        · have hk_lt : k < mcl2 := by
            have hlt : k % 2 ^ 64 < mcl2 % 2 ^ 64 := by
              simpa [BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : mcl2 < 2 ^ 64)] at hlt
          have hk_ws1 : k < sck.work_stk1.length := by
            rw [hlenk.scratch_ok.work_stk1_len]; omega
          let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
            (by rw [fs_bv64_ofNat (by omega)]; exact hk_ws1)
          have hbv_eq : bv = ws2[k]'(by rw [hws2]; omega) := by
            dsimp only [bv]; exact fs_getElem_congr hws1k (fs_bv64_ofNat (by omega))
          have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
            have hcov_k := hcovk.2.2.1 k hk_lt
            dsimp only [sk, s2, fidMkBumpState] at hcov_k
            rw [hws1k, List.getElem?_eq_getElem (by rw [hws2]; omega),
              Option.getD_some] at hcov_k
            simpa [hbv_eq] using hcov_k.1
          have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
            BitVec.eq_of_toNat_eq (by
              rw [show (1 : BitVec 64) = 1#64 from rfl,
                fs_bv64_add1 (by rw [fs_bv64_ofNat (by omega)]; omega),
                fs_bv64_ofNat (by omega), fs_bv64_ofNat (by omega)])
          have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
            rw [fs_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullScratch)
            (Inv := fun sc' m' =>
              let sk' : FullState := { s2 with scratch := sc' }
              sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s2 sk' ∧
              sc'.work_stk1 = ws2 ∧ sc'.work_stk2 = s2.scratch.work_stk2 ∧
              (FullMem c sk' ⋆ R_hdr) m')
            (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
              rw [Blocks.get_here]; c0_hsteps; rw [hk1_bv]
              exact ihk (k + 1, sc') m' (by dsimp only; omega)
                ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
            (fun Jstep hJstep => ?_)
          c0_hsteps_nogrp
          · exact fid_bump_pass_step rfl (hBumpVar · · · ·) hlenk hcovk hprek hws1k hws2k
              hmk rfl fun sc' m' h1 h2 h3 h4 h5 h6 => hJstep sc' m' ⟨h1, h2, h3, h4, h5, h6⟩
          · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
          · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
        · c0_hsteps_nogrp
          fs_call hBumpDecay
          refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk' m' hcore' hsafe' hpres' hm' => ?_⟩
          dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
            Full.fullSafetySlice_safe] at hcore' hsafe' hm'
          have hcs' : sk'.core = sk.core := @Full.fullCoreState_agrees_with_scratch c sk sk' hcore'
          let sf : FullState :=
            { s with core := { s.core with mrk := mrk2, min_clr_len := mcl2 }
                     scratch := sk'.scratch }
          have hsf_eq : sk' = sf := by
            cases sk'; dsimp only [sk, s2, fidMkBumpState, sf] at hcs' ⊢; rw [hcs']
          rw [hsf_eq] at hsafe' hm'
          c0_hsteps
          exact hJmode () m' ⟨sk'.scratch, hsafe', fid_anaMarksCov_of_core_eq hcovk rfl hpres'.2.1,
            ⟨hpres'.1.1.trans hprek.1, hpres'.1.2.trans hprek.2⟩,
            hpres'.2.2.1.trans hws2k, hm'⟩
    · fs_call hDrAllow
      refine m6HdrDrAllowSpec_of hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
        fun allow ext1 m1 hinit1 hext_eq hm1 => ?_
      have hext1 : M6HdrExtOk ext1 := hinit1.toOk
      have hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ ext1 = ext :=
        fun hi => ⟨hext_eq hi ▸ hi, hext_eq hi⟩
      rw [fullM6HdrMem_iff] at hm1
      let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
      c0_hsteps_nogrp
      · refine wp_join_state1 (t := i64) (α := Nat)
          (proj := BitVec.ofNat 64)
          (Inv := fun tlen mt => tlen ≤ s.core.cur_vars ∧ mt = m1)
          (fun Jt tlen mt ⟨htlen_le, hmt⟩ => ?_) (fun Jt hJt => ?_)
        · rcases hmt with rfl; rw [Blocks.get_here]; dsimp only
          have htlen_bv : (BitVec.ofNat 64 tlen).toNat = tlen := fs_bv64_ofNat (by omega)
          c0_hsteps_nogrp
          refine wp_while_state1 (t := i64) (α := Nat × FidBumpSt)
            (proj := fun st => BitVec.ofNat 64 st.1)
            (μ := fun st => tlen - st.1)
            (Inv := fun st mi => st.1 ≤ tlen ∧ fidBumpAllowInv c s R_hdr st.2 mi)
            (fun Ji hJi => by
              c0_hsteps; exact hJi (0, s.core.mrk, saved, s.scratch.work_stk1) mt
                ⟨Nat.zero_le _, hmrk0_len, hws10_len, by simpa [fidMkBumpState, saved] using hcov,
                  hm1⟩)
            (fun Ji (i, mrk_i, mcl_i, ws_i) mi ⟨hi_le, hmrk_i, hws_i, hcov_i, hmi⟩ ihi => ?_)
          dsimp only at hi_le hmrk_i hws_i hcov_i hmi ihi
          rw [Blocks.get_here]; dsimp only
          let si := fidMkBumpState s mrk_i mcl_i ws_i
          have hcv_si : si.core.cur_vars = s.core.cur_vars := rfl
          refine wp_join_group (ts := [])
            (fun () mr => ∃ st_a : FidBumpSt, fidBumpAllowInv c s R_hdr st_a mr)
            (fun _ () mr ⟨⟨mrk_a, mcl_a, ws_a⟩, hmrk_a, hws_a, hcov_a, hmr⟩ => by
              rw [Blocks.get_here]
              refine wp_join_group (ts := [])
                (fun () m_out => ∃ st_out : FidBumpSt, fidBumpAllowInv c s R_hdr st_out m_out)
                (fun _ () m_out ⟨⟨mrk_r, mcl_r, ws_r⟩, hmrk_r, hws_r, hcov_r, hmr_r⟩ => by
                  rw [Blocks.get_here]; c0_hsteps
                  exact hJallow () m_out
                    ⟨ext1, ⟨mrk_r, mcl_r, ws_r⟩, hext1, hinit_pres, hmrk_r, hws_r, hcov_r, hmr_r⟩)
                (fun Jrb hJrb => ?_)
              c0_hsteps_nogrp
              · refine wp_while_state0 (α := FidBumpSt)
                  (μ := fun st => st.2.1)
                  (Inv := fun st mr' => fidBumpAllowInv c s R_hdr st mr')
                  (fun Jr hJr => ?_)
                  (fun Jr (mrk_r, mcl_r, ws_r) mr' ⟨hmrk_r, hws_r, hcov_r, hmr'⟩ ihr => ?_)
                · c0_hsteps
                  exact hJr (mrk_a, mcl_a, ws_a) mr ⟨hmrk_a, hws_a, hcov_a, hmr⟩
                · dsimp only at hmrk_r hws_r hcov_r hmr' ihr
                  rw [Blocks.get_here]; dsimp only
                  let sr := fidMkBumpState s mrk_r mcl_r ws_r
                  have hmcl_r_cv : mcl_r ≤ s.core.cur_vars := hcov_r.1
                  c0_hsteps_nogrp
                  · have hmcl_r_pos : 0 < mcl_r := by
                      have hgt : saved % 2 ^ 64 < mcl_r % 2 ^ 64 := by assumption
                      rw [Nat.mod_eq_of_lt (by omega : saved < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : mcl_r < 2 ^ 64)] at hgt
                      omega
                    have hmcl_m1_bv : (BitVec.ofNat 64 mcl_r - 1#64).toNat = mcl_r - 1 := by
                      have hm_nz : BitVec.ofNat 64 mcl_r ≠ 0#64 := fun h0 => by
                        have := congrArg BitVec.toNat h0
                        rw [fs_bv64_ofNat (by omega), show (0#64 : BitVec 64).toNat = 0 from rfl]
                          at this
                        omega
                      rw [fs_bv64_sub1 hm_nz, fs_bv64_ofNat (by omega)]
                    have hmcl_ws :
                        (BitVec.ofNat 64 mcl_r - 1#64).toNat < sr.scratch.work_stk1.length := by
                      rw [hmcl_m1_bv, hws_r]; omega
                    let rv := sr.scratch.work_stk1[(BitVec.ofNat 64 mcl_r - 1#64).toNat]'hmcl_ws
                    have hmcl_ws' : mcl_r - 1 < ws_r.length := by rw [hws_r]; omega
                    have hrv_eq : rv = ws_r[mcl_r - 1]'hmcl_ws' :=
                      fs_getElem_congr rfl hmcl_m1_bv
                    have hrv_lt : rv.toNat < s.core.cur_vars := by
                      have hcov_prev :=
                        (hcov_r.2.2.1 (mcl_r - 1) (by dsimp only [fidMkBumpState]; omega)).1
                      dsimp only [sr, fidMkBumpState] at hcov_prev
                      rw [List.getElem?_eq_getElem hmcl_ws', Option.getD_some] at hcov_prev
                      simpa [hrv_eq] using hcov_prev
                    have hrv_mrk : (rv.setWidth 64).toNat < mrk_r.length := by
                      rw [fs_bv32_setWidth64, hmrk_r]; omega
                    refine wp_join_state0 (α := FidBumpSt)
                      (Inv := fun st mr'' => st.2.1 < mcl_r ∧ fidBumpAllowInv c s R_hdr st mr'')
                      (fun _ st mr'' ⟨hm_lt, hinv⟩ => by
                        rw [Blocks.get_here]; c0_hsteps; exact ihr st mr'' hm_lt hinv)
                      (fun Js2 hJs2 => ?_)
                    c0_hsteps_nogrp
                    · have hcov_pop := fid_bump_pop_marksCov hmrk_r hws_r hcv_le hcov_r hmcl_r_pos
                      c0_hsteps
                      have hmod32 :
                          ∀ (b : BitVec 32), b.toNat % 18446744073709551616 = b.toNat :=
                        fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                      exact hJs2 (mrk_r.set rv.toNat 0#8, mcl_r - 1, ws_r) _
                        ⟨by dsimp only; omega, by simp [hmrk_r], hws_r,
                          by simpa [hrv_eq] using hcov_pop, by
                          simpa [sr, fidMkBumpState, rv, hmcl_m1_bv, fs_bv32_setWidth64, hmod32,
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
                        (fs_getElem_congr rfl hge_idx).trans hrv_eq.symm
                      have hge := hc
                      rw [hrv_hc, Nat.mod_eq_of_lt hcv_lt64] at hge
                      omega
                  · exact hJrb () mr' ⟨(mrk_r, mcl_r, ws_r), hmrk_r, hws_r, hcov_r, hmr'⟩
              · exact hJrb () mr ⟨(mrk_a, mcl_a, ws_a), hmrk_a, hws_a, hcov_a, hmr⟩)
            (fun Jafter hJafter => ?_)
          c0_hsteps_nogrp
          · have hi_lt : i < tlen := by
              have hlt : i % 2 ^ 64 < tlen % 2 ^ 64 := by
                simpa [BitVec.toNat_ofNat] using (by assumption : _)
              rwa [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : tlen < 2 ^ 64)] at hlt
            have hi_tmp : i < si.core.tmp.length := by
              rw [show si.core.tmp = s.core.tmp from rfl, hco.tmp_len_arr]; omega
            have hi_tmp_bv : (BitVec.ofNat 64 i).toNat < si.core.tmp.length := by
              rw [fs_bv64_ofNat (by omega)]; exact hi_tmp
            have hi1_bv : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) :=
              BitVec.eq_of_toNat_eq (by
                rw [show (1 : BitVec 64) = 1#64 from rfl,
                  fs_bv64_add1 (by rw [fs_bv64_ofNat (by omega)]; omega),
                  fs_bv64_ofNat (by omega), fs_bv64_ofNat (by omega)])
            let uv32 := (si.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp_bv) >>> 1#32
            c0_hsteps_nogrp
            refine wp_join_state1 (t := i32) (α := BitVec 32)
              (proj := fun x => x) (Inv := fun _ mr => mr = mi)
              (fun Jr rsn mr hmr => ?_) (fun Jr hJr => ?_)
            · rw [hmr] at *; clear mr hmr; rw [Blocks.get_here]; dsimp only
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FidBumpSt)
                (Inv := fun st' mi' => fidBumpAllowInv c s R_hdr st' mi')
                (fun _ st' mi' hst' => by
                  rw [Blocks.get_here]; try dsimp only
                  c0_hsteps; rw [hi1_bv]
                  exact ihi (i + 1, st') mi' (by dsimp only; omega) ⟨by omega, hst'⟩)
                (fun Jstep hJstep => ?_)
              refine wp_join_group (ts := []) (fun () m' => m' = mi)
                (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
              · rw [hm'] at *; clear m' hm'; rw [Blocks.get_here]; dsimp only
                refine wp_join_state0 (α := FidBumpSt)
                  (Inv := fun st' mi' => fidBumpAllowInv c s R_hdr st' mi')
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
                  have hrsn2 : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
                  have hrsn2_eq : (rsn.setWidth 64 + 2#64).toNat = (rsn.toNat + 2) % 2 ^ 64 := by
                    bv_omega
                  let sz := s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn2
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FidBumpSt)
                    (Inv := fun st' mj' => fidBumpAllowInv c s R_hdr st' mj')
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
                    refine wp_while_state1 (t := i32) (α := BitVec 32 × FidBumpSt)
                      (proj := fun st => st.1) (μ := fun st => sz.toNat - st.1.toNat)
                      (Inv := fun st mj => st.1.toNat ≤ sz.toNat ∧
                        fidBumpAllowInv c s R_hdr st.2 mj)
                      (fun Jj hJj => by
                        c0_hsteps; exact hJj (0#32, mrk_i, mcl_i, ws_i) mi
                          ⟨Nat.zero_le _, hmrk_i, hws_i, hcov_i, hmi⟩)
                      (fun Jj (j, mrk_j, mcl_j, ws_j) mj ⟨hj_le, hmrk_j, hws_j, hcov_j, hmj⟩
                        ihj => ?_)
                    dsimp only at hj_le hmrk_j hws_j hcov_j hmj ihj
                    rw [Blocks.get_here]; dsimp only
                    let sj := fidMkBumpState s mrk_j mcl_j ws_j
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
                        dsimp only [sj, fidMkBumpState]; bv_omega
                      let ov : BitVec 32 :=
                        (sj.core.arena[(rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat]'har_j) >>>
                          (1 : Nat)
                      have hj1_bv : (j + 1#32).toNat = j.toNat + 1 :=
                        fs_bv32_add1 (by have := sz.isLt; omega)
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FidBumpSt)
                        (Inv := fun st' mj' => fidBumpAllowInv c s R_hdr st' mj')
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
                          rw [fs_bv32_setWidth64, hco.lvl_len]; omega
                        have hov_mrk : (ov.setWidth 64).toNat < mrk_j.length := by
                          rw [fs_bv32_setWidth64, hmrk_j]; omega
                        c0_hsplit
                        · c0_hsplit
                          · have hmrk_hc := hc
                            c0_hsplit
                            · obtain ⟨hcov', hmcl1_bv⟩ := fid_bump_push_ok hmrk_j hws_j hcv_le
                                hcv_lt64 hcov_j hov_cv (by assumption) (by
                                  rw [List.getElem?_eq_getElem (by rw [hmrk_j]; omega),
                                    Option.getD_some]
                                  refine fs_bv8_zext32_eq0_iff.mp ?_
                                  have hmod32 : ∀ (b : BitVec 32),
                                      b.toNat % 18446744073709551616 = b.toNat :=
                                    fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                                  simpa [ov, sj, fidMkBumpState, BitVec.toNat_ushiftRight, hmod32,
                                    Nat.shiftRight_eq_div_pow,
                                    show BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32
                                      from rfl] using hmrk_hc)
                              c0_hsteps
                              have hmod32 :
                                  ∀ (b : BitVec 32), b.toNat % 18446744073709551616 = b.toNat :=
                                fun b => Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
                              exact hJjs (mrk_j.set ov.toNat 1#8, mcl_j + 1, ws_j.set mcl_j ov) _
                                ⟨by simp [hmrk_j], by simp [hws_j], hcov', by
                                  simpa [sj, fidMkBumpState, ov, hmcl1_bv, hmod32,
                                    BitVec.toNat_ushiftRight,
                                    fs_bv64_ofNat (by omega : mcl_j < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by omega : mcl_j + 1 < 2 ^ 64),
                                    show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                            · exact hJjs (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                          · exact hJjs (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                        · exact hJjs (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                      · exact hJjs (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                    · exact hJsz (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                    · exact hJsz (mrk_j, mcl_j, ws_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                  · exact hJsz (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                  · exact hJsz (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJs (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJs (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
              · c0_hsteps_nogrp
                · refine wp_join_state0 (α := FidBumpSt)
                    (Inv := fun st' mi' => fidBumpAllowInv c s R_hdr st' mi')
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
                      rw [fs_bv32_setWidth64, hco.lvl_len]; omega
                    have hov_mrk : (ov.setWidth 64).toNat < mrk_i.length := by
                      rw [fs_bv32_setWidth64, hmrk_i]; omega
                    c0_hsplit
                    · c0_hsplit
                      · have hmrk_hc := hc
                        c0_hsplit
                        · have hmod_rsn : rsn.toNat % 18446744073709551616 = rsn.toNat :=
                            Nat.mod_eq_of_lt (Nat.lt_trans rsn.isLt (by decide))
                          obtain ⟨hcov', hmcl1_bv⟩ := fid_bump_push_ok hmrk_i hws_i hcv_le
                            hcv_lt64 hcov_i hov_cv (by assumption) (by
                              rw [List.getElem?_eq_getElem (by rw [hmrk_i]; omega),
                                Option.getD_some]
                              exact fs_bv8_zext32_eq0_iff.mp (by
                                simpa [ov, BitVec.toNat_ushiftRight, BitVec.toNat_and, hmod_rsn,
                                  Nat.shiftRight_eq_div_pow,
                                  show BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32
                                    from rfl] using hmrk_hc))
                          c0_hsteps
                          exact hJbin (mrk_i.set ov.toNat 1#8, mcl_i + 1, ws_i.set mcl_i ov) _
                            ⟨by simp [hmrk_i], by simp [hws_i], hcov', by
                              simpa [fidMkBumpState, ov, hmcl1_bv, hmod_rsn,
                                BitVec.toNat_ushiftRight, BitVec.toNat_and,
                                fs_bv64_ofNat (by omega : mcl_i < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : mcl_i + 1 < 2 ^ 64),
                                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                        · exact hJbin (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                      · exact hJbin (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                    · exact hJbin (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                  · exact hJbin (mrk_i, mcl_i, ws_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                · exact hJelse () mi rfl
                · exact hJelse () mi rfl
            · c0_hsteps_nogrp
              · have huv_lt : uv32.toNat < s.core.cur_vars := by
                  have h1 : uv32.toNat < s.core.cur_vars % 2 ^ 64 := by
                    simpa [uv32, si, fidMkBumpState, fs_bv32_setWidth64, fs_bv32_lshr1] using
                      (by assumption : _)
                  rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                have huv_cv : (uv32.setWidth 64).toNat < si.core.rsns.length := by
                  rw [fs_bv32_setWidth64, hco.rsns_len]; omega
                c0_hsteps; exact hJr _ mi rfl
              · c0_hsteps; exact hJr _ mi rfl
          · exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i), hmrk_i, hws_i, hcov_i, hmi⟩
          · exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i), hmrk_i, hws_i, hcov_i, hmi⟩
        · c0_hsteps
          · exact hJt s.core.cur_vars m1 ⟨Nat.le_refl _, rfl⟩
          · have htlen_le : s.core.tmp_len ≤ s.core.cur_vars := by
              have hcv64 : s.core.cur_vars < 2 ^ 64 := hcv_lt64
              have htl_le := hco.tmp_len_le
              have htl64 : s.core.tmp_len < 2 ^ 64 := by omega
              have hle : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by assumption
              rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt htl64] at hle; omega
            exact hJt s.core.tmp_len m1 ⟨htlen_le, rfl⟩
      · exact hJallow () m1 ⟨ext1, ⟨s.core.mrk, saved, s.scratch.work_stk1⟩, hext1, hinit_pres,
          hmrk0_len, hws10_len, by simpa [fidMkBumpState, saved] using hcov, hm1⟩

end BumpAnalyzedProof

/-! ## 3. `full_switch_mode_fid_wp` (`FullM7Search.m7SwitchModeSpec`) -/

section SwitchModeProof

private theorem fid_apply_ite {α β : Type} (f : α → β) (P : Prop) [Decidable P] (a b : α) :
    f (if P then a else b) = if P then f a else f b := by
  by_cases h : P <;> simp [h]

private theorem fid_ite_eq {α : Type} (P : Prop) [Decidable P] {a b c : α}
    (ha : a = c) (hb : b = c) : (if P then a else b) = c := by
  by_cases h : P <;> simp [h, ha, hb]

private theorem fid_emaSwapSc_proj {α : Type} (f : FullScratch → α)
    (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
      f { sc with
        stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
        ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc)
    (sc : FullScratch) (om nm : BitVec 64) :
    f (m7EmaSwapSc sc om nm) = f sc := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [fid_apply_ite f]
  exact fid_ite_eq _ (hf _ _ _ _ _ _ _) (hf _ _ _ _ _ _ _)

private theorem fid_probePres_emaSwap (sc : FullScratch) (om nm : BitVec 64)
    {s0 s1 : FullState} (hp : FullProbeScratchPres s0 s1)
    (hsc : s1.scratch = sc) :
    FullProbeScratchPres s0 { s1 with scratch := m7EmaSwapSc sc om nm } := by
  subst hsc
  have h : ∀ {α} (f : FullScratch → α)
      (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
        f { sc with
          stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
          ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc),
      f (m7EmaSwapSc s1.scratch om nm) = f s1.scratch :=
    fun f hf => fid_emaSwapSc_proj f hf s1.scratch om nm
  exact ⟨⟨(h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.1,
      (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.2⟩,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.2⟩

private theorem fid_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fid_probePres_trans {s0 s1 s2 : FullState}
    (h1 : FullProbeScratchPres s0 s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s0 s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

private theorem fid_ema_swap_f2s_stable (sc : FullScratch) :
    (m7EmaSwapSc sc 0#64 1#64).stable = 1#64 := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [fid_apply_ite FullScratch.stable]
  exact fid_ite_eq _ rfl rfl

private theorem fid_get64_emaSet_mask (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    m7Get64Val (m7ModeEmaSet gu mode v) m7GuEmaMaskIdx = m7Get64Val gu m7GuEmaMaskIdx := by
  have hltG : ∀ (g : List (BitVec 32)) idx val, 40 ≤ idx →
      m7Get64Val (m7Set64List g idx val) m7GuEmaMaskIdx = m7Get64Val g m7GuEmaMaskIdx :=
    fun g idx val hidx => m7Get64Val_set64_ne val (Or.inl (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaSet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hltG _ 46 _ (by omega), hltG _ 44 _ (by omega),
      hltG _ 42 _ (by omega), hltG _ 40 _ (by omega)]
  · rw [hltG _ 54 _ (by omega), hltG _ 52 _ (by omega),
      hltG _ 50 _ (by omega), hltG _ 48 _ (by omega)]

private theorem fid_modeEmaGet_set_mask (gu : List (BitVec 32)) (mode : Nat)
    (idx : BitVec 64) :
    m7ModeEmaGet (m7Set64List gu m7GuEmaMaskIdx idx) mode = m7ModeEmaGet gu mode := by
  have hge : ∀ j, 40 ≤ j → m7Get64Val (m7Set64List gu m7GuEmaMaskIdx idx) j = m7Get64Val gu j :=
    fun j hj => m7Get64Val_set64_ne idx (Or.inr (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hge 40 (by omega), hge 42 (by omega), hge 44 (by omega), hge 46 (by omega)]
  · rw [hge 48 (by omega), hge 50 (by omega), hge 52 (by omega), hge 54 (by omega)]

private theorem fid_bit0_or_left {a b : BitVec 64} (h : (a &&& 1#64) ≠ 0#64) :
    ((a ||| b) &&& 1#64) ≠ 0#64 := by
  intro hc
  have h1 := congrArg (fun x : BitVec 64 => x[0]) hc
  simp only [BitVec.getElem_and, BitVec.getElem_or,
    show (1#64 : BitVec 64)[0] = true by decide, Bool.and_true,
    show (0#64 : BitVec 64)[0] = false by decide, Bool.or_eq_false_iff] at h1
  apply h
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rcases k with rfl | k
  · simp [h1.1]
  · have hb : (1#64 : BitVec 64)[k + 1] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#64 : BitVec 64).toNat = 1 by decide,
        Nat.testBit_succ]
      simp
    simp only [BitVec.getElem_and, BitVec.getElem_zero, hb, Bool.and_false]

private theorem fid_ema_swap_s2f_facts (sc : FullScratch) (hgu : sc.glue_used.length = 64) :
    let sc' := m7EmaSwapSc sc 1#64 0#64
    sc'.stable = 0#64 ∧
      m7ModeEmaGet sc'.glue_used 1 =
        (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp) ∧
      ((m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic ∧
        (m7Get64Val sc.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
       let saved := m7ModeEmaGet sc.glue_used 0
       sc'.ema_fast_biased = saved.1 ∧ sc'.ema_fast_exp = saved.2.1 ∧
       sc'.ema_slow_biased = saved.2.2.1 ∧ sc'.ema_slow_exp = saved.2.2.2) := by
  rw [m7EmaSwapSc_eq]; dsimp only
  simp only [show ((1#64 : BitVec 64) ≠ 0#64) = True by decide,
    show ((0#64 : BitVec 64) ≠ 0#64) = False by decide, ↓reduceIte]
  let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 1 }
  have hgu0 : gu0.length = 64 := (m7StateInitGu_length _).trans hgu
  let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
  let gu1 := m7ModeEmaSet gu0 1 curV
  let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| 1#64 <<< 1
  refine ⟨?_, ?_, ?_⟩
  · rw [fid_apply_ite FullScratch.stable]; exact fid_ite_eq _ rfl rfl
  · by_cases hcond : mask &&& 1#64 <<< 0 ≠ 0#64
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_true hc', ↓reduceIte, fid_modeEmaGet_set_mask]
      exact m7ModeEmaGet_set_self curV hgu0
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_false hc', ↓reduceIte, fid_modeEmaGet_set_mask]
      rw [m7ModeEmaGet_set_other _ (by decide : (0 = 0) ≠ (1 = 0))]
      exact m7ModeEmaGet_set_self curV hgu0
  · rintro ⟨hmag, hmask⟩
    have hgu0_eq : gu0 = sc.glue_used := m7StateInitGu_of_magic hmag
    have hmask1 : m7Get64Val gu1 m7GuEmaMaskIdx = m7Get64Val sc.glue_used m7GuEmaMaskIdx := by
      dsimp only [gu1]; rw [fid_get64_emaSet_mask, hgu0_eq]
    have hcond : mask &&& 1#64 <<< 0 ≠ 0#64 := by
      rw [show (1#64 <<< 0 : BitVec 64) = 1#64 by decide]
      dsimp only [mask]; rw [hmask1]
      exact fid_bit0_or_left hmask
    have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
    simp only [eq_true hc', ↓reduceIte]
    have hnw : m7ModeEmaGet gu1 0 = m7ModeEmaGet sc.glue_used 0 := by
      dsimp only [gu1]; rw [m7ModeEmaGet_set_other _ (by decide : (1 = 0) ≠ (0 = 0)), hgu0_eq]
    rw [hnw]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem fid_modeEmaGet1_set64_ge56 (gu : List (BitVec 32)) {idx : Nat} (val : BitVec 64)
    (hidx : 56 ≤ idx) :
    m7ModeEmaGet (m7Set64List gu idx val) 1 = m7ModeEmaGet gu 1 := by
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma1FbIdx_eq]; dsimp only
  simp only [show (1 = 0) = False by decide, ↓reduceIte]
  rw [m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega))]

private theorem fid_call_set64_randec {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {s0 s : FullState} {idx val : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, val, ()))
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hidx_lo : 56 ≤ idx.toNat) (hidx_hi : idx.toNat < 63)
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hps : FullProbeScratchPres s0 s)
    (hpre : M7GuPrefixPres s0 s) (hinit : M7StateInitOk s.scratch.glue_used)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      s'.core = s0.core → s'.LengthsOk c → FullProbeScratchPres s0 s' →
      M7GuPrefixPres s0 s' → M7StateInitOk s'.scratch.glue_used →
      m7ModeEmaGet s'.scratch.glue_used 1 = m7ModeEmaGet s.scratch.glue_used 1 →
      s'.scratch.stable = s.scratch.stable →
      s'.scratch.conflicts = s.scratch.conflicts →
      s'.scratch.ema_fast_biased = s.scratch.ema_fast_biased →
      s'.scratch.ema_fast_exp = s.scratch.ema_fast_exp →
      s'.scratch.ema_slow_biased = s.scratch.ema_slow_biased →
      s'.scratch.ema_slow_exp = s.scratch.ema_slow_exp →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ (m7Set64Spec_of hlen hm fun hlen' m' hm' => ?_)
  dsimp only at hlen' hm'
  simp only [hidx_hi, ↓reduceIte] at hlen' hm'
  let sc' : FullScratch :=
    { s.scratch with glue_used := m7Set64List s.scratch.glue_used idx.toNat val }
  let s' : FullState := { s with scratch := sc' }
  have hps' : FullProbeScratchPres s0 s' := hps
  have hpre' : M7GuPrefixPres s0 s' :=
    M7GuPrefixPres.trans hpre (M7GuPrefixPres.of_set64 val (by omega))
  have hinit' : M7StateInitOk s'.scratch.glue_used :=
    M7StateInitOk.of_set64 hinit (by omega) val
  have hema1' : m7ModeEmaGet s'.scratch.glue_used 1 = m7ModeEmaGet s.scratch.glue_used 1 :=
    fid_modeEmaGet1_set64_ge56 s.scratch.glue_used val hidx_lo
  exact hk s' m' hcore hlen' hps' hpre' hinit' hema1' rfl rfl rfl rfl rfl rfl hm'

/-- WP proof for `full_switch_mode_fid` against `FullM7Search.m7SwitchModeSpec`,
additionally resetting `M7_GU_RANDEC_{REM,LIM,SEQ,CFL}` (`glue_used[56..63]`) on focused switch. -/
theorem full_switch_mode_fid_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7SwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, hc_eq, hlen, hm, hQ⟩ := m7SwitchModeSpec_elim hspec
  dsimp only at hc_eq; subst hc_eq
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  let P : Tup Val [i64, i64] → Mem 64 → Prop := fun (om, nm, _) mJ =>
    ∃ sJ : FullState,
      sJ.core = s.core ∧ sJ.LengthsOk c ∧ FullProbeScratchPres s sJ ∧
      om = (if s.scratch.stable = 0#64 then 0#64 else 1#64) ∧
      nm = (if s.scratch.stable = 0#64 then 1#64 else 0#64) ∧
      (s.scratch.stable = 0#64 → s.scratch.mode_confl_lim ≤ s.scratch.conflicts) ∧
      (s.scratch.stable ≠ 0#64 →
        s.scratch.mode_tick_lim ≤ s.scratch.search_ticks ∧ M7GuPrefixPres s sJ ∧
        sJ.scratch.glue_used = s.scratch.glue_used ∧
        sJ.scratch.ema_fast_biased = s.scratch.ema_fast_biased ∧
        sJ.scratch.ema_fast_exp = s.scratch.ema_fast_exp ∧
        sJ.scratch.ema_slow_biased = s.scratch.ema_slow_biased ∧
        sJ.scratch.ema_slow_exp = s.scratch.ema_slow_exp) ∧
      (FullMem c sJ ⋆ R) mJ
  refine wp_join_group P ?_ ?_
  · rintro Js ⟨om, nm, ⟨⟩⟩ mJ ⟨sJ, hcJ, hlenJ, hpsJ, hom, hnm, hf2s, hs2f, hmJ⟩
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64
      mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c := fid_len_scalars hlenJ
    fs_call hEmaSwap
    refine m7EmaSwapSpec_of hlenJ1 (by assumption) fun hlenSw hpreSw hinitSw mSw hmSw => ?_
    let sSw : FullState := { sJ1 with scratch := m7EmaSwapSc sJ1.scratch om nm }
    let Pret : Tup Val [] → Mem 64 → Prop := fun _ mRet =>
      ∃ sRet : FullState,
        sRet.core = s.core ∧ sRet.LengthsOk c ∧ FullProbeScratchPres s sRet ∧
        (s.scratch.stable = 0#64 →
          M7StateInitOk sRet.scratch.glue_used ∧ sRet.scratch.stable = 1#64) ∧
        (s.scratch.stable ≠ 0#64 →
          M7GuPrefixPres s sRet ∧ M7StateInitOk sRet.scratch.glue_used ∧
          m7ModeEmaGet sRet.scratch.glue_used 1 =
            (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
             s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
          sRet.scratch.stable = 0#64 ∧
          ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
            (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
           let saved := m7ModeEmaGet s.scratch.glue_used 0
           sRet.scratch.ema_fast_biased = saved.1 ∧ sRet.scratch.ema_fast_exp = saved.2.1 ∧
           sRet.scratch.ema_slow_biased = saved.2.2.1 ∧
           sRet.scratch.ema_slow_exp = saved.2.2.2)) ∧
        (FullMem c sRet ⋆ R) mRet
    refine wp_join_group Pret ?_ ?_
    · rintro Js_r ⟨⟩ mRet ⟨sRet, hcRet, hlenRet, hpsRet, hrf2s, hrs2f, hmRet⟩
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      refine hQ sRet mRet hcRet hlenRet hpsRet ?_ ?_ ?_ hmRet
      · intro hEarly
        exfalso
        rcases hEarly with ⟨hst0, hlt⟩ | ⟨hstne, hlt⟩
        · have hle := hf2s hst0
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
        · have hle := (hs2f hstne).1
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
      · rintro ⟨hst0, _⟩; exact hrf2s hst0
      · rintro ⟨hstne, _⟩; exact hrs2f hstne
    · intro Js_r hJs_r
      have hpsSw : FullProbeScratchPres s sSw :=
        fid_probePres_emaSwap sJ1.scratch om nm hpsJ rfl
      fs_nojnz
      fs_jnz hstab0
      · simp only [beq_iff_eq] at hstab0
        have hstne : s.scratch.stable ≠ 0#64 := by
          intro hst0
          have hom0 : om = 0#64 := by simp [hom, hst0]
          have hnm1 : nm = 1#64 := by simp [hnm, hst0]
          have h1 : sSw.scratch.stable = 1#64 := by
            dsimp only [sSw]; rw [hom0, hnm1]; exact fid_ema_swap_f2s_stable _
          rw [h1] at hstab0
          exact absurd hstab0 (by decide)
        obtain ⟨_, hpreJ, hguJ, hfbJ, hfeJ, hsbJ, hseJ⟩ := hs2f hstne
        have hom1 : om = 1#64 := by simp [hom, hstne]
        have hnm0 : nm = 0#64 := by simp [hnm, hstne]
        have hguSw : sJ1.scratch.glue_used.length = 64 := hlenJ1.scratch_ok.glue_used_len
        have hfacts := fid_ema_swap_s2f_facts sJ1.scratch hguSw
        have heq_f : sSw.scratch = m7EmaSwapSc sJ1.scratch 1#64 0#64 := by
          dsimp only [sSw]; rw [hom1, hnm0]
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mRl => mRl = mSw) ?_ ?_
        · rintro J_rl ⟨rs, ⟨⟩⟩ mRl rfl
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          let sRet0 : FullState := { sSw with scratch := { sSw.scratch with
            restart_limit := sSw.scratch.conflicts + rs } }
          have hlenRet0 : sRet0.LengthsOk c := fid_len_scalars hlenSw
          have hpre0 : M7GuPrefixPres s sRet0 :=
            M7GuPrefixPres.trans hpreJ (@M7GuPrefixPres.congr_glue sJ1 sSw sJ sRet0 rfl rfl hpreSw)
          have hema1_0 : m7ModeEmaGet sRet0.scratch.glue_used 1 =
              (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
               s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) := by
            change m7ModeEmaGet sSw.scratch.glue_used 1 = _
            rw [heq_f, hfacts.2.1]
            change (sJ.scratch.ema_fast_biased, sJ.scratch.ema_fast_exp,
              sJ.scratch.ema_slow_biased, sJ.scratch.ema_slow_exp) = _
            rw [hfbJ, hfeJ, hsbJ, hseJ]
          have hst0_0 : sRet0.scratch.stable = 0#64 := by
            change sSw.scratch.stable = 0#64; rw [heq_f]; exact hfacts.1
          have hmag_eq : m7Get64Val sJ1.scratch.glue_used m7GuMagicIdx =
              m7Get64Val s.scratch.glue_used m7GuMagicIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hmsk_eq : m7Get64Val sJ1.scratch.glue_used m7GuEmaMaskIdx =
              m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hget0_eq : m7ModeEmaGet sJ1.scratch.glue_used 0 =
              m7ModeEmaGet s.scratch.glue_used 0 := by
            change m7ModeEmaGet sJ.scratch.glue_used 0 = _; rw [hguJ]
          have hsaved0 :
              ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
                (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
               let saved := m7ModeEmaGet s.scratch.glue_used 0
               sRet0.scratch.ema_fast_biased = saved.1 ∧ sRet0.scratch.ema_fast_exp = saved.2.1 ∧
               sRet0.scratch.ema_slow_biased = saved.2.2.1 ∧
               sRet0.scratch.ema_slow_exp = saved.2.2.2) := by
            intro ⟨hm1, hm2⟩
            have hsav := hfacts.2.2 ⟨by rw [hmag_eq]; exact hm1, by rw [hmsk_eq]; exact hm2⟩
            rw [← hget0_eq]
            change sSw.scratch.ema_fast_biased = _ ∧ sSw.scratch.ema_fast_exp = _ ∧
              sSw.scratch.ema_slow_biased = _ ∧ sSw.scratch.ema_slow_exp = _
            rw [heq_f]; exact hsav
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenRet0 hcJ hpsSw
            hpre0 hinitSw (by assumption) fun sR1 mR1 hcR1 hlenR1 hpsR1 hpreR1 hinitR1 hemaR1
            hstR1 _ hfb1 hfe1 hsb1 hse1 hmR1 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR1 hcR1 hpsR1
            hpreR1 hinitR1 hmR1 fun sR2 mR2 hcR2 hlenR2 hpsR2 hpreR2 hinitR2 hemaR2
            hstR2 _ hfb2 hfe2 hsb2 hse2 hmR2 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR2 hcR2 hpsR2
            hpreR2 hinitR2 hmR2 fun sR3 mR3 hcR3 hlenR3 hpsR3 hpreR3 hinitR3 hemaR3
            hstR3 _ hfb3 hfe3 hsb3 hse3 hmR3 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR3 hcR3 hpsR3
            hpreR3 hinitR3 hmR3 fun sR4 mR4 hcR4 hlenR4 hpsR4 hpreR4 hinitR4 hemaR4
            hstR4 _ hfb4 hfe4 hsb4 hse4 hmR4 => ?_
          c0_hsteps_nogrp
          refine hJs_r () mR4 ⟨sR4, hcR4, hlenR4, hpsR4, fun h0 => absurd h0 hstne, fun _ => ?_,
            hmR4⟩
          refine ⟨hpreR4, hinitR4, ?_, ?_, fun hcond => ?_⟩
          · rw [hemaR4, hemaR3, hemaR2, hemaR1, hema1_0]
          · rw [hstR4, hstR3, hstR2, hstR1, hst0_0]
          · have hs0 := hsaved0 hcond
            rw [hfb4, hfe4, hsb4, hse4, hfb3, hfe3, hsb3, hse3, hfb2, hfe2, hsb2, hse2,
              hfb1, hfe1, hsb1, hse1]
            exact hs0
        · intro J_rl hJ_rl
          fs_nojnz
          fs_jnz hrg0
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = mSw) ?_ ?_
            · rintro J_r2 ⟨rc, ⟨⟩⟩ m2 hm2
              subst m2; rw [Blocks.get_here]; c0_hsteps_nogrp
              fs_call hIlog; intro r _ _
              refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = mSw) ?_ ?_
              · rintro J_r3 ⟨d, ⟨⟩⟩ m3 hm3
                subst m3; rw [Blocks.get_here]; c0_hsteps_nogrp
                exact hJ_rl (d, ()) mSw rfl
              · intro J_r3 hJ_r3; fs_nojnz
                fs_jnz hdg1 <;> c0_hsteps_nogrp <;> exact hJ_r3 _ mSw rfl
            · intro J_r2 hJ_r2; fs_nojnz
              fs_jnz hrlim <;> c0_hsteps_nogrp <;> exact hJ_r2 _ mSw rfl
          · c0_hsteps_nogrp; exact hJ_rl (1#64, ()) mSw rfl
      · simp only [beq_eq_false_iff_ne] at hstab0
        have hst0 : s.scratch.stable = 0#64 := by
          by_cases hst : s.scratch.stable = 0#64
          · exact hst
          · exfalso
            have hom1 : om = 1#64 := by simp [hom, hst]
            have hnm0 : nm = 0#64 := by simp [hnm, hst]
            have h0 : sSw.scratch.stable = 0#64 := by
              dsimp only [sSw]; rw [hom1, hnm0]
              exact (fid_ema_swap_s2f_facts sJ1.scratch hlenJ1.scratch_ok.glue_used_len).1
            exact hstab0 h0
        have hom0 : om = 0#64 := by simp [hom, hst0]
        have hnm1 : nm = 1#64 := by simp [hnm, hst0]
        have h1 : sSw.scratch.stable = 1#64 := by
          dsimp only [sSw]; rw [hom0, hnm1]; exact fid_ema_swap_f2s_stable _
        c0_hsteps_nogrp
        exact hJs_r () mSw ⟨sSw, hcJ, hlenSw, hpsSw,
          fun _ => ⟨hinitSw, h1⟩, fun hne => absurd hst0 hne, hmSw⟩
  · intro Js hJs
    fs_nojnz
    fs_jnz hst0
    · simp only [beq_iff_eq] at hst0
      fs_nojnz
      fs_jnz hconfl
      · simp only [BitVec.ult, decide_eq_true_eq] at hconfl
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (fid_probePres_refl s) (fun _ => rfl)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hconfl))
          (fun ⟨hne, _⟩ => absurd hst0 hne) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hconfl
        have hle_confl : s.scratch.mode_confl_lim ≤ s.scratch.conflicts :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hconfl)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
        refine wp_join_group (ts := [i64])
          (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_d ⟨delta, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          let s2 : FullState := { s1 with scratch := { s1.scratch with
            mode_tick_lim := s1.scratch.search_ticks + delta
            mode_saved_ticks := s1.scratch.search_ticks } }
          refine wp_join_group (ts := [i64])
            (fun _ m2 => (FullMem c s2 ⋆ R) m2) ?_ ?_
          · rintro J_l ⟨lim, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s3 : FullState := { s2 with scratch := { s2.scratch with
              rel_wait := lim, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
            have hlen3 : s3.LengthsOk c := fid_len_scalars hlen
            have hps3 : FullProbeScratchPres s s3 := fid_probePres_refl s
            refine wp_loop_inv (ts := [i64, i64])
              (fun (hl, i, ()) mL => ∃ hp ps : List (BitVec 32),
                hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
                hl.toNat ≤ i.toNat ∧ i.toNat ≤ s.core.cur_vars ∧
                (FullMem c { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps } } ⋆ R) mL)
              (fun (_, i, ()) _ => s.core.cur_vars - i.toNat) ?_ ?_
            · intro J3 hJ3; c0_hsteps_nogrp
              exact hJ3 (0#64, 0#64, ()) _ ⟨s3.scratch.heap, s3.scratch.pos,
                hsok.heap_len_arr, hsok.pos_len, by simp, Nat.zero_le _, by assumption⟩
            · rintro J3 ⟨hl, i, ⟨⟩⟩ mL ⟨hp, ps, hhp, hps_len, hle_hi, hi_le, hmL⟩ hJ3
              rw [Blocks.get_here]; fs_nojnz
              fs_jnz hilt
              · simp only [BitVec.ult, decide_eq_true_eq] at hilt
                have hi_lt : i.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hilt
                  rw [Nat.mod_eq_of_lt (by omega)] at hilt; exact hilt
                have hi_mx : i.toNat < c.max_vars := by omega
                refine wp_join_group (ts := [i64])
                  (fun (hl', ()) mN => ∃ hp' ps' : List (BitVec 32),
                    hp'.length = c.max_vars ∧ ps'.length = c.max_vars ∧
                    hl'.toNat ≤ i.toNat + 1 ∧
                    (FullMem c { s3 with scratch :=
                      { s3.scratch with heap := hp', pos := ps' } } ⋆ R) mN)
                  ?_ ?_
                · rintro J_nx ⟨hl', ⟨⟩⟩ mN ⟨hp', ps', hhp', hps', hle', hmN⟩
                  rw [Blocks.get_here]; c0_hsteps_nogrp
                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := fs_bv64_add1 (by omega)
                  exact hJ3 (hl', i + 1#64, ()) mN (by dsimp only; rw [hi1]; omega)
                    ⟨hp', ps', hhp', hps', by rw [hi1]; exact hle', by omega, hmN⟩
                · intro J_nx hJ_nx
                  have hfl_lt : i.toNat < s3.core.flags.length := by rw [hok.flags_len]; omega
                  fs_nojnz
                  fs_jnz hact
                  · have hhp_lt : hl.toNat < hp.length := by omega
                    have hps_lt : i.toNat < ps.length := by omega
                    rw [wp_let_mul_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    rw [wp_let_add_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    c0_hsteps_nogrp
                    have hhl1 : (hl + 1#64).toNat = hl.toNat + 1 := fs_bv64_add1 (by omega)
                    exact hJ_nx (hl + 1#64, ()) _ ⟨hp.set hl.toNat (i.setWidth 32),
                      ps.set i.toNat (hl.setWidth 32), by simpa using hhp,
                      by simpa using hps_len, by omega, by assumption⟩
                  · have hps_lt : i.toNat < ps.length := by omega
                    c0_hsteps_nogrp
                    exact hJ_nx (hl, ()) _ ⟨hp, ps.set i.toNat 0xFFFFFFFF#32, hhp,
                      by simpa using hps_len, by omega, by assumption⟩
              · c0_hsteps_nogrp
                have hhl_le : hl.toNat ≤ c.max_vars := by omega
                let s4 : FullState := { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps, heap_len := hl.toNat } }
                have hlen4 : s4.LengthsOk c :=
                  ⟨hlen3.core_ok, { hlen3.scratch_ok with heap_len_arr := hhp, pos_len := hps_len }⟩
                refine wp_loop_inv (ts := [i64])
                  (fun (k, ()) mD => ∃ sD : FullState,
                    sD.core = s.core ∧ sD.LengthsOk c ∧ FullProbeScratchPres s sD ∧
                    k.toNat ≤ c.max_vars ∧ (FullMem c sD ⋆ R) mD)
                  (fun (k, ()) _ => k.toNat) ?_ ?_
                · intro J4 hJ4; c0_hsteps_nogrp
                  exact hJ4 (hl >>> 1#64, ()) _ ⟨s4, rfl, hlen4, hps3,
                    le_trans (fs_bv64_lshr1_le hl) hhl_le, by assumption⟩
                · rintro J4 ⟨k, ⟨⟩⟩ mD ⟨sD, hcD, hlenD, hpsD, hk_le, hmD⟩ hJ4
                  rw [Blocks.get_here]; fs_nojnz
                  fs_jnz hkpos
                  · simp only [BitVec.ult, decide_eq_true_eq] at hkpos
                    have hk_gt : 0 < k.toNat := by simpa using hkpos
                    have hk1 : (k - 1#64).toNat = k.toNat - 1 :=
                      fs_bv64_sub1 (fun h => by simp [h] at hk_gt)
                    have hk1_hp : (k - 1#64).toNat < sD.scratch.heap.length := by
                      rw [hlenD.scratch_ok.heap_len_arr]; omega
                    c0_hsteps_nogrp
                    fs_call hHeapDown
                    refine ⟨c, sD, R, rfl, hlenD, hmD, fun () sD' mD' hcD' hlenD' hpost hmD' => ?_⟩
                    rcases hpost with ⟨_, hpsD'⟩
                    have hcD'_eq : sD'.core = sD.core := hcD'
                    exact hJ4 (k - 1#64, ()) mD' (by dsimp only; rw [hk1]; omega)
                      ⟨sD', hcD'_eq.trans hcD, hlenD', fid_probePres_trans hpsD hpsD',
                        by rw [hk1]; omega, hmD'⟩
                  · c0_hsteps_nogrp
                    exact hJs (0#64, 1#64, ()) mD ⟨sD, hcD, hlenD, hpsD,
                      by simp [hst0], by simp [hst0], fun _ => hle_confl,
                      fun hne => absurd hst0 hne, hmD⟩
          · intro J_l hJ_l; fs_nojnz
            fs_jnz hlim1
            · fs_nojnz
              fs_jnz hlim2 <;> c0_hsteps_nogrp <;> exact hJ_l _ _ (by assumption)
            · c0_hsteps_nogrp; exact hJ_l _ _ (by assumption)
        · intro J_d hJ_d; fs_nojnz
          fs_jnz hdiff <;> c0_hsteps_nogrp <;> exact hJ_d _ _ (by assumption)
    · simp only [beq_eq_false_iff_ne] at hst0
      fs_nojnz
      fs_jnz hticks
      · simp only [BitVec.ult, decide_eq_true_eq] at hticks
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (fid_probePres_refl s) (fun _ => rfl)
          (fun ⟨h0, _⟩ => absurd h0 hst0)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hticks)) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hticks
        have hle_ticks : s.scratch.mode_tick_lim ≤ s.scratch.search_ticks :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hticks)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        refine wp_join_group (ts := [i64]) (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_c ⟨cc, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          fs_call hLog10
          refine m7Log10Q16Spec_of fun r _ _ => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1 ⋆ R) m2) ?_ ?_
          · rintro J_d ⟨delta, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s4 : FullState := { s1 with scratch := { s1.scratch with
              mode_confl_lim := s1.scratch.conflicts + delta
              mode_saved_ticks := s1.scratch.search_ticks
              q_search_idx := s1.scratch.q_last } }
            refine wp_join_group (ts := [])
              (fun _ m5 => ∃ qss : BitVec 64,
                (FullMem c { s4 with scratch :=
                  { s4.scratch with q_search_stamp := qss } } ⋆ R) m5) ?_ ?_
            · rintro J_q ⟨⟩ m5 ⟨qss, hm5⟩
              rw [Blocks.get_here]; c0_hsteps_nogrp
              let sJ : FullState := { s4 with scratch :=
                { s4.scratch with q_search_stamp := qss } }
              have hlenJ : sJ.LengthsOk c := fid_len_scalars hlen
              exact hJs (1#64, 0#64, ()) m5 ⟨sJ, rfl, hlenJ, fid_probePres_refl s,
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                fun h0 => absurd h0 hst0,
                fun _ => ⟨hle_ticks,
                  @M7GuPrefixPres.congr_glue s s s sJ rfl rfl (M7GuPrefixPres.refl s),
                  rfl, rfl, rfl, rfl, rfl⟩, hm5⟩
            · intro J_q hJ_q; fs_nojnz
              fs_jnz hqlt
              · simp only [BitVec.ult, decide_eq_true_eq] at hqlt
                have hq_nat : s.scratch.q_last.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hqlt
                  rw [Nat.mod_eq_of_lt (by omega)] at hqlt; exact hqlt
                have hq_len : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
                  rw [hsok.q_stamp_len]; omega
                c0_hsteps_nogrp; exact hJ_q () _ ⟨_, by assumption⟩
              · c0_hsteps_nogrp; exact hJ_q () _ ⟨s4.scratch.q_search_stamp, by assumption⟩
          · intro J_d hJ_d; fs_nojnz
            fs_jnz hcle
            · c0_hsteps_nogrp; exact hJ_d _ _ (by assumption)
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mx => (FullMem c s1 ⋆ R) mx) ?_ ?_
              · rintro J_x ⟨cv, ⟨⟩⟩ mx hmx2
                rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJ_d _ _ hmx2
              · intro J_x hJ_x; fs_nojnz
                fs_jnz hcgt <;> c0_hsteps_nogrp <;> exact hJ_x _ _ (by assumption)
        · intro J_c hJ_c; fs_nojnz
          fs_jnz hcc <;> c0_hsteps_nogrp <;> exact hJ_c _ _ (by assumption)

end SwitchModeProof

/-! ## 4. `m6_hdr_decide_fid_wp` (`FullM6Hdr.m6HdrDecideSpec`) -/

section HdrDecideProof

/-- WP proof for `m6_hdr_decide_fid` against `FullM6Hdr.m6HdrDecideSpec`, delegating
decision selection + `randec` + phase alternation to `full_decide_m7`. -/
theorem m6_hdr_decide_fid_wp (Γ : Env)
    (hDecide : ∀ a m Q X, m7DecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩ := m6HdrDecideSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hcore0 := hinv.coreInv
  unfold Func.wp m6_hdr_decide_fid_body
  c0_hsteps_nogrp
  fs_call hDecide
  refine m7DecideSpec_of hcore0 ((fullM6HdrMem_iff ..).mp hm)
    fun r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m1
      hinv1 hpres1 hdom h0 h1 hm1 => ?_
  let s1 : FullState :=
    { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', frame_trail := ftrl',
                            frame_dec := fdec', trail_end := te', cur_level := cl',
                            unassigned := unass', unflushed := unfl' }
      scratch := sc' }
  c0_hsteps_nogrp
  · exact hQ 0#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext m1
      (FullM6HdrCoreInv.mk_inv hcfg hext hinv1) hpres1 (Or.inl rfl)
      (fun _ => h0 hc) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm1)
  · have hr1 : r = 1#64 := hdom.resolve_left hc
    fs_call hDrInit
    refine m6HdrDrMutSpec_of hcfg hext hinv1.lengths ((fullM6HdrMem_iff ..).mpr hm1)
      fun ext4 m4 hinit4 hw4 hm4 => ?_
    have hl4 : ext4.length = 288 := hinit4.toOk.len
    let mask56 : BitVec 64 := (1#64 <<< 56) - 1#64
    let st4 := ext4[1]'(by omega)
    let hi4 := st4 &&& ~~~mask56
    let decs4 := st4 &&& mask56
    let ext4' := ext4.set 1 (hi4 ||| (decs4 + 1#64))
    rw [fullM6HdrMem_iff] at hm4
    c0_hsteps
    · refine hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
        ext4' _ (FullM6HdrCoreInv.mk_inv hcfg (hinit4.set_pos _ (by decide)).toOk hinv1)
        hpres1 (Or.inr rfl) (fun h => by cases h)
        (fun _ => ⟨(h1 hr1).1, (h1 hr1).2.1, hinit4.set_pos _ (by decide),
          fun hi => (hw4 hi).trans (M6ExtW2aPres.set_w2b _ (by decide) (by decide))⟩)
        ((fullM6HdrMem_iff ..).mpr ?_)
      simpa [ext4', hi4, decs4, st4, mask56] using (by assumption : _)
    · exact hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
        ext4 m4 (FullM6HdrCoreInv.mk_inv hcfg hinit4.toOk hinv1) hpres1 (Or.inr rfl)
        (fun h => by cases h) (fun _ => ⟨(h1 hr1).1, (h1 hr1).2.1, hinit4, hw4⟩)
        ((fullM6HdrMem_iff ..).mpr hm4)

end HdrDecideProof

end LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
