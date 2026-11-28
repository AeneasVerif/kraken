/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce0
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.CoreLemmas1
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics

/-!
# Kissat 1-UIP Reason-Step & OTFS Semantics (`Proof.Deduce.WpDeduce1`)

Pure semantic transitions for `full_analyze_rsn_m6_hdr` (seed + loop), OTFS pigeonhole
subsumption/entailment (`ant_sz > res_sz`), and conflict-state preservation across OTFS/clear
(`public section`, `0` legacy imports, `0` `import all`, `0` `@[expose]` on theorems/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Pure Arena, Nodup, Witness & Conflict Preservation Helpers -/

theorem ded_arenaVarsNodup_of_pres {s s' : FullState}
    (hnd : FullArenaVarsNodup s)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hpres : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
  obtain ⟨hg, hl⟩ := hpres r hr0
  rw [hl]
  exact hnd r hr0 (by rw [← hg]; exact hng)

theorem ded_arenaVarsNodup_same_core_arena {s s' : FullState}
    (hnd : FullArenaVarsNodup s) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) : FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
    fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits
    fullArenaClauseLitsCore fullArenaClauseSizeCore at hnd ⊢
  rw [har, hal]; exact hnd

theorem ded_otfsInvW_of_cutInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hmc : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hdm : s.core.dense_mode = 0#64) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨hlen, hw.toFullOtfsWitnessInv, hmc, hnd, hext, hdm⟩

theorem ded_cutInvW_of_parts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hmc : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hdm : s.core.dense_mode = 0#64) :
    FullCutInvW c F0 F_cur cut s :=
  ⟨hlen, hw, hmc, hnd, hext, hdm⟩

theorem ded_litMarksClear_of_clear {c : FullCfg} {s s0 : FullState}
    (hm0 : FullLitMarksClear c s0)
    (hmrk : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hlm : s.core.lit_mark = s0.core.lit_mark) : FullLitMarksClear c s :=
  ⟨hmrk, by rw [hlm]; exact hm0.2⟩

theorem ded_extScratchOk_of_pres {c : FullCfg} {s s0 : FullState}
    (h0 : FullExtScratchOk c s0) (hext : FullExtScratchPres s0 s)
    (_hcv : s.core.cur_vars = s0.core.cur_vars)
    (hrefs : fullArenaClauseRefs s = fullArenaClauseRefs s0) :
    FullExtScratchOk c s := by
  refine ⟨fun i hi => ?_, by rw [hext.2]; exact h0.2⟩
  have h := h0.1 i hi
  dsimp only at h ⊢
  unfold fullArenaClauseRefs at hrefs ⊢
  rw [hext.1, hrefs]; exact h

theorem ded_lengthsOk_same_core_res {c : FullCfg} {s s' : FullState} {r : BitVec 64}
    (hlen : s.LengthsOk c) (hc : s'.core = s.core)
    (hsc : s'.scratch = { s.scratch with res_sz := r }) : s'.LengthsOk c := by
  obtain ⟨h1, h2⟩ := hlen
  refine ⟨by rw [hc]; exact h1, ?_⟩
  rw [hsc]; cases h2; constructor <;> assumption

theorem ded_nodup_map_filter {α β : Type} {f : α → β} (p : α → Bool) :
    ∀ {lits : List α}, (lits.map f).Nodup → ((lits.filter p).map f).Nodup
  | [], _ => by simp
  | a :: xs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons]
    by_cases hpa : p a
    · rw [ite_eq_left (by simp [hpa]), List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ded_nodup_map_filter p hnd.2⟩
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
      exact hnd.1 (hfb ▸ List.mem_map_of_mem (List.mem_filter.mp hb).1)
    · rw [ite_eq_right (by simp [hpa])]
      exact ded_nodup_map_filter p hnd.2

theorem ded_nodup_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {lits : List α}, (lits.map f).Nodup → lits.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact List.nodup_cons.mpr
      ⟨fun ha => hnd.1 (List.mem_map_of_mem ha), ded_nodup_of_map_nodup hnd.2⟩

theorem ded_mem_div2_ne_of_map_nodup {lits : List Nat}
    (hnd : (lits.map (· / 2)).Nodup) {a b : Nat}
    (ha : a ∈ lits) (hb : b ∈ lits) (hne : a ≠ b) : a / 2 ≠ b / 2 := by
  induction lits with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | hax <;> rcases List.mem_cons.mp hb with rfl | hbx
    · exact absurd rfl hne
    · intro h; exact hnd.1 (h ▸ List.mem_map_of_mem hbx)
    · intro h; exact hnd.1 (h.symm ▸ List.mem_map_of_mem hax)
    · exact ih hnd.2 hax hbx

private theorem ded_nodup_filter_ne_length (a : Nat) :
    ∀ {l : List Nat}, l.Nodup → a ∈ l →
      l.length = (l.filter fun x => decide (x ≠ a)).length + 1
  | [], _, ha => by simp at ha
  | x :: xs, hnd, ha => by
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa
      have hcongr : xs.filter (fun y => decide (y ≠ x)) = xs := by
        rw [List.filter_eq_self]
        intro y hy
        exact decide_eq_true (fun heq => hnd.1 (heq ▸ hy))
      rw [List.filter_cons, ite_eq_right (by simp), hcongr, List.length_cons]
    · have ha' : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
      have ih := ded_nodup_filter_ne_length a hnd.2 ha'
      rw [List.filter_cons, ite_eq_left (by simp [hxa]), List.length_cons, List.length_cons, ih]

private theorem ded_curTrailIdxs_cut_eq {k : FullCoreState} {mrk : List (BitVec 8)}
    {cut lim : Nat} (hle : cut ≤ lim) (hcm : FullCurMarksBelow lim k mrk cut) :
    fullCurTrailIdxs k mrk lim = fullCurTrailIdxs k mrk cut := by
  induction lim with
  | zero =>
    have : cut = 0 := by omega
    subst this; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · rfl
    · have hnot : ¬ (mrk[(k.trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
          (k.lvl[(k.trl[n]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) :=
        fun ⟨hm, hl⟩ => by have := hcm n (Nat.lt_succ_self n) hm hl; omega
      rw [fullCurTrailIdxs_succ_eq_self hnot]
      exact ih (Nat.le_of_lt_succ hlt) fun j hj hm hl => hcm j (Nat.lt_succ_of_lt hj) hm hl

private theorem ded_activeResolvent_mem_of_pos_lvl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut lim : Nat} {s : FullState} {l : Nat}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hlow : FullLowerInv c s.core s.core.tmp s.core.mrk s.core.tmp_len)
    (hmcov : FullMarksCov s.core s.core.tmp s.core.mrk s.core.tmp_len)
    (htl_len : s.core.tmp_len ≤ s.core.tmp.length)
    (hl_lt : l < 2 * s.core.cur_vars)
    (hf : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (_hpos : 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat)
    (hm_nz : s.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (htr : (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < lim, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1) :
    l ∈ fullActiveResolvent s.core s.core.tmp s.core.mrk s.core.tmp_len lim := by
  unfold fullActiveResolvent; rw [List.mem_append]
  have hcov := hmcov (l / 2) (by omega) hm_nz
  rcases Nat.lt_or_eq_of_le hcov.2.1 with hlt_lv | heq_lv
  · right
    obtain ⟨j, hj1, hj2, hjeq⟩ := hcov.2.2 hlt_lv
    refine (fullLowerLits_mem_iff htl_len).mpr ⟨j, hj1, hj2, ?_⟩
    have hlj := hlow.1 j hj1 hj2
    exact ded_lit_eq_of_div2_eq_falsified hw.toFullOtfsWitnessInv hlj.1 hl_lt hlj.2.1 hf hjeq
  · left
    obtain ⟨m, hm_lim, hmeq⟩ := htr heq_lv
    unfold fullCurLits; rw [List.mem_map]
    refine ⟨m, fullCurTrailIdxs_mem_iff.mpr ⟨hm_lim, ?_, ?_⟩, ?_⟩
    · rwa [hmeq, ded_lit_xor1_div2]
    · rwa [hmeq, ded_lit_xor1_div2]
    · rw [hmeq, ded_lit_xor1_xor1]

/-! ## 2. Seed-Reason Semantic Transition (`deduce_seed_rsn_sem`) -/

theorem deduce_seed_rsn_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s sl s2 : FullState} {mrk' : List (BitVec 8)} {tmp' mclr' : List (BitVec 32)}
    {tc' tl' mcl' : Nat} {arena' : List (BitVec 32)} {sc' : FullScratch}
    (hs_cut : FullCutInvW c F0 F_cur cut s)
    (hconfl : FullConflictOkCut F_cur cut s)
    (hsl_c : sl.core = { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 })
    (hsl_sc : sl.scratch = { s.scratch with ant_sz := 0#64, res_sz := 0#64 })
    (hlen_l : sl.LengthsOk c)
    (hs2_eq : s2 =
      { sl with
        core := { sl.core with mrk := mrk', tmp := tmp', min_clr := mclr',
                               tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hcov2 : FullAnaMarksCov c s2) (hext2 : FullExtScratchPres sl s2)
    (hws2_2 : sc'.work_stk2 = sl.scratch.work_stk2)
    (htl2_ge : 1 ≤ tl') (htl2_cv : tl' ≤ sl.core.cur_vars)
    (htc2_ge : 0 ≤ tc') (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs sl)
    (hcl2 : ∀ r ∈ fullArenaClauseRefs sl, fullArenaClauseSize s2 r = fullArenaClauseSize sl r ∧
      fullArenaClauseGarb s2 r = fullArenaClauseGarb sl r ∧
      fullArenaClauseLits s2 r = fullArenaClauseLits sl r)
    (hmp : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      mrk'[v]?.getD 0#8 = sl.core.mrk[v]?.getD 0#8)
    (htp : ∀ k < 1, tmp'[k]? = sl.core.tmp[k]?)
    (hnm : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32),
        l / 2 = v ∧ v < sl.core.cur_vars ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (sl.core.lvl[v]?.getD 0#32).toNat ∧
        (sl.core.lvl[v]?.getD 0#32).toNat ≤ sl.core.cur_level)
    (hnt : ∀ j, 1 ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32) ∧ l < 2 * sl.core.cur_vars ∧
      l / 2 ≠ (0xFFFFFFFF#32).toNat ∧ sl.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
      0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_j : ∀ j1 j2, 1 ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hcnt : tc' - 0 = ((List.range sl.core.cur_vars).filter fun w =>
      decide (sl.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((sl.core.lvl[w]?.getD 0#32).toNat = sl.core.cur_level)).length)
    (hres2 : sc'.res_sz = sl.scratch.res_sz + BitVec.ofNat 64 ((List.range sl.core.cur_vars).filter
      fun w => decide (sl.core.mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)
    (hok_lits : ∀ l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32),
      l / 2 < sl.core.cur_vars ∧ (l / 2 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
          (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level ∧
          (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat →
            (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level →
            ∃ j, 1 ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hnbin : sl.core.confl_type ≠ 1#64) :
    FullDeduceStateInv c F0 F_cur cut s2.core.trail_end s s2 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hs_cut.1.core_ok.cur_vars_le
  have hstat_sl : FullDeduceStaticEq s.core sl.core := by
    rw [hsl_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hext_sl : FullExtScratchPres s sl := by
    unfold FullExtScratchPres; rw [hsl_sc]; exact ⟨rfl, rfl⟩
  have hws2_sl : sl.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hsl_sc]
  have hrefs_sl : fullArenaClauseRefs sl = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hsl_c]
  have hw_sl : FullWitnessCutInv c F0 F_cur cut sl.core := by
    rw [hsl_c]; exact deduce_same_core_cut hs_cut.2.1 _ _ _ _ _
  have hmrk_sl : sl.core.mrk = s.core.mrk := by rw [hsl_c]
  have htl_sl : sl.core.tmp_len = 1 := by rw [hsl_c]
  have htc_sl : sl.core.tmp_cnt = 0 := by rw [hsl_c]
  have hres_sl : sl.scratch.res_sz = 0#64 := by rw [hsl_sc]
  have hnbin_s : s.core.confl_type ≠ 1#64 := by rwa [hsl_c] at hnbin
  have hconfl_sl : FullConflictOkCut F_cur cut sl := by
    obtain ⟨h1 | h2, htail⟩ := hconfl
    · exact absurd h1.1 hnbin_s
    · have hok2 : sl.core.confl_type = 2#64 ∧
          sl.core.confl_ref.toNat ∈ fullArenaClauseRefs sl ∧
          fullArenaClauseGarb sl sl.core.confl_ref.toNat = false ∧
          (∀ l ∈ fullArenaClauseLits sl sl.core.confl_ref.toNat,
            sl.core.vals[l]?.getD 0#8 = 0xFF#8) := by
        unfold fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
          fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits fullArenaClauseLitsCore
          fullArenaClauseSizeCore at h2 ⊢
        rw [hsl_c]; exact h2
      refine ⟨Or.inr hok2, ?_⟩
      rw [ite_eq_right (by rw [hsl_c]; exact hnbin_s)]
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore at htail ⊢
      rw [ite_eq_right (by rw [h2.1]; decide)] at htail
      rw [hsl_c]; exact htail
  obtain ⟨_, _, _, _, _, hrsn_ref, hlits_eq⟩ := deduce_seed_rsn_pre hlen_l hw_sl hconfl_sl hnbin
  have hrsn_garb : fullArenaClauseGarb sl sl.core.confl_ref.toNat = false := by
    rcases hconfl_sl.1 with h1 | h2
    · exact absurd h1.1 hnbin
    · exact h2.2.2.1
  have hrsn_fals : ∀ l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32),
      l / 2 ≠ (0xFFFFFFFF#32).toNat → sl.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    intro l hl _
    rw [hlits_eq] at hl
    rcases hconfl_sl.1 with h1 | h2
    · exact absurd h1.1 hnbin
    · exact h2.2.2.2 l hl
  have hcur_tr : ∀ l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32),
      l / 2 ≠ (0xFFFFFFFF#32).toNat → sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
      (sl.core.lvl[l / 2]?.getD 0#32).toNat = sl.core.cur_level →
      ∃ m < cut, (sl.core.trl[m]?.getD 0#32).toNat / 2 = l / 2 := by
    intro l hl _ _ hlev
    rw [hlits_eq] at hl
    have hc2 := hconfl_sl.2
    rw [ite_eq_right hnbin] at hc2
    obtain ⟨m, hm, hmeq⟩ := hc2 l hl hlev
    exact ⟨m, hm, by rw [hmeq, ded_lit_xor1_div2]⟩
  have hnd_sl : FullArenaVarsNodup sl :=
    ded_arenaVarsNodup_same_core_arena hs_cut.2.2.2.1 (by rw [hsl_c]) (by rw [hsl_c])
  have hnd2 : FullArenaVarsNodup s2 :=
    ded_arenaVarsNodup_of_pres hnd_sl hrefs2 (fun r hr => (hcl2 r hr).2)
  have htc_eq_sl : sl.core.tmp_cnt = (fullCurTrailIdxs sl.core sl.core.mrk cut).length := by
    rw [htc_sl]; symm; apply List.eq_nil_iff_length_eq_zero.mp
    unfold fullCurTrailIdxs
    rw [List.filter_eq_nil_iff]
    intro j hj
    simp only [decide_eq_true_iff, not_and]
    intro hm
    have hv := hw_sl.trail_lits_lt j (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hw_sl.cut_le)
    have hcv_sl : sl.core.cur_vars ≤ c.max_vars := hlen_l.core_ok.cur_vars_le
    have hmz := hs_cut.2.2.1.1 ((sl.core.trl[j]?.getD 0#32).toNat / 2) (by omega)
    rw [← hmrk_sl] at hmz
    exact absurd hmz hm
  have hlow_sl : FullLowerInv c sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len := by
    rw [htl_sl]; exact ⟨fun j hj1 hj2 => by omega, fun j1 j2 hj1 hj12 hj2 => by omega⟩
  have hmcov_sl : FullMarksCov sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len := by
    intro v hv hnz
    have hmz := hs_cut.2.2.1.1 v (by rw [hstat_sl.cv] at hv; omega)
    rw [← hmrk_sl] at hmz
    exact absurd hmz hnz
  have hcm_sl : FullCurMarksBelow cut sl.core sl.core.mrk cut := by
    intro j hj hnz
    have hv := hw_sl.trail_lits_lt j (Nat.lt_of_lt_of_le hj hw_sl.cut_le)
    have hcv_sl : sl.core.cur_vars ≤ c.max_vars := hlen_l.core_ok.cur_vars_le
    have hmz := hs_cut.2.2.1.1 ((sl.core.trl[j]?.getD 0#32).toNat / 2) (by omega)
    rw [← hmrk_sl] at hmz
    exact absurd hmz hnz
  have hs2_cv : s2.core.cur_vars = sl.core.cur_vars := by rw [hs2_eq]
  have hs2_cl : s2.core.cur_level = sl.core.cur_level := by rw [hs2_eq]
  have hs2_te : s2.core.trail_end = sl.core.trail_end := by rw [hs2_eq]
  have hs2_trl : s2.core.trl = sl.core.trl := by rw [hs2_eq]
  have hs2_lvl : s2.core.lvl = sl.core.lvl := by rw [hs2_eq]
  have hs2_rs : s2.core.rsns = sl.core.rsns := by rw [hs2_eq]
  have hs2_vals : s2.core.vals = sl.core.vals := by rw [hs2_eq]
  have hs2_fu : s2.core.fuel = sl.core.fuel := by rw [hs2_eq]
  have hs2_dm : s2.core.dense_mode = sl.core.dense_mode := by rw [hs2_eq]
  have hs2_lm : s2.core.lit_mark = sl.core.lit_mark := by rw [hs2_eq]
  have hs2_m : s2.core.mrk = mrk' := by rw [hs2_eq]
  have hs2_tmp : s2.core.tmp = tmp' := by rw [hs2_eq]
  have hs2_tc : s2.core.tmp_cnt = tc' := by rw [hs2_eq]
  have hs2_tl : s2.core.tmp_len = tl' := by rw [hs2_eq]
  have hs2_res : s2.scratch.res_sz = sc'.res_sz := by rw [hs2_eq]
  have hs2_ws2 : s2.scratch.work_stk2 = sl.scratch.work_stk2 := by rw [hs2_eq]; exact hws2_2
  obtain ⟨hlen2', hw2', hcov2', hext2', hws2', hnd2', hrefs2', hstat2', htl2_ge1', htl2_cv',
      htc2_eq', hlow2', hmcov2', hcm2', hres2', hall_mrk⟩ :=
    ded_rsn_inv_step (extra := 0) hlen_l hw_sl hstat_sl (by rw [htl_sl]; exact le_refl 1)
      (by rw [htl_sl]; exact Nat.le_trans htl2_ge htl2_cv)
      htc_eq_sl hw_sl.cut_le (le_refl cut) hlow_sl hmcov_sl hcm_sl
      (by rw [hres_sl, htl_sl, htc_sl])
      ⟨hs2_cv, hs2_cl, hs2_te, hs2_trl, hs2_lvl, hs2_rs, hs2_vals, hs2_fu, hs2_dm, hs2_lm⟩
      hlen2 hw2 hcov2 hext2 hs2_ws2
      (by rw [hs2_tl, htl_sl]; exact htl2_ge) (by rw [hs2_tl]; exact htl2_cv)
      (by rw [hs2_tc, htc_sl]; exact htc2_ge) hrefs2 hnd2
      (by rw [hs2_m]; exact hmp) (by rw [htl_sl, hs2_tmp]; exact htp)
      (by rw [hs2_m]; exact hnm) (by rw [htl_sl, hs2_tl, hs2_tmp, hs2_m]; exact hnt)
      (by rw [htl_sl, hs2_tl, hs2_tmp]; exact hnd_j)
      (by rw [hs2_tc, htc_sl, hs2_m]; exact hcnt)
      (by rw [hs2_res, hs2_m]; exact hres2)
      (by rw [hs2_m, htl_sl, hs2_tl, hs2_tmp]; exact hok_lits)
      hrsn_fals hcur_tr hext_sl hws2_sl hrefs_sl
  have hres_s2 := ded_rsn_lit_resolved_or_falsified hw2' hlow2' hmcov2'
    (by rw [hlen2'.core_ok.tmp_len_arr]
        exact Nat.le_trans htl2_cv' (by rw [hstat2'.cv]; exact hcv_le))
    (fun l hl => by rw [hs2_cv]; exact (hok_lits l hl).1)
    (fun l hl hne => by
      refine ⟨by rw [hs2_vals]; exact hrsn_fals l hl hne, fun hlv => ?_⟩
      rw [hs2_lvl, hs2_cl] at hlv
      have hc2 := hconfl_sl.2; rw [ite_eq_right hnbin] at hc2
      rw [hlits_eq] at hl
      obtain ⟨m, hm_cut, hmeq⟩ := hc2 l hl hlv
      exact ⟨m, hm_cut, by rw [hs2_trl]; exact hmeq⟩)
    hall_mrk hw2'.cut_le
  have hent_cut : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len cut)) := by
    have htr_ref : (sl.core.confl_ref.truncate 32).toNat = sl.core.confl_ref.toNat := by assumption
    have hrsn_ref' : sl.core.confl_ref.toNat ∈ fullArenaClauseRefsCore sl.core := by
      rw [← htr_ref]; exact hrsn_ref
    refine ded_clause_entails_strip
      (hw_sl.arena.entails sl.core.confl_ref.toNat hrsn_ref' hrsn_garb) (fun l hl => ?_)
    · change l ∈ fullArenaClauseLits sl sl.core.confl_ref.toNat at hl
      have hl' : l ∈ fullRsnLits sl (sl.core.confl_ref.truncate 32) := by rwa [hlits_eq]
      have hdiv_lt : l / 2 < s.core.cur_vars := hstat_sl.cv ▸ (hok_lits l hl').1
      have hne : l / 2 ≠ (0xFFFFFFFF#32).toNat := by
        intro heq
        have hv : (0xFFFFFFFF#32).toNat = 4294967295 := rfl
        omega
      exact hres_s2 l hl' hne
  have hcm2_te : FullCurMarksBelow s2.core.trail_end s2.core s2.core.mrk cut := by
    intro j hj hnz hlev
    have hv := hw2'.trail_lits_lt j hj
    have hcv2 : s2.core.cur_vars ≤ c.max_vars := hlen2'.core_ok.cur_vars_le
    have hm0 : sl.core.mrk[(s2.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
      rw [hmrk_sl]; exact hs_cut.2.2.1.1 _ (by omega)
    have hnz' : mrk'[(s2.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
      rwa [← hs2_m]
    obtain ⟨l, hl, hlv, _, hne, _, _⟩ := hnm _ (by omega) hm0 hnz'
    have hlev' : (sl.core.lvl[l / 2]?.getD 0#32).toNat = sl.core.cur_level := by
      rw [hlv, ← hs2_lvl, ← hs2_cl]; exact hlev
    obtain ⟨m, hm, hmeq⟩ := hcur_tr l hl (by rwa [hlv]) (by rwa [hlv]) hlev'
    have hmj := hw_sl.trail_vars_nodup m j (Nat.lt_of_lt_of_le hm hw_sl.cut_le)
      (by rwa [← hs2_te]) (by rw [hmeq, hlv, hs2_trl])
    omega
  have hcur_eq : fullCurTrailIdxs s2.core s2.core.mrk s2.core.trail_end =
      fullCurTrailIdxs s2.core s2.core.mrk cut :=
    ded_curTrailIdxs_cut_eq hw2'.cut_le hcm2_te
  have hent_te : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s2.core s2.core.tmp s2.core.mrk
        s2.core.tmp_len s2.core.trail_end)) := by
    unfold fullActiveResolvent fullCurLits at hent_cut ⊢
    rw [hcur_eq]; exact hent_cut
  exact ⟨hlen2', hw2', hcov2', hext2', hws2', hnd2', hrefs2', hstat2',
    htl2_ge1', htl2_cv', by rw [hcur_eq]; exact htc2_eq', hlow2', hmcov2', hcm2_te,
    hent_te, by rw [hres2', Nat.add_zero]⟩

/-! ## 3. Loop-Reason Semantic Transition (`deduce_loop_rsn_sem`) -/

private theorem ded_rsn_ant_sz_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {sl s2 : FullState} {rsn p_bv : BitVec 32} {sc' : FullScratch}
    (hlen_l : sl.LengthsOk c) (hw_l : FullWitnessCutInv c F0 F_cur cut sl.core)
    (hnd_l : FullArenaVarsNodup sl) (hidx_cut : idx' < cut)
    (hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hrsn_get : sl.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hant_l : sl.scratch.ant_sz = 0#64) (hs2_lvl : s2.core.lvl = sl.core.lvl)
    (hs2_refs : fullArenaClauseRefs s2 = fullArenaClauseRefs sl)
    (hs2_cl : ∀ r ∈ fullArenaClauseRefs sl, fullArenaClauseSize s2 r = fullArenaClauseSize sl r ∧
      fullArenaClauseGarb s2 r = fullArenaClauseGarb sl r ∧
      fullArenaClauseLits s2 r = fullArenaClauseLits sl r)
    (hs2_sc : s2.scratch = sc') (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hnb : rsn &&& 0x80000000#32 = 0#32)
    (hant_spec : sc'.ant_sz = sl.scratch.ant_sz + BitVec.ofNat 64
      ((fullRsnLits sl rsn).countP fun l =>
        decide (l / 2 < sl.core.cur_vars ∧ 0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level))) :
    rsn.toNat ∈ fullArenaClauseRefs s2 ∧ fullArenaClauseGarb s2 rsn.toNat = false ∧
      s2.scratch.ant_sz.toNat = ((fullArenaClauseLits s2 rsn.toNat).filter fun l =>
        decide (0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat)).length := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen_l.core_ok.cur_vars_le
  have hinv := hw_l.reason_inv_cut idx' hidx_cut (by rw [hp_get, hrsn_get]; exact hrsn_ne)
  rw [hp_get, hrsn_get, ite_eq_right (fun h => h hnb)] at hinv
  have hrsn_ref : rsn.toNat ∈ fullArenaClauseRefs sl := hinv.1
  have hrsn_garb : fullArenaClauseGarb sl rsn.toNat = false := hinv.2.1
  have hlits_eq : fullRsnLits sl rsn = fullArenaClauseLits sl rsn.toNat := by
    unfold fullRsnLits; rw [ite_eq_right hrsn_ne, ite_eq_right (fun h => h hnb)]
  have hcl_eq := hs2_cl rsn.toNat hrsn_ref
  refine ⟨by rw [hs2_refs]; exact hrsn_ref, by rw [hcl_eq.2.1]; exact hrsn_garb, ?_⟩
  have hfilt : (fullRsnLits sl rsn).filter (fun l =>
      decide (l / 2 < sl.core.cur_vars ∧ 0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level)) =
      (fullArenaClauseLits s2 rsn.toNat).filter
        (fun l => decide (0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat)) := by
    rw [hlits_eq, hcl_eq.2.2, hs2_lvl]
    apply List.filter_congr; intro l hl
    have hl_lt : l < 2 * sl.core.cur_vars :=
      hw_l.arena.lits_lt rsn.toNat hrsn_ref hrsn_garb l hl
    have hl_le : (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level := by
      rcases hinv.2.2 l hl with rfl | ⟨m, hm_lt, hm_eq, _⟩
      · have hle := hw_l.lvl_le idx' (Nat.lt_of_lt_of_le hidx_cut hw_l.cut_le)
        rwa [hp_get] at hle
      · have hle := hw_l.lvl_le m (Nat.lt_trans hm_lt (Nat.lt_of_lt_of_le hidx_cut hw_l.cut_le))
        rwa [hm_eq, ded_lit_xor1_div2] at hle
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨fun h => h.2.1, fun h => ⟨by omega, h, hl_le⟩⟩
  have hnd_vars := hnd_l rsn.toNat hrsn_ref hrsn_garb
  have hlen_sub : ((fullArenaClauseLits s2 rsn.toNat).filter fun l =>
      decide (0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat)).length ≤ sl.core.cur_vars := by
    have hsub : ((fullArenaClauseLits s2 rsn.toNat).filter fun l =>
        decide (0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat)).map (· / 2) ⊆
        List.range sl.core.cur_vars := by
      intro v hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      rw [List.mem_filter, hcl_eq.2.2] at hl
      have hlt := hw_l.arena.lits_lt rsn.toNat hrsn_ref hrsn_garb l hl.1
      rw [List.mem_range]; omega
    have hnd_f : (((fullArenaClauseLits s2 rsn.toNat).filter fun l =>
        decide (0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat)).map (· / 2)).Nodup := by
      rw [hcl_eq.2.2]; exact ded_nodup_map_filter _ hnd_vars
    have hle := List.Nodup.length_le_of_subset hnd_f hsub
    rwa [List.length_map, List.length_range] at hle
  rw [hs2_sc, hant_spec, hant_l, BitVec.zero_add, List.countP_eq_length_filter, hfilt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem deduce_loop_rsn_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s s1 sl s2 s3 : FullState} {rsn p_bv : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp' mclr' : List (BitVec 32)} {tc' tl' mcl' : Nat}
    {arena' : List (BitVec 32)} {sc' : FullScratch}
    (hs1 : FullDeduceStateInv c F0 F_cur cut (idx' + 1) s s1)
    (hidx_te : idx' < s1.core.trail_end)
    (hp_get : (s1.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hm_p : s1.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl_p : (s1.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s1.core.cur_level)
    (hrsn_get : s1.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hsl_c : sl.core = { s1.core with tmp_cnt := s1.core.tmp_cnt - 1 })
    (hsl_sc : sl.scratch = { s1.scratch with ant_sz := 0#64 })
    (hlen_l : sl.LengthsOk c)
    (hs2_eq : s2 =
      { sl with
        core := { sl.core with mrk := mrk', tmp := tmp', min_clr := mclr',
                               tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hcov2 : FullAnaMarksCov c s2) (hext2 : FullExtScratchPres sl s2)
    (hws2_2 : sc'.work_stk2 = sl.scratch.work_stk2)
    (htl2_ge : sl.core.tmp_len ≤ tl') (htl2_cv : tl' ≤ sl.core.cur_vars)
    (htc2_ge : sl.core.tmp_cnt ≤ tc') (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs sl)
    (hcl2 : ∀ r ∈ fullArenaClauseRefs sl, fullArenaClauseSize s2 r = fullArenaClauseSize sl r ∧
      fullArenaClauseGarb s2 r = fullArenaClauseGarb sl r ∧
      fullArenaClauseLits s2 r = fullArenaClauseLits sl r)
    (hmp : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      mrk'[v]?.getD 0#8 = sl.core.mrk[v]?.getD 0#8)
    (htp : ∀ k < sl.core.tmp_len, tmp'[k]? = sl.core.tmp[k]?)
    (hnm : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ fullRsnLits sl rsn, l / 2 = v ∧ v < sl.core.cur_vars ∧ v ≠ p_bv.toNat / 2 ∧
        0 < (sl.core.lvl[v]?.getD 0#32).toNat ∧
        (sl.core.lvl[v]?.getD 0#32).toNat ≤ sl.core.cur_level)
    (hnt : ∀ j, sl.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ fullRsnLits sl rsn ∧ l < 2 * sl.core.cur_vars ∧ l / 2 ≠ p_bv.toNat / 2 ∧
      sl.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_j : ∀ j1 j2, sl.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hcnt : tc' - sl.core.tmp_cnt = ((List.range sl.core.cur_vars).filter fun w =>
      decide (sl.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((sl.core.lvl[w]?.getD 0#32).toNat = sl.core.cur_level)).length)
    (hres2 : sc'.res_sz = sl.scratch.res_sz + BitVec.ofNat 64 ((List.range sl.core.cur_vars).filter
      fun w => decide (sl.core.mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hant_spec : sc'.ant_sz = sl.scratch.ant_sz + BitVec.ofNat 64
      ((fullRsnLits sl rsn).countP fun l =>
        decide (l / 2 < sl.core.cur_vars ∧ 0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level)))
    (hok_lits : ∀ l ∈ fullRsnLits sl rsn, l / 2 < sl.core.cur_vars ∧ (l / 2 ≠ p_bv.toNat / 2 →
      (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
      (sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
        (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level ∧
        (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat →
          (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level →
          ∃ j, sl.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hs3_eq : s3 = { s2 with scratch := { s2.scratch with res_sz := s2.scratch.res_sz - 1#64 } }) :
    idx' < cut ∧ 0#64 < s2.scratch.res_sz ∧ FullDeduceStateInv c F0 F_cur cut idx' s s3 ∧
      (rsn &&& 0x80000000#32 = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s3 ∧
        fullArenaClauseGarb s3 rsn.toNat = false ∧
        s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 rsn.toNat).filter fun l =>
          decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length) ∧
      (∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ p_bv.toNat / 2 →
        0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8) := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hs1.len.core_ok.cur_vars_le
  have hidx_cut : idx' < cut :=
    hs1.cmcut idx' (Nat.lt_succ_self idx') (by rw [hp_get]; exact hm_p)
      (by rw [hp_get]; exact hl_p)
  have hsucc_eq : fullCurTrailIdxs s1.core s1.core.mrk (idx' + 1) =
      fullCurTrailIdxs s1.core s1.core.mrk idx' ++ [idx'] :=
    fullCurTrailIdxs_succ_true (by rw [hp_get]; exact hm_p) (by rw [hp_get]; exact hl_p)
  have htc1_eq : s1.core.tmp_cnt = (fullCurTrailIdxs s1.core s1.core.mrk idx').length + 1 := by
    rw [hs1.tc_eq, hsucc_eq, List.length_append, List.length_singleton]
  have hstat_sl : FullDeduceStaticEq s.core sl.core :=
    hs1.stat.trans (by rw [hsl_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hext_sl : FullExtScratchPres s sl :=
    fullExtScratchPres_trans hs1.ext (by unfold FullExtScratchPres; rw [hsl_sc]; exact ⟨rfl, rfl⟩)
  have hws2_sl : sl.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hsl_sc]; exact hs1.ws2
  have hrefs_sl : fullArenaClauseRefs sl = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore
    rw [hsl_c]; exact hs1.hrefs
  have hw_sl : FullWitnessCutInv c F0 F_cur cut sl.core := by
    rw [hsl_c]; exact deduce_same_core_cut hs1.hw _ _ _ _ _
  have hnd_sl : FullArenaVarsNodup sl :=
    ded_arenaVarsNodup_same_core_arena hs1.nd (by rw [hsl_c]) (by rw [hsl_c])
  have hnd2 : FullArenaVarsNodup s2 :=
    ded_arenaVarsNodup_of_pres hnd_sl hrefs2 (fun r hr => (hcl2 r hr).2)
  have htl_sl : sl.core.tmp_len = s1.core.tmp_len := by rw [hsl_c]
  have htc_sl : sl.core.tmp_cnt = s1.core.tmp_cnt - 1 := by rw [hsl_c]
  have hte_sl : sl.core.trail_end = s1.core.trail_end := by rw [hsl_c]
  have hmrk_sl : sl.core.mrk = s1.core.mrk := by rw [hsl_c]
  have htmp_sl : sl.core.tmp = s1.core.tmp := by rw [hsl_c]
  have htrl_sl : sl.core.trl = s1.core.trl := by rw [hsl_c]
  have hlvl_sl : sl.core.lvl = s1.core.lvl := by rw [hsl_c]
  have hcl_sl : sl.core.cur_level = s1.core.cur_level := by rw [hsl_c]
  have hcv_sl : sl.core.cur_vars = s1.core.cur_vars := by rw [hsl_c]
  have hrs_sl : sl.core.rsns = s1.core.rsns := by rw [hsl_c]
  have htc_eq_sl : sl.core.tmp_cnt = (fullCurTrailIdxs sl.core sl.core.mrk idx').length := by
    rw [htc_sl, htc1_eq]
    unfold fullCurTrailIdxs
    rw [htrl_sl, hmrk_sl, hlvl_sl, hcl_sl]; omega
  have hlow_sl : FullLowerInv c sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len := by
    have hl1 := hs1.low; unfold FullLowerInv at hl1 ⊢
    rw [hsl_c]; exact hl1
  have hmcov_sl : FullMarksCov sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len := by
    have hm1 := hs1.mcov; unfold FullMarksCov at hm1 ⊢
    rw [hsl_c]; exact hm1
  have hcm_sl : FullCurMarksBelow idx' sl.core sl.core.mrk cut := by
    intro j hj hm hl
    have hc1 := hs1.cmcut j (Nat.lt_succ_of_lt hj)
    rw [← htrl_sl, ← hmrk_sl, ← hlvl_sl, ← hcl_sl] at hc1
    exact hc1 hm hl
  have hres_sl : sl.scratch.res_sz =
      BitVec.ofNat 64 ((sl.core.tmp_len - 1) + sl.core.tmp_cnt + 1) := by
    rw [hsl_sc, hs1.res_eq, htl_sl, htc_sl]; congr 1; omega
  have hinv_idx := hw_sl.reason_inv_cut idx' hidx_cut
    (by rw [htrl_sl, hp_get, hrs_sl, hrsn_get]; exact hrsn_ne)
  have hcur_tr_ex : ∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ p_bv.toNat / 2 →
      ∃ m < idx', (sl.core.trl[m]?.getD 0#32).toNat = l ^^^ 1 := by
    intro l hl hne
    by_cases hnb : rsn &&& 0x80000000#32 = 0#32
    · rw [htrl_sl, hp_get, hrs_sl, hrsn_get, ite_eq_right (fun h => h hnb)] at hinv_idx
      unfold fullRsnLits at hl
      rw [ite_eq_right hrsn_ne, ite_eq_right (fun h => h hnb)] at hl
      rcases hinv_idx.2.2 l hl with hpeq | ⟨m, hm, hmeq, _⟩
      · exact absurd (by rw [hpeq]) hne
      · exact ⟨m, hm, by rw [htrl_sl]; exact hmeq⟩
    · rw [htrl_sl, hp_get, hrs_sl, hrsn_get, ite_eq_left hnb] at hinv_idx
      unfold fullRsnLits at hl
      rw [ite_eq_right hrsn_ne, ite_eq_left hnb, List.mem_singleton] at hl
      subst hl; obtain ⟨m, hm, hmeq, _⟩ := hinv_idx.2.2
      exact ⟨m, hm, by rw [htrl_sl]; exact hmeq⟩
  have hrsn_fals : ∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ p_bv.toNat / 2 →
      sl.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    intro l hl hne
    obtain ⟨m, hm, hmeq⟩ := hcur_tr_ex l hl hne
    have hlt_l : l < 2 * sl.core.cur_vars := by have := (hok_lits l hl).1; omega
    exact (hw_sl.vals_false_iff l hlt_l).mpr
      ⟨m, Nat.lt_trans hm (by rw [hte_sl]; exact hidx_te), hmeq⟩
  have hcur_tr : ∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ p_bv.toNat / 2 →
      sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
      (sl.core.lvl[l / 2]?.getD 0#32).toNat = sl.core.cur_level →
      ∃ m < idx', (sl.core.trl[m]?.getD 0#32).toNat / 2 = l / 2 := by
    intro l hl hne _ _
    obtain ⟨m, hm, hmeq⟩ := hcur_tr_ex l hl hne
    exact ⟨m, hm, by rw [hmeq, ded_lit_xor1_div2]⟩
  have hs2_cv : s2.core.cur_vars = sl.core.cur_vars := by rw [hs2_eq]
  have hs2_cl : s2.core.cur_level = sl.core.cur_level := by rw [hs2_eq]
  have hs2_te : s2.core.trail_end = sl.core.trail_end := by rw [hs2_eq]
  have hs2_trl : s2.core.trl = sl.core.trl := by rw [hs2_eq]
  have hs2_lvl : s2.core.lvl = sl.core.lvl := by rw [hs2_eq]
  have hs2_rs : s2.core.rsns = sl.core.rsns := by rw [hs2_eq]
  have hs2_vals : s2.core.vals = sl.core.vals := by rw [hs2_eq]
  have hs2_fu : s2.core.fuel = sl.core.fuel := by rw [hs2_eq]
  have hs2_dm : s2.core.dense_mode = sl.core.dense_mode := by rw [hs2_eq]
  have hs2_lm : s2.core.lit_mark = sl.core.lit_mark := by rw [hs2_eq]
  have hs2_m : s2.core.mrk = mrk' := by rw [hs2_eq]
  have hs2_tmp : s2.core.tmp = tmp' := by rw [hs2_eq]
  have hs2_tc : s2.core.tmp_cnt = tc' := by rw [hs2_eq]
  have hs2_tl : s2.core.tmp_len = tl' := by rw [hs2_eq]
  have hs2_res : s2.scratch.res_sz = sc'.res_sz := by rw [hs2_eq]
  have hs2_ws2 : s2.scratch.work_stk2 = sl.scratch.work_stk2 := by rw [hs2_eq]; exact hws2_2
  have hsk : (p_bv >>> 1#32).toNat = p_bv.toNat / 2 := bv32_shr1_toNat p_bv
  obtain ⟨hlen2', hw2', hcov2', hext2', hws2', hnd2', hrefs2', hstat2', htl2_ge1', htl2_cv',
      htc2_eq', hlow2', hmcov2', hcm2', hres2', hall_mrk⟩ :=
    ded_rsn_inv_step (extra := 1) (skip_var := p_bv >>> 1#32)
      hlen_l hw_sl hstat_sl (by rw [htl_sl]; exact hs1.tl_ge)
      (by rw [htl_sl, hcv_sl]; exact hs1.tl_cv) htc_eq_sl
      (by rw [hte_sl]; exact Nat.le_of_lt hidx_te) (Nat.le_of_lt hidx_cut) hlow_sl hmcov_sl
      hcm_sl hres_sl
      ⟨hs2_cv, hs2_cl, hs2_te, hs2_trl, hs2_lvl, hs2_rs, hs2_vals, hs2_fu, hs2_dm, hs2_lm⟩
      hlen2 hw2 hcov2 hext2 hs2_ws2
      (by rw [hs2_tl]; exact htl2_ge) (by rw [hs2_tl]; exact htl2_cv)
      (by rw [hs2_tc]; exact htc2_ge) hrefs2 hnd2
      (by rw [hs2_m]; exact hmp) (by rw [hs2_tmp]; exact htp)
      (by rw [hs2_m, hsk]; exact hnm) (by rw [hs2_tl, hs2_tmp, hs2_m, hsk]; exact hnt)
      (by rw [hs2_tl, hs2_tmp]; exact hnd_j)
      (by rw [hs2_tc, hs2_m]; exact hcnt)
      (by rw [hs2_res, hs2_m]; exact hres2)
      (by rw [hs2_m, hs2_tl, hs2_tmp, hsk]; exact hok_lits)
      (by rw [hsk]; exact hrsn_fals) (by rw [hsk]; exact hcur_tr)
      hext_sl hws2_sl hrefs_sl
  have hres_s2 := ded_rsn_lit_resolved_or_falsified (lim := idx') (skip_var := p_bv >>> 1#32)
    hw2' hlow2' hmcov2'
    (by rw [hlen2'.core_ok.tmp_len_arr]
        exact Nat.le_trans htl2_cv' (by rw [hs2_cv, hcv_sl]; exact hcv_le))
    (fun l hl => by rw [hs2_cv]; exact (hok_lits l hl).1)
    (fun l hl hne => by
      rw [hsk] at hne
      refine ⟨by rw [hs2_vals]; exact hrsn_fals l hl hne, fun _ => ?_⟩
      obtain ⟨m, hm, hmeq⟩ := hcur_tr_ex l hl hne
      exact ⟨m, hm, by rw [hs2_trl]; exact hmeq⟩)
    hall_mrk (by rw [hs2_te, hte_sl]; exact Nat.le_of_lt hidx_te)
  have hs1_to_s2 : ∀ l ∈ fullActiveResolvent s1.core s1.core.tmp s1.core.mrk s1.core.tmp_len
      (idx' + 1), l = p_bv.toNat ^^^ 1 ∨
      l ∈ fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len idx' := by
    intro l hl
    unfold fullActiveResolvent at hl ⊢
    rw [List.mem_append] at hl
    rcases hl with hcur | hlow
    · have hsucc := fullCurLits_succ_true (by rw [hp_get]; exact hm_p)
        (by rw [hp_get]; exact hl_p)
      rw [hsucc, hp_get, List.mem_append, List.mem_singleton] at hcur
      rcases hcur with hl' | rfl
      · right; rw [List.mem_append]; left
        unfold fullCurLits at hl' ⊢; rw [List.mem_map] at hl' ⊢
        obtain ⟨j, hj, hjeq⟩ := hl'
        obtain ⟨hj_lt, hj_m, hj_l⟩ := fullCurTrailIdxs_mem_iff.mp hj
        have hj_te := Nat.lt_trans hj_lt hidx_te
        have hj_v := hs1.hw.trail_lits_lt j hj_te
        refine ⟨j, fullCurTrailIdxs_mem_iff.mpr ⟨hj_lt, ?_, ?_⟩, ?_⟩
        · have hj_lt_m : (sl.core.trl[j]?.getD 0#32).toNat / 2 < c.max_vars := by
            rw [htrl_sl]; omega
          rw [hs2_m, hs2_trl, hmp _ hj_lt_m (by rw [hmrk_sl, htrl_sl]; exact hj_m),
            hmrk_sl, htrl_sl]
          exact hj_m
        · rw [hs2_lvl, hs2_cl, hs2_trl, hlvl_sl, hcl_sl, htrl_sl]; exact hj_l
        · rw [hs2_trl, htrl_sl]; exact hjeq
      · exact Or.inl rfl
    · right; rw [List.mem_append]; right
      have htl1 := hlen_l.core_ok.tmp_len_le
      rw [htl_sl] at htl1
      have htl1' : s1.core.tmp_len ≤ s1.core.tmp.length := by
        rw [hs1.len.core_ok.tmp_len_arr]; exact htl1
      obtain ⟨j, hj1, hj2, hjeq⟩ := (fullLowerLits_mem_iff htl1').mp hlow
      have htl2' : s2.core.tmp_len ≤ s2.core.tmp.length := by
        rw [hlen2'.core_ok.tmp_len_arr]
        exact Nat.le_trans htl2_cv' (by rw [hs2_cv, hcv_sl]; exact hcv_le)
      refine (fullLowerLits_mem_iff htl2').mpr ⟨j, hj1, Nat.lt_of_lt_of_le hj2
        (by rw [hs2_tl, ← htl_sl]; exact htl2_ge), ?_⟩
      rw [hs2_tmp, htp j (by rw [htl_sl]; exact hj2), htmp_sl, hjeq]
  have hs1_to_s2' : ∀ l ∈ fullActiveResolvent s1.core s1.core.tmp s1.core.mrk s1.core.tmp_len
      (idx' + 1), l = p_bv.toNat ^^^ 1 ∨
      l ∈ fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len idx' ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := fun l hl =>
    match hs1_to_s2 l hl with
    | Or.inl h => Or.inl h
    | Or.inr h => Or.inr (Or.inl h)
  have hent_s2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len idx')) := by
    by_cases hnb : rsn &&& 0x80000000#32 = 0#32
    · rw [htrl_sl, hp_get, hrs_sl, hrsn_get, ite_eq_right (fun h => h hnb)] at hinv_idx
      refine ded_clause_entails_resolve_step (p := p_bv.toNat) hs1.ent
        (hw_sl.arena.entails rsn.toNat hinv_idx.1 hinv_idx.2.1)
        hs1_to_s2' (fun q hq => ?_)
      by_cases hqp : q / 2 = p_bv.toNat / 2
      · rcases hinv_idx.2.2 q hq with hq_eq | ⟨m, hm, hmeq, _⟩
        · exact Or.inl hq_eq
        · have hidx_eq := hw_sl.trail_vars_nodup m idx'
            (Nat.lt_trans hm (by rw [hte_sl]; exact hidx_te)) (by rw [hte_sl]; exact hidx_te)
            (by rw [htrl_sl, hmeq, ded_lit_xor1_div2, hqp, hp_get])
          omega
      · right
        have hq' : q ∈ fullRsnLits sl rsn := by
          unfold fullRsnLits; rw [ite_eq_right hrsn_ne, ite_eq_right (fun h => h hnb)]; exact hq
        exact hres_s2 q hq' (by rw [hsk]; exact hqp)
    · rw [htrl_sl, hp_get, hrs_sl, hrsn_get, ite_eq_left hnb] at hinv_idx
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      refine ded_clause_entails_resolve_step (p := p_bv.toNat) hs1.ent hinv_idx.2.1
        hs1_to_s2' (fun q hq => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hqp | hqot
      · exact Or.inl hqp
      · right; subst hqot
        obtain ⟨m, hm, hmeq, _⟩ := hinv_idx.2.2
        have hne : ot / 2 ≠ p_bv.toNat / 2 := fun heq => by
          have hidx_eq := hw_sl.trail_vars_nodup m idx'
            (Nat.lt_trans hm (by rw [hte_sl]; exact hidx_te)) (by rw [hte_sl]; exact hidx_te)
            (by rw [htrl_sl, hmeq, ded_lit_xor1_div2, heq, hp_get])
          omega
        have hot' : ot ∈ fullRsnLits sl rsn := by
          unfold fullRsnLits; rw [ite_eq_right hrsn_ne, ite_eq_left hnb, List.mem_singleton]
        exact hres_s2 ot hot' (by rw [hsk]; exact hne)
  have hsum_le : (s2.core.tmp_len - 1) + s2.core.tmp_cnt ≤ s2.core.cur_vars := by
    rw [htc2_eq']
    refine fullActiveResolvent_le_cur_vars
      (by rw [hs2_te, hte_sl]; exact Nat.le_of_lt hidx_te)
      htl2_ge1' (by rw [hlen2'.core_ok.tmp_len_arr]
                    exact Nat.le_trans htl2_cv' (by rw [hs2_cv, hcv_sl]; exact hcv_le))
      hlow2' hw2'.trail_lits_lt hw2'.trail_vars_nodup
  have hsum_lt : (s2.core.tmp_len - 1) + s2.core.tmp_cnt + 1 < 2 ^ 64 := by
    have := hlen2'.core_ok.cur_vars_le; omega
  have hpos_res : 0#64 < s2.scratch.res_sz := by
    rw [hres2']
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt]
    omega
  have hres_s3 : s3.scratch.res_sz = BitVec.ofNat 64 ((s3.core.tmp_len - 1) + s3.core.tmp_cnt) := by
    have hs3_c : s3.core = s2.core := by rw [hs3_eq]
    have hs3_res : s3.scratch.res_sz = s2.scratch.res_sz - 1#64 := by rw [hs3_eq]
    rw [hs3_c, hs3_res, hres2']
    apply BitVec.eq_of_toNat_eq
    have h1_le : (1#64).toNat ≤
        (BitVec.ofNat 64 (s2.core.tmp_len - 1 + s2.core.tmp_cnt + 1)).toNat := by
      rw [show (1#64).toNat = 1 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt]; omega
    rw [bv64_sub_small_eq h1_le]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt,
      Nat.mod_eq_of_lt (by omega : s2.core.tmp_len - 1 + s2.core.tmp_cnt < 2 ^ 64)]
    omega
  have hs3_core : s3.core = s2.core := by rw [hs3_eq]
  have hlen3 : s3.LengthsOk c :=
    ded_lengthsOk_same_core_res hlen2' hs3_core (by rw [hs3_eq])
  have hext3 : FullExtScratchPres s s3 :=
    fullExtScratchPres_trans hext2' (by unfold FullExtScratchPres; rw [hs3_eq]; exact ⟨rfl, rfl⟩)
  have hws2_3 : s3.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hs3_eq]; exact hws2'
  have hs3_inv : FullDeduceStateInv c F0 F_cur cut idx' s s3 := by
    refine ⟨hlen3, by rw [hs3_core]; exact hw2',
      by unfold FullAnaMarksCov; rw [hs3_core, show s3.scratch.work_stk1 = s2.scratch.work_stk1
          by rw [hs3_eq]]; exact hcov2',
      hext3, hws2_3,
      ded_arenaVarsNodup_same_core_arena hnd2' (by rw [hs3_core]) (by rw [hs3_core]),
      by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hs3_core]; exact hrefs2',
      hstat2'.trans (by rw [hs3_core]; exact fullDeduceStaticEq_refl _),
      hs3_core ▸ htl2_ge1', hs3_core ▸ htl2_cv', ?_, ?_, ?_, ?_, ?_, hres_s3⟩
    · unfold fullCurTrailIdxs; rw [hs3_core]; exact htc2_eq'
    · unfold FullLowerInv; rw [hs3_core]; exact hlow2'
    · unfold FullMarksCov; rw [hs3_core]; exact hmcov2'
    · have hc2 := hcm2'; unfold FullCurMarksBelow at hc2 ⊢; rw [hs3_core]; exact hc2
    · unfold fullActiveResolvent fullLowerLits fullCurLits fullCurTrailIdxs
      rw [hs3_core]; exact hent_s2
  refine ⟨hidx_cut, hpos_res, hs3_inv, fun hnb => ?_, fun l hl hne hpos => ?_⟩
  · have hants := ded_rsn_ant_sz_eq (p_bv := p_bv) hlen_l hw_sl hnd_sl hidx_cut
      (by rw [htrl_sl]; exact hp_get) (by rw [hrs_sl]; exact hrsn_get) (by rw [hsl_sc])
      hs2_lvl hrefs2 hcl2 (by rw [hs2_eq]) hrsn_ne hnb hant_spec
    have hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s2 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hs3_core]
    have hgarb3 : fullArenaClauseGarb s3 rsn.toNat = fullArenaClauseGarb s2 rsn.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs3_core]
    have hlits3 : fullArenaClauseLits s3 rsn.toNat = fullArenaClauseLits s2 rsn.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hs3_core]
    have hant3 : s3.scratch.ant_sz = s2.scratch.ant_sz := by rw [hs3_eq]
    rw [hrefs3, hgarb3, hlits3, hs3_core, hant3]; exact hants
  · rw [hs3_core] at hpos ⊢; rw [hsk] at hall_mrk; exact hall_mrk l hl hne hpos

/-! ## 4. OTFS Pigeonhole, Entailment & Conflict Preservation Lemmas -/

theorem otfs_active_subset_rsn {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s s3 : FullState} {cref uip : BitVec 32}
    (hs3 : FullDeduceStateInv c F0 F_cur cut idx' s s3)
    (hcur_pos : 0 < s.core.cur_level)
    (hidx_te : idx' < s3.core.trail_end) (hidx_cut : idx' < cut)
    (hp_get : (s3.core.trl[idx']?.getD 0#32).toNat = uip.toNat)
    (hrsn_get : s3.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlvl_u : (s3.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hnb : cref &&& 0x80000000#32 = 0#32)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s3) (hng : fullArenaClauseGarb s3 cref.toNat = false)
    (hall_mrk : ∀ l ∈ fullArenaClauseLits s3 cref.toNat, l / 2 ≠ uip.toNat / 2 →
      0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hant_eq : s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 cref.toNat).filter fun l =>
      decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length)
    (hlt_ant : s3.scratch.res_sz < s3.scratch.ant_sz) :
    (∀ l ∈ fullActiveResolvent s3.core s3.core.tmp s3.core.mrk s3.core.tmp_len idx',
      l ∈ (fullArenaClauseLits s3 cref.toNat).filter fun q =>
        decide (q ≠ uip.toNat ∧ 0 < (s3.core.lvl[q / 2]?.getD 0#32).toNat)) ∧
    ((fullArenaClauseLits s3 cref.toNat).filter fun q =>
      decide (q ≠ uip.toNat ∧ 0 < (s3.core.lvl[q / 2]?.getD 0#32).toNat)).length =
        s3.scratch.res_sz.toNat := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hs3.len.core_ok.cur_vars_le
  have hrsn_ne : cref ≠ 0xFFFFFFFF#32 := fun h => by subst h; simp at hnb
  have hinv := hs3.hw.reason_inv_cut idx' hidx_cut (by rw [hp_get, hrsn_get]; exact hrsn_ne)
  rw [hp_get, hrsn_get, ite_eq_right (fun h => h hnb)] at hinv
  have huip_mem : uip.toNat ∈ fullArenaClauseLits s3 cref.toNat := by
    have hm := hs3.hw.reason_lit_mem_cut idx' hidx_cut (by rw [hp_get, hrsn_get]; exact hrsn_ne)
      (by rw [hp_get, hrsn_get]; exact hnb)
    rw [hp_get, hrsn_get] at hm; exact hm
  let lits := fullArenaClauseLits s3 cref.toNat
  let act := lits.filter fun l => decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)
  let actNoU := lits.filter fun l =>
    decide (l ≠ uip.toNat ∧ 0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)
  let res := fullActiveResolvent s3.core s3.core.tmp s3.core.mrk s3.core.tmp_len idx'
  have hnd_lits_vars : (lits.map (· / 2)).Nodup := hs3.nd cref.toNat hcref hng
  have hnd_lits : lits.Nodup := ded_nodup_of_map_nodup hnd_lits_vars
  have hnd_act : act.Nodup := List.Pairwise.filter _ hnd_lits
  have hnd_actNoU : actNoU.Nodup := List.Pairwise.filter _ hnd_lits
  have huip_pos : 0 < (s3.core.lvl[uip.toNat / 2]?.getD 0#32).toNat := by
    rw [hlvl_u, hs3.stat.cl]; exact hcur_pos
  have huip_act : uip.toNat ∈ act := by
    rw [List.mem_filter, decide_eq_true_iff]; exact ⟨huip_mem, huip_pos⟩
  have hcongr_act : act.filter (fun x => decide (x ≠ uip.toNat)) = actNoU := by
    rw [List.filter_filter]
    apply List.filter_congr; intro l _
    rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff]
  have hlen_act : act.length = actNoU.length + 1 := by
    rw [← hcongr_act]; exact ded_nodup_filter_ne_length uip.toNat hnd_act huip_act
  have hact_sub_res : actNoU ⊆ res := by
    intro q hq
    rw [List.mem_filter, decide_eq_true_iff] at hq
    obtain ⟨hq_mem, hq_ne, hq_pos⟩ := hq
    have hq_div : q / 2 ≠ uip.toNat / 2 :=
      ded_mem_div2_ne_of_map_nodup hnd_lits_vars hq_mem huip_mem hq_ne
    have hq_lt : q < 2 * s3.core.cur_vars := hs3.hw.arena.lits_lt cref.toNat hcref hng q hq_mem
    have hq_tr : ∃ m < idx', (s3.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 := by
      rcases hinv.2.2 q hq_mem with hq_u | ⟨m, hm, hmeq, _⟩
      · exact absurd hq_u hq_ne
      · exact ⟨m, hm, hmeq⟩
    obtain ⟨m0, hm0, hm0_eq⟩ := hq_tr
    have hq_f : s3.core.vals[q]?.getD 0#8 = 0xFF#8 :=
      (hs3.hw.vals_false_iff q hq_lt).mpr ⟨m0, Nat.lt_trans hm0 hidx_te, hm0_eq⟩
    have htl_len : s3.core.tmp_len ≤ s3.core.tmp.length := by
      rw [hs3.len.core_ok.tmp_len_arr]
      exact Nat.le_trans hs3.tl_cv hs3.len.core_ok.cur_vars_le
    exact ded_activeResolvent_mem_of_pos_lvl hs3.hw hs3.low hs3.mcov htl_len hq_lt hq_f hq_pos
      (hall_mrk q hq_mem hq_div hq_pos) (fun _ => ⟨m0, hm0, hm0_eq⟩)
  have hle_act_res : actNoU.length ≤ res.length :=
    List.Nodup.length_le_of_subset hnd_actNoU hact_sub_res
  have hres_len_eq : res.length = s3.scratch.res_sz.toNat := by
    have htl_len : s3.core.tmp_len ≤ s3.core.tmp.length := by
      rw [hs3.len.core_ok.tmp_len_arr]
      exact Nat.le_trans hs3.tl_cv hs3.len.core_ok.cur_vars_le
    have hsum_le : (s3.core.tmp_len - 1) + s3.core.tmp_cnt ≤ s3.core.cur_vars := by
      rw [hs3.tc_eq]
      exact fullActiveResolvent_le_cur_vars (Nat.le_of_lt hidx_te) hs3.tl_ge htl_len
        hs3.low hs3.hw.trail_lits_lt hs3.hw.trail_vars_nodup
    have hres_n : res.length = (s3.core.tmp_len - 1) + s3.core.tmp_cnt := by
      unfold res fullActiveResolvent fullCurLits
      rw [List.length_append, List.length_map, fullLowerLits_length hs3.tl_ge htl_len,
        ← hs3.tc_eq]; omega
    have hcv3 := hs3.len.core_ok.cur_vars_le
    have hsum_lt : (s3.core.tmp_len - 1) + s3.core.tmp_cnt < 2 ^ 64 := by omega
    rw [hs3.res_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt, hres_n]
  have hlt_nat : s3.scratch.res_sz.toNat < act.length := by
    rw [← hant_eq]; exact BitVec.lt_def.mp hlt_ant
  have hact_len_eq : actNoU.length = s3.scratch.res_sz.toNat := by omega
  have hnd_res : res.Nodup := by
    have htl_len : s3.core.tmp_len ≤ s3.core.tmp.length := by
      rw [hs3.len.core_ok.tmp_len_arr]
      exact Nat.le_trans hs3.tl_cv hs3.len.core_ok.cur_vars_le
    have hndL := fullLowerLits_vars_nodup hs3.low htl_len
    have hndC : ((fullCurLits s3.core s3.core.mrk idx').map (· / 2)).Nodup := by
      unfold fullCurLits; rw [List.map_map]
      refine ded_nodup_map_on (fun i hi j hj heq => ?_)
        (List.Pairwise.filter _ List.nodup_range)
      have hi1 := (fullCurTrailIdxs_mem_iff.mp hi).1
      have hj1 := (fullCurTrailIdxs_mem_iff.mp hj).1
      simp only [Function.comp_apply, ded_lit_xor1_div2] at heq
      exact hs3.hw.trail_vars_nodup i j (Nat.lt_trans hi1 hidx_te) (Nat.lt_trans hj1 hidx_te) heq
    have hdisj : ∀ v ∈ (fullLowerLits s3.core.tmp s3.core.tmp_len).map (· / 2),
        v ∉ (fullCurLits s3.core s3.core.mrk idx').map (· / 2) := by
      intro v hvL hvC
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvL
      obtain ⟨j, hj1, hj2, hjeq⟩ := (fullLowerLits_mem_iff htl_len).mp hl
      obtain ⟨l2, hl2, hl2eq⟩ := List.mem_map.mp hvC
      unfold fullCurLits at hl2; obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hl2
      have hci := fullCurTrailIdxs_mem_iff.mp hi
      have hlt := (hs3.low.1 j hj1 hj2).2.2.2.1
      rw [hjeq, ← hl2eq, ← hieq, ded_lit_xor1_div2, hci.2.2] at hlt; omega
    have hnd_vars : (res.map (· / 2)).Nodup := by
      unfold res fullActiveResolvent
      rw [List.map_append]
      exact List.nodup_append.mpr ⟨hndC, hndL, fun v hvC w hvL heq =>
        hdisj w hvL (heq ▸ hvC)⟩
    exact ded_nodup_of_map_nodup hnd_vars
  refine ⟨fun x hx => ?_, hact_len_eq⟩
  exact Classical.byContradiction fun hnx => by
    have hsub_er : actNoU ⊆ res.erase x := by
      intro y hy
      have hne_yx : y ≠ x := fun heq => hnx (heq ▸ hy)
      exact (List.mem_erase_of_ne hne_yx).mpr (hact_sub_res hy)
    have hle_er := List.Nodup.length_le_of_subset hnd_actNoU hsub_er
    have her_len := List.length_erase_of_mem hx
    rw [her_len, hact_len_eq, hres_len_eq] at hle_er
    have hx_pos : 0 < res.length := List.length_pos_of_mem hx
    rw [hres_len_eq] at hx_pos
    omega

theorem otfs_entails_large_of_res_lt_ant {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s s3 : FullState} {cref uip : BitVec 32}
    (hs3 : FullDeduceStateInv c F0 F_cur cut idx' s s3)
    (hcur_pos : 0 < s.core.cur_level)
    (hidx_te : idx' < s3.core.trail_end) (hidx_cut : idx' < cut)
    (hp_get : (s3.core.trl[idx']?.getD 0#32).toNat = uip.toNat)
    (hrsn_get : s3.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlvl_u : (s3.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hnb : cref &&& 0x80000000#32 = 0#32)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s3) (hng : fullArenaClauseGarb s3 cref.toNat = false)
    (hall_mrk : ∀ l ∈ fullArenaClauseLits s3 cref.toNat, l / 2 ≠ uip.toNat / 2 →
      0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hant_eq : s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 cref.toNat).filter fun l =>
      decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length)
    (hlt_ant : s3.scratch.res_sz < s3.scratch.ant_sz) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s3 cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s3.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s3.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))) := by
  obtain ⟨hsub, _⟩ := otfs_active_subset_rsn hs3 hcur_pos hidx_te hidx_cut hp_get hrsn_get hlvl_u
    hnb hcref hng hall_mrk hant_eq hlt_ant
  refine ded_clause_entails_of_subset hs3.ent fun l hl => ?_
  have hmem := hsub l hl
  rw [List.mem_filter, decide_eq_true_iff] at hmem ⊢
  exact ⟨hmem.1, hmem.2.1, Or.inl hmem.2.2⟩

theorem otfs_entails_bin_of_res_lt_ant {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s s3 : FullState} {cref uip : BitVec 32}
    (hs3 : FullDeduceStateInv c F0 F_cur cut idx' s s3)
    (hcur_pos : 0 < s.core.cur_level)
    (hidx_te : idx' < s3.core.trail_end) (hidx_cut : idx' < cut)
    (hp_get : (s3.core.trl[idx']?.getD 0#32).toNat = uip.toNat)
    (hrsn_get : s3.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlvl_u : (s3.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hnb : cref &&& 0x80000000#32 = 0#32)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s3) (hng : fullArenaClauseGarb s3 cref.toNat = false)
    (hall_mrk : ∀ l ∈ fullArenaClauseLits s3 cref.toNat, l / 2 ≠ uip.toNat / 2 →
      0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hant_eq : s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 cref.toNat).filter fun l =>
      decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length)
    (hant3 : s3.scratch.ant_sz = 3#64) (hlt_ant : s3.scratch.res_sz < s3.scratch.ant_sz)
    (f0 f1 : BitVec 32)
    (hf0_mem : f0.toNat ∈ fullArenaClauseLits s3 cref.toNat)
    (hf1_mem : f1.toNat ∈ fullArenaClauseLits s3 cref.toNat)
    (hf0_ne : f0 ≠ uip) (hf1_ne : f1 ≠ uip) (hf_ne : f0 ≠ f1)
    (hf0_pos : 0 < (s3.core.lvl[f0.toNat / 2]?.getD 0#32).toNat)
    (hf1_pos : 0 < (s3.core.lvl[f1.toNat / 2]?.getD 0#32).toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]) := by
  obtain ⟨hsub, hlen⟩ := otfs_active_subset_rsn hs3 hcur_pos hidx_te hidx_cut hp_get hrsn_get hlvl_u
    hnb hcref hng hall_mrk hant_eq hlt_ant
  have hlt3 : s3.scratch.res_sz.toNat < 3 := by
    have := BitVec.lt_def.mp hlt_ant; rwa [hant3] at this
  have hne0 : f0.toNat ≠ uip.toNat := fun h => hf0_ne (BitVec.eq_of_toNat_eq h)
  have hne1 : f1.toNat ≠ uip.toNat := fun h => hf1_ne (BitVec.eq_of_toNat_eq h)
  have hne01 : f0.toNat ≠ f1.toNat := fun h => hf_ne (BitVec.eq_of_toNat_eq h)
  let actNoU := (fullArenaClauseLits s3 cref.toNat).filter fun q =>
    decide (q ≠ uip.toNat ∧ 0 < (s3.core.lvl[q / 2]?.getD 0#32).toNat)
  have hf0_in : f0.toNat ∈ actNoU := by
    rw [List.mem_filter, decide_eq_true_iff]; exact ⟨hf0_mem, hne0, hf0_pos⟩
  have hf1_in : f1.toNat ∈ actNoU := by
    rw [List.mem_filter, decide_eq_true_iff]; exact ⟨hf1_mem, hne1, hf1_pos⟩
  refine ded_clause_entails_of_subset hs3.ent fun l hl => ?_
  have hl_in := hsub l hl
  rcases Classical.em (l = f0.toNat ∨ l = f1.toNat) with heq | hne
  · simpa [List.mem_cons] using heq
  · have hnd3 : ([f0.toNat, f1.toNat, l] : List Nat).Nodup := by
      simp [hne01, Ne.symm (fun h => hne (Or.inl h)), Ne.symm (fun h => hne (Or.inr h))]
    have hsub3 : [f0.toNat, f1.toNat, l] ⊆ actNoU := by
      intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have hlen3 := List.Nodup.length_le_of_subset hnd3 hsub3
    change 3 ≤ actNoU.length at hlen3
    rw [hlen] at hlen3
    omega

theorem deduce_otfs_old_cr_nonactive {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_otfs : FullState}
    (hs_cut : FullCutInvW c F0 F_cur cut s) (hconfl : FullConflictOkCut F_cur cut s)
    (hiu_cut : idx_u < cut) (hstat : FullDeduceStaticEq s.core s_otfs.core)
    (hold2 : s.core.confl_type = 2#64) (_hold_ne : s.core.confl_ref ≠ 0xFFFFFFFF#64) :
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    (∀ rsn_u : BitVec 32,
      (s_otfs.core.trl[idx_u]?.getD 0#32).toNat < 2 * s_otfs.core.cur_vars →
      s_otfs.core.rsns[(s_otfs.core.trl[idx_u]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        rsn_u →
      rsn_u ≠ 0xFFFFFFFF#32 → rsn_u &&& 0x80000000#32 = 0#32 →
      rsn_u.toNat ≠ s.core.confl_ref.toNat) ∧
    (∀ idx < s_otfs.core.trail_end,
      let v := (s_otfs.core.trl[idx]?.getD 0#32).toNat / 2
      let rsn := s_otfs.core.rsns[v]?.getD 0xFFFFFFFF#32
      idx < idx_u ∨ (s_otfs.core.lvl[v]?.getD 0#32).toNat < s_otfs.core.cur_level →
      rsn ≠ 0xFFFFFFFF#32 → rsn &&& 0x80000000#32 = 0#32 → rsn.toNat ≠ s.core.confl_ref.toNat) := by
  have h2 : s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
      ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
        s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hconfl.1 with h1 | h2
    · exact absurd h1.1 (by rw [hold2]; decide)
    · exact h2.2
  have hnon := falsified_clause_nonactive hs_cut.2.1 (cref := s.core.confl_ref.toNat) h2.2.2
  refine ⟨h2.1, fun rsn_u _ hrs_u hne hnb => ?_, fun idx hidx hdisj hne hnb => ?_⟩
  · have hidx_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hs_cut.2.1.cut_le
    have hna := hnon idx_u hidx_te (Or.inl hiu_cut)
    rw [hstat.trl, hstat.rsns] at hrs_u
    rw [hrs_u] at hna
    exact hna hne hnb
  · rw [hstat.te] at hidx
    have hdisj' : idx < cut ∨
        (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          s.core.cur_level := by
      rcases hdisj with h1 | h2'
      · exact Or.inl (Nat.lt_trans h1 hiu_cut)
      · right; rw [hstat.trl, hstat.lvl, hstat.cl] at h2'; exact h2'
    have hna := hnon idx hidx hdisj'
    rw [hstat.trl, hstat.rsns]
    exact hna (by rw [← hstat.trl, ← hstat.rsns]; exact hne)
      (by rw [← hstat.trl, ← hstat.rsns]; exact hnb)

theorem deduce_conflOk_with_counts {F_cur : List (List Nat)} {cut : Nat} {s s' : FullState}
    (hconfl : FullConflictOkCut F_cur cut s)
    (hc : s'.core.confl_type = s.core.confl_type ∧ s'.core.confl_ref = s.core.confl_ref ∧
      s'.core.confl_lit0 = s.core.confl_lit0 ∧ s'.core.confl_lit1 = s.core.confl_lit1 ∧
      s'.core.cur_vars = s.core.cur_vars ∧ s'.core.vals = s.core.vals ∧
      s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
      s'.core.cur_level = s.core.cur_level)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hpres : s.core.confl_type = 2#64 →
      fullArenaClauseGarb s' s.core.confl_ref.toNat =
        fullArenaClauseGarb s s.core.confl_ref.toNat ∧
      fullArenaClauseLits s' s.core.confl_ref.toNat =
        fullArenaClauseLits s s.core.confl_ref.toNat) :
    FullConflictOkCut F_cur cut s' := by
  rcases hc with ⟨hct, hcr, hc0, hc1, hcv, hv, hl, htr, hcl⟩
  obtain ⟨h1 | h2, htail⟩ := hconfl
  · refine ⟨Or.inl ?_, ?_⟩
    · rw [hct, hc0, hc1, hcv, hv]; exact h1
    · rw [ite_eq_left (by rw [hct, h1.1])]
      rw [ite_eq_left (by rw [h1.1])] at htail
      rw [hl, hc0, hc1, hcl, htr]; exact htail
  · obtain ⟨hg, hlt⟩ := hpres h2.1
    refine ⟨Or.inr ?_, ?_⟩
    · rw [hct, hcr, hrefs, hg, hlt, hv]; exact h2
    · rw [ite_eq_right (by rw [hct, h2.1]; decide)]
      rw [ite_eq_right (by rw [h2.1]; decide)] at htail
      rw [hcr, hlt, hl, hcl, htr]; exact htail

theorem deduce_conflOk_large_init {F_cur : List (List Nat)} {idx_u : Nat} {s : FullState}
    {cref : BitVec 32}
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hct : s.core.confl_type = 2#64) (hcr : s.core.confl_ref = cref.setWidth 64)
    (hvals : ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
        ∃ m < idx_u, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) :
    FullConflictOkCut F_cur idx_u s := by
  have hcr_nat : s.core.confl_ref.toNat = cref.toNat := by
    rw [hcr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans cref.isLt (by decide))]
  refine ⟨Or.inr ⟨hct, by rw [hcr_nat]; exact hcref, by rw [hcr_nat]; exact hng,
    fun l hl => (hvals l (by rwa [← hcr_nat])).1⟩, ?_⟩
  rw [ite_eq_right (by rw [hct]; decide)]
  intro l hl hlv
  exact (hvals l (by rwa [← hcr_nat])).2 hlv

end LeanQbe.T.Examples.Kissat.Proof.Deduce
