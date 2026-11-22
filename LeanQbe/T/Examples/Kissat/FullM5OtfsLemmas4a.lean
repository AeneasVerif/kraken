/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas3
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M5 `Func.wp` Proofs — Part 4a (`full_one_lit_confl_m5` Core & Repair Helpers)

Zero `import all LeanQbe.*`. Provides shared UNSAT-soundness building blocks (`XPost := False`)
for `full_one_lit_confl_m5_wp`:
1. `m5_chronoAssign_preserves_fullWitness_sameLvl`, `M5OneLitBtInv`, `m5_oneLit_after_bt`.
2. `M5OneLitPost` (without `r = 0#64` watch equalities, matching `Full.fullOneLitConflSpec`),
   `M5OneLitTailPre`, `m5_oneLit_after_bt_assign_wp`, `m5_oneLit_large_tail_exec_wp`.
3. `m5_oneLit_bin_branch_wp` (binary branch `confl_type == 1`).
4. `M5OneLitScanInv`, `m5_oneLit_scan_bds`, `m5_wstack_ensure2_ret2_wp` (`ret 2#64` on OOM),
   `m5_oneLit_swap_arena_inv`, and `m5_oneLit_swap_push_branch_wp` (`hp != pos`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_unwatch_large_body full_unwatch_large_wf
  full_otfs_large_body full_otfs_large_wf full_otfs_large_wp full_otfs_large_wp_weak
  full_prop_lit_body full_prop_lit_wf
  full_propagate_ignore_body full_propagate_ignore_wf
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics

/-! ## 1. Fixed-`F_cur` chronological unit-assignment & backtrack helpers -/

theorem m5_otfsInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : Full.FullOtfsWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    Full.FullOtfsWitnessInv c F0 F_cur { k with oom := oom' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

private theorem m5_chronoAssign_preserves_fullWitness_sameLvl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : Full.FullWitnessInv c F0 F_cur s.core) {lit rsn : BitVec 32} {alvl : Nat}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ s.core.cur_level) (hrsn_ne_ff : rsn ≠ 0xFFFFFFFF#32)
    (hl0 : alvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = lit.toNat ∨ ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ alvl)
    (hrsn_mem : 0 < alvl → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore s.core rsn.toNat) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else rsn
    Full.FullWitnessInv c F0 F_cur
      { s.core with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
        rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unassigned', unflushed := unflushed' } := by
  intro v rsn'
  let k' : FullCoreState :=
    { s.core with
      vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
      rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
      trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
      trail_end := s.core.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
  have hcl := hlen.core_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := Full.fullInv_max_vars_lt32 c; have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := Full.fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1, (k'.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (k'.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, k'.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; simp only [k', ↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · simp only [k', h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, k'.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlt_w : ∀ i, i < s.core.trail_end → (s.core.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
    fun i hi => by have := hw.trail_lits_lt i hi; omega
  have hlift_rsn : ∀ {up p0 : Nat} {rv : BitVec 32} {p_lvl : Nat}, up ≤ s.core.trail_end →
      (rv &&& 0x80000000#32) ≠ 0#32 → p0 / 2 < s.core.cur_vars →
      (k'.lvl[p0 / 2]?.getD 0#32).toNat = p_lvl →
      ((let ot := (rv &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
        ∃ m < up, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ p_lvl) →
      let ot := (rv &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k'.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
      ∃ m < up, (k'.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k'.lvl[ot / 2]?.getD 0#32).toNat ≤ (k'.lvl[p0 / 2]?.getD 0#32).toNat) := by
    rintro up p0 rv p_lvl hup _ _ hpl ⟨hlt, hent, m, hm, hmeq, hlvl_le⟩
    have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm hup
    have hot_v : (rv &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := fun heqv => by
      have hme := hnot_var m hm'; rw [hmeq] at hme
      exact hme (by simpa [fullInv_var_xor1] using heqv)
    exact ⟨hlt, hent, m, hm,
      by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq],
      by rw [hpl, hlvl_get _ (by omega), ite_eq_right hot_v]; exact hlvl_le⟩
  have hlift_lg : ∀ {up p0 : Nat} {rv : BitVec 32} {p_lvl : Nat}, up ≤ s.core.trail_end →
      p0 / 2 < s.core.cur_vars → (k'.lvl[p0 / 2]?.getD 0#32).toNat = p_lvl →
      (rv.toNat ∈ fullArenaClauseRefsCore s.core ∧ fullArenaClauseGarbCore s.core rv.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rv.toNat,
          q = p0 ∨ ∃ m < up, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ p_lvl) →
      rv.toNat ∈ fullArenaClauseRefsCore k' ∧ fullArenaClauseGarbCore k' rv.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k' rv.toNat,
        q = p0 ∨ ∃ m < up, (k'.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k'.lvl[q / 2]?.getD 0#32).toNat ≤ (k'.lvl[p0 / 2]?.getD 0#32).toNat := by
    rintro up p0 rv p_lvl hup _ hpl ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun q hq => ?_⟩
    have hq' : q ∈ fullArenaClauseLitsCore s.core rv.toNat := by
      simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hq
    exact (h3 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm,
      by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq], by
        have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm hup
        have hq_lt := hw.arena.lits_lt _ h1 h2 q hq'
        have hqv : q / 2 ≠ v := fun heqv => by
          have hme := hnot_var m hm'; rw [hmeq] at hme
          exact hme (by simpa [fullInv_var_xor1] using heqv)
        rw [hpl, hlvl_get _ (by omega), ite_eq_right hqv]; exact hlvl_le⟩
  exact {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr
    cur_level_le := Nat.le_trans hw.cur_level_le (Nat.le_succ _)
    trail_lits_lt := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]
      split <;> (first | exact hlit | exact hw.trail_lits_lt i (by omega))
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only at hi hj ⊢; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]
      split; exact Or.inr (Or.inr rfl); split; exact Or.inr (Or.inl rfl); exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq
            change lit.toNat ^^^ 1 = litNeg (litNeg l) at h
            rw [litNeg_litNeg] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      dsimp only at hi ⊢; change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ _
      rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)]; exact hw.lvl_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      dsimp only at hi hj hleq hdec ⊢; change _ ≤ _ at ⊢
      rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        simp [rsn', hal0, hrsn_ne_ff] at hdec
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (hlt_w i hilt), hlvl_get _ (hlt_w j hjlt)] at hleq
          rw [hlvl_get _ (hlt_w j hjlt), hrsn_get _ (hlt_w j hjlt)] at hdec
          simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      dsimp only at hL1 hLle ⊢; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
      exact ⟨i, by omega, by
        rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi),
          ite_eq_right (hnot_var i hi)]; exact hli⟩
    level0_sound := fun i hi hli => by
      dsimp only at hi hli ⊢; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; exact hl0 hli
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)] at hli
        exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte, List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp only at hidx hli ⊢; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv] at hli
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv]; exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => Nat.le_trans (hw.frame_trail_lt L hL) (Nat.le_succ _)
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      dsimp only at hL1 hLle hi ⊢
      have hi_le : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
      rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi_le),
        ite_eq_right (hnot_var i hi_le)]
      exact hw.frame_trail_before_lt L hL1 hLle i hi
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      dsimp only at hidx hne ⊢; rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne ⊢; rw [hrsn_get v (by omega)] at hne ⊢
        simp only [↓reduceIte] at hne ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have hrs := hrsn (Nat.zero_lt_of_ne_zero hal0)
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          have hkv : (k'.lvl[lit.toNat / 2]?.getD 0#32).toNat = alvl := by
            change (k'.lvl[v]?.getD 0#32).toNat = alvl
            rw [hlvl_get v (by omega), ite_eq_left rfl]
          by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hbin] at hrs ⊢
            exact hlift_rsn (by omega) hbin (by omega) hkv hrs
          · rw [ite_eq_right hbin] at hrs ⊢
            exact hlift_lg (by omega) (by omega) hkv hrs
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne ⊢
        have hrs := hw.reason_inv idx hilt hne
        have hl_eq : (k'.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv]
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hlift_rsn (by omega) hbin (hlt_w idx hilt) hl_eq hrs
        · rw [ite_eq_right hbin] at hrs ⊢; exact hlift_lg (by omega) (hlt_w idx hilt) hl_eq hrs
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp only at hidx hne hlg ⊢; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢; rw [hrsn_get v (by omega)] at hne hlg ⊢
        simp only [↓reduceIte] at hne hlg ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using
            hrsn_mem (Nat.zero_lt_of_ne_zero hal0) hlg
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using
          hw.reason_lit_mem idx hilt hne hlg }

structure M5OneLitBtInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 : FullState) (cut1 clvl : Nat) : Prop where
  cut1_le : cut1 ≤ s1.core.trail_end
  hw1 : Full.FullWitnessCutInv c F0 F_cur cut1 s1.core
  len1 : s1.LengthsOk c
  cl1_eq : s1.core.cur_level = clvl
  cl_pos : 0 < clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : s1.core.cur_vars = s.core.cur_vars
  fuel_eq : s1.core.fuel = s.core.fuel
  ws2_eq : s1.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : s1.core.dense_mode = 0#64
  prob_eq : s1.core.probing = s.core.probing
  wvec_eq : s1.core.wvec = s.core.wvec
  wstk_eq : s1.core.wstk = s.core.wstk
  wlen_eq : s1.core.wlen = s.core.wlen
  wus_eq : s1.core.wusable = s.core.wusable
  marks1 : Full.FullLitMarksClear c s1
  nodup1 : Full.FullArenaVarsNodup s1
  ext1 : Full.FullExtScratchOk c s1
  confl1 : Full.FullConflictOkCut F_cur cut1 s1
  vals_keep : ∀ l < 2 * s.core.cur_vars,
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8
  lvl_keep : ∀ l < 2 * s.core.cur_vars,
    s.core.vals[l]?.getD 0#8 = 0xFF#8 →
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl →
    s1.core.lvl[l / 2]?.getD 0#32 = s.core.lvl[l / 2]?.getD 0#32
  arena_eq : s1.core.arena = s.core.arena
  arena_len_eq : s1.core.arena_len = s.core.arena_len
  confl_type_eq : s1.core.confl_type = s.core.confl_type
  confl_ref_eq : s1.core.confl_ref = s.core.confl_ref

theorem m5_oneLit_after_bt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut clvl : Nat} {s s1 : FullState} (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : Full.FullLitMarksClear c s)
    (hnd : Full.FullArenaVarsNodup s) (hext : Full.FullExtScratchOk c s)
    (hcut_le : cut ≤ s.core.trail_end) (hconfl : Full.FullConflictOkCut F_cur cut s)
    (hcl_pos : 0 < clvl) (hcl_le : clvl ≤ s.core.cur_level)
    (hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
        (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
      (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
      (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl)
    (hs1 : s.core.cur_level ≤ clvl ∧ s1 = s ∨
      clvl < s.core.cur_level ∧ s1.LengthsOk c ∧ s1.core.cur_level = clvl ∧
      s1.core.fuel = s.core.fuel ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len ∧
      s1.core.dense_mode = 0#64 ∧ s1.core.probing = s.core.probing ∧
      s1.core.cur_vars = s.core.cur_vars ∧ s1.core.wvec = s.core.wvec ∧
      s1.core.wstk = s.core.wstk ∧ s1.core.wlen = s.core.wlen ∧ s1.core.wusable = s.core.wusable ∧
      s1.core.mrk = s.core.mrk ∧ s1.core.lit_mark = s.core.lit_mark ∧
      s1.core.arena = s.core.arena ∧ s1.core.arena_len = s.core.arena_len ∧
      s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_lit0 = s.core.confl_lit0 ∧
      s1.core.confl_lit1 = s.core.confl_lit1 ∧ s1.core.confl_ref = s.core.confl_ref ∧
      (∀ l < 2 * s.core.cur_vars, s1.core.vals[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl then s.core.vals[l]?.getD 0#8 else 0#8) ∧
      (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
        s1.core.lvl[v]?.getD 0#32 =
          if (s.core.lvl[v]?.getD 0#32).toNat ≤ clvl then s.core.lvl[v]?.getD 0#32 else 0#32) ∧
      Full.FullWitnessInv c F0 F_cur s1.core) :
    ∃ cut1, M5OneLitBtInv c F0 F_cur s s1 cut1 clvl := by
  rcases hs1 with ⟨hle, rfl⟩ | ⟨_, hlen1, hcl1, hfu1, hws2, hll1, hel1, hdm1, hpr1, hcv1, hwv1,
      hws1, hwl1, hwu1, hmk1, hlm1, har1, hal1, hct1, hc01, hc11, hcr1, hvals1, hlvl1, hw1⟩
  · exact ⟨cut, hcut_le, hw, hlen, by omega, hcl_pos, hcl_le, rfl, rfl, rfl, hdm, rfl, rfl, rfl,
      rfl, rfl, hmarks, hnd, hext, hconfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl,
      rfl, rfl⟩
  · have hrefs : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core := by
      simp [fullArenaClauseRefsCore, har1, hal1]
    have hmarks1 : Full.FullLitMarksClear c s1 :=
      ⟨fun v hv => by rw [hmk1]; exact hmarks.1 v hv, fun l hl => by rw [hlm1]; exact hmarks.2 l hl⟩
    have hnd1 : Full.FullArenaVarsNodup s1 := fun r hr hng => by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs] at hr
      change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
      simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
      exact hnd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, har1] using hng)
    have hext1 : Full.FullExtScratchOk c s1 := ⟨fun i hi => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s1.core
      rw [hrefs, hll1]; exact hext.1 i hi, by rw [hel1]; exact hext.2⟩
    have hconfl1 : Full.FullConflictOkCut F_cur s1.core.trail_end s1 := by
      refine Full.FullConflictOkW.toCut hw1 ?_
      rcases hconfl.1 with ⟨hbin, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨hct2, href, hng, hf⟩
      · left; rw [hct1, hc01, hc11, hcv1]
        have hf0' : s1.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h0lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inl rfl⟩)), hf0]
        have hf1' : s1.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hvals1 _ h1lt, ite_eq_left (hbt_lt _ (Or.inl ⟨hbin, Or.inr rfl⟩)), hf1]
        exact ⟨hbin, h0lt, h1lt, hf0', hf1', hent⟩
      · right
        have hne1 : s.core.confl_type ≠ 1#64 := by rw [hct2]; decide
        have hgarb : fullArenaClauseGarb s1 s.core.confl_ref.toNat =
            fullArenaClauseGarb s s.core.confl_ref.toNat := by
          simp [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har1]
        have hlits : fullArenaClauseLits s1 s.core.confl_ref.toNat =
            fullArenaClauseLits s s.core.confl_ref.toNat := by
          simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, har1]
        rw [hct1, hcr1, show fullArenaClauseRefs s1 = fullArenaClauseRefs s from hrefs,
          hgarb, hlits]
        refine ⟨hct2, href, hng, fun l hl => ?_⟩
        have hllt := hw.arena.lits_lt _ href hng l hl
        rw [hvals1 l hllt, ite_eq_left (hbt_lt l (Or.inr ⟨hne1, hl⟩)), hf l hl]
    refine ⟨s1.core.trail_end, Nat.le_refl _, hw1.toCut, hlen1, hcl1, hcl_pos,
      hcl_le, hcv1, hfu1, hws2, hdm1, hpr1, hwv1, hws1, hwl1, hwu1, hmarks1, hnd1, hext1, hconfl1,
      fun l hl hle => by rw [hvals1 l hl, ite_eq_left hle], fun l hl hfl hle => ?_, har1, hal1,
      hct1, hcr1⟩
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hl).mp hfl
    have hv := hlvl1 i hi; dsimp only at hv; rw [hieq, fullInv_var_xor1] at hv
    rw [hv, ite_eq_left hle]

def M5OneLitPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r s' m',
    s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
    s'.scratch.work_stk2 = s.scratch.work_stk2 →
    s'.core.dense_mode = 0#64 → s'.core.probing = s.core.probing →
    Full.FullLitMarksClear c s' → Full.FullArenaVarsNodup s' → Full.FullExtScratchOk c s' →
    (s.core.confl_type = 1#64 → r ≠ 2#64) →
    (r = 20#64 → F0.Unsat ∧ s' = s) →
    (r = 1#64 → Full.FullWitnessInv c F0 F_cur s'.core ∧ s'.core.cur_level < s.core.cur_level) →
    (r = 2#64 → Full.FullOtfsWitnessInv c F0 F_cur s'.core) →
    (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
      Full.FullWitnessCutInv c F0 F_cur cut' s'.core ∧ 0 < s'.core.cur_level ∧
      s'.core.cur_level ≤ s.core.cur_level ∧ Full.FullConflictOkCut F_cur cut' s') →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private structure M5OneLitTailPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sb : FullState) (cut1 clvl jlvl : Nat) (forced rsn : BitVec 32) : Prop where
  len : sb.LengthsOk c
  hw : Full.FullWitnessCutInv c F0 F_cur cut1 sb.core
  marks : Full.FullLitMarksClear c sb
  nd : Full.FullArenaVarsNodup sb
  ext : Full.FullExtScratchOk c sb
  cl_eq : sb.core.cur_level = clvl
  cl_le : clvl ≤ s.core.cur_level
  cv_eq : sb.core.cur_vars = s.core.cur_vars
  fu_eq : sb.core.fuel = s.core.fuel
  ws2_eq : sb.scratch.work_stk2 = s.scratch.work_stk2
  dm0 : sb.core.dense_mode = 0#64
  prob_eq : sb.core.probing = s.core.probing
  forced_lt : forced.toNat < 2 * sb.core.cur_vars
  forced_lvl : (sb.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl
  rsn_ne : rsn ≠ 0xFFFFFFFF#32
  rsn_pre :
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * sb.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
      sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
    else
      rsn.toNat ∈ fullArenaClauseRefsCore sb.core ∧
      fullArenaClauseGarbCore sb.core rsn.toNat = false ∧
      forced.toNat ∈ fullArenaClauseLitsCore sb.core rsn.toNat ∧
      ∀ q ∈ fullArenaClauseLitsCore sb.core rsn.toNat,
        q = forced.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
          (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl)

private theorem m5_oneLit_after_bt_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl nlvl : Nat} {s s1 s2 : FullState}
    {forced rsn : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {m2 : Mem 64}
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hpre : M5OneLitTailPre c F0 F_cur s s1 cut1 clvl jlvl forced rsn)
    (hjv_eq : jlvlv.toNat = jlvl) (hj_lt32 : jlvl < 2 ^ 32)
    (hjlvl_le : jlvl ≤ nlvl) (hnlvl_lt : nlvl < clvl)
    (hs2_len : s2.LengthsOk c) (hs2_cl : s2.core.cur_level = nlvl)
    (hs2_fu : s2.core.fuel = s1.core.fuel) (hs2_ws2 : s2.scratch.work_stk2 = s1.scratch.work_stk2)
    (hs2_ll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hs2_el : s2.scratch.extend_len = s1.scratch.extend_len)
    (hs2_dm : s2.core.dense_mode = 0#64) (hs2_pr : s2.core.probing = s1.core.probing)
    (hs2_cv : s2.core.cur_vars = s1.core.cur_vars)
    (hs2_mk : s2.core.mrk = s1.core.mrk) (hs2_lm : s2.core.lit_mark = s1.core.lit_mark)
    (hs2_ar : s2.core.arena = s1.core.arena) (hs2_al : s2.core.arena_len = s1.core.arena_len)
    (hs2_vals : ∀ l < 2 * s1.core.cur_vars, s2.core.vals[l]?.getD 0#8 =
      if (s1.core.lvl[l / 2]?.getD 0#32).toNat ≤ nlvl then s1.core.vals[l]?.getD 0#8 else 0#8)
    (hs2_lvl : ∀ i < s1.core.trail_end, let v := (s1.core.trl[i]?.getD 0#32).toNat / 2
      s2.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ nlvl then s1.core.lvl[v]?.getD 0#32 else 0#32)
    (hw2 : Full.FullWitnessInv c F0 F_cur s2.core) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : M5OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
        (Arg.var c.hdr, Arg.var forced, Arg.var rsn, Arg.var (jlvlv.setWidth 32), ())
        fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) m2 := by
  have htr_eq : jlvlv.setWidth 32 = BitVec.ofNat 32 jlvl := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, hjv_eq, bv32_ofNat_toNat hj_lt32, Nat.mod_eq_of_lt hj_lt32])
  have hf_un : s2.core.vals[forced.toNat]?.getD 0#8 = 0#8 := by
    rw [hs2_vals _ hpre.forced_lt, ite_eq_right (by have := hpre.forced_lvl; omega)]
  have hte2_lt : s2.core.trail_end < s2.core.cur_vars :=
    hw2.trail_end_lt_of_unassigned (hs2_cv ▸ hpre.forced_lt) hf_un
  have hng_guard : ¬ (s2.core.cur_vars ≤ forced.toNat / 2 ∨
      c.max_vars ≤ s2.core.trail_end ∨ s2.core.vals[forced.toNat]?.getD 0#8 ≠ 0#8) :=
    not_or.mpr ⟨Nat.not_le.mpr (Nat.div_lt_of_lt_mul (hs2_cv ▸ hpre.forced_lt)), not_or.mpr
      ⟨Nat.not_le.mpr (by have := hs2_len.core_ok.cur_vars_le; omega), fun h => h hf_un⟩⟩
  c0_call hAss
  refine ⟨c, s2, R, rfl, hs2_len, hm2, ?_⟩
  simp only [hng_guard, ↓reduceIte]
  intro fl' unass3 ph' m3 hfl3 hph3 hm3
  let v := forced.toNat / 2
  let rsn' := if jlvl = 0 then 0xFFFFFFFF#32 else rsn
  let s3 : FullState :=
    { s2 with
      core :=
        { s2.core with
          vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
          flags := fl', lvl := s2.core.lvl.set v (BitVec.ofNat 32 jlvl)
          rsns := s2.core.rsns.set v rsn', trl := s2.core.trl.set s2.core.trail_end forced
          trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
          trail_end := s2.core.trail_end + 1, unassigned := unass3
          unflushed := if jlvlv.setWidth 32 = 0#32
            then s2.core.unflushed + 1#64 else s2.core.unflushed }
      scratch := { s2.scratch with phases := ph' } }
  have hcv2 := hs2_len.core_ok.cur_vars_le
  have hlen3 : s3.LengthsOk c :=
    ⟨{ hs2_len.core_ok with
        vals_len := by simp [s3, hs2_len.core_ok.vals_len], flags_len := hfl3,
        lvl_len := by simp [s3, hs2_len.core_ok.lvl_len],
        rsns_len := by simp [s3, hs2_len.core_ok.rsns_len],
        trl_len := by simp [s3, hs2_len.core_ok.trl_len],
        trail_pos_len := by simp [s3, hs2_len.core_ok.trail_pos_len],
        trail_end_le := by dsimp [s3]; omega,
        propagated_le := Nat.le_trans hs2_len.core_ok.propagated_le (Nat.le_succ _) },
     { hs2_len.scratch_ok with phases_len := by dsimp [s3]; exact hph3 }⟩
  have hmarks3 : Full.FullLitMarksClear c s3 := ⟨fun w hw => by
    change s2.core.mrk[w]?.getD 0#8 = 0#8; rw [hs2_mk]; exact hpre.marks.1 w hw,
    fun l hl => by change s2.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs2_lm]; exact hpre.marks.2 l hl⟩
  have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s1.core := by
    simp [fullArenaClauseRefsCore, s3, hs2_ar, hs2_al]
  have hnd3 : Full.FullArenaVarsNodup s3 := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs] at hr
    change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
    simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3, hs2_ar]
    exact hpre.nd r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3, hs2_ar] using hng)
  have hext3 : Full.FullExtScratchOk c s3 := ⟨fun i hi => by
    change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s3.core; rw [hrefs, hs2_ll]; exact hpre.ext.1 i hi,
    by change s2.scratch.extend_len ≤ c.extend_cap; rw [hs2_el]; exact hpre.ext.2⟩
  have h_s2_false : ∀ q < 2 * s1.core.cur_vars, s1.core.vals[q]?.getD 0#8 = 0xFF#8 →
      (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl →
      ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := fun q hq hqf hql => by
    have hqf2 : s2.core.vals[q]?.getD 0#8 = 0xFF#8 := by
      rw [hs2_vals q hq, ite_eq_left (by omega), hqf]
    obtain ⟨m, hm, hmeq⟩ := (hw2.vals_false_iff q (hs2_cv ▸ hq)).mp hqf2
    obtain ⟨i, hi, hieq⟩ := (hpre.hw.vals_false_iff q hq).mp hqf
    have hlv := hs2_lvl i hi; dsimp only at hlv; rw [hieq, fullInv_var_xor1] at hlv
    exact ⟨m, hm, hmeq, by rw [hlv, ite_eq_left (by omega)]; exact hql⟩
  have hrsn_pre := hpre.rsn_pre
  have hl0 : jlvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat]) := by
    intro hj0; subst hj0; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      obtain ⟨m, hm, hmeq, hml0⟩ := h_s2_false _ hot_lt hot_f hot_lv
      have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [hmeq, fullInv_var_xor1]; omega
      exact entails_of_mem_or_false hent fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.elim (fun h => h ▸ Or.inl List.mem_cons_self) fun h =>
          Or.inr (h ▸ by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
    · rw [ite_eq_right hbin] at hrsn_pre; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      exact entails_of_mem_or_false (hw2.arena.entails rsn.toNat h1' h2') fun q hq => by
        have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
        rcases h4 q hq1 with rfl | ⟨hqf, hql⟩
        · exact Or.inl List.mem_cons_self
        · obtain ⟨m, hm, hmeq, hml⟩ := h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq)
            hqf hql
          have htr0 : (s2.core.lvl[(s2.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0
              := by rw [hmeq, fullInv_var_xor1]; omega
          exact Or.inr (by have hs := hw2.level0_sound m hm htr0; rwa [hmeq] at hs)
  have hrsn2 : 0 < jlvl → if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, ot]) ∧
        ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s2.core ∧
        fullArenaClauseGarbCore s2.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s2.core rsn.toNat,
          q = forced.toNat ∨ ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := by
    intro _; by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrsn_pre ⊢; obtain ⟨hot_lt, hent, hot_f, hot_lv⟩ := hrsn_pre
      exact ⟨hs2_cv ▸ hot_lt, hent, h_s2_false _ hot_lt hot_f hot_lv⟩
    · rw [ite_eq_right hbin] at hrsn_pre ⊢; obtain ⟨h1, h2, _, h4⟩ := hrsn_pre
      have h1' : rsn.toNat ∈ fullArenaClauseRefsCore s2.core := by
        simpa [fullArenaClauseRefsCore, hs2_ar, hs2_al] using h1
      have h2' : fullArenaClauseGarbCore s2.core rsn.toNat = false := by
        simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hs2_ar] using h2
      refine ⟨h1', h2', fun q hq => ?_⟩
      have hq1 : q ∈ fullArenaClauseLitsCore s1.core rsn.toNat := by
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hq
      exact (h4 q hq1).elim Or.inl fun ⟨hqf, hql⟩ =>
        Or.inr (h_s2_false q (hs2_cv ▸ hw2.arena.lits_lt _ h1' h2' q hq) hqf hql)
  have hrsn_mem2 : 0 < jlvl → (rsn &&& 0x80000000#32) = 0#32 →
      forced.toNat ∈ fullArenaClauseLitsCore s2.core rsn.toNat := fun _ hlg => by
    rw [ite_eq_right (fun h => absurd hlg h)] at hrsn_pre
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs2_ar] using hrsn_pre.2.2.1
  have hw3 := m5_chronoAssign_preserves_fullWitness_sameLvl hs2_len hw2 (hs2_cv ▸ hpre.forced_lt)
    hf_un (hs2_cl ▸ hjlvl_le) hpre.rsn_ne hl0 hrsn2 hrsn_mem2 (flags' := fl')
    (unassigned' := unass3) (unflushed' := s3.core.unflushed)
  have hj_z : (jlvlv.setWidth 32 = 0#32) ↔ jlvl = 0 := by
    rw [htr_eq]; constructor
    · intro h; simpa [bv32_ofNat_toNat hj_lt32] using congrArg BitVec.toNat h
    · intro h; simp [h]
  have hrsn_eq : (if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else rsn) =
      if jlvl = 0 then 0xFFFFFFFF#32 else rsn := by
    by_cases hj : jlvl = 0
    · rw [ite_eq_left (hj_z.mpr hj), ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj (hj_z.mp h)), ite_eq_right hj]
  fa_fast_steps
  exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (hs2_cv.trans hpre.cv_eq)
    (hs2_fu.trans hpre.fu_eq) (hs2_ws2.trans hpre.ws2_eq) hs2_dm (hs2_pr.trans hpre.prob_eq)
    hmarks3 hnd3 hext3 (fun _ h => by cases h) (fun h => by cases h)
    (fun _ => ⟨hw3, by dsimp [s3]; have := hpre.cl_le; omega⟩)
    (fun h => by cases h) (fun h => by cases h)
    (m5_fullMem_of_eq hm3 (by dsimp only [s3, rsn', v]; rw [hrsn_eq, htr_eq]) rfl)

private theorem m5_oneLit_bin_swap_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s s1 : FullState} {a b : BitVec 32}
    {la lb : BitVec 32} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (_hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : M5OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat)
    (hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat)
    (hmax : clvl = max la.toNat lb.toNat) (hne : la ≠ lb)
    (hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8)
    (hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : M5OneLitPost c F0 F_cur s R Q) :
    let forced := if la > lb then a else b
    let other := if la > lb then b else a
    let jlvl : Nat := if la > lb then lb.toNat else la.toNat
    ∀ nlvl : BitVec 64,
      (0 < s1.core.cur_level → jlvl < s1.core.cur_level →
        jlvl ≤ nlvl.toNat ∧ nlvl.toNat < s1.core.cur_level) →
      wp Γ Q X
        (Expr.call (as := [i64, i64]) "full_backtrack"
            (Arg.var c.hdr, Arg.var nlvl, ()) fun (_ : Tup Val []) =>
          Expr.let_ {
            sig := [i32, i32], code := OpCode.and i32,
            args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p_26 =>
          Expr.let_ {
            sig := [i32, i32], code := OpCode.or i32,
            args := (Arg.var p_26.fst, Arg.imm 2147483648#32, ()) } fun p_27 =>
          Expr.let_ {
            sig := [i64], code := OpCode.trunc 64 32,
            args := (Arg.var (BitVec.ofNat 64 jlvl), ()) } fun p_28 =>
          Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
            (Arg.var c.hdr, Arg.var forced, Arg.var p_27.fst, Arg.var p_28.fst, ())
            fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) m1 := by
  intro forced other jlvl nlvl hnlvl
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hobt.len1.core_ok.cur_vars_le
  have h2cv : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by have := hobt.cv_eq; omega
  have hjlt : jlvl < clvl := by
    dsimp only [jlvl]; split <;> rename_i hgt
    · have : lb.toNat < la.toNat := hgt; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp hgt
      have hneq : la.toNat ≠ lb.toNat := fun he => hne (BitVec.eq_of_toNat_eq he); omega
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (hobt.cl1_eq ▸ hobt.cl_pos) (hobt.cl1_eq ▸ hjlt)
  rw [hobt.cl1_eq] at hnl_lt
  c0_call hBt
  refine ⟨c, s1, R, rfl, hobt.len1, by
    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    fun h => by have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    hobt.hw1.trail_lits_lt, hm1, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hobt.cl1_eq]; omega
  have hw2' := hw2 F0 F_cur hobt.hw1.toFullOtfsWitnessInv (by rw [hobt.cl1_eq]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hobt.hw1.toFullOtfsWitnessInv⟩
  have hforced_lt : forced.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [forced]; split <;> assumption
  have hother_lt : other.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [other]; split <;> assumption
  have hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl := by
    dsimp only [forced]; split
    · have : lb.toNat < la.toNat := ‹la > lb›
      rw [hobt.lvl_keep _ ha_lt hfa (by omega), ← hla_val]; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp ‹¬ la > lb›
      rw [hobt.lvl_keep _ hb_lt hfb (by omega), ← hlb_val]; omega
  have hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    dsimp only [other, jlvl]; split
    · rw [hobt.lvl_keep _ hb_lt hfb (by rw [← hlb_val]; omega), hlb_val]
    · rw [hobt.lvl_keep _ ha_lt hfa (by rw [← hla_val]; omega), hla_val]
  have hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    dsimp only [other]; split
    · rw [hobt.vals_keep _ hb_lt (by rw [← hlb_val]; omega)]; exact hfb
    · rw [hobt.vals_keep _ ha_lt (by rw [← hla_val]; omega)]; exact hfa
  let bin_rsn := (other &&& 0x7FFFFFFF#32) ||| 0x80000000#32
  have hbin_p := bin_rsn_mask_props (l := other) (by have := hobt.cv_eq; have := hother_lt; omega)
  have hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]) := by
    dsimp only [forced, other]; split
    · exact hent
    · exact entails_of_mem_or_false hent fun l hl => Or.inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> simp)
  have hj_lt32 : jlvl < 2 ^ 32 := by
    have := Full.fullInv_max_vars_lt32 c; have := hobt.hw1.cur_level_le
    have := hobt.len1.core_ok.trail_end_le; have := hobt.cl1_eq; omega
  have hrsn_pre :
      if (bin_rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (bin_rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s1.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
        s1.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s1.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
      else
        bin_rsn.toNat ∈ fullArenaClauseRefsCore s1.core ∧
        fullArenaClauseGarbCore s1.core bin_rsn.toNat = false ∧
        forced.toNat ∈ fullArenaClauseLitsCore s1.core bin_rsn.toNat ∧
        ∀ q ∈ fullArenaClauseLitsCore s1.core bin_rsn.toNat,
          q = forced.toNat ∨ (s1.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (s1.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl) := by
    dsimp only [bin_rsn]; rw [ite_eq_left hbin_p.2.1, hbin_p.2.2]
    exact ⟨hother_lt, hent_fo, hother_f, Nat.le_of_eq hother_lvl⟩
  let hpre : M5OneLitTailPre c F0 F_cur s s1 cut1 clvl jlvl forced bin_rsn :=
    ⟨hobt.len1, hobt.hw1, hobt.marks1, hobt.nodup1, hobt.ext1, hobt.cl1_eq, hobt.cl_le,
      hobt.cv_eq, hobt.fuel_eq, hobt.ws2_eq, hobt.dm0, hobt.prob_eq, hforced_lt, hforced_lvl,
      hbin_p.1, hrsn_pre⟩
  fa_fast_steps_nogrp
  exact m5_oneLit_after_bt_assign_wp hAss hpre (bv64_ofNat_toNat (lt_trans hj_lt32 (by decide)))
    hj_lt32 hjl_le_nl hnl_lt hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hobt.dm0 rfl rfl
    rfl rfl rfl rfl hvals2 hlvl2 hw2' hm2 hQ

theorem m5_oneLit_bin_branch_wp (Γ : Env)
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : Full.FullLitMarksClear c s)
    (hnd : Full.FullArenaVarsNodup s) (hext : Full.FullExtScratchOk c s)
    (hcut_le : cut ≤ s.core.trail_end) (hconfl : Full.FullConflictOkCut F_cur cut s)
    (hbin : s.core.confl_type = 1#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : M5OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_m5_body (c.hdr, ()) m Q X := by
  have hmax32 := Full.fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_bt0 {cut1 clvl : Nat} {s1 : FullState} {m1 : Mem 64}
      (hobt : M5OneLitBtInv c F0 F_cur s s1 cut1 clvl)
      (hm1 : (FullMem c s1 ⋆ R) m1) : Q (0#64, ()) m1 :=
    hQ 0#64 s1 m1 hobt.len1 (Or.inl rfl) hobt.cv_eq hobt.fuel_eq hobt.ws2_eq hobt.dm0 hobt.prob_eq
      hobt.marks1 hobt.nodup1 hobt.ext1 (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨cut1, hobt.cut1_le, hobt.hw1, hobt.cl1_eq ▸ hobt.cl_pos,
        hobt.cl1_eq ▸ hobt.cl_le, hobt.confl1⟩) hm1
  have hconfl0 : Full.FullConflictOkCut F_cur cut s := hconfl
  have hbin_cf : s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
      s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
    rcases hconfl.1 with ⟨_, h0, h1, fa, fb, he⟩ | ⟨hbad, _⟩
    · exact ⟨h0, h1, fa, fb, he⟩
    · exact absurd (hbin.symm.trans hbad) (by decide)
  obtain ⟨h0lt, h1lt, hfa, hfb, hent⟩ := hbin_cf
  unfold Func.wp full_one_lit_confl_m5_body
  fa_fast_steps_nogrp
  · have h0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have h1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a := s.core.confl_lit0.setWidth 32; let b := s.core.confl_lit1.setWidth 32
    have ha_eq : a.toNat = s.core.confl_lit0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h0_32]
    have hb_eq : b.toNat = s.core.confl_lit1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1_32]
    have ha_bd : (BitVec.setWidth 64 (a >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, ha_eq]; omega
    have hb_bd : (BitVec.setWidth 64 (b >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, hb_eq]; omega
    let la := s.core.lvl[(BitVec.setWidth 64 (a >>> 1)).toNat]'ha_bd
    let lb := s.core.lvl[(BitVec.setWidth 64 (b >>> 1)).toNat]'hb_bd
    have hla_64 : la.setWidth 64 = BitVec.ofNat 64 la.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hlb_64 : lb.setWidth 64 = BitVec.ofNat 64 lb.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [la]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (getElem_eq_of_idx (by rw [bv_c0_zext32_64, bv32_lshr_1]))
    have hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [lb]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (getElem_eq_of_idx (by rw [bv_c0_zext32_64, bv32_lshr_1]))
    have hla_le : la.toNat ≤ s.core.cur_level := by
      obtain ⟨ma, hma, hma_eq⟩ := (hw.vals_false_iff _ h0lt).mp hfa
      have h1 := hw.lvl_le ma hma; rw [hma_eq, fullInv_var_xor1, ← ha_eq] at h1; omega
    have hlb_le : lb.toNat ≤ s.core.cur_level := by
      obtain ⟨mb, hmb, hmb_eq⟩ := (hw.vals_false_iff _ h1lt).mp hfb
      have h1 := hw.lvl_le mb hmb; rw [hmb_eq, fullInv_var_xor1, ← hb_eq] at h1; omega
    fa_fast_steps_nogrp
    refine wp_join_group (ts := [i64]) (fun (clvlv, ()) m0 =>
        m0 = m ∧ clvlv = BitVec.ofNat 64 (max la.toNat lb.toNat)) ?_ ?_
    · rintro _ ⟨clvlv, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
      let clvl := max la.toNat lb.toNat
      have hcl_le : clvl ≤ s.core.cur_level := Nat.max_le.mpr ⟨hla_le, hlb_le⟩
      fa_fast_steps_nogrp
      · have hcl0 : clvl = 0 := ofNat64_eq_zero (by omega) ‹_›
        have hl0a : (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        have hl0b : (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact hQ 20#64 s m0 hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks hnd
          hext (fun _ h => by cases h)
          (fun _ => ⟨unsat_of_level0_bin_conflict (m5_canonCut_to_anaCut hw) h0lt h1lt
            (ha_eq ▸ hl0a) (hb_eq ▸ hl0b) hfa hfb hent, rfl⟩)
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm
      · have hcl_pos : 0 < clvl := ofNat64_pos ‹_›
        have hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
            (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
            (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl := fun l hl => by
          rcases hl with ⟨_, rfl | rfl⟩ | ⟨hbad, _⟩
          · rw [← ha_eq, ← hla_val]; exact Nat.le_max_left _ _
          · rw [← hb_eq, ← hlb_val]; exact Nat.le_max_right _ _
          · exact absurd hbin hbad
        refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, M5OneLitBtInv c F0 F_cur s s1 cut1 clvl ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
          fa_fast_steps_nogrp
          · exact hret_bt0 hobt hm1
          · have hne : la ≠ lb := ‹_›
            refine wp_join_group (ts := [i32]) (fun (fc, ()) mf =>
                mf = m1 ∧ fc = if la > lb then a else b) ?_ ?_
            · rintro _ ⟨fc, ⟨⟩⟩ mf ⟨rfl, rfl⟩
              refine wp_join_group (ts := [i32]) (fun (oc, ()) mo =>
                  mo = mf ∧ oc = if la > lb then b else a) ?_ ?_
              · rintro _ ⟨oc, ⟨⟩⟩ mo ⟨rfl, rfl⟩
                refine wp_join_group (ts := [i64]) (fun (jc, ()) mj =>
                    mj = mo ∧ jc = BitVec.ofNat 64
                      (if la > lb then lb.toNat else la.toNat)) ?_ ?_
                · rintro _ ⟨jc, ⟨⟩⟩ mj ⟨rfl, rfl⟩
                  fa_fast_steps_nogrp; c0_call hDet
                  refine ⟨c, s1, R, rfl, hobt.len1, by
                    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le
                    have := hobt.len1.core_ok.cur_vars_le; omega,
                    hm1, fun nlvl _ hnlvl => ?_⟩
                  have hjl_lt64 : (if la > lb then lb.toNat else la.toNat) < 2 ^ 64 := by
                    split <;> omega
                  exact m5_oneLit_bin_swap_if hDet hBt hAss hobt (ha_eq ▸ h0lt) (hb_eq ▸ h1lt)
                    hla_val hlb_val rfl hne (ha_eq ▸ hfa) (hb_eq ▸ hfb)
                    (ha_eq ▸ hb_eq ▸ hent) hm1 hQ nlvl
                    (by simpa only [bv64_ofNat_toNat hjl_lt64] using hnlvl)
                · intro Jj hJj; fa_fast_steps
                  · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_left hgt]; exact hlb_64⟩
                  · have hng : ¬ la > lb := fun h =>
                      (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                        (BitVec.lt_def.mp h)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_right hng]; exact hla_64⟩
              · intro Jo hJo; fa_fast_steps
                · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                  exact hJo _ _ ⟨rfl, by simp [hgt, b]⟩
                · have hng : ¬ la > lb := fun h =>
                    (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                      (BitVec.lt_def.mp h)
                  exact hJo _ _ ⟨rfl, by simp [hng, a]⟩
            · intro Jf hJf; fa_fast_steps
              · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                exact hJf _ _ ⟨rfl, by simp [hgt, a]⟩
              · have hng : ¬ la > lb := fun h =>
                  (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat) (BitVec.lt_def.mp h)
                exact hJf _ _ ⟨rfl, by simp [hng, b]⟩
        · intro Jbt hJbt; fa_fast_steps_nogrp
          · have hlt_cl : s.core.cur_level > clvl := by
              have hb : clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; exact hb
            c0_call hBt
            refine ⟨c, s, R, rfl, hlen, hcl_lt64,
              fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
                          rw [bv64_ofNat_toNat (by omega)]; omega,
              hw.trail_lits_lt, hm, ?_⟩
            have hcl_lt64' : clvl < 2 ^ 64 := by omega
            dsimp only
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
              hvl1 _ hw1 hm1
            have hcl1_eq : cl1 = clvl := by
              rw [hcl1, bv64_ofNat_toNat hcl_lt64']; omega
            obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
            obtain ⟨cut1, hobt⟩ := m5_oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inr ⟨hlt_cl, hlen1, hcl1_eq,
                rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                fun l hl => by have h := hvs1 l hl; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                fun i hi => by have h := hls1 i hi; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                hw1 F0 F_cur hw.toFullOtfsWitnessInv (by rw [bv64_ofNat_toNat hcl_lt64']; omega)⟩)
            exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
          · have hle_cl : s.core.cur_level ≤ clvl := by
              have hb : ¬ clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; omega
            obtain ⟨cut1, hobt⟩ := m5_oneLit_after_bt hlen hdm hw hmarks hnd hext hcut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
            exact hJbt () m0 ⟨s, cut1, hobt, hm⟩
    · intro Jmx hJmx
      have ha_i : s.core.confl_lit0.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (a >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, ha_eq, Nat.mod_eq_of_lt h0_32]
      have hb_i : s.core.confl_lit1.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (b >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hb_eq, Nat.mod_eq_of_lt h1_32]
      fa_fast_steps
      · have hle : lb.toNat ≤ la.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          dsimp only [la, lb]
          rwa [getElem_eq_of_idx (hj := hb_bd) hb_i, getElem_eq_of_idx (hj := ha_bd) ha_i] at hc
        refine hJmx _ _ ⟨rfl, ?_⟩; rw [Nat.max_eq_left hle]; exact hla_64
      · have hlt : la.toNat < lb.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat <
              (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat :=
            Nat.lt_of_not_le ‹_›
          dsimp only [la, lb]
          rwa [getElem_eq_of_idx (hj := ha_bd) ha_i, getElem_eq_of_idx (hj := hb_bd) hb_i] at hc
        refine hJmx _ _ ⟨rfl, ?_⟩; rw [Nat.max_eq_right (Nat.le_of_lt hlt)]; exact hlb_64
  · exfalso; exact ‹¬ s.core.confl_type = 1› (by simp [hbin])
  · exfalso; exact ‹¬ s.core.confl_type = 1› (by simp [hbin])

/-! ## 2. Large-Branch Scan, Tail Execution, Headroom & 2WL Swap/Push Helpers -/

def M5OneLitScanInv (s : FullState) (cref forcedv : BitVec 32)
    (csz_val i : Nat) (clvlv jlvlv cntv : BitVec 64) : Prop :=
  i ≤ csz_val ∧ clvlv.toNat ≤ s.core.cur_level ∧ jlvlv.toNat ≤ s.core.cur_level ∧
  cntv.toNat ≤ i ∧
  (i = 0 → clvlv = 0#64 ∧ jlvlv = 0#64 ∧ cntv = 0#64 ∧ forcedv = 0xFFFFFFFF#32) ∧
  (0 < i → 1 ≤ cntv.toNat ∧
    (∀ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat ≤ clvlv.toNat) ∧
    (∃ q < i, (s.core.lvl[(s.core.arena[cref.toNat + 3 + q]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat = clvlv.toNat)) ∧
  (0 < i → cntv = 1#64 → ∃ q_f < i,
    forcedv = s.core.arena[cref.toNat + 3 + q_f]?.getD 0#32 ∧
    (s.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvlv.toNat ∧
    (0 < clvlv.toNat → jlvlv.toNat < clvlv.toNat) ∧
    ∀ q' < i, q' ≠ q_f →
      (s.core.lvl[(s.core.arena[cref.toNat + 3 + q']?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ≤ jlvlv.toNat)

theorem m5_oneLit_scan_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
    {csz_val i : Nat} (hlen : s.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcap : c.arena_cap < 2 ^ 31 - 1) (hcsz_bd : cref.toNat + 3 + csz_val ≤ s.core.arena_len)
    (hilt : i < csz_val) (hl_lt : (s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat <
      2 * s.core.cur_vars) (hcref_eq : cref = s.core.confl_ref.setWidth 32) :
    let li := s.core.arena[cref.toNat + 3 + i]'(by
      have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega)
    let ll : BitVec 64 := (s.core.lvl[li.toNat / 2]?.getD 0#32).setWidth 64
    ∃ (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
        s.core.arena.length)
      (hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length),
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat = cref.toNat + 3 + i ∧
      s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li ∧
      ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat ∧
      s.core.arena[(cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd = li ∧
      ((s.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i).setWidth 64).toNat]'hz_bd >>> 1).setWidth 64).toNat <
        s.core.lvl.length ∧
      (s.core.arena[(s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
        i % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s.core.lvl.length ∧
      (∀ pf1 pf2, BitVec.setWidth 64 (s.core.lvl[(BitVec.setWidth 64
        (s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 >>> 1)).toNat]'pf2) = ll) := by
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hcr_i_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat =
      cref.toNat + 3 + i := by
    have : cref.toNat < 2 ^ 31 - 1 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat (BitVec.ofNat 32 i) (by decide), bv32_ofNat_toNat (by omega)]
    simp only [BitVec.reduceToNat]; omega
  have hcr_eq : cref.toNat = s.core.confl_ref.toNat % 2 ^ 32 := by
    rw [hcref_eq, BitVec.toNat_setWidth]
  have hc_idx : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 = cref.toNat + 3 + i := by
    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, ← hcr_eq]; omega
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
      s.core.arena.length := by rw [hcr_i_bd]; omega
  have hc_bd : (s.core.confl_ref.toNat % 2 ^ 32 + BitVec.toNat (3 : BitVec 64) +
      i % 2 ^ 32) % 2 ^ 64 < s.core.arena.length := by rw [hc_idx]; omega
  intro li ll
  have hli_get : s.core.arena[cref.toNat + 3 + i]?.getD 0#32 = li := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hll_val : ll.toNat = (s.core.lvl[(s.core.arena[cref.toNat + 3 + i]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat := by
    dsimp only [ll, li]; rw [hli_get, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (BitVec.isLt _) (by decide)
  have hli_idx : ∀ pf, s.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = li := fun _ => getElem_eq_of_idx hcr_i_bd
  have hli_var : li.toNat / 2 < s.core.cur_vars := by
    rw [← hli_get]; exact Nat.div_lt_of_lt_mul hl_lt
  have hbd_lvl : li.toNat / 2 < s.core.lvl.length := by
    rw [hlvl_len]; exact Nat.lt_of_lt_of_le hli_var hcv_le
  refine ⟨hz_bd, hc_bd, hcr_i_bd, hli_get, hll_val, hli_idx hz_bd, ?_, ?_, fun pf1 pf2 => ?_⟩
  · rw [bv_c0_zext32_64, bv32_lshr_1, hli_idx hz_bd]; exact hbd_lvl
  · rw [getElem_eq_of_idx hc_idx]; exact hbd_lvl
  · dsimp only [ll]; congr 1; rw [List.getElem?_eq_getElem hbd_lvl, Option.getD_some]
    exact getElem_eq_of_idx (by
      rw [bv_c0_zext32_64, bv32_lshr_1]
      have ha_li : s.core.arena[((s.core.confl_ref.setWidth 32).setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'pf1 = li :=
        (getElem_eq_of_idx (hj := hz_bd)
          (by rw [← hcref_eq, show (3 : BitVec 64) = 3#64 from rfl])).trans (hli_idx hz_bd)
      rw [ha_li])

def m5OneLitTailExpr (hdr jlvlv : BitVec 64) (forcedv cref : BitVec 32) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64, i64]) "full_det_new_level" (Arg.var hdr, Arg.var jlvlv, ())
    fun (p_29 : Tup Val [i64]) =>
      Expr.call (as := [i64, i64]) "full_backtrack" (Arg.var hdr, Arg.var p_29.fst, ())
        fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (.trunc 64 32) (Arg.var jlvlv, ())) fun p_31 =>
            Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
              (Arg.var hdr, Arg.var forcedv, Arg.var cref, Arg.var p_31.fst, ())
              fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())

theorem m5_oneLit_large_tail_exec_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s sb : FullState}
    {cref forcedv : BitVec 32} {jlvlv : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]}
    {X : XPost} {mb : Mem 64}
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt_le : clvl ≤ s.core.cur_level) (hcl_pos : 0 < clvl) (hjl_lt : jlvlv.toNat < clvl)
    (hcr32 : cref.toNat < 2 ^ 31 - 1)
    (hbref : cref.toNat ∈ fullArenaClauseRefsCore sb.core)
    (hbng : fullArenaClauseGarbCore sb.core cref.toNat = false)
    (hbfmem : forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat)
    (hbfoth : ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
      q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
        (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat))
    (hblen : sb.LengthsOk c) (hbw : Full.FullWitnessCutInv c F0 F_cur cut1 sb.core)
    (hbmk : Full.FullLitMarksClear c sb) (hbnd : Full.FullArenaVarsNodup sb)
    (hbext : Full.FullExtScratchOk c sb) (hbcl : sb.core.cur_level = clvl)
    (hbcv : sb.core.cur_vars = s.core.cur_vars) (hbfu : sb.core.fuel = s.core.fuel)
    (hbws2 : sb.scratch.work_stk2 = s.scratch.work_stk2) (hbdm : sb.core.dense_mode = 0#64)
    (hbpr : sb.core.probing = s.core.probing)
    (hf_lvl_sb : (sb.core.lvl[forcedv.toNat / 2]?.getD 0#32).toNat = clvl)
    (hf_lt : forcedv.toNat < 2 * s.core.cur_vars)
    (hmb : (FullMem c sb ⋆ R) mb) (hQ : M5OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X (m5OneLitTailExpr c.hdr jlvlv forcedv cref) mb := by
  have hj_lt_cl : jlvlv.toNat < sb.core.cur_level := by rw [hbcl]; exact hjl_lt
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold m5OneLitTailExpr; c0_call hDet
  refine ⟨c, sb, R, rfl, hblen, by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega,
    hmb, fun nlvl _ hnlvl => ?_⟩
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (by omega) hj_lt_cl; rw [hbcl] at hnl_lt
  c0_call hBt
  refine ⟨c, sb, R, rfl, hblen, by
    have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
    have := hblen.core_ok.cur_vars_le; omega,
    fun h => by have := hbw.cur_level_le; have := hblen.core_ok.trail_end_le
                have := hblen.core_ok.cur_vars_le; omega,
    hbw.trail_lits_lt, hmb, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hbcl]; omega
  have hw2' := hw2 F0 F_cur hbw.toFullOtfsWitnessInv (by rw [hbcl]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hbw.toFullOtfsWitnessInv⟩
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (Nat.lt_trans hcr32 (by omega))).2.2
  have hrsn_pre :
      if (cref &&& 0x80000000#32) ≠ 0#32 then
        let ot := (cref &&& 0x7FFFFFFF#32).toNat
        ot < 2 * sb.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forcedv.toNat, ot]) ∧
        sb.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (sb.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvlv.toNat
      else
        cref.toNat ∈ fullArenaClauseRefsCore sb.core ∧
        fullArenaClauseGarbCore sb.core cref.toNat = false ∧
        forcedv.toNat ∈ fullArenaClauseLitsCore sb.core cref.toNat ∧
        ∀ q ∈ fullArenaClauseLitsCore sb.core cref.toNat,
          q = forcedv.toNat ∨ (sb.core.vals[q]?.getD 0#8 = 0xFF#8 ∧
            (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvlv.toNat) := by
    rw [ite_eq_right (fun h => absurd hcref_lg h)]; exact ⟨hbref, hbng, hbfmem, hbfoth⟩
  let hpre : M5OneLitTailPre c F0 F_cur s sb cut1 clvl jlvlv.toNat forcedv cref :=
    ⟨hblen, hbw, hbmk, hbnd, hbext, hbcl, hobt_le, hbcv, hbfu, hbws2, hbdm, hbpr,
      hbcv ▸ hf_lt, hf_lvl_sb, hcref_ne, hrsn_pre⟩
  fa_fast_steps_nogrp
  exact m5_oneLit_after_bt_assign_wp hAss hpre rfl
    (by have := Full.fullInv_max_vars_lt32 c; have := hbw.cur_level_le
        have := hblen.core_ok.trail_end_le; omega)
    hjl_le_nl hnl_lt hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hbdm rfl rfl rfl rfl rfl
    rfl hvals2 hlvl2 hw2' hm2 hQ

/-- Shared WP for watch-stack headroom pre-check in `full_one_lit_confl_m5` (`ret 2#64` on
post-defrag OOM). -/
theorem m5_wstack_ensure2_ret2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Jd : Cont []}
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hmw : ModeWatchesInv F_cur s.core) (hm : (FullMem c s ⋆ R) m)
    (hOom : ∀ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
      (wu_i : BitVec 64) (wso_i : List (BitVec 32)) (ml_o : Mem 64),
      s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } →
      s_i.scratch = { s.scratch with wsort := wso_i } →
      s_i.LengthsOk c → ModeWatchesInv F_cur s_i.core →
      (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o →
      Q (2#64, ()) ml_o)
    (hJd : ∀ xs ml_d,
      (∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧
        (FullMem c s_d ⋆ R) ml_d) →
      Jd xs ml_d) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_49 =>
       Expr.load i64 (Arg.var p_49.fst) fun ld =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_50 =>
       Expr.load i64 (Arg.var p_50.fst) fun ld_9 =>
       Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_9, ())) fun p_51 =>
       Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_51.fst, Arg.imm 2, ())) fun p_52 =>
       Expr.jnz (Arg.var p_52.fst)
         (Expr.group (fun (_ : Tup Cont [[]]) =>
             Blocks.cons (fun (_ : Tup Val []) =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_54 =>
               Expr.load i64 (Arg.var p_54.fst) fun ld =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_55 =>
               Expr.load i64 (Arg.var p_55.fst) fun ld_10 =>
               Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_10, ())) fun p_56 =>
               Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                 (Arg.var p_56.fst, Arg.imm 2, ())) fun p_57 =>
               Expr.jnz (Arg.var p_57.fst)
                 (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                    (Expr.ret (Arg.imm 2#64, ())))
                 (Expr.jump Jd ())) Blocks.nil)
           fun Js =>
           Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_53 =>
           Expr.load i64 (Arg.var p_53.fst) fun ld =>
           Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_54 =>
           Expr.jnz (Arg.var p_54.fst)
             (Expr.call (rs := [i64]) (as := [i64]) (bs := [])
               "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
               Expr.jump Js.fst ())
             (Expr.jump Js.fst ()))
         (Expr.jump Jd ())) m := by
  have hcv_lt32 : s.core.cur_vars < 2 ^ 32 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  have hwcap_lt64 : c.wcap < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at *; omega
  have hwlen_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hlay0 : Full.WatchStackLayout s.core := by
    have h := hmw; unfold ModeWatchesInv at h
    simp only [hdm, ↓reduceIte] at h; exact h.layout
  fa_fast_steps_nogrp
  · refine wp_join_group (ts := []) (fun () ml_i =>
      ∃ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
        (wu_i : BitVec 64) (wso_i : List (BitVec 32)),
        s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } ∧
        s_i.scratch = { s.scratch with wsort := wso_i } ∧
        s_i.LengthsOk c ∧ ModeWatchesInv F_cur s_i.core ∧ (FullMem c s_i ⋆ R) ml_i) ?_ ?_
    · rintro _ ⟨⟩ ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
      have hwli_le : s_i.core.wlen ≤ c.wcap := hlen_i.core_ok.wlen_le
      fa_fast_steps
      · exact hOom s_i wv_i ws_i wl_i wu_i wso_i _ hsi_c hsi_sc hlen_i hmw_i (by assumption)
      · exact hJd () ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
    · intro Ji hJi
      fa_fast_steps_nogrp
      · c0_call hDefrag
        refine ⟨c, s, R, rfl, hlen, hlay0, hm,
          fun wv_i ws_i wl_i wso_i ml_i hlen_i hlay_i _ hpres hm_i => ?_⟩
        obtain ⟨s_i, hsi_c, hsi_sc, hm_i'⟩ :=
          m5_otfs_opaque_state (s_old := { s with
            core := { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            scratch := { s.scratch with wsort := wso_i } })
            { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            { s.scratch with wsort := wso_i } hm_i rfl rfl
        have hmw_i : ModeWatchesInv F_cur s_i.core := by
          rw [hsi_c]
          exact Full.fullWstackDefrag_preserves_modeWatchesInv hmw hlay_i rfl rfl
            (fun _ hr => hr) hpres
        have hlen_i' : s_i.LengthsOk c :=
          ⟨by rw [hsi_c]; exact hlen_i.core_ok, by rw [hsi_sc]; exact hlen_i.scratch_ok⟩
        exact hJi () ml_i ⟨s_i, wv_i, ws_i, wl_i, 0#64, wso_i, hsi_c, hsi_sc, hlen_i', hmw_i,
          hm_i'⟩
      · exact hJi () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
          s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩
  · exact hJd () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
      s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩

theorem m5_oneLit_swap_arena_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut1 : Nat} {s_in : FullState} {cref : BitVec 32} {csz_val i j : Nat}
    (hlen : s_in.LengthsOk c) (hw : Full.FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hnd : Full.FullArenaVarsNodup s_in) (hext : Full.FullExtScratchOk c s_in)
    (href : cref.toNat ∈ fullArenaClauseRefsCore s_in.core)
    (hng : fullArenaClauseGarbCore s_in.core cref.toNat = false)
    (hsz : fullArenaClauseSizeCore s_in.core cref.toNat = csz_val)
    (hi : i < csz_val) (hj : j < csz_val) (li lj : BitVec 32)
    (hli : li = s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32)
    (hlj : lj = s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32) :
    let ar' := (s_in.core.arena.set (cref.toNat + 3 + i) lj).set (cref.toNat + 3 + j) li
    let s' : FullState := { s_in with core := { s_in.core with arena := ar' } }
    s'.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut1 s'.core ∧
    Full.FullArenaVarsNodup s' ∧ Full.FullExtScratchOk c s' ∧
    fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore s'.core ∧
    fullArenaClauseGarbCore s'.core cref.toNat = false ∧
    fullArenaClauseSizeCore s'.core cref.toNat = csz_val ∧
    (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
  intro ar' s'
  have har_len := hlen.core_ok.arena_len_arr
  obtain ⟨hw', hrefs', hsz', hng', hperm', hother'⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen.core_ok (m5_canonCut_to_anaCut hw) href (i := i)
      (j := j) (by rw [hsz]; exact hi) (by rw [hsz]; exact hj)
  have har_sym : (s_in.core.arena.set (cref.toNat + 3 + i)
      (s_in.core.arena[cref.toNat + 3 + j]?.getD 0#32)).set (cref.toNat + 3 + j)
      (s_in.core.arena[cref.toNat + 3 + i]?.getD 0#32) = ar' := by
    dsimp only [ar']; rw [← hli, ← hlj]
  have hw_s' : Full.FullWitnessCutInv c F0 F_cur cut1 s'.core :=
    m5_anaCut_to_canonCut (by simpa only [s', ← har_sym] using hw') hw.cut_le
  have hrefs_s' : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s_in.core := by
    simpa only [s', ← har_sym] using hrefs'
  have hperm_s' : (fullArenaClauseLitsCore s'.core cref.toNat).Perm
      (fullArenaClauseLitsCore s_in.core cref.toNat) := by
    simpa only [s', ← har_sym] using hperm'
  have hsz_s' : fullArenaClauseSizeCore s'.core cref.toNat = csz_val := by
    rw [show fullArenaClauseSizeCore s'.core cref.toNat =
      fullArenaClauseSizeCore s_in.core cref.toNat from by simpa only [s', ← har_sym] using hsz',
      hsz]
  have hng_s' : fullArenaClauseGarbCore s'.core cref.toNat = false := by
    simpa only [s', ← har_sym, hng] using hng'
  have hnd_s' : Full.FullArenaVarsNodup s' := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs_s'] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm_s'.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
    · have ho := hother' r hr hrc; change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [show fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s_in.core r from by
        simpa only [s', ← har_sym] using ho.2.2]
      change fullArenaClauseGarbCore s'.core r = false at hngr
      simp only [s', ← har_sym] at hngr; rw [ho.2.1] at hngr; exact hnd r hr hngr
  exact ⟨⟨{ hlen.core_ok with arena_len_arr := by simp [s', ar', har_len] }, hlen.scratch_ok⟩,
    hw_s', hnd_s', ⟨fun k hk => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs_s']; exact hext.1 k hk, hext.2⟩,
    hrefs_s', by rw [hrefs_s']; exact href, hng_s', hsz_s', hperm_s'⟩

theorem m5_oneLit_swap_push_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl pos_n hp_n csz_val : Nat} {s s_in : FullState}
    {cref lit_pos high_lit : BitVec 32} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {Js_out : Cont []} {m_in : Mem 64}
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hlen_in : s_in.LengthsOk c) (hw_in : Full.FullWitnessCutInv c F0 F_cur cut1 s_in.core)
    (hmk_in : Full.FullLitMarksClear c s_in) (hnd_in : Full.FullArenaVarsNodup s_in)
    (hext_in : Full.FullExtScratchOk c s_in)
    (hbin : s.core.confl_type ≠ 1#64)
    (hcr32 : cref.toNat < 2 ^ 31 - 1) (hcsz_ge3 : 3 ≤ csz_val)
    (hpos_lt2 : pos_n < 2) (hhp_lt : hp_n < csz_val) (hhp_ne : hp_n ≠ pos_n)
    (hcsz_bd : cref.toNat + 3 + csz_val ≤ s_in.core.arena_len)
    (hcref_in : cref.toNat ∈ fullArenaClauseRefsCore s_in.core)
    (hng_in : fullArenaClauseGarbCore s_in.core cref.toNat = false)
    (hsz_in : fullArenaClauseSizeCore s_in.core cref.toNat = csz_val)
    (hlit_pos : lit_pos = s_in.core.arena[cref.toNat + 3 + pos_n]?.getD 0#32)
    (hhigh : high_lit = s_in.core.arena[cref.toNat + 3 + hp_n]?.getD 0#32)
    (hhi_lt : high_lit.toNat < 2 * s_in.core.cur_vars)
    (h_stat_in : s_in.core.cur_vars = s.core.cur_vars ∧ s_in.core.cur_level = clvl ∧
      s_in.core.fuel = s.core.fuel ∧ s_in.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s_in.core.dense_mode = 0#64 ∧ s_in.core.probing = s.core.probing ∧
      s_in.core.vals = s_in.core.vals ∧ s_in.core.lvl = s_in.core.lvl ∧
      s_in.core.trail_end = s_in.core.trail_end)
    (h_confl_eq : ∀ q, q ∈ fullArenaClauseLitsCore s_in.core cref.toNat ↔
      q ∈ fullArenaClauseLits s s.core.confl_ref.toNat)
    (hm_in : (FullMem c s_in ⋆ R) m_in) (hQ : M5OneLitPost c F0 F_cur s R Q)
    (hJs : ∀ mb,
      (∃ s_out : FullState,
        s_out.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut1 s_out.core ∧
        Full.FullLitMarksClear c s_out ∧ Full.FullArenaVarsNodup s_out ∧
        Full.FullExtScratchOk c s_out ∧
        s_out.core.cur_vars = s.core.cur_vars ∧ s_out.core.cur_level = clvl ∧
        s_out.core.fuel = s.core.fuel ∧ s_out.scratch.work_stk2 = s.scratch.work_stk2 ∧
        s_out.core.dense_mode = 0#64 ∧ s_out.core.probing = s.core.probing ∧
        s_out.core.vals = s_in.core.vals ∧ s_out.core.lvl = s_in.core.lvl ∧
        s_out.core.trl = s_in.core.trl ∧
        s_out.core.trail_end = s_in.core.trail_end ∧
        s_out.core.arena_len = s_in.core.arena_len ∧
        s_out.core.confl_type = s_in.core.confl_type ∧
        s_out.core.confl_ref = s_in.core.confl_ref ∧
        cref.toNat ∈ fullArenaClauseRefsCore s_out.core ∧
        fullArenaClauseGarbCore s_out.core cref.toNat = false ∧
        fullArenaClauseSizeCore s_out.core cref.toNat = csz_val ∧
        (∀ q, q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔
          q ∈ fullArenaClauseLits s s.core.confl_ref.toNat) ∧
        (FullMem c s_out ⋆ R) mb) →
      Js_out () mb) :
    let posv := BitVec.ofNat 32 pos_n
    let hpv := BitVec.ofNat 32 hp_n
    wp Γ Q X
      (Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var hpv, Arg.imm 1, ())) fun p_41 =>
       Expr.jnz (Arg.var p_41.fst)
         (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_42 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_42.fst, Arg.imm 3, ())) fun p_43 =>
          Expr.let_ (Op.mk (.xor i32) (Arg.var posv, Arg.imm 1, ())) fun p_44 =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_44.fst, ())) fun p_45 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_43.fst, Arg.var p_45.fst, ())) fun p_46 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p_46.fst, Arg.imm 4, ())) fun p_47 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_47.fst, ())) fun p_48 =>
          Expr.load i32 (Arg.var p_48.fst) fun ld_8 =>
          Expr.group (fun (_ : Tup Cont [[]]) =>
            Blocks.cons (fun (_ : Tup Val []) =>
              Expr.let_ (Op.mk (.and i32) (Arg.var ld_8, Arg.imm 2147483647, ())) fun p_50 =>
              Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                "full_watch_push"
                (Arg.var c.hdr, Arg.var high_lit, Arg.var p_50.fst, Arg.var cref,
                  Arg.imm 2, ()) fun p_51 =>
              Expr.jnz (Arg.var p_51.fst)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_52 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var p_52.fst, Arg.imm 3, ())) fun p_53 =>
                 Expr.let_ (Op.mk (.zext 32 64) (Arg.var posv, ())) fun p_54 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var p_53.fst, Arg.var p_54.fst, ())) fun p_55 =>
                 Expr.let_ (Op.mk (.mul i64) (Arg.var p_55.fst, Arg.imm 4, ())) fun p_56 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_56.fst, ())) fun p_57 =>
                 Expr.store (t := i32) (Arg.var high_lit) (Arg.var p_57.fst)
                   (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_58 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var p_58.fst, Arg.imm 3, ())) fun p_59 =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var hpv, ())) fun p_60 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var p_59.fst, Arg.var p_60.fst, ()))
                      fun p_61 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_61.fst, Arg.imm 4, ())) fun p_62 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_62.fst, ()))
                      fun p_63 =>
                    Expr.store (t := i32) (Arg.var lit_pos) (Arg.var p_63.fst)
                      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
                        (Arg.var c.hdr, Arg.var lit_pos, Arg.var cref, ()) fun _ =>
                        Expr.jump Js_out ())))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                 Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                   (Expr.ret (Arg.imm 2, ())))
              ) Blocks.nil) fun _Js =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_49 =>
            Expr.load i64 (Arg.var p_49.fst) fun ld =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_50 =>
            Expr.load i64 (Arg.var p_50.fst) fun ld_9 =>
            Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_9, ())) fun p_51 =>
            Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
              (Arg.var p_51.fst, Arg.imm 2, ())) fun p_52 =>
            Expr.jnz (Arg.var p_52.fst)
              (Expr.group (fun (_ : Tup Cont [[]]) =>
                  Blocks.cons (fun (_ : Tup Val []) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_54 =>
                    Expr.load i64 (Arg.var p_54.fst) fun ld =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_55 =>
                    Expr.load i64 (Arg.var p_55.fst) fun ld_10 =>
                    Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_10, ())) fun p_56 =>
                    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                      (Arg.var p_56.fst, Arg.imm 2, ())) fun p_57 =>
                    Expr.jnz (Arg.var p_57.fst)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                       Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                         (Expr.ret (Arg.imm 2, ())))
                      (Expr.jump _Js.fst ())) Blocks.nil)
                fun Js =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_53 =>
                Expr.load i64 (Arg.var p_53.fst) fun ld =>
                Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                  (Arg.var ld, Arg.imm 0, ())) fun p_54 =>
                Expr.jnz (Arg.var p_54.fst)
                  (Expr.call (rs := [i64]) (as := [i64]) (bs := [])
                    "full_wstack_defrag" (Arg.var c.hdr, ()) fun _ => Expr.jump Js.fst ())
                  (Expr.jump Js.fst ()))
              (Expr.jump _Js.fst ()))
         (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 3, ())) fun p =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var posv, ())) fun p_42 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.var p_42.fst, ())) fun p =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
          Expr.store (t := i32) (Arg.var high_lit) (Arg.var p.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 3, ())) fun p =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var hpv, ())) fun p_43 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.var p_43.fst, ())) fun p =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
             Expr.store (t := i32) (Arg.var lit_pos) (Arg.var p.fst)
               (Expr.jump Js_out ())))) m_in := by
  intro posv hpv
  obtain ⟨hcv_in, hcl_in, hfu_in, hws2_in, hdm_in, hpr_in, _, _, _⟩ := h_stat_in
  have har_len_in := hlen_in.core_ok.arena_len_arr
  have har_le_in := hlen_in.core_ok.arena_len_le
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have har_in_cap : s_in.core.arena.length = c.arena_cap := har_len_in
  have hcr_pos_z : (cref.setWidth 64 + 3 + posv.setWidth 64).toNat = cref.toNat + 3 + pos_n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat posv (by decide), bv32_ofNat_toNat (by omega),
      show (3 : BitVec 64).toNat = 3 from rfl]; omega
  have hcr_hp_z : (cref.setWidth 64 + 3 + hpv.setWidth 64).toNat = cref.toNat + 3 + hp_n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
      zext_toNat hpv (by decide), bv32_ofNat_toNat (by omega),
      show (3 : BitVec 64).toNat = 3 from rfl]; omega
  fa_fast_steps_nogrp
  · -- `hp_n > 1`: load `other` -> headroom -> `full_watch_push` -> swap -> `full_unwatch_large`
    let oth_n := pos_n ^^^ 1
    have hoth_lt2 : oth_n < 2 := by
      rcases (by omega : pos_n = 0 ∨ pos_n = 1) with rfl | rfl <;> decide
    have hxor_bv : (posv ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 oth_n := by
      apply BitVec.eq_of_toNat_eq
      rcases (by omega : pos_n = 0 ∨ pos_n = 1) with rfl | rfl <;> decide
    have hcr_oth_z : (cref.setWidth 64 + 3 + (posv ^^^ 1).setWidth 64).toNat =
        cref.toNat + 3 + oth_n := by
      rw [hxor_bv, BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
        zext_toNat (BitVec.ofNat 32 oth_n) (by decide), bv32_ofNat_toNat (by omega),
        show (3 : BitVec 64).toNat = 3 from rfl]; omega
    have hcr_oth_bd : (cref.setWidth 64 + 3 + (posv ^^^ 1).setWidth 64).toNat <
        s_in.core.arena.length := by rw [hcr_oth_z, har_len_in]; omega
    let oth := s_in.core.arena[(cref.setWidth 64 + 3 +
      (posv ^^^ 1).setWidth 64).toNat]'hcr_oth_bd
    have hoth_lt_vars : oth.toNat < 2 * s_in.core.cur_vars := by
      have hoth_mem : oth.toNat ∈ fullArenaClauseLitsCore s_in.core cref.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_in]; omega)]
        exact ⟨oth_n, by rw [hsz_in]; omega, by
          dsimp only [oth]; exact congrArg BitVec.toNat (m5_list_getElem_of_idx hcr_oth_z.symm)⟩
      exact hw_in.arena.lits_lt cref.toNat hcref_in hng_in _ hoth_mem
    have hoth_31 : oth.toNat < 2 ^ 31 - 1 := by
      have := hlen_in.core_ok.cur_vars_le; omega
    have hoth_31' : oth.toNat < 2 ^ 31 := by omega
    have hoth_m_ne : oth &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [(bv32_lit_lo31_props hoth_31').1]; exact bv32_lit_neq_ff hoth_31
    have hoth_m_and : ((oth &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
      rw [(bv32_lit_lo31_props hoth_31').1]; exact (bv32_lit_lo31_props hoth_31').2.2
    have hhi_31 : high_lit.toNat < 2 ^ 31 - 1 := by
      have := hlen_in.core_ok.cur_vars_le; omega
    have hcr_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr32
    fa_fast_steps_nogrp
    refine wp_join_group (ts := []) (fun () ml_d =>
      ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s_in.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s_in.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧ (FullMem c s_d ⋆ R) ml_d) ?_ ?_
    · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hmw_d, hm_d⟩
      clear hm_in
      have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm_in
      have hsd_cv : s_d.core.cur_vars = s_in.core.cur_vars := by rw [hsd_c]
      have hsd_cref : cref.toNat ∈ fullArenaClauseRefsCore s_d.core := by
        change cref.toNat ∈ fullArenaClauseRefsCore s_in.core at hcref_in
        rwa [show fullArenaClauseRefsCore s_d.core = fullArenaClauseRefsCore s_in.core by
          simp [fullArenaClauseRefsCore, hsd_c]]
      have hlay_d : Full.WatchStackLayout s_d.core := by
        have h := hmw_d; unfold ModeWatchesInv at h; rw [ite_eq_left hsd_dm] at h; exact h.layout
      fa_fast_steps_nogrp
      c0_call hPush
      refine ⟨c, s_d, R, rfl, hlen_d, hlay_d, fun h => absurd h (by decide),
        fun _ => ⟨hoth_m_ne, hcr_ne⟩, hm_d,
        fun ok_p wv_p ws_p wl_p wu_p wso_p m_p hlen_p hlay_p hoth_p hT hF hm_p => ?_⟩
      clear hm_d
      obtain ⟨s_p, hsp_d_eq, hm_p'⟩ : ∃ s_p : FullState,
          s_p = { s_d with
            core := { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
            scratch := { s_d.scratch with wsort := wso_p } } ∧
          (FullMem c s_p ⋆ R) m_p := ⟨_, rfl, hm_p⟩
      clear hm_p
      have hsp_c : s_p.core = { s_in.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } := by
        rw [hsp_d_eq]; dsimp only; rw [hsd_c]
      have hsp_sc : s_p.scratch = { s_in.scratch with wsort := wso_p } := by
        rw [hsp_d_eq]; dsimp only; rw [hsd_sc]
      have hlen_p' : s_p.LengthsOk c := by
        rw [hsp_d_eq]; exact ⟨{ hlen_p.core_ok with }, hlen_p.scratch_ok⟩
      by_cases hok_c : ok_p = true
      · subst hok_c
        obtain ⟨_, _, hsz_p, hsame_p, hw0_p, hw1_p⟩ := hT rfl
        have hm_wp : ModeWatchesInv F_cur s_p.core := by
          have hsp_d_c : s_p.core = { s_d.core with
              wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
            congrArg FullState.core hsp_d_eq
          rw [hsp_d_c]
          exact fa_watchPush_large_preserves hsd_dm hmw_d (by rw [hsd_cv]; exact hhi_lt)
            hlay_p hoth_p hsz_p hsame_p hw0_p (hw1_p rfl) hoth_m_and (by omega) hsd_cref
        have hw_p : Full.FullWitnessCutInv c F0 F_cur cut1 s_p.core := by
          have h_w : s_p.core = { s_in.core with
              wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } := hsp_c
          rw [h_w] at hm_wp ⊢; exact m5_canonCut_with_watches hw_in hm_wp
        have hnd_p : Full.FullArenaVarsNodup s_p := fun r hr hgr => by
          change r ∈ fullArenaClauseRefsCore s_p.core at hr
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          rw [hrf] at hr
          change ((fullArenaClauseLitsCore s_p.core r).map (· / 2)).Nodup
          rw [show fullArenaClauseLitsCore s_p.core r = fullArenaClauseLitsCore s_in.core r by
            simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c]]
          exact hnd_in r hr (by
            change fullArenaClauseGarbCore s_in.core r = false
            simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hgr)
        have hext_p : Full.FullExtScratchOk c s_p := ⟨fun i hi => by
          change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s_p.core
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          have hll : s_p.scratch.last_learned = s_in.scratch.last_learned := by rw [hsp_sc]
          rw [hrf, hll]; exact hext_in.1 i hi,
          by change s_p.scratch.extend_len ≤ c.extend_cap
             rw [hsp_sc]; exact hext_in.2⟩
        have hcref_p : cref.toNat ∈ fullArenaClauseRefsCore s_p.core := by
          simpa [fullArenaClauseRefsCore, hsp_c] using hcref_in
        have hng_p : fullArenaClauseGarbCore s_p.core cref.toNat = false := by
          simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hng_in
        have hsz_p' : fullArenaClauseSizeCore s_p.core cref.toNat = csz_val := by
          simpa [fullArenaClauseSizeCore, hsp_c] using hsz_in
        have hsp_ar : s_p.core.arena = s_in.core.arena := by rw [hsp_c]
        have hsp_pos_bd : (cref.setWidth 64 + 3 + posv.setWidth 64).toNat <
            s_p.core.arena.length := by rw [hcr_pos_z, hsp_ar, har_len_in]; omega
        have hsp_hp_bd : (cref.setWidth 64 + 3 + hpv.setWidth 64).toNat <
            (s_p.core.arena.set (cref.setWidth 64 + 3 + posv.setWidth 64).toNat
              high_lit).length := by
          rw [List.length_set, hcr_hp_z, hsp_ar, har_len_in]; omega
        obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, hrefs_sw, hcref_sw, hng_sw, hsz_sw, hperm_sw⟩ :=
          m5_oneLit_swap_arena_inv hlen_p' hw_p hnd_p hext_p hcref_p hng_p hsz_p' (i := pos_n)
            (j := hp_n) (by omega) hhp_lt lit_pos high_lit (by rw [hsp_ar]; exact hlit_pos)
            (by rw [hsp_ar]; exact hhigh)
        let ar_sw := (s_p.core.arena.set (cref.toNat + 3 + pos_n) high_lit).set
          (cref.toNat + 3 + hp_n) lit_pos
        let ar_raw := (s_p.core.arena.set (cref.setWidth 64 + 3 + posv.setWidth 64).toNat
          high_lit).set (cref.setWidth 64 + 3 + hpv.setWidth 64).toNat lit_pos
        have har_eq_sw : ar_raw = ar_sw := by
          dsimp only [ar_raw, ar_sw]; rw [hcr_pos_z, hcr_hp_z]
        let s_sw : FullState := { s_p with core := { s_p.core with arena := ar_sw } }
        have hlay_sw : Full.WatchStackLayout s_sw.core := by
          have h := hw_sw.watches; unfold ModeWatchesInv at h
          rw [ite_eq_left (by change s_p.core.dense_mode = 0#64; rw [hsp_c]; exact hdm_in)] at h
          exact h.layout
        fa_fast_steps_nogrp
        have hm_sw : (FullMem c s_sw ⋆ R) _ :=
          m5_fullMem_of_eq (s1 := { s_p with core := { s_p.core with arena := ar_raw } })
            (by assumption) (congrArg (fun a => { s_p.core with arena := a }) har_eq_sw) rfl
        c0_call hUnw
        refine ⟨c, s_sw, R, rfl, hlen_sw, hlay_sw, hm_sw,
          fun wv_u ws_u wu_u m_u hlen_u _ hmw_u hm_u => ?_⟩
        let s_out : FullState :=
          { s_sw with core := { s_sw.core with wvec := wv_u, wstk := ws_u, wusable := wu_u } }
        have hlen_out : s_out.LengthsOk c := ⟨hlen_u.core_ok, hlen_u.scratch_ok⟩
        have hw_out : Full.FullWitnessCutInv c F0 F_cur cut1 s_out.core :=
          m5_canonCut_with_watches hw_sw (hmw_u F_cur hw_sw.watches)
        have hm_out' : Full.FullLitMarksClear c s_out :=
          ⟨fun v hv => by
            change s_p.core.mrk[v]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.1 v hv,
           fun l hl => by
            change s_p.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.2 l hl⟩
        have hnd_out : Full.FullArenaVarsNodup s_out := fun r hr hgr => by
          change r ∈ fullArenaClauseRefsCore s_out.core at hr
          have hr' : r ∈ fullArenaClauseRefsCore s_sw.core := hr
          have hg' : fullArenaClauseGarbCore s_sw.core r = false := hgr
          exact hnd_sw r hr' hg'
        have hext_out : Full.FullExtScratchOk c s_out := hext_sw
        have hcref_out : cref.toNat ∈ fullArenaClauseRefsCore s_out.core := hcref_sw
        have hng_out : fullArenaClauseGarbCore s_out.core cref.toNat = false := hng_sw
        have hsz_out : fullArenaClauseSizeCore s_out.core cref.toNat = csz_val := hsz_sw
        have hlits_out : ∀ q, q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔
            q ∈ fullArenaClauseLits s s.core.confl_ref.toNat := fun q => by
          change q ∈ fullArenaClauseLitsCore s_sw.core cref.toNat ↔ _
          rw [hperm_sw.mem_iff]
          simpa only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c] using
            h_confl_eq q
        fa_fast_steps
        exact hJs _ ⟨s_out, hlen_out, hw_out, hm_out', hnd_out, hext_out,
          by rw [show s_out.core.cur_vars = s_in.core.cur_vars by simp [s_out, s_sw, hsp_c]]
             exact hcv_in,
          by rw [show s_out.core.cur_level = s_in.core.cur_level by simp [s_out, s_sw, hsp_c]]
             exact hcl_in,
          by rw [show s_out.core.fuel = s_in.core.fuel by simp [s_out, s_sw, hsp_c]]; exact hfu_in,
          by rw [show s_out.scratch.work_stk2 = s_in.scratch.work_stk2 by
               simp [s_out, s_sw, hsp_sc]]; exact hws2_in,
          by rw [show s_out.core.dense_mode = s_in.core.dense_mode by simp [s_out, s_sw, hsp_c]]
             exact hdm_in,
          by rw [show s_out.core.probing = s_in.core.probing by simp [s_out, s_sw, hsp_c]]
             exact hpr_in,
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          by simp [s_out, s_sw, hsp_c],
          hcref_out, hng_out, hsz_out, hlits_out, hm_u⟩
      · -- `full_watch_push` failed: `h->oom = 1ULL; return 2ULL;`
        have hok_f : ok_p = false := Bool.eq_false_iff.mpr hok_c
        subst hok_f
        obtain ⟨hsame_f, _⟩ := hF rfl
        have hsp_d_c : s_p.core = { s_d.core with
            wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
          congrArg FullState.core hsp_d_eq
        have hm_wpf : ModeWatchesInv F_cur s_p.core := by
          rw [hsp_d_c]
          exact fa_watchPush_fail_preserves hsd_dm hmw_d hlay_p fun l hl =>
            if hle : l = high_lit.toNat then
              by subst l; exact hsame_f (by rw [hsd_cv]; exact hhi_lt)
            else hoth_p l hl hle
        have hw_pf : Full.FullWitnessCutInv c F0 F_cur cut1 s_p.core := by
          rw [hsp_c] at hm_wpf ⊢; exact m5_canonCut_with_watches hw_in hm_wpf
        fa_fast_steps
        let s_po : FullState := { s_p with core := { s_p.core with oom := 1#64 } }
        have hlen_po : s_po.LengthsOk c := ⟨{ hlen_p'.core_ok with }, hlen_p'.scratch_ok⟩
        have hnd_po : Full.FullArenaVarsNodup s_po := fun r hr hgr => by
          change r ∈ fullArenaClauseRefsCore s_p.core at hr
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          rw [hrf] at hr
          change ((fullArenaClauseLitsCore s_p.core r).map (· / 2)).Nodup
          rw [show fullArenaClauseLitsCore s_p.core r = fullArenaClauseLitsCore s_in.core r by
            simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c]]
          exact hnd_in r hr (by
            dsimp only [s_po] at hgr
            change fullArenaClauseGarbCore s_in.core r = false
            simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hgr)
        have hext_po : Full.FullExtScratchOk c s_po := ⟨fun i hi => by
          change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s_p.core
          have hrf : fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s_in.core := by
            simp [fullArenaClauseRefsCore, hsp_c]
          have hll : s_p.scratch.last_learned = s_in.scratch.last_learned := by rw [hsp_sc]
          rw [hrf, hll]; exact hext_in.1 i hi,
          by change s_p.scratch.extend_len ≤ c.extend_cap
             rw [hsp_sc]; exact hext_in.2⟩
        have hmk_po : Full.FullLitMarksClear c s_po :=
          ⟨fun v hv => by
             change s_p.core.mrk[v]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.1 v hv,
           fun l hl => by
             change s_p.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hsp_c]; exact hmk_in.2 l hl⟩
        exact hQ 2#64 s_po _ hlen_po (Or.inr (Or.inr (Or.inl rfl)))
          (by dsimp [s_po]; rw [hsp_c]; exact hcv_in)
          (by dsimp [s_po]; rw [hsp_c]; exact hfu_in)
          (by dsimp [s_po]; rw [hsp_sc]; exact hws2_in)
          (by dsimp [s_po]; rw [hsp_c]; exact hdm_in)
          (by dsimp [s_po]; rw [hsp_c]; exact hpr_in)
          hmk_po hnd_po hext_po (fun h => absurd h hbin) (fun h => by cases h) (fun h => by cases h)
          (fun _ => m5_otfsInv_with_oom hw_pf.toFullOtfsWitnessInv 1#64) (fun h => by cases h)
          (by assumption)
    · intro Jd hJd
      have hmw_in : ModeWatchesInv F_cur s_in.core := hw_in.watches
      exact m5_wstack_ensure2_ret2_wp hDefrag hlen_in hdm_in hmw_in hm_in
        (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o => by
          have hw_i : Full.FullWitnessCutInv c F0 F_cur cut1 s_i.core := by
            rw [hsi_c] at hmw_i ⊢; exact m5_canonCut_with_watches hw_in hmw_i
          let s_io : FullState := { s_i with core := { s_i.core with oom := 1#64 } }
          have hnd_io : Full.FullArenaVarsNodup s_io := fun r hr hgr => by
            change r ∈ fullArenaClauseRefsCore s_i.core at hr
            have hrf : fullArenaClauseRefsCore s_i.core = fullArenaClauseRefsCore s_in.core := by
              simp [fullArenaClauseRefsCore, hsi_c]
            rw [hrf] at hr
            change ((fullArenaClauseLitsCore s_i.core r).map (· / 2)).Nodup
            rw [show fullArenaClauseLitsCore s_i.core r = fullArenaClauseLitsCore s_in.core r by
              simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsi_c]]
            exact hnd_in r hr (by
              dsimp only [s_io] at hgr
              change fullArenaClauseGarbCore s_in.core r = false
              simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsi_c] using hgr)
          have hext_io : Full.FullExtScratchOk c s_io := ⟨fun i hi => by
            change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s_i.core
            have hrf : fullArenaClauseRefsCore s_i.core = fullArenaClauseRefsCore s_in.core := by
              simp [fullArenaClauseRefsCore, hsi_c]
            have hll : s_i.scratch.last_learned = s_in.scratch.last_learned := by rw [hsi_sc]
            rw [hrf, hll]; exact hext_in.1 i hi,
            by change s_i.scratch.extend_len ≤ c.extend_cap
               rw [hsi_sc]; exact hext_in.2⟩
          have hmk_io : Full.FullLitMarksClear c s_io :=
            ⟨fun v hv => by
               change s_i.core.mrk[v]?.getD 0#8 = 0#8; rw [hsi_c]; exact hmk_in.1 v hv,
             fun l hl => by
               change s_i.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hsi_c]; exact hmk_in.2 l hl⟩
          exact hQ 2#64 s_io ml_o ⟨{ hlen_i.core_ok with }, hlen_i.scratch_ok⟩
            (Or.inr (Or.inr (Or.inl rfl)))
            (by dsimp [s_io]; rw [hsi_c]; exact hcv_in)
            (by dsimp [s_io]; rw [hsi_c]; exact hfu_in)
            (by dsimp [s_io]; rw [hsi_sc]; exact hws2_in)
            (by dsimp [s_io]; rw [hsi_c]; exact hdm_in)
            (by dsimp [s_io]; rw [hsi_c]; exact hpr_in)
            hmk_io hnd_io hext_io (fun h => absurd h hbin) (fun h => by cases h)
            (fun h => by cases h)
            (fun _ => m5_otfsInv_with_oom hw_i.toFullOtfsWitnessInv 1#64) (fun h => by cases h)
            hm_o)
        hJd
  · -- `hp_n ≤ 1`: pure arena swap `(pos_n, hp_n)` with no watch changes
    have hin_pos_bd : (cref.setWidth 64 + 3 + posv.setWidth 64).toNat <
        s_in.core.arena.length := by rw [hcr_pos_z, har_len_in]; omega
    have hin_hp_bd : (cref.setWidth 64 + 3 + hpv.setWidth 64).toNat <
        (s_in.core.arena.set (cref.setWidth 64 + 3 + posv.setWidth 64).toNat
          high_lit).length := by
      rw [List.length_set, hcr_hp_z, har_len_in]; omega
    obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, _, hcref_sw, hng_sw, hsz_sw, hperm_sw⟩ :=
      m5_oneLit_swap_arena_inv hlen_in hw_in hnd_in hext_in hcref_in hng_in hsz_in
        (i := pos_n) (j := hp_n) (by omega) hhp_lt lit_pos high_lit hlit_pos hhigh
    let ar_sw := (s_in.core.arena.set (cref.toNat + 3 + pos_n) high_lit).set
      (cref.toNat + 3 + hp_n) lit_pos
    let ar_raw := (s_in.core.arena.set (cref.setWidth 64 + 3 + posv.setWidth 64).toNat
      high_lit).set (cref.setWidth 64 + 3 + hpv.setWidth 64).toNat lit_pos
    have har_eq_sw : ar_raw = ar_sw := by
      dsimp only [ar_raw, ar_sw]; rw [hcr_pos_z, hcr_hp_z]
    let s_out : FullState := { s_in with core := { s_in.core with arena := ar_sw } }
    fa_fast_steps
    have hm_out : (FullMem c s_out ⋆ R) _ :=
      m5_fullMem_of_eq (s1 := { s_in with core := { s_in.core with arena := ar_raw } })
        (by assumption) (congrArg (fun a => { s_in.core with arena := a }) har_eq_sw) rfl
    exact hJs _ ⟨s_out, hlen_sw, hw_sw, hmk_in, hnd_sw, hext_sw, hcv_in, hcl_in, hfu_in,
      hws2_in, hdm_in, hpr_in, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcref_sw, hng_sw, hsz_sw,
      fun q => by
        change q ∈ fullArenaClauseLitsCore s_out.core cref.toNat ↔ _
        rw [hperm_sw.mem_iff]; exact h_confl_eq q,
      hm_out⟩

end LeanQbe.T.Examples.Kissat.FullM5Otfs
