/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify

import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Vivify Clause Driver WP Proofs (`Proof.Vivify.WpClause`)

Parametric `(Γ : Env)` `Func.wp` proofs for:
1. `full_viv_has_l0_m6_wp` (`Spec.fullVivHasL0M6Spec`)
2. `full_viv_l0_simp_m6_wp` (`Spec.fullVivL0SimpM6Spec`)
3. `full_viv_reuse_prefix_m6_wp` (`Spec.fullVivReusePrefixM6Spec`)
4. `full_viv_clause_m6_wp` (`Spec.vivClauseM6Spec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics

public section

/-! ## 1. Pure BV / List & Decision-Assign Helpers -/

private theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

private theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

private theorem bv32_lshr_1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  simpa using bv32_lshr1_toNat x

private theorem viv_tmp_mem_of_perm {tmp' : List (BitVec 32)} {lits : List Nat} {sz : Nat}
    (hsz' : sz ≤ tmp'.length) (hperm : ((tmp'.take sz).map BitVec.toNat).Perm lits) :
    (∀ k < sz, (tmp'[k]?.getD 0#32).toNat ∈ lits) ∧
    (∀ l ∈ lits, ∃ k < sz, (tmp'[k]?.getD 0#32).toNat = l) := by
  constructor
  · intro k hk
    have hk_take : (tmp'[k]?.getD 0#32).toNat ∈ (tmp'.take sz).map BitVec.toNat := by
      rw [List.mem_map]
      refine ⟨tmp'[k]'(by omega), ?_, ?_⟩
      · have hlt : k < (tmp'.take sz).length := by simp [List.length_take]; omega
        simpa [List.getElem_take] using List.getElem_mem hlt
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hperm.mem_iff.mp hk_take
  · intro l hl
    have hmem := hperm.mem_iff.mpr hl
    rw [List.mem_map] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < sz := by rw [List.length_take] at hk; omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take] at hget
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]

private theorem viv_decide_assign_preserves_sparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)}
    {unass' unfl' : BitVec 64} (hfll : flags'.length = c.max_vars)
    (hphl : phases'.length = c.max_vars) :
    let nlvl := s.core.cur_level + 1
    let dlit := lit ^^^ 1#32
    let v := dlit.toNat / 2
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl dlit
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end dlit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unass', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    nlvl ≤ c.max_vars ∧ FullSparseInvW c F0 F_cur s' ∧
    (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    s'.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
  intro nlvl dlit v ftrl' fdec' s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := viv_bv32_xor1_toNat lit
  have hdlit_lt : dlit.toNat < 2 * s.core.cur_vars := viv_bv32_xor1_lt hlit
  have hv_eq : v = lit.toNat / 2 := by dsimp only [v]; rw [hdlit_nat, fullInv_var_xor1]
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnlvl_le : nlvl ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    rw [hv_eq]; exact (hw.vals_zero_iff hlit).mp hun
  have hne_lit : dlit.toNat ^^^ 1 ≠ dlit.toNat := litNeg_ne_self dlit.toNat
  have hdlit_neg : dlit.toNat ^^^ 1 = lit.toNat := by
    rw [hdlit_nat]; exact litNeg_litNeg lit.toNat
  have hv_lt : v < c.max_vars := by rw [hv_eq]; have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hnlvl_lt32 : nlvl < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then dlit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then nlvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat hnlvl_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = dlit.toNat ^^^ 1 then 0xFF#8 else if l = dlit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = dlit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = dlit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
      lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
      trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
      frame_trail_len := by simp [s', ftrl', hcl.frame_trail_len],
      frame_dec_len := by simp [s', fdec', hcl.frame_dec_len],
      trail_end_le := by dsimp [s']; omega,
      propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hscl with phases_len := hphl }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by have := hw.cur_level_le; dsimp [s', nlvl]; omega
      trail_lits_lt := fun i hi => by
        rw [htrl_get i hi]; split
        · exact hdlit_lt
        · exact hw.trail_lits_lt i (by dsimp [s'] at hi; omega)
      trail_vars_nodup := fun i j hi hj hveq => by
        rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by dsimp [s'] at hj; omega))
        · exact absurd hveq (hnot_var i (by dsimp [s'] at hi; omega))
        · exact hw.trail_vars_nodup i j (by dsimp [s'] at hi; omega)
            (by dsimp [s'] at hj; omega) hveq
      vals_domain := fun l hl => by
        rw [hvals_get l hl]; split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = dlit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = dlit.toNat
            · exact ⟨s.core.trail_end, by dsimp [s']; omega,
                by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by dsimp [s']; omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by dsimp [s'] at hi; omega)
            have h1 : l ≠ dlit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ dlit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr
              ⟨i, by dsimp [s'] at hi; omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = dlit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by dsimp [s']; omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = dlit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by dsimp [s']; omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = dlit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by dsimp [s'] at hi; omega); rw [heq] at h
              rwa [fullInv_var_xor1] at h
            have h1 : l ≠ dlit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ dlit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr
              ⟨i, by dsimp [s'] at hi; omega, heq⟩
      lvl_le := fun i hi => by
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp [s', nlvl]
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]
          have := hw.lvl_le i hilt; dsimp [s', nlvl]; omega
      dec_earliest := fun i j hi hj hleq hdec => by
        rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = s.core.trail_end
        · subst hje; simp only [↓reduceIte] at hleq hdec
          by_cases hie : i = s.core.trail_end
          · omega
          · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
            simp only [hie, ↓reduceIte] at hleq
            rw [hlvl_get v (by omega),
              hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hleq
            simp only [hnot_var i hilt, ↓reduceIte] at hleq
            have := hw.lvl_le i hilt; omega
        · by_cases hie : i = s.core.trail_end
          · dsimp [s'] at hj; omega
          · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
            have hjlt : j < s.core.trail_end := by dsimp [s'] at hj; omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
              hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by
        by_cases hLn : L = nlvl
        · subst hLn; refine ⟨s.core.trail_end, by dsimp [s']; omega, ?_⟩
          rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hLold : L ≤ s.core.cur_level := by dsimp [s', nlvl] at hLle; omega
          obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLold
          refine ⟨i, by dsimp [s']; omega, ?_⟩
          rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega)]; simp [hnot_var i hi, hli]
      level0_sound := fun i hi hli => by
        rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp [nlvl] at hli
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw.level0_sound i hilt hli
      trail_pos_inv := fun i hi => by
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by dsimp [s'] at hi; omega
          simp only [hie, ↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hli => by
        rw [htrl_get idx hidx] at hli ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp [nlvl] at hli
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
          rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
          simp only [hnv, ↓reduceIte] at hli
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnv, ↓reduceIte]; exact hw.level0_rsn_none idx hilt hli
      frame_trail_lt := fun L hL => by
        dsimp only [s', ftrl'] at hL ⊢
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]; omega
        · rw [List.getElem?_set_ne (Ne.symm hLn)]
          have := hw.frame_trail_lt L (by dsimp [nlvl] at hL; omega); omega
      frame_trail_mono := fun L1 L2 h12 h2 => by
        dsimp only [s', ftrl'] at h2 ⊢
        by_cases h2n : L2 = nlvl
        · subst h2n; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
          by_cases h1n : L1 = nlvl
          · subst h1n; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
              Option.getD_some, bv32_ofNat_toNat hte_lt32]
            exact Nat.le_refl _
          · rw [List.getElem?_set_ne (Ne.symm h1n)]
            exact hw.frame_trail_lt L1 (by dsimp [nlvl] at h12; omega)
        · have h1n : L1 ≠ nlvl := by dsimp [nlvl] at h2; omega
          rw [List.getElem?_set_ne (Ne.symm h1n), List.getElem?_set_ne (Ne.symm h2n)]
          exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at h2; omega)
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        dsimp only [s', ftrl'] at hLle hi
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega),
            Option.getD_some, bv32_ofNat_toNat hte_lt32] at hi
          rw [htrl_get i (by omega), ite_eq_right (by omega)]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi; omega), ite_eq_right (hnot_var i hi)]
          have := hw.lvl_le i hi; dsimp [nlvl]; omega
        · rw [List.getElem?_set_ne (Ne.symm hLn)] at hi
          have hLle0 : L ≤ s.core.cur_level := by dsimp [s', nlvl] at hLle; omega
          have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle0)
          rw [htrl_get i (by omega), ite_eq_right (by omega)]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hi_lt; omega),
            ite_eq_right (hnot_var i hi_lt)]
          exact hw.frame_trail_before_lt L hL1 hLle0 i hi
      frame_dec_lt := fun L hL1 hLle => by
        dsimp only [s', fdec'] at hLle ⊢
        by_cases hLn : L = nlvl
        · subst hLn; rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega),
            Option.getD_some]; exact hdlit_lt
        · rw [List.getElem?_set_ne (Ne.symm hLn)]
          exact hw.frame_dec_lt L hL1 (by dsimp [s', nlvl] at hLle; omega)
      reason_inv := fun idx hidx hne => by
        rw [htrl_get idx hidx] at hne ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
          simp only [hnv, ↓reduceIte] at hne ⊢
          have hrs := hw.reason_inv idx hilt hne
          by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hb] at hrs ⊢; obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
            refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hot_v : ((s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
              rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
          · rw [ite_eq_right hb] at hrs ⊢
            refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
            have hq' : q ∈ fullArenaClauseLitsCore s.core
                (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32).toNat := by
              simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
            refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
              simp [hnv, hqv, hlvl_le]
      reason_lit_mem := fun idx hidx hne hlg => by
        rw [htrl_get idx hidx] at hne hlg ⊢; by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
        · have hilt : idx < s.core.trail_end := by dsimp [s'] at hidx; omega
          simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
          simp only [hnv, ↓reduceIte] at hne hlg ⊢
          simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
            hw.reason_lit_mem idx hilt hne hlg }
  refine ⟨hnlvl_le, ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    fun l hl hff => ?_, ?_⟩
  · rw [hvals_get l hl]; split
    · rfl
    · split
      · rename_i hpos; exfalso
        have hlv : l / 2 ≠ v := by
          obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hff
          have := hnot_var i hi; rw [heq, fullInv_var_xor1] at this; exact this
        exact hlv (by rw [hpos])
      · exact hff
  · rw [hvals_get lit.toNat hlit, ite_eq_left hdlit_neg.symm]

/-! ## 2. `full_viv_has_l0_m6`, `full_viv_l0_simp_m6`, `full_viv_reuse_prefix_m6` -/

theorem full_viv_has_l0_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivHasL0M6Spec a m Q X → Func.wp Γ full_viv_has_l0_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, hsz, hm0, hQ⟩
  have hwf := hsp.2.1.arena.refs_wf cref.toNat href
  have hcl := hsp.1.core_ok
  have harc := c.harena; have hmx := c.hmaxv; unfold dimacsBound at harc hmx
  have har_len := hcl.arena_len_arr; have har_le := hcl.arena_len_le
  have hvl := hcl.vals_len; have hll := hcl.lvl_len; have hcv := hcl.cur_vars_le
  have hbd : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
    rw [hsz]; unfold fullArenaClauseSize at *; omega
  unfold Func.wp full_viv_has_l0_m6_body
  viv_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ sz.toNat ∧ ml = m0)
    (fun (i, ()) _ => sz.toNat - i.toNat)
    (fun J hJ => by viv_steps; exact hJ (0#32, ()) m0 ⟨Nat.zero_le _, rfl⟩)
    (fun J ⟨i, ⟨⟩⟩ ml ⟨hi_le, rfl⟩ ih => by
      viv_steps
      · have hi_lt : i.toNat < sz.toNat := by c0_bound
        have hidx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hidx_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
            s.core.arena.length := by omega
        have hl_mem : (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat
            ∈ fullArenaClauseLits s cref.toNat := by
          unfold fullArenaClauseLits fullArenaClauseLitsCore
          rw [show fullArenaClauseSizeCore s.core cref.toNat = sz.toNat from hsz.symm, List.mem_map]
          refine ⟨s.core.arena[cref.toNat + 3 + i.toNat]'(by omega), ?_, ?_⟩
          · have hlt : i.toNat < ((s.core.arena.drop (cref.toNat + 3)).take sz.toNat).length := by
              simp [List.length_take, List.length_drop]; omega
            simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
          · exact congrArg BitVec.toNat (Option.some.inj (by
              rw [← List.getElem?_eq_getElem (by omega), ← hidx,
                List.getElem?_eq_getElem hidx_lt]))
        have hl_lt : (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat <
            2 * s.core.cur_vars := hsp.2.1.arena.lits_lt cref.toNat href hng _ hl_mem
        have hl_vl : ((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
            hidx_lt).setWidth 64).toNat < s.core.vals.length := by
          rw [bv32_setWidth64_toNat]; omega
        have hl_lv : (((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
            hidx_lt) >>> (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
          rw [bv32_setWidth64_toNat]
          have : ((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt) >>>
              1).toNat = (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
              hidx_lt).toNat / 2 := bv32_lshr_1 _
          rw [show (1#32 : BitVec 32).toNat = 1 from rfl, this]; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        viv_steps
        · exact hQ true
        · exact ih (i + 1#32, ()) ml (by dsimp only; omega) ⟨by omega, rfl⟩
        · exact ih (i + 1#32, ()) ml (by dsimp only; omega) ⟨by omega, rfl⟩
      · exact hQ false)

theorem full_viv_l0_simp_m6_wp (Γ : Env)
    (hHasL0 : Γ.Has "full_viv_has_l0_m6" fullVivHasL0M6Spec)
    (hBacktrack : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hSimplify : Γ.Has "full_viv_simplify_m6" fullVivSimplifyM6Spec) :
    ∀ a m Q X, fullVivL0SimpM6Spec a m Q X → Func.wp Γ full_viv_l0_simp_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  unfold Func.wp full_viv_l0_simp_m6_body
  viv_steps
  viv_call hHasL0
  refine ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hm0, fun hasl0 => ?_⟩
  viv_to_group
  · refine wp_join_group (ts := [])
      (fun () m_bt => ∃ s_bt : FullState,
        FullSparseInvW c F0 F_cur s_bt ∧ s_bt.core.cur_level = 0 ∧
        s_bt.core.cur_vars = s.core.cur_vars ∧ s_bt.core.probing = s.core.probing ∧
        s_bt.core.fuel = s.core.fuel ∧ s_bt.core.arena_len = s.core.arena_len ∧
        fullArenaClauseRefs s_bt = fullArenaClauseRefs s ∧
        s_bt.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs s_bt ∧ fullArenaClauseGarb s_bt cref.toNat = false ∧
        (FullMem c s_bt ⋆ R) m_bt) ?_ ?_
    · rintro _ ⟨⟩ m_bt ⟨s_bt, hsp_bt, hcl_bt0, hcv_bt, hpr_bt, hfl_bt, hal_bt, hrefs_bt, hrr_bt,
        href_bt, hng_bt, hm_bt⟩
      viv_steps
      viv_call hSimplify
      refine ⟨c, F0, F_cur, s_bt, R, rfl, hsp_bt, hcl_bt0, href_bt, hng_bt, hm_bt,
        fun sr s_s m_s hsp_s _ hcv_s hal_s hpr_s hfl_s hrefs_s hrr_s _ hsr h20 h0 hm_s => ?_⟩
      viv_steps
      exact hQ sr s_s m_s hsp_s (hcv_s.trans hcv_bt) (hpr_s.trans hpr_bt) (hfl_s.trans hfl_bt)
        (hal_s.trans hal_bt) (hrefs_s.trans hrefs_bt) (hrr_s.trans hrr_bt) hsr h20 h0 hm_s
    · intro Jbt hJbt
      have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
        have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le
        have := hcl0.cur_vars_le; omega
      viv_steps
      · viv_call hBacktrack
        refine ⟨c, s, R, rfl, hsp0.1, hcl0_lt,
          (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro
              have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le
              have := hcl0.cur_vars_le; omega),
          hsp0.2.1.trail_lits_lt, hm0,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
            hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
        have hsp_bt : FullSparseInvW c F0 F_cur _ :=
          viv_sparseW_of_backtrack hsp0 (Nat.zero_le _) hlen_bt hpres_bt
            (hw_bt F0 F_cur hsp0.2.1 (Nat.zero_le _))
        rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, rfl, rfl, rfl, rfl, rfl, rfl,
          href0, hng0, hm_bt⟩
      · have hcl0_eq : s.core.cur_level = 0 := by
          have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
        exact hJbt () m0 ⟨s, hsp0, hcl0_eq, rfl, rfl, rfl, rfl, rfl, rfl, href0, hng0, hm0⟩
  · viv_steps
    exact hQ 0#64 s m0 hsp0 rfl rfl rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h)
      (fun _ => ⟨href0, hng0⟩) hm0

theorem full_viv_reuse_prefix_m6_wp (Γ : Env)
    (hBacktrack : Γ.Has "full_backtrack" fullBacktrackSpec) :
    ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Func.wp Γ full_viv_reuse_prefix_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, htmp0_lt, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  have hclvl_le : s.core.cur_level ≤ c.max_vars := by
    have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hclvl_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  unfold Func.wp full_viv_reuse_prefix_m6_body
  viv_to_group
  · viv_steps; exact hQ s m0 hsp0 rfl rfl rfl rfl rfl rfl rfl hm0
  · viv_to_group
    let clvl : BitVec 64 := BitVec.ofNat 64 s.core.cur_level
    have hclvl_nat : clvl.toNat = s.core.cur_level := by
      simp [clvl, Nat.mod_eq_of_lt hclvl_lt64]
    refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
      (fun (keep_b, _ib, ()) mb => keep_b.toNat ≤ s.core.cur_level ∧ mb = m0)
      (fun rem (keep, i, ()) mp =>
        keep.toNat ≤ s.core.cur_level ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ mp = m0)
      ?_ ?_ ?_
    · rintro _ ⟨keep_b, _ib, ⟨⟩⟩ mb ⟨hkb_le, hmb⟩
      rw [hmb]
      refine wp_loop_inv (ts := [i64, i32])
        (fun (kl, j, ()) ml => j.toNat ≤ sz.toNat ∧ kl.toNat ≤ s.core.cur_level ∧ ml = m0)
        (fun (_, j, ()) _ => sz.toNat - j.toNat) ?_ ?_
      · intro J2 hJ2; viv_steps; exact hJ2 (keep_b, 0#32, ()) m0 ⟨Nat.zero_le _, hkb_le, rfl⟩
      · intro J2 ⟨kl, j, ⟨⟩⟩ ml ⟨hj_le, hkl_le, hml⟩ ih2
        rw [hml]
        viv_steps
        · have hj_lt : j.toNat < sz.toNat := by c0_bound
          have hj_nat : (j.setWidth 64).toNat = j.toNat := bv32_setWidth64_toNat j
          have hj_tmp : (j.setWidth 64).toNat < s.core.tmp.length := by
            rw [hj_nat, hcl0.tmp_len_arr]; omega
          have hl_lt : (s.core.tmp[(j.setWidth 64).toNat]'hj_tmp).toNat < 2 * s.core.cur_vars :=
            by
            have h := htmp0_lt j.toNat hj_lt
            rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
            simpa [hj_nat] using h
          have hl_vl : ((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp).setWidth 64).toNat <
              s.core.vals.length := by
            rw [bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
          have hl_rsn : (((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp) >>>
              (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.rsns.length := by
            rw [bv32_setWidth64_toNat, hcl0.rsns_len,
              show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
            have := hcl0.cur_vars_le; omega
          have hl_lv : (((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp) >>>
              (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
            rw [bv32_setWidth64_toNat, hcl0.lvl_len,
              show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
            have := hcl0.cur_vars_le; omega
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
          viv_to_group
          refine wp_join_group (ts := [i64])
            (fun (kl', ()) mj => kl'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
          · rintro _ ⟨kl', ⟨⟩⟩ mj ⟨hkl', hmj⟩
            rw [hmj]; viv_steps
            exact ih2 (kl', j + 1#32, ()) m0 (by dsimp only; omega) ⟨by omega, hkl', rfl⟩
          · intro Jj hJj
            viv_to_group
            · refine wp_join_group (ts := [i64])
                (fun (kl', ()) mj => kl'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
              · rintro _ ⟨kl', ⟨⟩⟩ mj h; viv_steps; exact hJj (kl', ()) mj h
              · intro Ji hJi
                viv_steps
                · exact hJi (0#64, ()) m0 ⟨Nat.zero_le _, rfl⟩
                · exact hJi _ m0 ⟨Nat.le_trans (Nat.le_of_lt (by c0_bound)) hkl_le, rfl⟩
                · exact hJi (kl, ()) m0 ⟨hkl_le, rfl⟩
            · viv_steps; exact hJj (kl, ()) m0 ⟨hkl_le, rfl⟩
            · viv_steps; exact hJj (kl, ()) m0 ⟨hkl_le, rfl⟩
        all_goals try exact hQ s m0 hsp0 rfl rfl rfl rfl rfl rfl rfl hm0
        all_goals
          have hkl_lt : kl.toNat < s.core.cur_level := by
            have hc0 : kl.toNat < clvl.toNat := by c0_bound
            omega
          viv_call hBacktrack
          refine ⟨c, s, R, rfl, hsp0.1, hclvl_lt64, fun _ => by omega,
            hsp0.2.1.trail_lits_lt, hm0,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            viv_sparseW_of_backtrack hsp0 (by omega) hlen_bt hpres_bt
              (hw_bt F0 F_cur hsp0.2.1 (by omega))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          dsimp only; apply hJ; viv_steps
          exact hQ _ m_bt hsp_bt rfl rfl rfl rfl rfl rfl rfl hm_bt
    · intro B L rem ⟨keep, i, ⟨⟩⟩ mp hB hL ⟨hkp_le, hi_le, hrem, hmp⟩
      subst hrem; rw [hmp]
      viv_steps
      · have hi_lt : i.toNat < sz.toNat := by c0_bound
        have hkp_lt : keep.toNat < s.core.cur_level := by
          have hc0 : keep.toNat < clvl.toNat := by c0_bound
          omega
        have hi_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
        have hi_tmp : (i.setWidth 64).toNat < s.core.tmp.length := by
          rw [hi_nat, hcl0.tmp_len_arr]; omega
        have hfd_idx : (keep + 1#64).toNat < s.core.frame_dec.length := by
          rw [hcl0.frame_dec_len]; bv_omega
        have hl_lt : (s.core.tmp[(i.setWidth 64).toNat]'hi_tmp).toNat < 2 * s.core.cur_vars := by
          have h := htmp0_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
          simpa [hi_nat] using h
        have hl_vl : ((s.core.tmp[(i.setWidth 64).toNat]'hi_tmp).setWidth 64).toNat <
            s.core.vals.length := by
          rw [bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
        have hl_lv : (((s.core.tmp[(i.setWidth 64).toNat]'hi_tmp) >>>
            (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
          rw [bv32_setWidth64_toNat, hcl0.lvl_len,
            show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
          have := hcl0.cur_vars_le; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hkp1 : (keep + 1#64).toNat = keep.toNat + 1 := by bv_omega
        viv_to_group
        refine wp_join_group (ts := [i64])
          (fun (keep', ()) mj => keep'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
        · rintro _ ⟨keep', ⟨⟩⟩ mj ⟨hkp', hmj⟩
          rw [hmj]; viv_steps
          exact hL (sz.toNat - (i + 1#32).toNat) (keep', i + 1#32, ()) m0
            (by rw [hi1]; omega) ⟨hkp', by rw [hi1]; omega, rfl, rfl⟩
        · intro Jk hJk
          viv_steps
          · exact hJk (keep + 1#64, ()) m0 ⟨by rw [hkp1]; omega, rfl⟩
          · exact hJk (keep, ()) m0 ⟨hkp_le, rfl⟩
          · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
          · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
      · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
      · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
    · intro B L _ hL
      viv_steps
      exact hL sz.toNat (0#64, 0#32, ()) m0 ⟨Nat.zero_le _, Nat.zero_le _, by simp, rfl⟩

/-! ## 3. Clause Driver Invariants & Helpers -/

private abbrev VivClauseBrkInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop)
    (cref sz : BitVec 32) (tmp5 : List (BitVec 32)) (lits2 : List Nat) :
    Tup Val [i32, .bool, i32] → Mem 64 → Prop :=
  fun (ib, confl, implied, ()) mb =>
    ∃ (extb : List (BitVec 64)) (sb : FullState),
      M6HdrExtOk extb ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk extb ∧ M6ExtW2bPres ext0 extb) ∧
      FullSparseInvW c F0 F_cur sb ∧
      sb.core.cur_vars = s.core.cur_vars ∧ sb.core.arena_len = s.core.arena_len ∧
      sb.core.probing = s.core.probing ∧ sb.core.tmp = tmp5 ∧
      sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
      sb.scratch.red_refs = s.scratch.red_refs ∧
      cref.toNat ∈ fullArenaClauseRefs sb ∧
      fullArenaClauseGarb sb cref.toNat = false ∧
      fullArenaClauseSize sb cref.toNat = sz.toNat ∧
      (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
      (confl = true → FullConflictOkW F_cur sb) ∧
      (confl = false → implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * sb.core.cur_vars ∧
        sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (confl = false → implied = 0xFFFFFFFF#32 → ib = sz →
        sb.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (FullMem c sb ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) mb

private abbrev VivClauseLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop)
    (cref sz : BitVec 32) (tmp5 : List (BitVec 32)) (lits2 : List Nat) :
    Nat → Tup Val [i32] → Mem 64 → Prop :=
  fun rem (i, ()) mp =>
    ∃ (extp : List (BitVec 64)) (sp : FullState),
      i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ M6HdrExtOk extp ∧
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk extp ∧ M6ExtW2bPres ext0 extp) ∧
      FullSparseInvW c F0 F_cur sp ∧
      sp.core.cur_vars = s.core.cur_vars ∧ sp.core.arena_len = s.core.arena_len ∧
      sp.core.probing = s.core.probing ∧ sp.core.tmp = tmp5 ∧
      sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      fullArenaClauseRefs sp = fullArenaClauseRefs s ∧
      sp.scratch.red_refs = s.scratch.red_refs ∧
      cref.toNat ∈ fullArenaClauseRefs sp ∧
      fullArenaClauseGarb sp cref.toNat = false ∧
      fullArenaClauseSize sp cref.toNat = sz.toNat ∧
      (fullArenaClauseLits sp cref.toNat).Perm lits2 ∧
      sp.core.confl_type = 0#64 ∧
      (∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
      (FullMem c sp ⋆ (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R)) mp

private abbrev VivClauseJoinInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop)
    (cref sz i : BitVec 32) (tmp5 : List (BitVec 32)) (lits2 : List Nat) :
    Tup Val [.bool, i32] → Mem 64 → Prop :=
  fun _ m_jn =>
    ∃ (ext_jn : List (BitVec 64)) (s_jn : FullState),
      M6HdrExtOk ext_jn ∧
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext_jn ∧ M6ExtW2bPres ext0 ext_jn) ∧
      FullSparseInvW c F0 F_cur s_jn ∧
      s_jn.core.cur_vars = s.core.cur_vars ∧ s_jn.core.arena_len = s.core.arena_len ∧
      s_jn.core.probing = s.core.probing ∧ s_jn.core.tmp = tmp5 ∧
      s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
      s_jn.scratch.red_refs = s.scratch.red_refs ∧
      cref.toNat ∈ fullArenaClauseRefs s_jn ∧
      fullArenaClauseGarb s_jn cref.toNat = false ∧
      fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
      (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
      s_jn.core.confl_type = 0#64 ∧
      (∀ k < (i + 1#32).toNat,
        s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
      (FullMem c s_jn ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_jn ⋆ R)) m_jn

private theorem viv_clause_prop_step (Γ : Env)
    (hPropIgn : Γ.Has "full_propagate_ignore" PropSearch.Spec.propIgnoreM6Spec)
    (hBacktrack : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hBestImpl : Γ.Has "full_viv_best_implied_m6" fullVivBestImpliedM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext_as : List (BitVec 64)} {s sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool, i32]}
    {cref i lit sz : BitVec 32} {tmp5 : List (BitVec 32)} {lits2 : List Nat} {m_as : Mem 64}
    (hcfg : FullM6HdrCfgOk c) (hext_as : M6HdrExtOk ext_as)
    (hinit_as : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext_as ∧ M6ExtW2bPres ext0 ext_as)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      r = 1#64 ∨ r = 2#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (hB : ∀ r m', VivClauseBrkInv c F0 F_cur ext0 s R cref sz tmp5 lits2 r m' → B r m')
    (hJ_jn : ∀ xs m, VivClauseJoinInv c F0 F_cur ext0 s R cref sz i tmp5 lits2 xs m → J_jn xs m)
    (hsp_as : FullSparseInvW c F0 F_cur s_as) (hsz_le_mv : sz.toNat ≤ c.max_vars)
    (hcvp : sp.core.cur_vars = s.core.cur_vars) (hcv_as : s_as.core.cur_vars = sp.core.cur_vars)
    (halp : sp.core.arena_len = s.core.arena_len)
    (hal_as : s_as.core.arena_len = sp.core.arena_len)
    (hprp : sp.core.probing = s.core.probing) (hpr_as : s_as.core.probing = sp.core.probing)
    (hflp : sp.core.fuel.toNat ≤ s.core.fuel.toNat) (hfl_as : s_as.core.fuel = sp.core.fuel)
    (hrefsp : fullArenaClauseRefs sp = fullArenaClauseRefs s)
    (hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp)
    (hrr_as : s_as.scratch.red_refs = s.scratch.red_refs)
    (hrefp : cref.toNat ∈ fullArenaClauseRefs sp)
    (hng_as : fullArenaClauseGarb s_as cref.toNat = false)
    (hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat)
    (hpermp : (fullArenaClauseLits sp cref.toNat).Perm lits2)
    (hlits_as : fullArenaClauseLits s_as cref.toNat = fullArenaClauseLits sp cref.toNat)
    (hct_as : s_as.core.confl_type = 0#64) (htmp_as : s_as.core.tmp = tmp5)
    (hlits2_lt : ∀ l ∈ lits2, l < 2 * s.core.cur_vars)
    (hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2)
    (hi_lt : i.toNat < sz.toNat) (hlit_eq : lit = tmp5[i.toNat]?.getD 0#32)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hfalp : ∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hfal_as : ∀ l < 2 * sp.core.cur_vars,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 → s_as.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlit_as_ff : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hm_as : (FullMem c s_as ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_as ⋆ R)) m_as) :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore"
        (Arg.var c.hdr, Arg.var (cref.setWidth 64), ()) fun p =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 2, ()) }
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
            (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            Expr.ret (Arg.imm 2, ()))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.imm 1, ()) }
            fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.jump B (Arg.var i, Arg.imm true, Arg.imm 4294967295, ()))
              (Expr.call (as := [i64, i32]) (bs := [i32]) "full_viv_best_implied_m6"
                (Arg.var c.hdr, Arg.var sz, ()) fun p =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                    args := (Arg.var p.fst, Arg.imm 4294967295, ()) }
                  fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.jump B (Arg.var i, Arg.imm false, Arg.var p.fst, ()))
                  (Expr.jump J_jn (Arg.imm false, Arg.imm 4294967295, ())))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  viv_call hPropIgn
  refine ⟨c, F0, F_cur, ext_as, s_as, R, rfl, hcfg, hext_as, hsp_as.1, hsp_as.2.1,
    hsp_as.2.2.2.2.2, fullM6HdrMem_unfocus_full hm_as, ?_⟩
  intro pr ext_p vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p wvec_p
    arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p sc_p m_p _ hext_p hinit_p
    hlen_p hw_p htr_p _ hperm_p hsc_pres hrr_p _ _ _ hfl_p hpr_disj hpr0 hpr1 _ _ hm_p
  let s_p : FullState :=
    { core := { s_as.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    viv_sparseInvW_of_prop_canon hsp_as hlen_p hw_p hperm_p hsc_pres
  have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_as := hperm_p.2.1
  have hcv_p : s_p.core.cur_vars = s.core.cur_vars := hcv_as.trans hcvp
  have hal_p : s_p.core.arena_len = s.core.arena_len := hal_as.trans halp
  have hpr_p : s_p.core.probing = s.core.probing := hpr_as.trans hprp
  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p (hfl_as ▸ hflp)
  have hrefs_p' : fullArenaClauseRefs s_p = fullArenaClauseRefs s :=
    hrefs_p.trans (hrefs_as.trans hrefsp)
  have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_p.trans hrr_as
  have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ hrefs_as ▸ hrefp
  have hprops_p := hperm_p.2.2 cref.toNat (by
    change cref.toNat ∈ fullArenaClauseRefs s_as; rw [hrefs_as]; exact hrefp)
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng_as
  have hsz_p : fullArenaClauseSize s_p cref.toNat = sz.toNat := hprops_p.1.trans hsz_as
  have hlits_p : (fullArenaClauseLits s_p cref.toNat).Perm lits2 :=
    hprops_p.2.2.trans (by
      change (fullArenaClauseLits s_as cref.toNat).Perm lits2; rw [hlits_as]; exact hpermp)
  have hm_p' : (FullMem c s_p ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R)) m_p :=
    fullM6HdrMem_focus_full hm_p
  have hcv_p_as : s_p.core.cur_vars = s_as.core.cur_vars := rfl
  have htmp_p : s_p.core.tmp = tmp5 := htmp_as
  have hte_p' : s_as.core.trail_end ≤ s_p.core.trail_end := htr_p.1
  have htrl_p' : ∀ idx < s_as.core.trail_end, s_p.core.trl[idx]? = s_as.core.trl[idx]? := htr_p.2.1
  have hcok_p_fn : pr = 1#64 → FullConflictOkW F_cur s_p := fun h => (hpr1 h).2.2.1
  have hct_p0_fn : pr = 0#64 → s_p.core.confl_type = 0#64 := fun h => (hpr0 h).2.1.trans hct_as
  have hinit_p' := viv_ext_pres_trans hinit_as hinit_p
  clear_value s_p; clear hm_p hm_as hprops_p hperm_p htr_p
  viv_steps
  · have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by
      have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
      have := hsp_p.1.core_ok.cur_vars_le; omega
    viv_call hBacktrack
    refine ⟨c, s_p, (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R), rfl, hsp_p.1, hp_cl_lt,
      (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro
          have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
          have := hsp_p.1.core_ok.cur_vars_le; omega),
      hsp_p.2.1.trail_lits_lt, hm_p',
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_b
        hlen_b _ _ _ hpres_b hsc_b _ _ hw_b _ hm_b => ?_⟩
    have hsp_b : FullSparseInvW c F0 F_cur _ :=
      viv_sparseW_of_backtrack hsp_p (Nat.zero_le _) hlen_b hpres_b
        (hw_b F0 F_cur hsp_p.2.1 (Nat.zero_le _))
    rcases hsc_b with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    viv_steps
    exact hQ 2#64 ext_p _ m_b hext_p hinit_p' hsp_b hcv_p hpr_p hfl_p'
      hal_p hrefs_p' hrr_p (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fullM6HdrMem_unfocus_full hm_b)
  · have hpr_eq1 : pr = 1#64 := by c0_bound
    viv_steps
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨ext_p, s_p, hext_p, hinit_p', hsp_p, hcv_p, hal_p,
      hpr_p, htmp_p, hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p,
      fun _ => hcok_p_fn hpr_eq1, (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have htmp_p_lt : ∀ k < sz.toNat, (s_p.core.tmp[k]?.getD 0#32).toNat < 2 * s_p.core.cur_vars :=
      fun k hk => by rw [htmp_p, hcv_p]; exact hlits2_lt _ (hlits2_mem k hk)
    viv_call hBestImpl
    refine ⟨c, F0, F_cur, s_p, (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R), rfl, hsp_p, hsz_le_mv,
      htmp_p_lt, hm_p', fun bi hbi => ?_⟩
    viv_steps
    · have hbi_ne : bi ≠ 0xFFFFFFFF#32 := by c0_bound
      exact hB (i, false, bi, ()) _ ⟨ext_p, s_p, hext_p, hinit_p', hsp_p, hcv_p, hal_p, hpr_p,
        htmp_p, hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, (fun h => by cases h),
        fun _ _ => hbi hbi_ne, fun _ h => absurd h hbi_ne, hm_p'⟩
    · have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hfal_p1 : ∀ k < (i + 1#32).toNat,
          s_p.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
        intro k hk; rw [hi1_nat] at hk
        rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · have hk_lt_sp : (tmp5[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem k (by omega))
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hk_lt_sp) (hfal_as _ hk_lt_sp (hfalp k hk'))
        · rw [← hlit_eq]
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hlit_lt) hlit_as_ff
      exact hJ_jn _ _ ⟨ext_p, s_p, hext_p, hinit_p', hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p',
        hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

private theorem viv_clr_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_f : FullState} {cref : BitVec 32}
    (hspf : FullSparseInvW c F0 F_cur s_f)
    (href_f : cref.toNat ∈ fullArenaClauseRefs s_f)
    (hcr_f_lt : cref.toNat < s_f.core.arena.length) :
    let hdr_v := (s_f.core.arena[cref.toNat]'hcr_f_lt) &&& ~~~0x00100000#32
    let s_v : FullState :=
      { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
    FullSparseInvW c F0 F_cur s_v ∧ fullArenaClauseRefs s_v = fullArenaClauseRefs s_f := by
  let hdr_f := s_f.core.arena[cref.toNat]'hcr_f_lt
  have hhdr_f : fullArenaHdr s_f cref.toNat = hdr_f := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_f_lt, Option.getD_some]
  let hdr_v := hdr_f &&& ~~~0x00100000#32
  obtain ⟨hsp_v, hrefs_v, _⟩ :=
    fullSparseInvW_set_hdr_non_gs hspf href_f hdr_v
      s_f.core.num_irred s_f.core.num_redundant
      (by rw [hhdr_f]; exact bv32_clr_viv_garb hdr_f)
      (by rw [hhdr_f]; exact bv32_clr_viv_shrk hdr_f)
  exact ⟨hsp_v, hrefs_v⟩

private theorem viv_assign_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {lit : BitVec 32} (hspp : FullSparseInvW c F0 F_cur sp)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let nlvl := sp.core.cur_level + 1
    let dlit := lit ^^^ 1#32
    let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
    let fdec' := sp.core.frame_dec.set nlvl dlit
    let s_pre : FullState :=
      { sp with core :=
        { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
    sp.core.trail_end < c.max_vars ∧ nlvl ≤ c.max_vars ∧
    s_pre.LengthsOk c ∧
    ¬ (s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
       c.max_vars ≤ s_pre.core.trail_end ∨
       s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8) := by
  have hsp_len := hspp.1.core_ok
  have hte_lt : sp.core.trail_end < c.max_vars := by
    have := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
    have := hsp_len.cur_vars_le; omega
  have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
    have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
  let nlvl := sp.core.cur_level + 1
  let dlit := lit ^^^ 1#32
  let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
  let fdec' := sp.core.frame_dec.set nlvl dlit
  let s_pre : FullState :=
    { sp with core :=
      { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
  have hlen_pre : s_pre.LengthsOk c :=
    ⟨{ hsp_len with
         frame_trail_len := by simp [s_pre, ftrl', hsp_len.frame_trail_len],
         frame_dec_len := by simp [s_pre, fdec', hsp_len.frame_dec_len] },
     hspp.1.scratch_ok⟩
  have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := viv_bv32_xor1_toNat lit
  have hdlit_lt : dlit.toNat < 2 * sp.core.cur_vars := viv_bv32_xor1_lt hlit_lt
  have hdlit_zero : sp.core.vals[dlit.toNat]?.getD 0#8 = 0#8 :=
    hdlit_nat ▸ vals_xor1_eq_zero hspp.2.1 hlit_lt hlv0
  refine ⟨hte_lt, hnlvl_le, hlen_pre, fun hor => ?_⟩
  have h1xor : (lit ^^^ 1 : BitVec 32).toNat = dlit.toNat := rfl
  rw [h1xor] at hor
  rcases hor with h1 | h2 | h3
  · dsimp only [s_pre] at h1; omega
  · have := hsp_len.cur_vars_le; dsimp only [s_pre] at h2; omega
  · exact h3 hdlit_zero

private theorem viv_vals_ff_of_ne {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {lit : BitVec 32} (hspp : FullSparseInvW c F0 F_cur sp)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hlit_lt_vals : lit.toNat < sp.core.vals.length)
    (hne0_raw : (sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32 ≠ 0#32)
    (hflt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32) = false) :
    sp.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
  have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
  have hlv_eq : sp.core.vals[lit.toNat]? = some (sp.core.vals[lit.toNat]'hlit_lt_vals) :=
    List.getElem?_eq_getElem hlit_lt_vals
  have hne1 : sp.core.vals[lit.toNat]'hlit_lt_vals ≠ 1#8 := fun heq => by
    have hgt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32) = true := by
      rw [heq]; decide
    exact Bool.false_ne_true (hflt.symm.trans hgt)
  have hne0 : sp.core.vals[lit.toNat]'hlit_lt_vals ≠ 0#8 := fun heq => by
    have heq0 : (sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32 = 0#32 := by
      rw [heq]; decide
    exact hne0_raw heq0
  rw [hlv_eq, Option.getD_some]
  rcases (by simpa [hlv_eq] using hdom) with h | h | h
  · exact absurd h hne0
  · exact absurd h hne1
  · exact h

private theorem viv_post_reuse_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 s4r s5 : FullState} {cref sz : BitVec 32} {lits2 : List Nat}
    (hs5 : s5 = { s4r with core :=
      { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } })
    (hlits2 : lits2 = fullArenaClauseLits s2 cref.toNat)
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hsp4r : FullSparseInvW c F0 F_cur s4r)
    (hcv4r : s4r.core.cur_vars = s2.core.cur_vars)
    (hpr4r : s4r.core.probing = s2.core.probing)
    (har4r : s4r.core.arena = s2.core.arena) (hal4r : s4r.core.arena_len = s2.core.arena_len)
    (hfl4r : s4r.core.fuel = s2.core.fuel) (hrr4r : s4r.scratch.red_refs = s2.scratch.red_refs)
    (hcv1 : s2.core.cur_vars = s.core.cur_vars) (hpr1 : s2.core.probing = s.core.probing)
    (hfl1 : s2.core.fuel.toNat ≤ s.core.fuel.toNat) (hal1 : s2.core.arena_len = s.core.arena_len)
    (hrefs1 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hrr1 : s2.scratch.red_refs = s.scratch.red_refs)
    (href2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat) :
    FullSparseInvW c F0 F_cur s5 ∧
    s5.core.cur_vars = s.core.cur_vars ∧ s5.core.probing = s.core.probing ∧
    s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    s5.core.arena_len = s.core.arena_len ∧ fullArenaClauseRefs s5 = fullArenaClauseRefs s ∧
    s5.scratch.red_refs = s.scratch.red_refs ∧ cref.toNat ∈ fullArenaClauseRefs s5 ∧
    fullArenaClauseGarb s5 cref.toNat = false ∧ fullArenaClauseSize s5 cref.toNat = sz.toNat ∧
    (fullArenaClauseLits s5 cref.toNat).Perm lits2 ∧
    ∀ l ∈ lits2, l < 2 * s.core.cur_vars := by
  subst hs5 hlits2
  have hrefs_eq4r : fullArenaClauseRefs
      { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } } =
      fullArenaClauseRefs s2 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; change _ = _; rw [har4r, hal4r]
  refine ⟨viv_with_confl hsp4r 0#64 0xFFFFFFFF#64,
    hcv4r.trans hcv1, hpr4r.trans hpr1,
    by change s4r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl4r]; exact hfl1,
    hal4r.trans hal1, hrefs_eq4r.trans hrefs1, hrr4r.trans hrr1, hrefs_eq4r ▸ href2, ?_, ?_, ?_, ?_⟩
  · unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    change (s4r.core.arena[cref.toNat]?.getD 0#32 &&& 0x00080000#32 != 0#32) = false
    rw [har4r]; exact hng2
  · unfold fullArenaClauseSize fullArenaClauseSizeCore
    change (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat = sz.toNat; rw [har4r]; exact hsz2
  · have heq : fullArenaClauseLits
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
        cref.toNat = fullArenaClauseLits s2 cref.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      change ((s4r.core.arena.drop (cref.toNat + 3)).take
        (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat = _
      rw [har4r]
    rw [heq]
  · exact fun l hl => by
      rw [← hcv1]; exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 l hl

/-! ## 4. `full_viv_clause_m6_wp` -/

theorem full_viv_clause_m6_wp (Γ : Env)
    (hL0Simp : Γ.Has "full_viv_l0_simp_m6" fullVivL0SimpM6Spec)
    (hSort : Γ.Has "full_viv_sort_counts_m6" fullVivSortCountsM6Spec)
    (hReuse : Γ.Has "full_viv_reuse_prefix_m6" fullVivReusePrefixM6Spec)
    (hBestImpl : Γ.Has "full_viv_best_implied_m6" fullVivBestImpliedM6Spec)
    (hAssign : Γ.Has "full_assign" fullAssignSpec)
    (hPropIgn : Γ.Has "full_propagate_ignore" PropSearch.Spec.propIgnoreM6Spec)
    (hBacktrack : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hFinish : Γ.Has "full_viv_finish_m6" vivFinishM6Spec) :
    ∀ a m Q X, vivClauseM6Spec a m Q X → Func.wp Γ full_viv_clause_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hcfg, hext0, hsp0, href0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have hwf0 := hsp0.2.1.arena.refs_wf cref.toNat href0; have hcl0 := hsp0.1.core_ok
  have hcr0_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
  have hcr0_bv0 : (cref.setWidth 64).toNat < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr2_nat : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcr2_lt0 : cref.toNat + 2 < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr2_bv0 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  have hm0_f := fullM6HdrMem_focus_full hm0
  have hinit0 := viv_ext_pres_refl ext0
  have htriv0 := hQ 1#64 ext0 s m0 hext0 hinit0 hsp0 rfl rfl (Nat.le_refl _) rfl rfl rfl
    (Or.inl rfl) (fun h => by cases h) hm0
  unfold Func.wp full_viv_clause_m6_body
  viv_steps
  · exact htriv0
  · exact htriv0
  · exact htriv0
  · have hgb_eq : (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0 &&& 0x00080000#32) = 0#32 := by
      c0_bound
    have hng0 : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      have hg : s.core.arena[cref.toNat]? =
          some (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0) := by
        rw [← hcr0_nat, List.getElem?_eq_getElem hcr0_bv0]
      rw [hg, Option.getD_some, hgb_eq]; rfl
    let sz0 := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv0
    have hsz0_eq : sz0 = s.core.arena[cref.toNat + 2]'hcr2_lt0 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv0, hcr2_nat, List.getElem?_eq_getElem hcr2_lt0])
    have hsz0_nat : sz0.toNat = fullArenaClauseSize s cref.toNat := by
      rw [hsz0_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt0, Option.getD_some]
    viv_call hL0Simp
    refine ⟨c, F0, F_cur, s, (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl, hsp0, href0, hng0,
      hsz0_nat, hm0_f,
      fun l0r s1 m1 hsp1 hcv1 hpr1 hfl1_eq hal1 hrefs1 hrr1 hl0r h20_1 h0_1 hm1 => ?_⟩
    have hfl1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfl1_eq]; exact Nat.le_refl _
    by_cases hl0 : l0r ≠ 0#64
    · rcases hl0r with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · viv_steps; exact hQ 1#64 ext0 s1 _ hext0 hinit0 hsp1 hcv1 hpr1 hfl1 hal1 hrefs1 hrr1
          (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm1)
      · viv_steps; exact hQ 2#64 ext0 s1 _ hext0 hinit0 hsp1 hcv1 hpr1 hfl1 hal1 hrefs1 hrr1
          (Or.inr (Or.inl rfl)) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm1)
      · viv_steps; exact hQ 20#64 ext0 s1 _ hext0 hinit0 hsp1 hcv1 hpr1 hfl1 hal1 hrefs1 hrr1
          (Or.inr (Or.inr rfl)) (fun _ => h20_1 rfl) (fullM6HdrMem_unfocus_full hm1)
    obtain rfl : l0r = 0#64 := Classical.not_not.mp hl0
    viv_steps
    · contradiction
    obtain ⟨href1, hng1⟩ := h0_1 rfl
    have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
    have hcl1 := hsp1.1.core_ok
    have hcr2_lt1 : cref.toNat + 2 < s1.core.arena.length := by
      have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
    have hcr2_bv1 : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by omega
    have htriv1 := hQ 1#64 ext0 s1 _ hext0 hinit0 hsp1 hcv1 hpr1 hfl1 hal1 hrefs1 hrr1
      (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm1)
    viv_steps
    · exact htriv1
    · exact htriv1
    let sz := s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv1
    have hsz_eq : sz = s1.core.arena[cref.toNat + 2]'hcr2_lt1 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv1, hcr2_nat, List.getElem?_eq_getElem hcr2_lt1])
    have hsz_nat : sz.toNat = fullArenaClauseSize s1 cref.toNat := by
      rw [hsz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt1, Option.getD_some]
    have hsz_le_cv : sz.toNat ≤ s1.core.cur_vars := by
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := hcl1.cur_vars_le; omega
      have hc0 : ¬ (BitVec.ofNat 64 s1.core.cur_vars).toNat < (sz.setWidth 64).toNat := by
        c0_bound
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt, bv32_setWidth64_toNat] at hc0
      omega
    have hsz_le_mv : sz.toNat ≤ c.max_vars := by have := hcl1.cur_vars_le; omega
    let s2 : FullState := s1; have hsp2 : FullSparseInvW c F0 F_cur s2 := hsp1
    have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := href1
    have hng2 : fullArenaClauseGarb s2 cref.toNat = false := hng1
    have hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat := hsz_nat.symm
    have har2_len : s2.core.arena.length = c.arena_cap := hsp2.1.core_ok.arena_len_arr
    have htmp2_len : s2.core.tmp.length = c.max_vars := hsp2.1.core_ok.tmp_len_arr
    have hbd2 : cref.toNat + 3 + sz.toNat ≤ s2.core.arena.length := by
      have := hwf1.2.2.1; have := hwf1.2.2.2.1; have := hcl1.arena_len_le
      rw [hsz_nat]
      change cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤ s2.core.arena.length
      omega
    clear hL0Simp hwf0 hcl0 hgb_eq hfl1_eq h20_1 h0_1 hm0 hm0_f; viv_steps
    refine wp_loop_inv (ts := [i32])
      (fun (i, ()) mc => ∃ tmpc : List (BitVec 32),
        i.toNat ≤ sz.toNat ∧ tmpc.length = c.max_vars ∧
        (∀ k < i.toNat, tmpc[k]? = s2.core.arena[cref.toNat + 3 + k]?) ∧
        (FullMem c { s2 with core := { s2.core with tmp := tmpc } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mc)
      (fun (i, ()) _ => sz.toNat - i.toNat)
      (fun Jc hJc => by
        viv_steps
        exact hJc (0#32, ()) _ ⟨s2.core.tmp, Nat.zero_le _, htmp2_len,
          fun _ hk => by simp at hk, hm1⟩)
      (fun Jc ⟨i, ⟨⟩⟩ mc ⟨tmpc, hi_le, htc_len, hcp, hmc⟩ ihc => ?_)
    viv_steps
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hidx_nat : (cref.setWidth 64 + 3 + i.setWidth 64).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
      have hi_lt_ar : (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s2.core.arena.length := by
        omega
      have hi_lt_tmp : i.toNat < tmpc.length := by omega
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      viv_steps
      let tmpc' := tmpc.set i.toNat (s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega))
      have har_eq : s2.core.arena[(cref.setWidth 64 + 3 + i.setWidth 64).toNat]'hi_lt_ar =
          s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem hi_lt_ar, hidx_nat, List.getElem?_eq_getElem (by omega)])
      refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
        ⟨tmpc', by omega, by simp [tmpc', htc_len], fun k hk => ?_, ?_⟩
      · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · dsimp only [tmpc']; rw [List.getElem?_set_ne (by omega)]; exact hcp k hk'
        · dsimp only [tmpc']
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · simpa only [tmpc', hi64_nat, har_eq] using hm
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
      rw [hi_eq] at hcp
      have htmpc_lits_lt : ∀ k < sz.toNat, (tmpc[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hmem : (tmpc[k]?.getD 0#32).toNat ∈ fullArenaClauseLits s2 cref.toNat := by
          have := (viv_tmp_mem_of_perm (by omega)
            (vivCopy_perm_lits (by omega) hbd2 hcp
              (List.Perm.refl (tmpc.take sz.toNat)) (by omega))).1 k hk
          simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
        have := hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
        have := hsp2.1.core_ok.cur_vars_le; omega
      viv_call hSort
      refine ⟨c, { s2 with core := { s2.core with tmp := tmpc } },
        (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl,
        ⟨{ hsp2.1.core_ok with tmp_len_arr := htc_len }, hsp2.1.scratch_ok⟩,
        hsz_le_mv, htmpc_lits_lt, hmc, fun tmp4 m4 htmp4_len hperm4 _ hm4 => ?_⟩
      have hperm_lits4 : ((tmp4.take sz.toNat).map BitVec.toNat).Perm
          (fullArenaClauseLits s2 cref.toNat) := by
        have := vivCopy_perm_lits (by omega) hbd2 hcp hperm4 (by omega)
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
      let s4 : FullState := { s2 with core := { s2.core with tmp := tmp4 } }
      have hsp4 : FullSparseInvW c F0 F_cur s4 := viv_with_tmp hsp2 htmp4_len
      have htmp4_lt_cv : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat < 2 * s4.core.cur_vars := by
        intro k hk
        have hmem := (viv_tmp_mem_of_perm (by omega) hperm_lits4).1 k hk
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
      viv_steps
      viv_call hReuse
      refine ⟨c, F0, F_cur, s4, (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl, hsp4,
        hsz_le_mv, htmp4_lt_cv, hm4,
        fun s4r m4r hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hm4r => ?_⟩
      let tmp5 := s4r.core.tmp
      let lits2 := fullArenaClauseLits s2 cref.toNat
      have hperm_lits5 : ((tmp5.take sz.toNat).map BitVec.toNat).Perm lits2 := by
        dsimp only [tmp5, lits2]; rw [htmp4r]; exact hperm_lits4
      obtain ⟨htmp5_mem, hlits5_inv⟩ := viv_tmp_mem_of_perm
        (by rw [show tmp5.length = c.max_vars from hsp4r.1.core_ok.tmp_len_arr]; omega)
        hperm_lits5
      viv_to_group
      let s5 : FullState :=
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
      obtain ⟨hsp5, hcv5, hpr5, hfl5, hal5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hlits2_lt⟩ :=
        viv_post_reuse_facts (s5 := s5) (lits2 := lits2) rfl rfl hsp2 hsp4r
          hcv4r hpr4r har4r hal4r hfl4r hrr4r hcv1 hpr1 hfl1 hal1 hrefs1 hrr1 href2 hng2 hsz2
      have hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2 := htmp5_mem
      have hlits2_inv : ∀ l ∈ lits2, ∃ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat = l := hlits5_inv
      have hct5 : s5.core.confl_type = 0#64 := rfl
      have htmp5 : s5.core.tmp = tmp5 := rfl
      have htmp5_len : tmp5.length = c.max_vars := hsp4r.1.core_ok.tmp_len_arr
      have hm5 : (FullMem c s5 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m := hm
      clear_value s5 s4 s2 tmp5 lits2
      clear hSort hReuse har_cap hm hwf1 hperm4 hperm_lits4 htmp5_mem hlits5_inv hsp4 hsp2
        s4 href2 hng2 hsz2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1 hcv1 hpr1
        hfl1 hal1 hrefs1 hrr1 href1 hng1 hcl1 hsz_nat hsz_le_cv hsp0 href0
        hng0 hm1 hm4 hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r htmp4_lt_cv
      try clear hi_eq ihc hmc hcp htc_len hi_le tmpc mc Jc i s2 s4r
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
        (VivClauseBrkInv c F0 F_cur ext0 s R cref sz tmp5 lits2)
        (VivClauseLoopInv c F0 F_cur ext0 s R cref sz tmp5 lits2) ?_ ?_ ?_
      · rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
          ⟨extb, sb, hextb, hinitb, hspb, hcvb, halb, hprb, htmpb, hflb, hrefsb, hrrb, hrefb, hngb,
           hszb, hpermb, hcokb, himplb, hfalb, hmb⟩
        viv_steps
        viv_call hFinish
        refine ⟨c, F0, F_cur, extb, sb, R, rfl, hcfg, hextb, hspb, hsz_le_mv,
          hrefb, hngb, hszb, (by rw [htmpb]; exact hperm_lits5.trans hpermb.symm),
          hcokb, himplb,
          fun hc hi hall => hfalb hc hi (by
            revert hall; cases Decidable.em (i_b = sz) <;> simp [*]),
          fullM6HdrMem_unfocus_full hmb,
          fun r_f ext_f s_f m_f hext_f hinit_f hspf hcvf hprf hflf half hrefsf hrrf hrf h20f
            hm_f => ?_⟩
        clear hFinish hBestImpl hAssign hPropIgn hBacktrack hsz_le_mv hspb hcokb himplb hfalb hmb
        have hinit_f' := viv_ext_pres_trans hinitb hinit_f
        have href_f : cref.toNat ∈ fullArenaClauseRefs s_f := hrefsf ▸ hrefb
        have hwf_f := hspf.2.1.arena.refs_wf cref.toNat href_f
        have hcr_f_lt : cref.toNat < s_f.core.arena.length := by
          have := hspf.1.core_ok.arena_len_arr; have := hspf.1.core_ok.arena_len_le; omega
        have hcr_f_bv : (cref.setWidth 64).toNat < s_f.core.arena.length := by omega
        have hm_f_foc := fullM6HdrMem_focus_full hm_f
        viv_steps
        · obtain ⟨hsp_v, hrefs_v⟩ := viv_clr_hdr_ok hspf href_f hcr_f_lt
          let hdr_v := (s_f.core.arena[cref.toNat]'hcr_f_lt) &&& ~~~0x00100000#32
          let s_v : FullState :=
            { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
          have hm_v : (FullMem c s_v ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_f ⋆ R)) m := by
            dsimp only [s_v, hdr_v]
            rw [← show (1048576#32 : BitVec 32) = 0x00100000#32 from rfl,
              ← show (1048576 : BitVec 32) = 1048576#32 from rfl]
            simpa only [hcr0_nat] using hm
          exact hQ r_f ext_f _ m hext_f hinit_f' hsp_v (hcvf.trans hcvb) (hprf.trans hprb)
            (Nat.le_trans hflf hflb) (half.trans halb) (hrefs_v.trans (hrefsf.trans hrefsb))
            (hrrf.trans hrrb) hrf h20f (fullM6HdrMem_unfocus_full hm_v)
        all_goals
          exact hQ r_f ext_f s_f m_f hext_f hinit_f' hspf (hcvf.trans hcvb) (hprf.trans hprb)
            (Nat.le_trans hflf hflb) (half.trans halb) (hrefsf.trans hrefsb) (hrrf.trans hrrb)
            hrf h20f hm_f
      · intro B L rem ⟨i, ⟨⟩⟩ mp hB hL
          ⟨extp, sp, hi_le, hrem, hextp, hinitp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp,
           hrrp, hrefp, hngp, hszp, hpermp, hct0, hfalp, hmp⟩
        clear hFinish
        viv_steps
        · have hi_lt : i.toNat < sz.toNat := by c0_bound
          have hi_ne_sz : i ≠ sz := fun heq => by rw [heq] at hi_lt; exact Nat.lt_irrefl _ hi_lt
          have hsp_len := hspp.1.core_ok
          have hi_lt_tmp : i.toNat < sp.core.tmp.length := by rw [hsp_len.tmp_len_arr]; omega
          have hlit_lt_cv : (tmp5[i.toNat]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem i.toNat hi_lt)
          have hlit_lt_vals : (tmp5[i.toNat]?.getD 0#32).toNat < sp.core.vals.length := by
            rw [hsp_len.vals_len]; have := hsp_len.cur_vars_le; omega
          have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
          have hi_lt_tmp64 : (i.setWidth 64).toNat < sp.core.tmp.length := by
            rw [hi64_nat]; exact hi_lt_tmp
          have htmp_i_eq : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 =
              tmp5[i.toNat]?.getD 0#32 := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hi_lt_tmp64, htmpp, hi64_nat,
              List.getElem?_eq_getElem (by omega), Option.getD_some])
          have htmp_i_lt' : (sp.core.tmp[(i.setWidth 64).toNat].setWidth 64).toNat <
              sp.core.vals.length := by rw [bv32_setWidth64_toNat, htmp_i_eq]; exact hlit_lt_vals
          let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
          have hlit_eq : lit = tmp5[i.toNat]?.getD 0#32 := Option.some.inj (by
            dsimp only [lit]
            rw [← List.getElem?_eq_getElem hi_lt_tmp, htmpp,
              List.getElem?_eq_getElem (by omega), Option.getD_some])
          have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
            rw [htmp_i_eq, hlit_eq]
          have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := by rw [hlit_eq]; exact hlit_lt_cv
          have hlit_lt_vals' : lit.toNat < sp.core.vals.length := by
            rw [hlit_eq]; exact hlit_lt_vals
          viv_to_group
          · have htmp_sp_lt : ∀ k < sz.toNat,
                (sp.core.tmp[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := fun k hk => by
              rw [htmpp, hcvp]; exact hlits2_lt _ (hlits2_mem k hk)
            viv_call hBestImpl
            refine ⟨c, F0, F_cur, sp, (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R), rfl, hspp,
              hsz_le_mv, htmp_sp_lt, hmp, fun bi hbi => ?_⟩
            viv_steps
            exact hB (i, false, bi, ()) mp ⟨extp, sp, hextp, hinitp, hspp, hcvp, halp, hprp,
              htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
              fun _ hne => hbi hne, fun _ _ heq => absurd heq hi_ne_sz, hmp⟩
          · refine wp_join_group (ts := [.bool, i32])
              (VivClauseJoinInv c F0 F_cur ext0 s R cref sz i tmp5 lits2) ?_ ?_
            · rintro _ ⟨confl_j, impl_j, ⟨⟩⟩ m_jn ⟨ext_jn, s_jn, hext_jn, hinit_jn, hsp_jn,
                hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn, hrefs_jn, hrr_jn, href_jn, hng_jn,
                hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
              have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              viv_steps
              exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by (try dsimp only); (try rw [hi1_nat]); omega)
                ⟨ext_jn, s_jn, by omega, rfl, hext_jn, hinit_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn,
                 htmp_jn, hfl_jn, hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn,
                 hperm_jn, hct_jn, hfal_jn, hm_jn⟩
            · intro J_jn hJ_jn
              viv_steps
              · exfalso
                have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hnlvl_le := (viv_assign_prep hspp hlit_lt hlv0).2.1
                have hc0 : c.max_vars % 2 ^ 64 <
                    (sp.core.cur_level + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by assumption
                have h1n : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h1n] at hc0; omega
              · have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                obtain ⟨hte_lt, hnlvl_le, hlen_pre, hnot_guard⟩ :=
                  viv_assign_prep hspp hlit_lt hlv0
                have hnlvl_nat : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat =
                    sp.core.cur_level + 1 := by bv_omega
                have hnlvl_lt_ft : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_trail.length := by rw [hnlvl_nat, hsp_len.frame_trail_len]; omega
                have hnlvl_lt_fd : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_dec.length := by rw [hnlvl_nat, hsp_len.frame_dec_len]; omega
                viv_steps
                let nlvl := sp.core.cur_level + 1
                let dlit := lit ^^^ 1#32
                let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
                let fdec' := sp.core.frame_dec.set nlvl dlit
                let s_pre : FullState :=
                  { sp with core :=
                    { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
                have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 sp.core.trail_end) =
                    BitVec.ofNat 32 sp.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                rw [hlit_i64]
                viv_call hAssign
                refine ⟨c, s_pre, (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R), rfl, hlen_pre,
                  by dsimp [s_pre, nlvl]; omega,
                  (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]
                      exact (by assumption)),
                  ?_⟩
                by_cases hguard : s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8
                · exact absurd hguard hnot_guard
                simp only [hguard, ↓reduceIte]
                intro flags' unass' phases' m_as hfll' hphl' hm_as
                have hnlvl_ne0 : nlvl ≠ 0 := by omega
                simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
                obtain ⟨_, hsp_as, hfal_as, hlit_as_ff⟩ :=
                  viv_decide_assign_preserves_sparseW hspp hlit_lt hlv0 hfll' hphl'
                let s_as : FullState :=
                  { sp with
                    core :=
                      { sp.core with
                        vals := (sp.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
                        flags := flags',
                        lvl := sp.core.lvl.set (dlit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sp.core.rsns.set (dlit.toNat / 2) 0xFFFFFFFF#32,
                        trl := sp.core.trl.set sp.core.trail_end dlit,
                        trail_pos := sp.core.trail_pos.set (dlit.toNat / 2)
                          (BitVec.ofNat 32 sp.core.trail_end),
                        frame_trail := ftrl', frame_dec := fdec',
                        trail_end := sp.core.trail_end + 1, cur_level := nlvl,
                        unassigned := unass' }
                    scratch := { sp.scratch with phases := phases' } }
                clear_value s_as
                try clear hm_as hlen_pre hguard hnot_guard
                viv_steps
                exact viv_clause_prop_step Γ hPropIgn hBacktrack hBestImpl hcfg hextp
                  hinitp hQ hB hJ_jn hsp_as hsz_le_mv hcvp rfl halp rfl hprp rfl hflp rfl
                  hrefsp rfl hrrp hrefp hngp hszp hpermp rfl hct0 htmpp hlits2_lt hlits2_mem
                  hi_lt hlit_eq hlit_lt hfalp hfal_as hlit_as_ff hm_as
              · have hlv_ff := viv_vals_ff_of_ne hspp hlit_lt hlit_lt_vals'
                  (by assumption) (by assumption)
                have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                viv_steps
                exact hJ_jn _ _ ⟨extp, sp, hextp, hinitp, hspp, hcvp, halp, hprp, htmpp, hflp,
                  hrefsp, hrrp, hrefp, hngp, hszp, hpermp, hct0, fun k hk => by
                    rw [hi1_nat] at hk
                    rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
                    · exact hfalp k hk'
                    · rw [← hlit_eq]; exact hlv_ff,
                  hmp⟩
        · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
          have hfal_all : ∀ l ∈ fullArenaClauseLits sp cref.toNat,
              sp.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            intro l hl
            obtain ⟨k, hk, hget⟩ := hlits2_inv l (hpermp.mem_iff.mp hl)
            rw [← hget]; exact hfalp k (by omega)
          viv_steps
          exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨extp, sp, hextp, hinitp, hspp, hcvp, halp,
            hprp, htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
            fun _ h => absurd rfl h, fun _ _ _ => ⟨hct0, hfal_all⟩, hmp⟩
      · intro B L _ hL
        viv_steps
        exact hL sz.toNat (0#32, ()) _ ⟨ext0, s5, Nat.zero_le _,
          by rw [BitVec.toNat_ofNat]; simp, hext0, hinit0,
          hsp5, hcv5, hal5, hpr5, htmp5, hfl5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hct5,
          fun _ hk => by simp at hk, hm5⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
