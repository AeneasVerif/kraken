/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Vivify Instantiation Strengthening WP Proof (`Proof.Vivify.WpInst`)

Parametric `(Γ : Env)` `Func.wp` certification (`public section`, zero legacy imports, zero SAT
model proofs) for `full_viv_inst_m6` (`Spec.vivInstM6Spec`) over `FullM6HdrMem`, certifying both
resolvent entailment (`inst_resolve_entails` when `ant_sz = -1`) and subsuming-witness entailment
(`viv_inst_sub_witness_entails` when `ant_sz ≠ -1`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Pure & Decision-Assign Helpers -/

private theorem inst_bv32_setWidth64_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

private theorem inst_tmp_lt_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cref sz : BitVec 32}
    (hsp : FullSparseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (hperm : ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s cref.toNat)) :
    ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  intro k hk
  have hk_tmp : k < s.core.tmp.length := by rw [hsp.1.core_ok.tmp_len_arr]; omega
  have hmem : (s.core.tmp[k]?.getD 0#32).toNat ∈ fullArenaClauseLits s cref.toNat := by
    apply hperm.mem_iff.mp
    rw [List.mem_map]
    refine ⟨s.core.tmp[k]'hk_tmp, ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    · rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some]
  exact hsp.2.1.arena.lits_lt cref.toNat href hng _ hmem

/-- Positive decision step (`cur_level := cur_level + 1`, storing `frame_trail`/`frame_dec`,
then calling `full_assign(h, lit, 0xFFFFFFFF#32)`) preserves `FullSparseInvW c F0 F_cur`. -/
private theorem inst_decideAssign_preserves_sparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {lit : BitVec 32}
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)}
    {unass' unfl' : BitVec 64} (hfll : flags'.length = c.max_vars)
    (hphl : phases'.length = c.max_vars) :
    let nlvl := s.core.cur_level + 1
    let v := lit.toNat / 2
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unass', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    nlvl ≤ c.max_vars ∧ FullSparseInvW c F0 F_cur s' ∧
    s'.core.trl[s.core.trail_end]?.getD 0#32 = lit ∧
    s'.core.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
  intro nlvl v ftrl' fdec' s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars :=
    hw.trail_end_lt_of_unassigned hlit hun
  have hnlvl_le : nlvl ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hnlvl_lt32 : nlvl < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
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
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
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
        · exact hlit
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
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
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
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr
              ⟨i, by dsimp [s'] at hi; omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by dsimp [s']; omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by dsimp [s']; omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by dsimp [s'] at hi; omega); rw [heq] at h
              rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
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
            Option.getD_some]; exact hlit
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
  refine ⟨hnlvl_le, ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩, ?_, ?_⟩
  · dsimp only [s']
    rw [List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max), Option.getD_some]
  · exact (hrsn_get v (by omega)).trans (by simp)

private theorem inst_entails_of_deduce {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ws2_d : List (BitVec 32)} {cref sz iolen lit : BitVec 32}
    (hsp0 : FullSparseInvW c F0 F_cur s)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s)
    (hng0 : fullArenaClauseGarb s cref.toNat = false)
    (hsz1 : 1 ≤ sz.toNat) (hsz_le : sz.toNat ≤ c.max_vars)
    (hperm0 : ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s cref.toNat))
    (hlit_eq : lit = s.core.tmp[sz.toNat - 1]'(by rw [hsp0.1.core_ok.tmp_len_arr]; omega))
    (hiol_le : iolen.toNat ≤ ws2_d.length)
    (hws2_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((ws2_d.take iolen.toNat).map BitVec.toNat)))
    (hsub_ic : ∀ i < iolen.toNat,
      ws2_d[i]?.getD 0#32 = lit ^^^ 1#32 ∨
      ∃ j, j + 1 < sz.toNat ∧ ws2_d[i]?.getD 0#32 = s.core.tmp[j]?.getD 0#32) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat)) := by
  have hcl0 := hsp0.1.core_ok
  have hfull : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat) ++ [lit.toNat])) := by
    have hsnoc : (s.core.tmp.take sz.toNat).map BitVec.toNat =
        ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat) ++ [lit.toNat] := by
      rw [viv_take_snoc (by omega) (by rw [hcl0.tmp_len_arr]; omega),
        List.map_append, List.map_singleton, ← hlit_eq]
    rw [← hsnoc]
    exact viv_entails_of_perm hperm0 (hsp0.2.1.arena.entails cref.toNat href0 hng0)
  refine inst_resolve_entails hws2_ent hfull fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [List.mem_iff_getElem] at hy
  obtain ⟨idx, hidx, hyeq⟩ := hy
  have hidx_lt : idx < iolen.toNat := by rw [List.length_take] at hidx; omega
  have hyeq' : ws2_d[idx]?.getD 0#32 = y := by
    have hlt_w : idx < ws2_d.length := by omega
    rw [List.getElem?_eq_getElem hlt_w, Option.getD_some]
    simpa [List.getElem_take] using hyeq
  rcases hsub_ic idx hidx_lt with heq_not | ⟨j, hj, heq_j⟩
  · left; rw [← hyeq', heq_not, viv_bv32_xor1_toNat]
  · right; rw [List.mem_map]
    refine ⟨y, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨j, by rw [List.length_take, hcl0.tmp_len_arr]; omega, ?_⟩
    rw [List.getElem_take, ← hyeq', heq_j]
    have hlt_t : j < s.core.tmp.length := by rw [hcl0.tmp_len_arr]; omega
    change s.core.tmp[j]'hlt_t = (s.core.tmp[j]?.getD 0#32)
    rw [List.getElem?_eq_getElem hlt_t, Option.getD_some]

private theorem inst_entails_of_sub {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_p : FullState} {sz lit : BitVec 32}
    (hsp0 : FullSparseInvW c F0 F_cur s)
    (hsp_p : FullSparseInvW c F0 F_cur s_p)
    (hsz1 : 1 ≤ sz.toNat) (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_p : s_p.core.tmp = s.core.tmp)
    (hlit_eq : lit = s.core.tmp[sz.toNat - 1]'(by rw [hsp0.1.core_ok.tmp_len_arr]; omega))
    (hsub_w : VivDeduceSubWitness F_cur s_p sz.toNat)
    (hlit_val_p : s_p.core.vals[lit.toNat]?.getD 0#8 = 1#8)
    (hlit_rsn_p : s_p.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat)) := by
  have hsz_tmp_p : sz.toNat ≤ s_p.core.tmp.length := by
    rw [hsp_p.1.core_ok.tmp_len_arr]; omega
  have hlast_p : sz.toNat - 1 < s_p.core.tmp.length := by omega
  have hlast_0 : sz.toNat - 1 < s.core.tmp.length := by rw [hsp0.1.core_ok.tmp_len_arr]; omega
  have htmp_last_eq : (s_p.core.tmp[sz.toNat - 1]'hlast_p).toNat = lit.toNat := by
    have h1 : s_p.core.tmp[sz.toNat - 1]?.getD 0#32 = s.core.tmp[sz.toNat - 1]?.getD 0#32 := by
      rw [htmp_p]
    rw [List.getElem?_eq_getElem hlast_p, List.getElem?_eq_getElem hlast_0,
      Option.getD_some, Option.getD_some] at h1
    rw [h1, ← hlit_eq]
  have hent_p := viv_inst_sub_witness_entails hsp_p.2.1 hsz1 hsz_tmp_p hsub_w
    (by rw [htmp_last_eq]; exact hlit_val_p)
    (by rw [htmp_last_eq]; exact hlit_rsn_p)
  rwa [htmp_p] at hent_p

/-! ## 2. Sub-Expression WP Helpers (`backtrack-ret-0` & `copy-commit`) -/

private theorem inst_backtrack_ret0_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext ext' : List (BitVec 64)}
    {s s_f : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m_f : Mem 64}
    (hext' : M6HdrExtOk ext')
    (hpres' : M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext')
    (hsp_f : FullSparseInvW c F0 F_cur s_f)
    (hcl_pos : 0 < s_f.core.cur_level)
    (hcv_f : s_f.core.cur_vars = s.core.cur_vars)
    (hprb_f : s_f.core.probing = s.core.probing)
    (hfl_f : s_f.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hal_f : s_f.core.arena_len = s.core.arena_len)
    (hrefs_f : fullArenaClauseRefs s_f = fullArenaClauseRefs s)
    (hrr_f : s_f.scratch.red_refs = s.scratch.red_refs)
    (hm_f : (FullMem c s_f ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R)) m_f)
    (hQ : ∀ r ext'' s' m', M6HdrExtOk ext'' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext'' ∧ M6ExtW2bPres ext ext'') →
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext'' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
        (Arg.var c.hdr, Arg.var (BitVec.ofNat 64 s_f.core.cur_level - 1), ()) fun _ =>
       Expr.ret (Arg.imm 0, ())) m_f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl_le : s_f.core.cur_level ≤ c.max_vars := by
    have := hsp_f.2.1.cur_level_le; have := hsp_f.1.core_ok.trail_end_le
    have := hsp_f.1.core_ok.cur_vars_le; omega
  have hcl_lt : s_f.core.cur_level < 2 ^ 64 := by omega
  have htgt : (BitVec.ofNat 64 s_f.core.cur_level - 1).toNat = s_f.core.cur_level - 1 := by
    have hcv : (BitVec.ofNat 64 s_f.core.cur_level).toNat = s_f.core.cur_level := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_sub, hcv, h1]; omega
  viv_call hBt
  refine ⟨c, s_f, m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R, rfl, hsp_f.1, hcl_lt,
    fun _ => by rw [htgt]; omega, hsp_f.2.1.trail_lits_lt, hm_f,
    fun vals_2 lvl_2 rsns_2 trl_2 tp_2 te_2 prop_2 cl_2 unass_2 sc_2 m_2
      hlen_2 _ _ _ hpres_2 hsc_2 _ _ hw_2 _ hm_2 => ?_⟩
  have hle_f : (BitVec.ofNat 64 s_f.core.cur_level - 1).toNat ≤ s_f.core.cur_level := by
    rw [htgt]; omega
  have hsp_2 := viv_sparseW_of_backtrack hsp_f hle_f hlen_2 hpres_2
    (hw_2 F0 F_cur hsp_f.2.1 hle_f)
  rcases hsc_2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  viv_hsteps_nogrp
  exact hQ 0#64 ext' _ m_2 hext' hpres' hsp_2 hcv_f hprb_f hfl_f hal_f hrefs_f hrr_f
    (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm_2)

private theorem inst_copy_commit_wp (Γ : Env)
    (hCommit : Γ.Has "full_viv_commit_m6" fullVivCommitM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext ext' : List (BitVec 64)}
    {s s_ic : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {cref sz : BitVec 32}
    {m_ic : Mem 64}
    (hext' : M6HdrExtOk ext')
    (hpres' : M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext')
    (hsp0 : FullSparseInvW c F0 F_cur s)
    (hsp_ic : FullSparseInvW c F0 F_cur s_ic)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s)
    (hng0 : fullArenaClauseGarb s cref.toNat = false)
    (hsz3 : 3 ≤ sz.toNat) (hsz_le : sz.toNat ≤ c.max_vars)
    (hperm0 : ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s cref.toNat))
    (htmp0_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hcv_ic : s_ic.core.cur_vars = s.core.cur_vars)
    (hprb_ic : s_ic.core.probing = s.core.probing)
    (hal_ic : s_ic.core.arena_len = s.core.arena_len)
    (htmp_ic : s_ic.core.tmp = s.core.tmp)
    (hrr_ic : s_ic.scratch.red_refs = s.scratch.red_refs)
    (hfl_ic : s_ic.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hrefs_ic : fullArenaClauseRefs s_ic = fullArenaClauseRefs s)
    (hng_ic : fullArenaClauseGarb s_ic cref.toNat = false)
    (hrest_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat)))
    (hm_ic : (FullMem c s_ic ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R)) m_ic)
    (hQ : ∀ r ext'' s' m', M6HdrExtOk ext'' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext'' ∧ M6ExtW2bPres ext ext'') →
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext'' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js => Blocks.cons (fun p_1 =>
          fvOp (OpCode.cmp CmpOp.ult i32 Ty.bool rfl)
            (Arg.var p_1.fst, Arg.var (sz - 1#32), ()) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (fvOp (OpCode.zext 32 64) (Arg.var p_1.fst, ()) fun p =>
             fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
             fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
             fvOp (OpCode.zext 32 64) (Arg.var p_1.fst, ()) fun p_3 =>
             fvOp (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ()) fun p_4 =>
             fvOp (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_4.fst, ()) fun p_5 =>
             Expr.load i32 (Arg.var p_5.fst) fun ld =>
             Expr.store (Arg.var ld) (Arg.var p.fst)
               (fvOp (OpCode.add i32) (Arg.var p_1.fst, Arg.imm 1, ()) fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.call (as := [i64, i32, i32, i32]) (bs := [i64]) "full_viv_commit_m6"
              (Arg.var c.hdr, Arg.var cref, Arg.var (sz - 1#32), Arg.imm 4294967295, ())
              fun p => Expr.ret (Arg.var p.fst, ()))) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m_ic := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  let nsz : BitVec 32 := sz - 1#32
  have hnsz_nat : nsz.toNat = sz.toNat - 1 := by dsimp only [nsz]; bv_omega
  have hws2_len0 : s_ic.scratch.work_stk2.length = 2 * c.max_vars :=
    hsp_ic.1.scratch_ok.work_stk2_len
  let R_ext := m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R
  refine wp_loop_inv (ts := [i32])
    (fun (k, ()) mk => ∃ ws2k : List (BitVec 32),
      k.toNat ≤ nsz.toNat ∧ ws2k.length = 2 * c.max_vars ∧
      (∀ j < k.toNat, ws2k[j]? = s_ic.core.tmp[j]?) ∧
      (FullMem c { s_ic with scratch := { s_ic.scratch with work_stk2 := ws2k } } ⋆ R_ext) mk)
    (fun (k, ()) _ => nsz.toNat - k.toNat)
    (fun Jk hJk => by
      rw [wp_jump]
      exact hJk (0#32, ()) m_ic ⟨s_ic.scratch.work_stk2, Nat.zero_le _, hws2_len0,
        fun _ hj => by simp at hj, hm_ic⟩)
    (fun Jk ⟨k, ⟨⟩⟩ mk ⟨ws2k, hk_le, hws2k_len, hcp_k, hmk⟩ ihk => ?_)
  rw [Blocks.get_here]; dsimp only [fvOp]
  viv_hsteps_nogrp
  · have hk_lt : k.toNat < nsz.toNat := by c0_bound
    have hk64 : (k.setWidth 64).toNat = k.toNat := inst_bv32_setWidth64_toNat k
    have hk_tmp : (k.setWidth 64).toNat < s_ic.core.tmp.length := by
      rw [hk64, hsp_ic.1.core_ok.tmp_len_arr]; omega
    have hk_ws2 : (k.setWidth 64).toNat < ws2k.length := by rw [hk64]; omega
    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
    viv_hsteps_nogrp
    let ws2k' := ws2k.set k.toNat (s_ic.core.tmp[k.toNat]'(by
      rw [hsp_ic.1.core_ok.tmp_len_arr]; omega))
    have htmp_eq : s_ic.core.tmp[(k.setWidth 64).toNat]'hk_tmp =
        s_ic.core.tmp[k.toNat]'(by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega) :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hk_tmp, hk64,
          List.getElem?_eq_getElem (by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega)])
    refine ihk (k + 1#32, ()) _ (by dsimp only; omega)
      ⟨ws2k', by omega, by simp [ws2k', hws2k_len], fun j hj => ?_, ?_⟩
    · rcases (by omega : j < k.toNat ∨ j = k.toNat) with hj' | rfl
      · dsimp only [ws2k']; rw [List.getElem?_set_ne (by omega)]; exact hcp_k j hj'
      · dsimp only [ws2k']
        rw [List.getElem?_set_self (by omega),
          List.getElem?_eq_getElem (by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega)]
    · simpa only [ws2k', hk64, htmp_eq] using ‹(FullMem c _ ⋆ R_ext) _›
  · have hk_eq : k.toNat = nsz.toNat := by c0_bound
    rw [hk_eq] at hcp_k
    let s_cm : FullState :=
      { s_ic with scratch := { s_ic.scratch with work_stk2 := ws2k } }
    have hsp_cm : FullSparseInvW c F0 F_cur s_cm := viv_with_ws2 hsp_ic hws2k_len
    have htk_eq : ws2k.take nsz.toNat = s.core.tmp.take (sz.toNat - 1) := by
      rw [hnsz_nat]
      exact viv_take_eq_of_copy (by simpa [hnsz_nat, htmp_ic] using hcp_k)
    have hrest_lt : ∀ j < nsz.toNat,
        (ws2k[j]?.getD 0#32).toNat < 2 * s_cm.core.cur_vars := fun j hj => by
      have h1 : ws2k[j]? = s.core.tmp[j]? := by rw [hcp_k j hj, htmp_ic]
      rw [h1, show s_cm.core.cur_vars = s.core.cur_vars from hcv_ic]
      exact htmp0_lt j (by omega)
    have hrest_nd : ((ws2k.take nsz.toNat).map fun x => x.toNat / 2).Nodup := by
      rw [htk_eq]
      exact viv_nodup_prefix_of_perm (by omega) hperm0
        (hsp0.2.2.2.1 cref.toNat href0 hng0)
    viv_call hCommit
    refine ⟨c, F0, F_cur, s_cm, R_ext, rfl, hsp_cm,
      (by simpa [s_cm, hrefs_ic] using href0),
      (by simpa [s_cm] using hng_ic), (by change nsz.toNat ≤ c.max_vars; omega),
      fun _ => ⟨hrest_lt, hrest_nd, by rw [htk_eq]; exact hrest_ent⟩, hmk,
      fun r_c s_f m_f hsp_f hcv_f hal_f hprb_f hfl_f hrefs_f hrr_f _ hr_c h20_c hm_f => ?_⟩
    viv_hsteps_nogrp
    exact hQ r_c ext' s_f m_f hext' hpres' hsp_f (hcv_f.trans hcv_ic) (hprb_f.trans hprb_ic)
      (by rw [hfl_f]; exact hfl_ic) (hal_f.trans hal_ic) (hrefs_f.trans hrefs_ic)
      (hrr_f.trans hrr_ic) (Or.inr hr_c) h20_c (fullM6HdrMem_unfocus_full hm_f)

/-! ## 3. Main WP Proof (`full_viv_inst_m6`) -/

/-- Certification of `full_viv_inst_m6` against `Spec.vivInstM6Spec`. -/
theorem full_viv_inst_m6_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hAs : Γ.Has "full_assign" fullAssignSpec)
    (hProp : Γ.Has "full_propagate_ignore" PropSearch.Spec.propIgnoreM6Spec)
    (hDed : Γ.Has "full_viv_deduce_m6" vivDeduceM6Spec)
    (hChk : Γ.Has "full_viv_inst_check_m6" fullVivInstCheckM6Spec)
    (hCommit : Γ.Has "full_viv_commit_m6" fullVivCommitM6Spec) :
    ∀ a m Q X, vivInstM6Spec a m Q X →
      Func.wp Γ full_viv_inst_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext0, hsp0, href0, hng0, _hsz0, hsz_le, hperm0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  have hcl0_le : s.core.cur_level ≤ c.max_vars := by
    have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hcl0_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  have htmp0_lt := inst_tmp_lt_of_perm hsp0 href0 hng0 hsz_le hperm0
  have hret0 : Q (0#64, ()) m0 :=
    hQ 0#64 ext s m0 hext0 (viv_ext_pres_refl ext) hsp0 rfl rfl (Nat.le_refl _) rfl rfl rfl
      (Or.inl rfl) (fun h => by cases h) hm0
  let R_ext := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  have hm0F : (FullMem c s ⋆ R_ext) m0 := fullM6HdrMem_focus_full hm0
  unfold Func.wp full_viv_inst_m6_body
  viv_hsteps_nogrp
  · exact hret0
  · exact hret0
  · have hcl0_pos : 0 < s.core.cur_level := by
      have hne : BitVec.ofNat 64 s.core.cur_level ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
    have hsz3 : 3 ≤ sz.toNat := by c0_bound
    have hsz1_nat : (sz - 1#32).toNat = sz.toNat - 1 := by bv_omega
    have hsz1_64 : ((sz - 1#32).setWidth 64).toNat = sz.toNat - 1 := by
      rw [inst_bv32_setWidth64_toNat, hsz1_nat]
    have hsz1_tmp : ((sz - 1#32).setWidth 64).toNat < s.core.tmp.length := by
      rw [hsz1_64, hcl0.tmp_len_arr]; omega
    let lit := s.core.tmp[((sz - 1#32).setWidth 64).toNat]'hsz1_tmp
    have hlit_eq : lit = s.core.tmp[sz.toNat - 1]'(by rw [hcl0.tmp_len_arr]; omega) :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hsz1_tmp, hsz1_64,
          List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega)])
    have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have h := htmp0_lt (sz.toNat - 1) (by omega)
      rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
      rwa [hlit_eq]
    have hlit_vl : (lit.setWidth 64).toNat < s.core.vals.length := by
      rw [inst_bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
    have hlit_lv : ((lit >>> 1#32).setWidth 64).toNat < s.core.lvl.length := by
      rw [inst_bv32_setWidth64_toNat, hcl0.lvl_len, bv32_lshr1_toNat]
      have := hcl0.cur_vars_le; omega
    have hlit_rs : ((lit >>> 1#32).setWidth 64).toNat < s.core.rsns.length := by
      rw [inst_bv32_setWidth64_toNat, hcl0.rsns_len, bv32_lshr1_toNat]
      have := hcl0.cur_vars_le; omega
    viv_hsteps_nogrp
    all_goals try exact hret0
    have hbt_tgt : (BitVec.ofNat 64 s.core.cur_level - 1).toNat = s.core.cur_level - 1 := by
      have hcv : (BitVec.ofNat 64 s.core.cur_level).toNat = s.core.cur_level := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt64]
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hcv, h1]; omega
    viv_call hBt
    refine ⟨c, s, R_ext, rfl, hsp0.1, hcl0_lt64, fun _ => by rw [hbt_tgt]; omega,
      hsp0.2.1.trail_lits_lt, hm0F,
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_bt
        hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
    have hle_bt : (BitVec.ofNat 64 s.core.cur_level - 1).toNat ≤ s.core.cur_level := by
      rw [hbt_tgt]; omega
    have hsp_bt := viv_sparseW_of_backtrack hsp0 hle_bt hlen_bt hpres_bt
      (hw_bt F0 F_cur hsp0.2.1 hle_bt)
    rcases hsc_bt with ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩
    let s_bt : FullState :=
      { s with
        core := { s.core with
          vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
          trail_pos := tp_b, trail_end := te_b, propagated := prop_b, cur_level := cl_b,
          unassigned := unass_b }
        scratch := sc_b }
    have hsp_bt' : FullSparseInvW c F0 F_cur s_bt := hsp_bt
    have hm_bt' : (FullMem c s_bt ⋆ R_ext) m_bt := hm_bt
    have hrr_bt : s_bt.scratch.red_refs = s.scratch.red_refs := by dsimp only [s_bt]; rw [hsc_eq]
    have hlit_vl_bt : (lit.setWidth 64).toNat < s_bt.core.vals.length := by
      rw [inst_bv32_setWidth64_toNat, hsp_bt'.1.core_ok.vals_len]; have := hcl0.cur_vars_le; omega
    have hbt_cl_le : s_bt.core.cur_level ≤ c.max_vars := by
      have := hsp_bt'.2.1.cur_level_le; have := hsp_bt'.1.core_ok.trail_end_le
      have := hsp_bt'.1.core_ok.cur_vars_le; omega
    have hret_bt : Q (0#64, ()) m_bt :=
      hQ 0#64 ext s_bt m_bt hext0 (viv_ext_pres_refl ext) hsp_bt' rfl rfl (Nat.le_refl _) rfl rfl
        hrr_bt (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm_bt')
    viv_hsteps_nogrp
    all_goals try exact hret_bt
    have hlv0 : s_bt.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
      have hlt_v : lit.toNat < s_bt.core.vals.length := by
        rw [hsp_bt'.1.core_ok.vals_len]; have := hcl0.cur_vars_le; omega
      rw [List.getElem?_eq_getElem hlt_v, Option.getD_some]
      have hse : (s_bt.core.vals[(lit.setWidth 64).toNat]'hlit_vl_bt).signExtend 32 = 0#32 := by
        first | assumption | c0_bound
      have hget : s_bt.core.vals[(lit.setWidth 64).toNat]'hlit_vl_bt =
          s_bt.core.vals[lit.toNat]'hlt_v := Option.some.inj (by
        rw [← List.getElem?_eq_getElem hlit_vl_bt, inst_bv32_setWidth64_toNat,
          List.getElem?_eq_getElem hlt_v])
      rw [hget] at hse
      exact (bv8_sext32_eq0_iff _).mp hse
    have hte_lt := hsp_bt'.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
    have hnlvl_le : s_bt.core.cur_level + 1 ≤ c.max_vars := by
      have := hsp_bt'.2.1.cur_level_le; have := hsp_bt'.1.core_ok.cur_vars_le; omega
    have hnlvl_nat : (BitVec.ofNat 64 s_bt.core.cur_level + 1#64).toNat =
        s_bt.core.cur_level + 1 := by bv_omega
    have hnlvl_ft : (BitVec.ofNat 64 s_bt.core.cur_level + 1#64).toNat <
        s_bt.core.frame_trail.length := by
      rw [hnlvl_nat, hsp_bt'.1.core_ok.frame_trail_len]; omega
    have hnlvl_fd : (BitVec.ofNat 64 s_bt.core.cur_level + 1#64).toNat <
        s_bt.core.frame_dec.length := by
      rw [hnlvl_nat, hsp_bt'.1.core_ok.frame_dec_len]; omega
    viv_hsteps_nogrp
    let nlvl := s_bt.core.cur_level + 1
    let ftrl' := s_bt.core.frame_trail.set nlvl (BitVec.ofNat 32 s_bt.core.trail_end)
    let fdec' := s_bt.core.frame_dec.set nlvl lit
    let s_pre : FullState :=
      { s_bt with core :=
        { s_bt.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
    have hlen_pre : s_pre.LengthsOk c :=
      ⟨{ hsp_bt'.1.core_ok with
           frame_trail_len := by simp [s_pre, ftrl', hsp_bt'.1.core_ok.frame_trail_len],
           frame_dec_len := by simp [s_pre, fdec', hsp_bt'.1.core_ok.frame_dec_len] },
       hsp_bt'.1.scratch_ok⟩
    have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 s_bt.core.trail_end) =
        BitVec.ofNat 32 s_bt.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
    have hnot_guard : ¬ (s_pre.core.cur_vars ≤ lit.toNat / 2 ∨
        c.max_vars ≤ s_pre.core.trail_end ∨ s_pre.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
      intro hor; rcases hor with h1 | h2 | h3
      · dsimp only [s_pre, s_bt] at h1; omega
      · have := hsp_bt'.1.core_ok.cur_vars_le; dsimp only [s_pre] at h2; omega
      · exact h3 hlv0
    viv_call hAs
    refine ⟨c, s_pre, R_ext, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega,
      (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]; exact (by assumption)),
      ?_⟩
    refine (ite_eq_right hnot_guard).mpr ?_
    dsimp only
    intro flags' unass' phases' m_as hfll' hphl' hm_as
    have hnlvl_ne0 : nlvl ≠ 0 := by omega
    simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
    obtain ⟨_, hsp_as_raw, hi0_trl, hlit_rsn_as⟩ :=
      inst_decideAssign_preserves_sparseW (unass' := unass') (unfl' := s_bt.core.unflushed)
        hsp_bt' hlit_lt hlv0 hfll' hphl'
    let s_as : FullState :=
      { s_bt with
        core :=
          { s_bt.core with
            vals := (s_bt.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags',
            lvl := s_bt.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
            rsns := s_bt.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
            trl := s_bt.core.trl.set s_bt.core.trail_end lit,
            trail_pos := s_bt.core.trail_pos.set (lit.toNat / 2)
              (BitVec.ofNat 32 s_bt.core.trail_end),
            frame_trail := ftrl', frame_dec := fdec',
            trail_end := s_bt.core.trail_end + 1, cur_level := nlvl,
            unassigned := unass' }
        scratch := { s_bt.scratch with phases := phases' } }
    have hsp_as : FullSparseInvW c F0 F_cur s_as := hsp_as_raw
    viv_hsteps_nogrp
    let s_c : FullState :=
      { s_as with core := { s_as.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
    have hsp_c : FullSparseInvW c F0 F_cur s_c := viv_with_confl hsp_as 0#64 0xFFFFFFFF#64
    have hm_c : (FullM6HdrMem c ext s_c ⋆ R) _ := fullM6HdrMem_unfocus_full (by assumption)
    viv_call hProp
    refine ⟨c, F0, F_cur, ext, s_c, R, rfl, hcfg, hext0, hsp_c.1, hsp_c.2.1,
      hsp_c.2.2.2.2.2, hm_c,
      fun pr ext_p vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
        wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p sc_p m_p
        hext_p hpres_p hlen_p hw_p htext_p hrsns_p hperm_p hps_p hrr_pc _ _ _ hfl_p _ _ hpr1 _ _
        hm_p => ?_⟩
    let s_p : FullState :=
      { s_c with
        core := { s_c.core with
          vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
          trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
          unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
          arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
          fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
          confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
        scratch := sc_p }
    have hsp_p : FullSparseInvW c F0 F_cur s_p :=
      viv_sparseInvW_of_prop_canon hsp_c hlen_p hw_p hperm_p hps_p
    let R_ext_p := m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R
    have hm_pF : (FullMem c s_p ⋆ R_ext_p) m_p := fullM6HdrMem_focus_full hm_p
    have hcv_p : s_p.core.cur_vars = s.core.cur_vars := rfl
    have hprb_p : s_p.core.probing = s.core.probing := rfl
    have hal_p : s_p.core.arena_len = s.core.arena_len := rfl
    have htmp_p : s_p.core.tmp = s.core.tmp := rfl
    have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_pc.trans hrr_bt
    have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s := hperm_p.2.1
    have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ href0
    have hprops_p := hperm_p.2.2 cref.toNat href0
    have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng0
    have hcl_p_eq : s_p.core.cur_level = nlvl := rfl
    have hcl_p_pos : 0 < s_p.core.cur_level := by rw [hcl_p_eq]; omega
    have hcl_p_lt64 : s_p.core.cur_level < 2 ^ 64 := by omega
    have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p
    have hlit_val_p : s_p.core.vals[lit.toNat]?.getD 0#8 = 1#8 := by
      refine (hw_p.vals_true_iff lit.toNat hlit_lt).mpr
        ⟨s_bt.core.trail_end, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htext_p.1, ?_⟩
      rw [htext_p.2.1 s_bt.core.trail_end (Nat.lt_succ_self _)]
      exact congrArg BitVec.toNat hi0_trl
    have hlit_rsn_p : s_p.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
      have hrp := hrsns_p s_bt.core.trail_end (Nat.lt_succ_self _)
      change s_p.core.rsns[(s_as.core.trl[s_bt.core.trail_end]?.getD 0#32).toNat / 2]? =
        s_as.core.rsns[(s_as.core.trl[s_bt.core.trail_end]?.getD 0#32).toNat / 2]? at hrp
      rw [hi0_trl] at hrp
      rw [hrp]; exact hlit_rsn_as
    have hcok_p_fn : pr = 1#64 → FullVivConflictOk F_cur s_p :=
      fun h => viv_conflictOkW_to_viv (hpr1 h).2.2.1
    clear_value s_p s_c s_as s_pre s_bt
    clear hm_p hm_c hsp_c hsp_as hsp_as_raw hlen_pre hnot_guard hte_bv hsp_bt' hsp_bt hAs hProp
      hperm_p hprops_p hpr1 hw_p hlen_p hfl_p htext_p hrsns_p hps_p hrr_pc hi0_trl hlit_rsn_as
    viv_hsteps_nogrp
    · -- `pr == 2ULL`: backtrack to 0 and return `2ULL`
      viv_call hBt
      refine ⟨c, s_p, R_ext_p, rfl, hsp_p.1, hcl_p_lt64,
        (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro; omega),
        hsp_p.2.1.trail_lits_lt, hm_pF,
        fun vals_2 lvl_2 rsns_2 trl_2 tp_2 te_2 prop_2 cl_2 unass_2 sc_2 m_2
          hlen_2 _ _ _ hpres_2 hsc_2 _ _ hw_2 _ hm_2 => ?_⟩
      have hsp_2 := viv_sparseW_of_backtrack hsp_p (Nat.zero_le _) hlen_2 hpres_2
        (hw_2 F0 F_cur hsp_p.2.1 (Nat.zero_le _))
      rcases hsc_2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      viv_hsteps_nogrp
      exact hQ 2#64 ext_p _ m_2 hext_p hpres_p hsp_2 hcv_p hprb_p hfl_p' hal_p hrefs_p hrr_p
        (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm_2)
    · -- `pr != 1ULL`: backtrack 1 level and return `0ULL`
      exact inst_backtrack_ret0_wp Γ hBt hext_p hpres_p hsp_p hcl_p_pos hcv_p hprb_p hfl_p'
        hal_p hrefs_p hrr_p hm_pF hQ
    · -- `pr == 1ULL`: deduce + inst_check + copy + commit
      have hpr_eq1 : pr = 1#64 := by c0_bound
      have hcok_p := hcok_p_fn hpr_eq1
      viv_call hDed
      refine ⟨c, F0, F_cur, s_p, R_ext_p, rfl, hsp_p, href_p, hng_p, hsz_le,
        (by rw [htmp_p, hcv_p]; exact htmp0_lt),
        fun _ => Or.inl hcok_p, fun h => absurd rfl h, hm_pF,
        fun iolen ar_d mclr_d mrk_d lm_d ws1_d ws2_d asz_d rsz_d m_d
          hsp_d _ _ hrefs_dp hcl_dp hent_d hsub_d hm_d => ?_⟩
      let s_d : FullState :=
        { s_p with
          core := { s_p.core with arena := ar_d, min_clr := mclr_d, mrk := mrk_d, lit_mark := lm_d }
          scratch := { s_p.scratch with
            work_stk1 := ws1_d, work_stk2 := ws2_d, ant_sz := asz_d, res_sz := rsz_d } }
      have hsp_d' : FullSparseInvW c F0 F_cur s_d := hsp_d
      have hm_d' : (FullMem c s_d ⋆ R_ext_p) m_d := hm_d
      have hcv_d : s_d.core.cur_vars = s.core.cur_vars := hcv_p
      have hprb_d : s_d.core.probing = s.core.probing := hprb_p
      have hal_d : s_d.core.arena_len = s.core.arena_len := hal_p
      have htmp_d : s_d.core.tmp = s.core.tmp := htmp_p
      have hrr_d : s_d.scratch.red_refs = s.scratch.red_refs := hrr_p
      have hcl_d_pos : 0 < s_d.core.cur_level := hcl_p_pos
      have hfl_d : s_d.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p'
      have hrefs_d : fullArenaClauseRefs s_d = fullArenaClauseRefs s := hrefs_dp.trans hrefs_p
      have hng_d : fullArenaClauseGarb s_d cref.toNat = false :=
        (hcl_dp cref.toNat href_p).1.trans hng_p
      have hws2_d_eq : s_d.scratch.work_stk2 = ws2_d := rfl
      clear_value s_d; clear hsp_d hm_d hDed hcok_p hcok_p_fn hrefs_dp hcl_dp
      refine wp_join_group (ts := [])
        (fun () mj => ∃ sj : FullState,
          FullSparseInvW c F0 F_cur sj ∧ 0 < sj.core.cur_level ∧
          sj.core.cur_vars = s.core.cur_vars ∧ sj.core.probing = s.core.probing ∧
          sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ sj.core.arena_len = s.core.arena_len ∧
          fullArenaClauseRefs sj = fullArenaClauseRefs s ∧
          sj.scratch.red_refs = s.scratch.red_refs ∧
          (FullMem c sj ⋆ R_ext_p) mj)
        (fun _ () mj ⟨sj, hsp_j, hcl_j, hcv_j, hprb_j, hfl_j, hal_j, hrefs_j, hrr_j, hm_j⟩ => by
          rw [Blocks.get_here]
          viv_hsteps_nogrp
          exact inst_backtrack_ret0_wp Γ hBt hext_p hpres_p hsp_j hcl_j hcv_j hprb_j hfl_j
            hal_j hrefs_j hrr_j hm_j hQ)
        (fun _ hJ74 => ?_)
      viv_hsteps_nogrp
      · exact hJ74 () m_d
          ⟨s_d, hsp_d', hcl_d_pos, hcv_d, hprb_d, hfl_d, hal_d, hrefs_d, hrr_d, hm_d'⟩
      · have hiolen_ne : iolen ≠ 0xFFFFFFFF#32 := by c0_bound
        have hio_bds : iolen.toNat ≤ s_p.core.cur_vars ∧
            ∀ k < iolen.toNat, (ws2_d[k]?.getD 0#32).toNat < 2 * s_p.core.cur_vars := by
          by_cases hasz : asz_d = 0xFFFFFFFFFFFFFFFF#64
          · obtain ⟨h1, h2, _, _⟩ := hent_d hasz hiolen_ne; exact ⟨h1, h2⟩
          · obtain ⟨h1, h2, _⟩ := hsub_d hasz hiolen_ne; exact ⟨h1, h2⟩
        have hiol_mv : iolen.toNat ≤ c.max_vars :=
          Nat.le_trans hio_bds.1 hsp_p.1.core_ok.cur_vars_le
        viv_call hChk
        refine ⟨c, F0, F_cur, s_d, R_ext_p, rfl, hsp_d', by omega, hsz_le, hiol_mv,
          (by rw [htmp_d, hcv_d]; exact htmp0_lt),
          (by rw [hws2_d_eq, hcv_d, ← hcv_p]; exact hio_bds.2), hm_d',
          fun ok lm_ic m_ic hsp_ic hok_ic hm_ic => ?_⟩
        let s_ic : FullState := { s_d with core := { s_d.core with lit_mark := lm_ic } }
        have hsp_ic' : FullSparseInvW c F0 F_cur s_ic := hsp_ic
        have hm_ic' : (FullMem c s_ic ⋆ R_ext_p) m_ic := hm_ic
        have hcv_ic : s_ic.core.cur_vars = s.core.cur_vars := hcv_d
        have hprb_ic : s_ic.core.probing = s.core.probing := hprb_d
        have hal_ic : s_ic.core.arena_len = s.core.arena_len := hal_d
        have htmp_ic : s_ic.core.tmp = s.core.tmp := htmp_d
        have hrr_ic : s_ic.scratch.red_refs = s.scratch.red_refs := hrr_d
        have hcl_ic_pos : 0 < s_ic.core.cur_level := hcl_d_pos
        have hfl_ic : s_ic.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_d
        have hrefs_ic : fullArenaClauseRefs s_ic = fullArenaClauseRefs s := hrefs_d
        have hng_ic : fullArenaClauseGarb s_ic cref.toNat = false := hng_d
        clear_value s_ic; clear hsp_ic hm_ic hChk
        viv_hsteps_nogrp
        · have hok_t : ok = true := by c0_bound
          have hsub_ic := hok_ic hok_t
          have hrest_ent : (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat)) := by
            by_cases hasz : asz_d = 0xFFFFFFFFFFFFFFFF#64
            · obtain ⟨_, _, _, hws2_ent⟩ := hent_d hasz hiolen_ne
              refine inst_entails_of_deduce hsp0 href0 hng0 (by omega) hsz_le hperm0 hlit_eq
                (by rw [← hws2_d_eq, hsp_d'.1.scratch_ok.work_stk2_len]; omega) hws2_ent ?_
              intro i hi
              rcases hsub_ic i hi with h1 | h2
              · left; rw [← hws2_d_eq]; exact h1
              · right; rwa [← hws2_d_eq, ← htmp_d]
            · obtain ⟨_, _, hsub_w⟩ := hsub_d hasz hiolen_ne
              exact inst_entails_of_sub hsp0 hsp_p (by omega) hsz_le htmp_p hlit_eq hsub_w
                hlit_val_p hlit_rsn_p
          exact inst_copy_commit_wp Γ hCommit hext_p hpres_p hsp0 hsp_ic' href0 hng0 hsz3 hsz_le
            hperm0 htmp0_lt hcv_ic hprb_ic hal_ic htmp_ic hrr_ic hfl_ic hrefs_ic hng_ic hrest_ent
            hm_ic' hQ
        · exact hJ74 () m_ic
            ⟨s_ic, hsp_ic', hcl_ic_pos, hcv_ic, hprb_ic, hfl_ic, hal_ic, hrefs_ic, hrr_ic, hm_ic'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
