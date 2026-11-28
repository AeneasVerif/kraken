/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate0

/-!
# Congruence Gate Re-Evaluation AND-Gate WP Proof (`WpEvalGateTag0`)

Proves `ev_tag0_wp` for `evTag0Expr` (AND / wide-AND gate simplification, deduplication,
unit/equivalence folding, and hash-gate preparation in `full_cong_eval_gate`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

attribute [local c0_load] ev_c0_load_full_tmp0 ev_c0_load_full_tmp1 ev_c0_load_full_tmp2
attribute [local c0_store] ev_c0_store_full_tmp0 ev_c0_store_full_tmp1 ev_c0_store_full_tmp2

local macro "ev_u" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_steps" : tactic =>
  `(tactic| (ev_u; c0_hsteps!))

local macro "ev_steps_ng" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp))

local macro "ev_split" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp; c0_hsplit))

/-! ## 1. Pure AND-Fold Semantic & List Lemmas -/

private theorem t0_andFold_has_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hex : ∃ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ k.vals[r]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs]) := by
  refine entails_of_eval_mem fun α hα => ?_
  obtain ⟨x, hx, r, hr_lt, heqv, hval⟩ := hex
  have hrf := entails_neg_eval_false (valsff_entails_neg hw hcl0 hr_lt hval) hα
  have hxf : evalLitVal α x = false := (litEquiv_eval hα heqv).trans hrf
  have hall_f : rhs.all (evalLitVal α) = false :=
    List.all_eq_false.mpr ⟨x, hx, by simp [hxf]⟩
  have hl0 := andGateDef_eval hα hand; rw [hall_f] at hl0
  exact ⟨litNeg lhs, List.mem_cons_self .., by
    rw [evalLitVal_litNeg, ← litEquiv_eval hα hlhs, hl0]; rfl⟩

private theorem t0_andFold_all_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hall : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ k.vals[r]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hall_t : rhs.all (evalLitVal α) = true := List.all_eq_true.mpr fun x hx => by
    obtain ⟨r, hr_lt, heqv, hval⟩ := hall x hx
    rw [litEquiv_eval hα heqv]; exact entails_eval_true (vals1_entails hw hcl0 hr_lt hval) hα
  have hl0 := andGateDef_eval hα hand; rw [hall_t] at hl0
  exact ⟨lhs, List.mem_cons_self .., by rw [← litEquiv_eval hα hlhs, hl0]⟩

private theorem t0_andFold_clash {F_cur : List (List Nat)} {lhs0 lhs : Nat}
    {rhs unass : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hsub : ∀ l ∈ unass, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l)
    (hcl : litNeg lhs ∈ unass ∨ ∃ z ∈ unass, litNeg z ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs]) := by
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs, List.mem_cons_self .., ?_⟩
  rw [evalLitVal_litNeg]
  rcases hcl with hmem | ⟨z, hz1, hz2⟩
  · obtain ⟨x, hx, heqv⟩ := hsub (litNeg lhs) hmem
    have hl0 := andGateDef_eval hα hand
    rw [litEquiv_eval hα hlhs] at hl0
    cases hl : evalLitVal α lhs
    · rfl
    · have hxf : evalLitVal α x = false := by
        rw [litEquiv_eval hα heqv, evalLitVal_litNeg, hl]; rfl
      have hf : rhs.all (evalLitVal α) = false := List.all_eq_false.mpr ⟨x, hx, by simp [hxf]⟩
      rw [hl, hf] at hl0; cases hl0
  · obtain ⟨x1, hx1, he1⟩ := hsub z hz1
    obtain ⟨x2, hx2, he2⟩ := hsub (litNeg z) hz2
    have hboth : (evalLitVal α x1 && evalLitVal α x2) = false := by
      rw [litEquiv_eval hα he1, litEquiv_eval hα he2, evalLitVal_litNeg]
      cases evalLitVal α z <;> rfl
    have hall_f : rhs.all (evalLitVal α) = false := by
      cases h1 : evalLitVal α x1 with
      | false => exact List.all_eq_false.mpr ⟨x1, hx1, by simp [h1]⟩
      | true =>
        have h2 : evalLitVal α x2 = false := by simpa [h1] using hboth
        exact List.all_eq_false.mpr ⟨x2, hx2, by simp [h2]⟩
    have hl0 := andGateDef_eval hα hand; rw [hall_f] at hl0
    rw [← litEquiv_eval hα hlhs, hl0]; rfl

private theorem t0_andFold_eval_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs0 lhs : Nat} {rhs unass : List Nat}
    (hand : AndGateDef (cnfOfClauses F_cur) lhs0 rhs)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0 lhs)
    (hfwd : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars,
      LitEquiv (cnfOfClauses F_cur) x r ∧ (k.vals[r]?.getD 0#8 = 1#8 ∨ r ∈ unass))
    (hbwd : ∀ l ∈ unass, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = unass.all (evalLitVal α) := by
  intro α hα
  rw [← litEquiv_eval hα hlhs, andGateDef_eval hα hand]
  by_cases hu : unass.all (evalLitVal α) = true
  · rw [hu, List.all_eq_true]; intro x hx
    obtain ⟨r, hr_lt, heqv, hval | hmem⟩ := hfwd x hx
    · rw [litEquiv_eval hα heqv]; exact entails_eval_true (vals1_entails hw hcl0 hr_lt hval) hα
    · rw [litEquiv_eval hα heqv]; exact List.all_eq_true.mp hu r hmem
  · have huf : unass.all (evalLitVal α) = false := Bool.eq_false_iff.mpr hu
    rw [huf, List.all_eq_false]; rw [List.all_eq_false] at huf
    obtain ⟨l, hl, hlf⟩ := huf; obtain ⟨x, hx, heqv⟩ := hbwd l hl
    exact ⟨x, hx, by rw [litEquiv_eval hα heqv]; exact hlf⟩

private theorem t0_raw_of_rhs {F_cur : List (List Nat)} {scr0 tmpi : List (BitVec 32)}
    {g ar_n : Nat} (_har_le : ar_n ≤ tmpi.length) (hscr_ge : g + 2 + ar_n ≤ scr0.length)
    (hraw_eqv : ∀ k < ar_n, LitEquiv (cnfOfClauses F_cur) (scr0[g + 2 + k]?.getD 0#32).toNat
      ((tmpi.take ar_n)[k]?.getD 0#32).toNat) :
    (∀ x ∈ (((scr0.drop (g + 2)).take ar_n).map BitVec.toNat),
      ∃ k < ar_n, LitEquiv (cnfOfClauses F_cur) x ((tmpi.take ar_n)[k]?.getD 0#32).toNat) ∧
    (∀ k < ar_n, ∃ x ∈ (((scr0.drop (g + 2)).take ar_n).map BitVec.toNat),
      LitEquiv (cnfOfClauses F_cur) x ((tmpi.take ar_n)[k]?.getD 0#32).toNat) := by
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · rw [List.mem_map] at hx; obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hb
    rw [List.length_take, List.length_drop] at hk
    have hk' : k < ar_n := by omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take, List.getElem_drop] at hget
    have he := hraw_eqv k hk'
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at he
  · have hlt : k < ((scr0.drop (g + 2)).take ar_n).length := by
      rw [List.length_take, List.length_drop]; omega
    have hmem : scr0[g + 2 + k]'(by omega) ∈ (scr0.drop (g + 2)).take ar_n := by
      simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
    refine ⟨(scr0[g + 2 + k]'(by omega)).toNat, List.mem_map_of_mem hmem, ?_⟩
    have he := hraw_eqv k hk
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at he

private theorem t0_post_sort {F_cur : List (List Nat)} {vals : List (BitVec 8)}
    {cv0 ar_n na_n maxv : Nat} {rhs : List Nat} {tmpl tmps raw : List (BitVec 32)}
    (htl_s : tmps.length = maxv) (htl_l : tmpl.length = maxv)
    (hna_le : na_n ≤ ar_n) (har_le : ar_n ≤ maxv)
    (hperm : List.Perm (tmps.take na_n) (tmpl.take na_n))
    (hsub_l : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hfwd_l : ∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmpl[j]?.getD 0#32).toNat = r)) :
    (∀ j < na_n, ∃ k < ar_n, tmps[j]? = raw[k]?) ∧
    (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmps[j]?.getD 0#32).toNat = r)) := by
  refine ⟨fun j hj => ?_, fun x hx => ?_⟩
  · have hmem : tmps[j]'(by omega) ∈ tmpl.take na_n :=
      hperm.mem_iff.mp (ev_mem_take_of_lt hj (by omega))
    obtain ⟨q, hq, hgetq⟩ := ev_lt_take_of_mem hmem
    simp only [Nat.lt_min] at hq
    obtain ⟨k, hk, hgetk⟩ := hsub_l q hq.1
    refine ⟨k, hk, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), ← hgetq]; exact hgetk
  · obtain ⟨r, hr_lt, heqv, h1 | ⟨j, hj, rfl⟩⟩ := hfwd_l x hx
    · exact ⟨r, hr_lt, heqv, Or.inl h1⟩
    · have hmem : tmpl[j]'(by omega) ∈ tmps.take na_n :=
        hperm.mem_iff.mpr (ev_mem_take_of_lt hj (by omega))
      obtain ⟨q, hq, hgetq⟩ := ev_lt_take_of_mem hmem
      simp only [Nat.lt_min] at hq
      refine ⟨_, hr_lt, heqv, Or.inr ⟨q, hq.1, ?_⟩⟩
      rw [hgetq, List.getElem?_eq_getElem (by omega)]

private theorem t0_dedup_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lhs0 lhs : BitVec 32} {rhs : List Nat} {tmps tmpd : List (BitVec 32)}
    {ua_n na_n cv0 : Nat} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    (hcv : k.cur_vars = cv0) (htld : ua_n ≤ tmpd.length)
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hfwd_s : ∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (k.vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmps[j]?.getD 0#32).toNat = r))
    (hcov_d : ∀ j < na_n, ∃ q < ua_n, (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32)
    (hsub_raw_d : ∀ j < ua_n, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (tmpd[j]?.getD 0#32).toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range ua_n).all (fun i => evalLitVal α (tmpd[i]?.getD 0#32).toNat) := by
  let unass_n := (tmpd.take ua_n).map BitVec.toNat
  have hfwd_n : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars, LitEquiv (cnfOfClauses F_cur) x r ∧
      (k.vals[r]?.getD 0#8 = 1#8 ∨ r ∈ unass_n) := by
    intro x hx; obtain ⟨r, hr_lt, heqv, h1 | ⟨j, hj, rfl⟩⟩ := hfwd_s x hx
    · exact ⟨r, hcv ▸ hr_lt, heqv, Or.inl h1⟩
    · obtain ⟨q, hq, hq_eq⟩ := hcov_d j hj
      refine ⟨_, hcv ▸ hr_lt, heqv, Or.inr (List.mem_map.mpr ⟨tmpd[q]?.getD 0#32, ?_, ?_⟩)⟩
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact ev_mem_take_of_lt hq htld
      · exact congrArg BitVec.toNat hq_eq
  have hbwd_n : ∀ l ∈ unass_n, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l := by
    intro l hl; rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hb
    rw [List.length_take] at hj; rw [List.getElem_take] at hget
    obtain ⟨x, hx, heqv⟩ := hsub_raw_d j (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at heqv
    exact ⟨x, hx, heqv⟩
  intro α hα
  have h1 := t0_andFold_eval_iff hw hcl0 hand0 hlhs_eqv hfwd_n hbwd_n α hα
  rw [h1, List.all_map]
  have htake_eq : tmpd.take ua_n = (List.range ua_n).map (fun i => tmpd[i]?.getD 0#32) := by
    apply List.ext_getElem
    · simp [List.length_take, List.length_map, List.length_range, Nat.min_eq_left htld]
    · intro i hi1 _
      have hi_d : i < tmpd.length := by rw [List.length_take] at hi1; omega
      simp [List.getElem_take, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi_d]
  rw [htake_eq, List.all_map]; rfl

private theorem t0_dedup_clash {tmpd tmps : List (BitVec 32)} {ua_n si_n na_n : Nat}
    {prev : BitVec 32} (htl : ua_n ≤ tmpd.length) (htmps_len : na_n ≤ tmps.length)
    (hua_pos : 0 < ua_n) (hsi_lt : si_n < na_n)
    (hprev_eq : prev = tmpd[ua_n - 1]'(by omega))
    (hsub_tmps : ∀ j < ua_n, ∃ k < na_n, tmpd[j]? = tmps[k]?)
    (hcur_xor : tmps[si_n]'(by omega) = prev ^^^ 1#32) :
    ∃ z ∈ (tmps.take na_n).map BitVec.toNat,
      litNeg z ∈ (tmps.take na_n).map BitVec.toNat := by
  obtain ⟨kp, hkp, hgetp⟩ := hsub_tmps (ua_n - 1) (by omega)
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hgetp
  have hp_tmps : prev = tmps[kp]'(by omega) := hprev_eq.trans (Option.some.inj hgetp)
  have hcur_mem : (tmps[si_n]'(by omega)).toNat ∈ (tmps.take na_n).map BitVec.toNat :=
    List.mem_map_of_mem (ev_mem_take_of_lt hsi_lt htmps_len)
  have hprev_mem : prev.toNat ∈ (tmps.take na_n).map BitVec.toNat := by
    rw [hp_tmps]; exact List.mem_map_of_mem (ev_mem_take_of_lt hkp htmps_len)
  refine ⟨prev.toNat, hprev_mem, ?_⟩
  rw [← bv32_xor1_eq_litNeg, ← hcur_xor]; exact hcur_mem

private theorem t0_vals_ff_of_slt0 {vals : List (BitVec 8)} {raw : List (BitVec 32)} {il : Nat}
    (hil : il < raw.length) (hv : (raw[il]'hil).toNat < vals.length)
    (hdom : vals[(raw[il]'hil).toNat]?.getD 0#8 = 0#8 ∨
      vals[(raw[il]'hil).toNat]?.getD 0#8 = 1#8 ∨ vals[(raw[il]'hil).toNat]?.getD 0#8 = 0xFF#8)
    (hlt : ((vals[(raw[il]'hil).toNat]'hv).signExtend 32).slt 0#32 = true) :
    vals[(raw[il]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hil, Option.getD_some, List.getElem?_eq_getElem hv, Option.getD_some]
  have hd : vals[(raw[il]'hil).toNat]'hv = 0#8 ∨ vals[(raw[il]'hil).toNat]'hv = 1#8 ∨
      vals[(raw[il]'hil).toNat]'hv = 0xFF#8 := by simpa [List.getElem?_eq_getElem hv] using hdom
  rcases hd with h | h | h <;> rw [h] at hlt ⊢ <;> first | rfl | exact absurd hlt (by decide)

private theorem t0_vals_1_of_nslt0_ne0 {vals : List (BitVec 8)} {raw : List (BitVec 32)} {il : Nat}
    (hil : il < raw.length) (hv : (raw[il]'hil).toNat < vals.length)
    (hdom : vals[(raw[il]'hil).toNat]?.getD 0#8 = 0#8 ∨
      vals[(raw[il]'hil).toNat]?.getD 0#8 = 1#8 ∨ vals[(raw[il]'hil).toNat]?.getD 0#8 = 0xFF#8)
    (hnslt : ((vals[(raw[il]'hil).toNat]'hv).signExtend 32).slt 0#32 = false)
    (hne : (vals[(raw[il]'hil).toNat]'hv).signExtend 32 ≠ 0#32) :
    vals[(raw[il]?.getD 0#32).toNat]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hil, Option.getD_some, List.getElem?_eq_getElem hv, Option.getD_some]
  have hd : vals[(raw[il]'hil).toNat]'hv = 0#8 ∨ vals[(raw[il]'hil).toNat]'hv = 1#8 ∨
      vals[(raw[il]'hil).toNat]'hv = 0xFF#8 := by simpa [List.getElem?_eq_getElem hv] using hdom
  rcases hd with h | h | h <;> rw [h] at hnslt hne ⊢ <;>
    first | rfl | exact absurd rfl hne | exact absurd hnslt (by decide)

private theorem t0_dedup_set0_inv {tmpd tmps : List (BitVec 32)} {si_n na_n : Nat}
    (hsi0 : si_n = 0) (h0_na : 0 < na_n) (h0_d : 0 < tmpd.length) (hsi_ts : si_n < tmps.length)
    (htail : ∀ j, si_n ≤ j → j < na_n → tmpd[j]? = tmps[j]?) :
    (∀ j, 1 ≤ j → j < na_n → (tmpd.set 0 (tmps[si_n]'hsi_ts))[j]? = tmps[j]?) ∧
    (∀ j < 1, ∃ k < na_n, (tmpd.set 0 (tmps[si_n]'hsi_ts))[j]? = tmps[k]?) ∧
    (∀ j < 1, ∃ q < 1, (tmpd.set 0 (tmps[si_n]'hsi_ts))[q]?.getD 0#32 = tmps[j]?.getD 0#32) := by
  refine ⟨fun j hj1 hj2 => by rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2,
    fun j hj => ⟨0, by omega, by
      have : j = 0 := by omega
      subst this; rw [List.getElem?_set_self h0_d, List.getElem?_eq_getElem (by omega)]
      simp [hsi0]⟩,
    fun j hj => ⟨0, by decide, by
      have : j = 0 := by omega
      subst this; rw [List.getElem?_set_self h0_d, Option.getD_some,
        List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [hsi0]⟩⟩

private theorem t0_dedup_set_inv {tmpd tmps : List (BitVec 32)} {ua_n si_n na_n : Nat}
    (hua_le : ua_n ≤ si_n) (hsi_lt : si_n < na_n) (hua_d : ua_n < tmpd.length)
    (hsi_ts : si_n < tmps.length)
    (htail : ∀ j, si_n ≤ j → j < na_n → tmpd[j]? = tmps[j]?)
    (hsub : ∀ j < ua_n, ∃ k < na_n, tmpd[j]? = tmps[k]?)
    (hcov : ∀ j < si_n, ∃ q < ua_n, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) :
    let t' := tmpd.set ua_n (tmps[si_n]'hsi_ts)
    (∀ j, si_n + 1 ≤ j → j < na_n → t'[j]? = tmps[j]?) ∧
    (∀ j < ua_n + 1, ∃ k < na_n, t'[j]? = tmps[k]?) ∧
    (∀ j < si_n + 1, ∃ q < ua_n + 1, t'[q]?.getD 0#32 = tmps[j]?.getD 0#32) := by
  refine ⟨fun j hj1 hj2 => by rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2,
    fun j hj => by
      by_cases hju : j = ua_n
      · subst hju; exact ⟨si_n, hsi_lt, by
          rw [List.getElem?_set_self hua_d, List.getElem?_eq_getElem hsi_ts]⟩
      · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hsub j (by omega),
    fun j hj => by
      by_cases hjs : j = si_n
      · subst hjs; exact ⟨ua_n, by omega, by
          rw [List.getElem?_set_self hua_d, Option.getD_some,
            List.getElem?_eq_getElem hsi_ts, Option.getD_some]⟩
      · obtain ⟨q, hq, hcq⟩ := hcov j (by omega)
        exact ⟨q, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hcq⟩⟩

private theorem t0_pass1_set_inv {tmpl raw : List (BitVec 32)} {vals : List (BitVec 8)}
    {na_n il_n ar_n : Nat} (hna_le : na_n ≤ il_n) (hil_lt : il_n < ar_n)
    (hna_d : na_n < tmpl.length) (hil_r : il_n < raw.length)
    (htail : ∀ j, il_n ≤ j → j < ar_n → tmpl[j]? = raw[j]?)
    (hsub : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hnohf : ∀ k < il_n, vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      ∃ j < na_n, tmpl[j]? = raw[k]?) :
    let t' := tmpl.set na_n (raw[il_n]'hil_r)
    (∀ j, il_n + 1 ≤ j → j < ar_n → t'[j]? = raw[j]?) ∧
    (∀ j < na_n + 1, ∃ k < ar_n, t'[j]? = raw[k]?) ∧
    (∀ k < il_n + 1, vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      ∃ j < na_n + 1, t'[j]? = raw[k]?) := by
  refine ⟨fun j hj1 hj2 => by rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2,
    fun j hj => by
      by_cases hjn : j = na_n
      · subst hjn; exact ⟨il_n, hil_lt, by
          rw [List.getElem?_set_self hna_d, List.getElem?_eq_getElem hil_r]⟩
      · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hsub j (by omega),
    fun k hk => by
      by_cases hki : k = il_n
      · subst hki; exact Or.inr ⟨na_n, by omega, by
          rw [List.getElem?_set_self hna_d, List.getElem?_eq_getElem hil_r]⟩
      · rcases hnohf k (by omega) with h1 | ⟨j, hj, hgj⟩
        · exact Or.inl h1
        · exact Or.inr ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hgj⟩⟩

private abbrev T0Out (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (fl0 : BitVec 64) (ar0 : List (BitVec 32))
    (arl0 g_len ctrl_off ht_off ht_sz : Nat) (scr0 scr_in : List (BitVec 32))
    (gtype lhs : BitVec 32) (R : Mem 64 → Prop) : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
  fun (har', nh', _, ()) mj => ∃ stj : FullState,
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in stj ∧
    (nh' = true → EvHashGateOk maxA F_cur cv0 gtype gtype har' lhs stj.core.tmp) ∧
    (FullMem c stj ⋆ R) mj

public section

/-- Canonical WP proof for the AND / wide-AND gate branch `evTag0Expr`. -/
theorem ev_tag0_wp (Γ : Env)
    (hSort : Γ.Has "full_sort_u32" fullSortU32Spec)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz g_n : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep arity gtype lhs lhs0 : BitVec 32}
    {J37 : Cont [i32, i32, i32, i32, .bool, .bool]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hgtype : gtype = 0#32)
    (har_cv : arity.toNat ≤ cv0) (har_max : arity.toNat ≤ maxA)
    (hscr_ge : g_n + 2 + arity.toNat ≤ scr0.length)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g_n + 2)).take arity.toNat).map BitVec.toNat))
    (htmp_i : ∀ k < arity.toNat, (s0.core.tmp[k]?.getD 0#32).toNat < 2 * cv0 ∧
      LitEquiv (cnfOfClauses F_cur) (scr0[g_n + 2 + k]?.getD 0#32).toNat
        (s0.core.tmp[k]?.getD 0#32).toNat)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ37 : ∀ iw har' nh' ch' s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in s' →
      (nh' = true → EvHashGateOk maxA F_cur cv0 gtype gtype har' lhs s'.core.tmp) →
      (FullMem c s' ⋆ R) m' → J37 (lhs, iw, gtype, har', nh', ch', ()) m') :
    wp Γ Q X (evTag0Expr c.hdr ctrl_off c.pTmp c.pVals next_ep arity gtype lhs J37) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hw0 := hok0.1.2.1; have hcl0 := hok0.1.2.2.2.2.2.1
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr; have hvlen0 := hok0.1.1.core_ok.vals_len
  let rhs : List Nat := ((scr0.drop (g_n + 2)).take arity.toNat).map BitVec.toNat
  let raw := s0.core.tmp.take arity.toNat
  have hraw_len : raw.length = arity.toNat := by simp only [raw, List.length_take]; omega
  obtain ⟨hraw_of_rhs, hrhs_of_raw⟩ :=
    t0_raw_of_rhs (tmpi := s0.core.tmp) (by omega) hscr_ge fun k hk => by
    have h := (htmp_i k hk).2; simpa only [List.getElem?_take_of_lt hk] using h
  have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
    have h := (htmp_i k hk).1; simpa only [raw, List.getElem?_take_of_lt hk] using h
  let P_t0 := T0Out maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
    gtype lhs R
  unfold evTag0Expr; ev_steps_ng
  refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
    (fun (il, hf, na, ()) ml => ∃ tmpl : List (BitVec 32), tmpl.length = c.max_vars ∧
      na.toNat ≤ arity.toNat ∧
      (hf = true → ∃ k < arity.toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
      (hf = false → il.toNat = arity.toNat ∧
        (∀ j < na.toNat, ∃ k < arity.toNat, tmpl[j]? = raw[k]?) ∧
        (∀ k < arity.toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
          ∃ j < na.toNat, tmpl[j]? = raw[k]?)) ∧
      (FullMem c { s0 with core := { s0.core with tmp := tmpl } } ⋆ R) ml)
    (fun rem (il, na, ()) ml => rem = arity.toNat - il.toNat ∧ ∃ tmpl : List (BitVec 32),
      tmpl.length = c.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ arity.toNat ∧
      (∀ j, il.toNat ≤ j → j < arity.toNat → tmpl[j]? = raw[j]?) ∧
      (∀ j < na.toNat, ∃ k < arity.toNat, tmpl[j]? = raw[k]?) ∧
      (∀ k < il.toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
      (FullMem c { s0 with core := { s0.core with tmp := tmpl } } ⋆ R) ml) ?_ ?_ ?_
  · rintro _ ⟨il, hf, na, ⟨⟩⟩ ml ⟨tmpl, htl_l, hna_le, hhf_l, hnohf_l, hml⟩
    let sl : FullState := { s0 with core := { s0.core with tmp := tmpl } }
    have hokl := evCoreOk_tmp hok0 htl_l
    ev_steps_ng
    refine wp_join_group P_t0
      (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj ⟨stj, hk, hg, hm⟩ => by
        ev_steps; exact hJ37 il har' nh' ch' stj mj hk hg hm) ?_
    intro Jt0 hJt0; ev_split
    · obtain ⟨k, hk, hff⟩ := hhf_l hc
      obtain ⟨x, hx_mem, hx_eqv⟩ := hrhs_of_raw k hk
      have hun := t0_andFold_has_false hw0 hcl0 hand0 hlhs_eqv
        ⟨x, hx_mem, (raw[k]?.getD 0#32).toNat, hcv_eq.symm ▸ hraw_lt k hk, hx_eqv, hff⟩
      clear hc; ev_steps
      refine ev_unit_wp Γ hUnit hokl (ev_bv32_xor1_lt_cv hlhs_lt)
        (by change (cnfOfClauses F_cur).EntailsClause (cnfClause [(lhs ^^^ 1#32).toNat])
            rw [bv32_xor1_eq_litNeg]; exact hun) hml hQ2 fun ch' s' m' _ _ hok' hm' => by
          ev_steps; exact hJt0 (arity, false, ch', ()) m' ⟨s', hok', (fun h => by cases h), hm'⟩
    obtain ⟨_, hsub_l, hnohf'⟩ := hnohf_l hc; clear hc; ev_steps_ng
    refine wp_join_group P_t0
      (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by ev_steps; exact hJt0 (har', nh', ch', ()) mj h) ?_
    intro Jt0b hJt0b; ev_split
    · have hna0 : na.toNat = 0 := by rw [hc]; rfl
      have hun := t0_andFold_all_true hw0 hcl0 hand0 hlhs_eqv fun x hx => by
        obtain ⟨k, hk, heqv⟩ := hraw_of_rhs x hx
        refine ⟨(raw[k]?.getD 0#32).toNat, hcv_eq.symm ▸ hraw_lt k hk, heqv, ?_⟩
        rcases hnohf' k hk with h1 | ⟨j, hj, _⟩
        · exact h1
        · omega
      clear hc; ev_steps
      refine ev_unit_wp Γ hUnit hokl hlhs_lt hun hml hQ2 fun ch' s' m' _ _ hok' hm' => by
        ev_steps; exact hJt0b (arity, false, ch', ()) m' ⟨s', hok', (fun h => by cases h), hm'⟩
    have hna_pos : 0 < na.toNat := by
      rcases Nat.eq_zero_or_pos na.toNat with hz | hp
      · exact absurd (BitVec.eq_of_toNat_eq hz) hc
      · exact hp
    have hfwd_l : ∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
        (s0.core.vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na.toNat, (tmpl[j]?.getD 0#32).toNat = r) := by
      intro x hx; obtain ⟨k, hk, heqv⟩ := hraw_of_rhs x hx
      refine ⟨(raw[k]?.getD 0#32).toNat, hraw_lt k hk, heqv, ?_⟩
      rcases hnohf' k hk with h1 | ⟨j, hj, hget⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j, hj, by rw [hget]⟩
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [])
      (fun () ms => ∃ tmps : List (BitVec 32), tmps.length = c.max_vars ∧
        (∀ j < na.toNat, ∃ k < arity.toNat, tmps[j]? = raw[k]?) ∧
        (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
          (s0.core.vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na.toNat, (tmps[j]?.getD 0#32).toNat = r)) ∧
        (FullMem c { s0 with core := { s0.core with tmp := tmps } } ⋆ R) ms) ?_ ?_
    · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hsub_s, hfwd_s, hms⟩
      ev_steps_ng
      refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
        (fun (clash, ua, _, ()) md => ∃ tmpd : List (BitVec 32), tmpd.length = c.max_vars ∧
          ua.toNat ≤ na.toNat ∧
          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
          (clash = true → litNeg lhs.toNat ∈ (tmps.take na.toNat).map BitVec.toNat ∨
            ∃ z ∈ (tmps.take na.toNat).map BitVec.toNat,
              litNeg z ∈ (tmps.take na.toNat).map BitVec.toNat) ∧
          (clash = false → 0 < ua.toNat ∧
            ∀ j < na.toNat, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
          (FullMem c { s0 with core := { s0.core with tmp := tmpd } } ⋆ R) md)
        (fun remd (ua, si, ()) md => remd = na.toNat - si.toNat ∧ ∃ tmpd : List (BitVec 32),
          tmpd.length = c.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na.toNat ∧
          (0 < si.toNat → 0 < ua.toNat) ∧
          (∀ j, si.toNat ≤ j → j < na.toNat → tmpd[j]? = tmps[j]?) ∧
          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
          (∀ j < si.toNat, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
          (FullMem c { s0 with core := { s0.core with tmp := tmpd } } ⋆ R) md) ?_ ?_ ?_
      · rintro _ ⟨clash, ua, _, ⟨⟩⟩ md ⟨tmpd, htl_d, hua_le, hsub_tmps, hcl_d, huf_d, hmd⟩
        let sd : FullState := { s0 with core := { s0.core with tmp := tmpd } }
        have hokd := evCoreOk_tmp hok0 htl_d
        have hsub_d : ∀ j < ua.toNat, ∃ k < arity.toNat, tmpd[j]? = raw[k]? := fun j hj => by
          obtain ⟨k, hk, h1⟩ := hsub_tmps j hj; obtain ⟨kr, hkr, h2⟩ := hsub_s k hk
          exact ⟨kr, hkr, h1.trans h2⟩
        have hsub_raw_d : ∀ j < ua.toNat, ∃ x ∈ rhs,
            LitEquiv (cnfOfClauses F_cur) x (tmpd[j]?.getD 0#32).toNat := fun j hj => by
          obtain ⟨k, hk, hget⟩ := hsub_d j hj; obtain ⟨x, hx, he⟩ := hrhs_of_raw k hk
          exact ⟨x, hx, by rwa [hget]⟩
        have htmpd_lt : ∀ j < ua.toNat, (tmpd[j]?.getD 0#32).toNat < 2 * cv0 := fun j hj => by
          obtain ⟨k, hk, hget⟩ := hsub_d j hj; rw [hget]; exact hraw_lt k hk
        ev_steps_ng
        refine wp_join_group P_t0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by ev_steps; exact hJt0b (har', nh', ch', ()) mj h) ?_
        intro Jt0c hJt0c; ev_split
        · have hsub_unass : ∀ l ∈ (tmps.take na.toNat).map BitVec.toNat,
              ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l := fun l hl => by
            rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
            obtain ⟨j, hj, hget⟩ := ev_lt_take_of_mem hb; simp only [Nat.lt_min] at hj
            obtain ⟨k, hk, hgk⟩ := hsub_s j hj.1; obtain ⟨x, hx, he⟩ := hrhs_of_raw k hk
            refine ⟨x, hx, ?_⟩
            rw [← hgk, hget, Option.getD_some] at he; exact he
          have hun := t0_andFold_clash hand0 hlhs_eqv hsub_unass (hcl_d hc)
          clear hc; ev_steps
          refine ev_unit_wp Γ hUnit hokd (ev_bv32_xor1_lt_cv hlhs_lt)
            (by change (cnfOfClauses F_cur).EntailsClause (cnfClause [(lhs ^^^ 1#32).toNat])
                rw [bv32_xor1_eq_litNeg]; exact hun) hmd hQ2 fun ch' s' m' _ _ hok' hm' => by
              ev_steps
              exact hJt0c (arity, false, ch', ()) m' ⟨s', hok', (fun h => by cases h), hm'⟩
        obtain ⟨hua_pos, hcov_d⟩ := huf_d hc; clear hc; ev_steps_ng
        refine wp_join_group P_t0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by ev_steps; exact hJt0c (har', nh', ch', ()) mj h) ?_
        intro Jt0d hJt0d; ev_split
        have hev_d :=
          t0_dedup_eval hw0 hcl0 hcv_eq (by omega) hand0 hlhs_eqv hfwd_s hcov_d hsub_raw_d
        clear hc; ev_steps_ng
        refine wp_join_group P_t0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by ev_steps; exact hJt0d (har', nh', ch', ()) mj h) ?_
        have h0_d : 0 < tmpd.length := by omega
        intro Jt0e hJt0e; ev_split
        · have hua1 : ua.toNat = 1 := by rw [hc]; rfl
          have ht0_lt : (tmpd[0]'h0_d).toNat < 2 * cv0 := by
            simpa [List.getElem?_eq_getElem h0_d] using htmpd_lt 0 (by omega)
          have ht0_eqv : LitEquiv (cnfOfClauses F_cur) lhs.toNat (tmpd[0]'h0_d).toNat :=
            ev_litEquiv_of_eval fun α hα => by
              have h := hev_d α hα
              rw [hua1, List.range_one, List.all_cons, List.all_nil, Bool.and_true,
                List.getElem?_eq_getElem h0_d, Option.getD_some] at h
              exact h
          clear hc; ev_steps
          refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hokd hlhs_lt ht0_lt ht0_eqv hmd hQ2
            fun ch' s' m' _ hok' hm' => by
              ev_steps
              exact hJt0e (arity, false, ch', ()) m' ⟨s', hok', (fun h => by cases h), hm'⟩
        have hua_ge2 : 2 ≤ ua.toNat := by
          have : ua.toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq h); omega
        have hlhs_vals : (lhs.setWidth 64).toNat < s0.core.vals.length := by
          rw [bv_zext32_toNat, hvlen0]; omega
        clear hc; ev_steps_ng
        refine wp_join_group P_t0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by ev_steps; exact hJt0e (har', nh', ch', ()) mj h) ?_
        intro Jt0f hJt0f; ev_split
        · have hv1 : s0.core.vals[lhs.toNat]?.getD 0#8 = 1#8 := by
            have hd := hw0.vals_domain lhs.toNat (hcv_eq.symm ▸ hlhs_lt)
            have hlhs_v : lhs.toNat < s0.core.vals.length := by omega
            have hget : s0.core.vals[lhs.toNat]'hlhs_v =
                s0.core.vals[lhs.toNat]?.getD 0#8 := by
              rw [List.getElem?_eq_getElem hlhs_v, Option.getD_some]
            rw [← hget]
            exact bv8_eq1_of_signExtend32_sgt0 (by rwa [hget]) (by simpa [sd] using hc)
          have hents : ∀ j < ua.toNat,
              (cnfOfClauses F_cur).EntailsClause (cnfClause [(tmpd[j]?.getD 0#32).toNat]) :=
            fun j hj => ev_entails_of_eval fun α hα => by
              have h1 := entails_eval_true (vals1_entails hw0 hcl0 (hcv_eq.symm ▸ hlhs_lt) hv1) hα
              have h2 := hev_d α hα; rw [h1] at h2
              exact List.all_eq_true.mp h2.symm j (List.mem_range.mpr hj)
          clear hc; ev_steps_ng
          refine wp_loop_inv (ts := [.bool, i32])
            (fun (_, k, ()) mk => ∃ stk : FullState, k.toNat ≤ ua.toNat ∧ stk.core.tmp = tmpd ∧
              EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
                scr0 scr_in stk ∧ (FullMem c stk ⋆ R) mk)
            (fun (_, k, ()) _ => ua.toNat - k.toNat)
            (fun _ hJk => by
              ev_steps; exact hJk (false, 0#32, ()) md ⟨sd, Nat.zero_le _, rfl, hokd, hmd⟩)
            (fun _ ⟨ch_k, k, ⟨⟩⟩ mk ⟨stk, hk_le, htmp_k, hokk, hmk⟩ ihk => ?_)
          by_cases hk_lt : k.toNat < ua.toNat
          · have hk_arr : (k.setWidth 64).toNat < stk.core.tmp.length := by
              rw [bv_zext32_toNat, htmp_k]; omega
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
            have htk_eq :
                stk.core.tmp[(k.setWidth 64).toNat]'hk_arr = tmpd[k.toNat]?.getD 0#32 := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have h1 : stk.core.tmp[(k.setWidth 64).toNat]'hk_arr =
                  tmpd[(k.setWidth 64).toNat]'(by rw [← htmp_k]; exact hk_arr) := by
                cases htmp_k; rfl
              exact h1.trans (list_getElem_congr (bv_zext32_toNat k) _ _)
            ev_steps
            refine ev_unit_wp Γ hUnit hokk (by rw [htk_eq]; exact htmpd_lt k.toNat hk_lt)
              (by rw [htk_eq]; exact hents k.toNat hk_lt) hmk hQ2
              fun ch_u su mu _ htmpu hoku hmu => by
                ev_steps; exact ihk (ch_u, k + 1#32, ()) mu (by dsimp only; omega)
                  ⟨su, by omega, htmpu.trans htmp_k, hoku, hmu⟩
          · ev_steps
            exact hJt0f (arity, false, ch_k, ()) mk ⟨stk, hokk, (fun h => by cases h), hmk⟩
        · ev_steps; exact hJt0f (ua, true, false, ()) md
            ⟨sd, hokd, fun _ => ⟨hlhs_lt, by omega, by omega, hua_ge2, htmpd_lt, Or.inl rfl,
              fun _ => hev_d, fun h => absurd (hgtype.symm.trans h) (by decide),
              fun h => absurd (hgtype.symm.trans h) (by decide), Or.inl hgtype⟩, hmd⟩
      · rintro Bd Ld remd ⟨ua, si, ⟨⟩⟩ md hBd hLd
          ⟨rfl, tmpd, htl_d, hua_le, hsi_le, hua_pos_if, htail_d, hsub_tmps, hcov_d, hmd⟩
        let sd : FullState := { s0 with core := { s0.core with tmp := tmpd } }
        by_cases hsi_lt : si.toNat < na.toNat
        · have hsi_arr : (si.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
          have hsi_tl : si.toNat < tmpd.length := by omega
          have hsi_ts : si.toNat < tmps.length := by omega
          let cur := tmps[si.toNat]'hsi_ts
          have hcur_tl : tmpd[si.toNat]'hsi_tl = cur := by
            have h1 := (htail_d si.toNat (Nat.le_refl _) hsi_lt).trans
              (List.getElem?_eq_getElem hsi_ts)
            rw [List.getElem?_eq_getElem hsi_tl] at h1; exact Option.some.inj h1
          have hcur_eq : tmpd[(si.setWidth 64).toNat]'hsi_arr = cur :=
            (list_getElem_congr (bv_zext32_toNat si) hsi_arr hsi_tl).trans hcur_tl
          have hsi1 : (si + 1#32).toNat = si.toNat + 1 := bv32_add1_lt_of (by omega)
          have hua1 : (ua + 1#32).toNat = ua.toNat + 1 := bv32_add1_lt_of (by omega)
          ev_split
          · have hcl_lhs : litNeg lhs.toNat ∈ (tmps.take na.toNat).map BitVec.toNat := by
              have hc' : cur = lhs ^^^ 1#32 := by simpa [sd, hcur_tl] using hc
              rw [← bv32_xor1_eq_litNeg, ← hc']
              exact List.mem_map_of_mem (ev_mem_take_of_lt hsi_lt (by omega))
            ev_steps; exact hBd (true, ua, si + 1#32, ()) md
              ⟨tmpd, htl_d, by omega, hsub_tmps, fun _ => Or.inl hcl_lhs,
               (fun h => by cases h), hmd⟩
          clear hc; ev_steps_ng
          refine wp_join_group (ts := [.bool, i32])
            (fun (_, ua', ()) md' => ∃ t' : List (BitVec 32), t'.length = c.max_vars ∧
              ua'.toNat ≤ (si + 1#32).toNat ∧ (si + 1#32).toNat ≤ na.toNat ∧
              (0 < (si + 1#32).toNat → 0 < ua'.toNat) ∧
              (∀ j, (si + 1#32).toNat ≤ j → j < na.toNat → t'[j]? = tmps[j]?) ∧
              (∀ j < ua'.toNat, ∃ k < na.toNat, t'[j]? = tmps[k]?) ∧
              (∀ j < (si + 1#32).toNat, ∃ q < ua'.toNat, t'[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
              (FullMem c { s0 with core := { s0.core with tmp := t' } } ⋆ R) md')
            (fun _ ⟨_, ua', ⟨⟩⟩ md' h => by
              ev_steps; exact hLd (na.toNat - (si + 1#32).toNat) (ua', si + 1#32, ()) md'
                (by omega) ⟨rfl, h⟩) ?_
          intro Jua hJua
          by_cases hua0_c : ua = 0#32
          · have hua0 : ua.toNat = 0 := by rw [hua0_c]; rfl
            have hsi0 : si.toNat = 0 :=
              Nat.eq_zero_of_not_pos fun h => by have := hua_pos_if h; omega
            have h0_d : 0 < tmpd.length := by omega
            have h1_n : (1#32 : BitVec 32).toNat = 1 := rfl
            obtain ⟨ht0, hs0, hc0⟩ := t0_dedup_set0_inv hsi0 hna_pos h0_d hsi_ts htail_d
            ev_steps
            refine hJua (false, 1#32, ()) m ⟨tmpd.set 0 cur, by simp [htl_d], by omega, by omega,
              fun _ => by decide, (fun j hj1 hj2 => ht0 j (by omega) hj2),
              (fun j hj => hs0 j (by omega)), (fun j hj => hc0 j (by omega)),
              (by dsimp only [sd] at hm; rw [hcur_eq] at hm; simpa using hm)⟩
          · have hua_pos : 0 < ua.toNat := by
              rcases Nat.eq_zero_or_pos ua.toNat with hz | hp
              · exact absurd (BitVec.eq_of_toNat_eq hz) hua0_c
              · exact hp
            have hum1_n : ((ua - 1#32).setWidth 64).toNat = ua.toNat - 1 := by
              rw [bv_zext32_toNat, ev_bv32_sub1_toNat hua_pos]
            have hum1_arr : ((ua - 1#32).setWidth 64).toNat < tmpd.length := by rw [hum1_n]; omega
            let prev := tmpd[((ua - 1#32).setWidth 64).toNat]'hum1_arr
            have hprev_eq : prev = tmpd[ua.toNat - 1]'(by omega) :=
              list_getElem_congr hum1_n hum1_arr (by omega)
            have hum1_mod : (4294967295 + ua.toNat) % 4294967296 = ua.toNat - 1 := by omega
            have hprev_hc :
                tmpd[(4294967295 + ua.toNat) % 4294967296]'(by omega) = prev :=
              (list_getElem_congr hum1_mod _ _).trans hprev_eq.symm
            have hua_arr : (ua.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
            ev_split
            · have hcp : cur = tmpd[ua.toNat - 1]'(by omega) := by
                have h1 : cur = prev := by simpa [sd, hcur_tl, hprev_hc] using hc
                exact h1.trans hprev_eq
              ev_steps; exact hLd (na.toNat - (si + 1#32).toNat) (ua, si + 1#32, ()) md (by omega)
                ⟨rfl, tmpd, htl_d, by omega, by omega, fun _ => hua_pos,
                 fun j hj1 hj2 => htail_d j (by omega) hj2, hsub_tmps,
                 fun j hj => by
                   rw [hsi1] at hj
                   by_cases hjs : j = si.toNat
                   · subst hjs; refine ⟨ua.toNat - 1, by omega, ?_⟩
                     rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hcp,
                       List.getElem?_eq_getElem hsi_ts, Option.getD_some]
                   · exact hcov_d j (by omega), hmd⟩
            · have hcx : cur = prev ^^^ 1#32 := by simpa [sd, hcur_tl, hprev_hc] using hc
              have hcl :=
                t0_dedup_clash (by omega) (by omega) hua_pos hsi_lt hprev_eq hsub_tmps hcx
              ev_steps; exact hBd (true, ua, si + 1#32, ()) md
                ⟨tmpd, htl_d, by omega, hsub_tmps, fun _ => Or.inr hcl,
                 (fun h => by cases h), hmd⟩
            · obtain ⟨ht', hs', hc'⟩ :=
                t0_dedup_set_inv hua_le hsi_lt (by omega) hsi_ts htail_d hsub_tmps hcov_d
              clear hc; ev_steps
              refine hJua (false, ua + 1#32, ()) m ⟨tmpd.set ua.toNat cur, by simp [htl_d],
                by omega, by omega, fun _ => by omega,
                (fun j hj1 hj2 => ht' j (by omega) hj2), (fun j hj => hs' j (by omega)),
                (fun j hj => by rw [hua1]; exact hc' j (by omega)),
                (by dsimp only [sd] at hm; rw [bv_zext32_toNat, hcur_eq] at hm; exact hm)⟩
        · have hsi_eq : si.toNat = na.toNat := by omega
          rw [hsi_eq] at hua_pos_if hcov_d
          ev_steps; exact hBd (false, ua, si, ()) md
            ⟨tmpd, htl_d, hsi_eq ▸ hua_le, hsub_tmps, (fun h => by cases h),
             fun _ => ⟨hua_pos_if hna_pos, hcov_d⟩, hmd⟩
      · intro _ Ld _ hLd; ev_steps
        exact hLd na.toNat (0#32, 0#32, ()) ms ⟨rfl, tmps, htl_s, Nat.zero_le _, Nat.zero_le _,
          fun h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
          fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), hms⟩
    · intro _ hJsort; ev_split
      · clear hc; ev_steps; c0_call hSort
        refine ⟨tmpl, ArrayField.tmp.rest c sl ⋆ R, by omega, focus_full_tmp hml,
          fun tmps ms htl_s hperm_s _ hms => ?_⟩
        have hms' : (FullMem c { s0 with core := { s0.core with tmp := tmps } } ⋆ R) ms :=
          unfocus_full_tmp hms
        obtain ⟨hsub_s, hfwd_s⟩ := t0_post_sort (htl_s.trans htl_l) htl_l hna_le
          (Nat.le_trans har_cv hcv_le) hperm_s hsub_l hfwd_l
        ev_steps; exact hJsort () ms ⟨tmps, htl_s.trans htl_l, hsub_s, hfwd_s, hms'⟩
      · ev_steps; exact hJsort () ml ⟨tmpl, htl_l, hsub_l, hfwd_l, hml⟩
  · rintro Bl Ll rem ⟨il, na, ⟨⟩⟩ ml hBl hLl
      ⟨rfl, tmpl, htl_l, hna_le, hil_le, htail_l, hsub_l, hnohf_l, hml⟩
    let sl : FullState := { s0 with core := { s0.core with tmp := tmpl } }
    change (FullMem c sl ⋆ R) ml at hml
    by_cases hil_lt : il.toNat < arity.toNat
    · have hil_arr : (il.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
      have hil_tl : il.toNat < tmpl.length := by omega
      have hil_raw : il.toNat < raw.length := by omega
      have hr_tl : tmpl[il.toNat]'hil_tl = raw[il.toNat]'hil_raw := by
        have h1 := (htail_l il.toNat (Nat.le_refl _) hil_lt).trans
          (List.getElem?_eq_getElem hil_raw)
        rw [List.getElem?_eq_getElem hil_tl] at h1; exact Option.some.inj h1
      have hr_eq : tmpl[(il.setWidth 64).toNat]'hil_arr = raw[il.toNat]'hil_raw :=
        (list_getElem_congr (bv_zext32_toNat il) hil_arr hil_tl).trans hr_tl
      have hr_lt : (raw[il.toNat]'hil_raw).toNat < 2 * cv0 := by
        simpa [List.getElem?_eq_getElem hil_raw] using hraw_lt il.toNat hil_lt
      have hr_vals' : (raw[il.toNat]'hil_raw).toNat < s0.core.vals.length := by omega
      have hr_vals_tl : (tmpl[il.toNat]'hil_tl).toNat < s0.core.vals.length := by
        rw [hr_tl]; exact hr_vals'
      have hr_vals : ((tmpl[(il.setWidth 64).toNat]'hil_arr).setWidth 64).toNat <
          s0.core.vals.length := by rw [hr_eq, bv_zext32_toNat]; exact hr_vals'
      have hr_vals_sl : (BitVec.setWidth 64
          (sl.core.tmp[(BitVec.setWidth 64 il).toNat]'hil_arr)).toNat < sl.core.vals.length :=
        hr_vals
      have hrv_get_tl : s0.core.vals[(tmpl[il.toNat]'hil_tl).toNat]'hr_vals_tl =
          s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' :=
        list_getElem_congr (by rw [hr_tl]) hr_vals_tl hr_vals'
      have hrv_dom := hw0.vals_domain (raw[il.toNat]'hil_raw).toNat (hcv_eq.symm ▸ hr_lt)
      have hil1 : (il + 1#32).toNat = il.toNat + 1 := bv32_add1_lt_of (by omega)
      have hna1 : (na + 1#32).toNat = na.toNat + 1 := bv32_add1_lt_of (by omega)
      ev_split
      · have hff := t0_vals_ff_of_slt0 hil_raw hr_vals' hrv_dom
          (by rw [← hrv_get_tl]; simpa [sl] using hc)
        ev_steps; exact hBl (il, true, na, ()) ml
          ⟨tmpl, htl_l, by omega, fun _ => ⟨il.toNat, hil_lt, hff⟩, (fun h => by cases h), hml⟩
      have hnslt : ((s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals').signExtend 32).slt
          0#32 = false := by rw [← hrv_get_tl]; simpa [sl] using hc
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [i32])
        (fun (na', ()) ml' => ∃ t' : List (BitVec 32), t'.length = c.max_vars ∧
          na'.toNat ≤ (il + 1#32).toNat ∧ (il + 1#32).toNat ≤ arity.toNat ∧
          (∀ j, (il + 1#32).toNat ≤ j → j < arity.toNat → t'[j]? = raw[j]?) ∧
          (∀ j < na'.toNat, ∃ k < arity.toNat, t'[j]? = raw[k]?) ∧
          (∀ k < (il + 1#32).toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
            ∃ j < na'.toNat, t'[j]? = raw[k]?) ∧
          (FullMem c { s0 with core := { s0.core with tmp := t' } } ⋆ R) ml')
        (fun _ ⟨na', ⟨⟩⟩ ml' h => by
          ev_steps; exact hLl (arity.toNat - (il + 1#32).toNat) (il + 1#32, na', ()) ml'
            (by omega) ⟨rfl, h⟩) ?_
      have hna_arr : (na.setWidth 64).toNat < sl.core.tmp.length := by
        change (na.setWidth 64).toNat < tmpl.length; rw [bv_zext32_toNat]; omega
      intro Jna hJna; ev_split
      · obtain ⟨ht', hs', hn'⟩ :=
          t0_pass1_set_inv hna_le hil_lt (by omega) hil_raw htail_l hsub_l hnohf_l
        clear hc; ev_steps
        refine hJna (na + 1#32, ()) m ⟨tmpl.set na.toNat (raw[il.toNat]'hil_raw), by simp [htl_l],
          by omega, by omega, (fun j hj1 hj2 => ht' j (by omega) hj2),
          (fun j hj => hs' j (by omega)),
          (fun k hk => by rw [hna1]; exact hn' k (by omega)),
          (by dsimp only [sl] at hm; rw [bv_zext32_toNat, hr_eq] at hm; exact hm)⟩
      · have h1_val := t0_vals_1_of_nslt0_ne0 hil_raw hr_vals' hrv_dom hnslt
          (by rw [← hrv_get_tl]; simpa [sl] using hc)
        ev_steps; exact hJna (na, ()) ml ⟨tmpl, htl_l, by omega, by omega,
          fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l,
          fun k hk => by
            rw [hil1] at hk; by_cases hki : k = il.toNat
            · subst hki; exact Or.inl h1_val
            · exact hnohf_l k (by omega), hml⟩
    · have hil_eq : il.toNat = arity.toNat := by omega
      ev_steps; exact hBl (il, false, na, ()) ml
        ⟨tmpl, htl_l, by omega, (fun h => by cases h),
         fun _ => ⟨hil_eq, hsub_l, hil_eq ▸ hnohf_l⟩, hml⟩
  · intro _ _ _ hLp; ev_steps
    exact hLp arity.toNat (0#32, 0#32, ()) m0 ⟨rfl, s0.core.tmp, htmpl0, Nat.zero_le _,
      Nat.zero_le _, fun j _ hj => by simp only [raw, List.getElem?_take_of_lt hj],
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
