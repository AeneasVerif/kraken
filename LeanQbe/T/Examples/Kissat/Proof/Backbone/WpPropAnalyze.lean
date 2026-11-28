/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Backbone WP Proofs — Propagation & Analysis (`Proof.Backbone.WpPropAnalyze`)

Canonical `(Γ : Env)` `Func.wp` proofs (`0` `@[expose]` on theorems/lemmas) for:
1. `full_backbone_prop_m6_wp` (`fullBackbonePropM6Spec`)
2. `full_backbone_analyze_m6_wp` (`fullBackboneAnalyzeM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Backbone
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. File-Local Step Helpers -/

private theorem pa_strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem pa_strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem pa_strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "bb_strip" : tactic =>
  `(tactic| first
    | apply pa_strip_le_32_64 | apply pa_strip_le_8_32 | apply pa_strip_le_8_64)
local macro "bb_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "bb_step" : tactic => `(tactic| ((try bb_unmdata); (repeat bb_strip); c0_step))
local macro "bb_steps" : tactic =>
  `(tactic| (
      (try bb_unmdata)
      (repeat bb_strip)
      c0_steps
      repeat (any_goals (bb_strip; repeat bb_strip); c0_steps)))

open Lean Elab Tactic in
local elab "bb_to_group" : tactic => do
  evalTactic (← `(tactic| ((try bb_unmdata); (repeat bb_strip))))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push g
    setGoals out.toList
  go 500

/-! ## 2. `full_backbone_prop_m6_wp` (`fullBackbonePropM6Spec`) -/

private def S13BbPropStInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (saved0 max_lvl prop_start : Nat)
    (R : Mem 64 → Prop) (vals' : List (BitVec 8)) (lvl' rsns' trl' : List (BitVec 32))
    (te' : Nat) (c0' c1' asz' : BitVec 64) (m : Mem 64) : Prop :=
  let st' : FullState :=
    { st with
      core := { st.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
        confl_lit0 := c0', confl_lit1 := c1' }
      scratch := { st.scratch with ant_sz := asz' } }
  BbTrailInv c F0 F_cur s0 st' saved0 max_lvl ∧ st.core.trail_end ≤ te' ∧
  (∀ i < st.core.trail_end, trl'[i]? = st.core.trl[i]?) ∧
  (∀ i < st.core.trail_end,
    let v := (st.core.trl[i]?.getD 0#32).toNat / 2
    lvl'[v]? = st.core.lvl[v]? ∧ rsns'[v]? = st.core.rsns[v]?) ∧
  (st.core.cur_level = 0 → ∀ i, prop_start ≤ i → i < te' →
    (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
  (∀ saved, saved0 ≤ saved → saved ≤ prop_start → 0 < st.core.cur_level →
    BackboneProbeSeg F_cur st saved st.core.cur_level →
    BackboneProbeSeg F_cur st' saved st.core.cur_level) ∧
  (FullMem c st' ⋆ R) m

theorem full_backbone_prop_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackbonePropM6Spec a m Q X →
      Func.wp Γ full_backbone_prop_m6_body a m Q X := by
  rintro ⟨h, prop_start, stop_early, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt0, hs0_le, hps_le, hmode, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.core_ok.cur_vars_le
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt0.same_core]
  have hmw : WatchesInv F_cur s0.core := by
    have h := hsp0.2.1.watches; simp only [ModeWatchesInv, hsp0.2.2.2.2.2, ↓reduceIte] at h
    exact h
  have hwl_le : s0.core.wlen ≤ c.wcap := hsp0.1.core_ok.wlen_le
  have hcl_lt32 : st.core.cur_level < 2 ^ 32 := by
    rcases hmode with ⟨hc0, _⟩ | ⟨_, hcm⟩ <;> omega
  have hcl_tr : ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = st.core.cur_level := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : st.core.cur_level < 2 ^ 64), Nat.mod_eq_of_lt hcl_lt32]
  have hnlits_eq :
      ((BitVec.ofNat 64 st.core.cur_vars) <<< (BitVec.signExtend 64 1#32)).toNat =
        2 * s0.core.cur_vars := by
    rw [hcv_st,
      bb_bv64_shl1_sext _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_backbone_prop_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (tk, prop, ()) m1 =>
      ∃ vals1 lvl1 rsns1 trl1 te1 c01 c11 asz1,
        prop_start.toNat ≤ prop.toNat ∧ prop.toNat ≤ te1 ∧
        S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
          vals1 lvl1 rsns1 trl1 te1 c01 c11 asz1 m1)
    (fun (_, prop, ()) _ => c.max_vars - prop.toNat) ?_ ?_
  · intro J1 hJ1; bb_steps
    exact hJ1 (st.scratch.ant_sz, prop_start, ()) m0
      ⟨st.core.vals, st.core.lvl, st.core.rsns, st.core.trl, st.core.trail_end,
       st.core.confl_lit0, st.core.confl_lit1, st.scratch.ant_sz, Nat.le_refl _, hps_le,
       hbt0, Nat.le_refl _, (fun _ _ => rfl), (fun _ _ => ⟨rfl, rfl⟩),
       (fun hc0 => hmode.elim (fun h => h.2) (fun h => by omega)),
       (fun _ _ _ _ hsg => hsg), hm0⟩
  · rintro J1 ⟨tk, prop, ⟨⟩⟩ m1
      ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hps1, hp_le, hbt1, hte_ge, htrl_pre,
       hlvl_pre, hl0_1, hseg_1, hm1⟩ ih1
    let st1 : FullState :=
      { st with
        core := { st.core with
          vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_end := te1,
          confl_lit0 := c01, confl_lit1 := c11 }
        scratch := { st.scratch with ant_sz := asz1 } }
    have hcv_st1 : st1.core.cur_vars = s0.core.cur_vars := by rw [hbt1.same_core]
    have hte1_le : te1 ≤ c.max_vars :=
      Nat.le_trans hbt1.len_ok.core_ok.trail_end_le (by rw [hcv_st1]; omega)
    c0_hsplit
    · have hp_lt : prop.toNat < te1 := by
        have h1 : prop.toNat < te1 % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hp_trl : prop.toNat < st1.core.trl.length := by
        dsimp only [st1]; rw [hbt1.len_ok.core_ok.trl_len]; omega
      have hp1 : (prop + 1#64).toNat = prop.toNat + 1 := by bv_omega
      let lit := trl1[prop.toNat]'hp_trl
      let not_lit := lit ^^^ 1#32
      have hlit_get : (trl1[prop.toNat]?.getD 0#32) = lit := by
        rw [List.getElem?_eq_getElem hp_trl, Option.getD_some]
      have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by
        have := hbt1.trl_lits_lt prop.toNat hp_lt; rwa [hlit_get] at this
      have hnl_eq : not_lit.toNat = lit.toNat ^^^ 1 := bb_bv32_xor1 lit
      have hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars := by
        rw [hnl_eq]; exact litNeg_lt_two_mul hlit_lt
      have hwv_eq : st1.core.wvec = s0.core.wvec := by rw [hbt1.same_core]
      have hwv_len : st1.core.wvec.length = 4 * c.max_vars := hbt1.len_ok.core_ok.wvec_len
      have hnl_64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hnl_w0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat := by
        rw [bb_bv64_shl1_nat _ (by rw [hnl_64]; omega), hnl_64]
      have hnl_w1 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
          2 * not_lit.toNat + 1 := by
        rw [BitVec.toNat_add, hnl_w0, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hnl_w0_lt : (BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1).toNat <
          st1.core.wvec.length := by
        change (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st1.core.wvec.length; omega
      have hnl_w1_lt : ((BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1) + 1#64).toNat <
          st1.core.wvec.length := by
        change ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st1.core.wvec.length; omega
      have hbd_nl := hmw.layout.bounds not_lit.toNat hnl_lt
      have hslice0 := hmw.slices not_lit.toNat hnl_lt
      let off_n := fullWatchOffCore s0.core not_lit.toNat
      let sz_n := fullWatchSizeCore s0.core not_lit.toNat
      have hend_bd : off_n + sz_n ≤ c.wcap := Nat.le_trans hbd_nl hwl_le
      have hoff_eq :
          (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).toNat =
            off_n := by
        unfold off_n fullWatchOffCore
        have hg : st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega) =
            s0.core.wvec[2 * not_lit.toNat]?.getD 0#32 := by
          rw [← hwv_eq, ← hnl_w0, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hg]
      have hsz_eq :
          (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
            sz_n := by
        unfold sz_n fullWatchSizeCore
        have hg : st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega) =
            s0.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32 := by
          rw [← hwv_eq, ← hnl_w1, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hg]
      have hoff_64 :
          (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 =
            BitVec.ofNat 64 off_n :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, hoff_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)])
      have hsz_64 :
          (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
            omega)).setWidth 64 = BitVec.ofNat 64 sz_n :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, hsz_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)])
      have hend_64 :
          ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 +
           (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
            omega)).setWidth 64).toNat = off_n + sz_n := by
        rw [hoff_64, hsz_64, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, .bool]) (lpTs := [i64])
        (fun (_q_o, confl_o, ()) m_o =>
          ∃ vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2,
            prop.toNat + 1 ≤ te2 ∧
            S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
              vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m_o ∧
            (confl_o = true →
              c02.toNat < 2 * s0.core.cur_vars ∧ c12.toNat < 2 * s0.core.cur_vars ∧
              vals2[c02.toNat]?.getD 0#8 = 0xFF#8 ∧ vals2[c12.toNat]?.getD 0#8 = 0xFF#8 ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [c02.toNat, c12.toNat]) ∧
              ∃ idx0, prop_start.toNat ≤ idx0 ∧ idx0 < te2 ∧
                (trl2[idx0]?.getD 0#32).toNat = c02.toNat ^^^ 1))
        (fun rem (q, ()) m2 =>
          ∃ vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2,
            off_n ≤ q.toNat ∧ q.toNat ≤ off_n + sz_n ∧ rem = off_n + sz_n - q.toNat ∧
            WatchSliceOk F_cur s0.core not_lit.toNat q.toNat (off_n + sz_n - q.toNat) ∧
            te1 ≤ te2 ∧ (∀ i < te1, trl2[i]? = trl1[i]?) ∧
            S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
              vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m2) ?_ ?_ ?_
      · rintro _ ⟨_q_o, confl_o, ⟨⟩⟩ m_o
          ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hp_le2,
           ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm_o⟩, hcf2⟩
        bb_to_group
        refine wp_join_group (ts := [i64]) (fun _ m_t => m_t = m_o)
          (fun _ ⟨tk_n, ⟨⟩⟩ m_t heq => by
            subst heq; c0_hsplit
            · c0_hsteps
              exact hQ false vals2 lvl2 rsns2 trl2 te2 c02 c12 tk_n _
                (BbTrailInv.with_ant_sz hbt2 tk_n) hte2 htp2 hlp2
                (fun sv hs1 hs2 hc' hsg => bb_probeSeg_with_confl_asz
                  (hsg2 sv hs1 hs2 hc' hsg) c02 c12 tk_n)
                (fun _ => hcf2 (by revert hc; cases confl_o <;> decide)) (by assumption)
            · c0_hsteps
              exact ih1 (tk_n, prop + 1#64, ()) m_t (by dsimp only; omega)
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega, by omega,
                 hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm_o⟩)
          (fun Jt hJt => by c0_hsteps <;> exact hJt _ _ rfl)
      · rintro B L rem ⟨q, ⟨⟩⟩ m2 hB hL
          ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hq_ge, hq_le, hrem, hslice_q,
           hte12, htrl12, hinv2⟩
        subst hrem
        rcases hinv2 with ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
        let st2 : FullState :=
          { st with
            core := { st.core with
              vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
              confl_lit0 := c02, confl_lit1 := c12 }
            scratch := { st.scratch with ant_sz := asz2 } }
        have hcv_st2 : st2.core.cur_vars = s0.core.cur_vars := by rw [hbt2.same_core]
        have hte2_le : te2 ≤ c.max_vars :=
          Nat.le_trans hbt2.len_ok.core_ok.trail_end_le (by rw [hcv_st2]; omega)
        c0_hsplit
        · have hq_lt : q.toNat < off_n + sz_n := by
            have hwvl : st.core.wvec.length = 4 * c.max_vars := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              rw [hwv, hwv_len]
            have hnl_v : trl1[prop.toNat].toNat ^^^ 1 = not_lit.toNat := hnl_eq.symm
            have h0_mod : (2 * not_lit.toNat) % 2 ^ 64 = 2 * not_lit.toNat :=
              Nat.mod_eq_of_lt (by omega)
            have h1_mod : (2 * not_lit.toNat + 1) % 2 ^ 64 = 2 * not_lit.toNat + 1 :=
              Nat.mod_eq_of_lt (by omega)
            have h0 : st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64].toNat = off_n := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              have helem : st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64] =
                  st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat] := by
                rw [← Option.some_inj,
                  ← List.getElem?_eq_getElem (by rw [hwv, hwv_len]; omega),
                  ← List.getElem?_eq_getElem (by rw [hwv_len, hnl_w0]; omega), hwv]
                simp only [hnl_v, h0_mod, hnl_w0]
              rw [helem, hoff_eq]
            have h1 :
                st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64].toNat = sz_n := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              have helem : st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64] =
                  st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat] := by
                rw [← Option.some_inj,
                  ← List.getElem?_eq_getElem (by rw [hwv, hwv_len]; omega),
                  ← List.getElem?_eq_getElem (by rw [hwv_len, hnl_w1]; omega), hwv]
                simp only [hnl_v, h1_mod, hnl_w1]
              rw [helem, hsz_eq]
            have hc' : q.toNat <
                (st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64].toNat +
                 st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64].toNat) %
                  2 ^ 64 := by
              simpa [hnl_v, (by omega : (2 * not_lit.toNat + 1) % 2 ^ 64 < st.core.wvec.length)]
                using hc
            rw [h0, h1] at hc'
            omega
          have hq_ws : q.toNat < st2.core.wstk.length := by
            have : st2.core.wstk.length = c.wcap := hbt2.len_ok.core_ok.wstk_len_arr; omega
          let qw := st2.core.wstk[q.toNat]'hq_ws
          have hqw_s0 : s0.core.wstk[q.toNat]? = some qw := by
            have hws2 : st2.core.wstk = s0.core.wstk := by rw [hbt2.same_core]
            rw [← hws2, List.getElem?_eq_getElem hq_ws]
          c0_hsplit
          · have hlg_f : (qw &&& 0x80000000#32) = 0#32 := by c0_bound
            obtain ⟨_, _, _, _, _, hslice_2⟩ :=
              watchSlice_inv_large hslice_q (by omega) hqw_s0 hlg_f
            c0_hsplit
            · c0_hsteps
              exact hB (q, false, ()) m2
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega,
                 ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩, fun h => by cases h⟩
            · have hq2 : (q + 2#64).toNat = q.toNat + 2 := by bv_omega
              c0_hsteps
              exact hL (off_n + sz_n - (q.toNat + 2)) (q + 2#64, ()) m2 (by omega)
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega, by omega, by rw [hq2],
                 by simpa [hq2, show off_n + sz_n - (q.toNat + 2) =
                   off_n + sz_n - q.toNat - 2 by omega] using hslice_2,
                 hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
          · have hbf : (qw &&& 0x80000000#32) ≠ 0#32 := by c0_bound
            obtain ⟨_, hot_lt, hent_bin, hslice_1⟩ :=
              watchSlice_inv_bin hslice_q (by omega) hqw_s0 hbf
            have hq1 : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
            let ot := qw &&& 0x7FFFFFFF#32
            have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
            have hot_v : ot.toNat < vals2.length := by
              have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
            have hot_not_lt : ot.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hot_lt'
            have hot_not_v : (ot ^^^ 1#32).toNat < (vals2.set ot.toNat 1#8).length := by
              rw [List.length_set, bb_bv32_xor1]
              have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [.bool])
              (fun _ m3 => ∃ vals3 lvl3 rsns3 trl3 te3 c03 c13 asz3,
                te1 ≤ te3 ∧ (∀ i < te1, trl3[i]? = trl1[i]?) ∧
                S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
                  vals3 lvl3 rsns3 trl3 te3 c03 c13 asz3 m3)
              (fun _ ⟨_, ⟨⟩⟩ m3 ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3,
                  hte13, htrl13, hinv3⟩ => by
                c0_hsteps
                exact hL (off_n + sz_n - (q.toNat + 1)) (q + 1#64, ()) m3 (by omega)
                  ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3, by omega, by omega,
                   by rw [hq1], by simpa [hq1, show off_n + sz_n - (q.toNat + 1) =
                     off_n + sz_n - q.toNat - 1 by omega] using hslice_1,
                   hte13, htrl13, hinv3⟩)
              (fun Jc hJc => by
                have hot_dom := hbt2.vals_dom ot.toNat hot_lt'
                rw [List.getElem?_eq_getElem hot_v, Option.getD_some] at hot_dom
                c0_hsplit
                · c0_hsplit
                  · have hot_ff : vals2[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                      rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                      exact (bb_bv8_dom_slt0 hot_dom).mp hc
                    have hnl_ff : vals2[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
                      have hv := (hbt2.trl_vals_ok prop.toNat (by dsimp only [st2]; omega)).2
                      rw [htrl12 prop.toNat hp_lt, hlit_get] at hv; rwa [hnl_eq]
                    have hnl64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by bv_omega
                    have hot64 : (ot.setWidth 64).toNat = ot.toNat := by bv_omega
                    c0_hsteps
                    refine hB (q + 1#64, true, ()) _
                      ⟨vals2, lvl2, rsns2, trl2, te2, not_lit.setWidth 64, ot.setWidth 64, asz2,
                       by omega, ⟨BbTrailInv.with_confl_asz hbt2 (not_lit.setWidth 64)
                         (ot.setWidth 64) asz2, hte2, htp2, hlp2, hl0_2,
                         fun sv hs1 hs2 hc' hsg => bb_probeSeg_with_confl_asz
                           (hsg2 sv hs1 hs2 hc' hsg) _ _ _, by assumption⟩,
                       fun _ => ⟨by rw [hnl64]; exact hnl_lt, by rw [hot64]; exact hot_lt',
                         by rw [hnl64]; exact hnl_ff, by rw [hot64]; exact hot_ff,
                         by rw [hnl64, hot64]; exact hent_bin, prop.toNat, hps1, by omega,
                         by rw [htrl12 prop.toNat hp_lt, hlit_get, hnl64, hnl_eq,
                              bb_xor1_xor1]⟩⟩
                  · refine wp_unroll_group fun Jn hJn => ?_
                    c0_hsplit
                    · have hot_z : vals2[ot.toNat]?.getD 0#8 = 0#8 := by
                        rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                        exact (bb_bv8_sext32_eq0 _).mp hc
                      c0_hsplit
                      · have hte2_lt : te2 < c.max_vars := by
                          have h1 : te2 % 2 ^ 64 < c.max_vars % 2 ^ 64 := by c0_bound
                          rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                        have hte2_trl : te2 < trl2.length := by
                          have : trl2.length = c.max_vars := hbt2.len_ok.core_ok.trl_len; omega
                        have hte2_bv : (BitVec.ofNat 64 te2).toNat = te2 := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        have hot64 : (ot.setWidth 64).toNat = ot.toNat := m6_zext32_toNat ot
                        have hotn64 : ((ot ^^^ 1).setWidth 64).toNat = ot.toNat ^^^ 1 := by
                          rw [m6_zext32_toNat]; exact bb_bv32_xor1 ot
                        have hotr64 : ((ot >>> 1).setWidth 64).toNat = ot.toNat / 2 := by
                          rw [m6_zext32_toNat]
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                        have hot_v2 : (ot >>> 1).toNat < lvl2.length := by
                          have : lvl2.length = c.max_vars := hbt2.len_ok.core_ok.lvl_len
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                        have hot_r2 : (ot >>> 1).toNat < rsns2.length := by
                          have : rsns2.length = c.max_vars := hbt2.len_ok.core_ok.rsns_len
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                        have hte2_add : (BitVec.ofNat 64 te2 + 1).toNat = te2 + 1 := by
                          rw [BitVec.toNat_add, hte2_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have hmiss2 := BbTrailInv.var_unassigned hbt2 hot_lt' hot_z
                        let rsn_b := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                        have hl0_ent :
                            ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = 0 →
                            (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat]) := by
                          intro hc0'; rw [hcl_tr] at hc0'
                          have hlv_p : (lvl2[(trl2[prop.toNat]?.getD 0#32).toNat / 2]?.getD
                              0#32).toNat = 0 := hl0_2 hc0' prop.toNat hps1 (by omega)
                          have hlit_ent :=
                            hbt2.l0_entails prop.toNat (by dsimp only [st2]; omega) hlv_p
                          rw [htrl12 prop.toNat hp_lt, hlit_get] at hlit_ent
                          exact backbone_resolve_l0 (bb_entails_comm2 hent_bin)
                            (by rw [hnl_eq, bb_xor1_xor1]; exact hlit_ent)
                        have hbt3 := BbTrailInv.push hbt2 (Nat.le_refl _) (lit := ot)
                          (rsn := rsn_b)
                          (lv_bv := (BitVec.ofNat 64 st.core.cur_level).truncate 32)
                          (cl' := st.core.cur_level) hot_lt' hot_z hte2_lt
                          (by rw [hcl_tr]; exact hbt2.cur_le_max) hbt2.cur_le_max hl0_ent
                        c0_hsteps
                        refine hJc (false, ()) _ ⟨_, _, _, _, te2 + 1, c02, c12, asz2, by omega,
                          (fun i hi => by
                            rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                            exact htrl12 i hi),
                          hbt3, by omega,
                          (fun i hi => by
                            rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                            exact htp2 i hi),
                          (fun i hi => by
                            have hne_v : (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ot.toNat / 2 := by
                              rw [← htp2 i hi]; exact hmiss2 i (by dsimp only [st2]; omega)
                            dsimp only
                            rw [List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
                            exact hlp2 i hi),
                          (fun hc0' i hi1 hi2 => by
                            by_cases he : i = te2
                            · subst he
                              rw [List.getElem?_set_self hte2_trl, Option.getD_some,
                                List.getElem?_set_self (by
                                  rw [hbt2.len_ok.core_ok.lvl_len]; omega), Option.getD_some,
                                hcl_tr, hc0']
                            · rw [List.getElem?_set_ne (Ne.symm he),
                                List.getElem?_set_ne (Ne.symm (hmiss2 i
                                  (by dsimp only [st2]; omega)))]
                              exact hl0_2 hc0' i hi1 (by omega)),
                          (fun sv hs1 hs2 hc' hsg =>
                            bb_probeSeg_push hbt2 (hsg2 sv hs1 hs2 hc' hsg) hot_lt' hot_z
                              hte2_lt hcl_tr hnl_lt (bb_entails_comm2 hent_bin)
                              (by omega : sv ≤ prop.toNat)
                              (by dsimp only [st2]; omega : prop.toNat < st2.core.trail_end)
                              (by dsimp only [st2]; rw [htrl12 prop.toNat hp_lt, hlit_get,
                                hnl_eq, bb_xor1_xor1])), ?_⟩
                        refine bb_fullMem_eq ?_ (by assumption)
                        dsimp only [st2, ot, qw, rsn_b, not_lit]
                        rw [m6_zext32_toNat, m6_zext32_toNat, m6_zext32_toNat, hte2_bv, hte2_add]
                        simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                        rw [show ((st.core.wstk[q.toNat]'hq_ws &&& 2147483647) ^^^ 1).toNat =
                          (st.core.wstk[q.toNat]'hq_ws &&& 2147483647).toNat ^^^ 1 from
                          bb_bv32_xor1 _]; rfl
                      · c0_hsteps
                        exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                          hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                    · c0_hsteps
                      exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                        hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                · c0_hsteps
                  exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                    hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩)
        · c0_hsteps
          exact hB (q, false, ()) m2
            ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega,
             ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩, fun h => by cases h⟩
      · intro B L _ hL; c0_hsteps
        have hq0 : ((st.core.wvec[((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
            (1 : Nat)).toNat]'hnl_w0_lt).setWidth 64).toNat = off_n := by
          change ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
            hnl_w0_lt).setWidth 64).toNat = off_n
          rw [hoff_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hL sz_n (_, ()) m1
          ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1,
           by dsimp only; simpa only [hq0] using (Nat.le_refl off_n),
           by dsimp only; simpa only [hq0] using (Nat.le_add_right off_n sz_n),
           by dsimp only; simp only [hq0, Nat.add_sub_cancel_left],
           by dsimp only; simpa only [hq0, Nat.add_sub_cancel_left] using hslice0,
           Nat.le_refl _, (fun _ _ => rfl), hbt1, hte_ge, htrl_pre, hlvl_pre, hl0_1, hseg_1,
           hm1⟩
    · bb_steps
      exact hQ true vals1 lvl1 rsns1 trl1 te1 c01 c11 tk _ (BbTrailInv.with_ant_sz hbt1 tk)
        hte_ge htrl_pre hlvl_pre (fun sv hs1 hs2 hc hsg => bb_probeSeg_with_confl_asz
          (hseg_1 sv hs1 hs2 hc hsg) c01 c11 tk) (fun h => by cases h) (by assumption)

/-! ## 3. `full_backbone_analyze_m6_wp` (`fullBackboneAnalyzeM6Spec`) -/

theorem full_backbone_analyze_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneAnalyzeM6Spec a m Q X →
      Func.wp Γ full_backbone_analyze_m6_body a m Q X := by
  rintro ⟨h, c0, c1, saved, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt, hcl_pos, hres_eq, hs0_sav,
     hrsn_sav, hseg, hc0_lt, hc1_lt, hc0_ff, hc1_ff, hent_c,
     ⟨idx0, hidx0_ge, hidx0_lt, hidx0_eq⟩, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_st ▸ hcl.cur_vars_le
  have hte_le : st.core.trail_end ≤ c.max_vars := Nat.le_trans hcl.trail_end_le (by omega)
  have hs0_le : saved0 ≤ st.core.trail_end := Nat.le_trans hs0_sav (Nat.le_of_lt hseg.1)
  have hs0_64 : saved0 < 2 ^ 64 := by omega
  let saved_b0 := BitVec.ofNat 64 saved0
  have hsaved_nat : saved_b0.toNat = saved0 := by
    dsimp only [saved_b0]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs0_64]
  have hmrk0 : FullMrkZero c st := by
    have hm_eq : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
    exact fun v hv => by rw [hm_eq]; exact hsp0.2.2.1.1 v hv
  have hc0v : (c0 >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
  have hc1v : (c1 >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
  have hc0_lvl : (c0 >>> 1#32).toNat < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hc1_lvl : (c1 >>> 1#32).toNat < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hc0_64_lvl : (BitVec.setWidth 64 (c0 >>> 1#32)).toNat < st.core.lvl.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hc0_lvl
  have hc1_64_lvl : (BitVec.setWidth 64 (c1 >>> 1#32)).toNat < st.core.lvl.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hc1_lvl
  have hc0_mrk : (c0 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  have hc1_mrk : (c1 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  obtain ⟨idx1, hidx1_lt, hidx1_eq⟩ := hbt.vals_false_trl c1.toNat hc1_lt hc1_ff
  unfold Func.wp full_backbone_analyze_m6_body
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  · have hlv1_0 : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
      have h1 : st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl = 0#32 := by c0_bound
      have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
          st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by congr 1
      rw [heq, h1]; rfl
    have hc1_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [c1.toNat ^^^ 1]) := by
      have h := hbt.l0_entails idx1 hidx1_lt (by rw [hidx1_eq, fullInv_var_xor1]; exact hlv1_0)
      rwa [hidx1_eq] at h
    bb_steps
    exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
      ⟨by rw [bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
       by rw [bb_bv32_xor1, bb_xor1_xor1]; exact backbone_resolve_l0 hent_c hc1_ent⟩) hm0
  · have hlv1_nz : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat ≠ 0 := by
      have h1 : st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl ≠ 0#32 := by c0_bound
      rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
      have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
          st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by congr 1
      rw [heq]; intro h0; apply h1; exact BitVec.eq_of_toNat_eq h0
    have hidx1_ge : saved0 ≤ idx1 :=
      Classical.byContradiction fun hlt => by
        have hlt' : idx1 < saved0 := Nat.lt_of_not_le hlt
        have htp := hbt.trl_prefix idx1 hlt'
        have hlp := (hbt.lvl_prefix idx1 hlt').1
        have h1 := hsp0.2.1.lvl_le idx1 (hbt.saved0_eq ▸ hlt')
        rw [← hlp] at h1
        rw [← htp, hbt.s0_l0] at h1
        rw [hidx1_eq, fullInv_var_xor1] at h1
        exact hlv1_nz (by omega)
    c0_hsplit
    · have hlv0_0 : (st.core.lvl[c0.toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
        have h1 : st.core.lvl[(c0 >>> 1#32).toNat]'hc0_lvl = 0#32 := by c0_bound
        have heq : st.core.lvl[c0.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
            st.core.lvl[(c0 >>> 1#32).toNat]'hc0_lvl := by congr 1
        rw [heq, h1]; rfl
      have hc0_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat ^^^ 1]) := by
        have h := hbt.l0_entails idx0 hidx0_lt (by rw [hidx0_eq, fullInv_var_xor1]; exact hlv0_0)
        rwa [hidx0_eq] at h
      bb_steps
      exact hQ (c1 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
        ⟨by rw [bb_bv32_xor1]; exact litNeg_lt_two_mul hc1_lt,
         by rw [bb_bv32_xor1, bb_xor1_xor1]
            exact backbone_resolve_l0 (bb_entails_comm2 hent_c) hc0_ent⟩) hm0
    · c0_hsplit
      · have hce : c0 = c1 := by c0_bound
        subst hce; bb_steps
        exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
          ⟨by rw [bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
           by rw [bb_bv32_xor1, bb_xor1_xor1]; exact backbone_collapse_eq hent_c⟩) hm0
      · have hc_ne : c0 ≠ c1 := by c0_bound
        have hidx_ne : idx0 ≠ idx1 := fun he => by
          subst he
          have h1 := congrArg (· ^^^ 1) (hidx0_eq.symm.trans hidx1_eq)
          rw [bb_xor1_xor1, bb_xor1_xor1] at h1
          exact hc_ne (BitVec.eq_of_toNat_eq h1)
        have hv_ne : c0.toNat / 2 ≠ c1.toNat / 2 := fun he =>
          hidx_ne (hbt.trl_vars_nodup idx0 idx1 hidx0_lt hidx1_lt
            (by rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact he))
        have hc0_mrk64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat < st.core.mrk.length := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := BitVec.isLt (c0 >>> 1); omega)]
          exact hc0_mrk
        have hc1_mrk64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat <
            (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).length := by
          rw [List.length_set, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := BitVec.isLt (c1 >>> 1); omega)]
          exact hc1_mrk
        c0_hstraight
        refine wp_join_group (ts := [i64, i32])
          (fun (_, res, ()) m_cl => ∃ mrk_c : List (BitVec 8), mrk_c.length = c.max_vars ∧
            (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 ≠ 0#8 →
              ∃ i, saved0 ≤ i ∧ i < st.core.trail_end ∧
                (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
            (res ≠ 0xFFFFFFFF#32 → res.toNat < 2 * s0.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [res.toNat ^^^ 1])) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_c } } ⋆ R) m_cl)
          (fun _ ⟨_, res, ⟨⟩⟩ m_cl ⟨mrk_c, hmc_len, hmc_dom, hres_ok, hm_cl⟩ => by
            have hc0_mc : (BitVec.setWidth 64 (c0 >>> 1)).toNat < mrk_c.length := by
              rw [hmc_len, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := BitVec.isLt (c0 >>> 1); omega)]
              exact hc0v
            let mrk_c1 := mrk_c.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 0#8
            have hc1_mc : (BitVec.setWidth 64 (c1 >>> 1)).toNat < mrk_c1.length := by
              dsimp only [mrk_c1]
              rw [List.length_set, hmc_len, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := BitVec.isLt (c1 >>> 1); omega)]
              exact hc1v
            let mrk_c2 := mrk_c1.set (BitVec.setWidth 64 (c1 >>> 1)).toNat 0#8
            have hmc2_len : mrk_c2.length = c.max_vars := by simp [mrk_c2, mrk_c1, hmc_len]
            have hmc2_dom : ∀ v < c.max_vars, mrk_c2[v]?.getD 0#8 ≠ 0#8 →
                ∃ i, saved0 ≤ i ∧ i < st.core.trail_end ∧
                  (st.core.trl[i]?.getD 0#32).toNat / 2 = v := by
              intro v hv hnz
              dsimp only [mrk_c2, mrk_c1] at hnz
              by_cases h1 : v = (BitVec.setWidth 64 (c1 >>> 1)).toNat
              · subst h1; rw [List.getElem?_set_self hc1_mc, Option.getD_some] at hnz
                exact absurd rfl hnz
              · rw [List.getElem?_set_ne (Ne.symm h1)] at hnz
                by_cases h0 : v = (BitVec.setWidth 64 (c0 >>> 1)).toNat
                · subst h0; rw [List.getElem?_set_self hc0_mc, Option.getD_some] at hnz
                  exact absurd rfl hnz
                · rw [List.getElem?_set_ne (Ne.symm h0)] at hnz
                  exact hmc_dom v hv hnz
            c0_hsteps_nogrp
            refine wp_loop_inv (ts := [i64])
              (fun (k, ()) mk => ∃ mrk_k : List (BitVec 8), mrk_k.length = c.max_vars ∧
                saved0 ≤ k.toNat ∧ k.toNat ≤ st.core.trail_end ∧
                (∀ v < c.max_vars, mrk_k[v]?.getD 0#8 ≠ 0#8 →
                  ∃ i, k.toNat ≤ i ∧ i < st.core.trail_end ∧
                    (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
                (FullMem c { st with core := { st.core with mrk := mrk_k } } ⋆ R) mk)
              (fun (k, ()) _ => st.core.trail_end - k.toNat) ?_ ?_
            · intro Jk hJk; bb_steps
              have hres_nat : st.scratch.res_sz.toNat = saved0 := by
                rw [hres_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs0_64]
              exact hJk (st.scratch.res_sz, ()) _
                ⟨mrk_c2, hmc2_len, by rw [hres_nat]; exact Nat.le_refl _, by rw [hres_nat]; omega,
                 by simpa only [hres_nat] using hmc2_dom, by assumption⟩
            · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨mrk_k, hmk_len, hk_ge, hk_le, hmk_dom, hmk⟩ ihk
              bb_step; bb_step; bb_step
              · have hk_lt : k.toNat < st.core.trail_end := by
                  have h1 : k.toNat < st.core.trail_end % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                have hk_trl : k.toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
                let zk := st.core.trl[k.toNat]'hk_trl
                have hzk_lt : zk.toNat < 2 * s0.core.cur_vars := by
                  have := hbt.trl_lits_lt k.toNat hk_lt
                  rwa [List.getElem?_eq_getElem hk_trl, Option.getD_some] at this
                have hzk_mrk : (zk >>> 1#32).toNat < mrk_k.length := by
                  rw [bb_bv32_lshr1, hmk_len]; omega
                bb_steps
                refine ihk (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨mrk_k.set (zk >>> 1#32).toNat 0#8, by simp [hmk_len], by omega, by omega,
                   fun v hv hnz => ?_, hm⟩
                have hv_ne_k : v ≠ (zk >>> 1#32).toNat := fun he => by
                  subst he; rw [List.getElem?_set_self hzk_mrk, Option.getD_some] at hnz
                  exact hnz rfl
                rw [List.getElem?_set_ne hv_ne_k.symm] at hnz
                obtain ⟨i, hi1, hi2, hieq⟩ := hmk_dom v hv hnz
                have hi_ne_k : i ≠ k.toNat := fun he => by
                  subst he; apply hv_ne_k
                  rw [bb_bv32_lshr1, ← hieq, List.getElem?_eq_getElem hk_trl, Option.getD_some]
                exact ⟨i, by omega, hi2, hieq⟩
              · have hk_eq : k.toNat = st.core.trail_end := by
                  have h1 : st.core.trail_end % 2 ^ 64 ≤ k.toNat := by c0_bound
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
                bb_steps
                refine hQ res mrk_k mk hmk_len
                  (fun v hv => Classical.byContradiction fun hnz => by
                    obtain ⟨i, hi1, hi2, _⟩ := hmk_dom v hv hnz; omega)
                  hres_ok hmk)
          (fun Jbr hJbr => ?_)
        refine wp_loop_inv (ts := [i64])
          (fun (t, ()) mt => ∃ mrk_t : List (BitVec 8), mrk_t.length = c.max_vars ∧
            saved0 ≤ t.toNat ∧ t.toNat ≤ st.core.trail_end ∧
            (∃ i1 i2, saved0 ≤ i1 ∧ i1 < i2 ∧ saved.toNat ≤ i2 ∧ i2 < t.toNat ∧
              (∀ v < c.max_vars, mrk_t[v]?.getD 0#8 ≠ 0#8 ↔
                v = (st.core.trl[i1]?.getD 0#32).toNat / 2 ∨
                v = (st.core.trl[i2]?.getD 0#32).toNat / 2) ∧
              (cnfOfClauses F_cur).EntailsClause
                (cnfClause [(st.core.trl[i1]?.getD 0#32).toNat ^^^ 1,
                            (st.core.trl[i2]?.getD 0#32).toNat ^^^ 1])) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_t } } ⋆ R) mt)
          (fun (t, ()) _ => t.toNat) ?_ ?_
        · intro Jt hJt; bb_steps
          let mrk_init := (st.core.mrk.set (c0 >>> 1#32).toNat 1#8).set (c1 >>> 1#32).toNat 1#8
          have hmi_len : mrk_init.length = c.max_vars := by simp [mrk_init, hcl.mrk_len]
          have hmi_iff : ∀ v < c.max_vars,
              mrk_init[v]?.getD 0#8 ≠ 0#8 ↔ v = c0.toNat / 2 ∨ v = c1.toNat / 2 := fun v hv => by
            dsimp only [mrk_init]
            by_cases h1 : v = c1.toNat / 2
            · subst h1
              rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from bb_bv32_lshr1 c1,
                List.getElem?_set_self (by simp [hcl.mrk_len]; omega), Option.getD_some]
              exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
            · rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from bb_bv32_lshr1 c1,
                List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : v = c0.toNat / 2
              · subst h0
                rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from bb_bv32_lshr1 c0,
                  List.getElem?_set_self (by rw [hcl.mrk_len]; omega), Option.getD_some]
                exact ⟨fun _ => Or.inl rfl, fun _ => by decide⟩
              · rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from bb_bv32_lshr1 c0,
                  List.getElem?_set_ne (Ne.symm h0), hmrk0 v hv]
                exact ⟨fun h => absurd rfl h,
                  fun h => h.elim (fun he => absurd he h0) (fun he => absurd he h1)⟩
          have hst_mi : ({ st with core := { st.core with
              mrk := (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).set
                (BitVec.setWidth 64 (c1 >>> 1)).toNat 1#8 } } : FullState) =
              { st with core := { st.core with mrk := mrk_init } } := by
            dsimp only [mrk_init]
            have h0_64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat = (c0 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c0 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            have h1_64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat = (c1 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c1 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            rw [h0_64, h1_64]
          refine hJt (BitVec.ofNat 64 st.core.trail_end, ()) _
            ⟨mrk_init, hmi_len, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
             by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _, ?_,
             bb_fullMem_eq hst_mi hm⟩
          rcases Nat.lt_or_gt_of_ne hidx_ne with h01 | h10
          · refine ⟨idx0, idx1, Nat.le_trans hs0_sav hidx0_ge, h01, by omega,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx1_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, bb_xor1_xor1, bb_xor1_xor1]; exact hent_c⟩
          · refine ⟨idx1, idx0, hidx1_ge, h10, hidx0_ge,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx0_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1, or_comm]
                exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, bb_xor1_xor1, bb_xor1_xor1]
                 exact bb_entails_comm2 hent_c⟩
        · rintro Jt ⟨t, ⟨⟩⟩ mt
            ⟨mrk_t, hmt_len, ht_ge, ht_le, ⟨i1, i2, hi1_ge, hi12, hi2_sav, hi2_lt, hdom, hent2⟩,
             hmt⟩ iht
          bb_step; bb_step
          · have ht_gt : saved0 < t.toNat := by
              have h1 : saved_b0.toNat < t.toNat := by simpa [hres_eq] using (by c0_bound : _)
              rwa [hsaved_nat] at h1
            have ht_sub : (t - 1#64).toNat = t.toNat - 1 := by bv_omega
            have ht1_trl : (t - 1#64).toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
            let z := st.core.trl[(t - 1#64).toNat]'ht1_trl
            have hz_get : st.core.trl[t.toNat - 1]?.getD 0#32 = z := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [z]
              simp only [ht_sub]
            have hz_lt : z.toNat < 2 * s0.core.cur_vars := by
              have := hbt.trl_lits_lt (t.toNat - 1) (by omega); rwa [hz_get] at this
            have hzv_lt : (z >>> 1#32).toNat < c.max_vars := by rw [bb_bv32_lshr1]; omega
            have hzv_mrk : (z >>> 1#32).toNat < mrk_t.length := by rw [hmt_len]; omega
            have hzv_rsn : (z >>> 1#32).toNat < st.core.rsns.length := by
              rw [hcl.rsns_len]; omega
            bb_step; bb_step; bb_step
            · have hm_z0 : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some]
                exact (bb_bv8_zext32_eq0 _).mp (by c0_bound)
              have hi2_ne : i2 ≠ t.toNat - 1 := fun he => by
                have hnz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 :=
                  (hdom _ hzv_lt).mpr (Or.inr (by rw [bb_bv32_lshr1, he, hz_get]))
                exact hnz hm_z0
              bb_steps
              exact iht (t - 1#64, ()) mt (by dsimp only; omega)
                ⟨mrk_t, hmt_len, by omega, by omega,
                 ⟨i1, i2, hi1_ge, hi12, hi2_sav, by omega, hdom, hent2⟩, hmt⟩
            · have hm_znz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some] at h0
                exact (by c0_bound : (mrk_t[(z >>> 1#32).toNat]'hzv_mrk).setWidth 32 ≠ 0#32)
                  ((bb_bv8_zext32_eq0 _).mpr h0)
              have hi2_eq : t.toNat - 1 = i2 := by
                rcases (hdom _ hzv_lt).mp hm_znz with h_eq1 | h_eq2
                · have := hbt.trl_vars_nodup (t.toNat - 1) i1 (by omega) (by omega)
                    (by rw [hz_get, ← bb_bv32_lshr1]; exact h_eq1)
                  omega
                · exact hbt.trl_vars_nodup (t.toNat - 1) i2 (by omega) (by omega)
                    (by rw [hz_get, ← bb_bv32_lshr1]; exact h_eq2)
              let mrk1 := mrk_t.set (z >>> 1#32).toNat 0#8
              have hm1_len : mrk1.length = c.max_vars := by simp [mrk1, hmt_len]
              have hv1_ne_v2 : (st.core.trl[i1]?.getD 0#32).toNat / 2 ≠
                  (st.core.trl[i2]?.getD 0#32).toNat / 2 := fun he => by
                have := hbt.trl_vars_nodup i1 i2 (by omega) (by omega) he; omega
              have hm1_iff : ∀ v < c.max_vars,
                  mrk1[v]?.getD 0#8 ≠ 0#8 ↔ v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := by
                intro v hv; dsimp only [mrk1]
                by_cases he : v = (z >>> 1#32).toNat
                · subst he; rw [List.getElem?_set_self hzv_mrk, Option.getD_some]
                  exact ⟨fun h => absurd rfl h, fun h => absurd h.symm (by
                    rw [bb_bv32_lshr1, ← hz_get, hi2_eq]; exact hv1_ne_v2)⟩
                · rw [List.getElem?_set_ne (Ne.symm he), hdom v hv]
                  exact ⟨fun ho => ho.elim id fun h2 => absurd
                    (by rw [h2, ← hi2_eq, hz_get, bb_bv32_lshr1]) he, Or.inl⟩
              have hrsn_get : st.core.rsns[(st.core.trl[i2]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32 = st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn := by
                rw [← hi2_eq, hz_get, ← bb_bv32_lshr1,
                  List.getElem?_eq_getElem hzv_rsn, Option.getD_some]
              c0_hsplit
              · c0_hsteps
                exact hJbr (t - 1#64, 0xFFFFFFFF#32, ()) _ ⟨mrk1, hm1_len,
                  (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                  (fun h => absurd rfl h), hm⟩
              · have hrsn_ne_ff : st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn ≠ 0xFFFFFFFF#32 := by
                  c0_bound
                c0_hsplit
                · c0_hsteps
                  exact hJbr (t - 1#64, 0xFFFFFFFF#32, ()) _ ⟨mrk1, hm1_len,
                    (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                    (fun h => absurd rfl h), hm⟩
                · have hi2_ne_sav : i2 ≠ saved.toNat := fun he => by
                    rw [← hrsn_get, he] at hrsn_ne_ff; exact hrsn_ne_ff hrsn_sav
                  have hi2_gt_s : saved.toNat < i2 := by omega
                  obtain ⟨_, hnq_lt, hent_z, j, hj_ge, hj_lt, hj_eq⟩ :=
                    (hseg.2.2 i2 (by omega) (by omega)).2 hi2_gt_s
                  rw [hrsn_get] at hnq_lt hent_z hj_eq
                  let p_l := (st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn &&& 0x7FFFFFFF#32) ^^^ 1#32
                  have hp_eq : p_l.toNat = (st.core.trl[j]?.getD 0#32).toNat := by
                    dsimp only [p_l]; rw [bb_bv32_xor1, hj_eq]
                  have hp_lt : p_l.toNat < 2 * s0.core.cur_vars := by
                    rw [hp_eq]; exact hbt.trl_lits_lt j (by omega)
                  have hpv_lt : (p_l >>> 1#32).toNat < c.max_vars := by
                    rw [bb_bv32_lshr1]; omega
                  have hpv_mrk : (p_l >>> 1#32).toNat < mrk1.length := by rw [hm1_len]; omega
                  have hent_res : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [p_l.toNat ^^^ 1, (st.core.trl[i1]?.getD 0#32).toNat ^^^ 1]) := by
                    refine backbone_resolve2 (bb_entails_comm2 hent2) ?_
                    simpa [p_l, bb_bv32_xor1, bb_xor1_xor1] using hent_z
                  c0_hsplit
                  · have hm1_pnz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                      rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some] at h0
                      exact (by c0_bound : (mrk1[(p_l >>> 1#32).toNat]'hpv_mrk).setWidth 32 ≠ 0#32)
                        ((bb_bv8_zext32_eq0 _).mpr h0)
                    have hj_eq_i1 : j = i1 := hbt.trl_vars_nodup j i1 (by omega) (by omega) (by
                      rw [← hp_eq, ← bb_bv32_lshr1]; exact (hm1_iff _ hpv_lt).mp hm1_pnz)
                    have hp_eq_i1 : (st.core.trl[i1]?.getD 0#32).toNat = p_l.toNat := by
                      rw [← hj_eq_i1, hp_eq]
                    have hent_uip :
                        (cnfOfClauses F_cur).EntailsClause (cnfClause [p_l.toNat ^^^ 1]) :=
                      backbone_collapse_eq (by rwa [hp_eq_i1] at hent_res)
                    bb_steps
                    exact hJbr (t - 1#64, p_l, ()) _ ⟨mrk1, hm1_len,
                      (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                      (fun _ => ⟨hp_lt, hent_uip⟩), hm⟩
                  · have hm1_pz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some]
                      exact (bb_bv8_zext32_eq0 _).mp (by c0_bound)
                    have hj_ne_i1 : j ≠ i1 := fun he => by
                      subst he
                      have hnz := (hm1_iff _ hpv_lt).mpr (by rw [bb_bv32_lshr1, hp_eq])
                      exact hnz hm1_pz
                    let mrk2 := mrk1.set (p_l >>> 1#32).toNat 1#8
                    have hm2_iff : ∀ v < c.max_vars, mrk2[v]?.getD 0#8 ≠ 0#8 ↔
                        v = (st.core.trl[j]?.getD 0#32).toNat / 2 ∨
                        v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := fun v hv => by
                      dsimp only [mrk2]
                      by_cases he : v = (p_l >>> 1#32).toNat
                      · subst he; rw [List.getElem?_set_self hpv_mrk, Option.getD_some]
                        exact ⟨fun _ => Or.inl (by rw [bb_bv32_lshr1, hp_eq]),
                          fun _ => by decide⟩
                      · rw [List.getElem?_set_ne (Ne.symm he), hm1_iff v hv]
                        exact ⟨Or.inr, fun ho => ho.elim
                          (fun h => absurd (by rw [bb_bv32_lshr1, hp_eq]; exact h) he) id⟩
                    have hsw_z : (BitVec.setWidth 64
                        (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat =
                        (z >>> 1#32).toNat := m6_zext32_toNat _
                    have hpv_c0 : (BitVec.setWidth 64
                        ((st.core.rsns[(BitVec.setWidth 64
                          (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat]'(by
                            rw [hsw_z]; exact hzv_rsn) &&& 0x7FFFFFFF#32 ^^^ 1#32) >>>
                          1#32)).toNat < (mrk_t.set (BitVec.setWidth 64
                        (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat 0#8).length := by
                      rw [List.length_set, m6_zext32_toNat]
                      change (BitVec.setWidth 64 (p_l >>> 1#32)).toNat < mrk_t.length
                      rw [m6_zext32_toNat, hmt_len]; exact hpv_lt
                    c0_hsteps
                    refine iht (t - 1#64, ()) _ (by dsimp only; omega)
                      ⟨mrk2, by simp [mrk2, hm1_len], by omega, by omega, ?_,
                       bb_fullMem_eq (by dsimp only [mrk2, mrk1])
                         (by assumption)⟩
                    rcases Nat.lt_or_gt_of_ne hj_ne_i1 with hji | hij
                    · exact ⟨j, i1, Nat.le_trans hs0_sav hj_ge, hji, by omega, by omega, hm2_iff,
                        by rwa [hp_eq] at hent_res⟩
                    · exact ⟨i1, j, hi1_ge, hij, hj_ge, by omega,
                        fun v hv => by rw [or_comm]; exact hm2_iff v hv,
                        bb_entails_comm2 (by rwa [hp_eq] at hent_res)⟩

end LeanQbe.T.Examples.Kissat.Proof.Backbone
