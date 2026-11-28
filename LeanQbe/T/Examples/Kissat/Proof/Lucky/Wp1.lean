/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat.Src.Lucky` Part 1 (`Wp1`)

Proves `full_lucky_scan_wp` and `full_lucky_late_m7_wp` (factored into small
`< 220`-line helpers) against canonical `Proof.Lucky.Spec` with zero legacy imports.
-/

set_option autoImplicit false

private theorem lk1_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem lk1_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem lk1_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "lk1_strip" : tactic =>
  `(tactic| first | apply lk1_strip_32_64 | apply lk1_strip_8_32 | apply lk1_strip_8_64)

local macro "lk1_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)

local elab "lk1_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local macro "lk1_steps" : tactic =>
  `(tactic| (
    (try lk1_unmdata)
    (repeat lk1_strip)
    c0_steps
    repeat (any_goals (lk1_strip; repeat lk1_strip); c0_steps)))

open Lean Elab Tactic in
local elab "lk1_to_group_step" : tactic => do
  for _ in [:500] do
    let mut progressed := false
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g'' ← g.change ty (checkDefEq := false)
        replaceMainGoal [g'']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push (← getMainGoal)
      else if ← LeanQbe.T.C0Step.stepOnce then
        progressed := true
        evalTactic (← `(tactic| all_goals (try (repeat lk1_strip))))
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push (← getMainGoal)
    setGoals out.toList
    if !progressed then break

local macro "lk1_to_group" : tactic =>
  `(tactic| ((try lk1_unmdata); (repeat lk1_strip); lk1_to_group_step))

open Lean Elab Tactic in
local elab "lk1_split" : tactic => do
  for _ in [:120] do
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step))
      break
    evalTactic (← `(tactic| all_goals (repeat lk1_strip)))
    if ← Lean.Elab.Tactic.tryTactic (evalTactic (← `(tactic| c0_step))) then
      evalTactic (← `(tactic| all_goals (repeat lk1_strip)))
    else
      break

local macro "lk1_call" hSpec:term : tactic =>
  `(tactic| (
    lk1_unmdata
    refine LeanQbe.T.wp_call_of_spec _ _ ($hSpec _ _ _ _ ?_)
    try c0_let_simp))

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Lucky
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

private theorem lk1_bv64_four : (4#64 : BitVec 64) = (4 : BitVec 64) := rfl
private theorem lk1_bv64_144 : (144#64 : BitVec 64) = (144 : BitVec 64) := rfl
private theorem lk1_bv64_160 : (160#64 : BitVec 64) = (160 : BitVec 64) := rfl
private theorem lk1_bv64_168 : (168#64 : BitVec 64) = (168 : BitVec 64) := rfl
private theorem lk1_bv64_768 : (768#64 : BitVec 64) = (768 : BitVec 64) := rfl

/-! ## 1. `full_lucky_scan_wp` -/

theorem full_lucky_scan_wp (Γ : Env)
    (hOrd : ∀ args m Q X, luckyOrdSpec args m Q X →
      Γ "full_lucky_ord_fid" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, PropSearch.Spec.propagateM6Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, m6HdrAnalyzeSpec args m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] args m Q X) :
    ∀ args m Q X, luckyScanSpec args m Q X →
      Func.wp Γ full_lucky_scan_body args m Q X := by
  rintro ⟨h, pol?, fwd?, ⟨⟩⟩ m Q X hs
  unfold luckyScanSpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, ⟨hsp, hcl0⟩, hm, hQ0⟩ := M6HdrContract.elim hs
  let hQ : ∀ r ext' s' m', s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r ext' s' m' hlen' hext' hr hfl h20 h02 h10 hm' =>
      hQ0 (r, ()) ext' s' m' hext' trivial hlen' ⟨hr, hfl, h20, h02, h10⟩ hm'
  unfold Func.wp full_lucky_scan_body
  rw [fullM6HdrMem_iff] at hm
  lk1_steps
  lk1_call hOrd
  dsimp only [luckyOrdSpec]
  refine FullContract.intro (w := ()) hsp.1.lengths trivial hm
    fun ⟨n_bv, ⟨⟩⟩ s0 m0 hlen0 hpost0 hm0 => ?_
  rcases hpost0 with ⟨hcore0, hn_le, hpres0⟩
  change n_bv.toNat ≤ s.core.cur_vars at hn_le
  have hceq0 : s0.core = s.core := hcore0
  have hsp0 : FullSparseInv c F0 s0 := by
    refine ⟨hsp.1.with_scratch hlen0 hcore0, ?_, ?_, ?_, ?_⟩
    · unfold FullLitMarksClear FullMrkZero; rw [hceq0]; exact hsp.2.1
    · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      rw [hceq0]; exact hsp.2.2.1
    · exact hsp.2.2.2.1.of_pres hpres0 (fun _ hr => by
        unfold fullArenaClauseRefs at hr ⊢; rw [hceq0]; exact hr)
    · rw [hceq0]; exact hsp.2.2.2.2
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hsp.1.lengths.core_ok.cur_vars_le
  dsimp only
  c0_hsteps_nogrp
  have hret_bt : ∀ r (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb → (r = 0#64 ∨ r = 2#64) →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm r, PUnit.unit)) mb := by
    intro r ext_b s_b mb hext_b hsb hfl_b hmb hr_or
    refine call_backtrack0_wp hBt hext_b hsb hfl_b (fullM6HdrMem_unfocus_full hmb)
      fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    lk1_steps
    (try rw [← fullM6HdrMem_iff] at hm')
    exact hQ r ext_b s' m' hlen' hext_b (by rcases hr_or with rfl | rfl <;> simp) hfl'
      (fun h => by rcases hr_or with rfl | rfl <;> cases h) (fun _ => ⟨hsp', hcl0'⟩)
      (fun _ => hsp'.2.2.2.1.2) hm'
  have hret_otfs_bt : ∀ F_cur (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullOtfsInvW c F0 F_cur s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb := by
    intro F_cur ext_b s_b mb hext_b hotfs hfl_b hmb
    refine call_backtrack0_otfs_ret2_wp hBt hext_b hotfs hfl_b (fullM6HdrMem_unfocus_full hmb)
      fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    lk1_steps
    (try rw [← fullM6HdrMem_iff] at hm')
    exact hQ 2#64 ext_b s' m' hlen' hext_b (Or.inr (Or.inl rfl)) hfl'
      (fun h => absurd h (by decide)) (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2) hm'
  refine wp_loop_group (ts := [i64])
    (fun rem (idx, _) ml => ∃ (extL : List (BitVec 64)) (st : FullState),
      rem = n_bv.toNat - idx.toNat ∧ idx.toNat ≤ n_bv.toNat ∧ M6HdrExtOk extL ∧
      st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
      st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c st ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) ml) ?_ ?_
  · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨extL, st, rfl, hidx_le, hextL, hcv_eq, hst, hfl, hml⟩
    have hcv_le := hst.1.lengths.core_ok.cur_vars_le
    dsimp [Blocks.get]
    simp only [wp_let, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat]
    rw [wp_jnz]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hult => ?_, fun _ => ?_⟩
    · have hidx_lt : idx.toNat < n_bv.toNat := by
        have h1 : BitVec.ult idx n_bv = true := hult
        rwa [BitVec.ult, decide_eq_true_eq] at h1
      have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
      refine wp_join_group (ts := [i64]) (fun (j_bv, _) mj =>
          mj = ml ∧ j_bv.toNat < n_bv.toNat) ?_ ?_
      · rintro Jj ⟨j_bv, ⟨⟩⟩ _ ⟨rfl, hj_lt⟩
        dsimp [Blocks.get]
        have hj_tr : j_bv.toNat < st.scratch.tarjan_reach.length := by
          rw [hst.1.lengths.scratch_ok.tarjan_reach_len]; omega
        c0_hsteps_nogrp
        refine wp_load_of (FullArenaTactics.c0_load_full_tarjan_reach hj_tr hml) ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ (ext' : List (BitVec 64)) (st' : FullState),
              M6HdrExtOk ext' ∧ st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨ext', st', hext', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]; lk1_steps
          exact ih (n_bv.toNat - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨ext', st', by simp [hidx1_nat], by omega, hext', hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          c0_hsplit
          · let v : BitVec 64 := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).setWidth 64
            have hv_lt : v.toNat < st.core.cur_vars := by
              have h1 : (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).toNat <
                  s.core.cur_vars % 2 ^ 64 := by assumption
              dsimp only [v]; simp only [BitVec.toNat_setWidth]
              have := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).isLt; rw [hcv_eq]; omega
            have hv_fl : v.toNat < st.core.flags.length := by
              have := hst.1.lengths.core_ok.flags_len; omega
            have hv2_vl : (v <<< 1#64).toNat < st.core.vals.length := by
              have := hst.1.lengths.core_ok.vals_len
              rw [lk_bv64_shl1_toNat (by omega)]; omega
            lk1_unmdata
            simp only [lk1_bv64_four, lk1_bv64_144, lk1_bv64_160, lk1_bv64_168, lk1_bv64_768]
            lk1_to_group
            · exact hret_bt 2#64 extL st _ hextL hst hfl hml (Or.inr rfl)
            · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hc
              have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                lk_bv64_sub1_toNat hfl_ne
              have hval0 : st.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                have h2v : (v <<< 1#64).toNat = 2 * v.toNat := lk_bv64_shl1_toNat (by omega)
                have h_eq : BitVec.signExtend 32 st.core.vals[2 * v.toNat % 2 ^ 64] = 0#32 := by
                  assumption
                have h_mod : 2 * v.toNat % 2 ^ 64 = 2 * v.toNat := by omega
                rw [lk_bv8_sext32_eq0_iff] at h_eq
                have hv2_lt : 2 * v.toNat < st.core.vals.length := by rw [← h2v]; exact hv2_vl
                have h_eq0 : st.core.vals[2 * v.toNat] = 0#8 := by simpa [h_mod] using h_eq
                simp [List.getElem?_eq_getElem hv2_lt, h_eq0]
              let st1 : FullState :=
                { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
              have hst1 : FullSparseInv c F0 st1 :=
                fullSparseInv_with_fuel hst (st.core.fuel - 1#64)
              have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
              refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                  (FullMem c st1 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) mlit ∧
                    lit.toNat / 2 = v.toNat) ?_ ?_
              · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
                dsimp [Blocks.get]
                obtain ⟨_, _, _, hnlvl_bv, _, _, _⟩ := decide_nlvl_ok hst1 hv_lt hval0
                have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                  have := hst1.1.lengths.core_ok.cur_vars_le; omega
                lk1_unmdata
                simp only [lk1_bv64_four, lk1_bv64_144, lk1_bv64_160, lk1_bv64_768]
                c0_steps!
                rw [hnlvl_bv, lk_bv64_trunc32_ofNat hte32_1] at *
                refine call_assign_prop_decide_wp (R := R) hAssign hProp hcfg hextL hst1 hfl1
                  hv_lt hval0 hlit_v (fullM6HdrMem_unfocus_full (by assumption))
                  fun r1 F_cur1 ext1 s_asn1 s_p1 mp1 hext1 hlen1 hsp1 hw1 hcl1 hcv1
                    hfl_p1 hr1 hcf1 htr1 hte1 htrl1 hlvl1 hmp1 => ?_
                rw [fullM6HdrMem_iff] at hmp1
                lk1_unmdata; lk1_to_group
                · exact hret_bt 2#64 ext1 s_p1 mp1 hext1 hsp1 hfl_p1 hmp1 (Or.inr rfl)
                · refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                      ∃ (ext_a : List (BitVec 64)) (s_a : FullState),
                        M6HdrExtOk ext_a ∧ s_a.core.cur_vars = s.core.cur_vars ∧
                        FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c s_a ⋆ (array64 (c.hdr - 2304) ext_a ⋆ R)) m_a) ?_ ?_
                  · rintro Jafter2 ⟨_, ⟨⟩⟩ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                    dsimp [Blocks.get]; lk1_steps
                    exact hJnext PUnit.unit m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                  · intro Jafter2 hJafter2
                    lk1_unmdata; lk1_to_group
                    · have hr1_eq : r1 = 1#64 := by assumption
                      refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                          ∃ (ext_a : List (BitVec 64)) (s_a : FullState),
                            M6HdrExtOk ext_a ∧ s_a.core.cur_vars = s.core.cur_vars ∧
                            FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullMem c s_a ⋆ (array64 (c.hdr - 2304) ext_a ⋆ R)) m_a) ?_ ?_
                      · rintro Jbt ⟨_, ⟨⟩⟩ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                        dsimp [Blocks.get]; lk1_steps
                        exact hJafter2 _ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                      · intro Jbt hJbt
                        lk1_unmdata; simp only [lk1_bv64_168]; lk1_to_group
                        · have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le; have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_mod : 1 < s_p1.core.cur_level % 2 ^ 64 := by simpa using hc
                          have hcl_gt1 : 1 < s_p1.core.cur_level := by omega
                          have hcl_bv : (BitVec.ofNat 64 s_p1.core.cur_level - 1#64).toNat =
                              st1.core.cur_level := by rw [hcl1]; bv_omega
                          lk1_call hBt
                          refine ⟨c, s_p1, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlen1, hcl_lt64,
                            fun _ => by
                              have := hlen1.core_ok.cur_vars_le; rw [hcl_bv, hcl1] at *; omega,
                            hw1.trail_lits_lt, hmp1, ?_⟩
                          dsimp only
                          intro vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b mb
                            hlen_b _ _ _ hps_b _ _ hbv_b hwt_b _ hmb
                          let s_b : FullState :=
                            { core := { s_p1.core with
                                vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
                                trail_pos := tp_b, trail_end := te_b, propagated := prop_b,
                                cur_level := cl_b, unassigned := unass_b }
                              scratch := sc_b }
                          have hsp_b : FullSparseInv c F0 s_b :=
                            fullSparseInv_of_fullBacktrack hsp1 hlen_b
                              (hwt_b F0 F_cur1 hw1 (by rw [hcl_bv, hcl1]; omega))
                              rfl rfl rfl rfl rfl hps_b.1.1 hps_b.1.2
                          have hv_lt_b : v.toNat < s_b.core.cur_vars := by
                            change v.toNat < s_p1.core.cur_vars; rw [hcv1]; exact hv_lt
                          have hval0_b : s_b.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                            refine scan_backtrack_unassigned hlit_v hte1 htrl1 hlvl1 ?_ htr1
                              (by rw [hcv1]; exact Nat.mul_lt_mul_of_pos_left hv_lt (by decide)) ?_
                            · change st1.core.cur_level + 1 < 2 ^ 32; omega
                            · intro l hl
                              have := (hbv_b ⟨F0, F_cur1, Or.inl hw1⟩).1 l hl
                              simpa [hcl_bv] using this
                          lk1_unmdata; c0_step; (repeat lk1_strip); c0_step
                          · exact hret_bt 2#64 ext1 s_b mb hext1 hsp_b hfl_p1 hmb (Or.inr rfl)
                          · have hfl_ne_b : s_b.core.fuel ≠ 0#64 := hc
                            have hfl_sub_b :
                                (s_b.core.fuel - 1#64).toNat = s_b.core.fuel.toNat - 1 :=
                              lk_bv64_sub1_toNat hfl_ne_b
                            let s_b1 : FullState :=
                              { s_b with core := { s_b.core with fuel := s_b.core.fuel - 1#64 } }
                            have hsb1 : FullSparseInv c F0 s_b1 :=
                              fullSparseInv_with_fuel hsp_b (s_b.core.fuel - 1#64)
                            have hfl_b1 : s_b1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change (s_b.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                              rw [hfl_sub_b]
                              have : s_b.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p1; omega
                            obtain ⟨_, _, _, hnlvl_b1, _, _, _⟩ :=
                              decide_nlvl_ok hsb1 hv_lt_b hval0_b
                            have hte32_b1 : s_b1.core.trail_end < 2 ^ 32 := by
                              have := hsb1.1.lengths.core_ok.cur_vars_le; omega
                            lk1_unmdata; c0_steps!
                            rw [hnlvl_b1, lk_bv64_trunc32_ofNat hte32_b1] at *
                            refine call_assign_prop_decide_wp (R := R) hAssign hProp hcfg hext1
                              hsb1 hfl_b1 hv_lt_b hval0_b
                              ((lk_bv32_xor1_div2 lit).trans hlit_v)
                              (fullM6HdrMem_unfocus_full (by assumption))
                              fun r2 F_cur2 ext2 s_asn2 s_p2 mp2 hext2 hlen2 hsp2 hw2 hcl2 hcv2
                                hfl_p2 hr2 hcf2 htr2 hte2 htrl2 hlvl2 hmp2 => ?_
                            rw [fullM6HdrMem_iff] at hmp2
                            lk1_unmdata; lk1_to_group
                            · exact hret_bt 2#64 ext2 s_p2 mp2 hext2 hsp2 hfl_p2 hmp2 (Or.inr rfl)
                            · exact hret_bt 0#64 ext2 s_p2 mp2 hext2 hsp2 hfl_p2 hmp2 (Or.inl rfl)
                            · lk1_steps
                              exact hJbt _ mp2 ⟨ext2, s_p2, hext2, by
                                change s_p2.core.cur_vars = s.core.cur_vars; rw [hcv2]
                                change s_b.core.cur_vars = s.core.cur_vars
                                change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq,
                                hsp2, hfl_p2, hmp2⟩
                        · have hcl_mod : s_p1.core.cur_level % 2 ^ 64 ≤ 1 := by simpa using hc
                          have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le; have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_eq1 : s_p1.core.cur_level = 1 := by omega
                          refine scan_ana_branch_wp hProp hAna hcfg hext1 hsp1 hw1 hcl_eq1
                            (hcf1 hr1_eq) hfl_p1 (fullM6HdrMem_unfocus_full hmp1)
                            (fun ext_b s_b mb hext_b hsb hfl_b hmb =>
                              hret_bt 2#64 ext_b s_b mb hext_b hsb hfl_b
                                ((fullM6HdrMem_iff ..).mp hmb) (Or.inr rfl))
                            (fun ext_b s_b mb hext_b hotfs hfl_b hmb =>
                              hret_otfs_bt F_cur1 ext_b s_b mb hext_b hotfs hfl_b
                                ((fullM6HdrMem_iff ..).mp hmb))
                            (fun ext_u s_u mu hext_u hlen_u hfl_u huns hmu =>
                              hQ 20#64 ext_u s_u mu hlen_u hext_u (Or.inr (Or.inr (Or.inr rfl)))
                                hfl_u (fun _ => huns) (fun h => by rcases h with h | h <;> cases h)
                                (fun h => by cases h) hmu)
                            (fun ext_o s_o mo hext_o hcv_o hsp_o hfl_o hmo =>
                              hJbt _ mo ⟨ext_o, s_o, hext_o, by
                                change s_o.core.cur_vars = s.core.cur_vars; rw [hcv_o]
                                change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq,
                                hsp_o, hfl_o, (fullM6HdrMem_iff ..).mp hmo⟩)
                    · lk1_steps
                      exact hJafter2 _ mp1 ⟨ext1, s_p1, hext1, by
                        change s_p1.core.cur_vars = s.core.cur_vars; rw [hcv1]; exact hcv_eq,
                        hsp1, hfl_p1, hmp1⟩
              · intro Jlit hJlit; lk1_steps
                · have hl : (BitVec.setWidth 32 (v <<< 1)).toNat = 2 * v.toNat := by bv_omega
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
                · have h_eq1 : (v <<< 1) = (v <<< 1#64) := rfl
                  have hl : (BitVec.setWidth 32 (v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
                    rw [h_eq1]; exact lk_bv32_shl1_or1_trunc32_toNat (by omega)
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
            · exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
            · exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
          · c0_hsteps; exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
      · intro Jj hJj; lk1_steps
        · exact hJj _ ml ⟨rfl, hidx_lt⟩
        · have hsub_nat : (n_bv - 1#64 - idx).toNat = n_bv.toNat - 1 - idx.toNat := by bv_omega
          exact hJj _ ml ⟨rfl, by rw [hsub_nat]; omega⟩
    · lk1_steps
      exact hQ 10#64 extL st ml hst.1.lengths hextL (Or.inr (Or.inr (Or.inl rfl))) hfl
        (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
        (fun _ => hst.2.2.2.1.2) ((fullM6HdrMem_iff ..).mpr hml)
  · intro Jloop hJloop; lk1_steps
    exact hJloop n_bv.toNat (0#64, PUnit.unit) m0
      ⟨ext, s0, by simp, Nat.zero_le _, hext, hceq0 ▸ rfl, hsp0,
        by rw [hceq0]; exact Nat.le_refl _, hm0⟩

/-! ## 2. `full_lucky_late_m7_wp` -/

private theorem lk1_bt0_wp {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} {k : Expr Val Cont [i64]}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hK : ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel →
      FullM6HdrInv c F0 ext s' → s'.core.cur_level = 0 →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var c.hdr, Arg.imm 0#64, ()) (fun _ => k)) m := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hinv.sparse.1.lengths.core_ok.trail_end_le
    have := hinv.sparse.1.lengths.core_ok.cur_vars_le; omega
  have h0_toNat : (0#64 : BitVec 64).toNat = 0 := rfl
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  lk1_call hBt
  refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.1.lengths, hcl_lt,
    (fun hpos => by
      have := hw.cur_level_le; have := hinv.sparse.1.lengths.core_ok.trail_end_le
      have := hinv.sparse.1.lengths.core_ok.cur_vars_le; rw [h0_toNat] at hpos; omega),
    hw.trail_lits_lt, hmf, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s'
    hlen' _ _ hcl' hps _ _ _ hwt _ hm'
  have hsp' : FullSparseInv c F0 s' :=
    fullSparseInv_of_fullBacktrack hinv.sparse hlen' (hwt F0 F_cur hw (Nat.zero_le _))
      rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  have hcl0 : s'.core.cur_level = 0 := by dsimp only [s']; simpa [h0_toNat] using hcl'
  exact hK s' m' hlen' rfl (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hcl0
    (fullM6HdrMem_unfocus_full hm')

local macro "lk1_hsteps_ns_run" : tactic =>
  `(tactic| (
    (try lk1_unmdata)
    (repeat lk1_strip)
    lk1_hsteps_ns
    repeat (any_goals (lk1_strip; repeat lk1_strip); lk1_hsteps_ns)))

local macro "lk1_late_scan_chain"
    c:ident F0:ident s:ident R:ident
    hScan:ident hinv3:ident hcl2_0:ident hfl2:ident hQ:ident : tactic =>
  `(tactic| (
    let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
      ∃ (extr : List (BitVec 64)) (sr : FullState), sr.LengthsOk $c ∧ M6HdrExtOk extr ∧
        (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        sr.core.fuel.toNat ≤ ($s).core.fuel.toNat ∧ (r = 20#64 → ($F0).Unsat) ∧
        (r = 0#64 ∨ r = 2#64 → FullM6HdrInv $c $F0 extr sr ∧ sr.core.cur_level = 0) ∧
        (r = 10#64 → sr.scratch.extend_len ≤ ($c).extend_cap) ∧ (FullM6HdrMem $c extr sr ⋆ $R) mr
    lk1_hsteps_ns_run; lk1_call $hScan
    dsimp only [luckyScanSpec]
    refine M6HdrContract.intro ($hinv3).cfgOk ($hinv3).extOk ($hinv3).sparse.1.lengths
      ⟨($hinv3).sparse, $hcl2_0⟩ (fullM6HdrMem_unfocus_full (by assumption)) ?_
    rintro ⟨r1, ⟨⟩⟩ extr1 s1_ m1_ hext1 _ hlen1 ⟨hr1, hfl1, huns1, h02_1, h10_1⟩ hm1_
    lk1_hsteps_ns_run
    refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
    · rintro _ ⟨rA, ⟨⟩⟩ mA ⟨extA, srA, hlenA, hextA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
      rw [Blocks.get_here]; lk1_hsteps_ns_run
      refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
      · rintro _ ⟨rB, ⟨⟩⟩ mB ⟨extB, srB, hlenB, hextB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
        rw [Blocks.get_here]; lk1_hsteps_ns_run
        refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
        · rintro _ ⟨rF, ⟨⟩⟩ mF ⟨extF, srF, hlenF, hextF, hrF, hflF, hunsF, h02F, h10F, hmF⟩
          rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hmF fun _ => ?_; lk1_steps
          let sr' : FullState := { srF with core := { srF.core with probing := 0#64 } }
          have hlen' : sr'.LengthsOk $c :=
            ⟨{ hlenF.core_ok with vals_len := hlenF.core_ok.vals_len }, hlenF.scratch_ok⟩
          exact $hQ rF extF sr' _ hlen' hextF hrF hflF rfl hunsF
            (fun h => let ⟨hi, hcl⟩ := h02F h
              ⟨FullM6HdrInv.mk_inv hi.cfgOk hi.extOk (fullSparseInv_with_probing hi.sparse 0#64),
                hcl⟩)
            h10F (fullM6HdrMem_unfocus_full (by assumption))
        · intro _ hJsF; lk1_hsteps_ns_run; lk1_split
          · have hrb_eq : rB = 0#64 := by simpa using ‹_›
            obtain ⟨hinvB, hclB⟩ := h02B (Or.inl hrb_eq)
            lk1_hsteps_ns_run; lk1_call $hScan
            dsimp only [luckyScanSpec]
            refine M6HdrContract.intro hinvB.cfgOk hinvB.extOk hinvB.sparse.1.lengths
              ⟨hinvB.sparse, hclB⟩ hmB ?_
            rintro ⟨r3, ⟨⟩⟩ ext3 sr3 m3' hext3 _ hlen3 ⟨hr3, hfl3', huns3, h02_3, h10_3⟩ hm3'
            exact hJsF (r3, ()) m3' ⟨ext3, sr3, hlen3, hext3, hr3, Nat.le_trans hfl3' hflB, huns3,
              (fun h => let ⟨hi, hc⟩ := h02_3 h
                ⟨FullM6HdrInv.mk_inv hinvB.cfgOk hext3 hi, hc⟩),
              h10_3, hm3'⟩
          · lk1_steps
            exact hJsF (rB, ()) mB ⟨extB, srB, hlenB, hextB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
      · intro _ hJsB; lk1_hsteps_ns_run; lk1_split
        · have hra_eq : rA = 0#64 := by simpa using ‹_›
          obtain ⟨hinvA, hclA⟩ := h02A (Or.inl hra_eq)
          lk1_hsteps_ns_run; lk1_call $hScan
          dsimp only [luckyScanSpec]
          refine M6HdrContract.intro hinvA.cfgOk hinvA.extOk hinvA.sparse.1.lengths
            ⟨hinvA.sparse, hclA⟩ hmA ?_
          rintro ⟨r2, ⟨⟩⟩ ext2 sr2 m2 hext2 _ hlen2 ⟨hr2, hfl2', huns2, h02_2, h10_2⟩ hm2
          exact hJsB (r2, ()) m2 ⟨ext2, sr2, hlen2, hext2, hr2, Nat.le_trans hfl2' hflA, huns2,
            (fun h => let ⟨hi, hc⟩ := h02_2 h
              ⟨FullM6HdrInv.mk_inv hinvA.cfgOk hext2 hi, hc⟩),
            h10_2, hm2⟩
        · lk1_steps
          exact hJsB (rA, ()) mA ⟨extA, srA, hlenA, hextA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
    · intro _ hJsA; lk1_hsteps_ns_run; lk1_split
      · have hr1_eq : r1 = 0#64 := by simpa using ‹_›
        obtain ⟨hinv1_, hcl1_⟩ := h02_1 (Or.inl hr1_eq)
        have hinv1_m : FullM6HdrInv $c $F0 extr1 s1_ :=
          FullM6HdrInv.mk_inv ($hinv3).cfgOk hext1 hinv1_
        lk1_hsteps_ns_run; lk1_call $hScan
        dsimp only [luckyScanSpec]
        refine M6HdrContract.intro hinv1_m.cfgOk hinv1_m.extOk hinv1_m.sparse.1.lengths
          ⟨hinv1_m.sparse, hcl1_⟩ hm1_ ?_
        rintro ⟨r1b, ⟨⟩⟩ ext1b sr1b m1b hext1b _ hlen1b
          ⟨hr1b, hfl1b, huns1b, h02_1b, h10_1b⟩ hm1b
        exact hJsA (r1b, ()) m1b ⟨ext1b, sr1b, hlen1b, hext1b, hr1b,
          Nat.le_trans hfl1b (Nat.le_trans hfl1 $hfl2), huns1b,
          (fun h => let ⟨hi, hc⟩ := h02_1b h
            ⟨FullM6HdrInv.mk_inv hinv1_m.cfgOk hext1b hi, hc⟩),
          h10_1b, hm1b⟩
      · lk1_steps
        exact hJsA (r1, ()) m1_ ⟨extr1, s1_, hlen1, hext1, hr1, Nat.le_trans hfl1 $hfl2, huns1,
          (fun h => let ⟨hi, hc⟩ := h02_1 h
            ⟨FullM6HdrInv.mk_inv ($hinv3).cfgOk hext1 hi, hc⟩),
          h10_1, hm1_⟩))

theorem full_lucky_late_m7_wp (Γ : Env)
    (hPolar : ∀ args m Q X, luckyPolarSpec args m Q X →
      Γ "full_lucky_polar_m7" [i64] [i64] args m Q X)
    (hScan : ∀ args m Q X, luckyScanSpec args m Q X →
      Γ "full_lucky_scan" [i64, .bool, .bool] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, PropSearch.Spec.propagateM6Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ a m Q X, luckySpec a m Q X →
      Func.wp Γ full_lucky_late_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold luckySpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, hsp, hm, hQ0⟩ := M6HdrContract.elim hs
  have hinv : FullM6HdrInv c F0 ext s := ⟨hcfg, hext, hsp⟩
  let hQ : ∀ r ext' s' m', s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.probing = 0#64 → (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r ext' s' m' hlen' hext' hr hfl hpr h20 h02 h10 hm' =>
      hQ0 (r, ()) ext' s' m' hext' trivial hlen'
        ⟨hr, hfl, hpr, h20, (fun h02' => let ⟨hi, hc⟩ := h02 h02'; ⟨hi.sparse, hc⟩), h10⟩ hm'
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_lucky_late_m7_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  lk1_hsteps_ns_run; lk1_split
  · have hunsat : F0.Unsat := hinv.sparse.inconsistent_unsat (by simpa using ‹_›)
    lk1_steps
    let s' : FullState := { s with core := { s.core with probing := 0#64 } }
    have hsp' := fullSparseInv_with_probing hinv.sparse 0#64
    exact hQ 20#64 ext s' _ hsp'.1.lengths hinv.extOk (Or.inr (Or.inr (Or.inr rfl))) (Nat.le_refl _)
      rfl (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
      (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
  · lk1_hsteps_ns_run
    refine wp_join_group (ts := []) (fun _ m1 => ∃ s1 : FullState,
      FullM6HdrInv c F0 ext s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
    · rintro J1 ⟨⟩ m1 ⟨s1, hinv1, hcl1_0, hfl1, hm1⟩
      rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hm1 fun _ => ?_; lk1_hsteps_ns_run
      refine wp_join_group (ts := []) (fun _ m2 => ∃ ext2 s2,
        FullM6HdrInv c F0 ext2 s2 ∧ s2.core.cur_level = 0 ∧
        s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2) ?_ ?_
      · rintro J2 ⟨⟩ m2 ⟨ext2, s2, hinv2, hcl2_0, hfl2, hm2⟩
        rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hm2 fun _ => ?_; lk1_steps
        let s3 : FullState := { s2 with core := { s2.core with probing := 1#64 } }
        have hinv3 := FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk
          (fullSparseInv_with_probing hinv2.sparse 1#64)
        lk1_call hPolar
        dsimp only [luckyPolarSpec]
        refine FullContract.intro hinv3.sparse.1.lengths hinv3.sparse.1 (by assumption) ?_
        rintro ⟨pol, ⟨⟩⟩ s3' m3' _ ⟨hs3_eq, hpol⟩ hm3'
        subst s3'
        lk1_hsteps_ns_run; lk1_split
        · lk1_hsteps_ns_run
          refine wp_loop_inv (ts := [i64]) (fun (idx, ()) ml => ∃ extl st,
            idx.toNat ≤ s3.core.cur_vars ∧ st.core.cur_vars = s3.core.cur_vars ∧
            FullM6HdrInv c F0 extl st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c extl st ⋆ R) ml) (fun (idx, ()) _ => s3.core.cur_vars - idx.toNat) ?_ ?_
          · intro Jloop hJloop; lk1_steps; exact hJloop (0#64, ()) _
              ⟨ext2, s3, Nat.zero_le _, rfl, hinv3, hfl2, fullM6HdrMem_unfocus_full (by assumption)⟩
          · rintro Jloop ⟨idx, ⟨⟩⟩ ml ⟨extl, st, hidx_le, hcv_eq, hinvl, hfl, hml⟩ hJloop
            rw [Blocks.get_here]
            have hcl_ok := hinvl.sparse.1.lengths.core_ok; have hcv_st_le := hcl_ok.cur_vars_le
            refine wp_m6Hdr_focus_frame hml fun _ => ?_; lk1_hsteps_ns_run; lk1_split
            · have hidx_lt : idx.toNat < st.core.cur_vars := by
                have hlt : idx.toNat < st.core.cur_vars % 2 ^ 64 := by simpa [BitVec.ult] using ‹_›
                rw [Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
              have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
              have hidx_fl : idx.toNat < st.core.flags.length := by rw [hcl_ok.flags_len]; omega
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat := lk_bv64_shl1_toNat (by omega)
              have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
                rw [h2v, hcl_ok.vals_len]; omega
              lk1_hsteps_ns_run
              refine wp_join_group (ts := []) (fun _ mn =>
                ∃ ext' st', st'.core.cur_vars = s3.core.cur_vars ∧ FullM6HdrInv c F0 ext' st' ∧
                  st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext' st' ⋆ R) mn) ?_ ?_
              · rintro Jnext ⟨⟩ mn ⟨ext', st', hcv', hinv', hfl', hmn⟩
                rw [Blocks.get_here]; lk1_steps
                exact hJloop (idx + 1#64, ()) mn (by dsimp only; rw [hidx1_nat]; omega)
                  ⟨ext', st', by rw [hidx1_nat]; omega, hcv', hinv', hfl', hmn⟩
              · intro Jnext hJnext; lk1_hsteps_ns_run; lk1_split
                · lk1_hsteps_ns_run; lk1_split
                  · have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
                      rw [← h2v, List.getElem?_eq_getElem hidx2_vl, Option.getD_some]
                      exact (lk_bv8_sext32_eq0_iff _).mp (by simpa using ‹_›)
                    lk1_hsteps_ns_run; lk1_split
                    · lk1_steps
                      refine lk1_bt0_wp hBt hinvl (fullM6HdrMem_unfocus_full (by assumption))
                        fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                      refine wp_m6Hdr_focus_frame hmb fun _ => ?_; lk1_steps
                      let s' : FullState := { s_bt with core := { s_bt.core with probing := 0#64 } }
                      have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                      have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl_b]; exact hfl
                      exact hQ 2#64 extl s' _ hsp'.1.lengths hinv_b.extOk (Or.inr (Or.inl rfl)) hfl'
                        rfl (fun h => by cases h)
                        (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hinv_b.extOk hsp', hcl0_b⟩)
                        (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                    · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using ‹_›
                      have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                        lk_bv64_sub1_toNat hfl_ne
                      let st1 : FullState :=
                        { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
                      have hsp1 := fullSparseInv_with_fuel hinvl.sparse (st.core.fuel - 1#64)
                      have hinv1_st := FullM6HdrInv.mk_inv hinvl.cfgOk hinvl.extOk hsp1
                      have hfl1_le : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
                      have hph1_len : idx.toNat < st1.scratch.phases.length := by
                        rw [hsp1.1.lengths.scratch_ok.phases_len]; omega
                      lk1_hsteps_ns_run
                      refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                        (FullM6HdrMem c extl st1 ⋆ R) mlit ∧
                          (lit.toNat = 2 * idx.toNat ∨ lit.toNat = 2 * idx.toNat + 1)) ?_ ?_
                      · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_eq⟩
                        rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hmlit fun _ => ?_
                        obtain ⟨_, _, _, hnlvl_bv, _, _, _⟩ := decide_nlvl_ok hsp1 hidx_lt hval0
                        have hte32_1 : st1.core.trail_end < 2 ^ 32 :=
                          Nat.lt_of_le_of_lt (Nat.le_trans hsp1.1.lengths.core_ok.trail_end_le
                            hsp1.1.lengths.core_ok.cur_vars_le) (by omega)
                        lk1_hsteps_ns_run; lk1_split
                        · lk1_steps
                          refine lk1_bt0_wp hBt hinv1_st hmlit
                            fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                          refine wp_m6Hdr_focus_frame hmb fun _ => ?_; lk1_steps
                          let s' : FullState :=
                            { s_bt with core := { s_bt.core with probing := 0#64 } }
                          have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                          have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                            rw [hfl_b]; exact hfl1_le
                          exact hQ 0#64 extl s' _ hsp'.1.lengths hinv_b.extOk (Or.inl rfl) hfl' rfl
                            (fun h => by cases h)
                            (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hinv_b.extOk hsp', hcl0_b⟩)
                            (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                        · have hlit_v : lit.toNat / 2 = idx.toNat := by omega
                          lk1_unmdata
                          (try simp only [lk1_bv64_four, lk1_bv64_144, lk1_bv64_160, lk1_bv64_768])
                          c0_steps!
                          (try rw [lk_bv64_trunc32_ofNat hte32_1] at *)
                          refine call_assign_prop_decide_wp (R := R) hAssign hProp hinvl.cfgOk
                            hinvl.extOk hsp1 hfl1_le hidx_lt hval0 hlit_v
                            (fullM6HdrMem_unfocus_full (by
                              have h1 : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat =
                                  st1.core.cur_level + 1 := hnlvl_bv
                              have h2 :
                                  (BitVec.ofNat 64 st1.core.cur_level + (1 : BitVec 64)).toNat =
                                    st1.core.cur_level + 1 := hnlvl_bv
                              have hm' := hm
                              try rw [h1] at hm'
                              try rw [h2] at hm'
                              try rw [lk_bv64_trunc32_ofNat hte32_1] at hm'
                              exact hm'))
                            fun rp _ extp _ s_p mp hextp hlenp hspp _ _ hcvp hfl_p
                              _ _ _ _ _ _ hmp => ?_
                          have hinv_p := FullM6HdrInv.mk_inv hinvl.cfgOk hextp hspp
                          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p
                          have hcv_p : s_p.core.cur_vars = s3.core.cur_vars := by
                            change s_p.core.cur_vars = _ at hcvp; rw [hcvp]; exact hcv_eq
                          refine wp_m6Hdr_focus_frame hmp fun _ => ?_; lk1_hsteps_ns_run; lk1_split
                          · lk1_steps
                            refine lk1_bt0_wp hBt hinv_p hmp
                              fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                            refine wp_m6Hdr_focus_frame hmb fun _ => ?_; lk1_steps
                            let s' : FullState :=
                              { s_bt with core := { s_bt.core with probing := 0#64 } }
                            have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                            have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                              rw [hfl_b]; exact hfl_p'
                            exact hQ 2#64 extp s' _ hsp'.1.lengths hextp (Or.inr (Or.inl rfl)) hfl'
                              rfl (fun h => by cases h)
                              (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hextp hsp', hcl0_b⟩)
                              (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                          · lk1_hsteps_ns_run; lk1_split
                            · lk1_steps
                              refine lk1_bt0_wp hBt hinv_p hmp
                                fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                              refine wp_m6Hdr_focus_frame hmb fun _ => ?_; lk1_steps
                              let s' : FullState :=
                                { s_bt with core := { s_bt.core with probing := 0#64 } }
                              have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                              have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                rw [hfl_b]; exact hfl_p'
                              exact hQ 0#64 extp s' _ hsp'.1.lengths hextp (Or.inl rfl) hfl' rfl
                                (fun h => by cases h)
                                (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hextp hsp', hcl0_b⟩)
                                (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                            · lk1_steps; exact hJnext () mp ⟨extp, s_p, hcv_p, hinv_p, hfl_p', hmp⟩
                      · intro Jlit hJlit; lk1_hsteps_ns_run; lk1_split
                        · lk1_steps
                          exact hJlit (_, ()) _ ⟨fullM6HdrMem_unfocus_full (by assumption),
                            Or.inl (lk_bv32_shl1_trunc32_toNat (by omega))⟩
                        · lk1_steps
                          exact hJlit (_, ()) _ ⟨fullM6HdrMem_unfocus_full (by assumption),
                            Or.inr (lk_bv32_shl1_or1_trunc32_toNat (by omega))⟩
                  · lk1_steps; exact hJnext () ml ⟨extl, st, hcv_eq, hinvl, hfl, hml⟩
                · lk1_steps; exact hJnext () ml ⟨extl, st, hcv_eq, hinvl, hfl, hml⟩
            · lk1_steps
              let st' : FullState := { st with core := { st.core with probing := 0#64 } }
              have hsp' := fullSparseInv_with_probing hinvl.sparse 0#64
              exact hQ 10#64 extl st' _ hsp'.1.lengths hinvl.extOk (Or.inr (Or.inr (Or.inl rfl)))
                hfl rfl (fun h => absurd h (by decide))
                (fun h => by rcases h with h | h <;> cases h)
                (fun _ => hsp'.2.2.2.1.2) (fullM6HdrMem_unfocus_full (by assumption))
        · lk1_late_scan_chain c F0 s R hScan hinv3 hcl2_0 hfl2 hQ
      · intro J2 hJ2; lk1_hsteps_ns_run; lk1_split
        · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
          lk1_call hProp
          refine ⟨c, F0, F_cur1, ext, s1, R, rfl, hinv1.cfgOk, hinv1.extOk,
            hinv1.sparse.1.lengths, hw1, hinv1.sparse.2.2.2.2, hm1, ?_⟩
          dsimp only
          intro pr0 ext_p vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena'
            wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc_p m_p
            hext_p _ hlen_p hw_p htr_p _ hperm_p hsc_p _ _ _ _ hfl_p hr_or _ h1_p _ _ hm_p
          let s_p : FullState :=
            { core := { s1.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
                wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
              scratch := sc_p }
          have hll_p : s_p.scratch.last_learned = s1.scratch.last_learned := hsc_p.1.1
          have hext_l_p : s_p.scratch.extend_len = s1.scratch.extend_len := hsc_p.1.2
          have hsp_p := fullSparseInv_of_fullPropagate hinv1.sparse hlen_p hw_p hperm_p
            rfl rfl rfl hll_p hext_l_p
          have hinv_p := FullM6HdrInv.mk_inv hinv1.cfgOk hext_p hsp_p
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl1
          refine wp_m6Hdr_focus_frame hm_p fun _ => ?_; lk1_hsteps_ns_run; lk1_split
          · obtain ⟨_, _, hconf⟩ := h1_p (by simpa using ‹_›)
            have hcl_p : s_p.core.cur_level = 0 := hcl1_0
            have hunsat : F0.Unsat := level0_unsat_of_conflict_okW hw_p hcl_p hconf
            lk1_steps
            let s' : FullState :=
              { s_p with core := { s_p.core with inconsistent := 1#64, probing := 0#64 } }
            have hlen' : s'.LengthsOk c :=
              ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len }, hlen_p.scratch_ok⟩
            exact hQ 20#64 ext_p s' _ hlen' hext_p (Or.inr (Or.inr (Or.inr rfl))) hfl_p' rfl
              (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
              (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
          · lk1_hsteps_ns_run; lk1_split
            · lk1_steps
              let s' : FullState := { s_p with core := { s_p.core with probing := 0#64 } }
              have hsp' := fullSparseInv_with_probing hsp_p 0#64
              exact hQ 2#64 ext_p s' _ hsp'.1.lengths hext_p (Or.inr (Or.inl rfl)) hfl_p' rfl
                (fun h => by cases h)
                (fun _ => ⟨FullM6HdrInv.mk_inv hinv1.cfgOk hext_p hsp', hcl1_0⟩)
                (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
            · lk1_steps; exact hJ2 () m_p ⟨ext_p, s_p, hinv_p, hcl1_0, hfl_p', hm_p⟩
        · lk1_steps; exact hJ2 () m1 ⟨ext, s1, hinv1, hcl1_0, hfl1, hm1⟩
    · intro J1 hJ1; lk1_hsteps_ns_run; lk1_split
      · refine lk1_bt0_wp hBt hinv hm fun s1 m1 _ hfl1 hinv1 hcl1 hm1 => ?_
        exact hJ1 () m1 ⟨s1, hinv1, hcl1, by rw [hfl1]; exact Nat.le_refl _, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have := hinv.sparse.1.witness.choose_spec.cur_level_le
          have := hinv.sparse.1.lengths.core_ok.trail_end_le
          have := hinv.sparse.1.lengths.core_ok.cur_vars_le
          have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := ‹_›
          rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
        exact hJ1 () m ⟨s, hinv, hcl0, Nat.le_refl _, hm⟩

end LeanQbe.T.Examples.Kissat.Proof.Lucky
