/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce0
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce1
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce2
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Kissat 1-UIP Top-Level WP (`Proof.Deduce.WpDeduceTop`)

Proves `full_deduce_1uip_m6_hdr_loop_wp` over `WpDeduce2` (`deduce_seed_wp`,
`deduce_seed_unsat_or_ret0_wp`, `deduce_clear_ret0_wp`, `deduce_hdr_clear_wp`)
parameterized by `DeduceLoopRsnStep` (matching `WpDeduce3a.deduce_loop_rsn_wp`)
(`public section`, `0` legacy imports, `0` `import-all`, `0` `expose`-attrs on theorems/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
open scoped FullArenaTactics DeduceTactics
open Kraken.Bedrock2.Test

local elab "d_hsteps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "d_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

/-! ## 1. Loop State Invariant, Skip Step & 1-UIP Exit WP -/

private def DeduceLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut0 : Nat) (s0 : FullState) (R : Mem 64 → Prop)
    (ys : Tup Val [i64, i64, i64]) (m : Mem 64) : Prop :=
  ∃ (cut_cur idx : Nat) (ext_cur : List (BitVec 64)) (s_cur : FullState),
    ys.1 = BitVec.ofNat 64 s_cur.core.tmp_cnt ∧
    ys.2.1 = BitVec.ofNat 64 idx ∧
    cut_cur ≤ s_cur.core.trail_end ∧ idx ≤ s_cur.core.trail_end ∧
    ys.2.2.1.toNat + idx ≤ s0.core.trail_end ∧
    M6HdrExtOk ext_cur ∧ FullDeduceStateInv c F0 F_cur cut_cur idx s0 s_cur ∧
    (ys.2.2.1 = 0#64 → cut_cur = cut0 ∧
      s_cur.core.confl_type = s0.core.confl_type ∧ s_cur.core.confl_ref = s0.core.confl_ref) ∧
    (FullM6HdrMem c ext_cur s_cur ⋆ R) m

private theorem ded_stateInv_skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s0 s_cur : FullState} {p_bv : BitVec 32}
    (hs : FullDeduceStateInv c F0 F_cur cut (idx' + 1) s0 s_cur)
    (hp_get : (s_cur.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hnot : ¬ (s_cur.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s_cur.core.cur_level)) :
    FullDeduceStateInv c F0 F_cur cut idx' s0 s_cur := by
  have hnot_tr : ¬ (s_cur.core.mrk[(s_cur.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s_cur.core.lvl[(s_cur.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        s_cur.core.cur_level) := by rwa [hp_get]
  have htc : s_cur.core.tmp_cnt =
      (fullCurTrailIdxs s_cur.core s_cur.core.mrk idx').length := by
    rw [← fullCurTrailIdxs_succ_eq_self hnot_tr]; exact hs.tc_eq
  have hcm : FullCurMarksBelow idx' s_cur.core s_cur.core.mrk cut := fun j hj hm hl =>
    hs.cmcut j (Nat.lt_succ_of_lt hj) hm hl
  have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      (fullActiveResolvent s_cur.core s_cur.core.tmp s_cur.core.mrk
        s_cur.core.tmp_len idx')) := by
    have h1 := hs.ent
    unfold fullActiveResolvent fullCurLits at h1 ⊢
    rwa [fullCurTrailIdxs_succ_eq_self hnot_tr] at h1
  exact ⟨hs.len, hs.hw, hs.cov, hs.ext, hs.ws2, hs.nd, hs.hrefs, hs.stat,
    hs.tl_ge, hs.tl_cv, htc, hs.low, hs.mcov, hcm, hent, hs.res_eq⟩

private theorem ded_clear_ret0_cut_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_c : Nat}
    {ext : List (BitVec 64)} {s0 s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcut0 : FullCutInvW c F0 F_cur cut0 s0)
    (hext_ok : M6HdrExtOk ext) (hlen_c : s_cur.LengthsOk c)
    (hw_c : FullWitnessCutInv c F0 F_cur cut_c s_cur.core)
    (hcov_c : FullAnaMarksCov c s_cur) (hnd_c : FullArenaVarsNodup s_cur)
    (hext_p : FullExtScratchPres s0 s_cur) (hws2_c : s_cur.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs_c : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hstat_c : FullDeduceStaticEq s0.core s_cur.core)
    (hm : (FullM6HdrMem c ext s_cur ⋆ R) m)
    (hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
      Expr.ret (Arg.imm 0#64, ())) m := by
  refine deduce_hdr_clear_wp hClr hlen_c hm fun mrk' m' hm_len _ _ hm_all hm' => ?_
  d_hsteps
  let s' : FullState := { s_cur with core := { s_cur.core with mrk := mrk', min_clr_len := 0 } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen_c.core_ok with mrk_len := hm_len, min_clr_len_le := Nat.zero_le _ }, hlen_c.scratch_ok⟩
  have hw' := ded_witnessCut_with_ana hw_c mrk' s_cur.core.tmp
    s_cur.core.tmp_cnt s_cur.core.tmp_len 0
  have hnd' : FullArenaVarsNodup s' := ded_arenaVarsNodup_same_core_arena hnd_c rfl rfl
  have hotfs := ded_otfsInvW_of_cleared_state hlen' hw' (hm_all hcov_c) hcut0.2.2.1
    hstat_c.lm hnd' hcut0.2.2.2.2.1 ⟨rfl, rfl⟩ hext_p hstat_c.cv rfl hrefs_c
    (hstat_c.dm.trans hcut0.2.2.2.2.2)
  exact hQ0 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs hm'

private theorem ded_uip_exit_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_e : Nat}
    {ext : List (BitVec 64)} {s0 s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {uip_lit : BitVec 32}
    (hcut0 : FullCutInvW c F0 F_cur cut0 s0)
    (hext_ok : M6HdrExtOk ext) (hlen_c : s_cur.LengthsOk c)
    (hw_c : FullWitnessCutInv c F0 F_cur cut_e s_cur.core)
    (hcov_c : FullAnaMarksCov c s_cur) (hnd_c : FullArenaVarsNodup s_cur)
    (hext_p : FullExtScratchPres s0 s_cur) (hws2_c : s_cur.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs_c : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hstat_c : FullDeduceStaticEq s0.core s_cur.core)
    (hgood : uip_lit ≠ 0xFFFFFFFF#32 → ∃ (cut_p idx' : Nat) (s_prev : FullState) (p_bv : BitVec 32),
      FullDeduceStateInv c F0 F_cur cut_p (idx' + 1) s0 s_prev ∧
      s_cur.core.cur_vars = s_prev.core.cur_vars ∧ s_cur.core.cur_level = s_prev.core.cur_level ∧
      s_cur.core.trail_end = s_prev.core.trail_end ∧ s_cur.core.trl = s_prev.core.trl ∧
      s_cur.core.lvl = s_prev.core.lvl ∧ s_cur.core.vals = s_prev.core.vals ∧
      s_cur.core.mrk = s_prev.core.mrk ∧ s_cur.core.tmp = s_prev.core.tmp ∧
      s_cur.core.tmp_len = s_prev.core.tmp_len ∧
      idx' < s_prev.core.trail_end ∧ (s_prev.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
      uip_lit = p_bv ^^^ 1#32 ∧ s_prev.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s_prev.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s_prev.core.cur_level ∧
      (fullCurTrailIdxs s_prev.core s_prev.core.mrk idx').length = 0)
    (hm : (FullM6HdrMem c ext s_cur ⋆ R) m)
    (hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m')
    (hQ1 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_level = s0.core.cur_level →
      1 ≤ s'.core.tmp_len → s'.core.tmp_len ≤ s'.core.cur_vars →
      (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup →
      (∀ k < s'.core.tmp_len,
        (s'.core.tmp[k]?.getD 0#32).toNat < 2 * s'.core.cur_vars ∧
        s'.core.vals[(s'.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) →
      (∀ k, 1 ≤ k → k < s'.core.tmp_len →
        0 < (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
        (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s'.core.cur_level) →
      (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (1#64, ()) m') :
    wp Γ Q X
      (Expr.let_ (ts := [.bool])
        { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
          args := (Arg.var uip_lit, Arg.imm 0xFFFFFFFF, ()) } fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.ret (Arg.imm 0, ()))
          (Expr.let_ (ts := [i64])
            { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p_2 =>
            Expr.let_ (ts := [i64])
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_3 =>
              Expr.let_ (ts := [i64])
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.pTmp, Arg.var p_3.fst, ()) } fun p_4 =>
                Expr.store (t := i32) (Arg.var uip_lit) (Arg.var p_4.fst)
                  (Expr.let_ (ts := [i64])
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 272, ()) } fun p =>
                    Expr.load i64 (Arg.var p.fst) fun ld =>
                      Expr.let_ (ts := [i64])
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 1144, ()) } fun p =>
                        Expr.store (Arg.var ld) (Arg.var p.fst)
                          (Expr.call (as := [i64]) (bs := []) "full_clear_ana"
                            (Arg.var c.hdr, ()) fun _ => Expr.ret (Arg.imm 1, ()))))) m := by
  d_hsteps_nogrp
  · exact ded_clear_ret0_cut_wp hClr hcut0 hext_ok hlen_c hw_c hcov_c hnd_c hext_p hws2_c
      hrefs_c hstat_c hm hQ0
  · obtain ⟨cut_p, idx', s_prev, p_bv, hs1, hcv_p, hcl_p, hte_p, htrl_p, hlvl_p, hvals_p,
      hmrk_p, htmp_p, htl_p, hidx_te, hp_get, huip_eq, hm_p, hl_p, hempty⟩ := hgood ‹_›
    have hmcl_lt : s_cur.core.min_clr_len < 2 ^ 64 := by
      have := hlen_c.core_ok.min_clr_len_le; have := fullInv_max_vars_lt32 c; omega
    have htmp_pos : 0 < s_cur.core.tmp.length := by
      rw [hlen_c.core_ok.tmp_len_arr]
      have := hs1.tl_ge; have := hs1.tl_cv; have := hlen_c.core_ok.cur_vars_le; omega
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    d_hsteps_nogrp
    let s1 : FullState :=
      { s_cur with
        core := { s_cur.core with tmp := s_cur.core.tmp.set 0 uip_lit }
        scratch := { s_cur.scratch with res_sz := BitVec.ofNat 64 s_cur.core.min_clr_len } }
    have hso1 := hlen_c.scratch_ok
    have hlen1 : s1.LengthsOk c :=
      ⟨{ hlen_c.core_ok with tmp_len_arr := (by
           dsimp [s1]; rw [List.length_set, hlen_c.core_ok.tmp_len_arr]) },
        { hso1 with walk_vals_len := hso1.walk_vals_len }⟩
    have htmp0 : s1.core.tmp[0]? = some uip_lit := List.getElem?_set_self htmp_pos
    have htl_len1 : s1.core.tmp_len ≤ s1.core.tmp.length := by
      rw [hlen1.core_ok.tmp_len_arr]; exact hlen1.core_ok.tmp_len_le
    have huip_div2 : uip_lit.toNat / 2 = p_bv.toNat / 2 := by
      rw [huip_eq, BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, ded_lit_xor1_div2]
    have huip_nat : uip_lit.toNat = p_bv.toNat ^^^ 1 := by
      rw [huip_eq, BitVec.toNat_xor]; rfl
    have hlow_c : FullLowerInv c s_cur.core s_cur.core.tmp s_cur.core.mrk s_cur.core.tmp_len := by
      have h := hs1.low; unfold FullLowerInv at h ⊢
      rw [hcv_p, hvals_p, hlvl_p, hcl_p, htmp_p, hmrk_p, htl_p]; exact h
    have htl_ge_c : 1 ≤ s_cur.core.tmp_len := htl_p ▸ hs1.tl_ge
    have htl_cv_c : s_cur.core.tmp_len ≤ s_cur.core.cur_vars := htl_p ▸ hcv_p ▸ hs1.tl_cv
    have hnodup1 : (List.map (fun x => x.toNat / 2)
        (List.take s1.core.tmp_len s1.core.tmp)).Nodup := by
      refine fullTmpTake_uip_nodup htl_ge_c htl_len1 htmp0
        (ded_fullLowerInv_set0 uip_lit hlow_c) ?_
      rw [huip_div2, hlvl_p, hcl_p]; exact hl_p
    have hp_lt : p_bv.toNat < 2 * s_prev.core.cur_vars := by
      rw [← hp_get]; exact hs1.hw.trail_lits_lt idx' hidx_te
    have huip_lt : uip_lit.toNat < 2 * s_cur.core.cur_vars := by rw [huip_nat, hcv_p]; omega
    have huip_fals : s_cur.core.vals[uip_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      rw [hvals_p, huip_nat, hs1.hw.vals_false_iff (p_bv.toNat ^^^ 1) (by omega)]
      exact ⟨idx', hidx_te, by rw [hp_get, ded_lit_xor1_xor1]⟩
    have hent_prev : (cnfOfClauses F_cur).EntailsClause (cnfClause
        (fullActiveResolvent s_cur.core s_cur.core.tmp s_cur.core.mrk
          s_cur.core.tmp_len (idx' + 1))) := by
      have h := hs1.ent
      unfold fullActiveResolvent fullLowerLits fullCurLits fullCurTrailIdxs at h ⊢
      rw [htmp_p, htl_p, htrl_p, hlvl_p, hcl_p, hmrk_p]; exact h
    have hent1 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s1.core.tmp_len s1.core.tmp))) := by
      rw [fullLowerLits_take_eq htl_ge_c htmp0,
        show fullLowerLits s1.core.tmp s1.core.tmp_len =
          fullLowerLits s_cur.core.tmp s_cur.core.tmp_len from
          ded_fullLowerLits_set0 uip_lit htl_ge_c
            (by rw [hlen_c.core_ok.tmp_len_arr]; exact hlen_c.core_ok.tmp_len_le),
        huip_eq]
      exact fullDeduce_uip_entails
        (by unfold fullCurTrailIdxs; rw [htrl_p, hmrk_p, hlvl_p, hcl_p]; exact hempty)
        (by rw [hmrk_p, htrl_p]; exact hp_get ▸ hm_p)
        (by rw [hlvl_p, hcl_p, htrl_p]; exact hp_get ▸ hl_p)
        (by rw [htrl_p]; exact hp_get) hent_prev
    refine deduce_hdr_clear_wp hClr hlen1 (fullM6HdrMem_unfocus_full (s := s1) ‹_›)
      fun mrk' m' hm_len _ _ hm_all hm' => ?_
    d_hsteps
    let s' : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
    have hlen' : s'.LengthsOk c :=
      ⟨{ hlen1.core_ok with mrk_len := hm_len, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
    have hw' := ded_witnessCut_with_ana hw_c mrk' s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len 0
    have hnd' : FullArenaVarsNodup s' := ded_arenaVarsNodup_same_core_arena hnd_c rfl rfl
    have hotfs := ded_otfsInvW_of_cleared_state hlen' hw' (hm_all hcov_c) hcut0.2.2.1
      hstat_c.lm hnd' hcut0.2.2.2.2.1 ⟨rfl, rfl⟩ hext_p hstat_c.cv rfl hrefs_c
      (hstat_c.dm.trans hcut0.2.2.2.2.2)
    refine hQ1 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs hstat_c.cl
      htl_ge_c htl_cv_c hnodup1 (fun k hk => ?_) (fun k hk1 hk2 => ?_) ?_ hent1 hm'
    · by_cases hk0 : k = 0
      · subst hk0
        dsimp only [s', s1]
        rw [List.getElem?_set_self htmp_pos, Option.getD_some]
        exact ⟨huip_lt, huip_fals⟩
      · have hs_set : s'.core.tmp[k]? = s_cur.core.tmp[k]? := List.getElem?_set_ne (by omega)
        have hlowk := hlow_c.1 k (by omega) hk
        dsimp only [s', s1] at hs_set ⊢
        rw [hs_set]
        exact ⟨hlowk.1, hlowk.2.1⟩
    · have hs_set : s'.core.tmp[k]? = s_cur.core.tmp[k]? := List.getElem?_set_ne (by omega)
      have hlowk := hlow_c.1 k hk1 hk2
      dsimp only [s', s1] at hs_set ⊢
      rw [hs_set]
      exact ⟨hlowk.2.2.1, hlowk.2.2.2.1⟩
    · dsimp only [s', s1]
      rw [List.getElem?_set_self htmp_pos, Option.getD_some, huip_div2, hlvl_p, hcl_p]
      exact hl_p

private theorem ded_seed_init_facts' {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s sl : FullState}
    (hcut0 : FullCutInvW c F0 F_cur cut s) (hpos : 0 < s.core.cur_level)
    (hsl_c : sl.core = { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 })
    (hsl_sc : sl.scratch = { s.scratch with ant_sz := 0#64, res_sz := 0#64 }) :
    FullState.LengthsOk c sl ∧ FullWitnessCutInv c F0 F_cur cut sl.core ∧
    FullAnaMarksCov c sl ∧ FullArenaVarsNodup sl ∧
    fullArenaClauseRefs sl = fullArenaClauseRefs s ∧ FullExtScratchPres s sl ∧
    sl.scratch.work_stk2 = s.scratch.work_stk2 ∧ FullDeduceStaticEq s.core sl.core ∧
    1 ≤ sl.core.cur_vars ∧ FullLowerInv c sl.core sl.core.tmp sl.core.mrk 1 ∧
    FullMarksCov sl.core sl.core.tmp sl.core.mrk 1 ∧
    FullCurMarksBelow sl.core.trail_end sl.core sl.core.mrk cut ∧
    sl.core.tmp_cnt = (fullCurTrailIdxs sl.core sl.core.mrk sl.core.trail_end).length := by
  have h1_cv : 1 ≤ s.core.cur_vars := by
    have := hcut0.2.1.cur_level_le; have := hcut0.1.core_ok.trail_end_le; omega
  have h1_mv : 1 ≤ c.max_vars := Nat.le_trans h1_cv hcut0.1.core_ok.cur_vars_le
  have hlen : sl.LengthsOk c := by
    refine ⟨?_, ?_⟩
    · rw [hsl_c]
      exact { hcut0.1.core_ok with tmp_len_le := h1_mv, min_clr_len_le := Nat.zero_le _ }
    · rw [hsl_sc]
      have hso := hcut0.1.scratch_ok
      exact { hso with walk_vals_len := hso.walk_vals_len }
  have hw : FullWitnessCutInv c F0 F_cur cut sl.core := by
    rw [hsl_c]; exact ded_witnessCut_with_ana hcut0.2.1 _ _ 0 1 0
  have hclr : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 = 0#8 := by
    intro v hv; rw [hsl_c]; exact hcut0.2.2.1.1 v hv
  have hcov : FullAnaMarksCov c sl := fullAnaMarksCov_of_clear hclr (by rw [hsl_c])
  have hnd : FullArenaVarsNodup sl :=
    ded_arenaVarsNodup_same_core_arena hcut0.2.2.2.1 (by rw [hsl_c]) (by rw [hsl_c])
  have hrefs : fullArenaClauseRefs sl = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hsl_c]
  have hext : FullExtScratchPres s sl := by
    unfold FullExtScratchPres; rw [hsl_sc]; exact ⟨rfl, rfl⟩
  have hws2 : sl.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hsl_sc]
  have hstat : FullDeduceStaticEq s.core sl.core := by
    rw [hsl_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlow : FullLowerInv c sl.core sl.core.tmp sl.core.mrk 1 :=
    ⟨fun _ h1 _ => by omega, fun _ _ h1 _ _ => by omega⟩
  have hmcov : FullMarksCov sl.core sl.core.tmp sl.core.mrk 1 := by
    intro v hv hnz
    have hmv : v < c.max_vars := by
      have := hcut0.1.core_ok.cur_vars_le; rw [hsl_c] at hv; dsimp only at hv; omega
    exact absurd (hclr v hmv) hnz
  have hcm : FullCurMarksBelow sl.core.trail_end sl.core sl.core.mrk cut := by
    intro j hj hnz
    have hlt := hw.trail_lits_lt j hj
    have hv_lt : (sl.core.trl[j]?.getD 0#32).toNat / 2 < c.max_vars := by
      have := hcut0.1.core_ok.cur_vars_le; rw [hsl_c] at hlt ⊢; dsimp only at hlt ⊢; omega
    exact absurd (hclr _ hv_lt) hnz
  have hnil : fullCurTrailIdxs sl.core sl.core.mrk sl.core.trail_end = [] :=
    ded_curTrailIdxs_nil_of_clear (Nat.le_refl _) (by rw [hsl_c]; exact hcut0.1.core_ok.cur_vars_le)
      hw.trail_lits_lt hclr
  exact ⟨hlen, hw, hcov, hnd, hrefs, hext, hws2, hstat, by rw [hsl_c]; exact h1_cv,
    hlow, hmcov, hcm, by rw [hnil, hsl_c]; rfl⟩

private theorem ded_seed_confl_wp {Γ : Env}
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" Spec.s13AnalyzeRsnHdrSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s sl : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {J : Cont [.bool]} {X : XPost} {Q : Post [i64]}
    (hcfg : FullM6HdrCfgOk c) (hcut0 : FullCutInvW c F0 F_cur cut s) (hext_ok : M6HdrExtOk ext)
    (hpos : 0 < s.core.cur_level) (hconfl : FullConflictOkCut F_cur cut s)
    (hsl_c : sl.core = { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 })
    (hsl_sc : sl.scratch = { s.scratch with ant_sz := 0#64, res_sz := 0#64 })
    (hm : (FullM6HdrMem c ext sl ⋆ R) m)
    (hJ : ∀ (ok : Bool) (ext1 : List (BitVec 64)) (s1 : FullState) (ml : Mem 64),
      M6HdrExtOk ext1 → s1.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s1.core →
      FullAnaMarksCov c s1 → FullArenaVarsNodup s1 → FullExtScratchPres s s1 →
      s1.scratch.work_stk2 = s.scratch.work_stk2 →
      fullArenaClauseRefs s1 = fullArenaClauseRefs s → FullDeduceStaticEq s.core s1.core →
      s1.core.confl_type = s.core.confl_type → s1.core.confl_ref = s.core.confl_ref →
      (ok = true → FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1) →
      (FullM6HdrMem c ext1 s1 ⋆ R) ml → J (ok, ()) ml) :
    wp Γ Q X
      (Expr.let_ (ts := [i64]) { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var c.hdr, Arg.imm 528, ()) } fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_ (ts := [.bool])
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var ld, Arg.imm 1, ()) } fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.group (sig := [[.bool]]) (fun _ =>
                Blocks.cons (fun p => Expr.jump (ts := [.bool]) J (Arg.var p.fst, ()))
                  Blocks.nil) fun Js =>
                Expr.let_ (ts := [i64])
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 536, ()) } fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                    Expr.let_ (ts := [i32])
                      { sig := [i64], code := OpCode.trunc 64 32,
                        args := (Arg.var ld, ()) } fun p =>
                      Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                        (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ()) fun p =>
                        Expr.jnz (Arg.var p.fst)
                          (Expr.let_ (ts := [i64])
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 544, ()) } fun p =>
                            Expr.load i64 (Arg.var p.fst) fun ld =>
                              Expr.let_ (ts := [i32])
                                { sig := [i64], code := OpCode.trunc 64 32,
                                  args := (Arg.var ld, ()) } fun p =>
                                Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                                  (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ())
                                  fun p => Expr.jnz (Arg.var p.fst)
                                    (Expr.jump (ts := [.bool]) Js.fst (Arg.imm true, ()))
                                    (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))
                          (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))
              (Expr.group (sig := [[.bool]]) (fun _ =>
                Blocks.cons (fun p => Expr.jump (ts := [.bool]) J (Arg.var p.fst, ()))
                  Blocks.nil) fun Js =>
                Expr.let_ (ts := [i64])
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 176, ()) } fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                    Expr.let_ (ts := [i64])
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var ld, Arg.imm 3, ()) } fun p =>
                      Expr.let_ (ts := [i64])
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p_1 =>
                        Expr.load i64 (Arg.var p_1.fst) fun ld =>
                          Expr.let_ (ts := [.bool])
                            { sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64 Ty.bool rfl,
                              args := (Arg.var p.fst, Arg.var ld, ()) } fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (Expr.let_ (ts := [i64])
                                { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var c.hdr, Arg.imm 176, ()) } fun p =>
                                Expr.load i64 (Arg.var p.fst) fun ld =>
                                  Expr.let_ (ts := [i32])
                                    { sig := [i64], code := OpCode.trunc 64 32,
                                      args := (Arg.var ld, ()) } fun p =>
                                    Expr.call (as := [i64, i32, i32]) (bs := [.bool])
                                      "full_analyze_rsn_m6_hdr"
                                      (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ())
                                      fun p => Expr.jump (ts := [.bool]) Js.fst
                                        (Arg.var p.fst, ()))
                              (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))) m := by
  obtain ⟨hlen_l, hw_l, hcov_l, hnd_l, hrefs_l, hext_l, hws2_l, hstat_l, h1_cv_l,
    hlow_l, hmcov_l, hcm_l, htc_l⟩ := ded_seed_init_facts' hcut0 hpos hsl_c hsl_sc
  have hmax28 : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hmax32 := fullInv_max_vars_lt32 c
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcut0.1.core_ok.cur_vars_le
  have hcur32_l : sl.core.cur_level < 2 ^ 32 := by
    have := hw_l.cur_level_le; have := hlen_l.core_ok.trail_end_le
    have := hlen_l.core_ok.cur_vars_le; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  d_hsteps_nogrp
  · have hct1 : sl.core.confl_type = 1#64 := by assumption
    have hct_s1 : s.core.confl_type = 1#64 := by rwa [hsl_c] at hct1
    have hco_w : s.core.confl_type = 1#64 ∧ s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
        s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
        s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
        s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
      rcases hconfl.1 with hc1 | hc2
      · exact hc1
      · exfalso; rw [hct_s1] at hc2; cases hc2.1
    have hco_cut := hconfl.2; rw [ite_eq_left hct_s1] at hco_cut
    have hl0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by have := hco_w.2.1; omega
    have hl1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by have := hco_w.2.2.1; omega
    have hl0_tr : (BitVec.truncate 32 sl.core.confl_lit0).toNat = s.core.confl_lit0.toNat := by
      rw [hsl_c]; exact ded_bv32_truncate_toNat_of_lt _ hl0_32
    have hl1_tr : (BitVec.truncate 32 sl.core.confl_lit1).toNat = s.core.confl_lit1.toNat := by
      rw [hsl_c]; exact ded_bv32_truncate_toNat_of_lt _ hl1_32
    refine wp_unroll_group fun Js hJs => ?_
    d_hsteps_nogrp
    refine deduce_hdr_lit_wp hLit hlen_l hcur32_l
      (by have h := h1_cv_l; rw [hsl_c] at h ⊢; exact h)
      (by rw [hsl_c]; dsimp only; omega) hcov_l (fullM6HdrMem_unfocus_full hmf)
      fun ok1 mrk1 tmp1 tc1 tl1 mcl1 ws1_1 ant1 res1 m1 hlen1 hcov1 htl1_ge htl1_le htl1_cv
        htc1_ge hant1 hres1 htc1_eq hmp1 htp1 hnm1 hnt1 hok1 hm1 => ?_
    let sa : FullState :=
      { sl with
        core := { sl.core with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1,
                               min_clr_len := mcl1 }
        scratch := { sl.scratch with work_stk1 := ws1_1, ant_sz := ant1, res_sz := res1 } }
    d_hsteps_nogrp
    · have hok1t : ok1 = true := by assumption
      subst ok1
      have h_ok1 := hok1 rfl
      have hff : (4294967295 : BitVec 32).toNat = 4294967295 := rfl
      have hne1 : (BitVec.setWidth 32 sl.core.confl_lit0, ()).fst.toNat / 2 ≠
          (4294967295 : BitVec 32).toNat := by
        have h1 := h_ok1.1; have h2 := hlen_l.core_ok.cur_vars_le; omega
      have hsa_pres := deduce_seed_lit_step hlen_l hw_l hnd_l hrefs_l hext_l hws2_l hstat_l
        (by rw [hsl_c]; dsimp only; omega) (by rw [hsl_c]; exact Nat.zero_le _) htc_l
        (by have h := hlow_l; rw [hsl_c] at h ⊢; exact h)
        (by have h := hmcov_l; rw [hsl_c] at h ⊢; exact h) hcm_l
        (by rw [hsl_c, hsl_sc]; rfl) (by rw [hl0_tr, hsl_c]; exact hco_w.2.1)
        (by rw [hl0_tr, hsl_c]; exact hco_w.2.2.2.1)
        (by rw [hl0_tr, hsl_c]; exact hco_cut.1) sa rfl rfl hlen1 hcov1 htl1_cv htl1_ge htl1_le
        hmp1 htp1 hnm1 hnt1 hres1 htc1_eq ⟨h_ok1.1, h_ok1.2 hne1⟩
      obtain ⟨hl_a, hw_a, hcov_a, hext_a, hws2_a, hnd_a, hrefs_a, hstat_a, htl1_a, htl_cv_a,
        htc_eq_a, hlow_a, hmcov_a, hcm_a, _, hl0_res, hres_a⟩ := hsa_pres
      have htc_a_le1 : sa.core.tmp_cnt ≤ 1 := by
        dsimp [sa]; rw [htc1_eq, hsl_c]; dsimp only; split <;> omega
      have hcur32_a : sa.core.cur_level < 2 ^ 32 := by
        rw [hstat_a.cl, ← hstat_l.cl]; exact hcur32_l
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      d_hsteps_nogrp
      refine deduce_hdr_lit_wp hLit hl_a hcur32_a htl_cv_a (by omega) hcov_a
        (fullM6HdrMem_unfocus_full hm1f)
        fun ok2 mrk2 tmp2 tc2 tl2 mcl2 ws1_2 ant2 res2 m2 hlen2 hcov2 htl2_ge htl2_le htl2_cv
          htc2_ge hant2 hres2 htc2_eq hmp2 htp2 hnm2 hnt2 hok2 hm2 => ?_
      let sb : FullState :=
        { sa with
          core := { sa.core with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2,
                                 min_clr_len := mcl2 }
          scratch := { sa.scratch with work_stk1 := ws1_2, ant_sz := ant2, res_sz := res2 } }
      have hw_b : FullWitnessCutInv c F0 F_cur cut sb.core :=
        ded_witnessCut_with_ana hw_a _ _ _ _ _
      have hnd_b : FullArenaVarsNodup sb := ded_arenaVarsNodup_same_core_arena hnd_a rfl rfl
      have hrefs_b : fullArenaClauseRefs sb = fullArenaClauseRefs s := hrefs_a
      have hext_b : FullExtScratchPres s sb := hext_a
      have hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2 := hws2_a
      have hstat_b : FullDeduceStaticEq s.core sb.core :=
        ⟨hstat_a.cv, hstat_a.cl, hstat_a.te, hstat_a.trl, hstat_a.lvl, hstat_a.rsns,
          hstat_a.vals, hstat_a.fuel, hstat_a.dm, hstat_a.lm⟩
      have hct_sb : sb.core.confl_type = s.core.confl_type := by
        change sa.core.confl_type = s.core.confl_type; change sl.core.confl_type = _
        rw [hsl_c]
      have hcr_sb : sb.core.confl_ref = s.core.confl_ref := by
        change sa.core.confl_ref = s.core.confl_ref; change sl.core.confl_ref = _
        rw [hsl_c]
      d_hsteps_nogrp
      · have hok2t : ok2 = true := by assumption
        subst ok2
        have h_ok2 := hok2 rfl
        have hne2 : (BitVec.setWidth 32 sa.core.confl_lit1, ()).fst.toNat / 2 ≠
            (4294967295 : BitVec 32).toNat := by
          have h1 := h_ok2.1; have h2 := hl_a.core_ok.cur_vars_le; omega
        have hl1_sa : (BitVec.setWidth 32 sa.core.confl_lit1, ()).fst.toNat =
            s.core.confl_lit1.toNat := by
          dsimp only [sa]; rw [← BitVec.truncate_eq_setWidth]; exact hl1_tr
        have hsb_sem := deduce_seed_lit_step hl_a hw_a hnd_a hrefs_a hext_a hws2_a hstat_a
          htl1_a htc_a_le1 htc_eq_a hlow_a hmcov_a hcm_a hres_a
          (by rw [hstat_a.cv, hl1_sa]; exact hco_w.2.2.1)
          (by rw [hstat_a.vals, hl1_sa]; exact hco_w.2.2.2.2.1)
          (by rw [hstat_a.lvl, hstat_a.cl, hstat_a.trl, hl1_sa]; exact hco_cut.2)
          sb rfl rfl hlen2 hcov2 htl2_cv htl2_ge htl2_le hmp2 htp2 hnm2 hnt2 hres2 htc2_eq
          ⟨h_ok2.1, h_ok2.2 hne2⟩
        obtain ⟨hl_b, hw_b', hcov_b, hext_b', hws2_b', hnd_b', hrefs_b', hstat_b',
          htl1_b, htl_cv_b, htc_eq_b, hlow_b, hmcov_b, hcm_b, _, hl1_res, hres_b⟩ := hsb_sem
        have hl0_sa : (BitVec.setWidth 32 sl.core.confl_lit0, ()).fst.toNat =
            s.core.confl_lit0.toNat := by
          dsimp only; rw [← BitVec.truncate_eq_setWidth]; exact hl0_tr
        have hl1_sb : (BitVec.setWidth 32 sl.core.confl_lit1).toNat =
            s.core.confl_lit1.toNat := by
          rw [← BitVec.truncate_eq_setWidth]; exact hl1_tr
        have hinv_b := deduce_seed_bin_sem (s := s) (sa := sa) (sb := sb)
          hco_w.2.2.2.2.2
          (by simpa only [hl0_sa] using hl0_res)
          (by simpa only [hl1_sb] using hl1_res)
          (fun hmem => ded_mem_activeResolvent_mono hl_a.core_ok hw_a
            (by dsimp only [sb] at hlen2
                rw [hlen2.core_ok.tmp_len_arr]; exact hlen2.core_ok.tmp_len_le)
            htl2_ge htp2 hmp2 hmem)
          hl_b hw_b' hcov_b hext_b' hws2_b' hnd_b' hrefs_b' hstat_b' htl1_b htl_cv_b
          htc_eq_b hlow_b hmcov_b hcm_b hres_b
        exact hJ true ext sb m2 hext_ok hl_b hw_b' hcov_b hnd_b'
          hext_b' hws2_b' hrefs_b' hstat_b' hct_sb hcr_sb (fun _ => hinv_b) hm2
      · exact hJ false ext sb m2 hext_ok hlen2 hw_b hcov2 hnd_b
          hext_b hws2_b hrefs_b hstat_b hct_sb hcr_sb (fun h => Bool.noConfusion h) hm2
    · have hw_a : FullWitnessCutInv c F0 F_cur cut sa.core :=
        ded_witnessCut_with_ana hw_l _ _ _ _ _
      have hstat_a : FullDeduceStaticEq s.core sa.core :=
        ⟨hstat_l.cv, hstat_l.cl, hstat_l.te, hstat_l.trl, hstat_l.lvl, hstat_l.rsns,
          hstat_l.vals, hstat_l.fuel, hstat_l.dm, hstat_l.lm⟩
      have hct_sa : sa.core.confl_type = s.core.confl_type := by
        change sl.core.confl_type = _; rw [hsl_c]
      have hcr_sa : sa.core.confl_ref = s.core.confl_ref := by
        change sl.core.confl_ref = _; rw [hsl_c]
      exact hJ false ext sa m1 hext_ok hlen1 hw_a hcov1
        (ded_arenaVarsNodup_same_core_arena hnd_l rfl rfl) hext_l hws2_l hrefs_l hstat_a
        hct_sa hcr_sa (fun h => Bool.noConfusion h) hm1
  · have hn1_l : sl.core.confl_type ≠ 1#64 := by assumption
    have hpre_rsn := deduce_seed_rsn_pre hlen_l hw_l (by
      unfold FullConflictOkCut FullConflictOkW at hconfl ⊢
      simpa only [hsl_c, fullArenaClauseRefs, fullArenaClauseRefsCore,
        fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore,
        fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSize,
        fullArenaClauseSizeCore] using hconfl) hn1_l
    obtain ⟨_, hbd3, _, _, _, href_cr, _⟩ := hpre_rsn
    have har_lt64 : sl.core.arena_len < 2 ^ 64 := by
      have := hlen_l.core_ok.arena_len_le
      have : c.arena_cap < 2 * 2 ^ 28 := c.harena
      omega
    have hcr_lt64 : sl.core.confl_ref.toNat + 3 < 2 ^ 64 := by omega
    refine wp_unroll_group fun Js hJs => ?_
    d_hsteps_nogrp
    · refine wp_call_of_spec _ _ (hRsn (c.hdr, BitVec.truncate 32 sl.core.confl_ref,
        0xFFFFFFFF#32, ()) _
        (fun r m' => wp Γ Q X (Expr.jump (ts := [.bool]) Js (Arg.var r.fst, ())) m') X ?_)
      refine ⟨c, F0, F_cur, cut, ext, sl, R, rfl, hcfg, hext_ok, hlen_l, hw_l, hcov_l,
        (by have h := h1_cv_l; rw [hsl_c] at h ⊢; exact h),
        (by have h := hlen_l.core_ok.cur_vars_le; rw [hsl_c] at h ⊢; dsimp only at *; omega),
        (fun _ _ => href_cr), fullM6HdrMem_unfocus_full hmf,
        fun ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m' hext' _ hlen2 hw2 hcov2
          hext2 hws2_2 htl2_ge htl2_cv htc2_ge hrefs2 hcl2 hmp htp hnm hnt hnd_j hcnt hres2
          hok_lits hm2 => ?_⟩
      let s2 : FullState :=
        { core := { sl.core with tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl',
                                 mrk := mrk', tmp := tmp', min_clr := mclr', arena := arena' }
          scratch := sc' }
      have hnd2 : FullArenaVarsNodup s2 := ded_arenaVarsNodup_of_pres hnd_l hrefs2
        (fun r hr => ⟨(hcl2 r hr).2.1, (hcl2 r hr).2.2⟩)
      have hext_s2 : FullExtScratchPres s s2 := ⟨hext2.1.trans hext_l.1, hext2.2.trans hext_l.2⟩
      have hws2_s2 : s2.scratch.work_stk2 = s.scratch.work_stk2 := hws2_2.trans hws2_l
      have hrefs_s2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s := hrefs2.trans hrefs_l
      have hstat_s2 : FullDeduceStaticEq s.core s2.core :=
        ⟨hstat_l.cv, hstat_l.cl, hstat_l.te, hstat_l.trl, hstat_l.lvl, hstat_l.rsns,
          hstat_l.vals, hstat_l.fuel, hstat_l.dm, hstat_l.lm⟩
      have hct_s2 : s2.core.confl_type = s.core.confl_type := by
        change sl.core.confl_type = _; rw [hsl_c]
      have hcr_s2 : s2.core.confl_ref = s.core.confl_ref := by
        change sl.core.confl_ref = _; rw [hsl_c]
      d_hsteps_nogrp
      exact hJ ok ext' s2 m' hext' hlen2 hw2 hcov2 hnd2 hext_s2 hws2_s2
        hrefs_s2 hstat_s2 hct_s2 hcr_s2 (fun hokt => by
          have hok_lits' := hok_lits hokt
          exact deduce_seed_rsn_sem hcut0 hconfl hsl_c hsl_sc hlen_l rfl hlen2 hw2 hcov2
            hext2 hws2_2 (by rw [hsl_c] at htl2_ge; exact htl2_ge) htl2_cv
            (by rw [hsl_c] at htc2_ge; exact htc2_ge) hrefs2 hcl2 hmp
            (by simpa only [hsl_c] using htp) hnm
            (by simpa only [hsl_c] using hnt)
            (by simpa only [hsl_c] using hnd_j)
            (by simpa only [hsl_c] using hcnt)
            hres2 (by simpa only [hsl_c] using hok_lits'.2.2) hn1_l) hm2
    · exfalso
      have hule : ¬(sl.core.confl_ref.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 ≤
          sl.core.arena_len % 2 ^ 64 := by assumption
      rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt hcr_lt64,
        Nat.mod_eq_of_lt har_lt64] at hule
      exact hule hbd3

/-! ## 2. Parametric Loop Reason Signature & Main Theorem -/

/-- Exact signature of `WpDeduce3a.deduce_loop_rsn_wp`, abstracted over the reason-step proof
so `WpDeduceTop` checks independently over `WpDeduce{0,1,2}` and composes cleanly in `Cert`. -/
abbrev DeduceLoopRsnStep (Γ : Env) : Prop :=
  ∀ {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_cur idx' : Nat}
    {ext : List (BitVec 64)} {s0 s1 sl : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {Js_2 : Cont [i64, i32, i64]}
    {steps init_res_sz : BitVec 64} {p_bv skip_var : BitVec 32},
    skip_var = p_bv >>> 1#32 → FullM6HdrCfgOk c → FullCutInvW c F0 F_cur cut0 s0 →
    FullConflictOkCut F_cur cut0 s0 → 0 < s0.core.cur_level → M6HdrExtOk ext →
    FullDeduceStateInv c F0 F_cur cut_cur (idx' + 1) s0 s1 → idx' < s1.core.trail_end →
    (s1.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat →
    s1.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 →
    (s1.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s1.core.cur_level →
    sl.core = { s1.core with tmp_cnt := s1.core.tmp_cnt - 1 } → sl.scratch = s1.scratch →
    (steps = 0#64 → cut_cur = cut0 ∧
      s1.core.confl_type = s0.core.confl_type ∧ s1.core.confl_ref = s0.core.confl_ref) →
    (FullM6HdrMem c ext sl ⋆ R) m →
    (∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m') →
    (∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m') →
    (∀ (cut_j : Nat) (ext_j : List (BitVec 64)) (s_j : FullState) (m_j : Mem 64),
      cut_j ≤ s_j.core.trail_end → M6HdrExtOk ext_j →
      FullDeduceStateInv c F0 F_cur cut_j idx' s0 s_j →
      (FullM6HdrMem c ext_j s_j ⋆ R) m_j →
      Js_2 (BitVec.ofNat 64 s_j.core.tmp_cnt, 0xFFFFFFFF#32, steps + 1#64, ()) m_j) →
    wp Γ Q X
      (Expr.let_ (Op.mk (.zext 32 64) (Arg.var skip_var, ())) fun p_41 =>
       Expr.let_ (Op.mk (.mul i64) (Arg.var p_41.fst, Arg.imm 4, ())) fun p_42 =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.pReason, Arg.var p_42.fst, ())) fun p_43 =>
       Expr.load i32 (Arg.var p_43.fst) fun ld_13 =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ())) fun p_44 =>
       Expr.store (t := i64) (Arg.imm 0) (Arg.var p_44.fst)
         (Expr.let_ (Op.mk (.add i64) (Arg.var steps, Arg.imm 1, ())) fun p_45 =>
          Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_rsn_m6_hdr"
            (Arg.var c.hdr, Arg.var ld_13, Arg.var skip_var, ()) fun p_46 =>
          Expr.jnz (Arg.var p_46.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 184, ())) fun p_47 =>
             Expr.load i64 (Arg.var p_47.fst) fun ld_14 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_48 =>
             Expr.load i64 (Arg.var p_48.fst) fun ld_15 =>
             Expr.group (sig := [[i64]]) (fun _ =>
               Blocks.cons (fun p_49 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ())) fun p_50 =>
                 Expr.load i64 (Arg.var p_50.fst) fun ld_16 =>
                 Expr.group (sig := [[]]) (fun _ =>
                   Blocks.cons (fun _ =>
                     Expr.jump Js_2
                       (Arg.var ld_14, Arg.imm 4294967295, Arg.var p_45.fst, ()))
                   Blocks.nil) fun Js_1 =>
                 Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var ld_16, Arg.imm 3, ()))
                   fun p_51 =>
                 Expr.jnz (Arg.var p_51.fst)
                   (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                      (Arg.var p_49.fst, Arg.var ld_16, ())) fun p_52 =>
                    Expr.jnz (Arg.var p_52.fst)
                      (Expr.let_ (Op.mk (.and i32) (Arg.var ld_13, Arg.imm 2147483648, ()))
                         fun p_53 =>
                       Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var p_53.fst, Arg.imm 0, ()))
                         fun p_54 =>
                       Expr.jnz (Arg.var p_54.fst)
                         (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p_55 =>
                          Expr.load i64 (Arg.var p_55.fst) fun ld_17 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ())) fun p_56 =>
                          Expr.load i64 (Arg.var p_56.fst) fun ld_18 =>
                          Expr.group (sig := [[]]) (fun _ =>
                            Blocks.cons (fun _ => Expr.jump Js_1.fst ()) Blocks.nil) fun Js_3 =>
                          Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                            (Arg.var ld_16, Arg.imm 3, ())) fun p_57 =>
                          Expr.jnz (Arg.var p_57.fst)
                            (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_bin"
                              (Arg.var c.hdr, Arg.var ld_13, Arg.var p_bv, ()) fun p_58 =>
                             Expr.jnz (Arg.var p_58.fst)
                               (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 112, ()))
                                  fun p_59 =>
                                Expr.load i64 (Arg.var p_59.fst) fun ld_19 =>
                                Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_13, ())) fun p_60 =>
                                Expr.let_ (Op.mk (.mul i64) (Arg.var p_60.fst, Arg.imm 4, ()))
                                  fun p_61 =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var ld_19, Arg.var p_61.fst, ()))
                                  fun p_62 =>
                                Expr.load i32 (Arg.var p_62.fst) fun ld_20 =>
                                Expr.let_ (Op.mk (.and i32) (Arg.var ld_20, Arg.imm 4194304, ()))
                                  fun p_63 =>
                                Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                  (Arg.var p_63.fst, Arg.imm 0, ())) fun p_64 =>
                                Expr.group (sig := [[]]) (fun _ =>
                                  Blocks.cons (fun _ =>
                                    Expr.group (sig := [[]]) (fun _ =>
                                      Blocks.cons (fun _ =>
                                        Expr.let_ (Op.mk (.add i64)
                                          (Arg.var c.hdr, Arg.imm 272, ())) fun p_67 =>
                                        Expr.load i64 (Arg.var p_67.fst) fun ld_mcl =>
                                        Expr.let_ (Op.mk (.add i64)
                                          (Arg.var c.hdr, Arg.imm 1144, ())) fun p_68 =>
                                        Expr.store (Arg.var ld_mcl) (Arg.var p_68.fst)
                                          (Expr.call (as := [i64]) (bs := []) "full_clear_ana"
                                             (Arg.var c.hdr, ()) fun _ => Expr.ret (Arg.imm 2, ())))
                                      Blocks.nil) fun Js_4 =>
                                    Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                      (Arg.var p_45.fst, Arg.imm 1, ())) fun p_66 =>
                                    Expr.jnz (Arg.var p_66.fst)
                                      (Expr.let_ (Op.mk (.add i64)
                                         (Arg.var c.hdr, Arg.imm 1144, ())) fun p_67 =>
                                       Expr.load i64 (Arg.var p_67.fst) fun ld_21 =>
                                       Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                         (Arg.var ld_21, Arg.var init_res_sz, ())) fun p_68 =>
                                       Expr.jnz (Arg.var p_68.fst)
                                         (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := [])
                                            "full_otfs_subsume"
                                           (Arg.var c.hdr, Arg.imm 0, Arg.var ld_17, Arg.var ld_18,
                                             Arg.imm true, ()) fun _ => Expr.jump Js_4.fst ())
                                         (Expr.jump Js_4.fst ()))
                                      (Expr.jump Js_4.fst ()))
                                  Blocks.nil) fun Js_4 =>
                                Expr.jnz (Arg.var p_64.fst)
                                  (Expr.group (sig := [[]]) (fun _ =>
                                     Blocks.cons (fun _ => Expr.jump Js_4.fst ()) Blocks.nil)
                                     fun Js_5 =>
                                   Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ()))
                                     fun p_65 =>
                                   Expr.load i64 (Arg.var p_65.fst) fun ld =>
                                   Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                                     (Arg.var ld, Arg.imm 0, ())) fun p_66 =>
                                   Expr.jnz (Arg.var p_66.fst)
                                     (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ()))
                                        fun p_67 =>
                                      Expr.load i64 (Arg.var p_67.fst) fun ld =>
                                      Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.imm 1, ()))
                                        fun p_68 =>
                                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ()))
                                        fun p =>
                                      Expr.store (Arg.var p_68.fst) (Arg.var p.fst)
                                        (Expr.jump Js_5.fst ()))
                                     (Expr.jump Js_5.fst ()))
                                  (Expr.group (sig := [[]]) (fun _ =>
                                     Blocks.cons (fun _ => Expr.jump Js_4.fst ()) Blocks.nil)
                                     fun Js_5 =>
                                   Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ()))
                                     fun p_65 =>
                                   Expr.load i64 (Arg.var p_65.fst) fun ld =>
                                   Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                                     (Arg.var ld, Arg.imm 0, ())) fun p_66 =>
                                   Expr.jnz (Arg.var p_66.fst)
                                     (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ()))
                                        fun p_67 =>
                                      Expr.load i64 (Arg.var p_67.fst) fun ld =>
                                      Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.imm 1, ()))
                                        fun p_68 =>
                                      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ()))
                                        fun p =>
                                      Expr.store (Arg.var p_68.fst) (Arg.var p.fst)
                                        (Expr.jump Js_5.fst ()))
                                     (Expr.jump Js_5.fst ())))
                               (Expr.jump Js_3.fst ()))
                            (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_large"
                              (Arg.var c.hdr, Arg.var ld_13, Arg.var p_bv, ()) fun p_58 =>
                             Expr.jnz (Arg.var p_58.fst)
                               (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ()))
                                  fun p_59 =>
                                Expr.store (t := i64) (Arg.imm 2) (Arg.var p_59.fst)
                                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_13, ())) fun p_60 =>
                                   Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ()))
                                     fun p_61 =>
                                   Expr.store (Arg.var p_60.fst) (Arg.var p_61.fst)
                                     (Expr.group (sig := [[]]) (fun _ =>
                                        Blocks.cons (fun _ =>
                                          Expr.let_ (Op.mk (.add i64)
                                             (Arg.var c.hdr, Arg.imm 272, ())) fun p_63 =>
                                          Expr.load i64 (Arg.var p_63.fst) fun ld_mcl =>
                                          Expr.let_ (Op.mk (.add i64)
                                            (Arg.var c.hdr, Arg.imm 1144, ())) fun p_64 =>
                                          Expr.store (Arg.var ld_mcl) (Arg.var p_64.fst)
                                            (Expr.call (as := [i64]) (bs := []) "full_clear_ana"
                                               (Arg.var c.hdr, ()) fun _ =>
                                               Expr.ret (Arg.imm 2, ())))
                                        Blocks.nil) fun Js_4 =>
                                      Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                        (Arg.var p_45.fst, Arg.imm 1, ())) fun p_62 =>
                                      Expr.jnz (Arg.var p_62.fst)
                                        (Expr.let_ (Op.mk (.add i64)
                                           (Arg.var c.hdr, Arg.imm 1144, ())) fun p_63 =>
                                         Expr.load i64 (Arg.var p_63.fst) fun ld_19 =>
                                         Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                           (Arg.var ld_19, Arg.var init_res_sz, ())) fun p_64 =>
                                         Expr.jnz (Arg.var p_64.fst)
                                           (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := [])
                                              "full_otfs_subsume"
                                             (Arg.var c.hdr, Arg.var ld_13, Arg.var ld_17,
                                               Arg.var ld_18, Arg.imm false, ()) fun _ =>
                                             Expr.jump Js_4.fst ())
                                           (Expr.jump Js_4.fst ()))
                                        (Expr.jump Js_4.fst ()))))
                               (Expr.jump Js_3.fst ())))
                         (Expr.jump Js_1.fst ()))
                      (Expr.jump Js_1.fst ()))
                   (Expr.jump Js_1.fst ()))
               Blocks.nil) fun Js =>
             Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld_15, Arg.imm 0, ())) fun p_49 =>
             Expr.jnz (Arg.var p_49.fst)
               (Expr.let_ (Op.mk (.sub i64) (Arg.var ld_15, Arg.imm 1, ())) fun p_50 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p =>
                Expr.store (Arg.var p_50.fst) (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.var p_50.fst, ())))
               (Expr.jump Js.fst (Arg.var ld_15, ())))
            (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
             Expr.ret (Arg.imm 0, ())))) m

private theorem ded_unfocus_tmp_dec {c : FullCfg} {ext_cur : List (BitVec 64)}
    {s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64} {new_tc : Nat}
    (hnew : new_tc = s_cur.core.tmp_cnt - 1)
    (hm : (FullMem c { s_cur with core := { s_cur.core with tmp_cnt := new_tc } } ⋆
        (m6ExtMem (m6ExtAddr c.hdr) ext_cur ⋆ R)) m) :
    (FullM6HdrMem c ext_cur { s_cur with
        core := { s_cur.core with tmp_cnt := s_cur.core.tmp_cnt - 1 } } ⋆ R) m := by
  subst hnew
  exact fullM6HdrMem_unfocus_full hm

private theorem ded_loop_rsn_let3 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {m : Mem 64} {sv : BitVec 32} {k : Val i32 → Expr Val Cont rs}
    (h : wp Γ Q X (Expr.let_ (Op.mk (.zext 32 64) (Arg.var sv, ())) fun p_41 =>
      Expr.let_ (Op.mk (.mul i64) (Arg.var p_41.fst, Arg.imm 4, ())) fun p_42 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.pReason, Arg.var p_42.fst, ())) fun p_43 =>
        Expr.load i32 (Arg.var p_43.fst) k) m) :
    wp Γ Q X (Expr.load i32 (Arg.var (c.pReason + BitVec.setWidth 64 sv * 4)) k) m := by
  have h2 : ∀ (P : Prop), (if i64.hasFloat = true then False else P) = P :=
    fun P => propext ⟨fun h => by simpa using h, fun h => by simpa using h⟩
  rw [wp_let] at h; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2] at h; have h := h.2
  rw [wp_let] at h; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2] at h; rw [h2] at h
  rw [wp_let] at h; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2] at h; rw [h2] at h
  exact h

theorem full_deduce_1uip_m6_hdr_loop_wp (Γ : Env)
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" Spec.s13AnalyzeRsnHdrSpec)
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    (hLoopRsn : DeduceLoopRsnStep Γ) :
    ∀ a m Q X, Spec.fullDeduce1uipM6HdrSpec a m Q X →
      Func.wp Γ Src.Deduce.full_deduce_1uip_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut0, ext0, s0, R, rfl, hcfg, hext0, hcut0, hcur_pos, hconfl0, hm, hPost⟩
  have hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m' :=
    fun ext' s' m' he' hl' hcv' hfu' hws2' hot' hm' =>
      hPost 0#64 ext' s' m' he' hl' (Or.inl rfl) hcv' hfu' hws2'
        (fun h => by cases h) (fun _ => hot') (fun h => by cases h) (fun h => by cases h) hm'
  have hQ20 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → F0.Unsat → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_level ≤ s0.core.cur_level → s'.core.dense_mode = s0.core.dense_mode →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (20#64, ()) m' :=
    fun ext' s' m' he' hl' hcv' hfu' hws2' hu' hot' hcl' hdm' hm' =>
      hPost 20#64 ext' s' m' he' hl' (Or.inr (Or.inr (Or.inr rfl))) hcv' hfu' hws2'
        (fun _ => ⟨hu', hot', hcl', hdm'⟩) (fun h => by cases h)
        (fun h => by cases h) (fun h => by cases h) hm'
  have hQ1 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_level = s0.core.cur_level →
      1 ≤ s'.core.tmp_len → s'.core.tmp_len ≤ s'.core.cur_vars →
      (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup →
      (∀ k < s'.core.tmp_len,
        (s'.core.tmp[k]?.getD 0#32).toNat < 2 * s'.core.cur_vars ∧
        s'.core.vals[(s'.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) →
      (∀ k, 1 ≤ k → k < s'.core.tmp_len →
        0 < (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
        (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s'.core.cur_level) →
      (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (1#64, ()) m' :=
    fun ext' s' m' he' hl' hcv' hfu' hws2' hot' hcl' ht1 htl hnd hv hlow hl0 hent hm' =>
      hPost 1#64 ext' s' m' he' hl' (Or.inr (Or.inl rfl)) hcv' hfu' hws2'
        (fun h => by cases h) (fun h => by cases h)
        (fun _ => ⟨hot', hcl', ht1, htl, hnd, hv, hlow, hl0, hent⟩)
        (fun h => by cases h) hm'
  have hQ2 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m' :=
    fun ext' s' m' cut' he' hl' hle' hcut' _ hcv' hfu' hws2' hcl' hcf' hm' =>
      hPost 2#64 ext' s' m' he' hl' (Or.inr (Or.inr (Or.inl rfl))) hcv' hfu' hws2'
        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
        (fun _ => ⟨cut', hle', hcut', hcl', hcf'⟩) hm'
  unfold Func.wp Src.Deduce.full_deduce_1uip_m6_hdr_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  d_hsteps_nogrp
  let s_init : FullState :=
    { core := { s0.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 }
      scratch := { s0.scratch with ant_sz := 0#64, res_sz := 0#64 } }
  refine wp_join_group (ts := [.bool])
    (fun (ok_s, ()) m_sd => ∃ ext1 s1,
      M6HdrExtOk ext1 ∧ s1.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut0 s1.core ∧
      FullAnaMarksCov c s1 ∧ FullArenaVarsNodup s1 ∧ FullExtScratchPres s0 s1 ∧
      s1.scratch.work_stk2 = s0.scratch.work_stk2 ∧
      fullArenaClauseRefs s1 = fullArenaClauseRefs s0 ∧ FullDeduceStaticEq s0.core s1.core ∧
      s1.core.confl_type = s0.core.confl_type ∧ s1.core.confl_ref = s0.core.confl_ref ∧
      (ok_s = true → FullDeduceStateInv c F0 F_cur cut0 s1.core.trail_end s0 s1) ∧
      (FullM6HdrMem c ext1 s1 ⋆ R) m_sd) ?_ ?_
  · rintro Js ⟨ok_s, ⟨⟩⟩ m_sd
      ⟨ext1, s1, hext1, hlen1, hw1, hcov1, hnd1, hextp1, hws2_1, hrefs1, hstat1,
        hc_t, hc_r, hinv1, hm1⟩
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    d_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun _ m_u => ∃ ext_u s_u,
        M6HdrExtOk ext_u ∧ s_u.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut0 s_u.core ∧
        FullAnaMarksCov c s_u ∧ FullArenaVarsNodup s_u ∧ FullExtScratchPres s0 s_u ∧
        s_u.scratch.work_stk2 = s0.scratch.work_stk2 ∧
        fullArenaClauseRefs s_u = fullArenaClauseRefs s0 ∧ FullDeduceStaticEq s0.core s_u.core ∧
        (ok_s = true →
          FullDeduceStateInv c F0 F_cur cut0 s_u.core.trail_end s0 s_u ∧ s_u.core.tmp_cnt = 0) ∧
        (FullM6HdrMem c ext_u s_u ⋆ R) m_u) ?_ ?_
    · rintro Js_u _ m_u
        ⟨ext_u, s_u, hextu, hlenu, hwu, hcovu, hndu, hextpu, hws2u, hrefsu, hstatu, hinvu, hmu⟩
      exact deduce_seed_unsat_or_ret0_wp hClear hcut0 hextu hlenu hwu hcovu hndu hextpu hws2u
        hrefsu hstatu hinvu hmu hQ0 hQ20
    · intro Js_u hJs_u
      d_hsteps_nogrp
      · have hokt : ok_s = true := by assumption
        subst hokt
        have htc_lt64 : s1.core.tmp_cnt < 2 ^ 64 := by
          have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this
          have htc := (hinv1 rfl).tc_eq
          have hle : (fullCurTrailIdxs s1.core s1.core.mrk s1.core.trail_end).length ≤
              s1.core.trail_end := by
            unfold fullCurTrailIdxs
            exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq List.length_range)
          have := hlen1.core_ok.trail_end_le; omega
        have htc0 : s1.core.tmp_cnt = 0 := by
          have hb : BitVec.ofNat 64 s1.core.tmp_cnt = 0#64 := by assumption
          have ht := congrArg BitVec.toNat hb
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htc_lt64] at ht; exact ht
        exact hJs_u () _ ⟨ext1, s1, hext1, hlen1, hw1, hcov1, hnd1, hextp1, hws2_1, hrefs1,
          hstat1, fun _ => ⟨hinv1 rfl, htc0⟩, fullM6HdrMem_unfocus_full hm1f⟩
      · have hokt : ok_s = true := by assumption
        subst hokt
        have hm1_u := fullM6HdrMem_unfocus_full hm1f
        have hcl32 : s1.core.cur_level < 2 ^ 32 := by
          have := hw1.cur_level_le; have := hlen1.core_ok.trail_end_le
          have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
        have hte_lt64 : s1.core.trail_end < 2 ^ 64 := by
          have := hlen1.core_ok.trail_end_le; have := hlen1.core_ok.cur_vars_le
          have := c.hmaxv; unfold dimacsBound at this; omega
        have hcv_lt64 : s1.core.cur_vars < 2 ^ 64 := by
          have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
        have hlvl_tr : BitVec.truncate 32 (BitVec.ofNat 64 s1.core.cur_level) =
            BitVec.ofNat 32 s1.core.cur_level :=
          BitVec.eq_of_toNat_eq (by
            rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
              bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt hcl32, bv32_ofNat_toNat hcl32])
        d_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64, i32, i64])
          (fun (_, _, uip_v, _) m_e => ∃ cut_e ext_e s_e,
            M6HdrExtOk ext_e ∧ s_e.LengthsOk c ∧
            FullWitnessCutInv c F0 F_cur cut_e s_e.core ∧ FullAnaMarksCov c s_e ∧
            FullArenaVarsNodup s_e ∧ FullExtScratchPres s0 s_e ∧
            s_e.scratch.work_stk2 = s0.scratch.work_stk2 ∧
            fullArenaClauseRefs s_e = fullArenaClauseRefs s0 ∧
            FullDeduceStaticEq s0.core s_e.core ∧
            (uip_v ≠ 0xFFFFFFFF#32 → ∃ (cut_p idx' : Nat) (s_prev : FullState) (p_bv : BitVec 32),
              FullDeduceStateInv c F0 F_cur cut_p (idx' + 1) s0 s_prev ∧
              s_e.core.cur_vars = s_prev.core.cur_vars ∧
              s_e.core.cur_level = s_prev.core.cur_level ∧
              s_e.core.trail_end = s_prev.core.trail_end ∧
              s_e.core.trl = s_prev.core.trl ∧ s_e.core.lvl = s_prev.core.lvl ∧
              s_e.core.vals = s_prev.core.vals ∧ s_e.core.mrk = s_prev.core.mrk ∧
              s_e.core.tmp = s_prev.core.tmp ∧ s_e.core.tmp_len = s_prev.core.tmp_len ∧
              idx' < s_prev.core.trail_end ∧
              (s_prev.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
              uip_v = p_bv ^^^ 1#32 ∧ s_prev.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
              (s_prev.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s_prev.core.cur_level ∧
              (fullCurTrailIdxs s_prev.core s_prev.core.mrk idx').length = 0) ∧
            (FullM6HdrMem c ext_e s_e ⋆ R) m_e) ?_ ?_
        · rintro Js_e ⟨_, _, uip_v, _, ⟨⟩⟩ m_e
            ⟨cut_e, ext_e, s_e, hext_e, hlen_e, hw_e, hcov_e, hnd_e, hextp_e, hws2_e, hrefs_e,
              hstat_e, hgood_e, hm_e⟩
          exact ded_uip_exit_wp hClear hcut0 hext_e hlen_e hw_e hcov_e hnd_e hextp_e hws2_e
            hrefs_e hstat_e hgood_e hm_e hQ0 hQ1
        · intro Js_e hJs_e
          d_hsteps_nogrp
          refine wp_loop_inv (ts := [i64, i64, i64])
            (DeduceLoopInv c F0 F_cur cut0 s0 R) (fun ys _ => ys.2.1.toNat) ?_ ?_
          · intro Js_l hL
            exact hL _ _
              ⟨cut0, s1.core.trail_end, ext1, s1, rfl, rfl, hw1.cut_le, Nat.le_refl _,
                by rw [hstat1.te]; simp, hext1, hinv1 rfl, fun _ => ⟨rfl, hc_t, hc_r⟩, hm1_u⟩
          · rintro Js_l ⟨tcnt_v, idx_v, steps_v, ⟨⟩⟩ m_l
              ⟨cut_cur, idx, ext_cur, s_cur, rfl, rfl, hcut_le, hidx_le, hst_bd, hext_c, hs_c,
                hstep0, hm_l⟩ hL
            have hte_c : s_cur.core.trail_end < 2 ^ 64 := by
              rw [hs_c.stat.te, ← hstat1.te]; exact hte_lt64
            have hcv_c : s_cur.core.cur_vars < 2 ^ 64 := by
              rw [hs_c.stat.cv, ← hstat1.cv]; exact hcv_lt64
            have hcl_c : s_cur.core.cur_level < 2 ^ 32 := by
              rw [hs_c.stat.cl, ← hstat1.cl]; exact hcl32
            have hidx_64 : (BitVec.ofNat 64 idx).toNat = idx :=
              bv64_ofNat_toNat (by omega)
            have htc_c : s_cur.core.tmp_cnt < 2 ^ 64 := by
              have := hs_c.tc_eq
              have hle : (fullCurTrailIdxs s_cur.core s_cur.core.mrk idx).length ≤ idx := by
                unfold fullCurTrailIdxs
                exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq List.length_range)
              omega
            d_hsteps_nogrp
            · have hidx0 : idx = 0 := by
                have hc' : BitVec.ofNat 64 idx = 0#64 := by assumption
                have ht := congrArg BitVec.toNat hc'
                rwa [hidx_64] at ht
              exact ded_clear_ret0_cut_wp hClear hcut0 hext_c hs_c.len hs_c.hw hs_c.cov
                hs_c.nd hs_c.ext hs_c.ws2 hs_c.hrefs hs_c.stat hm_l hQ0
            ·
                have htc_pos : 0 < s_cur.core.tmp_cnt := by
                  have hc' : (0#64 : BitVec 64).toNat <
                      (BitVec.ofNat 64 s_cur.core.tmp_cnt).toNat := by assumption
                  rwa [bv64_ofNat_toNat htc_c] at hc'
                have hidx_pos : 0 < idx := by
                  rcases Nat.eq_zero_or_pos idx with rfl | hp
                  · exact absurd rfl (by assumption : BitVec.ofNat 64 0 ≠ 0#64)
                  · exact hp
                let idx' := idx - 1
                have hidx_te : idx' < s_cur.core.trail_end := by omega
                have hidx'_bv : BitVec.ofNat 64 idx - 1#64 = BitVec.ofNat 64 idx' := by
                  apply BitVec.eq_of_toNat_eq
                  simp [bv64_ofNat_toNat (by omega : idx < 2 ^ 64),
                    bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
                  omega
                have hidx'_nat : (BitVec.ofNat 64 idx - 1#64).toNat = idx' := by
                  rw [hidx'_bv, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
                have hidx'_lt : (BitVec.ofNat 64 idx - 1#64).toNat <
                    (BitVec.ofNat 64 idx).toNat := by
                  rw [hidx'_nat, hidx_64]; omega
                have hidx'_trl : (BitVec.ofNat 64 idx - 1).toNat < s_cur.core.trl.length := by
                  rw [show (BitVec.ofNat 64 idx - 1).toNat = idx' from hidx'_nat,
                    hs_c.len.core_ok.trl_len]
                  have := hs_c.len.core_ok.trail_end_le
                  have := hs_c.len.core_ok.cur_vars_le; omega
                let p_bv : BitVec 32 := s_cur.core.trl[idx']'(by
                  rw [hs_c.len.core_ok.trl_len]; have := hs_c.len.core_ok.trail_end_le
                  have := hs_c.len.core_ok.cur_vars_le; omega)
                have hp_get : (s_cur.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
                  rw [List.getElem?_eq_getElem, Option.getD_some]
                have hp_lt : p_bv.toNat < 2 * s_cur.core.cur_vars :=
                  hp_get ▸ hs_c.hw.trail_lits_lt idx' hidx_te
                have hidx_succ : idx' + 1 = idx := by omega
                have hsub_idx :
                    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64 = idx' := by
                  rw [← hidx'_nat]
                  simp [BitVec.toNat_sub, bv64_ofNat_toNat (by omega : idx < 2 ^ 64)]
                have hsub_trl :
                    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64 <
                      s_cur.core.trl.length := by
                  rw [hsub_idx, hs_c.len.core_ok.trl_len]
                  have := hs_c.len.core_ok.trail_end_le
                  have := hs_c.len.core_ok.cur_vars_le; omega
                have hsub_mrk :
                    s_cur.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                      idx) % 2 ^ 64].toNat / 2 < s_cur.core.mrk.length := by
                  have heq : s_cur.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                      idx) % 2 ^ 64] = p_bv := by
                    simp only [hsub_idx, p_bv]
                  rw [heq, hs_c.len.core_ok.mrk_len]
                  have := hs_c.len.core_ok.cur_vars_le; omega
                have hsub_lvl :
                    s_cur.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                      idx) % 2 ^ 64].toNat / 2 < s_cur.core.lvl.length := by
                  rw [hs_c.len.core_ok.lvl_len, ← hs_c.len.core_ok.mrk_len]; exact hsub_mrk
                refine wp_m6Hdr_focus_frame hm_l fun hm_lf => ?_
                d_hsteps_nogrp
                · exfalso
                  have hcv_eq : s1.core.cur_vars = s_cur.core.cur_vars :=
                    hstat1.cv.trans hs_c.stat.cv.symm
                  have hge : s_cur.core.cur_vars ≤ p_bv.toNat / 2 := by
                    have heq : s_cur.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                        idx) % 2 ^ 64] = p_bv := by
                      simp only [hsub_idx, p_bv]
                    have hc_g : s1.core.cur_vars % 2 ^ 64 ≤
                        s_cur.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
                          idx) % 2 ^ 64].toNat / 2 := by assumption
                    rw [hcv_eq, Nat.mod_eq_of_lt hcv_c, heq] at hc_g
                    exact hc_g
                  omega
                · have hml_u := fullM6HdrMem_unfocus_full hm_lf
                  refine wp_join_group (ts := [i64, i32, i64])
                    (fun (tc_n, _, st_n, ()) m_n => ∃ cut_n ext_n s_n,
                      tc_n = BitVec.ofNat 64 s_n.core.tmp_cnt ∧
                      cut_n ≤ s_n.core.trail_end ∧ M6HdrExtOk ext_n ∧
                      FullDeduceStateInv c F0 F_cur cut_n idx' s0 s_n ∧
                      (st_n.toNat + idx' ≤ s0.core.trail_end) ∧
                      (st_n = 0#64 → cut_n = cut0 ∧
                        s_n.core.confl_type = s0.core.confl_type ∧
                        s_n.core.confl_ref = s0.core.confl_ref) ∧
                      (FullM6HdrMem c ext_n s_n ⋆ R) m_n) ?_ ?_
                  · rintro Js_2 ⟨tc_n, _, st_n, _, ⟨⟩⟩ m_n
                      ⟨cut_n, ext_n, s_n, htc_n, hcut_n, hext_n, hs_n, hst_n_bd, hst_n, hm_n⟩
                    d_hsteps_nogrp
                    exact hL _ _ hidx'_lt
                      ⟨cut_n, idx', ext_n, s_n, htc_n, hidx'_bv, hcut_n,
                        Nat.le_of_lt (by rw [hs_n.stat.te, ← hs_c.stat.te]; exact hidx_te),
                        hst_n_bd, hext_n, hs_n, hst_n, hm_n⟩
                  · intro Js_2 hJs_2
                    have hp_bv_eq : s_cur.core.trl[(BitVec.ofNat 64 idx - 1).toNat] = p_bv := by
                      simp only [show (BitVec.ofNat 64 idx - 1).toNat = idx' from hidx'_nat, p_bv]
                    have hpv_nat : (BitVec.setWidth 64
                        (s_cur.core.trl[(BitVec.ofNat 64 idx - 1).toNat] >>>
                          OfNat.ofNat 1)).toNat = p_bv.toNat / 2 := by
                      rw [hp_bv_eq, BitVec.toNat_setWidth,
                        show (p_bv >>> OfNat.ofNat 1) = p_bv >>> 1#32 from rfl,
                        DeduceTactics.ded_bv32_lshr_1,
                        Nat.mod_eq_of_lt (by omega : p_bv.toNat / 2 < 2 ^ 64)]
                    have hpv_mrk : (BitVec.setWidth 64
                        (s_cur.core.trl[(BitVec.ofNat 64 idx - 1).toNat] >>>
                          OfNat.ofNat 1)).toNat < s_cur.core.mrk.length := by
                      rw [hpv_nat, hs_c.len.core_ok.mrk_len]
                      have := hs_c.len.core_ok.cur_vars_le; omega
                    have hpv_lvl : (BitVec.setWidth 64
                        (s_cur.core.trl[(BitVec.ofNat 64 idx - 1).toNat] >>>
                          OfNat.ofNat 1)).toNat < s_cur.core.lvl.length := by
                      rw [hs_c.len.core_ok.lvl_len, ← hs_c.len.core_ok.mrk_len]; exact hpv_mrk
                    have hcl_eq : s1.core.cur_level = s_cur.core.cur_level :=
                      hstat1.cl.trans hs_c.stat.cl.symm
                    have hlvl_bv32 : BitVec.setWidth 32 (BitVec.ofNat 64 s1.core.cur_level) =
                        BitVec.ofNat 32 s_cur.core.cur_level := by
                      rw [← BitVec.truncate_eq_setWidth, hlvl_tr, hcl_eq]
                    have mk_hm_p : ¬s_cur.core.mrk[s_cur.core.trl[(2 ^ 64 -
                          BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64].toNat / 2] = 0#8 →
                        s_cur.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 := fun hc_m => by
                      rw [List.getElem?_eq_getElem (by
                        rw [hs_c.len.core_ok.mrk_len]
                        have := hs_c.len.core_ok.cur_vars_le; omega), Option.getD_some]
                      simpa only [hsub_idx, p_bv] using hc_m
                    have mk_hl_p : s_cur.core.lvl[s_cur.core.trl[(2 ^ 64 -
                          BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64].toNat / 2] =
                        BitVec.setWidth 32 (BitVec.ofNat 64 s1.core.cur_level) →
                        (s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat =
                          s_cur.core.cur_level := fun hc_l => by
                      have heq : s_cur.core.lvl[p_bv.toNat / 2]? =
                          some (BitVec.ofNat 32 s_cur.core.cur_level) := by
                        rw [List.getElem?_eq_getElem (by
                          rw [hs_c.len.core_ok.lvl_len]
                          have := hs_c.len.core_ok.cur_vars_le; omega)]
                        exact congrArg some (by simpa only [hsub_idx, p_bv, hlvl_bv32] using hc_l)
                      rw [heq, Option.getD_some, bv32_ofNat_toNat hcl_c]
                    have htc1_bv : (BitVec.ofNat 64 s_cur.core.tmp_cnt - 1#64).toNat =
                        s_cur.core.tmp_cnt - 1 := by
                      rw [BitVec.toNat_sub, bv64_ofNat_toNat htc_c,
                        show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
                    refine wp_m6Hdr_focus_frame hml_u fun hmf_u => ?_
                    d_hsteps_nogrp
                    · have hm_p := mk_hm_p (by assumption)
                      have hl_p := mk_hl_p (by assumption)
                      let sl : FullState :=
                        { s_cur with
                          core := { s_cur.core with tmp_cnt := s_cur.core.tmp_cnt - 1 } }
                      have htc1 : s_cur.core.tmp_cnt = 1 := by
                        have hb : BitVec.ofNat 64 s_cur.core.tmp_cnt - 1#64 = 0#64 := by
                          assumption
                        have ht := congrArg BitVec.toNat hb
                        rw [htc1_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at ht; omega
                      have hlen_sl : sl.LengthsOk c :=
                        ⟨{ hs_c.len.core_ok with }, hs_c.len.scratch_ok⟩
                      have hw_sl : FullWitnessCutInv c F0 F_cur cut_cur sl.core :=
                        deduce_same_core_cut hs_c.hw _ _ _ _ _
                      have hcov_sl : FullAnaMarksCov c sl := hs_c.cov
                      have hnd_sl : FullArenaVarsNodup sl :=
                        ded_arenaVarsNodup_same_core_arena hs_c.nd rfl rfl
                      have hstat_sl : FullDeduceStaticEq s0.core sl.core :=
                        ⟨hs_c.stat.cv, hs_c.stat.cl, hs_c.stat.te, hs_c.stat.trl,
                          hs_c.stat.lvl, hs_c.stat.rsns, hs_c.stat.vals, hs_c.stat.fuel,
                          hs_c.stat.dm, hs_c.stat.lm⟩
                      have hm_tr :
                          s_cur.core.mrk[(s_cur.core.trl[idx']?.getD 0#32).toNat / 2]?.getD
                            0#8 ≠ 0#8 := by rwa [hp_get]
                      have hl_tr :
                          (s_cur.core.lvl[(s_cur.core.trl[idx']?.getD 0#32).toNat / 2]?.getD
                            0#32).toNat = s_cur.core.cur_level := by rwa [hp_get]
                      have hct0 :
                          (fullCurTrailIdxs s_cur.core s_cur.core.mrk idx').length = 0 := by
                        have hsuc :=
                          congrArg List.length (fullCurTrailIdxs_succ_true hm_tr hl_tr)
                        simp only [List.length_append, List.length_singleton] at hsuc
                        have := hs_c.tc_eq; rw [← hidx_succ, htc1] at this; omega
                      have huip_eq :
                          s_cur.core.trl[(BitVec.ofNat 64 idx - 1).toNat] ^^^ 1 =
                            p_bv ^^^ 1#32 := by
                        simp only [hp_bv_eq]; rfl
                      have hm_sl : (FullM6HdrMem c ext_cur sl ⋆ R) _ :=
                        ded_unfocus_tmp_dec htc1_bv ‹_›
                      exact hJs_e (_, _, _, _, ()) _
                        ⟨cut_cur, ext_cur, sl, hext_c, hlen_sl, hw_sl, hcov_sl, hnd_sl,
                          hs_c.ext, hs_c.ws2, hs_c.hrefs, hstat_sl,
                          fun _ => ⟨cut_cur, idx', s_cur, p_bv, hidx_succ ▸ hs_c,
                            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                            hidx_te, hp_get, huip_eq, hm_p, hl_p, hct0⟩,
                          hm_sl⟩
                    · have hm_p := mk_hm_p (by assumption)
                      have hl_p := mk_hl_p (by assumption)
                      let sl : FullState :=
                        { s_cur with
                          core := { s_cur.core with tmp_cnt := s_cur.core.tmp_cnt - 1 } }
                      have hte0_64 : s0.core.trail_end < 2 ^ 64 := hs_c.stat.te ▸ hte_c
                      have hstp1 : (steps_v + 1#64).toNat = steps_v.toNat + 1 := by
                        dsimp only at hst_bd
                        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      have hm_sl : (FullM6HdrMem c ext_cur sl ⋆ R) _ :=
                        ded_unfocus_tmp_dec htc1_bv ‹_›
                      have hLoop := hLoopRsn (s1 := s_cur) (sl := sl) (X := X)
                        (init_res_sz := s1.scratch.res_sz) (p_bv := p_bv)
                        rfl hcfg hcut0 hconfl0 hcur_pos hext_c
                        (hidx_succ ▸ hs_c) hidx_te hp_get hm_p hl_p rfl rfl hstep0 hm_sl
                        hQ0 hQ2 (fun cut_j ext_j s_j m_j hcj hej hsj hmj =>
                          hJs_2 (_, _, _, ()) m_j
                            ⟨cut_j, ext_j, s_j, rfl, hcj, hej, hsj,
                              by dsimp only at hst_bd ⊢; rw [hstp1]; omega,
                              fun h => by
                                have ht := congrArg BitVec.toNat h
                                rw [hstp1, show (0#64 : BitVec 64).toNat = 0 from rfl] at ht
                                omega,
                              hmj⟩)
                      have hLoop' := ded_loop_rsn_let3 hLoop; rw [hp_bv_eq]; exact hLoop'
                    · have hc_nl : ¬s_cur.core.lvl[s_cur.core.trl[(2 ^ 64 -
                          BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64].toNat / 2] =
                          BitVec.setWidth 32 (BitVec.ofNat 64 s1.core.cur_level) := by
                        assumption
                      have hnot : ¬ (s_cur.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                          (s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat =
                            s_cur.core.cur_level) := fun ⟨_, hcl⟩ => by
                        have hlt_l : p_bv.toNat / 2 < s_cur.core.lvl.length := by
                          rw [hs_c.len.core_ok.lvl_len]
                          have := hs_c.len.core_ok.cur_vars_le; omega
                        have hl_eq : s_cur.core.lvl[p_bv.toNat / 2] =
                            BitVec.ofNat 32 s_cur.core.cur_level :=
                          BitVec.eq_of_toNat_eq (by
                            have hget_l : s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32 =
                                s_cur.core.lvl[p_bv.toNat / 2] := by
                              rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                            rw [bv32_ofNat_toNat hcl_c, ← hget_l]; exact hcl)
                        apply hc_nl
                        simpa only [hsub_idx, p_bv, hlvl_bv32] using hl_eq
                      exact hJs_2 (_, _, _, ()) m_l
                        ⟨cut_cur, ext_cur, s_cur, rfl, hcut_le, hext_c,
                          ded_stateInv_skip (hidx_succ ▸ hs_c) hp_get hnot,
                          by dsimp only at hst_bd; omega, hstep0, hm_l⟩
                    · have hc_zm : s_cur.core.mrk[s_cur.core.trl[(2 ^ 64 -
                          BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64].toNat / 2] = 0#8 := by
                        assumption
                      have hnot : ¬ (s_cur.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                          (s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat =
                            s_cur.core.cur_level) := fun ⟨hm_k, _⟩ => by
                        apply hm_k
                        rw [List.getElem?_eq_getElem (by
                          rw [hs_c.len.core_ok.mrk_len]
                          have := hs_c.len.core_ok.cur_vars_le; omega), Option.getD_some]
                        simpa only [hsub_idx, p_bv] using hc_zm
                      exact hJs_2 (_, _, _, ()) m_l
                        ⟨cut_cur, ext_cur, s_cur, rfl, hcut_le, hext_c,
                          ded_stateInv_skip (hidx_succ ▸ hs_c) hp_get hnot,
                          by dsimp only at hst_bd; omega, hstep0, hm_l⟩
            · exact hJs_e (_, _, _, _, ()) m_l
                ⟨cut_cur, ext_cur, s_cur, hext_c, hs_c.len, hs_c.hw, hs_c.cov, hs_c.nd,
                    hs_c.ext, hs_c.ws2, hs_c.hrefs, hs_c.stat,
                    fun h => absurd rfl h, hm_l⟩
      · exact hJs_u () _ ⟨ext1, s1, hext1, hlen1, hw1, hcov1, hnd1, hextp1, hws2_1, hrefs1,
          hstat1, fun h => absurd h (by rw [‹ok_s = false›]; decide),
          fullM6HdrMem_unfocus_full hm1f⟩
  · intro Js hJs
    exact ded_seed_confl_wp hLit hRsn hcfg hcut0 hext0 hcur_pos hconfl0 rfl rfl
      (fullM6HdrMem_unfocus_full (s := s_init) ‹_›)
      fun ok1 ext1 s1 ml he1 hl1 hw1 hc1 hnd1 hext1 hws2_1 hrefs1 hstat1 hct1 hcr1 hinv1 hm1 =>
        hJs (ok1, ()) ml ⟨ext1, s1, he1, hl1, hw1, hc1, hnd1, hext1, hws2_1, hrefs1, hstat1,
          hct1, hcr1, hinv1, hm1⟩

end LeanQbe.T.Examples.Kissat.Proof.Deduce
