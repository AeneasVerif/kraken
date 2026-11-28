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
# Kissat 1-UIP Loop Reason-Step & OTFS Sub-Proof (`Proof.Deduce.WpDeduce3a`)

Splits `deduce_otfs_ret2_subsume_wp` and `deduce_loop_rsn_wp` from `WpDeduce3` so every file in
`Proof/Deduce/` remains well below `1,500` LOC (`public section`, `0` legacy imports, `0`
`import all`, `0` `@[expose]` on theorems/lemmas/sections).
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

/-! ## 1. Parametric Call Wrappers & OTFS Helper Invariants -/

private theorem ded_rsn_hdr_wp {Γ : Env}
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" Spec.s13AnalyzeRsnHdrSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {rsn skip_var : BitVec 32} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcov : FullAnaMarksCov c s)
    (htl : s.core.tmp_len ≤ s.core.cur_vars)
    (htc : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64)
    (href : rsn ≠ 0xFFFFFFFF#32 → rsn &&& 0x80000000#32 = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' mclr' : List (BitVec 32))
      (tc' tl' mcl' : Nat) (arena' : List (BitVec 32)) (sc' : FullScratch)
      (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl',
                                mrk := mrk', tmp := tmp', min_clr := mclr', arena := arena' }
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core →
      FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 → s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars →
      s.core.tmp_cnt ≤ tc' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ i < s.core.tmp_len, tmp'[i]? = s.core.tmp[i]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length →
      sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter
        fun w => decide (s.core.mrk[w]?.getD 0#8 = 0#8) &&
          decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_rsn_m6_hdr"
      (Arg.var c.hdr, Arg.var rsn, Arg.var skip_var, ()) k) m := by
  refine wp_call_of_spec _ _ (hRsn _ m _ X ?_)
  exact ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hw, hcov, htl, htc, href, hm,
    fun ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hm' =>
      hk ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
        h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hm'⟩

private theorem ded_otfs_subsume_imm_wp {Γ : Env}
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {new_confl_arg : Arg Val i32} {new_confl : BitVec 32}
    {old_ctype old_cref : BitVec 64} {to_bin : Bool}
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs}
    (hnc : new_confl_arg.val = new_confl)
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s)
    (hold : old_ctype = 2#64 → old_cref ≠ 0xFFFFFFFF#64 →
      old_cref.toNat ∈ fullArenaClauseRefs s ∧
      (to_bin = false → new_confl.toNat ∈ fullArenaClauseRefs s) ∧
      ∀ idx < s.core.trail_end,
        let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        idx < cut ∨ (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level →
        rsn ≠ 0xFFFFFFFF#32 → rsn &&& 0x80000000#32 = 0#32 → rsn.toNat ≠ old_cref.toNat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (arena' : List (BitVec 32)) (ag' ni' nr' : BitVec 64) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with arena_garbage := ag', num_irred := ni', num_redundant := nr',
                                arena := arena' } }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullArenaVarsNodup s' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
        ((old_ctype = 2#64 → r ≠ old_cref.toNat) →
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r)) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := []) "full_otfs_subsume"
      (Arg.var c.hdr, new_confl_arg, Arg.var old_ctype, Arg.var old_cref,
        Arg.imm to_bin, ()) k) m := by
  refine wp_call_of_spec _ _ (hSub _ m _ X ?_)
  refine ⟨c, F0, F_cur, cut, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hw, hnd,
    fun h1 h2 => ?_, fullM6HdrMem_focus_full hm,
    fun arena' ag' ni' nr' m' h1 h2 h3 h4 h5 hm' => ?_⟩
  · have h_ok := hold h1 h2
    rwa [← hnc] at h_ok
  · exact hk arena' ag' ni' nr' m' h1 h2 h3 h4 h5 (fullM6HdrMem_unfocus_full hm')

private theorem ded_inv_otfs_fail {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut_cur idx' : Nat} {s0 s3 s' : FullState}
    (hs3 : FullDeduceStateInv c F0 F_cur cut_cur idx' s0 s3)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessCutInv c F0 F_cur idx' s'.core)
    (hnd' : FullArenaVarsNodup s') (hext' : FullExtScratchPres s3 s')
    (hws2' : s'.scratch.work_stk2 = s3.scratch.work_stk2)
    (hws1' : s'.scratch.work_stk1 = s3.scratch.work_stk1)
    (hres' : s'.scratch.res_sz = s3.scratch.res_sz)
    (hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s3)
    (hstat' : FullDeduceStaticEq s3.core s'.core)
    (hmrk' : s'.core.mrk = s3.core.mrk) (htmp' : s'.core.tmp = s3.core.tmp)
    (htc' : s'.core.tmp_cnt = s3.core.tmp_cnt) (htl' : s'.core.tmp_len = s3.core.tmp_len)
    (hmcl' : s'.core.min_clr_len = s3.core.min_clr_len) :
    FullDeduceStateInv c F0 F_cur idx' idx' s0 s' := by
  have hcov' : FullAnaMarksCov c s' := by
    have hcov3 := hs3.cov; unfold FullAnaMarksCov at hcov3 ⊢
    rw [hstat'.cv, hmrk', hmcl', hws1']; exact hcov3
  have hlow' : FullLowerInv c s'.core s'.core.tmp s'.core.mrk s'.core.tmp_len := by
    have hl3 := hs3.low; unfold FullLowerInv at hl3 ⊢
    rw [hstat'.cv, hstat'.vals, hstat'.lvl, hstat'.cl, htmp', hmrk', htl']; exact hl3
  have hmcov' : FullMarksCov s'.core s'.core.tmp s'.core.mrk s'.core.tmp_len := by
    have hm3 := hs3.mcov; unfold FullMarksCov at hm3 ⊢
    rw [hstat'.cv, hstat'.lvl, hstat'.cl, htmp', hmrk', htl']; exact hm3
  have hcm' : FullCurMarksBelow idx' s'.core s'.core.mrk idx' := fun _ hj _ _ => hj
  have htc_eq' : s'.core.tmp_cnt = (fullCurTrailIdxs s'.core s'.core.mrk idx').length := by
    have h3 := hs3.tc_eq
    unfold fullCurTrailIdxs at h3 ⊢
    rw [htc', hmrk', hstat'.trl, hstat'.lvl, hstat'.cl]; exact h3
  have hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s'.core s'.core.tmp s'.core.mrk s'.core.tmp_len idx')) := by
    have h3 := hs3.ent
    unfold fullActiveResolvent fullCurLits fullCurTrailIdxs fullLowerLits at h3 ⊢
    rw [hstat'.trl, hstat'.lvl, hstat'.cl, htmp', hmrk', htl']; exact h3
  exact ⟨hlen', hw', hcov', fullExtScratchPres_trans hs3.ext hext', hws2'.trans hs3.ws2,
    hnd', hrefs'.trans hs3.hrefs, hs3.stat.trans hstat', htl' ▸ hs3.tl_ge,
    by rw [htl', hstat'.cv]; exact hs3.tl_cv, htc_eq', hlow', hmcov', hcm', hent',
    by rw [hres', htl', htc']; exact hs3.res_eq⟩

/-! ## 2. Shared OTFS Exit (`subsume` + `clear` + `ret 2`) & OTFS Branch Helpers -/

theorem deduce_otfs_ret2_subsume_wp {Γ : Env}
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 idx_u : Nat}
    {ext4 : List (BitVec 64)} {s0 s4 : FullState} {R : Mem 64 → Prop} {m4 : Mem 64}
    {Q : Post [i64]} {X : XPost}
    {steps' init_res_sz old_ctype old_cref : BitVec 64}
    {new_confl_arg : Arg Val i32} {new_confl_val : BitVec 32} {to_bin : Bool}
    (hs0_cut : FullCutInvW c F0 F_cur cut0 s0)
    (hconfl0 : FullConflictOkCut F_cur cut0 s0)
    (hext4 : M6HdrExtOk ext4) (hlen4 : s4.LengthsOk c)
    (hw4 : FullWitnessCutInv c F0 F_cur idx_u s4.core)
    (hcov4 : FullAnaMarksCov c s4) (hnd4 : FullArenaVarsNodup s4)
    (hextp4 : FullExtScratchPres s0 s4) (hws2_4 : s4.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s0)
    (hstat4 : FullDeduceStaticEq s0.core s4.core)
    (hconfl4 : FullConflictOkCut F_cur idx_u s4)
    (hdm4 : s4.core.dense_mode = 0#64)
    (harg : new_confl_arg.val = new_confl_val)
    (hct_bin : to_bin = true → s4.core.confl_type = 1#64)
    (hstep1 : steps' = 1#64 →
      old_ctype = s0.core.confl_type ∧ old_cref = s0.core.confl_ref ∧ idx_u < cut0 ∧
      (to_bin = false → s4.core.confl_type = 2#64 ∧
        s4.core.confl_ref = BitVec.setWidth 64 new_confl_val ∧
        new_confl_val.toNat ∈ fullArenaClauseRefs s4 ∧
        (s4.core.trl[idx_u]?.getD 0#32).toNat < 2 * s4.core.cur_vars ∧
        s4.core.rsns[(s4.core.trl[idx_u]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          new_confl_val ∧
        new_confl_val ≠ 0xFFFFFFFF#32 ∧ new_confl_val &&& 0x80000000#32 = 0#32))
    (hm4 : (FullM6HdrMem c ext4 s4 ⋆ R) m4)
    (hRet2 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m') :
    wp Γ Q X
      (Expr.group (sig := [[]]) (fun _ =>
        Blocks.cons (fun _ =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p_67 =>
          Expr.load i64 (Arg.var p_67.fst) fun ld_mcl =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_68 =>
          Expr.store (Arg.var ld_mcl) (Arg.var p_68.fst)
            (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
             Expr.ret (Arg.imm 2, ())))
        Blocks.nil) fun Js =>
       Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var steps', Arg.imm 1, ())) fun p_66 =>
       Expr.jnz (Arg.var p_66.fst)
         (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_67 =>
          Expr.load i64 (Arg.var p_67.fst) fun ld_21 =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
            (Arg.var ld_21, Arg.var init_res_sz, ())) fun p_68 =>
          Expr.jnz (Arg.var p_68.fst)
            (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := []) "full_otfs_subsume"
              (Arg.var c.hdr, new_confl_arg, Arg.var old_ctype, Arg.var old_cref,
                Arg.imm to_bin, ()) fun _ => Expr.jump Js.fst ())
            (Expr.jump Js.fst ()))
         (Expr.jump Js.fst ())) m4 := by
  refine wp_join0
    (fun m_j => ∃ s_j : FullState,
      s_j.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s_j.core ∧
      FullAnaMarksCov c s_j ∧ FullArenaVarsNodup s_j ∧ FullExtScratchPres s0 s_j ∧
      s_j.scratch.work_stk2 = s0.scratch.work_stk2 ∧
      fullArenaClauseRefs s_j = fullArenaClauseRefs s0 ∧
      FullDeduceStaticEq s0.core s_j.core ∧ FullConflictOkCut F_cur idx_u s_j ∧
      s_j.core.dense_mode = 0#64 ∧ (FullM6HdrMem c ext4 s_j ⋆ R) m_j) ?_ ?_
  · rintro _ m_j ⟨s_j, hlen_j, hw_j, hcov_j, hnd_j, hext_j, hws2_j, hrefs_j, hstat_j,
        hconfl_j, hdm_j, hm_j⟩
    have hm_f := fullM6HdrMem_focus_full hm_j
    c0_hsteps_nogrp
    let s_r : FullState :=
      { s_j with scratch := { s_j.scratch with res_sz := BitVec.ofNat 64 s_j.core.min_clr_len } }
    have hlen_r : s_r.LengthsOk c :=
      ded_lengthsOk_same_core_res hlen_j rfl rfl
    have hcov_r : FullAnaMarksCov c s_r := by
      unfold FullAnaMarksCov at hcov_j ⊢; exact hcov_j
    refine deduce_hdr_clear_wp hClear hlen_r (fullM6HdrMem_unfocus_full ‹_›)
      fun mrk' m_c hmrk_len _ _ hclr hm_c => ?_
    let s_ret : FullState :=
      { s_r with core := { s_r.core with mrk := mrk', min_clr_len := 0 } }
    have hmrk_zero := hclr hcov_r
    have hlen_c : s_ret.LengthsOk c :=
      ⟨{ hlen_r.core_ok with mrk_len := hmrk_len, min_clr_len_le := Nat.zero_le _ },
        hlen_r.scratch_ok⟩
    have hw_c : FullWitnessCutInv c F0 F_cur idx_u s_ret.core :=
      deduce_same_core_cut hw_j mrk' s_j.core.tmp s_j.core.tmp_cnt s_j.core.tmp_len 0
    have hmc_c : FullLitMarksClear c s_ret :=
      ded_litMarksClear_of_clear hs0_cut.2.2.1 hmrk_zero hstat_j.lm
    have hnd_c : FullArenaVarsNodup s_ret :=
      ded_arenaVarsNodup_same_core_arena hnd_j rfl rfl
    have hext_pc : FullExtScratchPres s0 s_ret := hext_j
    have hrefs_c : fullArenaClauseRefs s_ret = fullArenaClauseRefs s0 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs_j ⊢; exact hrefs_j
    have hext_okc : FullExtScratchOk c s_ret :=
      ded_extScratchOk_of_pres hs0_cut.2.2.2.2.1 hext_pc hstat_j.cv hrefs_c
    have hcut_c : FullCutInvW c F0 F_cur idx_u s_ret :=
      ded_cutInvW_of_parts hlen_c hw_c hmc_c hnd_c hext_okc hdm_j
    have hotfs_c : FullOtfsInvW c F0 F_cur s_ret :=
      ded_otfsInvW_of_cutInv hlen_c hw_c hmc_c hnd_c hext_okc hdm_j
    have hconfl_c : FullConflictOkCut F_cur idx_u s_ret := by
      refine deduce_conflOk_with_counts hconfl_j ?_ rfl ?_
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro _
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
        exact ⟨rfl, rfl⟩
    rw [wp_ret]
    exact hRet2 ext4 s_ret m_c idx_u hext4 hlen_c hw_c.cut_le hcut_c hotfs_c hstat_j.cv
      hstat_j.fuel hws2_j hstat_j.cl hconfl_c hm_c
  · intro Js hJs
    have hbase : ∀ (m_cur : Mem 64), (FullM6HdrMem c ext4 s4 ⋆ R) m_cur → Js () m_cur := by
      intro m_cur hm_cur
      exact hJs m_cur ⟨s4, hlen4, hw4, hcov4, hnd4, hextp4, hws2_4, hrefs4, hstat4, hconfl4,
        hdm4, hm_cur⟩
    have hm4_f := fullM6HdrMem_focus_full hm4
    c0_hsteps_nogrp
    · have hs1_nat : steps' = 1#64 := by assumption
      obtain ⟨hct_eq, hcr_eq, hidx0, htb⟩ := hstep1 hs1_nat
      refine ded_otfs_subsume_imm_wp hSub harg hlen4 hw4 hnd4 (fun hct2 hcr_ne => ?_)
        (fullM6HdrMem_unfocus_full ‹_›) fun arena' ag' ni' nr' m' hlen' hw' hnd' hrefs'
          hgarb_lits hm' => ?_
      · have hct_s0 : s0.core.confl_type = 2#64 := hct_eq ▸ hct2
        have hcr_s0 : s0.core.confl_ref ≠ 0xFFFFFFFF#64 := hcr_eq ▸ hcr_ne
        have hnon := deduce_otfs_old_cr_nonactive hs0_cut hconfl0 hidx0 hstat4 hct_s0 hcr_s0
        refine ⟨hcr_eq ▸ hrefs4.symm ▸ hnon.1, fun htf => (htb htf).2.2.1, fun idx hidx hor => ?_⟩
        rw [hcr_eq]
        exact hnon.2.2 idx hidx hor
      · let s_sub : FullState :=
          { s4 with
            core := { s4.core with arena_garbage := ag', num_irred := ni', num_redundant := nr',
                                   arena := arena' } }
        have hstat_sub : FullDeduceStaticEq s0.core s_sub.core :=
          ⟨hstat4.cv, hstat4.cl, hstat4.te, hstat4.trl, hstat4.lvl, hstat4.rsns, hstat4.vals,
            hstat4.fuel, hstat4.dm, hstat4.lm⟩
        have hcov_sub : FullAnaMarksCov c s_sub := hcov4
        have hextp_sub : FullExtScratchPres s0 s_sub := hextp4
        have hrefs_sub : fullArenaClauseRefs s_sub = fullArenaClauseRefs s0 :=
          hrefs'.trans hrefs4
        have hconfl_sub : FullConflictOkCut F_cur idx_u s_sub := by
          refine deduce_conflOk_with_counts hconfl4 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            hrefs' (fun hc2 => ?_)
          have hbin_f : to_bin = false := by
            cases htb_v : to_bin with
            | false => rfl
            | true =>
              have hct1 := hct_bin htb_v
              change s4.core.confl_type = 2#64 at hc2
              rw [hct1] at hc2; cases hc2
          obtain ⟨_, hcr_sub_eq, hnc_in, htrl_lt, hrsn_eq, hnc_ne, hnc_nb⟩ := htb hbin_f
          have hcr_nat : s4.core.confl_ref.toNat = new_confl_val.toNat := by
            rw [hcr_sub_eq, BitVec.toNat_setWidth]
            exact Nat.mod_eq_of_lt (Nat.lt_trans new_confl_val.isLt (by decide))
          have hne_old : old_ctype = 2#64 → s4.core.confl_ref.toNat ≠ old_cref.toNat := by
            intro hct2
            by_cases hcr_ff : old_cref = 0xFFFFFFFF#64
            · rw [hcr_ff, hcr_nat]
              intro heq
              apply hnc_ne
              apply BitVec.eq_of_toNat_eq
              simpa [BitVec.toNat_ofNat] using heq
            · have hct_s0 : s0.core.confl_type = 2#64 := hct_eq ▸ hct2
              have hcr_s0 : s0.core.confl_ref ≠ 0xFFFFFFFF#64 := hcr_eq ▸ hcr_ff
              have hnon := deduce_otfs_old_cr_nonactive hs0_cut hconfl0 hidx0 hstat4 hct_s0 hcr_s0
              have hne_s0 := hnon.2.1 new_confl_val htrl_lt hrsn_eq hnc_ne hnc_nb
              rw [hcr_nat, hcr_eq]; exact hne_s0
          have hgl := hgarb_lits s4.core.confl_ref.toNat (hcr_nat ▸ hnc_in)
          exact ⟨hgl.2 hne_old, hgl.1⟩
        exact hJs m' ⟨s_sub, hlen', hw', hcov_sub, hnd', hextp_sub, hws2_4, hrefs_sub,
          hstat_sub, hconfl_sub, hdm4, hm'⟩
    · exact hbase m4 hm4
    · exact hbase m4 hm4

private theorem ded_loop_otfs_bin_wp {Γ : Env}
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    (hBin : Γ.Has "full_otfs_bin" Spec.fullOtfsBinSpec)
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_cur idx' : Nat}
    {ext2 : List (BitVec 64)} {s0 s3 : FullState} {R : Mem 64 → Prop} {m3 : Mem 64}
    {Q : Post [i64]} {X : XPost} {Js : Cont []}
    {rsn p_bv : BitVec 32} {steps' init_res_sz old_ctype old_cref : BitVec 64}
    (hs0_cut : FullCutInvW c F0 F_cur cut0 s0)
    (hconfl0 : FullConflictOkCut F_cur cut0 s0)
    (hcur_pos : 0 < s0.core.cur_level)
    (hext2 : M6HdrExtOk ext2)
    (hs3_inv : FullDeduceStateInv c F0 F_cur cut_cur idx' s0 s3)
    (hidx_te : idx' < s3.core.trail_end) (hidx_cut : idx' < cut_cur)
    (hp_get : (s3.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hrsn_get : s3.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hl_p : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hnb : rsn &&& 0x80000000#32 = 0#32)
    (hrsn_ref : rsn.toNat ∈ fullArenaClauseRefs s3)
    (hrsn_garb : fullArenaClauseGarb s3 rsn.toNat = false)
    (hall_mrk : ∀ l ∈ fullArenaClauseLits s3 rsn.toNat, l / 2 ≠ p_bv.toNat / 2 →
      0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hant_eq : s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 rsn.toNat).filter
      fun l => decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length)
    (hasz_eq : s3.scratch.ant_sz = 3#64)
    (hrsz_lt : s3.scratch.res_sz < s3.scratch.ant_sz)
    (hstep1 : steps' = 1#64 →
      old_ctype = s0.core.confl_type ∧ old_cref = s0.core.confl_ref ∧ idx' < cut0)
    (hm3 : (FullM6HdrMem c ext2 s3 ⋆ R) m3)
    (hJs : ∀ (cut_j : Nat) (s_j : FullState) (m_j : Mem 64),
      cut_j ≤ s_j.core.trail_end → s_j.core.tmp_cnt = s3.core.tmp_cnt →
      FullDeduceStateInv c F0 F_cur cut_j idx' s0 s_j → M6HdrExtOk ext2 →
      (FullM6HdrMem c ext2 s_j ⋆ R) m_j → Js () m_j)
    (hRet2 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_bin"
         (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p_58 =>
       Expr.jnz (Arg.var p_58.fst)
         (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 112, ())) fun p_59 =>
          Expr.load i64 (Arg.var p_59.fst) fun ld_19 =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var rsn, ())) fun p_60 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p_60.fst, Arg.imm 4, ())) fun p_61 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var ld_19, Arg.var p_61.fst, ())) fun p_62 =>
          Expr.load i32 (Arg.var p_62.fst) fun ld_20 =>
          Expr.let_ (Op.mk (.and i32) (Arg.var ld_20, Arg.imm 4194304, ())) fun p_63 =>
          Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p_63.fst, Arg.imm 0, ())) fun p_64 =>
          Expr.group (sig := [[]]) (fun _ =>
            Blocks.cons (fun _ =>
              Expr.group (sig := [[]]) (fun _ =>
                Blocks.cons (fun _ =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p_67 =>
                  Expr.load i64 (Arg.var p_67.fst) fun ld_mcl =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_68 =>
                  Expr.store (Arg.var ld_mcl) (Arg.var p_68.fst)
                    (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
                       fun _ => Expr.ret (Arg.imm 2, ())))
                Blocks.nil) fun Js_2 =>
              Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var steps', Arg.imm 1, ())) fun p_66 =>
              Expr.jnz (Arg.var p_66.fst)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_67 =>
                 Expr.load i64 (Arg.var p_67.fst) fun ld_21 =>
                 Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                   (Arg.var ld_21, Arg.var init_res_sz, ())) fun p_68 =>
                 Expr.jnz (Arg.var p_68.fst)
                   (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := []) "full_otfs_subsume"
                     (Arg.var c.hdr, Arg.imm 0, Arg.var old_ctype, Arg.var old_cref,
                       Arg.imm true, ()) fun _ => Expr.jump Js_2.fst ())
                   (Expr.jump Js_2.fst ()))
                (Expr.jump Js_2.fst ()))
            Blocks.nil) fun Js_1 =>
          Expr.jnz (Arg.var p_64.fst)
            (Expr.group (sig := [[]])
               (fun _ => Blocks.cons (fun _ => Expr.jump Js_1.fst ()) Blocks.nil)
              fun Js_2 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ())) fun p_65 =>
             Expr.load i64 (Arg.var p_65.fst) fun ld =>
             Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_66 =>
             Expr.jnz (Arg.var p_66.fst)
               (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ())) fun p_67 =>
                Expr.load i64 (Arg.var p_67.fst) fun ld =>
                Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.imm 1, ())) fun p_68 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 496, ())) fun p =>
                Expr.store (Arg.var p_68.fst) (Arg.var p.fst) (Expr.jump Js_2.fst ()))
               (Expr.jump Js_2.fst ()))
            (Expr.group (sig := [[]])
               (fun _ => Blocks.cons (fun _ => Expr.jump Js_1.fst ()) Blocks.nil)
              fun Js_2 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ())) fun p_65 =>
             Expr.load i64 (Arg.var p_65.fst) fun ld =>
             Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_66 =>
             Expr.jnz (Arg.var p_66.fst)
               (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ())) fun p_67 =>
                Expr.load i64 (Arg.var p_67.fst) fun ld =>
                Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.imm 1, ())) fun p_68 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 488, ())) fun p =>
                Expr.store (Arg.var p_68.fst) (Arg.var p.fst) (Expr.jump Js_2.fst ()))
               (Expr.jump Js_2.fst ())))
         (Expr.jump Js ())) m3 := by
  have hp_lt : p_bv.toNat < 2 * s3.core.cur_vars := by
    have hv := hs3_inv.hw.trail_lits_lt idx' hidx_te; omega
  have hdm3 : s3.core.dense_mode = 0#64 := hs3_inv.stat.dm ▸ hs0_cut.2.2.2.2.2
  have hent_bin := otfs_entails_bin_of_res_lt_ant hs3_inv hcur_pos hidx_te hidx_cut hp_get
    hrsn_get hl_p hnb hrsn_ref hrsn_garb hall_mrk hant_eq hasz_eq hrsz_lt
  refine deduce_hdr_otfs_bin_wp hBin hs3_inv.len hs3_inv.hw hs3_inv.nd hdm3 hrsn_ref hrsn_garb
    hp_lt hidx_cut hp_get hrsn_get hl_p hent_bin hm3
    fun ok arena' ag' wvec' wstk' wlen' wu' nb' ctype' cr' c0' c1' oom' sc' m4
      hlen4 hw4 hnd4 hext4 _hws1_4 hws2_4 hres4 hrefs4 h_ok hm4 => ?_
  let s4 : FullState :=
    { core := { s3.core with wlen := wlen', wusable := wu', arena_garbage := ag',
                             num_binary := nb', confl_ref := cr', confl_type := ctype',
                             confl_lit0 := c0', confl_lit1 := c1', oom := oom', wvec := wvec',
                             arena := arena', wstk := wstk' }
      scratch := sc' }
  have hstat4 : FullDeduceStaticEq s3.core s4.core :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases ok
  · simp only [wp_jnz, wp_jump]
    refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
    exact hJs idx' s4 m4 hw4.cut_le rfl
      (ded_inv_otfs_fail hs3_inv hlen4 hw4 hnd4 hext4 hws2_4 ‹_› hres4 hrefs4 hstat4
        rfl rfl rfl rfl rfl)
      hext2 hm4
  · obtain ⟨hct4, hconfl4⟩ := h_ok rfl
    simp only [wp_jnz]
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    have hrsn_ar_lt : (rsn.setWidth 64).toNat < s4.core.arena.length := by
      have href4 : rsn.toNat ∈ fullArenaClauseRefs s4 := hrefs4.symm ▸ hrsn_ref
      have hbd := (fullArenaScanRefs_mem_bounds href4).2
      have h1 := hlen4.core_ok.arena_len_le
      have h2 := hlen4.core_ok.arena_len_arr
      dsimp only [s4] at hbd h1 h2 ⊢
      have hsw : (rsn.setWidth 64).toNat = rsn.toNat := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le rsn.isLt (by decide))
      omega
    have hm4_f := fullM6HdrMem_focus_full hm4
    c0_hsteps_nogrp
    refine wp_join0
      (fun m_j => ∃ s_j : FullState,
        s_j.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx' s_j.core ∧
        FullAnaMarksCov c s_j ∧ FullArenaVarsNodup s_j ∧ FullExtScratchPres s0 s_j ∧
        s_j.scratch.work_stk2 = s0.scratch.work_stk2 ∧
        fullArenaClauseRefs s_j = fullArenaClauseRefs s0 ∧
        FullDeduceStaticEq s0.core s_j.core ∧ FullConflictOkCut F_cur idx' s_j ∧
        s_j.core.confl_type = 1#64 ∧
        s_j.core.dense_mode = 0#64 ∧ (FullM6HdrMem c ext2 s_j ⋆ R) m_j) ?_ ?_
    · rintro _ m_j ⟨s_j, hlen_j, hw_j, hcov_j, hnd_j, hext_j, hws2_j, hrefs_j, hstat_j,
          hconfl_j, hct1_j, hdm_j, hm_j⟩
      exact deduce_otfs_ret2_subsume_wp hClear hSub hs0_cut hconfl0 hext2 hlen_j hw_j hcov_j
        hnd_j hext_j hws2_j hrefs_j hstat_j hconfl_j hdm_j rfl (fun _ => hct1_j)
        (fun hs1 => let ⟨h1, h2, h3⟩ := hstep1 hs1; ⟨h1, h2, h3, fun h => Bool.noConfusion h⟩)
        hm_j hRet2
    · intro Js1 hJs1
      have hpack : ∀ (ni' nr' : BitVec 64) (m_p : Mem 64),
          let s_p : FullState := { s4 with core := { s4.core with num_irred := ni',
                                                                  num_redundant := nr' } }
          (FullMem c s_p ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m_p → Js1 () m_p := by
        intro ni' nr' m_p s_p hm_p
        have hcov4 : FullAnaMarksCov c s_p := by
          have hc3 := hs3_inv.cov; unfold FullAnaMarksCov at hc3 ⊢
          rw [← ‹s4.scratch.work_stk1 = s3.scratch.work_stk1›] at hc3; exact hc3
        have hw_p := fcut_with_counts hw4 ni' nr'
        have hlen_p : s_p.LengthsOk c := ⟨{ hlen4.core_ok with }, hlen4.scratch_ok⟩
        have hnd_p : FullArenaVarsNodup s_p := ded_arenaVarsNodup_same_core_arena hnd4 rfl rfl
        have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s0 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; exact hrefs4.trans hs3_inv.hrefs
        have hconfl_p := deduce_conflOk_with_counts hconfl4
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
          (fun _ => ⟨rfl, rfl⟩)
        have hstat_p : FullDeduceStaticEq s3.core s_p.core :=
          ⟨hstat4.cv, hstat4.cl, hstat4.te, hstat4.trl, hstat4.lvl, hstat4.rsns, hstat4.vals,
            hstat4.fuel, hstat4.dm, hstat4.lm⟩
        exact hJs1 m_p ⟨s_p, hlen_p, hw_p, hcov4, hnd_p,
          fullExtScratchPres_trans hs3_inv.ext hext4, hws2_4.trans hs3_inv.ws2,
          hrefs_p, hs3_inv.stat.trans hstat_p, hconfl_p, hct4, hdm3, fullM6HdrMem_unfocus_full hm_p⟩
      refine (wp_jnz _ _ _).mpr ⟨fun _ => ?_, fun _ => ?_⟩
      · refine wp_join0 (fun m_p => Js1 () m_p) (fun _ _ h => h) fun Js2 hJs2 => ?_
        c0_hsteps_nogrp
        · exact hJs2 _ (hpack s4.core.num_irred (s4.core.num_redundant - 1#64) _ ‹_›)
        · exact hJs2 _ (hpack s4.core.num_irred s4.core.num_redundant _ ‹_›)
      · refine wp_join0 (fun m_p => Js1 () m_p) (fun _ _ h => h) fun Js2 hJs2 => ?_
        c0_hsteps_nogrp
        · exact hJs2 _ (hpack (s4.core.num_irred - 1#64) s4.core.num_redundant _ ‹_›)
        · exact hJs2 _ (hpack s4.core.num_irred s4.core.num_redundant _ ‹_›)

private theorem ded_loop_otfs_large_wp {Γ : Env}
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    (hLarge : Γ.Has "full_otfs_large" Spec.step13OtfsLargeSpec)
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_cur idx' : Nat}
    {ext2 : List (BitVec 64)} {s0 s3 : FullState} {R : Mem 64 → Prop} {m3 : Mem 64}
    {Q : Post [i64]} {X : XPost} {Js : Cont []}
    {rsn p_bv : BitVec 32} {steps' init_res_sz old_ctype old_cref : BitVec 64}
    (hs0_cut : FullCutInvW c F0 F_cur cut0 s0)
    (hconfl0 : FullConflictOkCut F_cur cut0 s0)
    (hcur_pos : 0 < s0.core.cur_level)
    (hext2 : M6HdrExtOk ext2)
    (hs3_inv : FullDeduceStateInv c F0 F_cur cut_cur idx' s0 s3)
    (hidx_te : idx' < s3.core.trail_end) (hidx_cut : idx' < cut_cur)
    (hp_get : (s3.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hrsn_get : s3.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hl_p : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level)
    (hne : rsn ≠ 0xFFFFFFFF#32)
    (hnb : rsn &&& 0x80000000#32 = 0#32)
    (hrsn_ref : rsn.toNat ∈ fullArenaClauseRefs s3)
    (hrsn_garb : fullArenaClauseGarb s3 rsn.toNat = false)
    (hall_mrk : ∀ l ∈ fullArenaClauseLits s3 rsn.toNat, l / 2 ≠ p_bv.toNat / 2 →
      0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat → s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hant_eq : s3.scratch.ant_sz.toNat = ((fullArenaClauseLits s3 rsn.toNat).filter
      fun l => decide (0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat)).length)
    (hrsz_lt : s3.scratch.res_sz < s3.scratch.ant_sz)
    (hstep1 : steps' = 1#64 →
      old_ctype = s0.core.confl_type ∧ old_cref = s0.core.confl_ref ∧ idx' < cut0)
    (hm3 : (FullM6HdrMem c ext2 s3 ⋆ R) m3)
    (hJs : ∀ (cut_j : Nat) (s_j : FullState) (m_j : Mem 64),
      cut_j ≤ s_j.core.trail_end → s_j.core.tmp_cnt = s3.core.tmp_cnt →
      FullDeduceStateInv c F0 F_cur cut_j idx' s0 s_j → M6HdrExtOk ext2 →
      (FullM6HdrMem c ext2 s_j ⋆ R) m_j → Js () m_j)
    (hRet2 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_large"
         (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p_58 =>
       Expr.jnz (Arg.var p_58.fst)
         (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p_59 =>
          Expr.store (t := i64) (Arg.imm 2) (Arg.var p_59.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var rsn, ())) fun p_60 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ())) fun p_61 =>
             Expr.store (Arg.var p_60.fst) (Arg.var p_61.fst)
               (Expr.group (sig := [[]]) (fun _ =>
                  Blocks.cons (fun _ =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p_63 =>
                    Expr.load i64 (Arg.var p_63.fst) fun ld_mcl =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_64 =>
                    Expr.store (Arg.var ld_mcl) (Arg.var p_64.fst)
                      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
                         fun _ => Expr.ret (Arg.imm 2, ())))
                  Blocks.nil) fun Js_2 =>
                Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var steps', Arg.imm 1, ()))
                  fun p_62 =>
                Expr.jnz (Arg.var p_62.fst)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_63 =>
                   Expr.load i64 (Arg.var p_63.fst) fun ld_19 =>
                   Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                     (Arg.var ld_19, Arg.var init_res_sz, ())) fun p_64 =>
                   Expr.jnz (Arg.var p_64.fst)
                     (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := [])
                        "full_otfs_subsume"
                       (Arg.var c.hdr, Arg.var rsn, Arg.var old_ctype, Arg.var old_cref,
                         Arg.imm false, ()) fun _ => Expr.jump Js_2.fst ())
                     (Expr.jump Js_2.fst ()))
                  (Expr.jump Js_2.fst ()))))
         (Expr.jump Js ())) m3 := by
  have hp_lt : p_bv.toNat < 2 * s3.core.cur_vars := by
    have hv := hs3_inv.hw.trail_lits_lt idx' hidx_te; omega
  have hdm3 : s3.core.dense_mode = 0#64 := hs3_inv.stat.dm ▸ hs0_cut.2.2.2.2.2
  have hent_lg := otfs_entails_large_of_res_lt_ant hs3_inv hcur_pos hidx_te hidx_cut hp_get
    hrsn_get hl_p hnb hrsn_ref hrsn_garb hall_mrk hant_eq hrsz_lt
  refine deduce_hdr_otfs_large_wp hLarge hs3_inv.len hs3_inv.hw hs3_inv.nd hdm3 hrsn_ref
    hrsn_garb hp_lt hidx_cut hp_get hrsn_get hl_p hent_lg hm3
    fun ok flags' arena' wvec' wstk' wlen' wu' oom' sc' m4
      hlen4 hw4 hnd4 hext4 _hws1_4 hws2_4 hres4 hrefs4 h_ok hm4 => ?_
  let s4 : FullState :=
    { core := { s3.core with wlen := wlen', wusable := wu', oom := oom', flags := flags',
                             wvec := wvec', arena := arena', wstk := wstk' }
      scratch := sc' }
  have hstat4 : FullDeduceStaticEq s3.core s4.core :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases ok
  · simp only [wp_jnz, wp_jump]
    refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
    exact hJs idx' s4 m4 hw4.cut_le rfl
      (ded_inv_otfs_fail hs3_inv hlen4 hw4 hnd4 hext4 hws2_4 ‹_› hres4 hrefs4 hstat4
        rfl rfl rfl rfl rfl)
      hext2 hm4
  · obtain ⟨hr4, hgb4, hlits4⟩ := h_ok rfl
    simp only [wp_jnz]
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    have hm4_f := fullM6HdrMem_focus_full hm4
    c0_hsteps_nogrp
    let s5 : FullState :=
      { s4 with core := { s4.core with confl_type := 2#64, confl_ref := rsn.setWidth 64 } }
    have hcov5 : FullAnaMarksCov c s5 := by
      have hc3 := hs3_inv.cov; unfold FullAnaMarksCov at hc3 ⊢
      rw [← ‹s4.scratch.work_stk1 = s3.scratch.work_stk1›] at hc3; exact hc3
    have hw5 := fcut_with_confl hw4 2#64 s4.core.confl_lit0 s4.core.confl_lit1 (rsn.setWidth 64)
    have hlen5 : s5.LengthsOk c := ⟨{ hlen4.core_ok with }, hlen4.scratch_ok⟩
    have hnd5 : FullArenaVarsNodup s5 := ded_arenaVarsNodup_same_core_arena hnd4 rfl rfl
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s0 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; exact hrefs4.trans hs3_inv.hrefs
    have hconfl5 : FullConflictOkCut F_cur idx' s5 := by
      refine deduce_conflOk_large_init hr4 hgb4 rfl rfl fun l hl => ?_
      exact hlits4 l hl
    have hstat5 : FullDeduceStaticEq s3.core s5.core :=
      ⟨hstat4.cv, hstat4.cl, hstat4.te, hstat4.trl, hstat4.lvl, hstat4.rsns, hstat4.vals,
        hstat4.fuel, hstat4.dm, hstat4.lm⟩
    refine deduce_otfs_ret2_subsume_wp hClear hSub hs0_cut hconfl0 hext2 hlen5 hw5 hcov5 hnd5
      (fullExtScratchPres_trans hs3_inv.ext hext4) (hws2_4.trans hs3_inv.ws2) hrefs5
      (hs3_inv.stat.trans hstat5) hconfl5 hdm3 rfl (fun h => by cases h) (fun hs1 => ?_)
      (fullM6HdrMem_unfocus_full ‹_›) hRet2
    obtain ⟨h1, h2, h3⟩ := hstep1 hs1
    refine ⟨h1, h2, h3, fun _ => ⟨rfl, rfl, hr4, ?_, ?_, hne, hnb⟩⟩
    · change (s3.core.trl[idx']?.getD 0#32).toNat < 2 * s3.core.cur_vars
      rw [hp_get]; exact hp_lt
    · change s3.core.rsns[(s3.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = rsn
      rw [hp_get]; exact hrsn_get

private theorem ded_rsn_clear_ret0_wp {Γ : Env}
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_cur : Nat}
    {ext2 : List (BitVec 64)} {s0 s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hs0_cut : FullCutInvW c F0 F_cur cut0 s0) (hext2 : M6HdrExtOk ext2)
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut_cur s2.core)
    (hcov2 : FullAnaMarksCov c s2) (hnd2 : FullArenaVarsNodup s2)
    (hext02 : FullExtScratchPres s0 s2) (hws2_02 : s2.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs2_s0 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0)
    (hstat2 : FullDeduceStaticEq s0.core s2.core)
    (hm2 : (FullM6HdrMem c ext2 s2 ⋆ R) m2)
    (hRet0 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
      fun _ => Expr.ret (Arg.imm 0, ())) m2 := by
  refine deduce_hdr_clear_wp hClear hlen2 hm2 fun mrk'' m_c hmrk_len _ _ hclr hm_c => ?_
  let s_ret : FullState := { s2 with core := { s2.core with mrk := mrk'', min_clr_len := 0 } }
  have hlen_c : s_ret.LengthsOk c :=
    ⟨{ hlen2.core_ok with mrk_len := hmrk_len, min_clr_len_le := Nat.zero_le _ },
      hlen2.scratch_ok⟩
  have hw_c : FullWitnessCutInv c F0 F_cur cut_cur s_ret.core :=
    deduce_same_core_cut hw2 mrk'' s2.core.tmp s2.core.tmp_cnt s2.core.tmp_len 0
  have hmc_c : FullLitMarksClear c s_ret :=
    ded_litMarksClear_of_clear hs0_cut.2.2.1 (hclr hcov2) hstat2.lm
  have hnd_c : FullArenaVarsNodup s_ret := ded_arenaVarsNodup_same_core_arena hnd2 rfl rfl
  have hrefs_c : fullArenaClauseRefs s_ret = fullArenaClauseRefs s0 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs2_s0 ⊢; exact hrefs2_s0
  have hext_okc : FullExtScratchOk c s_ret :=
    ded_extScratchOk_of_pres hs0_cut.2.2.2.2.1 hext02 hstat2.cv hrefs_c
  have hotfs_c : FullOtfsInvW c F0 F_cur s_ret :=
    ded_otfsInvW_of_cutInv hlen_c hw_c hmc_c hnd_c hext_okc (hstat2.dm ▸ hs0_cut.2.2.2.2.2)
  rw [wp_ret]
  exact hRet0 ext2 s_ret m_c hext2 hlen_c hstat2.cv hstat2.fuel hws2_02 hotfs_c hm_c

/-! ## 3. Loop Reason Step (`deduce_loop_rsn_wp`) -/

theorem deduce_loop_rsn_wp {Γ : Env}
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" Spec.s13AnalyzeRsnHdrSpec)
    (hClear : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    (hBin : Γ.Has "full_otfs_bin" Spec.fullOtfsBinSpec)
    (hLarge : Γ.Has "full_otfs_large" Spec.step13OtfsLargeSpec)
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut0 cut_cur idx' : Nat}
    {ext : List (BitVec 64)} {s0 s1 sl : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {Js_2 : Cont [i64, i32, i64]}
    {steps init_res_sz : BitVec 64} {p_bv skip_var : BitVec 32}
    (hskip : skip_var = p_bv >>> 1#32)
    (hcfg : FullM6HdrCfgOk c) (hs0_cut : FullCutInvW c F0 F_cur cut0 s0)
    (hconfl0 : FullConflictOkCut F_cur cut0 s0) (hcur_pos : 0 < s0.core.cur_level)
    (hext : M6HdrExtOk ext) (hs1 : FullDeduceStateInv c F0 F_cur cut_cur (idx' + 1) s0 s1)
    (hidx_te : idx' < s1.core.trail_end)
    (hp_get : (s1.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hm_p : s1.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl_p : (s1.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s1.core.cur_level)
    (hsl_c : sl.core = { s1.core with tmp_cnt := s1.core.tmp_cnt - 1 })
    (hsl_sc : sl.scratch = s1.scratch)
    (hstep0 : steps = 0#64 → cut_cur = cut0 ∧
      s1.core.confl_type = s0.core.confl_type ∧ s1.core.confl_ref = s0.core.confl_ref)
    (hm : (FullM6HdrMem c ext sl ⋆ R) m)
    (hRet0 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m')
    (hRet2 : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) (cut' : Nat),
      M6HdrExtOk ext' → s'.LengthsOk c → cut' ≤ s'.core.trail_end →
      FullCutInvW c F0 F_cur cut' s' → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → s'.core.cur_level = s0.core.cur_level →
      FullConflictOkCut F_cur cut' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (2#64, ()) m')
    (hJs : ∀ (cut_j : Nat) (ext_j : List (BitVec 64)) (s_j : FullState) (m_j : Mem 64),
      cut_j ≤ s_j.core.trail_end → M6HdrExtOk ext_j →
      FullDeduceStateInv c F0 F_cur cut_j idx' s0 s_j →
      (FullM6HdrMem c ext_j s_j ⋆ R) m_j →
      Js_2 (BitVec.ofNat 64 s_j.core.tmp_cnt, 0xFFFFFFFF#32, steps + 1#64, ()) m_j) :
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
             Expr.group (sig := [[i64]]) (fun _Js =>
               Blocks.cons (fun p_49 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ())) fun p_50 =>
                 Expr.load i64 (Arg.var p_50.fst) fun ld_16 =>
                 Expr.group (sig := [[]]) (fun _Js_1 =>
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
                                     (Expr.group (sig := [[]]) (fun _Js_4 =>
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
             Expr.ret (Arg.imm 0, ())))) m := by
  subst hskip
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hv_lt : (p_bv >>> 1#32).toNat < sl.core.cur_vars := by
    rw [DeduceTactics.ded_bv32_lshr_1, hsl_c]
    have h1 := hs1.hw.trail_lits_lt idx' hidx_te
    rw [hp_get] at h1; exact Nat.div_lt_of_lt_mul h1
  have hlen_sl : sl.LengthsOk c :=
    ⟨by rw [hsl_c]; exact { hs1.len.core_ok with }, by rw [hsl_sc]; exact hs1.len.scratch_ok⟩
  have hpv_rsns : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.rsns.length := by
    rw [BitVec.toNat_setWidth]
    have := hlen_sl.core_ok.cur_vars_le; have := hlen_sl.core_ok.rsns_len
    have : (p_bv >>> 1#32).toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]; omega
  have hm_f := fullM6HdrMem_focus_full hm
  c0_hsteps_nogrp
  let rsn := sl.core.rsns[((p_bv >>> 1#32).setWidth 64).toNat]
  let sl_ant : FullState := { sl with scratch := { sl.scratch with ant_sz := 0#64 } }
  have hrsn_get : s1.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
    have hsw : ((p_bv >>> 1#32).setWidth 64).toNat = p_bv.toNat / 2 := by
      rw [BitVec.toNat_setWidth, DeduceTactics.ded_bv32_lshr_1]
      exact Nat.mod_eq_of_lt (by omega)
    have hlt1 : p_bv.toNat / 2 < s1.core.rsns.length := by
      rw [hsl_c] at hpv_rsns; exact hsw ▸ hpv_rsns
    simp only [rsn, hsl_c, hsw, List.getElem?_eq_getElem hlt1, Option.getD_some]
  have hpre := deduce_loop_rsn_pre hs1.hw hs1.cmcut hidx_te
    (by rw [hp_get]; exact hm_p) (by rw [hp_get]; exact hl_p)
  have hp_bv_eq : s1.core.trl[idx']?.getD 0#32 = p_bv := BitVec.eq_of_toNat_eq hp_get
  dsimp only at hpre; rw [hp_bv_eq, hrsn_get] at hpre
  have hw_ant : FullWitnessCutInv c F0 F_cur cut_cur sl_ant.core := by
    rw [show sl_ant.core = sl.core from rfl, hsl_c]
    exact deduce_same_core_cut hs1.hw _ _ (s1.core.tmp_cnt - 1) _ _
  have hcov_ant : FullAnaMarksCov c sl_ant := by
    have hc1 := hs1.cov; unfold FullAnaMarksCov at hc1 ⊢
    change FullAnaMarksCov c
      { core := sl.core, scratch := { sl.scratch with ant_sz := 0#64 } }
    rw [hsl_c, hsl_sc]; exact hc1
  have hlen_ant : sl_ant.LengthsOk c := ⟨hlen_sl.core_ok, { hlen_sl.scratch_ok with }⟩
  have htl_ant : sl_ant.core.tmp_len ≤ sl_ant.core.cur_vars := by
    change sl.core.tmp_len ≤ sl.core.cur_vars; rw [hsl_c]; exact hs1.tl_cv
  have htc_fit : sl_ant.core.tmp_cnt + sl_ant.core.cur_vars + 1 < 2 ^ 64 := by
    have hu : sl_ant.core.tmp_cnt = s1.core.tmp_cnt - 1 := by
      change sl.core.tmp_cnt = _; rw [hsl_c]
    have hv : sl_ant.core.cur_vars = s1.core.cur_vars := by
      change sl.core.cur_vars = _; rw [hsl_c]
    have h1 := hs1.tc_eq
    have htl_arr : s1.core.tmp_len ≤ s1.core.tmp.length := by
      rw [hs1.len.core_ok.tmp_len_arr]
      exact Nat.le_trans hs1.tl_cv hs1.len.core_ok.cur_vars_le
    have h2 := fullActiveResolvent_le_cur_vars hidx_te hs1.tl_ge htl_arr
      hs1.low hs1.hw.trail_lits_lt hs1.hw.trail_vars_nodup
    rw [Nat.succ_eq_add_one] at h2
    have h3 := hs1.len.core_ok.cur_vars_le
    have h4 := hs1.tl_ge
    rw [hu, hv]; omega
  have href_ant : rsn ≠ 0xFFFFFFFF#32 → rsn &&& 0x80000000#32 = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs sl_ant := by
    intro hne hnb
    unfold fullArenaClauseRefs fullArenaClauseRefsCore
    change rsn.toNat ∈ fullArenaClauseRefsCore sl.core
    rw [hsl_c]; exact hpre.2 hne hnb
  have hnd_ant : FullArenaVarsNodup sl_ant :=
    ded_arenaVarsNodup_same_core_arena hs1.nd (by change sl.core.arena = _; rw [hsl_c])
      (by change sl.core.arena_len = _; rw [hsl_c])
  refine ded_rsn_hdr_wp hRsn hcfg hext hlen_ant hw_ant hcov_ant htl_ant htc_fit href_ant
    (fullM6HdrMem_unfocus_full ‹_›)
    fun ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext2 m2 hext2 _ hlen2 hw2 hcov2 hext2_p
      hws2_2 htl2_ge htl2_cv htc2_ge hrefs2 hcl2 hmp htp hnm hnt hnd_j hcnt hres2 h_ok hm2 => ?_
  let s2 : FullState :=
    { core := { sl_ant.core with tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl',
                                 mrk := mrk', tmp := tmp', min_clr := mclr', arena := arena' }
      scratch := sc' }
  have hnd2 : FullArenaVarsNodup s2 :=
    ded_arenaVarsNodup_of_pres hnd_ant hrefs2 (fun r hr => (hcl2 r hr).2)
  have hext_s1_ant : FullExtScratchPres s1 sl_ant := by
    unfold FullExtScratchPres
    change ({ sl.scratch with ant_sz := 0#64 }.last_learned = s1.scratch.last_learned ∧
      { sl.scratch with ant_sz := 0#64 }.extend_len = s1.scratch.extend_len)
    rw [hsl_sc]; exact ⟨rfl, rfl⟩
  have hstat_sl : FullDeduceStaticEq s1.core sl.core := by
    rw [hsl_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases ok
  · simp only [wp_jnz]
    refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
    have hstat2 : FullDeduceStaticEq s0.core s2.core :=
      ⟨hstat_sl.cv.trans hs1.stat.cv, hstat_sl.cl.trans hs1.stat.cl,
       hstat_sl.te.trans hs1.stat.te, hstat_sl.trl.trans hs1.stat.trl,
       hstat_sl.lvl.trans hs1.stat.lvl, hstat_sl.rsns.trans hs1.stat.rsns,
       hstat_sl.vals.trans hs1.stat.vals, hstat_sl.fuel.trans hs1.stat.fuel,
       hstat_sl.dm.trans hs1.stat.dm, hstat_sl.lm.trans hs1.stat.lm⟩
    have hrefs2_s0 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0 := by
      rw [hrefs2]; unfold fullArenaClauseRefs fullArenaClauseRefsCore
      rw [show sl_ant.core = sl.core from rfl, hsl_c]; exact hs1.hrefs
    have hext02 : FullExtScratchPres s0 s2 :=
      fullExtScratchPres_trans hs1.ext (fullExtScratchPres_trans hext_s1_ant hext2_p)
    have hws2_02 : s2.scratch.work_stk2 = s0.scratch.work_stk2 :=
      hws2_2.trans (by change sl.scratch.work_stk2 = s0.scratch.work_stk2
                       rw [hsl_sc]; exact hs1.ws2)
    exact ded_rsn_clear_ret0_wp hClear hs0_cut hext2 hlen2 hw2 hcov2 hnd2 hext02 hws2_02
      hrefs2_s0 hstat2 hm2 hRet0
  · obtain ⟨hrsn_ne, hant_spec, hok_lits⟩ := h_ok rfl
    simp only [wp_jnz]
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    let s3 : FullState :=
      { s2 with scratch := { s2.scratch with res_sz := s2.scratch.res_sz - 1#64 } }
    have hsem := deduce_loop_rsn_sem hs1 hidx_te hp_get hm_p hl_p hrsn_get
      (show sl_ant.core = _ from hsl_c)
      (show sl_ant.scratch = _ by change { sl.scratch with ant_sz := 0#64 } = _; rw [hsl_sc])
      hlen_ant rfl hlen2 hw2 hcov2 hext2_p hws2_2 htl2_ge htl2_cv htc2_ge hrefs2 hcl2 hmp htp
      hnm hnt hnd_j hcnt hres2 hrsn_ne hant_spec hok_lits rfl
    obtain ⟨hidx_cut, hpos_res, hs3_inv, hrsn_ant, hall_mrk_sl⟩ := hsem
    have hm2_f := fullM6HdrMem_focus_full hm2
    c0_hsteps_nogrp
    refine wp_join_state1 (fun s_j : FullState => s_j.scratch.res_sz)
      (fun s_j m_j => s_j = s3 ∧
        (FullMem c s_j ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m_j) ?_ ?_
    · rintro _ s_j m_j ⟨rfl, hm3_f⟩
      c0_hsteps_nogrp
      refine wp_join0
        (fun m_j => ∃ cut_j s_j, cut_j ≤ s_j.core.trail_end ∧ s_j.core.tmp_cnt = tc' ∧
          FullDeduceStateInv c F0 F_cur cut_j idx' s0 s_j ∧ M6HdrExtOk ext2 ∧
          (FullM6HdrMem c ext2 s_j ⋆ R) m_j) ?_ ?_
      · rintro _ m_j ⟨cut_j, s_j, hcut_j, htc_j, hsj_inv, hext_j, hm_j⟩
        simp only [Blocks.get]; rw [wp_jump]
        exact htc_j ▸ hJs cut_j ext2 s_j m_j hcut_j hext_j hsj_inv hm_j
      · intro Js_1 hJs_1
        have hfail : ∀ m_f,
            (FullMem c s3 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m_f → Js_1 () m_f :=
          fun m_f hm_f =>
            hJs_1 m_f ⟨cut_cur, s3, hs3_inv.hw.cut_le, rfl, hs3_inv, hext2,
              fullM6HdrMem_unfocus_full hm_f⟩
        c0_hsteps_nogrp
        · have hnb : rsn &&& 0x80000000#32 = 0#32 := by assumption
          have hrsz_lt' : s3.scratch.res_sz < s3.scratch.ant_sz :=
            BitVec.lt_def.mpr (by assumption)
          obtain ⟨hrsn_ref, hrsn_garb, hant_eq⟩ := hrsn_ant hnb
          have hstep1 : steps + 1#64 = 1#64 →
              s3.core.confl_type = s0.core.confl_type ∧ s3.core.confl_ref = s0.core.confl_ref ∧
              idx' < cut0 := by
            intro hs1
            have hs0 : steps = 0#64 := by
              apply BitVec.eq_of_toNat_eq
              have h := congrArg BitVec.toNat hs1
              rw [BitVec.toNat_add] at h
              change (steps.toNat + 1) % 2 ^ 64 = 1 at h
              rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt steps.isLt) with hlt | heq
              · rw [Nat.mod_eq_of_lt hlt] at h; exact Nat.succ_inj.mp h
              · rw [Nat.succ_eq_add_one] at heq
                rw [heq, Nat.mod_self] at h
                exact False.elim (Nat.zero_ne_one h)
            obtain ⟨hcut_eq, hct_eq, hcr_eq⟩ := hstep0 hs0
            have hct3 : s3.core.confl_type = s1.core.confl_type := by
              change s2.core.confl_type = s1.core.confl_type
              change sl.core.confl_type = s1.core.confl_type; rw [hsl_c]
            have hcr3 : s3.core.confl_ref = s1.core.confl_ref := by
              change s2.core.confl_ref = s1.core.confl_ref
              change sl.core.confl_ref = s1.core.confl_ref; rw [hsl_c]
            exact ⟨hct3.trans hct_eq, hcr3.trans hcr_eq, hcut_eq ▸ hidx_cut⟩
          have hall_mrk : ∀ l ∈ fullArenaClauseLits s3 rsn.toNat, l / 2 ≠ p_bv.toNat / 2 →
              0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat →
              s3.core.mrk[l / 2]?.getD 0#8 ≠ 0#8 := by
            intro l hl hne hpos
            have hl_sl : l ∈ fullRsnLits sl_ant rsn := by
              unfold fullRsnLits
              rw [ite_eq_right hrsn_ne, ite_eq_right (fun h => h hnb)]
              have hcl := (hcl2 rsn.toNat (href_ant hrsn_ne hnb)).2.2
              have h32 : fullArenaClauseLits s3 rsn.toNat =
                  fullArenaClauseLits s2 rsn.toNat := by
                unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rfl
              rw [h32, hcl] at hl; exact hl
            exact hall_mrk_sl l hl_sl hne hpos
          have hp_get3 : (s3.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
            change (s2.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat
            rw [show s2.core.trl = sl_ant.core.trl from rfl,
                show sl_ant.core.trl = sl.core.trl from rfl, hsl_c]; exact hp_get
          have hrsn_get3 : s3.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
            change s2.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn
            rw [show s2.core.rsns = sl_ant.core.rsns from rfl,
                show sl_ant.core.rsns = sl.core.rsns from rfl, hsl_c]; exact hrsn_get
          have hl_p3 : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level := by
            change (s2.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s2.core.cur_level
            rw [show s2.core.lvl = sl_ant.core.lvl from rfl,
                show sl_ant.core.lvl = sl.core.lvl from rfl,
                show s2.core.cur_level = sl_ant.core.cur_level from rfl,
                show sl_ant.core.cur_level = sl.core.cur_level from rfl, hsl_c]; exact hl_p
          have hidx_te3 : idx' < s3.core.trail_end := by
            rw [hs3_inv.stat.te, ← hs1.stat.te]; exact hidx_te
          have hm3_u := fullM6HdrMem_unfocus_full ‹_›
          refine wp_join0 (fun m_j => Js_1 () m_j) (fun _ _ h => h) fun Js_3 hJs_3 => ?_
          c0_hsteps_nogrp
          · have hasz3' : s3.scratch.ant_sz = 3#64 := by assumption
            exact ded_loop_otfs_bin_wp hClear hBin hSub hs0_cut hconfl0 hcur_pos hext2 hs3_inv
              hidx_te3 hidx_cut hp_get3 hrsn_get3 hl_p3 hnb hrsn_ref hrsn_garb hall_mrk hant_eq
              hasz3' hrsz_lt' hstep1 hm3_u
              (fun cj sj mj hc ht hi he hm =>
                hJs_3 mj (hJs_1 mj ⟨cj, sj, hc, ht, hi, he, hm⟩))
              hRet2
          · exact ded_loop_otfs_large_wp hClear hLarge hSub hs0_cut hconfl0 hcur_pos hext2 hs3_inv
              hidx_te3 hidx_cut hp_get3 hrsn_get3 hl_p3 hrsn_ne hnb hrsn_ref hrsn_garb hall_mrk
              hant_eq hrsz_lt' hstep1 hm3_u
              (fun cj sj mj hc ht hi he hm =>
                hJs_3 mj (hJs_1 mj ⟨cj, sj, hc, ht, hi, he, hm⟩))
              hRet2
        · exact hfail _ ‹_›
        · exact hfail _ ‹_›
        · exact hfail _ ‹_›
    · intro Js hJs
      c0_hsteps_nogrp
      exact hJs s3 _ ⟨rfl, ‹_›⟩
