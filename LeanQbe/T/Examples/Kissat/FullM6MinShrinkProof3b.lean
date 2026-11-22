module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3b1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B` Proof Shard 3b (`full_ana_failed_lit_m6`)

Proves `full_ana_failed_lit_m6_wp` certifying level-1 failed-literal / multi-UIP resolution,
VMTF bumping (`full_bump_analyzed_m6`), backtracking to level 0 (`full_backtrack`), and unit
propagation / UNSAT detection (`full_assign_lvl`, `r = 20#64` / `1#64` / `0#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullLearnAnaSpecs
open LeanQbe.T.Examples.Kissat.Full.FullLearnAnaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullLearnAnaTactics
open Kraken.Bedrock2.Test

section Helpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem fl_bv32_lshr1_loc (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem fl_bv32_xor1_loc (x : BitVec 32) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  fl_bv32_xor1 x

private theorem fl_bv32_setWidth64_loc (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem fl_sext32_64_1 :
    BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

private theorem fl_bv32_lshr_nat1 (x : BitVec 32) :
    (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem fl_bv32_0_add (x : BitVec 32) : 0#32 + x = x := by simp

attribute [local bv_c0] fl_bv32_lshr1_loc fl_bv32_xor1_loc fl_bv32_setWidth64_loc
  fl_sext32_64_1 fl_bv32_lshr_nat1 fl_bv32_0_add

private theorem fl_bv32_lit_neq_ff {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    l ≠ 0xFFFFFFFF#32 := by
  intro h
  have h0 := congrArg BitVec.toNat h
  rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 from rfl] at h0
  omega

private theorem fl_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

end Helpers

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev flPostLoopBlock (c : FullCfg) (cv : BitVec 64) (nf : BitVec 32) :
    Blocks Val Cont [i64] [[i64, i64, .bool, i64, i32, .bool]] :=
  Blocks.cons (fun (p : Tup Val [i64, i64, .bool, i64, i32, .bool]) =>
    Expr.jnz (Arg.var p.snd.snd.snd.snd.snd.fst)
      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
        Expr.ret (Arg.imm 0, ()))
      (Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var p.snd.fst, Arg.var cv, ()))
        fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.ret (Arg.imm 0, ()))
          (Expr.let_ (Op.mk (.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun p_2 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p_2.fst, ())) fun p_3 =>
            Expr.store (t := i32) (Arg.var nf) (Arg.var p_3.fst) (
            Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 192, ())) fun p_4 =>
            Expr.store (t := i64) (Arg.var p.fst) (Arg.var p_4.fst) (
            Expr.call (as := [i64]) (bs := []) "full_bump_analyzed_m6" (Arg.var c.hdr, ()) fun _ =>
            Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
              (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            @Expr.group Val Cont [i64] [[i64]] (fun Js_lp =>
              Blocks.cons (fun (p_8 : Tup Val [i64]) =>
                Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var p_8.fst, Arg.var p.fst, ())) fun p_c =>
                Expr.jnz (Arg.var p_c.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p_8.fst, Arg.imm 4, ())) fun p_m =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p_m.fst, ())) fun p_a =>
                  Expr.load i32 (Arg.var p_a.fst) fun ld =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_z =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p_z.fst, ())) fun p_v =>
                  Expr.load i8 (Arg.var p_v.fst) fun ld_1 =>
                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_t0 =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_1, ())) fun p_9 =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_t0.fst, ())) fun p_z0 =>
                  Expr.let_ (Op.mk (.cmp .slt i32 .bool rfl)
                      (Arg.var p_9.fst, Arg.var p_z0.fst, ())) fun p_s =>
                  Expr.jnz (Arg.var p_s.fst)
                    (Expr.ret (Arg.imm 20, ()))
                    (@Expr.group Val Cont [i64] [[]] (fun _ =>
                      Blocks.cons (fun _ =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var p_8.fst, Arg.imm 1, ()))
                          fun p_k1 =>
                        Expr.jump Js_lp.fst (Arg.var p_k1.fst, ()))
                      Blocks.nil) fun Js_nxt =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_z2 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p_z2.fst, ())) fun p_v2 =>
                    Expr.load i8 (Arg.var p_v2.fst) fun ld_2 =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_t1 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_2, ())) fun p_10 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_t1.fst, ())) fun p_z1 =>
                    Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                        (Arg.var p_10.fst, Arg.var p_z1.fst, ())) fun p_eq =>
                    Expr.jnz (Arg.var p_eq.fst)
                      (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
                        (Arg.var c.hdr, Arg.var ld, Arg.imm 0xFFFFFFFF, Arg.imm 0, ())
                        fun _ => Expr.jump Js_nxt.fst ())
                      (Expr.jump Js_nxt.fst ())))
                  (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_c1 =>
                  Expr.load i64 (Arg.var p_c1.fst) fun ld =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1, ())) fun p_c2 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_9 =>
                  Expr.store (t := i64) (Arg.var p_c2.fst) (Arg.var p_9.fst) (
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 344, ())) fun p_l1 =>
                  Expr.load i64 (Arg.var p_l1.fst) fun ld_1 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.imm 1, ())) fun p_l2 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 344, ())) fun p_10 =>
                  Expr.store (t := i64) (Arg.var p_l2.fst) (Arg.var p_10.fst) (
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1032, ())) fun p_it =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var p_it.fst)
                    (Expr.ret (Arg.imm 1, ()))))))
              Blocks.nil) fun Js_lp => Expr.jump Js_lp.fst (Arg.imm 0, ()))))))
    Blocks.nil

private theorem fl_post_loop_wp {Γ Q X}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s : FullState} {R : Mem 64 → Prop} {not_failed : BitVec 32}
    (hcut : Full.FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hnf_lt : not_failed.toNat < 2 * s.core.cur_vars)
    (hnf_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_failed.toNat]))
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    {unres_f ucnt_f : Nat} {done_f : Bool} {t_f : Nat} {unit_f : BitVec 32} {err_f : Bool}
    {s_f : FullState} {m_f : Mem 64}
    (hok_f : FailedStateOk c s s_f cut) (_ht_f_le : t_f ≤ s.core.trail_end)
    (hucnt_le : ucnt_f ≤ s.core.cur_vars)
    (htmp_f : ∀ k < ucnt_f, (s_f.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s_f.core.tmp[k]?.getD 0#32).toNat]))
    (_hact_f : !err_f → !done_f → unres_f = (flIdxs s.core s_f.core.mrk t_f).length ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s.core s_f.core.mrk t_f)))
    (hm_f : (FullMem c s_f ⋆ R) m_f) :
    wp Γ Q X ((flPostLoopBlock c (BitVec.ofNat 64 s.core.cur_vars) not_failed).get
      Member.here (BitVec.ofNat 64 unres_f, BitVec.ofNat 64 ucnt_f, done_f,
        BitVec.ofNat 64 t_f, unit_f, err_f, ())) m_f := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hcut
  have hcl := hlen0.core_ok
  have hcv_le := hcl.cur_vars_le
  dsimp only [flPostLoopBlock]
  rw [Blocks.get_here]; dsimp only
  c0_hsplit
  · -- `if (err)`: `full_clear_ana(h); return 0;`
    have herr : err_f = true := by assumption
    c0_hsteps_nogrp; c0_hcall hClear
    refine ⟨c, s_f, R, rfl, hok_f.len, hm_f, fun mrk' m_c hml' _ _ hcov_c hm_c => ?_⟩
    c0_hsteps
    let s_c : FullState :=
      { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
    have hok_c : FailedStateOk c s s_c cut :=
      ⟨⟨{ hok_f.len.core_ok with mrk_len := hml', min_clr_len_le := Nat.zero_le _ },
        hok_f.len.scratch_ok⟩,
       by dsimp [s_c]; rw [hok_f.core], by dsimp [s_c]; rw [hok_f.scr],
       ⟨Nat.zero_le _, by simp [s_c], fun _ hk => absurd hk (Nat.not_lt_zero _),
        fun v hv hnz => absurd (hcov_c hok_f.cov v hv) hnz⟩,
       fl_mb_empty (fun v hv => hcov_c hok_f.cov v (by omega))⟩
    exact hQ 0#64 s_c m_c hok_c.len (Or.inl rfl)
      (by rw [hok_c.core]) (by rw [hok_c.core]) (by rw [hok_c.scr])
      (fun h => by cases h)
      (fun _ => fl_otfsInvW_of_ok hcut hok_c (hcov_c hok_f.cov))
      (fun h => by cases h) hm_c
  · c0_hsplit
    · -- `if (ucnt >= cv)`: `full_clear_ana(h); return 0;`
      c0_hsteps_nogrp; c0_hcall hClear
      refine ⟨c, s_f, R, rfl, hok_f.len, hm_f, fun mrk' m_c hml' _ _ hcov_c hm_c => ?_⟩
      c0_hsteps
      let s_c : FullState :=
        { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
      have hok_c : FailedStateOk c s s_c cut :=
        ⟨⟨{ hok_f.len.core_ok with mrk_len := hml', min_clr_len_le := Nat.zero_le _ },
          hok_f.len.scratch_ok⟩,
         by dsimp [s_c]; rw [hok_f.core], by dsimp [s_c]; rw [hok_f.scr],
         ⟨Nat.zero_le _, by simp [s_c], fun _ hk => absurd hk (Nat.not_lt_zero _),
          fun v hv hnz => absurd (hcov_c hok_f.cov v hv) hnz⟩,
         fl_mb_empty (fun v hv => hcov_c hok_f.cov v (by omega))⟩
      exact hQ 0#64 s_c m_c hok_c.len (Or.inl rfl)
        (by rw [hok_c.core]) (by rw [hok_c.core]) (by rw [hok_c.scr])
        (fun h => by cases h)
        (fun _ => fl_otfsInvW_of_ok hcut hok_c (hcov_c hok_f.cov))
        (fun h => by cases h) hm_c
    · -- `tmp[ucnt] = not_failed; ucnt = ucnt + 1; tmp_len = ucnt; bump; clear; backtrack; unit`
      have hucnt_lt : ucnt_f < s.core.cur_vars := by
        have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
        have huc64 : ucnt_f < 2 ^ 64 := by omega
        have hnge : ¬ s.core.cur_vars % 2 ^ 64 ≤ ucnt_f % 2 ^ 64 := by
          simpa only [hok_f.core] using (by assumption : _)
        rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt huc64] at hnge
        exact Nat.lt_of_not_le hnge
      have hucnt_tmp : (BitVec.ofNat 64 ucnt_f).toNat < s_f.core.tmp.length := by
        rw [bv64_ofNat_toNat (by omega), hok_f.len.core_ok.tmp_len_arr]; omega
      have hucnt1_bv : (BitVec.ofNat 64 ucnt_f + 1).toNat = ucnt_f + 1 := by
        rw [show (1 : BitVec 64) = 1#64 from rfl,
          fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
          bv64_ofNat_toNat (by omega)]
      c0_hsteps_nogrp
      let s_t : FullState :=
        { s_f with core :=
          { s_f.core with tmp := s_f.core.tmp.set ucnt_f not_failed,
                          tmp_len := ucnt_f + 1 } }
      have hok_t0 : FailedStateOk c s
          { s_f with core := { s_f.core with tmp := s_f.core.tmp.set ucnt_f not_failed } }
          cut :=
        fl_failedStateOk_with_tmp hok_f (by simp [hok_f.len.core_ok.tmp_len_arr])
      have hok_t : FailedStateOk c s s_t cut :=
        ⟨⟨{ hok_t0.len.core_ok with tmp_len_le := by dsimp [s_t]; omega },
          hok_t0.len.scratch_ok⟩,
         by
           dsimp only [s_t]
           exact congrArg (fun k => { k with
             tmp := s_f.core.tmp.set ucnt_f not_failed,
             tmp_len := ucnt_f + 1 }) hok_f.core,
         hok_t0.scr, hok_t0.cov, hok_t0.mb⟩
      have hm_t : (FullMem c s_t ⋆ R) m := by
        simpa only [s_t, bv64_ofNat_toNat (by omega : ucnt_f < 2 ^ 64), hucnt1_bv] using hm
      have htmp_t : ∀ k < ucnt_f + 1,
          (s_t.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(s_t.core.tmp[k]?.getD 0#32).toNat]) := by
        intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · dsimp [s_t]; rw [List.getElem?_set_ne (by omega)]; exact htmp_f k hlt
        · dsimp [s_t]
          rw [List.getElem?_set_self (by rw [hok_f.len.core_ok.tmp_len_arr]; omega),
            Option.getD_some]
          exact ⟨hnf_lt, hnf_ent⟩
      try clear hm_f
      c0_hcall hBumpAna
      refine ⟨c, s_t, R, rfl, hok_t.len, hok_t.cov, hm_t, ?_⟩
      intro mrk_b mcl_b sc_b m_b _ hlen_b hcov_b hpres_b hws2_b hm_b
      let s_b : FullState :=
        { core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b }
      c0_hsteps_nogrp; c0_hcall hClear
      refine ⟨c, s_b, R, rfl, hlen_b, hm_b, fun mrk_c m_c hml_c _ _ hcov_c hm_c => ?_⟩
      let s_c : FullState :=
        { s_b with core := { s_b.core with mrk := mrk_c, min_clr_len := 0 } }
      have hsc_eq : s_c.core =
          { s.core with mrk := mrk_c, tmp := s_t.core.tmp,
                        tmp_cnt := s.core.tmp_cnt, tmp_len := ucnt_f + 1,
                        min_clr_len := 0 } := by
        dsimp only [s_c, s_b]
        exact congrArg (fun k => { k with mrk := mrk_c, min_clr_len := 0 }) hok_t.core
      have hlen_c : s_c.LengthsOk c :=
        ⟨{ hlen_b.core_ok with mrk_len := hml_c, min_clr_len_le := Nat.zero_le _ },
         hlen_b.scratch_ok⟩
      have hw_c : Full.FullWitnessCutInv c F0 F_cur cut s_c.core := by
        rw [hsc_eq]
        exact Full.deduce_same_core_cut hw0 mrk_c s_t.core.tmp s.core.tmp_cnt
          (ucnt_f + 1) 0
      have hmrk_c : ∀ v < c.max_vars, s_c.core.mrk[v]?.getD 0#8 = 0#8 :=
        hcov_c hcov_b
      have hnd_c : Full.FullArenaVarsNodup s_c := by
        unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs
          Full.fullArenaClauseRefsCore Full.fullArenaClauseGarb
          Full.fullArenaClauseGarbCore Full.fullArenaClauseLits
          Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore
          Full.fullArenaHdrCore
        rw [hsc_eq]; exact hnd0
      have hext_pres_c : Full.FullExtScratchPres s s_c :=
        ⟨by dsimp only [s_c, s_b]
            exact hpres_b.1.trans (by rw [hok_t.scr]),
         by dsimp only [s_c, s_b]
            exact hpres_b.2.trans (by rw [hok_t.scr])⟩
      have hsc_core_cl : s_c.core.cur_level = 1 := by rw [hsc_eq]; exact hcl1
      have hsc_otfs : Full.FullOtfsInvW c F0 F_cur s_c :=
        ⟨hlen_c, hw_c.toFullOtfsWitnessInv,
         ⟨hmrk_c, fun l hl => by rw [hsc_eq]; exact hlm0.2 l hl⟩,
         hnd_c,
         Full.FullExtScratchOk.of_pres hext0 hext_pres_c (fun _ hr => by
           unfold Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore at hr ⊢
           rw [hsc_eq]; exact hr),
         by rw [hsc_eq]; exact hdm0⟩
      have hws2_c : s_c.scratch.work_stk2 = s.scratch.work_stk2 := by
        dsimp only [s_c, s_b]
        exact hws2_b.trans (by rw [hok_t.scr])
      clear hm_t hm_b
      c0_hsteps_nogrp; c0_hcall hBacktrack
      refine ⟨c, s_c, R, rfl, hlen_c, by omega, fun _ => by omega,
        hw_c.trail_lits_lt, hm_c, ?_⟩
      intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt
        m_bt _ hbt_len hbt_te hbt_prop hbt_cl hbt_pres hbt_sc _ _ _ hbt_wo hm_bt
      let s_bt : FullState :=
        { s_c with
          core := { s_c.core with
            vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
            trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
            cur_level := cl_bt, unassigned := unass_bt }
          scratch := sc_bt }
      have hw_bt := hbt_wo F0 F_cur hw_c.toFullOtfsWitnessInv
        (by rw [hsc_core_cl]; decide)
      have hbt_sp : Full.FullSparseInvW c F0 F_cur s_bt := by
        refine ⟨hbt_len, hw_bt, hsc_otfs.2.2.1, ?_,
          Full.FullExtScratchOk.of_pres hsc_otfs.2.2.2.2.1 hbt_pres.1
            (fun _ h => by
              unfold Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore at h ⊢
              exact h),
          hsc_otfs.2.2.2.2.2⟩
        unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs
          Full.fullArenaClauseRefsCore Full.fullArenaClauseGarb
          Full.fullArenaClauseGarbCore Full.fullArenaClauseLits
          Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore
          Full.fullArenaHdrCore
        exact hsc_otfs.2.2.2.1
      have hbt_cl0 : s_bt.core.cur_level = 0 := by
        dsimp only [s_bt]; rw [hbt_cl]; exact Nat.min_zero _
      have hbt_cv : s_bt.core.cur_vars = s.core.cur_vars := by
        dsimp only [s_bt]; rw [hsc_eq]
      have hbt_fu : s_bt.core.fuel = s.core.fuel := by
        dsimp only [s_bt]; rw [hsc_eq]
      have hbt_dm : s_bt.core.dense_mode = s.core.dense_mode := by
        dsimp only [s_bt]; rw [hsc_eq]
      have hbt_ws2 : s_bt.scratch.work_stk2 = s.scratch.work_stk2 :=
        hbt_pres.2.2.1.trans hws2_c
      have hbt_tmp : s_bt.core.tmp = s_t.core.tmp := rfl
      clear hm_c
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (α := Nat × FullState)
        (proj := fun st => (BitVec.ofNat 64 st.1, ()))
        (μ := fun st => (ucnt_f + 1) - st.1)
        (Inv := fun st m1 =>
          st.1 ≤ ucnt_f + 1 ∧ Full.FullSparseInvW c F0 F_cur st.2 ∧
          st.2.core.cur_level = 0 ∧ st.2.core.cur_vars = s.core.cur_vars ∧
          st.2.core.fuel = s.core.fuel ∧ st.2.core.dense_mode = s.core.dense_mode ∧
          st.2.scratch.work_stk2 = s.scratch.work_stk2 ∧ st.2.core.tmp = s_t.core.tmp ∧
          (FullMem c st.2 ⋆ R) m1) ?_ ?_
      · intro Jk hJk; c0_hsteps
        exact hJk (0, s_bt) m_bt ⟨Nat.zero_le _, hbt_sp, hbt_cl0, hbt_cv, hbt_fu,
          hbt_dm, hbt_ws2, hbt_tmp, hm_bt⟩
      · intro Jk ⟨k, s_k⟩ m_k
          ⟨hk_le, hsp_k, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, hm_k⟩ ih_k
        dsimp only at hk_le hsp_k hcl_k hcv_k hfu_k hdm_k hws2_k htmp_k hm_k ih_k
        rw [Blocks.get_here]; dsimp only
        have hkl_k := hsp_k.1.core_ok
        have hk_lt_bd : ucnt_f + 1 < 2 ^ 64 := by omega
        c0_hsplit
        · have hk_lt : k < ucnt_f + 1 := by
            have hk64 : k < 2 ^ 64 := by omega
            have hlt : k % 2 ^ 64 < (ucnt_f + 1) % 2 ^ 64 := by
              simpa only [BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hk_lt_bd] at hlt
          have hk_tmp : (BitVec.ofNat 64 k).toNat < s_k.core.tmp.length := by
            rw [bv64_ofNat_toNat (by omega), hkl_k.tmp_len_arr]; omega
          let u := s_k.core.tmp[(BitVec.ofNat 64 k).toNat]'hk_tmp
          have hu_prop := htmp_t k hk_lt
          have hu_eq : u.toNat = (s_t.core.tmp[k]?.getD 0#32).toNat := by
            have hk_t : k < s_t.core.tmp.length := by rw [← htmp_k, hkl_k.tmp_len_arr]; omega
            rw [List.getElem?_eq_getElem hk_t, Option.getD_some]
            dsimp [u]
            exact congrArg BitVec.toNat (fl_getElem_congr_list htmp_k (bv64_ofNat_toNat (by omega)))
          have hu_lt : u.toNat < 2 * s_k.core.cur_vars := by rw [hu_eq, hcv_k]; exact hu_prop.1
          have hu_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]) := by
            rw [hu_eq]; exact hu_prop.2
          have hu_val_lt : (u.setWidth 64).toNat < s_k.core.vals.length := by
            rw [fl_bv32_setWidth64, hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
          have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
            BitVec.eq_of_toNat_eq (by
              rw [show (1 : BitVec 64) = 1#64 from rfl,
                fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
          c0_hsplit
          · -- `vals[u] < 0`: UNSAT! Return `20#64`
            have hu_ff : s_k.core.vals[u.toNat]?.getD 0#8 = 0xFF#8 := by
              have hdom := hsp_k.2.1.vals_domain u.toNat hu_lt
              have hidx : u.toNat < s_k.core.vals.length := by
                rw [hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
              rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hdom ⊢
              exact fl_i8_slt0_neg_iff hdom (by simpa [u] using (by assumption : _))
            obtain ⟨ti, hti_te, hti_eq⟩ := (hsp_k.2.1.vals_false_iff u.toNat hu_lt).mp hu_ff
            have hti_lvl0 :
                (s_k.core.lvl[(s_k.core.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
              have hle := hsp_k.2.1.lvl_le ti hti_te; omega
            have hnu_ent := hsp_k.2.1.level0_sound ti hti_te hti_lvl0
            rw [hti_eq] at hnu_ent
            have hunsat : F0.Unsat :=
              hsp_k.2.1.ext_sound.2 (fl_unsat_of_unit_pair hu_ent hnu_ent)
            c0_hsteps
            exact hQ 20#64 s_k m_k hsp_k.1 (Or.inr (Or.inr rfl)) hcv_k hfu_k hws2_k
              (fun _ => ⟨hunsat, hsp_k.toOtfs, by omega, hdm_k⟩)
              (fun h => by cases h) (fun h => by cases h) hm_k
          · refine wp_join_state (ts := []) (α := FullState) (proj := fun _ => ())
              (Inv := fun st m1 =>
                Full.FullSparseInvW c F0 F_cur st ∧ st.core.cur_level = 0 ∧
                st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
                st.core.dense_mode = s.core.dense_mode ∧
                st.scratch.work_stk2 = s.scratch.work_stk2 ∧
                st.core.tmp = s_t.core.tmp ∧ (FullMem c st ⋆ R) m1) ?_ ?_
            · intro _ s_n m_n ⟨hsp_n, hcl_n, hcv_n, hfu_n, hdm_n, hws2_n, htmp_n, hm_n⟩
              rw [Blocks.get_here]; c0_hsteps; rw [hk1_bv]
              exact ih_k (k + 1, s_n) m_n (by omega)
                ⟨by omega, hsp_n, hcl_n, hcv_n, hfu_n, hdm_n, hws2_n, htmp_n, hm_n⟩
            · intro Jk1 hJk1
              c0_hsplit
              · -- `vals[u] == 0`: `full_assign_lvl(h, u, -1, 0)`
                have hu_z : s_k.core.vals[u.toNat]?.getD 0#8 = 0#8 := by
                  have hidx : u.toNat < s_k.core.vals.length := by
                    rw [hkl_k.vals_len]; have := hkl_k.cur_vars_le; omega
                  rw [List.getElem?_eq_getElem hidx, Option.getD_some]
                  exact fl_i8_sext32_eq0_iff.mp (by simpa [u] using (by assumption : _))
                have hte_lt : s_k.core.trail_end < c.max_vars := by
                  have := hsp_k.2.1.trail_end_lt_of_unassigned hu_lt hu_z
                  have := hkl_k.cur_vars_le; omega
                have hng : ¬ (s_k.core.cur_vars ≤ u.toNat / 2 ∨ c.max_vars ≤ s_k.core.trail_end ∨
                    s_k.core.vals[u.toNat]?.getD 0#8 ≠ 0#8) := by
                  simp only [hu_z, ne_eq, not_true_eq_false, or_false]; omega
                c0_hsteps_nogrp; c0_hcall hAssignLvl
                refine ⟨c, s_k, R, rfl, hsp_k.1, hm_k, ?_⟩
                rw [ite_eq_right (by simpa only [u, Arg.val_var] using hng)]
                dsimp only
                intro flags' unass' phases' m_n hfll' hphl' hm_n
                let s_n : FullState :=
                  { s_k with
                    core :=
                      { s_k.core with
                        vals := (s_k.core.vals.set u.toNat 1#8).set (u.toNat ^^^ 1) 0xFF#8
                        flags := flags', lvl := s_k.core.lvl.set (u.toNat / 2) 0#32
                        rsns := s_k.core.rsns.set (u.toNat / 2) 0xFFFFFFFF#32
                        trl := s_k.core.trl.set s_k.core.trail_end u
                        trail_pos := s_k.core.trail_pos.set (u.toNat / 2)
                          (BitVec.ofNat 32 s_k.core.trail_end)
                        trail_end := s_k.core.trail_end + 1, unassigned := unass'
                        unflushed := s_k.core.unflushed + 1#64 }
                    scratch := { s_k.scratch with phases := phases' } }
                have hsp_n := fl_assign0_preserves_sparseW hsp_k hcl_k hu_lt hu_z hu_ent hfll' hphl'
                  (unass' := unass') (unflushed' := s_k.core.unflushed + 1#64)
                c0_hsteps
                refine hJk1 s_n m_n ⟨hsp_n, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, ?_⟩
                simpa only [s_n, u, Arg.val_var, Arg.val_imm,
                  show (0 : BitVec 32) = 0#32 from rfl,
                  show ((0#32 : BitVec 32) = 0#32) ↔ True by decide, ↓reduceIte,
                  show (BitVec.ofNat 32 0 = 0#32) from rfl,
                  show (4294967295#32 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm_n
              · c0_hsteps
                exact hJk1 s_k m_k ⟨hsp_k, hcl_k, hcv_k, hfu_k, hdm_k, hws2_k, htmp_k, hm_k⟩
        · -- Loop finished: `conflicts += 1; learned_lits += 1; iterating = 1; return 1;`
          c0_hsteps
          let s_fin : FullState :=
            { s_k with scratch :=
              { s_k.scratch with
                conflicts := s_k.scratch.conflicts + 1#64,
                learned_lits := s_k.scratch.learned_lits + 1#64,
                iterating := 1#64 } }
          have hsp_fin' : Full.FullSparseInvW c F0 F_cur s_fin :=
            ⟨⟨hkl_k, { hsp_k.1.scratch_ok with }⟩, hsp_k.2.1, hsp_k.2.2.1,
              hsp_k.2.2.2.1, Full.FullExtScratchOk.of_pres hsp_k.2.2.2.2.1 ⟨rfl, rfl⟩
                (fun _ h => h),
              hsp_k.2.2.2.2.2⟩
          exact hQ 1#64 s_fin m hsp_fin'.1 (Or.inr (Or.inl rfl))
            hcv_k hfu_k hws2_k (fun h => by cases h) (fun h => by cases h)
            (fun _ => ⟨hsp_fin', by dsimp [s_fin]; omega⟩)
            (by simpa only [s_fin, show (1 : BitVec 64) = 1#64 from rfl] using hm)

/-! ## 3. Main `full_ana_failed_lit_m6_wp` Proof -/

/-- Wave-2B level-1 failed-literal / multi-UIP resolution `Func.wp` certification. -/
theorem full_ana_failed_lit_m6_wp (Γ : Env)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpAna : ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6" [i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m6AnaFailedLitSpec a m Q X →
      Func.wp Γ full_ana_failed_lit_m6_body a m Q X := by
  intro a m0 Q X hspec
  refine m6AnaFailedLitSpec_elim hspec fun c F0 F_cur cut s R ha hcut _ hconfl hm0 hQ => ?_
  subst ha
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hcut
  have hcl := hlen0.core_ok
  have hcv_le := hcl.cur_vars_le
  have hte_le := hcl.trail_end_le
  have hcur_le := hw0.cur_level_le
  unfold Func.wp full_ana_failed_lit_m6_body
  dsimp only
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
      (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
  · have hcl1 : s.core.cur_level = 1 := by bv_omega
    c0_hsplit
    · c0_hsteps
      exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
        (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
    · have hcv_pos : 0 < s.core.cur_vars := by bv_omega
      have hfdec1_len : 1 < s.core.frame_dec.length := by rw [hcl.frame_dec_len]; omega
      c0_hsplit
      · c0_hsteps
        exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
          (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
      · let failed := s.core.frame_dec[(1#64 : BitVec 64).toNat]'(by simpa using hfdec1_len)
        let fv := failed >>> 1
        let not_failed := failed ^^^ 1#32
        have hfv_lt : fv.toNat < s.core.cur_vars := by
          have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
          have hnge : ¬ s.core.cur_vars % 2 ^ 64 ≤ failed.toNat / 2 := by assumption
          rw [Nat.mod_eq_of_lt hcv64] at hnge
          dsimp only [fv]; rw [bv32_lshr_1]; exact Nat.lt_of_not_le hnge
        have hfl_lt : failed.toNat < 2 * s.core.cur_vars := by
          dsimp only [fv] at hfv_lt; rw [bv32_lshr_1] at hfv_lt; omega
        have hfl_val_lt : (failed.setWidth 64).toNat < s.core.vals.length := by
          rw [fl_bv32_setWidth64, hcl.vals_len]; omega
        have hfv_lvl_lt : (fv.setWidth 64).toNat < s.core.lvl.length := by
          rw [fl_bv32_setWidth64, hcl.lvl_len]; omega
        have hfv_rsn_lt : (fv.setWidth 64).toNat < s.core.rsns.length := by
          rw [fl_bv32_setWidth64, hcl.rsns_len]; omega
        c0_hsplit
        · c0_hsteps
          exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
            (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
        · have hfl_val : s.core.vals[failed.toNat]?.getD 0#8 = 1#8 := by
            have hdom := hw0.vals_domain failed.toNat hfl_lt
            have hidx : failed.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
            rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hdom ⊢
            exact fl_i8_pos_of_not_sle hdom
              (by simpa [failed, Bool.not_eq_true] using (by assumption : _))
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
              (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
          · have hfl_lvl1 : (s.core.lvl[failed.toNat / 2]?.getD 0#32).toNat = 1 := by
              have hidx : failed.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
              have heq1 : s.core.lvl[failed.toNat / 2]'hidx = 1#32 := by assumption
              rw [List.getElem?_eq_getElem hidx, Option.getD_some]
              exact congrArg BitVec.toNat heq1
            c0_hsplit
            · c0_hsteps
              exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
                (fun _ => hcut.toOtfs) (fun h => by cases h) hm0
            · have hfl_rsn : s.core.rsns[failed.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
                have hidx : failed.toNat / 2 < s.core.rsns.length := by rw [hcl.rsns_len]; omega
                have heq : s.core.rsns[failed.toNat / 2]'hidx = 0xFFFFFFFF#32 := by assumption
                rw [List.getElem?_eq_getElem hidx, Option.getD_some]; exact heq
              have himp := failedLit_trail_imp hw0 hcl1 hfl_val hfl_lt hfl_lvl1 hfl_rsn
              have hnf_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_failed.toNat]) := by
                have hent := failedLit_not_failed_of_confl hw0 hcl1 hconfl himp
                simpa only [not_failed, fl_bv32_xor1] using hent
              have hnf_lt : not_failed.toNat < 2 * s.core.cur_vars := by
                rw [fl_bv32_xor1]; exact litNeg_lt_two_mul hfl_lt
              c0_hsteps_nogrp
              let s0 : FullState := { s with core := { s.core with min_clr_len := 0 } }
              have hok0 : FailedStateOk c s s0 cut :=
                ⟨⟨{ hcl with min_clr_len_le := Nat.zero_le _ }, hlen0.scratch_ok⟩, rfl, rfl,
                 ⟨Nat.zero_le _, by simp [s0], fun _ hk => absurd hk (Nat.not_lt_zero _),
                  fun v hv hnz => absurd (hlm0.1 v hv) hnz⟩,
                 fl_mb_empty (fun v hv => hlm0.1 v (by omega))⟩
              have hm_s0 : (FullMem c s0 ⋆ R) m := by simpa [s0]
              refine wp_join_state (ts := [i64, .bool]) (α := Nat × Bool × FullState)
                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                (Inv := fun st m1 =>
                  st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2 cut ∧
                  (!st.2.1 → st.1 = (flIdxs s.core st.2.2.core.mrk s.core.trail_end).length ∧
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (flLits s.core st.2.2.core.mrk s.core.trail_end))) ∧
                  (FullMem c st.2.2 ⋆ R) m1) ?_ ?_
              · -- `G@8678` consumer: outer resolution loop + post-loop + unit propagation
                intro Jseed ⟨unres0, done0, s_sd⟩ m_sd
                  ⟨hunres0_le, hok_sd, hact_sd, hm_sd⟩
                dsimp only at hunres0_le hok_sd hact_sd hm_sd
                rw [Blocks.get_here]; dsimp only
                c0_hsteps_nogrp
                let PostIn := Nat × Bool × FullState
                let LpIn := Nat × Nat × Bool × Nat × BitVec 32 × Bool × FullState
                refine wp_join_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
                  (proj := fun st =>
                    (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
                     BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
                  (Inv := fun st m1 =>
                    let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
                    let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
                    FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
                    (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                    (!err → !done →
                      unres = (flIdxs s.core s1.core.mrk t).length ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause (flLits s.core s1.core.mrk t))) ∧
                    (FullMem c s1 ⋆ R) m1) ?_ ?_
                · -- `G@8706` post-loop exit (`if (err)`, `if (ucnt >= cv)`, bump, backtrack, unit
                  -- loop)
                  intro Jexit ⟨unres_f, ucnt_f, done_f, t_f, unit_f, err_f, s_f⟩ m_f
                    ⟨hok_f, ht_f_le, hucnt_le, htmp_f, hact_f, hm_f⟩
                  dsimp only
                  exact fl_post_loop_wp hClear hBumpAna hBacktrack hAssignLvl hcut hcl1
                    hnf_lt hnf_ent hQ hok_f ht_f_le hucnt_le htmp_f hact_f hm_f
                · -- `G@9329` entry & body: `while (!done && !err)`
                  intro Jexit hJexit
                  c0_hsteps_nogrp
                  refine wp_while_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
                    (proj := fun st =>
                      (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
                       BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
                    (μ := fun st => 2 * st.2.2.2.1 + if st.2.2.1 || st.2.2.2.2.2.1 then 0 else 1)
                    (Inv := fun st m1 =>
                      let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
                      let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
                      FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
                      (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                      (!err → !done →
                        unres = (flIdxs s.core s1.core.mrk t).length ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause (flLits s.core s1.core.mrk t))) ∧
                      (FullMem c s1 ⋆ R) m1) ?_ ?_
                  · intro Jlp hJlp; c0_hsteps
                    have hte_sd : s_sd.core.trail_end = s.core.trail_end := by rw [hok_sd.core]
                    simpa only [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
                      show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl, hte_sd] using
                      hJlp (unres0, 0, done0, s.core.trail_end, 0xFFFFFFFF#32, false, s_sd)
                        m_sd ⟨hok_sd, Nat.le_refl _, Nat.zero_le _, (fun _ hk => by cases hk),
                          fun _ hnd => hact_sd hnd, hm_sd⟩
                  · intro Jlp ⟨unres, ucnt, done, t, unit, err, s_lp⟩ m1
                      ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩ ih_lp
                    dsimp only at hok_lp ht_le hucnt_le htmp_ok hact_ok hm1 ih_lp
                    rw [Blocks.get_here]; dsimp only
                    c0_hsplit
                    · -- `done = true` -> exit to `Jexit`
                      c0_hsteps
                      exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
                        ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
                    · have hdone_f : done = false := by assumption
                      c0_hsplit
                      · -- `err = true` -> exit to `Jexit`
                        c0_hsteps
                        exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
                          ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
                      · have herr_f : err = false := by assumption
                        obtain ⟨hunres_len, hact_ent⟩ :=
                          hact_ok (by simp [herr_f]) (by simp [hdone_f])
                        have hunres_bd : unres ≤ s.core.cur_vars :=
                          Nat.le_trans (hunres_len ▸ flIdxs_length_le) (by omega)
                        c0_hsteps_nogrp
                        let FindSt := Nat × Bool × BitVec 32
                        refine wp_join_state (ts := [i64, .bool, i32]) (α := FindSt)
                          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2, ()))
                          (Inv := fun st m_f =>
                            let t' := st.1; let err' := st.2.1; let lit' := st.2.2
                            m_f = m1 ∧ if err' then t' ≤ t
                            else t' < t ∧ (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat ∧
                              lit'.toNat < 2 * s.core.cur_vars ∧
                              s_lp.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                              unres = (flIdxs s.core s_lp.core.mrk (t' + 1)).length ∧
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause (flLits s.core s_lp.core.mrk (t' + 1)))) ?_ ?_
                        · -- `G@9371` consumer: check `err'`, `lit' == -1`, `unres == 1`, resolve
                          -- `rsn`
                          intro Jfind ⟨t', err', lit'⟩ m_f ⟨hm_eq, hfind⟩
                          dsimp only at hfind
                          rw [Blocks.get_here]; dsimp only
                          c0_hsplit
                          · -- `err' = true` -> exit to `Jexit`
                            have he : err' = true := by assumption
                            rw [ite_eq_left he] at hfind
                            c0_hsteps
                            exact hJexit (unres, ucnt, done, t', unit, true, s_lp) m_f
                              ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok,
                                         (fun h => by cases h),
                                hm_eq ▸ hm1⟩
                          · have he_f : err' = false := by assumption
                            rw [ite_eq_right (he_f ▸ Bool.false_ne_true)] at hfind
                            obtain ⟨ht'_lt, htrl_t', hlit'_lt, hmrk_t'_0, hunres_t'_0, hact_t'_0⟩ :=
                              hfind
                            have hlit'_ne : lit' ≠ 0xFFFFFFFF#32 := fl_bv32_lit_neq_ff (by omega)
                            c0_hsplit
                            · c0_hsteps; exact absurd (by assumption) hlit'_ne
                            · -- `G@9432` join for `(ucnt', unit', brk_unused)` after `if (unres ==
                              -- 1)`
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64, i32, .bool])
                                (α := Nat × BitVec 32 × Bool × FullState)
                                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                                (Inv := fun st m2 =>
                                  let ucnt' := st.1; let unit' := st.2.1; let s1 := st.2.2.2
                                  st.2.2.1 = false ∧
                                  FailedStateOk c s s1 cut ∧
                                  s1.core.mrk = s_lp.core.mrk ∧
                                  s1.core.min_clr_len = s_lp.core.min_clr_len ∧
                                  s1.scratch.work_stk1 = s_lp.scratch.work_stk1 ∧
                                  ucnt' ≤ s.core.cur_vars ∧
                                  (∀ k < ucnt', (s1.core.tmp[k]?.getD 0#32).toNat <
                                    2 * s.core.cur_vars ∧
                                    (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                                  (FullMem c s1 ⋆ R) m2) ?_ ?_
                              · -- `G@9432` consumer: load `rsns[lit' >> 1]`, resolve!
                                intro Juc ⟨ucnt', unit', _brk', s1⟩ m2
                                  ⟨hbrk', hok1, hmrk1_eq, hmcl1_eq, hws1_eq, hucnt'_le, htmp_ok',
                                    hm2⟩
                                dsimp only
                                  at hbrk' hok1 hmrk1_eq hmcl1_eq hws1_eq hucnt'_le htmp_ok' hm2
                                rw [Blocks.get_here]; dsimp only
                                have hl1_cv := hok1.len.core_ok
                                have hcv_s1 : s1.core.cur_vars = s.core.cur_vars := by
                                  rw [hok1.core]
                                have hmrk_t' : s1.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                                  rw [hmrk1_eq]; exact hmrk_t'_0
                                have hmrk_t'_trl :
                                    s1.core.mrk[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠
                                      0#8 := by
                                  rw [htrl_t']; exact hmrk_t'
                                have hunres_t' :
                                    unres = (flIdxs s.core s1.core.mrk (t' + 1)).length := by
                                  rw [hmrk1_eq]; exact hunres_t'_0
                                have hact_t' : (cnfOfClauses F_cur).EntailsClause
                                    (cnfClause (flLits s.core s1.core.mrk (t' + 1))) := by
                                  rw [hmrk1_eq]; exact hact_t'_0
                                have hlv_rsn : ((lit' >>> 1#32).setWidth 64).toNat <
                                    s1.core.rsns.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hl1_cv.rsns_len]
                                  have := hok1.len.core_ok.cur_vars_le; omega
                                c0_hsplit
                                · -- `rsn == -1`: `err = true` -> exit to `Jexit`
                                  c0_hsteps
                                  exact hJexit (unres, ucnt', done, t', unit', true, s1) m2
                                    ⟨hok1, by dsimp only; omega, hucnt'_le, htmp_ok',
                                      (fun h => by cases h), hm2⟩
                                · -- `rsn ≠ -1`: prove `t' < cut` so `hw0.reason_inv_cut` applies!
                                  have hrsn_ne :
                                      s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 ≠
                                        0xFFFFFFFF#32 := by
                                    have hidx : lit'.toNat / 2 < s1.core.rsns.length := by
                                      rw [hl1_cv.rsns_len]; omega
                                    have heq : s1.core.rsns[lit'.toNat / 2]'hidx ≠
                                        0xFFFFFFFF#32 := by assumption
                                    have hlt_eq : s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                        s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                      rw [hok1.core]
                                    rw [← hlt_eq, List.getElem?_eq_getElem hidx, Option.getD_some]
                                    exact heq
                                  have hrsn_ne' :
                                      s.core.rsns[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD
                                        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                    rw [htrl_t']; exact hrsn_ne
                                  have ht'_cut : t' < cut := by
                                    obtain ⟨_, m_c, hm_cut, hm_eq⟩ :=
                                      fl_mb_get hok1.mb (Nat.div_lt_of_lt_mul hlit'_lt) hmrk_t'
                                    have htm : t' = m_c := hw0.trail_vars_nodup t' m_c (by omega)
                                      (Nat.lt_of_lt_of_le hm_cut hw0.cut_le)
                                      (by rw [htrl_t', hm_eq])
                                    omega
                                  have hri := hw0.reason_inv_cut t' ht'_cut hrsn_ne'
                                  rw [htrl_t'] at hri
                                  have hl_t'_lvl1 :
                                      (s.core.lvl[lit'.toNat / 2]?.getD 0#32).toNat = 1 :=
                                    (fl_mb_get hok1.mb (Nat.div_lt_of_lt_mul hlit'_lt) hmrk_t').1
                                  c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i64, .bool, .bool])
                                    (α := Nat × Bool × Bool × FullState)
                                    (proj := fun st =>
                                      (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                                    (Inv := fun st m3 =>
                                      let unres' := st.1; let done' := st.2.1; let err'' := st.2.2.1
                                      let s3 := st.2.2.2
                                      FailedStateOk c s s3 cut ∧
                                      s3.core.tmp = s1.core.tmp ∧
                                      (!err'' → !done' →
                                        unres' = (flIdxs s.core s3.core.mrk t').length + 1 ∧
                                        (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause (flLits s.core s3.core.mrk t'))) ∧
                                      (FullMem c s3 ⋆ R) m3) ?_ ?_
                                  · -- `G@9543` consumer: if `done' || err'' || unres' == 0` ->
                                    -- `Jexit`, else `ih_lp`!
                                    intro Jrsn ⟨unres', done', err'', s3⟩ m3
                                      ⟨hok3, htmp3, hrsn_ok, hm3⟩
                                    dsimp only at hok3 htmp3 hrsn_ok hm3
                                    rw [Blocks.get_here]; dsimp only
                                    c0_hsplit
                                    · have hd'_t : done' = true := by assumption
                                      c0_hsteps
                                      have htmp3' : ∀ k < ucnt',
                                          (s3.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                                          (cnfOfClauses F_cur).EntailsClause
                                            (cnfClause [(s3.core.tmp[k]?.getD 0#32).toNat]) := by
                                        intro k hk; rw [htmp3]; exact htmp_ok' k hk
                                      exact hJexit (unres', ucnt', done', t', unit', err'', s3) m3
                                        ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                          (fun _ hd => by dsimp only at hd; rw [hd'_t] at hd; cases
                                                         hd), hm3⟩
                                    · have hd'_f : done' = false := by assumption
                                      c0_hsplit
                                      · have he''_t : err'' = true := by assumption
                                        c0_hsteps
                                        have htmp3' : ∀ k < ucnt',
                                            (s3.core.tmp[k]?.getD 0#32).toNat <
                                              2 * s.core.cur_vars ∧
                                            (cnfOfClauses F_cur).EntailsClause
                                              (cnfClause [(s3.core.tmp[k]?.getD 0#32).toNat]) := by
                                          intro k hk; rw [htmp3]; exact htmp_ok' k hk
                                        exact hJexit (unres', ucnt', done', t', unit', err'', s3) m3
                                          ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                            (fun he => by dsimp only at he; rw [he''_t] at he; cases
                                                         he), hm3⟩
                                      · have he''_f : err'' = false := by assumption
                                        obtain ⟨hunres'_eq, hent3⟩ :=
                                          hrsn_ok (by simp [he''_f]) (by simp [hd'_f])
                                        have hunres'_bd : unres' ≤ s.core.cur_vars + 1 :=
                                          Nat.le_trans
                                            (by
                                              rw [hunres'_eq];
                                              exact Nat.succ_le_succ flIdxs_length_le)
                                            (by omega)
                                        c0_hsplit
                                        · have hz : (BitVec.ofNat 64 unres') = 0#64 := by assumption
                                          have h0 := congrArg BitVec.toNat hz
                                          rw [bv64_ofNat_toNat (by omega),
                                            show (0#64 : BitVec 64).toNat = 0 from rfl] at h0
                                          omega
                                        · c0_hsteps
                                          have hsub_bv : BitVec.ofNat 64 unres' - 1 =
                                              BitVec.ofNat 64 (unres' - 1) :=
                                            BitVec.eq_of_toNat_eq (by
                                              rw [show (1 : BitVec 64) = 1#64 from rfl,
                                                fl_bv64_sub1_toNat (by
                                                  rw [bv64_ofNat_toNat (by omega)]; omega),
                                                bv64_ofNat_toNat (by omega), bv64_ofNat_toNat
                                                  (by omega)])
                                          rw [hsub_bv]
                                          have htmp3' : ∀ k < ucnt',
                                              (s3.core.tmp[k]?.getD 0#32).toNat <
                                                2 * s.core.cur_vars ∧
                                              (cnfOfClauses F_cur).EntailsClause
                                                (cnfClause [(s3.core.tmp[k]?.getD
                                                  0#32).toNat]) := by
                                            intro k hk; rw [htmp3]; exact htmp_ok' k hk
                                          exact ih_lp (unres' - 1, ucnt', done', t', unit', err'',
                                            s3)
                                            m3 (by
                                              dsimp only; rw [hdone_f, herr_f, hd'_f, he''_f]; simp;
                                              omega)
                                            ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                                              fun _ _ => ⟨by dsimp only; omega, hent3⟩, hm3⟩
                                  · -- `G@9543` producer: binary vs large `rsn`
                                    intro Jrsn hJrsn
                                    have hunres_t'_s :
                                        unres = (flIdxs s.core s1.core.mrk t').length + 1 := by
                                      rw [flIdxs_succ_marked hmrk_t'_trl, List.length_append,
                                        List.length_singleton] at hunres_t'
                                      exact hunres_t'
                                    c0_hsplit
                                    · -- Binary reason (`(rsn &&& 0x80000000) ≠ 0`)
                                      have hlv_rsn_d : lit'.toNat / 2 < s1.core.rsns.length := by
                                        rw [hl1_cv.rsns_len]; omega
                                      have hbin :
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                          0x80000000#32) ≠ 0#32 := by
                                        have hne : (s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&&
                                            0x80000000#32) ≠ 0#32 := by assumption
                                        have heq_r :
                                            s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                            s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                          rw [hok1.core]
                                        rw [← heq_r, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                        exact hne
                                      rw [ite_eq_left hbin] at hri
                                      obtain ⟨hot_lt, hent_bin, m_ot, hm_ot_lt, hm_ot_eq,
                                        hm_ot_lv⟩ := hri
                                      have h_ot_norm : (s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&&
                                          0x7FFFFFFF#32).toNat =
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                            0x7FFFFFFF#32).toNat := by
                                        have heq_r :
                                            s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                            s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                          rw [hok1.core]
                                        rw [← heq_r, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                      let ot32 :=
                                        s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&& 0x7FFFFFFF#32
                                      have hot32_lt : ot32.toNat < 2 * s.core.cur_vars := by
                                        dsimp only [ot32]; rw [h_ot_norm]; exact hot_lt
                                      c0_hsplit
                                      · c0_hsteps
                                        exact hJexit (unres, ucnt', true, t', unit', _brk', s1) m2
                                          ⟨hok1, by dsimp only; omega, hucnt'_le, htmp_ok',
                                            (fun _ hd => by simp at hd), hm2⟩
                                      · have hov_lt : ot32.toNat / 2 < s.core.cur_vars :=
                                          Nat.div_lt_of_lt_mul hot32_lt
                                        have hov_lvl_lt : ot32.toNat / 2 < s1.core.lvl.length := by
                                          rw [hl1_cv.lvl_len]
                                          have := hok1.len.core_ok.cur_vars_le; omega
                                        have hov_mrk_lt : ot32.toNat / 2 < s1.core.mrk.length := by
                                          rw [hl1_cv.mrk_len]
                                          have := hok1.len.core_ok.cur_vars_le; omega
                                        c0_hsplit
                                        · exfalso
                                          have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                                          have hge : s.core.cur_vars % 2 ^ 64 ≤ ot32.toNat / 2 := by
                                            dsimp only [ot32]
                                            simpa only [show (2147483647 : BitVec 32) =
                                              0x7FFFFFFF#32 from rfl] using (by assumption : _)
                                          rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                        · c0_hsteps_nogrp
                                          refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                            (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                            (Inv := fun st m3 =>
                                              FailedStateOk c s st.2 cut ∧
                                              st.2.core.tmp = s1.core.tmp ∧
                                              st.1 = (flIdxs s.core st.2.core.mrk t').length + 1 ∧
                                              (∀ l ∈ flLits s.core s1.core.mrk t',
                                                l ∈ flLits s.core st.2.core.mrk t') ∧
                                              ((cnfOfClauses F_cur).EntailsClause
                                                  (cnfClause [ot32.toNat ^^^ 1]) ∨
                                                ot32.toNat ∈ flLits s.core st.2.core.mrk t') ∧
                                              (FullMem c st.2 ⋆ R) m3) ?_ ?_
                                          · intro Jbin ⟨unres_b, s_b⟩ m3
                                              ⟨hok_b, htmp_b, hunres_b, hpres_b, hot_in, hm3⟩
                                            dsimp only at hok_b htmp_b hunres_b hpres_b hot_in hm3
                                            rw [Blocks.get_here]; dsimp only
                                            have hent_b : (cnfOfClauses F_cur).EntailsClause
                                                (cnfClause (flLits s.core s_b.core.mrk t')) := by
                                              refine fl_resolve_step hmrk_t'_trl hact_t' hpres_b
                                                (by simpa [h_ot_norm, ot32, htrl_t'] using hent_bin)
                                                fun q hq => ?_
                                              simp only [List.mem_cons, List.not_mem_nil, or_false]
                                                at hq
                                              rcases hq with rfl | rfl
                                              · exact Or.inl htrl_t'.symm
                                              · exact Or.inr (by
                                                  have hot_in' :
                                                      (cnfOfClauses F_cur).EntailsClause
                                                        (cnfClause [ot32.toNat ^^^ 1]) ∨
                                                      ot32.toNat ∈ flLits s.core s_b.core.mrk t' :=
                                                        hot_in
                                                  simpa only [ot32, BitVec.toNat_and,
                                                    show (0x7FFFFFFF#32 : BitVec 32).toNat =
                                                      2147483647 from rfl,
                                                    h_ot_norm] using hot_in')
                                            c0_hsteps
                                            exact hJrsn (unres_b, done, _brk', s_b) m3
                                              ⟨hok_b, htmp_b, fun _ _ => ⟨hunres_b, hent_b⟩, hm3⟩
                                          · intro Jbin hJbin
                                            have hot_eq_norm : ot32.toNat =
                                                (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                                  0x7FFFFFFF#32).toNat := h_ot_norm
                                            have hcv1_eq : s1.core.cur_vars = s.core.cur_vars := by
                                              rw [hok1.core]
                                            c0_hsplit
                                            · c0_hsplit
                                              · have hmrk0_ov :
                                                    s1.core.mrk[ot32.toNat / 2]?.getD 0#8 =
                                                    0#8 :=
                                                  fl_mark_zero_eq hok1 hov_lt
                                                    (by dsimp only [ot32]; assumption)
                                                have hlvl_pos : 0 <
                                                    (s.core.lvl[ot32.toNat / 2]?.getD
                                                      0#32).toNat := by
                                                  have hpos : (0#32).toNat <
                                                      (s1.core.lvl[ot32.toNat /
                                                        2]'hov_lvl_lt).toNat := by
                                                    dsimp only [ot32]; assumption
                                                  have heql :
                                                      s1.core.lvl[ot32.toNat / 2]?.getD 0#32 =
                                                      s.core.lvl[ot32.toNat / 2]?.getD 0#32 := by
                                                    rw [hok1.core]
                                                  rw [← heql, List.getElem?_eq_getElem hov_lvl_lt,
                                                    Option.getD_some]
                                                  exact hpos
                                                obtain ⟨hmcl_lt, hok2, hfl_len, hfl_pres, hot_in⟩ :=
                                                  fl_mark_lit_push hw0 hcl1 hok1
                                                    (by omega) hot32_lt hmrk0_ov
                                                    hlvl_pos
                                                    ⟨m_ot, hm_ot_lt, by rw [hm_ot_eq, hot_eq_norm]⟩
                                                    ⟨m_ot, by omega, by rw [hm_ot_eq, hot_eq_norm]⟩
                                                let ov := ot32.toNat / 2
                                                let ov32 := BitVec.ofNat 32 ov
                                                let s2 : FullState :=
                                                  { core :=
                                                      { s1.core with
                                                        mrk := s1.core.mrk.set ov 1#8,
                                                        min_clr_len := s1.core.min_clr_len + 1 }
                                                    scratch :=
                                                      { s1.scratch with
                                                        work_stk1 :=
                                                          s1.scratch.work_stk1.set
                                                            s1.core.min_clr_len ov32 } }
                                                have hunres1_bv : BitVec.ofNat 64 unres + 1 =
                                                    BitVec.ofNat 64 (unres + 1) :=
                                                  BitVec.eq_of_toNat_eq (by
                                                    rw [show (1 : BitVec 64) = 1#64 from rfl,
                                                      fl_bv64_add1_toNat
                                                        (by
                                                          rw [bv64_ofNat_toNat (by omega)]; omega),
                                                      bv64_ofNat_toNat (by omega),
                                                      bv64_ofNat_toNat (by omega)])
                                                have hmcl1_bv :
                                                    (BitVec.ofNat 64 s1.core.min_clr_len +
                                                      1).toNat =
                                                    s1.core.min_clr_len + 1 := by
                                                  have := hok1.cov.1
                                                  rw [show (1 : BitVec 64) = 1#64 from rfl,
                                                    fl_bv64_add1_toNat
                                                      (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                                    bv64_ofNat_toNat (by omega)]
                                                c0_hsplit
                                                have hmcl_ws :
                                                    (BitVec.ofNat 64 s1.core.min_clr_len).toNat <
                                                    s1.scratch.work_stk1.length := by
                                                  have := hok1.cov.1
                                                  rw [bv64_ofNat_toNat (by omega),
                                                    hok1.len.scratch_ok.work_stk1_len]; omega
                                                have hov32_eq : ov32 = ot32 >>> 1 :=
                                                  BitVec.eq_of_toNat_eq (by
                                                    rw [bv32_ofNat_toNat (by omega), bv32_lshr_1])
                                                c0_hsteps
                                                have hm2' : (FullMem c s2 ⋆ R) m := by
                                                  have := hok1.cov.1
                                                  simpa only [s2, ov, ov32, hov32_eq,
                                                    fl_bv32_setWidth64,
                                                    bv32_lshr_1, bv64_ofNat_toNat (by omega :
                                                      s1.core.min_clr_len < 2 ^ 64), hmcl1_bv,
                                                    show (2147483647 : BitVec 32) =
                                                      0x7FFFFFFF#32 from rfl,
                                                    show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                                rw [hunres1_bv]
                                                exact hJbin (unres + 1, s2) m
                                                  ⟨hok2, rfl, by
                                                    rw [hunres_t'_s]; dsimp only [s2, ov];
                                                    rw [hfl_len],
                                                   hfl_pres, hot_in, hm2'⟩
                                              · -- `mrk[ov] ≠ 0`
                                                have hmrk_nz :
                                                    s1.core.mrk[ot32.toNat / 2]?.getD 0#8 ≠ 0#8 :=
                                                  fl_mark_nz_eq hok1 hov_lt
                                                    (by dsimp only [ot32]; assumption)
                                                have hot_in := fl_mark_lit_skip hw0 hcl1 (by omega)
                                                  (fun _ => ⟨m_ot, by omega, by rw [hm_ot_eq,
                                                                               hot_eq_norm]⟩)
                                                  (fun _ => ⟨hmrk_nz, m_ot, hm_ot_lt, by
                                                    rw [hm_ot_eq, hot_eq_norm]⟩)
                                                c0_hsteps
                                                exact hJbin (unres, s1) m2
                                                  ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in,
                                                    hm2⟩
                                            · -- `lvl[ov] = 0`
                                              have hlvl0 :
                                                  (s.core.lvl[ot32.toNat / 2]?.getD 0#32).toNat =
                                                  0 := by
                                                have hno : ¬ (0#32).toNat <
                                                    (s1.core.lvl[ot32.toNat /
                                                      2]'hov_lvl_lt).toNat := by
                                                  dsimp only [ot32]; assumption
                                                have heql : s1.core.lvl[ot32.toNat / 2]?.getD 0#32 =
                                                    s.core.lvl[ot32.toNat / 2]?.getD 0#32 := by
                                                  rw [hok1.core]
                                                rw [← heql, List.getElem?_eq_getElem hov_lvl_lt,
                                                  Option.getD_some]
                                                have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
                                                omega
                                              have hot_in := fl_mark_lit_skip (s1 := s1) (t := t')
                                                (q := ot32.toNat) hw0 hcl1 (by omega)
                                                (fun _ => ⟨m_ot, by omega, by rw [hm_ot_eq,
                                                                             hot_eq_norm]⟩)
                                                (fun hp => by omega)
                                              c0_hsteps
                                              exact hJbin (unres, s1) m2
                                                ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in,
                                                  hm2⟩
                                    · -- Large reason (`(rsn &&& 0x80000000) == 0`)
                                      have hlv_rsn_d : lit'.toNat / 2 < s1.core.rsns.length := by
                                        rw [hl1_cv.rsns_len]; omega
                                      have hlg :
                                          (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                                          0x80000000#32) = 0#32 := by
                                        have heq0 : (s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d &&&
                                            0x80000000#32) = 0#32 := by
                                          simpa only [show (2147483648 : BitVec 32) =
                                            0x80000000#32 from rfl,
                                            show (0 : BitVec 32) = 0#32 from rfl] using
                                              (by assumption : _)
                                        have heq_r :
                                            s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                            s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                          rw [hok1.core]
                                        rw [← heq_r, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                        exact heq0
                                      rw [ite_eq_right (fun h => absurd hlg h)] at hri
                                      obtain ⟨href, hng, hall⟩ := hri
                                      have hwf := hw0.arena.refs_wf _ href
                                      let rsn32 := s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d
                                      have hrsn_eq : rsn32.toNat =
                                          (s.core.rsns[lit'.toNat / 2]?.getD
                                            0xFFFFFFFF#32).toNat := by
                                        have heq_r :
                                            s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                            s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                                          rw [hok1.core]
                                        dsimp [rsn32]
                                        rw [← heq_r, List.getElem?_eq_getElem hlv_rsn_d,
                                          Option.getD_some]
                                      have hal_eq : s1.core.arena_len = s.core.arena_len := by
                                        rw [hok1.core]
                                      have har_len : s1.core.arena.length = c.arena_cap :=
                                        hl1_cv.arena_len_arr
                                      have har_cap := c.harena; unfold dimacsBound at har_cap
                                      have hal_le := hl1_cv.arena_len_le
                                      have hrsn_add2_lt : (rsn32.setWidth 64 + 2#64).toNat <
                                          s1.core.arena.length := by
                                        rw [BitVec.toNat_add, fl_bv32_setWidth64,
                                          show (2#64 : BitVec 64).toNat = 2 from rfl,
                                          Nat.mod_eq_of_lt (by omega : rsn32.toNat + 2 < 2 ^ 64)]
                                        omega
                                      c0_hsplit
                                      · exfalso
                                        have hle3 : rsn32.toNat + 3 ≤ s.core.arena_len := by
                                          rw [hrsn_eq]; exact hwf.1
                                        have hal64 : s1.core.arena_len < 2 ^ 64 := by omega
                                        have hgt : s1.core.arena_len % 2 ^ 64 <
                                            (rsn32.toNat + 3) % 2 ^ 64 := by
                                          dsimp only [rsn32]; assumption
                                        rw [hal_eq, Nat.mod_eq_of_lt
                                          (by omega : s.core.arena_len < 2 ^ 64),
                                          Nat.mod_eq_of_lt
                                            (by omega : rsn32.toNat + 3 < 2 ^ 64)] at hgt
                                        omega
                                      · have hrsz_eq :
                                            (s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'
                                            hrsn_add2_lt).toNat =
                                            Full.fullArenaClauseSizeCore s.core rsn32.toNat := by
                                          rw [hrsn_eq]
                                          unfold Full.fullArenaClauseSizeCore
                                          have hidx : (s.core.rsns[lit'.toNat / 2]?.getD
                                              0xFFFFFFFF#32).toNat + 2 < s.core.arena.length := by
                                            rw [hcl.arena_len_arr, ← hrsn_eq]; omega
                                          have hget :
                                              (s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'
                                              hrsn_add2_lt) =
                                              s.core.arena[(s.core.rsns[lit'.toNat / 2]?.getD
                                                0xFFFFFFFF#32).toNat + 2]'hidx := by
                                            refine fl_getElem_congr_list (by rw [hok1.core]) ?_
                                            rw [BitVec.toNat_add, fl_bv32_setWidth64,
                                              show (2#64 : BitVec 64).toNat = 2 from rfl,
                                              Nat.mod_eq_of_lt
                                                (by omega : rsn32.toNat + 2 < 2 ^ 64),
                                              hrsn_eq]
                                          rw [hget, List.getElem?_eq_getElem hidx, Option.getD_some]
                                        let rsz := s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'
                                          hrsn_add2_lt
                                        c0_hsplit
                                        · exfalso
                                          have hlt3 : rsz.toNat < 3 := by
                                            dsimp only [rsz, rsn32]; assumption
                                          have hge3 : 3 ≤ rsz.toNat := by
                                            change 3 ≤ (s1.core.arena[
                                              (rsn32.setWidth 64 + 2#64).toNat]'hrsn_add2_lt).toNat
                                            rw [hrsz_eq, hrsn_eq]; exact hwf.2.1
                                          omega
                                        · c0_hsplit
                                          · exfalso
                                            have hle_a : rsn32.toNat + 3 + rsz.toNat ≤
                                                s.core.arena_len := by
                                              have : rsz.toNat =
                                                  Full.fullArenaClauseSizeCore s.core rsn32.toNat :=
                                                hrsz_eq
                                              rw [this, hrsn_eq]; have := hwf.2.2.1;
                                              have := hwf.2.2.2.1; omega
                                            have hgt : s1.core.arena_len % 2 ^ 64 <
                                                (rsn32.toNat + 3 + rsz.toNat) % 2 ^ 64 := by
                                              dsimp only [rsz, rsn32]; assumption
                                            rw [hal_eq, Nat.mod_eq_of_lt
                                              (by omega : s.core.arena_len < 2 ^ 64),
                                              Nat.mod_eq_of_lt
                                                (by
                                                  omega : rsn32.toNat + 3 + rsz.toNat < 2 ^ 64)]
                                                    at hgt
                                            omega
                                          · -- `G@10576` (`[i64, .bool, .bool, i32]`) & `G@10594`
                                            -- (`[i64, i32]`)
                                            have hrsz_bd : rsz.toNat < 2 ^ 32 := rsz.isLt
                                            have hrsn_bd : rsn32.toNat + 3 +
                                                Full.fullArenaClauseSizeCore s.core rsn32.toNat ≤
                                                  s.core.arena.length := by
                                              have hle_a : rsn32.toNat + 3 +
                                                  Full.fullArenaClauseSizeCore s.core rsn32.toNat ≤
                                                    s.core.arena_len := by
                                                rw [hrsn_eq];
                                                exact Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
                                              rw [hcl.arena_len_arr]
                                              exact Nat.le_trans hle_a hcl.arena_len_le
                                            have hlits_len :
                                                (Full.fullArenaClauseLitsCore s.core
                                                  rsn32.toNat).length =
                                                  rsz.toNat :=
                                              (fl_arenaClauseLitsCore_length hrsn_bd).trans
                                                hrsz_eq.symm
                                            let BrkJ := Nat × Bool × Bool × BitVec 32 × FullState
                                            let RsnLp := Nat × BitVec 32 × FullState
                                            c0_hsteps_nogrp
                                            refine wp_join_state (ts := [i64, .bool, .bool, i32])
                                              (α := BrkJ)
                                              (proj := fun st =>
                                                (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1,
                                                 st.2.2.2.1, ()))
                                              (Inv := fun st m3 =>
                                                let u' := st.1; let d' := st.2.1; let e' := st.2.2.1
                                                let s3 := st.2.2.2.2
                                                FailedStateOk c s s3 cut ∧ s3.core.tmp =
                                                  s1.core.tmp ∧
                                                (!e' → !d' →
                                                  u' = (flIdxs s.core s3.core.mrk t').length + 1 ∧
                                                  (cnfOfClauses F_cur).EntailsClause
                                                    (cnfClause (flLits s.core s3.core.mrk t'))) ∧
                                                (FullMem c s3 ⋆ R) m3) ?_ ?_
                                            · intro Jb ⟨u', d', e', _j, s3⟩ m3
                                                ⟨hok3, htmp3, hok_b, hm3⟩
                                              dsimp only at hok3 htmp3 hok_b hm3
                                              rw [Blocks.get_here]; dsimp only
                                              c0_hsteps
                                              exact hJrsn (u', d', e', s3) m3
                                                ⟨hok3, htmp3, hok_b, hm3⟩
                                            · intro Jb hJb
                                              refine wp_while_state (ts := [i64, i32]) (α := RsnLp)
                                                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1,
                                                  ()))
                                                (μ := fun st => rsz.toNat - st.2.1.toNat)
                                                (Inv := fun st m3 =>
                                                  let uj := st.1; let j := st.2.1; let sj := st.2.2
                                                  j.toNat ≤ rsz.toNat ∧ FailedStateOk c s sj cut ∧
                                                  sj.core.tmp = s1.core.tmp ∧
                                                  uj = (flIdxs s.core sj.core.mrk t').length + 1 ∧
                                                  (∀ l ∈ flLits s.core s1.core.mrk t',
                                                    l ∈ flLits s.core sj.core.mrk t') ∧
                                                  (∀ q ∈ (Full.fullArenaClauseLitsCore s.core
                                                    rsn32.toNat).take
                                                      j.toNat,
                                                    q = lit'.toNat ∨
                                                    (cnfOfClauses F_cur).EntailsClause (cnfClause [q
                                                      ^^^ 1]) ∨
                                                    q ∈ flLits s.core sj.core.mrk t') ∧
                                                  (FullMem c sj ⋆ R) m3) ?_ ?_
                                              · intro Jl hJl; c0_hsteps
                                                exact hJl (unres, 0#32, s1) m2
                                                  ⟨Nat.zero_le _, hok1, rfl, hunres_t'_s,
                                                    fun _ hl => hl,
                                                   fun _ hq => by simp at hq, hm2⟩
                                              · intro Jl ⟨uj, j, sj⟩ m3
                                                  ⟨hj_le, hokj, htmpj, huj_eq, hpresj, hcovj,
                                                    hm3⟩ ih_j
                                                dsimp only
                                                  at hj_le hokj htmpj huj_eq hpresj hcovj hm3 ih_j
                                                rw [Blocks.get_here]; dsimp only
                                                have hj_cv := hokj.len.core_ok
                                                have huj_bd : uj ≤ s.core.cur_vars + 1 :=
                                                  Nat.le_trans
                                                    (by
                                                      rw [huj_eq];
                                                      exact Nat.succ_le_succ flIdxs_length_le)
                                                    (by omega)
                                                c0_hsplit
                                                · -- `j < rsz`: load `ot = ar[rsn + 3 + j]`
                                                  have hj_lt : j.toNat < rsz.toNat := by
                                                    dsimp only [rsz, rsn32]; assumption
                                                  have hot_ar_lt :
                                                      (rsn32.setWidth 64 + 3#64 +
                                                        j.setWidth 64).toNat <
                                                        sj.core.arena.length := by
                                                    rw [hokj.len.core_ok.arena_len_arr]
                                                    rw [BitVec.toNat_add, BitVec.toNat_add,
                                                      fl_bv32_setWidth64, fl_bv32_setWidth64,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 3 < 2 ^ 64),
                                                      Nat.mod_eq_of_lt
                                                        (by
                                                          omega : rsn32.toNat + 3 + j.toNat <
                                                            2 ^ 64)]
                                                    have : rsz.toNat =
                                                        Full.fullArenaClauseSizeCore s.core
                                                          rsn32.toNat :=
                                                      hrsz_eq
                                                    rw [hrsn_eq] at this ⊢; omega
                                                  let ot32 := sj.core.arena[
                                                    (rsn32.setWidth 64 + 3#64 +
                                                      j.setWidth 64).toNat]'
                                                    hot_ar_lt
                                                  have hot_ar_lt_c :
                                                      (s1.core.rsns[lit'.toNat / 2].toNat + 3 +
                                                        j.toNat) % 2 ^ 64 <
                                                        sj.core.arena.length := by
                                                    change (rsn32.toNat + 3 + j.toNat) % 2 ^ 64 <
                                                      sj.core.arena.length
                                                    simpa only [BitVec.toNat_add,
                                                      fl_bv32_setWidth64,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by
                                                          omega : rsn32.toNat + 3 < 2 ^ 64)] using
                                                            hot_ar_lt
                                                  have hot_hc :
                                                      sj.core.arena[(s1.core.rsns[lit'.toNat /
                                                        2].toNat + 3 +
                                                        j.toNat) % 2 ^ 64]'hot_ar_lt_c = ot32 := by
                                                    dsimp only [ot32, rsn32]; congr 1
                                                    rw [BitVec.toNat_add, BitVec.toNat_add,
                                                      fl_bv32_setWidth64, fl_bv32_setWidth64,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 3 < 2 ^ 64)]
                                                  have hot_mem : ot32.toNat ∈
                                                      Full.fullArenaClauseLitsCore s.core
                                                        rsn32.toNat := by
                                                    dsimp [ot32]
                                                    rw [Full.mem_fullArenaClauseLitsCore_iff
                                                      hrsn_bd]
                                                    refine ⟨j.toNat, by rw [← hrsz_eq]; exact hj_lt,
                                                                       ?_⟩
                                                    have hidx : rsn32.toNat + 3 + j.toNat <
                                                          s.core.arena.length := by
                                                      rw [hcl.arena_len_arr,
                                                        ← hokj.len.core_ok.arena_len_arr]
                                                      simpa [BitVec.toNat_add, fl_bv32_setWidth64,
                                                        Nat.mod_eq_of_lt
                                                          (by omega : rsn32.toNat + 3 < 2 ^ 64),
                                                        Nat.mod_eq_of_lt
                                                          (by
                                                            omega : rsn32.toNat + 3 + j.toNat <
                                                              2 ^ 64)]
                                                        using hot_ar_lt
                                                    have heq :
                                                        sj.core.arena[(rsn32.setWidth 64 + 3#64 +
                                                        j.setWidth 64).toNat]'hot_ar_lt =
                                                        s.core.arena[rsn32.toNat + 3 +
                                                          j.toNat]'hidx := by
                                                      refine fl_getElem_congr_list
                                                        (by rw [hokj.core]) ?_
                                                      rw [BitVec.toNat_add, BitVec.toNat_add,
                                                        fl_bv32_setWidth64, fl_bv32_setWidth64,
                                                        show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                        Nat.mod_eq_of_lt
                                                          (by omega : rsn32.toNat + 3 < 2 ^ 64),
                                                        Nat.mod_eq_of_lt
                                                          (by
                                                            omega : rsn32.toNat + 3 + j.toNat <
                                                              2 ^ 64)]
                                                    exact congrArg BitVec.toNat heq.symm
                                                  have hot_lt :
                                                      ot32.toNat < 2 * s.core.cur_vars := by
                                                    rw [hrsn_eq] at hot_mem
                                                    exact hw0.arena.lits_lt _ href hng _ hot_mem
                                                  have hj1_bv : (j + 1#32).toNat = j.toNat + 1 :=
                                                    fl_bv32_add1_toNat (by omega)
                                                  c0_hsteps_nogrp
                                                  refine wp_join_state (ts := [i64, .bool, .bool])
                                                    (α := Nat × FullState)
                                                    (proj := fun st =>
                                                      (BitVec.ofNat 64 st.1, done, _brk', ()))
                                                    (Inv := fun st m4 =>
                                                      let uj' := st.1; let sj' := st.2
                                                      FailedStateOk c s sj' cut ∧ sj'.core.tmp =
                                                        s1.core.tmp ∧
                                                      (∀ l ∈ flLits s.core s1.core.mrk t',
                                                        l ∈ flLits s.core sj'.core.mrk t') ∧
                                                      uj' = (flIdxs s.core sj'.core.mrk t').length +
                                                        1 ∧
                                                      (∀ q ∈ (Full.fullArenaClauseLitsCore s.core
                                                        rsn32.toNat).take
                                                          (j.toNat + 1),
                                                        q = lit'.toNat ∨
                                                        (cnfOfClauses F_cur).EntailsClause
                                                          (cnfClause [q ^^^ 1]) ∨
                                                        q ∈ flLits s.core sj'.core.mrk t') ∧
                                                      (FullMem c sj' ⋆ R) m4) ?_ ?_
                                                  · intro Jc ⟨uj', sj'⟩ m4
                                                      ⟨hokj', htmpj', hpresj', huj'_eq, hcov_j1,
                                                        hm4⟩
                                                    dsimp only
                                                      at hokj' htmpj' hpresj' huj'_eq hcov_j1 hm4
                                                    rw [Blocks.get_here]; dsimp only
                                                    c0_hsteps
                                                    exact ih_j (uj', j + 1#32, sj') m4
                                                      (by dsimp only; omega)
                                                      ⟨by
                                                        dsimp only;
                                                        omega, hokj', htmpj', huj'_eq, hpresj',
                                                       by
                                                         dsimp only;
                                                         simpa only [hj1_bv] using hcov_j1, hm4⟩
                                                  · intro Jc hJc
                                                    have hot_lits_len :
                                                        j.toNat <
                                                          (Full.fullArenaClauseLitsCore s.core
                                                            rsn32.toNat).length := by
                                                      rw [hlits_len]; exact hj_lt
                                                    have hot_ar_j :
                                                        rsn32.toNat + 3 + j.toNat <
                                                          s.core.arena.length := by
                                                      rw [hcl.arena_len_arr,
                                                        ← hokj.len.core_ok.arena_len_arr]
                                                      simpa [BitVec.toNat_add, fl_bv32_setWidth64,
                                                        Nat.mod_eq_of_lt
                                                          (by omega : rsn32.toNat + 3 < 2 ^ 64),
                                                        Nat.mod_eq_of_lt (by omega :
                                                          rsn32.toNat + 3 + j.toNat < 2 ^ 64)] using
                                                            hot_ar_lt
                                                    have hot_get :
                                                        (Full.fullArenaClauseLitsCore s.core
                                                          rsn32.toNat)[
                                                          j.toNat]'hot_lits_len = ot32.toNat := by
                                                      rw [fl_arenaClauseLitsCore_getElem hrsn_bd
                                                        (by
                                                          rw [← hrsz_eq];
                                                          exact hj_lt) hot_lits_len hot_ar_j]
                                                      dsimp [ot32]
                                                      congr 1
                                                      have heq :
                                                          sj.core.arena[(rsn32.setWidth 64 + 3#64 +
                                                          j.setWidth 64).toNat]'hot_ar_lt =
                                                          s.core.arena[rsn32.toNat + 3 +
                                                            j.toNat]'hot_ar_j := by
                                                        refine fl_getElem_congr_list
                                                          (by rw [hokj.core]) ?_
                                                        rw [BitVec.toNat_add, BitVec.toNat_add,
                                                          fl_bv32_setWidth64, fl_bv32_setWidth64,
                                                          show (3#64 : BitVec 64).toNat = 3 from
                                                            rfl,
                                                          Nat.mod_eq_of_lt
                                                            (by omega : rsn32.toNat + 3 < 2 ^ 64),
                                                          Nat.mod_eq_of_lt
                                                            (by
                                                              omega : rsn32.toNat + 3 + j.toNat <
                                                                2 ^ 64)]
                                                      exact heq.symm
                                                    c0_hsplit
                                                    · -- `ot ≠ lit`
                                                      c0_hsplit
                                                      · -- `ot == not_failed` -> break via `Jb`
                                                        -- (`done = true`)!
                                                        c0_hsteps
                                                        exact hJb (uj, true, _brk', j, sj) m3
                                                          ⟨hokj, htmpj, fun _ hd => by simp at hd,
                                                                                      hm3⟩
                                                      · have hot_rsn := hall ot32.toNat (by
                                                          rw [hrsn_eq] at hot_mem; exact hot_mem)
                                                        have hot_ne : ot32.toNat ≠ lit'.toNat := by
                                                          intro he
                                                          have he32 : ot32 = lit' :=
                                                            BitVec.eq_of_toNat_eq he
                                                          exact
                                                            (by
                                                              rw [← hot_hc];
                                                              assumption : ot32 ≠ lit') he32
                                                        obtain ⟨m_ot, hm_ot_lt, hm_ot_eq, _⟩ :=
                                                          hot_rsn.resolve_left hot_ne
                                                        have hov_lt :
                                                            ot32.toNat / 2 < s.core.cur_vars :=
                                                          Nat.div_lt_of_lt_mul hot_lt
                                                        have hov_lvl_lt :
                                                            ot32.toNat / 2 <
                                                              sj.core.lvl.length := by
                                                          rw [hj_cv.lvl_len]
                                                          have := hokj.len.core_ok.cur_vars_le
                                                          have hcvj :
                                                              sj.core.cur_vars =
                                                                s.core.cur_vars := by
                                                            rw [hokj.core]
                                                          rw [hcvj] at this; omega
                                                        have hov_mrk_lt :
                                                            ot32.toNat / 2 <
                                                              sj.core.mrk.length := by
                                                          rw [hj_cv.mrk_len]
                                                          have := hokj.len.core_ok.cur_vars_le
                                                          have hcvj :
                                                              sj.core.cur_vars =
                                                                s.core.cur_vars := by
                                                            rw [hokj.core]
                                                          rw [hcvj] at this; omega
                                                        c0_hsplit
                                                        · exfalso
                                                          have hcv64 : s.core.cur_vars < 2 ^ 64 :=
                                                            by omega
                                                          have hcvj_eq :
                                                              sj.core.cur_vars =
                                                                s.core.cur_vars := by
                                                            rw [hokj.core]
                                                          first
                                                          | (have hge : s.core.cur_vars % 2 ^ 64 ≤
                                                              ot32.toNat / 2 := by
                                                               rw [← hot_hc]; assumption
                                                             rw [Nat.mod_eq_of_lt hcv64] at hge;
                                                             omega)
                                                          | (have hge : sj.core.cur_vars % 2 ^ 64 ≤
                                                              ot32.toNat / 2 := by
                                                               rw [← hot_hc]; assumption
                                                             rw [hcvj_eq, Nat.mod_eq_of_lt hcv64]
                                                               at hge; omega)
                                                        · refine wp_join_state (ts := [i64]) (α :=
                                                            Nat × FullState)
                                                            (proj := fun st => (BitVec.ofNat 64
                                                              st.1, ()))
                                                            (Inv := fun st m4 =>
                                                              let uj' := st.1; let sj' := st.2
                                                              FailedStateOk c s sj' cut ∧
                                                              sj'.core.tmp = s1.core.tmp ∧
                                                              (∀ l ∈ flLits s.core s1.core.mrk t',
                                                                l ∈ flLits s.core sj'.core.mrk t') ∧
                                                              uj' =
                                                                (flIdxs s.core sj'.core.mrk
                                                                  t').length + 1 ∧
                                                              (∀ q ∈ (Full.fullArenaClauseLitsCore
                                                                s.core
                                                                  rsn32.toNat).take (j.toNat + 1),
                                                                q = lit'.toNat ∨
                                                                (cnfOfClauses F_cur).EntailsClause
                                                                  (cnfClause [q ^^^ 1]) ∨
                                                                q ∈ flLits s.core sj'.core.mrk t') ∧
                                                              (FullMem c sj' ⋆ R) m4) ?_ ?_
                                                          · intro Jo ⟨uj', sj'⟩ m4
                                                              ⟨hokj', htmpj', hpresj', huj', hcovj1,
                                                                hm4⟩
                                                            dsimp only
                                                              at hokj' htmpj' hpresj' huj' hcovj1
                                                                 hm4
                                                            rw [Blocks.get_here]; dsimp only
                                                            c0_hsteps
                                                            exact hJc (uj', sj') m4
                                                              ⟨hokj', htmpj', hpresj', huj', hcovj1,
                                                                hm4⟩
                                                          · intro Jo hJo
                                                            have hcvj_eq :
                                                                sj.core.cur_vars =
                                                                  s.core.cur_vars := by
                                                              rw [hokj.core]
                                                            c0_hsplit
                                                            · c0_hsplit
                                                              · have hmrk0_ov :
                                                                    sj.core.mrk[ot32.toNat /
                                                                      2]?.getD 0#8 =
                                                                    0#8 := by
                                                                  refine fl_mark_zero_eq hokj
                                                                    hov_lt ?_
                                                                  simp only [← hot_hc]; assumption
                                                                have hlvl_pos : 0 <
                                                                    (s.core.lvl[ot32.toNat /
                                                                      2]?.getD 0#32).toNat := by
                                                                  have hpos : (0#32).toNat <
                                                                      (sj.core.lvl[ot32.toNat /
                                                                        2]'hov_lvl_lt).toNat := by
                                                                    simp only [← hot_hc,
                                                                      show (0#32 : BitVec 32).toNat
                                                                        =
                                                                        BitVec.toNat 0 from rfl]
                                                                    assumption
                                                                  have heql :
                                                                      sj.core.lvl[ot32.toNat /
                                                                        2]?.getD 0#32 =
                                                                      s.core.lvl[ot32.toNat /
                                                                        2]?.getD 0#32 := by
                                                                    rw [hokj.core]
                                                                  rw [← heql,
                                                                    List.getElem?_eq_getElem
                                                                      hov_lvl_lt,
                                                                    Option.getD_some]
                                                                  exact hpos
                                                                obtain ⟨hmcl_lt, hok2, hfl_len,
                                                                  hfl_pres, hot_in⟩ :=
                                                                  fl_mark_lit_push hw0 hcl1 hokj
                                                                    (by omega) hot_lt
                                                                    hmrk0_ov hlvl_pos
                                                                    ⟨m_ot, hm_ot_lt, hm_ot_eq⟩
                                                                    ⟨m_ot, by omega, hm_ot_eq⟩
                                                                let ov := ot32.toNat / 2
                                                                let ov32 := BitVec.ofNat 32 ov
                                                                let s2 : FullState :=
                                                                  { core :=
                                                                      { sj.core with
                                                                        mrk := sj.core.mrk.set ov
                                                                          1#8,
                                                                        min_clr_len :=
                                                                          sj.core.min_clr_len + 1 }
                                                                    scratch :=
                                                                      { sj.scratch with
                                                                        work_stk1 :=
                                                                          sj.scratch.work_stk1.set
                                                                            sj.core.min_clr_len
                                                                            ov32 } }
                                                                have hpres2 :
                                                                    ∀ l ∈ flLits s.core s1.core.mrk
                                                                      t',
                                                                    l ∈ flLits s.core s2.core.mrk
                                                                      t' :=
                                                                  fun l hl => hfl_pres l (hpresj l
                                                                    hl)
                                                                have hcov2 :
                                                                    ∀ q ∈
                                                                      (Full.fullArenaClauseLitsCore
                                                                    s.core rsn32.toNat).take
                                                                      (j.toNat + 1),
                                                                    q = lit'.toNat ∨
                                                                    (cnfOfClauses
                                                                      F_cur).EntailsClause
                                                                      (cnfClause [q ^^^ 1]) ∨
                                                                    q ∈ flLits s.core s2.core.mrk
                                                                      t' := by
                                                                  refine fl_take_succ_forall _
                                                                    hot_lits_len _
                                                                    (fun q hq => ?_) ?_
                                                                  · rcases hcovj q hq with rfl | h0
                                                                      | hm
                                                                    · exact Or.inl rfl
                                                                    · exact Or.inr (Or.inl h0)
                                                                    · exact Or.inr (Or.inr (hfl_pres
                                                                        q hm))
                                                                  · rw [hot_get]
                                                                    rcases hot_in with h0 | hm
                                                                    · exact Or.inr (Or.inl h0)
                                                                    · exact Or.inr (Or.inr hm)
                                                                have huj1_bv :
                                                                    BitVec.ofNat 64 uj + 1 =
                                                                    BitVec.ofNat 64 (uj + 1) :=
                                                                  BitVec.eq_of_toNat_eq (by
                                                                    rw [show (1 : BitVec 64) =
                                                                      1#64 from rfl,
                                                                      fl_bv64_add1_toNat
                                                                        (by
                                                                          rw [bv64_ofNat_toNat
                                                                            (by omega)]; omega),
                                                                      bv64_ofNat_toNat (by omega),
                                                                      bv64_ofNat_toNat (by omega)])
                                                                have hmcl1_bv :
                                                                    (BitVec.ofNat 64
                                                                      sj.core.min_clr_len +
                                                                        1).toNat =
                                                                      sj.core.min_clr_len + 1 := by
                                                                  have := hokj.cov.1
                                                                  rw [show (1 : BitVec 64) =
                                                                    1#64 from rfl,
                                                                    fl_bv64_add1_toNat
                                                                      (by
                                                                        rw [bv64_ofNat_toNat
                                                                          (by omega)]; omega),
                                                                    bv64_ofNat_toNat (by omega)]
                                                                c0_hsplit
                                                                have hmcl_ws : (BitVec.ofNat 64
                                                                      sj.core.min_clr_len).toNat <
                                                                  sj.scratch.work_stk1.length := by
                                                                  have := hokj.cov.1
                                                                  have hws := hokj.len.scratch_ok
                                                                  rw [bv64_ofNat_toNat (by omega),
                                                                    hws.work_stk1_len]
                                                                  omega
                                                                have hov32_eq : ov32 = ot32 >>> 1 :=
                                                                  BitVec.eq_of_toNat_eq (by
                                                                    rw [bv32_ofNat_toNat (by omega),
                                                                      bv32_lshr_1])
                                                                c0_hsteps
                                                                have hm2' :
                                                                    (FullMem c s2 ⋆ R) m := by
                                                                  have := hokj.cov.1
                                                                  simpa only [s2, ov, ov32,
                                                                    hov32_eq, ot32, rsn32,
                                                                    show (3 : BitVec 64) = 3#64 from
                                                                      rfl,
                                                                    show BitVec.ofNat 8 1 = 1#8 from
                                                                      rfl,
                                                                    fl_bv32_setWidth64, bv32_lshr_1,
                                                                    bv64_ofNat_toNat (by omega :
                                                                      sj.core.min_clr_len < 2 ^ 64),
                                                                    hmcl1_bv] using hm
                                                                rw [huj1_bv]
                                                                exact hJo (uj + 1, s2) m
                                                                  ⟨hok2, htmpj, hpres2, by
                                                                    rw [huj_eq];
                                                                    dsimp only [s2, ov];
                                                                    rw [hfl_len],
                                                                   hcov2, hm2'⟩
                                                              · -- `mrk[ov] ≠ 0`
                                                                have hmrk_nz :
                                                                    sj.core.mrk[ot32.toNat /
                                                                      2]?.getD 0#8 ≠
                                                                    0#8 := by
                                                                  refine fl_mark_nz_eq hokj
                                                                    hov_lt ?_
                                                                  simp only [← hot_hc]; assumption
                                                                have hot_in :=
                                                                  fl_mark_lit_skip hw0 hcl1
                                                                    (by omega)
                                                                  (fun _ => ⟨m_ot, by omega,
                                                                                     hm_ot_eq⟩)
                                                                  (fun _ => ⟨hmrk_nz, m_ot,
                                                                    hm_ot_lt, hm_ot_eq⟩)
                                                                have hcov2 :
                                                                    ∀ q ∈
                                                                      (Full.fullArenaClauseLitsCore
                                                                    s.core rsn32.toNat).take
                                                                      (j.toNat + 1),
                                                                    q = lit'.toNat ∨
                                                                    (cnfOfClauses
                                                                      F_cur).EntailsClause
                                                                      (cnfClause [q ^^^ 1]) ∨
                                                                    q ∈ flLits s.core sj.core.mrk
                                                                      t' :=
                                                                  fl_take_succ_forall _ hot_lits_len
                                                                    _ hcovj
                                                                    (hot_get ▸ hot_in.elim (fun h =>
                                                                      Or.inr (Or.inl h))
                                                                      (fun h => Or.inr (Or.inr h)))
                                                                c0_hsteps
                                                                exact hJo (uj, sj) m3
                                                                  ⟨hokj, htmpj, hpresj, huj_eq,
                                                                    hcov2, hm3⟩
                                                            · -- `lvl[ov] = 0`
                                                              have hlvl0 :
                                                                  (s.core.lvl[ot32.toNat / 2]?.getD
                                                                    0#32).toNat =
                                                                  0 := by
                                                                have hno : ¬ (0#32).toNat <
                                                                    (sj.core.lvl[ot32.toNat /
                                                                      2]'hov_lvl_lt).toNat := by
                                                                  simp only [← hot_hc,
                                                                    show (0#32 : BitVec 32).toNat =
                                                                      BitVec.toNat 0 from rfl]
                                                                  assumption
                                                                have heql :
                                                                    sj.core.lvl[ot32.toNat /
                                                                      2]?.getD 0#32 =
                                                                    s.core.lvl[ot32.toNat / 2]?.getD
                                                                      0#32 := by
                                                                  rw [hokj.core]
                                                                rw [← heql,
                                                                  List.getElem?_eq_getElem
                                                                    hov_lvl_lt,
                                                                  Option.getD_some]
                                                                have h0 :
                                                                    (0#32 : BitVec 32).toNat = 0 :=
                                                                      rfl
                                                                omega
                                                              have hot_in :=
                                                                fl_mark_lit_skip (s1 := sj)
                                                                (t := t') (q := ot32.toNat)
                                                                hw0 hcl1 (by omega)
                                                                (fun _ => ⟨m_ot, by omega,
                                                                                   hm_ot_eq⟩)
                                                                (fun hp => by omega)
                                                              have hcov2 :
                                                                  ∀ q ∈
                                                                    (Full.fullArenaClauseLitsCore
                                                                  s.core rsn32.toNat).take (j.toNat
                                                                    + 1),
                                                                  q = lit'.toNat ∨
                                                                  (cnfOfClauses F_cur).EntailsClause
                                                                    (cnfClause [q ^^^ 1]) ∨
                                                                  q ∈ flLits s.core sj.core.mrk
                                                                    t' :=
                                                                fl_take_succ_forall _ hot_lits_len _
                                                                  hcovj
                                                                  (hot_get ▸ hot_in.elim (fun h =>
                                                                    Or.inr (Or.inl h))
                                                                    (fun h => Or.inr (Or.inr h)))
                                                              c0_hsteps
                                                              exact hJo (uj, sj) m3
                                                                ⟨hokj, htmpj, hpresj, huj_eq, hcov2,
                                                                  hm3⟩
                                                    · -- `ot == lit`
                                                      have hot_eq : ot32.toNat = lit'.toNat := by
                                                        have hot32_eq : ot32 = lit' := by
                                                          simp only [← hot_hc]; assumption
                                                        exact congrArg BitVec.toNat hot32_eq
                                                      have hcov2 :
                                                          ∀ q ∈ (Full.fullArenaClauseLitsCore
                                                          s.core rsn32.toNat).take (j.toNat + 1),
                                                          q = lit'.toNat ∨
                                                          (cnfOfClauses F_cur).EntailsClause
                                                            (cnfClause [q ^^^ 1]) ∨
                                                          q ∈ flLits s.core sj.core.mrk t' :=
                                                        fl_take_succ_forall _ hot_lits_len _ hcovj
                                                          (hot_get ▸ Or.inl hot_eq)
                                                      c0_hsteps
                                                      exact hJc (uj, sj) m3
                                                        ⟨hokj, htmpj, hpresj, huj_eq, hcov2, hm3⟩
                                                · -- Loop `j = rsz` finished: resolve via
                                                  -- `fl_resolve_step`!
                                                  have hrsz_lt_c :
                                                      (s1.core.rsns[lit'.toNat / 2].toNat +
                                                        2) % 2 ^ 64 <
                                                        s1.core.arena.length := by
                                                    change (rsn32.toNat + 2) % 2 ^ 64 <
                                                      s1.core.arena.length
                                                    simpa only [BitVec.toNat_add,
                                                      fl_bv32_setWidth64,
                                                      show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by
                                                          omega : rsn32.toNat + 2 < 2 ^ 64)] using
                                                            hrsn_add2_lt
                                                  have hrsz_hc :
                                                      s1.core.arena[(s1.core.rsns[lit'.toNat /
                                                        2].toNat + 2) % 2 ^ 64]'
                                                        hrsz_lt_c = rsz := by
                                                    dsimp only [rsz, rsn32]; congr 1
                                                    try rw [BitVec.toNat_add, fl_bv32_setWidth64,
                                                      show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                      Nat.mod_eq_of_lt
                                                        (by omega : rsn32.toNat + 2 < 2 ^ 64)]
                                                  have hj_nge : ¬ j.toNat < rsz.toNat := by
                                                    rw [← hrsz_hc]; assumption
                                                  have hj_eq : j.toNat = rsz.toNat := by omega
                                                  have htake_all :
                                                      (Full.fullArenaClauseLitsCore s.core
                                                        rsn32.toNat).take j.toNat =
                                                        Full.fullArenaClauseLitsCore s.core
                                                          rsn32.toNat := by
                                                    rw [hj_eq, ← hlits_len]; exact List.take_length
                                                  rw [htake_all] at hcovj
                                                  have hent_j : (cnfOfClauses F_cur).EntailsClause
                                                      (cnfClause (flLits s.core sj.core.mrk
                                                        t')) := by
                                                    refine fl_resolve_step hmrk_t'_trl hact_t'
                                                      hpresj ?_
                                                      (by simpa only [htrl_t'] using hcovj)
                                                    rw [hrsn_eq]; exact hw0.arena.entails _ href hng
                                                  c0_hsteps
                                                  exact hJb (uj, done, _brk', j, sj) m3
                                                    ⟨hokj, htmpj, fun _ _ => ⟨huj_eq, hent_j⟩, hm3⟩
                              · -- `unres == 1` branch (`G@9432` producer)
                                intro Juc hJuc
                                c0_hsplit
                                · -- `unres == 1`
                                  have hu1 : unres = 1 := by
                                    have heq : BitVec.ofNat 64 unres = 1 := by assumption
                                    have h0 := congrArg BitVec.toNat heq
                                    rw [show (1 : BitVec 64) = 1#64 from rfl] at h0
                                    rwa [bv64_ofNat_toNat (by omega)] at h0
                                  let unit1 := lit' ^^^ 1#32
                                  have hlen1_id :
                                      (flIdxs s.core s_lp.core.mrk (t' + 1)).length = 1 := by
                                    rw [← hunres_t'_0, hu1]
                                  have hunit_ent : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [unit1.toNat]) := by
                                    have hsng := flLits_eq_singleton_of_len1
                                      (by rw [htrl_t']; exact hmrk_t'_0)
                                      hlen1_id
                                    rw [hsng, htrl_t'] at hact_t'_0
                                    simpa only [unit1, fl_bv32_xor1] using hact_t'_0
                                  have hunit_lt : unit1.toNat < 2 * s.core.cur_vars := by
                                    dsimp [unit1]
                                    try rw [fl_bv32_xor1]
                                    exact litNeg_lt_two_mul hlit'_lt
                                  c0_hsplit
                                  · have huc_lt : ucnt < s.core.cur_vars := by
                                      have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                                      have huc64 : ucnt < 2 ^ 64 := by omega
                                      have hlt : ucnt % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by
                                        simpa only [hok_lp.core] using (by assumption : _)
                                      rwa [Nat.mod_eq_of_lt huc64, Nat.mod_eq_of_lt hcv64] at hlt
                                    have huc_tmp :
                                        (BitVec.ofNat 64 ucnt).toNat < s_lp.core.tmp.length := by
                                      rw [bv64_ofNat_toNat
                                        (by omega), hok_lp.len.core_ok.tmp_len_arr]
                                      omega
                                    have huc1_bv :
                                        BitVec.ofNat 64 ucnt + 1 = BitVec.ofNat 64 (ucnt + 1) :=
                                      BitVec.eq_of_toNat_eq (by
                                        rw [show (1 : BitVec 64) = 1#64 from rfl,
                                          fl_bv64_add1_toNat
                                            (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                          bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
                                    let s2 : FullState :=
                                      { s_lp with core :=
                                        { s_lp.core with tmp := s_lp.core.tmp.set ucnt unit1 } }
                                    have hok2 := fl_failedStateOk_with_tmp hok_lp
                                      (tmp' := s_lp.core.tmp.set ucnt unit1)
                                      (by rw [List.length_set, hok_lp.len.core_ok.tmp_len_arr])
                                    have htmp2 : ∀ k < ucnt + 1,
                                        (s2.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                                        (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [(s2.core.tmp[k]?.getD 0#32).toNat]) := by
                                      intro k hk
                                      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt |
                                        rfl
                                      · dsimp [s2];
                                        rw [List.getElem?_set_ne (by omega)]; exact htmp_ok k hlt
                                      · dsimp [s2]
                                        rw [List.getElem?_set_self (by
                                          rw [hok_lp.len.core_ok.tmp_len_arr];
                                          omega), Option.getD_some]
                                        exact ⟨hunit_lt, hunit_ent⟩
                                    rw [hm_eq]
                                    c0_hsteps
                                    have hm2' : (FullMem c s2 ⋆ R) m := by
                                      simpa only [s2, unit1, show (1 : BitVec 32) = 1#32 from rfl,
                                        bv64_ofNat_toNat (by omega : ucnt < 2 ^ 64)] using hm
                                    rw [huc1_bv]
                                    exact hJuc (ucnt + 1, unit1, err', s2) m
                                      ⟨he_f, hok2, rfl, rfl, rfl, by omega, htmp2, hm2'⟩
                                  · c0_hsteps
                                    rw [hm_eq, show (lit' ^^^ (1 : BitVec 32)) = unit1 from rfl]
                                    exact hJexit (unres, ucnt, done, t', unit1, true, s_lp) m1
                                      ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok,
                                        (fun h => by cases h), hm1⟩
                                · c0_hsteps
                                  rw [hm_eq]
                                  exact hJuc (ucnt, unit, err', s_lp) m1
                                    ⟨he_f, hok_lp, rfl, rfl, rfl, hucnt_le, htmp_ok, hm1⟩
                        · -- `while (true)` find next marked literal (`G@11501`)
                          intro Jfind hJfind
                          c0_hsteps_nogrp
                          refine wp_while_state (ts := [i64]) (α := Nat) (proj := fun tc =>
                              (BitVec.ofNat 64 tc, ()))
                            (μ := fun tc => tc)
                            (Inv := fun tc m_w =>
                              tc ≤ t ∧
                              flIdxs s.core s_lp.core.mrk tc = flIdxs s.core s_lp.core.mrk t ∧
                              m_w = m1) ?_ ?_
                          · intro Jw hJw; c0_hsteps; exact hJw t m1 ⟨Nat.le_refl _, rfl, rfl⟩
                          · intro Jw tc m_w ⟨htc_le, hfl_eq, hm_eq⟩ ih_w
                            rw [Blocks.get_here]; dsimp only
                            c0_hsplit
                            · c0_hsplit
                              · have htc0 : tc = 0 := by
                                  have hz : BitVec.ofNat 64 tc = 0#64 := by assumption
                                  have := congrArg BitVec.toNat hz
                                  rwa [bv64_ofNat_toNat (by omega)] at this
                                c0_hsteps
                                refine hJfind (tc, true, 0xFFFFFFFF#32) m_w ⟨hm_eq, ?_⟩
                                simp only [↓reduceIte]; exact htc_le
                              · have htc_pos : 0 < tc := Nat.pos_of_ne_zero fun hz =>
                                  (by assumption : BitVec.ofNat 64 tc ≠ 0#64)
                                    (by subst hz; rfl)
                                have hsub_bv : BitVec.ofNat 64 tc - 1 = BitVec.ofNat 64 (tc - 1) :=
                                  BitVec.eq_of_toNat_eq (by
                                    rw [show (1 : BitVec 64) = 1#64 from rfl,
                                      fl_bv64_sub1_toNat
                                        (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                      bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
                                have htrl_lp : s_lp.core.trl = s.core.trl := by rw [hok_lp.core]
                                have hcv_lp : s_lp.core.cur_vars = s.core.cur_vars := by
                                  rw [hok_lp.core]
                                have htc1_lt : tc - 1 < s_lp.core.trl.length := by
                                  rw [hok_lp.len.core_ok.trl_len]; omega
                                have htc1_te : tc - 1 < s.core.trail_end := by omega
                                have htl_lt : (s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'
                                    (by rw [bv64_ofNat_toNat (by omega)]; exact htc1_lt)).toNat <
                                    2 * s.core.cur_vars := by
                                  simp only [bv64_ofNat_toNat (by omega : tc - 1 < 2 ^ 64), htrl_lp]
                                  have h1 := hw0.trail_lits_lt (tc - 1) htc1_te
                                  rwa [List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega),
                                    Option.getD_some] at h1
                                have htl_mrk_lt :
                                    (((s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'(by
                                      rw [bv64_ofNat_toNat (by omega)]; exact htc1_lt) >>>
                                      1#32).setWidth 64).toNat) < s_lp.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hok_lp.len.core_ok.mrk_len]
                                  omega
                                have hm_w : (FullMem c s_lp ⋆ R) m_w := hm_eq ▸ hm1
                                have hidx1 : (BitVec.ofNat 64 tc - 1).toNat = tc - 1 := by
                                  rw [hsub_bv, bv64_ofNat_toNat (by omega)]
                                have hidx2 : (2 ^ 64 - 1 + tc) % 2 ^ 64 = tc - 1 := by omega
                                have hidx3 : (BitVec.ofNat 64 (tc - 1)).toNat = tc - 1 :=
                                  bv64_ofNat_toNat (by omega)
                                have htc1_bv_lt :
                                    (BitVec.ofNat 64 tc - 1).toNat < s_lp.core.trl.length := by
                                  rw [hidx1]; exact htc1_lt
                                have htl_mrk_bv_lt :
                                    (((s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt >>>
                                      1#32).setWidth 64).toNat) < s_lp.core.mrk.length := by
                                  simpa only [hsub_bv] using htl_mrk_lt
                                c0_hsplit
                                · exfalso
                                  have hge := hc
                                  try simp only [hidx2] at hge
                                  have hlt1 := htl_lt
                                  simp only [hidx3] at hlt1
                                  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                                  rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                · have hsub1 : (tc - 1) + 1 = tc := Nat.sub_add_cancel htc_pos
                                  let tl :=
                                    s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt
                                  have htl_base : tl = s_lp.core.trl[tc - 1]'htc1_lt :=
                                    fl_getElem_congr_list rfl hidx1
                                  have htl_lt' : tl.toNat < 2 * s.core.cur_vars := by
                                    rw [htl_base]; simpa only [hidx3] using htl_lt
                                  have htl_eq : (s.core.trl[tc - 1]?.getD 0#32).toNat =
                                      tl.toNat := by
                                    rw [htl_base]
                                    have hget : s_lp.core.trl[tc - 1]'htc1_lt =
                                        s.core.trl[tc - 1]'(by rw [hcl.trl_len]; omega) :=
                                      fl_getElem_congr_list (by rw [hok_lp.core]) rfl
                                    rw [hget, List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega),
                                      Option.getD_some]
                                  c0_hsplit
                                  · have hmrk_nz : s_lp.core.mrk[tl.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                                      have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                                        rw [hok_lp.len.core_ok.mrk_len]; omega
                                      have hne0 : BitVec.setWidth 32
                                          (s_lp.core.mrk[tl.toNat / 2]'hov_m) ≠ 0#32 := by
                                        have hhc := hc
                                        try simp only [hidx2] at hhc
                                        dsimp only [tl]; try simp only [hidx1]
                                        exact hhc
                                      have hov : tl.toNat / 2 < s.core.cur_vars := by omega
                                      exact fl_mark_nz_eq hok_lp hov hne0
                                    c0_hsteps
                                    let fJ : BitVec 64 → Bool → Prop :=
                                      fun a b => Jfind (a, b, tl, ()) m_w
                                    change fJ (BitVec.ofNat 64 tc - 1) err
                                    rw [show fJ (BitVec.ofNat 64 tc - 1) err =
                                        fJ (BitVec.ofNat 64 (tc - 1)) false by
                                      dsimp only [fJ]; rw [hsub_bv, herr_f]]
                                    refine hJfind (tc - 1, false, tl) m_w ⟨hm_eq, ?_⟩
                                    simp only [Bool.false_eq_true, ↓reduceIte]
                                    refine ⟨by omega, htl_eq, htl_lt', hmrk_nz, ?_, ?_⟩
                                    · rw [hsub1, hfl_eq]; exact hunres_len
                                    · rw [hsub1, flLits_congr_idxs hfl_eq]
                                      exact hact_ent
                                  · have hmrk0_w : s_lp.core.mrk[
                                        (s.core.trl[tc - 1]?.getD 0#32).toNat / 2]?.getD 0#8 =
                                        0#8 := by
                                      have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                                        rw [hok_lp.len.core_ok.mrk_len]; omega
                                      have he0 : BitVec.setWidth 32
                                          (s_lp.core.mrk[tl.toNat / 2]'hov_m) = 0#32 := by
                                        have hhc := hc
                                        try simp only [hidx2] at hhc
                                        dsimp only [tl]; try simp only [hidx1]
                                        exact hhc
                                      have hov : tl.toNat / 2 < s.core.cur_vars := by omega
                                      rw [htl_eq]
                                      exact fl_mark_zero_eq hok_lp hov he0
                                    have hfl_next : flIdxs s.core s_lp.core.mrk (tc - 1) =
                                        flIdxs s.core s_lp.core.mrk t := by
                                      have hun : ∀ j, tc - 1 ≤ j → j < tc →
                                          s_lp.core.mrk[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD
                                            0#8 = 0#8 := fun j hj1 hj2 => by
                                        obtain rfl : j = tc - 1 := by omega
                                        exact hmrk0_w
                                      exact (flIdxs_eq_of_unmarked_above
                                        (by omega) hun).symm.trans hfl_eq
                                    c0_hsteps; rw [hsub_bv]
                                    exact ih_w (tc - 1) m_w (by omega) ⟨by omega, hfl_next, hm_eq⟩
                            · c0_hsteps; exact absurd (by assumption : true = false) (by decide)
              · -- `G@8678` producer: `confl_type == 1` vs `confl_type != 1` seed
                intro Jseed hJseed
                c0_hsplit
                · -- `confl_type == 1`
                  have hct1 : s.core.confl_type = 1#64 := by
                    simpa [s0] using (by assumption : _)
                  rcases hconfl.1 with ⟨_, hc0_lt, hc1_lt, hf0, hf1, hent_bin⟩ | ⟨hne, _⟩
                  · have hconfl2 := hconfl.2
                    rw [ite_eq_left hct1] at hconfl2
                    let c0 := s.core.confl_lit0.setWidth 32
                    let c1 := s.core.confl_lit1.setWidth 32
                    have hc0_to : c0.toNat = s.core.confl_lit0.toNat := by
                      dsimp [c0]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hc1_to : c1.toNat = s.core.confl_lit1.toNat := by
                      dsimp [c1]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hm_trail0 := (hw0.vals_false_iff _ hc0_lt).mp hf0
                    have hm_trail1 := (hw0.vals_false_iff _ hc1_lt).mp hf1
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64, .bool]) (α := Nat × Bool × FullState)
                      (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                      (Inv := fun st m1 =>
                        st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2 cut ∧
                        (!st.2.1 → st.1 = (flIdxs s.core st.2.2.core.mrk s.core.trail_end).length ∧
                          (cnfOfClauses F_cur).EntailsClause
                            (cnfClause (flLits s.core st.2.2.core.mrk s.core.trail_end))) ∧
                        (FullMem c st.2.2 ⋆ R) m1) ?_ ?_
                    · intro _ ⟨un1, dn1, sb1⟩ m1 ⟨hun1, hok1, hact1, hm1⟩
                      dsimp only at hun1 hok1 hact1 hm1
                      rw [Blocks.get_here]; dsimp only
                      c0_hsteps; exact hJseed (un1, dn1, sb1) m1 ⟨hun1, hok1, hact1, hm1⟩
                    · intro J1 hJ1
                      c0_hsplit
                      · c0_hsteps
                        refine hJ1 (0, true, s0) m ⟨Nat.zero_le _, hok0, (fun h => by cases h),
                          hm_s0⟩
                      · c0_hsplit
                        · c0_hsteps
                          refine hJ1 (0, true, s0) m ⟨Nat.zero_le _, hok0, (fun h => by cases h),
                            hm_s0⟩
                        · c0_hsplit
                          · exfalso
                            have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                            have hge : s.core.cur_vars % 2 ^ 64 ≤ c0.toNat / 2 := by
                              dsimp only [c0, s0]; assumption
                            rw [Nat.mod_eq_of_lt hcv64, hc0_to] at hge; omega
                          · c0_hsplit
                            · exfalso
                              have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                              have hge : s.core.cur_vars % 2 ^ 64 ≤ c1.toNat / 2 := by
                                dsimp only [c1, s0]; assumption
                              rw [Nat.mod_eq_of_lt hcv64, hc1_to] at hge; omega
                            · c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                (Inv := fun st m1 =>
                                  st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2 cut ∧
                                  st.1 = (flIdxs s.core st.2.core.mrk s.core.trail_end).length ∧
                                  ((cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat ^^^ 1]) ∨
                                    c0.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                  (FullMem c st.2 ⋆ R) m1) ?_ ?_
                              · intro Jv0 ⟨u1, sa⟩ m1 ⟨hu1_le, hoka, hu1_eq, hc0_in, hm1⟩
                                dsimp only at hu1_le hoka hu1_eq hc0_in hm1
                                rw [Blocks.get_here]; dsimp only
                                have hc1_lvl_lt : ((c1 >>> 1#32).setWidth 64).toNat <
                                    sa.core.lvl.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hc1_to,
                                    hoka.len.core_ok.lvl_len]
                                  omega
                                have hc1_mrk_lt : ((c1 >>> 1#32).setWidth 64).toNat <
                                    sa.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, fl_bv32_lshr1, hc1_to,
                                    hoka.len.core_ok.mrk_len]
                                  omega
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                  (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                  (Inv := fun st m2 =>
                                    st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2 cut ∧
                                    st.1 = (flIdxs s.core st.2.core.mrk s.core.trail_end).length ∧
                                    ((cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat ^^^ 1])
                                      ∨
                                      c0.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                    ((cnfOfClauses F_cur).EntailsClause (cnfClause [c1.toNat ^^^ 1])
                                      ∨
                                      c1.toNat ∈ flLits s.core st.2.core.mrk s.core.trail_end) ∧
                                    (FullMem c st.2 ⋆ R) m2) ?_ ?_
                                · intro Jv1 ⟨u2, sb⟩ m2 ⟨hu2_le, hoka_b, hu2_eq, hc0_b, hc1_b, hm2⟩
                                  dsimp only at hu2_le hoka_b hu2_eq hc0_b hc1_b hm2
                                  rw [Blocks.get_here]; dsimp only
                                  have hent_sb : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause (flLits s.core sb.core.mrk s.core.trail_end)) := by
                                    refine fl_entails_of_clause
                                      (by simpa only [hc0_to, hc1_to] using hent_bin) fun q hq => ?_
                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl
                                    · simpa only [hc0_to] using hc0_b
                                    · simpa only [hc1_to] using hc1_b
                                  c0_hsteps
                                  exact hJ1 (u2, false, sb) m2
                                    ⟨hu2_le, hoka_b, fun _ => ⟨hu2_eq, hent_sb⟩, hm2⟩
                                · intro Jv1 hJv1
                                  have hc1_to' : c1.toNat < 2 * s.core.cur_vars := by omega
                                  have hc1_v_to : (c1 >>> 1#32).toNat = c1.toNat / 2 :=
                                    fl_bv32_lshr1 c1
                                  have hcva_eq : sa.core.cur_vars = s.core.cur_vars := by
                                    rw [hoka.core]
                                  c0_hsplit
                                  · c0_hsplit
                                    · have hmrk0_v1 : sa.core.mrk[c1.toNat / 2]?.getD 0#8 = 0#8 :=
                                        fl_mark_zero_eq hoka (by omega)
                                          (by dsimp only [c1, s0]; assumption)
                                      have hlvl_pos1 :
                                          0 < (s.core.lvl[c1.toNat / 2]?.getD 0#32).toNat := by
                                        have hidx : c1.toNat / 2 < sa.core.lvl.length := by
                                          rw [hoka.len.core_ok.lvl_len]; omega
                                        have hpos : (0#32).toNat <
                                            (sa.core.lvl[c1.toNat / 2]'hidx).toNat := by
                                          dsimp only [c1, s0]; assumption
                                        have heql : sa.core.lvl[c1.toNat / 2]?.getD 0#32 =
                                            s.core.lvl[c1.toNat / 2]?.getD 0#32 := by rw [hoka.core]
                                        rw [← heql, List.getElem?_eq_getElem hidx, Option.getD_some]
                                        exact hpos
                                      have hlv1_cl : (s.core.lvl[c1.toNat / 2]?.getD 0#32).toNat =
                                          s.core.cur_level := by
                                        obtain ⟨m1, hm1_te, hm1_eq⟩ := hm_trail1
                                        have hle := hw0.lvl_le m1 hm1_te
                                        rw [hm1_eq, fl_xor1_div2, ← hc1_to] at hle
                                        omega
                                      obtain ⟨hmcl_lt, hokb, hfl_len, hfl_pres, hc1_in⟩ :=
                                        fl_mark_lit_push hw0 hcl1 hoka (Nat.le_refl _) hc1_to'
                                          hmrk0_v1
                                          hlvl_pos1 (hc1_to ▸ hm_trail1) (hc1_to ▸ hconfl2.2 (hc1_to
                                            ▸ hlv1_cl))
                                      let v1 := c1.toNat / 2
                                      let v1_32 := BitVec.ofNat 32 v1
                                      let sb : FullState :=
                                        { core := { sa.core with mrk := sa.core.mrk.set v1 1#8,
                                                                 min_clr_len :=
                                                                   sa.core.min_clr_len + 1 }
                                          scratch := { sa.scratch with
                                            work_stk1 :=
                                              sa.scratch.work_stk1.set sa.core.min_clr_len
                                              v1_32 } }
                                      have hmcl_ws : (BitVec.ofNat 64 sa.core.min_clr_len).toNat <
                                          sa.scratch.work_stk1.length := by
                                        have := hoka.cov.1
                                        rw [bv64_ofNat_toNat
                                          (by omega), hoka.len.scratch_ok.work_stk1_len]
                                        omega
                                      have hv1_eq : v1_32 = c1 >>> 1 := BitVec.eq_of_toNat_eq (by
                                        rw [bv32_ofNat_toNat (by omega), bv32_lshr_1])
                                      have hmcl1_bv :
                                          (BitVec.ofNat 64 sa.core.min_clr_len + 1).toNat =
                                          sa.core.min_clr_len + 1 := by
                                        have := hoka.cov.1
                                        rw [show (1 : BitVec 64) = 1#64 from rfl,
                                          fl_bv64_add1_toNat
                                            (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                          bv64_ofNat_toNat (by omega)]
                                      have hu1_bv :
                                          BitVec.ofNat 64 u1 + 1 = BitVec.ofNat 64 (u1 + 1) :=
                                        BitVec.eq_of_toNat_eq (by
                                          rw [show (1 : BitVec 64) = 1#64 from rfl,
                                            fl_bv64_add1_toNat
                                              (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                            bv64_ofNat_toNat (by omega), bv64_ofNat_toNat
                                              (by omega)])
                                      c0_hsteps
                                      have hm2' : (FullMem c sb ⋆ R) m := by
                                        have := hoka.cov.1
                                        simpa only [sb, v1, v1_32, hv1_eq, fl_bv32_setWidth64,
                                          bv32_lshr_1, bv64_ofNat_toNat (by omega :
                                            sa.core.min_clr_len < 2 ^ 64), hmcl1_bv] using hm
                                      have hc0_b : (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [c0.toNat ^^^ 1]) ∨
                                          c0.toNat ∈ flLits s.core sb.core.mrk s.core.trail_end :=
                                        hc0_in.elim Or.inl fun hmem => Or.inr (hfl_pres _ hmem)
                                      have hu1_succ_eq :
                                          u1 + 1 =
                                            (flIdxs s.core sb.core.mrk
                                              s.core.trail_end).length := by
                                        rw [hfl_len, hu1_eq]
                                      have hu1_succ_le : u1 + 1 ≤ s.core.cur_vars := by
                                        rw [hu1_succ_eq]; exact Nat.le_trans flIdxs_length_le hte_le
                                      rw [hu1_bv]
                                      exact hJv1 (u1 + 1, sb) m
                                        ⟨hu1_succ_le, hokb, hu1_succ_eq, hc0_b, hc1_in, hm2'⟩
                                    · have hmrk_nz : sa.core.mrk[c1.toNat / 2]?.getD 0#8 ≠ 0#8 :=
                                        fl_mark_nz_eq hoka (by omega)
                                          (by dsimp only [c1, s0]; assumption)
                                      have hc1_in := fl_mark_lit_skip hw0 hcl1 (Nat.le_refl _)
                                        (fun _ => by simpa [hc1_to] using hm_trail1)
                                        (fun _ => ⟨hmrk_nz, by simpa [hc1_to] using hm_trail1⟩)
                                      c0_hsteps
                                      exact hJv1 (u1, sa) m1 ⟨hu1_le, hoka, hu1_eq, hc0_in, hc1_in,
                                        hm1⟩
                                  · have hlvl0 :
                                        (s.core.lvl[c1.toNat / 2]?.getD 0#32).toNat = 0 := by
                                      have hidx : c1.toNat / 2 < sa.core.lvl.length := by
                                        rw [hoka.len.core_ok.lvl_len]; omega
                                      have hno : ¬ (0#32).toNat <
                                          (sa.core.lvl[c1.toNat / 2]'hidx).toNat := by
                                        dsimp only [c1, s0]; assumption
                                      have heql : sa.core.lvl[c1.toNat / 2]?.getD 0#32 =
                                          s.core.lvl[c1.toNat / 2]?.getD 0#32 := by rw [hoka.core]
                                      rw [← heql, List.getElem?_eq_getElem hidx, Option.getD_some]
                                      have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
                                      omega
                                    have hc1_in :=
                                      fl_mark_lit_skip (s1 := sa) (q := c1.toNat) hw0 hcl1
                                        (Nat.le_refl _)
                                        (fun _ => by simpa [hc1_to] using hm_trail1)
                                        (fun hp => by omega)
                                    c0_hsteps
                                    exact hJv1 (u1, sa) m1 ⟨hu1_le, hoka, hu1_eq, hc0_in, hc1_in,
                                      hm1⟩
                              · intro Jv0 hJv0
                                have hc0_to' : c0.toNat < 2 * s.core.cur_vars := by omega
                                have hc0_v_to : (c0 >>> 1#32).toNat = c0.toNat / 2 :=
                                  fl_bv32_lshr1 c0
                                have hc0_lvl_lt : ((c0 >>> 1#32).setWidth 64).toNat <
                                    s0.core.lvl.length := by
                                  rw [fl_bv32_setWidth64, hc0_v_to, hok0.len.core_ok.lvl_len]; omega
                                have hc0_mrk_lt : ((c0 >>> 1#32).setWidth 64).toNat <
                                    s0.core.mrk.length := by
                                  rw [fl_bv32_setWidth64, hc0_v_to, hok0.len.core_ok.mrk_len]; omega
                                c0_hsplit
                                · c0_hsplit
                                  · have hmrk0_v0 : s0.core.mrk[c0.toNat / 2]?.getD 0#8 = 0#8 :=
                                      fl_mark_zero_eq hok0 (by omega)
                                        (by dsimp only [c0, s0]; assumption)
                                    have hlvl_pos0 :
                                        0 < (s.core.lvl[c0.toNat / 2]?.getD 0#32).toNat := by
                                      have hidx : c0.toNat / 2 < s0.core.lvl.length := by
                                        rw [hok0.len.core_ok.lvl_len]; omega
                                      have hpos : (0#32).toNat <
                                          (s0.core.lvl[c0.toNat / 2]'hidx).toNat := by
                                        dsimp only [c0, s0]; assumption
                                      have heql : s0.core.lvl[c0.toNat / 2]?.getD 0#32 =
                                          s.core.lvl[c0.toNat / 2]?.getD 0#32 := by rw [hok0.core]
                                      rw [← heql, List.getElem?_eq_getElem hidx, Option.getD_some]
                                      exact hpos
                                    have hlv0_cl : (s.core.lvl[c0.toNat / 2]?.getD 0#32).toNat =
                                        s.core.cur_level := by
                                      obtain ⟨m0', hm0_te, hm0_eq⟩ := hm_trail0
                                      have hle := hw0.lvl_le m0' hm0_te
                                      rw [hm0_eq, fl_xor1_div2, ← hc0_to] at hle
                                      omega
                                    obtain ⟨hmcl_lt, hoka, hfl_len, _, hc0_in⟩ :=
                                      fl_mark_lit_push hw0 hcl1 hok0 (Nat.le_refl _) hc0_to'
                                        hmrk0_v0
                                        hlvl_pos0 (hc0_to ▸ hm_trail0) (hc0_to ▸ hconfl2.1 (hc0_to ▸
                                          hlv0_cl))
                                    let v0 := c0.toNat / 2
                                    let v0_32 := BitVec.ofNat 32 v0
                                    let sa : FullState :=
                                      { core := { s0.core with mrk := s0.core.mrk.set v0 1#8,
                                                               min_clr_len :=
                                                                 s0.core.min_clr_len + 1 }
                                        scratch := { s0.scratch with
                                          work_stk1 := s0.scratch.work_stk1.set s0.core.min_clr_len
                                            v0_32 } }
                                    have hv0_eq : v0_32 = c0 >>> 1 := BitVec.eq_of_toNat_eq (by
                                      rw [bv32_ofNat_toNat (by omega), bv32_lshr_1])
                                    have hmcl1_bv0 :
                                        (BitVec.ofNat 64 s0.core.min_clr_len + 1).toNat =
                                        s0.core.min_clr_len + 1 := by
                                      have := hok0.cov.1; have := hok0.core
                                      rw [show (1 : BitVec 64) = 1#64 from rfl,
                                        fl_bv64_add1_toNat
                                          (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                        bv64_ofNat_toNat (by omega)]
                                    have hmcl_ws0 : (BitVec.ofNat 64 s0.core.min_clr_len).toNat <
                                        s0.scratch.work_stk1.length := by
                                      have := hok0.cov.1
                                      rw [bv64_ofNat_toNat
                                        (by omega), hok0.len.scratch_ok.work_stk1_len]; omega
                                    c0_hsteps
                                    have hm1' : (FullMem c sa ⋆ R) m := by
                                      have := hok0.cov.1; have := hok0.core
                                      simpa only [sa, v0, v0_32, hv0_eq, c0, fl_bv32_setWidth64,
                                        bv32_lshr_1, bv64_ofNat_toNat (by omega :
                                          s0.core.min_clr_len < 2 ^ 64), hmcl1_bv0,
                                        show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                    exact hJv0 (1, sa) m
                                      ⟨by omega, hoka, by
                                        rw [hfl_len, flIdxs_eq_nil_of_zero (fun j hj =>
                                          hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                            (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                              (hw0.trail_lits_lt j hj)) hcv_le))]
                                        rfl,
                                       hc0_in, hm1'⟩
                                  · have hmrk_nz : s0.core.mrk[c0.toNat / 2]?.getD 0#8 ≠ 0#8 :=
                                      fl_mark_nz_eq hok0 (by omega)
                                        (by dsimp only [c0, s0]; assumption)
                                    have hc0_in := fl_mark_lit_skip hw0 hcl1 (Nat.le_refl _)
                                      (fun _ => by simpa [hc0_to] using hm_trail0)
                                      (fun _ => ⟨hmrk_nz, by simpa [hc0_to] using hm_trail0⟩)
                                    c0_hsteps
                                    exact hJv0 (0, s0) m
                                      ⟨Nat.zero_le _, hok0, by
                                        rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                          hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                            (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                              (hw0.trail_lits_lt j hj)) hcv_le))]
                                        rfl,
                                       hc0_in, hm_s0⟩
                                · have hlvl0 : (s.core.lvl[c0.toNat / 2]?.getD 0#32).toNat = 0 := by
                                    have hidx : c0.toNat / 2 < s0.core.lvl.length := by
                                      rw [hok0.len.core_ok.lvl_len]; omega
                                    have hno : ¬ (0#32).toNat <
                                        (s0.core.lvl[c0.toNat / 2]'hidx).toNat := by
                                      dsimp only [c0, s0]; assumption
                                    have heql : s0.core.lvl[c0.toNat / 2]?.getD 0#32 =
                                        s.core.lvl[c0.toNat / 2]?.getD 0#32 := by rw [hok0.core]
                                    rw [← heql, List.getElem?_eq_getElem hidx, Option.getD_some]
                                    have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
                                    omega
                                  have hc0_in :=
                                    fl_mark_lit_skip (s1 := s0) (q := c0.toNat) hw0 hcl1
                                      (Nat.le_refl _)
                                      (fun _ => by simpa [hc0_to] using hm_trail0)
                                      (fun hp => by omega)
                                  c0_hsteps
                                  exact hJv0 (0, s0) m
                                    ⟨Nat.zero_le _, hok0, by
                                      rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                        hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                          (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                            (hw0.trail_lits_lt j hj)) hcv_le))]
                                      rfl,
                                     hc0_in, hm_s0⟩
                  · exact absurd (hct1.symm.trans hne) (by decide)
                · -- `confl_type != 1` (`confl_type = 2`, arena clause)
                  have hct_ne : s.core.confl_type ≠ 1#64 := by
                    simpa [s0] using (by assumption : _)
                  rcases hconfl.1 with ⟨h1, _⟩ | ⟨hct2, href, hng, hfals⟩
                  · exact absurd h1 hct_ne
                  · have hconfl2 := hconfl.2
                    rw [ite_eq_right hct_ne] at hconfl2
                    have hwf := hw0.arena.refs_wf _ href
                    have har_cap := c.harena; unfold dimacsBound at har_cap
                    have hal_le := hcl.arena_len_le
                    have hwf1 := hwf.1
                    have hwf3 := hwf.2.2.1
                    have hwf4 := hwf.2.2.2.1
                    let cr32 := s0.core.confl_ref.setWidth 32
                    have hcr_to : cr32.toNat = s.core.confl_ref.toNat := by
                      dsimp [cr32, s0]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hcr_add2_lt : (cr32.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                      rw [hok0.len.core_ok.arena_len_arr, BitVec.toNat_add, fl_bv32_setWidth64,
                        show (2#64 : BitVec 64).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt (by omega : cr32.toNat + 2 < 2 ^ 64)]
                      have := hcl.arena_len_le; omega
                    c0_hsplit
                    · exfalso
                      have hle3 : cr32.toNat + 3 ≤ s.core.arena_len := by rw [hcr_to]; exact hwf.1
                      have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                      have hgt : s0.core.arena_len % 2 ^ 64 < (cr32.toNat + 3) % 2 ^ 64 := by
                        dsimp only [cr32, s0]; assumption
                      dsimp only [s0] at hgt
                      rw [Nat.mod_eq_of_lt hal64,
                        Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64)] at hgt
                      omega
                    · have hcsz_eq :
                          (s0.core.arena[(cr32.setWidth 64 + 2#64).toNat]'hcr_add2_lt).toNat =
                          Full.fullArenaClauseSizeCore s.core cr32.toNat := by
                        rw [hcr_to]; unfold Full.fullArenaClauseSizeCore
                        have hidx : s.core.confl_ref.toNat + 2 < s.core.arena.length := by
                          rw [hcl.arena_len_arr]; have := hcl.arena_len_le; omega
                        have heq : s0.core.arena[(cr32.setWidth 64 + 2#64).toNat]'hcr_add2_lt =
                            s.core.arena[s.core.confl_ref.toNat + 2]'hidx := by
                          dsimp only [s0]; congr 1
                          rw [BitVec.toNat_add, fl_bv32_setWidth64,
                            show (2#64 : BitVec 64).toNat = 2 from rfl,
                            Nat.mod_eq_of_lt (by omega : cr32.toNat + 2 < 2 ^ 64), hcr_to]
                        rw [heq, List.getElem?_eq_getElem hidx, Option.getD_some]
                      let csz := s0.core.arena[(cr32.setWidth 64 + 2#64).toNat]'hcr_add2_lt
                      have hcsz_bd : cr32.toNat + 3 +
                          Full.fullArenaClauseSizeCore s.core cr32.toNat ≤ s.core.arena.length := by
                        have hle_a : cr32.toNat + 3 +
                            Full.fullArenaClauseSizeCore s.core cr32.toNat ≤ s.core.arena_len := by
                          rw [hcr_to]; omega
                        exact Nat.le_trans hle_a (hcl.arena_len_arr ▸ hcl.arena_len_le)
                      have hcsz_lits_len :
                          (Full.fullArenaClauseLitsCore s.core cr32.toNat).length = csz.toNat :=
                        (fl_arenaClauseLitsCore_length hcsz_bd).trans hcsz_eq.symm
                      c0_hsplit
                      · exfalso
                        have hle_a : cr32.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                          rw [show csz.toNat = Full.fullArenaClauseSizeCore s.core cr32.toNat from
                            hcsz_eq, hcr_to]
                          have := hwf.2.2.1; have := hwf.2.2.2.1; omega
                        have hcsz_bd32 : csz.toNat < 2 ^ 32 := csz.isLt
                        have hal64 : s.core.arena_len < 2 ^ 64 := by omega
                        have hgt : s0.core.arena_len % 2 ^ 64 <
                            (cr32.toNat + 3 + csz.toNat) % 2 ^ 64 := by
                          dsimp only [csz, cr32, s0]; assumption
                        dsimp only [s0] at hgt
                        rw [Nat.mod_eq_of_lt hal64,
                          Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 + csz.toNat < 2 ^ 64)] at hgt
                        omega
                      · c0_hsteps_nogrp
                        refine wp_join_state (ts := [i64, .bool, i32])
                          (α := Nat × Bool × BitVec 32 × FullState)
                          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                          (Inv := fun st m1 =>
                            st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2.2 cut ∧
                            (!st.2.1 → st.1 =
                              (flIdxs s.core st.2.2.2.core.mrk s.core.trail_end).length ∧
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause (flLits s.core st.2.2.2.core.mrk s.core.trail_end))) ∧
                            (FullMem c st.2.2.2 ⋆ R) m1) ?_ ?_
                        · intro _ ⟨un_s, dn_s, _i_s, s_s⟩ m1 ⟨hun_le, hok_s, hact_s, hm1⟩
                          dsimp only at hun_le hok_s hact_s hm1
                          rw [Blocks.get_here]; dsimp only
                          c0_hsteps; exact hJseed (un_s, dn_s, s_s) m1 ⟨hun_le, hok_s, hact_s, hm1⟩
                        · intro J1 hJ1
                          let SdLp := Nat × BitVec 32 × FullState
                          refine wp_while_state (ts := [i64, i32]) (α := SdLp)
                            (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
                            (μ := fun st => csz.toNat - st.2.1.toNat)
                            (Inv := fun st m1 =>
                              let ui := st.1; let i := st.2.1; let si := st.2.2
                              i.toNat ≤ csz.toNat ∧ FailedStateOk c s si cut ∧
                              ui = (flIdxs s.core si.core.mrk s.core.trail_end).length ∧
                              (∀ q ∈ (Full.fullArenaClauseLitsCore s.core cr32.toNat).take i.toNat,
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                                q ∈ flLits s.core si.core.mrk s.core.trail_end) ∧
                              (FullMem c si ⋆ R) m1) ?_ ?_
                          · intro Jl hJl; c0_hsteps
                            exact hJl (0, 0#32, s0) m
                              ⟨Nat.zero_le _, hok0, by
                                rw [flIdxs_eq_nil_of_zero (fun j hj =>
                                  hlm0.1 ((s.core.trl[j]?.getD 0#32).toNat / 2)
                                    (Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul
                                      (hw0.trail_lits_lt j hj)) hcv_le))]
                                rfl,
                               fun _ hq => by simp at hq, hm_s0⟩
                          · intro Jl ⟨ui, i, si⟩ m1 ⟨hi_le, hoki, hui_eq, hcovi, hm1⟩ ih_i
                            dsimp only at hi_le hoki hui_eq hcovi hm1 ih_i
                            rw [Blocks.get_here]; dsimp only
                            have hi_cv := hoki.len.core_ok
                            have hui_bd : ui ≤ s.core.cur_vars :=
                              Nat.le_trans (hui_eq ▸ flIdxs_length_le) (by omega)
                            c0_hsplit
                            · have hi_lt : i.toNat < csz.toNat := by
                                dsimp only [csz, cr32, s0]; assumption
                              have hlit_ar_lt :
                                  (cr32.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                                    si.core.arena.length := by
                                rw [hi_cv.arena_len_arr, BitVec.toNat_add, BitVec.toNat_add,
                                  fl_bv32_setWidth64, fl_bv32_setWidth64,
                                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64),
                                  Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 + i.toNat < 2 ^ 64)]
                                have h3 : cr32.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                                  rw [show csz.toNat =
                                    Full.fullArenaClauseSizeCore s.core cr32.toNat from
                                    hcsz_eq, hcr_to]
                                  exact Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
                                have := hcl.arena_len_le; omega
                              let lit := si.core.arena[
                                (cr32.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hlit_ar_lt
                              have hlit_ar_lt_c :
                                  (s0.core.confl_ref.toNat % 2 ^ 32 + 3 + i.toNat) % 2 ^ 64 <
                                    si.core.arena.length := by
                                change (cr32.toNat + 3 + i.toNat) % 2 ^ 64 < si.core.arena.length
                                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt
                                    (by omega : cr32.toNat + 3 < 2 ^ 64)] using hlit_ar_lt
                              have hlit_hc :
                                  si.core.arena[(s0.core.confl_ref.toNat % 2 ^ 32 + 3 +
                                    i.toNat) % 2 ^ 64]'
                                    hlit_ar_lt_c = lit := by
                                dsimp only [lit, cr32]; congr 1
                                have hcr_lt64 : s0.core.confl_ref.toNat % 2 ^ 32 + 3 < 2 ^ 64 := by
                                  have := hcr_to; dsimp only [cr32] at this
                                  rw [BitVec.toNat_setWidth] at this; omega
                                try rw [BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64,
                                  fl_bv32_setWidth64, BitVec.toNat_setWidth,
                                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt hcr_lt64]
                              have hlit_lits_len :
                                  i.toNat <
                                    (Full.fullArenaClauseLitsCore s.core cr32.toNat).length := by
                                rw [hcsz_lits_len]; exact hi_lt
                              have hlit_get :
                                  (Full.fullArenaClauseLitsCore s.core cr32.toNat)[
                                    i.toNat]'hlit_lits_len = lit.toNat := by
                                rw [fl_arenaClauseLitsCore_getElem hcsz_bd
                                  (by rw [← hcsz_eq]; exact hi_lt) hlit_lits_len
                                  (by rw [hcl.arena_len_arr, ← hoki.len.core_ok.arena_len_arr]
                                      simpa [BitVec.toNat_add, fl_bv32_setWidth64,
                                        Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64),
                                        Nat.mod_eq_of_lt
                                          (by omega : cr32.toNat + 3 + i.toNat < 2 ^ 64)]
                                        using hlit_ar_lt)]
                                dsimp [lit]
                                congr 1
                                have har_i : cr32.toNat + 3 + i.toNat < s.core.arena.length := by
                                  have h1 : i.toNat <
                                      Full.fullArenaClauseSizeCore s.core cr32.toNat := by
                                    rw [← hcsz_eq]; exact hi_lt
                                  omega
                                have heq : si.core.arena[(cr32.setWidth 64 + 3#64 +
                                    i.setWidth 64).toNat]'hlit_ar_lt =
                                    s.core.arena[cr32.toNat + 3 + i.toNat]'har_i := by
                                  refine fl_getElem_congr_list (by rw [hoki.core]) ?_
                                  rw [BitVec.toNat_add, BitVec.toNat_add,
                                    fl_bv32_setWidth64, fl_bv32_setWidth64,
                                    show (3#64 : BitVec 64).toNat = 3 from rfl,
                                    Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by omega : cr32.toNat + 3 + i.toNat < 2 ^ 64)]
                                exact heq.symm
                              have hlit_mem :
                                  lit.toNat ∈ Full.fullArenaClauseLits s
                                    s.core.confl_ref.toNat := by
                                unfold Full.fullArenaClauseLits
                                rw [← hcr_to, ← hlit_get]; exact List.getElem_mem _
                              have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
                                hw0.arena.lits_lt _ href hng _ hlit_mem
                              have hi1_bv : (i + 1#32).toNat = i.toNat + 1 :=
                                fl_bv32_add1_toNat (by omega)
                              c0_hsplit
                              · -- `lit == not_failed`: break to `J1` (`done = true`)!
                                c0_hsteps
                                exact hJ1 (ui, true, i, si) m1 ⟨hui_bd, hoki, (fun h => by cases h),
                                  hm1⟩
                              · have hlv_lt : lit.toNat / 2 < s.core.cur_vars :=
                                  Nat.div_lt_of_lt_mul hlit_lt
                                have hcv_si : si.core.cur_vars = s.core.cur_vars := by
                                  rw [hoki.core]
                                have hlv_lvl_lt : lit.toNat / 2 < si.core.lvl.length := by
                                  rw [hi_cv.lvl_len]
                                  exact Nat.lt_of_lt_of_le hlv_lt
                                    (hcv_si ▸ hcv_le)
                                have hlv_mrk_lt : lit.toNat / 2 < si.core.mrk.length := by
                                  rw [hi_cv.mrk_len]
                                  exact Nat.lt_of_lt_of_le hlv_lt
                                    (hcv_si ▸ hcv_le)
                                c0_hsplit
                                · exfalso
                                  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
                                  have hge : s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2 := by
                                    rw [← hlit_hc]; assumption
                                  rw [Nat.mod_eq_of_lt hcv64] at hge; omega
                                · c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                                    (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                                    (Inv := fun st m2 =>
                                      let ui' := st.1; let si' := st.2
                                      FailedStateOk c s si' cut ∧
                                      ui' = (flIdxs s.core si'.core.mrk s.core.trail_end).length ∧
                                      (∀ q ∈ (Full.fullArenaClauseLitsCore s.core cr32.toNat).take
                                          (i.toNat + 1),
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                                        q ∈ flLits s.core si'.core.mrk s.core.trail_end) ∧
                                      (FullMem c si' ⋆ R) m2) ?_ ?_
                                  · intro Js_step ⟨ui', si'⟩ m2 ⟨hok', hui', hcov', hm2⟩
                                    dsimp only at hok' hui' hcov' hm2
                                    rw [Blocks.get_here]; dsimp only
                                    c0_hsteps
                                    exact ih_i (ui', i + 1#32, si') m2 (by dsimp only; omega)
                                      ⟨by dsimp only; omega, hok', hui',
                                       by dsimp only; simpa only [hi1_bv] using hcov', hm2⟩
                                  · intro Js_step hJs_step
                                    have hlit_trail :=
                                      (hw0.vals_false_iff _ hlit_lt).mp (hfals _ hlit_mem)
                                    have hlv_to : (lit >>> 1#32).toNat = lit.toNat / 2 :=
                                      fl_bv32_lshr1 lit
                                    have hcvi_eq : si.core.cur_vars = s.core.cur_vars := by
                                      rw [hoki.core]
                                    c0_hsplit
                                    · c0_hsplit
                                      · have hmrk0_lv :
                                            si.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
                                          refine fl_mark_zero_eq hoki hlv_lt ?_
                                          simp only [← hlit_hc]; assumption
                                        have hlvl_pos :
                                            0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat := by
                                          have hpos : (0#32).toNat <
                                              (si.core.lvl[lit.toNat / 2]'hlv_lvl_lt).toNat := by
                                            simp only [← hlit_hc,
                                              show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from
                                                rfl]
                                            assumption
                                          have heql : si.core.lvl[lit.toNat / 2]?.getD 0#32 =
                                              s.core.lvl[lit.toNat / 2]?.getD 0#32 := by
                                                rw [hoki.core]
                                          rw [← heql, List.getElem?_eq_getElem hlv_lvl_lt,
                                            Option.getD_some]
                                          exact hpos
                                        have hlv_cl : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat =
                                            s.core.cur_level := by
                                          obtain ⟨ml, hml_te, hml_eq⟩ := hlit_trail
                                          have hle := hw0.lvl_le ml hml_te
                                          rw [hml_eq, fl_xor1_div2] at hle; omega
                                        obtain ⟨hmcl_lt, hok2, hfl_len, hfl_pres, hlit_in⟩ :=
                                          fl_mark_lit_push hw0 hcl1 hoki (Nat.le_refl _) hlit_lt
                                            hmrk0_lv
                                            hlvl_pos hlit_trail (hconfl2 _ hlit_mem hlv_cl)
                                        let lv := lit.toNat / 2
                                        let lv32 := BitVec.ofNat 32 lv
                                        let s2 : FullState :=
                                          { core :=
                                              { si.core with
                                                mrk := si.core.mrk.set lv 1#8,
                                                min_clr_len := si.core.min_clr_len + 1 }
                                            scratch :=
                                              { si.scratch with
                                                work_stk1 :=
                                                  si.scratch.work_stk1.set si.core.min_clr_len
                                                    lv32 } }
                                        have hcov2 : ∀ q ∈ (Full.fullArenaClauseLitsCore
                                            s.core cr32.toNat).take (i.toNat + 1),
                                            (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1])
                                              ∨
                                            q ∈ flLits s.core s2.core.mrk s.core.trail_end := by
                                          refine fl_take_succ_forall _ hlit_lits_len _
                                            (fun q hq => ?_) ?_
                                          · rcases hcovi q hq with h0 | hm
                                            · exact Or.inl h0
                                            · exact Or.inr (hfl_pres q hm)
                                          · rw [hlit_get]; exact hlit_in
                                        have hmcl1_bv :
                                            (BitVec.ofNat 64 si.core.min_clr_len + 1).toNat =
                                            si.core.min_clr_len + 1 := by
                                          have := hoki.cov.1
                                          rw [show (1 : BitVec 64) = 1#64 from rfl,
                                            fl_bv64_add1_toNat
                                              (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                            bv64_ofNat_toNat (by omega)]
                                        have hmcl_ws : (BitVec.ofNat 64 si.core.min_clr_len).toNat <
                                            si.scratch.work_stk1.length := by
                                          have := hoki.cov.1
                                          rw [bv64_ofNat_toNat
                                            (by omega), hoki.len.scratch_ok.work_stk1_len]
                                          omega
                                        c0_hsteps_nogrp
                                        refine wp_join_state (ts := []) (α := FullState)
                                          (proj := fun _ => ())
                                          (Inv := fun si' m2 =>
                                            FailedStateOk c s si' cut ∧
                                            ui + 1 =
                                              (flIdxs s.core si'.core.mrk s.core.trail_end).length ∧
                                            (∀ q ∈ (Full.fullArenaClauseLitsCore s.core
                                                cr32.toNat).take (i.toNat + 1),
                                              (cnfOfClauses F_cur).EntailsClause
                                                (cnfClause [q ^^^ 1]) ∨
                                              q ∈ flLits s.core si'.core.mrk s.core.trail_end) ∧
                                            (FullMem c si' ⋆ R) m2) ?_ ?_
                                        · intro Jinc si' m2 ⟨hok', hui', hcov', hm2⟩
                                          rw [Blocks.get_here]; dsimp only
                                          have hui1_bv :
                                              BitVec.ofNat 64 ui + 1 = BitVec.ofNat 64 (ui + 1) :=
                                            BitVec.eq_of_toNat_eq (by
                                              rw [show (1 : BitVec 64) = 1#64 from rfl,
                                                fl_bv64_add1_toNat
                                                  (by rw [bv64_ofNat_toNat (by omega)]; omega),
                                                bv64_ofNat_toNat (by omega),
                                                bv64_ofNat_toNat (by omega)])
                                          c0_hsteps; rw [hui1_bv]
                                          exact hJs_step (ui + 1, si') m2 ⟨hok', hui', hcov', hm2⟩
                                        · intro Jinc hJinc
                                          c0_hsplit
                                          · have hlv32_eq : lv32 = lit >>> 1 :=
                                              BitVec.eq_of_toNat_eq
                                                (by rw [bv32_ofNat_toNat (by omega), bv32_lshr_1])
                                            c0_hsteps
                                            have hm2' : (FullMem c s2 ⋆ R) m := by
                                              have := hoki.cov.1
                                              simpa only [s2, lv, lv32, hlv32_eq, lit, cr32,
                                                show (3 : BitVec 64) = 3#64 from rfl,
                                                fl_bv32_setWidth64, bv32_lshr_1,
                                                bv64_ofNat_toNat (by omega :
                                                  si.core.min_clr_len < 2 ^ 64), hmcl1_bv,
                                                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                                            exact hJinc s2 m
                                              ⟨hok2, by
                                                rw [hui_eq]
                                                dsimp only [s2, lv]
                                                rw [hfl_len],
                                               hcov2, hm2'⟩
                                          · exfalso
                                            have := hoki.cov.1
                                            have hge : ¬ si.core.min_clr_len % 2 ^ 64 <
                                                s.core.cur_vars % 2 ^ 64 := by assumption
                                            rw [Nat.mod_eq_of_lt (by omega :
                                                si.core.min_clr_len < 2 ^ 64),
                                              Nat.mod_eq_of_lt
                                                (by omega : s.core.cur_vars < 2 ^ 64)] at hge
                                            omega
                                      · have hmrk_nz :
                                            si.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                                          refine fl_mark_nz_eq hoki hlv_lt ?_
                                          simp only [← hlit_hc]; assumption
                                        have hlit_in :=
                                          fl_mark_lit_skip (q := lit.toNat) hw0 hcl1 (Nat.le_refl _)
                                          (fun _ => hlit_trail)
                                          (fun _ => ⟨hmrk_nz, hlit_trail⟩)
                                        have hcov2 := fl_take_succ_forall _ hlit_lits_len _ hcovi
                                          (hlit_get ▸ hlit_in)
                                        c0_hsteps
                                        exact hJs_step (ui, si) m1 ⟨hoki, hui_eq, hcov2, hm1⟩
                                    · have hlvl0 :
                                          (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
                                        have hno : ¬ (0#32).toNat <
                                            (si.core.lvl[lit.toNat / 2]'hlv_lvl_lt).toNat := by
                                          simp only [← hlit_hc,
                                            show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from rfl]
                                          assumption
                                        have heql : si.core.lvl[lit.toNat / 2]?.getD 0#32 =
                                            s.core.lvl[lit.toNat / 2]?.getD 0#32 := by
                                              rw [hoki.core]
                                        rw [← heql, List.getElem?_eq_getElem hlv_lvl_lt,
                                          Option.getD_some]
                                        have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
                                        omega
                                      have hlit_in := fl_mark_lit_skip (s1 := si) (q := lit.toNat)
                                        hw0 hcl1 (Nat.le_refl _) (fun _ => hlit_trail)
                                        (fun hp => by omega)
                                      have hcov2 := fl_take_succ_forall _ hlit_lits_len _ hcovi
                                        (hlit_get ▸ hlit_in)
                                      c0_hsteps
                                      exact hJs_step (ui, si) m1 ⟨hoki, hui_eq, hcov2, hm1⟩
                            · have hcsz_lt_c :
                                  (s0.core.confl_ref.toNat % 2 ^ 32 + 2) % 2 ^ 64 <
                                    s0.core.arena.length := by
                                change (cr32.toNat + 2) % 2 ^ 64 < s0.core.arena.length
                                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                                  Nat.mod_eq_of_lt
                                    (by omega : cr32.toNat + 2 < 2 ^ 64)] using hcr_add2_lt
                              have hcsz_hc :
                                  s0.core.arena[(s0.core.confl_ref.toNat % 2 ^ 32 + 2) % 2 ^ 64]'
                                    hcsz_lt_c = csz := by
                                dsimp only [csz, cr32]; congr 1
                              have hi_nge : ¬ i.toNat < csz.toNat := by rw [← hcsz_hc]; assumption
                              have hi_eq : i.toNat = csz.toNat := by omega
                              have htake_all :
                                  (Full.fullArenaClauseLitsCore s.core cr32.toNat).take i.toNat =
                                    Full.fullArenaClauseLitsCore s.core cr32.toNat := by
                                rw [hi_eq, ← hcsz_lits_len]; exact List.take_length
                              rw [htake_all] at hcovi
                              have hent_sd : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause (flLits s.core si.core.mrk s.core.trail_end)) := by
                                refine fl_entails_of_clause ?_ hcovi
                                rw [hcr_to]; exact hw0.arena.entails _ href hng
                              c0_hsteps
                              exact hJ1 (ui, false, i, si) m1 ⟨hui_bd, hoki, fun _ => ⟨hui_eq,
                                hent_sd⟩, hm1⟩

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
