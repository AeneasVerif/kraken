/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityBva
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2b0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7BvaSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-13 S6a Unchanged-Caller Lifts — Part 1d0 (`full_bva_pick_cand` & Step-7 BVA Exit)

100% callee-parametric (`Γ : Env`) Step-13 lift for `FullFidelityBva.full_bva_pick_cand_body`
against `step13BvaPickCandSpec`, plus Step-7 `step7TryLitExitBlock`, `Step7BvaLayout` helpers,
and `s6a_bva_step7_exit_phase_wp` over `step7BvaCommitSpec` (`public section`, `0 @[expose]` on
theorems/lemmas, `0` `import all`, `<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullDenseWatchHelpers FullBvaFwdHelpers
open FullFidelityBva FullFidelityStep7
open scoped FullArenaTactics FullBvaHeapTactics FullBvaFwdTactics

@[local bv_c0] private theorem s6a_bva_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem s6a_bva_bv32_one : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem s6a_bva_bv64_two : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem s6a_bva_bv64_three : (3 : BitVec 64).toNat = 3 := rfl

@[expose] public section

/-- Step-7 exit block of `FullFidelityStep7.full_bva_try_lit_body` (`best_k == 0` early return,
`h->res_sz = best_k`, tail call `full_bva_commit`). -/
@[reducible] def step7TryLitExitBlock
    (V : Ty → Type) (L : List Ty → Type)
    (ecap_2 ecap_3 : V i64)
    (ecap_4 : Tup V [i64, i32, i64]) :
    Tup L [[i32, i32, i32, i32, i64]] →
    Blocks V L [Ty.bool] [[i32, i32, i32, i32, i64]] :=
  fun _Js =>
    Blocks.cons (fun p =>
    Expr.group (sig := [[i32]]) (fun Js =>
    Blocks.cons (fun p_1 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                args := (Arg.var p_1.fst, Arg.var p.snd.fst, ()) } fun p_2 =>
    Expr.jnz (Arg.var p_2.fst)
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_1.fst, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ecap_2, Arg.var p.fst, ()) } fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ecap_3, Arg.var p.fst, ()) } fun p =>
    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_3 =>
    Expr.store (Arg.var p_3.fst) (Arg.var p.fst)
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                args := (Arg.var p_1.fst, Arg.imm 1, ()) } fun p =>
    Expr.jump Js.fst (Arg.var p.fst, ())))
    (
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                args := (Arg.var p.snd.snd.snd.fst, Arg.imm 0, ()) } fun p_3 =>
    Expr.jnz (Arg.var p_3.fst) (
    Expr.ret (Arg.imm false, ()))
    (
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                args := (Arg.var p.snd.snd.snd.fst, ()) } fun p_4 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var ecap_4.fst, Arg.imm 1144, ()) } fun p_5 =>
    Expr.store (Arg.var p_4.fst) (Arg.var p_5.fst) (
    Expr.call (as := [i64, i32]) (bs := [Ty.bool]) "full_bva_commit"
      (Arg.var ecap_4.fst, Arg.var p.snd.snd.snd.fst, ()) fun p =>
    Expr.ret (Arg.var p.fst, ())))))
    Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.imm 0, ()))
    Blocks.nil

end

public section

/-- Parametric Step-13 lift of `FullFidelityBva.full_bva_pick_cand_body` certifying
`step13BvaPickCandSpec` (`ncntd ≤ 2 * c.max_vars`). -/
theorem full_bva_pick_cand_step13_wp (Γ : Env) :
    ∀ a m Q X, step13BvaPickCandSpec a m Q X →
      Func.wp Γ FullFidelityBva.full_bva_pick_cand_body a m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  unfold Func.wp FullFidelityBva.full_bva_pick_cand_body
  c0_hsteps
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps
    all_goals first
      | exact ih1 (_, _, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · let mkSt (ws : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := s.core.repr, min_clr := s.core.min_clr,
                              tmp_cnt := s.core.tmp_cnt, tmp_len := s.core.tmp_len }
        scratch := { s.scratch with wsort := ws, ant_sz := s.scratch.ant_sz,
                                    sim_sig := s.scratch.sim_sig,
                                    shrink_stk := s.scratch.shrink_stk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (ci, ()) m2 => ∃ ws2,
        ci.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
        (FullMem c (mkSt ws2) ⋆ R) m2)
      (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 (0#32, ()) ml ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hm⟩)
      (fun J2 (ci, ()) m2 ⟨ws2, hci_le, hws2_len, hm2⟩ ih2 => ?_)
    dsimp only [mkSt] at hm2
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps
      exact ih2 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by simp [hws2_len], hm⟩
    · have hinv_fin : FullDenseInvNoLm c F0 F_cur (mkSt ws2) :=
        fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
          hcl.flags_len hcl.tmp_len_le { hsc with wsort_len := hws2_len } rfl rfl
      c0_hsteps
      · exact hQ 0xFFFFFFFF#32 s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
      · exact hQ best_lit s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin
          (Or.inr (hbl_ok (by c0_bound))) hm2

theorem s6a_bva_step7_layout_one {c : FullCfg} {s : FullState} : Step7BvaLayout c s 1 :=
  ⟨fun _ hr hr0 => absurd hr0 (by omega), fun _ _ hrr hr' => absurd hrr (by omega)⟩

theorem s6a_bva_step7_layout_of_pre {c : FullCfg} {s s' : FullState} {step bump : Nat}
    (hstep : step ≤ fidStepsCap c.scratch_cap) (h4 : 4 * fidStepsCap c.scratch_cap ≤ bump)
    (hpres : ∀ idx < bump, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : Step7BvaLayout c s step) : Step7BvaLayout c s' step := by
  have e1 : ∀ r < step, s'.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]? := fun r hr => hpres _ (by omega)
  have e2 : ∀ r < step, s'.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]? := fun r hr => hpres _ (by omega)
  have e3 : ∀ r < step, s'.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]? := fun r hr => hpres _ (by omega)
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r hr hr0 => ?_, fun r r' hrr hr' => ?_⟩
  · rw [e1 r hr, e2 r hr, e3 r hr]; exact h1 r hr hr0
  · rw [e1 r (by omega), e2 r (by omega), e3 r (by omega), e1 r' hr', e2 r' hr']
    exact h2 r r' hrr hr'

theorem s6a_bva_step7_layout_extend {c : FullCfg} {F_cur : List (List Nat)} {s st : FullState}
    {sb3 : List (BitVec 32)} {step bump max_new : Nat}
    {best_lit new_qn nrow_off par_off : BitVec 32}
    (hstep1 : 1 ≤ step) (hstep_sc : step < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s step bump) (hlay : Step7BvaLayout c s step)
    (hsb3_len : sb3.length = c.scratch_cap)
    (hnrow_eq : nrow_off.toNat = bump) (hpar_eq : par_off.toNat = bump + max_new)
    (hnq_le : new_qn.toNat ≤ max_new)
    (hmax_le : max_new ≤
      (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD 0#32).toNat)
    (h4 : 4 * fidStepsCap c.scratch_cap ≤ bump)
    (hpres : ∀ idx < bump, sb3[idx]? = s.scratch.scratch_buf[idx]?)
    (hst : st.scratch.scratch_buf =
      (((sb3.set step best_lit).set (fidStepsCap c.scratch_cap + step) nrow_off).set
        (2 * fidStepsCap c.scratch_cap + step) new_qn).set
        (3 * fidStepsCap c.scratch_cap + step) par_off) :
    Step7BvaLayout c st (step + 1) := by
  have h4c := fidStepsCap_mul4_le c.scratch_cap
  obtain ⟨_, _, _, _, _, hrows⟩ := hmat
  obtain ⟨hl1, hl2⟩ := hlay
  have g1 : ∀ r < step, st.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[fidStepsCap c.scratch_cap + r]? := fun r hr => by
    rw [hst, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres _ (by omega)
  have g2 : ∀ r < step, st.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]? := fun r hr => by
    rw [hst, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres _ (by omega)
  have g3 : ∀ r < step, st.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]? =
      s.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + r]? := fun r hr => by
    rw [hst, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres _ (by omega)
  have hro_s : st.scratch.scratch_buf[fidStepsCap c.scratch_cap + step]?.getD 0#32 =
      nrow_off := by
    rw [hst, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  have hqn_s : st.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + step]?.getD 0#32 =
      new_qn := by
    rw [hst, List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
  have hpo_s : st.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + step]?.getD 0#32 =
      par_off := by
    rw [hst, List.getElem?_set_self
      (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  refine ⟨fun r hr hr0 => ?_, fun r r' hrr hr' => ?_⟩
  · by_cases hrs : r < step
    · rw [g1 r hrs, g2 r hrs, g3 r hrs]; exact hl1 r hrs hr0
    · rw [show r = step by omega, hro_s, hqn_s, hpo_s, hnrow_eq, hpar_eq]; omega
  · by_cases hrs' : r' < step
    · rw [g1 r (by omega), g2 r (by omega), g3 r (by omega), g1 r' hrs', g2 r' hrs']
      exact hl2 r r' hrr hrs'
    · have hr_st : r < step := by omega
      rw [show r' = step by omega, g1 r hr_st, g2 r hr_st, g3 r hr_st, hro_s, hqn_s, hnrow_eq]
      obtain ⟨_, _, _, hro2, hpo, _⟩ := hrows r hr_st
      have hq : (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + (step - 1)]?.getD
          0#32).toNat ≤ (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r]?.getD
          0#32).toNat := by
        by_cases hre : r = step - 1
        · exact Nat.le_of_eq (by rw [hre])
        · exact (hl2 r (step - 1) (by omega) (by omega)).1
      exact ⟨by omega, hro2, fun hr0 => (hpo hr0).2⟩

theorem s6a_bva_step7_exit_phase_wp (Γ : Env)
    (hCommit : ∀ a m Q X, step7BvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl : FullState} {R : Mem 64 → Prop}
    {f0 bump step cur_qn best_k : BitVec 32} {init_cv0 best_red : BitVec 64}
    {ml : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlm : FullLitMarksClear c s)
    (hlay : Step7BvaLayout c stl step.toNat)
    (hexit : StepExitBody c F0 F_cur s R (fidStepsCap c.scratch_cap)
      step best_k bump.toNat stl ml)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → ∃ bk, Step7BvaCommittedOk c s' bk) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Blocks.get
        (step7TryLitExitBlock Val Cont c.pScratchBuf c.pLitMark
          (c.hdr, f0, init_cv0, ()) ((fun _ _ => False), ()))
        .here (bump, step, cur_qn, best_k, best_red, ()))
      ml := by
  let sc_n := fidStepsCap c.scratch_cap
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  have hsc_le : sc_n ≤ 256 := fidStepsCap_le_256 c.scratch_cap
  obtain ⟨hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
          hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
          hmatl, hbkl, hlml_hi, hlml_set, hlml_only⟩ := hexit
  dsimp only [step7TryLitExitBlock, Blocks.get]
  refine wp_loop_inv (ts := [i32])
    (fun (ci, ()) mc => ∃ lmi : List (BitVec 8),
      let stc : FullState :=
        { stl with core := { stl.core with lit_mark := lmi } }
      (FullMem c stc ⋆ R) mc ∧ lmi.length = 2 * c.max_vars ∧
      ci.toNat ≤ step.toNat ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
        ∃ r, ci.toNat ≤ r ∧ r < step.toNat ∧
          (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
    (fun (ci, _) _ => step.toNat - ci.toNat)
    (fun Jci hJci => hJci (0#32, ()) ml
      ⟨stl.core.lit_mark, hml, hlenl.core_ok.lit_mark_len, Nat.zero_le _,
       hlml_hi, fun l hl hne => by
         obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
         exact ⟨r, Nat.zero_le _, hr, heq⟩⟩)
    (fun Jci (ci, ()) mc ⟨lmi, hmc, hlmi_l, hci_le, hlmi_hi, hlmi_only⟩ ihci => ?_)
  c0_hsplit
  · have hci_lt : ci.toNat < step.toNat := by assumption
    have hci_sb : (BitVec.setWidth 64 ci).toNat < stl.scratch.scratch_buf.length := by
      rw [bv64_setWidth_32, hlenl.scratch_ok.scratch_buf_len]; omega
    have hci_sb' : ci.toNat < stl.scratch.scratch_buf.length := by
      simpa only [bv64_setWidth_32] using hci_sb
    have hci_lm : (BitVec.setWidth 64
        (stl.scratch.scratch_buf[(BitVec.setWidth 64 ci).toNat]'hci_sb)).toNat <
        lmi.length := by
      have hr_lt := (hmatl.2.2.2.2.2 ci.toNat hci_lt).1
      rw [List.getElem?_eq_getElem hci_sb', Option.getD_some] at hr_lt
      rw [bv64_setWidth_32, hlmi_l]
      exact Nat.lt_of_lt_of_le hr_lt (Nat.mul_le_mul_left 2 (by rw [hcvl]; exact hcv_le))
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := fid_bv32_add1_n (by omega)
    c0_hsteps_nogrp
    exact ihci (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
      ⟨lmi.set (stl.scratch.scratch_buf[ci.toNat]'(by
          simpa only [bv64_setWidth_32] using hci_sb)).toNat 0#8,
       by simpa only [bv64_setWidth_32] using hm,
       by rw [List.length_set, hlmi_l], by rw [hci1]; exact hci_lt,
       fun l hl => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
             simpa only [bv64_setWidth_32] using hci_sb)).toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
         · rw [List.getElem?_set_ne (Ne.symm he)]; exact hlmi_hi l hl,
       fun l hl hne => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
             simpa only [bv64_setWidth_32] using hci_sb)).toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
           exact absurd rfl hne
         · rw [List.getElem?_set_ne (Ne.symm he)] at hne
           obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
           have hner : r ≠ ci.toNat := fun h => by
             subst h; rw [List.getElem?_eq_getElem (by
               simpa only [bv64_setWidth_32] using hci_sb), Option.getD_some] at heq
             exact he heq.symm
           exact ⟨r, by rw [hci1]; omega, hr2, heq⟩⟩
  · have hlm_clr_done :
        FullLitMarksClear c { stl with core := { stl.core with lit_mark := lmi } } := by
      refine fid_bva_try_lit_clear_lm_done (stepf := step.toNat)
        (fun v hv => by have := hlm.1 v hv; rwa [hmrkl]) hlmi_hi (fun l hl hne => ?_)
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hci_eq : ci.toNat = step.toNat := by
        have h1 : ¬ ci.toNat < step.toNat := by assumption
        omega
      rw [hci_eq] at hr1; exact ⟨r, hr1, hr2, heq⟩
    let stc : FullState := { stl with core := { stl.core with lit_mark := lmi } }
    have hinv_clr : FullDenseInvW c F0 F_cur stc :=
      ⟨⟨{ hlenl.core_ok with lit_mark_len := hlmi_l }, hlenl.scratch_ok⟩,
       { hwl with
         arena := { hwl.arena with len_ok := hwl.arena.len_ok }
         watches := hwl.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
       hlm_clr_done, hndl, hextl, hlv0l, hdml⟩
    have hmat_c : FidBvaMatrixInv c F_cur stc step.toNat bump.toNat :=
      fidBvaMatrixInv_congr (s := stl) (s' := stc) rfl rfl rfl rfl hmatl
    c0_hsplit
    · exact hQ false stc mc hinv_clr.toDense (hcvl ▸ Nat.le_refl _)
        (fun h => by contradiction) (fun h => by contradiction)
        (by dsimp only [stc]; exact hfuell)
        (by dsimp only [stc]; exact html) (by dsimp only [stc]; exact htrl) hmc
    · have hbk1 : 1 ≤ best_k.toNat := by
        rcases hbkl with rfl | ⟨h1, _⟩
        · exact absurd rfl (by assumption)
        · exact h1
      have hbk_lt_sc : best_k.toNat < sc_n := by
        rcases hbkl with rfl | ⟨_, h2⟩
        · exact absurd rfl (by assumption)
        · exact Nat.lt_of_lt_of_le h2 hst_sc
      have hbk_lt_st : best_k.toNat < step.toNat := by
        rcases hbkl with rfl | ⟨_, h2⟩
        · exact absurd rfl (by assumption)
        · exact h2
      c0_hsteps_nogrp
      let st_tc : FullState :=
        { stc with scratch := { stc.scratch with res_sz := BitVec.setWidth 64 best_k } }
      have hinv_tc : FullDenseInvW c F0 F_cur st_tc :=
        fullDenseInv_with_core_aux (tc' := stc.core.tmp_cnt) (tl' := stc.core.tmp_len)
          (sc' := st_tc.scratch) hinv_clr hinv_clr.1.core_ok.repr_len
          hinv_clr.1.core_ok.min_clr_len_arr hinv_clr.1.core_ok.tmp_len_arr
          hinv_clr.1.core_ok.flags_len hinv_clr.1.core_ok.tmp_len_le
          { hinv_clr.1.scratch_ok with } rfl rfl
      have hmat_tc : Step7BvaMatrixInv c F_cur st_tc (best_k.toNat + 1) bump.toNat :=
        ⟨fidBvaMatrixInv_congr (s := stc) rfl rfl rfl rfl
          (fid_bva_matrixInv_substep (k := best_k.toNat + 1) (by omega) (by omega) hmat_c),
         Step7BvaLayout.congr (s := stl) rfl (Step7BvaLayout.mono (by omega) hlay)⟩
      have hres_tc : st_tc.scratch.res_sz = BitVec.ofNat 64 best_k.toNat :=
        (BitVec.ofNat_toNat 64 best_k).symm
      refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, st_tc, R, bump.toNat, rfl, hinv_tc, hbk1, hbk_lt_sc, hmat_tc,
        hres_tc, hm, fun ok s' m' hinv' hcv' hcv_inc hok' hfuel' htm' htr' hm' => ?_⟩
      exact hQ ok s' m' hinv' (by rw [← hcvl]; exact hcv')
        (fun h => by rw [← hcvl]; exact hcv_inc h) (fun h => ⟨best_k.toNat, hok' h⟩)
        (hfuel'.trans hfuell) (htm'.trans html) (htr'.trans htrl) hm'

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
