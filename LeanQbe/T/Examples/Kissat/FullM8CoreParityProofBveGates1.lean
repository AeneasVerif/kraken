/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity BVE Gate Finders — Part 1 (`match_tern`, `ite`, `xor`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m8_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-- Parametric `Func.wp` proof for `full_bve_match_tern_m8`. -/
theorem full_bve_match_tern_m8_wp (Γ : Env) :
    ∀ a m Q X, m8BveMatchTernSpec a m Q X →
      Func.wp Γ full_bve_match_tern_m8_body a m Q X := by
  rintro ⟨h, opp_lit, x, y, opp_off, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hooff, hon2, hent_n, hm0, hQ⟩ :=
    m8BveMatchTernSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  unfold Func.wp full_bve_match_tern_m8_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (j, ()) mj => ∃ scr_j : List (BitVec 32),
      let sj : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_j } }
      scr_j.length = c.scratch_cap ∧ j.toNat ≤ opp_n.toNat ∧ rem = opp_n.toNat - j.toNat ∧
      (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
        scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
      (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · rintro L rem ⟨j, ⟨⟩⟩ mj hL ⟨scr_j, hscj, hj_le, rfl, hout_j, hmj⟩
    have h4132 : 4132 < scr_j.length := by rw [hscj]; omega
    c0_hsplit
    · have hj_lt : j.toNat < opp_n.toNat := hc
      c0_hsplit
      · have hoj_sc : ((opp_off + j).setWidth 64).toNat < scr_j.length := by
          rw [hscj, m6_zext32_toNat]; c0_bound
        have hwj_orig :
            scr_j[((opp_off + j).setWidth 64).toNat]'hoj_sc =
              s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
            rw [m6_zext32_toNat]; c0_bound
          have hget := hout_j (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
          have hoj' : opp_off.toNat + j.toNat < scr_j.length := by omega
          rw [List.getElem?_eq_getElem hoj'] at hget
          rw [← hget, Option.getD_some]
          exact m6_getElem_congr hoj_eq hoj_sc hoj'
        let scr_s := scr_j.set 4132 (scr_j[4132]'h4132 + 1#32)
        have hsc_s : scr_s.length = c.scratch_cap := by simp [scr_s, hscj]
        have hout_s : ∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
            scr_s[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor => by
          dsimp only [scr_s]; rw [List.getElem?_set_ne (by omega)]; exact hout_j i hi hor
        have hoj_sc_s : ((opp_off + j).setWidth 64).toNat < scr_s.length := by
          rw [hsc_s, m6_zext32_toNat]; c0_bound
        have hwj_s : scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s =
            s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          rw [← hwj_orig]; dsimp only [scr_s]; rw [List.getElem_set_ne (by c0_bound)]
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ mj' => (FullMem c { s0 with scratch := { s0.scratch with scratch_buf :=
            scr_s } } ⋆ R) mj')
          ?_ ?_
        · rintro _ _ mj' hmj'
          c0_hsteps!
          exact hL (opp_n.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj' (by omega)
            ⟨scr_s, hsc_s, by omega, rfl, hout_s, hmj'⟩
        · intro _ hJj
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun _ mb' => (FullMem c { s0 with scratch := { s0.scratch with scratch_buf :=
                scr_s } } ⋆ R) mb')
              ?_ ?_
            · rintro _ _ mb' hmb'
              c0_hsteps!; exact hQ (j ||| 0x80000000#32) scr_s mb' hsc_s hout_s
                (Or.inr (by rw [m8_u32_and7fff_or8000 j (by omega)]; exact hj_lt)) hmb'
            · intro _ hJret
              c0_hsplit
              · c0_hsteps!; exact hJret () _ hm
              · c0_hsplit
                · c0_hsteps!; exact hJret () _ hm
                · c0_hsteps!; exact hJj () _ hm
          ·
              let w := scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s
              have hent_j := hent_n j.toNat hj_lt
              rw [← hwj_s] at hent_j; unfold FullBveEntryOkW at hent_j
              rw [ite_eq_right (fun h => h hc)] at hent_j
              have href_j : w.toNat ∈ fullArenaClauseRefs s0 := hent_j.1
              have hng_j : fullArenaClauseGarb s0 w.toNat = false := hent_j.2
              have hwf := hdw0.2.1.arena.refs_wf w.toNat href_j
              have hw_bd : w.toNat + 3 + fullArenaClauseSizeCore s0.core w.toNat ≤
                  c.arena_cap := by
                have := hwf.2.2.1; have := hwf.2.2.2.1; omega
              have hsz_ge : 3 ≤ fullArenaClauseSizeCore s0.core w.toNat := hwf.2.1
              have hw2_ar : (w.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, m6_zext32_toNat,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                omega
              let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_ar
              have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := by
                unfold sz fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by
                  rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)]) _ _)
              c0_hsteps_nogrp
              refine wp_loop_break_group (brkTs := [.bool, .bool, .bool, i32])
                (lpTs := [.bool, .bool, i32])
                (fun (ok_b, sx_b, sy_b, _, ()) mb =>
                  (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_s } } ⋆
                    R) mb)
                (fun rem_k (sx_k, sy_k, k, ()) mk =>
                  (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_s } } ⋆
                    R) mk ∧
                  k.toNat ≤ sz.toNat ∧ rem_k = sz.toNat - k.toNat)
                ?_ ?_ ?_
              · rintro _ ⟨ok_b, sx_b, sy_b, _, ⟨⟩⟩ mb hmb
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun _ mb' => (FullMem c { s0 with scratch := { s0.scratch with scratch_buf :=
                    scr_s } } ⋆ R) mb')
                  ?_ ?_
                · rintro _ _ mb' hmb'; c0_hsteps!; exact hJj () mb' hmb'
                · intro _ hJskip
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun _ ms' => (FullMem c { s0 with scratch :=
                        { s0.scratch with scratch_buf := scr_s } } ⋆ R) ms')
                      ?_ ?_
                    · rintro _ _ ms' hms'
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun _ mo' => (FullMem c { s0 with scratch :=
                          { s0.scratch with scratch_buf := scr_s } } ⋆ R) mo')
                        ?_ ?_
                      · rintro _ _ mo' hmo'
                        c0_hsteps!
                        exact hQ (j ||| 0x80000000#32) scr_s mo' hsc_s hout_s
                          (Or.inr (by
                            rw [m8_u32_and7fff_or8000 j (by omega)]; exact hj_lt)) hmo'
                      · intro _ hJor
                        c0_hsplit
                        · c0_hsteps!; exact hJor () ms' hms'
                        · c0_hsplit
                          · c0_hsteps!; exact hJor () ms' hms'
                          · c0_hsteps!; exact hJskip () ms' hms'
                    · intro _ hJand
                      c0_hsplit
                      · c0_hsplit
                        · have hj31 : (j &&& 0x7FFFFFFF#32).toNat = j.toNat := by
                            rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat =
                              2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
                              Nat.mod_eq_of_lt (by omega)]
                          c0_hsteps!
                          exact hQ j scr_s mb hsc_s hout_s
                            (Or.inr (by rw [hj31]; exact hj_lt)) hmb
                        · c0_hsteps!; exact hJand () mb hmb
                      · c0_hsteps!; exact hJand () mb hmb
                  · c0_hsteps!; exact hJskip () mb hmb
              · rintro Bk Lk rem_k ⟨sx_k, sy_k, k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                c0_hsplit
                · have hk_lt : k.toNat < sz.toNat := hc
                  have hwk_eq : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                      w.toNat + 3 + k.toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                      m6_zext32_toNat, BitVec.toNat_ofNat]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  have hwk : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                      s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                  let l := s0.core.arena[(w.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                  have hl_mem : l.toNat ∈ fullArenaClauseLitsCore s0.core w.toNat := by
                    rw [mem_fullArenaClauseLitsCore_iff (by
                      rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                    exact ⟨k.toNat, by omega,
                      congrArg BitVec.toNat (m6_getElem_congr hwk_eq.symm _ _)⟩
                  have hl_lt : l.toNat < 2 * s0.core.cur_vars :=
                    hdw0.2.1.arena.lits_lt w.toNat href_j hng_j _ hl_mem
                  have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                  c0_hsteps_nogrp
                  c0_hsplit
                  · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) mk hmk
                  · c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [.bool, .bool, .bool]) (α :=
                      Bool × Bool × Bool)
                      (fun p => (p.1, p.2.1, p.2.2, ())) (fun _ => True)
                      ?_ ?_
                    · rintro _ ⟨_, sx', sy'⟩ _
                      c0_hsteps!
                      exact hLk (sz.toNat - (k + 1#32).toNat) (sx', sy', k + 1#32, ()) mk
                        (by omega) ⟨hmk, by omega, rfl⟩
                    · intro Jk hJk
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [.bool, .bool, .bool]) (α :=
                            Bool × Bool × Bool)
                            (fun p => (p.1, p.2.1, p.2.2, ())) (fun _ => True)
                            ?_ ?_
                          · rintro _ p _; c0_hsteps!; exact hJk p trivial
                          · intro _ hJk2
                            c0_hsplit
                            · c0_hsteps!; exact hJk2 (true, true, sy_k) trivial
                            · c0_hsplit
                              · c0_hsteps!; exact hJk2 (true, sx_k, true) trivial
                              · c0_hsteps!; exact hBk (false, sx_k, sy_k, k, ()) mk hmk
                        · c0_hsteps!; exact hJk (true, sx_k, sy_k) trivial
                      · c0_hsteps!; exact hJk (true, sx_k, sy_k) trivial
                · c0_hsteps!; exact hBk (true, sx_k, sy_k, k, ()) mk hmk
              · intro _ Lk _ hLk; c0_hsteps!
                exact hLk sz.toNat (false, false, 0#32, ()) _ ⟨hm, Nat.zero_le _, by simp⟩
      · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
  · intro L hL; c0_hsteps!
    exact hL opp_n.toNat (0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
       fun _ _ _ => rfl, hm0⟩

private def m8FullMemNoLmScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem m8_fullMem_eq_lm_scr (c : FullCfg) (s : FullState)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) :
    FullMem c { s with
      core := { s.core with lit_mark := lm }
      scratch := { s.scratch with scratch_buf := scr } } =
      (array (t := i8) c.pLitMark lm ⋆ array (t := i32) c.pScratchBuf scr ⋆
        m8FullMemNoLmScr c s) := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullScratchArrays FullScrDynArrs m8FullMemNoLmScr
  ac_rfl

private theorem m8_fullMem_lm_scr_iff (c : FullCfg) (s : FullState)
    (lm : List (BitVec 8)) (scr : List (BitVec 32)) (R : Mem 64 → Prop) :
    (FullMem c { s with
      core := { s.core with lit_mark := lm }
      scratch := { s.scratch with scratch_buf := scr } } ⋆ R) =
      (array (t := i8) c.pLitMark lm ⋆ array (t := i32) c.pScratchBuf scr ⋆
        (m8FullMemNoLmScr c s ⋆ R)) := by
  rw [m8_fullMem_eq_lm_scr]; ac_rfl

private theorem m8_fullMem_scr_iff (c : FullCfg) (s : FullState)
    (scr : List (BitVec 32)) (R : Mem 64 → Prop) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) =
      (array (t := i32) c.pScratchBuf scr ⋆
        (array (t := i8) c.pLitMark s.core.lit_mark ⋆ m8FullMemNoLmScr c s ⋆ R)) := by
  have h := m8_fullMem_lm_scr_iff c s s.core.lit_mark scr R
  dsimp only at h; rw [h]; ac_rfl

private theorem m8_sep_scr_lm_norm {pL pS : BitVec 64} {lm : List (BitVec 8)}
    {scr : List (BitVec 32)} {R' : Mem 64 → Prop} {m : Mem 64}
    (h : (array (t := i32) pS scr ⋆ (array (t := i8) pL lm ⋆ (R' ⋆ emp))) m) :
    (array (t := i8) pL lm ⋆ array (t := i32) pS scr ⋆ R') m := by
  rw [sep_emp, ← sep_assoc, sep_comm (array (t := i32) pS scr)] at h; exact h

private def m8SetMaskBitVarExpr (pScr : BitVec 64) (base idx : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var idx, Arg.imm 5, ())⟩ fun p0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var base, Arg.var p0.fst, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p2.fst, Arg.imm 4, ())⟩ fun p3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p3.fst, ())⟩ fun p4 =>
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var idx, Arg.imm 5, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var base, Arg.var q0.fst, ())⟩ fun q1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var q1.fst, ())⟩ fun q2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q2.fst, Arg.imm 4, ())⟩ fun q3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q3.fst, ())⟩ fun q4 =>
  Expr.load i32 (Arg.var q4.fst) fun ld =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var idx, Arg.imm 31, ())⟩ fun s0 =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var s0.fst, ())⟩ fun s1 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var ld, Arg.var s1.fst, ())⟩ fun s2 =>
  Expr.store (Arg.var s2.fst) (Arg.var p4.fst) k

private theorem m8_setMaskBit_var_wp (Γ : Env) (c : FullCfg)
    (scr : List (BitVec 32)) (R_scr : Mem 64 → Prop) (base idx : BitVec 32)
    (m : Mem 64) (Q : Post [.bool]) (X : XPost) (k : Expr Val Cont [.bool])
    (hsc : scr.length = c.scratch_cap) (hsc16 : 16384 ≤ c.scratch_cap)
    (hbase : base = 4002#32 ∨ base = 4066#32) (hidx_lt : idx.toNat < 2001)
    (hm : (array (t := i32) c.pScratchBuf scr ⋆ R_scr) m)
    (hk : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) → scr'[i]? = scr[i]?) →
      (array (t := i32) c.pScratchBuf scr' ⋆ R_scr) m' →
      wp Γ Q X k m') :
    wp Γ Q X (m8SetMaskBitVarExpr c.pScratchBuf base idx k) m := by
  have hm_idx := m8_mask_idx_lo base idx hbase hidx_lt
  have hoff_lt : ((base + (idx >>> (5 : Nat))).setWidth 64).toNat < scr.length := by
    rw [hsc, m6_zext32_toNat]; omega
  unfold m8SetMaskBitVarExpr
  c0_hsteps_nogrp
  refine hk _ m (by rw [List.length_set, hsc]) (fun i _ hor => ?_) hm
  rw [List.getElem?_set_ne]
  rw [m6_zext32_toNat]
  change (base + (idx >>> (5 : Nat))).toNat ≠ i
  rcases hbase with rfl | rfl <;> simp only [BitVec.toNat_ofNat] at hm_idx ⊢ <;> omega

private def m8FinishIteExpr (pScr : BitVec 64) (r0 r1 : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm (t := i32) 4130, ())⟩ fun p0 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p0.fst, Arg.imm 4, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.store (Arg.imm (t := i32) 1) (Arg.var p2.fst) (
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm (t := i32) 4131, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q0.fst, Arg.imm 4, ())⟩ fun q1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q1.fst, ())⟩ fun q2 =>
  Expr.group (sig := [[i32]])
    (fun _lbls =>
      Blocks.cons (fun arg =>
        Expr.store (Arg.var arg.fst) (Arg.var q2.fst)
          (Expr.ret (Arg.imm (t := .bool) true, ())))
        Blocks.nil)
    (fun lbls =>
      Expr.let_ ⟨OpCode.or i32, (Arg.var r0, Arg.var r1, ())⟩ fun t0 =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var t0.fst, Arg.imm 0x80000000#32, ())⟩ fun t1 =>
      Expr.let_ ⟨OpCode.ne i32, (Arg.var t1.fst, Arg.imm 0, ())⟩ fun t2 =>
      Expr.jnz (Arg.var t2.fst) (Expr.jump lbls.1 (Arg.imm 1, ()))
        (Expr.jump lbls.1 (Arg.imm 0, ()))))

private def m8IteHitExpr (pScr : BitVec 64) (litMask oppMask i0 i1 r0 r1 : BitVec 32) :
    Expr Val Cont [.bool] :=
  m8SetMaskBitVarExpr pScr litMask i0
    (m8SetMaskBitVarExpr pScr litMask i1
      (m8SetMaskBitVarExpr pScr oppMask (r0 &&& 0x7FFFFFFF#32)
        (m8SetMaskBitVarExpr pScr oppMask (r1 &&& 0x7FFFFFFF#32)
          (m8FinishIteExpr pScr r0 r1))))

private theorem m8_ite_hit_wp (Γ : Env) (c : FullCfg) (s0 : FullState)
    (scr0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (litMask oppMask i0 i1 r0 r1 : BitVec 32) (m0 : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hsc0 : scr0.length = c.scratch_cap) (hsc16 : 16384 ≤ c.scratch_cap)
    (hout0 : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
      scr0[i]? = s0.scratch.scratch_buf[i]?)
    (hlm_k : litMask = 4002#32 ∨ litMask = 4066#32)
    (hom_k : oppMask = 4002#32 ∨ oppMask = 4066#32)
    (hi0_lt : i0.toNat < 2001) (hi1_lt : i1.toNat < 2001)
    (hr0_lt : (r0 &&& 0x7FFFFFFF#32).toNat < 2001)
    (hr1_lt : (r1 &&& 0x7FFFFFFF#32).toNat < 2001)
    (hm0 : (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } ⋆ R) m0)
    (hQ : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m') :
    wp Γ Q X (m8IteHitExpr c.pScratchBuf litMask oppMask i0 i1 r0 r1) m0 := by
  let R_scr := array (t := i8) c.pLitMark s0.core.lit_mark ⋆ m8FullMemNoLmScr c s0 ⋆ R
  have hm0' : (array (t := i32) c.pScratchBuf scr0 ⋆ R_scr) m0 := by
    rw [m8_fullMem_scr_iff] at hm0; exact hm0
  unfold m8IteHitExpr
  refine m8_setMaskBit_var_wp Γ c scr0 R_scr litMask i0 m0 Q X _
    hsc0 hsc16 hlm_k hi0_lt hm0' ?_
  intro scr1 m1 hsc1 hout1 hm1
  have hout1' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
      scr1[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout1 i hi hor).trans (hout0 i hi hor)
  refine m8_setMaskBit_var_wp Γ c scr1 R_scr litMask i1 m1 Q X _
    hsc1 hsc16 hlm_k hi1_lt hm1 ?_
  intro scr2 m2 hsc2 hout2 hm2
  have hout2' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
      scr2[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout2 i hi hor).trans (hout1' i hi hor)
  refine m8_setMaskBit_var_wp Γ c scr2 R_scr oppMask (r0 &&& 0x7FFFFFFF#32) m2 Q X _
    hsc2 hsc16 hom_k hr0_lt hm2 ?_
  intro scr3 m3 hsc3 hout3 hm3
  have hout3' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
      scr3[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout3 i hi hor).trans (hout2' i hi hor)
  refine m8_setMaskBit_var_wp Γ c scr3 R_scr oppMask (r1 &&& 0x7FFFFFFF#32) m3 Q X _
    hsc3 hsc16 hom_k hr1_lt hm3 ?_
  intro scr4 m4 hsc4 hout4 hm4
  have hout4' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
      scr4[i]? = s0.scratch.scratch_buf[i]? :=
    fun i hi hor => (hout4 i hi hor).trans (hout3' i hi hor)
  unfold m8FinishIteExpr
  have h4130 : (4130#64).toNat < scr4.length := by
    rw [hsc4, show (4130#64).toNat = 4130 from rfl]; omega
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
    (fun x => (x, ())) (fun _ => True) ?_
    (fun _ hJtag => by c0_hsplit <;> (c0_hsteps!; exact hJtag _ trivial))
  intro _ tag _
  have h4131 : (4131#64).toNat < (scr4.set (4130#64).toNat 1#32).length := by
    rw [List.length_set, hsc4, show (4131#64).toNat = 4131 from rfl]; omega
  c0_hsteps!
  refine hQ true ((scr4.set (4130#64).toNat 1#32).set (4131#64).toNat tag) m
    (by simp [hsc4]) (fun idx hidx hor => by
      rw [List.getElem?_set_ne (by rw [show (4131#64).toNat = 4131 from rfl]; omega),
        List.getElem?_set_ne (by rw [show (4130#64).toNat = 4130 from rfl]; omega)]
      exact hout4' idx hidx hor) ?_
  rw [m8_fullMem_scr_iff]; exact hm

/-- Parametric `Func.wp` proof for `full_bve_find_ite_side_m8`. -/
theorem full_bve_find_ite_side_m8_wp (Γ : Env)
    (hGet : ∀ a m Q X, fullBveGetTernM7Spec a m Q X →
      Γ "full_bve_get_tern_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hMatch : ∀ a m Q X, m8BveMatchTernSpec a m Q X →
      Γ "full_bve_match_tern_m8" [i64, i32, i32, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, m8BveFindIteSideSpec a m Q X →
      Func.wp Γ full_bve_find_ite_side_m8_body a m Q X := by
  rintro ⟨h, v, np, nn, neg, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hv, hnp, hnn, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindIteSideSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  obtain ⟨hpl_val, hnl_val⟩ := m8_pl_nl_eq (v := v) (by omega)
  let lit_w := if neg then (v <<< (1 : Nat)) ||| 1#32 else v <<< (1 : Nat)
  let opp_w := lit_w ^^^ 1#32
  have hlit_val : lit_w.toNat = if neg then 2 * v.toNat + 1 else 2 * v.toNat := by
    dsimp only [lit_w]; split <;> first | exact hnl_val | exact hpl_val
  have hopp_val : opp_w.toNat = if neg then 2 * v.toNat else 2 * v.toNat + 1 := by
    dsimp only [opp_w, lit_w]; cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have : ((v <<< (1 : Nat)) ^^^ 1#32) = ((v <<< (1 : Nat)) ||| 1#32) := by
        ext i hi; simp only [BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_one]
        cases i with
        | zero => simp [BitVec.getElem_shiftLeft]
        | succ k => simp [Bool.bne_false]
      rw [this, hnl_val]
    · have : (((v <<< (1 : Nat)) ||| 1#32) ^^^ 1#32) = (v <<< (1 : Nat)) := by
        ext i hi; simp only [BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_one]
        cases i with
        | zero => simp [BitVec.getElem_shiftLeft]
        | succ k => simp [Bool.bne_false]
      rw [this, hpl_val]
  unfold Func.wp full_bve_find_ite_side_m8_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun neg_bit => neg_bit = if neg then 1#32 else 0#32) ?_ ?_
  · rintro _ neg_bit hnb
    have hlit_eq : ((v <<< (1#32 : BitVec 32)) ||| neg_bit) = lit_w := by
      rw [hnb]; cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, lit_w]
      · exact BitVec.or_zero
      · rfl
    have hlit_eq_n : ((v <<< (1 : Nat)) ||| neg_bit) = lit_w := hlit_eq
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun lit_off => lit_off.toNat = if neg then 2001 else 0) ?_ ?_
    · rintro _ lit_off hlo
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun lit_n => lit_n = if neg then nn else np) ?_ ?_
      · rintro _ lit_n hln
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
          (fun opp_off => opp_off.toNat = if neg then 0 else 2001) ?_ ?_
        · rintro _ opp_off hoo
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
            (fun opp_n => opp_n = if neg then np else nn) ?_ ?_
          · rintro _ opp_n hon
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
              (fun lit_mask => lit_mask = 4002#32 ∨ lit_mask = 4066#32) ?_ ?_
            · rintro _ lit_mask hlm_k
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                (fun opp_mask => opp_mask = 4002#32 ∨ opp_mask = 4066#32) ?_ ?_
              · rintro _ opp_mask hom_k
                have hln_2k : lit_n.toNat ≤ 2001 := by rw [hln]; cases neg <;> simp [hnp, hnn]
                have hon_2k : opp_n.toNat ≤ 2001 := by rw [hon]; cases neg <;> simp [hnp, hnn]
                have hlo_bnd : lit_off.toNat + lit_n.toNat ≤ 4002 := by
                  rw [hlo, hln]; cases neg <;> simp <;> omega
                have hoo_bnd : opp_off.toNat + opp_n.toNat ≤ 4002 := by
                  rw [hoo, hon]; cases neg <;> simp <;> omega
                have hlit_ent : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s0 lit_w.toNat
                    (s0.scratch.scratch_buf[lit_off.toNat + i]?.getD 0#32) := by
                  intro i hi; rw [hlit_val]
                  cases neg <;> simp_all [Nat.zero_add]
                have hopp_ent : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s0 opp_w.toNat
                    (s0.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32) := by
                  intro j hj; rw [hopp_val]
                  cases hneg : neg with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have ho1 : opp_off.toNat = 2001 := by rw [hoo, hneg]; decide
                    have ho2 : opp_n = nn := by rw [hon, hneg]; rfl
                    rw [ho1]; rw [ho2] at hj; exact hn_ok j hj
                  | true =>
                    simp only [↓reduceIte]
                    have ho1 : opp_off.toNat = 0 := by rw [hoo, hneg]; decide
                    have ho2 : opp_n = np := by rw [hon, hneg]; rfl
                    rw [ho1, Nat.zero_add]; rw [ho2] at hj; exact hp_ok j hj
                c0_hsplit
                · c0_hsteps!; exact hQ false s0.scratch.scratch_buf m0
                    hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0
                · c0_hsplit
                  · c0_hsteps!; exact hQ false s0.scratch.scratch_buf m0
                      hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0
                  · c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64, i32])
                      (fun rem1 (lc, idx, ()) m1 => m1 = m0 ∧ idx.toNat ≤ lit_n.toNat ∧
                        lc.toNat ≤ idx.toNat ∧ rem1 = lit_n.toNat - idx.toNat)
                      ?_ ?_
                    · rintro L1 rem1 ⟨lc, idx, ⟨⟩⟩ m1 hL1 ⟨hm1, hidx_le, hlc_le, rfl⟩
                      subst m1
                      c0_hsplit
                      · have hidx_lt : idx.toNat < lit_n.toNat := hc
                        have hidx_sc : ((lit_off + idx).setWidth 64).toNat <
                            s0.scratch.scratch_buf.length := by
                          rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
                        have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun x => (x, ())) (fun lc' => lc'.toNat ≤ idx.toNat + 1) ?_ ?_
                        · rintro _ lc' hlc'
                          c0_hsteps!
                          exact hL1 (lit_n.toNat - (idx + 1#32).toNat) (lc', idx + 1#32, ())
                            m0 (by omega) ⟨rfl, by omega, by rw [hidx1]; exact hlc', rfl⟩
                        · intro J1 hJ1
                          c0_hsplit
                          · c0_hsteps!; exact hJ1 (lc + 1#64) (by c0_bound)
                          · c0_hsteps!; exact hJ1 lc (by omega)
                      · have h4132_0 : 4132 < s0.scratch.scratch_buf.length := by
                          rw [hdw0.1.scratch_ok.scratch_buf_len]; omega
                        c0_hsplit
                        · c0_hsteps!; exact hQ false s0.scratch.scratch_buf m0
                            hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0
                        · c0_hsplit
                          · c0_hsteps!; exact hQ false s0.scratch.scratch_buf m0
                              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0
                          · c0_hsteps!
                            let scr_i0 := s0.scratch.scratch_buf.set 4132 0#32
                            have hsc_i0 : scr_i0.length = c.scratch_cap := by
                              simp [scr_i0, hdw0.1.scratch_ok.scratch_buf_len]
                            have hout_i0 : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                scr_i0[i]? = s0.scratch.scratch_buf[i]? := fun i _ hor => by
                              dsimp only [scr_i0]; exact List.getElem?_set_ne (by omega)
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i32])
                              (fun rem2 (i0, ()) m2 => ∃ scr2 : List (BitVec 32),
                                let s2 : FullState := { s0 with scratch :=
                                  { s0.scratch with scratch_buf := scr2 } }
                                scr2.length = c.scratch_cap ∧ i0.toNat ≤ lit_n.toNat ∧
                                rem2 = lit_n.toNat - i0.toNat ∧
                                (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                  scr2[i]? = s0.scratch.scratch_buf[i]?) ∧
                                (FullMem c s2 ⋆ R) m2)
                              ?_ ?_
                            · rintro L2 rem2 ⟨i0, ⟨⟩⟩ m2 hL2 ⟨scr2, hsc2, hi0_le, rfl, hout2, hm2⟩
                              have h4132_2 := m8_scr_imm_lt hsc2 hsc16 (k := 4132) (by decide)
                              c0_hsplit
                              · have hi0_lt1 : i0.toNat + 1 < lit_n.toNat := by
                                  have h1 : (i0 + 1#32).toNat < lit_n.toNat := hc
                                  have h2 : (i0 + 1#32).toNat = i0.toNat + 1 := by c0_bound
                                  omega
                                clear hc
                                c0_hsplit
                                · clear hc
                                  have hi0_sc : ((lit_off + i0).setWidth 64).toNat < scr2.length :=
                                    by
                                    rw [hsc2, m6_zext32_toNat]; c0_bound
                                  have hi0_eq : ((lit_off + i0).setWidth 64).toNat =
                                      lit_off.toNat + i0.toNat := by
                                    rw [m6_zext32_toNat]; c0_bound
                                  let w0 := scr2[((lit_off + i0).setWidth 64).toNat]'hi0_sc
                                  have hw0_orig : w0 =
                                      s0.scratch.scratch_buf[lit_off.toNat +
                                        i0.toNat]?.getD 0#32 := by
                                    have hget := hout2 (lit_off.toNat +
                                      i0.toNat) (by omega) (Or.inl (by omega))
                                    have hi0' : lit_off.toNat + i0.toNat < scr2.length := by omega
                                    rw [List.getElem?_eq_getElem hi0'] at hget
                                    rw [← hget, Option.getD_some]
                                    exact (m6_getElem_congr hi0_eq.symm hi0' hi0_sc).symm
                                  have hi0_1 : (i0 + 1#32).toNat = i0.toNat + 1 := by c0_bound
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [])
                                    (fun _ m2' => ∃ scr2' : List (BitVec 32),
                                      scr2'.length = c.scratch_cap ∧
                                      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                        scr2'[i]? = s0.scratch.scratch_buf[i]?) ∧
                                      (FullMem c { s0 with scratch :=
                                        { s0.scratch with scratch_buf := scr2' } } ⋆ R) m2')
                                    (fun _ _ m2' ⟨scr2', hsc2', hout2', hm2'⟩ => by
                                      c0_hsteps!
                                      exact hL2 (lit_n.toNat - (i0 + 1#32).toNat) (i0 + 1#32,
                                        ()) m2'
                                        (by omega) ⟨scr2', hsc2', by omega, rfl, hout2', hm2'⟩)
                                    ?_
                                  intro _ hJ2
                                  c0_hsplit
                                  · have hw0_c0 : w0 = scr2[(lit_off.toNat + i0.toNat) % 2 ^ 32]'(by
                                        rw [Nat.mod_eq_of_lt (by omega), hsc2]; omega) :=
                                      m6_getElem_congr (by rw [hi0_eq,
                                        Nat.mod_eq_of_lt (by omega)]) _ _
                                    have hw0_nb : (w0 &&& 0x80000000#32) = 0#32 := by
                                      rw [hw0_c0]; exact hc
                                    have hw0_ent := hlit_ent i0.toNat (by omega)
                                    rw [← hw0_orig] at hw0_ent; unfold FullBveEntryOkW at hw0_ent
                                    rw [ite_eq_right (fun h => h hw0_nb)] at hw0_ent
                                    c0_hsteps_nogrp
                                    try rw [hlit_eq]
                                    try rw [hlit_eq_n]
                                    m8_call hGet
                                    refine fullBveGetTernM7Spec_intro rfl (m8_fullDenseInvW_scr hdw0
                                      hsc2)
                                      hw0_ent.1 hw0_ent.2 (by simp; omega) hm2 ?_
                                    intro ok_t scr_t mt _ hsc_t hout_t' hmt
                                    have hout_t : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                        scr_t[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                      (hout_t' i hi (by rcases hor with h | h <;> simp <;>
                                        omega)).trans (hout2 i hi hor)
                                    clear hout_t'
                                    c0_hsplit
                                    · have h4134 := m8_scr_imm_lt hsc_t hsc16 (k :=
                                        4134) (by decide)
                                      have h4135 := m8_scr_imm_lt hsc_t hsc16 (k :=
                                        4135) (by decide)
                                      c0_hsteps_nogrp
                                      refine wp_loop_group (ts := [i32])
                                        (fun rem3 (i1, ()) m3 => ∃ scr3 : List (BitVec 32),
                                          let s3 : FullState :=
                                            { s0 with scratch := { s0.scratch with scratch_buf :=
                                              scr3 } }
                                          scr3.length = c.scratch_cap ∧ i1.toNat ≤ lit_n.toNat ∧
                                          rem3 = lit_n.toNat - i1.toNat ∧
                                          (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                            scr3[i]? = s0.scratch.scratch_buf[i]?) ∧
                                          (FullMem c s3 ⋆ R) m3)
                                        ?_ ?_
                                      · rintro L3 rem3 ⟨i1, ⟨⟩⟩ m3 hL3 ⟨scr3, hsc3, hi1_le, rfl,
                                          hout3, hm3⟩
                                        have h4132_3 := m8_scr_imm_lt hsc3 hsc16 (k :=
                                          4132) (by decide)
                                        c0_hsplit
                                        · have hi1_lt : i1.toNat < lit_n.toNat := hc
                                          clear hc
                                          c0_hsplit
                                          · clear hc
                                            have hi1_sc : ((lit_off + i1).setWidth 64).toNat <
                                              scr3.length := by
                                              rw [hsc3, m6_zext32_toNat]; c0_bound
                                            have hi1_eq : ((lit_off + i1).setWidth 64).toNat =
                                                lit_off.toNat + i1.toNat := by
                                              rw [m6_zext32_toNat]; c0_bound
                                            let w1 := scr3[((lit_off +
                                              i1).setWidth 64).toNat]'hi1_sc
                                            have hw1_orig : w1 =
                                                s0.scratch.scratch_buf[lit_off.toNat +
                                                  i1.toNat]?.getD 0#32 := by
                                              have hget := hout3 (lit_off.toNat +
                                                i1.toNat) (by omega)
                                                (Or.inl (by omega))
                                              have hi1' : lit_off.toNat + i1.toNat < scr3.length :=
                                                by omega
                                              rw [List.getElem?_eq_getElem hi1'] at hget
                                              rw [← hget, Option.getD_some]
                                              exact (m6_getElem_congr hi1_eq.symm hi1' hi1_sc).symm
                                            have hi1_1 : (i1 + 1#32).toNat = i1.toNat + 1 := by
                                              c0_bound
                                            c0_hsteps_nogrp
                                            refine wp_join_group (ts := [])
                                              (fun _ m3' => ∃ scr3' : List (BitVec 32),
                                                scr3'.length = c.scratch_cap ∧
                                                (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                                  scr3'[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                (FullMem c { s0 with scratch :=
                                                  { s0.scratch with scratch_buf := scr3' } } ⋆
                                                    R) m3')
                                              (fun _ _ m3' ⟨scr3', hsc3', hout3', hm3'⟩ => by
                                                c0_hsteps!
                                                exact hL3 (lit_n.toNat - (i1 + 1#32).toNat) (i1 +
                                                  1#32, ())
                                                  m3' (by omega) ⟨scr3', hsc3', by omega, rfl,
                                                    hout3', hm3'⟩)
                                              ?_
                                            intro _ hJ3
                                            c0_hsplit
                                            · have hw1_c0 : w1 = scr3[(lit_off.toNat +
                                                i1.toNat) % 2 ^ 32]'(by
                                                  rw [Nat.mod_eq_of_lt (by omega), hsc3]; omega) :=
                                                m6_getElem_congr (by rw [hi1_eq,
                                                  Nat.mod_eq_of_lt (by omega)]) _ _
                                              have hw1_nb : (w1 &&& 0x80000000#32) = 0#32 := by
                                                rw [hw1_c0]; exact hc
                                              have hw1_ent := hlit_ent i1.toNat hi1_lt
                                              rw [← hw1_orig] at hw1_ent
                                              unfold FullBveEntryOkW at hw1_ent
                                              rw [ite_eq_right (fun h => h hw1_nb)] at hw1_ent
                                              c0_hsteps_nogrp
                                              try rw [hlit_eq]
                                              try rw [hlit_eq_n]
                                              m8_call hGet
                                              refine fullBveGetTernM7Spec_intro rfl
                                                (m8_fullDenseInvW_scr hdw0 hsc3)
                                                hw1_ent.1 hw1_ent.2 (by simp; omega) hm3 ?_
                                              intro ok_t1 scr_t1 mt1 _ hsc_t1 hout_t1' hmt1
                                              have hout_t1 : ∀ i < c.scratch_cap, (i < 4002 ∨
                                                4138 ≤ i) →
                                                  scr_t1[i]? = s0.scratch.scratch_buf[i]? :=
                                                    fun i hi hor =>
                                                (hout_t1' i hi (by rcases hor with h | h <;>
                                                  simp <;> omega)).trans (hout3 i hi hor)
                                              clear hout_t1'
                                              c0_hsplit
                                              · have h4134' := m8_scr_imm_lt hsc_t1 hsc16 (k :=
                                                  4134) (by decide)
                                                have h4135' := m8_scr_imm_lt hsc_t1 hsc16 (k :=
                                                  4135) (by decide)
                                                have h4136 := m8_scr_imm_lt hsc_t1 hsc16 (k :=
                                                  4136) (by decide)
                                                have h4137 := m8_scr_imm_lt hsc_t1 hsc16 (k :=
                                                  4137) (by decide)
                                                c0_hsteps_nogrp
                                                refine wp_join_state_pure (ts := [.bool, i32, i32,
                                                  i32])
                                                  (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                                  (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2,
                                                    ())) (fun _ => True)
                                                  ?_
                                                  (fun _ hJc => by
                                                    c0_hsplit
                                                    · c0_hsteps!; exact hJc (_, _, _, _) trivial
                                                    · c0_hsteps_nogrp
                                                      refine wp_join_state_pure (ts := [.bool, i32,
                                                        i32, i32])
                                                        (α := Bool × BitVec 32 × BitVec 32 × BitVec
                                                          32)
                                                        (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2,
                                                          ())) (fun _ => True)
                                                        (fun _ p _ => by
                                                          c0_hsteps!; exact hJc p trivial)
                                                        (fun _ hJc2 => by
                                                          c0_hsplit
                                                          · c0_hsteps!; exact hJc2 (_, _, _,
                                                              _) trivial
                                                          · c0_hsteps_nogrp
                                                            refine wp_join_state_pure (ts :=
                                                              [.bool, i32, i32, i32])
                                                              (α := Bool × BitVec 32 × BitVec 32 ×
                                                                BitVec 32)
                                                              (fun p => (p.1, p.2.1, p.2.2.1,
                                                                p.2.2.2, ())) (fun _ => True)
                                                              (fun _ p _ => by
                                                                c0_hsteps!; exact hJc2 p trivial)
                                                              (fun _ hJc3 => by
                                                                c0_hsplit
                                                                · c0_hsteps!; exact hJc3 (_, _, _,
                                                                    _) trivial
                                                                · c0_hsteps_nogrp
                                                                  refine wp_join_state_pure (ts :=
                                                                    [.bool, i32, i32, i32])
                                                                    (α := Bool × BitVec 32 × BitVec
                                                                      32 × BitVec 32)
                                                                    (fun p => (p.1, p.2.1, p.2.2.1,
                                                                      p.2.2.2, ())) (fun _ => True)
                                                                    (fun _ p _ => by
                                                                      c0_hsteps!
                                                                      exact hJc3 p trivial)
                                                                    (fun _ hJc4 => by
                                                                      c0_hsplit
                                                                      · c0_hsteps!
                                                                        exact hJc4 (_, _, _,
                                                                          _) trivial
                                                                      · c0_hsteps!
                                                                        exact hJc4 (_, _, _,
                                                                          _) trivial))))
                                                rintro _ ⟨ok_c, cond, u, w⟩ _
                                                c0_hsteps_nogrp
                                                refine wp_join_group (ts := [])
                                                  (fun _ mf => ∃ scr_e : List (BitVec 32),
                                                    scr_e.length = c.scratch_cap ∧
                                                    (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                                      scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                    (FullMem c { s0 with scratch :=
                                                      { s0.scratch with scratch_buf := scr_e } } ⋆
                                                        R) mf)
                                                  (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                                    c0_hsteps!; exact hJ3 () mf ⟨scr_e, hse, houte,
                                                      hme⟩)
                                                  ?_
                                                intro _ hJno
                                                c0_hsplit
                                                · c0_hsteps_nogrp
                                                  rotate_left 1
                                                  · exact hJno () mt1 ⟨scr_t1, hsc_t1, hout_t1,
                                                      hmt1⟩
                                                  m8_call hMatch
                                                  refine m8BveMatchTernSpec_intro rfl
                                                    (m8_fullDenseInvW_scr hdw0 hsc_t1)
                                                    hsc16 hoo_bnd hon_2k
                                                    (fun j hj => by
                                                      dsimp only [Arg.val] at hj ⊢
                                                      rw [hout_t1 (opp_off.toNat +
                                                        j) (by omega) (Or.inl (by omega))]
                                                      exact hopp_ent j hj)
                                                    hmt1 ?_
                                                  intro m0_r scr_m0 m_m0 _ hsc_m0 hout_m0 hm0_ok
                                                    hm_m0
                                                  have hout_m0' : ∀ i < c.scratch_cap, (i < 4002 ∨
                                                    4138 ≤ i) →
                                                      scr_m0[i]? = s0.scratch.scratch_buf[i]? :=
                                                        fun i hi hor =>
                                                    (hout_m0 i hi (by omega)).trans (hout_t1 i hi
                                                      hor)
                                                  c0_hsteps_nogrp
                                                  refine wp_join_group (ts := [])
                                                    (fun _ mf => ∃ scr_e : List (BitVec 32),
                                                      scr_e.length = c.scratch_cap ∧
                                                      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                                        scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                      (FullMem c { s0 with scratch :=
                                                        { s0.scratch with scratch_buf :=
                                                          scr_e } } ⋆ R) mf)
                                                    (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                                      c0_hsteps!; exact hJno () mf ⟨scr_e, hse,
                                                        houte, hme⟩)
                                                    ?_
                                                  intro _ hJm0
                                                  c0_hsplit
                                                  · dsimp only [Arg.val] at hm0_ok
                                                    have hj0_lt : (m0_r &&& 0x7FFFFFFF#32).toNat <
                                                      opp_n.toNat :=
                                                      hm0_ok.resolve_left (by assumption)
                                                    c0_hsteps_nogrp
                                                    m8_call hMatch
                                                    refine m8BveMatchTernSpec_intro rfl
                                                      (m8_fullDenseInvW_scr hdw0 hsc_m0)
                                                      hsc16 hoo_bnd hon_2k
                                                      (fun j hj => by
                                                        dsimp only [Arg.val] at hj ⊢
                                                        rw [hout_m0' (opp_off.toNat +
                                                          j) (by omega) (Or.inl (by omega))]
                                                        exact hopp_ent j hj)
                                                      hm_m0 ?_
                                                    intro m1_r scr_m1 m_m1 _ hsc_m1 hout_m1 hm1_ok
                                                      hm_m1
                                                    have hout_m1' : ∀ i < c.scratch_cap,
                                                      (i < 4002 ∨ 4138 ≤ i) →
                                                        scr_m1[i]? = s0.scratch.scratch_buf[i]? :=
                                                          fun i hi hor =>
                                                      (hout_m1 i hi (by omega)).trans (hout_m0' i hi
                                                        hor)
                                                    c0_hsteps_nogrp
                                                    refine wp_join_group (ts := [])
                                                      (fun _ mf => ∃ scr_e : List (BitVec 32),
                                                        scr_e.length = c.scratch_cap ∧
                                                        (∀ i < c.scratch_cap, (i < 4002 ∨
                                                          4138 ≤ i) →
                                                          scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                        (FullMem c { s0 with scratch :=
                                                          { s0.scratch with scratch_buf :=
                                                            scr_e } } ⋆ R) mf)
                                                      (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                                        c0_hsteps!; exact hJm0 () mf ⟨scr_e, hse,
                                                          houte, hme⟩)
                                                      ?_
                                                    intro _ hJm1
                                                    c0_hsplit
                                                    · dsimp only [Arg.val] at hm1_ok
                                                      have hj1_lt : (m1_r &&&
                                                        0x7FFFFFFF#32).toNat < opp_n.toNat :=
                                                        hm1_ok.resolve_left (by assumption)
                                                      c0_hstep; c0_hstep; c0_hstep; c0_hsplit
                                                      rotate_left 1
                                                      · c0_hsteps!; exact hJm1 () m_m1 ⟨scr_m1,
                                                          hsc_m1, hout_m1', hm_m1⟩
                                                      exact m8_ite_hit_wp Γ c s0 scr_m1 R lit_mask
                                                        opp_mask
                                                        i0 i1 m0_r m1_r m_m1 Q X hsc_m1 hsc16
                                                          hout_m1'
                                                        hlm_k hom_k (by omega) (by omega)
                                                        (by omega) (by omega) hm_m1 hQ
                                                    · c0_hsteps!; exact hJm1 () m_m1 ⟨scr_m1,
                                                        hsc_m1, hout_m1', hm_m1⟩
                                                  · c0_hsteps!; exact hJm0 () m_m0 ⟨scr_m0, hsc_m0,
                                                      hout_m0', hm_m0⟩
                                                · c0_hsteps!; exact hJno () mt1 ⟨scr_t1, hsc_t1,
                                                    hout_t1, hmt1⟩
                                              · c0_hsteps!; exact hJ3 () mt1 ⟨scr_t1, hsc_t1,
                                                  hout_t1, hmt1⟩
                                            · c0_hsteps!; exact hJ3 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                                          · c0_hsteps!; exact hJ2 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                                        · c0_hsteps!; exact hJ2 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                                      · intro L3 hL3; c0_hsteps!
                                        exact hL3 (lit_n.toNat - (i0 + 1#32).toNat) (i0 + 1#32,
                                          ()) mt
                                          ⟨scr_t, hsc_t, by omega, rfl, hout_t, hmt⟩
                                    · c0_hsteps!; exact hJ2 () mt ⟨scr_t, hsc_t, hout_t, hmt⟩
                                  · c0_hsteps!; exact hJ2 () m2 ⟨scr2, hsc2, hout2, hm2⟩
                                · c0_hsteps!
                                  exact hQ false scr2 m2 hsc2 hout2 hm2
                              · c0_hsteps!
                                exact hQ false scr2 m2 hsc2 hout2 hm2
                            · intro L2 hL2; c0_hsteps!
                              exact hL2 lit_n.toNat (0#32, ()) _
                                ⟨scr_i0, hsc_i0, Nat.zero_le _, by simp, hout_i0, hm⟩
                    · intro L1 hL1; c0_hsteps!
                      exact hL1 lit_n.toNat (0#64, 0#32, ()) m0
                        ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl⟩
              · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by first | simp | simp [hc]))
            · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by first | simp | simp [hc]))
          · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by simp [hc]))
        · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by simp [hc]))
      · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by simp [hc]))
    · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by simp [hc]))
  · intro J hJ; c0_hsplit <;> (c0_hsteps!; exact hJ _ (by simp [hc]))

/-- Parametric `Func.wp` proof for `full_bve_find_ite_m8`. -/
theorem full_bve_find_ite_m8_wp (Γ : Env)
    (hSide : ∀ a m Q X, m8BveFindIteSideSpec a m Q X →
      Γ "full_bve_find_ite_side_m8" [i64, i32, i32, i32, .bool] [.bool] a m Q X) :
    ∀ a m Q X, m8BveFindIteSpec a m Q X →
      Func.wp Γ full_bve_find_ite_m8_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hv, hnp, hnn, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindIteSpec_elim hSpec
  unfold Func.wp full_bve_find_ite_m8_body
  c0_hsteps_nogrp
  m8_call hSide
  dsimp only [vals, Arg.val]
  refine m8BveFindIteSideSpec_intro rfl hdw0 hsc16 hv hnp hnn hp_ok hn_ok hm0
    (fun ok1 scr1 m1 hsc1 hout1 hm1 => by
      c0_hsplit
      · c0_hsteps!; exact hQ true scr1 m1 hsc1 hout1 hm1
      · c0_hsteps_nogrp
        m8_call hSide
        dsimp only [vals, Arg.val]
        refine m8BveFindIteSideSpec_intro rfl (m8_fullDenseInvW_scr hdw0 hsc1) hsc16 hv hnp hnn
          (fun i hi => by
            have hbe := m8_bveEntry_congr_core (hp_ok i hi) rfl rfl rfl
            rw [hout1 i (by omega) (Or.inl (by omega))]
            exact hbe)
          (fun j hj => by
            have hbe := m8_bveEntry_congr_core (hn_ok j hj) rfl rfl rfl
            rw [hout1 (2001 + j) (by omega) (Or.inl (by omega))]
            exact hbe)
          hm1 (fun ok2 scr2 m2 hsc2 hout2 hm2 => by
            c0_hsteps!; exact hQ ok2 scr2 m2 hsc2 (fun i hi hor => by
              rw [hout2 i hi hor]; exact hout1 i hi hor) hm2))

def M8XorMaskEntriesOk (scr : List (BitVec 32)) (base lim : Nat) (mask : BitVec 32) : Prop :=
  mask.toNat < 65536 ∧
  ∀ t < 16, (mask &&& (1#32 <<< t)) ≠ 0#32 → (scr[base + t]?.getD 0#32).toNat < lim

theorem m8_xorMaskEntriesOk_zero (scr : List (BitVec 32)) (base lim : Nat) :
    M8XorMaskEntriesOk scr base lim 0#32 :=
  ⟨by decide, fun _ _ h => absurd (by simp) h⟩

private theorem m8_bv32_bit_shl1 {m k : Nat} (hk : k < 32) :
    ((1#32 : BitVec 32) <<< m)[k] = decide (k = m) := by
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_one]
  by_cases hkm : k = m
  · subst hkm; simp
  · by_cases hlt : k < m
    · simp [hlt, hkm]
    · simp [hlt, hkm, show k - m ≠ 0 from by omega]

theorem m8_xorMaskEntriesOk_init {scr : List (BitVec 32)} {base lim : Nat} {idx : BitVec 32}
    (hscr : base + 16 ≤ scr.length) (hi : idx.toNat < lim) :
    M8XorMaskEntriesOk (scr.set base idx) base lim 1#32 := by
  refine ⟨by decide, fun t ht hb => ?_⟩
  have ht0 : t = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have hz : ((1#32 : BitVec 32) &&& (1#32 <<< t)) = 0#32 := by
      ext k hk
      simp only [BitVec.getElem_and, BitVec.getElem_zero, BitVec.getElem_one,
        m8_bv32_bit_shl1 hk]
      by_cases hk0 : k = 0
      · subst hk0; simp [Ne.symm hne]
      · simp [hk0]
    exact hb hz
  subst ht0
  rw [Nat.add_zero, List.getElem?_set_self (by omega), Option.getD_some]
  exact hi

theorem m8_xorMaskEntriesOk_set {scr : List (BitVec 32)} {base lim : Nat}
    {mask pat idx : BitVec 32} (hok : M8XorMaskEntriesOk scr base lim mask)
    (hscr : base + 16 ≤ scr.length) (hpat : pat.toNat < 16) (hi : idx.toNat < lim) :
    M8XorMaskEntriesOk (scr.set (base + pat.toNat) idx) base lim (mask ||| (1#32 <<< pat.toNat)) :=
      by
  have hp : 2 ^ pat.toNat < 65536 := by
    calc 2 ^ pat.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
      _ < 65536 := by decide
  have hsh_lt : (1#32 <<< pat.toNat : BitVec 32).toNat < 65536 := by
    rw [BitVec.toNat_shiftLeft, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    simpa [Nat.one_mul] using hp
  refine ⟨?_, fun t ht hb => ?_⟩
  · rw [BitVec.toNat_or]
    have hm1 : mask.toNat < 2 ^ 16 := hok.1
    have hm2 : (1#32 <<< pat.toNat : BitVec 32).toNat < 2 ^ 16 := hsh_lt
    exact Nat.or_lt_two_pow hm1 hm2
  · by_cases htp : t = pat.toNat
    · subst htp; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hi
    · rw [List.getElem?_set_ne (by omega)]
      apply hok.2 t ht
      intro hz; apply hb
      ext k hk
      have hzk := congrArg (·[k]) hz
      simp only [BitVec.getElem_and, BitVec.getElem_zero] at hzk
      simp only [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right,
        m8_bv32_bit_shl1 hk] at hzk ⊢
      by_cases hkp : k = pat.toNat
      · subst hkp; simp [Ne.symm htp]
      · simp [hkp, hzk]

theorem m8_xor_bit_test {m p : BitVec 32} (hp : p.toNat < 16)
    (hc : ((m >>> p.toNat) &&& 1#32) ≠ 0#32) :
    (m &&& (1#32 <<< p.toNat)) ≠ 0#32 := by
  have hbit0 : ((m >>> p.toNat) &&& 1#32)[0] = true := by
    refine Classical.byContradiction fun hf => ?_
    have hb0 : ((m >>> p.toNat) &&& 1#32)[0] = false := Bool.eq_false_iff.mpr hf
    apply hc; ext k hk
    cases k with
    | zero => simpa using hb0
    | succ j => simp
  have hmp : m[p.toNat] = true := by
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_one,
      decide_true, Bool.and_true, Nat.add_zero] at hbit0
    exact hbit0
  intro hz
  have hzk := congrArg (·[p.toNat]) hz
  simp only [BitVec.getElem_and, BitVec.getElem_zero,
    m8_bv32_bit_shl1 (Nat.lt_trans hp (by decide)),
    hmp, decide_true, Bool.true_and] at hzk
  exact absurd hzk (by decide)

private def m8XorLmClearExpr (pScr pLm : BitVec 64) (tmp_l k : BitVec 32)
    (after : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32]])
    (fun lbls =>
      Blocks.cons (fun c_idx =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var c_idx.fst, Arg.var k, ())⟩ fun b =>
        Expr.jnz (Arg.var b.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.var tmp_l, Arg.var c_idx.fst, ())⟩ fun p0 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p0.fst, ())⟩ fun p1 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p2.fst, ())⟩ fun p3 =>
           Expr.load i32 (Arg.var p3.fst) fun l =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var l, ())⟩ fun q0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var q0.fst, ())⟩ fun q1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z0 =>
           Expr.store (Arg.var z0.fst) (Arg.var q1.fst) (
           Expr.let_ ⟨OpCode.xor i32, (Arg.var l, Arg.imm 1, ())⟩ fun lx =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var lx.fst, ())⟩ fun r0 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pLm, Arg.var r0.fst, ())⟩ fun r1 =>
           Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm (t := i32) 0, ())⟩ fun z1 =>
           Expr.store (Arg.var z1.fst) (Arg.var r1.fst) (
           Expr.let_ ⟨OpCode.add i32, (Arg.var c_idx.fst, Arg.imm 1, ())⟩ fun nx =>
           Expr.jump lbls.1 (Arg.var nx.fst, ()))))
          after)
        Blocks.nil)
    (fun lbls => Expr.jump lbls.1 (Arg.imm (t := i32) 0, ()))

private theorem m8_xor_clean_lm_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (s : FullState) (scr : List (BitVec 32)) (R' : Mem 64 → Prop)
    (k : BitVec 32) (lm0 : List (BitVec 8)) (m0 : Mem 64)
    (after : Expr Val Cont [.bool])
    (hsc_len : scr.length = c.scratch_cap) (hsc16 : 16384 ≤ c.scratch_cap)
    (hk4 : k.toNat ≤ 4) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlm0 : lm0.length = 2 * c.max_vars)
    (hbd : ∀ j < k.toNat, (scr[4166 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnz : ∀ y < 2 * c.max_vars, lm0[y]?.getD 0#8 ≠ 0#8 →
      ∃ j < k.toNat,
        y = (scr[4166 + j]?.getD 0#32).toNat ∨
        y = ((scr[4166 + j]?.getD 0#32) ^^^ 1#32).toNat)
    (hm0 : (array (t := i8) c.pLitMark lm0 ⋆ array (t := i32) c.pScratchBuf scr ⋆ R') m0)
    (hafter : ∀ (lm' : List (BitVec 8)) (m' : Mem 64),
      lm'.length = 2 * c.max_vars →
      (∀ y < 2 * c.max_vars, lm'[y]?.getD 0#8 = 0#8) →
      (array (t := i8) c.pLitMark lm' ⋆ array (t := i32) c.pScratchBuf scr ⋆ R') m' →
      wp Γ Q X after m') :
    wp Γ Q X (m8XorLmClearExpr c.pScratchBuf c.pLitMark 4166#32 k after) m0 := by
  unfold m8XorLmClearExpr
  refine wp_loop_group (ts := [i32])
    (fun rem (ci, ()) m_i =>
      ∃ lmi : List (BitVec 8), lmi.length = 2 * c.max_vars ∧ ci.toNat ≤ k.toNat ∧
        rem = k.toNat - ci.toNat ∧
        (∀ y < 2 * c.max_vars, lmi[y]?.getD 0#8 ≠ 0#8 →
          ∃ j, ci.toNat ≤ j ∧ j < k.toNat ∧
            (y = (scr[4166 + j]?.getD 0#32).toNat ∨
             y = ((scr[4166 + j]?.getD 0#32) ^^^ 1#32).toNat)) ∧
        (array (t := i8) c.pLitMark lmi ⋆ array (t := i32) c.pScratchBuf scr ⋆ R') m_i)
    ?_ ?_
  · rintro Lc remc ⟨ci, ⟨⟩⟩ mc hLc ⟨lmc, hlmc, hci_le, rfl, hremc, hmc⟩
    c0_hsplit
    · have hci_lt : ci.toNat < k.toNat := hc
      have hci_sc : ((4166#32 + ci).setWidth 64).toNat < scr.length := by
        rw [hsc_len, m6_zext32_toNat]; c0_bound
      have hci_eq : ((4166#32 + ci).setWidth 64).toNat = 4166 + ci.toNat := by
        rw [m6_zext32_toNat]; c0_bound
      let lc := scr[((4166#32 + ci).setWidth 64).toNat]'hci_sc
      have hlc_eq : scr[4166 + ci.toNat]?.getD 0#32 = lc := by
        rw [List.getElem?_eq_getElem (by rw [hsc_len]; omega), Option.getD_some]
        exact m6_getElem_congr hci_eq.symm _ hci_sc
      have hlc_lt : lc.toNat < 2 * s.core.cur_vars := by
        rw [← hlc_eq]; exact hbd ci.toNat hci_lt
      have hlc_lm : (lc.setWidth 64).toNat < lmc.length := by
        rw [hlmc, m6_zext32_toNat]; omega
      have hlcn_lm : ((lc ^^^ 1#32).setWidth 64).toNat <
          (lmc.set (lc.setWidth 64).toNat 0#8).length := by
        have := (m8_bv32_xor1_lt lc hlc_lt).2
        rw [List.length_set, hlmc, m6_zext32_toNat]; omega
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps!
      refine hLc (k.toNat - (ci + 1#32).toNat) (ci + 1#32, ()) _ (by omega)
        ⟨_, by simp [hlmc], by omega, rfl,
         m8_lm_clear2_step hlmc (by rw [← hlmc]; exact hlc_lm)
           (by rw [← hlmc, ← List.length_set (a := 0#8) (i :=
             (lc.setWidth 64).toNat)]; exact hlcn_lm)
           (fun y hy hnzy => by
             obtain ⟨t, ht1, ht2, hyeq⟩ := hremc y hy hnzy
             rcases Nat.eq_or_lt_of_le ht1 with rfl | hgt
             · rw [hlc_eq] at hyeq
               rcases hyeq with h0 | h1
               · left; rw [m6_zext32_toNat, h0]
               · right; left; rw [m6_zext32_toNat, h1]
             · right; right; exact ⟨t, by omega, ht2, hyeq⟩),
         by dsimp only [lc]; simp only [sep_emp, sep_assoc] at hm ⊢; exact hm⟩
    · have hclr : ∀ y < 2 * c.max_vars, lmc[y]?.getD 0#8 = 0#8 := fun y hy =>
        Classical.byContradiction fun hnz_y => by
          obtain ⟨t, ht1, ht2, _⟩ := hremc y hy hnz_y; omega
      exact hafter lmc mc hlmc hclr hmc
  · intro Lc hLc; c0_hsteps!
    exact hLc k.toNat (0#32, ()) m0 ⟨lm0, hlm0, Nat.zero_le _, by simp,
      fun y hy hnz_y => let ⟨t, ht, h⟩ := hnz y hy hnz_y; ⟨t, Nat.zero_le _, ht, h⟩, hm0⟩

private def m8SetMaskBitExpr (pScr : BitVec 64) (base idx : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var idx, Arg.imm 5, ())⟩ fun p0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm base, Arg.var p0.fst, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p2.fst, Arg.imm 4, ())⟩ fun p3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p3.fst, ())⟩ fun p4 =>
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var idx, Arg.imm 5, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm base, Arg.var q0.fst, ())⟩ fun q1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var q1.fst, ())⟩ fun q2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q2.fst, Arg.imm 4, ())⟩ fun q3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q3.fst, ())⟩ fun q4 =>
  Expr.load i32 (Arg.var q4.fst) fun ld =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var idx, Arg.imm 31, ())⟩ fun s0 =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var s0.fst, ())⟩ fun s1 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var ld, Arg.var s1.fst, ())⟩ fun s2 =>
  Expr.store (Arg.var s2.fst) (Arg.var p4.fst) k

private def m8XorCommitExpr (pScr : BitVec 64) (tmp_e tmp_o k etgt otgt : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var k, ())⟩ fun nlim =>
  Expr.group (sig := [[i32]])
    (fun Lp2 =>
      Blocks.cons (fun p =>
        Expr.let_ ⟨OpCode.ult i32, (Arg.var p.fst, Arg.var nlim.fst, ())⟩ fun cond =>
        Expr.jnz (Arg.var cond.fst)
          (Expr.group (sig := [[]])
            (fun _ =>
              Blocks.cons (fun _ =>
                Expr.group (sig := [[]])
                  (fun _ =>
                    Blocks.cons (fun _ =>
                      Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun np =>
                      Expr.jump Lp2.1 (Arg.var np.fst, ())) Blocks.nil)
                  (fun Js2 =>
                    Expr.let_ ⟨OpCode.lshr i32, (Arg.var otgt, Arg.var p.fst, ())⟩ fun s =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
                    Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
                    Expr.jnz (Arg.var c0.fst)
                      (Expr.let_ ⟨OpCode.add i32, (Arg.var tmp_o, Arg.var p.fst, ())⟩ fun a0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                       Expr.load i32 (Arg.var a3.fst) fun idx =>
                       m8SetMaskBitExpr pScr 4066#32 idx (Expr.jump Js2.1 ()))
                      (Expr.jump Js2.1 ()))) Blocks.nil)
            (fun Js1 =>
              Expr.let_ ⟨OpCode.lshr i32, (Arg.var etgt, Arg.var p.fst, ())⟩ fun s =>
              Expr.let_ ⟨OpCode.and i32, (Arg.var s.fst, Arg.imm 1, ())⟩ fun b =>
              Expr.let_ ⟨OpCode.ne i32, (Arg.var b.fst, Arg.imm 0, ())⟩ fun c0 =>
              Expr.jnz (Arg.var c0.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.var tmp_e, Arg.var p.fst, ())⟩ fun a0 =>
                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                 Expr.load i32 (Arg.var a3.fst) fun idx =>
                 m8SetMaskBitExpr pScr 4002#32 idx (Expr.jump Js1.1 ()))
                (Expr.jump Js1.1 ())))
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm (t := i32) 4130, ())⟩ fun w0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var w0.fst, Arg.imm 4, ())⟩ fun w1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var w1.fst, ())⟩ fun w2 =>
           Expr.store (Arg.imm (t := i32) 1) (Arg.var w2.fst) (
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm (t := i32) 4131, ())⟩ fun y0 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var y0.fst, Arg.imm 4, ())⟩ fun y1 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var y1.fst, ())⟩ fun y2 =>
           Expr.store (Arg.imm (t := i32) 0) (Arg.var y2.fst) (
           Expr.ret (Arg.imm (t := .bool) true, ())))))
        Blocks.nil)
    (fun Lp2 => Expr.jump Lp2.1 (Arg.imm (t := i32) 0, ()))

private theorem m8_xor_commit_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (scrn : List (BitVec 32)) (R_scr : Mem 64 → Prop)
    (k etgt otgt : BitVec 32) (np nn : BitVec 32) (mc : Mem 64)
    (hsn : scrn.length = c.scratch_cap) (hsc16 : 16384 ≤ c.scratch_cap)
    (hk_le : k.toNat ≤ 4) (hnp_le : np.toNat ≤ 2001) (hnn_le : nn.toNat ≤ 2001)
    (hpm_n : M8XorMaskEntriesOk scrn 4134 np.toNat etgt)
    (hom_n : M8XorMaskEntriesOk scrn 4150 nn.toNat otgt)
    (hmc : (array (t := i32) c.pScratchBuf scrn ⋆ R_scr) mc)
    (hRet : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4132 ≤ idx) → scr'[idx]? = scrn[idx]?) →
      (array (t := i32) c.pScratchBuf scr' ⋆ R_scr) m' → Q (true, ()) m') :
    wp Γ Q X (m8XorCommitExpr c.pScratchBuf 4134#32 4150#32 k etgt otgt) mc := by
  have hk_pow : 1 <<< k.toNat ≤ 16 := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_le_pow_right (n := 2) (by decide) hk_le
  have hk_shl : ((1 : BitVec 32) <<< (k.toNat % 32)).toNat = 1 <<< k.toNat := by
    rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_shiftLeft,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  unfold m8XorCommitExpr m8SetMaskBitExpr
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun remp2 (p, ()) mp2 => ∃ scr_p : List (BitVec 32),
      scr_p.length = c.scratch_cap ∧ p.toNat ≤ (1 <<< k.toNat) ∧
      remp2 = (1 <<< k.toNat) - p.toNat ∧
      (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4130 ≤ idx) → scr_p[idx]? = scrn[idx]?) ∧
      (array (t := i32) c.pScratchBuf scr_p ⋆ R_scr) mp2)
    ?_ ?_
  · rintro Lp2 remp2 ⟨p, ⟨⟩⟩ mp2 hLp2 ⟨scr_p, hscp2, hp2_le, rfl, houtp2, hmp2⟩
    c0_hsplit
    · have hp2_lt : p.toNat < 1 <<< k.toNat := by rw [← hk_shl]; exact hc
      have hp2_16 : p.toNat < 16 := by omega
      have hp2_inc : (p + 1#32).toNat = p.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ ms1 => ∃ scr_s1 : List (BitVec 32),
          scr_s1.length = c.scratch_cap ∧
          (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4130 ≤ idx) → scr_s1[idx]? = scrn[idx]?) ∧
          (array (t := i32) c.pScratchBuf scr_s1 ⋆ R_scr) ms1)
        (fun _ _ ms1 ⟨scr_s1, hss1, houts1, hms1⟩ => by
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ ms2 => ∃ scr_s2 : List (BitVec 32),
              scr_s2.length = c.scratch_cap ∧
              (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4130 ≤ idx) → scr_s2[idx]? = scrn[idx]?) ∧
              (array (t := i32) c.pScratchBuf scr_s2 ⋆ R_scr) ms2)
            (fun _ _ ms2 ⟨scr_s2, hss2, houts2, hms2⟩ => by
              c0_hsteps!
              exact hLp2 ((1 <<< k.toNat) - (p + 1#32).toNat) (p + 1#32, ()) ms2 (by omega)
                ⟨scr_s2, hss2, by omega, rfl, houts2, hms2⟩)
            (fun _ hJs2 => by
              c0_hsplit
              · have hot_bit : (otgt &&& (1#32 <<< p.toNat)) ≠ 0#32 := by
                  refine m8_xor_bit_test hp2_16 ?_
                  rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                have hni_sc : ((4150#32 + p).setWidth 64).toNat < scr_s1.length := by
                  rw [hss1, m6_zext32_toNat]; c0_bound
                have hni_eq : ((4150#32 + p).setWidth 64).toNat = 4150 + p.toNat := by
                  rw [m6_zext32_toNat]; c0_bound
                let ni := scr_s1[((4150#32 + p).setWidth 64).toNat]'hni_sc
                have hni_orig : ni = scrn[4150 + p.toNat]?.getD 0#32 := by
                  have hg := houts1 (4150 + p.toNat) (by omega) (Or.inr (by omega))
                  have hi' : 4150 + p.toNat < scr_s1.length := by rw [hss1]; omega
                  rw [List.getElem?_eq_getElem hi'] at hg
                  rw [← hg, Option.getD_some]
                  exact (m6_getElem_congr hni_eq.symm hi' hni_sc).symm
                have hni_lt : ni.toNat < 2001 := by
                  have := hom_n.2 p.toNat hp2_16 hot_bit; rw [← hni_orig] at this; omega
                have hm_idx := m8_mask_idx_lo 4066#32 ni (Or.inr rfl) hni_lt
                have hm_sc : ((4066#32 + (ni >>> (5 : Nat))).setWidth 64).toNat < scr_s1.length :=
                  by
                  rw [hss1, m6_zext32_toNat]; omega
                c0_hsteps!
                refine hJs2 () _ ⟨_, by simp [hss1], fun idx hidx hor => by
                  rw [List.getElem?_set_ne (by
                    rw [m6_zext32_toNat, hm_idx.1]
                    simp only [BitVec.toNat_ofNat] at hm_idx ⊢; omega)]
                  exact houts1 idx hidx hor, hm⟩
              · c0_hsteps!; exact hJs2 () ms1 ⟨scr_s1, hss1, houts1, hms1⟩))
        (fun _ hJs1 => by
          c0_hsplit
          · have het_bit : (etgt &&& (1#32 <<< p.toNat)) ≠ 0#32 := by
              refine m8_xor_bit_test hp2_16 ?_
              rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
            have hei_sc : ((4134#32 + p).setWidth 64).toNat < scr_p.length := by
              rw [hscp2, m6_zext32_toNat]; c0_bound
            have hei_eq : ((4134#32 + p).setWidth 64).toNat = 4134 + p.toNat := by
              rw [m6_zext32_toNat]; c0_bound
            let ei := scr_p[((4134#32 + p).setWidth 64).toNat]'hei_sc
            have hei_orig : ei = scrn[4134 + p.toNat]?.getD 0#32 := by
              have hg := houtp2 (4134 + p.toNat) (by omega) (Or.inr (by omega))
              have hi' : 4134 + p.toNat < scr_p.length := by rw [hscp2]; omega
              rw [List.getElem?_eq_getElem hi'] at hg
              rw [← hg, Option.getD_some]
              exact (m6_getElem_congr hei_eq.symm hi' hei_sc).symm
            have hei_lt : ei.toNat < 2001 := by
              have := hpm_n.2 p.toNat hp2_16 het_bit; rw [← hei_orig] at this; omega
            have hm_idx := m8_mask_idx_lo 4002#32 ei (Or.inl rfl) hei_lt
            have hm_sc : ((4002#32 + (ei >>> (5 : Nat))).setWidth 64).toNat < scr_p.length := by
              rw [hscp2, m6_zext32_toNat]; omega
            c0_hsteps!
            refine hJs1 () _ ⟨_, by simp [hscp2], fun idx hidx hor => by
              rw [List.getElem?_set_ne (by
                rw [m6_zext32_toNat, hm_idx.1]
                simp only [BitVec.toNat_ofNat] at hm_idx ⊢; omega)]
              exact houtp2 idx hidx hor, hm⟩
          · c0_hsteps!; exact hJs1 () mp2 ⟨scr_p, hscp2, houtp2, hmp2⟩)
    · have h4130 : (4130#64).toNat < scr_p.length := by
        rw [hscp2, show (4130#64).toNat = 4130 from rfl]; omega
      have h4131 : (4131#64).toNat < (scr_p.set (4130#64).toNat 1#32).length := by
        rw [List.length_set, hscp2, show (4131#64).toNat = 4131 from rfl]; omega
      c0_hsteps!
      refine hRet _ _ (by simp [hscp2]) (fun idx hidx hor => by
        rw [List.getElem?_set_ne (by rw [show (4131#64).toNat = 4131 from rfl]; omega),
          List.getElem?_set_ne (by rw [show (4130#64).toNat = 4130 from rfl]; omega)]
        exact houtp2 idx hidx (by omega)) hm
  · intro Lp2 hLp2; c0_hsteps!
    exact hLp2 (1 <<< k.toNat) (0#32, ()) mc ⟨scrn, hsn, Nat.zero_le _, rfl, fun _ _ _ => rfl, hmc⟩

private def m8XorNegScanExpr (h pScr : Val i64) (nn nl k otgt tmp_o : Val i32)
    (onDone : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]])
    (fun Ln =>
      Blocks.cons
        (fun p =>
          Expr.let_ ⟨OpCode.ult i32, (Arg.var p.snd.fst, Arg.var nn, ())⟩ fun c1 =>
          Expr.jnz (Arg.var c1.fst)
            (Expr.let_ ⟨OpCode.ne i32, (Arg.var p.fst, Arg.var otgt, ())⟩ fun c2 =>
             Expr.jnz (Arg.var c2.fst)
               (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2001, Arg.var p.snd.fst, ())⟩ fun a0 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a0.fst, ())⟩ fun a1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var a1.fst, Arg.imm 4, ())⟩ fun a2 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a2.fst, ())⟩ fun a3 =>
                Expr.load i32 (Arg.var a3.fst) fun ld =>
                Expr.group (sig := [[i32]])
                  (fun _ =>
                    Blocks.cons
                      (fun px =>
                        Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩ fun nx =>
                        Expr.jump Ln.fst (Arg.var px.fst, Arg.var nx.fst, ()))
                      Blocks.nil)
                  (fun Jn' =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun b0 =>
                    Expr.let_ ⟨OpCode.eq i32, (Arg.var b0.fst, Arg.imm 0, ())⟩ fun b1 =>
                    Expr.jnz (Arg.var b1.fst)
                      (Expr.call "full_bve_xor_pat_m7" (as := [i64, i32, i32, i32]) (bs := [i32])
                        (Arg.var h, Arg.var nl, Arg.var ld, Arg.var k, ())
                        fun pat =>
                        Expr.group (sig := [[i32]])
                          (fun _ =>
                            Blocks.cons
                              (fun py => Expr.jump Jn'.fst (Arg.var py.fst, ()))
                              Blocks.nil)
                          (fun Jnm =>
                            Expr.let_ ⟨OpCode.ult i32, (Arg.var pat.fst, Arg.imm 16, ())⟩ fun d0 =>
                            Expr.jnz (Arg.var d0.fst)
                              (Expr.let_ ⟨OpCode.lshr i32, (Arg.var otgt, Arg.var pat.fst, ())⟩
                                 fun d1 =>
                               Expr.let_ ⟨OpCode.and i32, (Arg.var d1.fst, Arg.imm 1, ())⟩ fun d2 =>
                               Expr.let_ ⟨OpCode.ne i32, (Arg.var d2.fst, Arg.imm 0, ())⟩ fun d3 =>
                               Expr.jnz (Arg.var d3.fst)
                                 (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p.fst, Arg.var pat.fst, ())⟩
                                    fun d4 =>
                                  Expr.let_ ⟨OpCode.and i32, (Arg.var d4.fst, Arg.imm 1, ())⟩
                                    fun d5 =>
                                  Expr.let_ ⟨OpCode.eq i32, (Arg.var d5.fst, Arg.imm 0, ())⟩
                                    fun d6 =>
                                  Expr.jnz (Arg.var d6.fst)
                                    (Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var pat.fst, ())⟩
                                       fun d7 =>
                                     Expr.let_ ⟨OpCode.or i32, (Arg.var p.fst, Arg.var d7.fst, ())⟩
                                       fun d8 =>
                                     Expr.let_ ⟨OpCode.add i32, (Arg.var tmp_o, Arg.var pat.fst,
                                       ())⟩
                                       fun q0 =>
                                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var q0.fst, ())⟩ fun q1 =>
                                     Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩
                                       fun q2 =>
                                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q2.fst, ())⟩
                                       fun q3 =>
                                     Expr.store (Arg.var p.snd.fst) (Arg.var q3.fst)
                                       (Expr.jump Jnm.fst (Arg.var d8.fst, ())))
                                    (Expr.jump Jnm.fst (Arg.var p.fst, ())))
                                 (Expr.jump Jnm.fst (Arg.var p.fst, ())))
                              (Expr.jump Jnm.fst (Arg.var p.fst, ()))))
                      (Expr.jump Jn'.fst (Arg.var p.fst, ()))))
               (onDone p.fst))
            (onDone p.fst))
        Blocks.nil)
    (fun Ln => Expr.jump Ln.fst (Arg.imm (t := i32) 0, Arg.imm (t := i32) 0, ()))

private theorem m8_xor_neg_scan_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (lmb : List (BitVec 8)) (scrp' : List (BitVec 32)) (R : Mem 64 → Prop)
    (nn nl k_b otgt : BitVec 32) (mp' : Mem 64)
    (onDone : Val i32 → Expr Val Cont [.bool])
    (hPat : ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Γ "full_bve_xor_pat_m7" [i64, i32, i32, i32] [i32] a m Q X)
    (hdw0 : FullDenseInvW c F0 F_cur s)
    (hlmb : lmb.length = 2 * c.max_vars) (hscp' : scrp'.length = c.scratch_cap)
    (hnn_le : nn.toNat ≤ 2001) (hsc16 : 16384 ≤ c.scratch_cap)
    (hk2 : 2 ≤ k_b.toNat) (hk_le : k_b.toNat ≤ 4)
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hscr_orig : ∀ j < nn.toNat, scrp'[2001 + j]? = s.scratch.scratch_buf[2001 + j]?)
    (hmp' : (array (t := i8) c.pLitMark lmb ⋆ array (t := i32) c.pScratchBuf scrp' ⋆
      (m8FullMemNoLmScr c s ⋆ R)) mp')
    (honDone : ∀ (omask : BitVec 32) (scrn : List (BitVec 32)) (mn : Mem 64),
      scrn.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 4150 ∨ 4166 ≤ idx) → scrn[idx]? = scrp'[idx]?) →
      M8XorMaskEntriesOk scrn 4150 nn.toNat omask →
      (array (t := i8) c.pLitMark lmb ⋆ array (t := i32) c.pScratchBuf scrn ⋆
        (m8FullMemNoLmScr c s ⋆ R)) mn →
      wp Γ Q X (onDone omask) mn) :
    wp Γ Q X (m8XorNegScanExpr c.hdr c.pScratchBuf nn nl k_b otgt 4150#32 onDone) mp' := by
  let R' : Mem 64 → Prop := m8FullMemNoLmScr c s ⋆ R
  unfold m8XorNegScanExpr
  refine wp_loop_group (ts := [i32, i32])
    (fun remn (omask, n_idx, ()) mn => ∃ scrn : List (BitVec 32),
      scrn.length = c.scratch_cap ∧ n_idx.toNat ≤ nn.toNat ∧
      remn = nn.toNat - n_idx.toNat ∧
      (∀ idx < c.scratch_cap, (idx < 4150 ∨ 4166 ≤ idx) → scrn[idx]? = scrp'[idx]?) ∧
      M8XorMaskEntriesOk scrn 4150 nn.toNat omask ∧
      (array (t := i8) c.pLitMark lmb ⋆ array (t := i32) c.pScratchBuf scrn ⋆ R') mn)
    ?_ ?_
  · rintro Ln remn ⟨omask, n_idx, ⟨⟩⟩ mn hLn
      ⟨scrn, hsn, hn_le, rfl, hout_p, hom_ok, hmn⟩
    c0_hsplit
    · have hn_lt : n_idx.toNat < nn.toNat := hc
      clear hc
      c0_hsplit
      · clear hc
        have hn_sc : ((2001#32 + n_idx).setWidth 64).toNat < scrn.length := by
          rw [hsn, m6_zext32_toNat]; c0_bound
        have hn_eq : ((2001#32 + n_idx).setWidth 64).toNat = 2001 + n_idx.toNat := by
          rw [m6_zext32_toNat]; c0_bound
        let wn := scrn[((2001#32 + n_idx).setWidth 64).toNat]'hn_sc
        have hwn_orig : wn = s.scratch.scratch_buf[2001 + n_idx.toNat]?.getD 0#32 := by
          have h1 := hout_p (2001 + n_idx.toNat) (by omega) (Or.inl (by omega))
          have h2 := hscr_orig n_idx.toNat hn_lt
          have hi' : 2001 + n_idx.toNat < scrn.length := by rw [hsn]; omega
          rw [List.getElem?_eq_getElem hi'] at h1
          rw [← h1] at h2
          rw [← h2, Option.getD_some]
          exact (m6_getElem_congr hn_eq.symm hi' hn_sc).symm
        have hn1 : (n_idx + 1#32).toNat = n_idx.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32])
          (α := BitVec 32 × List (BitVec 32)) (fun x => (x.1, ()))
          (fun x mx => x.2.length = c.scratch_cap ∧
            (∀ idx < c.scratch_cap, (idx < 4150 ∨ 4166 ≤ idx) → x.2[idx]? = scrp'[idx]?) ∧
            M8XorMaskEntriesOk x.2 4150 nn.toNat x.1 ∧
            (array (t := i8) c.pLitMark lmb ⋆ array (t := i32) c.pScratchBuf x.2 ⋆ R') mx)
          (fun _ ⟨om', scrn'⟩ mx ⟨hsn', hout_p', hom', hmx⟩ => by
            c0_hsteps!
            exact hLn (nn.toNat - (n_idx + 1#32).toNat) (om', n_idx + 1#32, ()) mx (by omega)
              ⟨scrn', hsn', by omega, rfl, hout_p', hom', hmx⟩)
          (fun _ hJn' => by
            c0_hsplit
            · have hwn_c0 : wn = scrn[(2001 + n_idx.toNat) % 2 ^ 32]'(by
                  rw [Nat.mod_eq_of_lt (by omega), hsn]; omega) :=
                m6_getElem_congr (by rw [hn_eq, Nat.mod_eq_of_lt (by omega)]) _ _
              have hwn_nb : (wn &&& 0x80000000#32) = 0#32 := by rw [hwn_c0]; exact hc
              have hent_n := hn_ok n_idx.toNat hn_lt
              rw [← hwn_orig] at hent_n; unfold FullBveEntryOkW at hent_n
              rw [ite_eq_right (fun h => h hwn_nb)] at hent_n
              c0_hsteps_nogrp
              m8_call hPat
              refine fullBveXorPatM7Spec_intro
                (s := { s with
                  core := { s.core with lit_mark := lmb }
                  scratch := { s.scratch with scratch_buf := scrn } })
                rfl
                ⟨{ hdw0.1.core_ok with lit_mark_len := hlmb },
                  { hdw0.1.scratch_ok with scratch_buf_len := hsn }⟩
                { hdw0.2.1 with
                  arena := { hdw0.2.1.arena with len_ok := hdw0.2.1.arena.len_ok }
                  watches := hdw0.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                hent_n.1 hent_n.2 (Nat.le_trans (by decide) hk2) hk_le
                (by rw [m8_fullMem_lm_scr_iff]; exact hmn) ?_
              intro pat hpat
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32])
                (α := BitVec 32 × List (BitVec 32)) (fun x => (x.1, ()))
                (fun x mx => x.2.length = c.scratch_cap ∧
                  (∀ idx < c.scratch_cap, (idx < 4150 ∨ 4166 ≤ idx) → x.2[idx]? = scrp'[idx]?) ∧
                  M8XorMaskEntriesOk x.2 4150 nn.toNat x.1 ∧
                  (array (t := i8) c.pLitMark lmb ⋆ array (t := i32) c.pScratchBuf x.2 ⋆ R') mx)
                (fun _ p mx h => by c0_hsteps!; exact hJn' p mx h)
                (fun _ hJnm => by
                  c0_hsplit
                  · have hpat16 : pat.toNat < 16 := hc
                    c0_hsplit
                    · c0_hsplit
                      · have hdst_sc : ((4150#32 + pat).setWidth 64).toNat < scrn.length := by
                          rw [hsn, m6_zext32_toNat]; c0_bound
                        have hdst_eq : ((4150#32 + pat).setWidth 64).toNat = 4150 + pat.toNat := by
                          rw [m6_zext32_toNat]; c0_bound
                        c0_hsteps!
                        rw [m8_k6_set_congr hdst_eq rfl] at hm
                        have hsh : (1 : BitVec 32) <<< (pat.toNat % 32) = 1#32 <<< pat.toNat := by
                          rw [Nat.mod_eq_of_lt (by omega)]; rfl
                        rw [hsh]
                        refine hJnm (omask ||| 1#32 <<< pat.toNat,
                          scrn.set (4150 + pat.toNat) n_idx) _
                          ⟨by simp [hsn],
                           fun idx hidx hor => by
                             rw [List.getElem?_set_ne (by omega)]; exact hout_p idx hidx hor,
                           m8_xorMaskEntriesOk_set hom_ok (by rw [hsn]; omega) hpat16 hn_lt,
                           m8_sep_scr_lm_norm hm⟩
                      · c0_hsteps!; exact hJnm (omask, scrn) mn ⟨hsn, hout_p, hom_ok, hmn⟩
                    · c0_hsteps!; exact hJnm (omask, scrn) mn ⟨hsn, hout_p, hom_ok, hmn⟩
                  · c0_hsteps!; exact hJnm (omask, scrn) mn ⟨hsn, hout_p, hom_ok, hmn⟩)
            · c0_hsteps!; exact hJn' (omask, scrn) mn ⟨hsn, hout_p, hom_ok, hmn⟩)
      · exact honDone omask scrn mn hsn hout_p hom_ok hmn
    · exact honDone omask scrn mn hsn hout_p hom_ok hmn
  · intro Ln hLn; c0_hsteps!
    exact hLn nn.toNat (0#32, 0#32, ()) mp'
      ⟨scrp', hscp', Nat.zero_le _, rfl, fun _ _ _ => rfl, m8_xorMaskEntriesOk_zero _ _ _, hmp'⟩

/-- Parametric `Func.wp` proof for `full_bve_find_xor_m8`. -/
theorem full_bve_find_xor_m8_wp (Γ : Env)
    (hPat : ∀ a m Q X, fullBveXorPatM7Spec a m Q X →
      Γ "full_bve_xor_pat_m7" [i64, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, m8BveFindXorSpec a m Q X →
      Func.wp Γ full_bve_find_xor_m8_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s, R, rfl, hdw0, hsc16, hv_lt, hnp_le, hnn_le, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindXorSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hscr_len0 := hdw0.1.scratch_ok.scratch_buf_len
  have ⟨hpl_val, hnl_val⟩ := m8_pl_nl_eq (v := v) (by omega)
  unfold Func.wp full_bve_find_xor_m8_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32])
    (fun rem (lp, i, ()) mi => mi = m0 ∧ i.toNat ≤ np.toNat ∧ lp.toNat ≤ i.toNat ∧
      rem = np.toNat - i.toNat)
    ?_ ?_
  · rintro L1 rem1 ⟨lp, i, ⟨⟩⟩ m1 hL1 ⟨hm1, hi_le, hlp_le, rfl⟩
    subst m1
    c0_hsplit
    · have hi_lt : i.toNat < np.toNat := hc
      have hi_sc : (i.setWidth 64).toNat < s.scratch.scratch_buf.length := by
        rw [hscr_len0, m6_zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun lp' => lp'.toNat ≤ i.toNat + 1)
        ?_ ?_
      · rintro _ lp' hlp'
        c0_hsteps!
        exact hL1 (np.toNat - (i + 1#32).toNat) (lp', i + 1#32, ()) m0 (by omega)
          ⟨rfl, by omega, by rw [hi1]; exact hlp', rfl⟩
      · intro J1 hJ1
        c0_hsplit
        · c0_hsteps!; exact hJ1 (lp + 1#32) (by c0_bound)
        · c0_hsteps!; exact hJ1 lp (by omega)
    · c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32, i32])
        (fun rem2 (ln, j, ()) m2 => m2 = m0 ∧ j.toNat ≤ nn.toNat ∧ ln.toNat ≤ j.toNat ∧
          rem2 = nn.toNat - j.toNat)
        ?_ ?_
      · rintro L2 rem2 ⟨ln, j, ⟨⟩⟩ m2 hL2 ⟨hm2, hj_le, hln_le, rfl⟩
        subst m2
        c0_hsplit
        · have hj_lt : j.toNat < nn.toNat := hc
          have hj_sc : ((2001#32 + j).setWidth 64).toNat < s.scratch.scratch_buf.length := by
            rw [hscr_len0, m6_zext32_toNat]; c0_bound
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
            (fun ln' => ln'.toNat ≤ j.toNat + 1)
            ?_ ?_
          · rintro _ ln' hln'
            c0_hsteps!
            exact hL2 (nn.toNat - (j + 1#32).toNat) (ln', j + 1#32, ()) m0 (by omega)
              ⟨rfl, by omega, by rw [hj1]; exact hln', rfl⟩
          · intro J2 hJ2
            c0_hsplit
            · c0_hsteps!; exact hJ2 (ln + 1#32) (by c0_bound)
            · c0_hsteps!; exact hJ2 ln (by omega)
        · have hmul_nw : (lp.setWidth 64).toNat * (ln.setWidth 64).toNat < 2 ^ 64 := by
            rw [m6_zext32_toNat, m6_zext32_toNat]
            have : lp.toNat ≤ 2001 := by omega
            have : ln.toNat ≤ 2001 := by omega
            exact Nat.lt_of_le_of_lt (Nat.mul_le_mul ‹_› ‹_›) (by decide)
          c0_split
          · c0_hsteps!
            exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
              (fun _ _ _ => rfl) hm0
          next =>
          c0_split
          · c0_hsteps!
            exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
              (fun _ _ _ => rfl) hm0
          next =>
          c0_split
          · c0_hsteps!
            exact hQ false s.core.lit_mark s.scratch.scratch_buf m0 hdw0 hscr_len0
              (fun _ _ _ => rfl) hm0
          next =>
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem3 (i0, ()) mi => ∃ (lmi : List (BitVec 8)) (scri : List (BitVec 32)),
                      lmi.length = 2 * c.max_vars ∧
                      (∀ y < 2 * c.max_vars, lmi[y]?.getD 0#8 = 0#8) ∧
                      scri.length = c.scratch_cap ∧
                      (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                        scri[idx]? = s.scratch.scratch_buf[idx]?) ∧
                      i0.toNat ≤ np.toNat ∧ rem3 = np.toNat - i0.toNat ∧
                      (FullMem c { s with
                        core := { s.core with lit_mark := lmi }
                        scratch := { s.scratch with scratch_buf := scri } } ⋆ R) mi)
                    ?_ ?_
                  · rintro L3 rem3 ⟨i0, ⟨⟩⟩ mi hL3 ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len,
                      hscri_out, hi0_le, rfl, hmi⟩
                    have hdw_i := m8_fullDenseInvW_lm_scr hdw0 hlmi_len hlmi_z hscri_len
                    c0_hsplit
                    · have hi0_lt : i0.toNat < np.toNat := hc
                      have hi0_sc : (i0.setWidth 64).toNat < scri.length := by
                        rw [hscri_len, m6_zext32_toNat]; omega
                      let w0 := scri[(i0.setWidth 64).toNat]'hi0_sc
                      have hw0_orig : w0 = s.scratch.scratch_buf[i0.toNat]?.getD 0#32 := by
                        have hget := hscri_out i0.toNat (by omega) (Or.inl (by omega))
                        have hi0' : i0.toNat < scri.length := by rw [hscri_len]; omega
                        have hw0_c : w0 = scri[i0.toNat]'hi0' :=
                          m6_getElem_congr (m6_zext32_toNat i0) hi0_sc hi0'
                        rw [hw0_c, ← Option.getD_some (b := 0#32) (a := scri[i0.toNat]'hi0'),
                          ← List.getElem?_eq_getElem hi0', hget]
                      have hi0_1 : (i0 + 1#32).toNat = i0.toNat + 1 := by c0_bound
                      c0_hsteps_nogrp
                      refine wp_join0
                        (P := fun mn => ∃ (lmn : List (BitVec 8)) (scrn : List (BitVec 32)),
                          lmn.length = 2 * c.max_vars ∧
                          (∀ y < 2 * c.max_vars, lmn[y]?.getD 0#8 = 0#8) ∧
                          scrn.length = c.scratch_cap ∧
                          (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                            scrn[idx]? = s.scratch.scratch_buf[idx]?) ∧
                          (FullMem c { s with
                            core := { s.core with lit_mark := lmn }
                            scratch := { s.scratch with scratch_buf := scrn } } ⋆ R) mn)
                        ?_ ?_
                      · rintro _ mn ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out, hmn⟩
                        c0_hsteps!
                        exact hL3 (np.toNat - (i0 + 1#32).toNat) (i0 + 1#32, ()) mn (by omega)
                          ⟨lmn, scrn, hlmn_len, hlmn_z, hscrn_len, hscrn_out, by omega, rfl, hmn⟩
                      · intro _ hJ3
                        c0_hsplit
                        · have hw0_nb : (w0 &&& 0x80000000#32) = 0#32 := by
                            dsimp only [w0]; rw [m6_getElem_congr (m6_zext32_toNat i0)
                              (by rw [hscri_len, m6_zext32_toNat]; omega) hi0_sc]; exact hc
                          have hent_i0 := hp_ok i0.toNat hi0_lt
                          rw [← hw0_orig] at hent_i0; unfold FullBveEntryOkW at hent_i0
                          rw [ite_eq_right (fun h => h hw0_nb)] at hent_i0
                          have hwf_w0 := hdw0.2.1.arena.refs_wf w0.toNat hent_i0.1
                          have hw0_bd : w0.toNat + 3 + fullArenaClauseSizeCore s.core w0.toNat ≤
                              c.arena_cap := by
                            have := hwf_w0.2.2.1; have := hwf_w0.2.2.2.1; omega
                          have hw0_2ar : (w0.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                            rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, m6_zext32_toNat,
                              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                            omega
                          let sz := s.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw0_2ar
                          have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core w0.toNat := by
                            unfold sz fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem (by
                              rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                            exact congrArg BitVec.toNat (m6_getElem_congr (by
                              rw [BitVec.toNat_add, m6_zext32_toNat, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega)]) _ _)
                          c0_hsteps_nogrp
                          refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32,
                            i32])
                            (fun (ok_b, k_b, _, ()) mb =>
                              ∃ (lmb : List (BitVec 8)) (scrb : List (BitVec 32)),
                                lmb.length = 2 * c.max_vars ∧ k_b.toNat ≤ 4 ∧
                                scrb.length = c.scratch_cap ∧
                                (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                                  scrb[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                (∀ t < k_b.toNat, (scrb[4166 + t]?.getD 0#32).toNat <
                                  2 * s.core.cur_vars) ∧
                                (∀ y < 2 * c.max_vars, lmb[y]?.getD 0#8 ≠ 0#8 →
                                  ∃ t < k_b.toNat,
                                    y = (scrb[4166 + t]?.getD 0#32).toNat ∨
                                    y = ((scrb[4166 + t]?.getD 0#32) ^^^ 1#32).toNat) ∧
                                (FullMem c { s with
                                  core := { s.core with lit_mark := lmb }
                                  scratch := { s.scratch with scratch_buf := scrb } } ⋆ R) mb)
                            (fun rem_u (k_u, u, ()) mu =>
                              ∃ (lmu : List (BitVec 8)) (scru : List (BitVec 32)),
                                lmu.length = 2 * c.max_vars ∧ k_u.toNat ≤ 4 ∧ u.toNat ≤ sz.toNat ∧
                                rem_u = sz.toNat - u.toNat ∧ scru.length = c.scratch_cap ∧
                                (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                                  scru[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                (∀ t < k_u.toNat, (scru[4166 + t]?.getD 0#32).toNat <
                                  2 * s.core.cur_vars) ∧
                                (∀ y < 2 * c.max_vars, lmu[y]?.getD 0#8 ≠ 0#8 →
                                  ∃ t < k_u.toNat,
                                    y = (scru[4166 + t]?.getD 0#32).toNat ∨
                                    y = ((scru[4166 + t]?.getD 0#32) ^^^ 1#32).toNat) ∧
                                (FullMem c { s with
                                  core := { s.core with lit_mark := lmu }
                                  scratch := { s.scratch with scratch_buf := scru } } ⋆ R) mu)
                            ?_ ?_ ?_
                          · rintro _ ⟨ok_b, k_b, _, ⟨⟩⟩ mb
                              ⟨lmb, scrb, hlmb, hk_le, hscb, houtb, hbdb, hnzb, hmb⟩
                            let R' : Mem 64 → Prop := m8FullMemNoLmScr c s ⋆ R
                            have hmb' : (array (t := i8) c.pLitMark lmb ⋆
                                array (t := i32) c.pScratchBuf scrb ⋆ R') mb := by
                              rw [m8_fullMem_lm_scr_iff] at hmb; exact hmb
                            clear hmb
                            c0_hsteps_nogrp
                            refine wp_join0
                              (P := fun mf => ∃ (lmf : List (BitVec 8)) (scrf : List (BitVec 32)),
                                lmf.length = 2 * c.max_vars ∧
                                (∀ y < 2 * c.max_vars, lmf[y]?.getD 0#8 = 0#8) ∧
                                scrf.length = c.scratch_cap ∧
                                (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                                  scrf[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                (array (t := i8) c.pLitMark lmf ⋆
                                  array (t := i32) c.pScratchBuf scrf ⋆ R') mf)
                              (fun _ mf ⟨lmf, scrf, h1, h2, h3, h4, hm⟩ => by
                                c0_hsteps!; exact hJ3 mf ⟨lmf, scrf, h1, h2, h3, h4, by
                                  rw [m8_fullMem_lm_scr_iff]; exact hm⟩)
                              (fun _ hJfin => by
                                c0_hsteps_nogrp
                                refine wp_join0 (P := fun me => me = mb)
                                  (fun _ me hme => by
                                    subst me
                                    c0_hsteps_nogrp
                                    refine m8_xor_clean_lm_wp Γ Q X c s scrb R' k_b lmb mb _
                                      hscb hsc16 hk_le hcv_le hlmb hbdb hnzb hmb'
                                      (fun lmc mc hlmc hclr_c hmc => by
                                        c0_hsteps!; exact hJfin mc ⟨lmc, scrb, hlmc, hclr_c, hscb,
                                          houtb, hmc⟩))
                                  (fun _ hJelse => by
                                    clear hc
                                    c0_hsplit
                                    · -- `ok && k_b >= 2 && k_b <= 4`? Check `(2 <= k_b)`!
                                      clear hc
                                      c0_hsplit
                                      · have hk2 : 2 ≤ k_b.toNat := hc
                                        clear hc
                                        c0_hsplit
                                        · clear hc
                                          -- Now `2 ≤ k_b ≤ 4`, `etgt`, `otgt`, `tmp_e[0] = i0`,
                                            -- `p_idx` loop, `n_idx` loop, clear `lm`, check match!
                                          c0_hsteps_nogrp
                                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                            (fun x => (x, ())) (fun _ => True)
                                            (fun _ etgt _ => by
                                              c0_hsteps_nogrp
                                              refine wp_join_state_pure (ts := [i32]) (α :=
                                                BitVec 32)
                                                (fun x => (x, ())) (fun _ => True)
                                                (fun _ otgt _ => by
                                              have h4134 := m8_scr_imm_lt hscb hsc16 (k :=
                                                4134) (by decide)
                                              let scrb0 := scrb.set 4134 i0
                                              have hscb0 : scrb0.length = c.scratch_cap := by
                                                simp [scrb0, hscb]
                                              have houtb0 : ∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                4170 ≤ idx) →
                                                  scrb0[idx]? = s.scratch.scratch_buf[idx]? :=
                                                    fun idx hidx hor => by
                                                dsimp only [scrb0]; rw [List.getElem?_set_ne (by
                                                  omega)]
                                                exact houtb idx hidx hor
                                              have hbdb0 : ∀ t < k_b.toNat,
                                                (scrb0[4166 + t]?.getD 0#32).toNat <
                                                  2 * s.core.cur_vars := fun t ht => by
                                                dsimp only [scrb0]; rw [List.getElem?_set_ne (by
                                                  omega)]
                                                exact hbdb t ht
                                              have hnzb0 : ∀ y < 2 * c.max_vars,
                                                lmb[y]?.getD 0#8 ≠ 0#8 →
                                                  ∃ t < k_b.toNat,
                                                    y = (scrb0[4166 + t]?.getD 0#32).toNat ∨
                                                    y = ((scrb0[4166 +
                                                      t]?.getD 0#32) ^^^ 1#32).toNat :=
                                                fun y hy hnzy => by
                                                  obtain ⟨t, ht, hyeq⟩ := hnzb y hy hnzy
                                                  refine ⟨t, ht, ?_⟩
                                                  dsimp only [scrb0]
                                                  rw [List.getElem?_set_ne (by omega)]
                                                  exact hyeq
                                              c0_hsteps_nogrp
                                              -- Positive scan `p_idx < np && emask != etgt`
                                              refine wp_loop_group (ts := [i32, i32])
                                                (fun remp (emask, p_idx, ()) mp =>
                                                  ∃ scrp : List (BitVec 32),
                                                  scrp.length = c.scratch_cap ∧
                                                    p_idx.toNat ≤ np.toNat ∧
                                                  remp = np.toNat - p_idx.toNat ∧
                                                  (∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                    4150 ≤ idx) →
                                                    scrp[idx]? = scrb0[idx]?) ∧
                                                  M8XorMaskEntriesOk scrp 4134 np.toNat emask ∧
                                                  (array (t := i8) c.pLitMark lmb ⋆
                                                    array (t := i32) c.pScratchBuf scrp ⋆ R') mp)
                                                ?_ ?_
                                              · rintro Lp remp ⟨emask, p_idx, ⟨⟩⟩ mp hLp
                                                  ⟨scrp, hscp, hp_le, rfl, houtp, hpm_ok, hmp⟩
                                                c0_hsteps_nogrp
                                                refine wp_join0
                                                  (fun mp' => ∃ scrp' : List (BitVec 32),
                                                    scrp'.length = c.scratch_cap ∧
                                                    (∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                      4150 ≤ idx) →
                                                      scrp'[idx]? = scrb0[idx]?) ∧
                                                    M8XorMaskEntriesOk scrp' 4134 np.toNat emask ∧
                                                    (array (t := i8) c.pLitMark lmb ⋆
                                                      array (t := i32) c.pScratchBuf scrp' ⋆
                                                        R') mp')
                                                  (fun _ mp' ⟨scrp', hscp', houtp', hpm_ok',
                                                    hmp'⟩ => by
                                                    c0_hsteps_nogrp
                                                    refine wp_join_state (ts := [i32])
                                                      (α := BitVec 32 × List (BitVec 32)) (fun x =>
                                                        (x.1, ()))
                                                      (fun x mx => x.2.length = c.scratch_cap ∧
                                                        (∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                          4166 ≤ idx) →
                                                          x.2[idx]? = scrb0[idx]?) ∧
                                                        M8XorMaskEntriesOk x.2 4134 np.toNat emask ∧
                                                        M8XorMaskEntriesOk x.2 4150 nn.toNat x.1 ∧
                                                        (array (t := i8) c.pLitMark lmb ⋆
                                                          array (t := i32) c.pScratchBuf x.2 ⋆
                                                            R') mx)
                                                      (fun _ ⟨omask, scrn⟩ mn ⟨hsn, houtn, hpm_n,
                                                        hom_n, hmn⟩ => by
                                                        have hbd_n : ∀ t < k_b.toNat,
                                                          (scrn[4166 + t]?.getD 0#32).toNat <
                                                            2 * s.core.cur_vars := fun t ht => by
                                                          rw [houtn (4166 + t) (by omega)
                                                            (Or.inr (by omega))]
                                                          exact hbdb0 t ht
                                                        have hnz_n : ∀ y < 2 * c.max_vars,
                                                          lmb[y]?.getD 0#8 ≠ 0#8 →
                                                            ∃ t < k_b.toNat,
                                                              y = (scrn[4166 +
                                                                t]?.getD 0#32).toNat ∨
                                                              y = ((scrn[4166 +
                                                                t]?.getD 0#32) ^^^ 1#32).toNat :=
                                                                  fun y hy hnzy => by
                                                          obtain ⟨t, ht, hyeq⟩ := hnzb0 y hy hnzy
                                                          refine ⟨t, ht, ?_⟩
                                                          rw [houtn (4166 + t) (by omega)
                                                            (Or.inr (by omega))]
                                                          exact hyeq
                                                        c0_hsteps_nogrp
                                                        refine m8_xor_clean_lm_wp Γ Q X c s scrn R'
                                                          k_b lmb mn _
                                                          hsn hsc16 hk_le hcv_le hlmb hbd_n hnz_n
                                                            hmn
                                                          (fun lmc mc hlmc hclr_c hmc => by
                                                            c0_hsplit
                                                            · have hem_eq : emask = etgt := hc
                                                              clear hc
                                                              c0_hsplit
                                                              · have hom_eq : omask = otgt := hc
                                                                c0_hsteps_nogrp
                                                                have hmc_s : (array (t :=
                                                                  i32) c.pScratchBuf scrn ⋆
                                                                    (array (t :=
                                                                      i8) c.pLitMark lmc ⋆
                                                                        R')) mc := by
                                                                  have := hmc; rw [sep_comm (array
                                                                    (t := i8) c.pLitMark lmc),
                                                                    sep_assoc] at this; exact this
                                                                exact m8_xor_commit_wp Γ Q X c scrn
                                                                  _ k_b etgt otgt
                                                                  np nn mc hsn hsc16 hk_le hnp_le
                                                                    hnn_le
                                                                  (hem_eq ▸ hpm_n) (hom_eq ▸ hom_n)
                                                                    hmc_s
                                                                  (fun scr' m' hsc' hout' hm' => by
                                                                    refine hQ true lmc scr' m'
                                                                      (m8_fullDenseInvW_lm_scr hdw0
                                                                        hlmc hclr_c hsc')
                                                                      hsc' (fun idx hidx hor => by
                                                                        rw [hout' idx hidx (by
                                                                          omega),
                                                                          houtn idx hidx (by omega)]
                                                                        exact houtb0 idx hidx hor)
                                                                          ?_
                                                                    rw [m8_fullMem_lm_scr_iff]
                                                                    rw [sep_comm (array (t :=
                                                                      i8) c.pLitMark lmc),
                                                                      sep_assoc]; exact hm')
                                                              · c0_hsteps!; exact hJfin mc ⟨lmc,
                                                                  scrn, hlmc, hclr_c, hsn,
                                                                  fun idx hidx hor => by
                                                                    rw [houtn idx hidx (by omega)]
                                                                    exact houtb0 idx hidx hor,
                                                                  hmc⟩
                                                            · c0_hsteps!; exact hJfin mc ⟨lmc,
                                                                scrn, hlmc, hclr_c, hsn,
                                                                fun idx hidx hor => by
                                                                  rw [houtn idx hidx (by omega)]
                                                                  exact houtb0 idx hidx hor,
                                                                hmc⟩))
                                                      (fun Jn hJn => by
                                                        c0_hsplit
                                                        · c0_hsteps_nogrp
                                                          refine m8_xor_neg_scan_wp Γ Q X c F0 F_cur
                                                            s
                                                            lmb scrp' R nn (v <<< (1 : Nat) |||
                                                              1#32)
                                                            k_b otgt mp'
                                                            (fun om => Expr.jump Jn (Arg.var om,
                                                              ()))
                                                            hPat hdw0 hlmb hscp'
                                                            hnn_le hsc16 hk2 hk_le
                                                            (fun j hj => by
                                                              rw [hnl_val]; exact hn_ok j hj)
                                                            (fun j hj =>
                                                              (houtp' (2001 +
                                                                j) (by omega) (Or.inl (by
                                                                  omega))).trans
                                                                (houtb0 (2001 +
                                                                  j) (by omega) (Or.inl (by
                                                                    omega))))
                                                            hmp' ?_
                                                          intro omask scrn mn hsn hout_p hom_ok hmn
                                                          have houtn : ∀ idx < c.scratch_cap,
                                                              (idx < 4002 ∨ 4166 ≤ idx) →
                                                              scrn[idx]? = scrb0[idx]? :=
                                                                fun idx hidx hor =>
                                                            (hout_p idx hidx (by omega)).trans
                                                              (houtp' idx hidx (by omega))
                                                          have hpm_ok_n : M8XorMaskEntriesOk scrn
                                                            4134 np.toNat emask :=
                                                            ⟨hpm_ok'.1, fun t ht hb => by
                                                              rw [hout_p (4134 +
                                                                t) (by omega) (Or.inl (by omega))]
                                                              exact hpm_ok'.2 t ht hb⟩
                                                          c0_hsteps!
                                                          exact hJn (omask, scrn) mn
                                                            ⟨hsn, houtn, hpm_ok_n, hom_ok, hmn⟩
                                                        · c0_hsteps!; exact hJn (0#32, scrp') mp'
                                                            ⟨hscp', fun idx hidx hor =>
                                                              houtp' idx hidx (by omega),
                                                             hpm_ok', m8_xorMaskEntriesOk_zero _ _
                                                               _, hmp'⟩))
                                                  (fun _ hJexp => by
                                                    c0_hsplit
                                                    · have hp_lt : p_idx.toNat < np.toNat := hc
                                                      clear hc
                                                      c0_hsplit
                                                      · clear hc
                                                        have hp_sc : (p_idx.setWidth 64).toNat <
                                                          scrp.length := by
                                                          rw [hscp, m6_zext32_toNat]; omega
                                                        let wp :=
                                                          scrp[(p_idx.setWidth 64).toNat]'hp_sc
                                                        have hwp_orig : wp =
                                                          s.scratch.scratch_buf[p_idx.toNat]?.getD
                                                            0#32 := by
                                                          have h1 :=
                                                            houtp p_idx.toNat (by omega) (Or.inl (by
                                                              omega))
                                                          have h2 :=
                                                            houtb0 p_idx.toNat (by omega) (Or.inl
                                                              (by omega))
                                                          have hi' : p_idx.toNat < scrp.length :=
                                                            by rw [hscp]; omega
                                                          rw [List.getElem?_eq_getElem hi'] at h1
                                                          rw [← h1] at h2
                                                          rw [← h2, Option.getD_some]
                                                          exact (m6_getElem_congr (m6_zext32_toNat
                                                            p_idx).symm hi' hp_sc).symm
                                                        have hp1 : (p_idx + 1#32).toNat =
                                                          p_idx.toNat + 1 := by c0_bound
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [i32])
                                                          (α := BitVec 32 × List (BitVec 32)) (fun
                                                            x => (x.1, ()))
                                                          (fun x mx => x.2.length = c.scratch_cap ∧
                                                            (∀ idx < c.scratch_cap, (idx < 4002 ∨
                                                              4150 ≤ idx) →
                                                              x.2[idx]? = scrb0[idx]?) ∧
                                                            M8XorMaskEntriesOk x.2 4134 np.toNat x.1
                                                              ∧
                                                            (array (t := i8) c.pLitMark lmb ⋆
                                                              array (t := i32) c.pScratchBuf x.2 ⋆
                                                                R') mx)
                                                          (fun _ ⟨em', scrp'⟩ mx ⟨hscp', houtp',
                                                            hpm', hmx⟩ => by
                                                            c0_hsteps!
                                                            exact hLp (np.toNat - (p_idx +
                                                              1#32).toNat) (em', p_idx + 1#32, ())
                                                              mx (by omega) ⟨scrp', hscp',
                                                                by omega, rfl, houtp', hpm', hmx⟩)
                                                          (fun _ hJp => by
                                                            c0_hsplit
                                                            rotate_left
                                                            · c0_hsteps!; exact hJp (emask,
                                                                scrp) mp ⟨hscp, houtp, hpm_ok, hmp⟩
                                                            c0_hsplit
                                                            rotate_left
                                                            · c0_hsteps!; exact hJp (emask,
                                                                scrp) mp ⟨hscp, houtp, hpm_ok, hmp⟩
                                                            have hwp_nb : (wp &&& 0x80000000#32) =
                                                              0#32 := by
                                                              dsimp only [wp]
                                                              rw [m6_getElem_congr (m6_zext32_toNat
                                                                p_idx)
                                                                (by
                                                                  rw [hscp, m6_zext32_toNat]; omega)
                                                                (by rw [hscp]; omega)]
                                                              exact hc
                                                            have hent_p := hp_ok p_idx.toNat hp_lt
                                                            rw [← hwp_orig] at hent_p
                                                            unfold FullBveEntryOkW at hent_p
                                                            rw [ite_eq_right (fun h =>
                                                              h hwp_nb)] at hent_p
                                                            c0_hsteps_nogrp
                                                            m8_call hPat
                                                            refine fullBveXorPatM7Spec_intro
                                                              (s := { s with
                                                                core := { s.core with lit_mark :=
                                                                  lmb }
                                                                scratch :=
                                                                  { s.scratch with scratch_buf :=
                                                                    scrp } })
                                                              rfl
                                                              ⟨{ hdw0.1.core_ok with
                                                                lit_mark_len := hlmb },
                                                                { hdw0.1.scratch_ok with
                                                                  scratch_buf_len := hscp }⟩
                                                              { hdw0.2.1 with
                                                                arena := { hdw0.2.1.arena with
                                                                  len_ok := hdw0.2.1.arena.len_ok }
                                                                watches :=
                                                                  hdw0.2.1.watches.with_wstk rfl rfl
                                                                    rfl rfl rfl (fun _ hr => hr) }
                                                              hent_p.1 hent_p.2 (Nat.le_trans (by
                                                                decide) hk2) hk_le
                                                              (by
                                                                rw [m8_fullMem_lm_scr_iff]
                                                                exact hmp) ?_
                                                            intro pat hpat
                                                            c0_hsteps_nogrp
                                                            refine wp_join_state (ts := [i32])
                                                              (α := BitVec 32 × List (BitVec 32))
                                                                (fun x => (x.1, ()))
                                                              (fun x mx => x.2.length =
                                                                c.scratch_cap ∧
                                                                (∀ idx < c.scratch_cap,
                                                                  (idx < 4002 ∨ 4150 ≤ idx) →
                                                                  x.2[idx]? = scrb0[idx]?) ∧
                                                                M8XorMaskEntriesOk x.2 4134 np.toNat
                                                                  x.1 ∧
                                                                (array (t := i8) c.pLitMark lmb ⋆
                                                                  array (t :=
                                                                    i32) c.pScratchBuf x.2 ⋆ R') mx)
                                                              (fun _ p mx h => by
                                                                c0_hsteps!; exact hJp p mx h)
                                                              (fun _ hJpm => by
                                                                c0_hsplit
                                                                · have hpat16 : pat.toNat < 16 := hc
                                                                  c0_hsplit
                                                                  · c0_hsplit
                                                                    · have hdst_sc : ((4134#32 +
                                                                        pat).setWidth 64).toNat <
                                                                          scrp.length := by
                                                                        rw [hscp,
                                                                          m6_zext32_toNat]; c0_bound
                                                                      have hdst_eq : (((4134 :
                                                                        BitVec 32) +
                                                                          pat).setWidth 64).toNat =
                                                                            4134 + pat.toNat := by
                                                                        rw [m6_zext32_toNat]
                                                                        c0_bound
                                                                      c0_hsteps!
                                                                      rw [m8_k6_set_congr hdst_eq
                                                                        rfl] at hm
                                                                      have hsh : (1 : BitVec 32) <<<
                                                                        (pat.toNat % 32) =
                                                                          1#32 <<< pat.toNat := by
                                                                        rw [Nat.mod_eq_of_lt (by
                                                                          omega)]; rfl
                                                                      rw [hsh]
                                                                      refine hJpm (emask |||
                                                                        1#32 <<< pat.toNat,
                                                                        scrp.set (4134 +
                                                                          pat.toNat) p_idx) _
                                                                        ⟨by simp [hscp],
                                                                          fun idx hidx hor => by
                                                                          rw [List.getElem?_set_ne
                                                                            (by omega)]
                                                                          exact houtp idx hidx hor,
                                                                         m8_xorMaskEntriesOk_set
                                                                           hpm_ok (by
                                                                             rw [hscp]; omega)
                                                                           hpat16 hp_lt,
                                                                         m8_sep_scr_lm_norm hm⟩
                                                                    · c0_hsteps!; exact hJpm
                                                                        (emask, scrp) mp ⟨hscp,
                                                                          houtp, hpm_ok, hmp⟩
                                                                  · c0_hsteps!; exact hJpm (emask,
                                                                      scrp) mp ⟨hscp, houtp,
                                                                        hpm_ok, hmp⟩
                                                                · c0_hsteps!; exact hJpm (emask,
                                                                    scrp) mp ⟨hscp, houtp, hpm_ok,
                                                                      hmp⟩))
                                                      · c0_hsteps!; exact hJexp mp ⟨scrp, hscp,
                                                          houtp, hpm_ok, hmp⟩
                                                    · c0_hsteps!; exact hJexp mp ⟨scrp, hscp,
                                                        houtp, hpm_ok, hmp⟩)
                                              · intro Lp hLp
                                                have h4134_sc : 4134 < scrb0.length := by
                                                  rw [hscb0]; omega
                                                c0_hsteps!
                                                change (array (t := i32) c.pScratchBuf scrb0 ⋆
                                                  (array (t := i8) c.pLitMark lmb ⋆ (R' ⋆
                                                    emp))) m at hm
                                                exact hLp np.toNat (1#32, 0#32, ()) _
                                                  ⟨scrb0, hscb0, Nat.zero_le _, rfl, fun _ _ _ =>
                                                    rfl,
                                                   by
                                                     have hinit :=
                                                       m8_xorMaskEntriesOk_init (base :=
                                                         4134) (lim := np.toNat) (idx :=
                                                           i0) (scr := scrb) (by
                                                             rw [hscb]; omega) hi0_lt
                                                     simpa only [scrb0] using hinit,
                                                   m8_sep_scr_lm_norm hm⟩)
                                                (fun _ h => by
                                                  c0_hsplit
                                                  · c0_hsteps!; exact h _ trivial
                                                  · refine wp_join_state_pure (ts := [i32]) (α :=
                                                      BitVec 32)
                                                      (fun x => (x, ())) (fun _ => True)
                                                      (fun _ x _ => by
                                                        c0_hsteps!; exact h x trivial)
                                                      (fun _ hi => by
                                                        c0_hsplit
                                                        · c0_hsteps!; exact hi _ trivial
                                                        · c0_hsteps!; exact hi _ trivial)))
                                            (fun _ h => by
                                              c0_hsplit
                                              · c0_hsteps!; exact h _ trivial
                                              · refine wp_join_state_pure (ts := [i32]) (α :=
                                                  BitVec 32)
                                                  (fun x => (x, ())) (fun _ => True)
                                                  (fun _ x _ => by c0_hsteps!; exact h x trivial)
                                                  (fun _ hi => by
                                                    c0_hsplit
                                                    · c0_hsteps!; exact hi _ trivial
                                                    · c0_hsteps!; exact hi _ trivial))
                                        · c0_hsteps!; exact hJelse mb rfl
                                      · c0_hsteps!; exact hJelse mb rfl
                                    · c0_hsteps!; exact hJelse mb rfl))
                          · -- Inner loop (`u < sz`) for collecting XOR vars into `scr[4166..4170)`
                            rintro Bu Lu rem_u ⟨k_u, u, ⟨⟩⟩ mu hBu hLu
                              ⟨lmu, scru, hlmu, hku_le, hu_le, rfl, hscu, houtu, hbdu, hnzu, hmu⟩
                            c0_hsplit
                            · have hu_lt : u.toNat < sz.toNat := hc
                              have hu_ar : (w0.setWidth 64 + 3#64 + u.setWidth 64).toNat <
                                s.core.arena.length := by
                                rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
                              let l := s.core.arena[(w0.setWidth 64 + 3#64 +
                                u.setWidth 64).toNat]'hu_ar
                              have hl_mem : l.toNat ∈ fullArenaClauseLitsCore s.core w0.toNat := by
                                rw [mem_fullArenaClauseLitsCore_iff (by
                                  rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                                exact ⟨u.toNat, by omega,
                                  congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                              have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                                hdw0.2.1.arena.lits_lt w0.toNat hent_i0.1 hent_i0.2 _ hl_mem
                              have hl_v : (l.setWidth 64).toNat < s.core.vals.length := by
                                rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                              have hl_lm : (l.setWidth 64).toNat < lmu.length := by
                                rw [hlmu, m6_zext32_toNat]; omega
                              have hu1 : (u + 1#32).toNat = u.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [.bool, i32]) (α := Bool × BitVec 32)
                                (fun x => (x.1, x.2, ()))
                                (fun (_, k') mu' =>
                                  ∃ (lmu' : List (BitVec 8)) (scru' : List (BitVec 32)),
                                  lmu'.length = 2 * c.max_vars ∧ k'.toNat ≤ 4 ∧
                                  scru'.length = c.scratch_cap ∧
                                  (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                                    scru'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                  (∀ t < k'.toNat, (scru'[4166 + t]?.getD 0#32).toNat <
                                    2 * s.core.cur_vars) ∧
                                  (∀ y < 2 * c.max_vars, lmu'[y]?.getD 0#8 ≠ 0#8 →
                                    ∃ t < k'.toNat,
                                      y = (scru'[4166 + t]?.getD 0#32).toNat ∨
                                      y = ((scru'[4166 + t]?.getD 0#32) ^^^ 1#32).toNat) ∧
                                  (FullMem c { s with
                                    core := { s.core with lit_mark := lmu' }
                                    scratch := { s.scratch with scratch_buf := scru' } } ⋆ R) mu')
                                (fun _ ⟨ok', k'⟩ mu' ⟨lmu', scru', hl', hk', hsc', hout', hbd',
                                  hnz', hm'⟩ => by
                                  c0_hsteps!
                                  exact hLu (sz.toNat - (u + 1#32).toNat) (k', u + 1#32,
                                    ()) mu' (by omega)
                                    ⟨lmu', scru', hl', hk', by omega, rfl, hsc', hout', hbd', hnz',
                                      hm'⟩)
                                (fun Ju hJu => by
                                  c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps!; exact hBu (false, k_u, u, ()) mu
                                        ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu, hnzu, hmu⟩
                                    · c0_hsteps_nogrp
                                      refine wp_join_state (ts := [.bool, i32]) (α :=
                                        Bool × BitVec 32)
                                        (fun x => (x.1, x.2, ()))
                                        (fun (_, k') mu' =>
                                          ∃ (lmu' : List (BitVec 8)) (scru' : List (BitVec 32)),
                                          lmu'.length = 2 * c.max_vars ∧ k'.toNat ≤ 4 ∧
                                          scru'.length = c.scratch_cap ∧
                                          (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4170 ≤ idx) →
                                            scru'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                          (∀ t < k'.toNat, (scru'[4166 + t]?.getD 0#32).toNat <
                                            2 * s.core.cur_vars) ∧
                                          (∀ y < 2 * c.max_vars, lmu'[y]?.getD 0#8 ≠ 0#8 →
                                            ∃ t < k'.toNat,
                                              y = (scru'[4166 + t]?.getD 0#32).toNat ∨
                                              y = ((scru'[4166 + t]?.getD 0#32) ^^^ 1#32).toNat) ∧
                                          (FullMem c { s with
                                            core := { s.core with lit_mark := lmu' }
                                            scratch := { s.scratch with scratch_buf := scru' } } ⋆
                                              R) mu')
                                        (fun _ ⟨ok', k'⟩ mu' hs' => by
                                          c0_hsteps!; exact hJu (ok', k') mu' hs')
                                        (fun Jm hJm => by
                                          c0_hsplit
                                          · c0_hsplit
                                            · c0_hsteps!; exact hBu (false, k_u, u, ()) mu
                                                ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu, hnzu,
                                                  hmu⟩
                                            · c0_hsplit
                                              · c0_hsteps!; exact hBu (false, k_u, u, ()) mu
                                                  ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu,
                                                    hnzu, hmu⟩
                                              · c0_hsplit
                                                · c0_hsteps!; exact hBu (false, k_u, u, ()) mu
                                                    ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu,
                                                      hnzu, hmu⟩
                                                · have hku4 : k_u.toNat < 4 := by c0_bound
                                                  have hl1_lt := (m8_bv32_xor1_lt l hl_lt).2
                                                  have hl1_lm : ((l ^^^ 1#32).setWidth 64).toNat <
                                                    lmu.length := by
                                                    rw [hlmu, m6_zext32_toNat]; omega
                                                  have hdst_sc : ((4166#32 +
                                                    k_u).setWidth 64).toNat < scru.length := by
                                                    rw [hscu, m6_zext32_toNat]; c0_bound
                                                  have hdst_eq : ((4166#32 +
                                                    k_u).setWidth 64).toNat = 4166 + k_u.toNat := by
                                                    rw [m6_zext32_toNat]; c0_bound
                                                  have hku1 : (k_u + 1#32).toNat = k_u.toNat + 1 :=
                                                    by c0_bound
                                                  have hl1_set : ((l ^^^ 1#32).setWidth 64).toNat <
                                                      (lmu.set (l.setWidth 64).toNat
                                                        (BitVec.setWidth 8 (2#32 +
                                                          (k_u <<< (1 : Nat))))).length := by
                                                    rw [List.length_set]; exact hl1_lm
                                                  c0_hsteps!
                                                  rw [hdst_eq] at hm
                                                  refine hJm (true, k_u + 1#32) _
                                                    ⟨_, _, by simp [hlmu], by omega, by simp [hscu],
                                                     fun idx hidx hor => by
                                                       rw [List.getElem?_set_ne (by omega)]; exact
                                                         houtu idx hidx hor,
                                                     fun t ht => by
                                                       by_cases htk : t = k_u.toNat
                                                       · subst htk
                                                         rw [List.getElem?_set_self (by
                                                           rw [hscu]; omega), Option.getD_some]
                                                         exact hl_lt
                                                       · rw [List.getElem?_set_ne (by omega)]; exact
                                                           hbdu t (by omega),
                                                     fun y hy hyn => by
                                                       by_cases hyl : y = l.toNat
                                                       · exact ⟨k_u.toNat, by omega, Or.inl (by
                                                           rw [List.getElem?_set_self (by
                                                             rw [hscu]; omega), Option.getD_some]
                                                           exact hyl)⟩
                                                       · by_cases hyl1 : y = (l ^^^ 1#32).toNat
                                                         · exact ⟨k_u.toNat, by omega, Or.inr (by
                                                             rw [List.getElem?_set_self (by
                                                               rw [hscu]; omega), Option.getD_some]
                                                             exact hyl1)⟩
                                                         · rw [List.getElem?_set_ne (by
                                                             rw [m6_zext32_toNat]; exact Ne.symm
                                                               hyl1),
                                                             List.getElem?_set_ne (by
                                                               rw [m6_zext32_toNat]; exact Ne.symm
                                                                 hyl)] at hyn
                                                           obtain ⟨t, ht, hyeq⟩ := hnzu y hy hyn
                                                           exact ⟨t, by omega,
                                                             by rw [List.getElem?_set_ne (by
                                                               omega)]; exact hyeq⟩,
                                                     hm⟩
                                          · c0_hsteps!; exact hJm (true, k_u) mu
                                              ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu, hnzu,
                                                hmu⟩)
                                  · c0_hsteps!; exact hJu (true, k_u) mu
                                      ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu, hnzu, hmu⟩)
                            · c0_hsteps!; exact hBu (true, k_u, u, ()) mu
                                ⟨lmu, scru, hlmu, hku_le, hscu, houtu, hbdu, hnzu, hmu⟩
                          · intro Bu Lu hBu hLu; c0_hsteps!
                            exact hLu sz.toNat (0#32, 0#32, ()) mi
                              ⟨lmi, scri, hlmi_len, Nat.zero_le _, Nat.zero_le _, rfl, hscri_len,
                                hscri_out,
                               fun _ ht => absurd ht (Nat.not_lt_zero _),
                               fun y hy hnz => absurd (hlmi_z y hy) hnz, hmi⟩
                        · c0_hsteps!; exact hJ3 mi ⟨lmi, scri, hlmi_len, hlmi_z, hscri_len,
                            hscri_out, hmi⟩
                    · have hdw_e := hdw_i.toDense
                      c0_hsteps!; exact hQ false lmi scri mi hdw_i hscri_len hscri_out hmi
                  · intro L3 hL3; c0_hsteps!
                    exact hL3 np.toNat (0#32, ()) m0
                      ⟨s.core.lit_mark, s.scratch.scratch_buf, hdw0.1.core_ok.lit_mark_len,
                       hdw0.2.2.1.2, hscr_len0, fun _ _ _ => rfl, Nat.zero_le _, rfl, hm0⟩
      · intro L2 hL2; c0_hsteps!
        exact hL2 nn.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 np.toNat (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl⟩


end LeanQbe.T.Examples.Kissat.FullM8CoreParity
