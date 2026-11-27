/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.WpHelpers

/-!
# Kissat Gates WP Proofs — M8 Ternary & ITE (`match_tern_m8`, `find_ite_side_m8`, `find_ite_m8`)

`CanonicalEnv`-clean `Func.wp` proofs for `full_bve_match_tern_m8`,
`full_bve_find_ite_side_m8`, and `full_bve_find_ite_m8`
(`0` legacy `Full*` imports; every decl `<= 450` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Gates
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "gates_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "m8_ite_neg_join" inv:term : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ())) ($inv) ?_
      (fun _ hJ => by
        c0_hsplit <;> (c0_hsteps!; exact hJ _ (by first | (simp; done) | (split <;> simp_all))))))

local macro "m8_ite_pick_step" hPrev:ident : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
      (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
      (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2, ())) (fun _ => True)
      (fun _ p _ => by c0_hsteps!; exact $hPrev p trivial) ?_))

public section

/-! ## 1. `full_bve_match_tern_m8` -/

/-- Canonical `Func.wp` proof for `full_bve_match_tern_m8`. -/
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
          rw [hscj, zext32_toNat]; c0_bound
        have hwj_orig :
            scr_j[((opp_off + j).setWidth 64).toNat]'hoj_sc =
              s0.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := by
          have hoj_eq : ((opp_off + j).setWidth 64).toNat = opp_off.toNat + j.toNat := by
            rw [zext32_toNat]; c0_bound
          have hget := hout_j (opp_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
          have hoj' : opp_off.toNat + j.toNat < scr_j.length := by omega
          rw [List.getElem?_eq_getElem hoj'] at hget
          rw [← hget, Option.getD_some]
          exact getElem_congr hoj_eq hoj_sc hoj'
        let scr_s := scr_j.set 4132 (scr_j[4132]'h4132 + 1#32)
        have hsc_s : scr_s.length = c.scratch_cap := by simp [scr_s, hscj]
        have hout_s : ∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
            scr_s[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor => by
          dsimp only [scr_s]; rw [List.getElem?_set_ne (by omega)]; exact hout_j i hi hor
        have hoj_sc_s : ((opp_off + j).setWidth 64).toNat < scr_s.length := by
          rw [hsc_s, zext32_toNat]; c0_bound
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
                (Or.inr (by rw [u32_and7fff_or8000_toNat j (by omega)]; exact hj_lt)) hmb'
            · intro _ hJret
              c0_hsplit
              · c0_hsteps!; exact hJret () _ hm
              · c0_hsplit
                · c0_hsteps!; exact hJret () _ hm
                · c0_hsteps!; exact hJj () _ hm
          · let w := scr_s[((opp_off + j).setWidth 64).toNat]'hoj_sc_s
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
              rw [hdw0.1.core_ok.arena_len_arr, BitVec.toNat_add, zext32_toNat,
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              omega
            let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_ar
            have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := by
              unfold sz fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
                Option.getD_some]
              exact congrArg BitVec.toNat (getElem_congr (by
                rw [BitVec.toNat_add, zext32_toNat, BitVec.toNat_ofNat,
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
                          rw [u32_and7fff_or8000_toNat j (by omega)]; exact hj_lt)) hmo'
                    · intro _ hJor
                      c0_hsplit
                      · c0_hsteps!; exact hJor () ms' hms'
                      · c0_hsplit
                        · c0_hsteps!; exact hJor () ms' hms'
                        · c0_hsteps!; exact hJskip () ms' hms'
                  · intro _ hJand
                    c0_hsplit
                    · c0_hsplit
                      · have hj31 : (j &&& 0x7FFFFFFF#32).toNat = j.toNat :=
                          u32_and7fff_self j (by omega)
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
                  rw [BitVec.toNat_add, BitVec.toNat_add, zext32_toNat,
                    zext32_toNat, BitVec.toNat_ofNat]
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                have hwk : (w.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                    s0.core.arena.length := by
                  rw [hdw0.1.core_ok.arena_len_arr, hwk_eq]; omega
                let l := s0.core.arena[(w.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hwk
                have hl_mem : l.toNat ∈ fullArenaClauseLitsCore s0.core w.toNat := by
                  rw [mem_fullArenaClauseLitsCore_iff (by
                    rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                  exact ⟨k.toNat, by omega,
                    congrArg BitVec.toNat (getElem_congr hwk_eq.symm _ _)⟩
                have hl_lt : l.toNat < 2 * s0.core.cur_vars :=
                  hdw0.2.1.arena.lits_lt w.toNat href_j hng_j _ hl_mem
                have hl_v : (l.setWidth 64).toNat < s0.core.vals.length := by
                  rw [hdw0.1.core_ok.vals_len, zext32_toNat]; omega
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

/-! ## 2. M8 ITE Mask Hit & `find_ite_side_m8`, `find_ite_m8` -/

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
    rw [hsc, zext32_toNat]; omega
  unfold m8SetMaskBitVarExpr
  c0_hsteps_nogrp
  refine hk _ m (by rw [List.length_set, hsc]) (fun i _ hor => ?_) hm
  rw [List.getElem?_set_ne]
  rw [zext32_toNat]
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
  let R_scr := array (t := i8) c.pLitMark s0.core.lit_mark ⋆ fullMemNoLmScr c s0 ⋆ R
  have hm0' : (array (t := i32) c.pScratchBuf scr0 ⋆ R_scr) m0 := by
    rw [fullMem_scr_iff] at hm0; exact hm0
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
  rw [fullMem_scr_iff]; exact hm

/-- Canonical `Func.wp` proof for `full_bve_find_ite_side_m8`. -/
theorem full_bve_find_ite_side_m8_wp (Γ : Env)
    (hGet : Γ.Has "full_bve_get_tern_m7" fullBveGetTernM7Spec)
    (hMatch : Γ.Has "full_bve_match_tern_m8" m8BveMatchTernSpec) :
    ∀ a m Q X, m8BveFindIteSideSpec a m Q X →
      Func.wp Γ full_bve_find_ite_side_m8_body a m Q X := by
  rintro ⟨h, v, np, nn, neg, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hv, hnp, hnn, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindIteSideSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmx hsc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  obtain ⟨hpl_val, hnl_val⟩ := pl_nl_eq v (by omega)
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
  m8_ite_neg_join (fun neg_bit => neg_bit = if neg then 1#32 else 0#32)
  rintro _ neg_bit hnb
  have hlit_eq : ((v <<< (1#32 : BitVec 32)) ||| neg_bit) = lit_w := by
    rw [hnb]; cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, lit_w]
    · exact BitVec.or_zero
    · rfl
  have hlit_eq_n : ((v <<< (1 : Nat)) ||| neg_bit) = lit_w := hlit_eq
  m8_ite_neg_join (fun lit_off => lit_off.toNat = if neg then 2001 else 0)
  rintro _ lit_off hlo
  m8_ite_neg_join (fun lit_n => lit_n = if neg then nn else np)
  rintro _ lit_n hln
  m8_ite_neg_join (fun opp_off => opp_off.toNat = if neg then 0 else 2001)
  rintro _ opp_off hoo
  m8_ite_neg_join (fun opp_n => opp_n = if neg then np else nn)
  rintro _ opp_n hon
  m8_ite_neg_join (fun lit_mask => lit_mask = 4002#32 ∨ lit_mask = 4066#32)
  rintro _ lit_mask hlm_k
  m8_ite_neg_join (fun opp_mask => opp_mask = 4002#32 ∨ opp_mask = 4066#32)
  rintro _ opp_mask hom_k
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
            rw [hdw0.1.scratch_ok.scratch_buf_len, zext32_toNat]; c0_bound
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
                    have hi0_sc : ((lit_off + i0).setWidth 64).toNat < scr2.length := by
                      rw [hsc2, zext32_toNat]; c0_bound
                    have hi0_eq : ((lit_off + i0).setWidth 64).toNat =
                        lit_off.toNat + i0.toNat := by rw [zext32_toNat]; c0_bound
                    let w0 := scr2[((lit_off + i0).setWidth 64).toNat]'hi0_sc
                    have hw0_orig : w0 =
                        s0.scratch.scratch_buf[lit_off.toNat + i0.toNat]?.getD 0#32 := by
                      have hget := hout2 (lit_off.toNat + i0.toNat) (by omega) (Or.inl (by omega))
                      have hi0' : lit_off.toNat + i0.toNat < scr2.length := by omega
                      rw [List.getElem?_eq_getElem hi0'] at hget
                      rw [← hget, Option.getD_some]
                      exact (getElem_congr hi0_eq.symm hi0' hi0_sc).symm
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
                        exact hL2 (lit_n.toNat - (i0 + 1#32).toNat) (i0 + 1#32, ()) m2'
                          (by omega) ⟨scr2', hsc2', by omega, rfl, hout2', hm2'⟩)
                      ?_
                    intro _ hJ2
                    c0_hsplit
                    · have hw0_c0 : w0 = scr2[(lit_off.toNat + i0.toNat) % 2 ^ 32]'(by
                          rw [Nat.mod_eq_of_lt (by omega), hsc2]; omega) :=
                        getElem_congr (by rw [hi0_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                      have hw0_nb : (w0 &&& 0x80000000#32) = 0#32 := by rw [hw0_c0]; exact hc
                      have hw0_ent := hlit_ent i0.toNat (by omega)
                      rw [← hw0_orig] at hw0_ent; unfold FullBveEntryOkW at hw0_ent
                      rw [ite_eq_right (fun h => h hw0_nb)] at hw0_ent
                      c0_hsteps_nogrp
                      try rw [hlit_eq]
                      try rw [hlit_eq_n]
                      gates_call hGet
                      refine fullBveGetTernM7Spec_intro rfl (fullDenseInvW_scr hdw0 hsc2)
                        hw0_ent.1 hw0_ent.2 (by simp; omega) hm2 ?_
                      intro ok_t scr_t mt _ hsc_t hout_t' hmt
                      have hout_t : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                          scr_t[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                        (hout_t' i hi (by rcases hor with h | h <;> simp <;> omega)).trans
                          (hout2 i hi hor)
                      clear hout_t'
                      c0_hsplit
                      · have h4134 := m8_scr_imm_lt hsc_t hsc16 (k := 4134) (by decide)
                        have h4135 := m8_scr_imm_lt hsc_t hsc16 (k := 4135) (by decide)
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem3 (i1, ()) m3 => ∃ scr3 : List (BitVec 32),
                            let s3 : FullState :=
                              { s0 with scratch := { s0.scratch with scratch_buf := scr3 } }
                            scr3.length = c.scratch_cap ∧ i1.toNat ≤ lit_n.toNat ∧
                            rem3 = lit_n.toNat - i1.toNat ∧
                            (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                              scr3[i]? = s0.scratch.scratch_buf[i]?) ∧
                            (FullMem c s3 ⋆ R) m3)
                          ?_ ?_
                        · rintro L3 rem3 ⟨i1, ⟨⟩⟩ m3 hL3 ⟨scr3, hsc3, hi1_le, rfl, hout3, hm3⟩
                          have h4132_3 := m8_scr_imm_lt hsc3 hsc16 (k := 4132) (by decide)
                          c0_hsplit
                          · have hi1_lt : i1.toNat < lit_n.toNat := hc
                            clear hc
                            c0_hsplit
                            · clear hc
                              have hi1_sc : ((lit_off + i1).setWidth 64).toNat < scr3.length := by
                                rw [hsc3, zext32_toNat]; c0_bound
                              have hi1_eq : ((lit_off + i1).setWidth 64).toNat =
                                  lit_off.toNat + i1.toNat := by rw [zext32_toNat]; c0_bound
                              let w1 := scr3[((lit_off + i1).setWidth 64).toNat]'hi1_sc
                              have hw1_orig : w1 =
                                  s0.scratch.scratch_buf[lit_off.toNat + i1.toNat]?.getD 0#32 := by
                                have hget := hout3 (lit_off.toNat + i1.toNat) (by omega)
                                  (Or.inl (by omega))
                                have hi1' : lit_off.toNat + i1.toNat < scr3.length := by omega
                                rw [List.getElem?_eq_getElem hi1'] at hget
                                rw [← hget, Option.getD_some]
                                exact (getElem_congr hi1_eq.symm hi1' hi1_sc).symm
                              have hi1_1 : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ m3' => ∃ scr3' : List (BitVec 32),
                                  scr3'.length = c.scratch_cap ∧
                                  (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                    scr3'[i]? = s0.scratch.scratch_buf[i]?) ∧
                                  (FullMem c { s0 with scratch :=
                                    { s0.scratch with scratch_buf := scr3' } } ⋆ R) m3')
                                (fun _ _ m3' ⟨scr3', hsc3', hout3', hm3'⟩ => by
                                  c0_hsteps!
                                  exact hL3 (lit_n.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ())
                                    m3' (by omega) ⟨scr3', hsc3', by omega, rfl, hout3', hm3'⟩)
                                ?_
                              intro _ hJ3
                              c0_hsplit
                              · have hw1_c0 : w1 = scr3[(lit_off.toNat + i1.toNat) % 2 ^ 32]'(by
                                    rw [Nat.mod_eq_of_lt (by omega), hsc3]; omega) :=
                                  getElem_congr (by rw [hi1_eq, Nat.mod_eq_of_lt (by omega)]) _ _
                                have hw1_nb : (w1 &&& 0x80000000#32) = 0#32 := by
                                  rw [hw1_c0]; exact hc
                                have hw1_ent := hlit_ent i1.toNat hi1_lt
                                rw [← hw1_orig] at hw1_ent
                                unfold FullBveEntryOkW at hw1_ent
                                rw [ite_eq_right (fun h => h hw1_nb)] at hw1_ent
                                c0_hsteps_nogrp
                                try rw [hlit_eq]
                                try rw [hlit_eq_n]
                                gates_call hGet
                                refine fullBveGetTernM7Spec_intro rfl
                                  (fullDenseInvW_scr hdw0 hsc3) hw1_ent.1 hw1_ent.2
                                  (by simp; omega) hm3 ?_
                                intro ok_t1 scr_t1 mt1 _ hsc_t1 hout_t1' hmt1
                                have hout_t1 : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                    scr_t1[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                  (hout_t1' i hi (by rcases hor with h | h <;> simp <;>
                                    omega)).trans (hout3 i hi hor)
                                clear hout_t1'
                                c0_hsplit
                                · have h4134' := m8_scr_imm_lt hsc_t1 hsc16 (k := 4134) (by decide)
                                  have h4135' := m8_scr_imm_lt hsc_t1 hsc16 (k := 4135) (by decide)
                                  have h4136 := m8_scr_imm_lt hsc_t1 hsc16 (k := 4136) (by decide)
                                  have h4137 := m8_scr_imm_lt hsc_t1 hsc16 (k := 4137) (by decide)
                                  c0_hsteps_nogrp
                                  refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                    (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                    (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2, ())) (fun _ => True)
                                    ?_
                                    (fun _ hJc => by
                                      c0_hsplit
                                      · c0_hsteps!; exact hJc (_, _, _, _) trivial
                                      · m8_ite_pick_step hJc
                                        intro _ hJc2; c0_hsplit
                                        · c0_hsteps!; exact hJc2 (_, _, _, _) trivial
                                        · m8_ite_pick_step hJc2
                                          intro _ hJc3; c0_hsplit
                                          · c0_hsteps!; exact hJc3 (_, _, _, _) trivial
                                          · m8_ite_pick_step hJc3
                                            intro _ hJc4; c0_hsplit <;>
                                              (c0_hsteps!; exact hJc4 (_, _, _, _) trivial))
                                  rintro _ ⟨ok_c, cond, u, w⟩ _
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [])
                                    (fun _ mf => ∃ scr_e : List (BitVec 32),
                                      scr_e.length = c.scratch_cap ∧
                                      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                        scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                      (FullMem c { s0 with scratch :=
                                        { s0.scratch with scratch_buf := scr_e } } ⋆ R) mf)
                                    (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                      c0_hsteps!; exact hJ3 () mf ⟨scr_e, hse, houte, hme⟩)
                                    ?_
                                  intro _ hJno
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    rotate_left 1
                                    · exact hJno () mt1 ⟨scr_t1, hsc_t1, hout_t1, hmt1⟩
                                    gates_call hMatch
                                    refine m8BveMatchTernSpec_intro rfl
                                      (fullDenseInvW_scr hdw0 hsc_t1) hsc16 hoo_bnd hon_2k
                                      (fun j hj => by
                                        dsimp only [Arg.val] at hj ⊢
                                        rw [hout_t1 (opp_off.toNat + j) (by omega)
                                          (Or.inl (by omega))]
                                        exact hopp_ent j hj)
                                      hmt1 ?_
                                    intro m0_r scr_m0 m_m0 _ hsc_m0 hout_m0 hm0_ok hm_m0
                                    have hout_m0' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                        scr_m0[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                                      (hout_m0 i hi (by omega)).trans (hout_t1 i hi hor)
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := [])
                                      (fun _ mf => ∃ scr_e : List (BitVec 32),
                                        scr_e.length = c.scratch_cap ∧
                                        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                          scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                        (FullMem c { s0 with scratch :=
                                          { s0.scratch with scratch_buf := scr_e } } ⋆ R) mf)
                                      (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                        c0_hsteps!; exact hJno () mf ⟨scr_e, hse, houte, hme⟩)
                                      ?_
                                    intro _ hJm0
                                    c0_hsplit
                                    · dsimp only [Arg.val] at hm0_ok
                                      have hj0_lt : (m0_r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat :=
                                        hm0_ok.resolve_left (by assumption)
                                      c0_hsteps_nogrp
                                      gates_call hMatch
                                      refine m8BveMatchTernSpec_intro rfl
                                        (fullDenseInvW_scr hdw0 hsc_m0) hsc16 hoo_bnd hon_2k
                                        (fun j hj => by
                                          dsimp only [Arg.val] at hj ⊢
                                          rw [hout_m0' (opp_off.toNat + j) (by omega)
                                            (Or.inl (by omega))]
                                          exact hopp_ent j hj)
                                        hm_m0 ?_
                                      intro m1_r scr_m1 m_m1 _ hsc_m1 hout_m1 hm1_ok hm_m1
                                      have hout_m1' : ∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                          scr_m1[i]? = s0.scratch.scratch_buf[i]? :=
                                        fun i hi hor => (hout_m1 i hi (by omega)).trans
                                          (hout_m0' i hi hor)
                                      c0_hsteps_nogrp
                                      refine wp_join_group (ts := [])
                                        (fun _ mf => ∃ scr_e : List (BitVec 32),
                                          scr_e.length = c.scratch_cap ∧
                                          (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
                                            scr_e[i]? = s0.scratch.scratch_buf[i]?) ∧
                                          (FullMem c { s0 with scratch :=
                                            { s0.scratch with scratch_buf := scr_e } } ⋆ R) mf)
                                        (fun _ _ mf ⟨scr_e, hse, houte, hme⟩ => by
                                          c0_hsteps!; exact hJm0 () mf ⟨scr_e, hse, houte, hme⟩)
                                        ?_
                                      intro _ hJm1
                                      c0_hsplit
                                      · dsimp only [Arg.val] at hm1_ok
                                        have hj1_lt :
                                            (m1_r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat :=
                                          hm1_ok.resolve_left (by assumption)
                                        c0_hstep; c0_hstep; c0_hstep; c0_hsplit
                                        rotate_left 1
                                        · c0_hsteps!; exact hJm1 () m_m1 ⟨scr_m1,
                                            hsc_m1, hout_m1', hm_m1⟩
                                        exact m8_ite_hit_wp Γ c s0 scr_m1 R lit_mask opp_mask
                                          i0 i1 m0_r m1_r m_m1 Q X hsc_m1 hsc16 hout_m1'
                                          hlm_k hom_k (by omega) (by omega)
                                          (by omega) (by omega) hm_m1 hQ
                                      · c0_hsteps!; exact hJm1 () m_m1 ⟨scr_m1,
                                          hsc_m1, hout_m1', hm_m1⟩
                                    · c0_hsteps!; exact hJm0 () m_m0 ⟨scr_m0, hsc_m0,
                                        hout_m0', hm_m0⟩
                                  · c0_hsteps!; exact hJno () mt1 ⟨scr_t1, hsc_t1, hout_t1, hmt1⟩
                                · c0_hsteps!; exact hJ3 () mt1 ⟨scr_t1, hsc_t1, hout_t1, hmt1⟩
                              · c0_hsteps!; exact hJ3 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                            · c0_hsteps!; exact hJ2 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                          · c0_hsteps!; exact hJ2 () m3 ⟨scr3, hsc3, hout3, hm3⟩
                        · intro L3 hL3; c0_hsteps!
                          exact hL3 (lit_n.toNat - (i0 + 1#32).toNat) (i0 + 1#32, ()) mt
                            ⟨scr_t, hsc_t, by omega, rfl, hout_t, hmt⟩
                      · c0_hsteps!; exact hJ2 () mt ⟨scr_t, hsc_t, hout_t, hmt⟩
                    · c0_hsteps!; exact hJ2 () m2 ⟨scr2, hsc2, hout2, hm2⟩
                  · c0_hsteps!; exact hQ false scr2 m2 hsc2 hout2 hm2
                · c0_hsteps!; exact hQ false scr2 m2 hsc2 hout2 hm2
              · intro L2 hL2; c0_hsteps!
                exact hL2 lit_n.toNat (0#32, ()) _
                  ⟨scr_i0, hsc_i0, Nat.zero_le _, by simp, hout_i0, hm⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 lit_n.toNat (0#64, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl⟩

/-- Canonical `Func.wp` proof for `full_bve_find_ite_m8`. -/
theorem full_bve_find_ite_m8_wp (Γ : Env)
    (hSide : Γ.Has "full_bve_find_ite_side_m8" m8BveFindIteSideSpec) :
    ∀ a m Q X, m8BveFindIteSpec a m Q X →
      Func.wp Γ full_bve_find_ite_m8_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc16, hv, hnp, hnn, hp_ok, hn_ok, hm0, hQ⟩ :=
    m8BveFindIteSpec_elim hSpec
  unfold Func.wp full_bve_find_ite_m8_body
  c0_hsteps_nogrp
  gates_call hSide
  dsimp only [Arg.val]
  refine m8BveFindIteSideSpec_intro rfl hdw0 hsc16 hv hnp hnn hp_ok hn_ok hm0
    (fun ok1 scr1 m1 hsc1 hout1 hm1 => by
      c0_hsplit
      · c0_hsteps!; exact hQ true scr1 m1 hsc1 hout1 hm1
      · c0_hsteps_nogrp
        gates_call hSide
        refine m8BveFindIteSideSpec_intro rfl (fullDenseInvW_scr hdw0 hsc1) hsc16 hv hnp hnn
          (fun i hi => by
            dsimp only [Arg.val] at hi
            have hbe := bveEntry_congr_core (hp_ok i hi) rfl rfl rfl
            rw [hout1 i (by omega) (Or.inl (by omega))]
            exact hbe)
          (fun j hj => by
            dsimp only [Arg.val] at hj
            have hbe := bveEntry_congr_core (hn_ok j hj) rfl rfl rfl
            rw [hout1 (2001 + j) (by omega) (Or.inl (by omega))]
            exact hbe)
          hm1 (fun ok2 scr2 m2 hsc2 hout2 hm2 => by
            c0_hsteps!; exact hQ ok2 scr2 m2 hsc2 (fun i hi hor => by
              rw [hout2 i hi hor]; exact hout1 i hi hor) hm2))

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
