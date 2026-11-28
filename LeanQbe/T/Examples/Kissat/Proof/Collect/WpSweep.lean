/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveEnd
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersSweep0
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersSweep1
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpSweep0
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Arena Sweep WP Proofs (`Proof.Collect.WpSweep`)

Canonical `Func.wp` proofs for `full_arena_sweep_m6` and `full_arena_sweep` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Classical
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics M6Tactics1 M6Tactics2a

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev PreSweepValBrkInv' (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64, .bool]) (mB : Mem 64) : Prop :=
  let (p, _cnt, pre_ok, ()) := arg
  mB = m0 ∧ p.toNat ≤ fp ∧ (pre_ok = true → CleanIrredChain s.core.arena 0 p.toNat)

private abbrev PreSweepValInv' (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64]) (mL : Mem 64) : Prop :=
  let (p, _cnt, ()) := arg
  mL = m0 ∧ p.toNat ≤ fp ∧ CleanIrredChain s.core.arena 0 p.toNat

private abbrev PreSweepInv' (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (arg : Tup Val [i64, i64]) (mP : Mem 64) : Prop :=
  let (start, _pre_irred, ()) := arg
  start.toNat ≤ s.core.arena_len ∧
  (0 < start.toNat → 0 < s.core.cur_level ∧ start.toNat < s.core.arena_len) ∧
  ∃ arPre : List (BitVec 32),
    let sPre : FullState := { s with core := { s.core with arena := arPre } }
    sPre.LengthsOk c ∧ FullWitnessInv c F0 F_cur sPre.core ∧ FullArenaVarsNodup sPre ∧
    (start.toNat < s.core.arena_len → start.toNat ∈ fullArenaClauseRefs sPre) ∧
    CompactPrefixOk c F_cur s sPre.core start.toNat ∧
    SweepReasonMapInv sPre.core sPre.core start.toNat start.toNat ∧
    (0 < s.core.cur_level →
      ∀ idx < sPre.core.trail_end,
        let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
        0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
        (rsn &&& 0x80000000#32) = 0#32 → start.toNat ≤ rsn.toNat →
        (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
    (FullMem c sPre ⋆ R) mP

private abbrev M6SweepExitInv' (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sPre : FullState) (R : Mem 64 → Prop) (start : Nat)
    (arg : Tup Val [i64, i64, i64, i64, i64, .bool, .bool, .bool]) (mE : Mem 64) : Prop :=
  let (_src, dst, first_red, _ir, _rd, has_iar, unsat, new_unit, ()) := arg
  start ≤ dst.toNat ∧ dst.toNat ≤ s.core.arena_len ∧
  (has_iar = true → first_red ≠ 0xFFFFFFFF#64) ∧
  ∃ (sE : FullState) (rwE : Nat), M6SweepLike s sE ∧ sE.LengthsOk c ∧
    CompactPrefixOk c F_cur s sE.core dst.toNat ∧
    CompactPrefixOk c F_cur s sE.core start ∧ WatchStackLayout sE.core ∧
    (∀ l < 2 * sE.core.cur_vars,
      WatchSliceLtOk start F_cur sE.core l (fullWatchOff sE l) (fullWatchSize sE l)) ∧
    (start < dst.toNat →
      start ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst.toNat }) ∧
    FullWitnessInv c F0 F_cur { sE.core with arena_len := dst.toNat } ∧
    M6FirstRedOk c F_cur s sPre sE start dst.toNat rwE first_red ∧
    (0 < s.core.cur_level →
      SweepReasonMapInv sPre.core sE.core sPre.core.arena_len dst.toNat) ∧
    (unsat = true → s.core.cur_level = 0 ∧ F0.Unsat) ∧
    (new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sE.core.trail_end) ∧
    (0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧ sE.core.vals = s.core.vals ∧
      sE.core.lvl = s.core.lvl ∧ sE.core.trl = s.core.trl ∧ sE.core.trail_pos = s.core.trail_pos ∧
      sE.core.trail_end = s.core.trail_end) ∧
    (FullMem c sE ⋆ R) mE

private abbrev M6LastLearnedLoopInv' (c : FullCfg) (sM : FullState) (R : Mem 64 → Prop)
    (dst irred redd : BitVec 64) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (li, ()) := arg
  li.toNat ≤ 16 ∧
  ∃ llL : List (BitVec 32), llL.length = 16 ∧
    (∀ j < li.toNat, llL[j]? = some 0xFFFFFFFF#32) ∧
    (FullMem c
      { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                               num_irred := irred, num_redundant := redd }
        scratch := { sM.scratch with last_learned := llL } } ⋆ R) mL

/-! ## 1. Factored Post-Sweep Exit Block -/

private abbrev m6PostSweepExpr (h pArena start dst first_red irred redd : Val i64)
    (has_iar unsat new_unit at_root : Val Ty.bool) : Expr Val Cont [i64] :=
  Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
    Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 48)) fun p12 =>
    Expr.store (Arg.var dst) (Arg.var p12.1)
      (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 472)) fun p13 =>
       Expr.store (Arg.imm (t := i64) 0) (Arg.var p13.1)
         (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 488)) fun p14 =>
          Expr.store (Arg.var irred) (Arg.var p14.1)
            (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 496)) fun p15 =>
             Expr.store (Arg.var redd) (Arg.var p15.1)
               (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 936)) fun p16 =>
                Expr.load i64 (Arg.var p16.1) fun ld =>
                Expr.group (fun (Jli : Tup Cont [[i64]]) => Blocks.cons (ts := [i64]) (fun p17 =>
                  Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
                    (Arg.var p17.1) (Arg.imm 16)) fun p18 =>
                  Expr.jnz (Arg.var p18.1)
                    (Expr.let_ (swOp2 (.mul i64) (Arg.var p17.1) (Arg.imm 4)) fun p =>
                     Expr.let_ (swOp2 (.add i64) (Arg.var ld) (Arg.var p.1)) fun p =>
                     Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                       (Expr.let_ (swOp2 (.add i64) (Arg.var p17.1) (Arg.imm 1)) fun p =>
                        Expr.jump Jli.1 (Arg.var p.1, ())))
                    (Expr.jnz (Arg.var unsat) (Expr.ret (Arg.imm (t := i64) 2, ()))
                      (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p19 =>
                       Expr.load i64 (Arg.var p19.1) fun ld =>
                       Expr.let_ (swOp2 (.cmp .ne i64 .bool (by decide))
                         (Arg.var ld) (Arg.imm 0)) fun p20 =>
                       Expr.jnz (Arg.var p20.1) (Expr.ret (Arg.imm (t := i64) 3, ()))
                         (Expr.call "full_rewatch_range_m6" (as := [i64, i64, i64])
                            (bs := [.bool]) (Arg.var h, Arg.var start, Arg.var dst, ())
                            fun p =>
                          Expr.jnz (Arg.var p.1)
                            (Expr.group (fun _ => Blocks.cons (ts := [i64])
                               (fun p => Expr.ret (Arg.var p.1, ())) .nil) fun Jr =>
                             Expr.jnz (Arg.var new_unit)
                               (Expr.jump Jr.1 (Arg.imm 1, ())) (Expr.jump Jr.1 (Arg.imm 0, ())))
                            (Expr.ret (Arg.imm (t := i64) 3, ())))))) .nil)
                  fun Jli => Expr.jump Jli.1 (Arg.imm (t := i64) 0, ())))))) .nil) fun Jm =>
  Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
    Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 480)) fun p =>
    Expr.store (Arg.var first_red) (Arg.var p.1)
      (Expr.group (fun _ => Blocks.cons (ts := []) (fun _ => Expr.jump Jm.1 ()) .nil) fun Jc =>
       Expr.jnz (Arg.var at_root) (Expr.jump Jc.1 ())
         (Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
            (Arg.var first_red) (Arg.var dst)) fun p =>
          Expr.jnz (Arg.var p.1)
            (Expr.group (fun Jf => Blocks.cons (ts := [i64]) (fun p =>
               Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
                 (Arg.var p.1) (Arg.var dst)) fun p12 =>
               Expr.jnz (Arg.var p12.1)
                 (Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 2)) fun p13 =>
                  Expr.let_ (swOp2 (.mul i64) (Arg.var p13.1) (Arg.imm 4)) fun p14 =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p14.1)) fun p15 =>
                  Expr.load i32 (Arg.var p15.1) fun ld6 =>
                  Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p16 =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p16.1)) fun p17 =>
                  Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p18 =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p18.1)) fun p19 =>
                  Expr.load i32 (Arg.var p19.1) fun ld =>
                  Expr.let_ (swOp1 (.not i32) (Arg.imm 2097152)) fun p20 =>
                  Expr.let_ (swOp2 (.and i32) (Arg.var ld) (Arg.var p20.1)) fun p21 =>
                  Expr.store (Arg.var p21.1) (Arg.var p17.1)
                    (Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 3)) fun p =>
                     Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld6)) fun p22 =>
                     Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.var p22.1)) fun p =>
                     Expr.jump Jf.1 (Arg.var p.1, ())))
                 (Expr.jump Jc.1 ())) .nil) fun Jf => Expr.jump Jf.1 (Arg.var first_red, ()))
            (Expr.jump Jc.1 ())))) .nil) fun Jf =>
  Expr.jnz (Arg.var unsat) (Expr.jump Jf.1 ())
    (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p11 =>
     Expr.load i64 (Arg.var p11.1) fun ld =>
     Expr.let_ (swOp2 (.cmp .eq i64 .bool (by decide)) (Arg.var ld) (Arg.imm 0)) fun p12 =>
     Expr.jnz (Arg.var p12.1)
       (Expr.jnz (Arg.var has_iar)
          (Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
             (Arg.var first_red) (Arg.var dst)) fun p13 =>
           Expr.jnz (Arg.var p13.1)
             (Expr.call "full_move_red_end_m6" (as := [i64, i64, i64]) (bs := [])
                (Arg.var h, Arg.var first_red, Arg.var dst, ()) fun _ => Expr.jump Jm.1 ())
             (Expr.jump Jf.1 ()))
          (Expr.jump Jf.1 ()))
       (Expr.jump Jf.1 ()))

private theorem moveRangeChain_three_le {ar : List (BitVec 32)} {lo hi rw : Nat}
    (h : MoveRangeChain ar lo hi rw) (hlt : lo < hi) : lo + 3 ≤ hi := by
  cases h with | empty => omega | step h3 => exact h3

private theorem m6_sweep_post_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hMoveRed : Γ.Has "full_move_red_end_m6" fullMoveRedEndSpec)
    (hRewatchRange : Γ.Has "full_rewatch_range_m6" fullRewatchRangeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sPre : FullState}
    {R : Mem 64 → Prop} {start dst first_red irred redd : BitVec 64}
    {has_iar unsat new_unit : Bool} {mE : Mem 64}
    (hcap_lt : c.arena_cap < 2 * dimacsBound) (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hpre_eqs : M6PreEqs s sPre) (hnd0 : FullArenaVarsNodup s) (hdm0 : s.core.dense_mode = 0#64)
    (hstart0 : s.core.cur_level = 0 → start.toNat = 0)
    (hQ : M6SweepPostQ c F0 F_cur s R Q)
    (hexit : M6SweepExitInv' c F0 F_cur s sPre R start.toNat
      (0#64, dst, first_red, irred, redd, has_iar, unsat, new_unit, ()) mE) :
    wp Γ Q X (m6PostSweepExpr c.hdr c.pArena start dst first_red irred redd has_iar unsat new_unit
      (BitVec.ofNat 64 s.core.cur_level == 0)) mE := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  rcases hexit with ⟨hst_dst, hdst_le, hhas_iar, sE, rwE, hlikeE, hlenE, hcmpE, hcmpE_st, hlayE,
    hltE, hstE_in, hwEnd, hfrE, hrmE, hunsatE, hunitE, hposE, hmE⟩
  obtain ⟨hcvE, halE, hclE, hdmE, hftE, hfdE, hincE, helE, hws1E, hws2E⟩ := hlikeE.unchanged
  have hcap_num : c.arena_cap < 2 ^ 29 := by rw [hdb] at hcap_lt; omega
  have hdst_cap : dst.toNat ≤ c.arena_cap :=
    Nat.le_trans (halE ▸ hdst_le) hlenE.core_ok.arena_len_le
  have hdst_29 : dst.toNat < 2 ^ 29 := Nat.lt_of_le_of_lt hdst_cap hcap_num
  have harE_len : sE.core.arena.length = c.arena_cap := hlenE.core_ok.arena_len_arr
  dsimp only [m6PostSweepExpr]
  m6_to_group
  refine wp_join_group (M6PostMoveInv c F0 F_cur s R start.toNat dst unsat new_unit) ?_ ?_
  · rintro _ ⟨⟩ mM ⟨sM, hpostM, hlenM, hcvM, halM, hclM, hdmM, hftM, hfdM, hincM, helM,
        hws1M, hws2M, hwM, hnoM, hndM, hstM_in, hunsM, hunitM, hposM, hmM⟩
    have hll_len : sM.scratch.last_learned.length = 16 := hlenM.scratch_ok.last_learned_len
    m6_c0_steps
    refine wp_loop_inv (M6LastLearnedLoopInv' c sM R dst irred redd)
      (fun (li, ()) _ => 16 - li.toNat) (fun Jli hLoopLi => ?_) ?_
    · m6_c0_steps
      exact hLoopLi (0#64, ()) _ ⟨Nat.zero_le _, sM.scratch.last_learned, hll_len,
        fun _ hj => absurd hj (Nat.not_lt_zero _), by assumption⟩
    · rintro Jli ⟨li, ⟨⟩⟩ mL ⟨hli_le, llL, hllL, hallL, hmL⟩ hLoopLi
      m6_jnz
      · have hli_lt : li.toNat < 16 := by c0_bound
        have hli1_eq : (li + 1#64).toNat = li.toNat + 1 := bv64_add1_lt (by omega)
        m6_c0_steps
        refine hLoopLi (li + 1#64, ()) _ (by dsimp only; rw [hli1_eq]; omega)
          ⟨by rw [hli1_eq]; omega, llL.set li.toNat 0xFFFFFFFF#32, List.length_set.trans hllL,
           fun j hj => ?_, by assumption⟩
        rw [hli1_eq] at hj
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
        · exact List.getElem?_set_self (by omega)
        · rw [List.getElem?_set_ne (by omega)]; exact hallL j hlt
      · have hli_16 : li.toNat = 16 := by c0_bound
        have hll_ff : ∀ j < 16, llL[j]? = some 0xFFFFFFFF#32 := fun j hj => hallL j (by omega)
        let sPost : FullState := m6PostState sM dst irred redd llL
        have hlenP : sPost.LengthsOk c :=
          ⟨m6_core_lengths_upd hlenM.core_ok
            (Nat.le_trans (halM ▸ hdst_le) hlenM.core_ok.arena_len_le)
            0#64 sM.core.first_reducible irred redd,
           { hlenM.scratch_ok with last_learned_len := hllL }⟩
        have hllP : FullLastLearnedWf sPost := fullLastLearnedWf_of_all_sentinel hll_ff
        have hwP : FullWitnessInv c F0 F_cur sPost.core :=
          m6_witness_upd_stats hwM 0#64 irred redd
        have hndP : FullArenaVarsNodup sPost := fun r hr _ => hndM hnd0 r hr
        have hstP_in : start.toNat < sPost.core.arena_len →
            start.toNat ∈ fullArenaClauseRefs sPost := fun hlt => hstM_in hlt
        have hposP : 0 < s.core.cur_level → sM.core.vals = s.core.vals ∧
            sM.core.lvl = s.core.lvl ∧ sM.core.trl = s.core.trl ∧
            sM.core.trail_pos = s.core.trail_pos ∧ sM.core.trail_end = s.core.trail_end :=
          fun hp => (hposM hp).2.2
        m6_jnz
        · have hu_t : unsat = true := by simpa using hc
          m6_c0_steps
          exact m6_sweep_early_exit hpostM hlenP hllP hwP hndP helM hws1M hws2M hmL
            (Or.inl ⟨rfl, hunsM hu_t⟩) hQ hposP
        · clear hc; m6_jnz
          · have hoom_ne : sM.core.oom ≠ 0#64 := fun h0 => by
              have h1 : sPost.core.oom = 0#64 := h0; rw [h1] at hc; revert hc; decide
            m6_c0_steps
            exact m6_sweep_early_exit hpostM hlenP hllP hwP hndP helM hws1M hws2M hmL
              (Or.inr ⟨rfl, hoom_ne⟩) hQ hposP
          · have hoom0 : sM.core.oom = 0#64 :=
              BitVec.eq_of_toNat_eq (by change sPost.core.oom.toNat = 0; c0_bound)
            m6_c0_steps; c0_call hRewatchRange
            refine ⟨c, F0, F_cur, sPost, R, rfl, hlenP, hst_dst, hstP_in, rfl, hwP,
              hdmM.trans hdm0, hnoM, hmL, ?_⟩
            have hpost := m6_sweep_rewatch_exit hpostM hoom0 hll_ff hndP helM hws1M hws2M
              new_unit hunitM (fun hp => (hposM hp).2.1) hposP Q hQ
            intro ok arR wvecR wstkR wlenR wuR oomR wsR mR sR hlenR hwR hndR hrefsR
              hokf hokt hmR
            have hfin := hpost ok arR wvecR wstkR wlenR wuR oomR wsR mR hlenR hwR hndR
              hrefsR hokf hokt hmR
            dsimp only at hfin
            apply wp_jnz_of
            · intro hok_t; simp only [Arg.val_var] at hok_t
              rw [hok_t] at hfin; simp only [↓reduceIte] at hfin
              m6_c0_steps; m6_jnz
              · have hnu_t : new_unit = true := by simpa using hc
                m6_c0_steps; rw [hnu_t] at hfin; simpa using hfin
              · have hnu_f : new_unit = false := by cases new_unit <;> simp at hc ⊢
                m6_c0_steps; rw [hnu_f] at hfin; simpa using hfin
            · intro hok_f; simp only [Arg.val_var] at hok_f
              rw [hok_f] at hfin; simp only [Bool.false_eq_true, ↓reduceIte] at hfin
              m6_c0_steps; exact hfin
  · intro JM hJM
    m6_to_group
    refine wp_join_group (fun () mJ => mJ = mE) ?_ ?_
    · intro _ ⟨⟩ mJ hmJ_eq; subst hmJ_eq; m6_to_group
      let sE1 : FullState := { sE with core := { sE.core with first_reducible := first_red } }
      refine wp_join_group (M6PostMoveInv c F0 F_cur s R start.toNat dst unsat new_unit)
        (fun _ ⟨⟩ m2 h2 => by m6_c0_steps; exact hJM () m2 h2) ?_
      intro J2 hJ2
      have hcf0 := m6_move_red_post_cf hwPre (fun hs => by rw [hdmE]; exact hdm0) hlikeE hlenE
        hst_dst (Nat.le_trans hst_dst hdst_le) hdst_cap hpre_eqs harE_len
        (fun _ _ => rfl) hcmpE_st hcmpE hlayE hltE hstE_in rfl
        hstart0 hwEnd hunitE (fun hp => (hposE hp).2) hrmE hunsatE (by assumption)
      m6_jnz
      · m6_c0_steps; exact hJ2 () _ hcf0
      · have hpos : 0 < s.core.cur_level := by
          by_cases hcl0 : s.core.cur_level = 0
          · exact absurd (by simp [hcl0]) hc
          · exact Nat.pos_of_ne_zero hcl0
        m6_jnz
        · have hfr_lt_dst : first_red.toNat < dst.toNat := by c0_bound
          have hfr_ne : first_red ≠ 0xFFFFFFFF#64 := fun he => by
            rw [he] at hfr_lt_dst; simp at hfr_lt_dst; omega
          rcases hfrE with h_bad | ⟨hfr_st, _, hcmpE_fr, _, hmvE, hfr_inE, _⟩
          · exact absurd h_bad hfr_ne
          have hcmpE1 : CompactPrefixOk c F_cur s sE1.core dst.toNat :=
            ⟨{ len_ok := hcmpE.1.len_ok, refs_wf := hcmpE.1.refs_wf,
               shrk_term := hcmpE.1.shrk_term, lits_lt := hcmpE.1.lits_lt,
               entails := hcmpE.1.entails }, hcmpE.2.1, hcmpE.2.2⟩
          refine wp_loop_inv
            (fun (cp, ()) => M6ClearFallInv c F_cur s sPre sE1 R first_red.toNat dst.toNat cp)
            (fun (cp, ()) _ => dst.toNat - cp.toNat) (fun Jf hLoopF => ?_) ?_
          · m6_c0_steps
            exact hLoopF (first_red, ()) _ ⟨Nat.le_refl _, Nat.le_of_lt hfr_lt_dst,
              sE.core.arena, rwE, harE_len, fun _ _ => rfl, fun _ _ _ => rfl,
              hmvE, hcmpE1, hrmE, rfl, fun _ => hfr_inE, by assumption⟩
          · rintro Jf ⟨cp, ⟨⟩⟩ mF ⟨hfr_cp, hcp_le, arL, rwRem, harL_l, hpreL, htailL, hmvRem,
                hcmpL, hrmL, hrefsL, hcp_in, hmF⟩ hLoopF
            m6_jnz
            · have hcp_lt : cp.toNat < dst.toNat := by c0_bound
              have h3 : cp.toNat + 3 ≤ dst.toNat := moveRangeChain_three_le hmvRem hcp_lt
              have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
              let sF_ar : FullState := { sE1 with core := { sE1.core with arena := arL } }
              have hmF' : (FullMem c sF_ar ⋆ R) mF := hmF
              m6_tiny_lets
              rw [wp_load]; refine ⟨_, by
                have hl := @c0_load_full_arena c sF_ar R mF (cp + 2)
                  (by rw [show (cp + 2).toNat = (cp + 2#64).toNat from rfl, hcp2_eq, harL_l]
                      omega)
                  hmF'
                simpa only [Arg.val_var] using hl, ?_⟩
              m6_tiny_lets
              rw [wp_load]; refine ⟨_, by
                have hl := @c0_load_full_arena c sF_ar R mF cp
                  (by rw [harL_l]; omega) hmF'
                simpa only [Arg.val_var] using hl, ?_⟩
              m6_tiny_lets; try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
              apply wp_store_sep (by
                have hs := @c0_store_full_arena c sF_ar R mF cp
                  (arL[cp.toNat] &&& ~~~0x00200000#32) (by rw [harL_l]; omega) hmF'
                simpa only [Arg.val_var, Arg.val_imm, swOp1, swOp2, lift1, lift2,
                  show sF_ar.core.arena = arL from rfl,
                  show (2097152 : BitVec 32) = 2097152#32 from rfl] using hs)
              intro mF2 hmF2; m6_tiny_lets; try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
              rw [wp_jump]
              obtain ⟨hsz3, hfit, hinv'⟩ := m6_clear_fall_step hfr_cp hcp_lt hdst_cap hcap_lt
                harL_l hpreL htailL hmvRem hcmpL hrmL hrefsL (hcp_in hcp_lt)
                (hhdr := rfl) (hsz := rfl) hmF2
              have hnxt_eq : (cp + (3#64 + (arL[cp.toNat + 2]'(by
                  rw [harL_l]; omega)).setWidth 64)).toNat =
                  cp.toNat + 3 + (arL[cp.toNat + 2]'(by rw [harL_l]; omega)).toNat := by
                rw [BitVec.toNat_add, BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
                  zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
              simpa only [vals, Arg.val_var, sF_ar, BitVec.add_assoc, hcp2_eq,
                show (cp + 2).toNat = cp.toNat + 2 from hcp2_eq,
                show (3 : BitVec 64) = 3#64 from rfl] using
                hLoopF _ _ (by dsimp only; rw [hnxt_eq]; omega)
                  (by simpa only [hcp2_eq] using hinv')
            · have hcp_eq : cp.toNat = dst.toNat := by c0_bound
              m6_c0_steps
              have hcmpL0 : CompactPrefixOk c F_cur s { sE.core with arena := arL } dst.toNat :=
                ⟨{ len_ok := hcmpL.1.len_ok, refs_wf := hcmpL.1.refs_wf,
                   shrk_term := hcmpL.1.shrk_term, lits_lt := hcmpL.1.lits_lt,
                   entails := hcmpL.1.entails }, hcmpL.2.1, hcmpL.2.2⟩
              exact hJ2 () _ (m6_move_red_post_cf hwPre (fun hs => by rw [hdmE]; exact hdm0)
                hlikeE hlenE hst_dst (Nat.le_trans hst_dst hdst_le) hdst_cap hpre_eqs harL_l
                (fun i hi => hpreL i (by omega)) hcmpE_st hcmpL0 hlayE hltE hstE_in hrefsL
                hstart0 hwEnd hunitE (fun hp => (hposE hp).2) hrmL hunsatE hmF)
        · m6_c0_steps; exact hJ2 () _ hcf0
    · intro Jelse hJelse; m6_jnz
      · m6_c0_steps; exact hJelse () mE rfl
      · m6_jnz
        · m6_jnz
          · m6_jnz
            · have hns : unsat = false := by cases unsat <;> simp at hc ⊢
              have hfr_lt_dst : first_red.toNat < dst.toNat := by c0_bound
              have hfr_ne : first_red ≠ 0xFFFFFFFF#64 := fun he => by
                rw [he] at hfr_lt_dst; simp at hfr_lt_dst; omega
              rcases hfrE with hbad | ⟨hfr_st, _, hcmpE_fr, hrw_pos, hmvE, hfr_inE, hrs_mk⟩
              · exact absurd hbad hfr_ne
              have huniqE := moveRedRsnUnique_of_witness
                (k := { sE.core with arena_len := dst.toNat })
                (lo := first_red.toNat) (hi := dst.toNat) hwEnd (by have := hdst_29; omega)
              m6_c0_steps; c0_call hMoveRed
              refine ⟨c, sE, rwE, R, rfl, hlenE, hfr_lt_dst,
                by dsimp only [Arg.val_var]; have := hdst_cap; omega,
                hrw_pos, hmvE, fun l hl => hwEnd.vals_domain l hl, huniqE, by assumption,
                fun arM rsnsM fred' sc' rwOut mM harM_l hrsnsM_l hscM_ok helM hws1M hws2M
                  hpreM hmvM hblkM hrsnsM hmM => ?_⟩
              m6_c0_steps
              exact hJM () mM (hns ▸ m6_move_red_post_end hwPre
                (fun _ => by rw [hdmE]; exact hdm0)
                hlikeE hlenE hcap_lt hst_dst hdst_le hdst_cap hfr_st hfr_lt_dst
                hpre_eqs hcmpE hcmpE_st hcmpE_fr hlayE hltE hstE_in hmvE hfr_inE hrs_mk
                hstart0 hwEnd hunitE (fun hp => (hposE hp).2) hrmE
                harM_l hrsnsM_l hscM_ok helM hws1M hws2M hpreM hmvM hblkM hrsnsM hmM)
            · m6_tiny_jump; exact hJelse () mE rfl
          · m6_tiny_jump; exact hJelse () mE rfl
        · m6_c0_steps; exact hJelse () mE rfl

/-! ## 2. Factored Pre-Sweep Validation & Clear Block -/

private abbrev m6PreSweepExpr {rs : List Ty} (JPre : Cont [i64, i64])
    (h pArena alen : Val i64) (at_root : Val Ty.bool) : Expr Val Cont rs :=
  Expr.jnz (Arg.var at_root) (Expr.jump JPre (Arg.imm 0, Arg.imm 0, ()))
    (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 512)) fun p8 =>
     Expr.load i64 (Arg.var p8.1) fun ld6 =>
     Expr.let_ (swOp2 (.cmp .eq i64 .bool (by decide)) (Arg.var ld6) (Arg.imm 0)) fun p9 =>
     Expr.jnz (Arg.var p9.1)
       (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 480)) fun p10 =>
        Expr.load i64 (Arg.var p10.1) fun ld7 =>
        Expr.let_ (swOp2 (.cmp .ugt i64 .bool (by decide)) (Arg.var ld7) (Arg.imm 0)) fun p11 =>
        Expr.jnz (Arg.var p11.1)
          (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 480)) fun p12 =>
           Expr.load i64 (Arg.var p12.1) fun ld8 =>
           Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide)) (Arg.var ld8) (Arg.var alen))
             fun p13 =>
           Expr.jnz (Arg.var p13.1)
             (Expr.let_ (swOp2 (.add i64) (Arg.var h) (Arg.imm 480)) fun p =>
              Expr.load i64 (Arg.var p.1) fun ld9 =>
              Expr.group (fun _ => Blocks.cons (ts := [i64, i64, .bool]) (fun p =>
                Expr.group (fun _ => Blocks.cons (ts := [i64, i64]) (fun p =>
                  Expr.jump JPre (Arg.var p.1, Arg.var p.2.1, ())) .nil) fun Jret =>
                Expr.jnz (Arg.var p.2.2.1)
                  (Expr.let_ (swOp2 (.cmp .eq i64 .bool (by decide))
                     (Arg.var p.1) (Arg.var ld9)) fun p14 =>
                   Expr.jnz (Arg.var p14.1)
                     (Expr.group (fun Jc => Blocks.cons (ts := [i64]) (fun p15 =>
                        Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
                          (Arg.var p15.1) (Arg.var ld9)) fun p16 =>
                        Expr.jnz (Arg.var p16.1)
                          (Expr.let_ (swOp2 (.mul i64) (Arg.var p15.1) (Arg.imm 4)) fun p =>
                           Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p.1)) fun p =>
                           Expr.load i32 (Arg.var p.1) fun ld10 =>
                           Expr.let_ (swOp2 (.add i64) (Arg.var p15.1) (Arg.imm 2)) fun p =>
                           Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p =>
                           Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p.1)) fun p =>
                           Expr.load i32 (Arg.var p.1) fun ld11 =>
                           Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
                             Expr.let_ (swOp2 (.add i64) (Arg.var p15.1) (Arg.imm 3)) fun p =>
                             Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld11)) fun p17 =>
                             Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.var p17.1)) fun p =>
                             Expr.jump Jc.1 (Arg.var p.1, ())) .nil) fun J2 =>
                           Expr.let_ (swOp2 (.and i32) (Arg.var ld10) (Arg.imm 2097152)) fun p =>
                           Expr.let_ (swOp2 (.cmp .ne i32 .bool (by decide))
                             (Arg.var p.1) (Arg.imm 0)) fun p =>
                           Expr.jnz (Arg.var p.1)
                             (Expr.let_ (swOp2 (.mul i64) (Arg.var p15.1) (Arg.imm 4)) fun p =>
                              Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p.1)) fun p =>
                              Expr.let_ (swOp1 (.not i32) (Arg.imm 2097152)) fun p17 =>
                              Expr.let_ (swOp2 (.and i32) (Arg.var ld10) (Arg.var p17.1)) fun p18 =>
                              Expr.store (Arg.var p18.1) (Arg.var p.1) (Expr.jump J2.1 ()))
                             (Expr.jump J2.1 ()))
                          (Expr.jump Jret.1 (Arg.var ld9, Arg.var p.2.1, ()))) .nil)
                        fun Jc => Expr.jump Jc.1 (Arg.imm 0, ()))
                     (Expr.jump Jret.1 (Arg.imm 0, Arg.imm 0, ())))
                  (Expr.jump Jret.1 (Arg.imm 0, Arg.imm 0, ()))) .nil) fun Jv =>
              Expr.group (fun Jp => Blocks.cons (ts := [i64, i64]) (fun p =>
                Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide))
                  (Arg.var p.1) (Arg.var ld9)) fun p14 =>
                Expr.jnz (Arg.var p14.1)
                  (Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 3)) fun p15 =>
                   Expr.let_ (swOp2 (.cmp .ugt i64 .bool (by decide))
                     (Arg.var p15.1) (Arg.var ld9)) fun p16 =>
                   Expr.jnz (Arg.var p16.1)
                     (Expr.jump Jv.1 (Arg.var p.1, Arg.var p.2.1, Arg.imm false, ()))
                     (Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p17 =>
                      Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p17.1)) fun p18 =>
                      Expr.load i32 (Arg.var p18.1) fun ld10 =>
                      Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 2)) fun p19 =>
                      Expr.let_ (swOp2 (.mul i64) (Arg.var p19.1) (Arg.imm 4)) fun p20 =>
                      Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p20.1)) fun p21 =>
                      Expr.load i32 (Arg.var p21.1) fun ld =>
                      Expr.let_ (swOp2 (.or i32) (Arg.imm 524288) (Arg.imm 8388608)) fun p22 =>
                      Expr.let_ (swOp2 (.or i32) (Arg.var p22.1) (Arg.imm 4194304)) fun p23 =>
                      Expr.let_ (swOp2 (.and i32) (Arg.var ld10) (Arg.var p23.1)) fun p24 =>
                      Expr.let_ (swOp2 (.cmp .ne i32 .bool (by decide))
                        (Arg.var p24.1) (Arg.imm 0)) fun p25 =>
                      Expr.jnz (Arg.var p25.1)
                        (Expr.jump Jv.1 (Arg.var p.1, Arg.var p.2.1, Arg.imm false, ()))
                        (Expr.let_ (swOp2 (.cmp .ult i32 .bool (by decide))
                           (Arg.var ld) (Arg.imm 3)) fun p26 =>
                         Expr.jnz (Arg.var p26.1)
                           (Expr.jump Jv.1 (Arg.var p.1, Arg.var p.2.1, Arg.imm false, ()))
                           (Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 3)) fun p27 =>
                            Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld)) fun p28 =>
                            Expr.let_ (swOp2 (.add i64) (Arg.var p27.1) (Arg.var p28.1)) fun p29 =>
                            Expr.let_ (swOp2 (.cmp .ugt i64 .bool (by decide))
                              (Arg.var p29.1) (Arg.var ld9)) fun p30 =>
                            Expr.jnz (Arg.var p30.1)
                              (Expr.jump Jv.1 (Arg.var p.1, Arg.var p.2.1, Arg.imm false, ()))
                              (Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.imm 3)) fun p31 =>
                               Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld)) fun p32 =>
                               Expr.let_ (swOp2 (.add i64) (Arg.var p31.1) (Arg.var p32.1))
                                 fun p33 =>
                               Expr.let_ (swOp2 (.add i64) (Arg.var p.2.1) (Arg.imm 1)) fun p =>
                               Expr.jump Jp.1 (Arg.var p33.1, Arg.var p.1, ()))))))
                  (Expr.jump Jv.1 (Arg.var p.1, Arg.var p.2.1, Arg.imm true, ()))) .nil)
                fun Jp => Expr.jump Jp.1 (Arg.imm 0, Arg.imm 0, ()))
             (Expr.jump JPre (Arg.imm 0, Arg.imm 0, ())))
          (Expr.jump JPre (Arg.imm 0, Arg.imm 0, ())))
       (Expr.jump JPre (Arg.imm 0, Arg.imm 0, ())))

private theorem m6_pre_sweep_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (JPre : Cont [i64, i64])
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hcap_lt : c.arena_cap < 2 * dimacsBound)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd0 : FullArenaVarsNodup s)
    (hrmk0 : 0 < s.core.cur_level → FullReasonsMarked s)
    (hm : (FullMem c s ⋆ R) m) (hpre0 : PreSweepInv' c F0 F_cur s R (0#64, 0#64, ()) m)
    (hJPre : ∀ x mP, PreSweepInv' c F0 F_cur s R x mP → JPre x mP) :
    wp Γ Q X
      (m6PreSweepExpr JPre c.hdr c.pArena (BitVec.ofNat 64 s.core.arena_len)
        (BitVec.ofNat 64 s.core.cur_level == 0)) m := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hal_le := hlen.core_ok.arena_len_le
  have hcap_num : c.arena_cap < 2 ^ 29 := by rw [hdb] at hcap_lt; omega
  have hal_lt : s.core.arena_len < 2 ^ 29 := Nat.lt_of_le_of_lt hal_le hcap_num
  have har_len := hlen.core_ok.arena_len_arr
  have hte_le := hlen.core_ok.trail_end_le
  dsimp only [m6PreSweepExpr]
  m6_jnz
  · m6_c0_steps; try rw [wp_jump]
    exact hJPre (0#64, 0#64, ()) m hpre0
  · have hpos : 0 < s.core.cur_level := by
      by_cases h0 : s.core.cur_level = 0
      · exact absurd (by simp [h0]) hc
      · exact Nat.pos_of_ne_zero h0
    m6_jnz
    · m6_jnz
      · have hfp_pos : 0 < s.core.first_reducible.toNat := by c0_bound
        m6_jnz
        · have hfp_lt : s.core.first_reducible.toNat < s.core.arena_len := by c0_bound
          m6_to_group
          refine wp_join_group (PreSweepValBrkInv' s s.core.first_reducible.toNat m) ?_ ?_
          · rintro _ ⟨p, cnt, pre_ok, ⟨⟩⟩ mB ⟨hmB, hp_le, hchain⟩; subst mB
            refine wp_join_group (PreSweepInv' c F0 F_cur s R) ?_ ?_
            · rintro _ ⟨a1, a2, ⟨⟩⟩ mP hP
              m6_tiny_jump; try rw [wp_jump]
              exact hJPre (a1, a2, ()) mP hP
            · intro Jret hJPre'
              m6_jnz
              · have hpre_ok : pre_ok = true := hc
                m6_jnz
                · have hp_eq : p.toNat = s.core.first_reducible.toNat := congrArg BitVec.toNat hc
                  have hc0 : CleanIrredChain s.core.arena 0 s.core.first_reducible.toNat :=
                    hp_eq ▸ hchain hpre_ok
                  have h3_fp := cleanIrredChain_three_le hc0 hfp_pos
                  have h0_in_fp : 0 ∈ fullArenaClauseRefsCore
                      { s.core with arena_len := s.core.first_reducible.toNat } := by
                    unfold fullArenaClauseRefsCore
                    cases hal : s.core.first_reducible.toNat with
                    | zero => omega
                    | succ f => unfold fullArenaScanRefs; simp [show 0 + 3 ≤ f + 1 by omega]
                  m6_c0_steps
                  refine wp_loop_inv (fun (cp, ()) => PreSweepClrInv c s R
                      s.core.first_reducible.toNat cp)
                    (fun (cp, ()) _ => s.core.first_reducible.toNat - cp.toNat)
                    (fun Jc hLoopC => ?_) ?_
                  · m6_tiny_jump; exact hLoopC (0#64, ()) m ⟨Nat.zero_le _, .empty, hc0,
                      fun _ => h0_in_fp, s.core.arena, har_len, fun _ _ _ => rfl,
                      fun _ _ hlt => absurd hlt (by simp), hm⟩
                  · rintro Jc ⟨cp, ⟨⟩⟩ mC
                      ⟨hcp_le, hdone, hrem, hcp_in, arL, harL_l, htailL, hmatchL, hmC⟩ hLoopC
                    m6_jnz
                    · have hcp_lt : cp.toNat < s.core.first_reducible.toNat := by c0_bound
                      have hcp3 : cp.toNat + 3 ≤ s.core.first_reducible.toNat :=
                        cleanIrredChain_three_le hrem hcp_lt
                      have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
                      let sC_pre : FullState := { s with core := { s.core with arena := arL } }
                      have hmC' : (FullMem c sC_pre ⋆ R) mC := hmC
                      m6_tiny_lets
                      rw [wp_load]; refine ⟨_, by
                        have hl := @c0_load_full_arena c sC_pre R mC cp
                          (by rw [harL_l]; omega) hmC'
                        simpa only [Arg.val_var] using hl, ?_⟩
                      m6_tiny_lets
                      rw [wp_load]; refine ⟨_, by
                        have hl := @c0_load_full_arena c sC_pre R mC (cp + 2)
                          (by rw [show (cp + 2).toNat = (cp + 2#64).toNat from rfl, hcp2_eq, harL_l]
                              omega)
                          hmC'
                        simpa only [Arg.val_var] using hl, ?_⟩
                      m6_to_group
                      let nxt := cp + (3#64 + (arL[cp.toNat + 2]'(by
                        rw [harL_l]; omega)).setWidth 64)
                      refine wp_join_group
                        (fun _ mC2 => PreSweepClrInv c s R s.core.first_reducible.toNat nxt mC2)
                        (fun _ _ mC2 hC2 => ?_) (fun J2 hJ2 => ?_)
                      · m6_tiny_lets; rw [wp_jump]
                        have hnxt : nxt.toNat =
                            cp.toNat + 3 + (arL[cp.toNat + 2]'(by rw [harL_l]; omega)).toNat := by
                          rw [BitVec.toNat_add, BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
                            zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega),
                            Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
                        have hcp2_eq' : (cp + 2).toNat = cp.toNat + 2 := hcp2_eq
                        simpa only [vals, Arg.val_var, sC_pre, nxt, BitVec.add_assoc, hcp2_eq',
                          show (3 : BitVec 64) = 3#64 from rfl] using
                          hLoopC (nxt, ()) mC2 (by dsimp only; rw [hnxt]; omega) hC2
                      · m6_jnz
                        · m6_tiny_lets; try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                          apply wp_store_sep (by
                            have hs := @c0_store_full_arena c sC_pre R mC cp
                              (arL[cp.toNat] &&& ~~~0x00200000#32) (by rw [harL_l]; omega) hmC'
                            simpa only [Arg.val_var, Arg.val_imm, swOp1, swOp2, lift1, lift2,
                              show sC_pre.core.arena = arL from rfl,
                              show (2097152 : BitVec 32) = 2097152#32 from rfl] using hs)
                          intro mC2 hmC2; try rw [wp_jump]
                          exact hJ2 () mC2 (m6_pre_clr_step hcp_lt hcp3 (by omega) hal_le hcap_lt
                            hdone hrem hcp_in harL_l htailL hmatchL rfl rfl (Or.inl rfl) hmC2).2.2
                        · exact hJ2 () mC (m6_pre_clr_step hcp_lt hcp3 (by omega) hal_le hcap_lt
                            hdone hrem hcp_in harL_l htailL hmatchL rfl rfl
                            (Or.inr ⟨by simpa [sC_pre] using hc, rfl⟩) hmC).2.2
                    · have hcp_eq : cp.toNat = s.core.first_reducible.toNat := by c0_bound
                      rw [hcp_eq] at hdone hmatchL
                      obtain ⟨hlenP, hwP, hndP, hfpP, hcmpP, hrmP, hmkP⟩ :=
                        m6_pre_val_all_ok hlen hw hnd0 hrmk0 hfp_pos hfp_lt hdone harL_l
                          (fun i hi1 hi2 => htailL i (by omega) hi2)
                          (fun r hr => hmatchL r hr (by
                            unfold fullArenaClauseRefsCore at hr
                            have h1 := (fullArenaScanRefs_mem_bounds hr).2
                            dsimp only at h1; omega)) rfl
                      m6_tiny_lets; try rw [wp_jump]
                      exact hJPre' (s.core.first_reducible, cnt, ()) mC
                        ⟨Nat.le_of_lt hfp_lt, fun _ => ⟨hpos, hfp_lt⟩,
                         arL, hlenP, hwP, hndP, hfpP, hcmpP, hrmP, hmkP, hmC⟩
                · m6_c0_steps; try rw [wp_jump]
                  exact hJPre' (0#64, 0#64, ()) m hpre0
              · m6_c0_steps; try rw [wp_jump]
                exact hJPre' (0#64, 0#64, ()) m hpre0
          · intro Jv hJv
            refine wp_loop_inv (PreSweepValInv' s s.core.first_reducible.toNat m)
              (fun (p, _) _ => s.core.first_reducible.toNat - p.toNat) (fun Jp hLoopP => ?_) ?_
            · m6_tiny_jump; exact hLoopP (0#64, 0#64, ()) m ⟨rfl, Nat.zero_le _, .empty⟩
            · rintro Jp ⟨p, cnt, ⟨⟩⟩ mL ⟨rfl, hp_le, hc_p⟩ hLoopP
              m6_jnz
              · have hp_lt : p.toNat < s.core.first_reducible.toNat := by c0_bound
                m6_jnz
                · m6_tiny_jump; exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                · have hp3_fp : p.toNat + 3 ≤ s.core.first_reducible.toNat := by
                    have : ¬ (s.core.first_reducible.toNat < (p + 3#64).toNat) := by c0_bound
                    have := bv64_add3_lt (x := p) (by omega); omega
                  have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2_lt (by omega)
                  have hp_lt_ar : p.toNat < s.core.arena.length := by omega
                  have hp2_lt_ar : (p + 2#64).toNat < s.core.arena.length := by rw [hp2_eq]; omega
                  m6_jnz
                  · m6_tiny_jump; exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                  · have hfl : (s.core.arena[p.toNat]?.getD 0#32 &&& 0x00C80000#32) = 0#32 := by
                      rw [List.getElem?_eq_getElem hp_lt_ar, Option.getD_some]; simpa using hc
                    m6_jnz
                    · m6_tiny_jump
                      exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                    · have hsz_eq : (s.core.arena[(p + 2#64).toNat]'hp2_lt_ar).toNat =
                          (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by
                        rw [← Option.getD_some (a := s.core.arena[(p + 2#64).toNat]'hp2_lt_ar),
                          ← List.getElem?_eq_getElem hp2_lt_ar, hp2_eq]
                      have hsz3 : 3 ≤ (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by
                        rw [← hsz_eq]; c0_bound
                      try (refine ⟨by decide, ?_⟩)
                      m6_jnz
                      · m6_tiny_jump
                        exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                      · have hfit : p.toNat + 3 + (s.core.arena[p.toNat + 2]?.getD 0#32).toNat ≤
                            s.core.first_reducible.toNat := by
                          rw [← hsz_eq]
                          have h1 : ¬ (s.core.first_reducible.toNat <
                              ((p + 3#64) + (s.core.arena[(p + 2#64).toNat]'hp2_lt_ar).setWidth
                                64).toNat) := by c0_bound
                          have h2 := bv64_add3_zext_lt (p := p)
                            (sz := s.core.arena[(p + 2#64).toNat]'hp2_lt_ar) (by omega)
                          rw [h2] at h1; exact Nat.not_lt.mp h1
                        have hp2_eq' : (p + 2).toNat = p.toNat + 2 := hp2_eq
                        have hp_nxt := bv64_add3_zext_lt (p := p)
                          (sz := s.core.arena[(p + 2#64).toNat]'hp2_lt_ar) (by omega)
                        have hp_nxt' : (p + 3 + (s.core.arena[(p + 2).toNat]'(by
                            rw [hp2_eq']; omega)).setWidth 64).toNat =
                            p.toNat + 3 + (s.core.arena[(p + 2#64).toNat]'(by
                              rw [hp2_eq]; omega)).toNat :=
                          hp_nxt
                        have hp3_n : p.toNat + 3 ≤
                            p.toNat + 3 + (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by omega
                        m6_tiny_jump
                        exact hLoopP _ mL (by dsimp only; rw [hp_nxt', hsz_eq]; omega)
                          ⟨rfl, by simpa only [hp_nxt', hsz_eq] using hfit,
                           by simpa only [hp_nxt', hsz_eq] using hc_p.snoc hp3_n hfl hsz3 rfl⟩
              · m6_tiny_jump; exact hJv (p, cnt, true, ()) mL ⟨rfl, hp_le, fun _ => hc_p⟩
        · m6_tiny_jump; try rw [wp_jump]
          exact hJPre (0#64, 0#64, ()) m hpre0
      · m6_tiny_jump; try rw [wp_jump]
        exact hJPre (0#64, 0#64, ()) m hpre0
    · m6_tiny_jump; try rw [wp_jump]
      exact hJPre (0#64, 0#64, ()) m hpre0

/-! ## 3. Factored Post-Copy Writeback, Reason Update, & Branch Step -/

private abbrev m6PostCopyExpr {rs : List Ty}
    (JL : Cont [i64, i64, i64, i64, i64, .bool, .bool])
    (pArena pVals pRsns pCv src dst st nsrc first_red irred redd : Val i64)
    (has_iar new_unit at_root : Val Ty.bool) (hdr0 : Val i32) : Expr Val Cont rs :=
  Expr.let_ (swOp1 (.trunc 64 32) (Arg.var st)) fun st32 =>
  Expr.let_ (swOp2 (.or i32) (Arg.imm 8388608) (Arg.imm 2097152)) fun p33 =>
  Expr.let_ (swOp1 (.not i32) (Arg.var p33.1)) fun p34 =>
  Expr.let_ (swOp2 (.and i32) (Arg.var hdr0) (Arg.var p34.1)) fun p35 =>
  Expr.let_ (swOp2 (.mul i64) (Arg.var dst) (Arg.imm 4)) fun p36 =>
  Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p36.1)) fun p37 =>
  Expr.store (Arg.var p35.1) (Arg.var p37.1)
    (Expr.let_ (swOp2 (.add i64) (Arg.var dst) (Arg.imm 1)) fun p38 =>
     Expr.let_ (swOp2 (.mul i64) (Arg.var p38.1) (Arg.imm 4)) fun p39 =>
     Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p39.1)) fun p40 =>
     Expr.store (Arg.imm (t := i32) 2) (Arg.var p40.1)
       (Expr.let_ (swOp2 (.add i64) (Arg.var dst) (Arg.imm 2)) fun p41 =>
        Expr.let_ (swOp2 (.mul i64) (Arg.var p41.1) (Arg.imm 4)) fun p42 =>
        Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p42.1)) fun p43 =>
        Expr.store (Arg.var st32.1) (Arg.var p43.1)
          (Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
             Expr.group (fun _ => Blocks.cons (ts := [i64, i64, i64, .bool]) (fun p45 =>
               Expr.let_ (swOp2 (.add i64) (Arg.var dst) (Arg.imm 3)) fun p46 =>
               Expr.let_ (swOp1 (.zext 32 64) (Arg.var st32.1)) fun p =>
               Expr.let_ (swOp2 (.add i64) (Arg.var p46.1) (Arg.var p.1)) fun p =>
               Expr.jump JL (Arg.var nsrc, Arg.var p.1, Arg.var p45.1, Arg.var p45.2.1,
                 Arg.var p45.2.2.1, Arg.var p45.2.2.2.1, Arg.var new_unit, ())) .nil)
             fun Jend =>
             Expr.let_ (swOp2 (.and i32) (Arg.var hdr0) (Arg.imm 4194304)) fun p =>
             Expr.let_ (swOp2 (.cmp .ne i32 .bool (by decide)) (Arg.var p.1) (Arg.imm 0)) fun p =>
             Expr.jnz (Arg.var p.1)
               (Expr.group (fun _ => Blocks.cons (ts := [i64]) (fun p =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var redd) (Arg.imm 1)) fun p45 =>
                  Expr.jump Jend.1 (Arg.var p.1, Arg.var irred, Arg.var p45.1,
                    Arg.var has_iar, ())) .nil) fun Jfr =>
                Expr.let_ (swOp2 (.cmp .eq i64 .bool (by decide))
                  (Arg.var first_red) (Arg.imm 4294967295)) fun p =>
                Expr.jnz (Arg.var p.1)
                  (Expr.jump Jfr.1 (Arg.var dst, ())) (Expr.jump Jfr.1 (Arg.var first_red, ())))
               (Expr.group (fun _ => Blocks.cons (ts := [.bool]) (fun p =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var irred) (Arg.imm 1)) fun p45 =>
                  Expr.jump Jend.1 (Arg.var first_red, Arg.var p45.1, Arg.var redd,
                    Arg.var p.1, ())) .nil) fun Jfr =>
                Expr.let_ (swOp2 (.cmp .ne i64 .bool (by decide))
                  (Arg.var first_red) (Arg.imm 4294967295)) fun p =>
                Expr.jnz (Arg.var p.1)
                  (Expr.jump Jfr.1 (Arg.imm true, ())) (Expr.jump Jfr.1 (Arg.var has_iar, ()))))
             .nil) fun JR =>
           Expr.let_ (swOp2 (.and i32) (Arg.var hdr0) (Arg.imm 2097152)) fun p44 =>
           Expr.let_ (swOp2 (.cmp .ne i32 .bool (by decide)) (Arg.var p44.1) (Arg.imm 0))
             fun p45 =>
           Expr.jnz (Arg.var p45.1)
             (m6RsnLoopExpr JR.1 pArena pVals pRsns pCv src dst st32.1 p35.1 at_root first_red hdr0)
             (Expr.jump JR.1 ()))))

private theorem m6_sweep_post_copy_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {JL : Cont [i64, i64, i64, i64, i64, .bool, .bool]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sPre sL sC : FullState}
    {R : Mem 64 → Prop} {rwL : Nat} {start src dst st nsrc first_red irred redd : BitVec 64}
    {has_iar new_unit : Bool} {old_sz : BitVec 32} {mC : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hpre_eqs : M6PreEqs s sPre)
    (hndPre : FullArenaVarsNodup sPre) (hlikeL : M6SweepLike s sL) (hlikeC : M6SweepLike s sC)
    (hlenC0 : sC.LengthsOk c) (hcap_lt : c.arena_cap < 2 * dimacsBound)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcl_lt : s.core.cur_level < 2 ^ 64)
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (harL_len : sL.core.arena.length = c.arena_cap) (harC_len : sC.core.arena.length = c.arena_cap)
    (_hpreC : PrefixAgrees dst.toNat sL.core.arena sC.core.arena)
    (htailC : ∀ i, nsrc.toNat ≤ i → i < s.core.arena_len →
      sC.core.arena[i]? = sPre.core.arena[i]?)
    (hcmpC : CompactPrefixOk c F_cur s sC.core dst.toNat)
    (hcmpC_st : CompactPrefixOk c F_cur s sC.core start.toNat)
    (hcongrC : CompactPrefixCongr sL.core sC.core dst.toNat)
    (hst_dst : start.toNat ≤ dst.toNat) (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_lt8 : src.toNat < 0x80000000) (hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre)
    (hnsrc64 : nsrc.toNat = fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat)
    (hnxt_le_al : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ≤ s.core.arena_len)
    (hnxt_mem : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat = s.core.arena_len ∨
      fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ∈ fullArenaClauseRefs sPre)
    (hsrc_fit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hsz_orig : old_sz.toNat = fullArenaClauseSizeCore sPre.core src.toNat)
    (hwf0 : src.toNat + 3 ≤ sPre.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore sPre.core src.toNat ∧
      src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat ≤
        fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ∧
      fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ≤ sPre.core.arena_len)
    (hng_src : fullArenaClauseGarbCore sPre.core src.toNat = false)
    (hs0_lt : src.toNat < sL.core.arena.length)
    (hhdr_orig : sL.core.arena[src.toNat]'hs0_lt = fullArenaHdrCore sPre.core src.toNat)
    (hsrc_lits_eq : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore sPre.core src.toNat)
    (hstC_in : start.toNat < dst.toNat →
      start.toNat ∈ fullArenaClauseRefsCore { sC.core with arena_len := dst.toNat })
    (hfr_to_C : M6FirstRedOk c F_cur s sPre sC start.toNat dst.toNat rwL first_red)
    (hhas_iar : has_iar = true → first_red ≠ 0xFFFFFFFF#64)
    (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start.toNat dst.toNat new_unit)
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz
      (BitVec.ofNat 64 s.core.cur_level == 0) st)
    (hdec_cl0 : ∀ b : Bool, (BitVec.ofNat 64 s.core.cur_level == 0) = b ↔
      (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hnew3 : 3 ≤ st.toNat) (hnew_le : st.toNat ≤ old_sz.toNat)
    (hnew_lt : ∀ j < st.toNat,
      (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * sC.core.cur_vars)
    (hnew_sub : List.Sublist
      (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
      (fullArenaClauseLitsCore sPre.core src.toNat))
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)))
    (hlayC : WatchStackLayout sC.core)
    (hltC : ∀ l < 2 * sC.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sC.core l (fullWatchOff sC l) (fullWatchSize sC l))
    (hrmkPre : 0 < s.core.cur_level →
      ∀ idx < sPre.core.trail_end,
        let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
        0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
        (rsn &&& 0x80000000#32) = 0#32 → start.toNat ≤ rsn.toNat →
        (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32)
    (hmC0 : (FullMem c sC ⋆ R) mC)
    (hJL : ∀ d' fr' ir' rd' hia' mR,
      M6SweepLoopInv c F0 F_cur s sPre R start.toNat nsrc d' fr' hia' new_unit mR →
      JL (nsrc, d', fr', ir', rd', hia', new_unit, ()) mR) :
    wp Γ (Q := Q) (X := X)
      (m6PostCopyExpr JL c.pArena c.pVals c.pReason (BitVec.ofNat 64 s.core.cur_vars) src dst st
        nsrc first_red irred redd has_iar new_unit (BitVec.ofNat 64 s.core.cur_level == 0)
        (sL.core.arena[src.toNat]'hs0_lt)) mC := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcvL := hlikeL.unchanged.1
  have hcvC := hlikeC.unchanged.1
  have hnsz32_eq : (st.setWidth 32).toNat = st.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hd1_eq : (dst + 1).toNat = dst.toNat + 1 := bv64_add1_lt (by omega)
  have hd2_eq : (dst + 2).toNat = dst.toNat + 2 := bv64_add2_lt (by omega)
  let hdr0 := sL.core.arena[src.toNat]'hs0_lt
  let nhdr0 := hdr0 &&& ~~~((8388608 : BitVec 32) ||| (2097152 : BitVec 32))
  dsimp only [m6PostCopyExpr]
  m6_unmdata; try c0_let_simp
  apply wp_store_sep (by
    have hs := @c0_store_full_arena c sC R mC dst nhdr0
      (by show dst.toNat < sC.core.arena.length; omega) hmC0
    simpa only [Arg.val_var, swOp1, swOp2, lift1, lift2, nhdr0, hdr0] using hs)
  intro m1 hm1; m6_tiny_lets
  let sC1 : FullState :=
    { sC with core := { sC.core with arena := sC.core.arena.set dst.toNat nhdr0 } }
  apply wp_store_sep (by
    have hs := @c0_store_full_arena c sC1 R m1 (dst + 1) (2 : BitVec 32) (by
      show (dst + 1).toNat < sC1.core.arena.length
      simp [sC1, List.length_set]; omega) hm1
    simpa only [Arg.val_var, Arg.val_imm, swOp2, lift2, sC1, nhdr0, hdr0] using hs)
  intro m2 hm2; m6_tiny_lets
  let sC2 : FullState :=
    { sC1 with core :=
      { sC1.core with arena := sC1.core.arena.set (dst + 1).toNat (2 : BitVec 32) } }
  apply wp_store_sep (by
    have hs := @c0_store_full_arena c sC2 R m2 (dst + 2) (st.setWidth 32)
      (by show (dst + 2).toNat < sC2.core.arena.length
          simp [sC2, sC1, List.length_set]; omega) hm2
    simpa only [Arg.val_var, swOp1, swOp2, lift1, lift2, sC2, sC1, nhdr0, hdr0] using hs)
  intro m hm; m6_tiny_lets
  have hst32_of : st.setWidth 32 = BitVec.ofNat 32 st.toNat := by
    apply BitVec.eq_of_toNat_eq; rw [hnsz32_eq, bv32_ofNat_toNat (by omega)]
  obtain ⟨arH, harH_len, hpreH, hbodyH, harH_0, hszH, hdropH, hcmpH,
      hdst_inH, happend_mk, hm_arH⟩ :=
    m6_write_hdr_wrap hcmpC hcongrC (by rw [hcvC]) hnew3 harC_len
      (by omega) hd1_eq hd2_eq (bv32_ofNat_toNat (by omega)) hsrc_ref hng_src
      hhdr_orig (fun _ => hndPre) (fun j hj => hcvC ▸ hnew_lt j hj) hnew_sub hnew_ent
      (full_mem_cast hm (by dsimp only [sC2, sC1, nhdr0, hdr0]; rw [hst32_of]; rfl))
  have hdst_next_eq : (dst + 3#64 + (st.setWidth 32).setWidth 64).toNat =
      dst.toNat + 3 + st.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat _ (by decide), hnsz32_eq]; simp; omega
  let mark_allowed : Bool := !(decide (s.core.cur_level = 0)) &&
    (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))
  m6_to_group
  refine wp_join_group (M6RsnBranchInv c F_cur s sPre sC R arH
    nsrc.toNat dst.toNat st.toNat mark_allowed) ?_ ?_
  · rintro _ ⟨⟩ mR ⟨arR, rsnsR, harR_len, hrsnsR_len, hpreR, hbodyR, hszR,
        hflR, hredR, hcmpR, hdst_inR, hrsns_lt_dst, hrsns_r0, hrmR, hmkR, hmR⟩
    let hstep_next : ∀ fr' ir' rd' hia',
        (fr' ≠ 0xFFFFFFFF#64 →
          (first_red = 0xFFFFFFFF#64 → fr' = dst ∧ (hdr0 &&& 0x00400000#32) ≠ 0#32) ∧
          (first_red ≠ 0xFFFFFFFF#64 → fr' = first_red)) →
        (hia' = true → fr' ≠ 0xFFFFFFFF#64) →
        wp Γ (Q := Q) (X := X) (Expr.jump JL (Arg.var nsrc,
          Arg.var (dst + 3#64 + (st.setWidth 32).setWidth 64), Arg.var fr', Arg.var ir',
          Arg.var rd', Arg.var hia', Arg.var new_unit, ())) mR :=
      fun fr' ir' rd' hia' hfr_some hhia => by
        rw [wp_jump]
        exact hJL _ fr' ir' rd' hia' mR (m6_rsn_post_step hst_dst hal_le hdst_next_eq hnew3
          (by rw [hnsrc64]; omega) (by rw [hnsrc64]; exact hnxt_le_al)
          (by rw [hnsrc64]; exact hnxt_mem) hlikeC hlenC0 hpre_eqs harC_len
          hcmpC hcmpC_st hlayC hltC hstC_in hfr_to_C htailC hrootL hposL
          hdec_cl0 hout_ok0 hpreH hbodyH harH_0 hhdr_orig hng_src harR_len
          hrsnsR_len hpreR hbodyR hszR hflR hredR hcmpR hdst_inR hrsns_lt_dst
          hrsns_r0 hrmR hmkR hmR rfl hfr_some hhia)
    refine wp_unroll_group fun Js hJs => ?_
    try c0_let_simp
    apply wp_jnz_of
    · intro hc_red; simp only [Arg.val_var] at hc_red; c0_cond hc_red
      try c0_let_simp
      refine wp_unroll_group fun Js1 hJs1 => ?_
      try c0_let_simp
      apply wp_jnz_of
      · intro hc_feq; simp only [Arg.val_var] at hc_feq; c0_cond hc_feq
        m6_tiny_jump; apply hJs1; m6_tiny_jump; apply hJs; m6_tiny_jump
        exact hstep_next dst irred (redd + 1#64) has_iar
          (fun _ => ⟨fun _ => ⟨rfl, by simpa using hc_red⟩, fun h => absurd hc_feq h⟩)
          (fun h => absurd hc_feq (hhas_iar h))
      · intro hc_fne; simp only [Arg.val_var] at hc_fne; c0_cond hc_fne
        m6_tiny_jump; apply hJs1; m6_tiny_jump; apply hJs; m6_tiny_jump
        exact hstep_next first_red irred (redd + 1#64) has_iar
          (fun _ => ⟨fun h => absurd h hc_fne, fun _ => rfl⟩) hhas_iar
    · intro hc_nred; simp only [Arg.val_var] at hc_nred; c0_cond hc_nred
      try c0_let_simp
      refine wp_unroll_group fun Js2 hJs2 => ?_
      try c0_let_simp
      apply wp_jnz_of
      · intro hc_fne; simp only [Arg.val_var] at hc_fne; c0_cond hc_fne
        m6_tiny_jump; apply hJs2; m6_tiny_jump; apply hJs; m6_tiny_jump
        exact hstep_next first_red (irred + 1#64) redd true
          (fun _ => ⟨fun h => absurd h hc_fne, fun _ => rfl⟩) (fun _ => hc_fne)
      · intro hc_feq; simp only [Arg.val_var] at hc_feq; c0_cond hc_feq
        m6_tiny_jump; apply hJs2; m6_tiny_jump; apply hJs; m6_tiny_jump
        exact hstep_next first_red (irred + 1#64) redd has_iar
          (fun h => absurd hc_feq h) hhas_iar
  · intro JR hJR
    have hng_raw : (hdr0 &&& 0x00080000#32) = 0#32 := by
      unfold fullArenaClauseGarbCore at hng_src
      rw [← hhdr_orig] at hng_src; simpa [bne_iff_ne] using hng_src
    have hbits := m6_bv32_nhdr_bits hdr0 hng_raw
    have hdst_fit_arH : dst.toNat + 3 + st.toNat ≤ arH.length := by
      rw [harH_len]; exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_right hdst_src 3) hnew_le)
        hsrc_fit_cap
    m6_tiny_lets; apply wp_jnz_of
    · intro _
      exact m6_sweep_rsn_wp JR hwPre hpre_eqs hlikeC hlenC0 hcap_lt hcv_le
        hcl_lt harL_len harC_len harH_len hszH harH_0 hbodyH hdropH hcmpH
        hdst_inH hdst_src (by omega) hsrc_lt8 hsrc_ref hnsrc64 hsrc_fit_cap
        hdst_fit_arH hsrc_lits_eq hout_ok0 hdec_cl0 hposL happend_mk hnew_lt
        hbits hm_arH (fun mR h => by rw [wp_jump]; exact hJR () mR h)
    · intro hc; simp only [Arg.val_var, bne_eq_false_iff_eq] at hc
      have hrm_unm : ∀ hpos : 0 < s.core.cur_level,
          SweepReasonMapInv sPre.core { sC.core with arena := arH }
            nsrc.toNat (dst.toNat + 3 + st.toNat) := fun hpos => by
        obtain ⟨_, _, _, hrC, _, _, _, hlits_eq⟩ := sweep_pos_lits_eq hout_ok0
          ((hdec_cl0 false).mpr hpos) harL_len harC_len hsrc_fit_cap hdst_src hsrc_lits_eq
          hszH hdropH
        exact m6_sweep_rsn_unmarked_pos hwPre (Nat.le_trans hst_dst hdst_src)
          (hrmkPre hpos) hsrc_ref hnsrc64 hdst_src hsrc_lt8
          (hposL.get hpos).2.2.2.2.2.2 (happend_mk sC.core.rsns hlits_eq) hrC
          (by rw [← hhdr_orig]; exact hc)
      rw [wp_jump]
      exact hJR () m ⟨arH, sC.core.rsns, harH_len, hlenC0.core_ok.rsns_len,
        fun _ _ => rfl, fun _ _ => rfl, hszH,
        by rw [harH_0, Option.getD_some]; exact hbits.2.2.1, rfl,
        CompactPrefixOk.with_rsns hcmpH, hdst_inH, fun _ _ _ => rfl,
        fun _ => rfl, hrm_unm, fun hp _ idx hidx heq => by
          obtain ⟨-, -, -, -, hrC, _⟩ := hout_ok0.1 ((hdec_cl0 false).mpr hp)
          rw [hrC] at heq
          have hnot := m6_rsn_not_src_of_unmarked hwPre
            (Nat.le_trans hst_dst hdst_src) (hrmkPre hp) hsrc_lt8
            (by rw [← hhdr_orig]; exact hc) hidx
          exact absurd heq (m6_rsn_ne_dst_of_not_src_val hwPre hdst_src
            (by omega) (hposL.get hp).2.2.2.2.2.2 hnot hsrc_lt8 hidx),
        full_mem_cast hm_arH rfl⟩

public section

theorem full_arena_sweep_m6_wp (Γ : Env)
    (hSweepBinsRange : Γ.Has "full_sweep_bins_range_m6" fullSweepBinsRangeSpec)
    (hArenaNext : Γ.Has "full_arena_next" Proof.Spec.fullArenaNextSpec)
    (hSweepCopy : Γ.Has "full_sweep_copy" Proof.Spec.fullSweepCopySpec)
    (hMoveRed : Γ.Has "full_move_red_end_m6" fullMoveRedEndSpec)
    (hRewatchRange : Γ.Has "full_rewatch_range_m6" fullRewatchRangeSpec) :
    ∀ a m Q X, step13ArenaSweepSpec a m Q X →
      Func.wp Γ full_arena_sweep_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd0, hdm0, hrmk0, hm, hQ⟩
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hcap_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  have hcap_num : c.arena_cap < 2 ^ 29 := by rw [hdb] at hcap_lt; omega
  have hal_lt : s.core.arena_len < 2 ^ 29 := Nat.lt_of_le_of_lt hal_le hcap_num
  have har_len := hlen.core_ok.arena_len_arr
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
  have hdec_cl0 : ∀ b : Bool, (BitVec.ofNat 64 s.core.cur_level == 0) = b ↔
      (if b then s.core.cur_level = 0 else 0 < s.core.cur_level) := fun b => by
    cases b <;> simp only [beq_eq_false_iff_ne, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
    · constructor
      · intro hne; rcases Nat.eq_zero_or_pos s.core.cur_level with h0 | hpos
        · exact absurd (by simp [h0]) hne
        · exact hpos
      · intro hpos h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this; simp at this; omega
    · constructor
      · intro h0; have := congrArg BitVec.toNat h0
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this
      · intro h0; simp [h0]
  have hpre0 : PreSweepInv' c F0 F_cur s R (0#64, 0#64, ()) m :=
    ⟨Nat.zero_le _, fun h => absurd h (by simp), s.core.arena, hlen, hw, hnd0,
     fun hlt => fullArenaClauseRefs_zero_mem hw.arena hlt,
     ⟨fullArenaClausesInv_zero,
       fun _ hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs] at hr,
       fun _ _ hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs] at hr⟩,
     SweepReasonMapInv.init, fun hpos idx hidx hlvl hlg _ => hrmk0 hpos idx hidx hlvl hlg, hm⟩
  unfold Func.wp full_arena_sweep_m6_body
  m6_to_group
  refine wp_join_group (PreSweepInv' c F0 F_cur s R) ?_ ?_
  · rintro _ ⟨start, _pre_irred, ⟨⟩⟩ mP ⟨hstart_le, hstart_pos, arPre, hlenPre, hwPre, hndPre,
        hst_mem, hcmpPre, hrmPre_init, hrmkPre, hmP⟩
    let sPre : FullState := { s with core := { s.core with arena := arPre } }
    have hpre_al : sPre.core.arena_len = s.core.arena_len := rfl
    have harPre_len : sPre.core.arena.length = c.arena_cap := hlenPre.core_ok.arena_len_arr
    have hpre_eqs : M6PreEqs s sPre := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    m6_steps; c0_call hSweepBinsRange
    refine ⟨c, F0, F_cur, sPre, R, rfl, hlenPre, fun _ => hdm0, hwPre, hmP,
      fun wvec0 wstk0 wlen0 nb0 ws0 m0 hlen0 hlay0 hlt0 hw0 hm0 => ?_⟩
    clear hSweepBinsRange hmP
    let s0 : FullState :=
      { sPre with
        core := { sPre.core with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := 0#64,
                                 num_binary := nb0 }
        scratch := { sPre.scratch with wsort := ws0 } }
    have hlike0 : M6SweepLike s s0 := ⟨s.core.vals, s.core.flags, s.core.lvl, s.core.rsns,
      s.core.trl, s.core.trail_pos, s.core.trail_end, s.core.unassigned, s.core.unflushed,
      wvec0, wstk0, arPre, wlen0, 0#64, nb0, s.core.oom, s.scratch.phases, ws0, rfl⟩
    have hcmp0 : CompactPrefixOk c F_cur s s0.core start.toNat :=
      (arenaPrefix_preserves_compact (k := sPre.core) (k' := s0.core) hcmpPre rfl
        harPre_len harPre_len (by omega) (fun _ _ => rfl)).1
    m6_to_group
    refine wp_join_group (M6SweepExitInv' c F0 F_cur s sPre R start.toNat) ?_ ?_
    · rintro _ ⟨_srcE, dst, first_red, irred, redd, has_iar, unsat, new_unit, ⟨⟩⟩ mE hexit
      clear hArenaNext hSweepCopy hrmPre_init hrmkPre hcmp0 hw0 hlay0 hlt0 hlen0 hm0
        hst_mem hcmpPre
      have hstart0 : s.core.cur_level = 0 → start.toNat = 0 := fun hcl0 =>
        Classical.byContradiction fun hne => by
          have := (hstart_pos (Nat.pos_of_ne_zero hne)).1; omega
      exact m6_sweep_post_wp hMoveRed hRewatchRange hcap_lt hwPre hpre_eqs hnd0 hdm0
        hstart0 hQ hexit
    · intro JE hJE; clear hRewatchRange hQ hMoveRed
      refine wp_loop_inv
        (fun (src, dst, first_red, _ir, _rd, has_iar, new_unit, ()) =>
          M6SweepLoopInv c F0 F_cur s sPre R start.toNat src dst first_red has_iar new_unit)
        (fun (src, _, _, _, _, _, _, ()) _ => s.core.arena_len - src.toNat)
        (fun JL hLoopL => ?_) ?_
      · m6_c0_steps
        refine hLoopL (start, start, 0xFFFFFFFF#64, _pre_irred, 0#64, false, false, ()) m0
          ⟨Nat.le_refl _, Nat.le_refl _, hstart_le, hst_mem, fun h => Bool.noConfusion h,
           s0, 0, hlike0, hlen0, hcmp0, hcmp0, hlay0, hlt0, fun hlt => absurd hlt (by omega),
           .inl rfl, fun _ _ _ => rfl, ⟨fun hcl0 => ?_⟩, ⟨fun _ => ?_⟩, hm0⟩
        · have hst0 : start.toNat = 0 := Classical.byContradiction fun hne => by
            have := (hstart_pos (Nat.pos_of_ne_zero hne)).1; omega
          refine ⟨hst0, ?_, Nat.le_refl _, fun h => Bool.noConfusion h⟩
          have hw_zero := fullWitnessInv_arena_len_zero hw0 ⟨hlay0, fun l hl => by
            have h1 := hlt0 l hl; dsimp only [Arg.val_var] at h1
            rw [hst0] at h1; exact WatchSliceLtOk.toBinOnly h1⟩ hcl0
          simpa only [hst0] using hw_zero
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrmPre_init⟩
      · rintro JL ⟨src, dst, first_red, irred, redd, has_iar, new_unit, ⟨⟩⟩ mL
          ⟨hst_dst, hdst_src, hsrc_le, hsrc_mem, hhas_iar, sL, rwL, hlikeL, hlenL,
           hcmpL, hcmpL_st, hlayL, hltL, hstL_in, hfrL, htailL, hrootL, hposL, hmL⟩ hLoopL
        obtain ⟨hcvL, halL, hclL, hdmL, _, _, _, _, _, _⟩ := hlikeL.unchanged
        have harL_len : sL.core.arena.length = c.arena_cap := hlenL.core_ok.arena_len_arr
        m6_jnz
        · have hsrc_lt : src.toNat < s.core.arena_len := by c0_bound
          have hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre := hsrc_mem hsrc_lt
          have hwf0_full := hwPre.arena.refs_wf src.toNat hsrc_ref
          have hwf0 : src.toNat + 3 ≤ sPre.core.arena_len ∧
              3 ≤ fullArenaClauseSizeCore sPre.core src.toNat ∧
              src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat ≤
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ∧
              fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ≤
                sPre.core.arena_len :=
            ⟨hwf0_full.1, hwf0_full.2.1, hwf0_full.2.2.1, hwf0_full.2.2.2.1⟩
          have hsrc3_le : src.toNat + 3 ≤ s.core.arena_len := hwf0.1
          have hsrc_lt8 : src.toNat < 0x80000000 := by omega
          m6_split
          · have hs2_eq : (src + 2#64).toNat = src.toNat + 2 := bv64_add2_lt (by omega)
            have hs0_lt : src.toNat < sL.core.arena.length := by rw [harL_len]; omega
            have hs2_lt : (src + 2#64).toNat < sL.core.arena.length := by rw [harL_len]; omega
            have hhdr_orig :
                sL.core.arena[src.toNat]'hs0_lt = fullArenaHdrCore sPre.core src.toNat := by
              have h1 := htailL src.toNat (Nat.le_refl _) hsrc_lt
              unfold fullArenaHdrCore; rw [← h1, List.getElem?_eq_getElem hs0_lt, Option.getD_some]
            have hsz_orig : (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat =
                fullArenaClauseSizeCore sPre.core src.toNat := by
              have h1 := htailL (src.toNat + 2) (by omega) (by omega)
              unfold fullArenaClauseSizeCore
              rw [← h1, List.getElem?_eq_getElem (by rw [harL_len]; omega :
                src.toNat + 2 < sL.core.arena.length), Option.getD_some]; simp only [hs2_eq]
            have hsrc32 : (src.setWidth 32).toNat = src.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            have hnxt_eq := fullArenaNextOff_congr_block (htailL src.toNat (Nat.le_refl _) hsrc_lt)
              (htailL (src.toNat + 2) (by omega) (by omega))
              (fun k hk1 hk2 => htailL k (by omega)
                (Nat.lt_of_lt_of_le hk2 (fullArenaNextOff_bounds hwf0.1).2))
            have hnxt_bd := fullArenaNextOff_bounds hwf0.1 (ar := sPre.core.arena)
            have hnxt_le_al : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ≤
                s.core.arena_len := hwf0.2.2.2
            have hnxt_mem : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat =
                s.core.arena_len ∨
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ∈
                  fullArenaClauseRefs sPre := fullArenaClauseRefs_next_or_end hwPre.arena hsrc_ref
            m6_c0_steps; c0_call hArenaNext
            refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
            let nsrc32 := BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
              (src.setWidth 32).toNat)
            have hnsrc64 : (nsrc32.setWidth 64).toNat =
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat := by
              rw [zext_toNat nsrc32 (by decide)]
              dsimp only [nsrc32]; rw [halL, ← hpre_al, hsrc32, hnxt_eq]
              exact bv32_ofNat_toNat (by have := hnxt_le_al; omega)
            have hdec_m : s.core.arena_len - (nsrc32.setWidth 64).toNat <
                s.core.arena_len - src.toNat := by have := hnxt_bd.1; omega
            have hskip_go : (fullArenaClauseGarbCore sPre.core src.toNat = true ∨
                fullArenaClauseSizeCore sPre.core src.toNat < 3 ∨
                sPre.core.arena_len <
                  src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat) →
                JL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar, new_unit, ()) mL :=
              fun hsk => hLoopL _ mL hdec_m ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al,
                fun hlt => by rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega),
                hhas_iar, sL, rwL, hlikeL, hlenL, hcmpL, hcmpL_st, hlayL, hltL, hstL_in, hfrL,
                fun i hi1 hi2 => htailL i (by omega) hi2, hrootL, ⟨fun hpos => by
                  obtain ⟨hnu, hv, hl, ht, htp, hte, hrmL⟩ := hposL.get hpos
                  exact ⟨hnu, hv, hl, ht, htp, hte, hrmL.skip hwPre hsrc_ref hnsrc64 hsk⟩⟩, hmL⟩
            m6_jnz
            · m6_c0_steps; exact hskip_go (Or.inl (by
                unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc))
            · have hng_src : fullArenaClauseGarbCore sPre.core src.toNat = false := by
                unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc
              have hsz3 : 3 ≤ (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat := by
                rw [hsz_orig]; exact hwf0.2.1
              have hfit_pre : src.toNat + 3 +
                  (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat ≤ sPre.core.arena_len := by
                rw [hsz_orig]; have h1 := hwf0.2.2.1; have h2 := hwf0.2.2.2; omega
              m6_jnz
              · exfalso; have : (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat < 3 := by
                  c0_bound
                omega
              · m6_jnz
                · exfalso
                  have : s.core.arena_len <
                      (src + 3#64 + (sL.core.arena[(src + 2#64).toNat]'hs2_lt).setWidth
                        64).toNat := by c0_bound
                  have h1 := bv64_add3_zext_lt (p := src)
                    (sz := sL.core.arena[(src + 2#64).toNat]'hs2_lt) (by omega)
                  rw [h1] at this; change s.core.arena_len < src.toNat + 3 + _ at this; omega
                · clear hskip_go
                  have hsrc_lits_eq :
                      ((sL.core.arena.drop (src.toNat + 3)).take
                        (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat).map BitVec.toNat =
                        fullArenaClauseLitsCore sPre.core src.toNat := by
                    rw [hsz_orig]; unfold fullArenaClauseLitsCore; congr 1
                    apply List.ext_getElem (by simp [harL_len, harPre_len])
                    intro j hj1 _; have hj : j < fullArenaClauseSizeCore sPre.core src.toNat := by
                      simp at hj1; omega
                    simp only [List.getElem_take, List.getElem_drop]
                    have h1 := htailL (src.toNat + 3 + j) (by omega) (by omega)
                    rw [List.getElem?_eq_getElem
                          (by rw [harL_len]; omega : src.toNat + 3 + j < sL.core.arena.length),
                        List.getElem?_eq_getElem
                          (by rw [harPre_len]; omega : src.toNat + 3 + j < sPre.core.arena.length)]
                      at h1
                    exact Option.some.inj h1
                  have hlits_lt_src : ∀ j < (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat,
                      (sL.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * sL.core.cur_vars :=
                    fun j hj => by
                      rw [hcvL, htailL (src.toNat + 3 + j) (by omega) (by omega)]
                      have hbd : src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat ≤
                          sPre.core.arena.length := by
                        change _ ≤ arPre.length; rw [harPre_len]
                        exact Nat.le_trans (by rw [← hsz_orig]; exact hfit_pre) hal_le
                      have hmem : (sPre.core.arena[src.toNat + 3 + j]'(by omega)).toNat ∈
                          fullArenaClauseLitsCore sPre.core src.toNat :=
                        (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, by omega, rfl⟩
                      have hlt_j := hwPre.arena.lits_lt src.toNat hsrc_ref hng_src _ hmem
                      rwa [List.getElem?_eq_getElem
                        (by omega : src.toNat + 3 + j < sPre.core.arena.length), Option.getD_some]
                  m6_c0_steps; c0_call hSweepCopy
                  refine ⟨c, F0, F_cur, sL, R, rfl, hlenL, hdst_src, hsz3,
                    by dsimp only [Arg.val_var]
                       have h1 : sL.core.arena[(src + 2).toNat] =
                           sL.core.arena[(src + 2#64).toNat]'hs2_lt := rfl
                       rw [h1, hsz_orig, halL]
                       have := hpre_al; have := hwf0.2.2.1; have := hwf0.2.2.2; omega,
                    by rw [hclL]; exact Bool.eq_iff_iff.mpr (by simpa using hdec_cl0 true),
                    hlits_lt_src, fun hrt => ?_, hmL,
                    fun st arC valsC flagsC lvlC rsnsC trlC tpC teC unassC unflC wvecC wstkC
                      wlenC wuC nbC oomC phC wsC mC hlenC0 houtC0 hout_f hout_t hmC0 => ?_⟩
                  · have hcl0 := (hdec_cl0 true).mp hrt
                    have hrtL := hrootL.get hcl0
                    have hbinL : BinOnlyWatchesInv F_cur sL.core := ⟨hlayL, fun l hl => by
                      have h1 := hltL l (hcvL ▸ hl); rw [hrtL.1] at h1
                      exact WatchSliceLtOk.toBinOnly h1⟩
                    exact ⟨hrtL.2.1, hbinL.toFull, by
                      have h1 : List.map BitVec.toNat
                          (List.take sL.core.arena[(src + 2).toNat].toNat
                            (List.drop (src.toNat + 3) sL.core.arena)) =
                          fullArenaClauseLitsCore sPre.core src.toNat := hsrc_lits_eq
                      dsimp only [Arg.val_var]; rw [h1]
                      exact hwPre.arena.entails src.toNat hsrc_ref hng_src⟩
                  let sC : FullState :=
                    { core := { sL.core with arena := arC, vals := valsC, flags := flagsC,
                                             lvl := lvlC, rsns := rsnsC, trl := trlC,
                                             trail_pos := tpC, trail_end := teC,
                                             unassigned := unassC,
                                             unflushed := unflC, wvec := wvecC, wstk := wstkC,
                                             wlen := wlenC, wusable := wuC, num_binary := nbC,
                                             oom := oomC }
                      scratch := { sL.scratch with phases := phC, wsort := wsC } }
                  have hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst
                      (sL.core.arena[(src + 2#64).toNat]'hs2_lt)
                      (BitVec.ofNat 64 s.core.cur_level == 0) st :=
                    ⟨hout_f, fun hrt => by
                      obtain ⟨h1, hbin, hrest⟩ := hout_t hrt
                      exact ⟨h1, hbin, hrest⟩⟩
                  have hlikeC : M6SweepLike s sC := hlikeL.of_copy
                  have harC_len : sC.core.arena.length = c.arena_cap := hlenC0.core_ok.arena_len_arr
                  have hpreC : PrefixAgrees dst.toNat sL.core.arena sC.core.arena := fun idx hidx =>
                    houtC0 idx (Or.inl (Nat.lt_add_right 3 hidx))
                  have htailC : ∀ i, (nsrc32.setWidth 64).toNat ≤ i → i < s.core.arena_len →
                      sC.core.arena[i]? = sPre.core.arena[i]? := fun i hi1 hi2 => by
                    have hfit_n : src.toNat + 3 + (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat ≤
                        (nsrc32.setWidth 64).toNat := by
                      rw [hnsrc64, hsz_orig]; exact hwf0.2.2.1
                    have hge_d : dst.toNat + 3 +
                        (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat ≤ i :=
                      Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hdst_src 3) _)
                        (Nat.le_trans hfit_n hi1)
                    rw [houtC0 i (Or.inr hge_d)]
                    exact htailL i (Nat.le_trans (Nat.le_add_right src.toNat 3)
                      (Nat.le_trans (Nat.le_add_right (src.toNat + 3) _)
                        (Nat.le_trans hfit_n hi1))) hi2
                  obtain ⟨hcvC, halC, _⟩ := hlikeC.unchanged
                  obtain ⟨hcmpC, hcongrC⟩ := arenaPrefix_preserves_compact (s := s) (k := sL.core)
                    (k' := sC.core) hcmpL (hcvC.trans hcvL.symm) harL_len harC_len (by omega) hpreC
                  obtain ⟨hcmpC_st, hkeepC_st⟩ := m6_refs_lt_prefix_transfer hcmpL_st
                    (hcvC.trans hcvL.symm) harL_len harC_len (by omega) (by rw [halC]; omega)
                    (by omega) (fun i hi => hpreC i (by omega))
                  have hcl0_of_sp :
                      st = 0xFFFFFFFE#64 ∨ st = 0xFFFFFFFD#64 ∨ st = 1#64 ∨ st = 0xFFFFFFFF#64 →
                      s.core.cur_level = 0 := fun hsp => Classical.byContradiction fun hne => by
                    have hst_old := (hout_ok0.1 ((hdec_cl0 false).mpr (Nat.pos_of_ne_zero hne))).1
                    have hst_lt : st.toNat < 2 * dimacsBound := by
                      rw [hst_old, zext_toNat _ (by decide), hsz_orig]
                      have := hwf0.2.2.1; have := hwf0.2.2.2; omega
                    rcases hsp with rfl | rfl | rfl | rfl
                    · revert hst_lt; decide
                    · revert hst_lt; decide
                    · have h1 := congrArg BitVec.toNat hst_old
                      rw [zext_toNat _ (by decide), show (1#64).toNat = 1 from rfl] at h1; omega
                    · revert hst_lt; decide
                  have hfr_to_C :
                      M6FirstRedOk c F_cur s sPre sC start.toNat dst.toNat rwL first_red := by
                    rcases hfrL with rfl | ⟨h1, h2, hcmpL_fr, hrw0, hmvL, hfr_inL, hrm_mk⟩
                    · exact .inl rfl
                    · refine .inr ⟨h1, h2, (arenaPrefix_preserves_compact hcmpL_fr
                        (hcvC.trans hcvL.symm) harL_len harC_len (by omega)
                        (fun i hi => hpreC i (by omega))).1, hrw0,
                        hmvL.congr (fun i _ hi => hpreC i (by omega)),
                        by rw [hcongrC.1]; exact hfr_inL, ⟨fun hp r hr idx hidx heq => ?_⟩⟩
                      obtain ⟨-, hvC, -, -, hrC, _⟩ := hout_ok0.1 ((hdec_cl0 false).mpr hp)
                      have hr' := hr.congr (fun i _ hi => (hpreC i (by omega)).symm)
                      obtain ⟨ha, j, hj, hb, hc⟩ :=
                        hrm_mk.get hp r hr' idx hidx (by rw [← hrC]; exact heq)
                      have hrb := hr'.bounds
                      exact ⟨by rw [hpreC r (by omega)]; exact ha,
                        j, by rw [hpreC (r + 2) (by omega)]; exact hj,
                        by rw [hpreC (r + 3 + j) (by omega), hvC]; exact ⟨hb, hc⟩⟩
                  have hstC_in : start.toNat < dst.toNat →
                      start.toNat ∈
                        fullArenaClauseRefsCore { sC.core with arena_len := dst.toNat } :=
                    fun hlt => by rw [hcongrC.1]; exact hstL_in hlt
                  m6_tiny_lets; apply wp_jnz_of
                  · intro hc; simp only [Arg.val_var, beq_iff_eq] at hc
                    have hcl0 := hcl0_of_sp (Or.inl hc)
                    obtain ⟨hwC, hbinC, hteC, _, hunsC, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                    dsimp only [sC] at hteC; have hbinC' := FullBinOnlyWatchesInv.toBinOnly hbinC
                    have hst0 := (hrootL.get hcl0).1; rw [wp_jump]
                    exact hJE (src, dst, first_red, irred, redd, has_iar, true, new_unit, ()) mC
                      ⟨hst_dst, by omega, hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st,
                       hbinC'.1, fun l hl => by
                         rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC'.slices l hl),
                       hstC_in, hwC, hfr_to_C, fun hp => absurd hcl0 (by omega),
                       fun _ => ⟨hcl0, hunsC hc⟩, fun hnu => ⟨hcl0, by
                         change s.core.trail_end < teC
                         have := (hrootL.get hcl0).2.2.2 hnu; omega⟩,
                       fun hpos => absurd hcl0 (by omega), hmC0⟩
                  · intro hc; simp only [Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc
                    m6_tiny_lets; apply wp_jnz_of
                    · intro hc1; simp only [Arg.val_var, beq_iff_eq] at hc1
                      have hcl0 := hcl0_of_sp (Or.inr (Or.inl hc1))
                      obtain ⟨hwC, hbinC, hteC, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                      dsimp only [sC] at hteC; have hbinC' := FullBinOnlyWatchesInv.toBinOnly hbinC
                      have hst0 := (hrootL.get hcl0).1; rw [wp_jump]
                      exact hJE (src, dst, first_red, irred, redd, has_iar, false, new_unit, ()) mC
                        ⟨hst_dst, by omega, hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st,
                         hbinC'.1, fun l hl => by
                           rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC'.slices l hl),
                         hstC_in, hwC, hfr_to_C, fun hp => absurd hcl0 (by omega),
                         fun h => Bool.noConfusion h, fun hnu => ⟨hcl0, by
                           change s.core.trail_end < teC
                           have := (hrootL.get hcl0).2.2.2 hnu; omega⟩,
                         fun hpos => absurd hcl0 (by omega), hmC0⟩
                    · intro hc1; simp only [Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc1
                      m6_tiny_lets; apply wp_jnz_of
                      · intro hc2; simp only [Arg.val_var, beq_iff_eq] at hc2
                        have hcl0 := hcl0_of_sp (Or.inr (Or.inr (Or.inl hc2)))
                        obtain ⟨hwC, hbinC, hteC, _, _, _, _, hunitC, _⟩ :=
                          hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                        dsimp only [sC] at hteC
                        have hbinC' := FullBinOnlyWatchesInv.toBinOnly hbinC
                        have hst0 := (hrootL.get hcl0).1; rw [wp_jump]
                        exact hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar,
                            true, ()) mC hdec_m
                          ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al,
                           fun hlt => by
                             rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega),
                           hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st, hbinC'.1,
                           fun l hl => by
                             rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC'.slices l hl),
                           hstC_in, hfr_to_C, htailC, ⟨fun _ => ⟨hst0, hwC,
                             by change s.core.trail_end ≤ teC
                                have := (hrootL.get hcl0).2.2.1; omega,
                             fun _ => by change s.core.trail_end < teC
                                         have := (hrootL.get hcl0).2.2.1
                                         have huc := hunitC hc2; dsimp only [sC] at huc; omega⟩⟩,
                           ⟨fun hp => absurd hcl0 (by omega)⟩, hmC0⟩
                      · intro hc2; simp only [Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc2
                        m6_tiny_lets; apply wp_jnz_of
                        · intro hc3; simp only [Arg.val_var, beq_iff_eq] at hc3
                          have hcl0 := hcl0_of_sp (Or.inr (Or.inr (Or.inr hc3)))
                          obtain ⟨hwC, hbinC, hteC, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                          dsimp only [sC] at hteC
                          have hbinC' := FullBinOnlyWatchesInv.toBinOnly hbinC
                          have hst0 := (hrootL.get hcl0).1; rw [wp_jump]
                          exact hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar,
                              new_unit, ()) mC hdec_m
                            ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al,
                             fun hlt => by
                               rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega),
                             hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st, hbinC'.1,
                             fun l hl => by
                               rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC'.slices l hl),
                             hstC_in, hfr_to_C, htailC, ⟨fun _ => ⟨hst0, hwC,
                               by change s.core.trail_end ≤ teC
                                  have := (hrootL.get hcl0).2.2.1; omega,
                               fun hnu => by change s.core.trail_end < teC
                                             have := (hrootL.get hcl0).2.2.2 hnu; omega⟩⟩,
                             ⟨fun hp => absurd hcl0 (by omega)⟩, hmC0⟩
                        · intro hc3
                          simp only [Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc3
                          obtain ⟨hnew3, hnew_le, hnew_lt, hnew_sub, hnew_ent, hlayC, hltC⟩ :=
                            m6_sweep_copy_new_props hwPre (fun h => (hrootL.get h).1) hltL hlayL
                              (fun _ => hkeepC_st) hout_ok0 hdec_cl0 hcvL
                              (hcvC.trans hcvL.symm) hsz3 harL_len harC_len (by omega)
                              hdst_src hsrc_ref hng_src hsrc_lits_eq
                              (fun j hj => hcvL ▸ hlits_lt_src j hj)
                              (by assumption) (by assumption) (by assumption) (by assumption)
                          have hsrc_fit_cap : src.toNat + 3 +
                              (sL.core.arena[(src + 2#64).toNat]'hs2_lt).toNat ≤ c.arena_cap := by
                            rw [hsz_orig]; exact Nat.le_trans hwf0.2.2.1
                              (Nat.le_trans hwf0.2.2.2 hal_le)
                          exact m6_sweep_post_copy_wp hwPre hpre_eqs hndPre hlikeL hlikeC hlenC0
                            hcap_lt hcv_le hcl_lt hal_le harL_len harC_len hpreC htailC hcmpC
                            hcmpC_st hcongrC hst_dst hdst_src hsrc_lt8 hsrc_ref hnsrc64
                            hnxt_le_al hnxt_mem hsrc_fit_cap hsz_orig hwf0 hng_src hs0_lt
                            hhdr_orig hsrc_lits_eq hstC_in hfr_to_C hhas_iar hrootL hposL
                            hout_ok0 hdec_cl0 hnew3 hnew_le (fun j hj => hcvC ▸ hnew_lt j hj)
                            hnew_sub hnew_ent hlayC hltC hrmkPre hmC0
                            (fun _ _ _ _ _ mR hinv => hLoopL _ mR hdec_m hinv)
        · have hsrc_end : src.toNat = s.core.arena_len := by c0_bound
          m6_c0_steps
          have hwEnd := m6_sweep_end_witness hwPre (fun hs => by rw [hdmL]; exact hdm0) hlenL hlikeL
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hst_dst (by rw [halL]; omega) hcmpL hcmpL_st
            hlayL hltL hrootL (hsrc_end ▸ hposL)
          refine hJE (src, dst, first_red, irred, redd, has_iar, false, new_unit, ()) mL
            ⟨hst_dst, by omega, hhas_iar, sL, rwL, hlikeL, hlenL, hcmpL, hcmpL_st, hlayL, hltL,
             hstL_in, hwEnd, hfrL, fun hp => hsrc_end ▸ (hposL.get hp).2.2.2.2.2.2,
             fun h => Bool.noConfusion h, fun hnu => ?_, fun hpos => ?_, hmL⟩
          · by_cases hcl0 : s.core.cur_level = 0
            · exact ⟨hcl0, (hrootL.get hcl0).2.2.2 hnu⟩
            · exact absurd ((hposL.get (Nat.pos_of_ne_zero hcl0)).1) (by simp [hnu])
          · obtain ⟨hnu, hv, hl, ht, htp, hte, _⟩ := hposL.get hpos
            exact ⟨rfl, hnu, hv, hl, ht, htp, hte⟩
  · intro JPre hJPre
    exact m6_pre_sweep_wp JPre hlen hcap_lt hw hnd0 hrmk0 hm hpre0 hJPre

theorem full_arena_sweep_wp (Γ : Env)
    (hM6 : Γ.Has "full_arena_sweep_m6" step13ArenaSweepSpec) :
    ∀ a m Q X, step13ArenaSweepSpec a m Q X →
      Func.wp Γ full_arena_sweep_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_arena_sweep_body
  m6_steps; refine LeanQbe.T.wp_call_of_spec _ _ (hM6 _ _ _ _ ?_)
  simpa only [Arg.val_var, vals_cons, vals_nil, wp_ret, collect_fwd1_sweep] using hs

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
