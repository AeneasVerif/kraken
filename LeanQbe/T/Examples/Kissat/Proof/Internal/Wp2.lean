/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Internal State Init & Memory Init WP Proofs (`Proof.Internal.Wp2`)

Parametric `(Γ : Env)` `Func.wp` proofs (`0` legacy `Full*` imports, `0` `@[expose]` theorems):
1. `full_init_state_m5_wp` (`M5` ext/scr capacities, `full_avail_to_arrays`, `FullSparseInv`)
2. `full_init_state_wp` (wrapper delegating to `full_init_state_m5`)
3. `full_m6_mem_init_wp` (`3,456 B` carve + `FullM6HdrMem` pack + `m6_hdr_init`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Internal

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Internal

local elab "in_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "in_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

private theorem wp2_sext2_mod64 : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
attribute [local bv_c0] wp2_sext2_mod64

local macro "fp_jnz_t" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_true $h:ident
   in_steps))

local macro "fp_jnz_f" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_false $h:ident
   in_steps))

/-! ## 1. Arithmetic, Separation & Array Peeling Helpers -/

private def fullInitDelCap (rem : Nat) : Nat :=
  if 524288 ≤ rem then 4096 else 8

private theorem fullInitDelCap_lt {rem : Nat} : fullInitDelCap rem < dimacsBound := by
  unfold fullInitDelCap dimacsBound; split <;> omega

private theorem bv64_mul_nat3 (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem bv64_shl2_val {x : BitVec 64} (_hx : 4 * x.toNat < 2 ^ 64) :
    x <<< (((2 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (4 * x.toNat) := by
  simpa [show ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 from rfl, Nat.mul_comm,
    bv_ofNat_toNat_eq x] using bv_shl_sext2 (n := x.toNat)

private theorem bv64_ofNat_toNat' {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

private theorem last_learned_getD_ff_of_zero {xs : List (BitVec 32)}
    (h : ∀ i < 16, xs[i]?.getD 0#32 = 0xFFFFFFFF#32) :
    ∀ i < 8, xs[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := fun i hi => by
  have hi16 := h i (by omega)
  cases hx : xs[i]? with
  | none => rfl
  | some v => rw [hx, Option.getD_some] at hi16; simp [hi16]

private structure FullInitArrs (c : FullCfg) where
  (vals lit_mark mrk walk_vals phases phases_target phases_best walk_best : List (BitVec 8))
  (flags lvl rsns trl trail_pos tmp min_clr frame_trail frame_dec wvec repr min_stk :
    List (BitVec 32))
  (arena wstk heap pos shrink_stk q_prev q_next q_stamp : List (BitVec 32))
  (wsort work_stk1 work_stk2 tarjan_mark tarjan_reach : List (BitVec 32))
  (score sim_sig : List (BitVec 64))
  (glue_used last_learned delayed red_refs extend_stk scratch_buf : List (BitVec 32))
  ok : vals.length = 2 * c.max_vars ∧ lit_mark.length = 2 * c.max_vars ∧
    mrk.length = c.max_vars ∧ walk_vals.length = 2 * c.max_vars ∧
    phases.length = c.max_vars ∧ phases_target.length = c.max_vars ∧
    phases_best.length = c.max_vars ∧ walk_best.length = c.max_vars ∧
    flags.length = c.max_vars ∧ lvl.length = c.max_vars ∧ rsns.length = c.max_vars ∧
    trl.length = c.max_vars ∧ trail_pos.length = c.max_vars ∧ tmp.length = c.max_vars ∧
    min_clr.length = c.max_vars ∧ frame_trail.length = c.max_vars + 1 ∧
    frame_dec.length = c.max_vars + 1 ∧ wvec.length = 4 * c.max_vars ∧
    repr.length = 2 * c.max_vars ∧ min_stk.length = 2 * c.minDepth ∧
    arena.length = c.arena_cap ∧ wstk.length = c.wcap ∧ heap.length = c.max_vars ∧
    pos.length = c.max_vars ∧ shrink_stk.length = c.max_vars ∧ q_prev.length = c.max_vars ∧
    q_next.length = c.max_vars ∧ q_stamp.length = c.max_vars ∧ wsort.length = 2 * c.max_vars ∧
    work_stk1.length = 2 * c.max_vars ∧ work_stk2.length = 2 * c.max_vars ∧
    tarjan_mark.length = 2 * c.max_vars ∧ tarjan_reach.length = 2 * c.max_vars ∧
    score.length = c.max_vars ∧ sim_sig.length = c.max_vars ∧ glue_used.length = 64 ∧
    last_learned.length = 16 ∧ delayed.length = 3 * c.delayed_cap ∧
    red_refs.length = c.red_cap ∧ extend_stk.length = c.extend_cap ∧
    scratch_buf.length = c.scratch_cap

private def initFullState (c : FullCfg) (d_cur d_val fuel : BitVec 64) (a : FullInitArrs c) :
    FullState :=
  { core :=
      { d_cur := d_cur, d_val := d_val, cur_vars := c.mv,
        unassigned := 0#64, arena_len := 0, wlen := 1, wusable := 0#64,
        arena_garbage := 0#64, first_reducible := 0xFFFFFFFF#64, num_irred := 0#64,
        num_redundant := 0#64, num_binary := 0#64, unflushed := 0#64, probing := 0#64,
        trail_end := 0, propagated := 0, cur_level := 0, fuel := fuel,
        confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64,
        confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0,
        min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64,
        vals := a.vals, lit_mark := a.lit_mark, mrk := a.mrk, flags := a.flags, lvl := a.lvl,
        rsns := a.rsns, trl := a.trl, trail_pos := a.trail_pos, tmp := a.tmp,
        min_clr := a.min_clr, frame_trail := a.frame_trail, frame_dec := a.frame_dec,
        wvec := a.wvec, repr := a.repr, min_stk := a.min_stk, arena := a.arena, wstk := a.wstk }
    scratch :=
      { heap_len := 0, scinc := 0x3FF0000000000000#64, rel_period := 1024#64,
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64,
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64,
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64,
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64,
        search_ticks := 0#64, q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64,
        q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64, q_cur_stamp := 0#64,
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64,
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64,
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64,
        ema_fast_exp := 0x3FF0000000000000#64, ema_slow_biased := 0#64,
        ema_slow_exp := 0x3FF0000000000000#64, extend_len := 0,
        rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64),
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64,
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64,
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64,
        subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64,
        bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64,
        fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64, walk_vals := a.walk_vals,
        phases := a.phases, phases_target := a.phases_target, phases_best := a.phases_best,
        walk_best := a.walk_best, heap := a.heap, pos := a.pos, shrink_stk := a.shrink_stk,
        q_prev := a.q_prev, q_next := a.q_next, q_stamp := a.q_stamp, wsort := a.wsort,
        work_stk1 := a.work_stk1, work_stk2 := a.work_stk2, tarjan_mark := a.tarjan_mark,
        tarjan_reach := a.tarjan_reach, score := a.score, sim_sig := a.sim_sig,
        glue_used := a.glue_used, last_learned := a.last_learned, delayed := a.delayed,
        red_refs := a.red_refs, extend_stk := a.extend_stk, scratch_buf := a.scratch_buf } }

private theorem peel_bytes_block (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ vals wvals lmrk mrk ph ptgt pbst wbst : List (BitVec 8),
      vals.length = 2 * c.max_vars ∧ wvals.length = 2 * c.max_vars ∧
      lmrk.length = 2 * c.max_vars ∧ mrk.length = c.max_vars ∧ ph.length = c.max_vars ∧
      ptgt.length = c.max_vars ∧ pbst.length = c.max_vars ∧ wbst.length = c.max_vars ∧
      ((((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pLitMark lmrk ⋆
          array (t := i8) c.pMark mrk) ⋆
         (array (t := i8) c.pWalkVals wvals ⋆ array (t := i8) c.pPhases ph ⋆
          array (t := i8) c.pPhasesTarget ptgt ⋆ array (t := i8) c.pPhasesBest pbst ⋆
          array (t := i8) c.pWalkBest wbst)) ⋆ c.padBytes) ⋆
        region c.pFlags (c.avail - (1152 + 3 * valsBytes c.max_vars +
          5 * markBytes c.max_vars))) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hv := valsBytes_ge c.max_vars; have hmk := markBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have hle : fullFixedBytes c.max_vars ≤ c.avail := by omega
  have h0 : ((emp ⋆ emp) ⋆ region c.pVals (c.avail - 1152)) m := by
    rw [emp_sep, emp_sep]; exact hm
  let vb := valsBytes c.max_vars; let mb := markBytes c.max_vars
  let rem1 := c.avail - 1152 - vb
  obtain ⟨vals, hv1, h1⟩ := peel_step_i8 (b := c.pWalkVals) (2 * c.max_vars) vb rem1
    (c.avail - 1152) h0 (by rfl) (by omega) hv (by omega)
  obtain ⟨wvals, hv2, h2⟩ := peel_step_i8 (b := c.pLitMark) (2 * c.max_vars) vb (rem1 - vb)
    rem1 h1 (by rfl) (by omega) hv (by omega)
  obtain ⟨lmrk, hv3, h3⟩ := peel_step_i8 (b := c.pMark) (2 * c.max_vars) vb (rem1 - 2 * vb)
    (rem1 - vb) h2 (by rfl) (by omega) hv (by omega)
  obtain ⟨mrk, hm1, h4⟩ := peel_step_i8 (b := c.pPhases) c.max_vars mb
    (rem1 - 2 * vb - mb) (rem1 - 2 * vb) h3 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ph, hm2, h5⟩ := peel_step_i8 (b := c.pPhasesTarget) c.max_vars mb
    (rem1 - 2 * vb - 2 * mb) (rem1 - 2 * vb - mb) h4 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ptgt, hm3, h6⟩ := peel_step_i8 (b := c.pPhasesBest) c.max_vars mb
    (rem1 - 2 * vb - 3 * mb) (rem1 - 2 * vb - 2 * mb) h5 (by rfl) (by omega) hmk (by omega)
  obtain ⟨pbst, hm4, h7⟩ := peel_step_i8 (b := c.pWalkBest) c.max_vars mb
    (rem1 - 2 * vb - 4 * mb) (rem1 - 2 * vb - 3 * mb) h6 (by rfl) (by omega) hmk (by omega)
  obtain ⟨wbst, hm5, h8⟩ := peel_step_i8 (b := c.pFlags) c.max_vars mb
    (c.avail - (1152 + 3 * vb + 5 * mb)) (rem1 - 2 * vb - 4 * mb) h7
    (by rfl) (by omega) hmk (by omega)
  simp only [emp_sep] at h8
  refine ⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5, ?_⟩
  unfold FullCfg.padBytes
  dsimp only [vb, mb] at h8
  exact sep_mono2 (sep_mono2 (fun _ h => sep_ac h)
    (fun _ h => by simp only [sep_assoc] at h ⊢; exact h)) (fun _ h => h) m h8

private theorem peel_u32_5_block (max_v : Nat) (k1 k2 k3 k4 k5 : Nat)
    (a1 a2 a3 a4 a5 b : BitVec 64) {rtot rnext : Nat} {m : Mem 64}
    (ha2 : a2 = a1 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha3 : a3 = a2 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha4 : a4 = a3 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha5 : a5 = a4 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hb : b = a5 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hm : region a1 rtot m)
    (hk1 : 4 * k1 ≤ u32FullBytes max_v := by omega)
    (hk2 : 4 * k2 ≤ u32FullBytes max_v := by omega)
    (hk3 : 4 * k3 ≤ u32FullBytes max_v := by omega)
    (hk4 : 4 * k4 ≤ u32FullBytes max_v := by omega)
    (hk5 : 4 * k5 ≤ u32FullBytes max_v := by omega)
    (hrem : 5 * u32FullBytes max_v + rnext = rtot := by omega)
    (hle : rtot ≤ 2 ^ 64 := by omega) :
    ∃ x1 x2 x3 x4 x5 : List (BitVec 32),
      x1.length = k1 ∧ x2.length = k2 ∧ x3.length = k3 ∧ x4.length = k4 ∧ x5.length = k5 ∧
      ((array (t := i32) a1 x1 ⋆ array (t := i32) a2 x2 ⋆ array (t := i32) a3 x3 ⋆
        array (t := i32) a4 x4 ⋆ array (t := i32) a5 x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)) ⋆
       region b rnext) m := by
  let ub := u32FullBytes max_v
  have h0 : ((emp ⋆ emp) ⋆ region a1 rtot) m := by rw [emp_sep, emp_sep]; exact hm
  obtain ⟨x1, hx1, h1⟩ := peel_step_i32 (b := a2) k1 ub (4 * ub + rnext) rtot h0
    ha2.symm (by omega) hk1 (by omega)
  obtain ⟨x2, hx2, h2⟩ := peel_step_i32 (b := a3) k2 ub (3 * ub + rnext) (4 * ub + rnext) h1
    ha3.symm (by omega) hk2 (by omega)
  obtain ⟨x3, hx3, h3⟩ := peel_step_i32 (b := a4) k3 ub (2 * ub + rnext) (3 * ub + rnext) h2
    ha4.symm (by omega) hk3 (by omega)
  obtain ⟨x4, hx4, h4⟩ := peel_step_i32 (b := a5) k4 ub (ub + rnext) (2 * ub + rnext) h3
    ha5.symm (by omega) hk4 (by omega)
  obtain ⟨x5, hx5, h5⟩ := peel_step_i32 (b := b) k5 ub rnext (ub + rnext) h4
    hb.symm (by omega) hk5 (by omega)
  simp only [emp_sep] at h5
  exact ⟨x1, x2, x3, x4, x5, hx1, hx2, hx3, hx4, hx5, sep_ac h5⟩

private theorem peel_tail_block (c : FullCfg) {m : Mem 64}
    (hm : region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars)) m) :
    ∃ (wvec repr wsort ws1 ws2 tmk trc : List (BitVec 32))
      (sc sig : List (BitVec 64))
      (mstk gu ll ar wstk del red ext sbuf : List (BitVec 32)),
      (wvec.length = 4 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
        wsort.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
        ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
        trc.length = 2 * c.max_vars ∧ sc.length = c.max_vars ∧
        sig.length = c.max_vars ∧ mstk.length = 2 * c.minDepth ∧
        gu.length = 64 ∧ ll.length = 16 ∧ ar.length = c.arena_cap ∧
        wstk.length = c.wcap ∧ del.length = 3 * c.delayed_cap ∧
        red.length = c.red_cap ∧ ext.length = c.extend_cap ∧ sbuf.length = c.scratch_cap) ∧
      ((array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pRepr repr ⋆
        array (t := i32) c.pMinStk mstk ⋆
        array (t := i32) c.pArena ar ⋆ array (t := i32) c.pWstk wstk) ⋆
       ((array (t := i32) c.pWsort wsort ⋆ array (t := i32) c.pWorkStk1 ws1 ⋆
          array (t := i32) c.pWorkStk2 ws2 ⋆ array (t := i32) c.pTarjanMark tmk ⋆
          array (t := i32) c.pTarjanReach trc) ⋆
        (array64 c.pScore sc ⋆ array64 c.pSimSig sig ⋆
          array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pLastLearned ll) ⋆
        (array (t := i32) c.pDelayed del ⋆ array (t := i32) c.pRedRefs red ⋆
          array (t := i32) c.pExtendStk ext ⋆ array (t := i32) c.pScratchBuf sbuf)) ⋆
       region c.pSlack c.slack) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap; have hd := c.hdel
  have hr := c.hred; have he := c.hext; have hs := c.hscr
  unfold dimacsBound at hmx ha hw hd hr he hs
  have hfit := c.havail_fit; have hsz := c.hsize; have hmd := fullMinDepthOf_le c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have hslk : c.slack = c.avail - (fullFixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) := rfl
  let r0 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
    15 * u32FullBytes c.max_vars)
  have h0 : (emp ⋆ region c.pWvec r0) m := by rw [emp_sep]; exact hm
  obtain ⟨wvec, l1, h1⟩ := peel_step_exact_i32 (b := c.pRepr) (4 * c.max_vars)
    (r0 - 16 * c.max_vars) r0 h0 (show c.pWvec + BitVec.ofNat 64 (4 * (4 * c.max_vars)) = c.pRepr
      by unfold FullCfg.pRepr; rw [show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨repr, l2, h2⟩ := peel_step_exact_i32 (b := c.pWsort) (2 * c.max_vars)
    (r0 - 24 * c.max_vars) (r0 - 16 * c.max_vars) h1
    (show c.pRepr + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWsort by
      unfold FullCfg.pWsort; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨wsort, l3, h3⟩ := peel_step_exact_i32 (b := c.pWorkStk1) (2 * c.max_vars)
    (r0 - 32 * c.max_vars) (r0 - 24 * c.max_vars) h2
    (show c.pWsort + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk1 by
      unfold FullCfg.pWorkStk1; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨ws1, l4, h4⟩ := peel_step_exact_i32 (b := c.pWorkStk2) (2 * c.max_vars)
    (r0 - 40 * c.max_vars) (r0 - 32 * c.max_vars) h3
    (show c.pWorkStk1 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk2 by
      unfold FullCfg.pWorkStk2; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨ws2, l5, h5⟩ := peel_step_exact_i32 (b := c.pTarjanMark) (2 * c.max_vars)
    (r0 - 48 * c.max_vars) (r0 - 40 * c.max_vars) h4
    (show c.pWorkStk2 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanMark by
      unfold FullCfg.pTarjanMark; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨tmk, l6, h6⟩ := peel_step_exact_i32 (b := c.pTarjanReach) (2 * c.max_vars)
    (r0 - 56 * c.max_vars) (r0 - 48 * c.max_vars) h5
    (show c.pTarjanMark + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanReach by
      unfold FullCfg.pTarjanReach; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨trc, l7, h7⟩ := peel_step_exact_i32 (b := c.pScore) (2 * c.max_vars)
    (r0 - 64 * c.max_vars) (r0 - 56 * c.max_vars) h6
    (show c.pTarjanReach + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pScore by
      unfold FullCfg.pScore; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨sc, l8, h8⟩ := peel_step_exact_i64 (b := c.pSimSig) c.max_vars
    (r0 - 72 * c.max_vars) (r0 - 64 * c.max_vars) h7 rfl (by omega) (by omega)
  obtain ⟨sig, l9, h9⟩ := peel_step_exact_i64 (b := c.pMinStk) c.max_vars
    (r0 - 80 * c.max_vars) (r0 - 72 * c.max_vars) h8 rfl (by omega) (by omega)
  let r10 := r0 - 80 * c.max_vars
  obtain ⟨mstk, l10, h10⟩ := peel_step_exact_i32 (b := c.pGlueUsed) (2 * c.minDepth)
    (r10 - 8 * c.minDepth) r10 h9
    (show c.pMinStk + BitVec.ofNat 64 (4 * (2 * c.minDepth)) = c.pGlueUsed by
      unfold FullCfg.pGlueUsed; rw [show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega])
    (by omega) (by omega)
  obtain ⟨gu, l11, h11⟩ := peel_step_exact_i32 (b := c.pLastLearned) 64
    (r10 - 8 * c.minDepth - 256) (r10 - 8 * c.minDepth) h10 rfl (by omega) (by omega)
  obtain ⟨ll, l12, h12⟩ := peel_step_exact_i32 (b := c.pArena) 16
    (r10 - 8 * c.minDepth - 320) (r10 - 8 * c.minDepth - 256) h11 rfl (by omega) (by omega)
  let r13 := r10 - 8 * c.minDepth - 320
  obtain ⟨ar, l13, h13⟩ := peel_step_exact_i32 (b := c.pWstk) c.arena_cap
    (r13 - 4 * c.arena_cap) r13 h12 rfl (by omega) (by omega)
  obtain ⟨wstk, l14, h14⟩ := peel_step_exact_i32 (b := c.pDelayed) c.wcap
    (r13 - 4 * c.arena_cap - 4 * c.wcap) (r13 - 4 * c.arena_cap) h13 rfl (by omega) (by omega)
  obtain ⟨del, l15, h15⟩ := peel_step_exact_i32 (b := c.pRedRefs) (3 * c.delayed_cap)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    (r13 - 4 * c.arena_cap - 4 * c.wcap) h14
    (show c.pDelayed + BitVec.ofNat 64 (4 * (3 * c.delayed_cap)) = c.pRedRefs by
      unfold FullCfg.pRedRefs; rw [show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega])
    (by omega) (by omega)
  obtain ⟨red, l16, h16⟩ := peel_step_exact_i32 (b := c.pExtendStk) c.red_cap
    (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack) h15 rfl (by omega) (by omega)
  obtain ⟨ext, l17, h17⟩ := peel_step_exact_i32 (b := c.pScratchBuf) c.extend_cap
    (4 * c.scratch_cap + c.slack) (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    h16 rfl (by omega) (by omega)
  obtain ⟨sbuf, l18, h18⟩ := peel_step_exact_i32 (b := c.pSlack) c.scratch_cap c.slack
    (4 * c.scratch_cap + c.slack) h17 rfl (by omega) (by omega)
  refine ⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩,
    ?_⟩
  simp only [emp_sep] at h18
  exact sep_mono2 (fun _ h => sep_ac h) (fun _ h => h) m h18

private theorem zip_u32a_7 {A1 A2 A3 A4 A5 A6 A7 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ (A6 ⋆ A7)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7) m := sep_ac h

private theorem zip_u32b_5 {A1 A2 A3 A4 A5 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2) ⋆ (A3 ⋆ A4 ⋆ A5)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) m := sep_ac h

private theorem zip_scr32a_6 {A1 A2 A3 A4 A5 A6 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3) ⋆ (A4 ⋆ A5 ⋆ A6)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6) m := sep_ac h

private theorem zip_scr_fold {SB SU S1 S2 S3 : Mem 64 → Prop} {m : Mem 64}
    (h : (SB ⋆ SU ⋆ (S1 ⋆ S2 ⋆ S3)) m) : (SB ⋆ SU ⋆ S1 ⋆ S2 ⋆ S3) m := sep_ac h

private theorem sep_assoc3_l {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C)) m) : ((A ⋆ B) ⋆ C) m := sep_ac h

private theorem full_avail_to_arrays (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ a : FullInitArrs c, (FullCoreArrays c (initFullState c 0#64 0#64 0#64 a).core ⋆
      FullScratchArrays c (initFullState c 0#64 0#64 0#64 a).scratch ⋆ c.pad) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hu4 := u32FullBytes_ge4 c.max_vars; have hu := u32FullBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  let ub := u32FullBytes c.max_vars
  let r15 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub)
  have h15le : 1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub ≤ c.avail := by
    dsimp only [ub]; omega
  have hrem0_eq : c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) =
      15 * ub + r15 := by
    dsimp only [r15, ub]; omega
  have h15_264 : 15 * ub + r15 ≤ 2 ^ 64 := by dsimp only [r15]; omega
  have h10_264 : 10 * ub + r15 ≤ 2 ^ 64 := by omega
  have h5_264 : 5 * ub + r15 ≤ 2 ^ 64 := by omega
  have hrem15 : 5 * u32FullBytes c.max_vars + (10 * ub + r15) = 15 * ub + r15 := by
    dsimp only [ub]; omega
  have hrem10 : 5 * u32FullBytes c.max_vars + (5 * ub + r15) = 10 * ub + r15 := by
    dsimp only [ub]; omega
  obtain ⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5, h_b⟩ := peel_bytes_block c hm
  rw [hrem0_eq] at h_b
  have h_u1m := sep_mono_r (fun _ hr =>
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
      c.pFlags c.pLevel c.pReason c.pTrail c.pTrailPos c.pTmp (rtot := 15 * ub + r15)
      (rnext := 10 * ub + r15) rfl rfl rfl rfl rfl hr hu4 hu4 hu4 hu4 hu4 hrem15 h15_264) h_b
  simp only [sep_ex_r, sep_pure_r] at h_u1m
  obtain ⟨fl, lvl, rsns, trl, tpos, lfl, llv, lrs, ltr, ltp, h_u1⟩ := h_u1m
  have h_u2m := sep_mono_r (fun _ hr =>
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
      c.pTmp c.pHeap c.pPos c.pMinClr c.pShrinkStk c.pQPrev (rtot := 10 * ub + r15)
      (rnext := 5 * ub + r15) rfl rfl rfl rfl rfl hr hu4 hu4 hu4 hu4 hu4 hrem10 h10_264)
    (sep_assoc3_l h_u1)
  simp only [sep_ex_r, sep_pure_r] at h_u2m
  obtain ⟨tmp, hp, pos, mclr, shrk, ltmp, lhp, lps, lmc, lsh, h_u2⟩ := h_u2m
  have h_u3m := sep_mono_r (fun _ hr =>
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars (c.max_vars + 1) (c.max_vars + 1)
      c.pQPrev c.pQNext c.pQStamp c.pFrameTrail c.pFrameDec c.pWvec (rtot := 5 * ub + r15)
      (rnext := r15) rfl rfl rfl rfl rfl hr hu4 hu4 hu4 hu hu rfl h5_264)
    (sep_assoc3_l h_u2)
  simp only [sep_ex_r, sep_pure_r] at h_u3m
  obtain ⟨qp, qn, qs, ftrl, fdec, lqp, lqn, lqs, lft, lfd, h_u3⟩ := h_u3m
  have h_tlm := sep_mono_r (fun _ hr => peel_tail_block c hr) (sep_assoc3_l h_u3)
  simp only [sep_ex_r, sep_pure_r] at h_tlm
  obtain ⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, ⟨lwv, lrp, lws, l1, l2, ltm, ltrc, lsc, lsg, lms, lgu, lll, lar, lwk, ldl, lrd,
      lex, lsb⟩, hm_comb⟩ := h_tlm
  let a : FullInitArrs c :=
    ⟨vals, lmrk, mrk, wvals, ph, ptgt, pbst, wbst, fl, lvl, rsns, trl, tpos, tmp, mclr, ftrl,
      fdec, wvec, repr, mstk, ar, wstk, hp, pos, shrk, qp, qn, qs, wsort, ws1, ws2, tmk, trc, sc,
      sig, gu, ll, del, red, ext, sbuf, ⟨hv1, hv3, hm1, hv2, hm2, hm3, hm4, hm5, lfl, llv, lrs,
      ltr, ltp, ltmp, lmc, lft, lfd, lwv, lrp, lms, lar, lwk, lhp, lps, lsh, lqp, lqn, lqs, lws,
      l1, l2, ltm, ltrc, lsc, lsg, lgu, lll, ldl, lrd, lex, lsb⟩⟩
  refine ⟨a, ?_⟩
  unfold FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B FullCoreDynArrs
    FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs FullScrDynArrs
    FullCfg.pad FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C
  exact sep_ac hm_comb

private theorem init_hdr_remerge {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    {mv' nc' cur' val' : BitVec 64} {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32) ⋆ R) m') :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m' := by
  have h2 := sep_mono2 (sep_mono2 (fun _ => dimacsState_to_region) (fun _ h => h))
    (fun _ h => h) m' (show ((dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' from sep_ac hm')
  rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail - 32) (n := avail)
    (by omega) hle] at h2
  exact sep_ac h2

private theorem init_state_fail {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes rest : List UInt8} {mv nc : Nat} {cur' val' : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m' : Mem 64} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    (hhdr : parseHeader cnfBytes = some (mv, nc, rest))
    (hfail : avail < fullFixedBytes mv + nc * 40 + 136)
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) cur' val' ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m')
    (hQfalse : ∀ m'', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m'' →
      (∀ mv' nc' rest', parseHeader cnfBytes = some (mv', nc', rest') →
        avail < fullFixedBytes mv' + nc' * 40 + 136) → Q (false, ()) m'') : Q (false, ()) m' :=
  hQfalse m' (init_hdr_remerge h32 hle hm') fun _ _ _ h => by
    rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; exact hfail

private theorem init_state_split_tail {hdr_addr : BitVec 64} {avail : Nat}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {j nc mv : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h1152 : 1152 ≤ avail) (hav64 : avail ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
      region (hdr_addr + 32#64) (avail - 32) ⋆ R) m) :
    ∃ ws : List (BitVec 64), ws.length = 140 ∧
      (hdrTail4 hdr_addr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
          ((ws.drop 105).take 35) ⋆
        (region (hdr_addr + 1152#64) (avail - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆
          dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := by
  have hm1 : (region (hdr_addr + 32#64) (avail - 32) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := sep_ac hm
  have hm2 : ((region (hdr_addr + 32#64) 1120 ⋆ region (hdr_addr + 1152#64) (avail - 1152)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m :=
    sep_mono (fun _ h_reg =>
      reg_peel (b := hdr_addr + 1152#64) (n1 := 1120) (n2 := avail - 1152) h_reg
        (hb := by rw [BitVec.add_assoc]; rfl) (hn := by omega) (hle := by omega)) hm1
  have hm3 := sep_mono (fun _ h_s =>
    sep_mono (fun _ h_h => region_to_array64 140 (by decide) h_h) h_s) hm2
  simp only [sep_ex_l, sep_pure_l] at hm3
  obtain ⟨ws, hwl, h_m⟩ := hm3
  have h4 : ((hdrTail4 hdr_addr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
        ((ws.drop 105).take 35) ⋆ region (hdr_addr + 1152#64) (avail - 1152)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m :=
    sep_mono (fun _ => array64_to_hdrTail4 hwl) h_m
  exact ⟨ws, hwl, sep_ac h4⟩

/-! ## 2. `full_init_state_m5_wp` & `full_init_state_wp` -/

section InitStateM5
open scoped InHdrTactics

private theorem c0_load_dimacs_mv {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 d = some mv :=
  load_dimacs_mv hm

private theorem c0_load_dimacs_nc {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 8) = some nc :=
  load_dimacs_nc hm

attribute [local c0_load] c0_load_dimacs_mv c0_load_dimacs_nc

theorem full_init_state_m5_wp (Γ : Env)
    (hHdr : ∀ a m Q X, Dimacs.Spec.kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Spec.fullCalcExtCapM5Spec a m Q X →
      Γ "full_calc_ext_cap_m5" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, Spec.fullCalcScrCapM5Spec a m Q X →
      Γ "full_calc_scr_cap_m5" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, fullZeroTables1Spec a m Q X → Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, fullZeroTables2Spec a m Q X → Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X → Func.wp Γ full_init_state_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m_in Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, h1152, hm_in, hQfalse, hQtrue⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m_in := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  have hm0a := sep_mono (fun _ => region32_to_dimacsState)
    (sep_ac hm0 : (region hdr_addr 32 ⋆ (bytes cnf_ptr cnfBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m_in)
  obtain ⟨mv0, hm0b⟩ := sep_ex_l.mp hm0a
  obtain ⟨nc0, hm0c⟩ := sep_ex_l.mp hm0b
  obtain ⟨cur0, hm0d⟩ := sep_ex_l.mp hm0c
  obtain ⟨val0, hm_pre⟩ := sep_ex_l.mp hm0d
  unfold Func.wp full_init_state_m5_body
  in_steps_nogrp
  apply wp_call_of_spec; apply hHdr
  change Dimacs.Spec.kissatParseHeaderSpec
    (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ()) m_in _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro _ _ _ _ m' hm'; refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    rw [wp_ret]; exact hQfalse m' (init_hdr_remerge (by omega) hav_le (sep_ac hm'))
      (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd; unfold dimacsBound at hmv hnc
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    in_steps
    apply wp_call_of_spec; apply hFixed
    change fullFixedBytesSpec (BitVec.ofNat 64 mv, ()) m0 _ _
    have hmv_to : (BitVec.ofNat 64 mv).toNat = mv := bv64_ofNat_toNat' (by omega)
    have hnc_to : (BitVec.ofNat 64 nc).toNat = nc := bv64_ofNat_toNat' (by omega)
    refine ⟨by rw [hmv_to]; unfold dimacsBound; omega, ?_⟩
    rw [hmv_to]; have hfx0_lt := fullFixedBytes_lt (max_v := mv) (by unfold dimacsBound; omega)
    have hf0_to : (BitVec.ofNat 64 (fullFixedBytes mv)).toNat = fullFixedBytes mv :=
      bv64_ofNat_toNat' (by omega)
    dsimp only
    in_steps
    have hult_f0 : avail.ult (BitVec.ofNat 64 (fullFixedBytes mv)) =
        decide (avail.toNat < fullFixedBytes mv) := by
      rw [BitVec.ult, hf0_to]
    rw [hult_f0]
    refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
    · fp_jnz_t hlt
      exact init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
    · fp_jnz_f hge; in_steps
      have hsub_f0 : avail - BitVec.ofNat 64 (fullFixedBytes mv) =
          BitVec.ofNat 64 (avail.toNat - fullFixedBytes mv) := by
        simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
      have hnc40 : BitVec.ofNat 64 nc * (40 : BitVec 64) + 136 =
          BitVec.ofNat 64 (nc * 40 + 136) := by
        rw [show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
          show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl, bv64_mul_nat3, hnc_to,
          bv_add_ofNat]
      rw [hsub_f0, hnc40, bv_ult_eq (by have := avail.isLt; omega) (by omega)]
      refine wp_jnz_of (fun hlt2 => ?_) (fun hge2 => ?_)
      · fp_jnz_t hlt2
        exact init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
      · fp_jnz_f hge2
        apply wp_call_of_spec; apply hMaxV
        change fullCalcMaxVSpec (avail, BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
          BitVec.ofNat 64 (fullFixedBytes mv), ()) m0 _ _
        refine ⟨by rw [hmv_to]; exact hmv_bd, by rw [hnc_to]; exact hnc_bd,
          by rw [hmv_to]; exact hf0_to, by rw [hf0_to, hnc_to]; omega, ?_⟩
        intro max_v hmv_le hmx_bd hmax_fit
        rw [hmv_to] at hmv_le
        rw [hnc_to] at hmax_fit
        have hmx_b := hmx_bd; unfold dimacsBound at hmx_b
        have hfx_m_lt := fullFixedBytes_lt hmx_bd
        in_steps
        apply wp_call_of_spec; apply hFixed
        change fullFixedBytesSpec (max_v, ()) m0 _ _
        refine ⟨hmx_bd, ?_⟩
        dsimp only
        in_steps_nogrp
        have hrem_eq : avail - BitVec.ofNat 64 (fullFixedBytes max_v.toNat) =
            BitVec.ofNat 64 (avail.toNat - fullFixedBytes max_v.toNat) := by
          simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
        let rem := avail.toNat - fullFixedBytes max_v.toNat
        have hrem_to : (BitVec.ofNat 64 rem).toNat = rem :=
          bv64_ofNat_toNat' (by have := avail.isLt; omega)
        have hrem136 : nc * 40 + 136 ≤ rem := by omega
        rw [hrem_eq]
        let del_cap := fullInitDelCap rem
        have hdel_bd : del_cap < dimacsBound := fullInitDelCap_lt
        have hdel_bd' := hdel_bd; unfold dimacsBound at hdel_bd'
        refine wp_join_group
          (fun (v : Tup Val [i64]) md => v.1 = BitVec.ofNat 64 del_cap ∧ md = m0) ?_ ?_
        · rintro _ ⟨d_v, ⟨⟩⟩ md ⟨rfl, rfl⟩
          simp only [Blocks.get_here]; in_steps
          apply wp_call_of_spec; apply hExt
          change Spec.fullCalcExtCapM5Spec (BitVec.ofNat 64 rem, ()) md _ _
          intro ecap_v hecap_le hecap_z hecap_4
          dsimp only; in_steps
          apply wp_call_of_spec; apply hScr
          change Spec.fullCalcScrCapM5Spec (BitVec.ofNat 64 rem, ()) md _ _
          intro scap_v hscap_le hscap_z hscap_4
          dsimp only; in_steps_nogrp
          have hecap_lt : ecap_v.toNat < dimacsBound := by unfold dimacsBound; omega
          have hscap_lt : scap_v.toNat < dimacsBound := by unfold dimacsBound; omega
          have hecap_bv : BitVec.ofNat 64 ecap_v.toNat = ecap_v := bv_ofNat_toNat_eq ecap_v
          have hscap_bv : BitVec.ofNat 64 scap_v.toNat = scap_v := bv_ofNat_toNat_eq scap_v
          have hdel_mul : BitVec.ofNat 64 del_cap * (12 : BitVec 64) =
              BitVec.ofNat 64 (12 * del_cap) := by
            rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, bv64_mul_nat3,
              bv64_ofNat_toNat' (by omega), Nat.mul_comm]
          have hshl2_e : ecap_v <<< (2 : Nat) = BitVec.ofNat 64 (4 * ecap_v.toNat) := by
            simpa [wp2_sext2_mod64] using bv64_shl2_val (x := ecap_v) (by omega)
          have hshl2_s : scap_v <<< (2 : Nat) = BitVec.ofNat 64 (4 * scap_v.toNat) := by
            simpa [wp2_sext2_mod64] using bv64_shl2_val (x := scap_v) (by omega)
          refine wp_join_group (fun (v : Tup Val [i64, i64, i64]) mg =>
            ∃ ec sc : Nat, ec < dimacsBound ∧ sc < dimacsBound ∧
              v.1 = BitVec.ofNat 64 ec ∧ v.2.1 = BitVec.ofNat 64 sc ∧
              v.2.2.1 = BitVec.ofNat 64 (12 * del_cap + 4 * ec + 4 * sc) ∧
              12 * del_cap + 4 * ec + 4 * sc + 40 ≤ rem ∧ mg = md) ?_ ?_
          · rintro _ ⟨ec_v, sc_v, dyn_v, ⟨⟩⟩ mg ⟨ec, sc, hec, hsc, rfl, rfl, rfl, hd40, rfl⟩
            simp only [Blocks.get_here]
            have hm0_ac : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
                (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
                region (hdr_addr + 32#64) (avail.toNat - 32) ⋆ R) mg := sep_ac hm0
            obtain ⟨ws, hwl, hm_spl⟩ :=
              init_state_split_tail h1152 hav_le hm0_ac
            have hw0l : (ws.take 35).length = 35 := by simp [hwl]
            have hw1l : ((ws.drop 35).take 35).length = 35 := by simp [hwl]
            have hw2l : ((ws.drop 70).take 35).length = 35 := by simp [hwl]
            have hw3l : ((ws.drop 105).take 35).length = 35 := by simp [hwl]
            clear hm_in hm_pre hm0 hm0a hm0b hm0c hm0d
            in_steps
            let ws1 := ws.take 35 ++
              ((ws.drop 35).take 35).set 17 (BitVec.ofNat 64 del_cap) ++
              (ws.drop 70).take 35 ++
              (((ws.drop 105).take 35).set 4 (BitVec.ofNat 64 ec)).set 7 (BitVec.ofNat 64 sc)
            have hm_arr : (array64 (hdr_addr + 32) ws1 ⋆ (region (hdr_addr + 1152#64)
                (avail.toNat - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆
                dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := by
              rwa [hdrTail4_eq_array64 hw0l (by simp [hw1l]) hw2l] at hm
            have hws1_len : ws1.length = 140 := by simp [ws1, hw0l, hw1l, hw2l, hw3l]
            have h52_ws1 : ws1[52]? = some (BitVec.ofNat 64 del_cap) := by
              dsimp only [ws1]
              rw [append4_getElem?_1 hw0l (by simp [hw1l]) (by decide) (by decide)]
              simp [hw1l]
            have h109_ws1 : ws1[109]? = some (BitVec.ofNat 64 ec) := by
              dsimp only [ws1]
              rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have h112_ws1 : ws1[112]? = some (BitVec.ofNat 64 sc) := by
              dsimp only [ws1]
              rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have hsub_dyn : BitVec.ofNat 64 rem -
                BitVec.ofNat 64 (12 * del_cap + 4 * ec + 4 * sc) =
                BitVec.ofNat 64 (rem - (12 * del_cap + 4 * ec + 4 * sc)) :=
              bv_sub_ofNat (by omega) (by have := avail.isLt; omega)
            rw [hsub_dyn]
            apply wp_call_of_spec; apply hArenas
            change fullInitArenasSpec (hdr_addr, hdr_addr, max_v,
              BitVec.ofNat 64 (rem - (12 * del_cap + 4 * ec + 4 * sc)), ()) m _ _
            let adyn := rem - (12 * del_cap + 4 * ec + 4 * sc)
            have hadyn_to : (BitVec.ofNat 64 adyn).toNat = adyn :=
              bv64_ofNat_toNat' (by have := avail.isLt; omega)
            have hec' := hec; have hsc' := hsc; unfold dimacsBound at hec' hsc'
            refine ⟨ws1, del_cap, ec, sc, _, rfl, hws1_len, hmx_bd, hdel_bd, hec, hsc,
              h52_ws1, h109_ws1, h112_ws1, by rw [hadyn_to]; omega, hm_arr,
              fun acap wcap rcap ws2 m2 hws2l hac hwc hrc hsum hwpos hws2 hm2 => ?_⟩
            rw [hadyn_to] at hsum hwpos
            have hwcap_pos : 1 ≤ wcap := hwpos (by omega)
            let c : FullCfg :=
              { hdr := hdr_addr, avail := avail.toNat, mv := mv, max_vars := max_v.toNat,
                bva_cap := max_v.toNat - mv, nc := nc, arena_cap := acap, wcap := wcap,
                delayed_cap := del_cap, red_cap := rcap, extend_cap := ec, scratch_cap := sc,
                hbva := by omega, hmv := hmv_bd, hmaxv := hmx_bd, hnc := hnc_bd, harena := hac,
                hwcap := hwc, hdel := hdel_bd, hred := hrc, hext := hec, hscr := hsc,
                havail_fit := havel_fit, hsize := by omega }
            apply wp_call_of_spec; apply hInitHdr
            change fullInitHdrSpec (hdr_addr, BitVec.ofNat 64 mv, max_v, fuel, ()) m2 _ _
            have hws2_c := hws2 c rfl rfl rfl rfl rfl rfl rfl rfl
            refine ⟨c, ws2, _, rfl, rfl, (bv_ofNat_toNat_eq max_v).symm, hws2l,
              fun s0 i hi => ?_, hm2, fun s_hdr m3 hcv hal hwl hte hpr hcl htl hfu hunf hpb
                hmcl hmcf hoom hdm hinc hel hm3 => ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              unfold hdrTailWords HdrWordField.tailChunk0 HdrWordField.tailChunk1
                HdrWordField.tailChunk2 HdrWordField.tailChunk3
              repeat rcases hws2_c with ⟨h_, hws2_c⟩
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl <;> assumption
            · have hm3a : (region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 mv)
                    (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
                    array64 (c.hdr + 32) (hdrTailWords c s_hdr) ⋆ R)) m3 := sep_ac hm3
              have hm3b := sep_mono (fun _ h_reg => full_avail_to_arrays c h_reg) hm3a
              obtain ⟨arrs, hcomb⟩ := sep_ex_l.mp hm3b
              let s_pre : FullState :=
                { core := { s_hdr.core with
                    d_cur := cnf_ptr + BitVec.ofNat 64 j,
                    d_val := BitVec.ofNat 64 nc,
                    vals := arrs.vals, lit_mark := arrs.lit_mark, mrk := arrs.mrk,
                    flags := arrs.flags, lvl := arrs.lvl, rsns := arrs.rsns, trl := arrs.trl,
                    trail_pos := arrs.trail_pos, tmp := arrs.tmp, min_clr := arrs.min_clr,
                    frame_trail := arrs.frame_trail, frame_dec := arrs.frame_dec,
                    wvec := arrs.wvec, repr := arrs.repr, min_stk := arrs.min_stk,
                    arena := arrs.arena, wstk := arrs.wstk },
                  scratch := { s_hdr.scratch with
                    walk_vals := arrs.walk_vals, phases := arrs.phases,
                    phases_target := arrs.phases_target, phases_best := arrs.phases_best,
                    walk_best := arrs.walk_best, heap := arrs.heap, pos := arrs.pos,
                    shrink_stk := arrs.shrink_stk, q_prev := arrs.q_prev, q_next := arrs.q_next,
                    q_stamp := arrs.q_stamp, wsort := arrs.wsort, work_stk1 := arrs.work_stk1,
                    work_stk2 := arrs.work_stk2, tarjan_mark := arrs.tarjan_mark,
                    tarjan_reach := arrs.tarjan_reach, score := arrs.score, sim_sig := arrs.sim_sig,
                    glue_used := arrs.glue_used, last_learned := arrs.last_learned,
                    delayed := arrs.delayed, red_refs := arrs.red_refs,
                    extend_stk := arrs.extend_stk, scratch_buf := arrs.scratch_buf } }
              have h_pre_ca : FullCoreArrays c s_pre.core =
                  FullCoreArrays c (initFullState c 0#64 0#64 0#64 arrs).core := rfl
              have h_pre_sa : FullScratchArrays c s_pre.scratch =
                  FullScratchArrays c (initFullState c 0#64 0#64 0#64 arrs).scratch := rfl
              have h_pre_ht : hdrTailWords c s_pre = hdrTailWords c s_hdr := by
                simp only [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
                  HdrWordField.tailChunk2, HdrWordField.tailChunk3, s_pre]
              have hm_pre_full : (FullMem c s_pre ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := by
                rw [← h_pre_ca, ← h_pre_sa] at hcomb
                unfold FullMem; rw [h_pre_ht]
                exact sep_ac hcomb
              obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17,
                o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
                o35, o36, o37, o38, o39, o40, o41⟩ := arrs.ok
              have hlen_pre : s_pre.LengthsOk c :=
                ⟨⟨o1, o2, o3, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22,
                  by simp [s_pre, hcv], by simp [s_pre, hcv]; omega, by simp [s_pre, hal],
                  by simp [s_pre, hwl]; exact hwcap_pos, by simp [s_pre, hte],
                  by simp [s_pre, hpr, hte], by simp [s_pre, htl], by simp [s_pre, hmcl]⟩,
                 ⟨o4, o5, o6, o7, o8, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
                  o35, o36, o37, o38, o39, o40, o41⟩⟩
              apply wp_call_of_spec; apply hZt1
              change fullZeroTables1Spec (c.hdr, ()) m3 _ _
              refine ⟨c, s_pre, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_pre, hm_pre_full,
                fun wstk' mstk' repr' sc1 m4 hwstk' hmstk' hrepr' hsc1 hext1 hll1 hm4 => ?_⟩
              let s_1 : FullState :=
                { s_pre with
                  core := {
                    s_pre.core with
                    vals := List.replicate (2 * c.max_vars) 0#8,
                    lit_mark := List.replicate (2 * c.max_vars) 0#8,
                    wvec := List.replicate (4 * c.max_vars) 0#32, wstk := wstk',
                    min_stk := mstk', repr := repr' },
                  scratch := sc1 }
              have hlen1 : s_1.LengthsOk c :=
                ⟨{
                  hlen_pre.core_ok with
                  vals_len := by simp [s_1],
                  lit_mark_len := by simp [s_1], wvec_len := by simp [s_1],
                  repr_len := hrepr', min_stk_len := hmstk', wstk_len_arr := hwstk' }, hsc1⟩
              apply wp_call_of_spec; apply hZt2
              change fullZeroTables2Spec (c.hdr, ()) m4 _ _
              refine ⟨c, s_1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hm4,
                fun flags' fdec' sc2 m5 hfl' hfd' hsc2 hpres2 hm5 => ?_⟩
              dsimp only
              rw [wp_ret]
              let s_2 : FullState :=
                { s_1 with
                  core := {
                    s_1.core with
                    mrk := List.replicate c.max_vars 0#8, flags := flags',
                    lvl := List.replicate c.max_vars 0#32,
                    rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
                    frame_trail := List.replicate (c.max_vars + 1) 0#32,
                    frame_dec := fdec' },
                  scratch := sc2 }
              have hlen2 : s_2.LengthsOk c :=
                ⟨{
                  hlen1.core_ok with
                  mrk_len := by simp [s_2], flags_len := hfl',
                  lvl_len := by simp [s_2], rsns_len := by simp [s_2],
                  frame_trail_len := by simp [s_2], frame_dec_len := hfd' }, hsc2⟩
              have hll2 : ∀ i < 8, s_2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 =
                  0xFFFFFFFF#32 := by
                intro i hi8
                dsimp only [s_2]
                rw [hpres2.1]
                exact last_learned_getD_ff_of_zero hll1 i hi8
              have hext2 : s_2.scratch.extend_len = 0 := by
                dsimp only [s_2]; rw [hpres2.2, hext1]; exact hel
              have hft0 : (s_2.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
                simp [s_2]
              have hinv2 := fullInv_init_sparse (F0 := shiftDownCnf CNF.empty) hlen2
                hinc hal rfl hte hcl hft0 rfl rfl rfl hll2 hext2 hdm
              rw [sep_comm_l, ← sep_assoc] at hm5
              exact hQtrue c s_2 j rest m5 rfl rfl hhdr hj hdrop hinv2 hcv rfl hal hwl hte hpr hcl
                hfu hunf hpb hmcl hmcf hoom hinc rfl rfl rfl rfl hext2 hm5
          · intro Jg hJg; in_steps
            rw [hdel_mul, hshl2_e, hshl2_s, show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
              show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl,
              bv64_mul_nat3, hnc_to,
              show BitVec.ofNat 64 (12 * del_cap) + BitVec.ofNat 64 (4 * ecap_v.toNat) +
                BitVec.ofNat 64 (4 * scap_v.toNat) =
                BitVec.ofNat 64 (12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat) by
                repeat rw [bv_add_ofNat],
              bv_add_ofNat, bv_add_ofNat, bv_ult_eq (by have := avail.isLt; omega)
                (by unfold dimacsBound at *; omega)]
            refine wp_jnz_of (fun hdlt => ?_) (fun hdge => ?_)
            · fp_jnz_t hdlt
              refine hJg (0#64, 0#64, BitVec.ofNat 64 (12 * del_cap), ()) md
                ⟨0, 0, by unfold dimacsBound; omega, by unfold dimacsBound; omega,
                  rfl, rfl, rfl, ?_, rfl⟩
              by_cases hrem_b : 524288 ≤ rem <;>
                simp [fullInitDelCap, del_cap, hrem_b] <;> omega
            · fp_jnz_f hdge
              refine hJg (ecap_v, scap_v, _, ()) md ⟨ecap_v.toNat, scap_v.toNat, hecap_lt,
                hscap_lt, hecap_bv.symm, hscap_bv.symm, rfl, by omega, rfl⟩
        · intro Jd hJd; in_steps
          rw [show (524288 : BitVec 64) = BitVec.ofNat 64 524288 from rfl,
            bv_ule_eq (by decide) (by have := avail.isLt; omega)]
          refine wp_jnz_of (fun hbig => ?_) (fun hsmall => ?_)
          · fp_jnz_t hbig; refine hJd (4096#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hbig]
          · fp_jnz_f hsmall; refine hJd (8#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hsmall]

end InitStateM5

theorem full_init_state_wp (Γ : Env)
    (hInitM5 : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X → Func.wp Γ full_init_state_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, hc, hf1, hf2, h1152, hm, hQfalse, hQtrue⟩
  unfold Func.wp full_init_state_body
  in_steps_nogrp
  apply wp_call_of_spec
  exact hInitM5 _ m _ X ⟨cnfBytes, R, hc, hf1, hf2, h1152, hm,
    (fun m' hm' hfa => by dsimp only; rw [wp_ret]; exact hQfalse m' hm' hfa),
    (fun c s j rest m' hc' ha' hp' hj' hd' hs' hcv hdcur hal hwl hte hpr hcl hfu hunf hpb
      hmcl hmcf hoom hinc hvs hws hms hlm hel hm' => by
      dsimp only; rw [wp_ret]
      exact hQtrue c s j rest m' hc' ha' hp' hj' hd' hs' hcv hdcur hal hwl hte hpr hcl hfu hunf hpb
        hmcl hmcf hoom hinc hvs hws hms hlm hel hm')⟩

/-! ## 3. `full_m6_mem_init_wp` -/

private theorem sep_init_split {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C) ⋆ R) m) : (A ⋆ C ⋆ (B ⋆ R)) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => by rwa [sep_assoc] at x) m h
  exact sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h1

private theorem sep_init_merge {A B C R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ C ⋆ (B ⋆ R)) m) : (A ⋆ (B ⋆ C) ⋆ R) m := by
  rw [sep_assoc] at h ⊢
  have h1 : (A ⋆ (B ⋆ (C ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h
  rw [← sep_assoc B C R] at h1
  exact h1

private theorem sep_init_pull_ext {A F E R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ F ⋆ (E ⋆ R)) m) : (E ⋆ (A ⋆ F ⋆ R)) m := by
  rw [sep_assoc] at h
  have h1 : (A ⋆ (E ⋆ (F ⋆ R))) m :=
    sep_mono2 (fun _ x => x) (fun _ x => sep_swap_l x) m h
  have h2 := sep_swap_l h1
  rwa [← sep_assoc A F R] at h2

private theorem sep_init_pack {E A F R : Mem 64 → Prop} {m : Mem 64}
    (h : (E ⋆ (A ⋆ F ⋆ R)) m) : ((E ⋆ F) ⋆ (A ⋆ R)) m := by
  have h1 : (E ⋆ (A ⋆ (F ⋆ R))) m := by rwa [sep_assoc A F R] at h
  have h2 := sep_swap_l h1
  have h3 : (A ⋆ ((E ⋆ F) ⋆ R)) m :=
    sep_mono2 (fun _ x => x) (fun _ x => (congrFun (sep_assoc E F R) _).mpr x) m h2
  exact sep_swap_l h3

private theorem sep_init_unpack {H A R : Mem 64 → Prop} {m : Mem 64}
    (h : (H ⋆ (A ⋆ R)) m) : (A ⋆ H ⋆ R) m := by
  have h1 := sep_swap_l h
  rwa [← sep_assoc A H R] at h1

private theorem bv64_max_sub_ult_false {wb av : BitVec 64}
    (hfit : wb.toNat + av.toNat < 2 ^ 64) :
    (((18446744073709551615 : BitVec 64) - av).ult wb) = false := by
  have hav := av.isLt
  have hmax : (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : ((18446744073709551615 : BitVec 64) - av).toNat = 2 ^ 64 - 1 - av.toNat := by
    rw [BitVec.toNat_sub, hmax]
    have h1 : 2 ^ 64 - av.toNat + (2 ^ 64 - 1) = (2 ^ 64 - 1 - av.toNat) + 2 ^ 64 := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ult, hsub, decide_eq_false_iff_not]; omega

private theorem mem_init_sub_eq {av : BitVec 64} (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (av - 2304).toNat = av.toNat - fullM6ExtBytes := by
  rw [BitVec.toNat_sub, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *; omega

private theorem mem_init_hdr_toNat {wb av : BitVec 64} (hfit : wb.toNat + av.toNat < 2 ^ 64)
    (hge : fullM6HdrTotalBytes ≤ av.toNat) :
    (wb + 2304).toNat = wb.toNat + fullM6ExtBytes := by
  rw [BitVec.toNat_add, show (2304 : BitVec 64).toNat = 2304 from rfl]
  unfold fullM6ExtBytes fullM6HdrTotalBytes at *
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem mem_init_ext_fit : 8 * fullM6ExtWords ≤ 2 ^ 64 := by
  unfold fullM6ExtWords; decide

theorem full_m6_mem_init_wp (Γ : Env)
    (hInitState : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hHdrInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, Spec.fullM6MemInitExactSpec a m Q X → Func.wp Γ full_m6_mem_init_body a m Q X := by
  rintro ⟨cnf_ptr, cend, work_base, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, hcend, hfit, hwfit, hm, hFail, hOk⟩
  unfold Func.wp full_m6_mem_init_body
  in_steps_nogrp
  have hult_av : avail.ult 3456 = decide (avail.toNat < fullM6HdrTotalBytes) := by
    rw [BitVec.ult, show (3456 : BitVec 64).toNat = fullM6HdrTotalBytes from rfl]
  rw [hult_av]
  refine wp_jnz_of (fun hlt => ?_) (fun hnot_lt => ?_)
  · fp_jnz_t hlt
    exact hFail m hm (Or.inl hlt)
  · fp_jnz_f hnot_lt
    have hge3456 : fullM6HdrTotalBytes ≤ avail.toNat := Nat.le_of_not_lt hnot_lt
    rw [bv64_max_sub_ult_false hwfit]
    refine wp_jnz_of (fun h => by cases h) (fun _ => ?_)
    in_steps_nogrp
    have hav_le : avail.toNat ≤ 2 ^ 64 := Nat.le_of_lt avail.isLt
    have hsub_eq : (avail - 2304).toNat = avail.toNat - fullM6ExtBytes :=
      mem_init_sub_eq hge3456
    have hhdr_to : (work_base + 2304).toNat = work_base.toNat + fullM6ExtBytes :=
      mem_init_hdr_toNat hwfit hge3456
    have hhdr_bv : work_base + (2304 : BitVec 64) =
        work_base + BitVec.ofNat 64 fullM6ExtBytes := by
      unfold fullM6ExtBytes; rfl
    have hsum_av : fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) = avail.toNat :=
      Nat.add_sub_of_le (Nat.le_trans (by decide : fullM6ExtBytes ≤ fullM6HdrTotalBytes) hge3456)
    have hrem_fit :
        work_base.toNat + fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) < 2 ^ 64 := by
      rw [Nat.add_assoc, hsum_av]; exact hwfit
    have hrem_ge : 1152 ≤ avail.toNat - fullM6ExtBytes :=
      Nat.le_sub_of_add_le (by exact hge3456)
    have hsplit : (bytes cnf_ptr cnfBytes ⋆
        region (work_base + 2304) (avail - 2304).toNat ⋆
        (region work_base fullM6ExtBytes ⋆ R)) m := by
      have hm1 : (bytes cnf_ptr cnfBytes ⋆
          (region work_base fullM6ExtBytes ⋆
            region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
              (avail.toNat - fullM6ExtBytes)) ⋆ R) m := by
        rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
          (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le]
        exact hm
      rw [hsub_eq, hhdr_bv]; exact sep_init_split hm1
    c0_call hInitState
    refine ⟨cnfBytes, region work_base fullM6ExtBytes ⋆ R, hcend, hfit,
      by rw [hhdr_to, hsub_eq]; exact hrem_fit,
      by rw [hsub_eq]; exact hrem_ge, hsplit, ?_, ?_⟩
    · intro m1 hm1 hfail1
      refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
      rw [wp_ret]
      have hre : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m1 := by
        have hm2 : (bytes cnf_ptr cnfBytes ⋆
            (region work_base fullM6ExtBytes ⋆
              region (work_base + BitVec.ofNat 64 fullM6ExtBytes)
                (avail.toNat - fullM6ExtBytes)) ⋆ R) m1 := by
          rw [hsub_eq, hhdr_bv] at hm1; exact sep_init_merge hm1
        rw [region_merge_eq (a := work_base) (n1 := fullM6ExtBytes)
          (n2 := avail.toNat - fullM6ExtBytes) (n := avail.toNat) hsum_av hav_le] at hm2
        exact hm2
      exact hFail m1 hre (Or.inr fun mv nc rest hp => by
        have := hfail1 mv nc rest hp; rwa [hsub_eq] at this)
    · intro c s j rest m1 hchdr hcavail hparse hj hdrop hsp hcv hdcur hal hwl hte hpr hcl
        hfu _ hprob _ _ hoom hinc hvals hwvec _ _ _ hm1
      have hcfg : FullM6HdrCfgOk c := by
        unfold FullM6HdrCfgOk; rw [hchdr, hhdr_to]; exact Nat.le_add_left ..
      have hwa : m6ExtAddr c.hdr = work_base := by
        rw [hchdr]; exact m6ExtAddr_of_add_imm work_base
      have hm1' : (region work_base (8 * fullM6ExtWords) ⋆
          (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R)) m1 := by
        have h0 := sep_init_pull_ext hm1
        simpa only [show fullM6ExtBytes = 8 * fullM6ExtWords from rfl] using h0
      have hm2 := sep_mono (fun _ (hr : region work_base (8 * fullM6ExtWords) _) =>
        region_to_array64 fullM6ExtWords mem_init_ext_fit hr) hm1'
      obtain ⟨ext0, hm3⟩ := sep_ex_l.mp hm2
      obtain ⟨hext0_len, hm4⟩ := sep_pure_l.mp hm3
      have hm_ext : (FullM6HdrMem c ext0 s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m1 := by
        have h1 : (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆
            (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R)) m1 := by
          rw [hwa]; exact hm4
        unfold FullM6HdrMem; exact sep_init_pack h1
      in_steps_nogrp
      refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
      c0_call hHdrInit
      refine ⟨c, ext0, s, bytes cnf_ptr cnfBytes ⋆ R, hchdr.symm, hcfg, hext0_len,
        hsp.lengths, hm_ext, fun ext1 m2 hinit1 hm2 => ?_⟩
      in_steps
      rw [← hchdr]
      exact hOk c ext1 s j rest m2 (hchdr.trans hhdr_bv) (by rwa [hsub_eq] at hcavail) hcfg
        hinit1 hparse hj hdrop ⟨hcfg, hinit1.toOk, hsp⟩ hcv hdcur hal hwl hte hpr hcl hfu
        hoom hinc hprob hvals hwvec (sep_init_unpack hm2)

end LeanQbe.T.Examples.Kissat.Proof.Internal
