/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 2 S11-3 Activation & Init Proofs (`FullFidelityTumbleProofAct`)

Proves:
1. `full_zero_tables2_fid_wp` against exact canonical `Full.fullZeroTables2Spec`.
2. `full_init_hdr_fid_wp` against exact canonical `Full.fullInitHdrSpec`.
3. `full_activate_lit_fid_wp` against `fullActivateLitFidSpec` (using `Full.fullHeapPushSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open Kraken.Bedrock2.Test

/-! ## 1. `full_zero_tables2_fid` (`Full.fullZeroTables2Spec`) -/

section ZeroTables2FidProof

open scoped FullArenaTactics FullParseInitTactics

@[irreducible] private def Zt2FidCorePres (s st : FullState) : Prop :=
  st.core =
    { s.core with
      mrk := st.core.mrk, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns
      frame_trail := st.core.frame_trail, frame_dec := st.core.frame_dec }

private def Zt2FidLoopInv (c : FullCfg) (s st : FullState) (n : Nat) : Prop :=
  n ≤ c.max_vars ∧ Zt2FidCorePres s st ∧ st.LengthsOk c ∧
  Full.FullExtScratchPres s st ∧
  ∀ j < n,
    st.core.mrk[j]? = some 0#8 ∧ st.core.lvl[j]? = some 0#32 ∧
    st.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.core.frame_trail[j]? = some 0#32

private theorem bv64_add1_toNat {v : BitVec 64} {n : Nat} (hv : v.toNat < n) (hn : n < 2 ^ 64) :
    (v + 1#64).toNat = v.toNat + 1 := by
  simp only [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

private theorem zt2_fid_step_ok {c : FullCfg} {s st st' : FullState} {v : Nat}
    (hv : v < c.max_vars) (hinv : Zt2FidLoopInv c s st v)
    (hcore : st'.core =
      { st.core with
        mrk := st.core.mrk.set v 0#8, flags := st.core.flags.set v 0#32,
        lvl := st.core.lvl.set v 0#32, rsns := st.core.rsns.set v 0xFFFFFFFF#32,
        frame_trail := st.core.frame_trail.set v 0#32,
        frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 })
    (hsc_ok : st'.scratch.LengthsOk c)
    (hll : st'.scratch.last_learned = st.scratch.last_learned)
    (hel : st'.scratch.extend_len = st.scratch.extend_len) :
    Zt2FidLoopInv c s st' (v + 1) := by
  obtain ⟨_, hag, hlok, hpres, hall⟩ := hinv
  unfold Zt2FidCorePres at hag
  have hc := hlok.core_ok
  refine ⟨by omega, ?_,
    ⟨{ hc with
        cur_vars_ge := by rw [hcore]; exact hc.cur_vars_ge
        cur_vars_le := by rw [hcore]; exact hc.cur_vars_le
        trail_end_le := by rw [hcore]; exact hc.trail_end_le
        propagated_le := by rw [hcore]; exact hc.propagated_le
        arena_len_le := by rw [hcore]; exact hc.arena_len_le
        wlen_le := by rw [hcore]; exact hc.wlen_le
        tmp_len_le := by rw [hcore]; exact hc.tmp_len_le
        min_clr_len_le := by rw [hcore]; exact hc.min_clr_len_le
        vals_len := by rw [hcore]; exact hc.vals_len
        lit_mark_len := by rw [hcore]; exact hc.lit_mark_len
        mrk_len := by rw [hcore]; simp [hc.mrk_len]
        flags_len := by rw [hcore]; simp [hc.flags_len]
        lvl_len := by rw [hcore]; simp [hc.lvl_len]
        rsns_len := by rw [hcore]; simp [hc.rsns_len]
        trl_len := by rw [hcore]; exact hc.trl_len
        trail_pos_len := by rw [hcore]; exact hc.trail_pos_len
        tmp_len_arr := by rw [hcore]; exact hc.tmp_len_arr
        min_clr_len_arr := by rw [hcore]; exact hc.min_clr_len_arr
        frame_trail_len := by rw [hcore]; simp [hc.frame_trail_len]
        frame_dec_len := by rw [hcore]; simp [hc.frame_dec_len]
        wvec_len := by rw [hcore]; exact hc.wvec_len
        repr_len := by rw [hcore]; exact hc.repr_len
        min_stk_len := by rw [hcore]; exact hc.min_stk_len
        arena_len_arr := by rw [hcore]; exact hc.arena_len_arr
        wstk_len_arr := by rw [hcore]; exact hc.wstk_len_arr }, hsc_ok⟩,
    ⟨hll.trans hpres.1, hel.trans hpres.2⟩, fun j hj => ?_⟩
  · unfold Zt2FidCorePres
    rw [hcore]
    exact congrArg (fun x =>
      { x with
        mrk := st.core.mrk.set v 0#8, flags := st.core.flags.set v 0#32,
        lvl := st.core.lvl.set v 0#32, rsns := st.core.rsns.set v 0xFFFFFFFF#32,
        frame_trail := st.core.frame_trail.set v 0#32,
        frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 }) hag
  rw [hcore]
  by_cases hje : j = v
  · subst hje
    exact ⟨List.getElem?_set_self (by rw [hc.mrk_len]; exact hv),
      List.getElem?_set_self (by rw [hc.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hc.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hc.frame_trail_len]; omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall j (by omega)
    simp only [List.getElem?_set_ne (Ne.symm hje)]
    exact ⟨h1, h2, h3, h4⟩

private theorem list_eq_replicate_of_forall {α : Type} {xs : List α} {n : Nat} {v : α}
    (hlen : xs.length = n) (h : ∀ j < n, xs[j]? = some v) : xs = List.replicate n v := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    have hget := h i (by simpa [hlen] using hi1)
    rw [List.getElem?_eq_getElem hi1, Option.some.injEq] at hget
    simpa [List.getElem_replicate] using hget

private theorem zt2_fid_tail6_wp (Γ : Env) {c : FullCfg} {st1 : FullState}
    {v_v addr_fl : Val i64} {m : Mem 64} {Q : Post []} {X : XPost} {R : Mem 64 → Prop}
    {k : Expr Val Cont []}
    (haddr : addr_fl = c.pFlags + v_v * (4 : BitVec 64))
    (hfl1 : st1.core.flags.length = c.max_vars) (hhp1 : st1.scratch.heap.length = c.max_vars)
    (hps1 : st1.scratch.pos.length = c.max_vars) (hqp1 : st1.scratch.q_prev.length = c.max_vars)
    (hqn1 : st1.scratch.q_next.length = c.max_vars)
    (hqs1 : st1.scratch.q_stamp.length = c.max_vars)
    (hvv : v_v.toNat < c.max_vars) (hm1 : (FullMem c st1 ⋆ R) m)
    (hk : ∀ m',
      (FullMem c
        ({ core := { st1.core with flags := st1.core.flags.set v_v.toNat 0#32 },
           scratch := { st1.scratch with
             heap := st1.scratch.heap.set v_v.toNat 0#32,
             pos := st1.scratch.pos.set v_v.toNat 0xFFFFFFFF#32,
             q_prev := st1.scratch.q_prev.set v_v.toNat 0xFFFFFFFF#32,
             q_next := st1.scratch.q_next.set v_v.toNat 0xFFFFFFFF#32,
             q_stamp := st1.scratch.q_stamp.set v_v.toNat 0#32 } } :
          FullState) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X
      (Expr.store (Arg.imm (t := i32) 0) (Arg.var addr_fl)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
         Expr.let_ (Op.mk (.add i64) (Arg.var c.pHeap, Arg.var p.1, ())) fun p =>
         Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
           (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pPos, Arg.var p.1, ())) fun p =>
            Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.pQPrev, Arg.var p.1, ())) fun p =>
               Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                 (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pQNext, Arg.var p.1, ())) fun p =>
                  Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                    (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                     Expr.let_ (Op.mk (.add i64) (Arg.var c.pQStamp, Arg.var p.1, ())) fun p =>
                     Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1) k)))))) m := by
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  subst haddr
  fp_head_steps
  exact hk m hm

/-- S11-3 inactive `full_zero_tables2_fid` satisfies exact canonical `Full.fullZeroTables2Spec`. -/
theorem full_zero_tables2_fid_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables2Spec a m Q X →
      Func.wp Γ full_zero_tables2_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  unfold Func.wp full_zero_tables2_fid_body
  fp_head_steps
  refine wp_loop_inv
    (fun (v_v : Tup Val [i64]) ml => ∃ st : FullState, (FullMem c st ⋆ R) ml ∧
      Zt2FidLoopInv c s st v_v.1.toNat)
    (fun v_v _ => c.max_vars - v_v.1.toNat) ?_ ?_
  · intro L hL; fp_head_steps
    refine hL (0#64, ()) m ⟨s, hm, ⟨Nat.zero_le _, by unfold Zt2FidCorePres; rfl,
      hlen, ⟨rfl, rfl⟩, fun _ h0 => by cases h0⟩⟩
  · intro L ⟨v_v, ⟨⟩⟩ ml ⟨st, hm, hinv⟩ hL
    have hv_le := hinv.1; have hlok := hinv.2.2.1
    dsimp only at hv_le
    have hc := hlok.core_ok; have hs := hlok.scratch_ok
    have hmrk_l : st.core.mrk.length = c.max_vars := hc.mrk_len
    have hfl_l : st.core.flags.length = c.max_vars := hc.flags_len
    have hlvl_l : st.core.lvl.length = c.max_vars := hc.lvl_len
    have hrsns_l : st.core.rsns.length = c.max_vars := hc.rsns_len
    have hft_l : st.core.frame_trail.length = c.max_vars + 1 := hc.frame_trail_len
    have hfd_l : st.core.frame_dec.length = c.max_vars + 1 := hc.frame_dec_len
    have hph_l : st.scratch.phases.length = c.max_vars := hs.phases_len
    have hpt_l : st.scratch.phases_target.length = c.max_vars := hs.phases_target_len
    have hpb_l : st.scratch.phases_best.length = c.max_vars := hs.phases_best_len
    have hwb_l : st.scratch.walk_best.length = c.max_vars := hs.walk_best_len
    have hsc_l : st.scratch.score.length = c.max_vars := hs.score_len
    have hsg_l : st.scratch.sim_sig.length = c.max_vars := hs.sim_sig_len
    have hhp_l : st.scratch.heap.length = c.max_vars := hs.heap_len_arr
    have hps_l : st.scratch.pos.length = c.max_vars := hs.pos_len
    have hqp_l : st.scratch.q_prev.length = c.max_vars := hs.q_prev_len
    have hqn_l : st.scratch.q_next.length = c.max_vars := hs.q_next_len
    have hqs_l : st.scratch.q_stamp.length = c.max_vars := hs.q_stamp_len
    fp_head_steps
    refine wp_jnz_of (fun hvlt => ?_) (fun hvge => ?_)
    · have hvlt' : v_v.toNat < c.max_vars := by
        dsimp only [Arg.val_var, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hvlt
        rw [BitVec.ult, decide_eq_true_eq, hmx_to] at hvlt
        exact hvlt
      have hv1 : (v_v + 1#64).toNat = v_v.toNat + 1 :=
        bv64_add1_toNat hvlt' (Nat.lt_trans hmx (by decide))
      clear hc hlok hfl_l hhp_l hps_l hqp_l hqn_l hqs_l hs
      fp_head_steps
      have hc0 := hinv.2.2.1.core_ok
      have hs0 := hinv.2.2.1.scratch_ok
      obtain ⟨st1, hm1, hcore1, hll1, hel1, hfl1, hhp1, hps1, hqp1, hqn1, hqs1, hsc_ok1⟩ :
          ∃ st1 : FullState,
            (FullMem c st1 ⋆ R) m ∧
            st1.core =
              { st.core with
                mrk := st.core.mrk.set v_v.toNat 0#8,
                lvl := st.core.lvl.set v_v.toNat 0#32,
                rsns := st.core.rsns.set v_v.toNat 0xFFFFFFFF#32,
                frame_trail := st.core.frame_trail.set v_v.toNat 0#32,
                frame_dec := st.core.frame_dec.set v_v.toNat 0xFFFFFFFF#32 } ∧
            st1.scratch.last_learned = st.scratch.last_learned ∧
            st1.scratch.extend_len = st.scratch.extend_len ∧
            st1.core.flags.length = c.max_vars ∧
            st1.scratch.heap.length = c.max_vars ∧
            st1.scratch.pos.length = c.max_vars ∧
            st1.scratch.q_prev.length = c.max_vars ∧
            st1.scratch.q_next.length = c.max_vars ∧
            st1.scratch.q_stamp.length = c.max_vars ∧
            st1.scratch.LengthsOk c :=
        ⟨_, hm, rfl, rfl, rfl, hc0.flags_len, hs0.heap_len_arr, hs0.pos_len, hs0.q_prev_len,
          hs0.q_next_len, hs0.q_stamp_len,
          { hs0 with
            phases_len := by simp [hph_l], phases_target_len := by simp [hpt_l],
            phases_best_len := by simp [hpb_l], walk_best_len := by simp [hwb_l],
            score_len := by simp [hsc_l], sim_sig_len := by simp [hsg_l] }⟩
      clear hm hc0 hs0
      refine zt2_fid_tail6_wp Γ rfl hfl1 hhp1 hps1 hqp1 hqn1 hqs1 hvlt' hm1 fun m2 hm2 => ?_
      fp_head_steps
      exact hL (v_v + 1#64, ()) m2
        (by dsimp only; rw [hv1]; exact Nat.sub_lt_sub_left hvlt' (Nat.lt_succ_self _))
        ⟨_, hm2, by
          dsimp only; rw [hv1]
          refine zt2_fid_step_ok hvlt' hinv (by rw [hcore1]) ?_ hll1 hel1
          exact { hsc_ok1 with
            heap_len_arr := by simp [hhp1], pos_len := by simp [hps1],
            q_prev_len := by simp [hqp1], q_next_len := by simp [hqn1],
            q_stamp_len := by simp [hqs1] }⟩
    · have hvge' : ¬ v_v.toNat < c.max_vars := by
        dsimp only [Arg.val_var, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hvge
        rw [BitVec.ult, decide_eq_false_iff_not, hmx_to] at hvge
        exact hvge
      have hveq : v_v.toNat = c.max_vars := Nat.le_antisymm hv_le (Nat.not_lt.mp hvge')
      obtain ⟨_, hag, _, hpres, hall⟩ := hinv
      rw [hveq] at hall
      fp_head_steps
      have hmrk : st.core.mrk = List.replicate c.max_vars 0#8 :=
        list_eq_replicate_of_forall hmrk_l fun j hj => (hall j hj).1
      have hlvl : st.core.lvl = List.replicate c.max_vars 0#32 :=
        list_eq_replicate_of_forall hlvl_l fun j hj => (hall j hj).2.1
      have hrsns : st.core.rsns = List.replicate c.max_vars 0xFFFFFFFF#32 :=
        list_eq_replicate_of_forall hrsns_l fun j hj => (hall j hj).2.2.1
      let ftrl' := st.core.frame_trail.set c.max_vars 0#32
      let fdec' := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32
      have hftrl_len : ftrl'.length = c.max_vars + 1 := by simp [ftrl', hft_l]
      have hfdec_len : fdec'.length = c.max_vars + 1 := by simp [fdec', hfd_l]
      have hftrl : ftrl' = List.replicate (c.max_vars + 1) 0#32 := by
        refine list_eq_replicate_of_forall hftrl_len fun j hj => ?_
        by_cases hje : j = c.max_vars
        · subst hje; exact List.getElem?_set_self (by rw [hft_l]; exact Nat.lt_succ_self _)
        · rw [List.getElem?_set_ne (Ne.symm hje)]
          exact (hall j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hje)).2.2.2
      have hcore_eq :
          { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32,
            rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' } =
          { st.core with
            frame_trail := st.core.frame_trail.set c.max_vars 0#32,
            frame_dec := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32 } := by
        unfold Zt2FidCorePres at hag
        rw [hag, hmrk, hlvl, hrsns, ← hftrl]
      have hm_out : (FullMem c { s with
          core := { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32, rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
          scratch := st.scratch } ⋆ R) m := by
        rw [hcore_eq]; dsimp only [ftrl', fdec']; rw [hmx_to] at hm; exact hm
      exact hQ st.core.flags fdec' st.scratch m hfl_l hfdec_len hs hpres hm_out

end ZeroTables2FidProof

/-! ## 2. `full_init_hdr_fid` (`Full.fullInitHdrSpec`) -/

section InitHdrFidProof

open scoped FullArenaTactics FullParseInitTactics

private def hdrW0Fid (fuel : BitVec 64) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((w0.set 2 0#64).set 3 1#64).set 14 0#64).set 15 0#64).set 16 0#64).set
    17 fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set
    27 0#64).set 28 (1#64 <<< 28)).set 30 0#64).set 31 0#64).set
    32 1024#64).set 33 1048576#64).set 34 1024#64)

private def hdrW2Fid (mv max_v : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  (((((((((((((((((((((((((w2.set 22 (BitVec.ofNat 64 max_v)).set
    23 (BitVec.ofNat 64 mv)).set 24 (BitVec.ofNat 64 (max_v - mv))).set
    25 0#64).set 0 0#64).set 1 0#64).set 2 0xFFFFFFFF#64).set 3 0xFFFFFFFF#64).set
    4 0xFFFFFFFF#64).set 5 0#64).set 6 0#64).set 7 0#64).set 8 0#64).set
    9 1000#64).set 10 0#64).set 11 1000#64).set 12 0#64).set 13 2#64).set 14 6#64).set
    15 0#64).set 16 1#64).set 17 0#64).set 18 (1#64 <<< 24)).set 19 0#64).set
    20 (1#64 <<< 24)).set 21 0#64

private def hdrW3Fid (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set
    12 0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set
    18 0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set
    24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
    30 0#64).set 31 0#64).set 32 0#64).set 33 0#64).set 34 0#64

private theorem hdrW0Fid_len {fuel : BitVec 64} {w : List (BitVec 64)} :
    (hdrW0Fid fuel w).length = w.length := by simp [hdrW0Fid]

private theorem hdrW2Fid_len {mv max_v : Nat} {w : List (BitVec 64)} :
    (hdrW2Fid mv max_v w).length = w.length := by simp [hdrW2Fid]

private theorem hdrW3Fid_len {mv : Nat} {w : List (BitVec 64)} :
    (hdrW3Fid mv w).length = w.length := by simp [hdrW3Fid]

private theorem len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem decompose35 {α} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4 : α,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := len_cons10 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := len_cons10 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := len_cons10 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private def initHdrFidWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := 0#64
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
        cur_level := 0, fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
        confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0
        min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := 0, scinc := 1#64 <<< 28, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64, q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64
        q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0, rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

private theorem fid_init_hdr4_wp (Γ : Env) {h mv max_v fuel : BitVec 64}
    {w0 w1 w2 w3 : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hle : mv.toNat ≤ max_v.toNat)
    (hm : (hdrTail4 h w0 w1 w2 w3 ⋆ R) m)
    (hQ : ∀ m', (hdrTail4 h (hdrW0Fid fuel w0) (hdrW1 w1)
      (hdrW2Fid mv.toNat max_v.toNat w2) (hdrW3Fid mv.toNat w3) ⋆ R) m' → Q () m') :
    Func.wp Γ full_init_hdr_fid_body (h, mv, max_v, fuel, ()) m Q X := by
  have hsub_bva : max_v - mv = BitVec.ofNat 64 (max_v.toNat - mv.toNat) := by
    apply BitVec.eq_of_toNat_eq; have := max_v.isLt; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsh28 : (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 28) := rfl
  have hsh24 : (1 : BitVec 64) <<< (((24 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 24) := rfl
  unfold Func.wp full_init_hdr_fid_body
  fp_head_steps
  rw [hsub_bva, hsh28, hsh24] at hm
  unfold hdrW0Fid hdrW1 hdrW2Fid hdrW3Fid at hQ
  rw [bv_ofNat_toNat_eq mv, bv_ofNat_toNat_eq max_v] at hQ
  exact hQ m hm

private theorem hdrW0Fid_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (hdrTailWords0 c (initHdrFidWitness c fuel))[i]?) :
    hdrW0Fid fuel w0 = hdrTailWords0 c (initHdrFidWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [hdrTailWords0, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [hdrW0Fid, hdrTailWords0, initHdrFidWitness, e0, e1, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e21, e22, e23, e24, e25, e26, e29]

private theorem hdrW1Fid_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (hdrTailWords1 c (initHdrFidWitness c fuel))[i]?) :
    hdrW1 w1 = hdrTailWords1 c (initHdrFidWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [hdrTailWords1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [hdrW1, hdrTailWords1, initHdrFidWitness, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]

private theorem hdrW2Fid_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (hdrTailWords2 c (initHdrFidWitness c fuel))[i]?) :
    hdrW2Fid c.mv c.max_vars w2 = hdrTailWords2 c (initHdrFidWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [hdrTailWords2, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [hdrW2Fid, hdrTailWords2, initHdrFidWitness, hbva, e26, e27, e28, e29, e30, e31, e32, e33,
    e34]

private theorem hdrW3Fid_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (hdrTailWords3 c (initHdrFidWitness c fuel))[i]?) :
    hdrW3Fid c.mv w3 = hdrTailWords3 c (initHdrFidWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [hdrTailWords3, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e2 e3 e4 e6 e7 e8
  simp [hdrW3Fid, hdrTailWords3, initHdrFidWitness, e0, e1, e2, e3, e4, e6, e7, e8]

/-- S11-3 lazy-activation `full_init_hdr_fid` satisfies exact canonical `Full.fullInitHdrSpec`. -/
theorem full_init_hdr_fid_wp (Γ : Env) :
    ∀ a m Q X, Full.fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_fid_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := initHdrFidWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (hdrTailWords0 c s0).length = 35 := by simp [hdrTailWords0]
  have hw_len1 : (hdrTailWords1 c s0).length = 35 := by simp [hdrTailWords1]
  have hw_len2 : (hdrTailWords2 c s0).length = 35 := by simp [hdrTailWords2]
  refine fid_init_hdr4_wp Γ (by rw [hmv_to, hmx_to]; have := c.hbva; omega)
    (array64_to_hdrTail4 hw hm) fun m' hm' => ?_
  rw [hmv_to, hmx_to] at hm'
  have hm_arr : (array64 (c.hdr + 32) (hdrW0Fid fuel w0 ++ hdrW1 w1 ++
      hdrW2Fid c.mv c.max_vars w2 ++ hdrW3Fid c.mv w3) ⋆ R) m' := by
    rwa [hdrTail4_eq_array64 (by rw [hdrW0Fid_len]; exact h0l) (by rw [hdrW1_len]; exact h1l)
      (by rw [hdrW2Fid_len]; exact h2l) (by rw [hdrW3Fid_len]; exact h3l)] at hm'
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : hdrW0Fid fuel w0 = hdrTailWords0 c s0 := hdrW0Fid_eq c fuel w0 h0l fun i hi => by
    have ⟨hi', hm'⟩ := hi0 i hi; have hgi := hws0 i hm'
    dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
    unfold Full.hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : hdrW1 w1 = hdrTailWords1 c s0 := hdrW1Fid_eq c fuel w1 h1l fun i hi => by
    have ⟨hi35, hm'⟩ := hi1 i hi; have hgi := hws0 (35 + i) hm'
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : hdrW2Fid c.mv c.max_vars w2 = hdrTailWords2 c s0 :=
    hdrW2Fid_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi; have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold Full.hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : hdrW3Fid c.mv w3 = hdrTailWords3 c s0 := hdrW3Fid_eq c fuel w3 h3l fun i hi => by
    have ⟨hi35, hm'⟩ := hi3 i hi; have hgi := hws0 (105 + i) hm'
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  change (array64 (c.hdr + 32) (Full.hdrTailWords c s0) ⋆ R) m' at hm_arr
  exact hQ s0 m' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

end InitHdrFidProof

/-! ## 3. `full_activate_lit_fid` (`fullActivateLitFidSpec`) -/

section ActivateLitFidProof

open scoped FullArenaTactics

/-- S11-3 lazy activation `full_activate_lit_fid(h, v)` preserves all `FullWitnessInv` fields
and `FullExtScratchPres`, mutating only `flags`, `unassigned`, `glue_used[31]`, VMTF queue,
`score[v]`, and EVSIDS heap (via `full_heap_push`). -/
theorem full_activate_lit_fid_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullActivateLitFidSpec a m Q X →
      Func.wp Γ full_activate_lit_fid_body a m Q X := by
  rintro ⟨h, v32, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
  unfold Func.wp full_activate_lit_fid_body
  c0_hsteps_nogrp
  c0_hsplit
  · -- `(u64)v >= cv`: no-op
    c0_hsteps
    exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
  · -- `(u64)v < cv`
    have hv_lt : v32.toNat < s.core.cur_vars := by
      have h1 : ¬ s.core.cur_vars % 2 ^ 64 ≤ (v32.setWidth 64).toNat := by assumption
      have h2 : (v32.setWidth 64).toNat = v32.toNat := by simp [BitVec.toNat_setWidth]; omega
      omega
    have hv_fl : (v32.setWidth 64).toNat < s.core.flags.length := by
      rw [hlen.core_ok.flags_len]; simp [BitVec.toNat_setWidth]; omega
    c0_hsteps_nogrp
    c0_hsplit
    · -- Already active: no-op
      c0_hsteps
      exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
    · -- Activate `v`
      have hgu31 : 31 < s.scratch.glue_used.length := by rw [hlen.scratch_ok.glue_used_len]; decide
      c0_hsteps_nogrp
      -- Join after `if (k < 0xFFFFFFFFu) { k = k + 1u; }` so `k ≠ 0`
      refine wp_join_group (ts := [i32])
        (fun (k32, ()) m1 =>
          k32 ≠ 0#32 ∧
          ∃ fl1 un1,
            (FullMem c { core := { s.core with flags := fl1, unassigned := un1 },
                         scratch := s.scratch } ⋆ R) m1 ∧
            ({ core := { s.core with flags := fl1, unassigned := un1 },
               scratch := s.scratch } : FullState).LengthsOk c)
        (fun Jk ⟨k32, ⟨⟩⟩ m1 ⟨hk_ne0, fl1, un1, hm1, hlen1⟩ => ?_)
        (fun Jk hJk => ?_)
      · have hgu31_1 : 31 < s.scratch.glue_used.length := hgu31
        have hv_qp : (v32.setWidth 64).toNat < s.scratch.q_prev.length := by
          rw [hlen1.scratch_ok.q_prev_len]; simp [BitVec.toNat_setWidth]; omega
        have hv_qn : (v32.setWidth 64).toNat < s.scratch.q_next.length := by
          rw [hlen1.scratch_ok.q_next_len]; simp [BitVec.toNat_setWidth]; omega
        c0_hsteps_nogrp
        -- Join after `if ((u64)old_last >= cv) { h->q_first = v; } else { qn[old_last] = v; }`
        refine wp_join_state0 (α := FullState)
          (fun s2 m2 =>
            (FullMem c s2 ⋆ R) m2 ∧
            ∃ sc2,
              s2 = { core := { s.core with flags := fl1, unassigned := un1 }, scratch := sc2 } ∧
              s2.LengthsOk c ∧ Full.FullExtScratchPres s s2)
          (fun Jq s2 m2 ⟨hm2, sc2, hs2eq, hlen2, hpres2⟩ => ?_)
          (fun Jq hJq => ?_)
        · subst hs2eq
          have hv_qs : (v32.setWidth 64).toNat < sc2.q_stamp.length := by
            rw [hlen2.scratch_ok.q_stamp_len]; simp [BitVec.toNat_setWidth]; omega
          have hv_sc : (v32.setWidth 64).toNat < sc2.score.length := by
            rw [hlen2.scratch_ok.score_len]; simp [BitVec.toNat_setWidth]; omega
          have hk64_ne0 : k32.setWidth 64 ≠ 0#64 := by
            intro h0
            have h1 := congrArg BitVec.toNat h0
            simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1
            have : k32.toNat < 2 ^ 32 := k32.isLt
            have hk0 : k32.toNat = 0 := by
              rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
            exact hk_ne0 (BitVec.eq_of_toNat_eq hk0)
          c0_hsteps_nogrp
          c0_call hHeapPush
          refine ⟨c, _, R, rfl, ?_, hm, fun _ s3 m3 hcore3 hlen3 hpres3 hm3 => ?_⟩
          · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
              q_stamp_len := by simp [hlen2.scratch_ok.q_stamp_len]
              score_len := by simp [hlen2.scratch_ok.score_len] }⟩
          · have hceq3 : s3.core = { s.core with flags := fl1, unassigned := un1 } := hcore3
            have hs3_eq : s3 = { core := { s.core with flags := fl1, unassigned := un1 }
                                 scratch := s3.scratch } := by
              cases s3; simp only [FullState.mk.injEq, and_true]; exact hceq3
            have hpres_fin : Full.FullExtScratchPres s s3 :=
              ⟨hpres3.1.1.trans hpres2.1, hpres3.1.2.trans hpres2.2⟩
            c0_hsteps
            rw [hs3_eq] at hlen3 hpres_fin hm3
            exact hQ fl1 un1 s3.scratch m3 hlen3 hpres_fin hm3
        · c0_hsteps_nogrp
          · -- `old_last >= cv`
            exact hJq _ m ⟨hm, _, rfl,
              ⟨hlen1.core_ok, { hlen1.scratch_ok with
                glue_used_len := by simp [hlen1.scratch_ok.glue_used_len]
                q_prev_len := by simp [hlen1.scratch_ok.q_prev_len]
                q_next_len := by simp [hlen1.scratch_ok.q_next_len] }⟩,
              ⟨rfl, rfl⟩⟩
          · -- `old_last < cv`
            have hol_qn : ((s.scratch.q_last.setWidth 32).setWidth 64).toNat <
                (s.scratch.q_next.set (v32.setWidth 64).toNat 4294967295#32).length := by
              rw [List.length_set, hlen1.scratch_ok.q_next_len]
              have h1 : ¬ s.core.cur_vars % 2 ^ 64 ≤
                  (s.scratch.q_last.setWidth 32).toNat := by assumption
              simp only [BitVec.toNat_setWidth]
              have := (s.scratch.q_last.setWidth 32).isLt
              omega
            c0_hsteps
            exact hJq _ m ⟨hm, _, rfl,
              ⟨hlen1.core_ok, { hlen1.scratch_ok with
                glue_used_len := by simp [hlen1.scratch_ok.glue_used_len]
                q_prev_len := by simp [hlen1.scratch_ok.q_prev_len]
                q_next_len := by simp [hlen1.scratch_ok.q_next_len] }⟩,
              ⟨rfl, rfl⟩⟩
      · c0_hsteps_nogrp
        · -- `k < 0xFFFFFFFFu`: `k + 1 ≠ 0`
          have hk_lt : (s.scratch.glue_used[31]'hgu31).toNat < 4294967295 := by assumption
          have hk1_ne0 : s.scratch.glue_used[31]'hgu31 + 1#32 ≠ 0#32 := by
            intro h0
            have h1 := congrArg BitVec.toNat h0
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
            omega
          exact hJk (s.scratch.glue_used[31]'hgu31 + 1#32, ()) m
            ⟨hk1_ne0, _, _, hm,
             ⟨{ hlen.core_ok with flags_len := by simp [hlen.core_ok.flags_len] }, hlen.scratch_ok⟩⟩
        · -- `k == 0xFFFFFFFFu`: already `≠ 0`
          have hk_ge : 4294967295 ≤ (s.scratch.glue_used[31]'hgu31).toNat := by
            have h1 : ¬ (s.scratch.glue_used[31]'hgu31).toNat < 4294967295 := by assumption
            omega
          have hk_ne0 : s.scratch.glue_used[31]'hgu31 ≠ 0#32 := by
            intro h0; rw [h0] at hk_ge; simp at hk_ge
          exact hJk (s.scratch.glue_used[31]'hgu31, ()) m
            ⟨hk_ne0, _, _, hm,
             ⟨{ hlen.core_ok with flags_len := by simp [hlen.core_ok.flags_len] }, hlen.scratch_ok⟩⟩

end ActivateLitFidProof

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

end
