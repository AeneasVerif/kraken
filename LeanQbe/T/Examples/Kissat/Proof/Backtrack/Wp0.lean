/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Backtrack WP Proofs — Part 0 (`Proof.Backtrack.Wp0`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`) for:
1. `full_assign_lvl` (`fullAssignLvlSpec`)
2. `full_assign` (`fullAssignSpec`)
3. `full_save_target_best` (`fullSaveTargetBestSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Backtrack
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local elab "bt_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "bt_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local macro "bt_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv32_lshr_nat1 (x : BitVec 32) {k : Nat} (hk : k = 1) :
    (x >>> k).toNat = x.toNat / 2 := by
  subst hk; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv64_zext32_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem bv32_xor1_toNat (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

private theorem bv8_sext32_eq0_iff (b : BitVec 8) :
    b.signExtend 32 = 0#32 ↔ b = 0#8 := by
  constructor
  · intro h
    ext i hi
    have h1 := congrArg (·[i]) h
    simpa [BitVec.getElem_signExtend, hi, show i < 32 by omega] using h1
  · rintro rfl; decide

private theorem bv8_sext32_ne0_iff (b : BitVec 8) :
    b.signExtend 32 ≠ 0#32 ↔ b ≠ 0#8 := by
  constructor
  · intro hne heq; exact hne ((bv8_sext32_eq0_iff b).mpr heq)
  · intro hne heq; exact hne ((bv8_sext32_eq0_iff b).mp heq)

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv8_setWidth_neg1 : (BitVec.setWidth 8 (-1 : BitVec 32)) = 255#8 := by
  decide

private theorem bv64_shl1_toNat {x : BitVec 64} {k : Nat} (hk : k = 1)
    (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< k).toNat = 2 * x.toNat := by
  subst hk
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt hx]

private theorem bv64_ule_false_lt {a b : BitVec 64} (h : a.ule b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.ule b = true) := by simp [h]
  rw [BitVec.ule_iff_le] at h1
  have h2 : ¬ a.toNat ≤ b.toNat := fun hle => h1 hle
  omega

private theorem fullScratch_upd_eq (sc : FullScratch) (ta ba : BitVec 64)
    (pt pb : List (BitVec 8)) :
    { sc with
      target_assigned := ta, best_assigned := ba,
      phases_target := pt, phases_best := pb } =
      { heap_len := sc.heap_len, scinc := sc.scinc, rel_period := sc.rel_period,
        rel_limit := sc.rel_limit, rel_wait := sc.rel_wait, rel_u := sc.rel_u,
        rel_v := sc.rel_v, rel_trigger := sc.rel_trigger, conflicts := sc.conflicts,
        learned_lits := sc.learned_lits, min_removed := sc.min_removed,
        delayed_len := sc.delayed_len, stable := sc.stable, switched := sc.switched,
        mode_count := sc.mode_count, mode_confl_lim := sc.mode_confl_lim,
        mode_tick_lim := sc.mode_tick_lim, mode_saved_ticks := sc.mode_saved_ticks,
        search_ticks := sc.search_ticks, q_first := sc.q_first, q_last := sc.q_last,
        q_search_idx := sc.q_search_idx, q_search_stamp := sc.q_search_stamp,
        q_cur_stamp := sc.q_cur_stamp, target_assigned := ta, best_assigned := ba,
        rephase_limit := sc.rephase_limit, rephased := sc.rephased,
        reduce_limit := sc.reduce_limit, reductions := sc.reductions, tier1 := sc.tier1,
        tier2 := sc.tier2, restarts := sc.restarts, restart_limit := sc.restart_limit,
        ema_fast_biased := sc.ema_fast_biased, ema_fast_exp := sc.ema_fast_exp,
        ema_slow_biased := sc.ema_slow_biased, ema_slow_exp := sc.ema_slow_exp,
        extend_len := sc.extend_len, rng_state := sc.rng_state,
        chrono_levels := sc.chrono_levels, otfs_cnt := sc.otfs_cnt,
        eager_sub_cnt := sc.eager_sub_cnt, probe_limit := sc.probe_limit,
        probings := sc.probings, elim_limit := sc.elim_limit,
        eliminations := sc.eliminations, elim_bound := sc.elim_bound,
        iterating := sc.iterating, hbr_cnt := sc.hbr_cnt, trans_cnt := sc.trans_cnt,
        viv_cnt := sc.viv_cnt, subst_cnt := sc.subst_cnt, cong_cnt := sc.cong_cnt,
        sweep_cnt := sc.sweep_cnt, bve_cnt := sc.bve_cnt, bce_cnt := sc.bce_cnt,
        bva_cnt := sc.bva_cnt, walk_cnt_stat := sc.walk_cnt_stat,
        fwd_sub_cnt := sc.fwd_sub_cnt, fwd_str_cnt := sc.fwd_str_cnt,
        ant_sz := sc.ant_sz, res_sz := sc.res_sz, walk_vals := sc.walk_vals,
        phases := sc.phases, phases_target := pt, phases_best := pb,
        walk_best := sc.walk_best, heap := sc.heap, pos := sc.pos,
        shrink_stk := sc.shrink_stk, q_prev := sc.q_prev, q_next := sc.q_next,
        q_stamp := sc.q_stamp, wsort := sc.wsort, work_stk1 := sc.work_stk1,
        work_stk2 := sc.work_stk2, tarjan_mark := sc.tarjan_mark,
        tarjan_reach := sc.tarjan_reach, score := sc.score, sim_sig := sc.sim_sig,
        glue_used := sc.glue_used, last_learned := sc.last_learned,
        delayed := sc.delayed, red_refs := sc.red_refs, extend_stk := sc.extend_stk,
        scratch_buf := sc.scratch_buf } := by
  cases sc; rfl

theorem full_assign_lvl_wp (Γ : Env) :
    ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Func.wp Γ full_assign_lvl_body a m Q X := by
  rintro ⟨h, lit, rsn, alvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hPost⟩
  have hcl := hlen.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hcl.cur_vars_le
  have hte_le := hcl.trail_end_le
  have hvl := hcl.vals_len
  have hfl := hcl.flags_len
  have hll := hcl.lvl_len
  have hrl := hcl.rsns_len
  have htl := hcl.trl_len
  have htpl := hcl.trail_pos_len
  have hphl := hlen.scratch_ok.phases_len
  have hte_lt64 : s.core.trail_end < 2 ^ 64 := by omega
  have hmv_lt64 : c.max_vars < 2 ^ 64 := by omega
  have hv_zext : (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat = lit.toNat / 2 := by
    rw [bv64_zext32_toNat, bv32_lshr_nat1 lit rfl]
  have hlit_zext : (lit.setWidth 64).toNat = lit.toNat := bv64_zext32_toNat lit
  have hneg_zext : ((lit ^^^ (1 : BitVec 32)).setWidth 64).toNat = lit.toNat ^^^ 1 := by
    rw [bv64_zext32_toNat, bv32_xor1_toNat]
  unfold Func.wp full_assign_lvl_body
  bt_steps_nogrp
  refine wp_jnz_of (fun hc => ?_) (fun hnc => ?_)
  · simp only [Arg.val_var] at hc
    have hcv_le_v : s.core.cur_vars ≤ lit.toNat / 2 := by
      have h1 := BitVec.ule_iff_le.mp hc
      change (BitVec.ofNat 64 s.core.cur_vars).toNat ≤
        (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat at h1
      rwa [bv64_ofNat_toNat (by omega), hv_zext] at h1
    bt_steps_nogrp
    rw [ite_eq_left (Or.inl hcv_le_v)] at hPost
    exact hPost
  · simp only [Arg.val_var] at hnc
    have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
      have h1 := bv64_ule_false_lt hnc
      change (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat <
        (BitVec.ofNat 64 s.core.cur_vars).toNat at h1
      rwa [hv_zext, bv64_ofNat_toNat (by omega)] at h1
    have hlit_lt : lit.toNat < 2 * c.max_vars := by omega
    have hv_max : lit.toNat / 2 < c.max_vars := by omega
    have hlit_neg_lt : (lit.toNat ^^^ 1) < 2 * c.max_vars := nat_xor1_lt hlit_lt
    bt_steps_nogrp
    refine wp_jnz_of (fun hc2 => ?_) (fun hnc2 => ?_)
    · simp only [Arg.val_var] at hc2
      have hmv_le_te : c.max_vars ≤ s.core.trail_end := by
        have h1 := BitVec.ule_iff_le.mp hc2
        change (BitVec.ofNat 64 c.max_vars).toNat ≤
          (BitVec.ofNat 64 s.core.trail_end).toNat at h1
        rwa [bv64_ofNat_toNat hmv_lt64, bv64_ofNat_toNat hte_lt64] at h1
      bt_steps_nogrp
      rw [ite_eq_left (Or.inr (Or.inl hmv_le_te))] at hPost
      exact hPost
    · simp only [Arg.val_var] at hnc2
      have hte_max : s.core.trail_end < c.max_vars := by
        have h1 := bv64_ule_false_lt hnc2
        change (BitVec.ofNat 64 s.core.trail_end).toNat <
          (BitVec.ofNat 64 c.max_vars).toNat at h1
        rwa [bv64_ofNat_toNat hte_lt64, bv64_ofNat_toNat hmv_lt64] at h1
      bt_steps_nogrp
      refine wp_jnz_of (fun hc3 => ?_) (fun hnc3 => ?_)
      · simp only [Arg.val_var] at hc3
        have hv_ne0 : s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 := by
          have hne32 : (s.core.vals[(lit.setWidth 64).toNat]'(by omega)).signExtend 32 ≠
              0#32 := by simpa using hc3
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h8 := (bv8_sext32_ne0_iff _).mp hne32
          simpa [hlit_zext] using h8
        bt_steps_nogrp
        rw [ite_eq_left (Or.inr (Or.inr hv_ne0))] at hPost
        exact hPost
      · simp only [Arg.val_var] at hnc3
        have hval0 : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
          have heq32 : (s.core.vals[(lit.setWidth 64).toNat]'(by omega)).signExtend 32 =
              0#32 := by simpa using hnc3
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h8 := (bv8_sext32_eq0_iff _).mp heq32
          simpa [hlit_zext] using h8
        have hno : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
            s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
          rintro (h1 | h2 | h3)
          · exact Nat.not_lt_of_ge h1 hv_lt
          · exact Nat.not_lt_of_ge h2 hte_max
          · exact h3 hval0
        rw [ite_eq_right hno] at hPost
        bt_steps_nogrp
        let vals1 := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8
        have hm1 : (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m := by
          have h1 : (BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1)) = 1#8 := rfl
          have h2 : (BitVec.setWidth 8 (-1 : BitVec 32)) = 255#8 := bv8_setWidth_neg1
          have hset_eq : (s.core.vals.set (lit.setWidth 64).toNat
                (BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1))).set
              ((lit ^^^ (1 : BitVec 32)).setWidth 64).toNat
              (BitVec.setWidth 8 (-1 : BitVec 32)) = vals1 := by
            rw [hlit_zext, hneg_zext, h1, h2]
          rwa [← hset_eq]
        have hv_bv_eq : BitVec.setWidth 64 (lit >>> (1 : Nat)) =
            BitVec.ofNat 64 (lit.toNat / 2) := by
          apply BitVec.eq_of_toNat_eq
          rw [hv_zext, bv64_ofNat_toNat (by omega)]
        have hv_bv_lt : (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat < c.max_vars := by
          rw [hv_zext]; exact hv_max
        refine wp_join_group
          (fun () m1 => ∃ unass1 : BitVec 64,
            (FullMem c { s with core := { s.core with vals := vals1, unassigned := unass1 } } ⋆ R)
              m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨unass1, hm1'⟩
          refine wp_join_group
            (fun () m2 => ∃ phases1 : List (BitVec 8), phases1.length = c.max_vars ∧
              (FullMem c
                { core := { s.core with vals := vals1, unassigned := unass1 }
                  scratch := { s.scratch with phases := phases1 } } ⋆ R) m2) ?_ ?_
          · rintro _ ⟨⟩ m2 ⟨phases1, hph1, hm2⟩
            let s2 : FullState :=
              { core := { s.core with vals := vals1, unassigned := unass1 }
                scratch := { s.scratch with phases := phases1 } }
            bt_steps_nogrp
            refine wp_join_group
              (fun () m3 => ∃ flags1 : List (BitVec 32), flags1.length = c.max_vars ∧
                (FullMem c
                  { core :=
                      { s2.core with
                        lvl := s.core.lvl.set (lit.toNat / 2) alvl
                        flags := flags1
                        rsns := s.core.rsns.set (lit.toNat / 2)
                          (if alvl = 0#32 then 4294967295#32 else rsn)
                        unflushed := if alvl = 0#32 then s.core.unflushed + 1#64 else
                          s.core.unflushed }
                    scratch := s2.scratch } ⋆ R) m3) ?_ ?_
            · rintro _ ⟨⟩ m3 ⟨flags1, hfl1, hm3⟩
              have hte_bv32 : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                  BitVec.ofNat 32 s.core.trail_end := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
              have hte_nat : (BitVec.ofNat 64 s.core.trail_end).toNat = s.core.trail_end :=
                bv64_ofNat_toNat hte_lt64
              have hte_add1 : (BitVec.ofNat 64 s.core.trail_end + 1#64).toNat =
                  s.core.trail_end + 1 := by
                rw [bv64_add1_toNat (by rw [hte_nat]; omega), hte_nat]
              have hv_eq_nat : (BitVec.setWidth 64 (lit >>> (@OfNat.ofNat Nat 1 _))).toNat =
                  lit.toNat / 2 := hv_zext
              dsimp only [Blocks.get]
              bt_steps_nogrp
              rw [show BitVec.setWidth 64 (lit >>> (@OfNat.ofNat Nat 1 _)) =
                BitVec.ofNat 64 (lit.toNat / 2) from hv_bv_eq]
              have htp_nat : (BitVec.ofNat 64 (lit.toNat / 2)).toNat <
                  s2.core.trail_pos.length := by
                rw [bv64_ofNat_toNat (by omega)]; exact htpl ▸ hv_max
              have htrl_nat : (BitVec.ofNat 64 s.core.trail_end).toNat < s2.core.trl.length := by
                rw [hte_nat]; exact htl ▸ hte_max
              dsimp only at hm3 ⊢
              bt_steps
              (try dsimp only at ⊢)
              bt_steps
              refine hPost flags1 unass1 phases1 _ hfl1 hph1 ?_
              dsimp only [s2] at *
              rw [show (BitVec.ofNat 64 s.core.trail_end + 1).toNat =
                s.core.trail_end + 1 from hte_add1] at *
              simp only [bv64_ofNat_toNat (by omega : lit.toNat / 2 < 2 ^ 64),
                hte_bv32, hte_nat, vals1] at *
              assumption
            · intro J3 hJ3
              bt_steps_nogrp
              refine wp_jnz_of (fun ha0 => ?_) (fun hna0 => ?_)
              · have hal0 : alvl = 0#32 := by simpa using ha0
                bt_steps_nogrp
                exact hJ3 () _ ⟨_, And.symm ⟨by
                  simp only [hal0, ↓reduceIte, hv_zext] at *
                  assumption, by simp [hfl]⟩⟩
              · have haln0 : alvl ≠ 0#32 := by simpa using hna0
                bt_steps_nogrp
                refine hJ3 () _ ⟨s.core.flags, hfl, ?_⟩
                simp only [haln0, ↓reduceIte, hv_zext] at *
                assumption
          · intro J2 hJ2
            bt_steps_nogrp
            refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · bt_steps_nogrp
              refine wp_join_group (fun (_pv, ()) m2 => m2 = m1) ?_ ?_
              · rintro _ ⟨pv, ⟨⟩⟩ m2 rfl
                bt_steps_nogrp
                exact hJ2 () _ ⟨_, And.symm ⟨by assumption, by simp [hphl]⟩⟩
              · intro Jpv hJpv
                bt_steps_nogrp
                refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                · bt_steps_nogrp; exact hJpv _ _ rfl
                · bt_steps_nogrp; exact hJpv _ _ rfl
            · bt_steps_nogrp
              exact hJ2 () _ ⟨s.scratch.phases, hphl, hm1'⟩
        · intro J1 hJ1
          bt_steps_nogrp
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · bt_steps_nogrp
            refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · bt_steps_nogrp
              exact hJ1 () _ ⟨_, by assumption⟩
            · bt_steps_nogrp
              exact hJ1 () _ ⟨s.core.unassigned, hm1⟩
          · bt_steps_nogrp
            exact hJ1 () _ ⟨s.core.unassigned, hm1⟩

theorem full_assign_wp (Γ : Env)
    (hLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullAssignSpec a m Q X →
      Func.wp Γ full_assign_body a m Q X := by
  rintro ⟨h, lit, rsn, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl32, hm, hPost⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hcl32 (by decide)
  unfold Func.wp full_assign_body
  bt_steps
  bt_call hLvl
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  have hsw : (BitVec.ofNat 64 s.core.cur_level).setWidth 32 = BitVec.ofNat 32 s.core.cur_level := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have h0_iff : BitVec.ofNat 32 s.core.cur_level = 0#32 ↔ s.core.cur_level = 0 := by
    constructor
    · intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32] at ht; exact ht
    · intro heq; rw [heq]
  simp only [Arg.val_var, wp_ret, vals_nil]
  rw [hsw]
  by_cases hbad : s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
      s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8
  · simp only [hbad, ite_true] at hPost ⊢
    exact hPost
  · simp only [hbad, ite_false] at hPost ⊢
    intro flags' unass' phases' m' hf' hph' hm'
    refine hPost flags' unass' phases' m' hf' hph' ?_
    by_cases h0 : s.core.cur_level = 0
    · simp only [h0, ↓reduceIte] at hm' ⊢; exact hm'
    · have hne : BitVec.ofNat 32 s.core.cur_level ≠ 0#32 := fun heq => h0 (h0_iff.mp heq)
      simp only [h0, hne, ↓reduceIte] at hm' ⊢; exact hm'

private theorem save_phases_loop_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s0 : FullState} {R : Mem 64 → Prop} {ptr : BitVec 64}
    {mkSt : List (BitVec 8) → FullState}
    {arr0 : List (BitVec 8)} {m0 : Mem 64} {Js : Cont []}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hvals_len : s0.core.vals.length = 2 * c.max_vars) (harr0_len : arr0.length = c.max_vars)
    (hwp_load : ∀ xs (i : BitVec 64) (m : Mem 64) (f : Val i8 → Expr Val Cont []),
      xs.length = c.max_vars → (hi : i.toNat < c.max_vars) → (FullMem c (mkSt xs) ⋆ R) m →
      wp Γ Q X (f (s0.core.vals[2 * i.toNat]'(by rw [hvals_len]; omega))) m →
      wp Γ Q X (Expr.load i8 (Arg.var (c.pVals + (i <<< (1 : Nat)))) f) m)
    (hwp_store : ∀ xs (i : BitVec 64) (v : Val i8) (m : Mem 64) (e : Expr Val Cont []),
      xs.length = c.max_vars → i.toNat < c.max_vars → (FullMem c (mkSt xs) ⋆ R) m →
      (∀ m', (FullMem c (mkSt (xs.set i.toNat v)) ⋆ R) m' → wp Γ Q X e m') →
      wp Γ Q X (Expr.store (t := i8) (Arg.var v) (Arg.var (ptr + i)) e) m)
    (hm0 : (FullMem c (mkSt arr0) ⋆ R) m0)
    (hJs : ∀ arr' m', arr'.length = c.max_vars → (FullMem c (mkSt arr') ⋆ R) m' → Js () m') :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js_1 =>
          Blocks.cons
            (fun p =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                  args := (Arg.var p.fst, Arg.var (BitVec.ofNat 64 s0.core.cur_vars), ()) }
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
                    fun p_2 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.shl i64,
                        args := (Arg.var p.fst, Arg.var p_2.fst, ()) }
                      fun p_3 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.pVals, Arg.var p_3.fst, ()) }
                        fun p_4 =>
                        Expr.load i8 (Arg.var p_4.fst) fun ld =>
                          Expr.group (sig := [[]])
                            (fun _Js_2 =>
                              Blocks.cons
                                (fun _ =>
                                  Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var p.fst, Arg.imm 1, ()) }
                                    fun p => Expr.jump Js_1.fst (Arg.var p.fst, ()))
                                Blocks.nil)
                            fun Js_2 =>
                            Expr.let_
                              { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) }
                              fun p_5 =>
                              Expr.let_
                                { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) }
                                fun p_6 =>
                                Expr.let_
                                  { sig := [i8], code := OpCode.sext 8 32,
                                    args := (Arg.var p_5.fst, ()) }
                                  fun p_7 =>
                                  Expr.let_
                                    { sig := [i32, i32],
                                      code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                                      args := (Arg.var p_6.fst, Arg.var p_7.fst, ()) }
                                    fun p_8 =>
                                    Expr.jnz (Arg.var p_8.fst)
                                      (Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var ptr, Arg.var p.fst, ()) }
                                        fun p =>
                                        Expr.store (Arg.var ld) (Arg.var p.fst)
                                          (Expr.jump Js_2.fst ()))
                                      (Expr.jump Js_2.fst ()))
                  (Expr.jump Js ()))
            Blocks.nil)
        fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())) m0 := by
  unfold dimacsBound at hmaxv
  have hcv_lt64 : s0.core.cur_vars < 2 ^ 64 := by omega
  refine wp_loop_inv
    (fun (k, ()) ml => k.toNat ≤ s0.core.cur_vars ∧ ∃ arr : List (BitVec 8),
      arr.length = c.max_vars ∧ (FullMem c (mkSt arr) ⋆ R) ml)
    (fun (k, ()) _ => s0.core.cur_vars - k.toNat)
    (fun J hJ => by bt_steps_nogrp; exact hJ _ _ ⟨Nat.zero_le _, arr0, harr0_len, hm0⟩)
    (fun J (k, ()) ml ⟨hk_le, arr, harr_len, hm_k⟩ ih => ?_)
  bt_steps_nogrp
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · simp only [Arg.val_var] at hlt
    have hk_lt : k.toNat < s0.core.cur_vars := by
      have h1 := BitVec.ult_iff_lt.mp hlt
      change k.toNat < (BitVec.ofNat 64 s0.core.cur_vars).toNat at h1
      rwa [bv64_ofNat_toNat hcv_lt64] at h1
    have hk_max : k.toNat < c.max_vars := by omega
    have hk1_nat : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
    bt_steps_nogrp
    refine hwp_load arr k ml _ harr_len hk_max hm_k ?_
    refine wp_join_group (fun () m2 => ∃ arr' : List (BitVec 8),
      arr'.length = c.max_vars ∧ (FullMem c (mkSt arr') ⋆ R) m2) ?_ ?_
    · rintro _ ⟨⟩ m2 ⟨arr', harr', hm2⟩
      bt_steps_nogrp
      exact ih (k + 1#64, ()) m2 (by dsimp only; rw [hk1_nat]; omega)
        ⟨by rw [hk1_nat]; omega, arr', harr', hm2⟩
    · intro J2 hJ2
      bt_steps_nogrp
      refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
      · bt_steps_nogrp
        refine hwp_store arr k (s0.core.vals[2 * k.toNat]'(by rw [hvals_len]; omega))
          ml _ harr_len hk_max hm_k fun m2 hm2 => ?_
        bt_steps_nogrp
        exact hJ2 () m2 ⟨_, by simp [harr_len], hm2⟩
      · bt_steps_nogrp
        exact hJ2 () ml ⟨arr, harr_len, hm_k⟩
  · simp only [Arg.val_var] at hge
    bt_steps_nogrp
    exact hJs arr ml harr_len hm_k

theorem full_save_target_best_wp (Γ : Env) :
    ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Func.wp Γ full_save_target_best_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hPost⟩
  dsimp only [fullSafetySlice] at hlen hm hPost
  have hmaxv := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hvals_len := hlen.core_ok.vals_len
  have hpt_len := hlen.scratch_ok.phases_target_len
  have hpb_len := hlen.scratch_ok.phases_best_len
  have hpres_id : FullProbeScratchPres s s :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold Func.wp full_save_target_best_body
  bt_steps_nogrp
  refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
  · bt_steps_nogrp
    exact hPost () s m rfl hlen ⟨hpres_id, s.scratch.target_assigned, s.scratch.best_assigned,
      s.scratch.phases_target, s.scratch.phases_best,
      fullScratch_upd_eq s.scratch s.scratch.target_assigned s.scratch.best_assigned
        s.scratch.phases_target s.scratch.phases_best⟩ hm
  · bt_steps_nogrp
    refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
    · bt_steps_nogrp
      exact hPost () s m rfl hlen ⟨hpres_id, s.scratch.target_assigned, s.scratch.best_assigned,
        s.scratch.phases_target, s.scratch.phases_best,
        fullScratch_upd_eq s.scratch s.scratch.target_assigned s.scratch.best_assigned
          s.scratch.phases_target s.scratch.phases_best⟩ hm
    · bt_steps_nogrp
      refine wp_join_group (fun (_assigned, ()) ml => ml = m) ?_ ?_
      · rintro _ ⟨assigned, ⟨⟩⟩ ml rfl
        refine wp_join_group
          (fun () m1 => ∃ ta1 pt1, pt1.length = c.max_vars ∧
            (FullMem c { s with scratch :=
              { s.scratch with target_assigned := ta1, phases_target := pt1 } } ⋆ R) m1)
          ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨ta1, pt1, hpt1, hm1⟩
          let s1 : FullState :=
            ⟨s.core, { s.scratch with target_assigned := ta1, phases_target := pt1 }⟩
          have hm1' : (FullMem c s1 ⋆ R) m1 := hm1
          refine wp_join_group (fun () mf => Q () mf) ?_ ?_
          · rintro _ ⟨⟩ mf hQ_mf
            bt_steps_nogrp; exact hQ_mf
          · intro J_exit hJ_exit
            bt_steps_nogrp
            refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · bt_steps_nogrp
              let mkBest : List (BitVec 8) → FullState := fun pb =>
                ⟨s.core, { s.scratch with
                  target_assigned := ta1, best_assigned := assigned,
                  phases_target := pt1, phases_best := pb }⟩
              have hm_b : (FullMem c (mkBest s.scratch.phases_best) ⋆ R) m := by
                dsimp only [mkBest, s1] at *; assumption
              refine save_phases_loop_wp (c := c) (s0 := s1) (R := R) (ptr := c.pPhasesBest)
                (mkSt := mkBest) hmaxv hcv_le hvals_len hpb_len
                (fun xs i m f hxs hi hm_i hf => by
                  have h2k : (i <<< (1 : Nat)).toNat = 2 * i.toNat :=
                    bv64_shl1_toNat rfl (by unfold dimacsBound at hmaxv; omega)
                  dsimp only [mkBest] at hm_i
                  dsimp only [s1] at hf ⊢
                  bt_steps_nogrp
                  simpa only [h2k] using hf)
                (fun xs i v m e hxs hi hm_i he => by
                  dsimp only [mkBest] at hm_i ⊢
                  bt_steps_nogrp
                  exact he _ (by assumption))
                hm_b (fun pb' mb hpb' hmb => ?_)
              let sb : FullState := mkBest pb'
              have hpres_b : FullProbeScratchPres s sb :=
                ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have hlen_b : sb.LengthsOk c :=
                ⟨hlen.core_ok, { hlen.scratch_ok with
                  phases_target_len := hpt1, phases_best_len := hpb' }⟩
              exact hJ_exit () mb (hPost () sb mb rfl hlen_b
                ⟨hpres_b, ta1, assigned, pt1, pb',
                  fullScratch_upd_eq s.scratch ta1 assigned pt1 pb'⟩ hmb)
            · bt_steps_nogrp
              have hpres' : FullProbeScratchPres s s1 :=
                ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have hlen' : s1.LengthsOk c :=
                ⟨hlen.core_ok, { hlen.scratch_ok with phases_target_len := hpt1 }⟩
              exact hJ_exit () m1 (hPost () s1 m1 rfl hlen'
                ⟨hpres', ta1, s.scratch.best_assigned, pt1, s.scratch.phases_best,
                  fullScratch_upd_eq s.scratch ta1 s.scratch.best_assigned pt1
                    s.scratch.phases_best⟩
                hm1')
        · intro J2 hJ2
          bt_steps_nogrp
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · bt_steps_nogrp
            let mkTgt : List (BitVec 8) → FullState := fun pt =>
              ⟨s.core, { s.scratch with target_assigned := assigned, phases_target := pt }⟩
            have hm_t : (FullMem c (mkTgt s.scratch.phases_target) ⋆ R) m := by
              dsimp only [mkTgt] at *; assumption
            refine save_phases_loop_wp (c := c) (s0 := s) (R := R) (ptr := c.pPhasesTarget)
              (mkSt := mkTgt) hmaxv hcv_le hvals_len hpt_len
              (fun xs i m f hxs hi hm_i hf => by
                have h2k : (i <<< (1 : Nat)).toNat = 2 * i.toNat :=
                  bv64_shl1_toNat rfl (by unfold dimacsBound at hmaxv; omega)
                dsimp only [mkTgt] at hm_i
                bt_steps_nogrp
                simpa only [h2k] using hf)
              (fun xs i v m e hxs hi hm_i he => by
                dsimp only [mkTgt] at hm_i ⊢
                bt_steps_nogrp
                exact he _ (by assumption))
              hm_t (fun pt' mt hpt' hmt => hJ2 () mt ⟨assigned, pt', hpt', hmt⟩)
          · bt_steps_nogrp
            exact hJ2 () ml ⟨s.scratch.target_assigned, s.scratch.phases_target, hpt_len, hm⟩
      · intro J hJ
        bt_steps_nogrp
        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
        · bt_steps_nogrp
          exact hJ _ _ rfl
        · bt_steps_nogrp
          exact hJ _ _ rfl

end LeanQbe.T.Examples.Kissat.Proof.Backtrack
