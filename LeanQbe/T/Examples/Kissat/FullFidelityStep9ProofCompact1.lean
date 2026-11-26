/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2d
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M6 Watch/GC Proofs Part 2: `full_arena_sweep_m6_wp`

Proves `full_arena_sweep_m6_wp` against exact canonical `Full.fullArenaSweepSpec`, integrating:
1. Partial irredundant-prefix skipping when `!at_root && unflushed == 0 && 0 < first_reducible`,
2. `full_sweep_bins_range_m6` (keeping `< start` watches + binary dedup),
3. Irred/redundant arena compaction + live `first_reducible` / `has_irred_after_red` tracking,
4. `full_move_red_end_m6` (or `PH_RSN` clear) + `last_learned` reset + `full_rewatch_range_m6`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceSpecs FullReduceHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullReduceTactics M6Tactics1 M6Tactics2a

local macro "m6_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq, LeanQbe.T.wp_let_mul_eq,
      LeanQbe.T.wp_let_and_eq, LeanQbe.T.wp_let_or_eq,
      LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
      LeanQbe.T.wp_let_trunc_eq,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
      LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.sgt,
      LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
      LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq,
      LeanQbe.T.evalBits_sgt_eq,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, Bool.false_eq_true, ite_false, ite_true,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

local macro "m6_tiny_lets" : tactic =>
  `(tactic| (
    try m6_unmdata
    try repeat (first | (m6_strip; try m6_tiny_simp) | m6_tiny_simp)))

local macro "m6_tiny_jump" : tactic =>
  `(tactic| (
    m6_tiny_lets
    try repeat (first | (refine ⟨by decide, ?_⟩; m6_tiny_lets) | m6_strip)
    try simp only [LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there]
    try rw [wp_jump]
    try simp only [LeanQbe.T.wp_ret]))

open Lean Elab Tactic in
local elab "m6_jnz" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try m6_tiny_lets
        try repeat m6_strip
        try rw [wp_jump]))
      break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

/-! ## 1. `full_arena_sweep_m6_wp` (`Full.fullArenaSweepSpec`) -/

private def PreSweepValBrkInv (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64, .bool]) (mB : Mem 64) : Prop :=
  let (p, _cnt, pre_ok, ()) := arg
  mB = m0 ∧ p.toNat ≤ fp ∧ (pre_ok = true → CleanIrredChain s.core.arena 0 p.toNat)

private def PreSweepValInv (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64]) (mL : Mem 64) : Prop :=
  let (p, _cnt, ()) := arg
  mL = m0 ∧ p.toNat ≤ fp ∧ CleanIrredChain s.core.arena 0 p.toNat

private def PreSweepInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
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

private def M6SweepExitInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
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
    (start < dst.toNat → start ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst.toNat }) ∧
    FullWitnessInv c F0 F_cur { sE.core with arena_len := dst.toNat } ∧
    M6FirstRedOk c F_cur s sPre sE start dst.toNat rwE first_red ∧
    (0 < s.core.cur_level → SweepReasonMapInv sPre.core sE.core sPre.core.arena_len dst.toNat) ∧
    (unsat = true → s.core.cur_level = 0 ∧ F0.Unsat) ∧
    (new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sE.core.trail_end) ∧
    (0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧ sE.core.vals = s.core.vals ∧
      sE.core.lvl = s.core.lvl ∧ sE.core.trl = s.core.trl ∧ sE.core.trail_pos = s.core.trail_pos ∧
      sE.core.trail_end = s.core.trail_end) ∧
    (FullMem c sE ⋆ R) mE

private def M6LastLearnedLoopInv (c : FullCfg) (sM : FullState) (R : Mem 64 → Prop)
    (dst irred redd : BitVec 64) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (li, ()) := arg
  li.toNat ≤ 16 ∧
  ∃ llL : List (BitVec 32), llL.length = 16 ∧
    (∀ j < li.toNat, llL[j]? = some 0xFFFFFFFF#32) ∧
    (FullMem c
      { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                               num_irred := irred, num_redundant := redd }
        scratch := { sM.scratch with last_learned := llL } } ⋆ R) mL

private def M6RsnLoopInv (s sC : FullState) (arH : List (BitVec 32))
    (src dst st : Nat) (m0 : Mem 64) (arg : Tup Val [i32]) (mI : Mem 64) : Prop :=
  let (i, ()) := arg
  m0 = mI ∧ i.toNat ≤ st ∧
  (0 < s.core.cur_level → ∀ j < i.toNat,
    let lit := arH[dst + 3 + j]?.getD 0#32
    ¬ (lit.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))

private def M6RsnNextInv (s sC : FullState) (litI : BitVec 32) (src : Nat) (m0 : Mem 64)
    (_ : Tup Val []) (mN : Mem 64) : Prop :=
  m0 = mN ∧
  (0 < s.core.cur_level →
    ¬ (litI.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))


private theorem s9_pre_clr_no_chg_id (arL : List (BitVec 32)) {i : Nat} (hi : i < arL.length)
    (hzero : (arL[i]'hi) &&& 0x00200000#32 = 0#32) :
    arL.set i ((arL[i]'hi) &&& ~~~0x00200000#32) = arL := by
  have hno : ((arL[i]'hi) &&& ~~~0x00200000#32) = arL[i]'hi := by
    ext bi hbi
    have hbi' := congrArg (fun bv : BitVec 32 => bv[bi]'hbi) hzero
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at hbi' ⊢
    cases h1 : (arL[i]'hi)[bi] <;> cases h2 : (0x00200000#32)[bi] <;>
      simp only [h1, h2, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false] at hbi' ⊢ <;>
      first | rfl | exact absurd hbi' (by decide)
  rw [hno, List.set_getElem_self]

theorem full_arena_sweep_m6_step9_wp (Γ : Env)
    (hsweep_bins_r : ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Γ "full_sweep_bins_range_m6" [i64, i64] [] a m Q X)
    (hnext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hcopy : ∀ a m Q X, Full.fullSweepCopySpec a m Q X →
      Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X)
    (hmovered : ∀ a m Q X, fullMoveRedEndSpec a m Q X →
      Γ "full_move_red_end_m6" [i64, i64, i64] [] a m Q X)
    (hrewatch_r : ∀ a m Q X, fullRewatchRangeSpec a m Q X →
      Γ "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Func.wp Γ fidStep9ArenaSweepM6Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd0, hdm0, hrmk0, hm, hQ⟩
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hal_le : s.core.arena_len ≤ c.arena_cap := hlen.core_ok.arena_len_le
  have har_len : s.core.arena.length = c.arena_cap := hlen.core_ok.arena_len_arr
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hdec_cl0 : ∀ (b : Bool), (BitVec.ofNat 64 s.core.cur_level == 0) = b ↔
      (if b then s.core.cur_level = 0 else 0 < s.core.cur_level) := by
    intro b; cases b
    · simp only [beq_eq_false_iff_ne, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hne; rcases Nat.eq_zero_or_pos s.core.cur_level with h0 | hpos
        · exact absurd (by simp [h0]) hne
        · exact hpos
      · intro hpos h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this; simp at this; omega
    · simp only [beq_iff_eq, ↓reduceIte]
      constructor
      · intro h0; have := congrArg BitVec.toNat h0
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this
      · intro h0; simp [h0]
  have hcl_beq : (BitVec.ofNat 64 s.core.cur_level == 0) = decide (s.core.cur_level = 0) := by
    by_cases hcl0 : s.core.cur_level = 0
    · rw [(hdec_cl0 true).mpr hcl0]; simp [hcl0]
    · rw [(hdec_cl0 false).mpr (Nat.pos_of_ne_zero hcl0)]; simp [hcl0]
  -- Step 1: optional irredundant prefix validation & `PH_RSN` clear
  unfold Func.wp fidStep9ArenaSweepM6Fn; dsimp only; unfold full_arena_sweep_m6_body
  c0_hsteps_nogrp
  refine wp_join_group (PreSweepInv c F0 F_cur s R) ?_ ?_
  · rintro _ ⟨start, pre_irred, ⟨⟩⟩ mP
      ⟨hstart_le, hstart_pos, arPre, hlenPre, hwPre, hndPre, hst_mem, hcmpPre,
       hrmPre_init, hrmkPre, hmP⟩
    let sPre : FullState := { s with core := { s.core with arena := arPre } }
    change sPre.LengthsOk c at hlenPre
    change FullWitnessInv c F0 F_cur sPre.core at hwPre
    change FullArenaVarsNodup sPre at hndPre
    change (start.toNat < s.core.arena_len → start.toNat ∈ fullArenaClauseRefs sPre) at hst_mem
    change CompactPrefixOk c F_cur s sPre.core start.toNat at hcmpPre
    change SweepReasonMapInv sPre.core sPre.core start.toNat start.toNat at hrmPre_init
    change (0 < s.core.cur_level →
      ∀ idx < sPre.core.trail_end,
        let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
        0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
        (rsn &&& 0x80000000#32) = 0#32 → start.toNat ≤ rsn.toNat →
        (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32) at hrmkPre
    change (FullMem c sPre ⋆ R) mP at hmP
    clear hw hrmk0 hm har_len
    -- Call `full_sweep_bins_range_m6(h, start)`
    m6_steps; c0_call hsweep_bins_r
    refine fullSweepBinsRangeSpec.intro c F0 F_cur sPre R rfl hlenPre (fun _ => hdm0) hwPre hmP
      fun wvec0 wstk0 wlen0 nb0 ws0 m0 hlen0 hlay0 hlt0 hw0 hm0 => ?_
    clear hsweep_bins_r hmP
    let s0 : FullState :=
      { sPre with
        core := { sPre.core with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := 0#64,
                                 num_binary := nb0 }
        scratch := { sPre.scratch with wsort := ws0 } }
    have hlike0 : M6SweepLike s s0 := ⟨s.core.vals, s.core.flags, s.core.lvl, s.core.rsns,
      s.core.trl, s.core.trail_pos, s.core.trail_end, s.core.unassigned, s.core.unflushed,
      wvec0, wstk0, arPre, wlen0, 0#64, nb0, s.core.oom, s.scratch.phases, ws0, rfl⟩
    have harPre_len : sPre.core.arena.length = c.arena_cap := hlenPre.core_ok.arena_len_arr
    have hcmp0 : CompactPrefixOk c F_cur s s0.core start.toNat :=
      (arenaPrefix_preserves_compact (k := sPre.core) (k' := s0.core) hcmpPre rfl
        harPre_len harPre_len (by omega) (fun _ _ => rfl)).1
    have hrm0 : SweepReasonMapInv sPre.core s0.core start.toNat start.toNat := hrmPre_init
    -- Join point after main compaction loop
    m6_to_group
    refine wp_join_group (M6SweepExitInv c F0 F_cur s sPre R start.toNat) ?_ ?_
    · -- Post-loop: `full_move_red_end_m6` or `PH_RSN` clear, header scalars, `ll`, rewatch
      rintro _ ⟨_srcE, dst, first_red, irred, redd, has_iar, unsat, new_unit, ⟨⟩⟩ mE
        ⟨hst_dst, hdst_le, hhas_iar, sE, rwE, hlikeE, hlenE, hcmpE, hcmpE_st, hlayE, hltE,
         hstE_in, hwEnd, hfrE, hrmE, hunsatE, hunitE, hposE, hmE⟩
      clear hnext hcopy hrmPre_init hrmkPre hcmp0 hrm0 hw0 hlay0 hlt0 hlen0 hm0
        hstart_pos hst_mem hcmpPre hcl_beq
      obtain ⟨hcvE, halE, hclE, hdmE, hftE, hfdE, hincE, helE, hws2E⟩ := hlikeE.unchanged
      have harE_len : sE.core.arena.length = c.arena_cap := hlenE.core_ok.arena_len_arr
      -- Join point `M6PostMoveInv` after `if (!unsat && h->oom == 0 && has_iar && first_red < dst)`
      m6_to_group
      refine wp_join_group (M6PostMoveInv c F0 F_cur s R start.toNat dst unsat new_unit) ?_ ?_
      · rintro _ ⟨⟩ mM ⟨sM, hpostM, hlenM, hcvM, halM, hclM, hdmM, hftM, hfdM, hincM, helM, hws2M,
            hwM, hnoM, hndM, hstM_in, hunsM, hunitM, hposM, hmM⟩
        clear hmovered hlikeE hlenE hcmpE hcmpE_st hlayE hltE hwEnd hfrE hrmE hunsatE hunitE
          hposE hmE
        rcases hpostM with ⟨vM, fM, lM, rM, tM, tpM, teM, uM, ufM, wvM, wsM, arM, wlM, wuM,
          frM, nbM, oomM, hcoreM⟩
        have hll_len : sM.scratch.last_learned.length = 16 := hlenM.scratch_ok.last_learned_len
        m6_c0_steps
        refine wp_loop_inv (M6LastLearnedLoopInv c sM R dst irred redd)
          (fun (li, ()) _ => 16 - li.toNat) (fun Jli hLoopLi => ?_) ?_
        · m6_c0_steps
          exact hLoopLi (0#64, ()) _ ⟨Nat.zero_le _, sM.scratch.last_learned, hll_len,
            fun _ hj => absurd hj (Nat.not_lt_zero _), fullMem_cast hm rfl⟩
        · rintro Jli ⟨li, ⟨⟩⟩ mL ⟨hli_le, llL, hllL, hallL, hmL⟩ hLoopLi
          m6_jnz
          · have hli_lt : li.toNat < 16 := by c0_bound
            have hli1_eq : (li + (1 : BitVec 64)).toNat = li.toNat + 1 := bv64_add1_lt (by omega)
            m6_c0_steps
            refine hLoopLi (li + (1 : BitVec 64), ()) _ (by dsimp only; rw [hli1_eq]; omega)
              ⟨by rw [hli1_eq]; omega, llL.set li.toNat 0xFFFFFFFF#32, List.length_set.trans hllL,
               fun j hj => ?_, fullMem_cast hm rfl⟩
            rw [hli1_eq] at hj; by_cases hje : j = li.toNat
            · subst j; exact List.getElem?_set_self (by omega)
            · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hallL j (by omega)
          · have hli_16 : li.toNat = 16 := by c0_bound
            let scLL : FullScratch := { sM.scratch with last_learned := llL }
            let sLL : FullState :=
              { core :=
                  { s.core with
                    vals := vM, flags := fM, lvl := lM, rsns := rM, trl := tM, trail_pos := tpM,
                    trail_end := teM, unassigned := uM, unflushed := ufM, wvec := wvM, wstk := wsM,
                    arena := arM, arena_len := dst.toNat, wlen := wlM, wusable := wuM,
                    arena_garbage := 0#64, first_reducible := frM, num_irred := irred,
                    num_redundant := redd, num_binary := nbM, oom := oomM },
                scratch := scLL }
            obtain ⟨hlenLL, hll_wf, hwLL, hndLL, hnoLL, hstLL_in, hmLL⟩ :=
              m6_post_ll_witness hcoreM hlenM (by change dst.toNat ≤ c.arena_cap; omega) hllL
                (fun j hj => hallL j (by rw [hli_16]; exact hj)) hwM hnoM hndM hnd0
                start.toNat hstM_in hmL
            m6_jnz
            · -- `unsat = true`: return `2#64`
              have hu_t : unsat = true := by simpa using hc
              m6_c0_steps
              exact hQ 2#64 vM fM lM rM tM tpM teM uM ufM wvM wsM arM dst.toNat wlM wuM frM
                irred redd nbM oomM scLL mL hlenLL (Or.inr (Or.inr (Or.inl rfl))) helM hws2M
                hll_wf hwLL hndLL (fun h => by rcases h with h | h <;> cases h)
                (fun hpos => absurd (hposM hpos).1 (by simp [hu_t]))
                (fun h => by cases h) (fun _ => hunsM hu_t) (fun h => by cases h) hmLL
            · clear hc; m6_jnz
              · -- `h->oom != 0`: return `3#64`
                have hoom_ne : oomM ≠ 0#64 := fun h0 => by
                  rw [h0] at hc; revert hc; decide
                m6_c0_steps
                exact hQ 3#64 vM fM lM rM tM tpM teM uM ufM wvM wsM arM dst.toNat wlM wuM frM
                  irred redd nbM oomM scLL mL hlenLL (Or.inr (Or.inr (Or.inr rfl))) helM hws2M
                  hll_wf hwLL hndLL (fun h => by rcases h with h | h <;> cases h)
                  (fun hpos => by
                    obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposM hpos
                    rw [hcoreM] at hv hl ht htp hte
                    exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
                  (fun h => by cases h) (fun h => by cases h) (fun _ => hoom_ne) hmLL
              · -- `h->oom == 0`: `full_rewatch_range_m6(h, start, dst)`
                have hoom0 : oomM = 0#64 :=
                  BitVec.eq_of_toNat_eq (by change sLL.core.oom.toNat = 0; c0_bound)
                m6_c0_steps; c0_call hrewatch_r
                refine fullRewatchRangeSpec.intro c F0 F_cur sLL R rfl hlenLL hst_dst hstLL_in
                  rfl hwLL hdm0 hnoLL hmLL
                  fun ok arR wvecR wstkR wlenR wuR oomR wsR mR hlenR hwR _ hndR hokt hokf hmR =>
                    ?_
                let scR : FullScratch := { scLL with wsort := wsR }
                have hll_wfR : FullLastLearnedWf
                    { sLL with
                      core := { sLL.core with arena := arR, wvec := wvecR, wstk := wstkR,
                                              wlen := wlenR, wusable := wuR, oom := oomR }
                      scratch := scR } :=
                  fullLastLearnedWf_of_all_sentinel (fun j hj => hallL j (by omega))
                m6_jnz
                · -- `ok = true`: return `new_unit ? 1#64 : 0#64`
                  have hok_t : ok = true := by simpa using hc
                  have hoomR0 : oomR = 0#64 := (hokt hok_t).trans hoom0
                  m6_to_group
                  refine wp_join_group (fun (r, ()) m' =>
                    mR = m' ∧ ((r = 1#64 ∧ new_unit = true) ∨
                      (r = 0#64 ∧ new_unit = false))) ?_ ?_
                  · rintro _ ⟨r, ⟨⟩⟩ _ ⟨rfl, hr⟩
                    m6_c0_steps
                    rcases hr with ⟨rfl, hnu_t⟩ | ⟨rfl, hnu_f⟩
                    · exact hQ 1#64 vM fM lM rM tM tpM teM uM ufM wvecR wstkR arR dst.toNat wlenR
                        wuR frM irred redd nbM oomR scR mR hlenR (Or.inr (Or.inl rfl)) helM
                        hws2M hll_wfR hwR (hndR hndLL) (fun _ => hoomR0)
                        (fun hpos => absurd (hposM hpos).2.1 (by simp [hnu_t]))
                        (fun _ => by
                          have h1 := hunitM hnu_t; rw [hcoreM] at h1; exact h1)
                        (fun h => by cases h) (fun h => by cases h) hmR
                    · exact hQ 0#64 vM fM lM rM tM tpM teM uM ufM wvecR wstkR arR dst.toNat wlenR
                        wuR frM irred redd nbM oomR scR mR hlenR (Or.inl rfl) helM
                        hws2M hll_wfR hwR (hndR hndLL) (fun _ => hoomR0)
                        (fun hpos => by
                          obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposM hpos
                          rw [hcoreM] at hv hl ht htp hte
                          exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
                        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hmR
                  · intro Jret hJret
                    m6_jnz
                    · m6_tiny_jump; exact hJret (1#64, ()) mR ⟨rfl, Or.inl ⟨rfl, by simpa using hc⟩⟩
                    · m6_c0_steps; exact hJret (0#64, ()) mR ⟨rfl, Or.inr ⟨rfl, by simpa using hc⟩⟩
                · -- `!ok`: return `3#64`
                  have hoomR1 : oomR = 1#64 := hokf (by cases ok <;> simp at hc ⊢)
                  m6_c0_steps
                  exact hQ 3#64 vM fM lM rM tM tpM teM uM ufM wvecR wstkR arR dst.toNat wlenR
                    wuR frM irred redd nbM oomR scR mR hlenR (Or.inr (Or.inr (Or.inr rfl))) helM
                    hws2M hll_wfR hwR (hndR hndLL)
                    (fun h => by rcases h with h | h <;> cases h)
                    (fun hpos => by
                      obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposM hpos
                      rw [hcoreM] at hv hl ht htp hte
                      exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
                    (fun h => by cases h) (fun h => by cases h) (fun _ => by simp [hoomR1]) hmR
      · -- Entry to `if (!unsat && h->oom == 0 && has_iar && first_red < dst)`
        intro JM hJM
        clear hrewatch_r hQ
        m6_to_group
        refine wp_join_group (fun () mJ => mJ = mE) ?_ ?_
        · -- `else` block (`Js_1`): `h->first_reducible = first_red`, optional `PH_RSN` clear
          rintro _ ⟨⟩ mJ rfl
          m6_to_group
          let sE1 : FullState := { sE with core := { sE.core with first_reducible := first_red } }
          refine wp_join_group (M6PostMoveInv c F0 F_cur s R start.toNat dst unsat new_unit)
            (fun _ ⟨⟩ m2 h2 => by m6_c0_steps; exact hJM () m2 h2) ?_
          intro J2 hJ2
          have hlikeE1 : M6PostLike s sE1 := by
            rcases hlikeE with ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, ar, wl, wu, nb, o, _, _, hEq⟩
            exact ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, ar, wl, wu, first_red, nb, o,
              by rw [show sE1.core = { sE.core with first_reducible := first_red } from rfl, hEq]⟩
          have hlenE1 : sE1.LengthsOk c :=
            ⟨{ hlenE.core_ok with arena_len_le := hlenE.core_ok.arena_len_le }, hlenE.scratch_ok⟩
          have hwE1 : FullWitnessInv c F0 F_cur { sE1.core with arena_len := dst.toNat } :=
            m6_trivial_post_witness hwEnd
          m6_jnz
          · -- `at_root = true`: jump directly to `J2`
            m6_c0_steps
            exact hJ2 () _ ⟨sE1, hlikeE1, hlenE1, hcvE, halE, hclE, hdmE, hftE, hfdE, hincE, helE,
              hws2E, hwE1, hcmpE.2.1, hcmpE.2.2, hstE_in, hunsatE, hunitE, hposE,
              fullMem_cast hm rfl⟩
          · -- `!at_root`: check `first_red < dst`
            have hpos : 0 < s.core.cur_level := by
              by_cases hcl0 : s.core.cur_level = 0
              · exact absurd (by simp [hcl0]) hc
              · exact Nat.pos_of_ne_zero hcl0
            m6_jnz
            · -- `first_red < dst`: clear `PH_RSN` in `[first_red, dst)`
              have hfr_lt_dst : first_red.toNat < dst.toNat := by c0_bound
              have hfr_ne : first_red ≠ 0xFFFFFFFF#64 := fun he => by
                rw [he] at hfr_lt_dst; simp at hfr_lt_dst; omega
              rcases hfrE with h_bad | ⟨hfr_st, _, hcmpE_fr, _, hmvE, hfr_inE, _⟩
              · exact absurd h_bad hfr_ne
              have hcmpE1 : CompactPrefixOk c F_cur s sE1.core dst.toNat :=
                (arenaPrefix_preserves_compact (k' := sE1.core) hcmpE rfl harE_len harE_len
                  (Nat.le_trans hdst_le hal_le) (fun _ _ => rfl)).1
              have hrmE1 : 0 < s.core.cur_level →
                  SweepReasonMapInv sPre.core sE1.core sPre.core.arena_len dst.toNat :=
                fun hp => hrmE hp
              have hfr_inE1 : first_red.toNat ∈
                  fullArenaClauseRefsCore { sE1.core with arena_len := dst.toNat } := hfr_inE
              refine wp_loop_inv
                (fun (cp, ()) => M6ClearFallInv c F_cur s sPre sE1 R first_red.toNat dst.toNat cp)
                (fun (cp, ()) _ => dst.toNat - cp.toNat) (fun Jf hLoopF => ?_) ?_
              · m6_c0_steps
                exact hLoopF (first_red, ()) _
                  ⟨Nat.le_refl _, Nat.le_of_lt hfr_lt_dst, sE.core.arena, rwE, harE_len,
                   fun _ _ => rfl, fun _ _ _ => rfl, hmvE, hcmpE1, hrmE1, rfl,
                   fun _ => hfr_inE1, fullMem_cast hm rfl⟩
              · rintro Jf ⟨cp, ⟨⟩⟩ mF
                  ⟨hfr_cp, hcp_le, arL, rwRem, harL_l, hpreL, htailL, hmvRem, hcmpL, hrmL,
                   hrefsL, hcp_in, hmF⟩
                  hLoopF
                m6_jnz
                · have hcp_lt : cp.toNat < dst.toNat := by c0_bound
                  generalize hcp_nat : cp.toNat = cpn at hmvRem
                  cases hmvRem with
                  | empty => omega
                  | @step _ _ rwTl hp3 hfl hsz hfit htl =>
                    rw [← hcp_nat] at hp3 hfl hsz hfit htl
                    have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
                    have hcp_lt_ar : cp.toNat < arL.length := by omega
                    have hcp2_lt_ar : (cp + 2#64).toNat < arL.length := by rw [hcp2_eq]; omega
                    let sF_ar : FullState := { sE1 with core := { sE1.core with arena := arL } }
                    have hmF' : (FullMem c sF_ar ⋆ R) mF := hmF
                    m6_tiny_lets
                    apply wp_load_of
                    · simp only [LeanQbe.T.Arg.val_var]
                      exact FullArenaTactics.c0_load_full_arena (s := sF_ar) hcp2_lt_ar hmF'
                    m6_tiny_lets
                    apply wp_load_of
                    · simp only [LeanQbe.T.Arg.val_var]
                      exact FullArenaTactics.c0_load_full_arena (s := sF_ar) hcp_lt_ar hmF'
                    m6_tiny_lets
                    try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                    apply wp_store_sep
                    · simp only [LeanQbe.T.Arg.val_var]
                      exact FullArenaTactics.c0_store_full_arena (s := sF_ar) _ hcp_lt_ar hmF'
                    intro mF2 hmF2
                    m6_tiny_lets
                    try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                    rw [wp_jump]
                    obtain ⟨hcp_nxt, hsz_eq, hinv'⟩ :=
                      m6_clear_fall_step rfl hfr_cp hcp_lt hal_le hdst_le harL_l hpreL htailL hp3
                        hfl hsz hfit htl (hcp_in hcp_lt) hcmpL hrmL hrefsL hmF2
                    exact hLoopF _ _
                      (by simp only [LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var]
                          dsimp only [sF_ar]
                          change dst.toNat -
                            (cp + 3#64 + (arL[(cp + 2#64).toNat]'hcp2_lt_ar).setWidth 64).toNat <
                            dst.toNat - cp.toNat
                          rw [hcp_nxt, hsz_eq]; omega) hinv'
                · have hcp_eq : cp.toNat = dst.toNat := by c0_bound
                  let sM : FullState :=
                    { sE1 with core := { sE1.core with arena := arL } }
                  let kM_dst : FullCoreState := { sM.core with arena_len := dst.toNat }
                  have hlikeM : M6PostLike s sM := by
                    rcases hlikeE with ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, _, wl, wu, nb, o,
                      _, _, hEq⟩
                    exact ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, arL, wl, wu, first_red, nb, o,
                      by rw [show sM.core = { sE.core with arena := arL,
                                                           first_reducible := first_red } from rfl,
                           hEq]⟩
                  have hlenM : sM.LengthsOk c :=
                    ⟨{ hlenE.core_ok with arena_len_arr := harL_l }, hlenE.scratch_ok⟩
                  have hcmpE_st_dst : CompactPrefixOk c F_cur s
                      { sE.core with arena_len := dst.toNat } start.toNat :=
                    (arenaPrefix_preserves_compact (k' := { sE.core with arena_len := dst.toNat })
                      hcmpE_st rfl harE_len harE_len (by omega) (fun _ _ => rfl)).1
                  obtain ⟨_, hkeep_st⟩ := m6_refs_lt_prefix_transfer
                    (k := { sE.core with arena_len := dst.toNat }) (k' := kM_dst) hcmpE_st_dst
                    rfl harE_len harL_l (by dsimp; omega) (by dsimp [kM_dst]; omega)
                    (by omega) (fun i hi => hpreL i (by omega))
                  have hltM : ∀ l < 2 * kM_dst.cur_vars,
                      WatchSliceLtOk start.toNat F_cur kM_dst l
                        (fullWatchOffCore kM_dst l) (fullWatchSizeCore kM_dst l) := fun l hl =>
                    (hltE l hl).relocate (k := sE.core) (k' := kM_dst)
                      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
                      (fun r hr hrlt =>
                        hkeep_st r (m6_refs_lt_compactPrefix hcmpE
                          (by rw [halE]; exact hdst_le) r hr (by omega)) hrlt)
                      (fun _ _ => rfl)
                  have hlayM : WatchStackLayout kM_dst := hlayE.with_wstk rfl rfl rfl rfl
                  obtain ⟨_, _, hvE, hlE, htE, htpE, hteE⟩ := hposE hpos
                  have hcoreM_ok : FullCoreState.LengthsOk c kM_dst :=
                    { hlenM.core_ok with arena_len_le := by dsimp [kM_dst]; omega }
                  have hwM : FullWitnessInv c F0 F_cur kM_dst :=
                    SweepReasonMapInv.toFullWitnessInvLt (c := c) (F0 := F0) (F_cur := F_cur)
                      (k0 := sPre.core) (kL := kM_dst) (keep := start.toNat) (dst := dst.toNat)
                      hcoreM_ok hwPre hcmpL.1 (fun _ => hdmE.trans hdm0) hlayM hltM
                      (fun _ hr _ => hr) hvE hlE htE htpE hteE hclE hcvE hftE hfdE hincE
                      (hrmL hpos)
                  have hstM_in : start.toNat < dst.toNat →
                      start.toNat ∈ fullArenaClauseRefsCore
                        { sM.core with arena_len := dst.toNat } := fun hlt => by
                    change start.toNat ∈
                      fullArenaClauseRefsCore { sE1.core with arena := arL, arena_len := dst.toNat }
                    rw [hrefsL]; exact hstE_in hlt
                  m6_c0_steps
                  exact hJ2 () _ ⟨sM, hlikeM, hlenM, hcvE, halE, hclE, hdmE, hftE, hfdE, hincE,
                    helE, hws2E, hwM, hcmpL.2.1, hcmpL.2.2, hstM_in, hunsatE, hunitE, hposE, hmF⟩
            · -- `¬ (first_red < dst)`: jump directly to `J2`
              m6_c0_steps
              exact hJ2 () _ ⟨sE1, hlikeE1, hlenE1, hcvE, halE, hclE, hdmE, hftE, hfdE, hincE, helE,
                hws2E, hwE1, hcmpE.2.1, hcmpE.2.2, hstE_in, hunsatE, hunitE, hposE,
                fullMem_cast hm rfl⟩
        · -- `&&` chain for `(!unsat && h->oom == 0 && has_irred_after_red && first_red < dst)`
          intro Jelse hJelse
          m6_jnz
          · m6_c0_steps; exact hJelse () mE rfl
          · m6_jnz
            · m6_jnz
              · m6_jnz
                · -- Enter `full_move_red_end_m6(h, first_red, dst)`
                  have hns : unsat = false := by
                    cases unsat
                    · rfl
                    · simp at hc
                  have hoomE0 : sE.core.oom = 0#64 :=
                    BitVec.eq_of_toNat_eq (by change sE.core.oom.toNat = 0; c0_bound)
                  have hia_t : has_iar = true := by c0_bound
                  have hfr_lt_dst : first_red.toNat < dst.toNat := by c0_bound
                  have hfr_ne : first_red ≠ 0xFFFFFFFF#64 := fun he => by
                    rw [he] at hfr_lt_dst; simp at hfr_lt_dst; omega
                  rcases hfrE with h_bad |
                    ⟨hfr_st, _, hcmpE_fr, hrw_pos, hmvE, hfr_inE, hrs_mk⟩
                  · exact absurd h_bad hfr_ne
                  have huniqE : MoveRedRsnUnique sE.core.arena sE.core.vals sE.core.rsns
                      sE.core.cur_vars first_red.toNat dst.toNat :=
                    (moveRedRsnUnique_of_witness hwEnd (by omega)).cast_ar
                  m6_c0_steps; c0_call hmovered
                  refine fullMoveRedEndSpec.intro c sE rwE R rfl hlenE hfr_lt_dst
                    (Nat.le_trans hdst_le hal_le) hrw_pos hmvE hwEnd.vals_domain huniqE hmE
                    fun arM rsnsM fred' sc' rwOut mM harM_l hrsnsM_l hscM_ok helM hws2M hpreM hmvM
                      hblkM hrsnsM hmM => ?_
                  m6_c0_steps
                  exact hJM () mM (m6_move_red_post hwPre rfl hwEnd hnd0 hal_le hdst_le hdm0
                    hfr_lt_dst (by omega)
                    hlikeE hlenE hcvE halE hclE hdmE hftE hfdE hincE helE hws2E harE_len
                    hcmpE hcmpE_st hcmpE_fr hrw_pos hmvE hfr_inE hrs_mk hlayE hltE hstE_in hrmE
                    hunsatE hunitE hposE harM_l hrsnsM_l hscM_ok helM hws2M hpreM hmvM
                    (fun r hr => let ⟨h0, src0, hs0, hsz0, hl0⟩ := hblkM r hr
                      ⟨h0, src0, hs0, hsz0.symm, fun j hj => hl0 j (hsz0 ▸ hj)⟩)
                    hrsnsM hmM)
                · m6_tiny_jump; exact hJelse () mE rfl
              · m6_tiny_jump; exact hJelse () mE rfl
            · m6_c0_steps; exact hJelse () mE rfl
    · -- Entry to main compaction loop (`while (src < alen)`)
      intro JE hJE
      clear hrewatch_r hQ hmovered
      refine wp_loop_inv
        (fun (src, dst, first_red, _ir, _rd, has_iar, new_unit, ()) =>
          M6SweepLoopInv c F0 F_cur s sPre R start.toNat src dst first_red has_iar new_unit)
        (fun (src, _, _, _, _, _, _, ()) _ => s.core.arena_len - src.toNat)
        (fun JL hLoopL => ?_) ?_
      · m6_c0_steps
        refine hLoopL (start, start, 0xFFFFFFFF#64, pre_irred, 0#64, false, false, ()) m0
          ⟨Nat.le_refl _, Nat.le_refl _, hstart_le, hst_mem, fun h => Bool.noConfusion h,
           s0, 0, hlike0, hlen0, hcmp0, hcmp0, hlay0, hlt0, fun hlt => absurd hlt (by omega),
           .inl rfl, fun _ _ _ => rfl, ⟨fun hcl0 => ?_⟩, ⟨fun hpos => ?_⟩, hm0⟩
        · have hst0 : start.toNat = 0 := Classical.byContradiction fun hne => by
            have := (hstart_pos (Nat.pos_of_ne_zero hne)).1; omega
          have hst_bv0 : start = 0#64 := BitVec.eq_of_toNat_eq hst0
          refine ⟨hst0, ?_, Nat.le_refl _, fun h => Bool.noConfusion h⟩
          have hw_zero := fullWitnessInv_arena_len_zero hw0
            ⟨hlay0, fun l hl => by
              have h1 := hlt0 l hl; rw [hst0] at h1; exact h1.toBinOnly⟩ hcl0
          simpa only [hst0] using hw_zero
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrm0⟩
      · rintro JL ⟨src, dst, first_red, irred, redd, has_iar, new_unit, ⟨⟩⟩ mL
          ⟨hst_dst, hdst_src, hsrc_le, hsrc_mem, hhas_iar, sL, rwL, hlikeL, hlenL,
           hcmpL, hcmpL_st, hlayL, hltL, hstL_in, hfrL, htailL, hrootL, hposL, hmL⟩ hLoopL
        obtain ⟨hcvL, halL, hclL, hdmL, hftL, hfdL, hincL, helL, hws2L⟩ := hlikeL.unchanged
        have harL_len : sL.core.arena.length = c.arena_cap := hlenL.core_ok.arena_len_arr
        m6_jnz
        · -- `src < alen`
          have hsrc_lt : src.toNat < s.core.arena_len := by c0_bound
          have hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre := hsrc_mem hsrc_lt
          have hwf0 := hwPre.arena.refs_wf src.toNat hsrc_ref
          have hsrc3_le : src.toNat + 3 ≤ s.core.arena_len := by
            change src.toNat + 3 ≤ sPre.core.arena_len; exact hwf0.1
          have hsrc_lt8 : src.toNat < 0x80000000 := by omega
          m6_split
          · have hs2_eq : (src + (2 : BitVec 64)).toNat = src.toNat + 2 := bv64_add2_lt (by omega)
            have hs0_lt : src.toNat < sL.core.arena.length := by omega
            have hs2_lt : (src + (2 : BitVec 64)).toNat < sL.core.arena.length := by omega
            have hhdr_orig :
                sL.core.arena[src.toNat]'hs0_lt = fullArenaHdrCore sPre.core src.toNat := by
              have h1 := htailL src.toNat (Nat.le_refl _) hsrc_lt
              unfold fullArenaHdrCore
              rw [← h1, List.getElem?_eq_getElem hs0_lt, Option.getD_some]
            have hsz_orig : (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat =
                fullArenaClauseSizeCore sPre.core src.toNat := by
              have h1 := htailL (src.toNat + 2) (by omega) (by omega)
              unfold fullArenaClauseSizeCore
              rw [← h1, List.getElem?_eq_getElem (by omega : src.toNat + 2 < sL.core.arena.length),
                Option.getD_some]
              simp only [hs2_eq]
            have hsrc32 : (src.setWidth 32).toNat = src.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            have hnxt_eq : fullArenaNextOff sL.core.arena s.core.arena_len src.toNat =
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat :=
              fullArenaNextOff_congr_block (htailL src.toNat (Nat.le_refl _) hsrc_lt)
                (htailL (src.toNat + 2) (by omega) (by omega))
                (fun k hk1 hk2 => htailL k (by omega)
                  (Nat.lt_of_lt_of_le hk2
                    (fullArenaNextOff_bounds (ar := sPre.core.arena) hwf0.1).2))
            have hnxt_bd := fullArenaNextOff_bounds hwf0.1 (ar := sPre.core.arena)
            have hnxt_le_al : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ≤
                s.core.arena_len := hwf0.2.2.2.1
            have hnxt_mem : fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat =
                s.core.arena_len ∨
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat ∈
                  fullArenaClauseRefs sPre :=
              fullArenaClauseRefs_next_or_end hwPre.arena hsrc_ref
            m6_c0_steps; c0_call hnext
            refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
            let nsrc32 := BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
              (src.setWidth 32).toNat)
            have hnsrc64 : (nsrc32.setWidth 64).toNat =
                fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat := by
              rw [zext_toNat nsrc32 (by decide)]
              dsimp only [nsrc32]; rw [halL, hsrc32, hnxt_eq]
              have hal_pre : sPre.core.arena_len = s.core.arena_len := rfl
              exact bv32_ofNat_toNat (by omega)
            have hnsrc_gt : src.toNat < (nsrc32.setWidth 64).toNat := by
              have h1 := hnxt_bd.1; rw [hnsrc64]; omega
            have hdec_m :
                s.core.arena_len - (nsrc32.setWidth 64).toNat < s.core.arena_len - src.toNat := by
              omega
            have hskip_go : (fullArenaClauseGarbCore sPre.core src.toNat = true ∨
                fullArenaClauseSizeCore sPre.core src.toNat < 3 ∨
                sPre.core.arena_len <
                  src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat) →
                JL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar, new_unit, ()) mL :=
              fun hsk => by
                refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar,
                    new_unit, ()) mL hdec_m
                  ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                   hhas_iar, sL, rwL, hlikeL, hlenL, hcmpL, hcmpL_st, hlayL, hltL, hstL_in, hfrL,
                   fun i hi1 hi2 => htailL i (by omega) hi2, hrootL, ⟨fun hpos => ?_⟩, hmL⟩
                · rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                · obtain ⟨hnu, hv, hl, ht, htp, hte, hrmL⟩ := hposL.get hpos
                  exact ⟨hnu, hv, hl, ht, htp, hte, hrmL.skip hwPre hsrc_ref hnsrc64 hsk⟩
            -- Check skip conditions
            m6_jnz
            · m6_c0_steps; exact hskip_go (Or.inl (by
                unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc))
            · have hng_src : fullArenaClauseGarbCore sPre.core src.toNat = false := by
                unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc
              have hsz3_pre :
                  3 ≤ (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat := by
                rw [hsz_orig]; exact hwf0.2.1
              have hfit_pre : src.toNat + 3 +
                  (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                  sPre.core.arena_len := by
                rw [hsz_orig]
                have h1 := hwf0.2.2.1; have h2 := hwf0.2.2.2.1; omega
              clear hskip_go
              have hsz3 : 3 ≤ (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat :=
                hsz3_pre
              have hsrc_fit : src.toNat + 3 +
                  (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                  s.core.arena_len := hfit_pre
              have hsrc_lits_eq :
                  ((sL.core.arena.drop (src.toNat + 3)).take
                    (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat).map
                    BitVec.toNat = fullArenaClauseLitsCore sPre.core src.toNat := by
                rw [hsz_orig]; unfold fullArenaClauseLitsCore; congr 1
                apply List.ext_getElem (by simp [harL_len, harPre_len])
                intro j hj1 _
                have hj : j < fullArenaClauseSizeCore sPre.core src.toNat := by
                  simp at hj1; omega
                simp only [List.getElem_take, List.getElem_drop]
                have h1 := htailL (src.toNat + 3 + j) (by omega) (by omega)
                rw [List.getElem?_eq_getElem
                      (by omega : src.toNat + 3 + j < sL.core.arena.length),
                    List.getElem?_eq_getElem
                      (by omega : src.toNat + 3 + j < sPre.core.arena.length)] at h1
                exact Option.some.inj h1
              have hlits_lt_src : ∀ j <
                    (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat,
                  (sL.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * sL.core.cur_vars :=
                fun j hj => by
                  rw [hcvL, htailL (src.toNat + 3 + j) (by omega) (by omega)]
                  have hbd : src.toNat + 3 + fullArenaClauseSizeCore sPre.core src.toNat ≤
                      sPre.core.arena.length := by
                    change _ ≤ arPre.length
                    rw [show arPre.length = c.arena_cap from harPre_len]
                    exact Nat.le_trans (by rw [← hsz_orig]; exact hfit_pre) hal_le
                  have hj' : j < fullArenaClauseSizeCore sPre.core src.toNat := by omega
                  have hmem : (sPre.core.arena[src.toNat + 3 + j]'(by omega)).toNat ∈
                      fullArenaClauseLitsCore sPre.core src.toNat :=
                    (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj', rfl⟩
                  have hlt_j := hwPre.arena.lits_lt src.toNat hsrc_ref hng_src _ hmem
                  rwa [List.getElem?_eq_getElem
                      (by omega : src.toNat + 3 + j < sPre.core.arena.length),
                    Option.getD_some]
              -- Call `full_sweep_copy(h, src, dst, old_sz, at_root)`
              m6_c0_steps; c0_call hcopy
              refine ⟨c, F0, F_cur, sL, R, rfl, hlenL, hdst_src, hsz3, by omega, ?_,
                hlits_lt_src, fun hrt => ?_, hmL,
                fun st arC valsC flagsC lvlC rsnsC trlC tpC teC unassC unflC wvecC wstkC
                  wlenC wuC nbC oomC phC wsC mC hlenC0 houtC0 hout_f hout_t hmC0 => ?_⟩
              · rw [hclL, hcl_beq]
              · have hcl0 : s.core.cur_level = 0 := (hdec_cl0 true).mp hrt
                have hrtL := hrootL.get hcl0
                have hbinL : BinOnlyWatchesInv F_cur sL.core :=
                  ⟨hlayL, fun l hl => by
                    have h1 := hltL l (hcvL ▸ hl); rw [hrtL.1] at h1; exact h1.toBinOnly⟩
                exact ⟨hrtL.2.1, hbinL.toFull,
                  by rw [hsrc_lits_eq]; exact hwPre.arena.entails src.toNat hsrc_ref hng_src⟩
              have hout_ok0 :
                  fullSweepCopyOutcome c F0 F_cur sL
                    { core := { sL.core with arena := arC, vals := valsC, flags := flagsC,
                                             lvl := lvlC, rsns := rsnsC, trl := trlC,
                                             trail_pos := tpC, trail_end := teC,
                                             unassigned := unassC, unflushed := unflC,
                                             wvec := wvecC, wstk := wstkC, wlen := wlenC,
                                             wusable := wuC, num_binary := nbC, oom := oomC }
                      scratch := { sL.scratch with phases := phC, wsort := wsC } }
                    src dst (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt)
                    (BitVec.ofNat 64 s.core.cur_level == 0) st :=
                ⟨hout_f, fun hrt => by
                  obtain ⟨h1, hbin, hrest⟩ := hout_t hrt
                  have hwlenC :
                      ({ sL.core with wlen := wlenC, wstk := wstkC } : FullCoreState).wlen ≤
                      wstkC.length := by
                    have hwl := hlenC0.core_ok.wlen_le
                    have hws := hlenC0.core_ok.wstk_len_arr
                    dsimp only at hwl hws ⊢; omega
                  exact ⟨h1, m6_binOnly_of_full hwlenC hbin, hrest⟩⟩
              let sC : FullState :=
                { core := { sL.core with arena := arC, vals := valsC, flags := flagsC,
                                         lvl := lvlC, rsns := rsnsC, trl := trlC, trail_pos := tpC,
                                         trail_end := teC, unassigned := unassC, unflushed := unflC,
                                         wvec := wvecC, wstk := wstkC, wlen := wlenC,
                                         wusable := wuC, num_binary := nbC, oom := oomC }
                  scratch := { sL.scratch with phases := phC, wsort := wsC } }
              have hdst_fit_pre : dst.toNat + 3 +
                  (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤ c.arena_cap :=
                by omega
              have hlikeC : M6SweepLike s sC := hlikeL.of_copy
              have harC_len : sC.core.arena.length = c.arena_cap := hlenC0.core_ok.arena_len_arr
              have hpreC : PrefixAgrees dst.toNat sL.core.arena sC.core.arena := fun idx hidx =>
                houtC0 idx (Or.inl (by omega))
              have htailC : ∀ i, (nsrc32.setWidth 64).toNat ≤ i → i < s.core.arena_len →
                  sC.core.arena[i]? = sPre.core.arena[i]? := fun i hi1 hi2 => by
                have hfit_n : src.toNat + 3 +
                    (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                    (nsrc32.setWidth 64).toNat := by
                  rw [hnsrc64, hsz_orig]; exact hwf0.2.2.1
                have hi_ge : dst.toNat + 3 +
                    (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤ i :=
                  Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hdst_src 3) _)
                    (Nat.le_trans hfit_n hi1)
                rw [houtC0 i (Or.inr hi_ge)]
                exact htailL i (by omega) hi2
              obtain ⟨hcvC, halC, _⟩ := hlikeC.unchanged
              obtain ⟨hcmpC, hcongrC⟩ := arenaPrefix_preserves_compact
                (s := s) (k := sL.core) (k' := sC.core) hcmpL
                (hcvC.trans hcvL.symm) harL_len harC_len (by omega) hpreC
              obtain ⟨hcmpC_st, hkeepC_st⟩ := m6_refs_lt_prefix_transfer hcmpL_st
                (hcvC.trans hcvL.symm) harL_len harC_len (by omega) (by rw [halC]; omega)
                (by omega) (fun i hi => hpreC i (by omega))
              have hcl0_of_special :
                  st = 0xFFFFFFFE#64 ∨ st = 0xFFFFFFFD#64 ∨ st = 1#64 ∨ st = 0xFFFFFFFF#64 →
                  s.core.cur_level = 0 := fun hsp => Classical.byContradiction fun hne => by
                have hst_old := (hout_ok0.1 ((hdec_cl0 false).mpr (Nat.pos_of_ne_zero hne))).1
                have hst_lt : st.toNat < 2 * 2 ^ 28 := by
                  rw [hst_old, zext_toNat _ (by decide)]; omega
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
                · refine .inr ⟨h1, h2, ?_, hrw0, ?_, ?_, ⟨?_⟩⟩
                  · exact (arenaPrefix_preserves_compact hcmpL_fr
                      (hcvC.trans hcvL.symm) harL_len harC_len (by omega)
                      (fun i hi => hpreC i (by omega))).1
                  · exact hmvL.congr (fun i _ hi => hpreC i (by omega))
                  · have hcon := (arenaPrefix_preserves_compact hcmpL
                      (hcvC.trans hcvL.symm) harL_len harC_len (by omega) hpreC).2
                    rw [hcon.1]; exact hfr_inL
                  · intro hp r hr idx hidx heq
                    obtain ⟨-, -, -, -, hrC, -, -, -, -, -, -, -, -, -, -, -, -, _, _⟩ :=
                      hout_ok0.1 ((hdec_cl0 false).mpr hp)
                    have hr' := hr.congr (fun i _ hi => (hpreC i (by omega)).symm)
                    obtain ⟨ha, j, hj, hb, hc⟩ :=
                      hrm_mk.get hp r hr' idx hidx (by rw [← hrC]; exact heq)
                    have hrb := hr'.bounds
                    refine ⟨by rw [hpreC r (by omega)]; exact ha,
                      j, by rw [hpreC (r + 2) (by omega)]; exact hj, ?_⟩
                    obtain ⟨-, hvC, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
                      hout_ok0.1 ((hdec_cl0 false).mpr hp)
                    rw [hpreC (r + 3 + j) (by omega), hvC]; exact ⟨hb, hc⟩
              have hstC_in : start.toNat < dst.toNat →
                  start.toNat ∈ fullArenaClauseRefsCore { sC.core with arena_len := dst.toNat } :=
                fun hlt => by rw [hcongrC.1]; exact hstL_in hlt
              m6_tiny_lets; apply wp_jnz_of
              · -- `st == 0xFFFFFFFE`: UNSAT
                intro hc; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc
                have hcl0 := hcl0_of_special (Or.inl hc)
                obtain ⟨hwC, _, hteC, _, hunsC, _, _, _, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                dsimp only [sC] at hteC
                have hst0 : start.toNat = 0 := (hrootL.get hcl0).1
                have hlayC : WatchStackLayout sC.core := by
                  obtain ⟨_, hbinC, _, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                  exact hbinC.1
                have hltC : ∀ l < 2 * sC.core.cur_vars,
                    WatchSliceLtOk start.toNat F_cur sC.core l
                      (fullWatchOff sC l) (fullWatchSize sC l) := fun l hl => by
                  obtain ⟨_, hbinC, _, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                  rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC.slices l hl)
                rw [wp_jump]
                exact hJE (src, dst, first_red, irred, redd, has_iar, true, new_unit, ()) mC
                  ⟨hst_dst, by omega, hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st,
                   hlayC, hltC, hstC_in, hwC, hfr_to_C, fun hp => absurd hcl0 (by omega),
                   fun _ => ⟨hcl0, hunsC hc⟩,
                   fun hnu => ⟨hcl0, by
                     change s.core.trail_end < teC
                     have := (hrootL.get hcl0).2.2.2 hnu; omega⟩,
                   fun hpos => absurd hcl0 (by omega), hmC0⟩
              · intro hc; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc
                m6_tiny_lets; apply wp_jnz_of
                · -- `st == 0xFFFFFFFD`: OOM
                  intro hc1; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc1
                  have hcl0 := hcl0_of_special (Or.inr (Or.inl hc1))
                  obtain ⟨hwC, hbinC, hteC, _, _, _, _, _, _⟩ :=
                    hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                  dsimp only [sC] at hteC
                  have hst0 : start.toNat = 0 := (hrootL.get hcl0).1
                  have hltC : ∀ l < 2 * sC.core.cur_vars,
                      WatchSliceLtOk start.toNat F_cur sC.core l
                        (fullWatchOff sC l) (fullWatchSize sC l) := fun l hl => by
                    rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC.slices l hl)
                  rw [wp_jump]
                  exact hJE (src, dst, first_red, irred, redd, has_iar, false, new_unit, ()) mC
                    ⟨hst_dst, by omega, hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st,
                     hbinC.1, hltC, hstC_in, hwC, hfr_to_C, fun hp => absurd hcl0 (by omega),
                     fun h => Bool.noConfusion h,
                     fun hnu => ⟨hcl0, by
                       change s.core.trail_end < teC
                       have := (hrootL.get hcl0).2.2.2 hnu; omega⟩,
                     fun hpos => absurd hcl0 (by omega), hmC0⟩
                · intro hc1; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc1
                  m6_tiny_lets; apply wp_jnz_of
                  · -- `st == 1`: new unit
                    intro hc2; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc2
                    have hcl0 := hcl0_of_special (Or.inr (Or.inr (Or.inl hc2)))
                    obtain ⟨hwC, hbinC, hteC, _, _, _, _, hunitC, _⟩ :=
                      hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                    dsimp only [sC] at hteC hunitC
                    have hst0 : start.toNat = 0 := (hrootL.get hcl0).1
                    have hltC : ∀ l < 2 * sC.core.cur_vars,
                        WatchSliceLtOk start.toNat F_cur sC.core l
                          (fullWatchOff sC l) (fullWatchSize sC l) := fun l hl => by
                      rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC.slices l hl)
                    rw [wp_jump]
                    refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar,
                        true, ()) mC hdec_m
                      ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                       hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st, hbinC.1, hltC,
                       hstC_in, hfr_to_C, htailC, ⟨fun _ => ⟨hst0, hwC,
                         by change s.core.trail_end ≤ teC; have := (hrootL.get hcl0).2.2.1; omega,
                         fun _ => by
                           change s.core.trail_end < teC
                           have := (hrootL.get hcl0).2.2.1; have := hunitC hc2; omega⟩⟩,
                       ⟨fun hp => absurd hcl0 (by omega)⟩, hmC0⟩
                    rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                  · intro hc2; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc2
                    m6_tiny_lets; apply wp_jnz_of
                    · -- `st == 0xFFFFFFFF`: sat or binary
                      intro hc3; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc3
                      have hcl0 := hcl0_of_special (Or.inr (Or.inr (Or.inr hc3)))
                      obtain ⟨hwC, hbinC, hteC, _, _, _, _, _, _⟩ :=
                        hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
                      dsimp only [sC] at hteC
                      have hst0 : start.toNat = 0 := (hrootL.get hcl0).1
                      have hltC : ∀ l < 2 * sC.core.cur_vars,
                          WatchSliceLtOk start.toNat F_cur sC.core l
                            (fullWatchOff sC l) (fullWatchSize sC l) := fun l hl => by
                        rw [hst0]; exact WatchSliceLtOk.ofBinOnly (hbinC.slices l hl)
                      rw [wp_jump]
                      refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, has_iar,
                          new_unit, ()) mC hdec_m
                        ⟨hst_dst, by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                         hhas_iar, sC, rwL, hlikeC, hlenC0, hcmpC, hcmpC_st, hbinC.1, hltC,
                         hstC_in, hfr_to_C, htailC, ⟨fun _ => ⟨hst0, hwC,
                           by change s.core.trail_end ≤ teC; have := (hrootL.get hcl0).2.2.1; omega,
                           fun hnu => by
                             change s.core.trail_end < teC
                             have := (hrootL.get hcl0).2.2.2 hnu; omega⟩⟩,
                         ⟨fun hp => absurd hcl0 (by omega)⟩, hmC0⟩
                      rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                    · intro hc3
                      simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc3
                      -- Live compacted block: `3 ≤ new_sz ≤ old_sz`
                      clear hcl0_of_special hJE JE hcmpL htailL
                      obtain ⟨hnew3, hnew_le, hnew_lt, hnew_sub, hnew_ent, hlayC, hltC⟩ :=
                        m6_sweep_copy_new_props hwPre (fun h => (hrootL.get h).1) hltL hlayL
                          (fun _ => hkeepC_st) hout_ok0 hdec_cl0 hcvL
                          (hcvC.trans hcvL.symm) hsz3 harL_len harC_len (by omega)
                          hdst_src hsrc_ref hng_src hsrc_lits_eq
                          (fun j hj => hcvL ▸ hlits_lt_src j hj)
                          (by assumption) (by assumption) (by assumption) (by assumption)
                      clear hsz3 hsrc_fit hlits_lt_src hnext hcopy hcl_beq
                      have hnsz32_eq : (st.setWidth 32).toNat = st.toNat := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      have hd1_eq : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1 :=
                        bv64_add1_lt (by omega)
                      have hd2_eq : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2 :=
                        bv64_add2_lt (by omega)
                      have harC_l' : arC.length = c.arena_cap := harC_len
                      have hdar3 : dst.toNat + 3 ≤ arC.length := by omega
                      m6_unmdata
                      try c0_let_simp
                      apply wp_store_sep
                      · simp only [LeanQbe.T.Arg.val_var]
                        exact FullArenaTactics.c0_store_full_arena _
                          (by show dst.toNat < arC.length; omega) hmC0
                      intro m1 hm1; clear hmC0
                      m6_tiny_lets
                      apply wp_store_sep
                      · simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                        exact FullArenaTactics.c0_store_full_arena _
                          (by simp only [List.length_set, hd1_eq]; omega) hm1
                      intro m2 hm2; clear hm1
                      m6_tiny_lets
                      apply wp_store_sep
                      · simp only [LeanQbe.T.Arg.val_var]
                        exact FullArenaTactics.c0_store_full_arena _
                          (by simp only [List.length_set, hd2_eq]; omega) hm2
                      intro m hm; clear hm2
                      m6_tiny_lets
                      let hdr0 := sL.core.arena[src.toNat]'hs0_lt
                      have hst32_of : st.setWidth 32 = BitVec.ofNat 32 st.toNat := by
                        apply BitVec.eq_of_toNat_eq
                        rw [hnsz32_eq, bv32_ofNat_toNat (by omega)]
                      obtain ⟨arH, harH_len, hpreH, hbodyH, harH_0, hszH, hdropH, hcmpH, hdst_inH,
                          happend_mk, hm_arH⟩ :=
                        m6_write_hdr_wrap hcmpC hcongrC (by rw [hcvC]) hnew3 harC_len
                          (by omega) hd1_eq hd2_eq (bv32_ofNat_toNat (by omega)) hsrc_ref hng_src
                          hhdr_orig (fun _ => hndPre) hnew_lt hnew_sub hnew_ent
                          (fullMem_cast hm (by simp only [hst32_of]; congr 1))
                      clear hm hcongrC
                      have hdst_next_eq :
                          (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64).toNat =
                          dst.toNat + 3 + st.toNat := by
                        rw [BitVec.toNat_add, BitVec.toNat_add,
                          zext_toNat (st.setWidth 32) (by decide), hnsz32_eq]
                        simp; omega
                      let mark_allowed : Bool :=
                        !(decide (s.core.cur_level = 0)) &&
                        (decide (first_red ≠ 0xFFFFFFFF#64) ||
                         decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))
                      m6_to_group
                      refine wp_join_group (M6RsnBranchInv c F_cur s sPre sC R arH
                        (nsrc32.setWidth 64).toNat dst.toNat st.toNat mark_allowed) ?_ ?_
                      · -- After `PH_RSN`: update `first_red`/`redd`/`irred`/`has_iar`
                        rintro _ ⟨⟩ mR ⟨arR, rsnsR, harR_len, hrsnsR_len, hpreR, hbodyR, hszR,
                            hflR, hredR, hcmpR, hdst_inR, hrsns_lt_dst, hrsns_r0, hrmR, hmkR, hmR⟩
                        let hstep_next : ∀ fr' ir' rd' hia',
                            (fr' = 0xFFFFFFFF#64 → first_red = 0xFFFFFFFF#64 ∧
                              (hdr0 &&& 0x00400000#32) = 0#32) →
                            (fr' ≠ 0xFFFFFFFF#64 →
                              (first_red = 0xFFFFFFFF#64 →
                                fr' = dst ∧ (hdr0 &&& 0x00400000#32) ≠ 0#32) ∧
                              (first_red ≠ 0xFFFFFFFF#64 → fr' = first_red)) →
                            (hia' = true → fr' ≠ 0xFFFFFFFF#64) →
                            JL (nsrc32.setWidth 64,
                                dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64,
                                fr', ir', rd', hia', new_unit, ()) mR :=
                          fun fr' ir' rd' hia' hfr_nil hfr_some hhia =>
                            hLoopL _ mR hdec_m (m6_rsn_post_step hwPre hst_dst hdst_src hal_le
                              hdst_next_eq hnew3
                              (by rw [hnsrc64]; have h1 := hwf0.2.2.1
                                  rw [← hsz_orig] at h1; omega)
                              (by rw [hnsrc64]; exact hnxt_le_al)
                              (by rw [hnsrc64]; exact hnxt_mem)
                              hlikeC hlenC0 hcvL rfl harC_len hcmpC hcmpC_st hlayC hltC
                              hstC_in hfr_to_C
                              htailC hrootL hposL hdec_cl0 hout_ok0 hpreH hbodyH harH_0 hhdr_orig
                              hng_src harR_len hrsnsR_len hpreR hbodyR hszR hflR hredR hcmpR
                              hdst_inR hrsns_lt_dst hrsns_r0 hrmR hmkR hmR rfl hfr_nil hfr_some
                              hhia)
                        -- Post-RsnBranch: `if ((hdr & PH_RED) != 0) ... else ...`
                        refine wp_unroll_group fun Js hJs => ?_
                        try c0_let_simp
                        apply wp_jnz_of
                        · intro hc_red
                          simp only [LeanQbe.T.Arg.val_var] at hc_red
                          c0_cond hc_red
                          try c0_let_simp
                          refine wp_unroll_group fun Js1 hJs1 => ?_
                          try c0_let_simp
                          apply wp_jnz_of
                          · intro hc_feq
                            simp only [LeanQbe.T.Arg.val_var] at hc_feq
                            c0_cond hc_feq
                            m6_tiny_jump; apply hJs1; m6_tiny_jump
                            apply hJs; m6_tiny_jump
                            exact hstep_next dst irred (redd + 1#64) has_iar
                              (fun h => by
                                have h1 := congrArg BitVec.toNat h
                                simp at h1; omega)
                              (fun _ => ⟨fun _ => ⟨rfl, by simpa using hc_red⟩,
                                fun h => absurd hc_feq h⟩)
                              (fun h => absurd hc_feq (hhas_iar h))
                          · intro hc_fne
                            simp only [LeanQbe.T.Arg.val_var] at hc_fne
                            c0_cond hc_fne
                            m6_tiny_jump; apply hJs1; m6_tiny_jump
                            apply hJs; m6_tiny_jump
                            exact hstep_next first_red irred (redd + 1#64) has_iar
                              (fun h => absurd h hc_fne)
                              (fun _ => ⟨fun h => absurd h hc_fne, fun _ => rfl⟩)
                              hhas_iar
                        · intro hc_nred
                          simp only [LeanQbe.T.Arg.val_var] at hc_nred
                          c0_cond hc_nred
                          try c0_let_simp
                          refine wp_unroll_group fun Js2 hJs2 => ?_
                          try c0_let_simp
                          apply wp_jnz_of
                          · intro hc_fne
                            simp only [LeanQbe.T.Arg.val_var] at hc_fne
                            c0_cond hc_fne
                            m6_tiny_jump; apply hJs2; m6_tiny_jump
                            apply hJs; m6_tiny_jump
                            exact hstep_next first_red (irred + 1#64) redd true
                              (fun h => absurd h hc_fne)
                              (fun _ => ⟨fun h => absurd h hc_fne, fun _ => rfl⟩)
                              (fun _ => hc_fne)
                          · intro hc_feq
                            simp only [LeanQbe.T.Arg.val_var] at hc_feq
                            c0_cond hc_feq
                            m6_tiny_jump; apply hJs2; m6_tiny_jump
                            apply hJs; m6_tiny_jump
                            exact hstep_next first_red (irred + 1#64) redd has_iar
                              (fun _ => ⟨hc_feq, by simpa [bne_iff_ne] using hc_nred⟩)
                              (fun h => absurd hc_feq h)
                              hhas_iar
                      · -- Entry to `if ((hdr & PH_RSN) != 0)`
                        intro JR hJR
                        clear hLoopL JL hcmpC hcmpC_st htailC hrootL hnxt_le_al hnxt_mem
                          hdst_next_eq hdec_m hnxt_bd hsz3_pre hfit_pre hstC_in hstL_in
                        m6_tiny_lets; apply wp_jnz_of
                        · -- `(hdr & PH_RSN) != 0`
                          intro _
                          m6_to_group
                          refine wp_join_group (fun (_ : Tup Val [i32]) =>
                              M6RsnBranchInv c F_cur s sPre sC R arH
                                (nsrc32.setWidth 64).toNat dst.toNat st.toNat mark_allowed ())
                            ?_ ?_
                          · rintro _ ⟨_iB, ⟨⟩⟩ mB hB; (first | rw [wp_jump] | m6_c0_steps)
                            exact hJR () mB hB
                          · intro Jbrk hJbrk
                            refine wp_loop_inv
                              (M6RsnLoopInv s sC arH src.toNat dst.toNat st.toNat m)
                              (fun (i, ()) _ => st.toNat - i.toNat) (fun Ji hLoopI => ?_) ?_
                            · m6_c0_steps; exact hLoopI (0#32, ()) m ⟨rfl, Nat.zero_le _,
                                fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
                            · rintro Ji ⟨i, ⟨⟩⟩ mI ⟨hmI, hi_le, hmissI⟩ hLoopI
                              subst mI
                              m6_jnz
                              · have hi_lt : i.toNat < st.toNat := by
                                  have : i.toNat < (st.setWidth 32).toNat := by c0_bound
                                  omega
                                have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
                                  bv32_add1 (by omega)
                                have hdi_eq : (dst + (3 : BitVec 64) + i.setWidth 64).toNat =
                                    dst.toNat + 3 + i.toNat := by
                                  rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat i (by decide)]
                                  simp; omega
                                have hdi_lt : (dst + (3 : BitVec 64) + i.setWidth 64).toNat <
                                    arH.length := by omega
                                let litI :=
                                  arH[(dst + (3 : BitVec 64) + i.setWidth 64).toNat]'hdi_lt
                                have hlitI_lt : litI.toNat < 2 * s.core.cur_vars := by
                                  have h1' : arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
                                    rw [List.getElem?_eq_getElem
                                        (by omega : dst.toNat + 3 + i.toNat < arH.length),
                                      Option.getD_some]
                                    simp only [litI, hdi_eq]
                                  have h1 := hnew_lt i.toNat hi_lt
                                  rw [← hbodyH (dst.toNat + 3 + i.toNat) (by omega), h1'] at h1
                                  exact h1
                                have hvI_eq : (litI >>> (1 : BitVec 32)).toNat = litI.toNat / 2 :=
                                  bv32_shr1_toNat litI
                                have hlitI_v : litI.toNat < sC.core.vals.length := by
                                  rw [hlenC0.core_ok.vals_len]
                                  exact Nat.lt_of_lt_of_le hlitI_lt (Nat.mul_le_mul_left 2 hcv_le)
                                have hvI_r : (litI >>> (1 : BitVec 32)).toNat <
                                    sC.core.rsns.length := by
                                  rw [hlenC0.core_ok.rsns_len, hvI_eq]
                                  exact Nat.lt_of_lt_of_le
                                    (Nat.div_lt_of_lt_mul (by omega)) hcv_le
                                have hvI_r' : litI.toNat / 2 < sC.core.rsns.length :=
                                  hvI_eq ▸ hvI_r
                                have hlitI_v64 :
                                    (litI.setWidth 64).toNat < sC.core.vals.length := by
                                  rw [zext_toNat _ (by decide)]; exact hlitI_v
                                have hvI_r64 :
                                    ((litI >>> (1 : BitVec 32)).setWidth 64).toNat <
                                      sC.core.rsns.length := by
                                  rw [zext_toNat _ (by decide), hvI_eq]; exact hvI_r
                                try (refine ⟨by decide, ?_⟩)
                                m6_to_group_strip
                                try (refine ⟨by decide, ?_⟩)
                                refine wp_join_group
                                  (M6RsnNextInv s sC litI src.toNat m) ?_ ?_
                                · rintro _ ⟨⟩ _ ⟨rfl, hmiss_cur⟩
                                  m6_c0_steps
                                  refine hLoopI (i + (1 : BitVec 32), ()) m
                                    (by dsimp only; rw [hi1_eq]; omega)
                                    ⟨rfl, by rw [hi1_eq]; omega, fun hpos j hj => ?_⟩
                                  rw [hi1_eq] at hj; by_cases hje : j = i.toNat
                                  · subst j
                                    have hlit_eq :
                                        arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
                                      rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 +
                                        i.toNat < arH.length), Option.getD_some]
                                      simp only [litI, hdi_eq]
                                    simpa [hlit_eq] using hmiss_cur hpos
                                  · exact hmissI hpos j (by omega)
                                · intro Jni hJni
                                  let sH : FullState :=
                                    { sC with core := { sC.core with arena := arH } }
                                  m6_tiny_lets; refine ⟨by decide, ?_⟩; apply wp_jnz_of
                                  · intro _
                                    m6_tiny_lets; refine ⟨by decide, ?_⟩; m6_tiny_lets
                                    apply wp_load_of
                                    · simp only [LeanQbe.T.Arg.val_var]
                                      apply FullArenaTactics.c0_load_full_vals
                                        (s := sH) (hm := hm_arH)
                                      change _ < sC.core.vals.length
                                      simp only [LeanQbe.T.bv_c0_zext32_64]; exact hlitI_v
                                    m6_tiny_lets
                                    try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                    try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                    try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                    apply wp_jnz_of
                                    · intro hval_gt0; simp only [LeanQbe.T.Arg.val_var] at hval_gt0
                                      m6_tiny_lets
                                      try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                      try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                      apply wp_load_of
                                      · simp only [LeanQbe.T.Arg.val_var]
                                        apply FullArenaTactics.c0_load_full_rsns
                                          (s := sH) (hm := hm_arH)
                                        change _ < sC.core.rsns.length
                                        simp only [LeanQbe.T.bv_c0_zext32_64,
                                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                          Nat.pow_one]; exact hvI_r'
                                      m6_tiny_lets
                                      try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                      try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                      apply wp_jnz_of; intro hc
                                      simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc
                                      · m6_tiny_lets
                                        try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                        try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                        try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                        apply wp_store_sep
                                        · simp only [LeanQbe.T.Arg.val_var]
                                          apply FullArenaTactics.c0_store_full_rsns
                                            (s := sH) (hm := hm_arH)
                                          change _ < sC.core.rsns.length
                                          simp only [LeanQbe.T.bv_c0_zext32_64,
                                            BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                            Nat.pow_one]; exact hvI_r'
                                        intro mS hmS; clear hm_arH
                                        have hrsn_eq :
                                            (sC.core.rsns[litI.toNat / 2]?.getD
                                              0xFFFFFFFF#32).toNat = src.toNat := by
                                          have h1 := congrArg BitVec.toNat hc
                                          simp only [LeanQbe.T.bv_c0_zext32_64] at h1
                                          rw [List.getElem?_eq_getElem hvI_r', Option.getD_some]
                                          simpa only [sH, litI, BitVec.toNat_ushiftRight,
                                            Nat.shiftRight_eq_div_pow, Nat.pow_one] using h1
                                        have hvg : (0#32).slt
                                            ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) =
                                            true := by
                                          simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64]
                                            using hval_gt0
                                        have hidx_eq :
                                            (BitVec.setWidth 64
                                              (arH[(dst + 3 + i.setWidth 64).toNat] >>>
                                                (1 : Nat))).toNat = litI.toNat / 2 := by
                                          simp only [LeanQbe.T.bv_c0_zext32_64,
                                            BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                            Nat.pow_one]; rfl
                                        rw [hidx_eq] at hmS
                                        have hng_raw : (hdr0 &&& 0x00080000#32) = 0#32 := by
                                          unfold fullArenaClauseGarbCore at hng_src
                                          rw [← hhdr_orig] at hng_src
                                          simpa [bne_iff_ne] using hng_src
                                        have hbits := m6_bv32_nhdr_bits hdr0 hng_raw
                                        have hsrc_fit_cap :
                                            src.toNat + 3 + (sL.core.arena[(src +
                                              (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                                              c.arena_cap := by
                                          rw [hsz_orig]
                                          exact Nat.le_trans hwf0.2.2.1
                                            (Nat.le_trans hwf0.2.2.2.1 hal_le)
                                        have hlitI_eq : arH[dst.toNat + 3 + i.toNat]?.getD 0#32 =
                                            litI := by
                                          rw [List.getElem?_eq_getElem (by omega :
                                            dst.toNat + 3 + i.toNat < arH.length),
                                            Option.getD_some]
                                          simp [litI]; congr 2; omega
                                        m6_to_group
                                        refine wp_join_group (fun (_ : Tup Val []) mK =>
                                          M6RsnBranchInv c F_cur s sPre sC R arH
                                            (nsrc32.setWidth 64).toNat dst.toNat st.toNat
                                            mark_allowed () mK) ?_ ?_
                                        · rintro _ ⟨⟩ mK hK
                                          first | rw [wp_jump] | m6_c0_steps
                                          exact hJbrk (i, ()) mK hK
                                        · intro Jm hJm; m6_jnz
                                          · have hcl0 : s.core.cur_level = 0 := by
                                              have h1 := congrArg BitVec.toNat hc
                                              rw [bv64_ofNat_toNat_id hcl_lt] at h1; exact h1
                                            try rw [wp_jump]
                                            exact hJm () _ (m6_hit_rsn_nomark_step hwPre rfl rfl
                                              hlikeC hlenC0 hcv_le hcvL harL_len harC_len harH_len
                                              hszH harH_0 hdropH hcmpH hdst_inH hdst_src hsrc_lt8
                                              hsrc_ref hnsrc64 hsrc_fit_cap hsrc_lits_eq hout_ok0
                                              hdec_cl0 hposL happend_mk hbits.2.2.1 hlitI_lt
                                              hlitI_v hvI_r' (by omega) hvg hrsn_eq (Or.inl hcl0)
                                              hmS)
                                          · have hpos : 0 < s.core.cur_level := by
                                              by_cases h0 : s.core.cur_level = 0
                                              · exfalso; apply hc
                                                rw [h0]; rfl
                                              · exact Nat.pos_of_ne_zero h0
                                            m6_to_group
                                            refine wp_join_group
                                              (fun (_ : Tup Val []) mR => mR = mS) ?_ ?_
                                            · rintro _ ⟨⟩ mR hmR_eq; subst hmR_eq
                                              have hdst_lt_arH : dst.toNat < arH.length := by omega
                                              m6_tiny_lets
                                              try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                                              apply wp_store_sep
                                              · simp only [LeanQbe.T.Arg.val_var]
                                                exact FullArenaTactics.c0_store_full_arena _
                                                  hdst_lt_arH hmS
                                              intro mR2 hmR2
                                              rw [wp_jump]
                                              let nhdr0 :=
                                                hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)
                                              have hmR_cast :
                                                  (FullMem c { sC with core := { sC.core with
                                                    arena := arH.set dst.toNat
                                                      (nhdr0 ||| 0x00200000#32)
                                                    rsns := sC.core.rsns.set (litI.toNat / 2)
                                                      (dst.setWidth 32) } } ⋆ R) mR2 := hmR2
                                              exact hJm () _ (m6_hit_rsn_mark_step hwPre rfl rfl
                                                hlenC0 hcv_le hcvL harL_len harC_len harH_len hszH
                                                harH_0 hbodyH hdropH hcmpH hdst_inH (by omega)
                                                hdst_src hsrc_lt8 hsrc_ref hnsrc64 hsrc_fit_cap
                                                hsrc_lits_eq hout_ok0 hdec_cl0 hposL happend_mk
                                                hbits hi_lt hlitI_lt hlitI_v hvI_r' hvg hrsn_eq
                                                hlitI_eq hpos hmR_cast)
                                            · intro Js hJs
                                              m6_jnz
                                              · exact hJs () mS rfl
                                              · have hfr_nil : first_red = 0xFFFFFFFF#64 := by
                                                  simpa [LeanQbe.T.Arg.val_var] using hc
                                                m6_jnz
                                                · exact hJs () mS rfl
                                                · have hred0 : (hdr0 &&& 0x00400000#32) = 0#32 := by
                                                    simpa [LeanQbe.T.Arg.val_var, hdr0,
                                                      hhdr_orig] using hc
                                                  exact hJm () _ (m6_hit_rsn_nomark_step hwPre rfl
                                                    rfl hlikeC hlenC0 hcv_le hcvL harL_len harC_len
                                                    harH_len hszH harH_0 hdropH hcmpH hdst_inH
                                                    hdst_src hsrc_lt8 hsrc_ref hnsrc64 hsrc_fit_cap
                                                    hsrc_lits_eq hout_ok0 hdec_cl0 hposL happend_mk
                                                    hbits.2.2.1 hlitI_lt hlitI_v hvI_r' (by omega)
                                                    hvg hrsn_eq (Or.inr ⟨hfr_nil, hred0⟩) hmS)
                                      · intro hc
                                        simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne,
                                          ne_eq] at hc
                                        rw [wp_jump]
                                        refine hJni () m ⟨rfl, fun _ ⟨_, _, hrs⟩ => ?_⟩
                                        apply hc; apply BitVec.eq_of_toNat_eq
                                        rw [LeanQbe.T.bv_c0_zext32_64]
                                        have h1 := congrArg BitVec.toNat hrs
                                        rw [bv32_ofNat_toNat (by omega),
                                          List.getElem?_eq_getElem hvI_r', Option.getD_some] at h1
                                        simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64,
                                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                          Nat.pow_one] using h1
                                    · intro hc; simp only [LeanQbe.T.Arg.val_var] at hc
                                      rw [wp_jump]; refine hJni () m ⟨rfl, fun _ ⟨_, hvg, _⟩ => ?_⟩
                                      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some] at hvg
                                      exact Bool.false_ne_true (hc.symm.trans
                                        (by simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64]
                                              using hvg))
                                  · intro hc
                                    simp only [LeanQbe.T.Arg.val_var, BitVec.ult,
                                      decide_eq_false_iff_not, LeanQbe.T.bv_c0_zext32_64,
                                      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                      Nat.pow_one, BitVec.toNat_ofNat] at hc
                                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                                    change ¬ (litI.toNat / 2 < s.core.cur_vars) at hc; omega
                              · -- Loop ended (`i = new_sz`) without match
                                have hi_eq : i.toNat = st.toNat := by omega
                                try rw [wp_jump]
                                have hng_raw : (hdr0 &&& 0x00080000#32) = 0#32 := by
                                  unfold fullArenaClauseGarbCore at hng_src
                                  rw [← hhdr_orig] at hng_src; simpa [bne_iff_ne] using hng_src
                                have hbits := m6_bv32_nhdr_bits hdr0 hng_raw
                                have hsrc_fit_cap : src.toNat + 3 +
                                    (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                                    c.arena_cap := by
                                  rw [hsz_orig]; exact Nat.le_trans hwf0.2.2.1
                                    (Nat.le_trans hwf0.2.2.2.1 hal_le)
                                have hdst_fit_arH : dst.toNat + 3 + st.toNat ≤ arH.length := by
                                  rw [harH_len]
                                  exact Nat.le_trans
                                    (Nat.add_le_add (Nat.add_le_add_right hdst_src 3) hnew_le)
                                    hsrc_fit_cap
                                have hrm_miss : ∀ hpos : 0 < s.core.cur_level,
                                    SweepReasonMapInv sPre.core
                                      { sC.core with arena := arH } (nsrc32.setWidth 64).toNat
                                      (dst.toNat + 3 + st.toNat) := fun hpos => by
                                  obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
                                    sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hpos)
                                      harL_len harC_len hsrc_fit_cap hdst_src hsrc_lits_eq hszH
                                      hdropH
                                  exact SweepReasonMapInv.congr_rsns_arena rfl rfl
                                    (SweepReasonMapInv.keep_step (kL := sL.core) hwPre hsrc_ref
                                      hnsrc64 hdst_src hsrc_lt8 (hposL.get hpos).2.2.2.2.2.2
                                      (happend_mk sC.core.rsns hlits_eq)
                                      (fun _ _ _ => by rw [hrC])
                                      (fun idx hidx heq => absurd heq
                                        (m6_rsn_not_src_of_miss hwPre
                                          (hposL.get hpos).2.2.2.2.2.2
                                          (hvC.trans (hposL.get hpos).2.1) hrC hszH
                                          hdst_fit_arH hsrc_lt8 hlits_eq
                                          (fun j hj => hmissI hpos j (by omega)) hidx)))
                                refine hJbrk (i, ()) m ⟨arH, sC.core.rsns, harH_len,
                                  hlenC0.core_ok.rsns_len, fun _ _ => rfl, fun _ _ => rfl, hszH,
                                  by rw [harH_0, Option.getD_some]; exact hbits.2.2.1, rfl,
                                  hcmpH.with_rsns, hdst_inH, fun _ _ _ => rfl, fun _ => rfl,
                                  hrm_miss, fun hp _ idx hidx heq => by
                                    obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
                                      sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hp)
                                        harL_len harC_len hsrc_fit_cap hdst_src hsrc_lits_eq
                                        hszH hdropH
                                    have hnot := m6_rsn_not_src_of_miss hwPre
                                      (hposL.get hp).2.2.2.2.2.2 (hvC.trans (hposL.get hp).2.1)
                                      hrC hszH hdst_fit_arH hsrc_lt8 hlits_eq
                                      (fun j hj => hmissI hp j (by omega)) hidx
                                    exact absurd (hrC ▸ heq)
                                      (m6_rsn_ne_dst_of_not_src_val hwPre hdst_src
                                        (by omega) (hposL.get hp).2.2.2.2.2.2 hnot hsrc_lt8 hidx),
                                  fullMem_cast hm_arH rfl⟩
                        · -- `(hdr & PH_RSN) == 0`
                          intro hc; simp only [LeanQbe.T.Arg.val_var, bne_eq_false_iff_eq] at hc
                          have hng_raw : (hdr0 &&& 0x00080000#32) = 0#32 := by
                            unfold fullArenaClauseGarbCore at hng_src
                            rw [← hhdr_orig] at hng_src; simpa [bne_iff_ne] using hng_src
                          have hbits := m6_bv32_nhdr_bits hdr0 hng_raw
                          have hrm_unm : ∀ hpos : 0 < s.core.cur_level,
                              SweepReasonMapInv sPre.core
                                { sC.core with arena := arH } (nsrc32.setWidth 64).toNat
                                (dst.toNat + 3 + st.toNat) := fun hpos => by
                            have hsrc_fit_cap : src.toNat + 3 +
                                (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                                c.arena_cap := by
                              rw [hsz_orig]; exact Nat.le_trans hwf0.2.2.1
                                (Nat.le_trans hwf0.2.2.2.1 hal_le)
                            obtain ⟨_, _, _, hrC, _, _, _, hlits_eq⟩ :=
                              sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hpos) harL_len
                                harC_len hsrc_fit_cap hdst_src hsrc_lits_eq hszH hdropH
                            exact m6_sweep_rsn_unmarked_pos hwPre (Nat.le_trans hst_dst hdst_src)
                              (hrmkPre hpos) hsrc_ref hnsrc64 hdst_src hsrc_lt8
                              (hposL.get hpos).2.2.2.2.2.2 (happend_mk sC.core.rsns hlits_eq) hrC
                              (by rw [← hhdr_orig]; exact hc)
                          rw [wp_jump]
                          exact hJR () m ⟨arH, sC.core.rsns, harH_len, hlenC0.core_ok.rsns_len,
                            fun _ _ => rfl, fun _ _ => rfl, hszH,
                            by rw [harH_0, Option.getD_some]; exact hbits.2.2.1, rfl,
                            CompactPrefixOk.with_rsns hcmpH, hdst_inH, fun _ _ _ => rfl,
                            fun _ => rfl, hrm_unm,
                            fun hp _ idx hidx heq => by
                              obtain ⟨-, -, -, -, hrC, _⟩ := hout_ok0.1 ((hdec_cl0 false).mpr hp)
                              rw [hrC] at heq
                              have hnot := m6_rsn_not_src_of_unmarked hwPre
                                (Nat.le_trans hst_dst hdst_src) (hrmkPre hp) hsrc_lt8
                                (by rw [← hhdr_orig]; exact hc) hidx
                              exact absurd heq (m6_rsn_ne_dst_of_not_src_val hwPre hdst_src
                                (by omega) (hposL.get hp).2.2.2.2.2.2 hnot hsrc_lt8 hidx),
                            fullMem_cast hm_arH rfl⟩
        · -- Exit compaction loop (`src = alen`): jump to `JE`
          have hsrc_end : src.toNat = s.core.arena_len := by c0_bound
          m6_c0_steps
          have hwEnd : FullWitnessInv c F0 F_cur { sL.core with arena_len := dst.toNat } :=
            m6_sweep_end_witness (_rwL := rwL) hwPre rfl hal_le (by omega) hdm0 hcvL halL hclL
              hdmL hftL hfdL hincL harL_len hst_dst hlenL hcmpL hcmpL_st hlayL hltL hrootL
              (hsrc_end ▸ hposL)
          refine hJE (src, dst, first_red, irred, redd, has_iar, false, new_unit, ()) mL
            ⟨hst_dst, by omega, hhas_iar, sL, rwL, hlikeL, hlenL, hcmpL, hcmpL_st, hlayL, hltL,
             hstL_in, hwEnd, hfrL, fun hp => hsrc_end ▸ (hposL.get hp).2.2.2.2.2.2,
             fun h => Bool.noConfusion h, fun hnu => ?_, fun hpos => ?_, hmL⟩
          · by_cases hcl0 : s.core.cur_level = 0
            · exact ⟨hcl0, (hrootL.get hcl0).2.2.2 hnu⟩
            · exact absurd ((hposL.get (Nat.pos_of_ne_zero hcl0)).1) (by simp [hnu])
          · obtain ⟨hnu, hv, hl, ht, htp, hte, _⟩ := hposL.get hpos
            exact ⟨rfl, hnu, hv, hl, ht, htp, hte⟩
  · -- Entry to optional `[0, fp)` prefix validation & conditional `PH_RSN` clear
    intro JPre hJPre
    clear hsweep_bins_r hnext hcopy hmovered hrewatch_r hcap_lt hmax_lt hcv_le hcl_lt
      hdec_cl0 hcl_beq hQ
    have hpre0 : JPre (0#64, 0#64, ()) m :=
      hJPre (0#64, 0#64, ()) m ⟨Nat.zero_le _, fun h => absurd h (by simp), s.core.arena,
        hlen, hw, hnd0, fun hlt => fullArenaClauseRefs_zero_mem hw.arena hlt,
        ⟨fullArenaClausesInv_zero, fun _ hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs]
            at hr,
          fun _ _ hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs] at hr⟩,
        SweepReasonMapInv.init, fun hpos idx hidx hlvl hlg _ => hrmk0 hpos idx hidx hlvl hlg, hm⟩
    m6_jnz
    · m6_c0_steps; exact hpre0
    · have hpos : 0 < s.core.cur_level := by
        by_cases h0 : s.core.cur_level = 0
        · exact absurd (by simp [h0]) hc
        · exact Nat.pos_of_ne_zero h0
      m6_jnz
      · have hunfl0 : s.core.unflushed = 0#64 :=
          BitVec.eq_of_toNat_eq (by change s.core.unflushed.toNat = 0; c0_bound)
        m6_jnz
        · have hfp_pos : 0 < s.core.first_reducible.toNat := by c0_bound
          m6_jnz
          · have hfp_lt : s.core.first_reducible.toNat < s.core.arena_len := by c0_bound
            m6_to_group
            refine wp_join_group (PreSweepValBrkInv s s.core.first_reducible.toNat m) ?_ ?_
            · rintro _ ⟨p, cnt, pre_ok, ⟨⟩⟩ mB ⟨hmB, hp_le, hchain⟩
              subst mB
              m6_jnz
              · have hpre_ok : pre_ok = true := hc
                m6_jnz
                · have hp_eq : p.toNat = s.core.first_reducible.toNat :=
                    congrArg BitVec.toNat (by assumption)
                  have hc0 : CleanIrredChain s.core.arena 0 s.core.first_reducible.toNat := by
                    rw [← hp_eq]; exact hchain hpre_ok
                  have h3_fp : 3 ≤ s.core.first_reducible.toNat := by
                    have h := cleanIrredChain_three_le hc0 hfp_pos; omega
                  have h0_in_fp : 0 ∈ fullArenaClauseRefsCore
                      { s.core with arena_len := s.core.first_reducible.toNat } := by
                    unfold fullArenaClauseRefsCore
                    cases hfp : s.core.first_reducible.toNat with
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
                      have hcp_lt_al : cp.toNat < s.core.arena_len := by omega
                      generalize hcp_nat : cp.toNat = cpn at hrem
                      cases hrem with
                      | empty => omega
                      | @step _ _ h3 hfl hsz hfit htl =>
                        rw [← hcp_nat] at h3 hfl hsz hfit htl
                        have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
                        have hcp_lt_ar : cp.toNat < arL.length := by omega
                        have hcp2_lt_ar : (cp + 2#64).toNat < arL.length := by rw [hcp2_eq]; omega
                        let sC_pre : FullState := { s with core := { s.core with arena := arL } }
                        have hmC' : (FullMem c sC_pre ⋆ R) mC := hmC
                        m6_tiny_lets
                        apply wp_load_of
                        · simp only [LeanQbe.T.Arg.val_var]
                          exact FullArenaTactics.c0_load_full_arena (s := sC_pre) hcp_lt_ar hmC'
                        m6_tiny_lets
                        apply wp_load_of
                        · simp only [LeanQbe.T.Arg.val_var]
                          exact FullArenaTactics.c0_load_full_arena (s := sC_pre) hcp2_lt_ar hmC'
                        m6_tiny_lets
                        refine wp_join_group (fun (_ : Tup Val []) mC2 =>
                            (FullMem c { s with core := { s.core with
                              arena := arL.set cp.toNat
                                ((arL[cp.toNat]'hcp_lt_ar) &&& ~~~0x00200000#32) } } ⋆ R) mC2)
                          ?_ ?_
                        · rintro _ ⟨⟩ mC2 hmC2
                          m6_tiny_lets
                          try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                          rw [wp_jump]
                          obtain ⟨hcp_nxt, hsz_eq, hinv'⟩ :=
                            m6_pre_clr_step hcp_lt hfp_lt hal_le harL_l hdone hsz hfl hsz hfit htl
                              (hcp_in hcp_lt) htailL hmatchL hmC2
                          exact hLoopC _ _
                            (by simp only [LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var]
                                dsimp only [sC_pre]
                                change s.core.first_reducible.toNat -
                                  (cp + 3#64 +
                                    (arL[(cp + 2#64).toNat]'hcp2_lt_ar).setWidth 64).toNat <
                                  s.core.first_reducible.toNat - cp.toNat
                                rw [hcp_nxt, hsz_eq]; omega) hinv'
                        · intro Jif hJif
                          m6_jnz
                          · m6_tiny_lets
                            try (refine ⟨by decide, ?_⟩; m6_tiny_lets)
                            apply wp_store_sep
                            · simp only [LeanQbe.T.Arg.val_var]
                              exact FullArenaTactics.c0_store_full_arena (s := sC_pre) _
                                hcp_lt_ar hmC'
                            intro mC2 hmC2
                            rw [wp_jump]
                            exact hJif () mC2 hmC2
                          · have hzero : (arL[cp.toNat]'hcp_lt_ar) &&& 0x00200000#32 = 0#32 := by
                              dsimp only [sC_pre] at hc; exact hc
                            have har_id : arL.set cp.toNat
                                ((arL[cp.toNat]'hcp_lt_ar) &&& ~~~0x00200000#32) = arL :=
                              s9_pre_clr_no_chg_id arL hcp_lt_ar hzero
                            exact hJif () mC (Eq.mp (congrArg (fun a => (FullMem c
                              { s with core := { s.core with arena := a } } ⋆ R) mC) har_id.symm)
                              hmC')
                    · have hcp_eq : cp.toNat = s.core.first_reducible.toNat := by c0_bound
                      rw [hcp_eq] at hdone hmatchL
                      obtain ⟨hlenP, hwP, hndP, hfpP, hcmpP, hrmP, hmkP⟩ :=
                        m6_pre_val_all_ok hlen hw hnd0 hrmk0 hfp_pos hfp_lt hdone harL_l
                          (fun i hi1 hi2 => htailL i (by omega) hi2)
                          (fun r hr => hmatchL r hr (by
                            unfold fullArenaClauseRefsCore at hr
                            have h1 := (fullArenaScanRefs_mem_bounds hr).2
                            dsimp only at h1; omega))
                          rfl
                      m6_tiny_lets
                      try rw [wp_jump]
                      try (apply hJ; dsimp only [Blocks.get_here, Blocks.get_there])
                      try rw [wp_jump]
                      exact hJPre (s.core.first_reducible, cnt, ()) mC
                        ⟨Nat.le_of_lt hfp_lt, fun _ => ⟨hpos, hfp_lt⟩,
                         arL, hlenP, hwP, hndP, hfpP, hcmpP, hrmP, hmkP, hmC⟩
                · m6_c0_steps; exact hpre0
              · m6_c0_steps; exact hpre0
            · intro Jv hJv
              clear hJPre hpre0 hw hnd0 hrmk0 hpos hunfl0
              refine wp_loop_inv (PreSweepValInv s s.core.first_reducible.toNat m)
                (fun (p, _) _ => s.core.first_reducible.toNat - p.toNat)
                (fun Jp hLoopP => ?_) ?_
              · m6_tiny_jump; exact hLoopP (0#64, 0#64, ()) m ⟨rfl, Nat.zero_le _, .empty⟩
              · rintro Jp ⟨p, cnt, ⟨⟩⟩ mL ⟨rfl, hp_le, hc_p⟩ hLoopP
                have har_cap : c.arena_cap < 2 ^ 30 := by
                  have h := c.harena; unfold dimacsBound at h; omega
                have hfp_cap : s.core.first_reducible.toNat < c.arena_cap :=
                  Nat.lt_of_lt_of_le hfp_lt hal_le
                m6_jnz
                · have hp_lt : p.toNat < s.core.first_reducible.toNat := by c0_bound
                  m6_jnz
                  · m6_tiny_jump
                    exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                  · have hp3_64 : p.toNat + 3 < 2 ^ 64 := by omega
                    have h3 := bv64_add3_lt (x := p) hp3_64
                    have hp3_fp : p.toNat + 3 ≤ s.core.first_reducible.toNat := by
                      have hnot : ¬ s.core.first_reducible.toNat <
                          (p.toNat + BitVec.toNat 3) % 2 ^ 64 := hc
                      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                        Nat.mod_eq_of_lt hp3_64] at hnot
                      exact Nat.not_lt.mp hnot
                    have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2_lt (by omega)
                    have hp_lt_ar : p.toNat < s.core.arena.length := by omega
                    have hp2_lt_ar : (p + 2#64).toNat < s.core.arena.length := by
                      rw [hp2_eq]; omega
                    let hdr := s.core.arena[p.toNat]'hp_lt_ar
                    let sz := s.core.arena[(p + 2#64).toNat]'hp2_lt_ar
                    m6_jnz
                    · m6_tiny_jump
                      exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                    · have hfl : (s.core.arena[p.toNat]?.getD 0#32 &&& 0x00C80000#32) = 0#32 := by
                        rw [List.getElem?_eq_getElem hp_lt_ar, Option.getD_some]
                        simpa [hdr] using hc
                      m6_jnz
                      · m6_tiny_jump
                        exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                      · have hsz_eq : sz.toNat = (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by
                          rw [← hp2_eq, List.getElem?_eq_getElem hp2_lt_ar, Option.getD_some]
                        have hsz3 : 3 ≤ (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by
                          have h := hc
                          simp only [show (BitVec.toNat (2 : BitVec 64)) = 2 from rfl,
                            show (BitVec.toNat (3 : BitVec 32)) = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega : p.toNat + 2 < 2 ^ 64)] at h
                          rw [← hsz_eq]; simp only [sz, hp2_eq]; exact Nat.not_lt.mp h
                        have hpsz_64 : p.toNat + 3 + sz.toNat < 2 ^ 64 := by
                          have hsz_u32 : sz.toNat < 2 ^ 32 := sz.isLt; omega
                        have hp_nxt : (p + 3#64 + sz.setWidth 64).toNat =
                            p.toNat + 3 + sz.toNat := bv64_add3_zext_lt hpsz_64
                        try (refine ⟨by decide, ?_⟩)
                        m6_jnz
                        · m6_tiny_jump
                          exact hJv (p, cnt, false, ()) mL ⟨rfl, hp_le, fun h => by cases h⟩
                        · have hfit :
                              p.toNat + 3 + (s.core.arena[p.toNat + 2]?.getD 0#32).toNat ≤
                              s.core.first_reducible.toNat := by
                            have hmodp2 : (p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                                (p + 2#64).toNat := by
                              rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, hp2_eq,
                                Nat.mod_eq_of_lt (by omega)]
                            have h1 : ¬ s.core.first_reducible.toNat <
                                ((p.toNat + 3 + sz.toNat) % 2 ^ 64) := by
                              have h := hc
                              simp only [hmodp2,
                                show BitVec.toNat (3 : BitVec 64) = 3 from rfl] at h
                              exact h
                            rw [Nat.mod_eq_of_lt hpsz_64] at h1
                            rw [← hsz_eq]; exact Nat.not_lt.mp h1
                          m6_tiny_jump
                          exact hLoopP (p + 3#64 + sz.setWidth 64, cnt + 1#64, ()) mL
                            (by dsimp only; rw [hp_nxt, hsz_eq]; omega)
                            ⟨rfl, by rw [hp_nxt, hsz_eq]; exact hfit,
                             by rw [hp_nxt]; exact hc_p.snoc (by omega) hfl hsz3 (by rw [hsz_eq])⟩
                · m6_tiny_jump; exact hJv (p, cnt, true, ()) mL ⟨rfl, hp_le, fun _ => hc_p⟩
          · m6_tiny_jump; exact hpre0
        · m6_tiny_jump; exact hpre0
      · m6_tiny_jump; exact hpre0

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end
