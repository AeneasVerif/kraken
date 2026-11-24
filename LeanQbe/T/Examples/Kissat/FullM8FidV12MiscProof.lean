/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8FidV12
public import LeanQbe.T.Examples.Kissat.FullM5Sched
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof0
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof1a
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
public import LeanQbe.T.Examples.Kissat.FullM7CompactFixProof
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

private theorem m8_cnfOfClauses_cons_nil_unsat (F : List (List Nat)) :
    (cnfOfClauses ([] :: F)).Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause []).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0
  rcases h0 with ⟨l, hl, _⟩
  exact absurd (mem_cnfClause_iff.mp hl) (by simp)

private theorem m8_cnfOfClauses_cons_nil_entails (F : List (List Nat)) :
    (cnfOfClauses ([] :: F)).Entails (cnfOfClauses F) := by
  rw [CNF.entails_def]
  intro α hα
  have h0 : (cnfClause []).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) (cnfClause [])
      (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0
  rcases h0 with ⟨l, hl, _⟩
  exact absurd (mem_cnfClause_iff.mp hl) (by simp)

private theorem m8_fullWitnessInv_cons_nil_of_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (inc' : BitVec 64) (hu : F0.Unsat) :
    FullWitnessInv c F0 ([] :: F_cur) { k with inconsistent := inc' } := by
  have hEnt := m8_cnfOfClauses_cons_nil_entails F_cur
  refine
    { ext_sound := ⟨fun cl hcl => by
        rcases List.mem_cons.mp hcl with rfl | hmem
        · intro l hl; cases hl
        · exact hw.ext_sound.1 cl hmem, fun _ => hu⟩
      inconsistent_sound := fun _ => m8_cnfOfClauses_cons_nil_unsat F_cur
      arena := { hw.arena.mono hEnt with len_ok := hw.arena.len_ok }
      watches := hw.watches.mono hEnt |>.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := hw.cur_level_le
      trail_lits_lt := hw.trail_lits_lt
      trail_vars_nodup := hw.trail_vars_nodup
      vals_domain := hw.vals_domain
      vals_true_iff := hw.vals_true_iff
      vals_false_iff := hw.vals_false_iff
      lvl_le := hw.lvl_le
      dec_earliest := hw.dec_earliest
      levels_inhabited := hw.levels_inhabited
      level0_sound := fun i hi hl => CNF.entails_clause_trans hEnt (hw.level0_sound i hi hl)
      trail_pos_inv := hw.trail_pos_inv
      level0_rsn_none := hw.level0_rsn_none
      frame_trail_lt := hw.frame_trail_lt
      frame_trail_mono := hw.frame_trail_mono
      frame_trail_before_lt := hw.frame_trail_before_lt
      frame_dec_lt := hw.frame_dec_lt
      reason_inv := fun idx hidx hne => by
        have hr := hw.reason_inv idx hidx hne
        dsimp only at hr ⊢
        split at hr <;> split <;> try contradiction
        · exact ⟨hr.1, CNF.entails_clause_trans hEnt hr.2.1, hr.2.2⟩
        · exact hr
      reason_lit_mem := hw.reason_lit_mem }

private theorem m8_fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with unflushed := 0#64 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem m8_fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem m8_fullSparseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    m8_fullWitnessInv_with_inconsistent hsp.2.1 hu inc',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m8_level0_fcur_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_)
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private theorem m8_sparseInvW_of_prop_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (_hlenS : s.LengthsOk c) (hndS : FullArenaVarsNodup s)
    (hextS : FullExtScratchOk c s) (hlmS : FullLitMarksClear c s) (_hdmS : s.core.dense_mode = 0#64)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (_htr' : FullTrailExt s.core s'.core) (hperm' : FullArenaPermEq s.core s'.core)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hex' : s'.scratch.extend_len = s.scratch.extend_len) (hdm' : s'.core.dense_mode = 0#64) :
    FullSparseInvW c F0 F_cur s' := by
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hndS r' hr0' hgb0)
  have hll_wf' : FullLastLearnedWf s' :=
    hextS.1.of_refs_subset hll' fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hlm_ok' : FullLitMarksClear c s' := by
    exact ⟨fun v hv => by rw [hmrk']; exact hlmS.1 v hv, fun l hl => by rw [hlm']; exact hlmS.2 l hl⟩
  exact ⟨hlen', hw', hlm_ok', hnd', ⟨hll_wf', by rw [hex']; exact hextS.2⟩, hdm'⟩

section M8RestartDue
open LeanQbe.T.Examples.Kissat.FullM5Sched
open LeanQbe.T.Examples.Kissat.Full hiding
  full_ema_update_body full_ema_update_wf
  full_rephase_body full_rephase_wf
  full_switch_mode_body full_switch_mode_wf
  full_restart_due_body full_restart_due_wf
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
private theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

private theorem wp_let_add64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .add i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_mul64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .mul i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_mul_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_ugt64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ult b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ugt i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ugt_eq, cast_eq] using hc

private theorem wp_let_ult64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

private theorem probePres_refl (s : Full.FullState) : Full.FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem probePres_trans {s₁ s₂ s₃ : Full.FullState}
    (h12 : Full.FullProbeScratchPres s₁ s₂) (h23 : Full.FullProbeScratchPres s₂ s₃) :
    Full.FullProbeScratchPres s₁ s₃ :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem bv64_add1_toNat {k : BitVec 64} (hk : k.toNat + 1 < 2 ^ 64) :
    (k + 1#64).toNat = k.toNat + 1 := by
  bv_omega

section M5SchedTactics

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops, stopping at `Expr.group` instead of inlining join points. -/
local elab "m5_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops on the main goal until `Expr.jnz`, then split it once. -/
local elab "m5_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

open Lean Elab Tactic in
/-- Step all `C0Step` goals up to `Expr.jnz` (without splitting `jnz`). -/
local elab "m5_to_jnz" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops until `OpCode.udiv`, `Expr.jnz`, or `Expr.group`. -/
local elab "m5_to_udiv" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).headBeta
      if e.isAppOf ``LeanQbe.T.Expr.group || e.isAppOf ``LeanQbe.T.Expr.jnz then return
      let st ← saveState
      let isDiv ← try
        evalTactic (← `(tactic| refine wp_udiv_of ?_ ?_))
        pure true
      catch _ => pure false
      st.restore
      if isDiv then return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100


private theorem fullState_lengths_with_restart_limit {c : Full.FullCfg} {s : Full.FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ s with scratch := { s.scratch with restart_limit := v } } : Full.FullState).LengthsOk c :=
  h.with_scratch { h.scratch_ok with walk_vals_len := h.scratch_ok.walk_vals_len }

theorem m8_restart_due_wp (Γ : Env)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullRestartDueSpec a m Q X → Func.wp Γ m8_restart_due_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hlen hm hQ
  c0_step; m5_split
  · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
  · m5_split
    · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
    · m5_split
      · m5_split
        · c0_steps
          let sc' : Full.FullScratch := { s.scratch with rel_trigger := 0#64 }
          have hlen' : ({ s with scratch := sc' } : Full.FullState).LengthsOk c :=
            hlen.with_scratch
              { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
          exact hQ (1#64, ()) { s with scratch := sc' } _ rfl hlen' ⟨Or.inr rfl, rfl, rfl⟩ hm
        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
      · m5_to_jnz
        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
        · m5_to_jnz
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
          · m5_to_jnz
            refine wp_jnz_of (fun _ => ?_) (fun hfd_ne => ?_)
            · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
            · m5_to_jnz
              refine wp_jnz_of (fun _ => ?_) (fun hsd_ne => ?_)
              · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
              · simp only [Arg.val_var] at hfd_ne hsd_ne
                c0_cond hfd_ne
                c0_cond hsd_ne
                have hfd_nz : (1#64 <<< 32 - s.scratch.ema_fast_exp) ≠ 0#64 := hfd_ne
                have hsd_nz : (1#64 <<< 32 - s.scratch.ema_slow_exp) ≠ 0#64 := hsd_ne
                m5_to_group
                refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1)
                  (fun _ (fbc, ()) _ hm1 => ?_) ?_
                · rcases hm1 with rfl; m5_to_group
                  refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
                    (fun _ (sbc, ()) _ hm2 => ?_) ?_
                  · rcases hm2 with rfl
                    m5_to_udiv
                    refine wp_udiv_of
                      (by simp only [Arg.val_var]; exact hfd_nz) ?_
                    m5_to_udiv
                    refine wp_udiv_of
                      (by simp only [Arg.val_var]; exact hsd_nz) ?_
                    m5_to_group
                    refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
                      (fun _ (fval, ()) _ hm3 => ?_) ?_
                    · rcases hm3 with rfl
                      m5_to_group
                      refine wp_join_group (ts := [i64]) (fun _ m4 => m = m4)
                        (fun _ (sval, ()) _ hm4 => ?_) ?_
                      · rcases hm4 with rfl
                        m5_to_jnz
                        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                        · m5_to_group
                          refine wp_join_group (ts := [i64]) (fun _ m5 => m = m5)
                            (fun _ (rst, ()) _ hm5 => ?_) ?_
                          · rcases hm5 with rfl
                            m5_to_group
                            c0_call hIlog
                            intro d10 _ _
                            m5_to_group
                            refine wp_join_group (ts := [i64]) (fun _ m6 => m = m6)
                              (fun _ (delta, ()) _ hm6 => ?_) ?_
                            · rcases hm6 with rfl
                              c0_steps
                              let sc' : Full.FullScratch :=
                                { s.scratch with restart_limit := s.scratch.conflicts + delta }
                              exact hQ (1#64, ()) { s with scratch := sc' } _ rfl
                                (fullState_lengths_with_restart_limit hlen _)
                                ⟨Or.inr rfl, rfl, rfl⟩ hm
                            · intro _ hJd; c0_steps
                              exact hJd (d10, ()) m rfl
                          · intro _ hJrc; c0_steps
                            · exact hJrc (s.scratch.restarts + 1#64, ()) m rfl
                            · exact hJrc (1000000000000#64, ()) m rfl
                        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
                      · intro _ hJs; c0_steps
                        · exact hJs (1#64 <<< 32, ()) m rfl
                        · exact hJs (_, ()) m rfl
                    · intro _ hJf; c0_steps
                      · exact hJf (1#64 <<< 32, ()) m rfl
                      · exact hJf (_, ()) m rfl
                  · intro _ hJsb; c0_steps
                    · exact hJsb (16384#64 <<< 32, ()) m rfl
                    · exact hJsb (s.scratch.ema_slow_biased, ()) m rfl
                · intro _ hJfb; c0_steps
                  · exact hJfb (16384#64 <<< 32, ()) m rfl
                  · exact hJfb (s.scratch.ema_fast_biased, ()) m rfl

end M5SchedTactics
end M8RestartDue


section M8SwitchMode
open LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
local macro "fs_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "fs_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

local elab "fs_nojnz" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local elab "fs_nojnz_grp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

/-! ## 1. Shared BV & State-Preservation Helpers -/

private theorem fs_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem fs_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fs_bv64_sub1 {x : BitVec 64} (hx : x ≠ 0#64) : (x - 1#64).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 =>
    hx (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

private theorem fs_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fs_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem fs_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

private theorem fs_bv64_lshr1_le (x : BitVec 64) : (x >>> 1#64).toNat ≤ x.toNat := by
  change (x >>> (1 : Nat)).toNat ≤ _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega

private theorem fs_getElem_congr {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem fs_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem fid_len_scalars {c : FullCfg} {s s' : FullState} (h : s.LengthsOk c)
    (hc : s'.core = s.core := by rfl)
    (h1 : s'.scratch.walk_vals = s.scratch.walk_vals := by rfl)
    (h2 : s'.scratch.phases = s.scratch.phases := by rfl)
    (h3 : s'.scratch.phases_target = s.scratch.phases_target := by rfl)
    (h4 : s'.scratch.phases_best = s.scratch.phases_best := by rfl)
    (h5 : s'.scratch.walk_best = s.scratch.walk_best := by rfl)
    (h6 : s'.scratch.heap = s.scratch.heap := by rfl)
    (h7 : s'.scratch.pos = s.scratch.pos := by rfl)
    (h8 : s'.scratch.shrink_stk = s.scratch.shrink_stk := by rfl)
    (h9 : s'.scratch.q_prev = s.scratch.q_prev := by rfl)
    (h10 : s'.scratch.q_next = s.scratch.q_next := by rfl)
    (h11 : s'.scratch.q_stamp = s.scratch.q_stamp := by rfl)
    (h12 : s'.scratch.wsort = s.scratch.wsort := by rfl)
    (h13 : s'.scratch.work_stk1 = s.scratch.work_stk1 := by rfl)
    (h14 : s'.scratch.work_stk2 = s.scratch.work_stk2 := by rfl)
    (h15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark := by rfl)
    (h16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach := by rfl)
    (h17 : s'.scratch.score = s.scratch.score := by rfl)
    (h18 : s'.scratch.sim_sig = s.scratch.sim_sig := by rfl)
    (h19 : s'.scratch.glue_used = s.scratch.glue_used := by rfl)
    (h20 : s'.scratch.last_learned = s.scratch.last_learned := by rfl)
    (h21 : s'.scratch.delayed = s.scratch.delayed := by rfl)
    (h22 : s'.scratch.red_refs = s.scratch.red_refs := by rfl)
    (h23 : s'.scratch.extend_stk = s.scratch.extend_stk := by rfl)
    (h24 : s'.scratch.scratch_buf = s.scratch.scratch_buf := by rfl) : s'.LengthsOk c :=
  ⟨hc ▸ h.core_ok, ⟨h1 ▸ h.scratch_ok.walk_vals_len, h2 ▸ h.scratch_ok.phases_len,
    h3 ▸ h.scratch_ok.phases_target_len, h4 ▸ h.scratch_ok.phases_best_len,
    h5 ▸ h.scratch_ok.walk_best_len, h6 ▸ h.scratch_ok.heap_len_arr, h7 ▸ h.scratch_ok.pos_len,
    h8 ▸ h.scratch_ok.shrink_stk_len, h9 ▸ h.scratch_ok.q_prev_len, h10 ▸ h.scratch_ok.q_next_len,
    h11 ▸ h.scratch_ok.q_stamp_len, h12 ▸ h.scratch_ok.wsort_len, h13 ▸ h.scratch_ok.work_stk1_len,
    h14 ▸ h.scratch_ok.work_stk2_len, h15 ▸ h.scratch_ok.tarjan_mark_len,
    h16 ▸ h.scratch_ok.tarjan_reach_len, h17 ▸ h.scratch_ok.score_len,
    h18 ▸ h.scratch_ok.sim_sig_len, h19 ▸ h.scratch_ok.glue_used_len,
    h20 ▸ h.scratch_ok.last_learned_len, h21 ▸ h.scratch_ok.delayed_len_arr,
    h22 ▸ h.scratch_ok.red_refs_len, h23 ▸ h.scratch_ok.extend_stk_len,
    h24 ▸ h.scratch_ok.scratch_buf_len⟩⟩


/-! ## 2. `full_bump_analyzed_fid_wp` (`m6aBumpAnalyzedSpec`) -/

section BumpAnalyzedProof


private theorem fid_apply_ite {α β : Type} (f : α → β) (P : Prop) [Decidable P] (a b : α) :
    f (if P then a else b) = if P then f a else f b := by
  by_cases h : P <;> simp [h]

private theorem fid_ite_eq {α : Type} (P : Prop) [Decidable P] {a b c : α}
    (ha : a = c) (hb : b = c) : (if P then a else b) = c := by
  by_cases h : P <;> simp [h, ha, hb]

private theorem fid_emaSwapSc_proj {α : Type} (f : FullScratch → α)
    (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
      f { sc with
        stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
        ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc)
    (sc : FullScratch) (om nm : BitVec 64) :
    f (m7EmaSwapSc sc om nm) = f sc := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [fid_apply_ite f]
  exact fid_ite_eq _ (hf _ _ _ _ _ _ _) (hf _ _ _ _ _ _ _)

private theorem fid_probePres_emaSwap (sc : FullScratch) (om nm : BitVec 64)
    {s0 s1 : FullState} (hp : FullProbeScratchPres s0 s1)
    (hsc : s1.scratch = sc) :
    FullProbeScratchPres s0 { s1 with scratch := m7EmaSwapSc sc om nm } := by
  subst hsc
  have h : ∀ {α} (f : FullScratch → α)
      (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
        f { sc with
          stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
          ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc),
      f (m7EmaSwapSc s1.scratch om nm) = f s1.scratch :=
    fun f hf => fid_emaSwapSc_proj f hf s1.scratch om nm
  exact ⟨⟨(h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.1,
      (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.2⟩,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.2⟩

private theorem fid_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fid_probePres_trans {s0 s1 s2 : FullState}
    (h1 : FullProbeScratchPres s0 s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s0 s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

private theorem fid_ema_swap_f2s_stable (sc : FullScratch) :
    (m7EmaSwapSc sc 0#64 1#64).stable = 1#64 := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [fid_apply_ite FullScratch.stable]
  exact fid_ite_eq _ rfl rfl

private theorem fid_get64_emaSet_mask (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    m7Get64Val (m7ModeEmaSet gu mode v) m7GuEmaMaskIdx = m7Get64Val gu m7GuEmaMaskIdx := by
  have hltG : ∀ (g : List (BitVec 32)) idx val, 40 ≤ idx →
      m7Get64Val (m7Set64List g idx val) m7GuEmaMaskIdx = m7Get64Val g m7GuEmaMaskIdx :=
    fun g idx val hidx => m7Get64Val_set64_ne val (Or.inl (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaSet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hltG _ 46 _ (by omega), hltG _ 44 _ (by omega),
      hltG _ 42 _ (by omega), hltG _ 40 _ (by omega)]
  · rw [hltG _ 54 _ (by omega), hltG _ 52 _ (by omega),
      hltG _ 50 _ (by omega), hltG _ 48 _ (by omega)]

private theorem fid_modeEmaGet_set_mask (gu : List (BitVec 32)) (mode : Nat)
    (idx : BitVec 64) :
    m7ModeEmaGet (m7Set64List gu m7GuEmaMaskIdx idx) mode = m7ModeEmaGet gu mode := by
  have hge : ∀ j, 40 ≤ j → m7Get64Val (m7Set64List gu m7GuEmaMaskIdx idx) j = m7Get64Val gu j :=
    fun j hj => m7Get64Val_set64_ne idx (Or.inr (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hge 40 (by omega), hge 42 (by omega), hge 44 (by omega), hge 46 (by omega)]
  · rw [hge 48 (by omega), hge 50 (by omega), hge 52 (by omega), hge 54 (by omega)]

private theorem fid_bit0_or_left {a b : BitVec 64} (h : (a &&& 1#64) ≠ 0#64) :
    ((a ||| b) &&& 1#64) ≠ 0#64 := by
  intro hc
  have h1 := congrArg (fun x : BitVec 64 => x[0]) hc
  simp only [BitVec.getElem_and, BitVec.getElem_or,
    show (1#64 : BitVec 64)[0] = true by decide, Bool.and_true,
    show (0#64 : BitVec 64)[0] = false by decide, Bool.or_eq_false_iff] at h1
  apply h
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rcases k with rfl | k
  · simp [h1.1]
  · have hb : (1#64 : BitVec 64)[k + 1] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#64 : BitVec 64).toNat = 1 by decide,
        Nat.testBit_succ]
      simp
    simp only [BitVec.getElem_and, BitVec.getElem_zero, hb, Bool.and_false]

private theorem fid_ema_swap_s2f_facts (sc : FullScratch) (hgu : sc.glue_used.length = 64) :
    let sc' := m7EmaSwapSc sc 1#64 0#64
    sc'.stable = 0#64 ∧
      m7ModeEmaGet sc'.glue_used 1 =
        (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp) ∧
      ((m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic ∧
        (m7Get64Val sc.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
       let saved := m7ModeEmaGet sc.glue_used 0
       sc'.ema_fast_biased = saved.1 ∧ sc'.ema_fast_exp = saved.2.1 ∧
       sc'.ema_slow_biased = saved.2.2.1 ∧ sc'.ema_slow_exp = saved.2.2.2) := by
  rw [m7EmaSwapSc_eq]; dsimp only
  simp only [show ((1#64 : BitVec 64) ≠ 0#64) = True by decide,
    show ((0#64 : BitVec 64) ≠ 0#64) = False by decide, ↓reduceIte]
  let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 1 }
  have hgu0 : gu0.length = 64 := (m7StateInitGu_length _).trans hgu
  let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
  let gu1 := m7ModeEmaSet gu0 1 curV
  let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| 1#64 <<< 1
  refine ⟨?_, ?_, ?_⟩
  · rw [fid_apply_ite FullScratch.stable]; exact fid_ite_eq _ rfl rfl
  · by_cases hcond : mask &&& 1#64 <<< 0 ≠ 0#64
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_true hc', ↓reduceIte, fid_modeEmaGet_set_mask]
      exact m7ModeEmaGet_set_self curV hgu0
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_false hc', ↓reduceIte, fid_modeEmaGet_set_mask]
      rw [m7ModeEmaGet_set_other _ (by decide : (0 = 0) ≠ (1 = 0))]
      exact m7ModeEmaGet_set_self curV hgu0
  · rintro ⟨hmag, hmask⟩
    have hgu0_eq : gu0 = sc.glue_used := m7StateInitGu_of_magic hmag
    have hmask1 : m7Get64Val gu1 m7GuEmaMaskIdx = m7Get64Val sc.glue_used m7GuEmaMaskIdx := by
      dsimp only [gu1]; rw [fid_get64_emaSet_mask, hgu0_eq]
    have hcond : mask &&& 1#64 <<< 0 ≠ 0#64 := by
      rw [show (1#64 <<< 0 : BitVec 64) = 1#64 by decide]
      dsimp only [mask]; rw [hmask1]
      exact fid_bit0_or_left hmask
    have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
    simp only [eq_true hc', ↓reduceIte]
    have hnw : m7ModeEmaGet gu1 0 = m7ModeEmaGet sc.glue_used 0 := by
      dsimp only [gu1]; rw [m7ModeEmaGet_set_other _ (by decide : (1 = 0) ≠ (0 = 0)), hgu0_eq]
    rw [hnw]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem fid_modeEmaGet1_set64_ge56 (gu : List (BitVec 32)) {idx : Nat} (val : BitVec 64)
    (hidx : 56 ≤ idx) :
    m7ModeEmaGet (m7Set64List gu idx val) 1 = m7ModeEmaGet gu 1 := by
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma1FbIdx_eq]; dsimp only
  simp only [show (1 = 0) = False by decide, ↓reduceIte]
  rw [m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega))]

private theorem fid_call_set64_randec {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {s0 s : FullState} {idx val : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, val, ()))
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hidx_lo : 56 ≤ idx.toNat) (hidx_hi : idx.toNat < 63)
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hps : FullProbeScratchPres s0 s)
    (hpre : M7GuPrefixPres s0 s) (hinit : M7StateInitOk s.scratch.glue_used)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      s'.core = s0.core → s'.LengthsOk c → FullProbeScratchPres s0 s' →
      M7GuPrefixPres s0 s' → M7StateInitOk s'.scratch.glue_used →
      m7ModeEmaGet s'.scratch.glue_used 1 = m7ModeEmaGet s.scratch.glue_used 1 →
      s'.scratch.stable = s.scratch.stable →
      s'.scratch.conflicts = s.scratch.conflicts →
      s'.scratch.ema_fast_biased = s.scratch.ema_fast_biased →
      s'.scratch.ema_fast_exp = s.scratch.ema_fast_exp →
      s'.scratch.ema_slow_biased = s.scratch.ema_slow_biased →
      s'.scratch.ema_slow_exp = s.scratch.ema_slow_exp →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ (m7Set64Spec_of hlen hm fun hlen' m' hm' => ?_)
  dsimp only at hlen' hm'
  simp only [hidx_hi, ↓reduceIte] at hlen' hm'
  let sc' : FullScratch :=
    { s.scratch with glue_used := m7Set64List s.scratch.glue_used idx.toNat val }
  let s' : FullState := { s with scratch := sc' }
  have hps' : FullProbeScratchPres s0 s' := hps
  have hpre' : M7GuPrefixPres s0 s' :=
    M7GuPrefixPres.trans hpre (M7GuPrefixPres.of_set64 val (by omega))
  have hinit' : M7StateInitOk s'.scratch.glue_used :=
    M7StateInitOk.of_set64 hinit (by omega) val
  have hema1' : m7ModeEmaGet s'.scratch.glue_used 1 = m7ModeEmaGet s.scratch.glue_used 1 :=
    fid_modeEmaGet1_set64_ge56 s.scratch.glue_used val hidx_lo
  exact hk s' m' hcore hlen' hps' hpre' hinit' hema1' rfl rfl rfl rfl rfl rfl hm'

/-- WP proof for `full_switch_mode_fid` against `FullM7Search.m7SwitchModeSpec`,
additionally resetting `M7_GU_RANDEC_{REM,LIM,SEQ,CFL}` (`glue_used[56..63]`) on focused switch. -/

theorem m8_switch_mode_m7_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7SwitchModeSpec a m Q X → Func.wp Γ m8_switch_mode_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, hc_eq, hlen, hm, hQ⟩ := m7SwitchModeSpec_elim hspec
  dsimp only at hc_eq; subst hc_eq
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  let P : Tup Val [i64, i64] → Mem 64 → Prop := fun (om, nm, _) mJ =>
    ∃ sJ : FullState,
      sJ.core = s.core ∧ sJ.LengthsOk c ∧ FullProbeScratchPres s sJ ∧
      om = (if s.scratch.stable = 0#64 then 0#64 else 1#64) ∧
      nm = (if s.scratch.stable = 0#64 then 1#64 else 0#64) ∧
      (s.scratch.stable = 0#64 → s.scratch.mode_confl_lim ≤ s.scratch.conflicts) ∧
      (s.scratch.stable ≠ 0#64 →
        s.scratch.mode_tick_lim ≤ s.scratch.search_ticks ∧ M7GuPrefixPres s sJ ∧
        sJ.scratch.glue_used = s.scratch.glue_used ∧
        sJ.scratch.ema_fast_biased = s.scratch.ema_fast_biased ∧
        sJ.scratch.ema_fast_exp = s.scratch.ema_fast_exp ∧
        sJ.scratch.ema_slow_biased = s.scratch.ema_slow_biased ∧
        sJ.scratch.ema_slow_exp = s.scratch.ema_slow_exp) ∧
      (FullMem c sJ ⋆ R) mJ
  refine wp_join_group P ?_ ?_
  · rintro Js ⟨om, nm, ⟨⟩⟩ mJ ⟨sJ, hcJ, hlenJ, hpsJ, hom, hnm, hf2s, hs2f, hmJ⟩
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64
      mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c := fid_len_scalars hlenJ
    fs_call hEmaSwap
    refine m7EmaSwapSpec_of hlenJ1 (by assumption) fun hlenSw hpreSw hinitSw mSw hmSw => ?_
    let sSw : FullState := { sJ1 with scratch := m7EmaSwapSc sJ1.scratch om nm }
    let Pret : Tup Val [] → Mem 64 → Prop := fun _ mRet =>
      ∃ sRet : FullState,
        sRet.core = s.core ∧ sRet.LengthsOk c ∧ FullProbeScratchPres s sRet ∧
        (s.scratch.stable = 0#64 →
          M7StateInitOk sRet.scratch.glue_used ∧ sRet.scratch.stable = 1#64) ∧
        (s.scratch.stable ≠ 0#64 →
          M7GuPrefixPres s sRet ∧ M7StateInitOk sRet.scratch.glue_used ∧
          m7ModeEmaGet sRet.scratch.glue_used 1 =
            (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
             s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
          sRet.scratch.stable = 0#64 ∧
          ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
            (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
           let saved := m7ModeEmaGet s.scratch.glue_used 0
           sRet.scratch.ema_fast_biased = saved.1 ∧ sRet.scratch.ema_fast_exp = saved.2.1 ∧
           sRet.scratch.ema_slow_biased = saved.2.2.1 ∧
           sRet.scratch.ema_slow_exp = saved.2.2.2)) ∧
        (FullMem c sRet ⋆ R) mRet
    refine wp_join_group Pret ?_ ?_
    · rintro Js_r ⟨⟩ mRet ⟨sRet, hcRet, hlenRet, hpsRet, hrf2s, hrs2f, hmRet⟩
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      refine hQ sRet mRet hcRet hlenRet hpsRet ?_ ?_ ?_ hmRet
      · intro hEarly
        exfalso
        rcases hEarly with ⟨hst0, hlt⟩ | ⟨hstne, hlt⟩
        · have hle := hf2s hst0
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
        · have hle := (hs2f hstne).1
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
      · rintro ⟨hst0, _⟩; exact hrf2s hst0
      · rintro ⟨hstne, _⟩; exact hrs2f hstne
    · intro Js_r hJs_r
      have hpsSw : FullProbeScratchPres s sSw :=
        fid_probePres_emaSwap sJ1.scratch om nm hpsJ rfl
      fs_nojnz
      fs_jnz hstab0
      · simp only [beq_iff_eq] at hstab0
        have hstne : s.scratch.stable ≠ 0#64 := by
          intro hst0
          have hom0 : om = 0#64 := by simp [hom, hst0]
          have hnm1 : nm = 1#64 := by simp [hnm, hst0]
          have h1 : sSw.scratch.stable = 1#64 := by
            dsimp only [sSw]; rw [hom0, hnm1]; exact fid_ema_swap_f2s_stable _
          rw [h1] at hstab0
          exact absurd hstab0 (by decide)
        obtain ⟨_, hpreJ, hguJ, hfbJ, hfeJ, hsbJ, hseJ⟩ := hs2f hstne
        have hom1 : om = 1#64 := by simp [hom, hstne]
        have hnm0 : nm = 0#64 := by simp [hnm, hstne]
        have hguSw : sJ1.scratch.glue_used.length = 64 := hlenJ1.scratch_ok.glue_used_len
        have hfacts := fid_ema_swap_s2f_facts sJ1.scratch hguSw
        have heq_f : sSw.scratch = m7EmaSwapSc sJ1.scratch 1#64 0#64 := by
          dsimp only [sSw]; rw [hom1, hnm0]
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mRl => mRl = mSw) ?_ ?_
        · rintro J_rl ⟨rs, ⟨⟩⟩ mRl rfl
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          let sRet0 : FullState := { sSw with scratch := { sSw.scratch with
            restart_limit := sSw.scratch.conflicts + rs } }
          have hlenRet0 : sRet0.LengthsOk c := fid_len_scalars hlenSw
          have hpre0 : M7GuPrefixPres s sRet0 :=
            M7GuPrefixPres.trans hpreJ (@M7GuPrefixPres.congr_glue sJ1 sSw sJ sRet0 rfl rfl hpreSw)
          have hema1_0 : m7ModeEmaGet sRet0.scratch.glue_used 1 =
              (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
               s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) := by
            change m7ModeEmaGet sSw.scratch.glue_used 1 = _
            rw [heq_f, hfacts.2.1]
            change (sJ.scratch.ema_fast_biased, sJ.scratch.ema_fast_exp,
              sJ.scratch.ema_slow_biased, sJ.scratch.ema_slow_exp) = _
            rw [hfbJ, hfeJ, hsbJ, hseJ]
          have hst0_0 : sRet0.scratch.stable = 0#64 := by
            change sSw.scratch.stable = 0#64; rw [heq_f]; exact hfacts.1
          have hmag_eq : m7Get64Val sJ1.scratch.glue_used m7GuMagicIdx =
              m7Get64Val s.scratch.glue_used m7GuMagicIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hmsk_eq : m7Get64Val sJ1.scratch.glue_used m7GuEmaMaskIdx =
              m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hget0_eq : m7ModeEmaGet sJ1.scratch.glue_used 0 =
              m7ModeEmaGet s.scratch.glue_used 0 := by
            change m7ModeEmaGet sJ.scratch.glue_used 0 = _; rw [hguJ]
          have hsaved0 :
              ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
                (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
               let saved := m7ModeEmaGet s.scratch.glue_used 0
               sRet0.scratch.ema_fast_biased = saved.1 ∧ sRet0.scratch.ema_fast_exp = saved.2.1 ∧
               sRet0.scratch.ema_slow_biased = saved.2.2.1 ∧
               sRet0.scratch.ema_slow_exp = saved.2.2.2) := by
            intro ⟨hm1, hm2⟩
            have hsav := hfacts.2.2 ⟨by rw [hmag_eq]; exact hm1, by rw [hmsk_eq]; exact hm2⟩
            rw [← hget0_eq]
            change sSw.scratch.ema_fast_biased = _ ∧ sSw.scratch.ema_fast_exp = _ ∧
              sSw.scratch.ema_slow_biased = _ ∧ sSw.scratch.ema_slow_exp = _
            rw [heq_f]; exact hsav
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenRet0 hcJ hpsSw
            hpre0 hinitSw (by assumption) fun sR1 mR1 hcR1 hlenR1 hpsR1 hpreR1 hinitR1 hemaR1
            hstR1 _ hfb1 hfe1 hsb1 hse1 hmR1 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR1 hcR1 hpsR1
            hpreR1 hinitR1 hmR1 fun sR2 mR2 hcR2 hlenR2 hpsR2 hpreR2 hinitR2 hemaR2
            hstR2 _ hfb2 hfe2 hsb2 hse2 hmR2 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR2 hcR2 hpsR2
            hpreR2 hinitR2 hmR2 fun sR3 mR3 hcR3 hlenR3 hpsR3 hpreR3 hinitR3 hemaR3
            hstR3 _ hfb3 hfe3 hsb3 hse3 hmR3 => ?_
          c0_hsteps_nogrp
          refine fid_call_set64_randec rfl hSet64 (by decide) (by decide) hlenR3 hcR3 hpsR3
            hpreR3 hinitR3 hmR3 fun sR4 mR4 hcR4 hlenR4 hpsR4 hpreR4 hinitR4 hemaR4
            hstR4 _ hfb4 hfe4 hsb4 hse4 hmR4 => ?_
          c0_hsteps_nogrp
          refine hJs_r () mR4 ⟨sR4, hcR4, hlenR4, hpsR4, fun h0 => absurd h0 hstne, fun _ => ?_,
            hmR4⟩
          refine ⟨hpreR4, hinitR4, ?_, ?_, fun hcond => ?_⟩
          · rw [hemaR4, hemaR3, hemaR2, hemaR1, hema1_0]
          · rw [hstR4, hstR3, hstR2, hstR1, hst0_0]
          · have hs0 := hsaved0 hcond
            rw [hfb4, hfe4, hsb4, hse4, hfb3, hfe3, hsb3, hse3, hfb2, hfe2, hsb2, hse2,
              hfb1, hfe1, hsb1, hse1]
            exact hs0
        · intro J_rl hJ_rl
          fs_nojnz
          fs_jnz hrg0
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = mSw) ?_ ?_
            · rintro J_r2 ⟨rc, ⟨⟩⟩ m2 hm2
              subst m2; rw [Blocks.get_here]; c0_hsteps_nogrp
              fs_call hIlog; intro r _ _
              refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = mSw) ?_ ?_
              · rintro J_r3 ⟨d, ⟨⟩⟩ m3 hm3
                subst m3; rw [Blocks.get_here]; c0_hsteps_nogrp
                exact hJ_rl (d, ()) mSw rfl
              · intro J_r3 hJ_r3; fs_nojnz
                fs_jnz hdg1 <;> c0_hsteps_nogrp <;> exact hJ_r3 _ mSw rfl
            · intro J_r2 hJ_r2; fs_nojnz
              fs_jnz hrlim <;> c0_hsteps_nogrp <;> exact hJ_r2 _ mSw rfl
          · c0_hsteps_nogrp; exact hJ_rl (1#64, ()) mSw rfl
      · simp only [beq_eq_false_iff_ne] at hstab0
        have hst0 : s.scratch.stable = 0#64 := by
          by_cases hst : s.scratch.stable = 0#64
          · exact hst
          · exfalso
            have hom1 : om = 1#64 := by simp [hom, hst]
            have hnm0 : nm = 0#64 := by simp [hnm, hst]
            have h0 : sSw.scratch.stable = 0#64 := by
              dsimp only [sSw]; rw [hom1, hnm0]
              exact (fid_ema_swap_s2f_facts sJ1.scratch hlenJ1.scratch_ok.glue_used_len).1
            exact hstab0 h0
        have hom0 : om = 0#64 := by simp [hom, hst0]
        have hnm1 : nm = 1#64 := by simp [hnm, hst0]
        have h1 : sSw.scratch.stable = 1#64 := by
          dsimp only [sSw]; rw [hom0, hnm1]; exact fid_ema_swap_f2s_stable _
        c0_hsteps_nogrp
        exact hJs_r () mSw ⟨sSw, hcJ, hlenSw, hpsSw,
          fun _ => ⟨hinitSw, h1⟩, fun hne => absurd hst0 hne, hmSw⟩
  · intro Js hJs
    fs_nojnz
    fs_jnz hst0
    · simp only [beq_iff_eq] at hst0
      fs_nojnz
      fs_jnz hconfl
      · simp only [BitVec.ult, decide_eq_true_eq] at hconfl
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (fid_probePres_refl s) (fun _ => rfl)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hconfl))
          (fun ⟨hne, _⟩ => absurd hst0 hne) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hconfl
        have hle_confl : s.scratch.mode_confl_lim ≤ s.scratch.conflicts :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hconfl)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
        refine wp_join_group (ts := [i64])
          (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_d ⟨delta, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          let s2 : FullState := { s1 with scratch := { s1.scratch with
            mode_tick_lim := s1.scratch.search_ticks + delta
            mode_saved_ticks := s1.scratch.search_ticks } }
          refine wp_join_group (ts := [i64])
            (fun _ m2 => (FullMem c s2 ⋆ R) m2) ?_ ?_
          · rintro J_l ⟨lim, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s3 : FullState := { s2 with scratch := { s2.scratch with
              rel_wait := lim, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
            have hlen3 : s3.LengthsOk c := fid_len_scalars hlen
            have hps3 : FullProbeScratchPres s s3 := fid_probePres_refl s
            refine wp_loop_inv (ts := [i64, i64])
              (fun (hl, i, ()) mL => ∃ hp ps : List (BitVec 32),
                hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
                hl.toNat ≤ i.toNat ∧ i.toNat ≤ s.core.cur_vars ∧
                (FullMem c { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps } } ⋆ R) mL)
              (fun (_, i, ()) _ => s.core.cur_vars - i.toNat) ?_ ?_
            · intro J3 hJ3; c0_hsteps_nogrp
              exact hJ3 (0#64, 0#64, ()) _ ⟨s3.scratch.heap, s3.scratch.pos,
                hsok.heap_len_arr, hsok.pos_len, by simp, Nat.zero_le _, by assumption⟩
            · rintro J3 ⟨hl, i, ⟨⟩⟩ mL ⟨hp, ps, hhp, hps_len, hle_hi, hi_le, hmL⟩ hJ3
              rw [Blocks.get_here]; fs_nojnz
              fs_jnz hilt
              · simp only [BitVec.ult, decide_eq_true_eq] at hilt
                have hi_lt : i.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hilt
                  rw [Nat.mod_eq_of_lt (by omega)] at hilt; exact hilt
                have hi_mx : i.toNat < c.max_vars := by omega
                refine wp_join_group (ts := [i64])
                  (fun (hl', ()) mN => ∃ hp' ps' : List (BitVec 32),
                    hp'.length = c.max_vars ∧ ps'.length = c.max_vars ∧
                    hl'.toNat ≤ i.toNat + 1 ∧
                    (FullMem c { s3 with scratch :=
                      { s3.scratch with heap := hp', pos := ps' } } ⋆ R) mN)
                  ?_ ?_
                · rintro J_nx ⟨hl', ⟨⟩⟩ mN ⟨hp', ps', hhp', hps', hle', hmN⟩
                  rw [Blocks.get_here]; c0_hsteps_nogrp
                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := fs_bv64_add1 (by omega)
                  exact hJ3 (hl', i + 1#64, ()) mN (by dsimp only; rw [hi1]; omega)
                    ⟨hp', ps', hhp', hps', by rw [hi1]; exact hle', by omega, hmN⟩
                · intro J_nx hJ_nx
                  have hfl_lt : i.toNat < s3.core.flags.length := by rw [hok.flags_len]; omega
                  fs_nojnz
                  fs_jnz hact
                  · have hhp_lt : hl.toNat < hp.length := by omega
                    have hps_lt : i.toNat < ps.length := by omega
                    rw [wp_let_mul_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    rw [wp_let_add_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    c0_hsteps_nogrp
                    have hhl1 : (hl + 1#64).toNat = hl.toNat + 1 := fs_bv64_add1 (by omega)
                    exact hJ_nx (hl + 1#64, ()) _ ⟨hp.set hl.toNat (i.setWidth 32),
                      ps.set i.toNat (hl.setWidth 32), by simpa using hhp,
                      by simpa using hps_len, by omega, by assumption⟩
                  · have hps_lt : i.toNat < ps.length := by omega
                    c0_hsteps_nogrp
                    exact hJ_nx (hl, ()) _ ⟨hp, ps.set i.toNat 0xFFFFFFFF#32, hhp,
                      by simpa using hps_len, by omega, by assumption⟩
              · c0_hsteps_nogrp
                have hhl_le : hl.toNat ≤ c.max_vars := by omega
                let s4 : FullState := { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps, heap_len := hl.toNat } }
                have hlen4 : s4.LengthsOk c :=
                  ⟨hlen3.core_ok, { hlen3.scratch_ok with heap_len_arr := hhp, pos_len := hps_len }⟩
                refine wp_loop_inv (ts := [i64])
                  (fun (k, ()) mD => ∃ sD : FullState,
                    sD.core = s.core ∧ sD.LengthsOk c ∧ FullProbeScratchPres s sD ∧
                    k.toNat ≤ c.max_vars ∧ (FullMem c sD ⋆ R) mD)
                  (fun (k, ()) _ => k.toNat) ?_ ?_
                · intro J4 hJ4; c0_hsteps_nogrp
                  exact hJ4 (hl >>> 1#64, ()) _ ⟨s4, rfl, hlen4, hps3,
                    le_trans (fs_bv64_lshr1_le hl) hhl_le, by assumption⟩
                · rintro J4 ⟨k, ⟨⟩⟩ mD ⟨sD, hcD, hlenD, hpsD, hk_le, hmD⟩ hJ4
                  rw [Blocks.get_here]; fs_nojnz
                  fs_jnz hkpos
                  · simp only [BitVec.ult, decide_eq_true_eq] at hkpos
                    have hk_gt : 0 < k.toNat := by simpa using hkpos
                    have hk1 : (k - 1#64).toNat = k.toNat - 1 :=
                      fs_bv64_sub1 (fun h => by simp [h] at hk_gt)
                    have hk1_hp : (k - 1#64).toNat < sD.scratch.heap.length := by
                      rw [hlenD.scratch_ok.heap_len_arr]; omega
                    c0_hsteps_nogrp
                    fs_call hHeapDown
                    refine ⟨c, sD, R, rfl, hlenD, hmD, fun () sD' mD' hcD' hlenD' hpost hmD' => ?_⟩
                    rcases hpost with ⟨_, hpsD'⟩
                    have hcD'_eq : sD'.core = sD.core := hcD'
                    exact hJ4 (k - 1#64, ()) mD' (by dsimp only; rw [hk1]; omega)
                      ⟨sD', hcD'_eq.trans hcD, hlenD', fid_probePres_trans hpsD hpsD',
                        by rw [hk1]; omega, hmD'⟩
                  · c0_hsteps_nogrp
                    exact hJs (0#64, 1#64, ()) mD ⟨sD, hcD, hlenD, hpsD,
                      by simp [hst0], by simp [hst0], fun _ => hle_confl,
                      fun hne => absurd hst0 hne, hmD⟩
          · intro J_l hJ_l; fs_nojnz
            fs_jnz hlim1
            · fs_nojnz
              fs_jnz hlim2 <;> c0_hsteps_nogrp <;> exact hJ_l _ _ (by assumption)
            · c0_hsteps_nogrp; exact hJ_l _ _ (by assumption)
        · intro J_d hJ_d; fs_nojnz
          fs_jnz hdiff <;> c0_hsteps_nogrp <;> exact hJ_d _ _ (by assumption)
    · simp only [beq_eq_false_iff_ne] at hst0
      fs_nojnz
      fs_jnz hticks
      · simp only [BitVec.ult, decide_eq_true_eq] at hticks
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (fid_probePres_refl s) (fun _ => rfl)
          (fun ⟨h0, _⟩ => absurd h0 hst0)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hticks)) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hticks
        have hle_ticks : s.scratch.mode_tick_lim ≤ s.scratch.search_ticks :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hticks)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        refine wp_join_group (ts := [i64]) (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_c ⟨cc, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          fs_call hLog10
          refine m7Log10Q16Spec_of fun r _ _ => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1 ⋆ R) m2) ?_ ?_
          · rintro J_d ⟨delta, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s4 : FullState := { s1 with scratch := { s1.scratch with
              mode_confl_lim := s1.scratch.conflicts + delta
              mode_saved_ticks := s1.scratch.search_ticks
              q_search_idx := s1.scratch.q_last } }
            refine wp_join_group (ts := [])
              (fun _ m5 => ∃ qss : BitVec 64,
                (FullMem c { s4 with scratch :=
                  { s4.scratch with q_search_stamp := qss } } ⋆ R) m5) ?_ ?_
            · rintro J_q ⟨⟩ m5 ⟨qss, hm5⟩
              rw [Blocks.get_here]; c0_hsteps_nogrp
              let sJ : FullState := { s4 with scratch :=
                { s4.scratch with q_search_stamp := qss } }
              have hlenJ : sJ.LengthsOk c := fid_len_scalars hlen
              exact hJs (1#64, 0#64, ()) m5 ⟨sJ, rfl, hlenJ, fid_probePres_refl s,
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                fun h0 => absurd h0 hst0,
                fun _ => ⟨hle_ticks,
                  @M7GuPrefixPres.congr_glue s s s sJ rfl rfl (M7GuPrefixPres.refl s),
                  rfl, rfl, rfl, rfl, rfl⟩, hm5⟩
            · intro J_q hJ_q; fs_nojnz
              fs_jnz hqlt
              · simp only [BitVec.ult, decide_eq_true_eq] at hqlt
                have hq_nat : s.scratch.q_last.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hqlt
                  rw [Nat.mod_eq_of_lt (by omega)] at hqlt; exact hqlt
                have hq_len : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
                  rw [hsok.q_stamp_len]; omega
                c0_hsteps_nogrp; exact hJ_q () _ ⟨_, by assumption⟩
              · c0_hsteps_nogrp; exact hJ_q () _ ⟨s4.scratch.q_search_stamp, by assumption⟩
          · intro J_d hJ_d; fs_nojnz
            fs_jnz hcle
            · c0_hsteps_nogrp; exact hJ_d _ _ (by assumption)
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mx => (FullMem c s1 ⋆ R) mx) ?_ ?_
              · rintro J_x ⟨cv, ⟨⟩⟩ mx hmx2
                rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJ_d _ _ hmx2
              · intro J_x hJ_x; fs_nojnz
                fs_jnz hcgt <;> c0_hsteps_nogrp <;> exact hJ_x _ _ (by assumption)
        · intro J_c hJ_c; fs_nojnz
          fs_jnz hcc <;> c0_hsteps_nogrp <;> exact hJ_c _ _ (by assumption)

end BumpAnalyzedProof
end M8SwitchMode


section M8CongIte
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open scoped FullArenaTactics Full.FullCongTactics
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
private theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem fullWitnessInv_with_tmp_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) (lm' : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem litNeg_div2_m6 (n : Nat) : litNeg n / 2 = n / 2 := litVar_litNeg n

private theorem xor_bit01_lt_div2_m6 {cv : Nat} (x m : BitVec 32) (hx : x.toNat < 2 * cv) :
    (x ^^^ (m &&& 1#32)).toNat < 2 * cv ∧ (x ^^^ (m &&& 1#32)).toNat / 2 = x.toNat / 2 := by
  have hm_lt : (m &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  have hcases : (m &&& 1#32).toNat = 0 ∨ (m &&& 1#32).toNat = 1 := by omega
  rcases hcases with h0 | h1
  · have hb : (m &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0
    rw [hb]; simp [hx]
  · have hb : (m &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq h1
    rw [hb, FullCongHelpers.bv32_xor1_eq_litNeg]
    exact ⟨bv32_xor1_lt_even hx, litNeg_div2_m6 _⟩

private theorem slice_pop_step_m6 {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem bv32_ne_of_div2_ne_m6 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    x ≠ y := by
  intro heq; subst heq; exact h rfl

private theorem div2_ne_of_xor1_m6 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    x.toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, litNeg_div2_m6]; exact h

private theorem div2_ne_of_xor1_l_m6 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ y.toNat / 2 := by
  rw [bv32_xor1_litNeg, litNeg_div2_m6]; exact h

private theorem div2_ne_of_xor1_both_m6 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, bv32_xor1_litNeg, litNeg_div2_m6, litNeg_div2_m6]; exact h

private theorem cur_vars_ge3_of_distinct_m6 {v0 v1 v2 n : Nat}
    (h0 : v0 < n) (h1 : v1 < n) (h2 : v2 < n)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) : 3 ≤ n := by
  have hle := nodup_lt_length_le (n := n) (xs := [v0, v1, v2])
    (by simp [h01, h02, h12])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
  simpa using hle

private theorem closed_cons_get_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ts : List Ty} {b : Tup Val ts → Expr Val Cont rs} {Js : Tup Cont [ts]}
    (h : Closed Γ Q X (.cons b .nil) Js) (xs : Tup Val ts) (m : Mem 64)
    (hwp : wp Γ Q X (b xs) m) : Js.1 xs m := h.1 xs m hwp

private theorem bv64_add_n_m6 {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := Nat.mod_eq_of_lt h

private theorem ite_pick_e_ok_m6 {F_cur : List (List Nat)} {cv : Nat}
    {c_lit y l0 l1 l2 la lb lc : BitVec 32}
    (hcl : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat, l2.toNat]))
    (hnd : l0.toNat / 2 ≠ l1.toNat / 2 ∧ l0.toNat / 2 ≠ l2.toNat / 2 ∧
      l1.toNat / 2 ≠ l2.toNat / 2)
    (hlt : ∀ x ∈ [l0.toNat, l1.toNat, l2.toNat], x < 2 * cv)
    (h1 : la = c_lit) (h2 : lb = y ^^^ 1)
    (hcase : (la = l0 ∧ lb = l1 ∧ lc = l2) ∨ (la = l0 ∧ lb = l2 ∧ lc = l1) ∨
             (la = l1 ∧ lb = l0 ∧ lc = l2) ∨ (la = l1 ∧ lb = l2 ∧ lc = l0) ∨
             (la = l2 ∧ lb = l0 ∧ lc = l1) ∨ (la = l2 ∧ lb = l1 ∧ lc = l0)) :
    lc.toNat < 2 * cv ∧ lc.toNat / 2 ≠ c_lit.toNat / 2 ∧ lc.toNat / 2 ≠ y.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg y.toNat, c_lit.toNat, lc.toNat]) := by
  have hny : (y ^^^ 1 : BitVec 32).toNat = litNeg y.toNat := bv32_xor1_litNeg y
  have hdiv_ny : (y ^^^ 1 : BitVec 32).toNat / 2 = y.toNat / 2 := by rw [hny, litNeg_div2_m6]
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    (subst h1 h2; refine ⟨hlt _ (by simp), by omega, by rw [← hdiv_ny]; omega,
      entails_perm_clause (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rw [← hny]; rcases hx with rfl | rfl | rfl <;> simp) hcl⟩)

private theorem m6_ite_emit_gateSeq {F_cur : List (List Nat)} {cur_vars cap g_len : Nat}
    {scr : List (BitVec 32)} {y2 c1 t2 e2 : BitVec 32}
    (hscrl : scr.length = cap) (hg5_le : g_len + 5 ≤ cap) (hcv3 : 3 ≤ cur_vars)
    (hy2_lt : y2.toNat < 2 * cur_vars) (hc1_lt : c1.toNat < 2 * cur_vars)
    (ht2_lt : t2.toNat < 2 * cur_vars) (he2_lt : e2.toNat < 2 * cur_vars)
    (hite2 : IteGateDef (cnfOfClauses F_cur) y2.toNat c1.toNat t2.toNat e2.toNat)
    (hseq0 : M6GateSeqOk F_cur cur_vars scr g_len 0) :
    let scr5 := ((((scr.set g_len y2).set (g_len + 1) ((2#32 <<< 28) ||| 3#32)).set
      (g_len + 2) c1).set (g_len + 3) t2).set (g_len + 4) e2
    scr5.length = cap ∧ (∀ idx < g_len, scr5[idx]? = scr[idx]?) ∧
      M6GateSeqOk F_cur cur_vars scr5 (g_len + 5) 0 := by
  intro scr5
  have hlen5 : scr5.length = cap := by simp [scr5, hscrl]
  have hpref : ∀ idx < g_len, scr5[idx]? = scr[idx]? := fun idx hi => by
    simp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
  have h0 : scr5[g_len]? = some y2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have h1 : scr5[g_len + 1]? = some ((2#32 <<< 28) ||| 3#32) := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
  have h2 : scr5[g_len + 2]? = some c1 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h3 : scr5[g_len + 3]? = some t2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h4 : scr5[g_len + 4]? = some e2 := by
    simp only [scr5]; rw [List.getElem?_set_self (by simp [hscrl]; omega)]
  have hg_at : M6GateAt F_cur cur_vars scr5 (g_len + 5) g_len := by
    refine ⟨y2, (2#32 <<< 28) ||| 3#32, h0, h1, hy2_lt, by show g_len + 2 + 3 ≤ g_len + 5; omega,
      hcv3, by decide, fun k hk => ?_,
      Or.inr (Or.inr ⟨rfl, rfl, by rw [h2, h3, h4]; simpa using hite2⟩)⟩
    have hk3 : k < 3 := hk
    match k with
    | 0 => exact ⟨c1, h2, hc1_lt⟩
    | 1 => exact ⟨t2, h3, ht2_lt⟩
    | 2 => exact ⟨e2, h4, he2_lt⟩
    | _ + 3 => omega
  refine ⟨hlen5, hpref, m6GateSeqOk_append (by omega) hpref (.step hg_at ?_) hseq0⟩
  simpa [h1] using M6GateSeqOk.done

private theorem bv32_even_or_bit_toNat_m6 (y b : BitVec 32) :
    ((y &&& ~~~1#32) ||| (b &&& 1#32)).toNat = 2 * (y.toNat / 2) + b.toNat % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_or, Nat.testBit_or, m6_bv32_and_not1_toNat, BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32).toNat.testBit 0 = true := by decide
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [hb] <;> omega
  | succ k =>
    have h0 : (1#32 : BitVec 32).toNat.testBit (k + 1) = false := by
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0, Bool.and_false, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega

private theorem litSign_of_mod2_m6 (n : Nat) : litSign n = decide (n % 2 = 1) := by
  unfold litSign; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem xor_emit_sound_m6 {f : CNF Nat} {cur_vars : Nat} {x0 x1 x2 : BitVec 32}
    (hx0 : x0.toNat < 2 * cur_vars) (hx1 : x1.toNat < 2 * cur_vars)
    (hx2 : x2.toNat < 2 * cur_vars)
    (hxor : XorGateDef f (litNeg x0.toNat) x1.toNat x2.toNat) :
    let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
    let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32
    lhs.toNat < 2 * cur_vars ∧ r0.toNat < 2 * cur_vars ∧ r1.toNat < 2 * cur_vars ∧
    XorListGateDef f lhs.toNat [r0.toNat, r1.toNat] ∧
    XorListGateDef f lhs.toNat [r1.toNat, r0.toNat] := by
  intro lhs r0 r1
  have hlhs_n : lhs.toNat =
      2 * ((x0 ^^^ 1#32).toNat / 2) + (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 :=
    bv32_even_or_bit_toNat_m6 (x0 ^^^ 1#32) (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2)
  have hr0_n : r0.toNat = 2 * (x1.toNat / 2) := m6_bv32_and_not1_toNat x1
  have hr1_n : r1.toNat = 2 * (x2.toNat / 2) := m6_bv32_and_not1_toNat x2
  have hx0n_div : (x0 ^^^ 1#32).toNat / 2 = x0.toNat / 2 := by
    rw [FullCongHelpers.bv32_xor1_eq_litNeg, litNeg_div2_m6]
  have heval_eq : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α r0.toNat != evalLitVal α r1.toNat) := by
    intro α hα
    have hv := xorGateDef_eval hα hxor
    have hx0_eval : evalLitVal α (litNeg x0.toNat) =
        (α (x0.toNat / 2) != litSign (litNeg x0.toNat)) := by
      simp [evalLitVal, litVar, litNeg_div2_m6]
    have hx1_eval : evalLitVal α x1.toNat = (α (x1.toNat / 2) != litSign x1.toNat) := rfl
    have hx2_eval : evalLitVal α x2.toNat = (α (x2.toNat / 2) != litSign x2.toNat) := rfl
    have hr0_eval : evalLitVal α r0.toNat = α (x1.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr0_n]
    have hr1_eval : evalLitVal α r1.toNat = α (x2.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr1_n]
    have hvar_lhs : litVar lhs.toNat = x0.toNat / 2 := by
      simp only [litVar, hlhs_n, hx0n_div]; omega
    have hmod_xor : (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 =
        (((litNeg x0.toNat) % 2 ^^^ x1.toNat % 2) ^^^ x2.toNat % 2) := by
      rw [BitVec.toNat_xor, BitVec.toNat_xor, FullCongHelpers.bv32_xor1_eq_litNeg]
      have h1 := Nat.xor_mod_two_pow (a := (litNeg x0.toNat) ^^^ x1.toNat) (b := x2.toNat) (n := 1)
      have h2 := Nat.xor_mod_two_pow (a := litNeg x0.toNat) (b := x1.toNat) (n := 1)
      simpa using h1.trans (by rw [h2])
    have hsign_lhs : litSign lhs.toNat =
        ((litSign (litNeg x0.toNat) != litSign x1.toNat) != litSign x2.toNat) := by
      rw [litSign_of_mod2_m6, litSign_of_mod2_m6, litSign_of_mod2_m6, litSign_of_mod2_m6, hlhs_n]
      have hlm : (2 * ((x0 ^^^ 1#32).toNat / 2) +
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2) % 2 =
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 := by omega
      rw [hlm, hmod_xor]
      rcases Nat.mod_two_eq_zero_or_one (litNeg x0.toNat) with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one x1.toNat with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one x2.toNat with h2 | h2 <;>
        simp [h0, h1, h2]
    rw [evalLitVal, hvar_lhs, hsign_lhs, hr0_eval, hr1_eval]
    rw [hx0_eval, hx1_eval, hx2_eval] at hv
    cases ha0 : α (x0.toNat / 2) <;> cases ha1 : α (x1.toNat / 2) <;>
      cases ha2 : α (x2.toNat / 2) <;> cases hs0 : litSign (litNeg x0.toNat) <;>
      cases hs1 : litSign x1.toNat <;> cases hs2 : litSign x2.toNat <;> simp_all
  refine ⟨by omega, by omega, by omega,
    (fun α hα => by rw [xorEvalList_pair]; exact heval_eq α hα),
    (fun α hα => by
      rw [xorEvalList_pair, heval_eq α hα]
      cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl)⟩

private theorem xorGateDef_of_four_m6 {f : CNF Nat} {a b c : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b, c]))
    (h2 : f.EntailsClause (cnfClause [a, litNeg b, litNeg c]))
    (h3 : f.EntailsClause (cnfClause [litNeg a, b, litNeg c]))
    (h4 : f.EntailsClause (cnfClause [litNeg a, litNeg b, c])) :
    XorGateDef f (litNeg a) b c ∧ XorGateDef f (litNeg b) a c ∧ XorGateDef f (litNeg c) a b := by
  have h1' : XorGateDef f (litNeg a) b c :=
    ⟨entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h4,
     entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h3,
     by simpa [litNeg_litNeg] using h1,
     by simpa [litNeg_litNeg] using h2⟩
  refine ⟨h1', xorGateDef_of_eval_eq fun α hα => ?_, xorGateDef_of_eval_eq fun α hα => ?_⟩
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all


theorem m8_cong_try_xor_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, FullCongSpecs.fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X)
    (hEmitXor : ∀ args m Q X, m6CongEmitXorSpec args m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, m6CongTryXorIteSpec args m Q X →
      Func.wp Γ m8_cong_try_xor_ite_body args m Q X := by
  rintro ⟨h, a, b, cl, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hb_lt, hc_lt,
     hab_v, hac_v, hbc_v, hcl0_ent, hg_le, hgc_le, hseq0, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct_m6 (by omega) (by omega) (by omega) hab_v hac_v hbc_v
  have hna_lt : (a ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even ha_lt
  have hnb_lt : (b ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hb_lt
  have hnc_lt : (cl ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hc_lt
  have hdis_lit : ∀ x y : BitVec 32, x.toNat / 2 ≠ y.toNat / 2 → x ≠ y :=
    fun _ _ => bv32_ne_of_div2_ne_m6
  have hperm3 : ∀ {u v w u' v' w' : Nat},
      (u = u' ∨ u = v' ∨ u = w') → (v = u' ∨ v = v' ∨ v = w') → (w = u' ∨ w = v' ∨ w = w') →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u, v, w]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u', v', w']) :=
    fun hu hv hw_p hcl => entails_perm_clause (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> assumption) hcl
  have hret_glen : Q (g_len, ()) m0 :=
    hQ g_len s.scratch.scratch_buf m0 hscrl (Nat.le_refl _) (by omega) (fun _ _ => rfl) hseq0 hm0
  fc_to_group
  refine wp_join_group (ts := [i32]) (fun _ mj => m0 = mj) ?_ ?_
  · rintro _ ⟨mx1, ⟨⟩⟩ mj1 hmj1; subst mj1
    fc_to_group
    refine wp_join_group (ts := [i32]) (fun _ mj => m0 = mj) ?_ ?_
    · rintro _ ⟨mx, ⟨⟩⟩ mj2 hmj2; subst mj2
      fc_to_group
      refine wp_join_group (ts := []) (fun _ mj => m0 = mj) ?_ ?_
      · rintro _ ⟨⟩ mj3 hmj3; subst mj3
        fc_to_group
        refine wp_join_group (ts := []) (fun _ mj => m0 = mj) ?_ ?_
        · rintro _ ⟨⟩ mj4 hmj4; subst mj4
          fc_to_group
          refine wp_join_group (ts := []) (fun _ mj => m0 = mj) ?_ ?_
          · rintro _ ⟨⟩ mj5 hmj5; subst mj5
            fc_steps; c0_call hHasTern
            refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0,
              fun ok1 hok1 => ?_⟩
            fc_split
            · have ht1 : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
                simpa only [bv32_xor1_litNeg] using hok1 (by grind)
                  (hdis_lit _ _ (div2_ne_of_xor1_m6 hab_v))
                  (hdis_lit _ _ (div2_ne_of_xor1_m6 hac_v))
                  (hdis_lit _ _ (div2_ne_of_xor1_both_m6 hbc_v))
              fc_steps; c0_call hHasTern
              refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                fun ok2 hok2 => ?_⟩
              fc_split
              · have ht2 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [litNeg a.toNat, b.toNat, litNeg cl.toNat]) := by
                  simpa only [bv32_xor1_litNeg] using hok2 (by grind)
                    (hdis_lit _ _ (div2_ne_of_xor1_l_m6 hab_v))
                    (hdis_lit _ _ (div2_ne_of_xor1_both_m6 hac_v))
                    (hdis_lit _ _ (div2_ne_of_xor1_m6 hbc_v))
                fc_steps; c0_call hHasTern
                refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                  fun ok3 hok3 => ?_⟩
                fc_split
                · have ht3 : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [litNeg a.toNat, litNeg b.toNat, cl.toNat]) := by
                    simpa only [bv32_xor1_litNeg] using hok3 (by grind)
                      (hdis_lit _ _ (div2_ne_of_xor1_both_m6 hab_v))
                      (hdis_lit _ _ (div2_ne_of_xor1_l_m6 hac_v))
                      (hdis_lit _ _ (div2_ne_of_xor1_l_m6 hbc_v))
                  obtain ⟨hx1, hx2, hx3⟩ := xorGateDef_of_four_m6 hcl0_ent ht1 ht2 ht3
                  fc_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (ret, ()) mr => ∃ scr' : List (BitVec 32),
                      scr'.length = c.scratch_cap ∧ g_len.toNat ≤ ret.toNat ∧
                      ret.toNat ≤ g_cap.toNat ∧
                      (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                      M6GateSeqOk F_cur s.core.cur_vars scr' ret.toNat 0 ∧
                      (FullMem c { s with scratch :=
                        { s.scratch with scratch_buf := scr' } } ⋆ R) mr)
                    ?_ ?_
                  · rintro _ ⟨ret, ⟨⟩⟩ mr ⟨scr', hlen', hlo, hhi, hpref', hseq', hmr⟩
                    fc_let; exact hQ ret scr' mr hlen' hlo hhi hpref' hseq' hmr
                  · intro Jret hJret; fc_split
                    · have h12 : g_len.toNat + 12 ≤ g_cap.toNat := by bv_omega
                      have hg4 : (g_len + 4#64).toNat = g_len.toNat + 4 := by bv_omega
                      have hg8 : (g_len + 4#64 + 4#64).toNat = g_len.toNat + 8 := by
                        bv_omega
                      have hg12 : (g_len + 4#64 + 4#64 + 4#64).toNat =
                          g_len.toNat + 12 := by bv_omega
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, s.scratch.scratch_buf,
                        FullScrBufRest c s ⋆ R, ha_lt, hb_lt, hc_lt, by omega, by omega,
                        by omega, hx1, hseq0, focus_full_scratch_buf hm0,
                        fun scr1 m1 hlen1 hpref1 hseq1 hm1 => ?_⟩
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, scr1, FullScrBufRest c s ⋆ R,
                        hb_lt, ha_lt, hc_lt, by omega, by omega, by omega, hx2,
                        hg4 ▸ hseq1, hm1, fun scr2 m2 hlen2 hpref2 hseq2 hm2 => ?_⟩
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, scr2, FullScrBufRest c s ⋆ R,
                        hc_lt, ha_lt, hb_lt, by omega, by omega, by omega, hx3,
                        by rw [hg8]; rw [hg4, Nat.add_assoc] at hseq2; exact hseq2, hm2,
                        fun scr3 m3 hlen3 hpref3 hseq3 hm3 => ?_⟩
                      fc_let
                      exact hJret (g_len + 4#64 + 4#64 + 4#64, ()) m3
                        ⟨scr3, by omega, by omega, by omega,
                         fun idx hi => (hpref3 idx (by omega)).trans
                           ((hpref2 idx (by omega)).trans (hpref1 idx hi)),
                         by rw [hg12]; rw [hg8, Nat.add_assoc] at hseq3; exact hseq3,
                         unfocus_full_scratch_buf hm3⟩
                    · fc_let
                      exact hJret (g_len, ()) m0
                        ⟨s.scratch.scratch_buf, hscrl, Nat.le_refl _, by omega,
                         fun _ _ => rfl, hseq0, hm0⟩
                · fc_let; exact hret_glen
              · fc_let; exact hret_glen
            · fc_let; exact hret_glen
          · intro J3 hJ3; fc_split_fast
            · exact hJ3 () m0 rfl
            · clear hc; fc_split_fast
              · exact hJ3 () m0 rfl
              · fc_let; exact hret_glen
        · intro J2 hJ2; fc_split_fast
          · exact hJ2 () m0 rfl
          · clear hc; fc_split_fast
            · exact hJ2 () m0 rfl
            · fc_let; exact hret_glen
      · intro J1 hJ1; fc_split_fast
        · exact hJ1 () m0 rfl
        · clear hc; fc_split_fast
          · exact hJ1 () m0 rfl
          · fc_let; exact hret_glen
    · intro Jmx hJmx; fc_split_fast
      · fc_let; exact hJmx (cl, ()) m0 rfl
      · fc_let; exact hJmx (mx1, ()) m0 rfl
  · intro Jmx1 hJmx1; fc_split_fast
    · fc_let; exact hJmx1 (a, ()) m0 rfl
    · fc_let; exact hJmx1 (b, ()) m0 rfl
end M8CongIte


section M8EnterDense
open LeanQbe.T.Examples.Kissat.FullFastSched
open FullReduceHelpers FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open scoped FullArenaTactics
private def M8EnterOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧
  FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat

theorem m8_enter_dense_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Func.wp Γ m8_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  let _ := hProp
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp m8_enter_dense_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => M8EnterOk c F0 F_cur s s1 ∧ s1.core.dense_mode = 0#64 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hok1, hdm1, hm1⟩
    clear hm hsp0 hspw0
    have hspw1 : FullSparseInvW c F0 F_cur s1 :=
      ⟨hok1.1, hok1.2.1, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hdm1⟩
    c0_hsplit
    · -- `h->oom != 0`: return `false` immediately
      c0_hsteps
      exact hQ false s1 m1 hok1.2.2.2.2.2.1 hok1.2.2.2.2.2.2 (by simp)
        (fun _ => hspw1.toSparse) hm1
    · c0_hsplit
      · exact absurd hdm1 hc
      · -- `dense_mode == 0`: call `full_flush_trail`
        c0_hsteps; c0_call hFlush
        refine ⟨c, F0, s1, R, rfl, hspw1.toSparse, hm1, ?_⟩
        intro fr s1p m1p hsp1p _ _ hfl1p hcl1p_fn _ _ _ hm1p
        have hcl1p : s1p.core.cur_level = 0 := hcl1p_fn hok1.2.2.2.2.2.1
        have hfl1p' : s1p.core.fuel.toNat ≤ s.core.fuel.toNat :=
          Nat.le_trans hfl1p hok1.2.2.2.2.2.2
        c0_hsplit
        · -- `fr != 1`: return `false`
          c0_hsteps
          exact hQ false s1p m1p hcl1p hfl1p' (by simp) (fun _ => hsp1p) hm1p
        · -- `fr == 1`: V2a optional sparse sweep-propagate-flush if unflushed > 0, then sweep_bins
          refine wp_join_state0 (α := FullState)
            (fun s1u m1u => FullSparseInv c F0 s1u ∧ s1u.core.cur_level = 0 ∧
              s1u.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1u ⋆ R) m1u) ?_ ?_
          · rintro _ s1u m1u ⟨hsp1u, hcl1u, hfl1u', hm1u⟩
            obtain ⟨F_cur1, hspw1p⟩ := hsp1u.exists_witness
            have hdm1p : s1u.core.dense_mode = 0#64 := hspw1p.2.2.2.2.2
            c0_hsteps
            c0_call hSweepBins
            refine ⟨c, F0, F_cur1, s1u, R, rfl, hspw1p.1, hspw1p.2.1, hm1u,
              fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 _ hd2 hw2 hm2 => ?_⟩
            let s2 : FullState :=
              { s1u with
                core := { s1u.core with
                  wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
                scratch := { s1u.scratch with wsort := wsort2 } }
            have hok2 : M8EnterOk c F0 F_cur1 s s2 :=
              ⟨hlen2, hw2, hspw1p.2.2.1, hspw1p.2.2.2.1, hspw1p.2.2.2.2.1, hcl1u, hfl1u'⟩
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (p, ()) mP =>
                p.toNat ≤ s2.core.arena_len ∧
                (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
                ∃ sP : FullState,
                  M8EnterOk c F0 F_cur1 s sP ∧ DenseWatchesInv F_cur1 sP.core ∧
                  sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
                  sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
              (fun (p, ()) _ => s2.core.arena_len - p.toNat)
              (fun JP hLoopP => by
                c0_hsteps
                refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1p, hm2⟩
                by_cases hz : s2.core.arena_len = 0
                · exact Or.inl hz.symm
                · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hw2.arena
                    (Nat.pos_of_ne_zero hz)))
              (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩
                  hLoopP => ?_)
            have halP := hokP.1.core_ok.arena_len_le
            have haarP := hokP.1.core_ok.arena_len_arr
            have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
            c0_hsplit
            · have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
              have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
                rw [hrefsP]; exact hp_mem.resolve_left (by omega)
              have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
              have hp_lt32 : p.toNat < 2 ^ 32 := by omega
              have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
              have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
                (cref := p.toNat) hp_wf.1
              have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun sN mN => M8EnterOk c F0 F_cur1 s sN ∧ DenseWatchesInv F_cur1 sN.core ∧
                  sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
                  sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
                (fun _ sN mN ⟨hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
                  c0_hsteps; c0_call hArenaNext
                  refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
                  have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                      (p.setWidth 32).toNat)).setWidth 64).toNat =
                      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                    rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps
                  exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                    ⟨by rw [hn_eq]; omega,
                      by rw [hn_eq]
                         rcases hnxt_mem with hend | hmem
                         · exact Or.inl (hend.trans halenP)
                         · exact Or.inr (hrefsP ▸ hmem),
                      sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
                (fun JN hJN => ?_)
              c0_hsteps_nogrp
              · have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                    fullArenaClauseSizeCore sP.core p.toNat := by
                  have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
                have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                  rw [hsz_eq]; exact hp_wf.2.1
                have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
                  rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
                have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
                have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
                have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
                  rw [heq] at hp_lt31; revert hp_lt31; decide
                refine wp_loop_inv
                  (fun (k, ()) mK =>
                    k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                    ∃ sK : FullState,
                      M8EnterOk c F0 F_cur1 s sK ∧ DenseWatchesInv F_cur1 sK.core ∧
                      sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                      sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
                  (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
                  (fun JK hLoopK => by
                    c0_hsteps
                    exact hLoopK (0#32, ()) mP
                      ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
                  (fun JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
                have haarK := hokK.1.core_ok.arena_len_arr
                c0_hsplit
                · have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                    c0_bound
                  have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                  have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                    rw [hidx_eq]; rw [hsz_eq] at hk_lt
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                    have := hokK.1.core_ok.arena_len_le; omega
                  c0_hsteps; c0_call hWatchPush
                  refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                    fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                    fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                      hokF hmK' => ?_⟩
                  let sK' : FullState :=
                    { sK with
                      core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                             wusable := wuK' }
                      scratch := { sK.scratch with wsort := wsortK' } }
                  have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                    rw [hp_trunc]; unfold fullArenaClauseRefsCore
                    rw [harK, halenK, ← harP, ← halenP]; exact hp_in
                  have hdK' : DenseWatchesInv F_cur1 sK'.core :=
                    fullWatchPush_preserves_denseWatchesInv hdK hlayK' rfl (fun _ r => r)
                      hmask.1 hmask.2.2 hp_lt31 hp_inK hothK'
                      (fun ht => by
                        obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                        exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) (fun hf => (hokF hf).1)
                  have hwK' : FullWitnessInv c F0 F_cur1 sK'.core :=
                    { hokK.2.1 with
                      arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
                      watches := by
                        rw [ModeWatchesInv, ite_eq_left hdmK]
                        exact denseWatchesInv_toWatchesInv hdK' }
                  have hokK' : M8EnterOk c F0 F_cur1 s sK' :=
                    ⟨hlenK', hwK', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
                      hokK.2.2.2.2.2.2⟩
                  c0_hsplit
                  · have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                    c0_hsteps
                    exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                      ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
                  · c0_hsteps
                    let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                    have hlenOom : sOom.LengthsOk c :=
                      ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                        hlenK'.scratch_ok⟩
                    have hwOom := fullWitnessInv_with_oom hwK' 0#64
                    c0_call hSweep
                    refine ⟨c, F0, F_cur1, sOom, R, rfl, hlenOom, hwOom, hokK'.2.2.2.1, hdmK,
                      fun hpos => by
                        change 0 < sK.core.cur_level at hpos; have := hokK.2.2.2.2.2.1; omega,
                      hm, ?_⟩
                    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS hlenS _ hextS _ hllS
                      hwS hndS _ _ _ _ _ hmS
                    have hspS : FullSparseInv c F0 sS :=
                      ⟨⟨hlenS, F_cur1, hwS⟩, hokK'.2.2.1, hndS, ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩,
                        hdmK⟩
                    c0_hsteps
                    exact hQ false sS mS hokK'.2.2.2.2.2.1 hokK'.2.2.2.2.2.2
                      (by simp) (fun _ => hspS) hmS
                · c0_hsteps; exact hJN sK mK ⟨hokK, hdK, harK, halenK, hdmK, hmK⟩
              all_goals exact hJN sP mP ⟨hokP, hdP, harP, halenP, hdmP, hmP⟩
            · -- Outer loop exit: set `dense_mode = 1#64`, return `true`
              c0_hsteps
              let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
              have hlenFin : sFin.LengthsOk c :=
                ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
              have hwFin : FullWitnessInv c F0 F_cur1 sFin.core :=
                fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide)
              have hdenFin : FullDenseInv c F0 sFin :=
                ⟨⟨hlenFin, F_cur1, hwFin⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
                  hokP.2.2.2.2.2.1, show (1#64 : BitVec 64) ≠ 0#64 by decide⟩
              exact hQ true sFin _ hokP.2.2.2.2.2.1 hokP.2.2.2.2.2.2
                (fun _ => hdenFin) (by simp) hm
          · intro J1u hJ1u
            c0_hsteps_nogrp
            exact hJ1u s1p m1p ⟨hsp1p, hcl1p, hfl1p', hm1p⟩
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
        have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
        have := hspw0.1.core_ok.cur_vars_le; omega,
        hspw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hspw0.2.1 (Nat.zero_le _)
      have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hsp1 := m6cf_fullSparseInvW_after_bt0 hspw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
      c0_hsteps
      exact hJ1 s1 m1 ⟨⟨hsp1.1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hl01,
        Nat.le_refl _⟩, hsp1.2.2.2.2.2, hm1⟩
    · have hl00 : s.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps
      exact hJ1 s m ⟨⟨hspw0.1, hspw0.2.1, hspw0.2.2.1, hspw0.2.2.2.1, hspw0.2.2.2.2.1, hl00,
        Nat.le_refl _⟩, hspw0.2.2.2.2.2, hm⟩

end M8EnterDense


section M8Preprocess
open LeanQbe.T.Examples.Kissat.FullM6 (fullM6PreprocessSpec fullM6PreprocessSpec_elim)
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped FullArenaTactics
section PreprocessFid2Compact

private theorem m8_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧ (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom hr0 hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr0 hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid2_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid2_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private abbrev Fid2PrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem fid2Pre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem fid2Pre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2Pre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  fid2Pre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem fid2Pre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS
    let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine fid2_call_bcp rfl hProp hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact fid2Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (fid2_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, { hinvWP.sparseW.2.1 with
              arena := { hinvWP.sparseW.2.1.arena with len_ok := hinvWP.sparseW.2.1.arena.len_ok }
              watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
              }⟩⟩, hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem fid2_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact fid2Pre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

/-- Parametric `Func.wp` proof for `full_preprocess_fid2_body` against `fullM6PreprocessSpec`
(`fastel = 0`, `FullM4Compact.fullCompactNeededSpec`). -/
theorem m8_preprocess_m6_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ m8_preprocess_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp m8_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine fid2_call_bcp rfl hProp hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact fid2Pre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (fid2_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact fid2Pre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3; have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact fid2Pre_ret20 hQ (.refl c) hlen3 hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (.refl c) hlen3 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · exact fid2Pre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_› hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (ts := []) (fun (_ : Tup Val []) m3u => ∃ s3u,
              FullM6HdrInv c F0 ext s3u ∧ s3u.core.cur_level = 0 ∧
              s3u.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s3u ⋆ R) m3u) ?_ ?_
          · rintro _ _ m3u ⟨s3u, hinv3u, hcl3u, hfu3u, hm3u⟩
            refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
                FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
                s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
            · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
              refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
              c0_hsteps_nogrp
              · exact fid2Pre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
              · exact fid2Pre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · exact fid2Pre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · c0_call hScale
                refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                  hm4f, fun sd1 => ?_⟩
                c0_hsteps_nogrp; c0_call hScale
                refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                  (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                  by assumption, fun sd2 => ?_⟩
                c0_hsteps_nogrp
                have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
                have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                  s4.scratch.elim_bound
                have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
                have hm4' := fullM6HdrMem_unfocus (by assumption)
                c0_call hProbe
                refine FullM6Orch.m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                  fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
                have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
                c0_hsteps_nogrp
                · exact fid2Pre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
                · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                  refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                  c0_hsteps_nogrp
                  · exact fid2Pre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                  · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                          FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                          s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                    · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                      rw [hcmp4.hdr, ← hcmp6.hdr]
                      refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                      c0_hsteps_nogrp
                      · exact fid2Pre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_› (fullM6HdrMem_unfocus hm6f)
                      · exact fid2Pre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · exact fid2Pre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · c0_call hScale
                        refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                        c0_hsteps_nogrp; c0_call hScale
                        refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          (fullState_upd_probe_step hinv6.sparse.lengths sd3
                            s6.scratch.probings).1,
                          by assumption, fun sd4 => ?_⟩
                        c0_hsteps_nogrp
                        have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings
                        have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                          s6.scratch.elim_bound
                        have hinv6' := fullM6HdrInv_of_probeStep hinv6
                          (probeStep_trans hst6 hst6')
                        exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                          hinv6'.extOk (Or.inr (Or.inl rfl))
                          (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                          (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                          (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                    · exact fun _ hJC2 => wp_m6Hdr_focus_frame hm5 fun hm5f =>
                        fid2_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5 hcl5 hfu5' hm5f
                          hJC2 hQ
            · exact fun _ hJC1 => wp_m6Hdr_focus_frame hm3u fun hm3uf =>
                fid2_pre_compact_step hCompNeed hCompact rfl (.refl c) hinv3u hcl3u hfu3u hm3uf hJC1 hQ
          · intro _ hJ3u
            refine wp_m6Hdr_focus_frame hm3' fun hm3f => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ m_b => m3 = m_b) ?_ ?_
            · rintro _ ⟨⟩ mb hmb; subst mb
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ m_w => ∃ sW,
                  FullM6HdrInv c F0 ext sW ∧ sW.core.cur_level = 0 ∧
                  sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w) ?_ ?_
              · rintro _ _ m_w ⟨sW, hinvW, hclW, hfuW, hmW⟩
                c0_hsteps
                have hinvW' : FullM6HdrInv c F0 ext { sW with core := { sW.core with unflushed := 0#64 } } := by
                  obtain ⟨F_curW, hwW⟩ := hinvW.sparse.1.witness
                  exact FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk
                    ⟨⟨⟨{ hinvW.sparse.lengths.core_ok with vals_len := hinvW.sparse.lengths.core_ok.vals_len },
                       hinvW.sparse.lengths.scratch_ok⟩,
                      ⟨F_curW, m8_fullWitnessInv_with_unflushed hwW⟩⟩,
                     hinvW.sparse.2.1, hinvW.sparse.2.2.1, hinvW.sparse.2.2.2.1, hinvW.sparse.2.2.2.2⟩
                exact hJ3u () _ ⟨_, hinvW', hclW, hfuW, fullM6HdrMem_unfocus (by assumption)⟩
              · intro J_brk hJ_brk
                have hJ_brkF : ∀ (sW : FullState) m_w,
                    FullM6HdrInv c F0 ext sW → sW.core.cur_level = 0 →
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat →
                    (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w →
                    J_brk () m_w := fun sW m_w h1 h2 h3 hmW => hJ_brk () m_w ⟨sW, h1, h2, h3, hmW⟩
                c0_hsteps_nogrp
                refine wp_while_state0 (α := FullState)
                  (μ := fun st => st.core.fuel.toNat)
                  (Inv := fun sL mL => FullM6HdrInv c F0 ext sL ∧ sL.core.cur_level = 0 ∧
                    sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mL) ?_ ?_
                · intro JL hJL; c0_hsteps; exact hJL s3 m3 ⟨hinv3, hcl3, hfu3', hm3f⟩
                · intro JL sL mL ⟨hinvL, hclL, hfuL, hmL⟩ ihL
                  rw [Blocks.get_here]; dsimp only
                  obtain ⟨F_curL, hwL⟩ := hinvL.sparse.1.witness
                  have hpr_le : sL.core.propagated ≤ sL.core.trail_end :=
                    hinvL.sparse.lengths.core_ok.propagated_le
                  c0_hsteps_nogrp
                  · c0_call hSweep
                    refine ⟨c, F0, F_curL, sL, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
                      hinvL.sparse.lengths, hwL, hinvL.sparse.2.2.1, hinvL.sparse.2.2.2.2,
                      fun hpos => by omega, hmL,
                      fun sr2 valsS flagsS lvlS rsnsS trlS tpS teS unassS unflS wvecS wstkS
                        arenaS alenS wlenS wuS fredS niS nrS nbS oomS scS mS
                        hlenS hsr2 hexlenS _ hllS hwS hndS _ _ hsr1 h20S _ hmS => ?_⟩
                    let sS : FullState :=
                      { sL with
                        core := { sL.core with
                          vals := valsS, flags := flagsS, lvl := lvlS, rsns := rsnsS, trl := trlS,
                          trail_pos := tpS, trail_end := teS, unassigned := unassS, unflushed := unflS,
                          wvec := wvecS, wstk := wstkS, arena := arenaS, arena_len := alenS,
                          wlen := wlenS, wusable := wuS, arena_garbage := 0#64,
                          first_reducible := fredS, num_irred := niS, num_redundant := nrS,
                          num_binary := nbS, oom := oomS }
                        scratch := scS }
                    have hinvWS : FullM6HdrInvW c F0 F_curL ext sS :=
                      FullM6HdrInvW.mk_inv hinvL.cfgOk hinvL.extOk
                        ⟨hlenS, hwS, hinvL.sparse.2.1, hndS,
                          ⟨hllS, by
                            change scS.extend_len ≤ c.extend_cap
                            rw [hexlenS]; exact hinvL.sparse.2.2.2.1.2⟩,
                          hinvL.sparse.2.2.2.2⟩
                    have hinvS := hinvWS.toInv
                    c0_hsteps_nogrp
                    · exact fid2Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfuL
                        (h20S ‹_›).2 (fullM6HdrMem_unfocus hmS)
                    · exact hJ_brkF sS mS hinvS hclL hfuL hmS
                    · refine m8_call_bcp rfl hProp hinvWS (fullM6HdrMem_unfocus hmS)
                        fun pr2 sP mP hinvWP hclP _ _ hfuP hdomP hrP0 hrP1 hmP => ?_
                      have hinvP := hinvWP.toInv
                      have hfuP' : sP.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuP hfuL
                      c0_hsplit
                      · c0_hsteps
                        exact fid2Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
                          (fid2_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hclL) (hrP1 ‹_›).2.2) hmP
                      · c0_hsplit
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          c0_hsteps
                          exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          have hpr2_0 : pr2 = 0#64 := by
                            rcases hdomP with rfl | rfl | rfl <;> first | rfl | contradiction
                          have hpeq := (hrP0 hpr2_0).1
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps
                              exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                            · exfalso
                              have hbv_eq : BitVec.ofNat 64 sP.core.propagated =
                                  BitVec.ofNat 64 sP.core.trail_end := congrArg (BitVec.ofNat 64) hpeq
                              rw [hbv_eq] at *
                              bv_omega
                          · have hsr1_ne : sr2 ≠ 0#64 := by assumption
                            have hsr1_eq : sr2 = 1#64 := by
                              rcases hsr2 with rfl | rfl | rfl | rfl <;>
                                first | rfl | contradiction
                            have hte_lt := (hrP0 hpr2_0).2.2 (by
                              change sL.core.propagated < teS
                              have := (hsr1 hsr1_eq).2; omega)
                            have hfu_lt : sP.core.fuel.toNat < sL.core.fuel.toNat := hte_lt
                            c0_hsteps
                            exact ihL sP _ hfu_lt ⟨hinvP, hclP ▸ hclL, hfuP', hmPf⟩
                  · cases hc
            · intro Jb hJb; c0_hsplit
              · exact hJb () m3 rfl
              · c0_hsplit
                · exact hJb () m3 rfl
                · exact hJ3u () m3 ⟨s3, hinv3, hcl3, hfu3', hm3'⟩
    · exact fun _ hJ2 =>
        fid2_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

end PreprocessFid2Compact
end M8Preprocess

end LeanQbe.T.Examples.Kissat.FullM8FidV12
