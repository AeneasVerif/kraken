/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof3
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 7 `full_reduce` / `full_reduce_m6` Proofs (`FullFidelityStep7Proof0d`)

M1-clean, UNSAT-only parametric `Func.wp` proofs (`public section`, no exposed theorems) for the
Step-7 reduce replacements (`FullFidelityStep7.lean:226-355`), whose only differences from the
previously certified bodies are `reduce_limit = conflicts + full_isqrt(reductions * 1000000ULL)`
(was `conflicts + 1000ULL * full_isqrt(reductions)`) and, for `full_reduce_m6`, the simplified
sweep condition `force || unflushed == 0`:
1. `full_reduce_step7_wp` (`fidStep7ReduceFn`, `Full.fullReduceSpec`), adapted from
   `FullDenseWatchLemmas2.full_reduce_wp` (same `FullDenseWatchSpecs` callee contracts).
2. `full_reduce_m6_step7_wp` (`fidStep7ReduceM6Fn`, `FullM6Orch.m6ReduceSpec`), adapted from
   `FullM7FidelitySchedFixProof0.full_reduce_fid2_wp` (same callee contracts).
-/

set_option autoImplicit false

public section

/-! ## 1. `full_reduce` (`FullDenseWatchSpecs.fullReduceSpec` → `Full.fullReduceSpec`) -/

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

section Step7ReduceDW

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding fullArenaNextSpec fullArenaSweepSpec FullArenaVarsNodup
  fullBacktrackSpec fullIlog10Spec fullIsqrtSpec FullLastLearnedWf fullMarkReasonsSpec
  fullPropagateSpec FullReasonsMarked fullRecomputeTiersSpec fullSortRedsSpec FullSparseInv
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchSpecs
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

open Lean Elab Tactic in
/-- Step goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
local elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      let mut g := g
      let mut ty ← Lean.instantiateMVars (← g.getType)
      if ty.isMData then
        g ← g.replaceTargetDefEq ty.consumeMData
        ty := ty.consumeMData
      setGoals [g]
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Strip `mdata` wrappers (e.g. after `have`) and run `c0_steps`. -/
local elab "c0_go" : tactic => do
  let mut gs : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then gs := gs.push (← g.replaceTargetDefEq ty.consumeMData)
    else gs := gs.push g
  setGoals gs.toList
  LeanQbe.T.C0Step.steps 10000

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
local elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut g ← getMainGoal
    let mut ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then
      g ← g.replaceTargetDefEq ty.consumeMData
      ty := ty.consumeMData
      setGoals [g]
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

/-! ## 1. Pure state-transition helpers for `full_reduce` -/

private def ReduceStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInv c F0 s' ∧
  FullWitnessInv c F0 F_cur s'.core ∧
  s'.core.cur_level ≤ s.core.cur_level ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.tmp = s.core.tmp ∧
  s'.core.tmp_len = s.core.tmp_len ∧
  s'.core.frame_trail = s.core.frame_trail ∧
  s'.core.frame_dec = s.core.frame_dec ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.core.d_cur = s.core.d_cur ∧
  s'.core.d_val = s.core.d_val ∧
  s'.scratch.extend_len = s.scratch.extend_len ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  (0 < s'.core.cur_level →
    s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)

private theorem reduceStateOk_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core) :
    ReduceStateOk c F0 F_cur s s :=
  ⟨hsp, hw, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem reduceStateOk_trans {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 s2 : FullState} (h1 : ReduceStateOk c F0 F_cur s s1)
    (h2 : ReduceStateOk c F0 F_cur s1 s2) : ReduceStateOk c F0 F_cur s s2 :=
  ⟨h2.1, h2.2.1, Nat.le_trans h2.2.2.1 h1.2.2.1, Nat.le_trans h2.2.2.2.1 h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun hpos => by
      have hpos1 : 0 < s1.core.cur_level := Nat.lt_of_lt_of_le hpos h2.2.2.1
      have ha := h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos
      have hb := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos1
      exact ⟨ha.1.trans hb.1, ha.2.1.trans hb.2.1, ha.2.2.1.trans hb.2.2.1,
        ha.2.2.2.1.trans hb.2.2.2.1, ha.2.2.2.2.1.trans hb.2.2.2.2.1,
        ha.2.2.2.2.2.trans hb.2.2.2.2.2⟩⟩

private theorem reduceStateOk_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 : FullState} (h1 : ReduceStateOk c F0 F_cur s s1) {sc' : FullScratch}
    (hok : sc'.LengthsOk c) (hll : sc'.last_learned = s1.scratch.last_learned)
    (hext : sc'.extend_len = s1.scratch.extend_len)
    (hws2 : sc'.work_stk2 = s1.scratch.work_stk2) :
    ReduceStateOk c F0 F_cur s { s1 with scratch := sc' } := by
  have hsp1 := h1.1
  have hsp' : FullSparseInv c F0 { s1 with scratch := sc' } :=
    ⟨⟨hsp1.1.lengths.with_scratch hok, ⟨F_cur, h1.2.1⟩⟩, hsp1.2.1, hsp1.2.2.1,
      ⟨fun i hi => by
         change (sc'.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
           (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s1
         rw [hll]; exact hsp1.2.2.2.1.1 i hi,
       hext ▸ hsp1.2.2.2.1.2⟩, hsp1.2.2.2.2⟩
  exact reduceStateOk_trans h1 ⟨hsp', h1.2.1, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, hext, hws2, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem reduceStateOk_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s1 : FullState} (h1 : ReduceStateOk c F0 F_cur s s1)
    (u' : BitVec 64) :
    ReduceStateOk c F0 F_cur s { s1 with core := { s1.core with unflushed := u' } } := by
  have hsp1 := h1.1
  have hw' := fullWitnessInv_with_unflushed h1.2.1 u'
  have hlen' : ({ s1 with core := { s1.core with unflushed := u' } } : FullState).LengthsOk c :=
    ⟨{ hsp1.1.lengths.core_ok with vals_len := hsp1.1.lengths.core_ok.vals_len },
      hsp1.1.lengths.scratch_ok⟩
  have hsp' : FullSparseInv c F0 { s1 with core := { s1.core with unflushed := u' } } :=
    ⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
  exact reduceStateOk_trans h1 ⟨hsp', hw', Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem reduceStateOk_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 : FullState} {ar' : List (BitVec 32)}
    (h2 : ReduceStateOk c F0 F_cur s s2)
    (hlen' : ({ s2 with core := { s2.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { s2 with core := { s2.core with arena := ar' } } =
      fullArenaClauseRefs s2)
    (hper : ∀ r ∈ fullArenaClauseRefs s2,
      fullArenaClauseSize { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseSize s2 r ∧
      fullArenaClauseGarb { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseGarb s2 r ∧
      fullArenaClauseLits { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseLits s2 r)
    (hw' : FullWitnessInv c F0 F_cur { s2.core with arena := ar' }) :
    ReduceStateOk c F0 F_cur s { s2 with core := { s2.core with arena := ar' } } := by
  let s3 : FullState := { s2 with core := { s2.core with arena := ar' } }
  have hnd : FullArenaVarsNodup s3 := fun r hr hng => by
    rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
    exact h2.1.2.2.1 r hr hng
  have hll : FullLastLearnedWf s3 := fun i hi => by
    change s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s3
    rw [hrefs]; exact h2.1.2.2.2.1.1 i hi
  exact reduceStateOk_trans h2 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h2.1.2.1, hnd,
    ⟨hll, h2.1.2.2.2.1.2⟩, h2.1.2.2.2.2⟩, hw', Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem reduceStateOk_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s0 : FullState} (h0 : ReduceStateOk c F0 F_cur s s0)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} :
    let sB : FullState := { s0 with
      core := { s0.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
      scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = s0.scratch.last_learned →
    sc'.extend_len = s0.scratch.extend_len →
    sc'.work_stk2 = s0.scratch.work_stk2 →
    ReduceStateOk c F0 F_cur s sB := by
  intro sB hlen' hw' hll' hext' hws2'
  have hllB : FullLastLearnedWf sB := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s0
    rw [hll']; exact h0.1.2.2.2.1.1 i hi
  exact reduceStateOk_trans h0 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h0.1.2.1, h0.1.2.2.1,
    ⟨hllB, hext' ▸ h0.1.2.2.2.1.2⟩, h0.1.2.2.2.2⟩, hw', Nat.zero_le _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hext', hws2', fun hpos => by cases hpos⟩

private theorem reduceStateOk_propagate0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : ReduceStateOk c F0 F_cur s sA) (hcl0 : sA.core.cur_level = 0)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB : BitVec 64}
    {scB : FullScratch} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := scB }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaVarsNodup sB → (∀ ref ∈ fullArenaClauseRefs sA, ref ∈ fullArenaClauseRefs sB) →
    scB.last_learned = sA.scratch.last_learned →
    scB.extend_len = sA.scratch.extend_len →
    scB.work_stk2 = sA.scratch.work_stk2 →
    fuelB.toNat ≤ sA.core.fuel.toNat →
    ReduceStateOk c F0 F_cur s sB := by
  intro sB hlenB hwB hndB hrefsB hllB hextB hws2B hfuelB
  have hll' : FullLastLearnedWf sB := fun i hi => by
    change scB.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (scB.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sB
    rw [hllB]; exact (hA.1.2.2.2.1.1 i hi).imp id (hrefsB _)
  exact reduceStateOk_trans hA ⟨⟨⟨hlenB, ⟨F_cur, hwB⟩⟩, hA.1.2.1, hndB,
    ⟨hll', hextB ▸ hA.1.2.2.2.1.2⟩, hA.1.2.2.2.2⟩, hwB, Nat.le_refl _, hfuelB,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextB, hws2B,
    fun hpos => by change 0 < sA.core.cur_level at hpos; omega⟩

private theorem reduceStateOk_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : ReduceStateOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core →
    FullArenaVarsNodup sA → FullLastLearnedWf sA →
    sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level →
      vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    ReduceStateOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA
  exact reduceStateOk_trans hst ⟨⟨⟨hlenA, ⟨F_cur, hwA⟩⟩, hst.1.2.1, hndA,
    ⟨hllA, hextA ▸ hst.1.2.2.2.1.2⟩, hst.1.2.2.2.2⟩, hwA, Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextA, hws2A,
    fun hpos => by
      obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
      exact ⟨rfl, hv, hl, ht, htp, hte⟩⟩

private def RedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

private theorem redRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : RedRefsOk s rc) :
    RedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } } (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, bv32_ofNat_toNat hp_lt32] using And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem reduceStateOk_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p rc : Nat} {u : BitVec 32}
    (hokL : ReduceStateOk c F0 F_cur s sL) (hrmL : FullReasonsMarked sL)
    (hrrL : RedRefsOk sL rc) (hp_in : p ∈ fullArenaClauseRefs sL)
    (hp_ar : p < sL.core.arena.length) :
    let v' := (sL.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { sL with core := { sL.core with arena := sL.core.arena.set p v' } }
    ReduceStateOk c F0 F_cur s sU ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs sL ∧ RedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (sL.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hhdr_eq : sL.core.arena[p]'hp_ar = fullArenaHdr sL p := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := updateUsed_preserves_fullWitnessInv hokL.1.1.lengths hokL.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hokL.1.2.2.1 r hr hng
  have hllU : FullLastLearnedWf sU := fun i hi => by
    change sL.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sL.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sU
    rw [hrefsU]; exact hokL.1.2.2.2.1.1 i hi
  have hrmU : FullReasonsMarked sU := fun idx hidx hlp hlg => by
    have hne0 : sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro heq; rw [heq] at hlg; revert hlg; decide
    have hrs := hokL.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs
    rw [(hperU _ hrs.1).2.2.2]; exact hrmL idx hidx hlp hlg
  have hrrU : RedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj
    exact ⟨hrefsU ▸ hjm, (hperU _ hjm).2.2.2.trans hjr⟩
  have hokU : ReduceStateOk c F0 F_cur s sU :=
    reduceStateOk_trans hokL ⟨⟨⟨hlenU, ⟨F_cur, hwU⟩⟩, hokL.1.2.1, hndU,
      ⟨hllU, hokL.1.2.2.2.1.2⟩, hokL.1.2.2.2.2⟩, hwU, Nat.le_refl _, Nat.le_refl _,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact ⟨hokU, hrmU, hrefsU, hrrU, by rw [(hperU p hp_in).2.2.2, ← hhdr_eq]⟩

private theorem reduceStateOk_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sI : FullState} {cr rc : Nat} {agN : BitVec 64}
    (hokI : ReduceStateOk c F0 F_cur s sI) (hrmI : FullReasonsMarked sI)
    (hrrI : RedRefsOk sI rc) (hcr_mem : cr ∈ fullArenaClauseRefs sI)
    (hcr_norsn : (fullArenaHdr sI cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < sI.core.arena.length) :
    let sN : FullState :=
      { sI with core := { sI.core with
        arena := sI.core.arena.set cr (sI.core.arena[cr]'hcr_ar ||| 0x00080000#32)
        arena_garbage := agN } }
    ReduceStateOk c F0 F_cur s sN ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs sI ∧ RedRefsOk sN rc := by
  intro sN
  have hhdr_eq : sI.core.arena[cr]'hcr_ar = fullArenaHdr sI cr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := markGarb_nonact_of_reasonsMarked hokI.2.1 hrmI hcr_norsn
  have hmg := markGarb_preserves_fullWitnessInv hokI.1.1.lengths hokI.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hllN : FullLastLearnedWf sN := fun j hj => by
    change sI.scratch.last_learned[j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sI.scratch.last_learned[j]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sN
    rw [hrefsN]; exact hokI.1.2.2.2.1.1 j hj
  have hrmN : FullReasonsMarked sN := fun idx hidx hlp hlg => by
    have hne0 : sI.core.rsns[(sI.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro heq; rw [heq] at hlg; revert hlg; decide
    have hrs := hokI.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (sI.core.rsns[(sI.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs
    rw [hrsnN _ hrs.1]; exact hrmI idx hidx hlp hlg
  have hrrN : RedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj
    exact ⟨hrefsN ▸ hjm, (hrsnN _ hjm).trans hjr⟩
  have hokN : ReduceStateOk c F0 F_cur s sN :=
    reduceStateOk_trans hokI ⟨⟨⟨hlenN, ⟨F_cur, hwN⟩⟩, hokI.1.2.1,
      hndN hokI.1.2.2.1, ⟨hllN, hokI.1.2.2.2.1.2⟩, hokI.1.2.2.2.2⟩, hwN,
      Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact ⟨hokN, hrmN, hrefsN, hrrN⟩

/-! ## 2. Sweep/unmark tail helper for `full_reduce` (`Full2.lean:243-257`) -/

private def fullReduceTailExpr (hdr : Val i64) (force : Val .bool) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.ret (Arg.imm 1, ()))
      Blocks.nil) fun Js =>
    Expr.group (sig := [[]])
      (fun _ =>
        Blocks.cons
          (fun _ =>
            Expr.group (sig := [[]])
                (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil) fun Js =>
              Expr.group (sig := [[]])
                (fun Js_2 =>
                  Blocks.cons
                    (fun _ =>
                      Expr.jnz (Arg.imm true)
                        (Expr.call "full_arena_sweep" (as := [i64]) (bs := [i64])
                            (Arg.var hdr, ()) fun p =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                              args := (Arg.var p.fst, Arg.imm 2, ()) }
                            fun p_1 =>
                            Expr.jnz (Arg.var p_1.fst) (Expr.ret (Arg.imm 20, ()))
                              (Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                  args := (Arg.var p.fst, Arg.imm 3, ()) }
                                fun p_2 =>
                                Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.imm 0, ()))
                                  (Expr.let_
                                    { sig := [i64, i64],
                                      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                      args := (Arg.var p.fst, Arg.imm 0, ()) }
                                    fun p =>
                                    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst ())
                                      (Expr.call "full_propagate" (as := [i64]) (bs := [i64])
                                          (Arg.var hdr, ()) fun p =>
                                        Expr.let_
                                          { sig := [i64, i64],
                                            code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                            args := (Arg.var p.fst, Arg.imm 1, ()) }
                                          fun p_3 =>
                                          Expr.jnz (Arg.var p_3.fst) (Expr.ret (Arg.imm 20, ()))
                                            (Expr.let_
                                              { sig := [i64, i64],
                                                code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                                args := (Arg.var p.fst, Arg.imm 0, ()) }
                                              fun p =>
                                              Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 0, ()))
                                                (Expr.let_
                                                  { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var hdr, Arg.imm 512, ()) }
                                                  fun p =>
                                                  Expr.store (t := i64) (Arg.imm 0)
                                                    (Arg.var p.fst) (Expr.jump Js_2.fst ())))))))
                        (Expr.jump Js.fst ()))
                    Blocks.nil)
                fun Js => Expr.jump Js.fst ())
          Blocks.nil)
      fun Js_1 =>
      Expr.jnz (Arg.var force) (Expr.jump Js_1.fst ())
        (Expr.group (sig := [[]])
          (fun _ =>
            Blocks.cons
              (fun _ =>
                Expr.call "full_mark_reasons" (as := [i64, .bool]) (bs := [])
                    (Arg.var hdr, Arg.imm false, ()) fun _ =>
                  Expr.jump Js.fst ())
              Blocks.nil)
          fun Js =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var hdr, Arg.imm 512, ()) }
            fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var ld, Arg.imm 0, ()) }
                fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var hdr, Arg.imm 472, ()) }
                    fun p =>
                    Expr.load i64 (Arg.var p.fst) fun ld =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var ld, Arg.imm 4, ()) }
                        fun p =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var hdr, Arg.imm 48, ()) }
                          fun p_1 =>
                          Expr.load i64 (Arg.var p_1.fst) fun ld =>
                            Expr.let_
                              { sig := [i64, i64],
                                code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                args := (Arg.var p.fst, Arg.var ld, ()) }
                              fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var hdr, Arg.imm 48, ()) }
                                  fun p =>
                                  Expr.load i64 (Arg.var p.fst) fun ld =>
                                    Expr.let_
                                      { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var ld, Arg.imm 5, ()) }
                                      fun p =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var hdr, Arg.imm 32, ()) }
                                        fun p_2 =>
                                        Expr.load i64 (Arg.var p_2.fst) fun ld =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var ld, Arg.imm 4, ()) }
                                            fun p_3 =>
                                            Expr.let_
                                              { sig := [i64, i64],
                                                code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                                args := (Arg.var p.fst, Arg.var p_3.fst, ()) }
                                              fun p =>
                                              Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                                                (Expr.jump Js.fst ())))
                  (Expr.jump Js.fst ()))

private theorem full_reduce_tail_wp (Γ : Env)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (force : Val .bool) (Q : Post [i64]) (X : XPost)
    (hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      ReduceStateOk c F0 F_cur s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml)
    (s4 : FullState) (m4 : Mem 64) (hok4 : ReduceStateOk c F0 F_cur s s4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4)
    (hm4 : (FullMem c s4 ⋆ R) m4) :
    wp Γ Q X (fullReduceTailExpr c.hdr force) m4 := by
  unfold fullReduceTailExpr
  -- Outer join `J5`: `return 1ULL`.
  refine wp_join_group
    (fun _ m5 => ∃ s5 : FullState, ReduceStateOk c F0 F_cur s s5 ∧
      (s.core.oom = 0#64 → s5.core.oom = 0#64) ∧ (FullMem c s5 ⋆ R) m5)
    (fun _ _ m5 ⟨s5, hok5, hoom5, hm5⟩ => by
      c0_go
      exact hret 1#64 s5 m5 hok5 (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hoom5) hm5)
    (fun J5 hJ5 => ?_)
  c0_to_group
  -- Join `Jthen`: the `while (true)` sweep loop (appears once).
  refine wp_join_group
    (fun _ mT =>
      ∃ sT : FullState, ReduceStateOk c F0 F_cur s sT ∧
        (s.core.oom = 0#64 → sT.core.oom = 0#64) ∧ FullReasonsMarked sT ∧
        (FullMem c sT ⋆ R) mT)
    (fun _ _ mT ⟨sT, hokT, hoomT, hrmT, hmT⟩ => by
      clear s4 hok4 hoom4 hrm4 hm4 m4
      c0_to_group
      -- Join `Jbrk` for `break;` out of `while (true)` -> `jump J5`.
      refine wp_join_group
        (fun _ mK => ∃ sK : FullState, ReduceStateOk c F0 F_cur s sK ∧
          (s.core.oom = 0#64 → sK.core.oom = 0#64) ∧ (FullMem c sK ⋆ R) mK)
        (fun _ _ mK hK => by c0_go; exact hJ5 () mK hK)
        (fun Jbrk hJbrk => by
          c0_to_group
          refine wp_loop_group
            (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
              ReduceStateOk c F0 F_cur s st ∧
              (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
              (0 < st.core.cur_level → FullReasonsMarked st) ∧
              (FullMem c st ⋆ R) ml) ?_ ?_
          · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hoom_st, hrm_st, hm_st⟩
            dsimp only [Blocks.get]
            refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
            c0_call hSweep
            refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1.lengths, hok_st.2.1,
              hok_st.1.2.2.1, hok_st.1.2.2.2.2, hrm_st, hm_st,
              fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena'
                alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hwA hndA hllA hextA
                hws2A hsr_dom hoomA hposA hsr1 hsr2 hmA => ?_⟩
            obtain ⟨sA, hokA, hclA_eq, hteA, hoomA', hmA'⟩ :
                ∃ sA : FullState, ReduceStateOk c F0 F_cur s sA ∧
                  sA.core.cur_level = st.core.cur_level ∧ sA.core.trail_end = te' ∧
                  (sr = 0#64 ∨ sr = 1#64 → sA.core.oom = 0#64) ∧ (FullMem c sA ⋆ R) mA :=
              ⟨_, reduceStateOk_arena_sweep hok_st hlenA hwA hndA hllA hextA hws2A
                (fun hpos => by
                  obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
                  exact ⟨hv, hl, ht, htp, hte⟩),
                rfl, rfl, hoomA, hmA⟩
            clear hmA vals' flags' lvl' rsns' trl' tp' unass' unfl' wvec' wstk' arena' alen'
              wlen' wu' fred' ni' nr' nb' oom' sc' hlenA hwA hndA hllA hextA hws2A hoomA
              hposA
            c0_go
            · exact hret 20#64 sA mA hokA (Or.inr (Or.inr rfl)) (fun _ => (hsr2 hc).2)
                (fun h => by cases h) hmA'
            · exact hret 0#64 sA mA hokA (Or.inl rfl) (fun h => by cases h)
                (fun h => by cases h) hmA'
            · exact hJbrk () mA ⟨sA, hokA, fun _ => hoomA' (Or.inl hc), hmA'⟩
            · have hsr_eq1 : sr = 1#64 := by
                rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨hcl0, hte_lt⟩ := hsr1 hsr_eq1
              have hoomA0 : sA.core.oom = 0#64 := hoomA' (Or.inr hsr_eq1)
              have hclA0 : sA.core.cur_level = 0 := by omega
              c0_call hProp
              refine ⟨c, F0, F_cur, sA, R, rfl, hokA.1.1.lengths, hokA.2.1, hokA.1.2.2.1,
                hokA.1.2.2.2.2, hmA',
                fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB
                  wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB scB mB hlenB hwB hndB
                  hrefsB hllB hextB hws2B hteB hfuelB _ hoomB hconflB hmB => ?_⟩
              obtain ⟨sB, hokB, hteB_eq, hclB0, hoomB', hconflB', hmB'⟩ :
                  ∃ sB : FullState, ReduceStateOk c F0 F_cur s sB ∧
                    sB.core.trail_end = teB ∧ sB.core.cur_level = 0 ∧
                    (pr = 0#64 → sB.core.oom = 0#64) ∧ (pr = 1#64 → F0.Unsat) ∧
                    (FullMem c sB ⋆ R) mB :=
                ⟨_, reduceStateOk_propagate0 hokA hclA0 hlenB hwB hndB hrefsB hllB hextB
                  hws2B hfuelB, rfl, hclA0, fun h0 => hoomB h0 hoomA0,
                  fun h1 => fullConflictInv_level0_unsat hwB hclA0 (hconflB h1), hmB⟩
              clear hmB valsB flagsB lvlB rsnsB trlB tpB propB unassB unflB wvecB arenaB
                wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB scB hlenB hwB hndB hrefsB
                hllB hextB hws2B hfuelB hoomB hconflB
              c0_go
              · exact hret 20#64 sB mB hokB (Or.inr (Or.inr rfl))
                  (fun _ => hconflB' hc) (fun h => by cases h) hmB'
              · exact hret 0#64 sB mB hokB (Or.inl rfl) (fun h => by cases h)
                  (fun h => by cases h) hmB'
              · have hte_bd : sB.core.trail_end ≤ c.max_vars :=
                  Nat.le_trans hokB.1.1.lengths.core_ok.trail_end_le
                    hokB.1.1.lengths.core_ok.cur_vars_le
                exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
                  ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
                    reduceStateOk_with_unflushed hokB 0#64, fun _ => hoomB' hc,
                    fun hpos => by change 0 < sB.core.cur_level at hpos; omega, hm⟩
          · intro L hL; c0_go
            exact hL (c.max_vars - sT.core.trail_end) () mT
              ⟨sT, rfl, hokT, hoomT, fun _ => hrmT, hmT⟩))
    (fun Jthen hJthen => by
      c0_to_group
      · exact hJthen () m4 ⟨s4, hok4, hoom4, hrm4, hm4⟩
      · -- `force = false`: join `Jelse` (`full_mark_reasons(h, false)`).
        refine wp_join_group
          (fun _ mE => ∃ sE : FullState, ReduceStateOk c F0 F_cur s sE ∧
            (s.core.oom = 0#64 → sE.core.oom = 0#64) ∧ (FullMem c sE ⋆ R) mE)
          (fun _ _ mE ⟨sE, hokE, hoomE, hmE⟩ => by
            clear s4 hok4 hoom4 hrm4 hm4 m4
            c0_call hMarkRsn
            refine ⟨c, F0, F_cur, sE, R, rfl, hokE.1.1.lengths, hokE.2.1, hmE,
              fun ar5 m5 hlen5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
            c0_go
            exact hJ5 () m5 ⟨_, reduceStateOk_mark_reasons hokE hlen5 hrefs5 hper5 hw5,
              hoomE, hm5⟩)
          (fun Jelse hJelse => by
            c0_go
            all_goals first
            | exact hJthen () m4 ⟨s4, hok4, hoom4, hrm4, hm4⟩
            | exact hJelse () m4 ⟨s4, hok4, hoom4, hm4⟩))

/-! ### `full_reduce` Step-7 `Func.wp` theorem (DW contract) -/

private theorem step7_reduce_dw_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullReduceSpec a m Q X →
      Func.wp Γ FullFidelityStep7.full_reduce_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsp0 : FullSparseInv c F0 s := ⟨⟨hlen, ⟨F_cur, hw⟩⟩, hlm, hnd, hext, hdm⟩
  have hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      ReduceStateOk c F0 F_cur s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hok hr hu hoom hml
    exact hQ r st ml hok.1 hok.2.1 hr hu hoom hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
      hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.1
      hok.2.2.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2.2.1
      hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hml
  c0_to_group
  c0_call hIsqrt
  intro r_isq hr_isq; c0_to_group
  obtain ⟨s0, hok_s0, hlen0, hw0, hoom0, hm0⟩ :
      ∃ s0 : FullState, ReduceStateOk c F0 F_cur s s0 ∧ s0.LengthsOk c ∧
        FullWitnessInv c F0 F_cur s0.core ∧ s0.core.oom = s.core.oom ∧ (FullMem c s0 ⋆ R) m :=
    ⟨{ s with scratch :=
        { s.scratch with
          reductions := s.scratch.reductions + 1#64
          reduce_limit := s.scratch.conflicts + r_isq } },
      reduceStateOk_with_scratch (reduceStateOk_refl hsp0 hw)
        { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len } rfl rfl rfl,
      ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩,
      hw, rfl, hm⟩
  clear hm hsp0 hlen hw hlm hnd hext hdm hQ hr_isq r_isq
  -- Join point after `if (h->unflushed > 0ULL)`.
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, ReduceStateOk c F0 F_cur s s1 ∧
      (s.core.oom = 0#64 → s1.core.oom = 0#64) ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · -- Continuation after `if (h->unflushed > 0ULL)`.
    rintro _ _ m1 ⟨s1, hok1, hoom1, hm1⟩
    clear s0 hok_s0 hlen0 hw0 hoom0 hm0
    c0_to_group
    c0_call hRecomp
    refine ⟨c, s1, R, rfl, hok1.1.1.lengths, hm1, fun sc1 m2 hsc1 hll1 hext1 hws21 hm2 => ?_⟩
    obtain ⟨s2, hok2, hoom2, hm2'⟩ :
        ∃ s2 : FullState, ReduceStateOk c F0 F_cur s s2 ∧
          (s.core.oom = 0#64 → s2.core.oom = 0#64) ∧ (FullMem c s2 ⋆ R) m2 :=
      ⟨{ s1 with scratch := sc1 }, reduceStateOk_with_scratch hok1 hsc1 hll1 hext1 hws21,
        hoom1, hm2⟩
    clear hm2 s1 hok1 hoom1 hm1 sc1 hsc1 hll1 hext1 hws21
    c0_to_group
    c0_call hMarkRsn
    refine ⟨c, F0, F_cur, s2, R, rfl, hok2.1.1.lengths, hok2.2.1, hm2',
      fun ar2 m3 hlen3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
    obtain ⟨s3, hok3, hoom3, hrm3', hm3'⟩ :
        ∃ s3 : FullState, ReduceStateOk c F0 F_cur s s3 ∧
          (s.core.oom = 0#64 → s3.core.oom = 0#64) ∧ FullReasonsMarked s3 ∧
          (FullMem c s3 ⋆ R) m3 :=
      ⟨{ s2 with core := { s2.core with arena := ar2 } },
        reduceStateOk_mark_reasons hok2 hlen3 hrefs3 hper3 hw3, hoom2, hrm3 rfl, hm3⟩
    clear hm3 s2 hok2 hoom2 hm2' ar2 hlen3 hrefs3 hper3 hrm3 hw3
    c0_to_group
    -- Loop 1: `while (p < h->arena_len)` collecting non-reason reducible refs into `red_refs`.
    refine wp_loop_inv
      (fun (rc, p, ()) mL =>
        rc.toNat ≤ c.red_cap ∧ p.toNat ≤ s3.core.arena_len ∧
        (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
        ∃ sL : FullState,
          sL.core.arena_len = s3.core.arena_len ∧
          ReduceStateOk c F0 F_cur s sL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
          FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧
          RedRefsOk sL rc.toNat ∧ (FullMem c sL ⋆ R) mL)
      (fun (_, p, ()) _ => s3.core.arena_len - p.toNat)
      (fun JL hLoopL => by
        c0_to_group
        refine hLoopL (0#64, 0#64, ()) m3 ⟨Nat.zero_le _, Nat.zero_le _, ?_, s3, rfl,
          hok3, hoom3, hrm3', rfl, fun _ h => by simp at h, hm3'⟩
        by_cases hz : s3.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hok3.2.1.arena (Nat.pos_of_ne_zero hz)))
      (fun JL (rc, p, ()) mL
          ⟨hrc_le, hp_le, hp_mem, sL, halenL, hokL, hoomL, hrmL, hrefsL, hrrL, hmL⟩ hLoopL => ?_)
    · have hlenL := hokL.1.1.lengths
      have halL := hlenL.core_ok.arena_len_le
      have haarL := hlenL.core_ok.arena_len_arr
      have hrrlL := hlenL.scratch_ok.red_refs_len
      c0_to_group
      · -- Loop 1 body: `p < sL.core.arena_len`.
        have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
        have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
          rw [hrefsL]; exact hp_mem.resolve_left (by omega)
        have hp_wf := hokL.2.1.arena.refs_wf p.toNat hp_in
        have hp_lt32 : p.toNat < 2 ^ 32 := by omega
        have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
        c0_to_group
        c0_call hArenaNext
        refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
        have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
          (cref := p.toNat) hp_wf.1
        have hnxt_mem := fullArenaClauseRefs_next_mem hokL.2.1.arena hp_in
        have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
            (p.setWidth 32).toNat)).setWidth 64).toNat =
            fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
          rw [hp_trunc, BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        -- Join point at end of loop-1 iteration (`p = (u64)n;`).
        refine wp_join_group
          (fun (rc', ()) mN =>
            rc'.toNat ≤ c.red_cap ∧
            ∃ sN : FullState,
              sN.core.arena_len = s3.core.arena_len ∧
              ReduceStateOk c F0 F_cur s sN ∧ (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
              FullReasonsMarked sN ∧ fullArenaClauseRefs sN = fullArenaClauseRefs s3 ∧
              RedRefsOk sN rc'.toNat ∧ (FullMem c sN ⋆ R) mN)
          (fun _ (rc', ()) mN ⟨hrcN, sN, halenN, hokN, hoomN, hrmN, hrefsN, hrrN, hmN⟩ => by
            c0_go
            exact hLoopL (rc', _, ()) mN (by dsimp only; rw [hn_eq]; omega)
              ⟨hrcN, by rw [hn_eq]; omega,
                by rw [hn_eq]
                   rcases hnxt_mem with hend | hmem
                   · exact Or.inl (hend.trans halenL)
                   · exact Or.inr (hrefsL ▸ hmem),
                sN, halenN, hokN, hoomN, hrmN, hrefsN, hrrN, hmN⟩)
          (fun JN hJN => ?_)
        c0_to_group
        · -- Both `(hdr & PH_RED) != 0` and `(hdr & PH_GARB) == 0`.
          refine wp_join_group
            (fun _ mU =>
              ∃ sU : FullState,
                sU.core.arena_len = s3.core.arena_len ∧
                ReduceStateOk c F0 F_cur s sU ∧ (s.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                FullReasonsMarked sU ∧ fullArenaClauseRefs sU = fullArenaClauseRefs s3 ∧
                RedRefsOk sU rc.toNat ∧
                (fullArenaHdr sU p.toNat &&& 0x00200000#32) =
                  (sL.core.arena[p.toNat]'(by omega) &&& 0x00200000#32) ∧
                (FullMem c sU ⋆ R) mU)
            (fun _ _ mU ⟨sU, halenU, hokU, hoomU, hrmU, hrefsU, hrrU, hhdrU, hmU⟩ => by
              have hlenU := hokU.1.1.lengths
              have hrrlU := hlenU.scratch_ok.red_refs_len
              c0_to_group
              refine wp_join_group
                (fun (rc', ()) mR =>
                  rc'.toNat ≤ c.red_cap ∧
                  ∃ sR : FullState,
                    sR.core.arena_len = s3.core.arena_len ∧
                    ReduceStateOk c F0 F_cur s sR ∧ (s.core.oom = 0#64 → sR.core.oom = 0#64) ∧
                    FullReasonsMarked sR ∧ fullArenaClauseRefs sR = fullArenaClauseRefs s3 ∧
                    RedRefsOk sR rc'.toNat ∧ (FullMem c sR ⋆ R) mR)
                (fun _ (rc', ()) mR hR => by c0_go; exact hJN (rc', ()) mR hR)
                (fun JR hJR => by
                  c0_to_group
                  · have hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32 := by
                      rw [hhdrU]; exact hc
                    have hp_inU : p.toNat ∈ fullArenaClauseRefs sU := by
                      rw [hrefsU]; exact hp_mem.resolve_left (by omega)
                    refine wp_join_group (fun (_ : Tup Val [.bool]) mK => mK = mU)
                      (by
                        rintro _ ⟨keep, ⟨⟩⟩ mK rfl
                        c0_go
                        all_goals first
                        | exact hJR (rc, ()) mK ⟨hrc_le, sU, halenU, hokU, hoomU, hrmU, hrefsU,
                            hrrU, hmU⟩
                        | (have hrc_lt : rc.toNat < c.red_cap := by c0_bound
                           have hrc1 : (rc + 1#64).toNat = rc.toNat + 1 := by c0_bound
                           let sU' : FullState :=
                             { sU with scratch := { sU.scratch with
                               red_refs := sU.scratch.red_refs.set rc.toNat (p.setWidth 32) } }
                           have hokU' : ReduceStateOk c F0 F_cur s sU' :=
                             reduceStateOk_with_scratch hokU
                               { hlenU.scratch_ok with red_refs_len := by simp [hrrlU] }
                               rfl rfl rfl
                           have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat :=
                             BitVec.eq_of_toNat_eq (by rw [hp_trunc, bv32_ofNat_toNat hp_lt32])
                           have hrrU' : RedRefsOk sU' (rc + 1#64).toNat := by
                             dsimp only [sU']; rw [hrc1, hp_sw]
                             exact redRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU hno_rsn hrrU
                           exact hJR (rc + 1#64, ()) _ ⟨by omega, sU', halenU, hokU', hoomU, hrmU,
                             hrefsU, hrrU', hm⟩))
                      (fun JK hJK => by c0_go; all_goals exact hJK (_, ()) mU rfl)
                  · exact hJR (rc, ()) mU ⟨hrc_le, sU, halenU, hokU, hoomU, hrmU, hrefsU, hrrU,
                      hmU⟩))
            (fun JU hJU => by
              c0_to_group
              · let v' := (sL.core.arena[p.toNat]'(by omega) &&& 0x07FFFFFF#32) |||
                  ((((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat)) &&& 31#32) - 1#32) <<<
                    (27 : Nat))
                let sU : FullState :=
                  { sL with core := { sL.core with arena := sL.core.arena.set p.toNat v' } }
                obtain ⟨hokU, hrmU, hrefsU, hrrU, hhdrU⟩ :=
                  reduceStateOk_update_used
                    (u := (((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat))
                    &&& 31#32) - 1#32)) hokL hrmL hrrL hp_in (by omega)
                exact hJU () _ ⟨sU, halenL, hokU, hoomL, hrmU, hrefsU.trans hrefsL, hrrU, hhdrU,
                  hm⟩
              · have hhdr_eq : fullArenaHdr sL p.toNat = sL.core.arena[p.toNat]'(by omega) := by
                  unfold fullArenaHdr fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                exact hJU () mL ⟨sL, halenL, hokL, hoomL, hrmL, hrefsL, hrrL, by rw [hhdr_eq],
                  hmL⟩)
        all_goals exact hJN (rc, ()) mL ⟨hrc_le, sL, halenL, hokL, hoomL, hrmL, hrefsL, hrrL, hmL⟩
      · -- Loop 1 exit (`p ≥ arena_len`): `if (rc > 0ULL)` + sweep/unmark tail.
        refine wp_join_group
          (fun _ m4 =>
            ∃ s4 : FullState, ReduceStateOk c F0 F_cur s s4 ∧
              (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullReasonsMarked s4 ∧
              (FullMem c s4 ⋆ R) m4)
          ?_ ?_
        · -- Tail after `if (rc > 0ULL)`: `if (force || ...)` sweep or `full_mark_reasons false`.
          rintro _ _ m4 ⟨s4, hok4, hoom4, hrm4, hm4⟩
          c0_to_group
          exact full_reduce_tail_wp Γ hMarkRsn hProp hSweep c F0 F_cur s R force Q X hret s4 m4
            hok4 hoom4 hrm4 hm4
        · -- `if (rc > 0ULL)` body and else branch.
          intro J4 hJ4
          clear hc hok3 hoom3 hrm3' hm3' halenL hrefsL hp_le hp_mem m3 JL hLoopL
          c0_to_group
          · -- `rc > 0ULL`: `full_sort_reds`, `full_ilog10`, garbage-marking loop.
            have hrr_bd : ∀ k < rc.toNat,
                (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := fun k hk => by
              have hmem := (hrrL k hk).1
              have hwf := (hokL.2.1.arena.refs_wf _ hmem).1
              omega
            c0_call hSortReds
            refine ⟨c, sL, R, rfl, hlenL, hrc_le, hrr_bd, hmL,
              fun scS mS hscS hllS hextS hws2S hpermS hmS => ?_⟩
            obtain ⟨sS, hokS, hoomS, hrmS, hrrS, hmS'⟩ :
                ∃ sS : FullState, ReduceStateOk c F0 F_cur s sS ∧
                  (s.core.oom = 0#64 → sS.core.oom = 0#64) ∧ FullReasonsMarked sS ∧
                  RedRefsOk sS rc.toNat ∧ (FullMem c sS ⋆ R) mS :=
              ⟨{ sL with scratch := scS },
                reduceStateOk_with_scratch hokL hscS hllS hextS hws2S, hoomL, hrmL,
                fun k hk => by
                  obtain ⟨j, hj, heq⟩ := hpermS k hk
                  change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
                    (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&& 0x00200000#32) = 0#32
                  rw [heq]; exact hrrL j hj,
                hmS⟩
            clear hmS scS hscS hllS hextS hws2S hpermS hrr_bd sL hokL hoomL hrmL hrrL hmL
              hlenL halL haarL hrrlL
            c0_to_group
            c0_call hIlog10
            intro logv hlog1 _
            have hlog_ne : logv ≠ 0#64 := fun hz => by rw [hz] at hlog1; cases hlog1
            c0_to_group
            -- Loop 2: `while (i < target && i < rc)` marking `PH_GARB`.
            refine wp_loop_inv
              (fun (i, ()) mI =>
                i.toNat ≤ rc.toNat ∧
                ∃ sI : FullState,
                  ReduceStateOk c F0 F_cur s sI ∧ (s.core.oom = 0#64 → sI.core.oom = 0#64) ∧
                  FullReasonsMarked sI ∧ RedRefsOk sI rc.toNat ∧ (FullMem c sI ⋆ R) mI)
              (fun (i, ()) _ => rc.toNat - i.toNat)
              (fun JI hLoopI => by
                c0_go
                exact hLoopI (0#64, ()) mS ⟨Nat.zero_le _, sS, hokS, hoomS, hrmS, hrrS, hmS'⟩)
              (fun JI (i, ()) mI ⟨hi_le, sI, hokI, hoomI, hrmI, hrrI, hmI⟩ hLoopI => ?_)
            · clear sS hokS hoomS hrmS hrrS hmS' mS hlog1 hlog_ne
              have hlenI := hokI.1.1.lengths
              have hrrlI := hlenI.scratch_ok.red_refs_len
              have halI := hlenI.core_ok.arena_len_le
              have haarI := hlenI.core_ok.arena_len_arr
              c0_split
              · c0_split
                · have hi_lt : i.toNat < rc.toNat := by c0_bound
                  have hi_rr : i.toNat < sI.scratch.red_refs.length := by omega
                  have hcr_ok := hrrI i.toNat hi_lt
                  have hcr_get : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat =
                      (sI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
                    rw [List.getElem?_eq_getElem hi_rr, Option.getD_some]
                  have hcr_mem : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                      fullArenaClauseRefs sI := by rw [hcr_get]; exact hcr_ok.1
                  have hcr_norsn : (fullArenaHdr sI (sI.scratch.red_refs[i.toNat]'hi_rr).toNat &&&
                      0x00200000#32) = 0#32 := by rw [hcr_get]; exact hcr_ok.2
                  have hcr_wf := hokI.2.1.arena.refs_wf _ hcr_mem
                  have hcr_lt : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat <
                      sI.core.arena.length := by have := hcr_wf.1; omega
                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                  c0_go
                  · obtain ⟨hokN, hrmN, _, hrrN⟩ :=
                      reduceStateOk_mark_garb (agN := _) hokI hrmI hrrI hcr_mem hcr_norsn
                        (by omega)
                    exact hLoopI (i + 1#64, ()) _ (by dsimp only; omega)
                      ⟨by omega, _, hokN, hoomI, hrmN, hrrN, hm⟩
                  · exact hLoopI (i + 1#64, ()) mI (by dsimp only; omega)
                      ⟨by omega, sI, hokI, hoomI, hrmI, hrrI, hmI⟩
                · c0_go; exact hJ4 () mI ⟨sI, hokI, hoomI, hrmI, hmI⟩
              · c0_go; exact hJ4 () mI ⟨sI, hokI, hoomI, hrmI, hmI⟩
          · exact hJ4 () mL ⟨sL, hokL, hoomL, hrmL, hmL⟩
  · -- Entry to `if (h->unflushed > 0ULL)`.
    intro J1 hJ1
    c0_to_group
    · -- `unflushed > 0`: backtrack to 0 if needed, then propagate, then `unflushed := 0`.
      refine wp_join_group
        (fun _ mB => ∃ sB : FullState, ReduceStateOk c F0 F_cur s sB ∧ sB.core.cur_level = 0 ∧
          (s.core.oom = 0#64 → sB.core.oom = 0#64) ∧ (FullMem c sB ⋆ R) mB)
        (fun _ _ mB ⟨sB, hokB, hclB, hoomB0, hmB⟩ => by
          clear hc s0 hok_s0 hlen0 hw0 hoom0 hm0
          c0_to_group
          c0_call hProp
          refine ⟨c, F0, F_cur, sB, R, rfl, hokB.1.1.lengths, hokB.2.1, hokB.1.2.2.1,
            hokB.1.2.2.2.2, hmB,
            fun pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
              wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP mP hlenP hwP hndP hrefsP hllP hextP
              hws2P hteP hfuelP _ hoomP hconflP hmP => ?_⟩
          obtain ⟨sP, hokP, hoomP', hconflP', hmP'⟩ :
              ∃ sP : FullState, ReduceStateOk c F0 F_cur s sP ∧
                (pr = 0#64 → s.core.oom = 0#64 → sP.core.oom = 0#64) ∧
                (pr = 1#64 → F0.Unsat) ∧ (FullMem c sP ⋆ R) mP :=
            ⟨_, reduceStateOk_propagate0 hokB hclB hlenP hwP hndP hrefsP hllP hextP hws2P hfuelP,
              fun h0 hso => hoomP h0 (hoomB0 hso),
              fun h1 => fullConflictInv_level0_unsat hwP hclB (hconflP h1), hmP⟩
          clear hmP hteP valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
            wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP hlenP hwP hndP hrefsP hllP hextP hws2P
            hfuelP hoomP hconflP
          c0_go
          · exact hret 20#64 sP mP hokP (Or.inr (Or.inr rfl)) (fun _ => hconflP' hc)
              (fun h => by cases h) hmP'
          · exact hret 0#64 sP mP hokP (Or.inl rfl) (fun h => by cases h)
              (fun h => by cases h) hmP'
          · exact hJ1 () _ ⟨{ sP with core := { sP.core with unflushed := 0#64 } },
              reduceStateOk_with_unflushed hokP 0#64, hoomP' hc, hm⟩)
        (fun JB hJB => by
          c0_to_group
          · c0_call hBacktrack
            refine ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, Nat.zero_le _, hm0,
              fun vals' lvl' rsns' trl' tp' te' prop' unass' sc' m' hlen' hw' hll' hext' hws2'
                hm' => ?_⟩
            c0_go
            exact hJB () m' ⟨_, reduceStateOk_backtrack0 hok_s0 hlen' hw' hll' hext' hws2', rfl,
              fun h => hoom0.trans h, hm'⟩
          · have hcl0 : s0.core.cur_level = 0 := by
              have hle := hlen0.core_ok.trail_end_le
              have hcv := hlen0.core_ok.cur_vars_le
              have hcl := hw0.cur_level_le
              c0_bound
            exact hJB () _ ⟨s0, hok_s0, hcl0, fun h => hoom0.trans h, hm0⟩)
    · exact hJ1 () _ ⟨s0, hok_s0, fun h => hoom0.trans h, hm0⟩
/-- Parametric `Func.wp` proof for Step-7 `full_reduce` against canonical `Full.fullReduceSpec`
(callee contracts identical to `FullDenseWatchLemmas2.full_reduce_wp`). -/
theorem full_reduce_step7_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, LeanQbe.T.Examples.Kissat.Full.fullReduceSpec a m Q X →
      Func.wp Γ fidStep7ReduceFn.body a m Q X := by
  have hwp := step7_reduce_dw_wp Γ hIsqrt hIlog10 hArenaNext hRecomp hMarkRsn hSortReds
    hBacktrack hProp hSweep
  rintro ⟨h, force, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, Fc, s, R, rfl, ⟨hlen, hw, hlm, hnd0, hext, hdm⟩, hm, hQ⟩
  exact hwp (c.hdr, force, ()) m Q X
    ⟨c, F0, Fc, s, R, rfl, hlen, hw, hlm, hnd0, hext, hdm, hm,
      fun r s' m' hdw hw' hr hu hoom hcl hfu hcv htmp htl _ _ _ _ _ _ hws2 hpos hm' =>
        hQ r s' m' ⟨hdw.1.lengths, hw', hdw.2.1, hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2⟩
          hr hcl hfu hcv htmp htl hws2 hu hoom (fun _ => hpos) hm'⟩

end Step7ReduceDW

/-! ## 2. `full_reduce_m6` (`FullM6Orch.m6ReduceSpec`) -/

section Step7ReduceM6

open Std Std.Sat Std.ExtHashMap LeanQbe.T.Examples.LratBytes
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

/-! ### Shared proof helpers -/

private theorem fid2_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem fid2_bv32_ofNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem fid2_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
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

private theorem fid2_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb; change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem; unfold fullArenaClauseGarb at hgb; rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private structure Fid2RedSt (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (ext : List (BitVec 64))
    (st : FullState) (ml : Mem 64) : Prop where
  inv : FullM6HdrInvW c F0 F_cur ext st
  cl : st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars = s.core.cur_vars
  tmp : st.core.tmp = s.core.tmp
  tl : st.core.tmp_len = s.core.tmp_len
  ws2 : st.scratch.work_stk2 = s.scratch.work_stk2
  pos : 0 < st.core.cur_level →
    st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
    st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
    st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end
  mem : (FullM6HdrMem c ext st ⋆ R) ml

private theorem fid2RedSt_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    Fid2RedSt c F0 F_cur s R ext s m :=
  ⟨hinv, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

private theorem fid2RedSt_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) {sc' : FullScratch}
    (hsc : sc'.LengthsOk c) (hll : sc'.last_learned = st.scratch.last_learned)
    (hext : sc'.extend_len = st.scratch.extend_len) (hws2 : sc'.work_stk2 = st.scratch.work_stk2)
    {ml' : Mem 64} (hm' : (FullM6HdrMem c ext { st with scratch := sc' } ⋆ R) ml') :
    Fid2RedSt c F0 F_cur s R ext { st with scratch := sc' } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨⟨hsp.1.core_ok, hsc⟩, hsp.2.1, hsp.2.2.1,
      hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll, hext⟩ (fun _ hr => hr),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2.trans hst.ws2, hst.pos, hm'⟩

private theorem fid2RedSt_w2a {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) (hc : s'.core = st.core) (hl : s'.LengthsOk c)
    (hms : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c ext' s' ⋆ R) ml') : Fid2RedSt c F0 F_cur s R ext' s' ml' := by
  have hsp := hst.inv.sparseW
  have hlm' : FullLitMarksClear c s' :=
    ⟨fun v hv => by rw [hc]; exact hsp.2.2.1.1 v hv, by simpa only [hc] using hsp.2.2.1.2⟩
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hl, hc ▸ hsp.2.1, hlm',
      fun r hr hng => by
        change r ∈ fullArenaClauseRefs s' at hr; unfold fullArenaClauseRefs at hr
        unfold fullArenaClauseGarb at hng; unfold fullArenaClauseLits
        rw [hc] at hr hng ⊢; exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 hms.extPres
        fun _ hr => by unfold fullArenaClauseRefs at hr ⊢; rwa [hc],
      hc ▸ hsp.2.2.2.2.2⟩
  exact ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext hsp', hc ▸ hst.cl, hc ▸ hst.fu, hc ▸ hst.cv,
    hc ▸ hst.tmp, hc ▸ hst.tl, hms.ws2.trans hst.ws2,
    fun hpos => by rw [hc] at hpos ⊢; exact hst.pos hpos, hm'⟩

private theorem fid2RedSt_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) (u' : BitVec 64)
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with unflushed := u' } } ⋆ R) ml') :
    Fid2RedSt c F0 F_cur s R ext { st with core := { st.core with unflushed := u' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
    ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
      Full.FullDenseWatchHelpers.fullWitnessInv_with_unflushed hsp.2.1 u', hsp.2.2.1,
      hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem fid2RedSt_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {ar' : List (BitVec 32)} (hst : Fid2RedSt c F0 F_cur s R ext st ml)
    (hlen' : ({ st with core := { st.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { st with core := { st.core with arena := ar' } } =
      fullArenaClauseRefs st)
    (hper : ∀ r ∈ fullArenaClauseRefs st,
      fullArenaClauseSize { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseSize st r ∧
      fullArenaClauseGarb { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseGarb st r ∧
      fullArenaClauseLits { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseLits st r)
    (hw' : FullWitnessInv c F0 F_cur { st.core with arena := ar' })
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with arena := ar' } } ⋆ R) ml') :
    Fid2RedSt c F0 F_cur s R ext { st with core := { st.core with arena := ar' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, fun r hr hng => by
      rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => by rwa [hrefs]),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem fid2RedSt_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} {m' : Mem 64} :
    let sB : FullState :=
      { core := { st.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = st.scratch.last_learned → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (FullM6HdrMem c ext sB ⋆ R) m' → Fid2RedSt c F0 F_cur s R ext sB m' :=
  fun hlen' hw' hll' hext' hws2' hm' => have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll', hext'⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩,
    Nat.zero_le _, hst.fu, hst.cv, hst.tmp, hst.tl, hws2'.trans hst.ws2,
    (fun h => by cases h), hm'⟩

private theorem fid2_call_fullBcpS15_red {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' → Γ f [i64] [i64] a m' Q' X')
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) (hcl0 : st.core.cur_level = 0)
    (hk : ∀ r s' m', Fid2RedSt c F0 F_cur s R ext s' m' → s'.core.cur_level = 0 →
      st.core.trail_end ≤ s'.core.trail_end → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → F0.Unsat) → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hst.inv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
    hsp.1, hsp.2.1, hsp.2.2.2.2.2, fullM6HdrMem_focus_full hst.mem, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hs' hw' hte hap _hdel hfu hr h0 h1 _h2 _hno hm'
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hs', hw', hsp.2.2.1, fid2_arenaVarsNodup_perm hap hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr =>
        by unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1],
      hsp.2.2.2.2.2⟩
  have hst' : Fid2RedSt c F0 F_cur s R ext s' m' :=
    ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hsp', hst.cl,
      Nat.le_trans hfu hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2,
      fun hpos => by change 0 < st.core.cur_level at hpos; omega, fullM6HdrMem_unfocus_full hm'⟩
  exact hk r s' m' hst' hcl0 hte.1 hr (fun h0eq hso => (h0 h0eq).2.1 hso)
    (fun h1eq => fid2_level0_unsat hw' hcl0 (h1 h1eq).2.2)

private theorem fid2RedSt_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} {m' : Mem 64} :
    let sA : FullState :=
      { core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level → vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    (FullM6HdrMem c ext sA ⋆ R) m' → Fid2RedSt c F0 F_cur s R ext sA m' := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA hm'
  have hsp := hst.inv.sparseW
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlenA, hwA, hsp.2.2.1, hndA, ⟨hllA, hextA ▸ hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2A.trans hst.ws2, fun hpos => ?_, hm'⟩
  obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
  obtain ⟨hcl, hv0, hl0, ht0, htp0, hte0⟩ := hst.pos hpos
  exact ⟨hcl, hv.trans hv0, hl.trans hl0, ht.trans ht0, htp.trans htp0, hte.trans hte0⟩

private def Fid2RedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

private theorem fid2RedRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : Fid2RedRefsOk s rc) :
    Fid2RedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } } (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32] using And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem fid2RedSt_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {p rc : Nat} {u : BitVec 32}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) (hrmL : FullReasonsMarked st)
    (hrrL : Fid2RedRefsOk st rc) (hp_in : p ∈ fullArenaClauseRefs st)
    (hp_ar : p < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set p
            ((st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) }
        scratch := st.scratch } ⋆ R) ml') :
    let v' := (st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { st with core := { st.core with arena := st.core.arena.set p v' } }
    Fid2RedSt c F0 F_cur s R ext sU ml' ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs st ∧ Fid2RedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[p]'hp_ar = fullArenaHdr st p := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := Full.FullDenseWatchHelpers.updateUsed_preserves_fullWitnessInv hsp.1 hsp.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hsp.2.2.2.1 r hr hng
  have hspU : FullSparseInvW c F0 F_cur sU :=
    ⟨hlenU, hwU, hsp.2.2.1, hndU, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsU]), hsp.2.2.2.2.2⟩
  have hrmU : FullReasonsMarked sU := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [(hperU _ hrs.1).2.2.2]; exact hrmL idx hidx hlp hlg
  have hrrU : Fid2RedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj; exact ⟨hrefsU ▸ hjm, (hperU _ hjm).2.2.2.trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspU, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmU, hrefsU, hrrU,
    by rw [(hperU p hp_in).2.2.2, ← hhdr_eq]⟩

private theorem fid2RedSt_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {cr rc : Nat} {agN : BitVec 64}
    (hst : Fid2RedSt c F0 F_cur s R ext st ml) (hrmI : FullReasonsMarked st)
    (hrrI : Fid2RedRefsOk st rc) (hcr_mem : cr ∈ fullArenaClauseRefs st)
    (hcr_norsn : (fullArenaHdr st cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch } ⋆ R) ml') :
    let sN : FullState :=
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch }
    Fid2RedSt c F0 F_cur s R ext sN ml' ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs st ∧ Fid2RedRefsOk sN rc := by
  intro sN
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[cr]'hcr_ar = fullArenaHdr st cr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := Full.FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hsp.2.1 hrmI hcr_norsn
  have hmg := Full.FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hsp.1 hsp.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hspN : FullSparseInvW c F0 F_cur sN :=
    ⟨hlenN, hwN, hsp.2.2.1, hndN hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsN]), hsp.2.2.2.2.2⟩
  have hrmN : FullReasonsMarked sN := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [hrsnN _ hrs.1]; exact hrmI idx hidx hlp hlg
  have hrrN : Fid2RedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj; exact ⟨hrefsN ▸ hjm, (hrsnN _ hjm).trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspN, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmN, hrefsN, hrrN⟩

private theorem fid2_reduce_jt_loop {Γ : Env} {ret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sT : FullState}
    {R : Mem 64 → Prop} {mT : Mem 64} {Q : Post [i64]} {X : XPost} {Jt : Cont [i64]}
    {e_else : Expr Val Cont [i64]} (hret : ret = 1#64)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJt : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ st : FullState,
        Fid2RedSt c F0 F_cur s R ext2 st m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64)) →
      Jt xs m)
    (hstT : Fid2RedSt c F0 F_cur s R ext2 sT mT)
    (hoomT : s.core.oom = 0#64 → sT.core.oom = 0#64) (hrmT : FullReasonsMarked sT) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun L => Blocks.cons (fun _ =>
      Expr.jnz (Arg.imm true)
        (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 2, ())) fun p_1 =>
            Expr.jnz (Arg.var p_1.fst) (Expr.jump Jt (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 3, ()))
                  fun p_2 =>
                Expr.jnz (Arg.var p_2.fst) (Expr.jump Jt (Arg.imm 0, ()))
                  (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                      fun p_3 =>
                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Jt (Arg.var ret, ()))
                      (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                          (Arg.var c.hdr, ()) fun p_4 =>
                        Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                            (Arg.var p_4.fst, Arg.imm 1, ())) fun p_5 =>
                          Expr.jnz (Arg.var p_5.fst) (Expr.jump Jt (Arg.imm 20, ()))
                            (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                                (Arg.var p_4.fst, Arg.imm 0, ())) fun p_6 =>
                              Expr.jnz (Arg.var p_6.fst) (Expr.jump Jt (Arg.imm 0, ()))
                                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ()))
                                    fun p_7 =>
                                  Expr.store (t := i64) (Arg.imm 0) (Arg.var p_7.fst)
                                    (Expr.jump L.fst ()))))))) e_else) .nil)
      (fun L => Expr.jump L.fst ())) mT := by
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState,
      rem = c.max_vars - st.core.trail_end ∧
      Fid2RedSt c F0 F_cur s R ext2 st ml ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (0 < st.core.cur_level → FullReasonsMarked st))
    ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst_st, hoom_st, hrm_st⟩
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    refine wp_m6Hdr_focus_frame hst_st.mem fun hmf => ?_
    c0_call hSweep
    refine ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
      rfl, hst_st.inv.sparseW.1, hst_st.inv.sparseW.2.1,
      hst_st.inv.sparseW.2.2.2.1, hst_st.inv.sparseW.2.2.2.2.2,
      hrm_st, hmf,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
        wstk' arena' alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
        hlenA hsr_dom hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 _hsr3 hmA => ?_⟩
    have hstA := fid2RedSt_arena_sweep hst_st hlenA hwA hndA hllA hextA
      hws2A (fun hpos => by
        obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
        exact ⟨hv, hl, ht, htp, hte⟩) (fullM6HdrMem_unfocus_full hmA)
    c0_hsteps_nogrp
    · exact hJt (20#64, ()) mA ⟨_, hstA, Or.inr (Or.inr rfl),
        fun _ => (hsr2 hc).2, fun h => by cases h⟩
    · exact hJt (0#64, ()) mA ⟨_, hstA, Or.inl rfl,
        (fun h => by cases h), fun h => by cases h⟩
    · simpa only [← hret] using hJt (1#64, ()) mA ⟨_, hstA, Or.inr (Or.inl rfl),
        (fun h => by cases h), fun _ _ => hoomA (Or.inl hc)⟩
    · have hsr_eq1 : sr = 1#64 := by
        rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl0, hteA⟩ := hsr1 hsr_eq1
      have hoomA0 : oom' = 0#64 := hoomA (Or.inr hsr_eq1)
      refine fid2_call_fullBcpS15_red rfl
        (fun _ _ _ _ h => hProp _ _ _ _ h) hstA hcl0
        fun pr sB mB hstB hclB hteB hrB h0B h1B => ?_
      c0_hsteps_nogrp
      · exact hJt (20#64, ()) mB ⟨sB, hstB, Or.inr (Or.inr rfl),
          fun _ => h1B hc, fun h => by cases h⟩
      · exact hJt (0#64, ()) mB ⟨sB, hstB, Or.inl rfl,
          (fun h => by cases h), fun h => by cases h⟩
      · refine wp_m6Hdr_focus_frame hstB.mem fun hmBf => ?_
        c0_hsteps_nogrp
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hstB.inv.sparseW.1.core_ok.trail_end_le
            hstB.inv.sparseW.1.core_ok.cur_vars_le
        dsimp only at hteB
        exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
          ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
            fid2RedSt_with_unflushed hstB 0#64 (fullM6HdrMem_unfocus (by assumption)),
            fun _ => h0B hc hoomA0,
            fun hpos => by change 0 < sB.core.cur_level at hpos; omega⟩
  · intro L hL
    c0_hsteps_nogrp
    exact hL (c.max_vars - sT.core.trail_end) () mT ⟨sT, rfl, hstT, hoomT, fun _ => hrmT⟩

private theorem fid2_reduce_j4_post {Γ : Env} {ret : Val i64} {force : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s4 : FullState} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jret : Cont [i64]} (hret : ret = 1#64)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJret : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ extR sR,
        Fid2RedSt c F0 F_cur s R extR sR m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) →
      Jret xs m)
    (hst4 : Fid2RedSt c F0 F_cur s R ext2 s4 m4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4) :
    wp Γ Q X (Expr.group (sig := [[i64]])
      (fun _Js => Blocks.cons (fun p => Expr.jump Jret (Arg.var p.fst, ())) Blocks.nil)
      fun Js => Expr.group (sig := [[]])
        (fun _Js_1 => Blocks.cons (fun _ =>
          Expr.group (sig := [[i64]])
            (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
            fun Js => Expr.group (sig := [[]])
              (fun Js_2 => Blocks.cons (fun _ =>
                Expr.jnz (Arg.imm true)
                  (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                    (Arg.var c.hdr, ()) fun p =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p.fst, Arg.imm 2, ())) fun p_1 =>
                      Expr.jnz (Arg.var p_1.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                            (Arg.var p.fst, Arg.imm 3, ())) fun p_2 =>
                          Expr.jnz (Arg.var p_2.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                            (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var ret, ()))
                                (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                                    (Arg.var c.hdr, ()) fun p =>
                                  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                      (Arg.var p.fst, Arg.imm 1, ())) fun p_3 =>
                                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                                      (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                                          (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                                        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                                          (Expr.let_ (Op.mk (.add i64)
                                              (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                                            Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                              (Expr.jump Js_2.fst ())))))))
                  (Expr.jump Js.fst (Arg.var ret, ()))) Blocks.nil)
              fun Js => Expr.jump Js.fst ()) Blocks.nil)
        fun Js_1 => Expr.jnz (Arg.var force) (Expr.jump Js_1.fst ())
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
                Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                  (Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
                    (Arg.var c.hdr, Arg.imm false, ()) fun _ =>
                    Expr.jump Js.fst (Arg.var ret, ())))) m4 := by
  refine wp_join_group (fun ((rret : Val i64), ()) m5 => ∃ s5 : FullState,
      Fid2RedSt c F0 F_cur s R ext2 s5 m5 ∧
      (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
      (rret = 20#64 → F0.Unsat) ∧
      (rret = 1#64 → s.core.oom = 0#64 → s5.core.oom = 0#64))
    (fun _ (rret, ()) m5 ⟨s5, hst5, hr5, hu5, ho5⟩ => by
      c0_hsteps_nogrp
      exact hJret (rret, ()) m5 ⟨ext2, s5, hst5, hr5, hu5, ho5⟩)
    (fun J5 hJ5 => by
      refine wp_join_group (fun _ mT => ∃ sT : FullState,
          Fid2RedSt c F0 F_cur s R ext2 sT mT ∧
          (s.core.oom = 0#64 → sT.core.oom = 0#64) ∧ FullReasonsMarked sT)
        (fun _ _ mT ⟨sT, hstT, hoomT, hrmT⟩ => by
          refine wp_join_group (fun ((rret : Val i64), ()) mt => ∃ st : FullState,
              Fid2RedSt c F0 F_cur s R ext2 st mt ∧
              (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
              (rret = 20#64 → F0.Unsat) ∧
              (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64))
            (fun _ (rret, ()) mt h => hJ5 (rret, ()) mt h)
            (fun Jt hJt => @fid2_reduce_jt_loop Γ ret c F0 F_cur ext2 s sT R mT Q X Jt
              (Expr.jump Jt (Arg.var ret, ())) hret hProp hSweep hJt hstT hoomT hrmT))
        (fun JT hJT => by
          refine wp_m6Hdr_focus_frame hst4.mem fun hm4f => ?_
          c0_hsteps_nogrp
          all_goals first
            | exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
            | (c0_call hMarkRsn
               refine ⟨c, F0, F_cur, s4, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
                 rfl, hst4.inv.sparseW.1, hst4.inv.sparseW.2.1, hm4f,
                 fun ar5 m5 hl5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
               c0_hsteps_nogrp
               simpa only [← hret] using hJ5 (1#64, ()) _
                 ⟨_, fid2RedSt_mark_reasons hst4 hl5 hrefs5 hper5 hw5
                   (fullM6HdrMem_unfocus_full hm5), Or.inr (Or.inl rfl),
                   (fun h => absurd h (by decide)), fun _ => hoom4⟩)))

private abbrev fid2MarkGarbExpr (c : FullCfg) (rc target : Val i64) (J4 : Cont []) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
      (fun Js_2 => Blocks.cons (fun p_30 =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var target, ()))
            fun p_31 =>
          Expr.jnz (Arg.var p_31.fst)
            (Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var rc, ()))
                fun p_32 =>
              Expr.jnz (Arg.var p_32.fst)
                (Expr.let_ (Op.mk (.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_33 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_33.fst, ()))
                      fun p_34 =>
                    Expr.load i32 (Arg.var p_34.fst) fun ld_7 =>
                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_7, ())) fun p_35 =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_36 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_36.fst, ()))
                              fun p_37 =>
                            Expr.load i32 (Arg.var p_37.fst) fun ld_8 =>
                              Expr.group (sig := [[]])
                                (fun _Js => Blocks.cons (fun _p =>
                                  Expr.let_ (Op.mk (.add i64) (Arg.var p_30.fst, Arg.imm 1, ()))
                                      fun p =>
                                    Expr.jump Js_2.fst (Arg.var p.fst, ())) Blocks.nil)
                                fun Js =>
                                Expr.let_ (Op.mk (.and i32) (Arg.var ld_8, Arg.imm 524288, ()))
                                    fun p_38 =>
                                  Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl)
                                      (Arg.var p_38.fst, Arg.imm 0, ())) fun p_39 =>
            Expr.jnz (Arg.var p_39.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_40 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_40.fst, ())) fun p_41 =>
                  Expr.let_ (Op.mk (.or i32) (Arg.var ld_8, Arg.imm 524288, ())) fun p_42 =>
                    Expr.store (t := i32) (Arg.var p_42.fst) (Arg.var p_41.fst)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_43 =>
                        Expr.load i64 (Arg.var p_43.fst) fun ld_9 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ld_9, Arg.imm 3, ())) fun p_44 =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p_35.fst, Arg.imm 2, ()))
                                fun p_45 =>
                              Expr.let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ()))
                                  fun p_46 =>
                                Expr.let_ (Op.mk (.add i64)
                                    (Arg.var c.pArena, Arg.var p_46.fst, ())) fun p_47 =>
                                  Expr.load i32 (Arg.var p_47.fst) fun ld =>
                                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_48 =>
                                      Expr.let_ (Op.mk (.add i64)
                                          (Arg.var p_44.fst, Arg.var p_48.fst, ())) fun p_49 =>
                                        Expr.let_ (Op.mk (.add i64)
                                            (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
                                          Expr.store (t := i64) (Arg.var p_49.fst) (Arg.var p.fst)
                                            (Expr.jump Js.fst ())))
              (Expr.jump Js.fst ()))
                (Expr.jump J4 ()))
            (Expr.jump J4 ())) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

private theorem fid2_reduce_mark_garb_loop {Γ : Env} {rc target : Val i64} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sS : FullState}
    {R : Mem 64 → Prop} {mS : Mem 64} {Q : Post [i64]} {X : XPost} {J4 : Cont []}
    (hJ4 : ∀ (xs : Tup Val []) (m : Mem 64), (∃ s4 : FullState,
      Fid2RedSt c F0 F_cur s R ext2 s4 m ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
      FullReasonsMarked s4) → J4 xs m)
    (hstS : Fid2RedSt c F0 F_cur s R ext2 sS mS)
    (hoomS : s.core.oom = 0#64 → sS.core.oom = 0#64) (hrmS : FullReasonsMarked sS)
    (hrc_le : rc.toNat ≤ c.red_cap) (hrrS : Fid2RedRefsOk sS rc.toNat) :
    wp Γ Q X (fid2MarkGarbExpr c rc target J4) mS := by
  refine wp_loop_inv
    (fun (i, ()) mI => i.toNat ≤ rc.toNat ∧ ∃ sI : FullState,
      Fid2RedSt c F0 F_cur s R ext2 sI mI ∧ (s.core.oom = 0#64 → sI.core.oom = 0#64) ∧
      FullReasonsMarked sI ∧ Fid2RedRefsOk sI rc.toNat)
    (fun (i, ()) _ => rc.toNat - i.toNat)
    (fun JI hLoopI => by
      c0_hsteps_nogrp
      exact hLoopI (0#64, ()) _ ⟨Nat.zero_le _, sS, hstS, hoomS, hrmS, hrrS⟩)
    (fun JI (i, ()) mI ⟨hi_le, sI, hstI, hoomI, hrmI, hrrI⟩ hLoopI => ?_)
  have hlenI := hstI.inv.sparseW.1
  have hrrlI := hlenI.scratch_ok.red_refs_len
  have halI := hlenI.core_ok.arena_len_le
  have haarI := hlenI.core_ok.arena_len_arr
  refine wp_m6Hdr_focus_frame hstI.mem fun hmIf => ?_
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < rc.toNat := by c0_bound
    have hi_rr : i.toNat < sI.scratch.red_refs.length := by omega
    have hcr_ok := hrrI i.toNat hi_lt
    have hcr_get : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat =
        (sI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem hi_rr, Option.getD_some]
    have hcr_mem : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sI := by
      rw [hcr_get]; exact hcr_ok.1
    have hcr_norsn : (fullArenaHdr sI
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat &&& 0x00200000#32) = 0#32 := by
      rw [hcr_get]; exact hcr_ok.2
    have hcr_wf := hstI.inv.sparseW.2.1.arena.refs_wf _ hcr_mem
    have hcr_lt : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat < sI.core.arena.length := by
      have := hcr_wf.1; omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
    have hcr_idx : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat =
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (Nat.lt_trans (sI.scratch.red_refs[i.toNat]'hi_rr).isLt (by decide))]
    have hcr_z_lt : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
        sI.core.arena.length := by rw [hcr_idx]; exact hcr_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ mN => ∃ sN : FullState,
        Fid2RedSt c F0 F_cur s R ext2 sN mN ∧ (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
        FullReasonsMarked sN ∧ Fid2RedRefsOk sN rc.toNat) ?_ ?_
    · rintro _ _ mN ⟨sN, hstN, hoomN, hrmN, hrrN⟩
      c0_hsteps_nogrp
      exact hLoopI (i + 1#64, ()) mN (by dsimp only; omega) ⟨by omega, sN, hstN, hoomN, hrmN, hrrN⟩
    · intro _Js hJs
      c0_hsteps_nogrp
      · simp only [hcr_idx] at hc hm
        obtain ⟨hstN, hrmN, _, hrrN⟩ := fid2RedSt_mark_garb (agN := _)
          hstI hrmI hrrI hcr_mem hcr_norsn (by omega) (fullM6HdrMem_unfocus hm)
        exact hJs () _ ⟨_, hstN, hoomI, hrmN, hrrN⟩
      · exact hJs () mI ⟨sI, hstI, hoomI, hrmI, hrrI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩

private theorem fid2_reduce_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J1 : Cont [i64]}
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hJ1 : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (ret, ()) => ∃ ext1 s1,
        Fid2RedSt c F0 F_cur s R ext1 s1 m ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
        (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) →
      J1 xs m)
    (hst0 : Fid2RedSt c F0 F_cur s R ext s0 m) (hlen0 : s0.LengthsOk c)
    (hs0_core : s0.core = s.core) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_10 =>
      Expr.load i64 (Arg.var p_10.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_11 =>
          Expr.jnz (Arg.var p_11.fst)
            (Expr.group (sig := [[]])
              (fun _Js_1 => Blocks.cons (fun _p_12 =>
                Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                    fun p_13 =>
                  Expr.group (sig := [[i64]])
                    (fun _Js_2 => Blocks.cons (fun p => Expr.jump J1 (Arg.var p.fst, ()))
                      Blocks.nil)
                    fun Js =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                        fun p_14 =>
                      Expr.jnz (Arg.var p_14.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.group (sig := [[i64]])
                          (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                            Blocks.nil)
                          fun Js =>
                          Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                              (Arg.var p_13.fst, Arg.imm 0, ())) fun p_15 =>
                            Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ()))
                                  fun p =>
                                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.imm 1, ()))))) Blocks.nil)
              fun Js =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 160, ())) fun p_12 =>
                Expr.load i64 (Arg.var p_12.fst) fun ld =>
                  Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ()))
                      fun p_13 =>
                    Expr.jnz (Arg.var p_13.fst)
                      (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                          (Arg.var c.hdr, Arg.imm 0, ()) fun _p =>
                        Expr.jump Js.fst ())
                      (Expr.jump Js.fst ()))
            (Expr.jump J1 (Arg.imm 1, ()))) m := by
  refine wp_m6Hdr_focus_frame hst0.mem fun hm0f => ?_
  c0_hsteps_nogrp
  · refine wp_join_group (fun _ mB => ∃ sB : FullState,
        Fid2RedSt c F0 F_cur s R ext sB mB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64))
      (fun _ _ mB ⟨sB, hstB, hclB, hoomB⟩ => by
        c0_hsteps_nogrp
        refine fid2_call_fullBcpS15_red rfl (fun _ _ _ _ h => hProp _ _ _ _ h) hstB hclB
          fun pr sP mP hstP hclP _hteP hrP h0P h1P => ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
            Fid2RedSt c F0 F_cur s R ext sJ mJ ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
            (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64))
          ?_ ?_
        · rintro _ ⟨ret, ⟨⟩⟩ mJ ⟨sJ, hstJ, hrJ, huJ, hoJ⟩
          c0_hsteps_nogrp; exact hJ1 (ret, ()) mJ ⟨ext, sJ, hstJ, hrJ, huJ, hoJ⟩
        · intro Jp1 hJp1
          c0_hsteps_nogrp
          · exact hJp1 (20#64, ()) mP ⟨sP, hstP, Or.inr (Or.inr rfl),
              fun _ => h1P (by assumption), fun h => by cases h⟩
          · refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
                Fid2RedSt c F0 F_cur s R ext sJ mJ ∧
                (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
                (ret = 20#64 → F0.Unsat) ∧
                (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64)) ?_ ?_
            · rintro _ ⟨ret, ⟨⟩⟩ mJ hJ
              c0_hsteps_nogrp; exact hJp1 (ret, ()) mJ hJ
            · intro Jp2 hJp2
              c0_hsteps_nogrp
              · exact hJp2 (0#64, ()) mP ⟨sP, hstP, Or.inl rfl,
                  fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · refine wp_m6Hdr_focus_frame hstP.mem fun hmPf => ?_
                c0_hsteps_nogrp
                exact hJp2 (1#64, ()) _ ⟨_, fid2RedSt_with_unflushed hstP 0#64
                    (fullM6HdrMem_unfocus (by assumption)),
                  Or.inr (Or.inl rfl), fun h => absurd h (by decide),
                  fun _ hso => h0P (by assumption) (hoomB hso)⟩)
      (fun JB hJB => by
        c0_hsteps_nogrp
        · c0_call hBacktrack
          refine ⟨c, s0, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen0,
            by have hmax := c.hmaxv; unfold dimacsBound at hmax
               have := hst0.inv.sparseW.2.1.cur_level_le
               have := hlen0.core_ok.trail_end_le
               have := hlen0.core_ok.cur_vars_le; omega,
            fun _ => by
              have hmax := c.hmaxv; unfold dimacsBound at hmax
              have := hst0.inv.sparseW.2.1.cur_level_le
              have := hlen0.core_ok.trail_end_le
              have := hlen0.core_ok.cur_vars_le; omega,
            hst0.inv.sparseW.2.1.trail_lits_lt, hm0f,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
              hlen' _ _ hcl' _ hsc' _ _ hw' _ hm' => ?_⟩
          have hcl'0 : cl' = 0 := by simpa using hcl'
          subst hcl'0
          obtain ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩ := hsc'
          c0_hsteps_nogrp
          exact hJB () _
            ⟨_, fid2RedSt_backtrack0 hst0 hlen'
              (hw' F0 F_cur hst0.inv.sparseW.2.1 (Nat.zero_le _))
              (by rw [hsc_eq]) (by rw [hsc_eq]) (by rw [hsc_eq])
              (fullM6HdrMem_unfocus_full hm'),
              rfl, fun h => by dsimp only; rwa [hs0_core]⟩
        · have hcl0 : s0.core.cur_level = 0 := by
            have hmax := c.hmaxv; unfold dimacsBound at hmax
            have hle := hlen0.core_ok.trail_end_le
            have hcv := hlen0.core_ok.cur_vars_le
            have hcl := hst0.inv.sparseW.2.1.cur_level_le
            c0_bound
          exact hJB () m ⟨s0, hst0, hcl0, fun h => hs0_core ▸ h⟩)
  · exact hJ1 (1#64, ()) m
      ⟨ext, s0, hst0, Or.inr (Or.inl rfl), fun h => absurd h (by decide),
        fun _ hso => by rwa [hs0_core]⟩

private def Fid2RedLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s3 : FullState) (R : Mem 64 → Prop) (ext2 : List (BitVec 64))
    (rc : Val i64) (sL : FullState) (mL : Mem 64) : Prop :=
  rc.toNat ≤ c.red_cap ∧ sL.core.arena_len = s3.core.arena_len ∧
  Fid2RedSt c F0 F_cur s R ext2 sL mL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
  FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧
  Fid2RedRefsOk sL rc.toNat ∧ (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mL

private abbrev fid2PushRcExpr (c : FullCfg) (rc p : Val i64) (keep : Val .bool)
    (Jrc2 : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var keep) (Expr.jump Jrc2 (Arg.var rc, ()))
    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 440, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var rc, Arg.var ld, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var rc, Arg.imm 4, ())) fun p_3 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_3.fst, ())) fun p_4 =>
                Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) fun p_37 =>
                  Expr.store (t := i32) (Arg.var p_37.fst) (Arg.var p_4.fst)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var rc, Arg.imm 1, ())) fun p_5 =>
                      Expr.jump Jrc2 (Arg.var p_5.fst, ())))
            (Expr.jump Jrc2 (Arg.var rc, ())))

private abbrev fid2KeepBoolExpr (glue t1 t2 : Val i64) (old_u : Val i32)
    (JK : Cont [.bool]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]])
    (fun _Js_3 => Blocks.cons (fun _ =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t2, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .uge i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 30, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump JK (Arg.imm false, ())))
          (Expr.jump JK (Arg.imm false, ()))) Blocks.nil)
    fun Js_3 =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t1, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .ugt i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 0, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump Js_3.fst ()))
          (Expr.jump Js_3.fst ())

private theorem fid2_reduce_push_rc {Γ : Env} {rc p : Val i64} {keep : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s3 sU : FullState} {R : Mem 64 → Prop} {mU : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jrc2 : Cont [i64]}
    (hJrc2 : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, Fid2RedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → Jrc2 xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt32 : p.toNat < 2 ^ 32) (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_inU : p.toNat ∈ fullArenaClauseRefs sU)
    (hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32)
    (hlenU : sU.LengthsOk c) (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : Fid2RedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : Fid2RedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (fid2PushRcExpr c rc p keep Jrc2) mU := by
  have hrrlU := hlenU.scratch_ok.red_refs_len; dsimp only [fid2PushRcExpr]; c0_hsteps_nogrp
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩
  · have hrc_lt : rc.toNat < c.red_cap := by
      have := BitVec.lt_def.mp (by assumption : rc < BitVec.ofNat 64 c.red_cap)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hrc1 : (rc + 1#64).toNat = rc.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    c0_hsteps_nogrp
    let scU' : FullScratch :=
      { sU.scratch with red_refs := sU.scratch.red_refs.set rc.toNat (p.setWidth 32) }
    let sU' : FullState := { sU with scratch := scU' }
    have hmU' : (FullMem c sU' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
    have hstU' := fid2RedSt_with_scratch hstU (sc' := scU')
      { hlenU.scratch_ok with red_refs_len := by simp [scU', hrrlU] }
      rfl rfl rfl (fullM6HdrMem_unfocus hmU')
    have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat := BitVec.eq_of_toNat_eq
      (by rw [hp_trunc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32])
    have hrrU' : Fid2RedRefsOk sU' (rc + 1#64).toNat := by
      dsimp only [sU', scU']; rw [hrc1, hp_sw]
      exact fid2RedRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU hno_rsn hrrU
    exact hJrc2 (rc + 1#64, ()) _
      ⟨sU', by dsimp only; omega, halenU, hstU', hoomU, hrmU, hrefsU, hrrU', hmU'⟩
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

private theorem fid2_reduce_keep_bool {Γ : Env} {glue t1 t2 : Val i64} {old_u : Val i32}
    {mU : Mem 64} {Q : Post [i64]} {X : XPost} {JK : Cont [.bool]}
    (hJK : ∀ b, JK (b, ()) mU) : wp Γ Q X (fid2KeepBoolExpr glue t1 t2 old_u JK) mU := by
  dsimp only [fid2KeepBoolExpr]; c0_hsteps_nogrp
  refine wp_join_group (fun (_ : Tup Val []) mS => mS = mU)
    (fun _ _ _ hmS => by cases hmS; c0_hsteps_nogrp <;> exact hJK _)
    (fun _ hJs => by c0_hsteps_nogrp <;> first | exact hJK true | exact hJs () mU rfl)

private theorem fid2_reduce_collect_jr {Γ : Env} {hdr : Val i32} {rc p t1 t2 : Val i64}
    {old_u : Val i32} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext2 : List (BitVec 64)} {s s3 sU _sL : FullState} {R : Mem 64 → Prop} {mU : Mem 64}
    {Q : Post [i64]} {X : XPost} {JR : Cont [i64]}
    (hJR : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, Fid2RedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → JR xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt : p.toNat < s3.core.arena_len) (hp_lt32 : p.toNat < 2 ^ 32)
    (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_mem : p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3)
    (hhdrU : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = (hdr &&& 0x00200000#32))
    (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : Fid2RedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : Fid2RedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 2097152, ())) fun p_32 =>
      Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_32.fst, Arg.imm 0, ())) fun p_33 =>
        Expr.jnz (Arg.var p_33.fst)
          (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 524287, ())) fun p_34 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_34.fst, ())) fun p_35 =>
              Expr.group (sig := [[.bool]]) (fun _Js_3 => Blocks.cons (fun p_36 =>
                Expr.group (sig := [[i64]]) (fun _Js_4 => Blocks.cons (fun q =>
                  Expr.jump JR (Arg.var q.fst, ())) Blocks.nil)
                  (fun Js => fid2PushRcExpr c rc p p_36.fst Js.fst)) Blocks.nil)
                (fun Js => fid2KeepBoolExpr p_35.fst t1 t2 old_u Js.fst))
          (Expr.jump JR (Arg.var rc, ()))) mU := by
  have hlenU := hstU.inv.sparseW.1
  c0_hsteps_nogrp
  · have hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32 := hhdrU ▸ hc
    have hp_inU : p.toNat ∈ fullArenaClauseRefs sU :=
      hrefsU ▸ hp_mem.resolve_left (by omega)
    refine wp_join_group (fun (_ : Tup Val [.bool]) mK => mK = mU) (by
      rintro _ ⟨keep, ⟨⟩⟩ mK rfl
      refine wp_join_group
        (fun (rc', ()) mR => ∃ sR, Fid2RedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
        (fun _ (rc', ()) mR hR => by c0_hsteps_nogrp; exact hJR (rc', ()) mR hR)
        (fun _ hJrc2 => fid2_reduce_push_rc hJrc2 hrc_le hred_cap hp_lt32 hp_trunc hp_inU
          hno_rsn hlenU halenU hstU hoomU hrmU hrefsU hrrU hmU))
      (fun _ hJK => by c0_hsteps_nogrp; exact fid2_reduce_keep_bool fun b => hJK (b, ()) mU rfl)
  · exact hJR (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

private theorem fid2_reduce_ret_wm {Γ : Env} {rret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {extR : List (BitVec 64)} {s sR : FullState} {R : Mem 64 → Prop}
    {mr : Mem 64} {Q : Post [i64]} {X : XPost}
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hQ : ∀ r ext' s' m', FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level → s'.core.cur_level = s.core.cur_level ∧
        s'.core.vals = s.core.vals ∧ s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (hstR : Fid2RedSt c F0 F_cur s R extR sR mr)
    (hrR : rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) (huR : rret = 20#64 → F0.Unsat)
    (hoR : rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_12 =>
      Expr.load i64 (Arg.var p_12.fst) fun ld =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
            (Arg.var c.hdr, Arg.imm 2, Arg.var ld, ()) fun _ =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 600, ())) fun p_14 =>
            Expr.load i64 (Arg.var p_14.fst) fun ld =>
              Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
                  (Arg.var c.hdr, Arg.imm 3, Arg.var ld, ()) fun _ =>
                Expr.ret (Arg.var rret, ())) mr := by
  refine wp_m6Hdr_focus_frame hstR.mem fun hmRf => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR.inv.cfgOk
    hstR.inv.extOk hstR.inv.sparseW.1 (fullM6HdrMem_unfocus hmRf)
    fun _ extR1 sR1 mR1 hcR1 hlR1 hmsR1 hextR1 _ hmR1 => ?_
  have hstR1 := fid2RedSt_w2a hstR hcR1 hlR1 hmsR1 hextR1 hmR1
  refine wp_m6Hdr_focus_frame hstR1.mem fun hmR1f => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR1.inv.cfgOk
    hstR1.inv.extOk hstR1.inv.sparseW.1 (fullM6HdrMem_unfocus hmR1f)
    fun _ extR2 sR2 mR2 hcR2 hlR2 hmsR2 hextR2 _ hmR2 => ?_
  have hstR2 := fid2RedSt_w2a hstR1 hcR2 hlR2 hmsR2 hextR2 hmR2
  c0_hsteps_nogrp
  exact hQ rret extR2 sR2 mR2 hstR2.inv hrR hstR2.cl hstR2.fu hstR2.cv hstR2.tmp hstR2.tl
    hstR2.ws2 huR (fun h1 hso => by rw [hcR2, hcR1]; exact hoR h1 hso) (fun _ => hstR2.pos)
    hstR2.mem

/-- Parametric `Func.wp` proof for Step-7 `full_reduce_m6` against `m6ReduceSpec`
(callee contracts identical to `FullM7FidelitySchedFixProof0.full_reduce_fid2_wp`). -/
theorem full_reduce_m6_step7_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReduceSpec a m Q X → Func.wp Γ fidStep7ReduceM6Fn.body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X hs
  rcases m6ReduceSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm0, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  show Func.wp Γ FullFidelityStep7.full_reduce_m6_body _ m Q X
  unfold Func.wp FullFidelityStep7.full_reduce_m6_body
  have hst_init := fid2RedSt_refl hinv hm0
  refine wp_m6Hdr_focus_frame hm0 fun hmf => ?_
  c0_hsteps_nogrp; c0_call hIsqrt; intro r_isq hsq1 hsq2 hsq3; clear hsq1 hsq2 hsq3
  dsimp only; c0_hsteps_nogrp
  let s0 : FullState := { s with scratch :=
    { s.scratch with
      reductions := s.scratch.reductions + 1#64
      reduce_limit := s.scratch.conflicts + r_isq } }
  have hlen0 : s0.LengthsOk c :=
    ⟨hinv.sparseW.1.core_ok, { hinv.sparseW.1.scratch_ok with
      walk_vals_len := hinv.sparseW.1.scratch_ok.walk_vals_len }⟩
  have hmf0 : (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
    simpa only [s0, BitVec.ofNat_eq_ofNat] using hm
  have hst0 : Fid2RedSt c F0 F_cur s R ext s0 m :=
    fid2RedSt_with_scratch hst_init hlen0.scratch_ok rfl rfl rfl (fullM6HdrMem_unfocus hmf0)
  refine wp_join_group (fun ((ret : Val i64), ()) m1 => ∃ ext1 s1,
      Fid2RedSt c F0 F_cur s R ext1 s1 m1 ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
      (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) ?_ ?_
  · rintro J1 ⟨ret, ⟨⟩⟩ m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
    refine wp_join_group (ts := [i64]) (fun (rret, ()) mr => ∃ extR sR,
        Fid2RedSt c F0 F_cur s R extR sR mr ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) ?_ ?_
    · rintro _ ⟨rret, ⟨⟩⟩ mr ⟨extR, sR, hstR, hrR, huR, hoR⟩
      exact fid2_reduce_ret_wm hSetWm hQ hstR hrR huR hoR
    · intro Jret hJret
      c0_hsteps_nogrp
      · have hc_ret : ret = 1#64 := hc
        have hoom1 : s.core.oom = 0#64 → s1.core.oom = 0#64 := ho1 hc_ret
        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRecomp _ _ _ _ h) hst1.inv.cfgOk
          hst1.inv.extOk hst1.inv.sparseW.1 hst1.mem
          fun _ ext2 s2 m2 hc2 hl2 hms2 hext2 _ hm2 => ?_
        have hst2 := fid2RedSt_w2a hst1 hc2 hl2 hms2 hext2 hm2
        have hoom2 : s.core.oom = 0#64 → s2.core.oom = 0#64 := fun h => hc2 ▸ hoom1 h
        c0_hsteps_nogrp; c0_call hMarkRsn
        refine ⟨c, F0, F_cur, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl,
          hst2.inv.sparseW.1, hst2.inv.sparseW.2.1, fullM6HdrMem_focus_full hst2.mem,
          fun ar3 m3 hl3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
        have hst3 :=
          fid2RedSt_mark_reasons hst2 hl3 hrefs3 hper3 hw3 (fullM6HdrMem_unfocus_full hm3)
        let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
        have hrm3' : FullReasonsMarked s3 := hrm3 rfl
        have hoom3 : s.core.oom = 0#64 → s3.core.oom = 0#64 := hoom2
        refine wp_m6Hdr_focus_frame hst3.mem fun hm3f => ?_
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (rc, p, ()) mL => p.toNat ≤ s3.core.arena_len ∧
            (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
            ∃ sL : FullState, Fid2RedLoopInv c F0 F_cur s s3 R ext2 rc sL mL)
          (fun (_, p, ()) _ => s3.core.arena_len - p.toNat)
          (fun JL hLoopL => by
            c0_hsteps_nogrp
            refine hLoopL (0#64, 0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3,
              Nat.zero_le _, rfl, hst3, hoom3, hrm3', rfl, fun _ h => by simp at h, hm3f⟩
            by_cases hz : s3.core.arena_len = 0
            · exact Or.inl hz.symm
            · exact Or.inr (Full.FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem
                hst3.inv.sparseW.2.1.arena (Nat.pos_of_ne_zero hz)))
          (fun JL (rc, p, ()) mL ⟨hp_le, hp_mem, sL, hL⟩ hLoopL => ?_)
        · have ⟨hrc_le, halenL, hstL, hoomL, hrmL, hrefsL, hrrL, hmL⟩ := hL
          have hlenL := hstL.inv.sparseW.1; have halL := hlenL.core_ok.arena_len_le
          have haarL := hlenL.core_ok.arena_len_arr; have hrrlL := hlenL.scratch_ok.red_refs_len
          c0_hsteps_nogrp
          · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
            have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
              rw [hrefsL]; exact hp_mem.resolve_left (by omega)
            have hp_wf := hstL.inv.sparseW.2.1.arena.refs_wf p.toNat hp_in
            have hp_lt32 : p.toNat < 2 ^ 32 := by omega
            have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
              rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
            c0_call hArenaNext
            refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hmL, ?_⟩
            have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
              (cref := p.toNat) hp_wf.1
            have hnxt_mem :=
              FullDenseWatchHelpers.fullArenaClauseRefs_next_mem hstL.inv.sparseW.2.1.arena hp_in
            have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
                (p.setWidth 32).toNat)).setWidth 64).toNat =
                fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
              rw [hp_trunc, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            refine wp_join_group
              (fun (rc', ()) mN =>
                ∃ sN : FullState, Fid2RedLoopInv c F0 F_cur s s3 R ext2 rc' sN mN)
              (fun _ (rc', ()) mN ⟨sN, hN⟩ => by
                c0_hsteps_nogrp
                refine hLoopL (rc', _, ()) mN (by dsimp only; rw [hn_eq]; omega)
                  ⟨by rw [hn_eq]; omega, ?_, sN, hN⟩
                rw [hn_eq]; rcases hnxt_mem with hend | hmem
                · exact Or.inl (hend.trans halenL)
                · exact Or.inr (hrefsL ▸ hmem))
              (fun JN hJN => ?_)
            c0_hsteps_nogrp
            · refine wp_join_group
                (fun _ mU => ∃ sU : FullState, sU.core.arena_len = s3.core.arena_len ∧
                  Fid2RedSt c F0 F_cur s R ext2 sU mU ∧ (s.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                  FullReasonsMarked sU ∧ fullArenaClauseRefs sU = fullArenaClauseRefs s3 ∧
                  Fid2RedRefsOk sU rc.toNat ∧ (fullArenaHdr sU p.toNat &&& 0x00200000#32) =
                    (sL.core.arena[p.toNat]'(by omega) &&& 0x00200000#32) ∧
                  (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU)
                (fun _ _ mU ⟨sU, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hhdrU, hmU⟩ => by
                  c0_hsteps_nogrp
                  refine wp_join_group
                    (fun (rc', ()) mR => ∃ sR, Fid2RedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
                    (fun _ (rc', ()) mR hR => by c0_hsteps_nogrp; exact hJN (rc', ()) mR hR)
                    (fun _ hJR => fid2_reduce_collect_jr (_sL := sL) hJR hrc_le hred_cap
                      (by omega) hp_lt32 hp_trunc hp_mem (by rw [hhdrU]) halenU hstU
                      hoomU hrmU hrefsU hrrU hmU))
                (fun JU hJU => by
                  c0_hsteps_nogrp
                  · let sU : FullState :=
                      { core := { sL.core with
                          arena := sL.core.arena.set p.toNat
                            ((sL.core.arena[p.toNat]'(by omega) &&& 0x07FFFFFF#32) |||
                              ((((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat)) &&&
                                31#32) - 1#32) <<< (27 : Nat))) }
                        scratch := sL.scratch }
                    have hmUf : (FullMem c sU ⋆
                        (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
                    obtain ⟨hstU, hrmU, hrefsU, hrrU, hhdrU⟩ := fid2RedSt_update_used
                      (u := (((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat))
                      &&& 31#32) - 1#32)) hstL hrmL hrrL hp_in (by omega)
                      (fullM6HdrMem_unfocus hmUf)
                    exact hJU () m ⟨sU, halenL, hstU, hoomL, hrmU, hrefsU.trans hrefsL, hrrU,
                      hhdrU, hmUf⟩
                  · have hhdr_eq :
                        fullArenaHdr sL p.toNat = sL.core.arena[p.toNat]'(by omega) := by
                      unfold fullArenaHdr fullArenaHdrCore
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact hJU () mL ⟨sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL,
                      by rw [hhdr_eq], hmL⟩)
            all_goals exact hJN (rc, ()) mL ⟨sL, hL⟩
          · refine wp_join_group
              (fun _ m4 => ∃ s4 : FullState, Fid2RedSt c F0 F_cur s R ext2 s4 m4 ∧
                (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullReasonsMarked s4)
              (fun _ _ m4 ⟨s4, hst4, hoom4, hrm4⟩ =>
                fid2_reduce_j4_post hc_ret hMarkRsn hProp hSweep hJret hst4 hoom4 hrm4)
              fun J4 hJ4 => by
                c0_hsteps_nogrp
                · have hrr_bd : ∀ k < rc.toNat,
                      (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := fun k hk => by
                    have hwf := (hstL.inv.sparseW.2.1.arena.refs_wf _ (hrrL k hk).1).1
                    omega
                  c0_call hSortReds
                  refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hrc_le, hrr_bd,
                    hmL, fun rr' mS hrr_len hpermS hmS => ?_⟩
                  let scS : FullScratch := { sL.scratch with red_refs := rr' }
                  have hstS := fid2RedSt_with_scratch hstL (sc' := scS)
                    { hlenL.scratch_ok with red_refs_len := hrr_len }
                    rfl rfl rfl (fullM6HdrMem_unfocus_full hmS)
                  have hrrS : Fid2RedRefsOk { sL with scratch := scS } rc.toNat := fun k hk => by
                    obtain ⟨j, hj, heq⟩ := hpermS k hk
                    change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
                      (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&& 0x00200000#32) = 0#32
                    rw [heq]; exact hrrL j hj
                  let sS : FullState := { sL with scratch := scS }
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma => ma = mS)
                    (fun _ ⟨arg, ⟨⟩⟩ ma hma => by
                      subst ma; c0_hsteps_nogrp; c0_call hLog10
                      refine m7Log10Q16Spec_of fun qlog _ _ => ?_
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i64])
                        (fun (qv, ()) mb => mb = mS ∧ 65536 ≤ qv.toNat)
                        (fun _ ⟨qv, ⟨⟩⟩ mb ⟨rfl, hqv_ge⟩ => by
                          have hqv_ne : qv ≠ 0#64 := fun hz => by
                            rw [hz] at hqv_ge; exact absurd hqv_ge (by decide)
                          c0_hsteps_nogrp
                          exact fid2_reduce_mark_garb_loop (sS := sS) hJ4 hstS hoomL hrmL hrc_le
                            hrrS)
                        (fun Jq hJq => by
                          c0_hsteps_nogrp
                          · exact hJq (65536#64, ()) mS ⟨rfl, by decide⟩
                          · exact hJq (qlog, ()) mS ⟨rfl, by c0_bound⟩))
                    (fun Jarg hJarg => by c0_hsteps_nogrp <;> exact hJarg (_, ()) mS rfl)
                · exact hJ4 () mL ⟨sL, hstL, hoomL, hrmL⟩
      · exact hJret (ret, ()) m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
  · intro J1 hJ1; exact fid2_reduce_unflushed hBacktrack hProp hJ1 hst0 hlen0 rfl

end Step7ReduceM6

end LeanQbe.T.Examples.Kissat.FullFidelityStep7
