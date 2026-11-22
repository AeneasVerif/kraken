module

public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Unified M4 `full_reduce` Proof (`FullM4ReduceLemmas`, UNSAT-Only)

Proves `m4_reduce_wp` for `FullM4.full_reduce_body` against `m4ReduceSpec`:
- `force = true` (used by `full_learn_clause`): skips `full_promote_reasons` (`!force = false`) and
  satisfies exact canonical `Full.fullReduceSpec` (preserving fixed `F_cur` and `work_stk2`).
- `force = false` (used by periodic reduction in `full_simplify` / `full_search`): promotes trail
  reasons via `full_promote_reasons` when `0 < cur_level` and satisfies `m4ReduceLooseSpec`
  (preserving `FullSparseInv c F0 s'`, `cur_level`, `fuel`, `oom`, and `r = 20#64 → F0.Unsat`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullDenseWatchSpecs FullDenseWatchHelpers
open scoped FullArenaTactics

/-- Relaxed `full_reduce(h, false)` contract permitting `full_promote_reasons(h)` to mutate
`arena`, `glue_used`, and `work_stk2` (preserving `FullSparseInv c F0 s'` and UNSAT soundness). -/
def m4ReduceLooseSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ Full.FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      Full.FullSparseInv c F0 s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Unified `full_reduce` contract: exact `Full.fullReduceSpec` when `force = true` (so
`full_learn_clause` sees its exact canonical callee spec), and `m4ReduceLooseSpec` when
`force = false`. -/
def m4ReduceSpec : Spec [i64, .bool] [i64] := fun (h, force, ()) m Q X =>
  match force with
  | true => Full.fullReduceSpec (h, true, ()) m Q X
  | false => m4ReduceLooseSpec (h, false, ()) m Q X

open Lean Elab Tactic in
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

section Helpers

private def ReduceStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullDenseWatchSpecs.FullSparseInv c F0 s' ∧
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
    {s : FullState} (hsp : FullDenseWatchSpecs.FullSparseInv c F0 s)
    (hw : FullWitnessInv c F0 F_cur s.core) :
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
  have hsp' : FullDenseWatchSpecs.FullSparseInv c F0 { s1 with scratch := sc' } :=
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
  have hsp' : FullDenseWatchSpecs.FullSparseInv c F0
      { s1 with core := { s1.core with unflushed := u' } } :=
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
  have hnd : FullDenseWatchSpecs.FullArenaVarsNodup s3 := fun r hr hng => by
    rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
    exact h2.1.2.2.1 r hr hng
  have hll : FullDenseWatchSpecs.FullLastLearnedWf s3 := fun i hi => by
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
  have hllB : FullDenseWatchSpecs.FullLastLearnedWf sB := fun i hi => by
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
    FullDenseWatchSpecs.FullArenaVarsNodup sB →
    (∀ ref ∈ fullArenaClauseRefs sA, ref ∈ fullArenaClauseRefs sB) →
    scB.last_learned = sA.scratch.last_learned →
    scB.extend_len = sA.scratch.extend_len →
    scB.work_stk2 = sA.scratch.work_stk2 →
    fuelB.toNat ≤ sA.core.fuel.toNat →
    ReduceStateOk c F0 F_cur s sB := by
  intro sB hlenB hwB hndB hrefsB hllB hextB hws2B hfuelB
  have hll' : FullDenseWatchSpecs.FullLastLearnedWf sB := fun i hi => by
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
    FullDenseWatchSpecs.FullArenaVarsNodup sA → FullDenseWatchSpecs.FullLastLearnedWf sA →
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
    (hokL : ReduceStateOk c F0 F_cur s sL) (hrmL : FullDenseWatchSpecs.FullReasonsMarked sL)
    (hrrL : RedRefsOk sL rc) (hp_in : p ∈ fullArenaClauseRefs sL)
    (hp_ar : p < sL.core.arena.length) :
    let v' := (sL.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { sL with core := { sL.core with arena := sL.core.arena.set p v' } }
    ReduceStateOk c F0 F_cur s sU ∧ FullDenseWatchSpecs.FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs sL ∧ RedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (sL.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hhdr_eq : sL.core.arena[p]'hp_ar = fullArenaHdr sL p := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := updateUsed_preserves_fullWitnessInv hokL.1.1.lengths hokL.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullDenseWatchSpecs.FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hokL.1.2.2.1 r hr hng
  have hllU : FullDenseWatchSpecs.FullLastLearnedWf sU := fun i hi => by
    change sL.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sL.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sU
    rw [hrefsU]; exact hokL.1.2.2.2.1.1 i hi
  have hrmU : FullDenseWatchSpecs.FullReasonsMarked sU := fun idx hidx hlp hlg => by
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
    (hokI : ReduceStateOk c F0 F_cur s sI) (hrmI : FullDenseWatchSpecs.FullReasonsMarked sI)
    (hrrI : RedRefsOk sI rc) (hcr_mem : cr ∈ fullArenaClauseRefs sI)
    (hcr_norsn : (fullArenaHdr sI cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < sI.core.arena.length) :
    let sN : FullState :=
      { sI with core := { sI.core with
        arena := sI.core.arena.set cr (sI.core.arena[cr]'hcr_ar ||| 0x00080000#32)
        arena_garbage := agN } }
    ReduceStateOk c F0 F_cur s sN ∧ FullDenseWatchSpecs.FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs sI ∧ RedRefsOk sN rc := by
  intro sN
  have hhdr_eq : sI.core.arena[cr]'hcr_ar = fullArenaHdr sI cr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := markGarb_nonact_of_reasonsMarked hokI.2.1 hrmI hcr_norsn
  have hmg := markGarb_preserves_fullWitnessInv hokI.1.1.lengths hokI.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hllN : FullDenseWatchSpecs.FullLastLearnedWf sN := fun j hj => by
    change sI.scratch.last_learned[j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sI.scratch.last_learned[j]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sN
    rw [hrefsN]; exact hokI.1.2.2.2.1.1 j hj
  have hrmN : FullDenseWatchSpecs.FullReasonsMarked sN := fun idx hidx hlp hlg => by
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

private theorem dwIsqrt_adapter {Γ : Env}
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullIsqrtSpec a m Q X →
      Γ "full_isqrt" [i64] [i64] a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  exact hIsqrt _ m Q X fun r hsq _ _ => hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq)

private theorem dwRecomputeTiers_adapter {Γ : Env}
    (hRecomp : ∀ a m Q X, Full.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hRecomp _ m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hcore hlen' hpres hm' => ?_⟩
  rcases s' with ⟨c', sc'⟩
  change c' = s.core at hcore
  subst hcore
  exact hQ sc' m' hlen'.scratch_ok hpres.1.1 hpres.1.2 hpres.2.2.1 hm'

private theorem dwSortReds_adapter {Γ : Env}
    (hSortReds : ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
  refine hSortReds _ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, fun rr' m' hrr hmem hm' => ?_⟩
  exact hQ { s.scratch with red_refs := rr' } m'
    { hlen.scratch_ok with red_refs_len := hrr } rfl rfl rfl hmem hm'

private theorem dwBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hle, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_bd : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  have htg_bd : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
    intro _; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd, hw.trail_lits_lt, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' _ _ hcl' hps _ _ _ hwt _ hm' => ?_⟩
  have hmin : cl' = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
  subst hmin
  exact hQ vals' lvl' rsns' trl' tp' te' prop' unass' sc' m'
    hlen' (hwt F0 F_cur hw hle) hps.1.1 hps.1.2 hps.2.2.1 hm'

private theorem dwPropagate_adapter {Γ : Env}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfl hr hr0 hr1 _ _ hm'
  have hnd' : FullDenseWatchSpecs.FullArenaVarsNodup
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases' } } := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom'
    { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } m'
    hlen' hw' hnd' (fun ref href => by
      change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    rfl rfl rfl htr.1 hfl hr (fun h0 => (hr0 h0).2.1)
    (fun h1 => (hr1 h1).2.2.elim
      (fun ⟨ht, h0, h1', hf0, hf1, hent⟩ => Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩) Or.inr) hm'

private theorem dwArenaSweep_adapter {Γ : Env}
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, hQ⟩
  refine hSweep _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' m'
    hlen' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' m' hlen' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'

private theorem dwSparse_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseWatchSpecs.FullSparseInv c F0 s)
    (hw : FullWitnessInv c F0 F_cur s.core) : Full.FullSparseInv c F0 s :=
  ⟨⟨h.1.lengths, F_cur, hw⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem canon_to_dwSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : Full.FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core) :
    FullDenseWatchSpecs.FullSparseInv c F0 s :=
  ⟨⟨h.1.lengths, F_cur, hw⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private def m4ReduceTailExpr (hdr : Val i64) (force : Val .bool) : Expr Val Cont [i64] :=
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

private theorem m4_reduce_tail_wp (Γ : Env)
    (hMarkRsn : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur2 : List (List Nat)) (s2 : FullState) (R : Mem 64 → Prop)
    (force : Val .bool) (Q : Post [i64]) (X : XPost)
    (hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      ReduceStateOk c F0 F_cur2 s2 st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s2.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml)
    (s5 : FullState) (m5 : Mem 64) (hok5 : ReduceStateOk c F0 F_cur2 s2 s5)
    (hoom5 : s2.core.oom = 0#64 → s5.core.oom = 0#64)
    (hrm5 : FullDenseWatchSpecs.FullReasonsMarked s5)
    (hm5 : (FullMem c s5 ⋆ R) m5) :
    wp Γ Q X (m4ReduceTailExpr c.hdr force) m5 := by
  unfold m4ReduceTailExpr
  refine wp_join_group
    (fun _ m6 => ∃ s6 : FullState, ReduceStateOk c F0 F_cur2 s2 s6 ∧
      (s2.core.oom = 0#64 → s6.core.oom = 0#64) ∧ (FullMem c s6 ⋆ R) m6)
    (fun _ _ m6 ⟨s6, hok6, hoom6, hm6⟩ => by
      c0_go
      exact hret 1#64 s6 m6 hok6 (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hoom6) hm6)
    (fun J6 hJ6 => ?_)
  c0_to_group
  refine wp_join_group
    (fun _ mT =>
      ∃ sT : FullState, ReduceStateOk c F0 F_cur2 s2 sT ∧
        (s2.core.oom = 0#64 → sT.core.oom = 0#64) ∧
        FullDenseWatchSpecs.FullReasonsMarked sT ∧ (FullMem c sT ⋆ R) mT)
    (fun _ _ mT ⟨sT, hokT, hoomT, hrmT, hmT⟩ => by
      clear s5 hok5 hoom5 hrm5 hm5 m5
      c0_to_group
      refine wp_join_group
        (fun _ mK => ∃ sK : FullState, ReduceStateOk c F0 F_cur2 s2 sK ∧
          (s2.core.oom = 0#64 → sK.core.oom = 0#64) ∧ (FullMem c sK ⋆ R) mK)
        (fun _ _ mK hK => by c0_go; exact hJ6 () mK hK)
        (fun Jbrk hJbrk => by
          c0_to_group
          refine wp_loop_group
            (fun rem () ml => ∃ st : FullState,
              rem = c.max_vars - st.core.trail_end ∧
              ReduceStateOk c F0 F_cur2 s2 st ∧
              (s2.core.oom = 0#64 → st.core.oom = 0#64) ∧
              (0 < st.core.cur_level → FullDenseWatchSpecs.FullReasonsMarked st) ∧
              (FullMem c st ⋆ R) ml) ?_ ?_
          · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hoom_st, hrm_st, hm_st⟩
            dsimp only [Blocks.get]
            refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
            c0_call (dwArenaSweep_adapter hSweep)
            refine ⟨c, F0, F_cur2, st, R, rfl, hok_st.1.1.lengths, hok_st.2.1,
              hok_st.1.2.2.1, hok_st.1.2.2.2.2, hrm_st, hm_st,
              fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena'
                alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hwA hndA hllA hextA
                hws2A hsr_dom hoomA hposA hsr1 hsr2 hmA => ?_⟩
            obtain ⟨sA, hokA, _, _, hoomA', hmA'⟩ :
                ∃ sA : FullState, ReduceStateOk c F0 F_cur2 s2 sA ∧
                  sA.core.cur_level = st.core.cur_level ∧ sA.core.trail_end = te' ∧
                  (sr = 0#64 ∨ sr = 1#64 → sA.core.oom = 0#64) ∧ (FullMem c sA ⋆ R) mA :=
              ⟨_, reduceStateOk_arena_sweep hok_st hlenA hwA hndA hllA hextA hws2A
                (fun hpos => by
                  obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
                  exact ⟨hv, hl, ht, htp, hte⟩),
                rfl, rfl, hoomA, hmA⟩
            clear hmA vals' flags' lvl' rsns' trl' tp' unass' unfl' wvec' wstk' arena'
              alen' wlen' wu' fred' ni' nr' nb' oom' sc' hlenA hwA hndA hllA hextA hws2A
              hoomA hposA
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
              c0_call (dwPropagate_adapter hProp)
              refine ⟨c, F0, F_cur2, sA, R, rfl, hokA.1.1.lengths, hokA.2.1,
                hokA.1.2.2.1, hokA.1.2.2.2.2, hmA',
                fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB
                  arenaB wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB scB mB hlenB hwB
                  hndB hrefsB hllB hextB hws2B hteB hfuelB _ hoomB hconflB hmB => ?_⟩
              obtain ⟨sB, hokB, _, _, hoomB', hconflB', hmB'⟩ :
                  ∃ sB : FullState, ReduceStateOk c F0 F_cur2 s2 sB ∧
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
      · exact hJthen () m5 ⟨s5, hok5, hoom5, hrm5, hm5⟩
      · refine wp_join_group
          (fun _ mE => ∃ sE : FullState, ReduceStateOk c F0 F_cur2 s2 sE ∧
            (s2.core.oom = 0#64 → sE.core.oom = 0#64) ∧ (FullMem c sE ⋆ R) mE)
          (fun _ _ mE ⟨sE, hokE, hoomE, hmE⟩ => by
            clear s5 hok5 hoom5 hrm5 hm5 m5
            c0_call hMarkRsn
            refine ⟨c, F0, F_cur2, sE, R, rfl, hokE.1.1.lengths, hokE.2.1, hmE,
              fun ar5 m5 hlen5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
            c0_go
            exact hJ6 () m5 ⟨_, reduceStateOk_mark_reasons hokE hlen5 hrefs5 hper5 hw5,
              hoomE, hm5⟩)
          (fun Jelse hJelse => by
            c0_go
            all_goals first
            | exact hJthen () m5 ⟨s5, hok5, hoom5, hrm5, hm5⟩
            | exact hJelse () m5 ⟨s5, hok5, hoom5, hm5⟩))

private def m4ReduceUnflushedExpr (hdr : Val i64) (J1 : Cont []) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var hdr, Arg.imm 512, ()) }
    fun p =>
    Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
          args := (Arg.var ld, Arg.imm 0, ()) }
        fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.group (sig := [[]])
            (fun _ =>
              Blocks.cons
                (fun _ =>
                  Expr.call "full_propagate" (as := [i64]) (bs := [i64])
                      (Arg.var hdr, ()) fun p =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
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
                              Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                (Expr.jump J1 ()))))
                Blocks.nil)
            fun Js =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var hdr, Arg.imm 160, ()) }
              fun p =>
              Expr.load i64 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                    args := (Arg.var ld, Arg.imm 0, ()) }
                  fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.call "full_backtrack" (as := [i64, i64]) (bs := [])
                        (Arg.var hdr, Arg.imm 0, ()) fun _ =>
                      Expr.jump Js.fst ())
                    (Expr.jump Js.fst ()))
          (Expr.jump J1 ())

private theorem m4_reduce_unflushed_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur0 : List (List Nat)) (s s0 : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (hFinish : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      ReduceStateOk c F0 F_cur0 s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml)
    (hok_s0 : ReduceStateOk c F0 F_cur0 s s0)
    (hoom_s0 : s.core.oom = 0#64 → s0.core.oom = 0#64) (hm0 : (FullMem c s0 ⋆ R) m)
    (J1 : Cont [])
    (hJ1 : ∀ (xs : Tup Val []) (m1 : Mem 64),
      (∃ s1 : FullState, ReduceStateOk c F0 F_cur0 s s1 ∧
        (s.core.oom = 0#64 → s1.core.oom = 0#64) ∧ (FullMem c s1 ⋆ R) m1) →
      J1 xs m1) :
    wp Γ Q X (m4ReduceUnflushedExpr c.hdr J1) m := by
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  unfold m4ReduceUnflushedExpr
  c0_to_group
  · refine wp_join_group
      (fun _ mB => ∃ sB : FullState, ReduceStateOk c F0 F_cur0 s sB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64) ∧ (FullMem c sB ⋆ R) mB)
      (fun _ _ mB ⟨sB, hokB, hclB, hoomB0, hmB⟩ => by
        c0_to_group
        c0_call (dwPropagate_adapter hProp)
        refine ⟨c, F0, F_cur0, sB, R, rfl, hokB.1.1.lengths, hokB.2.1, hokB.1.2.2.1,
          hokB.1.2.2.2.2, hmB,
          fun pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
            wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP mP hlenP hwP hndP hrefsP hllP hextP
            hws2P hteP hfuelP _ hoomP hconflP hmP => ?_⟩
        obtain ⟨sP, hokP, hoomP', hconflP', hmP'⟩ :
            ∃ sP : FullState, ReduceStateOk c F0 F_cur0 s sP ∧
              (pr = 0#64 → s.core.oom = 0#64 → sP.core.oom = 0#64) ∧
              (pr = 1#64 → F0.Unsat) ∧ (FullMem c sP ⋆ R) mP :=
          ⟨_, reduceStateOk_propagate0 hokB hclB hlenP hwP hndP hrefsP hllP hextP hws2P hfuelP,
            fun h0 hso => hoomP h0 (hoomB0 hso),
            fun h1 => fullConflictInv_level0_unsat hwP hclB (hconflP h1), hmP⟩
        clear hmP hteP valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
          wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP hlenP hwP hndP hrefsP hllP hextP hws2P
          hfuelP hoomP hconflP
        c0_go
        · exact hFinish 20#64 sP mP hokP (Or.inr (Or.inr rfl)) (fun _ => hconflP' hc)
            (fun h => by cases h) hmP'
        · exact hFinish 0#64 sP mP hokP (Or.inl rfl) (fun h => by cases h)
            (fun h => by cases h) hmP'
        · exact hJ1 () _ ⟨{ sP with core := { sP.core with unflushed := 0#64 } },
            reduceStateOk_with_unflushed hokP 0#64, hoomP' hc, hm⟩)
      (fun JB hJB => by
        c0_to_group
        · c0_call (dwBacktrack_adapter hBacktrack)
          refine ⟨c, F0, F_cur0, s0, R, rfl, hok_s0.1.1.lengths, hok_s0.2.1, Nat.zero_le _, hm0,
            fun vals' lvl' rsns' trl' tp' te' prop' unass' sc' m' hlen' hw' hll' hext' hws2'
              hm' => ?_⟩
          c0_go
          exact hJB () m' ⟨_, reduceStateOk_backtrack0 hok_s0 hlen' hw' hll' hext' hws2', rfl,
            hoom_s0, hm'⟩
        · have hcl0 : s0.core.cur_level = 0 := by
            have hle := hok_s0.1.1.lengths.core_ok.trail_end_le
            have hcv := hok_s0.1.1.lengths.core_ok.cur_vars_le
            have hcl := hok_s0.2.1.cur_level_le
            c0_bound
          exact hJB () _ ⟨s0, hok_s0, hcl0, hoom_s0, hm0⟩)
  · exact hJ1 () _ ⟨s0, hok_s0, hoom_s0, hm0⟩

end Helpers

/-- `Func.wp` proof for unified M4 `full_reduce(h, force)` against `m4ReduceSpec`:
exact canonical `Full.fullReduceSpec` when `force = true` (`full_learn_clause`), and
`m4ReduceLooseSpec` with `full_promote_reasons` when `force = false`. -/
theorem m4_reduce_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPromRsn : ∀ a m Q X, FullM4Ternary.fullPromoteReasonsSpec a m Q X →
      Γ "full_promote_reasons" [i64] [i64] a m Q X)
    (hRecomp : ∀ a m Q X, Full.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m4ReduceSpec a m Q X → Func.wp Γ full_reduce_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur0, s, R, rfl, hlen0, hw0, hlm0, hnd0, hext0, hdm0, hm, hFinish⟩ :
      ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur0 : List (List Nat)) (s : FullState)
        (R : Mem 64 → Prop),
        h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur0 s.core ∧
        FullDenseWatchSpecs.FullLitMarksClear c s ∧ FullDenseWatchSpecs.FullArenaVarsNodup s ∧
        FullDenseWatchSpecs.FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : BitVec 64) (F_cur2 : List (List Nat)) (s2 st : FullState) (ml : Mem 64),
          ReduceStateOk c F0 F_cur2 s2 st →
          (force = true → F_cur2 = F_cur0 ∧ ReduceStateOk c F0 F_cur0 s s2) →
          s2.core.cur_level ≤ s.core.cur_level → s2.core.fuel.toNat ≤ s.core.fuel.toNat →
          (s.core.oom = 0#64 → s2.core.oom = 0#64) →
          (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
          (r = 1#64 → s2.core.oom = 0#64 → st.core.oom = 0#64) →
          (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    cases force
    · obtain ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩ := hspec
      obtain ⟨F_cur0, hspW⟩ := hsp.exists_witness
      refine ⟨c, F0, F_cur0, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.1, hspW.2.2.2.1,
        hspW.2.2.2.2.1, hspW.2.2.2.2.2, hm,
        fun r F_cur2 s2 st ml hok _ hcl2 hfu2 hoom2 hr hu hoom hml => ?_⟩
      exact hQ r st ml (dwSparse_to_canon hok.1 hok.2.1) hr
        (Nat.le_trans hok.2.2.1 hcl2) (Nat.le_trans hok.2.2.2.1 hfu2)
        hu (fun hr1 hso => hoom hr1 (hoom2 hso)) hml
    · obtain ⟨c, F0, F_cur0, s, R, rfl, ⟨hlen, hw, hlm, hnd, hext, hdm⟩, hm, hQ⟩ := hspec
      refine ⟨c, F0, F_cur0, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm,
        fun r F_cur2 s2 st ml hok_tail ht_eq _ _ hoom2 hr hu hoom hml => ?_⟩
      obtain ⟨rfl, hok_s2⟩ := ht_eq rfl
      rcases reduceStateOk_trans hok_s2 hok_tail with
        ⟨hsp', hw', hcl', hfu', hcv', htmp', htl', _, _, _, _, _, _, hws2', hpos'⟩
      have hspW' : FullSparseInvW c F0 F_cur2 st :=
        ⟨hsp'.1.lengths, hw', hsp'.2.1, hsp'.2.2.1, hsp'.2.2.2.1, hsp'.2.2.2.2⟩
      exact hQ r st ml hspW' hr hcl' hfu' hcv' htmp' htl' hws2' hu
        (fun hr1 hso => hoom hr1 (hoom2 hso)) (fun _ => hpos') hml
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsp0 : FullDenseWatchSpecs.FullSparseInv c F0 s :=
    ⟨⟨hlen0, ⟨F_cur0, hw0⟩⟩, hlm0, hnd0, hext0, hdm0⟩
  unfold Func.wp full_reduce_body
  c0_to_group
  c0_call (dwIsqrt_adapter hIsqrt)
  intro r_isq hr_isq; c0_to_group
  obtain ⟨s0, hok_s0, hoom_s0, hm0⟩ :
      ∃ s0 : FullState, ReduceStateOk c F0 F_cur0 s s0 ∧
        (s.core.oom = 0#64 → s0.core.oom = 0#64) ∧ (FullMem c s0 ⋆ R) m :=
    ⟨{ s with scratch :=
        { s.scratch with
          reductions := s.scratch.reductions + 1#64
          reduce_limit := s.scratch.conflicts + 1000#64 * r_isq } },
      reduceStateOk_with_scratch (reduceStateOk_refl hsp0 hw0)
        { hlen0.scratch_ok with walk_vals_len := hlen0.scratch_ok.walk_vals_len } rfl rfl rfl,
      id, hm⟩
  have hok_self : ReduceStateOk c F0 F_cur0 s s := reduceStateOk_refl hsp0 hw0
  clear hm hsp0 hlen0 hw0 hlm0 hnd0 hext0 hdm0 hr_isq r_isq
  -- Join 1: after `if (h->unflushed > 0ULL)`.
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, ReduceStateOk c F0 F_cur0 s s1 ∧
      (s.core.oom = 0#64 → s1.core.oom = 0#64) ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ _ m1 ⟨s1, hok1, hoom1, hm1⟩
    clear hoom_s0 s0 hok_s0 hm0
    c0_to_group
    -- Join 2: after `if (!force && h->cur_level > 0ULL)`.
    refine wp_join_group
      (fun _ m2 => ∃ (F_cur2 : List (List Nat)) (s2 : FullState),
        ReduceStateOk c F0 F_cur2 s2 s2 ∧ s2.core.cur_level ≤ s.core.cur_level ∧
        s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (s.core.oom = 0#64 → s2.core.oom = 0#64) ∧
        (force = true → F_cur2 = F_cur0 ∧ ReduceStateOk c F0 F_cur0 s s2) ∧
        (FullMem c s2 ⋆ R) m2)
      ?_ ?_
    · rintro _ _ m2 ⟨F_cur2, s2, hok2_self, hcl2_le, hfu2_le, hoom2, ht_eq2, hm2⟩
      clear s1 hok1 hoom1 hm1
      have hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
          ReduceStateOk c F0 F_cur2 s2 st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
          (r = 20#64 → F0.Unsat) → (r = 1#64 → s2.core.oom = 0#64 → st.core.oom = 0#64) →
          (FullMem c st ⋆ R) ml → Q (r, ()) ml :=
        fun r st ml hok_t hr hu hoom hml =>
          hFinish r F_cur2 s2 st ml hok_t ht_eq2 hcl2_le hfu2_le hoom2 hr hu hoom hml
      c0_to_group
      c0_call (dwRecomputeTiers_adapter hRecomp)
      refine ⟨c, s2, R, rfl, hok2_self.1.1.lengths, hm2, fun sc2 m3 hsc2 hll2 hext2 hws22 hm3 => ?_⟩
      obtain ⟨s3, hok3, hoom3, hm3'⟩ :
          ∃ s3 : FullState, ReduceStateOk c F0 F_cur2 s2 s3 ∧
            (s2.core.oom = 0#64 → s3.core.oom = 0#64) ∧ (FullMem c s3 ⋆ R) m3 :=
        ⟨{ s2 with scratch := sc2 }, reduceStateOk_with_scratch hok2_self hsc2 hll2 hext2 hws22,
          id, hm3⟩
      clear hm3 hm2 sc2 hsc2 hll2 hext2 hws22
      c0_to_group
      c0_call hMarkRsn
      refine ⟨c, F0, F_cur2, s3, R, rfl, hok3.1.1.lengths, hok3.2.1, hm3',
        fun ar3 m4 hlen4 hrefs4 hper4 hrm4 hw4 hm4 => ?_⟩
      obtain ⟨s4, hok4, hoom4, hrm4', hm4'⟩ :
          ∃ s4 : FullState, ReduceStateOk c F0 F_cur2 s2 s4 ∧
            (s2.core.oom = 0#64 → s4.core.oom = 0#64) ∧
            FullDenseWatchSpecs.FullReasonsMarked s4 ∧ (FullMem c s4 ⋆ R) m4 :=
        ⟨{ s3 with core := { s3.core with arena := ar3 } },
          reduceStateOk_mark_reasons hok3 hlen4 hrefs4 hper4 hw4, hoom3, hrm4 rfl, hm4⟩
      clear hm4 s3 hok3 hoom3 hm3' ar3 hlen4 hrefs4 hper4 hrm4 hw4
      c0_to_group
      -- Loop 1: `while (p < h->arena_len)` collecting non-reason reducible refs into `red_refs`.
      refine wp_loop_inv
        (fun (rc, p, ()) mL =>
          rc.toNat ≤ c.red_cap ∧ p.toNat ≤ s4.core.arena_len ∧
          (p.toNat = s4.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s4) ∧
          ∃ sL : FullState,
            sL.core.arena_len = s4.core.arena_len ∧
            ReduceStateOk c F0 F_cur2 s2 sL ∧ (s2.core.oom = 0#64 → sL.core.oom = 0#64) ∧
            FullDenseWatchSpecs.FullReasonsMarked sL ∧
            fullArenaClauseRefs sL = fullArenaClauseRefs s4 ∧
            RedRefsOk sL rc.toNat ∧ (FullMem c sL ⋆ R) mL)
        (fun (_, p, ()) _ => s4.core.arena_len - p.toNat)
        (fun JL hLoopL => by
          c0_to_group
          refine hLoopL (0#64, 0#64, ()) m4 ⟨Nat.zero_le _, Nat.zero_le _, ?_, s4, rfl,
            hok4, hoom4, hrm4', rfl, fun _ h => by simp at h, hm4'⟩
          by_cases hz : s4.core.arena_len = 0
          · exact Or.inl hz.symm
          · exact Or.inr (fullArenaClauseRefs_zero_mem hok4.2.1.arena (Nat.pos_of_ne_zero hz)))
        (fun JL (rc, p, ()) mL
            ⟨hrc_le, hp_le, hp_mem, sL, halenL, hokL, hoomL, hrmL, hrefsL, hrrL, hmL⟩ hLoopL => ?_)
      · have hlenL := hokL.1.1.lengths
        have halL := hlenL.core_ok.arena_len_le
        have haarL := hlenL.core_ok.arena_len_arr
        have hrrlL := hlenL.scratch_ok.red_refs_len
        c0_to_group
        · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
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
          refine wp_join_group
            (fun (rc', ()) mN =>
              rc'.toNat ≤ c.red_cap ∧
              ∃ sN : FullState,
                sN.core.arena_len = s4.core.arena_len ∧
                ReduceStateOk c F0 F_cur2 s2 sN ∧ (s2.core.oom = 0#64 → sN.core.oom = 0#64) ∧
                FullDenseWatchSpecs.FullReasonsMarked sN ∧
                fullArenaClauseRefs sN = fullArenaClauseRefs s4 ∧
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
          · refine wp_join_group
              (fun _ mU =>
                ∃ sU : FullState,
                  sU.core.arena_len = s4.core.arena_len ∧
                  ReduceStateOk c F0 F_cur2 s2 sU ∧ (s2.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                  FullDenseWatchSpecs.FullReasonsMarked sU ∧
                  fullArenaClauseRefs sU = fullArenaClauseRefs s4 ∧
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
                      sR.core.arena_len = s4.core.arena_len ∧
                      ReduceStateOk c F0 F_cur2 s2 sR ∧
                      (s2.core.oom = 0#64 → sR.core.oom = 0#64) ∧
                      FullDenseWatchSpecs.FullReasonsMarked sR ∧
                      fullArenaClauseRefs sR = fullArenaClauseRefs s4 ∧
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
                             have hokU' : ReduceStateOk c F0 F_cur2 s2 sU' :=
                               reduceStateOk_with_scratch hokU
                                 { hlenU.scratch_ok with red_refs_len := by simp [hrrlU] }
                                 rfl rfl rfl
                             have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat :=
                               BitVec.eq_of_toNat_eq (by rw [hp_trunc, bv32_ofNat_toNat hp_lt32])
                             have hrrU' : RedRefsOk sU' (rc + 1#64).toNat := by
                               dsimp only [sU']; rw [hrc1, hp_sw]
                               exact redRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU hno_rsn hrrU
                             exact hJR (rc + 1#64, ()) _ ⟨by omega, sU', halenU, hokU', hoomU,
                               hrmU, hrefsU, hrrU', hm⟩))
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
          all_goals exact hJN (rc, ()) mL ⟨hrc_le, sL, halenL, hokL, hoomL, hrmL, hrefsL, hrrL,
            hmL⟩
        · -- Loop 1 exit (`p >= arena_len`): `if (rc > 0ULL)` + sweep/unmark tail.
          refine wp_join_group
            (fun _ m5 =>
              ∃ s5 : FullState, ReduceStateOk c F0 F_cur2 s2 s5 ∧
                (s2.core.oom = 0#64 → s5.core.oom = 0#64) ∧
                FullDenseWatchSpecs.FullReasonsMarked s5 ∧ (FullMem c s5 ⋆ R) m5)
            ?_ ?_
          · -- Tail after `if (rc > 0ULL)`: `if (force || ...)` sweep or `full_mark_reasons false`.
            rintro _ _ m5 ⟨s5, hok5, hoom5, hrm5, hm5⟩
            c0_to_group
            exact m4_reduce_tail_wp Γ hMarkRsn hProp hSweep c F0 F_cur2 s2 R force Q X hret s5
              m5 hok5 hoom5 hrm5 hm5
          · -- `if (rc > 0ULL)` body and else branch.
            intro J5 hJ5
            clear hc hok4 hoom4 hrm4' hm4' halenL hrefsL hp_le hp_mem m4 JL hLoopL
            c0_to_group
            · have hrr_bd : ∀ k < rc.toNat,
                  (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := fun k hk => by
                have hmem := (hrrL k hk).1
                have hwf := (hokL.2.1.arena.refs_wf _ hmem).1
                omega
              c0_call (dwSortReds_adapter hSortReds)
              refine ⟨c, sL, R, rfl, hlenL, hrc_le, hrr_bd, hmL,
                fun scS mS hscS hllS hextS hws2S hpermS hmS => ?_⟩
              obtain ⟨sS, hokS, hoomS, hrmS, hrrS, hmS'⟩ :
                  ∃ sS : FullState, ReduceStateOk c F0 F_cur2 s2 sS ∧
                    (s2.core.oom = 0#64 → sS.core.oom = 0#64) ∧
                    FullDenseWatchSpecs.FullReasonsMarked sS ∧ RedRefsOk sS rc.toNat ∧
                    (FullMem c sS ⋆ R) mS :=
                ⟨{ sL with scratch := scS },
                  reduceStateOk_with_scratch hokL hscS hllS hextS hws2S, hoomL, hrmL,
                  fun k hk => by
                    obtain ⟨j, hj, heq⟩ := hpermS k hk
                    change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
                      (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&&
                        0x00200000#32) = 0#32
                    rw [heq]; exact hrrL j hj,
                  hmS⟩
              clear hmS scS hscS hllS hextS hws2S hpermS hrr_bd sL hokL hoomL hrmL hrrL hmL
                hlenL halL haarL hrrlL
              c0_to_group
              c0_call hIlog10
              intro logv hlog1 _
              have hlog_ne : logv ≠ 0#64 := fun hz => by rw [hz] at hlog1; cases hlog1
              c0_to_group
              refine wp_loop_inv
                (fun (i, ()) mI =>
                  i.toNat ≤ rc.toNat ∧
                  ∃ sI : FullState,
                    ReduceStateOk c F0 F_cur2 s2 sI ∧ (s2.core.oom = 0#64 → sI.core.oom = 0#64) ∧
                    FullDenseWatchSpecs.FullReasonsMarked sI ∧ RedRefsOk sI rc.toNat ∧
                    (FullMem c sI ⋆ R) mI)
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
                  · c0_go; exact hJ5 () mI ⟨sI, hokI, hoomI, hrmI, hmI⟩
                · c0_go; exact hJ5 () mI ⟨sI, hokI, hoomI, hrmI, hmI⟩
            · exact hJ5 () mL ⟨sL, hokL, hoomL, hrmL, hmL⟩
    · -- Entry to `if (!force && h->cur_level > 0ULL)`.
      intro J2 hJ2
      cases force
      · c0_go
        · c0_call hPromRsn
          refine ⟨c, F0, s1, R, rfl, dwSparse_to_canon hok1.1 hok1.2.1, hm1,
            fun _ ar' ws2' gu' m2 hsp2 hm2 => ?_⟩
          let s2 : FullState :=
            { core := { s1.core with arena := ar' }
              scratch := { s1.scratch with work_stk2 := ws2', glue_used := gu' } }
          obtain ⟨F_cur2, hspW2⟩ := hsp2.exists_witness
          have hok2 : ReduceStateOk c F0 F_cur2 s2 s2 :=
            reduceStateOk_refl (canon_to_dwSparse hsp2 hspW2.2.1) hspW2.2.1
          c0_go
          exact hJ2 () m2 ⟨F_cur2, s2, hok2, hok1.2.2.1, hok1.2.2.2.1, hoom1,
            (fun hft => by cases hft), hm2⟩
        · exact hJ2 () m1 ⟨F_cur0, s1, reduceStateOk_refl hok1.1 hok1.2.1,
            hok1.2.2.1, hok1.2.2.2.1, hoom1, (fun hft => by cases hft), hm1⟩
      · refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
        c0_go
        exact hJ2 () m1 ⟨F_cur0, s1, reduceStateOk_refl hok1.1 hok1.2.1,
          hok1.2.2.1, hok1.2.2.2.1, hoom1, (fun _ => ⟨rfl, hok1⟩), hm1⟩
  · -- Entry to `if (h->unflushed > 0ULL)`.
    intro J1 hJ1
    exact m4_reduce_unflushed_wp Γ hBacktrack hProp c F0 F_cur0 s s0 R Q X m
      (fun r st ml hok_st hr hu hoom hml =>
        hFinish r F_cur0 s st ml hok_st (fun _ => ⟨rfl, hok_self⟩)
          (Nat.le_refl _) (Nat.le_refl _) id hr hu hoom hml)
      hok_s0 hoom_s0 hm0 J1 hJ1

end LeanQbe.T.Examples.Kissat.FullM4
