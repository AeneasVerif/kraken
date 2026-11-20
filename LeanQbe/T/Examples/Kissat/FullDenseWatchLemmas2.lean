module

public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1

/-!
# Kissat `D-Full` `full_reduce` `Func.wp` Proof (`Stage 4`, Part 2)

Proves parametric `(Γ : Env)` `Func.wp` correctness for `full_reduce` (`Full2.lean:200-258`)
against `FullDenseWatchSpecs.fullReduceSpec`:
- Unconditionally preserves `FullSparseInv c F0 s'` and `FullWitnessInv c F0 F_cur s'.core`
  across all return codes `r ∈ {0#64, 1#64, 20#64}` (including OOM / fuel abort `r = 0#64`).
- Proves `r = 20#64 → F0.Unsat`, `r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64`,
  `s'.core.cur_level ≤ s.core.cur_level`, `s'.core.fuel.toNat ≤ s.core.fuel.toNat`,
  and preservation of `tmp`/`tmp_len`/`frame_trail`/`frame_dec`/`cur_vars`/`extend_len`/
  `work_stk2` (plus trail/vals preservation when `0 < s'.core.cur_level`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullDenseWatchSpecs
open FullDenseWatchHelpers
open scoped FullArenaTactics

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
  -- Join `Jthen`: the `while (true)` sweep loop (appears ONCE!).
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

/-! ## 3. `full_reduce` `Func.wp` theorem (`Full2.lean:200-258`) -/

theorem full_reduce_wp (Γ : Env)
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
    ∀ a m Q X, fullReduceSpec a m Q X → Func.wp Γ full_reduce_body a m Q X := by
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
          reduce_limit := s.scratch.conflicts + 1000#64 * r_isq } },
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

end LeanQbe.T.Examples.Kissat.Full
