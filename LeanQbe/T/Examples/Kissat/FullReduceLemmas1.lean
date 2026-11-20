/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.Full2
public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` GC / Sweep / Reduce Specs & Core Theory — Part 1 (`Stage 4`)

Defines strictly scoped tactics (`FullReduceTactics`), `Spec` contracts (`FullReduceSpecs`) for
the 10 owned GC/sweep/reduce functions and their callees, and shared pure helper lemmas in
`FullReduceHelpers`.
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

/-! ## 1. Strictly scoped tactics (`FullReduceTactics`) -/

namespace FullReduceTactics

open scoped FullArenaTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fr_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fr_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)
scoped macro "fr_steps" : tactic =>
  `(tactic| (
      (try fr_unmdata)
      (repeat fr_strip)
      c0_steps
      repeat (any_goals (fr_strip; repeat fr_strip); c0_steps)))

open Lean Elab Tactic in
scoped elab "fr_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ty.isAppOf ``And && ty.getAppNumArgs == 2 then
        try
          evalTactic (← `(tactic| fr_strip))
          go (fuel - 1); out := out ++ (← getUnsolvedGoals)
        catch _ => out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  evalTactic (← `(tactic| try fr_unmdata))
  go 500

open Lean Elab Tactic in
scoped elab "fr_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOf ``And && ty.getAppNumArgs == 2 then
      try evalTactic (← `(tactic| fr_strip)); go (fuel - 1); return catch _ => return
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  evalTactic (← `(tactic| try fr_unmdata))
  go 100

@[scoped c0_load] theorem load_full_red_refs0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.red_refs.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pRedRefs = some s.scratch.red_refs[0] := by
  simpa using FullArenaTactics.load_full_red_refs (i := 0) hi hm

@[scoped c0_load] theorem load_full_red_refs_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.red_refs.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pRedRefs + 0#64) = some s.scratch.red_refs[0] :=
  FullArenaTactics.load_full_red_refs (i := 0) hi hm

@[scoped c0_store] theorem store_full_red_refs0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.red_refs.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pRedRefs ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := s.scratch.red_refs.set 0 v } } ⋆
        R) (storeMem m i32 c.pRedRefs v) := by
  simpa using FullArenaTactics.store_full_red_refs (i := 0) v hi hm

@[scoped c0_store] theorem store_full_red_refs_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.red_refs.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pRedRefs + 0#64) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := s.scratch.red_refs.set 0 v } } ⋆
        R) (storeMem m i32 (c.pRedRefs + 0#64) v) :=
  FullArenaTactics.store_full_red_refs (i := 0) v hi hm

end FullReduceTactics

/-! ## 2. Shared auxiliary invariants & `Spec` contracts (`FullReduceSpecs`) -/

namespace FullReduceSpecs

/-- Per-clause variable distinctness for all non-garbage arena clauses (`FullCoreState`). -/
def FullArenaVarsNodupCore (k : FullCoreState) : Prop :=
  ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false →
    ((fullArenaClauseLitsCore k r).map (· / 2)).Nodup

/-- Watch slice containing ONLY valid binary watches (arena-independent). -/
inductive BinOnlyWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : BinOnlyWatchSliceOk F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      BinOnlyWatchSliceOk F_cur k lit (p + 1) rem →
      BinOnlyWatchSliceOk F_cur k lit p (rem + 1)

/-- All watch lists contain only valid binary watches (established by `full_sweep_bins`). -/
structure BinOnlyWatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  slices : ∀ l < 2 * k.cur_vars,
    BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Mode-indexed single-literal slice validity (`false` = sparse 2WL, `true` = dense occ). -/
def ModeWatchSliceOk (dense : Bool) (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if dense then DenseWatchSliceOk F_cur k lit p rem else WatchSliceOk F_cur k lit p rem

/-! ### Callee `Spec` contracts -/

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' phases' unass' m', flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1, unassigned := unass', unflushed := unfl' }
              scratch := { s.scratch with phases := phases' } }
          s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

/-! ### Owned 10 `Spec` contracts & shared outcome/post predicates -/

def fullMarkReasonsSpec : Spec [i64, .bool] [] := fun (h, set_flag, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ arena' m',
      let s' : FullState := { s with core := { s.core with arena := arena' } }
      s'.LengthsOk c →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (set_flag = true → FullReasonsMarked s') →
      FullWitnessInv c F0 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullRedLessSpec : Spec [i64, i32, i32] [.bool] := fun (ar_ptr, a, b, ()) m Q _ =>
  ∃ (ar : List (BitVec 32)) (R : Mem 64 → Prop),
    a.toNat + 2 < ar.length ∧ b.toNat + 2 < ar.length ∧
    (array (t := i32) ar_ptr ar ⋆ R) m ∧ ∀ res : Bool, Q (res, ()) m

def fullRedSiftSpec : Spec [i64, i64, i64, i64] [] := fun (ar_ptr, rr_ptr, start, n, ()) m Q _ =>
  ∃ (ar rr : List (BitVec 32)) (R : Mem 64 → Prop),
    start.toNat ≤ n.toNat ∧ n.toNat ≤ rr.length ∧ n.toNat < 2 ^ 62 ∧
    (∀ k < n.toNat, (rr[k]?.getD 0#32).toNat + 2 < ar.length) ∧
    (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr ⋆ R) m ∧
    ∀ rr' m', rr'.length = rr.length →
      (∀ k, n.toNat ≤ k → rr'[k]? = rr[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = rr[j]?) →
      (array (t := i32) ar_ptr ar ⋆ array (t := i32) rr_ptr rr' ⋆ R) m' → Q () m'

def fullSortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m', rr'.length = c.red_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

def fullLitRankSpec : Spec [i64, i64, i32] [i64] := fun (vals_ptr, lvl_ptr, l, ()) m Q _ =>
  ∃ (vals : List (BitVec 8)) (lvl : List (BitVec 32)) (R : Mem 64 → Prop),
    l.toNat < vals.length ∧ l.toNat / 2 < lvl.length ∧
    (array (t := i8) vals_ptr vals ⋆ array (t := i32) lvl_ptr lvl ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

def fullUnwatchLargeSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

def fullSweepBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' nb' wsort' m',
      let s' : FullState :=
        { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                                num_binary := nb' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → BinOnlyWatchesInv F_cur s'.core → FullBinOnlyWatchesInv F_cur s'.core →
      DenseWatchesInv F_cur s'.core → FullWitnessInv c F0 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSweepCopyOutcome (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) (src dst : BitVec 64) (old_sz : BitVec 32) (at_root : Bool)
    (r : BitVec 64) : Prop :=
  (at_root = false →
    r = old_sz.setWidth 64 ∧ s'.core.vals = s.core.vals ∧ s'.core.flags = s.core.flags ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.rsns = s.core.rsns ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end ∧
    s'.core.unassigned = s.core.unassigned ∧ s'.core.unflushed = s.core.unflushed ∧
    s'.core.wvec = s.core.wvec ∧ s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
    s'.core.wusable = s.core.wusable ∧ s'.core.num_binary = s.core.num_binary ∧
    s'.core.oom = s.core.oom ∧ s'.scratch.phases = s.scratch.phases ∧
    s'.scratch.wsort = s.scratch.wsort ∧
    ∀ j < old_sz.toNat, s'.core.arena[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
  (at_root = true →
    FullWitnessInv c F0 F_cur { s'.core with arena_len := dst.toNat } ∧
    BinOnlyWatchesInv F_cur s'.core ∧ s.core.trail_end ≤ s'.core.trail_end ∧
    (r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
      (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)) ∧
    (r = 0xFFFFFFFE#64 → F0.Unsat) ∧ (r = 0xFFFFFFFD#64 → s'.core.oom = 1#64) ∧
    (r ≠ 0xFFFFFFFD#64 → s'.core.oom = s.core.oom) ∧
    (r = 1#64 → s.core.trail_end < s'.core.trail_end) ∧
    (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
      (∀ j < r.toNat, (s'.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      List.Sublist (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
        (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat))))

def fullSweepCopyPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (src dst : BitVec 64) (old_sz : BitVec 32) (at_root : Bool)
    (Q : Post [i64]) : Prop :=
  ∀ r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom'
    ph' wsort' m',
    let s' : FullState :=
      { core :=
          { s.core with
            arena := arena', vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
            num_binary := nb', oom := oom' }
        scratch := { s.scratch with phases := ph', wsort := wsort' } }
    s'.LengthsOk c →
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arena' →
    fullSweepCopyOutcome c F0 F_cur s s' src dst old_sz at_root r →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepCopySpec : Spec [i64, i64, i64, i32, .bool] [i64] :=
  fun (h, src, dst, old_sz, at_root, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ dst.toNat ≤ src.toNat ∧ 3 ≤ old_sz.toNat ∧
      src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len ∧ at_root = decide (s.core.cur_level = 0) ∧
      (∀ j < old_sz.toNat,
        (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (at_root = true →
        FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat } ∧
        BinOnlyWatchesInv F_cur s.core ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧ fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q

def fullRewatchArenaPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' wsort' m',
    let s' : FullState :=
      { core := { s.core with arena := arena', wvec := wvec', wstk := wstk',
                              wlen := wlen', wusable := wu', oom := oom' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    fullArenaClauseRefs s' = fullArenaClauseRefs s →
    (FullArenaVarsNodup s → FullArenaVarsNodup s') →
    (ok = true → oom' = s.core.oom) → (ok = false → oom' = 1#64) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullRewatchArenaSpec : Spec [i64, i64] [.bool] := fun (h, dst, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ dst.toNat = s.core.arena_len ∧
    FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s r = false) ∧
    (FullMem c s ⋆ R) m ∧ fullRewatchArenaPost c F0 F_cur s R Q

def fullArenaSweepPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' m',
    let s' : FullState :=
      { core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
    FullLastLearnedWf s' → sc'.extend_len = s.scratch.extend_len →
    sc'.work_stk2 = s.scratch.work_stk2 →
    (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) → (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
    (0 < s.core.cur_level → r ≠ 1#64 ∧ r ≠ 2#64 ∧
      vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
      tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
    (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
    (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
    (r = 3#64 → oom' ≠ 0#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (0 < s.core.cur_level → FullReasonsMarked s) ∧
    (FullMem c s ⋆ R) m ∧ fullArenaSweepPost c F0 F_cur s R Q

end FullReduceSpecs

open FullReduceSpecs

/-! ## 3. Focus, bitvector, watch-slice, & compaction helpers (`FullReduceHelpers`) -/

namespace FullReduceHelpers

def FullArenaRedRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
  FullCoreU32B c s.core ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ c.pad

theorem focus_full_arena_red_refs {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
      (FullArenaRedRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreDynArrs FullScratchArrays FullScrDynArrs at hm
  unfold FullArenaRedRest; ecancel

theorem unfocus_full_arena_red_refs {c : FullCfg} {s : FullState} {rr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm : (array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pRedRefs rr' ⋆
      (FullArenaRedRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' := by
  let sc' : FullScratch := { s.scratch with red_refs := rr' }
  change (FullMem c { s with scratch := sc' } ⋆ R) m'
  unfold FullMem FullCoreArrays FullCoreDynArrs FullScratchArrays FullScrDynArrs
  rw [show hdrTailWords c { s with scratch := sc' } = hdrTailWords c s from rfl,
    show FullScrByteArrs c sc' = FullScrByteArrs c s.scratch from rfl,
    show FullScrU32A c sc' = FullScrU32A c s.scratch from rfl,
    show FullScrWksArrs c sc' = FullScrWksArrs c s.scratch from rfl,
    show FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch from rfl]
  unfold FullArenaRedRest at hm; dsimp only [sc']; ecancel

def FullValsLvlRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pReason s.core.rsns ⋆
  array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
  array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad

theorem focus_full_vals_lvl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      (FullValsLvlRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A at hm
  unfold FullValsLvlRest; ecancel

theorem unfocus_full_vals_lvl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      (FullValsLvlRest c s ⋆ R)) m) :
    (FullMem c s ⋆ R) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A
  unfold FullValsLvlRest at hm; ecancel

theorem fullMem_cast {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s1 ⋆ R) m) (heq : s1 = s2) : (FullMem c s2 ⋆ R) m := heq ▸ hm

theorem bv64_add_nat {x : BitVec 64} (n : Nat) (hn : n < 2 ^ 64) (h : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

theorem bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := bv64_add_nat 1 (by decide) h

theorem bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + (2 : BitVec 64)).toNat = x.toNat + 2 := bv64_add_nat 2 (by decide) h

theorem bv64_add3 {x : BitVec 64} (h : x.toNat + 3 < 2 ^ 64) :
    (x + (3 : BitVec 64)).toNat = x.toNat + 3 := bv64_add_nat 3 (by decide) h

theorem bv64_add4 {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + (4 : BitVec 64)).toNat = x.toNat + 4 := bv64_add_nat 4 (by decide) h

theorem bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + (1 : BitVec 32)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_shl1_toNat {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_add3_zext_toNat {x : BitVec 64} {y : BitVec 32} (h : x.toNat + 3 + y.toNat < 2 ^ 64) :
    (x + (3 : BitVec 64) + y.setWidth 64).toNat = x.toNat + 3 + y.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat y (by decide),
    show (3 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : x.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem modeWatchesInv_to_sparse {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) (hdm : k.dense_mode = 0#64) : WatchesInv F_cur k := by
  simpa [ModeWatchesInv, hdm] using h

theorem sparse_to_modeWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : WatchesInv F_cur k) (hdm : k.dense_mode = 0#64) : ModeWatchesInv F_cur k := by
  simpa [ModeWatchesInv, hdm] using h

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {oom' : BitVec 64} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem bv8_sext32_eq0_of_dom {x : BitVec 8}
    (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) : x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_gt0_of_dom {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    ((0#32).slt (x.signExtend 32) = true ↔ x = 1#8) ∧
    ((x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv32_bit21_or_pres (x : BitVec 32) :
    ((x ||| 0x00200000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x ||| 0x00200000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) ∧
    ((x ||| 0x00200000#32) &&& 0x00200000#32) ≠ 0#32 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i hi
    have h0 : ((0x00200000#32)[i] && (0x00080000#32)[i]) = false := by
      rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
    simp [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
  · ext i hi
    have h0 : ((0x00200000#32)[i] && (0x00800000#32)[i]) = false := by
      rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
    simp [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
  · intro h; have h21 := congrArg (·[21]) h
    revert h21; simp [show (0x00200000#32)[21] = true from rfl]

theorem bv32_bit21_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x00200000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x &&& ~~~0x00200000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨by rw [BitVec.and_assoc]; rfl, by rw [BitVec.and_assoc]; rfl⟩

theorem bv32_usage_upd_pres (x u : BitVec 32) :
    let y := (x &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    (y &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    (y &&& 0x00200000#32) = (x &&& 0x00200000#32) ∧
    (y &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  intro y
  have hsh : ∀ (k : Nat) (hk : k < 27), (u <<< (27 : Nat))[k]'(by omega) = false := fun k hk => by
    simp [BitVec.getElem_shiftLeft, show ¬ (27 ≤ k) by omega]
  have h19 : (0x07FFFFFF#32)[19] = true ∧ (0x00080000#32)[19] = true := by decide
  have h21 : (0x07FFFFFF#32)[21] = true ∧ (0x00200000#32)[21] = true := by decide
  have h23 : (0x07FFFFFF#32)[23] = true ∧ (0x00800000#32)[23] = true := by decide
  refine ⟨?_, ?_, ?_⟩ <;> (ext i hi; simp only [y, BitVec.getElem_and, BitVec.getElem_or])
  · by_cases hi19 : i = 19
    · subst hi19; simp [h19.1, hsh 19 (by omega)]
    · have hz : (0x00080000#32)[i] = false := by revert i hi hi19; decide
      simp [hz]
  · by_cases hi21 : i = 21
    · subst hi21; simp [h21.1, hsh 21 (by omega)]
    · have hz : (0x00200000#32)[i] = false := by revert i hi hi21; decide
      simp [hz]
  · by_cases hi23 : i = 23
    · subst hi23; simp [h23.1, hsh 23 (by omega)]
    · have hz : (0x00800000#32)[i] = false := by revert i hi hi23; decide
      simp [hz]

theorem bv32_clear_shrk_rsn (x : BitVec 32) (hng : (x &&& 0x00080000#32) = 0#32) :
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00800000#32) = 0#32 ∧
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00080000#32) = 0#32 :=
  ⟨by rw [BitVec.and_assoc]; exact BitVec.and_zero, by rw [BitVec.and_assoc]; exact hng⟩

theorem bv32_litmask_of_lt {x : BitVec 32} (hx : x.toNat < 0x80000000) :
    x &&& 0x7FFFFFFF#32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem bv32_bin_word_props {l : BitVec 32} (hl : l.toNat < 0x7FFFFFFF) :
    let w := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x7FFFFFFF#32) = l := by
  intro w
  have hl_eq : l &&& 0x7FFFFFFF#32 = l := bv32_litmask_of_lt (by omega)
  have hw7 : w &&& 0x7FFFFFFF#32 = l := by
    have h1 : w &&& 0x7FFFFFFF#32 = l &&& 0x7FFFFFFF#32 := by
      ext i hi
      have h0 : ((0x80000000#32)[i] && (0x7FFFFFFF#32)[i]) = false := by
        rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
      simp [w, BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
    rw [h1, hl_eq]
  have hw8 : (w &&& 0x80000000#32) ≠ 0#32 := by
    intro h; have h31 := congrArg (·[31]) h
    have hb : (0x80000000#32)[31]'(by decide) = true := by decide
    simp only [w, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, hb,
      Bool.or_true, Bool.true_and] at h31
    exact Bool.noConfusion h31
  exact ⟨hw8, binWatchWord_ne_sentinel (by rw [hw7]; exact hl), hw7⟩

theorem bv32_large_word_props (w : BitVec 32) :
    ((w &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
    (w &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  refine ⟨by rw [BitVec.and_assoc]; exact BitVec.and_zero, fun h => ?_⟩
  have h31 := congrArg (·[31]) h
  revert h31; simp [show (0x7FFFFFFF#32)[31] = false from rfl,
    show (0xFFFFFFFF#32)[31] = true from rfl]

theorem bv32_lt_highbit_iff (r : BitVec 32) :
    r.toNat < 0x80000000 ↔ (r &&& 0x80000000#32) = 0#32 := by
  constructor
  · intro h; rw [← bv32_litmask_of_lt h]; exact (bv32_large_word_props r).1
  · intro h
    have h31 : r[31] = false := by
      have hc := congrArg (·[31]) h
      simpa [show (0x80000000#32)[31] = true by decide] using hc
    have htb := BitVec.getElem_eq_testBit_toNat (x := r) (i := 31) (by decide)
    rw [h31] at htb
    have hmod : (r.toNat / 2 ^ 31) % 2 = 0 := by
      have h1 : (r.toNat >>> 31) &&& 1 = 0 := by
        simpa [Nat.testBit, bne_iff_ne] using htb.symm
      rwa [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at h1
    have hlt := r.isLt; omega

/-! ### Watch-slice, bin-only, mode-bridge, & layout shrink helpers -/

end FullReduceHelpers

namespace FullReduceSpecs

theorem BinOnlyWatchSliceOk.toWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih

theorem BinOnlyWatchSliceOk.toDenseWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih

theorem BinOnlyWatchSliceOk.ne_sentinel {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : BinOnlyWatchSliceOk F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := h.toWatchSliceOk.ne_sentinel

theorem BinOnlyWatchSliceOk.forall_elem {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} : ∀ {p rem : Nat}, BinOnlyWatchSliceOk F_cur k lit p rem →
      ∀ idx < rem,
        let w := k.wstk[p + idx]?.getD 0#32
        (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])
  | _, _, .empty, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, _, .bin hp hf _ hlt hent _, 0, _ => by
    simpa [Nat.add_zero, hp] using And.intro hf (And.intro hlt hent)
  | p, _, .bin _ _ _ _ _ hrest, idx + 1, hi => by
    rw [show p + (idx + 1) = (p + 1) + idx by omega]
    exact hrest.forall_elem idx (Nat.lt_of_succ_lt_succ hi)

theorem BinOnlyWatchSliceOk.relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : BinOnlyWatchSliceOk F k lit p rem) : BinOnlyWatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih (p' := p' + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))

theorem BinOnlyWatchSliceOk.append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : BinOnlyWatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    BinOnlyWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem BinOnlyWatchesInv.toWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : WatchesInv F_cur k :=
  ⟨h.layout, fun l hl => (h.slices l hl).toWatchSliceOk⟩

theorem BinOnlyWatchesInv.toDenseWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : DenseWatchesInv F_cur k :=
  ⟨h.layout, fun l hl => (h.slices l hl).toDenseWatchSliceOk⟩

theorem BinOnlyWatchesInv.toFull {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : FullBinOnlyWatchesInv F_cur k :=
  ⟨h.layout, fun l hl i hi => (h.slices l hl).forall_elem i hi⟩

theorem BinOnlyWatchesInv.toModeWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) : ModeWatchesInv F_cur k := by
  by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hc, ↓reduceIte]
  · exact h.toWatchesInv
  · exact h.toDenseWatchesInv

theorem BinOnlyWatchesInv.with_core {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : BinOnlyWatchesInv F_cur k) (hvars : k'.cur_vars = k.cur_vars)
    (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk) (hl : k'.wlen = k.wlen) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨h.layout.with_wstk hvars hw hs hl, fun l hl' => ?_⟩
  have ho : fullWatchOffCore k' l = fullWatchOffCore k l := by unfold fullWatchOffCore; rw [hw]
  have hsz : fullWatchSizeCore k' l = fullWatchSizeCore k l := by unfold fullWatchSizeCore; rw [hw]
  rw [ho, hsz]
  exact (h.slices l (hvars ▸ hl')).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
    (by omega) (fun _ _ => by rw [hs])

theorem ModeWatchSliceOk.empty {dense : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p : Nat} : ModeWatchSliceOk dense F_cur k lit p 0 := by
  cases dense <;> simp [ModeWatchSliceOk] <;> constructor

theorem ModeWatchSliceOk.ne_sentinel {dense : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : ModeWatchSliceOk dense F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h
  · exact h.ne_sentinel
  · exact h.ne_sentinel

theorem ModeWatchSliceOk.relocate {dense : Bool} {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : ModeWatchSliceOk dense F k lit p rem) : ModeWatchSliceOk dense F' k' lit p' rem := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact fullWatchSlice_relocate hF hvars hsub hwstk h
  · exact DenseWatchSliceOk.relocate hF hvars hsub hwstk h

theorem ModeWatchSliceOk.append_bin {dense : Bool} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : ModeWatchSliceOk dense F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    ModeWatchSliceOk dense F_cur k' lit p' (rem + 1) := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact fullWatchSlice_append_bin hvars hsub hwstk h hw0 hflag hne hlt hent
  · exact DenseWatchSliceOk.append_bin hvars hsub hwstk h hw0 hflag hne hlt hent

theorem ModeWatchSliceOk.append_pair {dense : Bool} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : ModeWatchSliceOk dense F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : dense = true → 3 ≤ w0.toNat)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    ModeWatchSliceOk dense F_cur k' lit p' (rem + 2) := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact fullWatchSlice_append_large hvars hsub hwstk h hw0 hw1 hflag hlt href
  · exact DenseWatchSliceOk.append_occ hvars hsub hwstk h hw0 hw1 hflag (hsz rfl) hlt href

theorem ModeWatchSliceOk.step {dense : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (h : ModeWatchSliceOk dense F_cur k lit p rem)
    (hpos : 0 < rem) (hw0 : k.wstk[p]? = some w0) :
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      ModeWatchSliceOk dense F_cur k lit (p + 1) (rem - 1)) ∧
    ((w0 &&& 0x80000000#32) = 0#32 →
      2 ≤ rem ∧ ∃ cr, k.wstk[p + 1]? = some cr ∧ (dense = true → 3 ≤ w0.toNat) ∧
        cr.toNat < 0x80000000 ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        ModeWatchSliceOk dense F_cur k lit (p + 2) (rem - 2)) := by
  cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · cases h with
    | empty => omega
    | bin hp hf hne hlt hent hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun _ => ⟨hne, hlt, hent, by simpa using hrest⟩, fun h0 => absurd h0 hf⟩
    | large hp hp1 hf hlt href hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun hne => absurd hf hne,
        fun _ => ⟨by omega, _, hp1, fun hc => False.elim hc, hlt, href, by simpa using hrest⟩⟩
  · cases h with
    | empty => omega
    | bin hp hf hne hlt hent hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun _ => ⟨hne, hlt, hent, by simpa using hrest⟩, fun h0 => absurd h0 hf⟩
    | occ hp hp1 hf hsz hlt href hrest =>
      rw [hp] at hw0; cases hw0
      exact ⟨fun hne => absurd hf hne,
        fun _ => ⟨by omega, _, hp1, fun _ => hsz, hlt, href, by simpa using hrest⟩⟩

end FullReduceSpecs

namespace FullReduceHelpers

theorem fullWstackDefrag_preserves_binOnly {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hw : BinOnlyWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars)
    (hpres : ∀ l < 2 * k.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hsz, hslice⟩ := hpres l (hvars ▸ hl); rw [hsz]
  exact (hw.slices l (hvars ▸ hl)).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
    (by omega) hslice

theorem fullWatchPush_preserves_binOnly {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit w0 : BitVec 32} {ok : Bool} (hw : BinOnlyWatchesInv F_cur k)
    (hlay : WatchStackLayout k') (hvars : k'.cur_vars = k.cur_vars)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?)
    (hok_t : ok = true → lit.toNat < 2 * k.cur_vars ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 1 ∧
      (∀ j < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + j]? = k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0)
    (hok_f : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ j < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + j]? = k.wstk[fullWatchOffCore k lit.toNat + j]?) :
    BinOnlyWatchesInv F_cur k' := by
  refine ⟨hlay, fun l hl => ?_⟩
  have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
  by_cases hle : l = lit.toNat
  · subst hle; cases ok with
    | false =>
      obtain ⟨hsz, hslice⟩ := hok_f rfl hl0; rw [hsz]
      exact (hw.slices _ hl0).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
        (by omega) hslice
    | true =>
      obtain ⟨_, hsz, hpre, hw0⟩ := hok_t rfl; rw [hsz]
      exact (hw.slices _ hl0).append_bin (by omega) hpre hw0 hbin.1 hbin.2.1 (by omega) hbin.2.2.2
  · obtain ⟨hsz, hslice⟩ := hother l hl0 hle; rw [hsz]
    exact (hw.slices l hl0).relocate (by rw [CNF.entails_def]; exact fun _ p => p)
      (by omega) hslice

theorem modeWatchesInv_slice_of_lt {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur k l
      (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [ModeWatchesInv, ModeWatchSliceOk, hc, ne_eq, not_true_eq_false, decide_false,
      not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact h.slices l hl
  · exact h.slices l hl

theorem watchStackLayout_shrink_slice {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c)
    {lit new_sz : Nat} (hlit : lit < 2 * k.cur_vars) (hle : new_sz ≤ fullWatchSizeCore k lit)
    {wstk' : List (BitVec 32)}
    (hout : ∀ i, i < fullWatchOffCore k lit ∨
      fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ i → wstk'[i]? = k.wstk[i]?)
    (hns : ∀ j < new_sz, wstk'[fullWatchOffCore k lit + j]? ≠ some 0xFFFFFFFF#32)
    (wu' nb' : BitVec 64) :
    let k' : FullCoreState :=
      { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
               wstk := wstk', wusable := wu', num_binary := nb' }
    WatchStackLayout k' ∧ fullWatchOffCore k' lit = fullWatchOffCore k lit ∧
    fullWatchSizeCore k' lit = new_sz ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k l + j]? = k.wstk[fullWatchOffCore k l + j]?) := by
  intro k'
  have hlt32 : new_sz < 2 ^ 32 := by
    have := (k.wvec[2 * lit + 1]?.getD 0#32).isLt; unfold fullWatchSizeCore at hle; omega
  have hwv_len : 2 * lit + 1 < k.wvec.length := by
    have := hlen.wvec_len; have := hlen.cur_vars_le; omega
  have hoff_eq : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore k'; rw [List.getElem?_set_ne (by omega)]
  have hsz_self : fullWatchSizeCore k' lit = new_sz := by
    unfold fullWatchSizeCore k'; rw [List.getElem?_set_self hwv_len, Option.getD_some,
      bv32_ofNat_toNat hlt32]
  have hsz_ne : ∀ l, l ≠ lit → fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l hne => by
    unfold fullWatchSizeCore k'; rw [List.getElem?_set_ne (by omega)]
  have hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k l + j]? = k.wstk[fullWatchOffCore k l + j]? := fun l hl hne =>
    ⟨hoff_eq l, hsz_ne l hne, fun j hj => by
      by_cases hsz0 : fullWatchSizeCore k lit = 0
      · exact hout _ (by omega)
      · rcases hlay.disjoint l lit hl hlit hne (by omega) (by omega) with h1 | h2
        · exact hout _ (Or.inl (by omega))
        · exact hout _ (Or.inr (by omega))⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hoff_eq lit, hsz_self, hother⟩
  · intro l hl; by_cases e : l = lit
    · subst e; rw [hoff_eq, hsz_self]; have := hlay.bounds _ hlit; dsimp [k']; omega
    · rw [hoff_eq, hsz_ne l e]; exact hlay.bounds l hl
  · intro l hl hpos; by_cases e : l = lit
    · subst e; rw [hoff_eq]; rw [hsz_self] at hpos; exact hlay.pos_off _ hlit (by omega)
    · rw [hoff_eq]; rw [hsz_ne l e] at hpos; exact hlay.pos_off l hl hpos
  · intro l1 l2 h1 h2 hne hp1 hp2; rw [hoff_eq, hoff_eq]
    by_cases e1 : l1 = lit
    · subst e1; rw [hsz_self] at hp1 ⊢; rw [hsz_ne l2 (Ne.symm hne)] at hp2 ⊢
      rcases hlay.disjoint _ l2 h1 h2 hne (by omega) hp2 with ha | hb
      · exact Or.inl (by omega)
      · exact Or.inr hb
    · rw [hsz_ne l1 e1] at hp1 ⊢
      by_cases e2 : l2 = lit
      · subst e2; rw [hsz_self] at hp2 ⊢
        rcases hlay.disjoint l1 _ h1 h2 hne hp1 (by omega) with ha | hb
        · exact Or.inl ha
        · exact Or.inr (by omega)
      · rw [hsz_ne l2 e2] at hp2 ⊢; exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
  · intro l hl idx hidx; by_cases e : l = lit
    · subst e; rw [hoff_eq]; rw [hsz_self] at hidx; exact hns idx hidx
    · obtain ⟨ho, hs, hw⟩ := hother l hl e
      rw [ho]; rw [hs] at hidx; rw [hw idx hidx]; exact hlay.no_sentinel l hl idx hidx

theorem modeWatchesInv_shrink_slice {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : ModeWatchesInv F_cur k) (hlen : k.LengthsOk c)
    {lit new_sz : Nat} (hlit : lit < 2 * k.cur_vars) (hle : new_sz ≤ fullWatchSizeCore k lit)
    {wstk' : List (BitVec 32)}
    (hout : ∀ i, i < fullWatchOffCore k lit ∨
      fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ i → wstk'[i]? = k.wstk[i]?)
    (wu' nb' : BitVec 64)
    (hslice : ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur
      { k with wstk := wstk' } lit (fullWatchOffCore k lit) new_sz) :
    ModeWatchesInv F_cur
      { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
               wstk := wstk', wusable := wu', num_binary := nb' } := by
  let k' : FullCoreState :=
    { k with wvec := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 new_sz),
             wstk := wstk', wusable := wu', num_binary := nb' }
  let kw : FullCoreState := { k with wstk := wstk' }
  change ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur kw lit (fullWatchOffCore k lit)
    new_sz at hslice
  change ModeWatchesInv F_cur k'
  obtain ⟨hlay', hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hw.layout hlen hlit hle hout hslice.ne_sentinel wu' nb'
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' := fun _ r => r
  have hrefs2 : ∀ r ∈ fullArenaClauseRefsCore kw, r ∈ fullArenaClauseRefsCore k' := fun _ r => r
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ p => p
  have hcv1 : k.cur_vars ≤ k'.cur_vars := Nat.le_refl _
  have hcv2 : kw.cur_vars ≤ k'.cur_vars := Nat.le_refl _
  by_cases hc : k.dense_mode = 0#64
  · simp only [ModeWatchesInv, ModeWatchSliceOk, show k'.dense_mode = k.dense_mode from rfl,
      hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hw hslice ⊢
    refine ⟨hlay', fun l hl => ?_⟩; by_cases e : l = lit
    · subst e; rw [hoff_self, hsz_self]
      exact fullWatchSlice_relocate hrefl hcv2 hrefs2 (fun _ _ => rfl) hslice
    · obtain ⟨ho, hs, hws⟩ := hother l hl e; rw [ho, hs]
      exact fullWatchSlice_relocate hrefl hcv1 hrefs hws (hw.slices l hl)
  · simp only [ModeWatchesInv, ModeWatchSliceOk, show k'.dense_mode = k.dense_mode from rfl,
      hc, decide_eq_true hc, ↓reduceIte] at hw hslice ⊢
    refine ⟨hlay', fun l hl => ?_⟩; by_cases e : l = lit
    · subst e; rw [hoff_self, hsz_self]; exact hslice.relocate hrefl hcv2 hrefs2 (fun _ _ => rfl)
    · obtain ⟨ho, hs, hws⟩ := hother l hl e; rw [ho, hs]
      exact (hw.slices l hl).relocate hrefl hcv1 hrefs hws

/-! ### Arena scan, compaction, reason uniqueness, & `SweepReasonMapInv` -/

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 3 ≤ k.arena_len := ha.len_ok.elim (fun hz => by omega) id
  unfold fullArenaClauseRefsCore
  cases hal : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [show 0 + 3 ≤ f + 1 by omega]

theorem fullArenaScanRefs_mem_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel → fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hn3 => by
    unfold fullArenaScanRefs at hr ⊢; split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · right; cases fuel with
        | zero => omega
        | succ _ => unfold fullArenaScanRefs; simp [hn3]
      · exact Or.inr (fullArenaScanRefs_mem_next (by omega) hrest hn3)
    · simp at hr

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  (ha.refs_wf r hr).2.2.2.2.elim Or.inl
    fun h3 => Or.inr (fullArenaScanRefs_mem_next (by omega) hr h3)

theorem fullArenaVarsNodup_of_refs_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hcl : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullArenaVarsNodup s' := by
  intro r hr hng; rw [hrefs] at hr; obtain ⟨hg, hl⟩ := hcl r hr
  rw [hl]; exact h r hr (hg.symm.trans hng)

theorem drop_take_succ {α : Type} {xs : List α} {off n : Nat} (hlt : off + n < xs.length) :
    (xs.drop off).take (n + 1) = (xs.drop off).take n ++ [xs[off + n]'hlt] := by
  have h1 : n < (xs.drop off).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem h1, List.getElem_drop]; simp

theorem drop_take_set_append {α : Type} {xs : List α} {off n : Nat} {v : α}
    (hlt : off + n < xs.length) :
    ((xs.set (off + n) v).drop off).take (n + 1) = (xs.drop off).take n ++ [v] := by
  have hlt' : off + n < (xs.set (off + n) v).length := by simp [hlt]
  rw [drop_take_succ hlt', List.getElem_set_self hlt']; congr 1
  refine List.ext_getElem (by simp) fun j hj1 _ => ?_
  have hjn : j < n := by simp at hj1; omega
  simp only [List.getElem_take, List.getElem_drop]; rw [List.getElem_set_ne (by omega)]

theorem modifyClauseBody_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) {p : Nat} (hp : p ∈ fullArenaClauseRefsCore k)
    {ar' : List (BitVec 32)} (hlen_ar : ar'.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + fullArenaClauseSizeCore k p) k.arena ar')
    (h2 : ar'[p + 2]? = k.arena[p + 2]?)
    (hmem : ∀ l, l ∈ fullArenaClauseLitsCore { k with arena := ar' } p ↔
      l ∈ fullArenaClauseLitsCore k p) :
    let k' := { k with arena := ar' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hpwf := hw.arena.refs_wf p hp
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      (r + 3 + fullArenaClauseSizeCore k r ≤ p ∧ fullArenaNextOff k.arena k.arena_len r ≤ p) ∨
      (p + 3 + fullArenaClauseSizeCore k p ≤ fullArenaNextOff k.arena k.arena_len p ∧
        fullArenaNextOff k.arena k.arena_len p ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr hp hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr hp hlt⟩
    · exact Or.inr ⟨hpwf.2.2.1, fullArenaScanRefs_disjoint hp hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff ar' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = p
    · subst r
      exact fullArenaNextOff_congr_block (hout.getElem?_lt (by omega)) h2
        (fun i hi _ => hout.getElem?_ge hi)
    · refine fullArenaNextOff_congr_block ?_ ?_ ?_
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · intro idx _ hi2; rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    by_cases hrp : r = p
    · subst r; have h0 := hout.getElem?_lt (i := p) (by omega)
      exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
        by unfold fullArenaClauseSizeCore k'; rw [h2],
        by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
    · rcases hne_out r hr hrp with ⟨h1, _⟩ | ⟨_, h2'⟩
      · have h0 := hout.getElem?_lt (i := r) (by omega)
        have hs := hout.getElem?_lt (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
      · have h0 := hout.getElem?_ge (i := r) (by omega)
        have hs := hout.getElem?_ge (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
  have hlits_other : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hrp => by
    have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore k r ≤ ar'.length := by
      rw [hlen_ar, ← hlen.arena_len_arr]; exact hbd1
    exact fullArenaClauseLitsCore_eq_of_hold (k := k) (k' := k') hbd1 hbd2
      (hmeta r hr).2.1 fun j hj => by
        rcases hne_out r hr hrp with ⟨h1, _⟩ | ⟨_, h2'⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
  have hmem_all : ∀ r ∈ fullArenaClauseRefsCore k,
      ∀ l, l ∈ fullArenaClauseLitsCore k' r ↔ l ∈ fullArenaClauseLitsCore k r := fun r hr l => by
    by_cases hrp : r = p
    · subst r; exact hmem l
    · rw [hlits_other r hr hrp]
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh
      have hr3 := (hw.arena.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hr3
        (by rw [hget_r, Option.getD_some]; exact hsh) ht1 ht2 hsent
      have hnxt_le := (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [(hmeta r hr).2.1]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; by_cases hrp : r = p
      · subst r; rw [hout.getElem?_ge ht0_lo]; exact ht0_sent
      · rcases hne_out r hr hrp with ⟨_, _⟩ | ⟨_, _⟩
        · rw [hout.getElem?_lt (by omega)]; exact ht0_sent
        · rw [hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2] at hng; rw [hmem_all r hr l] at hl; exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr; rw [(hmeta r hr).2.2] at hng
      exact entails_of_mem_or_false (hw.arena.entails r hr hng) fun l hl =>
        Or.inl ((hmem_all r hr l).mpr hl)
  refine ⟨hrefs, hmeta, hlits_other, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ hrs.1, (hmeta _ hrs.1).2.2.trans hrs.2.1,
          fun q hq => hrs.2.2 q ((hmem_all _ hrs.1 q).mp hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hmem_all _ hrs.1 _).mpr (hw.reason_lit_mem idx hidx hne hlg) }⟩

end FullReduceHelpers

end LeanQbe.T.Examples.Kissat.Full
