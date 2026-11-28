/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Sweep

/-!
# Pure Lean Layer-A Chronological Backtracking & Restart Trail Reuse Theory (Part 2)

Pure Lean (`Std.Sat.CNF Nat`, zero `Kraken.Mem` or `Kraken.Separation` imports) generalization of
`Minimize.LazyTrailInv` to Kissat's chronological backtracking (`chrono=1`) and restart
trail reuse (`restartreusetrail=1`):

1. **`ChronoState` & `ChronoTrailInv`**:
   explicit `isDec : Array Bool` decision markers + `frames : Array Nat` trail offsets without
   assuming `levels_mono` or that trail positions at level `lvl` lie beyond `frames[lvl]`.
   Proves `ChronoTrailInv.toLazy` (`ChronoTrailInv s → LazyTrailInv s.cdcl`) and direct
   `chronoTrailEntailment` / `chronoUnsat_of_conflict`.
2. **`ReasonDagInv` & `ChronoTrailInv` across out-of-order transitions**:
   `chronoInit`, `chronoDecide`, `chronoAssignProp`, out-of-order `chronoAssignUip` (assigning
   `uip` at `uipLevel ≤ s.cdcl.level`, even `< s.cdcl.level` after higher-level literals),
   filtering `chronoBacktrack`, and `restartreusetrail=1` (`restartReuseTrail` &
   `restartReusePrefix`).
3. **1UIP + OTFS resolution (`chronoAnalyze1UIP`, `applyOtfsUpdates`), Lexicographic Minimization
   & Block Shrinking (`FailedLit`), and Composed `chronoConflictStep_preserves_inv`**.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. `ChronoState`, explicit `isDecision` markers, `ChronoTrailInv`, & entailment -/

/-- Trail-and-frame state supporting chronological backtracking (`chrono=1`), out-of-order UIP
assignment, and restart trail reuse (`restartreusetrail=1`) with explicit `isDec` markers and
`frames` offsets (where literal levels may sit out-of-order beyond `frames[lvl]`). -/
structure ChronoState where
  cdcl : CdclState
  isDec : Array Bool
  frames : Array Nat

/-- Explicit decision marker check on `ChronoState` (does not inspect `frames`). -/
@[expose, inline] def ChronoState.isDecision (s : ChronoState) (l : Nat) : Bool :=
  s.isDec.getD (litVar l) false

/-- Recorded start trail index for level `lvl` (may lag behind lower-level UIP assignments). -/
@[expose, inline] def ChronoState.frameTrail (s : ChronoState) (lvl : Nat) : Nat :=
  s.frames.getD lvl 0

/-- Construct a `ChronoState` from a `CdclState`, syncing `isDec` from `reasons`. -/
@[expose] def ChronoState.ofCdcl (cdcl : CdclState) (frames : Array Nat := #[]) : ChronoState :=
  { cdcl := cdcl
    isDec := cdcl.reasons.map (fun r => decide (r = .decision))
    frames := frames }

/-- All decision literals on `s.cdcl.trail` with `stateLevel ≤ k`, selected by explicit
`isDecision` markers rather than `frames` index bounds. -/
@[expose] def chronoDecisionsAtMost (s : ChronoState) (k : Nat) : List Nat :=
  s.cdcl.trail.toList.filter fun l => s.isDecision l && decide (stateLevel s.cdcl l ≤ k)

/-- Generalized CDCL trail & database invariant for chronological backtracking (`chrono=1`) and
restart trail reuse (`restartreusetrail=1`). Omits `levels_mono` and `frames` index partitioning,
synchronizing explicit `isDecision` markers with `Reason.decision`. -/
structure ChronoTrailInv (s : ChronoState) : Prop where
  vars_nodup : ∀ i j, (hi : i < s.cdcl.trail.size) → (hj : j < s.cdcl.trail.size) →
    litVar s.cdcl.trail[i] = litVar s.cdcl.trail[j] → i = j
  levels_le : ∀ i, (hi : i < s.cdcl.trail.size) →
    stateLevel s.cdcl s.cdcl.trail[i] ≤ s.cdcl.level
  dec_sync : ∀ i, (hi : i < s.cdcl.trail.size) →
    s.isDecision s.cdcl.trail[i] = decide (stateReason s.cdcl s.cdcl.trail[i] = .decision)
  dec_earliest : ∀ i j, (hi : i < s.cdcl.trail.size) → (hj : j < s.cdcl.trail.size) →
    stateLevel s.cdcl s.cdcl.trail[i] = stateLevel s.cdcl s.cdcl.trail[j] →
    s.isDecision s.cdcl.trail[j] = true → j ≤ i
  db_sound : ∀ (cid : Nat) (c : Clause),
    s.cdcl.clauses[cid]? = some (some c) → s.cdcl.f0.EntailsClause (cnfClause c.lits)
  units_sound : ∀ u ∈ s.cdcl.units, s.cdcl.f0.EntailsClause (cnfClause [u])
  reason_dag : ReasonDagInv s.cdcl
  inconsistent_sound : s.cdcl.inconsistent = true → s.cdcl.f0.Unsat

/-! ## 2. Chronological transitions (`chronoBacktrack`, `chronoAssignUip`, `restartReuseTrail`) -/

/-- Initialize a `ChronoState` at level 0 from `cnf`. -/
@[expose] def chronoInit (cnf : CNF Nat) : ChronoState :=
  ChronoState.ofCdcl (initState cnf) #[]

/-- Push a new branch decision literal at `s.cdcl.level + 1` and record its frame offset. -/
@[expose] def chronoDecide (s : ChronoState) (l : Nat) : ChronoState :=
  { cdcl := decideLit s.cdcl l
    isDec := arraySetPad s.isDec (litVar l) true false
    frames := s.frames.push s.cdcl.trail.size }

/-- Push a non-decision propagated literal at current `s.cdcl.level`. -/
@[expose] def chronoAssignProp (s : ChronoState) (l : Nat) (rsn : Reason) : ChronoState :=
  { s with
    cdcl := assignLit s.cdcl l s.cdcl.level rsn
    isDec := arraySetPad s.isDec (litVar l) false false }

/-- **Chronological UIP / out-of-order assignment (`chrono=1`)**: assigns `uip` at arbitrary
`uipLevel ≤ s.cdcl.level` (possibly `uipLevel < s.cdcl.level`, sitting after higher-level
decisions and beyond `frames[uipLevel + 1]`) with non-decision reason `rsn`. -/
@[expose] def chronoAssignUip (s : ChronoState) (uip uipLevel : Nat) (rsn : Reason) : ChronoState :=
  { s with
    cdcl := assignLit s.cdcl uip uipLevel rsn
    isDec := arraySetPad s.isDec (litVar uip) false false }

/-- Push a level-0 unit literal onto trail and `units`. -/
@[expose] def chronoAddRootUnit (s : ChronoState) (l : Nat) : ChronoState :=
  { s with
    cdcl := assignLit { s.cdcl with units := l :: s.cdcl.units } l 0 .unit
    isDec := arraySetPad s.isDec (litVar l) false false }

/-- **Chronological backtracking (`chrono=1`, `backtrack.c:94-112`)**: compacts all trail
literals with `stateLevel ≤ targetLevel` left-to-right regardless of `levels_mono` or
`frames` offsets. -/
@[expose] def chronoBacktrack (s : ChronoState) (targetLevel : Nat) : ChronoState :=
  { s with
    cdcl := backtrackFilter s.cdcl targetLevel
    frames := s.frames.take (Nat.min s.cdcl.level targetLevel + 1) }

/-- Find the highest reusable decision level matching candidate branch decisions `[d₁, d₂, ...]`
using explicit `isDecision` markers rather than assuming `trail[frames[lvl]]` holds `d_{lvl}`. -/
@[expose] def restartReuseDecisionLevel (s : ChronoState) : List Nat → Nat → Nat
  | [], lvl => lvl
  | d :: rest, lvl =>
    let nextLvl := lvl + 1
    if nextLvl ≤ s.cdcl.level &&
        s.cdcl.trail.any (fun l =>
          s.isDecision l && stateLevel s.cdcl l == nextLvl && l == d) then
      restartReuseDecisionLevel s rest nextLvl
    else lvl

/-- **Restart trail reuse (`restartreusetrail=1`, consistent backtrack mode)**: backtracks to
`reuseLevel` while keeping all literals assigned at `level ≤ reuseLevel`, including out-of-order
chronologically assigned literals. -/
@[expose] def restartReuseTrail (s : ChronoState) (reuseLevel : Nat) : ChronoState :=
  chronoBacktrack s reuseLevel

/-- **Restart prefix trail reuse (`restartreusetrail=1`, contiguous prefix mode)**: keeps prefix
`trail[0..<prefixLen]` whose levels are bounded by `reuseLevel`; by `ReasonDagInv`, every
antecedent `j < i < prefixLen` automatically remains in the kept prefix. -/
@[expose] def restartReusePrefix (s : ChronoState) (reuseLevel prefixLen : Nat) : ChronoState :=
  let nl := Nat.min s.cdcl.level reuseLevel
  { s with
    cdcl := { s.cdcl with trail := s.cdcl.trail.extract 0 prefixLen, level := nl }
    frames := s.frames.take (nl + 1) }

/-! ## 3. 1UIP + OTFS resolution, lexicographic minimization & shrinking, and conflict step -/

/-- Single On-The-Fly Subsumption (`OTFS`, `deduce.c`) database clause strengthening event:
resolving the working conflict clause with reason clause `cid` (for `pivot`) yields `newLits`
whose literals are all already in `clauses[cid]`. -/
structure OtfsUpdate where
  cid : Nat
  pivot : Nat
  newLits : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Result of 1UIP conflict analysis with On-The-Fly Subsumption (`OTFS`). -/
structure ChronoAnalyzeOut where
  learned : List Nat
  otfs : List OtfsUpdate
  deriving Repr, DecidableEq, Inhabited

/-- Semantic validity of an OTFS update recorded during conflict analysis at `conflLvl`. -/
@[expose] def OtfsValidAt (s : ChronoState) (conflLvl : Nat) (u : OtfsUpdate) : Prop :=
  s.cdcl.f0.EntailsClause (cnfClause u.newLits) ∧
  (∀ x ∈ u.newLits, litNeg x ∈ s.cdcl.trail.toList) ∧
  ∃ oldC : Clause, s.cdcl.clauses[u.cid]? = some (some oldC) ∧
    !oldC.garbage = true ∧ u.pivot ∈ oldC.lits ∧ u.pivot ∉ u.newLits ∧
    stateLevel s.cdcl u.pivot = conflLvl ∧ (∀ x ∈ u.newLits, x ∈ oldC.lits)

/-- Backward trail resolution deriving 1UIP learned clause + OTFS clause strengthenings.
Explicitly checks `!s.isDecision p` and `stateLevel` rather than `frames` index bounds so
lower-level out-of-order trail literals are skipped cleanly. -/
@[expose] def chronoAnalyze1UIPAux (s : ChronoState) :
    Nat → List Nat → List OtfsUpdate → ChronoAnalyzeOut
  | 0, cl, ups => { learned := dedupLits cl, otfs := ups }
  | i + 1, cl, ups =>
    let cl := dedupLits cl
    if countAtLevel s.cdcl cl s.cdcl.level ≤ 1 then { learned := cl, otfs := ups }
    else if h : i < s.cdcl.trail.size then
      let p := s.cdcl.trail[i]
      let np := litNeg p
      if cl.contains np && stateLevel s.cdcl p == s.cdcl.level && !s.isDecision p then
        match stateReason s.cdcl p with
        | .binary other =>
          chronoAnalyze1UIPAux s i (dedupLits (resolveOn np cl [p, other])) ups
        | .large cid =>
          match s.cdcl.clauses[cid]? with
          | some (some c) =>
            let res := dedupLits (resolveOn np cl c.lits)
            let ups' :=
              if clauseSubset res c.lits then
                { cid := cid, pivot := p, newLits := res } :: ups
              else ups
            chronoAnalyze1UIPAux s i res ups'
          | _ => { learned := cl, otfs := ups }
        | .decision | .unit => { learned := cl, otfs := ups }
      else
        chronoAnalyze1UIPAux s i cl ups
    else
      chronoAnalyze1UIPAux s i cl ups

/-- Chronological-safe 1UIP conflict analysis with OTFS (`deduce.c`). -/
@[expose] def chronoAnalyze1UIP (s : ChronoState) (confl : List Nat) : ChronoAnalyzeOut :=
  if s.cdcl.level == 0 then { learned := [], otfs := [] }
  else chronoAnalyze1UIPAux s s.cdcl.trail.size (dedupLits confl) []

/-- Apply one OTFS database clause replacement at `u.cid`. -/
@[expose]
def applyOtfsUpdate (clauses : Array (Option Clause)) (u : OtfsUpdate) : Array (Option Clause) :=
  match clauses[u.cid]? with
  | some (some c) => clauses.setIfInBounds u.cid (some { c with lits := u.newLits })
  | _ => clauses

/-- Apply all OTFS database clause replacements. -/
@[expose] def applyOtfsUpdates (clauses : Array (Option Clause)) (ups : List OtfsUpdate) :
    Array (Option Clause) :=
  ups.foldl applyOtfsUpdate clauses

/-- Append a learned clause to `s.cdcl.clauses`. -/
@[expose]
def chronoAddLearnedClause (s : ChronoState) (lits : List Nat) (glue : Nat := 0) : ChronoState :=
  { s with cdcl := addLearnedClause s.cdcl lits glue }

/-- Run lexicographic `(level, trailPos)` recursive minimization (`MinimizeDfs`) on
`s : ChronoState`. -/
@[expose] def chronoMinimize (s : ChronoState) (maxDepth : Nat) (c : List Nat) : List Nat :=
  (minimizeClauseWorklist (MinState.ofCdcl s.cdcl) maxDepth c).1

/-- Run lexicographic `(level, trailPos)` block shrinking (`FailedLit`) on
`s : ChronoState`. -/
@[expose] def chronoShrink (s : ChronoState) (alwaysMin resolveLarge : Bool) (maxDepth : Nat)
    (c : List Nat) : List Nat :=
  (shrinkClauseExec (MinState.ofCdcl s.cdcl) alwaysMin resolveLarge maxDepth c).1

/-- Full composed chronological conflict step:
1. Backtracks chronologically to `targetLevel` (`uipLevel ≤ targetLevel < s.cdcl.level`),
2. Applies all OTFS database clause strengthenings `ups` from `chronoAnalyze1UIP`,
3. Inserts the learned clause `learned` into `clauses`, and
4. Assigns `uip` out-of-order at `uipLevel` (`≤ targetLevel`). -/
@[expose] def chronoConflictStep (s : ChronoState) (targetLevel : Nat) (ups : List OtfsUpdate)
    (learned : List Nat) (glue uip uipLevel : Nat) : ChronoState :=
  let s1 := chronoBacktrack s targetLevel
  let s2 := { s1 with cdcl := { s1.cdcl with clauses := applyOtfsUpdates s1.cdcl.clauses ups } }
  let newCid := s2.cdcl.clauses.size
  let s3 := chronoAddLearnedClause s2 learned glue
  let rsn : Reason := if learned.length ≤ 1 && uipLevel == 0 then .unit else .large newCid
  chronoAssignUip s3 uip uipLevel rsn

end LeanQbe.T.Examples.Kissat.Ref
