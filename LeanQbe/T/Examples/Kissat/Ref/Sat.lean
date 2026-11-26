/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Base

/-!
# Kissat Abstract CDCL Soundness Core (Layer A, pure definitions)

Pure Lean executable specification and transition functions for an abstract Kissat-style CDCL
SAT solver over `List`, `Array`, and `Std.Sat.CNF`:

1. DIMACS literal Int conversion (`litToDimacs`, `dimacsToLit`) on top of `Ref.Base`.
2. CNF database (`Clause`, `DB` with irredundant/redundant/garbage flags and root unit list),
   `Reason` (`decision`, `unit`, `binary`, `large`), and abstract state `CdclState`.
3. Pure executable transitions and checkers (`#eval`-ready): `modelFromTrail`, `stripRootUnits`,
   `pruneClause`, `strengthenWithBinary`, `unitPropStep`, `propagateAll`, `analyze1UIP`,
   `failedLitStep`, `minimizeClause`, `collect` (`RefMap`), and reference solver `cdclSolve`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Signed DIMACS `Int` literal bridges and trail model reconstruction -/

/-- Export a 0-based Kissat internal literal to 1-based signed DIMACS `Int`. -/
@[expose] def litToDimacs (l : Nat) : Int :=
  if litSign l then -Int.ofNat (litVar l + 1) else Int.ofNat (litVar l + 1)

/-- Import a non-zero 1-based signed DIMACS `Int` into a 0-based Kissat literal. -/
@[expose] def dimacsToLit (e : Int) : Option Nat :=
  if e == 0 then none
  else if e > 0 then some (2 * (e.natAbs - 1))
  else some (2 * (e.natAbs - 1) + 1)

/-- Reconstruct a `Bool` model of size `numVars` from a solver trail. -/
@[expose] def modelFromTrail (numVars : Nat) (trail : Array Nat) : Array Bool :=
  trail.foldl (init := Array.replicate numVars false) fun σ l =>
    let v := litVar l
    if h : v < σ.size then σ.set v (litPol l) h else σ

/-! ## 2. Clause database, trail reasons, and abstract CDCL state -/

/-- Clause database entry supporting irredundant, redundant, and garbage-marked clauses. -/
structure Clause where
  lits : List Nat
  redundant : Bool := false
  garbage : Bool := false
  glue : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Abstract clause database with indexed clause slots and root-level unit literals. -/
structure DB where
  clauses : Array (Option Clause)
  units : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- Lookup an active (present, non-garbage) clause in `DB` by ID. -/
@[expose] def DB.getClause? (db : DB) (cid : Nat) : Option Clause :=
  match db.clauses[cid]? with
  | some (some c) => if c.garbage then none else some c
  | _ => none

/-- All active (present, non-garbage) clauses in `DB`. -/
@[expose] def DB.activeClauses (db : DB) : List Clause :=
  db.clauses.toList.filterMap fun opt =>
    match opt with
    | some c => if c.garbage then none else some c
    | none => none

/-- All active irredundant clauses in `DB`. -/
@[expose] def DB.irredClauses (db : DB) : List Clause :=
  db.activeClauses.filter (fun c => !c.redundant)

/-- All active redundant (learned) clauses in `DB`. -/
@[expose] def DB.redClauses (db : DB) : List Clause :=
  db.activeClauses.filter (fun c => c.redundant)

/-- Append a new clause to `DB`, returning the updated `DB` and assigned clause ID. -/
@[expose] def DB.addClause (db : DB) (c : Clause) : DB × Nat :=
  let cid := db.clauses.size
  ({ db with clauses := db.clauses.push (some c) }, cid)

/-- Mark clause `cid` as garbage if present. -/
@[expose] def DB.markGarbage (db : DB) (cid : Nat) : DB :=
  match db.clauses[cid]? with
  | some (some c) => { db with clauses := db.clauses.set! cid (some { c with garbage := true }) }
  | _ => db

/-- Physically remove slot `cid` (`none`) in `DB`. -/
@[expose] def DB.deleteClause (db : DB) (cid : Nat) : DB :=
  { db with clauses := db.clauses.setIfInBounds cid none }

/-- Reason justification for an assigned literal on the CDCL trail. -/
inductive Reason where
  | decision
  | unit
  | binary (other : Nat)
  | large (cid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Abstract Layer-A CDCL solver state. -/
structure CdclState where
  f0 : CNF Nat
  numVars : Nat
  clauses : Array (Option Clause)
  units : List Nat
  trail : Array Nat
  levels : Array Nat
  reasons : Array Reason
  level : Nat
  inconsistent : Bool

/-- Project the clause database view of `CdclState`. -/
@[expose] def CdclState.db (s : CdclState) : DB :=
  ⟨s.clauses, s.units⟩

/-- Check if literal `l` appears on `trail`. -/
@[expose] def trailHasLit (trail : Array Nat) (l : Nat) : Bool :=
  trail.contains l

/-- Partial truth assignment of literal `l` induced by `trail`. -/
@[expose] def litStatus (trail : Array Nat) (l : Nat) : Option Bool :=
  if trail.contains l then some true
  else if trail.contains (litNeg l) then some false
  else none

/-- Find the first index of literal `l` on `trail`. -/
@[expose] def trailIdxOf? (trail : Array Nat) (l : Nat) : Option Nat :=
  trail.findIdx? (· == l)

/-- Decision level recorded for the variable of `l`. -/
@[expose, inline] def stateLevel (s : CdclState) (l : Nat) : Nat :=
  s.levels.getD (litVar l) 0

/-- Reason recorded for the variable of `l`. -/
@[expose, inline] def stateReason (s : CdclState) (l : Nat) : Reason :=
  s.reasons.getD (litVar l) .unit

/-- Push literal `l` onto `s.trail` at level `lvl` with reason `rsn`. -/
@[expose] def assignLit (s : CdclState) (l : Nat) (lvl : Nat) (rsn : Reason) : CdclState :=
  let v := litVar l
  { s with
    trail := s.trail.push l
    levels := arraySetPad s.levels v lvl 0
    reasons := arraySetPad s.reasons v rsn .unit }

/-- Make a new decision `l` at `s.level + 1`. -/
@[expose] def decideLit (s : CdclState) (l : Nat) : CdclState :=
  let lvl' := s.level + 1
  assignLit { s with level := lvl' } l lvl' .decision

/-- Backtrack `s.trail` to `targetLevel` by keeping the longest prefix at level `≤ targetLevel`. -/
@[expose] def backtrackTo (s : CdclState) (targetLevel : Nat) : CdclState :=
  let keepCount :=
    (s.trail.toList.takeWhile (fun l => s.levels.getD (litVar l) 0 ≤ targetLevel)).length
  { s with
    trail := s.trail.extract 0 keepCount
    level := Nat.min s.level targetLevel }

/-- Append a learned (or derived) clause to `s.clauses`. -/
@[expose] def addLearnedClause (s : CdclState) (lits : List Nat) (glue : Nat := 0) : CdclState :=
  let c : Clause := { lits := lits, redundant := true, garbage := false, glue := glue }
  { s with clauses := s.clauses.push (some c) }

/-- Delete/free clause slot `cid` in `s.clauses` (marking slot `none`). -/
@[expose] def deleteClauseState (s : CdclState) (cid : Nat) : CdclState :=
  { s with clauses := s.clauses.setIfInBounds cid none }

/-! ## 3. Root stripping, pruning, and binary strengthening -/

/-- Strip literals whose negation appears in root `units`. -/
@[expose] def stripRootUnits (units : List Nat) (c : List Nat) : List Nat :=
  stripFalsified (fun l => units.contains (litNeg l)) c

/-- Prune a clause against root `units`: returns `none` if already root-satisfied, else
`some` with root-falsified literals removed. -/
@[expose] def pruneClause (units : List Nat) (c : List Nat) : Option (List Nat) :=
  if c.any (fun l => units.contains l) then none
  else some (stripRootUnits units c)

/-- Self-subsuming binary strengthening: if `binOther ≠ litNeg pivot` and `binOther ∈ c` (where
`[pivot, binOther]` is entailed), drop `litNeg pivot` from `c`. -/
@[expose] def strengthenWithBinary (c : List Nat) (pivot binOther : Nat) : List Nat :=
  if binOther != litNeg pivot && c.contains binOther then c.filter (· != litNeg pivot) else c

/-! ## 4. Unit propagation -/

/-- Classification of a clause's literals under a partial trail assignment. -/
inductive PropClauseStatus where
  | satisfied
  | falsified
  | unit (lit : Nat)
  | unresolved
  deriving Repr, DecidableEq

@[expose] def classifyClauseAux (trail : Array Nat) :
    List Nat → Option Nat → PropClauseStatus
  | [], none => .falsified
  | [], some u => .unit u
  | l :: ls, cand =>
    match litStatus trail l with
    | some true => .satisfied
    | some false => classifyClauseAux trail ls cand
    | none =>
      match cand with
      | none => classifyClauseAux trail ls (some l)
      | some u =>
        if u == l then classifyClauseAux trail ls (some l) else .unresolved

/-- Classify a clause `lits` under `trail`. -/
@[expose] def classifyClause (trail : Array Nat) (lits : List Nat) : PropClauseStatus :=
  classifyClauseAux trail lits none

/-- Outcome of a single unit-propagation step. -/
inductive UnitPropRes where
  | unchanged (s : CdclState)
  | propagated (s : CdclState)
  | conflict (clits : List Nat) (s : CdclState)

@[expose] def unitPropUnitsAux (s : CdclState) : List Nat → Option UnitPropRes
  | [] => none
  | u :: us =>
    match litStatus s.trail u with
    | some true => unitPropUnitsAux s us
    | some false => some (.conflict [u] { s with inconsistent := (s.level == 0) })
    | none =>
      if s.level == 0 then some (.propagated (assignLit s u 0 .unit))
      else unitPropUnitsAux s us

@[expose] def unitReasonFor (cid : Nat) (lits : List Nat) (u : Nat) : Reason :=
  match lits with
  | [a, b] =>
    if a == u && b != u then .binary b
    else if b == u && a != u then .binary a
    else .large cid
  | _ => .large cid

@[expose] def unitPropClausesAux (s : CdclState) (idx : Nat) : UnitPropRes :=
  if h : idx < s.clauses.size then
    match s.clauses[idx] with
    | some c =>
      if c.garbage then
        unitPropClausesAux s (idx + 1)
      else
        match classifyClause s.trail c.lits with
        | .falsified => .conflict c.lits { s with inconsistent := (s.level == 0) }
        | .unit u => .propagated (assignLit s u s.level (unitReasonFor idx c.lits u))
        | .satisfied | .unresolved => unitPropClausesAux s (idx + 1)
    | none => unitPropClausesAux s (idx + 1)
  else
    .unchanged s
termination_by s.clauses.size - idx

/-- Perform one unit-propagation or conflict-detection step over `s.units` (at level 0) and
active entries in `s.clauses`. -/
@[expose] def unitPropStep (s : CdclState) : UnitPropRes :=
  match unitPropUnitsAux s s.units with
  | some res => res
  | none => unitPropClausesAux s 0

/-- Outcome of bounded exhaustive unit propagation (`propagateAll`). -/
inductive PropagateOut where
  | ok (s : CdclState)
  | conflict (clits : List Nat) (s : CdclState)
  | outOfFuel (s : CdclState)

/-- Propagate unit clauses to fixpoint, conflict, or fuel exhaustion. -/
@[expose] def propagateAll : Nat → CdclState → PropagateOut
  | 0, s => .outOfFuel s
  | fuel + 1, s =>
    match unitPropStep s with
    | .unchanged s' => .ok s'
    | .propagated s' => propagateAll fuel s'
    | .conflict clits s' => .conflict clits s'

/-! ## 5. 1UIP conflict analysis -/

/-- Count literals in `c` whose variable is assigned at level `lvl`. -/
@[expose] def countAtLevel (s : CdclState) (c : List Nat) (lvl : Nat) : Nat :=
  (c.filter (fun l => stateLevel s l == lvl)).length

/-- Backward trail walk deriving a 1UIP learned clause from `cl`. -/
@[expose] def analyze1UIPAux (s : CdclState) : Nat → List Nat → List Nat
  | 0, cl => dedupLits cl
  | i + 1, cl =>
    let cl := dedupLits cl
    if countAtLevel s cl s.level ≤ 1 then cl
    else if h : i < s.trail.size then
      let p := s.trail[i]
      let np := litNeg p
      if cl.contains np && stateLevel s p == s.level then
        match stateReason s p with
        | .binary other =>
          analyze1UIPAux s i (dedupLits (resolveOn np cl [p, other]))
        | .large cid =>
          match s.clauses[cid]? with
          | some (some c) =>
            analyze1UIPAux s i (dedupLits (resolveOn np cl c.lits))
          | _ => cl
        | .decision | .unit => cl
      else
        analyze1UIPAux s i cl
    else
      analyze1UIPAux s i cl

/-- 1UIP conflict analysis returning the derived learned clause (empty at level 0). -/
@[expose] def analyze1UIP (s : CdclState) (confl : List Nat) : List Nat :=
  if s.level == 0 then []
  else analyze1UIPAux s s.trail.size (dedupLits confl)

/-- Compute the backtrack level of `learned`: maximum level among literals not at `s.level`
(or `0` when all literals are at `s.level`). -/
@[expose] def backtrackLevel (s : CdclState) (learned : List Nat) : Nat :=
  learned.foldl (fun acc l =>
    let lvl := stateLevel s l
    if lvl < s.level then Nat.max acc lvl else acc) 0

/-! ## 6. Failed-literal probing -/

/-- Outcome of probing a candidate literal `l` at decision level 1. -/
inductive FailedLitRes where
  | normal (s : CdclState)
  | learnedUnit (u : Nat) (s : CdclState)
  | conflict (s : CdclState)

/-- Probe literal `l` at level 1 when `s.level == 0` and `l` is unassigned: if unit propagation
reaches a conflict, backtrack and add `litNeg l` as a level-0 root unit. -/
@[expose] def failedLitStep (fuel : Nat) (s : CdclState) (l : Nat) : FailedLitRes :=
  if s.level != 0 then .normal s
  else
    match litStatus s.trail l with
    | some true => .normal s
    | some false => .normal s
    | none =>
      let s1 := decideLit s l
      match propagateAll fuel s1 with
      | .conflict _ _ =>
        let nl := litNeg l
        let s' := assignLit { s with units := nl :: s.units } nl 0 .unit
        .learnedUnit nl s'
      | .ok _ | .outOfFuel _ => .normal s

/-! ## 7. Clause minimization cut and `RefMap` garbage relocation -/

/-- Lexicographic `(level, trailIdx)` measure of falsified literal `l` (bounded by `trail.size`). -/
@[expose] def lexMeasure (s : CdclState) (l : Nat) : Nat :=
  let lvl := stateLevel s l
  let idx := (trailIdxOf? s.trail (litNeg l)).getD s.trail.size
  lvl * (s.trail.size + 1) + idx

/-- Strict lexicographic `(level, trailIdx)` comparison on falsified literals. -/
@[expose] def lexLtBool (s : CdclState) (l1 l2 : Nat) : Bool :=
  let lvl1 := stateLevel s l1
  let lvl2 := stateLevel s l2
  if lvl1 < lvl2 then true
  else if lvl1 == lvl2 then
    match trailIdxOf? s.trail (litNeg l1), trailIdxOf? s.trail (litNeg l2) with
    | some i1, some i2 => i1 < i2
    | _, _ => false
  else false

@[expose] def litMinSubAux (s : CdclState) (c : List Nat) (rootLit : Nat) :
    Nat → Nat → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, curr, allowSelf =>
    if !trailHasLit s.trail (litNeg curr) then false
    else if stateLevel s curr == 0 then true
    else if allowSelf && c.contains curr && lexLtBool s curr rootLit then true
    else
      match stateReason s curr with
      | .decision => false
      | .unit => stateLevel s curr == 0
      | .binary other =>
        lexLtBool s other curr && litMinSubAux s c rootLit fuel other true
      | .large cid =>
        match s.clauses[cid]? with
        | some (some cl) =>
          let ncurr := litNeg curr
          !cl.garbage && cl.lits.contains ncurr &&
            cl.lits.all (fun x =>
              x == ncurr || (lexLtBool s x curr && litMinSubAux s c rootLit fuel x true))
        | _ => false

/-- Check whether literal `l ∈ c` can be safely eliminated against strictly `≺`-smaller clause
literals in `c` and level-0 literals along reason predecessors. -/
@[expose] def isMinimizable (s : CdclState) (c : List Nat) (l : Nat) : Bool :=
  litMinSubAux s c l (s.trail.size + 1) l false

/-- Minimize clause `c` by removing every literal certified by `isMinimizable`. -/
@[expose] def minimizeClause (s : CdclState) (c : List Nat) : List Nat :=
  c.filter (fun l => !isMinimizable s c l)

/-- Clause-ID relocation map produced by `collect`. -/
abbrev RefMap := Array (Option Nat)

/-- Lookup relocated clause ID in `RefMap`. -/
@[expose] def RefMap.lookup (rmap : RefMap) (cid : Nat) : Option Nat :=
  (rmap[cid]?).join

/-- Compact `clauses` by dropping `none` and `garbage = true` entries, returning the dense
clause array and its injective relocation map `RefMap`. -/
@[expose] def collectClauses (clauses : Array (Option Clause)) : Array (Option Clause) × RefMap :=
  clauses.foldl (init := (#[], #[])) fun (acc, rmap) opt =>
    match opt with
    | some c =>
      if c.garbage then
        (acc, rmap.push none)
      else
        let newId := acc.size
        (acc.push (some c), rmap.push (some newId))
    | none => (acc, rmap.push none)

/-- Remap a `Reason`'s large clause ID through `rmap`. -/
@[expose] def remapReason (rmap : RefMap) : Reason → Reason
  | .large cid =>
    match rmap.lookup cid with
    | some newCid => .large newCid
    | none => .large cid
  | r => r

/-- Compact `s.clauses` and relocate `s.reasons` via `RefMap`. -/
@[expose] def collect (s : CdclState) : CdclState × RefMap :=
  let (newClauses, rmap) := collectClauses s.clauses
  ({ s with
     clauses := newClauses
     reasons := s.reasons.map (remapReason rmap) }, rmap)

/-! ## 8. Fuel-bounded reference CDCL solver (`cdclSolve`) -/

/-- Reference solver result (`0` unknown, `10` sat + witness, `20` unsat). -/
inductive CdclResult where
  | unknown
  | sat (model : Array Bool)
  | unsat
  deriving Repr, DecidableEq, Inhabited

/-- Standard SAT-competition status code (`0`, `10`, `20`). -/
@[expose] def CdclResult.code : CdclResult → Nat
  | .unknown => 0
  | .sat _ => 10
  | .unsat => 20

/-- Initialize `CdclState` at level `0` from `cnf : CNF Nat`. -/
@[expose] def initState (cnf : CNF Nat) : CdclState :=
  let nv := maxVarCnf cnf
  { f0 := cnf
    numVars := nv
    clauses := cnf.clauses.map (fun c => some { lits := clauseOfCnf c })
    units := []
    trail := #[]
    levels := Array.replicate nv 0
    reasons := Array.replicate nv .unit
    level := 0
    inconsistent := false }

@[expose] def pickVarFrom? (s : CdclState) (idx : Nat) : Option Nat :=
  if _h : idx < s.numVars then
    let l := mkLit idx false
    match litStatus s.trail l with
    | none => some l
    | some _ => pickVarFrom? s (idx + 1)
  else none
termination_by s.numVars - idx

/-- Pick an unassigned decision literal from an unsatisfied clause or `0 ..< s.numVars`. -/
@[expose] def pickBranchLit? (s : CdclState) : Option Nat :=
  let fromClause := s.clauses.findSome? fun opt =>
    match opt with
    | some c =>
      if c.garbage then none
      else match classifyClause s.trail c.lits with
      | .satisfied => none
      | _ => c.lits.find? (fun l => (litStatus s.trail l).isNone)
    | none => none
  match fromClause with
  | some l => some l
  | none => pickVarFrom? s 0

/-- Main fuel-bounded CDCL loop preserving `TrailInv`. -/
@[expose] def cdclLoop : Nat → CdclState → CdclResult
  | 0, _ => .unknown
  | fuel + 1, s =>
    if s.inconsistent then .unsat
    else
      let propFuel := s.numVars + s.clauses.size + s.units.length + 16
      match propagateAll propFuel s with
      | .outOfFuel _ => .unknown
      | .conflict confl s1 =>
        if s1.level == 0 then
          .unsat
        else
          let raw := analyze1UIP s1 confl
          let learned := minimizeClause s1 raw
          if learned.isEmpty then
            .unsat
          else
            let blevel := Nat.min (s1.level - 1) (backtrackLevel s1 learned)
            let s2 := backtrackTo s1 blevel
            let s3 := addLearnedClause s2 learned
            cdclLoop fuel s3
      | .ok s1 =>
        match pickBranchLit? s1 with
        | some l => cdclLoop fuel (decideLit s1 l)
        | none =>
          let σ := modelFromTrail s1.numVars s1.trail
          if checkModel s1.f0 σ then .sat σ else .unknown

/-- Pure executable fuel-bounded CDCL reference solver over `Std.Sat.CNF Nat`. -/
@[expose] def cdclSolve (fuel : Nat) (cnf : CNF Nat) : CdclResult :=
  cdclLoop fuel (initState cnf)

end LeanQbe.T.Examples.Kissat.Ref
