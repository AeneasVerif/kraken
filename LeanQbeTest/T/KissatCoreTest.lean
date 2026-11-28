module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Cdcl
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesLemmas
meta import LeanQbe.T.Examples.Kissat.Ref.Sat
meta import LeanQbe.T.Examples.LratBytes

/-!
# Verification and Axiom Audit for `LeanQbe.T.Examples.Kissat`

Executable kernel/VM `#guard` checks and standard-axiom audits covering:
1. Kissat literal encoding, CNF conversion, and `checkModel`.
2. Resolution, root-unit pruning, and self-subsuming binary strengthening.
3. 1UIP conflict analysis, failed-literal probing, minimization cut, and `RefMap` collection.
4. `cdclSolve` across SAT, UNSAT (`PHP(3,2)`, `PHP(4,3)`, conflict chains, empty/tautological/
   duplicate-literal clauses), and `unknown` (`fuel = 0`).
5. Concrete `LeanQbe.T.Examples.LratBytes.parseDimacs` / `nvBytesCnf` bridges and `#print axioms`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatCoreTest

open Std.Sat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Helper CNF builders (Pigeonhole Principle `PHP(p, h)`) -/

/-- Encode Pigeonhole Principle `PHP(pigeons, holes)` in 0-based variable indexing (`v = i*h + j`),
using `mkLit` positive/negative literals (`2*v` / `2*v+1`). -/
public def phpClauses (pigeons holes : Nat) : List (List Nat) :=
  let alo := (List.range pigeons).map fun i =>
    (List.range holes).map fun j => mkLit (i * holes + j) true
  let amo := ((List.range holes).flatMap fun j =>
    (List.range pigeons).flatMap fun i1 =>
      (List.range pigeons).filterMap fun i2 =>
        if i1 < i2 then
          some [mkLit (i1 * holes + j) false, mkLit (i2 * holes + j) false]
        else none)
  alo ++ amo

public def php1Clauses (pigeons holes : Nat) : List (List Nat) :=
  let alo := (List.range pigeons).map fun i =>
    (List.range holes).map fun j => mkLit (1 + i * holes + j) true
  let amo := ((List.range holes).flatMap fun j =>
    (List.range pigeons).flatMap fun i1 =>
      (List.range pigeons).filterMap fun i2 =>
        if i1 < i2 then
          some [mkLit (1 + i1 * holes + j) false, mkLit (1 + i2 * holes + j) false]
        else none)
  alo ++ amo

public def phpCnf (pigeons holes : Nat) : CNF Nat :=
  cnfOfClauses (phpClauses pigeons holes)

public def php1Cnf (pigeons holes : Nat) : CNF Nat :=
  cnfOfClauses (php1Clauses pigeons holes)

/-! ## 2. Literal encoding, CNF bridge, and `checkModel` -/

#guard mkLit 0 true == 0
#guard mkLit 0 false == 1
#guard mkLit 5 true == 10
#guard mkLit 5 false == 11
#guard litVar 11 == 5 && litSign 11 == true && litPol 11 == false
#guard litNeg 0 == 1 && litNeg 1 == 0 && litNeg 10 == 11
#guard litToDimacs 0 == 1 && litToDimacs 1 == -1
#guard dimacsToLit 1 == some 0 && dimacsToLit (-1) == some 1 && dimacsToLit 0 == none
#guard litOfBitVec 0#32 == 0 && litOfBitVec 7#32 == 7
#guard litOfLiteral (litToLiteral 13) == 13
#guard clauseOfCnf (cnfClause [0, 3, 4]) == [0, 3, 4]

private def sat2Cnf : CNF Nat :=
  cnfOfClauses [[0, 2], [1, 4], [5, 2]]

#guard checkModel sat2Cnf #[true, true, true] == true
#guard checkModel sat2Cnf #[true, false, true] == false
#guard checkModel sat2Cnf #[false, false, false] == false
#guard checkModel nvBytesCnf #[true, false] == false
#guard checkModel nvBytesCnf #[true, true] == false

/-! ## 3. Resolution, root stripping, pruning, and binary strengthening -/

#guard resolveOn 2 [0, 2, 4] [3, 6] == [0, 4, 6]
#guard stripRootUnits [0, 3] [1, 2, 4] == [4]
#guard pruneClause [0, 3] [0, 4] == none
#guard pruneClause [0, 3] [1, 2, 4] == some [4]
#guard strengthenWithBinary [1, 2, 4] 0 2 == [2, 4]
#guard strengthenWithBinary [1, 2, 4] 0 1 == [1, 2, 4]

/-! ## 4. 1UIP conflict analysis, failed-literal probing, minimization, and `collect` -/

private def sample1UipState : CdclState :=
  -- Variables 0..3: dec x0=T @1, prop x1=T @1 (¬x0 ∨ x1), prop x2=T @1 (¬x0 ∨ x2),
  -- prop x3=T @1 (¬x1 ∨ ¬x2 ∨ x3). Conflict clause [¬x2, ¬x3] resolves x3 -> [¬x1, ¬x2],
  -- then x2 -> [¬x0, ¬x1] -> 1UIP resolves x1 -> [¬x0].
  { f0 := cnfOfClauses [[0], [1, 2], [1, 4], [3, 5, 6], [5, 7]]
    numVars := 4
    clauses := #[some { lits := [1, 2] }, some { lits := [1, 4] },
      some { lits := [3, 5, 6] }, some { lits := [5, 7] }]
    units := []
    trail := #[0, 2, 4, 6]
    levels := #[1, 1, 1, 1]
    reasons := #[.decision, .binary 1, .binary 1, .large 2]
    level := 1
    inconsistent := false }

#guard
  let learned := analyze1UIP sample1UipState [5, 7]
  learned == [1] && countAtLevel sample1UipState learned 1 ≤ 1

private def failedLitProbeState : CdclState :=
  -- (x0 ∨ x1) ∧ (x0 ∨ ¬x1) at level 0; probing ¬x0 (= 1) propagates x1 then fails.
  { f0 := cnfOfClauses [[0, 2], [0, 3]]
    numVars := 2
    clauses := #[some { lits := [0, 2] }, some { lits := [0, 3] }]
    units := []
    trail := #[]
    levels := #[0, 0]
    reasons := #[.unit, .unit]
    level := 0
    inconsistent := false }

#guard match failedLitStep 10 failedLitProbeState (litNeg 0) with
  | .learnedUnit u s' => u == 0 && litStatus s'.trail 0 == some true
  | _ => false

#guard match failedLitStep 10 failedLitProbeState 2 with
  | .normal _ => true
  | _ => false

private def minimizeTestState : CdclState :=
  -- Level 0: x0=T; Level 1: dec x1=T, prop x2=T from (¬x0 ∨ ¬x1 ∨ x2).
  -- On learned clause [¬x0, ¬x1, ¬x2], ¬x0 is level 0 and ¬x2 is subsumed by ¬x0, ¬x1.
  { f0 := cnfOfClauses [[0], [1, 3, 4]]
    numVars := 3
    clauses := #[some { lits := [1, 3, 4] }]
    units := [0]
    trail := #[0, 2, 4]
    levels := #[0, 1, 1]
    reasons := #[.unit, .decision, .large 0]
    level := 1
    inconsistent := false }

#guard minimizeClause minimizeTestState [1, 3, 5] == [3]

private def collectTestState : CdclState :=
  { f0 := cnfOfClauses [[0, 2], [1, 4], [3, 5]]
    numVars := 3
    clauses := #[some { lits := [0, 2], garbage := true }, none,
      some { lits := [1, 4], garbage := false }, some { lits := [3, 5], garbage := true },
      some { lits := [0, 5], garbage := false }]
    units := []
    trail := #[0, 4]
    levels := #[1, 1, 1]
    reasons := #[.decision, .unit, .large 2]
    level := 1
    inconsistent := false }

#guard
  let (s', rmap) := collect collectTestState
  rmap.lookup 0 == none && rmap.lookup 1 == none &&
  rmap.lookup 2 == some 0 && rmap.lookup 4 == some 1 &&
  s'.clauses.size == 2 && stateReason s' 4 == .large 0

#guard
  let s' := deleteClauseState collectTestState 0
  s'.clauses[0]? == some none

/-! ## 5. Executable `cdclSolve` tests (SAT, UNSAT, edge cases, `PHP(3,2)`, `PHP(4,3)`) -/

#guard (cdclSolve 20 (cnfOfClauses [])).code == 10
#guard match cdclSolve 20 sat2Cnf with
  | .sat σ => checkModel sat2Cnf σ
  | _ => false
#guard match cdclSolve 40 (cnfOfClauses [[0, 2, 4], [1, 2], [3, 4], [5, 0]]) with
  | .sat σ => checkModel (cnfOfClauses [[0, 2, 4], [1, 2], [3, 4], [5, 0]]) σ
  | _ => false

-- Empty clause, tautological clause + unsat core, duplicate-literal clauses, implication chain
#guard cdclSolve 20 (cnfOfClauses [[]]) == .unsat
#guard cdclSolve 20 (cnfOfClauses [[0, 1], [0], [1]]) == .unsat
#guard cdclSolve 20 (cnfOfClauses [[0, 0], [1, 1]]) == .unsat
#guard cdclSolve 30 (cnfOfClauses [[0], [1, 2], [3, 4], [5, 6], [7, 1]]) == .unsat
#guard cdclSolve 0 sat2Cnf == .unknown

-- Pigeonhole Principle UNSAT benchmarks
#guard cdclSolve 200 (phpCnf 3 2) == .unsat
#guard cdclSolve 1000 (phpCnf 4 3) == .unsat

/-! ## 6. Concrete `LratBytes.parseDimacs` + `nvBytesCnf` bridges & axiom audit -/

private def satDimacsBytes : List UInt8 :=
  ("p cnf 3 2\n1 -2 0\n2 3 0\n").toUTF8.toList

#guard (parseDimacs nvDimacsBytes).map clausesOfCnf == some (clausesOfCnf nvBytesCnf)
#guard cdclSolve 20 nvBytesCnf == .unsat
#guard match parseDimacs satDimacsBytes with
  | some cnf => match cdclSolve 20 cnf with
    | .sat σ => checkModel cnf σ
    | _ => false
  | none => false
#guard match parseDimacs (encodeDimacs (php1Cnf 3 2)) with
  | some cnf => cdclSolve 200 cnf == .unsat
  | none => false

/-- Concrete `LratBytes.parseDimacs` + `checkModel_sound` bridge. -/
public theorem parse_model_ok
    {bs : List UInt8} {cnf : CNF Nat} {σ : Array Bool}
    (hp : parseDimacs bs = some cnf) (h : checkModel cnf σ = true) :
    ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α :=
  checkModel_sound_of_parse (parse := parseDimacs) hp h

/-- Concrete `LratBytes.parseDimacs` + `cdclSolve_sound` bridge. -/
public theorem parse_cdcl_ok
    {bs : List UInt8} {cnf : CNF Nat} (fuel : Nat)
    (hp : parseDimacs bs = some cnf) :
    match cdclSolve fuel cnf with
    | .unsat => cnf.Unsat
    | .sat _ => ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α
    | .unknown => True :=
  cdclSolve_sound_of_parse (parse := parseDimacs) fuel hp

/-- Certified UNSAT soundness statement tying `parseDimacs nvDimacsBytes` to `cdclSolve`. -/
public theorem nv_cdcl_unsat (h : cdclSolve 20 nvBytesCnf = .unsat) : nvBytesCnf.Unsat := by
  have hsolve := parse_cdcl_ok 20 nvDimacsBytes_parse
  rw [h] at hsolve; exact hsolve

public abbrev ax_del_inv := @LeanQbe.T.Examples.Kissat.Ref.deleteClauseState_preserves_inv

#print axioms LeanQbe.T.Examples.Kissat.Ref.checkModel_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.analyze1UIP_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.failedLit_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.minimizeCut_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.collect_preserves_inv
#print axioms ax_del_inv
#print axioms LeanQbe.T.Examples.Kissat.Ref.cdclSolve_sound
#print axioms LeanQbeTest.T.KissatCoreTest.parse_model_ok
#print axioms LeanQbeTest.T.KissatCoreTest.parse_cdcl_ok
#print axioms LeanQbeTest.T.KissatCoreTest.nv_cdcl_unsat

end LeanQbeTest.T.KissatCoreTest