/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl
public import LeanQbe.T.Examples.Kissat.Ref.Substitute

/-!
# Pure Lean Layer-A Inprocessing Theory: Bounded Variable Elimination

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of single- and
multi-pivot bounded variable elimination (`BVE`, `bveElim`, `bveElimCnf`, `bveBoundedElim`) and
LIFO SAT witness reconstruction (`BveWitness`, `BveStack`, `extendBve`, `extendBveArray`)
modeling `kissat_extend`, plus end-to-end integration with `cdclSolve`:

1. **Tautology & literal helpers**: `litVar_eq_iff_mkLit`, `clauseIsTaut_congr`,
   `sat_cnfClause_congr`, `setModelVar`, `resolveOn_comm_mem` (reusing `Substitute`'s
   `clauseIsTaut`, `substUpdate`, and `clauseEvalVal`).
2. **Single-step pivot partition, UNSAT soundness & witness reconstruction**: `bvePartition`,
   `bveClauses`, `bve_unsat_sound`, `extendBveStep_sound`, `extendBveStep_sat`,
   `extendBveStepArr_sound`.
3. **Iterated elimination & LIFO witness stack**: `BveStack`, `bveStep`, `bveElim`,
   `bveElimCnf`, `bveBoundedElim`, `bveElim_unsat_sound`, `extendBve_sound`,
   `extendBveArray_cnf`, `bveElim_equisat`, and `cdclSolveAfterBve_sound`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Model variable update helper -/

/-- Pointwise variable update on executable `Array Bool` model. -/
@[expose] def setModelVar (σ : Array Bool) (v : Nat) (b : Bool) : Array Bool :=
  arraySetPad σ v b false

/-! ## 2. Pivot partition, BVE resolvents, and `bve` formula transformation -/

/-- Partition clauses on pivot variable `v` into `(P, N, R)`:
`P` (`pos ∈ C ∧ neg ∉ C`), `N` (`neg ∈ D ∧ pos ∉ D`), `R` (`pos ∉ C ∧ neg ∉ C`),
dropping tautological clauses that contain both `pos` and `neg`. -/
@[expose] def bvePartition (cs : List (List Nat)) (v : Nat) :
    List (List Nat) × List (List Nat) × List (List Nat) :=
  let pos := mkLit v true
  let neg := mkLit v false
  cs.foldr (fun c acc =>
    let (p, n, r) := acc
    if c.contains pos then
      if c.contains neg then (p, n, r) else (c :: p, n, r)
    else if c.contains neg then (p, c :: n, r)
    else (p, n, c :: r)) ([], [], [])

/-- All non-tautological resolvents `(C \ {pos}) ++ (D \ {¬pos})` for `C ∈ P`, `D ∈ N`. -/
@[expose] def bveResolvents (pos : Nat) (p n : List (List Nat)) : List (List Nat) :=
  (p.flatMap fun c => n.map fun d => resolveOn pos c d).filter fun r => !clauseIsTaut r

/-- Clauses after bounded variable elimination on variable `v`. -/
@[expose] def bveClauses (cs : List (List Nat)) (v : Nat) : List (List Nat) :=
  let (p, n, r) := bvePartition cs v
  bveResolvents (mkLit v true) p n ++ r

/-- Bounded variable elimination on `cnf : CNF Nat` for pivot variable `v`. -/
@[expose] def bve (cnf : CNF Nat) (v : Nat) : CNF Nat :=
  cnfOfClauses (bveClauses (clausesOfCnf cnf) v)

/-! ## 4. SAT witness reconstruction (`BveWitness`, `extendBveStep`, `extendBveStepArray`) -/

/-- Witness entry recorded when eliminating pivot variable `litVar lit` via side `lit`:
stores all clauses containing `lit` (`clauses`) for reconstruction (`kissat_extend`). -/
structure BveWitness where
  lit : Nat
  clauses : List (List Nat)
  deriving Repr, DecidableEq

/-- Choose smaller polarity side (`P` vs `N`) as the saved witness entry. -/
@[expose] def mkBveWitness (v : Nat) (p n : List (List Nat)) : BveWitness :=
  if p.length ≤ n.length then { lit := mkLit v true, clauses := p }
  else { lit := mkLit v false, clauses := n }

/-- Single-step SAT witness extension on assignment `α : Nat → Bool`: sets `w.lit` false
(`litVar w.lit := litSign w.lit`) if that satisfies all `w.clauses`, else flips `w.lit` true. -/
@[expose] def extendBveStep (w : BveWitness) (α : Nat → Bool) : Nat → Bool :=
  let αFalse := substUpdate α (litVar w.lit) (litSign w.lit)
  if w.clauses.all fun c => clauseEvalVal αFalse c then αFalse
  else substUpdate α (litVar w.lit) (!(litSign w.lit))

/-- Single-step SAT witness extension on executable `Array Bool`. -/
@[expose] def extendBveStepArray (w : BveWitness) (σ : Array Bool) : Array Bool :=
  let σFalse := setModelVar σ (litVar w.lit) (litSign w.lit)
  if w.clauses.all fun c => evalClause σFalse c then σFalse
  else setModelVar σ (litVar w.lit) (!(litSign w.lit))

/-! ## 5. Iterated BVE and LIFO reconstruction stack -/

/-- LIFO stack of elimination witness entries (`kissat_extend`). -/
abbrev BveStack := List BveWitness

/-- Single elimination step returning `(bveClauses cs v, witness)`. -/
@[expose] def bveStep (cs : List (List Nat)) (v : Nat) : List (List Nat) × BveWitness :=
  let (p, n, r) := bvePartition cs v
  (bveResolvents (mkLit v true) p n ++ r, mkBveWitness v p n)

/-- Auxiliary fold eliminating `pivots` in order while pushing witness entries onto `stack`. -/
@[expose] def bveElimAux : List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    let res := bveStep cs v
    bveElimAux vs res.1 (res.2 :: st)

/-- Eliminate a list of pivot variables `pivots`, returning `(reducedClauses, witnessStack)`. -/
@[expose] def bveElim (cs : List (List Nat)) (pivots : List Nat) : List (List Nat) × BveStack :=
  bveElimAux pivots cs []

/-- Eliminates `pivots` from `cnf : CNF Nat`, returning `(reducedCnf, witnessStack)`. -/
@[expose] def bveElimCnf (cnf : CNF Nat) (pivots : List Nat) : CNF Nat × BveStack :=
  let res := bveElim (clausesOfCnf cnf) pivots
  (cnfOfClauses res.1, res.2)

/-- Cost-bounded single step: eliminates `v` only if resolvent count does not exceed
`p.length + n.length + bound`. -/
@[expose] def bveBoundedStep (bound : Nat) (cs : List (List Nat)) (v : Nat) :
    List (List Nat) × Option BveWitness :=
  let (p, n, r) := bvePartition cs v
  let res := bveResolvents (mkLit v true) p n
  if res.length ≤ p.length + n.length + bound then (res ++ r, some (mkBveWitness v p n))
  else (cs, none)

@[expose] def bveBoundedElimAux (bound : Nat) :
    List Nat → List (List Nat) → BveStack → List (List Nat) × BveStack
  | [], cs, st => (cs, st)
  | v :: vs, cs, st =>
    match bveBoundedStep bound cs v with
    | (cs', some w) => bveBoundedElimAux bound vs cs' (w :: st)
    | (cs', none) => bveBoundedElimAux bound vs cs' st

/-- Cost-bounded iterated BVE pass over candidate variables `pivots`. -/
@[expose] def bveBoundedElim (bound : Nat) (cs : List (List Nat)) (pivots : List Nat) :
    List (List Nat) × BveStack :=
  bveBoundedElimAux bound pivots cs []

/-- LIFO SAT witness reconstruction on `α : Nat → Bool` (`kissat_extend`). -/
@[expose] def extendBve (stack : BveStack) (α : Nat → Bool) : Nat → Bool :=
  stack.foldl (fun acc w => extendBveStep w acc) α

/-- LIFO SAT witness reconstruction on executable `Array Bool` models. -/
@[expose] def extendBveArray (stack : BveStack) (σ : Array Bool) : Array Bool :=
  stack.foldl (fun acc w => extendBveStepArray w acc) σ

end LeanQbe.T.Examples.Kissat.Ref
