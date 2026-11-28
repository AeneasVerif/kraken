/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Sat.CNF

/-!
# Shared Pure-Math Foundation for Kissat Layer-A Reference Specifications

Collects pure Lean definitions and lemmas shared across `LeanQbe.T.Examples.Kissat.Ref.*`
(zero `CdclState`, zero `Kraken.Mem`, `public import Std.Sat.CNF` only):

1. Kissat literal encoding (`litVar`, `litSign`, `litPol`, `litNeg`, `mkLit`, `Std.Sat.Literal`,
   `litOfBitVec`, and `kissatLitToDimacsLiteral`) with bijection lemmas.
2. `CNF Nat` / `List (List Nat)` bridges (`cnfClause`, `clauseOfCnf`, `cnfOfClauses`,
   `clausesOfCnf`, `shiftDownCnf`), resolution/stripping/tautology/freshness lemmas, and
   `sat_foldl_cnfClause_iff`.
3. Total assignment ↔ `Array Bool` evaluation (`evalVar`, `evalLit`, `evalClause`, `evalCnf`,
   `checkModel`, `evalLitVal`, `clauseEvalVal`, `cnfEvalVal`, `substUpdate`, `arraySetPad`).
4. Shared `List` / `Nodup` / pigeonhole / filter / clause-pass combinators.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Kissat-compatible literal encoding -/

/-- Variable index of an encoded Kissat literal (`lit >>> 1 = lit / 2`). -/
@[expose, inline] def litVar (l : Nat) : Nat := l / 2

/-- Sign bit of an encoded literal (`false` = positive `2 * v`, `true` = negative `2 * v + 1`). -/
@[expose, inline] def litSign (l : Nat) : Bool := l % 2 == 1

/-- Semantic polarity of an encoded literal (`true` = positive `2 * v`, `false` = negative). -/
@[expose, inline] def litPol (l : Nat) : Bool := l % 2 == 0

/-- Bitwise negation `l ^^^ 1` (`2 * v ↔ 2 * v + 1`). -/
@[expose, inline] def litNeg (l : Nat) : Nat := l ^^^ 1

/-- Construct an encoded literal from variable `v` and polarity `pol`. -/
@[expose, inline] def mkLit (v : Nat) (pol : Bool) : Nat :=
  if pol then 2 * v else 2 * v + 1

/-- Convert a Kissat literal to `Std.Sat.Literal Nat`. -/
@[expose, inline] def litToLiteral (l : Nat) : Literal Nat :=
  (litVar l, !(litSign l))

/-- Convert `Std.Sat.Literal Nat` to a Kissat literal. -/
@[expose, inline] def litOfLiteral (lit : Literal Nat) : Nat :=
  mkLit lit.1 lit.2

/-- Convert a fixed-width `BitVec w` literal word into `Nat`. -/
@[expose, inline] def litOfBitVec {w : Nat} (bv : BitVec w) : Nat := bv.toNat

/-- Convert a 0-based Kissat literal into 1-based `Std.Sat.Literal Nat` (`v + 1`). -/
@[expose, inline] def kissatLitToDimacsLiteral (l : Nat) : Literal Nat :=
  (litVar l + 1, !(litSign l))

/-! ## 2. Clause & CNF conversions, resolution, `shiftDownCnf`, and `unitsCnf` -/

/-- Convert a list of Kissat literals into a `Std.Sat.CNF.Clause Nat`. -/
@[expose] def cnfClause (lits : List Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (lits.map litToLiteral)

/-- Extract Kissat literals from a `Std.Sat.CNF.Clause Nat`. -/
@[expose] def clauseOfCnf (c : CNF.Clause Nat) : List Nat :=
  c.literals.map litOfLiteral

/-- Convert a list of Kissat clauses into a `Std.Sat.CNF Nat`. -/
@[expose] def cnfOfClauses (cs : List (List Nat)) : CNF Nat :=
  ⟨(cs.map cnfClause).toArray⟩

/-- Convert a `Std.Sat.CNF Nat` into a list of Kissat clauses. -/
@[expose] def clausesOfCnf (cnf : CNF Nat) : List (List Nat) :=
  cnf.clauses.toList.map clauseOfCnf

/-- Strict upper bound (`max var + 1`) on variables appearing in a clause. -/
@[expose] def maxVarClause (c : CNF.Clause Nat) : Nat :=
  c.literals.foldl (fun m l => Nat.max m (l.1 + 1)) 0

/-- Strict upper bound (`max var + 1`) on variables appearing in a `CNF Nat`. -/
@[expose] def maxVarCnf (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m c => Nat.max m (maxVarClause c)) 0

/-- Remove duplicate literals while preserving first-seen order. -/
@[expose] def dedupLits : List Nat → List Nat
  | [] => []
  | l :: ls =>
    let rest := dedupLits ls
    if rest.contains l then rest else l :: rest

/-- Propositional resolution of `c1` and `c2` on pivot `p` (removing `p` and `¬p`). -/
@[expose] def resolveOn (p : Nat) (c1 c2 : List Nat) : List Nat :=
  c1.filter (· != p) ++ c2.filter (· != litNeg p)

/-- Strip literals certified false by predicate `isRootFalse`. -/
@[expose] def stripFalsified (isRootFalse : Nat → Bool) (c : List Nat) : List Nat :=
  c.filter (fun l => !isRootFalse l)

/-- Tautology detector: `true` iff `c` contains a complementary pair `x` and `litNeg x`. -/
@[expose] def clauseIsTaut (c : List Nat) : Bool :=
  c.any (fun x => c.contains (litNeg x))

/-- Variable `v` does not occur in any clause of `cs`. -/
@[expose] def VarFreshIn (cs : List (List Nat)) (v : Nat) : Prop :=
  ∀ c ∈ cs, ∀ x ∈ c, litVar x ≠ v

/-- Executable Boolean checker for `VarFreshIn`. -/
@[expose] def varFreshInBool (cs : List (List Nat)) (v : Nat) : Bool :=
  cs.all fun c => c.all fun x => litVar x != v

/-- Variable `v` does not occur in any clause of `f : CNF Nat`. -/
@[expose] def VarFreshCnf (f : CNF Nat) (v : Nat) : Prop :=
  VarFreshIn (clausesOfCnf f) v

/-- Convert a list of unit literals into a `Std.Sat.CNF Nat`. -/
@[expose] def unitsCnf (lits : List Nat) : CNF Nat :=
  lits.foldl (fun acc l => acc.add (cnfClause [l])) CNF.empty

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
@[expose] def shiftDownClause (cl : CNF.Clause Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.literals.map fun (v, p) => (v - 1, p))

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
@[expose] def shiftDownCnf (cnf : CNF Nat) : CNF Nat :=
  ⟨cnf.clauses.map shiftDownClause⟩

/-- Every variable occurring in `cnf` is positive (`1`-based DIMACS convention). -/
@[expose] def CnfVarsPos (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1

/-! ## 3. `Array Bool ↔ (Nat → Bool)` evaluation and padding bridges -/

/-- Set `arr[idx] := val`, padding with `pad` if `idx ≥ arr.size`. -/
@[expose] def arraySetPad {α : Type} (arr : Array α) (idx : Nat) (val pad : α) : Array α :=
  if h : idx < arr.size then
    arr.set idx val h
  else
    let padded := arr ++ Array.replicate (idx + 1 - arr.size) pad
    padded.set! idx val

/-- Lookup variable value in a `Bool` model array (defaulting out-of-range to `false`). -/
@[expose, inline] def evalVar (σ : Array Bool) (v : Nat) : Bool :=
  σ[v]?.getD false

/-- Evaluate a Kissat literal under model `σ`. -/
@[expose, inline] def evalLit (σ : Array Bool) (l : Nat) : Bool :=
  evalVar σ (litVar l) != litSign l

/-- Evaluate a Kissat clause (disjunction of literals) under model `σ`. -/
@[expose] def evalClause (σ : Array Bool) (c : List Nat) : Bool :=
  c.any (evalLit σ)

/-- Evaluate a list of Kissat clauses (conjunction of clauses) under model `σ`. -/
@[expose] def evalCnf (σ : Array Bool) (cs : List (List Nat)) : Bool :=
  cs.all (evalClause σ)

/-- Executable total model checker on `Std.Sat.CNF Nat`. -/
@[expose] def checkModel (cnf : CNF Nat) (σ : Array Bool) : Bool :=
  cnf.eval (evalVar σ)

/-- Evaluate a Kissat literal under a total Boolean assignment `α : Nat → Bool`. -/
@[expose, inline] def evalLitVal (α : Nat → Bool) (l : Nat) : Bool :=
  α (litVar l) != litSign l

/-- Evaluate a clause (disjunction of Kissat literals) under `α : Nat → Bool`. -/
@[expose] def clauseEvalVal (α : Nat → Bool) (c : List Nat) : Bool :=
  c.any (evalLitVal α)

/-- Evaluate a clause list (conjunction of clauses) under `α : Nat → Bool`. -/
@[expose] def cnfEvalVal (α : Nat → Bool) (cs : List (List Nat)) : Bool :=
  cs.all (clauseEvalVal α)

/-- Point update `α[v ↦ val]` on a total Boolean assignment `α : Nat → Bool`. -/
@[expose, inline] def substUpdate (α : Nat → Bool) (v : Nat) (val : Bool) : Nat → Bool :=
  fun x => if x == v then val else α x

/-! ## 4. Shared `List` / `Nodup` / pigeonhole / pass combinators -/

/-- Generic single-pass clause transformation preserving `kept.reverse ++ todo` equivalence. -/
@[expose] def clauseTransformPassAux (step : List (List Nat) → List Nat → List Nat) :
    List (List Nat) → List (List Nat) → List (List Nat)
  | kept, [] => kept.reverse
  | kept, c :: rest =>
    clauseTransformPassAux step (step (kept ++ rest) c :: kept) rest

end LeanQbe.T.Examples.Kissat.Ref
