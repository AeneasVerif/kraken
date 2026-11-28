/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Vivify
public import LeanQbe.T.Examples.Kissat.Ref.Eliminate
public import LeanQbe.T.Examples.Kissat.Ref.Factor
public import LeanQbe.T.Examples.Kissat.Ref.Collect
public import LeanQbe.T.Examples.Kissat.Ref.Cdcl

/-!
# Pure Lean Layer-A UNSAT Soundness Theory for Feature-Complete Kissat (Part 1)

Pure Lean (`Std.Sat.CNF Nat`, zero `Kraken.Mem` or `Kraken.Separation` imports) UNSAT-only
compositional soundness framework for Stage 4 (`D-Full`) feature-complete Kissat:

1. **`VarsBounded`, `ExtUnsatSound`, & DIMACS Initialization**:
   `ExtUnsatSound F0 mv_cur F_cur` (`VarsBounded mv_cur F_cur ∧ ((cnfOfClauses F_cur).Unsat →
   F0.Unsat)`), initialized from 0-based or 1-based DIMACS formulas (including parametric
   `parseDimacs` bridges), plus empty-clause & CDCL refutation.
2. **Arbitrary Clause Deletion / Filtering (`List.Sublist` / `deleteIdx` / `erase` / `filter`)**:
   one-line UNSAT soundness with zero SAT model-reconstruction side conditions covering
   `reduce`, satisfied-clause GC, forward subsumption deletion, BIG transitive reduction
   (`transitive.c`), BCE deletion, pure-literal deletion, and BVE/Gate-BVE pivot deletion.
3. **Entailed Clause Addition & Inprocessing Rules**:
   unified `EntailsClause` addition & replacement covering 1UIP, OTFS, eager subsumption, SSR,
   vivification, failed-literal probing, **Hyper-Binary Resolution (`HBR`)**, **Gate Congruence
   Closure (`congruence.c`: Equiv / AND / ITE / XOR)**, **Bounded SAT Sweeping (`sweep.c`)**,
   and **BVE / Gate-BVE** resolvents.
4. **BIG SCC Substitution (`substitute.c`) & Fresh-Variable BVA (`factor.c`)**:
   `substMapClauses` simultaneous SCC substitution, `BinReach` SCC contradiction refutation, and
   `mv_cur ↦ mv_cur + 1` fresh-variable BVA factoring.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Variable bounds, `ExtUnsatSound`, and DIMACS initialization -/

/-- Every literal occurring in any clause of `F` has variable index `< mv`. -/
@[expose] def VarsBounded (mv : Nat) (F : List (List Nat)) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, litVar l < mv

/-- Executable Boolean checker for `VarsBounded`. -/
@[expose] def varsBoundedBool (mv : Nat) (F : List (List Nat)) : Bool :=
  F.all fun c => c.all fun l => decide (litVar l < mv)

/-- 0-based `CNF Nat` variable bound: every variable occurring in `cnf` is `< mv`. -/
@[expose] def DimacsVarsBounded0 (mv : Nat) (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, lit.1 < mv

/-- 1-based DIMACS `CNF Nat` variable bound (`1 ≤ v ≤ mv`). -/
@[expose] def DimacsVarsBounded (mv : Nat) (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
abbrev shiftDimacsClause := shiftDownClause

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
abbrev shiftDimacsCnf := shiftDownCnf

/-- Pure Layer-A UNSAT soundness & variable-bound invariant for Stage 4 feature-complete
inprocessing: all literals in `F_cur` have variable `< mv_cur`, and unsatisfiability of `F_cur`
implies unsatisfiability of the original parsed formula `F0`. -/
@[expose] def ExtUnsatSound (F0 : CNF Nat) (mv_cur : Nat) (F_cur : List (List Nat)) : Prop :=
  VarsBounded mv_cur F_cur ∧ ((cnfOfClauses F_cur).Unsat → F0.Unsat)

/-! ### 3.1 Hyper-Binary Resolution (`HBR`) -/

/-- Executable HBR checker: propagates decision `d` at level `1` over `F_cur` and verifies
that `u ∈ C` and every other literal `x ∈ C \ {u}` is falsified on the resulting trail. -/
@[expose]
def hbrCheck (fuel : Nat) (F_cur : List (List Nat)) (d : Nat) (C : List Nat) (u : Nat) : Bool :=
  match propagateAll fuel (initState (cnfOfClauses F_cur)) with
  | .ok s0 =>
    match litStatus s0.trail d with
    | none =>
      match propagateAll fuel (decideLit s0 d) with
      | .ok s1 => C.contains u && C.all (fun x => x == u || trailHasLit s1.trail (litNeg x))
      | .conflict _ _ => true
      | .outOfFuel _ => false
    | some false => true
    | some true => false
  | .conflict _ _ => true
  | .outOfFuel _ => false

/-! ### 3.2 Gate Congruence Closure (`congruence.c`: Equiv / AND / ITE / XOR) -/

/-- Literal equivalence entailed by `f`: `f ⊨ [¬a, b]` and `f ⊨ [a, ¬b]`. -/
@[expose] def LitEquiv (f : CNF Nat) (a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [litNeg a, b]) ∧ f.EntailsClause (cnfClause [a, litNeg b])

/-- Equivalence gate definition `g ↔ x` entailed by `f`. -/
@[expose] def EquivGateDef (f : CNF Nat) (g x : Nat) : Prop :=
  LitEquiv f g x

/-- Multi-input AND gate definition `g ↔ (x₁ ∧ ... ∧ xₖ)` entailed by `f`. -/
@[expose] def AndGateDef (f : CNF Nat) (g : Nat) (xs : List Nat) : Prop :=
  f.EntailsClause (cnfClause (g :: xs.map litNeg)) ∧
  ∀ x ∈ xs, f.EntailsClause (cnfClause [litNeg g, x])

/-- ITE gate definition `g ↔ (if c then t else e)` entailed by `f`. -/
@[expose] def IteGateDef (f : CNF Nat) (g c t e : Nat) : Prop :=
  f.EntailsClause (cnfClause [g, litNeg c, litNeg t]) ∧
  f.EntailsClause (cnfClause [g, c, litNeg e]) ∧
  f.EntailsClause (cnfClause [litNeg g, litNeg c, t]) ∧
  f.EntailsClause (cnfClause [litNeg g, c, e])

/-- Binary XOR gate definition `g ↔ (a ⊕ b)` entailed by `f`. -/
@[expose] def XorGateDef (f : CNF Nat) (g a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [g, litNeg a, b]) ∧
  f.EntailsClause (cnfClause [g, a, litNeg b]) ∧
  f.EntailsClause (cnfClause [litNeg g, a, b]) ∧
  f.EntailsClause (cnfClause [litNeg g, litNeg a, litNeg b])

/-! ### 3.3 Bounded SAT Sweeping (`sweep.c`) -/

/-- Executable bounded SAT-sweeping checker for binary implication `a → b` over local `env`. -/
@[expose] def sweepCheckImplies (fuel : Nat) (env : List (List Nat)) (a b : Nat) : Bool :=
  cdclSolve fuel (cnfOfClauses ([a] :: [litNeg b] :: env)) == .unsat

/-- Executable bounded SAT-sweeping checker for backbone refutation `a ⊢ ⊥` over `env`. -/
@[expose] def sweepCheckBackbone (fuel : Nat) (env : List (List Nat)) (a : Nat) : Bool :=
  cdclSolve fuel (cnfOfClauses ([a] :: env)) == .unsat

end LeanQbe.T.Examples.Kissat.Ref
