module

import LeanQbe.T.Examples.BvDecideBridge
meta import LeanQbe.T.Examples.BvDecideBridge

/-!
# Tests and Axiom Audit for `BvDecideBridge` (`M1a`)

1. `#guard` tests on `validDimacsB` and `encodeDimacsBA` round-trip.
2. `#guard` tests exercising `verifyBVExprWith solvePlainInterp` on concrete UNSAT
   `BVLogicalExpr` goals (returning `true`) and SAT `BVLogicalExpr` goals (returning `false`).
3. Single-line `#print axioms` audit on `unsat_of_verifyBVExprWith`,
   `solvePlainInterp_sound`, and `unsat_of_verifyBVExprPlainInterp` (`<= std3`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BvDecideBridgeTest

open Std.Sat
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.BvDecideBridge

/-! ## 1. `validDimacsB` and `encodeDimacsBA` checks -/

private def badZeroVarCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(0, true)])

#guard validDimacsB nvBytesCnf == true
#guard validDimacsB (CNF.empty : CNF Nat) == true
#guard validDimacsB badZeroVarCnf == false
#guard (encodeDimacsBA nvBytesCnf).data.toList == encodeDimacs nvBytesCnf
#guard ((parseDimacs (encodeDimacsBA nvBytesCnf).data.toList).map
  (fun c => c.clauses.toList.map CNF.Clause.literals)) ==
  some (nvBytesCnf.clauses.toList.map CNF.Clause.literals)

/-! ## 2. Concrete UNSAT and SAT `BVLogicalExpr` checks via `solvePlainInterp` -/

/-- Negation of `4`-bit `x ^^^ x == 0#4` (UNSAT). -/
private def bv4XorSelfUnsat : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .xor (.var 0 : BVExpr 4)) .eq (.const 0#4)))

/-- Negation of `4`-bit `x + y == y + x` (UNSAT). -/
private def bv4AddCommUnsat : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .add (.var 1 : BVExpr 4)) .eq
    (.bin (.var 1 : BVExpr 4) .add (.var 0 : BVExpr 4))))

/-- Negation of `8`-bit De Morgan `~~~(x &&& y) == (~~~x ||| ~~~y)` (UNSAT). -/
private def bv8DeMorganUnsat : BVLogicalExpr :=
  let x : BVExpr 8 := .var 0
  let y : BVExpr 8 := .var 1
  .not (.literal (.bin (.un .not (.bin x .and y)) .eq
    (.bin (.un .not x) .or (.un .not y))))

/-- Negation of `8`-bit `x ^^^ y == y ^^^ x` (UNSAT). -/
private def bv8XorCommUnsat : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 8) .xor (.var 1 : BVExpr 8)) .eq
    (.bin (.var 1 : BVExpr 8) .xor (.var 0 : BVExpr 8))))

/-- Satisfiable `4`-bit predicate `x == 5#4` (`verifyBVExprWith` returns `false`). -/
private def bv4EqSat : BVLogicalExpr :=
  .literal (.bin (.var 0 : BVExpr 4) .eq (.const 5#4))

/-- Satisfiable `8`-bit predicate `x + 1#8 == 0#8` (`verifyBVExprWith` returns `false`). -/
private def bv8AddSat : BVLogicalExpr :=
  .literal (.bin (.bin (.var 0 : BVExpr 8) .add (.const 1#8)) .eq (.const 0#8))

#guard verifyBVExprWith solvePlainInterp bv4XorSelfUnsat 500000 == true
#guard verifyBVExprWith solvePlainInterp bv4AddCommUnsat 500000 == true
#guard verifyBVExprWith solvePlainInterp bv8DeMorganUnsat 500000 == true
#guard verifyBVExprWith solvePlainInterp bv8XorCommUnsat 500000 == true
#guard verifyBVExprWith solvePlainInterp bv4EqSat 500000 == false
#guard verifyBVExprWith solvePlainInterp bv8AddSat 500000 == false

/-! ## 3. Single-line `#print axioms` audit (`<= std3`) -/

#print axioms LeanQbe.T.Examples.BvDecideBridge.unsat_of_verifyBVExprWith
#print axioms LeanQbe.T.Examples.BvDecideBridge.solvePlainInterp_sound
#print axioms LeanQbe.T.Examples.BvDecideBridge.unsat_of_verifyBVExprPlainInterp

end LeanQbeTest.T.BvDecideBridgeTest
