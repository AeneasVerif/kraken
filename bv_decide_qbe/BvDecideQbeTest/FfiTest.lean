module

public import BvDecideQbe.FFI
public import LeanQbe.T.Examples.BvDecideBridge
meta import BvDecideQbe.FFI
meta import LeanQbe.T.Examples.BvDecideBridge

set_option autoImplicit false

public section

namespace BvDecideQbeTest.FfiTest

open Std.Sat
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.BvDecideBridge
open BvDecideQbe

private def strToByteArray (s : String) : ByteArray :=
  s.toUTF8

private def checkModelSatisfies (cnf : CNF Nat) (model : ByteArray) : Bool :=
  cnf.clauses.all fun cl =>
    cl.literals.any fun (v, pol) =>
      if v == 0 || v - 1 >= model.size then false
      else
        let val := model[v - 1]! != 0
        val == pol

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def bv4XorSelfUnsat : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .xor (.var 0 : BVExpr 4)) .eq (.const 0#4)))

private def bv4AddCommUnsat : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .add (.var 1 : BVExpr 4)) .eq
    (.bin (.var 1 : BVExpr 4) .add (.var 0 : BVExpr 4))))

private def bv8DeMorganUnsat : BVLogicalExpr :=
  let x : BVExpr 8 := .var 0
  let y : BVExpr 8 := .var 1
  .not (.literal (.bin (.un .not (.bin x .and y)) .eq
    (.bin (.un .not x) .or (.un .not y))))

private def bv4EqSat : BVLogicalExpr :=
  .literal (.bin (.var 0 : BVExpr 4) .eq (.const 5#4))

private def bv8AddSat : BVLogicalExpr :=
  .literal (.bin (.bin (.var 0 : BVExpr 8) .add (.const 1#8)) .eq (.const 0#8))

private def testDiffBV (name : String) (bv : BVLogicalExpr) (expectUnsat : Bool) : IO Unit := do
  let cnf := (AIG.toCNF bv.bitblast.relabelNat).relabel (· + 1)
  assertTrue s!"{name}: validDimacsB" (validDimacsB cnf)
  let ba := encodeDimacsBA cnf
  let interpRc := solvePlainInterp ba 500000
  let ffiRes := solveDimacs ba 500000
  if expectUnsat then
    assertTrue s!"{name}: interp == 20" (interpRc == 20)
    match ffiRes with
    | .unsat => pure ()
    | other => throw (IO.userError s!"{name}: expected .unsat, got {repr other}")
  else
    assertTrue s!"{name}: interp == 10" (interpRc == 10)
    match ffiRes with
    | .sat model =>
      assertTrue s!"{name}: model satisfies CNF" (checkModelSatisfies cnf model)
    | other => throw (IO.userError s!"{name}: expected .sat, got {repr other}")

def runAll : IO Unit := do
  -- 1. Direct UNSAT CNF
  let unsatDimacs := strToByteArray "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
  match solveDimacs unsatDimacs with
  | .unsat => pure ()
  | other => throw (IO.userError s!"unsatDimacs: expected .unsat, got {repr other}")
  assertTrue "unsatDimacs interp == 20" (solvePlainInterp unsatDimacs 500000 == 20)

  -- 2. Direct SAT CNF + model check
  let satStr := "p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n"
  let satDimacs := strToByteArray satStr
  let parsedSat ← match parseDimacs satDimacs.data.toList with
    | some c => pure c
    | none => throw (IO.userError "failed to parse satDimacs")
  match solveDimacs satDimacs with
  | .sat model =>
    assertTrue "satDimacs model size == 3" (model.size == 3)
    assertTrue "satDimacs model satisfies CNF" (checkModelSatisfies parsedSat model)
  | other => throw (IO.userError s!"satDimacs: expected .sat, got {repr other}")
  assertTrue "satDimacs interp == 10" (solvePlainInterp satDimacs 500000 == 10)

  -- 3. .workTooSmall & doubling retry
  assertTrue "work=1024 returns .workTooSmall"
    (solveDimacsWith unsatDimacs 1024 1024 1000000 == .workTooSmall)
  assertTrue "work=4096 returns .workTooSmall"
    (solveDimacsWith unsatDimacs 4096 4096 1000000 == .workTooSmall)
  assertTrue "work=4096..262144 retry returns .unsat"
    (solveDimacsWith unsatDimacs 4096 (256 * 1024) 1000000 == .unsat)
  assertTrue "work=4096..262144 retry on SAT returns .sat"
    (match solveDimacsWith satDimacs 4096 (256 * 1024) 1000000 with
     | .sat m => checkModelSatisfies parsedSat m
     | _ => false)

  -- 4. .unknown on fuel=1
  assertTrue "fuel=1 returns .unknown"
    (solveDimacsWith unsatDimacs 262144 262144 1 == .unknown)

  -- 5. nvBytesCnf differential check
  let nvBa := encodeDimacsBA nvBytesCnf
  let nvInterp := solvePlainInterp nvBa 500000
  let nvFfi := solveDimacs nvBa 500000
  assertTrue s!"nvBytesCnf differential match (interp={nvInterp})"
    (match nvFfi with
     | .unsat => nvInterp == 20
     | .sat m => nvInterp == 10 && checkModelSatisfies nvBytesCnf m
     | _ => false)

  -- 6. BVLogicalExpr differential checks against BvDecideBridge.solvePlainInterp
  testDiffBV "bv4XorSelfUnsat" bv4XorSelfUnsat true
  testDiffBV "bv4AddCommUnsat" bv4AddCommUnsat true
  testDiffBV "bv8DeMorganUnsat" bv8DeMorganUnsat true
  testDiffBV "bv4EqSat" bv4EqSat false
  testDiffBV "bv8AddSat" bv8AddSat false

  IO.println "FfiTest: ALL PASSED (UNSAT, SAT+model, workTooSmall+retry, fuel=1 unknown, 6 differential checks)"

#eval runAll

end BvDecideQbeTest.FfiTest

def main : IO Unit := BvDecideQbeTest.FfiTest.runAll
