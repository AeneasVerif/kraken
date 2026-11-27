module

public import BvDecideQbe.FFI
public import BvDecideQbe.Encode
public import BvDecideQbe.Counterexample
public import LeanQbe.T.Examples.BvDecideBridge
meta import BvDecideQbe.FFI
meta import BvDecideQbe.Encode
meta import BvDecideQbe.Counterexample
meta import LeanQbe.T.Examples.BvDecideBridge

set_option autoImplicit false

public section

namespace BvDecideQbeTest.FfiTest

open Std.Sat
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.BvDecideBridge
open BvDecideQbe

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def bvTrivUnsat : BVLogicalExpr := .const false
private def bvTrivSat : BVLogicalExpr := .const true

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

private def bv16AddCommUnsat : BVLogicalExpr :=
  let x : BVExpr 16 := .var 0
  let y : BVExpr 16 := .var 1
  .not (.literal (.bin (.bin x .add y) .eq (.bin y .add x)))

private def bv8DistUnsat : BVLogicalExpr :=
  let x : BVExpr 8 := .var 0
  let y : BVExpr 8 := .var 1
  .not (.literal (.bin (.bin (.bin x .and y) .or (.bin x .and (.un .not y))) .eq x))

private def bv4EqSat : BVLogicalExpr :=
  .literal (.bin (.var 0 : BVExpr 4) .eq (.const 5#4))

private def bv8AddSat : BVLogicalExpr :=
  .literal (.bin (.bin (.var 0 : BVExpr 8) .add (.const 1#8)) .eq (.const 0#8))

private def bv8LtSat : BVLogicalExpr :=
  .gate .and (.literal (.bin (.var 0 : BVExpr 8) .ult (.var 1 : BVExpr 8)))
    (.literal (.bin (.var 1 : BVExpr 8) .eq (.const 42#8)))

private def testDiffBV (name : String) (bv : BVLogicalExpr) (expectUnsat : Bool) : IO Unit := do
  let some enc := BvDecideQbe.encode bv
    | throw (IO.userError s!"{name}: encode failed")
  let cnf := (AIG.toCNF bv.bitblast.relabelNat).relabel (· + 1)
  assertTrue s!"{name}: validDimacsB" (validDimacsB cnf)
  let ba := encodeDimacsBA cnf
  let interpRc := solvePlainInterp ba 500000
  let ffiRes ← solveBVProg enc.words (estimateWorkSize enc.stats) defaultMaxWorkBytes 500000
  if expectUnsat then
    assertTrue s!"{name}: interp == 20" (interpRc == 20)
    match ffiRes with
    | .unsat witness =>
      assertTrue s!"{name}: witness.words == enc.words" (witness.words == enc.words)
    | .sat _ => throw (IO.userError s!"{name}: expected .unsat, got .sat")
    | .unknown => throw (IO.userError s!"{name}: expected .unsat, got .unknown")
    | .workTooSmall => throw (IO.userError s!"{name}: expected .unsat, got .workTooSmall")
    | .timeout => throw (IO.userError s!"{name}: expected .unsat, got .timeout")
  else
    assertTrue s!"{name}: interp == 10" (interpRc == 10)
    match ffiRes with
    | .sat model =>
      assertTrue s!"{name}: model passes evalEfficient" (decodeAndValidate bv enc model).isSome
    | .unsat _ => throw (IO.userError s!"{name}: expected .sat, got .unsat")
    | .unknown => throw (IO.userError s!"{name}: expected .sat, got .unknown")
    | .workTooSmall => throw (IO.userError s!"{name}: expected .sat, got .workTooSmall")
    | .timeout => throw (IO.userError s!"{name}: expected .sat, got .timeout")

def runAll : IO Unit := do
  -- 1. Trivial UNSAT & Trivial SAT (BV_TRIVIAL_SAT_MAGIC -> empty ByteArray)
  let some encTrivU := BvDecideQbe.encode bvTrivUnsat
    | throw (IO.userError "encode bvTrivUnsat failed")
  match ← solveBVProg encTrivU.words with
  | .unsat w => assertTrue "trivUnsat words" (w.words == encTrivU.words)
  | _ => throw (IO.userError "bvTrivUnsat expected .unsat")

  let some encTrivS := BvDecideQbe.encode bvTrivSat
    | throw (IO.userError "encode bvTrivSat failed")
  match ← solveBVProg encTrivS.words with
  | .sat m =>
    assertTrue "trivSat empty model" m.isEmpty
    assertTrue "trivSat evalEfficient" (decodeAndValidate bvTrivSat encTrivS m).isSome
  | _ => throw (IO.userError "bvTrivSat expected .sat")

  -- 2. .workTooSmall & 2x doubling retry via solveBVProgWithStats
  let some enc8 := BvDecideQbe.encode bv8DeMorganUnsat
    | throw (IO.userError "encode bv8DeMorganUnsat failed")
  let some enc8Sat := BvDecideQbe.encode bv8AddSat
    | throw (IO.userError "encode bv8AddSat failed")
  let some encDist := BvDecideQbe.encode bv8DistUnsat
    | throw (IO.userError "encode bv8DistUnsat failed")

  let r1024 ← solveBVProgWithStats encDist.words 1024 1024 1000000
  assertTrue "work=1024 returns .workTooSmall" (r1024.result matches .workTooSmall)
  let r4096 ← solveBVProgWithStats encDist.words 4096 4096 1000000
  assertTrue "work=4096 returns .workTooSmall" (r4096.result matches .workTooSmall)
  let rRetryU ← solveBVProgWithStats enc8.words 1024 (2 * 1024 * 1024) 1000000
  assertTrue "work=1024..2MiB retry returns .unsat with attempts > 1"
    ((rRetryU.result matches .unsat _) && rRetryU.attempts > 1)
  let rRetryS ← solveBVProgWithStats enc8Sat.words 1024 (2 * 1024 * 1024) 1000000
  match rRetryS.result with
  | .sat m =>
    assertTrue "retry SAT attempts > 1" (rRetryS.attempts > 1)
    assertTrue "retry SAT evalEfficient" (decodeAndValidate bv8AddSat enc8Sat m).isSome
  | _ => throw (IO.userError "work=1024..2MiB retry on SAT failed")

  -- 3. .timeout on fuel=0 and fuel=1 (NO 32x retry storm -> attempts == 1)
  let rFuel0 ← solveBVProgWithStats encDist.words (2 * 1024 * 1024) (2 * 1024 * 1024) 0
  assertTrue s!"fuel=0 returns .timeout in 1 attempt (attempts={rFuel0.attempts})"
    ((rFuel0.result matches .timeout) && rFuel0.attempts == 1)
  let rFuel1 ← solveBVProgWithStats encDist.words (2 * 1024 * 1024) (2 * 1024 * 1024) 1
  assertTrue s!"fuel=1 returns .timeout in 1 attempt (attempts={rFuel1.attempts})"
    ((rFuel1.result matches .timeout) && rFuel1.attempts == 1)

  -- 4. Invalid BVP1 returns .unknown in 1 attempt (NO 32x retry storm)
  let rBadMagic ← solveBVProgWithStats [0xDEADBEEF] 262144 262144 1000000
  assertTrue "bad magic returns .unknown in 1 attempt"
    ((rBadMagic.result matches .unknown) && rBadMagic.attempts == 1)
  let rBadOp ← solveBVProgWithStats [bvpMagic, bvpVersion, 0, 1, 0, 0, 0, 0, 999, 1, 0, 0, 0]
    262144 262144 1000000
  assertTrue "bad opcode returns .unknown in 1 attempt"
    ((rBadOp.result matches .unknown) && rBadOp.attempts == 1)

  -- 5. BVLogicalExpr differential checks against BvDecideBridge.solvePlainInterp
  testDiffBV "bv4XorSelfUnsat" bv4XorSelfUnsat true
  testDiffBV "bv4AddCommUnsat" bv4AddCommUnsat true
  testDiffBV "bv8DeMorganUnsat" bv8DeMorganUnsat true
  testDiffBV "bv16AddCommUnsat" bv16AddCommUnsat true
  testDiffBV "bv4EqSat" bv4EqSat false
  testDiffBV "bv8AddSat" bv8AddSat false
  testDiffBV "bv8LtSat" bv8LtSat false

  IO.println
    "FfiTest: ALL PASSED (bv_solve_bytes, triv SAT/UNSAT, retry, fuel=1, bad BVP1, 7 diff)"

#eval runAll

end BvDecideQbeTest.FfiTest

def main : IO Unit := BvDecideQbeTest.FfiTest.runAll
