module

public import BvDecideQbe.Encode
public import BvDecideQbe.Counterexample
public import BvDecideQbe.FFI
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
meta import BvDecideQbe.Encode
meta import BvDecideQbe.Counterexample
meta import BvDecideQbe.FFI
meta import LeanQbe.T.Examples.Bitblast.Ref.BVProg

/-!
# Round-Trip, Workspace Sizing, and Counterexample Tests (`S3a`)

Verifies:
1. `BVProg.parseWords (encode expr).words == some expr` and `BVProg.parse bytes == some expr`
   across all 25 `M0` AST shapes, all 32 `BVP1` opcodes (`0..31`), wide 256-bit constants,
   `w = 0`, sparse/repeated variables, and shared DAGs (`120` / `200` nodes).
2. `estimateWorkSize` bounds (`[256 KiB, 512 MiB]`), power-of-two rounding, and monotonicity.
3. `Counterexample` direct `model[atomBase[k] + j]` decoding, sparse `Assignment` lookup,
   `BVLogicalExpr.evalEfficient` acceptance/rejection, and `reconstructValidatedCounterExample`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbeTest.EncodeCexTest

open Lean
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.Bitblast.Ref
open BvDecideQbe

private def roundTripOk (e : BVLogicalExpr) : Bool :=
  match BvDecideQbe.encode e, BVProg.encode e with
  | some p, some refWs =>
    let wordsMatch := p.words == refWs
    let bytesMatch := p.bytes.data.toList == BVProg.wordsToBytesLE p.words
    let atomOk :=
      p.atomBase.size == p.varTable.size &&
      (if p.varTable.isEmpty then p.stats.totalAtomBits == 0
       else
         let rec checkBase (k acc : Nat) : Bool :=
           if h : k < p.varTable.size then
             if h2 : k < p.atomBase.size then
               p.atomBase[k] == acc && checkBase (k + 1) (acc + p.varTable[k].2)
             else false
           else acc - 1 == p.stats.totalAtomBits
         checkBase 0 1)
    match BVProg.parseWords p.words, BVProg.parse p.bytes.data.toList with
    | some e1, some e2 =>
      wordsMatch && bytesMatch && atomOk &&
      BVProg.logicalExprEq e1 e && BVProg.logicalExprEq e2 e
    | _, _ => false
  | _, _ => false

/-! ## 1. All 25 `M0` AST Shapes + `w = 0` + All 32 Opcodes + Shared DAGs -/

private def m0_a1 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  let z : BVExpr 32 := .var 2
  .not (.literal (.bin (.bin (.bin (.bin x .and y) .or (.bin x .and (.un .not y))) .xor z)
    .eq (.bin x .xor z)))

private def m0_a2 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  .not (.literal (.bin (.bin (.bin x .xor y) .add
    (.shiftLeft (.bin x .and y) (.const 1#32))) .eq (.bin x .add y)))

private def m0_a3 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  .not (.literal (.bin (.bin (.bin x .or y) .add (.un .not (.bin x .and y))) .eq
    (.bin x .xor y)))

private def m0_a4 : BVLogicalExpr :=
  let x : BVExpr 16 := .var 0
  .not (.literal (.bin
    (.bin (.bin (.shiftLeft x (.const 5#16)) .or (.shiftRight x (.const 11#16))) .add (.const 1#16))
    .eq (.bin (.un (.rotateLeft 5) x) .add (.const 1#16))))

private def m0_a5 : BVLogicalExpr :=
  let x : BVExpr 16 := .var 0
  let m : BVExpr 16 := .un (.arithShiftRightConst 15) x
  .ite (.literal (.getLsbD x 15))
    (.literal (.bin (.bin x .xor m) .eq (.bin (.un .not x) .add (.const 1#16))))
    (.literal (.bin (.bin x .xor m) .eq x))

private def m0_b1 : BVLogicalExpr :=
  let x : BVExpr 64 := .var 0
  let y : BVExpr 64 := .var 1
  .not (.literal (.bin (.bin (.bin x .xor y) .add
    (.shiftLeft (.bin x .and y) (.const 1#64))) .eq (.bin x .add y)))

private def m0_b2 : BVLogicalExpr :=
  let x : BVExpr 128 := .var 0
  let y : BVExpr 128 := .var 1
  let zx : BVExpr 129 := .append (.const 0#1) x (by decide)
  let zy : BVExpr 129 := .append (.const 0#1) y (by decide)
  .not (.literal (.bin (.shiftRight (.bin zx .add zy) (.const 1#129)) .eq
    (.append (.const 0#1) (.bin (.bin x .and y) .add
      (.shiftRight (.bin x .xor y) (.const 1#128))) (by decide))))

private def m0_b3 : BVLogicalExpr :=
  let a : BVExpr 128 := .var 0
  let b : BVExpr 128 := .var 1
  let c : BVExpr 128 := .var 2
  .not (.literal (.bin (.bin (.bin (.bin a .xor b) .xor c) .add
    (.shiftLeft (.bin (.bin a .and b) .or (.bin (.bin b .and c) .or (.bin a .and c)))
      (.const 1#128))) .eq (.bin (.bin a .add b) .add c)))

private def m0_b4 : BVLogicalExpr :=
  let a : BVExpr 256 := .var 0
  let b : BVExpr 256 := .var 1
  let c : BVExpr 256 := .var 2
  .not (.literal (.bin (.bin (.bin (.bin a .xor b) .xor c) .add
    (.shiftLeft (.bin (.bin a .and b) .or (.bin (.bin b .and c) .or (.bin a .and c)))
      (.const 1#256))) .eq (.bin (.bin a .add b) .add c)))

private def m0_b5 : BVLogicalExpr :=
  let a : BVExpr 256 := .var 0
  let b : BVExpr 256 := .var 1
  let c : BVExpr 256 := .var 2
  .gate .and (.literal (.bin a .ult b))
    (.gate .or (.literal (.bin b .ult c)) (.literal (.bin a .ult c)))

private def m0_b6 : BVLogicalExpr :=
  let x : BVExpr 256 := .var 0
  let s : BVExpr 256 := .var 1
  .gate .and (.not (.literal (.bin s .eq (.const 0#256))))
    (.gate .and (.literal (.bin s .ult (.const 256#256)))
      (.literal (.getLsbD (.shiftLeft x s) 0)))

private def m0_c1 : BVLogicalExpr :=
  let x : BVExpr 7 := .var 0
  let y : BVExpr 7 := .var 1
  .not (.literal (.bin (.bin x .mul y) .eq (.bin y .mul x)))

private def m0_c2 : BVLogicalExpr :=
  let x : BVExpr 8 := .var 0
  let y : BVExpr 8 := .var 1
  .gate .and (.not (.literal (.bin y .eq (.const 0#8))))
    (.not (.literal (.bin (.bin (.bin (.bin x .udiv y) .mul y) .add (.bin x .umod y)) .eq x)))

private def m0_c3 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  .gate .and (.not (.literal (.bin x .eq (.const 0#32))))
    (.not (.literal (.getLsbD (.shiftLeft x (.un .clz x)) 31)))

private def m0_c4 : BVLogicalExpr :=
  let x : BVExpr 64 := .var 0
  .gate .and (.not (.literal (.bin x .eq (.const 0#64))))
    (.not (.literal (.getLsbD (.shiftLeft x (.un .clz x)) 63)))

private def m0_c5 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  .not (.literal (.bin (.bin (.un .cpop x) .add (.un .cpop (.un .not x))) .eq (.const 32#32)))

private def m0_d1 : BVLogicalExpr :=
  let x : BVExpr 8 := .var 10
  let y : BVExpr 8 := .var 20
  .not (.literal (.bin (.bin x .mul y) .eq (.bin y .mul x)))

private def m0_d2 : BVLogicalExpr :=
  let x : BVExpr 7 := .var 0
  let y : BVExpr 7 := .var 1
  let z : BVExpr 7 := .var 2
  .not (.literal (.bin (.bin (.bin x .add y) .mul z) .eq
    (.bin (.bin x .mul z) .add (.bin y .mul z))))

private def m0_d3 : BVLogicalExpr :=
  let x : BVExpr 10 := .var 0
  let y : BVExpr 10 := .var 1
  .gate .and (.not (.literal (.bin y .eq (.const 0#10))))
    (.not (.literal (.bin (.bin (.bin (.bin x .udiv y) .mul y) .add (.bin x .umod y)) .eq x)))

private def m0_d4 : BVLogicalExpr :=
  let x : BVExpr 11 := .var 0
  let y : BVExpr 11 := .var 1
  .gate .and (.not (.literal (.bin y .eq (.const 0#11))))
    (.not (.literal (.bin (.bin (.bin (.bin x .udiv y) .mul y) .add (.bin x .umod y)) .eq x)))

private def m0_d5 : BVLogicalExpr :=
  let x : BVExpr 16 := .var 0
  let y : BVExpr 16 := .var 1
  .not (.literal (.bin (.bin (.un .cpop (.bin x .and y)) .add (.un .cpop (.bin x .or y))) .eq
    (.bin (.un .cpop x) .add (.un .cpop y))))

private def m0_d6 : BVLogicalExpr :=
  let x0 : BVExpr 4 := .var 0
  let x1 : BVExpr 4 := .var 1
  .gate .and (.literal (.bin x0 .ult (.const 10#4)))
    (.gate .and (.literal (.bin x1 .ult (.const 10#4)))
      (.not (.literal (.bin x0 .eq x1))))

private def m0_e1 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  let fx : BVExpr 32 := .var 2
  let fy : BVExpr 32 := .var 3
  .gate .and (.literal (.bin (.bin x .xor y) .eq (.const 0#32)))
    (.not (.literal (.bin fx .eq fy)))

private def m0_e2 : BVLogicalExpr :=
  let x : BVExpr 32 := .var 0
  let y : BVExpr 32 := .var 1
  .gate .beq (.literal (.bin x .ult y)) (.literal (.bin y .ult x))

private def m0_e3 : BVLogicalExpr :=
  let a : BVExpr 64 := .var 0
  let b : BVExpr 64 := .var 1
  .gate .xor (.literal (.bin a .eq b)) (.const true)

private def big256Const : BitVec 256 :=
  BitVec.ofNat 256 0xdeadbeefcafebabe0123456789abcdef112233445566778899aabbccddeeff00

private def wide256Expr : BVLogicalExpr :=
  let x : BVExpr 128 := .var 0
  let rep : BVExpr 256 := .replicate 2 x (by decide)
  let app : BVExpr 256 := .append (.extract 0 128 rep) (.extract 128 128 rep) (by decide)
  .not (.literal (.bin app .eq (.const big256Const)))

private def widthZeroExpr : BVLogicalExpr :=
  let v0 : BVExpr 0 := .var 7
  let c0 : BVExpr 0 := .const (BitVec.ofNat 0 0)
  let rep0 : BVExpr 0 := .replicate 0 (.var 1 : BVExpr 8) (by decide)
  let ext0 : BVExpr 0 := .extract 0 0 (.var 1 : BVExpr 8)
  let app0 : BVExpr 0 := .append v0 rep0 (by decide)
  let app0' : BVExpr 0 := .append c0 ext0 (by decide)
  .gate .and (.literal (.bin app0 .eq app0')) (.not (.literal (.getLsbD v0 0)))

private def all32OpcodesExpr : BVLogicalExpr :=
  let v0 : BVExpr 8 := .var 0
  let v1 : BVExpr 8 := .var 1
  let c : BVExpr 8 := .const 0x5a#8
  let ex : BVExpr 4 := .extract 1 4 v0
  let rep : BVExpr 8 := .replicate 2 ex (by decide)
  let app : BVExpr 8 := .append (.extract 0 4 v0) (.extract 4 4 v1) (by decide)
  let bAnd := BVExpr.bin v0 .and v1
  let bOr := BVExpr.bin bAnd .or c
  let bXor := BVExpr.bin bOr .xor rep
  let bAdd := BVExpr.bin bXor .add app
  let bMul := BVExpr.bin bAdd .mul v1
  let bDiv := BVExpr.bin bMul .udiv c
  let bMod := BVExpr.bin bDiv .umod v1
  let uNot := BVExpr.un .not bMod
  let uRotL := BVExpr.un (.rotateLeft 3) uNot
  let uRotR := BVExpr.un (.rotateRight 2) uRotL
  let uAshrC := BVExpr.un (.arithShiftRightConst 1) uRotR
  let uRev := BVExpr.un .reverse uAshrC
  let uClz := BVExpr.un .clz uRev
  let uCpop := BVExpr.un .cpop uClz
  let sShl := BVExpr.shiftLeft uCpop v0
  let sUshr := BVExpr.shiftRight sShl v1
  let sAshr := BVExpr.arithShiftRight sUshr v0
  let pEq : BVLogicalExpr := .literal (.bin sAshr .eq c)
  let pUlt : BVLogicalExpr := .literal (.bin sAshr .ult v0)
  let pLsb : BVLogicalExpr := .literal (.getLsbD sAshr 0)
  let bT : BVLogicalExpr := .const true
  let bF : BVLogicalExpr := .const false
  let gAnd : BVLogicalExpr := .gate .and pEq pUlt
  let gXor : BVLogicalExpr := .gate .xor gAnd pLsb
  let gBeq : BVLogicalExpr := .gate .beq gXor bT
  let gOr : BVLogicalExpr := .gate .or gBeq (.not bF)
  .ite gOr pEq bF

private def extractOpcodes (ws : List Nat) : Array Nat := Id.run do
  match ws with
  | _ :: _ :: nVars :: nNodes :: nCwords :: _ :: _ :: _ :: rest =>
    let skip := 2 * nVars + nCwords
    let nodeWords := rest.drop skip
    let mut ops : Array Nat := Array.emptyWithCapacity nNodes
    let mut cur := nodeWords
    for _ in [0:nNodes] do
      match cur with
      | op :: _ :: _ :: _ :: _ :: tl =>
        ops := ops.push op
        cur := tl
      | _ => break
    return ops
  | _ => #[]

private def coversAll32Opcodes (e : BVLogicalExpr) : Bool :=
  match BvDecideQbe.encode e with
  | none => false
  | some p =>
    let ops := extractOpcodes p.words
    (List.range 32).all fun op => ops.contains op

private def repeatedVarDiffWidthExpr : BVLogicalExpr :=
  let v4 : BVExpr 4 := .var 0
  let v8 : BVExpr 8 := .var 0
  .gate .and (.literal (.bin v4 .eq (.const 3#4)))
    (.literal (.bin (.extract 0 4 v8) .eq v4))

private def sharedDagExpr (n : Nat) : BVLogicalExpr :=
  Id.run do
    let x : BVExpr 32 := .var 0
    let y : BVExpr 32 := .var 1
    let mut cur : BVExpr 32 := .bin x .add y
    for i in [0:n] do
      if i % 2 == 0 then
        cur := .bin cur .xor y
      else
        cur := .bin cur .add x
    let mut dup : BVExpr 32 := cur
    dup := .bin dup .and (.un .not cur)
    return .not (.literal (.bin cur .eq dup))

#guard roundTripOk m0_a1
#guard roundTripOk m0_a2
#guard roundTripOk m0_a3
#guard roundTripOk m0_a4
#guard roundTripOk m0_a5
#guard roundTripOk m0_b1
#guard roundTripOk m0_b2
#guard roundTripOk m0_b3
#guard roundTripOk m0_b4
#guard roundTripOk m0_b5
#guard roundTripOk m0_b6
#guard roundTripOk m0_c1
#guard roundTripOk m0_c2
#guard roundTripOk m0_c3
#guard roundTripOk m0_c4
#guard roundTripOk m0_c5
#guard roundTripOk m0_d1
#guard roundTripOk m0_d2
#guard roundTripOk m0_d3
#guard roundTripOk m0_d4
#guard roundTripOk m0_d5
#guard roundTripOk m0_d6
#guard roundTripOk m0_e1
#guard roundTripOk m0_e2
#guard roundTripOk m0_e3
#guard roundTripOk wide256Expr
#guard roundTripOk widthZeroExpr
#guard roundTripOk all32OpcodesExpr
#guard coversAll32Opcodes all32OpcodesExpr
#guard roundTripOk repeatedVarDiffWidthExpr
#guard roundTripOk (sharedDagExpr 40)
#guard match BvDecideQbe.encode (sharedDagExpr 40) with
  | some p => p.stats.nNodes < 100
  | none => false

/-! ## 2. `estimateWorkSize` Bounds, Power-of-2, and Monotonicity -/

private def isPow2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

private def workSizeValid (e : BVLogicalExpr) : Bool :=
  let sz := (estimateWorkSizeOfExpr e).toNat
  minWorkBytes <= sz && sz <= maxWorkBytes && isPow2 sz

#guard workSizeValid (.const true)
#guard (estimateWorkSizeOfExpr (.const true)).toNat == minWorkBytes
#guard workSizeValid m0_a1
#guard workSizeValid m0_b4
#guard workSizeValid m0_b6
#guard workSizeValid m0_c2
#guard workSizeValid m0_c5
#guard (estimateWorkSizeOfExpr m0_b6).toNat > (estimateWorkSizeOfExpr m0_a1).toNat
#guard (estimateWorkSizeOfExpr m0_b4).toNat >= (estimateWorkSizeOfExpr m0_a2).toNat
#guard (estimateWorkSizeOfExpr (.literal (.bin (.bin (.var 0 : BVExpr 64) .mul (.var 1 : BVExpr 64)) .eq (.const 0#64)))).toNat >=
  (estimateWorkSizeOfExpr (.literal (.bin (.bin (.var 0 : BVExpr 16) .mul (.var 1 : BVExpr 16)) .eq (.const 0#16)))).toNat
private def hugeStats : ProgStats :=
  { nVars := 100
    nNodes := 10000
    nCwords := 0
    totalAtomBits := 100000
    estAigGates := 10000000
    estClauses := 30000001
    maxWidth := 256 }

#guard (estimateWorkSize hugeStats).toNat == maxWorkBytes

/-! ## 3. `Counterexample` Decoding & `evalEfficient` Validation -/

private def writeBits (arr : Array UInt8) (base width val : Nat) : Array UInt8 := Id.run do
  let mut out := arr
  while out.size < base + width do
    out := out.push 0
  for j in [0:width] do
    let bit : UInt8 := if (val >>> j) &&& 1 == 1 then 1 else 0
    out := out.set! (base + j) bit
  return out

private def testCexDecodeSat (expr : BVLogicalExpr) (vals : List (Nat × Nat)) : Bool :=
  match BvDecideQbe.encode expr with
  | none => false
  | some enc =>
    let arr := Id.run do
      let mut model := ByteArray.empty
      let mut bytes := Array.replicate (enc.stats.totalAtomBits + 5) (0 : UInt8)
      for h : k in [0:enc.varTable.size] do
        let (bvIdx, w) := enc.varTable[k]
        let base := enc.atomBase[k]!
        let v := (vals.find? (fun p => p.1 == bvIdx)).map (·.2) |>.getD 0
        bytes := writeBits bytes base w v
      model := ByteArray.mk bytes
      return model
    match decodeAndValidate expr enc arr with
    | none => false
    | some assign =>
      vals.all fun (bvIdx, expected) =>
        (assign.get bvIdx).bv.toNat == expected

#guard testCexDecodeSat (.literal (.bin (.var 0 : BVExpr 4) .eq (.const 5#4))) [(0, 5)]
#guard !testCexDecodeSat (.literal (.bin (.var 0 : BVExpr 4) .eq (.const 5#4))) [(0, 6)]
#guard testCexDecodeSat (.literal (.bin (.bin (.var 0 : BVExpr 8) .add (.const 1#8)) .eq (.const 0#8))) [(0, 255)]
#guard testCexDecodeSat (.gate .and (.literal (.bin (.var 10 : BVExpr 8) .ult (.var 20 : BVExpr 8)))
  (.literal (.bin (.var 20 : BVExpr 8) .eq (.const 42#8)))) [(10, 7), (20, 42)]
#guard testCexDecodeSat (.literal (.bin (.var 0 : BVExpr 256) .eq (.const big256Const))) [(0, big256Const.toNat)]
#guard !testCexDecodeSat (.literal (.bin (.var 0 : BVExpr 256) .eq (.const big256Const))) [(0, big256Const.toNat ^^^ 1)]
#guard testCexDecodeSat widthZeroExpr [(7, 0), (1, 0)]
#guard match BvDecideQbe.encode (.const true) with
  | some enc => (decodeAndValidate (.const true) enc ByteArray.empty).isSome
  | none => false

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

def runAll : IO Unit := do
  -- Shared DAG 200-node round-trip
  let dag200 := sharedDagExpr 200
  let some enc200 := BvDecideQbe.encode dag200
    | throw (IO.userError "encode dag200 failed")
  assertTrue "dag200 shares nodes (nNodes <= 410)" (enc200.stats.nNodes <= 410)
  assertTrue "dag200 roundTripOk" (roundTripOk dag200)
  assertTrue "dag200 workSize valid" (workSizeValid dag200)

  -- Reconstruct validated counterexample with atomsAssignment (including synthetic + unencoded)
  let expr : BVLogicalExpr :=
    .gate .and (.literal (.bin (.bin (.var 10 : BVExpr 8) .add (.var 20 : BVExpr 8)) .eq (.const 50#8)))
      (.literal (.bin (.var 10 : BVExpr 8) .ult (.const 30#8)))
  let some enc := BvDecideQbe.encode expr
    | throw (IO.userError "encode sparse sat expr failed")
  let mut bytes := Array.replicate (enc.stats.totalAtomBits + 8) (0 : UInt8)
  for k in [0:enc.varTable.size] do
    let (bvIdx, w) := enc.varTable[k]!
    let base := enc.atomBase[k]!
    let v := if bvIdx == 10 then 17 else 33
    bytes := writeBits bytes base w v
  let model := ByteArray.mk bytes
  let mut atoms : Std.HashMap Nat (Nat × Expr × Bool) := {}
  atoms := atoms.insert 10 (8, mkConst `x10, false)
  atoms := atoms.insert 20 (8, mkConst `x20, true)
  atoms := atoms.insert 99 (16, mkConst `unused99, false)
  match reconstructValidatedCounterExample expr enc model atoms with
  | .error err => throw (IO.userError s!"reconstructValidatedCounterExample failed: {err}")
  | .ok (assign, eqs) =>
    assertTrue "assign[10] == 17" ((assign.get 10).bv.toNat == 17)
    assertTrue "assign[20] == 33" ((assign.get 20).bv.toNat == 33)
    assertTrue "eqs has 3 entries" (eqs.size == 3)

  -- Corrupt model must be rejected by evalEfficient
  let badBytes := bytes.set! enc.atomBase[0]! (bytes[enc.atomBase[0]!]! ^^^ 1)
  match reconstructValidatedCounterExample expr enc (ByteArray.mk badBytes) atoms with
  | .ok _ => throw (IO.userError "corrupt model was unexpectedly accepted")
  | .error _ => pure ()

  -- Check estimateWorkSize monotonicity across width & op complexity
  let ws16 := (estimateWorkSizeOfExpr m0_a4).toNat
  let ws256 := (estimateWorkSizeOfExpr m0_b6).toNat
  assertTrue s!"ws256 ({ws256}) >= ws16 ({ws16})" (ws256 >= ws16)

  IO.println "EncodeCexTest: ALL PASSED (25 M0 + 32 opcodes + 256-bit + w=0 + DAG200 + sizing + CEX evalEfficient)"

#eval runAll

end BvDecideQbeTest.EncodeCexTest

def main : IO Unit := BvDecideQbeTest.EncodeCexTest.runAll
