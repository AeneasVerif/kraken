module

public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public meta import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import LeanQbe.T.Examples.Bitblast.Ref.Aig
public meta import LeanQbe.T.Examples.Bitblast.Ref.Aig
public import LeanQbe.T.Examples.Bitblast.Ref.Tseitin
public meta import LeanQbe.T.Examples.Bitblast.Ref.Tseitin
public import LeanQbe.T.Examples.BvDecideBridge
public meta import LeanQbe.T.Examples.BvDecideBridge

/-!
# Tests, Empirical Kernel `rfl` Gate (< 5 ms), and Axiom Audit for `Bitblast.Ref` (`S2a`)

1. `#guard` encode/decode round-trips across all 25 `M0`-style AST shapes and every `BVExpr`,
   `BVPred`, and `BVLogicalExpr` constructor (including 256-bit constants, `w = 0`, sparse vars,
   dependent `append`/`replicate`, `udiv`/`umod`, `clz`, `cpop`, `ite`).
2. Empirical kernel `rfl` gate (`set_option Elab.async false`, `set_option trace.profiler true`)
   for `BVProg.parseWords ws = some expr := rfl` on small, 256-bit, dependent, and
   120/200-node DAGs.
3. `Aig` and `Tseitin` (`coiMark`, `tseitin`, `ValidDimacsCnf`) sanity checks.
4. Single-line `#print axioms` audit (`<= std3`).
-/

set_option autoImplicit false
set_option Elab.async false

public section

namespace LeanQbeTest.T.BitblastRefTest

open Std.Sat
open Std.Tactic.BVDecide
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.BvDecideBridge
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Ref.Tseitin

private def roundTripOk (e : BVLogicalExpr) : Bool :=
  match BVProg.encode e with
  | none => false
  | some ws =>
    match BVProg.parseWords ws, BVProg.parse (BVProg.wordsToBytesLE ws) with
    | some e1, some e2 => BVProg.logicalExprEq e1 e && BVProg.logicalExprEq e2 e
    | _, _ => false

/-! ## 1. Round-Trip Tests Covering All Constructors & 25 `M0`-Style Shapes -/

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

private def allCtorsExpr : BVLogicalExpr :=
  let v0 : BVExpr 0 := .var 5
  let v8 : BVExpr 8 := .var 100
  let v8b : BVExpr 8 := .var 1000
  let v4 : BVExpr 4 := .extract 2 4 v8
  let rep : BVExpr 12 := .replicate 3 v4 (by decide)
  let rev : BVExpr 12 := .un .reverse rep
  let ror : BVExpr 12 := .un (.rotateRight 5) rev
  let asr : BVExpr 12 := .arithShiftRight ror v8b
  let ext : BVExpr 8 := .extract 0 8 asr
  let app : BVExpr 8 := .append (.extract 0 0 v0) ext (by decide)
  .ite (.const false) (.literal (.bin app .eq v8)) (.gate .or (.const true) (.not (.const false)))

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
#guard roundTripOk allCtorsExpr

/-! ## 2. Empirical Kernel `rfl` Gate (`BVProg.parseWords ws = some expr := rfl`) -/

/-- Small 4-bit `x ^^^ x == 0` AST and literal `BVP1` word list (5 nodes). -/
@[expose] def smallExpr : BVLogicalExpr :=
  .not (.literal (.bin (.bin (.var 0 : BVExpr 4) .xor (.var 0 : BVExpr 4)) .eq (.const 0#4)))

@[expose] def smallWs : List Nat :=
  [ 0x31505642, 1, 1, 5, 1, 4, 0, 0,
    0, 4,
    0,
    0, 4, 0, 0, 0,
    5, 4, 0, 0, 0,
    1, 4, 0, 0, 0,
    22, 1, 1, 2, 0,
    26, 1, 3, 0, 0 ]

section ProfilerGate
set_option trace.profiler true
set_option trace.profiler.threshold 1

theorem kernel_rfl_small : BVProg.parseWords smallWs = some smallExpr := rfl

end ProfilerGate

/-- Wide 256-bit constant + dependent `.append` + `.replicate` AST (8 nodes). -/
@[expose] def big256Const : BitVec 256 :=
  BitVec.ofNat 256 0xdeadbeefcafebabe0123456789abcdef112233445566778899aabbccddeeff00

@[expose] def wideDepExpr : BVLogicalExpr :=
  let x : BVExpr 128 := .var 0
  let rep : BVExpr 256 := .replicate 2 x (by decide)
  let app : BVExpr 256 := .append (.extract 0 128 rep) (.extract 128 128 rep) (by decide)
  .not (.literal (.bin app .eq (.const big256Const)))

@[expose] def wideDepWs : List Nat :=
  [ 0x31505642, 1, 1, 8, 8, 7, 0, 0,
    0, 128,
    0xddeeff00, 0x99aabbcc, 0x55667788, 0x11223344,
    0x89abcdef, 0x01234567, 0xcafebabe, 0xdeadbeef,
    0, 128, 0, 0, 0,
    18, 256, 0, 2, 0,
    2, 128, 0, 1, 0,
    2, 128, 128, 1, 0,
    17, 256, 2, 3, 0,
    1, 256, 0, 0, 0,
    22, 1, 4, 5, 0,
    26, 1, 6, 0, 0 ]

#guard BVProg.encode wideDepExpr == some wideDepWs

section ProfilerGateWide
set_option trace.profiler true
set_option trace.profiler.threshold 1

theorem kernel_rfl_wide_dep : BVProg.parseWords wideDepWs = some wideDepExpr := rfl

end ProfilerGateWide

@[expose] def dag120Expr : BVLogicalExpr :=
  let n0 : BVExpr 32 := .var 0
  let n1 : BVExpr 32 := .var 1
  let n2 : BVExpr 32 := .const 1#32
  let n3 : BVExpr 32 := .bin n2 .add n1
  let n4 : BVExpr 32 := .un .not n3
  let n5 : BVExpr 32 := .bin n4 .and n1
  let n6 : BVExpr 32 := .bin n5 .or n0
  let n7 : BVExpr 32 := .bin n6 .xor n1
  let n8 : BVExpr 32 := .bin n7 .add n0
  let n9 : BVExpr 32 := .un .not n8
  let n10 : BVExpr 32 := .bin n9 .and n0
  let n11 : BVExpr 32 := .bin n10 .or n1
  let n12 : BVExpr 32 := .bin n11 .xor n0
  let n13 : BVExpr 32 := .bin n12 .add n1
  let n14 : BVExpr 32 := .un .not n13
  let n15 : BVExpr 32 := .bin n14 .and n1
  let n16 : BVExpr 32 := .bin n15 .or n0
  let n17 : BVExpr 32 := .bin n16 .xor n1
  let n18 : BVExpr 32 := .bin n17 .add n0
  let n19 : BVExpr 32 := .un .not n18
  let n20 : BVExpr 32 := .bin n19 .and n0
  let n21 : BVExpr 32 := .bin n20 .or n1
  let n22 : BVExpr 32 := .bin n21 .xor n0
  let n23 : BVExpr 32 := .bin n22 .add n1
  let n24 : BVExpr 32 := .un .not n23
  let n25 : BVExpr 32 := .bin n24 .and n1
  let n26 : BVExpr 32 := .bin n25 .or n0
  let n27 : BVExpr 32 := .bin n26 .xor n1
  let n28 : BVExpr 32 := .bin n27 .add n0
  let n29 : BVExpr 32 := .un .not n28
  let n30 : BVExpr 32 := .bin n29 .and n0
  let n31 : BVExpr 32 := .bin n30 .or n1
  let n32 : BVExpr 32 := .bin n31 .xor n0
  let n33 : BVExpr 32 := .bin n32 .add n1
  let n34 : BVExpr 32 := .un .not n33
  let n35 : BVExpr 32 := .bin n34 .and n1
  let n36 : BVExpr 32 := .bin n35 .or n0
  let n37 : BVExpr 32 := .bin n36 .xor n1
  let n38 : BVExpr 32 := .bin n37 .add n0
  let n39 : BVExpr 32 := .un .not n38
  let n40 : BVExpr 32 := .bin n39 .and n0
  let n41 : BVExpr 32 := .bin n40 .or n1
  let n42 : BVExpr 32 := .bin n41 .xor n0
  let n43 : BVExpr 32 := .bin n42 .add n1
  let n44 : BVExpr 32 := .un .not n43
  let n45 : BVExpr 32 := .bin n44 .and n1
  let n46 : BVExpr 32 := .bin n45 .or n0
  let n47 : BVExpr 32 := .bin n46 .xor n1
  let n48 : BVExpr 32 := .bin n47 .add n0
  let n49 : BVExpr 32 := .un .not n48
  let n50 : BVExpr 32 := .bin n49 .and n0
  let n51 : BVExpr 32 := .bin n50 .or n1
  let n52 : BVExpr 32 := .bin n51 .xor n0
  let n53 : BVExpr 32 := .bin n52 .add n1
  let n54 : BVExpr 32 := .un .not n53
  let n55 : BVExpr 32 := .bin n54 .and n1
  let n56 : BVExpr 32 := .bin n55 .or n0
  let n57 : BVExpr 32 := .bin n56 .xor n1
  let n58 : BVExpr 32 := .bin n57 .add n0
  let n59 : BVExpr 32 := .un .not n58
  let n60 : BVExpr 32 := .bin n59 .and n0
  let n61 : BVExpr 32 := .bin n60 .or n1
  let n62 : BVExpr 32 := .bin n61 .xor n0
  let n63 : BVExpr 32 := .bin n62 .add n1
  let n64 : BVExpr 32 := .un .not n63
  let n65 : BVExpr 32 := .bin n64 .and n1
  let n66 : BVExpr 32 := .bin n65 .or n0
  let n67 : BVExpr 32 := .bin n66 .xor n1
  let n68 : BVExpr 32 := .bin n67 .add n0
  let n69 : BVExpr 32 := .un .not n68
  let n70 : BVExpr 32 := .bin n69 .and n0
  let n71 : BVExpr 32 := .bin n70 .or n1
  let n72 : BVExpr 32 := .bin n71 .xor n0
  let n73 : BVExpr 32 := .bin n72 .add n1
  let n74 : BVExpr 32 := .un .not n73
  let n75 : BVExpr 32 := .bin n74 .and n1
  let n76 : BVExpr 32 := .bin n75 .or n0
  let n77 : BVExpr 32 := .bin n76 .xor n1
  let n78 : BVExpr 32 := .bin n77 .add n0
  let n79 : BVExpr 32 := .un .not n78
  let n80 : BVExpr 32 := .bin n79 .and n0
  let n81 : BVExpr 32 := .bin n80 .or n1
  let n82 : BVExpr 32 := .bin n81 .xor n0
  let n83 : BVExpr 32 := .bin n82 .add n1
  let n84 : BVExpr 32 := .un .not n83
  let n85 : BVExpr 32 := .bin n84 .and n1
  let n86 : BVExpr 32 := .bin n85 .or n0
  let n87 : BVExpr 32 := .bin n86 .xor n1
  let n88 : BVExpr 32 := .bin n87 .add n0
  let n89 : BVExpr 32 := .un .not n88
  let n90 : BVExpr 32 := .bin n89 .and n0
  let n91 : BVExpr 32 := .bin n90 .or n1
  let n92 : BVExpr 32 := .bin n91 .xor n0
  let n93 : BVExpr 32 := .bin n92 .add n1
  let n94 : BVExpr 32 := .un .not n93
  let n95 : BVExpr 32 := .bin n94 .and n1
  let n96 : BVExpr 32 := .bin n95 .or n0
  let n97 : BVExpr 32 := .bin n96 .xor n1
  let n98 : BVExpr 32 := .bin n97 .add n0
  let n99 : BVExpr 32 := .un .not n98
  let n100 : BVExpr 32 := .bin n99 .and n0
  let n101 : BVExpr 32 := .bin n100 .or n1
  let n102 : BVExpr 32 := .bin n101 .xor n0
  let n103 : BVExpr 32 := .bin n102 .add n1
  let n104 : BVExpr 32 := .un .not n103
  let n105 : BVExpr 32 := .bin n104 .and n1
  let n106 : BVExpr 32 := .bin n105 .or n0
  let n107 : BVExpr 32 := .bin n106 .xor n1
  let n108 : BVExpr 32 := .bin n107 .add n0
  let n109 : BVExpr 32 := .un .not n108
  let n110 : BVExpr 32 := .bin n109 .and n0
  let n111 : BVExpr 32 := .bin n110 .or n1
  let n112 : BVExpr 32 := .bin n111 .xor n0
  let n113 : BVExpr 32 := .bin n112 .add n1
  let n114 : BVExpr 32 := .un .not n113
  let n115 : BVExpr 32 := .bin n114 .and n1
  let n116 : BVExpr 32 := .bin n115 .or n0
  let n117 : BVExpr 32 := .bin n116 .xor n1
  .not (.literal (.bin n116 .eq n117))

@[expose] def dag120Ws : List Nat :=
  [ 827348546, 1, 2, 120, 1, 119, 0, 0, 1, 32, 0, 32, 1, 1, 32, 0, 0, 0, 0, 32, 0, 0, 0, 6, 32,
    0, 1, 0, 10, 32, 2, 0, 0, 3, 32, 3, 1, 0, 0, 32, 1, 0, 0, 4, 32, 4, 5, 0, 5, 32, 6, 1, 0, 6,
    32, 7, 5, 0, 10, 32, 8, 0, 0, 3, 32, 9, 5, 0, 4, 32, 10, 1, 0, 5, 32, 11, 5, 0, 6, 32, 12, 1,
    0, 10, 32, 13, 0, 0, 3, 32, 14, 1, 0, 4, 32, 15, 5, 0, 5, 32, 16, 1, 0, 6, 32, 17, 5, 0, 10,
    32, 18, 0, 0, 3, 32, 19, 5, 0, 4, 32, 20, 1, 0, 5, 32, 21, 5, 0, 6, 32, 22, 1, 0, 10, 32, 23,
    0, 0, 3, 32, 24, 1, 0, 4, 32, 25, 5, 0, 5, 32, 26, 1, 0, 6, 32, 27, 5, 0, 10, 32, 28, 0, 0,
    3, 32, 29, 5, 0, 4, 32, 30, 1, 0, 5, 32, 31, 5, 0, 6, 32, 32, 1, 0, 10, 32, 33, 0, 0, 3, 32,
    34, 1, 0, 4, 32, 35, 5, 0, 5, 32, 36, 1, 0, 6, 32, 37, 5, 0, 10, 32, 38, 0, 0, 3, 32, 39, 5,
    0, 4, 32, 40, 1, 0, 5, 32, 41, 5, 0, 6, 32, 42, 1, 0, 10, 32, 43, 0, 0, 3, 32, 44, 1, 0, 4,
    32, 45, 5, 0, 5, 32, 46, 1, 0, 6, 32, 47, 5, 0, 10, 32, 48, 0, 0, 3, 32, 49, 5, 0, 4, 32, 50,
    1, 0, 5, 32, 51, 5, 0, 6, 32, 52, 1, 0, 10, 32, 53, 0, 0, 3, 32, 54, 1, 0, 4, 32, 55, 5, 0,
    5, 32, 56, 1, 0, 6, 32, 57, 5, 0, 10, 32, 58, 0, 0, 3, 32, 59, 5, 0, 4, 32, 60, 1, 0, 5, 32,
    61, 5, 0, 6, 32, 62, 1, 0, 10, 32, 63, 0, 0, 3, 32, 64, 1, 0, 4, 32, 65, 5, 0, 5, 32, 66, 1,
    0, 6, 32, 67, 5, 0, 10, 32, 68, 0, 0, 3, 32, 69, 5, 0, 4, 32, 70, 1, 0, 5, 32, 71, 5, 0, 6,
    32, 72, 1, 0, 10, 32, 73, 0, 0, 3, 32, 74, 1, 0, 4, 32, 75, 5, 0, 5, 32, 76, 1, 0, 6, 32, 77,
    5, 0, 10, 32, 78, 0, 0, 3, 32, 79, 5, 0, 4, 32, 80, 1, 0, 5, 32, 81, 5, 0, 6, 32, 82, 1, 0,
    10, 32, 83, 0, 0, 3, 32, 84, 1, 0, 4, 32, 85, 5, 0, 5, 32, 86, 1, 0, 6, 32, 87, 5, 0, 10, 32,
    88, 0, 0, 3, 32, 89, 5, 0, 4, 32, 90, 1, 0, 5, 32, 91, 5, 0, 6, 32, 92, 1, 0, 10, 32, 93, 0,
    0, 3, 32, 94, 1, 0, 4, 32, 95, 5, 0, 5, 32, 96, 1, 0, 6, 32, 97, 5, 0, 10, 32, 98, 0, 0, 3,
    32, 99, 5, 0, 4, 32, 100, 1, 0, 5, 32, 101, 5, 0, 6, 32, 102, 1, 0, 10, 32, 103, 0, 0, 3, 32,
    104, 1, 0, 4, 32, 105, 5, 0, 5, 32, 106, 1, 0, 6, 32, 107, 5, 0, 10, 32, 108, 0, 0, 3, 32,
    109, 5, 0, 4, 32, 110, 1, 0, 5, 32, 111, 5, 0, 6, 32, 112, 1, 0, 10, 32, 113, 0, 0, 3, 32,
    114, 1, 0, 4, 32, 115, 5, 0, 5, 32, 116, 1, 0, 22, 1, 116, 117, 0, 26, 1, 118, 0, 0 ]

@[expose] def dag200Expr : BVLogicalExpr :=
  let n0 : BVExpr 32 := .var 0
  let n1 : BVExpr 32 := .var 1
  let n2 : BVExpr 32 := .const 1#32
  let n3 : BVExpr 32 := .bin n2 .add n1
  let n4 : BVExpr 32 := .un .not n3
  let n5 : BVExpr 32 := .bin n4 .and n1
  let n6 : BVExpr 32 := .bin n5 .or n0
  let n7 : BVExpr 32 := .bin n6 .xor n1
  let n8 : BVExpr 32 := .bin n7 .add n0
  let n9 : BVExpr 32 := .un .not n8
  let n10 : BVExpr 32 := .bin n9 .and n0
  let n11 : BVExpr 32 := .bin n10 .or n1
  let n12 : BVExpr 32 := .bin n11 .xor n0
  let n13 : BVExpr 32 := .bin n12 .add n1
  let n14 : BVExpr 32 := .un .not n13
  let n15 : BVExpr 32 := .bin n14 .and n1
  let n16 : BVExpr 32 := .bin n15 .or n0
  let n17 : BVExpr 32 := .bin n16 .xor n1
  let n18 : BVExpr 32 := .bin n17 .add n0
  let n19 : BVExpr 32 := .un .not n18
  let n20 : BVExpr 32 := .bin n19 .and n0
  let n21 : BVExpr 32 := .bin n20 .or n1
  let n22 : BVExpr 32 := .bin n21 .xor n0
  let n23 : BVExpr 32 := .bin n22 .add n1
  let n24 : BVExpr 32 := .un .not n23
  let n25 : BVExpr 32 := .bin n24 .and n1
  let n26 : BVExpr 32 := .bin n25 .or n0
  let n27 : BVExpr 32 := .bin n26 .xor n1
  let n28 : BVExpr 32 := .bin n27 .add n0
  let n29 : BVExpr 32 := .un .not n28
  let n30 : BVExpr 32 := .bin n29 .and n0
  let n31 : BVExpr 32 := .bin n30 .or n1
  let n32 : BVExpr 32 := .bin n31 .xor n0
  let n33 : BVExpr 32 := .bin n32 .add n1
  let n34 : BVExpr 32 := .un .not n33
  let n35 : BVExpr 32 := .bin n34 .and n1
  let n36 : BVExpr 32 := .bin n35 .or n0
  let n37 : BVExpr 32 := .bin n36 .xor n1
  let n38 : BVExpr 32 := .bin n37 .add n0
  let n39 : BVExpr 32 := .un .not n38
  let n40 : BVExpr 32 := .bin n39 .and n0
  let n41 : BVExpr 32 := .bin n40 .or n1
  let n42 : BVExpr 32 := .bin n41 .xor n0
  let n43 : BVExpr 32 := .bin n42 .add n1
  let n44 : BVExpr 32 := .un .not n43
  let n45 : BVExpr 32 := .bin n44 .and n1
  let n46 : BVExpr 32 := .bin n45 .or n0
  let n47 : BVExpr 32 := .bin n46 .xor n1
  let n48 : BVExpr 32 := .bin n47 .add n0
  let n49 : BVExpr 32 := .un .not n48
  let n50 : BVExpr 32 := .bin n49 .and n0
  let n51 : BVExpr 32 := .bin n50 .or n1
  let n52 : BVExpr 32 := .bin n51 .xor n0
  let n53 : BVExpr 32 := .bin n52 .add n1
  let n54 : BVExpr 32 := .un .not n53
  let n55 : BVExpr 32 := .bin n54 .and n1
  let n56 : BVExpr 32 := .bin n55 .or n0
  let n57 : BVExpr 32 := .bin n56 .xor n1
  let n58 : BVExpr 32 := .bin n57 .add n0
  let n59 : BVExpr 32 := .un .not n58
  let n60 : BVExpr 32 := .bin n59 .and n0
  let n61 : BVExpr 32 := .bin n60 .or n1
  let n62 : BVExpr 32 := .bin n61 .xor n0
  let n63 : BVExpr 32 := .bin n62 .add n1
  let n64 : BVExpr 32 := .un .not n63
  let n65 : BVExpr 32 := .bin n64 .and n1
  let n66 : BVExpr 32 := .bin n65 .or n0
  let n67 : BVExpr 32 := .bin n66 .xor n1
  let n68 : BVExpr 32 := .bin n67 .add n0
  let n69 : BVExpr 32 := .un .not n68
  let n70 : BVExpr 32 := .bin n69 .and n0
  let n71 : BVExpr 32 := .bin n70 .or n1
  let n72 : BVExpr 32 := .bin n71 .xor n0
  let n73 : BVExpr 32 := .bin n72 .add n1
  let n74 : BVExpr 32 := .un .not n73
  let n75 : BVExpr 32 := .bin n74 .and n1
  let n76 : BVExpr 32 := .bin n75 .or n0
  let n77 : BVExpr 32 := .bin n76 .xor n1
  let n78 : BVExpr 32 := .bin n77 .add n0
  let n79 : BVExpr 32 := .un .not n78
  let n80 : BVExpr 32 := .bin n79 .and n0
  let n81 : BVExpr 32 := .bin n80 .or n1
  let n82 : BVExpr 32 := .bin n81 .xor n0
  let n83 : BVExpr 32 := .bin n82 .add n1
  let n84 : BVExpr 32 := .un .not n83
  let n85 : BVExpr 32 := .bin n84 .and n1
  let n86 : BVExpr 32 := .bin n85 .or n0
  let n87 : BVExpr 32 := .bin n86 .xor n1
  let n88 : BVExpr 32 := .bin n87 .add n0
  let n89 : BVExpr 32 := .un .not n88
  let n90 : BVExpr 32 := .bin n89 .and n0
  let n91 : BVExpr 32 := .bin n90 .or n1
  let n92 : BVExpr 32 := .bin n91 .xor n0
  let n93 : BVExpr 32 := .bin n92 .add n1
  let n94 : BVExpr 32 := .un .not n93
  let n95 : BVExpr 32 := .bin n94 .and n1
  let n96 : BVExpr 32 := .bin n95 .or n0
  let n97 : BVExpr 32 := .bin n96 .xor n1
  let n98 : BVExpr 32 := .bin n97 .add n0
  let n99 : BVExpr 32 := .un .not n98
  let n100 : BVExpr 32 := .bin n99 .and n0
  let n101 : BVExpr 32 := .bin n100 .or n1
  let n102 : BVExpr 32 := .bin n101 .xor n0
  let n103 : BVExpr 32 := .bin n102 .add n1
  let n104 : BVExpr 32 := .un .not n103
  let n105 : BVExpr 32 := .bin n104 .and n1
  let n106 : BVExpr 32 := .bin n105 .or n0
  let n107 : BVExpr 32 := .bin n106 .xor n1
  let n108 : BVExpr 32 := .bin n107 .add n0
  let n109 : BVExpr 32 := .un .not n108
  let n110 : BVExpr 32 := .bin n109 .and n0
  let n111 : BVExpr 32 := .bin n110 .or n1
  let n112 : BVExpr 32 := .bin n111 .xor n0
  let n113 : BVExpr 32 := .bin n112 .add n1
  let n114 : BVExpr 32 := .un .not n113
  let n115 : BVExpr 32 := .bin n114 .and n1
  let n116 : BVExpr 32 := .bin n115 .or n0
  let n117 : BVExpr 32 := .bin n116 .xor n1
  let n118 : BVExpr 32 := .bin n117 .add n0
  let n119 : BVExpr 32 := .un .not n118
  let n120 : BVExpr 32 := .bin n119 .and n0
  let n121 : BVExpr 32 := .bin n120 .or n1
  let n122 : BVExpr 32 := .bin n121 .xor n0
  let n123 : BVExpr 32 := .bin n122 .add n1
  let n124 : BVExpr 32 := .un .not n123
  let n125 : BVExpr 32 := .bin n124 .and n1
  let n126 : BVExpr 32 := .bin n125 .or n0
  let n127 : BVExpr 32 := .bin n126 .xor n1
  let n128 : BVExpr 32 := .bin n127 .add n0
  let n129 : BVExpr 32 := .un .not n128
  let n130 : BVExpr 32 := .bin n129 .and n0
  let n131 : BVExpr 32 := .bin n130 .or n1
  let n132 : BVExpr 32 := .bin n131 .xor n0
  let n133 : BVExpr 32 := .bin n132 .add n1
  let n134 : BVExpr 32 := .un .not n133
  let n135 : BVExpr 32 := .bin n134 .and n1
  let n136 : BVExpr 32 := .bin n135 .or n0
  let n137 : BVExpr 32 := .bin n136 .xor n1
  let n138 : BVExpr 32 := .bin n137 .add n0
  let n139 : BVExpr 32 := .un .not n138
  let n140 : BVExpr 32 := .bin n139 .and n0
  let n141 : BVExpr 32 := .bin n140 .or n1
  let n142 : BVExpr 32 := .bin n141 .xor n0
  let n143 : BVExpr 32 := .bin n142 .add n1
  let n144 : BVExpr 32 := .un .not n143
  let n145 : BVExpr 32 := .bin n144 .and n1
  let n146 : BVExpr 32 := .bin n145 .or n0
  let n147 : BVExpr 32 := .bin n146 .xor n1
  let n148 : BVExpr 32 := .bin n147 .add n0
  let n149 : BVExpr 32 := .un .not n148
  let n150 : BVExpr 32 := .bin n149 .and n0
  let n151 : BVExpr 32 := .bin n150 .or n1
  let n152 : BVExpr 32 := .bin n151 .xor n0
  let n153 : BVExpr 32 := .bin n152 .add n1
  let n154 : BVExpr 32 := .un .not n153
  let n155 : BVExpr 32 := .bin n154 .and n1
  let n156 : BVExpr 32 := .bin n155 .or n0
  let n157 : BVExpr 32 := .bin n156 .xor n1
  let n158 : BVExpr 32 := .bin n157 .add n0
  let n159 : BVExpr 32 := .un .not n158
  let n160 : BVExpr 32 := .bin n159 .and n0
  let n161 : BVExpr 32 := .bin n160 .or n1
  let n162 : BVExpr 32 := .bin n161 .xor n0
  let n163 : BVExpr 32 := .bin n162 .add n1
  let n164 : BVExpr 32 := .un .not n163
  let n165 : BVExpr 32 := .bin n164 .and n1
  let n166 : BVExpr 32 := .bin n165 .or n0
  let n167 : BVExpr 32 := .bin n166 .xor n1
  let n168 : BVExpr 32 := .bin n167 .add n0
  let n169 : BVExpr 32 := .un .not n168
  let n170 : BVExpr 32 := .bin n169 .and n0
  let n171 : BVExpr 32 := .bin n170 .or n1
  let n172 : BVExpr 32 := .bin n171 .xor n0
  let n173 : BVExpr 32 := .bin n172 .add n1
  let n174 : BVExpr 32 := .un .not n173
  let n175 : BVExpr 32 := .bin n174 .and n1
  let n176 : BVExpr 32 := .bin n175 .or n0
  let n177 : BVExpr 32 := .bin n176 .xor n1
  let n178 : BVExpr 32 := .bin n177 .add n0
  let n179 : BVExpr 32 := .un .not n178
  let n180 : BVExpr 32 := .bin n179 .and n0
  let n181 : BVExpr 32 := .bin n180 .or n1
  let n182 : BVExpr 32 := .bin n181 .xor n0
  let n183 : BVExpr 32 := .bin n182 .add n1
  let n184 : BVExpr 32 := .un .not n183
  let n185 : BVExpr 32 := .bin n184 .and n1
  let n186 : BVExpr 32 := .bin n185 .or n0
  let n187 : BVExpr 32 := .bin n186 .xor n1
  let n188 : BVExpr 32 := .bin n187 .add n0
  let n189 : BVExpr 32 := .un .not n188
  let n190 : BVExpr 32 := .bin n189 .and n0
  let n191 : BVExpr 32 := .bin n190 .or n1
  let n192 : BVExpr 32 := .bin n191 .xor n0
  let n193 : BVExpr 32 := .bin n192 .add n1
  let n194 : BVExpr 32 := .un .not n193
  let n195 : BVExpr 32 := .bin n194 .and n1
  let n196 : BVExpr 32 := .bin n195 .or n0
  let n197 : BVExpr 32 := .bin n196 .xor n1
  .not (.literal (.bin n196 .eq n197))

@[expose] def dag200Ws : List Nat :=
  [ 827348546, 1, 2, 200, 1, 199, 0, 0, 1, 32, 0, 32, 1, 1, 32, 0, 0, 0, 0, 32, 0, 0, 0, 6, 32,
    0, 1, 0, 10, 32, 2, 0, 0, 3, 32, 3, 1, 0, 0, 32, 1, 0, 0, 4, 32, 4, 5, 0, 5, 32, 6, 1, 0, 6,
    32, 7, 5, 0, 10, 32, 8, 0, 0, 3, 32, 9, 5, 0, 4, 32, 10, 1, 0, 5, 32, 11, 5, 0, 6, 32, 12, 1,
    0, 10, 32, 13, 0, 0, 3, 32, 14, 1, 0, 4, 32, 15, 5, 0, 5, 32, 16, 1, 0, 6, 32, 17, 5, 0, 10,
    32, 18, 0, 0, 3, 32, 19, 5, 0, 4, 32, 20, 1, 0, 5, 32, 21, 5, 0, 6, 32, 22, 1, 0, 10, 32, 23,
    0, 0, 3, 32, 24, 1, 0, 4, 32, 25, 5, 0, 5, 32, 26, 1, 0, 6, 32, 27, 5, 0, 10, 32, 28, 0, 0,
    3, 32, 29, 5, 0, 4, 32, 30, 1, 0, 5, 32, 31, 5, 0, 6, 32, 32, 1, 0, 10, 32, 33, 0, 0, 3, 32,
    34, 1, 0, 4, 32, 35, 5, 0, 5, 32, 36, 1, 0, 6, 32, 37, 5, 0, 10, 32, 38, 0, 0, 3, 32, 39, 5,
    0, 4, 32, 40, 1, 0, 5, 32, 41, 5, 0, 6, 32, 42, 1, 0, 10, 32, 43, 0, 0, 3, 32, 44, 1, 0, 4,
    32, 45, 5, 0, 5, 32, 46, 1, 0, 6, 32, 47, 5, 0, 10, 32, 48, 0, 0, 3, 32, 49, 5, 0, 4, 32, 50,
    1, 0, 5, 32, 51, 5, 0, 6, 32, 52, 1, 0, 10, 32, 53, 0, 0, 3, 32, 54, 1, 0, 4, 32, 55, 5, 0,
    5, 32, 56, 1, 0, 6, 32, 57, 5, 0, 10, 32, 58, 0, 0, 3, 32, 59, 5, 0, 4, 32, 60, 1, 0, 5, 32,
    61, 5, 0, 6, 32, 62, 1, 0, 10, 32, 63, 0, 0, 3, 32, 64, 1, 0, 4, 32, 65, 5, 0, 5, 32, 66, 1,
    0, 6, 32, 67, 5, 0, 10, 32, 68, 0, 0, 3, 32, 69, 5, 0, 4, 32, 70, 1, 0, 5, 32, 71, 5, 0, 6,
    32, 72, 1, 0, 10, 32, 73, 0, 0, 3, 32, 74, 1, 0, 4, 32, 75, 5, 0, 5, 32, 76, 1, 0, 6, 32, 77,
    5, 0, 10, 32, 78, 0, 0, 3, 32, 79, 5, 0, 4, 32, 80, 1, 0, 5, 32, 81, 5, 0, 6, 32, 82, 1, 0,
    10, 32, 83, 0, 0, 3, 32, 84, 1, 0, 4, 32, 85, 5, 0, 5, 32, 86, 1, 0, 6, 32, 87, 5, 0, 10, 32,
    88, 0, 0, 3, 32, 89, 5, 0, 4, 32, 90, 1, 0, 5, 32, 91, 5, 0, 6, 32, 92, 1, 0, 10, 32, 93, 0,
    0, 3, 32, 94, 1, 0, 4, 32, 95, 5, 0, 5, 32, 96, 1, 0, 6, 32, 97, 5, 0, 10, 32, 98, 0, 0, 3,
    32, 99, 5, 0, 4, 32, 100, 1, 0, 5, 32, 101, 5, 0, 6, 32, 102, 1, 0, 10, 32, 103, 0, 0, 3, 32,
    104, 1, 0, 4, 32, 105, 5, 0, 5, 32, 106, 1, 0, 6, 32, 107, 5, 0, 10, 32, 108, 0, 0, 3, 32,
    109, 5, 0, 4, 32, 110, 1, 0, 5, 32, 111, 5, 0, 6, 32, 112, 1, 0, 10, 32, 113, 0, 0, 3, 32,
    114, 1, 0, 4, 32, 115, 5, 0, 5, 32, 116, 1, 0, 6, 32, 117, 5, 0, 10, 32, 118, 0, 0, 3, 32,
    119, 5, 0, 4, 32, 120, 1, 0, 5, 32, 121, 5, 0, 6, 32, 122, 1, 0, 10, 32, 123, 0, 0, 3, 32,
    124, 1, 0, 4, 32, 125, 5, 0, 5, 32, 126, 1, 0, 6, 32, 127, 5, 0, 10, 32, 128, 0, 0, 3, 32,
    129, 5, 0, 4, 32, 130, 1, 0, 5, 32, 131, 5, 0, 6, 32, 132, 1, 0, 10, 32, 133, 0, 0, 3, 32,
    134, 1, 0, 4, 32, 135, 5, 0, 5, 32, 136, 1, 0, 6, 32, 137, 5, 0, 10, 32, 138, 0, 0, 3, 32,
    139, 5, 0, 4, 32, 140, 1, 0, 5, 32, 141, 5, 0, 6, 32, 142, 1, 0, 10, 32, 143, 0, 0, 3, 32,
    144, 1, 0, 4, 32, 145, 5, 0, 5, 32, 146, 1, 0, 6, 32, 147, 5, 0, 10, 32, 148, 0, 0, 3, 32,
    149, 5, 0, 4, 32, 150, 1, 0, 5, 32, 151, 5, 0, 6, 32, 152, 1, 0, 10, 32, 153, 0, 0, 3, 32,
    154, 1, 0, 4, 32, 155, 5, 0, 5, 32, 156, 1, 0, 6, 32, 157, 5, 0, 10, 32, 158, 0, 0, 3, 32,
    159, 5, 0, 4, 32, 160, 1, 0, 5, 32, 161, 5, 0, 6, 32, 162, 1, 0, 10, 32, 163, 0, 0, 3, 32,
    164, 1, 0, 4, 32, 165, 5, 0, 5, 32, 166, 1, 0, 6, 32, 167, 5, 0, 10, 32, 168, 0, 0, 3, 32,
    169, 5, 0, 4, 32, 170, 1, 0, 5, 32, 171, 5, 0, 6, 32, 172, 1, 0, 10, 32, 173, 0, 0, 3, 32,
    174, 1, 0, 4, 32, 175, 5, 0, 5, 32, 176, 1, 0, 6, 32, 177, 5, 0, 10, 32, 178, 0, 0, 3, 32,
    179, 5, 0, 4, 32, 180, 1, 0, 5, 32, 181, 5, 0, 6, 32, 182, 1, 0, 10, 32, 183, 0, 0, 3, 32,
    184, 1, 0, 4, 32, 185, 5, 0, 5, 32, 186, 1, 0, 6, 32, 187, 5, 0, 10, 32, 188, 0, 0, 3, 32,
    189, 5, 0, 4, 32, 190, 1, 0, 5, 32, 191, 5, 0, 6, 32, 192, 1, 0, 10, 32, 193, 0, 0, 3, 32,
    194, 1, 0, 4, 32, 195, 5, 0, 5, 32, 196, 1, 0, 22, 1, 196, 197, 0, 26, 1, 198, 0, 0 ]


#guard BVProg.encode dag120Expr == some dag120Ws
#guard BVProg.encode dag200Expr == some dag200Ws

theorem kernel_rfl_120 : BVProg.parseWords dag120Ws = some dag120Expr := rfl
theorem kernel_rfl_200 : BVProg.parseWords dag200Ws = some dag200Expr := rfl

/-! ## 3. `Aig` and `Tseitin` Sanity Checks -/

private def sampleAig : Aig :=
  { A := 2
    nodes := #[(2, 4), (3, 5), (6, 4)] }

private def sampleAigFull : Aig :=
  { A := 2
    nodes := #[(2, 4), (3, 5), (6, 8)] }

#guard (coiMark sampleAig 10).toList == [false, true, true, true, false, true]
#guard (coiMark sampleAigFull 10).toList == [false, true, true, true, true, true]
#guard validDimacsB (tseitin sampleAig (coiMark sampleAig 10) 10) == true
#guard ((parseDimacs (encodeDimacs (tseitin sampleAig (coiMark sampleAig 10) 10))).isSome) == true
#guard (tseitin sampleAig (coiMark sampleAig 0) 0).clauses.size == 1

theorem zero_axiom_reflection_smoke
    (hsolve : ∃ e', BVProg.parse (BVProg.wordsToBytesLE smallWs) = some e' ∧ e'.Unsat) :
    smallExpr.Unsat :=
  BVProg.unsat_of_bv_solve_words smallWs smallExpr hsolve kernel_rfl_small

/-! ## 4. Single-Line `#print axioms` Audit (`<= std3`) -/

#print axioms BVProg.parse_wordsToBytesLE
#print axioms BVProg.unsat_of_bv_solve_words
#print axioms Aig.evalLit_extend
#print axioms Aig.pushNode_evalLit
#print axioms SliceDenotes.extend
#print axioms Tseitin.tseitin_sound
#print axioms Tseitin.tseitin_sound_of_clauses
#print axioms Tseitin.validDimacs_tseitin
#print axioms Tseitin.parseDimacs_encodeDimacs_tseitin
#print axioms kernel_rfl_small
#print axioms kernel_rfl_wide_dep
#print axioms kernel_rfl_120
#print axioms kernel_rfl_200
#print axioms zero_axiom_reflection_smoke

end LeanQbeTest.T.BitblastRefTest
