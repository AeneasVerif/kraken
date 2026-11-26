/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InterpKissat
public meta import LeanQbe.T.InterpKissat
public import LeanQbe.T.Examples.Bitblast.Src.Aig
public meta import LeanQbe.T.Examples.Bitblast.Src.Aig
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public meta import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public meta import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Ref.Aig
public meta import LeanQbe.T.Examples.Bitblast.Ref.Aig
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public meta import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Differential Execution & Structural Tests for `Bitblast/Src/OpsShiftMul.lean` (`S4`)

Verifies every Phase-B `BVExpr` C0 bitblaster in `Bitblast/Src/OpsShiftMul.lean`
(`bv_blast_replicate`, `bv_blast_rotl`, `bv_blast_rotr`, `bv_blast_ashrc`, `bv_blast_reverse`,
`bv_blast_shl`, `bv_blast_ushr`, `bv_blast_ashr`, `bv_blast_mul`, `bv_blast_clz`) via
`InterpKissat` (linking `Aig` + `OpsCore` + `OpsShiftMul`) differentially against Lean `BitVec`
and `BVExpr.eval` across widths `w ∈ {0, 1, 2, 3, 4, 8, 16, 32, 64}`, `nw ≠ w` shifts,
`n ≥ w` rotates/ashrC, `replicate 0`, aliasing, const-folding, `clz` all-zeros/MSB-1,
OOM/overflow guards, and single-line `#print axioms` (`<= std3`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

public section

namespace LeanQbeTest.T.BitblastOpsShiftMulTest

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Ref
open Std.Tactic.BVDecide

/-! ## 1. Linked Module & Structural Metadata Checks -/

private def linkedOpsShiftMulModule : LeanQbe.T.Module :=
  { fns := Aig.fns ++ OpsCore.fns ++ OpsShiftMul.fns
    externs := []
    exits := [] }

#guard OpsShiftMul.opsShiftMulFns.length == 12
#guard (OpsShiftMul.fns.map (·.name)) == (OpsShiftMul.opsShiftMulFns.map (·.name))
#guard (OpsShiftMul.fns.map (·.name)).eraseDups.length == OpsShiftMul.fns.length
#guard OpsShiftMul.opsShiftMulModule.checkAcyclic == true
#guard OpsShiftMul.opsShiftMulModule.exits.isEmpty
#guard OpsShiftMul.fns.all (fun f => f.as.length <= 6)
#guard linkedOpsShiftMulModule.checkAcyclic == true
#guard (linkedOpsShiftMulModule.fns.map (·.name)).eraseDups.length ==
  linkedOpsShiftMulModule.fns.length

/-! ## 2. Memory, `BVHdr`, and AIG Evaluation Harness -/

private structure MemCfg where
  aigCap : Nat
  htMask : Nat
  litsCap : Nat

private def medCfg : MemCfg :=
  { aigCap := 2048, htMask := 4095, litsCap := 512 }

private def largeCfg : MemCfg :=
  { aigCap := 24576, htMask := 32767, litsCap := 512 }

private def hdrAddr : BitVec 64 := 0x1000#64
private def aigAddr : BitVec 64 := 0x1100#64

private def htAddr (c : MemCfg) : BitVec 64 :=
  aigAddr + BitVec.ofNat 64 (c.aigCap * 8)

private def litsAddr (c : MemCfg) : BitVec 64 :=
  htAddr c + BitVec.ofNat 64 ((c.htMask + 1) * 4)

private def totalBytes (c : MemCfg) : Nat :=
  0x100 + c.aigCap * 8 + (c.htMask + 1) * 4 + c.litsCap * 4

private def readU8 (m : Mem 64) (a : BitVec 64) : UInt8 :=
  m.getD a 0

private def writeU8 (m : Mem 64) (a : BitVec 64) (b : UInt8) : Mem 64 :=
  m.insert a b

private def readU32 (m : Mem 64) (a : BitVec 64) : BitVec 32 :=
  let b0 := (readU8 m a).toBitVec
  let b1 := (readU8 m (a + 1#64)).toBitVec
  let b2 := (readU8 m (a + 2#64)).toBitVec
  let b3 := (readU8 m (a + 3#64)).toBitVec
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) |||
    (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24)

private def writeU32 (m : Mem 64) (a : BitVec 64) (v : BitVec 32) : Mem 64 :=
  let m := writeU8 m a (UInt8.ofNat (v.toNat &&& 0xFF))
  let m := writeU8 m (a + 1#64) (UInt8.ofNat ((v.toNat >>> 8) &&& 0xFF))
  let m := writeU8 m (a + 2#64) (UInt8.ofNat ((v.toNat >>> 16) &&& 0xFF))
  writeU8 m (a + 3#64) (UInt8.ofNat ((v.toNat >>> 24) &&& 0xFF))

private def writeU64 (m : Mem 64) (a : BitVec 64) (v : BitVec 64) : Mem 64 :=
  let m := writeU32 m a (v.extractLsb' 0 32)
  writeU32 m (a + 4#64) (v.extractLsb' 32 32)

private def hdrAigLen (m : Mem 64) : Nat := (readU32 m (hdrAddr + 100#64)).toNat
private def baseAigLen : Nat := 129
private def hdrGatesLen (m : Mem 64) : Nat := hdrAigLen m - baseAigLen
private def hdrLitsLen (m : Mem 64) : Nat := (readU32 m (hdrAddr + 112#64)).toNat
private def hdrOom (m : Mem 64) : BitVec 32 := readU32 m (hdrAddr + 120#64)

private def writeLits (m : Mem 64) (c : MemCfg) (off : Nat) (ls : List (BitVec 32)) : Mem 64 :=
  Id.run do
    let mut mem := m
    let base := litsAddr c
    let mut i := 0
    for l in ls do
      mem := writeU32 mem (base + BitVec.ofNat 64 ((off + i) * 4)) l
      i := i + 1
    return mem

private def readLits (m : Mem 64) (c : MemCfg) (off w : Nat) : List (BitVec 32) :=
  Id.run do
    let mut acc : Array (BitVec 32) := #[]
    let base := litsAddr c
    for i in [0:w] do
      acc := acc.push (readU32 m (base + BitVec.ofNat 64 ((off + i) * 4)))
    return acc.toList

private def readAigNodes (m : Mem 64) (numAtoms : Nat := 128) : Array (UInt32 × UInt32) :=
  Id.run do
    let start := 1 + numAtoms
    let total := hdrAigLen m
    let mut acc := Array.mkEmpty (total - start)
    for i in [start:total] do
      let addr := aigAddr + BitVec.ofNat 64 (i * 8)
      let lhs := UInt32.ofBitVec (readU32 m addr)
      let rhs := UInt32.ofBitVec (readU32 m (addr + 4#64))
      acc := acc.push (lhs, rhs)
    return acc

private def atomLits (baseAtom w : Nat) (neg : Bool := false) : List (BitVec 32) :=
  (List.range w).map fun i =>
    BitVec.ofNat 32 (2 * (baseAtom + 1 + i) + if neg then 1 else 0)

private def constLits (w : Nat) (x : BitVec w) : List (BitVec 32) :=
  (List.range w).map fun i => if x.getLsbD i then 1#32 else 0#32

private def evalSliceWith (g : Aig) (env : Nat → Bool) (lits : List (BitVec 32)) (w : Nat) :
    BitVec w :=
  let vals := g.evalNodes env
  let bools := lits.map fun l => Aig.evalLitIn vals (UInt32.ofBitVec l)
  Id.run do
    let mut acc : Nat := 0
    let mut i := 0
    for b in bools do
      if b then
        acc := acc ||| (1 <<< i)
      i := i + 1
    return BitVec.ofNat w acc

private def medZeroMem : Mem 64 :=
  (List.replicate (totalBytes medCfg) 0).At hdrAddr

private def largeZeroMem : Mem 64 :=
  (List.replicate (totalBytes largeCfg) 0).At hdrAddr

private def setupHeader (zmem : Mem 64) (c : MemCfg) (numAtoms : Nat) (initFuel : Nat) :
    Option (Mem 64) :=
  let m0 := storeMem zmem c
  match interpModule linkedOpsShiftMulModule initFuel "bv_aig_init"
      [i64, i64, i32, i64, i32, i32] []
      (hdrAddr, aigAddr, BitVec.ofNat 32 c.aigCap, htAddr c,
       BitVec.ofNat 32 c.htMask, BitVec.ofNat 32 numAtoms, ()) m0 with
  | .ok () m1 => some m1
  | _ => none
where
  storeMem (m : Mem 64) (c : MemCfg) : Mem 64 :=
    let m := writeU64 m hdrAddr hdrAddr
    let m := writeU64 m (hdrAddr + 8#64) (hdrAddr + BitVec.ofNat 64 (totalBytes c))
    let m := writeU64 m (hdrAddr + 56#64) (litsAddr c)
    writeU32 m (hdrAddr + 116#64) (BitVec.ofNat 32 c.litsCap)

private def medBaseMem128 : Mem 64 :=
  (setupHeader medZeroMem medCfg 128 80000).getD medZeroMem

private def largeBaseMem128 : Mem 64 :=
  (setupHeader largeZeroMem largeCfg 128 400000).getD largeZeroMem

#guard hdrOom medBaseMem128 == 0#32
#guard readU32 medBaseMem128 (hdrAddr + 104#64) == 2048#32
#guard hdrOom largeBaseMem128 == 0#32
#guard readU32 largeBaseMem128 (hdrAddr + 104#64) == 24576#32

private def allocSlice (m : Mem 64) (cnt : Nat) : Option (BitVec 32 × Mem 64) :=
  match interpModule linkedOpsShiftMulModule 10000 "bv_lits_alloc"
      [i64, i32] [i32] (hdrAddr, BitVec.ofNat 32 cnt, ()) m with
  | .ok (off, ()) m' => some (off, m')
  | _ => none

private def initUnarySymbolic (c : MemCfg) (base : Mem 64) (w : Nat) (neg : Bool := false) :
    Option (Mem 64) :=
  match allocSlice base w with
  | some (0#32, m1) => some (writeLits m1 c 0 (atomLits 0 w neg))
  | _ => none

private def initBinarySymbolic (c : MemCfg) (base : Mem 64) (wx wy : Nat) :
    Option (Mem 64) :=
  match allocSlice base (wx + wy) with
  | some (0#32, m1) =>
    let m2 := writeLits m1 c 0 (atomLits 0 wx)
    some (writeLits m2 c wx (atomLits wx wy))
  | _ => none

private def unaryEnv {w : Nat} (x : BitVec w) (neg : Bool := false) (k : Nat) : Bool :=
  if 1 <= k && k <= w then (x.getLsbD (k - 1)) != neg else false

private def binaryEnv {wx wy : Nat} (x : BitVec wx) (y : BitVec wy) (k : Nat) : Bool :=
  if 1 <= k && k <= wx then x.getLsbD (k - 1)
  else if wx < k && k <= wx + wy then y.getLsbD (k - 1 - wx)
  else false

private def mkAssign2 {wx wy : Nat} (x : BitVec wx) (y : BitVec wy) : BVExpr.Assignment :=
  Lean.RArray.branch 1 (.leaf ⟨x⟩) (.leaf ⟨y⟩)

private def mkAssign1 {w : Nat} (x : BitVec w) : BVExpr.Assignment :=
  Lean.RArray.leaf ⟨x⟩

/-! ## 3. Sample Matrices Across `w ∈ {0, 1, 2, 3, 4, 8, 16, 32, 64}` -/

private def sampleVals : (w : Nat) → List (BitVec w)
  | 0 => [0#0]
  | 1 => [0#1, 1#1]
  | 2 => [0#2, 1#2, 2#2, 3#2]
  | 3 => (List.range 8).map (BitVec.ofNat 3)
  | 4 => (List.range 16).map (BitVec.ofNat 4)
  | w =>
    let allOnes := ~~~(0#w)
    let msb := 1#w <<< (w - 1)
    let altA := BitVec.ofNat w 0xAAAAAAAAAAAAAAAA
    let alt5 := BitVec.ofNat w 0x5555555555555555
    [0#w, 1#w, 2#w, 3#w, BitVec.ofNat w (w - 1), BitVec.ofNat w w,
     msb >>> 1, msb - 1#w, msb, msb ||| 1#w, alt5, altA, allOnes - 1#w, allOnes]

private def sampleShiftAmts : (nw : Nat) → Nat → List (BitVec nw)
  | 0, _ => [0#0]
  | 1, _ => [0#1, 1#1]
  | 2, _ => [0#2, 1#2, 2#2, 3#2]
  | 3, _ => (List.range 8).map (BitVec.ofNat 3)
  | nw, w =>
    let allOnes := ~~~(0#nw)
    let base :=
      [0#nw, 1#nw, 2#nw, BitVec.ofNat nw (w / 2), BitVec.ofNat nw (w - 1),
       BitVec.ofNat nw w, BitVec.ofNat nw (w + 1), BitVec.ofNat nw (w + 7),
       1#nw <<< (nw - 1), allOnes]
    if nw > 32 then
      base ++ [BitVec.ofNat nw (1 <<< 32), BitVec.ofNat nw ((1 <<< 32) + 3)]
    else
      base

private def sampleConstNats (w : Nat) : List Nat :=
  [0, 1, 2, w / 2, w - 1, w, w + 1, 2 * w + 3, 0xFFFFFFFE, 0xFFFFFFFF]

private def sampleMulPairs (w : Nat) : List (BitVec w × BitVec w) :=
  if w <= 4 then
    let xs := sampleVals w
    xs.flatMap fun x => xs.map fun y => (x, y)
  else if w <= 16 then
    let xs := sampleVals w
    xs.flatMap fun x => xs.map fun y => (x, y)
  else
    let allOnes := ~~~(0#w)
    let msb := 1#w <<< (w - 1)
    let altA := BitVec.ofNat w 0xAAAAAAAAAAAAAAAA
    let alt5 := BitVec.ofNat w 0x5555555555555555
    let xs := [0#w, 1#w, 2#w, 3#w, msb - 1#w, msb, alt5, altA, allOnes - 1#w, allOnes]
    let ys := [0#w, 1#w, 2#w, 7#w, msb, altA, allOnes - 1#w, allOnes]
    xs.flatMap fun x => ys.map fun y => (x, y)

/-! ## 4. Differential Checks: Replicate, Rotate, AshrC, Reverse -/

private def checkReplicate (aw n : Nat) (neg : Bool := false) : Bool :=
  match initUnarySymbolic medCfg medBaseMem128 aw neg with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule 50000 "bv_blast_replicate"
        [i64, i32, i32, i32] [i32]
        (hdrAddr, 0#32, BitVec.ofNat 32 aw, BitVec.ofNat 32 n, ()) m0 with
    | .ok (out, ()) m1 =>
      let outW := aw * n
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 aw ||
         hdrGatesLen m1 != 0 || hdrLitsLen m1 != aw + outW then
        false
      else
        let g : Aig := { A := 128, nodes := #[] }
        let lits := readLits m1 medCfg out.toNat outW
        (sampleVals aw).all fun x =>
          let got := evalSliceWith g (unaryEnv x neg) lits outW
          let expected : BitVec outW :=
            BVExpr.eval (mkAssign1 x) (.replicate n (.var 0 : BVExpr aw) rfl)
          got == (x.replicate n) && got == expected
    | _ => false

#guard [0, 1, 2, 3, 4, 8, 16].all fun aw =>
  [0, 1, 2, 3, 4].all fun n => checkReplicate aw n
#guard checkReplicate 8 8
#guard checkReplicate 32 2
#guard checkReplicate 64 0
#guard checkReplicate 64 1
#guard checkReplicate 8 3 true

private def checkUnaryNatOp (fnName : String) (w n : Nat)
    (specFn : BitVec w → Nat → BitVec w)
    (exprFn : BVExpr w → BVExpr w)
    (neg : Bool := false) : Bool :=
  match initUnarySymbolic medCfg medBaseMem128 w neg with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule 80000 fnName
        [i64, i32, i32, i32] [i32]
        (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 n, ()) m0 with
    | .ok (out, ()) m1 =>
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 w ||
         hdrGatesLen m1 != 0 || hdrLitsLen m1 != 2 * w then
        false
      else
        let g : Aig := { A := 128, nodes := #[] }
        let lits := readLits m1 medCfg out.toNat w
        (sampleVals w).all fun x =>
          let got := evalSliceWith g (unaryEnv x neg) lits w
          let expected := BVExpr.eval (mkAssign1 x) (exprFn (.var 0))
          got == specFn x n && got == expected
    | _ => false

private def checkReverse (w : Nat) (neg : Bool := false) : Bool :=
  match initUnarySymbolic medCfg medBaseMem128 w neg with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule 80000 "bv_blast_reverse"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, BitVec.ofNat 32 w, ()) m0 with
    | .ok (out, ()) m1 =>
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 w ||
         hdrGatesLen m1 != 0 || hdrLitsLen m1 != 2 * w then
        false
      else
        let g : Aig := { A := 128, nodes := #[] }
        let lits := readLits m1 medCfg out.toNat w
        (sampleVals w).all fun x =>
          let got := evalSliceWith g (unaryEnv x neg) lits w
          let expected := BVExpr.eval (mkAssign1 x) (.un .reverse (.var 0 : BVExpr w))
          got == x.reverse && got == expected
    | _ => false

private def allWidths : List Nat := [0, 1, 2, 3, 4, 8, 16, 32, 64]

#guard allWidths.all fun w =>
  (sampleConstNats w).all fun n =>
    checkUnaryNatOp "bv_blast_rotl" w n BitVec.rotateLeft (.un (.rotateLeft n)) &&
    checkUnaryNatOp "bv_blast_rotr" w n BitVec.rotateRight (.un (.rotateRight n)) &&
    checkUnaryNatOp "bv_blast_ashrc" w n BitVec.sshiftRight (.un (.arithShiftRightConst n))

#guard checkUnaryNatOp "bv_blast_rotl" 8 11 BitVec.rotateLeft (.un (.rotateLeft 11)) true
#guard checkUnaryNatOp "bv_blast_rotr" 8 11 BitVec.rotateRight (.un (.rotateRight 11)) true
#guard checkUnaryNatOp "bv_blast_ashrc" 8 5 BitVec.sshiftRight (.un (.arithShiftRightConst 5)) true
#guard allWidths.all fun w => checkReverse w
#guard checkReverse 16 true

/-! ## 5. Differential Checks: Variable Shifts (`shl`, `ushr`, `ashr`) -/

private def safeShl {w nw : Nat} (x : BitVec w) (y : BitVec nw) : BitVec w :=
  if y.toNat < w then x <<< y.toNat else 0#w

private def safeUshr {w nw : Nat} (x : BitVec w) (y : BitVec nw) : BitVec w :=
  if y.toNat < w then x >>> y.toNat else 0#w

private def safeAshr {w nw : Nat} (x : BitVec w) (y : BitVec nw) : BitVec w :=
  if y.toNat < w then x.sshiftRight y.toNat
  else if x.msb then ~~~(0#w) else 0#w

private def checkShiftVar (fnName : String) (w nw : Nat)
    (specFn : BitVec w → BitVec nw → BitVec w)
    (exprFn : BVExpr w → BVExpr nw → BVExpr w) : Bool :=
  match initBinarySymbolic medCfg medBaseMem128 w nw with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule 400000 fnName
        [i64, i32, i32, i32, i32] [i32]
        (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, BitVec.ofNat 32 nw, ()) m0 with
    | .ok (out, ()) m1 =>
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 (w + nw) ||
         hdrLitsLen m1 != w + nw + w then
        false
      else
        let g : Aig := { A := 128, nodes := readAigNodes m1 128 }
        let lits := readLits m1 medCfg out.toNat w
        let xs := sampleVals w
        let ys := sampleShiftAmts nw w
        xs.all fun x => ys.all fun y =>
          let got := evalSliceWith g (binaryEnv x y) lits w
          let exprOk :=
            if y.toNat < 0x80000000 then
              got == BVExpr.eval (mkAssign2 x y) (exprFn (.var 0) (.var 1))
            else
              true
          got == specFn x y && exprOk
    | _ => false

private def mixedShiftPairs : List (Nat × Nat) :=
  [(0, 0), (0, 4), (1, 0), (1, 1), (1, 8), (2, 1), (2, 8), (3, 2), (3, 5),
   (4, 2), (4, 8), (8, 3), (8, 16), (16, 4), (16, 32), (32, 5), (32, 64),
   (64, 4), (64, 6)]

#guard allWidths.all fun w =>
  checkShiftVar "bv_blast_shl" w w safeShl .shiftLeft &&
  checkShiftVar "bv_blast_ushr" w w safeUshr .shiftRight &&
  checkShiftVar "bv_blast_ashr" w w safeAshr .arithShiftRight

#guard mixedShiftPairs.all fun (w, nw) =>
  checkShiftVar "bv_blast_shl" w nw safeShl .shiftLeft &&
  checkShiftVar "bv_blast_ushr" w nw safeUshr .shiftRight &&
  checkShiftVar "bv_blast_ashr" w nw safeAshr .arithShiftRight

#guard checkShiftVar "bv_blast_shl" 64 64 safeShl .shiftLeft
#guard checkShiftVar "bv_blast_ushr" 64 64 safeUshr .shiftRight
#guard checkShiftVar "bv_blast_ashr" 64 64 safeAshr .arithShiftRight

-- Aliasing (`a_off == b_off`) and const-folding for variable shifts
private def checkShiftAliasAndConst (fnName : String) (w : Nat)
    (specFn : BitVec w → BitVec w → BitVec w) : Bool :=
  let aliasOk :=
    match initUnarySymbolic medCfg medBaseMem128 w false with
    | none => false
    | some m0 =>
      match interpModule linkedOpsShiftMulModule 300000 fnName
          [i64, i32, i32, i32, i32] [i32]
          (hdrAddr, 0#32, BitVec.ofNat 32 w, 0#32, BitVec.ofNat 32 w, ()) m0 with
      | .ok (out, ()) m1 =>
        if hdrOom m1 != 0#32 || hdrLitsLen m1 != 2 * w then false
        else
          let g : Aig := { A := 128, nodes := readAigNodes m1 128 }
          let lits := readLits m1 medCfg out.toNat w
          (sampleVals w).all fun x =>
            evalSliceWith g (unaryEnv x) lits w == specFn x x
      | _ => false
  let constOk :=
    match allocSlice medBaseMem128 (2 * w) with
    | some (0#32, m1) =>
      let xv := BitVec.ofNat w 0xA55A1234
      let yv := BitVec.ofNat w 5
      let m2 := writeLits (writeLits m1 medCfg 0 (constLits w xv)) medCfg w (constLits w yv)
      match interpModule linkedOpsShiftMulModule 100000 fnName
          [i64, i32, i32, i32, i32] [i32]
          (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ()) m2 with
      | .ok (out, ()) m3 =>
        hdrOom m3 == 0#32 && hdrGatesLen m3 == 0 &&
          evalSliceWith { A := 128, nodes := #[] } (fun _ => false)
            (readLits m3 medCfg out.toNat w) w == specFn xv yv
      | _ => false
    | _ => false
  aliasOk && constOk

#guard [0, 1, 4, 8, 16, 32, 64].all fun w =>
  checkShiftAliasAndConst "bv_blast_shl" w safeShl &&
  checkShiftAliasAndConst "bv_blast_ushr" w safeUshr &&
  checkShiftAliasAndConst "bv_blast_ashr" w safeAshr

/-! ## 6. Differential Checks: Multiply (`bv_blast_mul`) -/

private def checkMul (c : MemCfg) (base : Mem 64) (w fuel : Nat) : Bool :=
  match initBinarySymbolic c base w w with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule fuel "bv_blast_mul"
        [i64, i32, i32, i32] [i32]
        (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ()) m0 with
    | .ok (out, ()) m1 =>
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 (2 * w) ||
         hdrLitsLen m1 != 3 * w then
        false
      else
        let g : Aig := { A := 128, nodes := readAigNodes m1 128 }
        let lits := readLits m1 c out.toNat w
        (sampleMulPairs w).all fun (x, y) =>
          let got := evalSliceWith g (binaryEnv x y) lits w
          let expected := BVExpr.eval (mkAssign2 x y) (.bin (.var 0 : BVExpr w) .mul (.var 1))
          got == (x * y) && got == expected
    | _ => false

private def checkMulAliasAndConst (c : MemCfg) (base : Mem 64) (w fuel : Nat) : Bool :=
  let aliasOk :=
    match initUnarySymbolic c base w false with
    | none => false
    | some m0 =>
      match interpModule linkedOpsShiftMulModule fuel "bv_blast_mul"
          [i64, i32, i32, i32] [i32]
          (hdrAddr, 0#32, 0#32, BitVec.ofNat 32 w, ()) m0 with
      | .ok (out, ()) m1 =>
        if hdrOom m1 != 0#32 || hdrLitsLen m1 != 2 * w then false
        else
          let g : Aig := { A := 128, nodes := readAigNodes m1 128 }
          let lits := readLits m1 c out.toNat w
          (sampleVals w).all fun x => evalSliceWith g (unaryEnv x) lits w == x * x
      | _ => false
  let constOk :=
    match allocSlice base (2 * w) with
    | some (0#32, m1) =>
      let xv := BitVec.ofNat w 0x13579BDF02468ACE
      let yv := BitVec.ofNat w 0x0FEDCBA987654321
      let m2 := writeLits (writeLits m1 c 0 (constLits w xv)) c w (constLits w yv)
      match interpModule linkedOpsShiftMulModule fuel "bv_blast_mul"
          [i64, i32, i32, i32] [i32]
          (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ()) m2 with
      | .ok (out, ()) m3 =>
        hdrOom m3 == 0#32 && hdrGatesLen m3 == 0 &&
          evalSliceWith { A := 128, nodes := #[] } (fun _ => false)
            (readLits m3 c out.toNat w) w == xv * yv
      | _ => false
    | _ => false
  aliasOk && constOk

#guard [0, 1, 2, 3, 4, 8].all fun w => checkMul medCfg medBaseMem128 w 400000
#guard checkMul medCfg medBaseMem128 16 1200000
#guard checkMul largeCfg largeBaseMem128 32 4000000
#guard checkMul largeCfg largeBaseMem128 64 12000000
#guard [0, 1, 4, 8, 16].all fun w => checkMulAliasAndConst medCfg medBaseMem128 w 1200000
#guard checkMulAliasAndConst largeCfg largeBaseMem128 32 4000000
#guard checkMulAliasAndConst largeCfg largeBaseMem128 64 12000000

/-! ## 7. Differential Checks: Count Leading Zeros (`bv_blast_clz`) -/

private def sampleClzVals (w : Nat) : List (BitVec w) :=
  if w <= 8 then
    (List.range (1 <<< w)).map (BitVec.ofNat w)
  else
    let pows := (List.range w).map fun k => 1#w <<< k
    [0#w, ~~~(0#w), (1#w <<< (w - 1)) ||| 1#w] ++ pows ++ sampleVals w

private def checkClz (w : Nat) (neg : Bool := false) : Bool :=
  match initUnarySymbolic medCfg medBaseMem128 w neg with
  | none => false
  | some m0 =>
    match interpModule linkedOpsShiftMulModule 400000 "bv_blast_clz"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, BitVec.ofNat 32 w, ()) m0 with
    | .ok (out, ()) m1 =>
      if hdrOom m1 != 0#32 || out != BitVec.ofNat 32 w || hdrLitsLen m1 != 2 * w then
        false
      else
        let g : Aig := { A := 128, nodes := readAigNodes m1 128 }
        let lits := readLits m1 medCfg out.toNat w
        (sampleClzVals w).all fun x =>
          let got := evalSliceWith g (unaryEnv x neg) lits w
          let expected := BVExpr.eval (mkAssign1 x) (.un .clz (.var 0 : BVExpr w))
          got == x.clz && got == expected
    | _ => false

private def checkClzConst (w : Nat) (x : BitVec w) : Bool :=
  match allocSlice medBaseMem128 w with
  | some (0#32, m1) =>
    let m2 := writeLits m1 medCfg 0 (constLits w x)
    match interpModule linkedOpsShiftMulModule 100000 "bv_blast_clz"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, BitVec.ofNat 32 w, ()) m2 with
    | .ok (out, ()) m3 =>
      hdrOom m3 == 0#32 && hdrGatesLen m3 == 0 &&
        evalSliceWith { A := 128, nodes := #[] } (fun _ => false)
          (readLits m3 medCfg out.toNat w) w == x.clz
    | _ => false
  | _ => false

#guard allWidths.all fun w => checkClz w
#guard checkClz 8 true
#guard checkClz 64 true
#guard allWidths.all fun w =>
  checkClzConst w 0#w && checkClzConst w 1#w &&
    checkClzConst w (if w == 0 then 0#w else 1#w <<< (w - 1))

/-! ## 8. Error, OOM, and Overflow Guard Checks -/

private def expectOomFail (fnName : String) (as : List Ty) (args : Tup Val as)
    (m : Mem 64) (expectedLitsLen : Option Nat := none) : Bool :=
  match interpModule linkedOpsShiftMulModule 500000 fnName as [i32] args m with
  | .ok (ret, ()) m' =>
    ret == 0xFFFFFFFF#32 && hdrOom m' == 1#32 &&
      match expectedLitsLen with
      | some n => hdrLitsLen m' == n
      | none => true
  | _ => false

private def oomSetMem : Mem 64 :=
  writeU32 medBaseMem128 (hdrAddr + 120#64) 1#32

private def exactSliceMem (w aigCapVal litsCapVal : Nat) (numAtoms : Nat := w) : Mem 64 :=
  let c : MemCfg := { medCfg with aigCap := aigCapVal, litsCap := litsCapVal }
  match setupHeader medZeroMem c numAtoms 80000 with
  | some m1 =>
    match allocSlice m1 w with
    | some (0#32, m2) => writeLits m2 c 0 (atomLits 0 w)
    | _ => m1
  | none => medZeroMem

#guard hdrOom (exactSliceMem 8 128 100) == 0#32
#guard hdrOom (exactSliceMem 4 6 64) == 0#32
#guard hdrOom (exactSliceMem 8 10 64) == 0#32

-- Pre-existing `h->oom != 0` short-circuits cleanly
#guard expectOomFail "bv_blast_replicate" [i64, i32, i32, i32] (hdrAddr, 0#32, 0#32, 0#32, ())
  oomSetMem
#guard expectOomFail "bv_blast_rotl" [i64, i32, i32, i32] (hdrAddr, 0#32, 0#32, 0#32, ())
  oomSetMem
#guard expectOomFail "bv_blast_rotr" [i64, i32, i32, i32] (hdrAddr, 0#32, 0#32, 0#32, ())
  oomSetMem
#guard expectOomFail "bv_blast_ashrc" [i64, i32, i32, i32] (hdrAddr, 0#32, 0#32, 0#32, ())
  oomSetMem
#guard expectOomFail "bv_blast_reverse" [i64, i32, i32] (hdrAddr, 0#32, 0#32, ()) oomSetMem
#guard expectOomFail "bv_blast_shl" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 0#32, 0#32, 0#32, ()) oomSetMem
#guard expectOomFail "bv_blast_ushr" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 0#32, 0#32, 0#32, ()) oomSetMem
#guard expectOomFail "bv_blast_ashr" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 0#32, 0#32, 0#32, ()) oomSetMem
#guard expectOomFail "bv_blast_mul" [i64, i32, i32, i32] (hdrAddr, 0#32, 0#32, 0#32, ())
  oomSetMem
#guard expectOomFail "bv_blast_clz" [i64, i32, i32] (hdrAddr, 0#32, 0#32, ()) oomSetMem

-- Out-of-bounds / u32-wraparound input slices
#guard expectOomFail "bv_blast_replicate" [i64, i32, i32, i32]
  (hdrAddr, 0xFFFFFFF0#32, 32#32, 1#32, ()) medBaseMem128
#guard expectOomFail "bv_blast_rotl" [i64, i32, i32, i32] (hdrAddr, 0#32, 1#32, 0#32, ())
  medBaseMem128
#guard expectOomFail "bv_blast_shl" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 4#32, 0xFFFFFFF8#32, 16#32, ()) (exactSliceMem 8 128 100)
#guard expectOomFail "bv_blast_mul" [i64, i32, i32, i32]
  (hdrAddr, 0#32, 4#32, 8#32, ()) (exactSliceMem 8 128 100)

-- Replicate `u32` multiplication overflow guard (`aw * n >= 2^32`)
#guard expectOomFail "bv_blast_replicate" [i64, i32, i32, i32]
  (hdrAddr, 0#32, 256#32, 0x01000000#32, ()) (exactSliceMem 256 512 512)

-- Invalid `op` passed directly to `bv_blast_shift_var`
#guard expectOomFail "bv_blast_shift_var" [i64, i32, i32, i32, i32, i32]
  (hdrAddr, 0#32, 4#32, 0#32, 4#32, 99#32, ()) (exactSliceMem 4 128 100)

-- `lits_cap` exhaustion on `out` and inside `tmp` / `shifted` (no literal leak after release)
#guard expectOomFail "bv_blast_reverse" [i64, i32, i32]
  (hdrAddr, 0#32, 8#32, ()) (exactSliceMem 8 128 8) (some 8)
#guard expectOomFail "bv_blast_shl" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 4#32, 0#32, 4#32, ()) (exactSliceMem 4 128 8) (some 8)
#guard expectOomFail "bv_blast_mul" [i64, i32, i32, i32]
  (hdrAddr, 0#32, 0#32, 4#32, ()) (exactSliceMem 4 128 8) (some 8)

-- `aig_cap` exhaustion mid-circuit (`1` free AND slot, `bv_aig_ite` / `bv_mk_and`)
#guard expectOomFail "bv_blast_shl" [i64, i32, i32, i32, i32]
  (hdrAddr, 0#32, 4#32, 0#32, 4#32, ()) (exactSliceMem 4 6 64) (some 8)
#guard expectOomFail "bv_blast_mul" [i64, i32, i32, i32]
  (hdrAddr, 0#32, 0#32, 4#32, ()) (exactSliceMem 4 6 64) (some 8)
#guard expectOomFail "bv_blast_clz" [i64, i32, i32]
  (hdrAddr, 0#32, 8#32, ()) (exactSliceMem 8 10 64) (some 16)

/-! ## 9. Single-Line `#print axioms` Audit (`<= std3`, `< 115c`) -/

theorem audit_copy_wf : OpsShiftMul.bv_copy_lits_body.Wf := OpsShiftMul.bv_copy_lits_wf
theorem audit_replicate_wf : OpsShiftMul.bv_blast_replicate_body.Wf :=
  OpsShiftMul.bv_blast_replicate_wf
theorem audit_rotl_wf : OpsShiftMul.bv_blast_rotl_body.Wf := OpsShiftMul.bv_blast_rotl_wf
theorem audit_rotr_wf : OpsShiftMul.bv_blast_rotr_body.Wf := OpsShiftMul.bv_blast_rotr_wf
theorem audit_ashrc_wf : OpsShiftMul.bv_blast_ashrc_body.Wf := OpsShiftMul.bv_blast_ashrc_wf
theorem audit_reverse_wf : OpsShiftMul.bv_blast_reverse_body.Wf :=
  OpsShiftMul.bv_blast_reverse_wf
theorem audit_shift_var_wf : OpsShiftMul.bv_blast_shift_var_body.Wf :=
  OpsShiftMul.bv_blast_shift_var_wf
theorem audit_shl_wf : OpsShiftMul.bv_blast_shl_body.Wf := OpsShiftMul.bv_blast_shl_wf
theorem audit_ushr_wf : OpsShiftMul.bv_blast_ushr_body.Wf := OpsShiftMul.bv_blast_ushr_wf
theorem audit_ashr_wf : OpsShiftMul.bv_blast_ashr_body.Wf := OpsShiftMul.bv_blast_ashr_wf
theorem audit_mul_wf : OpsShiftMul.bv_blast_mul_body.Wf := OpsShiftMul.bv_blast_mul_wf
theorem audit_clz_wf : OpsShiftMul.bv_blast_clz_body.Wf := OpsShiftMul.bv_blast_clz_wf
theorem audit_ops_shift_mul_wf : ∀ f ∈ OpsShiftMul.fns, f.Wf := OpsShiftMul.fns_wf
theorem audit_ops_shift_mul_acyclic : OpsShiftMul.opsShiftMulModule.checkAcyclic = true :=
  OpsShiftMul.opsShiftMul_checkAcyclic

#print axioms audit_ops_shift_mul_wf
#print axioms audit_ops_shift_mul_acyclic

end LeanQbeTest.T.BitblastOpsShiftMulTest
