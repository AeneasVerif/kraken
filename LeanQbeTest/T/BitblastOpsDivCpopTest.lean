/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.InterpKissat
import LeanQbe.T.Examples.Bitblast.Src.Aig
import LeanQbe.T.Examples.Bitblast.Src.OpsCore
import LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
import LeanQbe.T.Examples.Bitblast.Ref.Aig
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.Examples.Bitblast.Src.Aig
meta import LeanQbe.T.Examples.Bitblast.Src.OpsCore
meta import LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
meta import LeanQbe.T.Examples.Bitblast.Ref.Aig
meta import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Differential `Interp` Tests & Axiom Audit for `Bitblast/Src/OpsDivCpop.lean` (`S5`)

Links `Aig.fns ++ OpsCore.fns ++ OpsDivCpop.fns` via `interpModule` and differentially compares
all Phase-B `S5` operations (`bv_blast_udiv`, `bv_blast_umod`, `bv_blast_cpop`) and helpers
(`bv_blast_sub_with_borrow`, `bv_blast_ite_slice`) against `Std.Tactic.BVDecide.BVExpr.eval` /
`BitVec.udiv` / `BitVec.umod` / `BitVec.cpop` across `w = 0, 1, 2, 3, 4, 8, 16, 32, 64`,
including `d = 0`, `d = 1`, `n < d`, `n = d`, max-uint, all-zeros, all-ones, aliasing,
constant folding, and OOM/overflow guards, plus `#print axioms` (`<= std3`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BitblastOpsDivCpopTest

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.Bitblast
open LeanQbe.T.Examples.Bitblast.Src

private def linkedAigDivCpopModule : Module :=
  { fns := Aig.fns ++ OpsCore.fns ++ OpsDivCpop.fns
    externs := []
    exits := [] }

#guard OpsDivCpop.opsDivCpopFns.map Fn.name == OpsDivCpop.fns.map Fn.name
theorem opsDivCpopFns_eq_fns : OpsDivCpop.opsDivCpopFns = OpsDivCpop.fns := rfl
#guard OpsDivCpop.opsDivCpopFns.length == 9
#guard (OpsDivCpop.opsDivCpopFns.map Fn.name).eraseDups.length == 9
#guard OpsDivCpop.opsDivCpopModule.checkAcyclic == true
#guard OpsDivCpop.opsDivCpopModule.exits.isEmpty
#guard OpsDivCpop.opsDivCpopFns.all (fun f => f.as.length <= 6)
#guard linkedAigDivCpopModule.checkAcyclic == true

private def hdrAddr : BitVec 64 := 0x1000#64
private def aigAddr : BitVec 64 := 0x1100#64

private structure MemCfg where
  aigCap : Nat
  htMask : Nat
  litsCap : Nat

private def MemCfg.htAddr (c : MemCfg) : BitVec 64 :=
  aigAddr + BitVec.ofNat 64 (8 * c.aigCap)

private def MemCfg.litsAddr (c : MemCfg) : BitVec 64 :=
  c.htAddr + BitVec.ofNat 64 (4 * (c.htMask + 1))

private def MemCfg.totalBytes (c : MemCfg) : Nat :=
  0x100 + 8 * c.aigCap + 4 * (c.htMask + 1) + 4 * c.litsCap

private def cfgFor (w : Nat) : MemCfg :=
  if w ≤ 8 then { aigCap := 1024, htMask := 127, litsCap := 128 }
  else { aigCap := 4096, htMask := 255, litsCap := 512 }

private def cfgCpop (w : Nat) : MemCfg :=
  if w ≤ 16 then cfgFor w
  else if w ≤ 32 then { aigCap := 512, htMask := 127, litsCap := 1600 }
  else { aigCap := 1024, htMask := 255, litsCap := 6400 }

private def cfgDiv32 : MemCfg := { aigCap := 13000, htMask := 127, litsCap := 256 }
private def cfgConstDiv : MemCfg := { aigCap := 32, htMask := 15, litsCap := 512 }
private def cfgConstCpop : MemCfg := { aigCap := 32, htMask := 15, litsCap := 6400 }

private def readMemU32 (m : Mem 64) (addr : BitVec 64) : Option UInt32 :=
  match loadVal m i32 addr with
  | some v => some (UInt32.ofBitVec v)
  | none => none

private def readU32Slice (m : Mem 64) (base : BitVec 64) (off len : Nat) :
    Option (List UInt32) :=
  go len 0 []
where
  go : Nat → Nat → List UInt32 → Option (List UInt32)
    | 0, _, acc => some acc.reverse
    | n + 1, j, acc =>
      match readMemU32 m (base + BitVec.ofNat 64 (4 * (off + j))) with
      | some v => go n (j + 1) (v :: acc)
      | none => none

private def writeU32Slice (m : Mem 64) (base : BitVec 64) (off : Nat) (ls : List UInt32) :
    Mem 64 :=
  (ls.zipIdx).foldl (fun acc (v, j) =>
    storeMem acc i32 (base + BitVec.ofNat 64 (4 * (off + j))) v.toBitVec) m

private def readAig (m : Mem 64) (numAtoms : Nat) : Option Ref.Aig := do
  let aigLen ← readMemU32 m (hdrAddr + 100)
  let len := aigLen.toNat
  if len < numAtoms + 1 then none
  let nGates := len - (numAtoms + 1)
  let mut nodes : Array (UInt32 × UInt32) := Array.mkEmpty nGates
  for i in [0:nGates] do
    let addr := aigAddr + BitVec.ofNat 64 (8 * (numAtoms + 1 + i))
    let some v := loadVal m i64 addr | none
    let n := v.toNat
    let lhs := UInt32.ofNat (n % 4294967296)
    let rhs := UInt32.ofNat (n / 4294967296)
    nodes := nodes.push (lhs, rhs)
  pure { A := numAtoms, nodes := nodes }

private def aigWfB (g : Ref.Aig) : Bool :=
  (List.range g.nodes.size).all fun i =>
    match g.nodes[i]? with
    | some (l, r) => (l >>> 1).toNat < g.A + 1 + i && (r >>> 1).toNat < g.A + 1 + i
    | none => false

private def initAigSliceMem (cfg : MemCfg) (wx wy : Nat)
    (xLits? : Option (List UInt32) := none)
    (yLits? : Option (List UInt32) := none)
    (numAtomsOverride? : Option Nat := none) : Option (Mem 64 × Nat) := do
  let numAtoms := numAtomsOverride?.getD (wx + wy)
  let m0 : Mem 64 := (List.replicate cfg.totalBytes 0).At hdrAddr
  let m1 := storeMem m0 i64 (hdrAddr + 0) hdrAddr
  let m2 := storeMem m1 i64 (hdrAddr + 8) (hdrAddr + BitVec.ofNat 64 cfg.totalBytes)
  let m3 := storeMem m2 i64 (hdrAddr + 56) cfg.litsAddr
  let m4 := storeMem m3 i32 (hdrAddr + 116) (BitVec.ofNat 32 cfg.litsCap)
  let initArgs : Tup Val [i64, i64, i32, i64, i32, i32] :=
    (hdrAddr, aigAddr, BitVec.ofNat 32 cfg.aigCap, cfg.htAddr,
      BitVec.ofNat 32 cfg.htMask, BitVec.ofNat 32 numAtoms, ())
  let m5 ← match interpModule linkedAigDivCpopModule 500000 "bv_aig_init"
      [i64, i64, i32, i64, i32, i32] [] initArgs m4 with
    | .ok _ m' => some m'
    | _ => none
  let xl := xLits?.getD ((List.range wx).map fun j => UInt32.ofNat (2 * (1 + j)))
  let yl := yLits?.getD ((List.range wy).map fun j => UInt32.ofNat (2 * (1 + wx + j)))
  if xl.length != wx || yl.length != wy then none
  let totLits := wx + wy
  let m6 ← match interpModule linkedAigDivCpopModule 5000 "bv_lits_alloc"
      [i64, i32] [i32] (hdrAddr, BitVec.ofNat 32 totLits, ()) m5 with
    | .ok (off, ()) m' =>
      if off == 0#32 then some m' else none
    | _ => none
  let m7 := writeU32Slice m6 cfg.litsAddr 0 xl
  let m8 := writeU32Slice m7 cfg.litsAddr wx yl
  some (m8, numAtoms)

private def atomEnv {wx wy : Nat} (xv : BitVec wx) (yv : BitVec wy) (n : Nat) : Bool :=
  if 1 ≤ n && n ≤ wx then xv.getLsbD (n - 1)
  else if wx < n && n ≤ wx + wy then yv.getLsbD (n - 1 - wx)
  else false

private def mkAssign {wx wy : Nat} (xv : BitVec wx) (yv : BitVec wy) : BVExpr.Assignment :=
  Lean.RArray.branch 1 (.leaf ⟨xv⟩) (.leaf ⟨yv⟩)

private def sampleVals (w : Nat) : List (BitVec w) :=
  let raw : List Nat :=
    [0, 1, 2, 3, 5, 0x55, 0xAA, 0x1234, 0x5555, 0xAAAA,
     0x5555555555555555, 0xAAAAAAAAAAAAAAAA]
  let extra : List (BitVec w) :=
    if w == 0 then [BitVec.ofNat w 0]
    else
      [ 0#w, 1#w, BitVec.allOnes w, BitVec.allOnes w - 1#w,
        BitVec.ofNat w (1 <<< (w - 1)), BitVec.ofNat w ((1 <<< (w - 1)) - 1) ]
  (extra ++ raw.map (BitVec.ofNat w)).eraseDups

private def samplePairs (wx wy : Nat) : List (BitVec wx × BitVec wy) :=
  if wx ≤ 3 && wy ≤ 3 then
    (List.range (1 <<< wx)).flatMap fun x =>
      (List.range (1 <<< wy)).map fun y => (BitVec.ofNat wx x, BitVec.ofNat wy y)
  else
    let xs := sampleVals wx
    let ys := sampleVals wy
    xs.flatMap fun x => ys.map fun y => (x, y)

private def edgePairs (w : Nat) : List (BitVec w × BitVec w) :=
  if w == 0 then [(0#w, 0#w)]
  else
    let maxU := BitVec.allOnes w
    let msb := BitVec.ofNat w (1 <<< (w - 1))
    let alt5 := BitVec.ofNat w 0x5555555555555555
    let altA := BitVec.ofNat w 0xAAAAAAAAAAAAAAAA
    [ (0#w, 0#w), (1#w, 0#w), (maxU, 0#w),
      (0#w, 1#w), (maxU, 1#w), (msb, 1#w),
      (0#w, maxU), (maxU - 1#w, maxU), (maxU, maxU),
      (msb - 1#w, msb), (msb, msb), (alt5, altA), (altA, 7#w) ]

private def runCheckOnMem {wx wy outW : Nat} (cfg : MemCfg) (fuel : Nat) (m0 : Mem 64)
    (numAtoms : Nat) (pairs : List (BitVec wx × BitVec wy)) (fnName : Sym) (as : List Ty)
    (args : Tup Val as) (expr : BVExpr outW) : Bool :=
  match interpModule linkedAigDivCpopModule fuel fnName as [i32] args m0 with
  | .ok (outOffBV, ()) m1 =>
    match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
        readAig m1 numAtoms with
    | some 0, some litsLen, some g =>
      let outOff := outOffBV.toNat
      if outOff + outW != litsLen.toNat || !aigWfB g then false
      else
        match readU32Slice m1 cfg.litsAddr outOff outW with
        | none => false
        | some outLits =>
          pairs.all fun (xv, yv) =>
            let vals := g.evalNodes (atomEnv xv yv)
            let expected := BVExpr.eval (mkAssign xv yv) expr
            (List.range outW).all fun i =>
              Ref.Aig.evalLitIn vals (outLits.getD i 0) == expected.getLsbD i
    | _, _, _ => false
  | _ => false

private def checkDivModPair (cfg : MemCfg) (fuel : Nat) (w : Nat)
    (pairs : List (BitVec w × BitVec w)) : Bool :=
  match initAigSliceMem cfg w w with
  | none => false
  | some (m0, numAtoms) =>
    let args : Tup Val [i64, i32, i32, i32] :=
      (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ())
    let udivOk := runCheckOnMem (wx := w) (wy := w) (outW := w) cfg fuel m0 numAtoms pairs
      "bv_blast_udiv" [i64, i32, i32, i32] args (.bin (.var 0) .udiv (.var 1))
    let umodOk := runCheckOnMem (wx := w) (wy := w) (outW := w) cfg fuel m0 numAtoms pairs
      "bv_blast_umod" [i64, i32, i32, i32] args (.bin (.var 0) .umod (.var 1))
    udivOk && umodOk

private def checkCpop (cfg : MemCfg) (fuel : Nat) (w : Nat) : Bool :=
  match initAigSliceMem cfg w 0 with
  | none => false
  | some (m0, numAtoms) =>
    let pairs := (sampleVals w).map fun x => (x, (0#0))
    let args : Tup Val [i64, i32, i32] := (hdrAddr, 0#32, BitVec.ofNat 32 w, ())
    runCheckOnMem (wx := w) (wy := 0) (outW := w) cfg fuel m0 numAtoms pairs
      "bv_blast_cpop" [i64, i32, i32] args (.un .cpop (.var 0))

/-! ## 1. Differential Symbolic Tests (`w = 0, 1, 2, 3, 4, 8, 16, 32, 64`) -/

#guard [0, 1, 2, 3, 4, 8, 16].all fun w => checkDivModPair (cfgFor w) 2000000 w (samplePairs w w)
#guard [0, 1, 2, 3, 4, 8, 16, 32, 64].all fun w => checkCpop (cfgCpop w) 2000000 w
#guard checkDivModPair cfgDiv32 5000000 32 (edgePairs 32)

-- 64-bit symbolic numerator (full 64 atoms) against key constant divisors (incl. d = 0, d = 1)
private def checkDiv64SymN (aigCap : Nat) (dVal : BitVec 64) : Bool :=
  let cfg : MemCfg := { aigCap := aigCap, htMask := 127, litsCap := 512 }
  let dLits := (List.range 64).map fun j => if dVal.getLsbD j then (1 : UInt32) else 0
  match initAigSliceMem cfg 64 64 none (some dLits) (some 64) with
  | none => false
  | some (m0, numAtoms) =>
    let xs := sampleVals 64
    let run := fun fnName (isMod : Bool) =>
      match interpModule linkedAigDivCpopModule 10000000 fnName [i64, i32, i32, i32] [i32]
          (hdrAddr, 0#32, 64#32, 64#32, ()) m0 with
      | .ok (outOff, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
            readAig m1 numAtoms, readU32Slice m1 cfg.litsAddr outOff.toNat 64 with
        | some 0, some litsLen, some g, some outLits =>
          outOff.toNat + 64 == litsLen.toNat && aigWfB g &&
          xs.all fun xv =>
            let nodes := g.evalNodes (atomEnv xv (0#0))
            let exp := if isMod then xv % dVal else xv / dVal
            (List.range 64).all fun i =>
              Ref.Aig.evalLitIn nodes (outLits.getD i 0) == exp.getLsbD i
        | _, _, _, _ => false
      | _ => false
    run "bv_blast_udiv" false && run "bv_blast_umod" true

#guard [(128, 0#64), (128, 1#64), (10240, 0x8000000000000001#64)].all fun (cap, d) =>
  checkDiv64SymN cap d

/-! ## 2. Sub-Helper Parity (`bv_blast_sub_with_borrow`, `bv_blast_ite_slice`) & Aliasing -/

private def testSubWithBorrow (w : Nat) : Bool :=
  let cfg := cfgFor w
  match initAigSliceMem cfg w w with
  | none => false
  | some (m0, numAtoms) =>
    match interpModule linkedAigDivCpopModule 5000 "bv_lits_alloc"
        [i64, i32] [i32] (hdrAddr, BitVec.ofNat 32 w, ()) m0 with
    | .ok (outOffBV, ()) m1 =>
      match interpModule linkedAigDivCpopModule 500000 "bv_blast_sub_with_borrow"
          [i64, i32, i32, i32, i32] [i32]
          (hdrAddr, 0#32, BitVec.ofNat 32 w, outOffBV, BitVec.ofNat 32 w, ()) m1 with
      | .ok (borrowLitBV, ()) m2 =>
        match readMemU32 m2 (hdrAddr + 120), readMemU32 m2 (hdrAddr + 112),
            readAig m2 numAtoms, readU32Slice m2 cfg.litsAddr outOffBV.toNat w with
        | some 0, some litsLen, some g, some diffLits =>
          let borrowLit := UInt32.ofBitVec borrowLitBV
          outOffBV.toNat + w == litsLen.toNat && aigWfB g &&
          (borrowLit >>> 1).toNat < g.A + 1 + g.nodes.size &&
          (samplePairs w w).all fun (xv, yv) =>
            let vals := g.evalNodes (atomEnv xv yv)
            let diffOk := (List.range w).all fun i =>
              Ref.Aig.evalLitIn vals (diffLits.getD i 0) == (xv - yv).getLsbD i
            let borOk := Ref.Aig.evalLitIn vals borrowLit == xv.ult yv
            diffOk && borOk
        | _, _, _, _ => false
      | _ => false
    | _ => false

private def testIteSlice (w : Nat) : Bool :=
  let cfg := cfgFor w
  match initAigSliceMem cfg w w with
  | none => false
  | some (m0, numAtoms) =>
    let mkAtom := fun cLit condVal =>
      match interpModule linkedAigDivCpopModule 500000 "bv_blast_ite_slice"
          [i64, i32, i32, i32, i32] [i32]
          (hdrAddr, cLit, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ()) m0 with
      | .ok (outOffBV, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
            readAig m1 numAtoms, readU32Slice m1 cfg.litsAddr outOffBV.toNat w with
        | some 0, some litsLen, some g, some outLits =>
          outOffBV.toNat + w == litsLen.toNat && aigWfB g &&
          (samplePairs w w).all fun (xv, yv) =>
            let vals := g.evalNodes (atomEnv xv yv)
            let exp := if condVal then xv else yv
            (List.range w).all fun i =>
              Ref.Aig.evalLitIn vals (outLits.getD i 0) == exp.getLsbD i
        | _, _, _, _ => false
      | _ => false
    mkAtom 1#32 true && mkAtom 0#32 false

#guard [0, 1, 4, 8, 16].all testSubWithBorrow
#guard [0, 1, 4, 8, 16].all testIteSlice

private def testAliasDivMod (w : Nat) : Bool :=
  let cfg := cfgFor w
  match initAigSliceMem cfg w 0 with
  | none => false
  | some (m0, numAtoms) =>
    let pairs := (sampleVals w).map fun x => (x, 0#0)
    let args : Tup Val [i64, i32, i32, i32] := (hdrAddr, 0#32, 0#32, BitVec.ofNat 32 w, ())
    let okUdiv := runCheckOnMem (wx := w) (wy := 0) (outW := w) cfg 2000000 m0 numAtoms pairs
      "bv_blast_udiv" [i64, i32, i32, i32] args (.bin (.var 0) .udiv (.var 0))
    let okUmod := runCheckOnMem (wx := w) (wy := 0) (outW := w) cfg 2000000 m0 numAtoms pairs
      "bv_blast_umod" [i64, i32, i32, i32] args (.bin (.var 0) .umod (.var 0))
    okUdiv && okUmod

#guard [0, 1, 2, 4, 8, 16].all testAliasDivMod

/-! ## 3. Constant-Folding Parity (`g.nodes.size == 0`) Across `w = 0..64` -/

private def constLitsOf {w : Nat} (v : BitVec w) : List UInt32 :=
  (List.range w).map fun j => if v.getLsbD j then (1 : UInt32) else 0

private def constEdgeFew (w : Nat) : List (BitVec w × BitVec w) :=
  if w == 0 then [(0#w, 0#w)]
  else
    let maxU := BitVec.allOnes w
    let altA := BitVec.ofNat w 0xAAAAAAAAAAAAAAAA
    if w == 64 then [(maxU, maxU), (altA, 7#w)]
    else [(maxU, 0#w), (altA, 7#w)]

private def checkConstDivMod (w : Nat) (xv yv : BitVec w) : Bool :=
  match initAigSliceMem cfgConstDiv w w
      (some (constLitsOf xv)) (some (constLitsOf yv)) (some 0) with
  | none => false
  | some (m0, numAtoms) =>
    let runBin := fun fnName (exp : BitVec w) =>
      match interpModule linkedAigDivCpopModule 2000000 fnName [i64, i32, i32, i32] [i32]
          (hdrAddr, 0#32, BitVec.ofNat 32 w, BitVec.ofNat 32 w, ()) m0 with
      | .ok (outOff, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
            readAig m1 numAtoms, readU32Slice m1 cfgConstDiv.litsAddr outOff.toNat w with
        | some 0, some litsLen, some g, some outLits =>
          outOff.toNat + w == litsLen.toNat && g.nodes.size == 0 &&
          (List.range w).all fun i =>
            g.evalLit (fun _ => false) (outLits.getD i 0) == exp.getLsbD i
        | _, _, _, _ => false
      | _ => false
    runBin "bv_blast_udiv" (xv / yv) && runBin "bv_blast_umod" (xv % yv)

private def checkConstCpop (w : Nat) (xv : BitVec w) : Bool :=
  let cfg := if w ≤ 16 then cfgConstDiv else cfgConstCpop
  match initAigSliceMem cfg w 0 (some (constLitsOf xv)) (some []) (some 0) with
  | none => false
  | some (m0, numAtoms) =>
    match interpModule linkedAigDivCpopModule 2000000 "bv_blast_cpop" [i64, i32, i32] [i32]
        (hdrAddr, 0#32, BitVec.ofNat 32 w, ()) m0 with
    | .ok (outOff, ()) m1 =>
      match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
          readAig m1 numAtoms, readU32Slice m1 cfg.litsAddr outOff.toNat w with
      | some 0, some litsLen, some g, some outLits =>
        outOff.toNat + w == litsLen.toNat && g.nodes.size == 0 &&
        (List.range w).all fun i =>
          g.evalLit (fun _ => false) (outLits.getD i 0) == xv.cpop.getLsbD i
      | _, _, _, _ => false
    | _ => false

#guard [0, 1, 2, 3, 4, 8, 16, 32, 64].all fun w =>
  (constEdgeFew w).all fun (xv, yv) => checkConstDivMod w xv yv
#guard [0, 1, 2, 3, 4, 8, 16, 32, 64].all fun w =>
  (sampleVals w).take 2 |>.all fun xv => checkConstCpop w xv

/-! ## 4. Error, Overflow, Temp-Pool Cleanup, and OOM Guards -/

private def testErrorAndOomGuards : Bool :=
  let cfg := cfgFor 4
  match initAigSliceMem cfg 4 4 with
  | none => false
  | some (m0, _) =>
    -- 1. Slice out-of-bounds
    let oobUdivOk := match interpModule linkedAigDivCpopModule 5000 "bv_blast_udiv"
        [i64, i32, i32, i32] [i32] (hdrAddr, 6#32, 0#32, 4#32, ()) m0 with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    let oobCpopOk := match interpModule linkedAigDivCpopModule 5000 "bv_blast_cpop"
        [i64, i32, i32] [i32] (hdrAddr, 6#32, 4#32, ()) m0 with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 2. u32 wraparound in slice check
    let wrapOk := match interpModule linkedAigDivCpopModule 5000 "bv_blast_umod"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 0xFFFFFFFE#32, 4#32, ()) m0 with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 3. `lits_cap` exhausted inside temp allocation restores `lits_len` cleanly
    let mSmallLitsDiv := storeMem m0 i32 (hdrAddr + 116) 14#32
    let litsOomDivOk := match interpModule linkedAigDivCpopModule 50000 "bv_blast_udiv"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 4#32, ()) mSmallLitsDiv with
      | .ok (0xFFFFFFFF#32, ()) m1 =>
        readMemU32 m1 (hdrAddr + 120) == some 1 && readMemU32 m1 (hdrAddr + 112) == some 8
      | _ => false
    let mSmallLitsCpop := storeMem m0 i32 (hdrAddr + 116) 16#32
    let litsOomCpopOk := match interpModule linkedAigDivCpopModule 50000 "bv_blast_cpop"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, 4#32, ()) mSmallLitsCpop with
      | .ok (0xFFFFFFFF#32, ()) m1 =>
        readMemU32 m1 (hdrAddr + 120) == some 1 && readMemU32 m1 (hdrAddr + 112) == some 8
      | _ => false
    -- 4. `w * w >= 2^32` overflow guard in `bv_blast_cpop`
    let mLenFake := storeMem (storeMem m0 i32 (hdrAddr + 116) 0xFFFFFFFF#32)
      i32 (hdrAddr + 112) 0x100000#32
    let cpopOvOk := match interpModule linkedAigDivCpopModule 50000 "bv_blast_cpop"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, 0x10000#32, ()) mLenFake with
      | .ok (0xFFFFFFFF#32, ()) m1 =>
        readMemU32 m1 (hdrAddr + 120) == some 1 && readMemU32 m1 (hdrAddr + 112) == some 0x100000
      | _ => false
    -- 5. `aig_cap` exhausted inside `bv_blast_udiv` and `bv_blast_cpop` restores `lits_len`
    let mSmallAig := storeMem m0 i32 (hdrAddr + 104) 10#32
    let aigOomDivOk := match interpModule linkedAigDivCpopModule 50000 "bv_blast_udiv"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 4#32, ()) mSmallAig with
      | .ok (0xFFFFFFFF#32, ()) m1 =>
        readMemU32 m1 (hdrAddr + 120) == some 1 && readMemU32 m1 (hdrAddr + 112) == some 8
      | _ => false
    let aigOomCpopOk := match interpModule linkedAigDivCpopModule 50000 "bv_blast_cpop"
        [i64, i32, i32] [i32] (hdrAddr, 0#32, 4#32, ()) mSmallAig with
      | .ok (0xFFFFFFFF#32, ()) m1 =>
        readMemU32 m1 (hdrAddr + 120) == some 1 && readMemU32 m1 (hdrAddr + 112) == some 8
      | _ => false
    -- 6. Pre-existing `h->oom != 0` short-circuits cleanly
    let mPreOom := storeMem m0 i32 (hdrAddr + 120) 1#32
    let preOomOk := match interpModule linkedAigDivCpopModule 5000 "bv_blast_sub_with_borrow"
        [i64, i32, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 0#32, 4#32, ()) mPreOom with
      | .ok (0#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    oobUdivOk && oobCpopOk && wrapOk && litsOomDivOk && litsOomCpopOk &&
      cpopOvOk && aigOomDivOk && aigOomCpopOk && preOomOk

#guard testErrorAndOomGuards

/-! ## 5. Single-Line `#print axioms` Audit (`<= std3`, `< 115c`) -/

theorem audit_ops_div_cpop_wf : ∀ f ∈ OpsDivCpop.opsDivCpopFns, f.Wf :=
  OpsDivCpop.opsDivCpopFns_wf
theorem audit_ops_div_cpop_acyclic : OpsDivCpop.opsDivCpopModule.checkAcyclic = true :=
  OpsDivCpop.opsDivCpop_checkAcyclic

#print axioms audit_ops_div_cpop_wf
#print axioms audit_ops_div_cpop_acyclic

end LeanQbeTest.T.BitblastOpsDivCpopTest
