/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InterpKissat
public import LeanQbe.T.Examples.Bitblast.Src.Aig
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public import LeanQbe.T.Examples.Bitblast.Ref.Aig
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

public meta import LeanQbe.T.InterpKissat
public meta import LeanQbe.T.Examples.Bitblast.Src.Aig
public meta import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public meta import LeanQbe.T.Examples.Bitblast.Ref.Aig
public meta import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Differential `Interp` Tests & Axiom Audit for `Bitblast/Src/OpsCore.lean` (`S3b`)

Links `Aig.fns ++ OpsCore.fns` via `interpModule` and differentially compares every Phase-A `S3`
operation (`extract`, `append`, `not`, `and`, `or`, `xor`, `add`, `eq`, `ult`, `getLsbD`)
against `Std.Tactic.BVDecide.BVExpr.eval` / `BVPred.eval` across `w = 0, 1, 4, 8, 16, 64`,
aliasing, constant-folding, overflow, and OOM edge cases, plus `#print axioms` (`<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastOpsCoreTest

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.Bitblast
open LeanQbe.T.Examples.Bitblast.Src

private def linkedAigOpsCoreModule : Module :=
  { fns := Aig.fns ++ OpsCore.fns
    externs := []
    exits := [] }

#guard OpsCore.opsCoreFns.map Fn.name == OpsCore.fns.map Fn.name
theorem opsCoreFns_eq_fns : OpsCore.opsCoreFns = OpsCore.fns := rfl
#guard OpsCore.opsCoreFns.length == 13
#guard (OpsCore.opsCoreFns.map Fn.name).eraseDups.length == 13
#guard OpsCore.opsCoreModule.checkAcyclic == true
#guard OpsCore.opsCoreModule.exits.isEmpty
#guard OpsCore.opsCoreFns.all (fun f => f.as.length <= 6)
#guard linkedAigOpsCoreModule.checkAcyclic == true

private def hdrAddr : BitVec 64 := 0x1000#64
private def aigAddr : BitVec 64 := 0x1100#64
private def htAddr : BitVec 64 := 0x3100#64
private def litsAddr : BitVec 64 := 0x4100#64
private def totalMemBytes : Nat := 0x3900
private def aigCapVal : Nat := 1024
private def htMaskVal : Nat := 1023
private def litsCapVal : Nat := 512

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

private def initAigSliceMem (wx wy : Nat) (xLits? : Option (List UInt32) := none)
    (yLits? : Option (List UInt32) := none) : Option (Mem 64 × Nat) := do
  let numAtoms := wx + wy
  let m0 : Mem 64 := (List.replicate totalMemBytes 0).At hdrAddr
  let m1 := storeMem m0 i64 (hdrAddr + 0) hdrAddr
  let m2 := storeMem m1 i64 (hdrAddr + 8) (hdrAddr + BitVec.ofNat 64 totalMemBytes)
  let m3 := storeMem m2 i64 (hdrAddr + 56) litsAddr
  let m4 := storeMem m3 i32 (hdrAddr + 116) (BitVec.ofNat 32 litsCapVal)
  let initArgs : Tup Val [i64, i64, i32, i64, i32, i32] :=
    (hdrAddr, aigAddr, BitVec.ofNat 32 aigCapVal, htAddr, BitVec.ofNat 32 htMaskVal,
      BitVec.ofNat 32 numAtoms, ())
  let m5 ← match interpModule linkedAigOpsCoreModule 100000 "bv_aig_init"
      [i64, i64, i32, i64, i32, i32] [] initArgs m4 with
    | .ok _ m' => some m'
    | _ => none
  let xl := xLits?.getD ((List.range wx).map fun j => UInt32.ofNat (2 * (1 + j)))
  let yl := yLits?.getD ((List.range wy).map fun j => UInt32.ofNat (2 * (1 + wx + j)))
  if xl.length != wx || yl.length != wy then none
  let totLits := wx + wy
  let m6 ← match interpModule linkedAigOpsCoreModule 5000 "bv_lits_alloc"
      [i64, i32] [i32] (hdrAddr, BitVec.ofNat 32 totLits, ()) m5 with
    | .ok (off, ()) m' =>
      if off == 0#32 then some m' else none
    | _ => none
  let m7 := writeU32Slice m6 litsAddr 0 xl
  let m8 := writeU32Slice m7 litsAddr wx yl
  some (m8, numAtoms)

private def atomEnv {wx wy : Nat} (xv : BitVec wx) (yv : BitVec wy) (n : Nat) : Bool :=
  if 1 ≤ n && n ≤ wx then xv.getLsbD (n - 1)
  else if wx < n && n ≤ wx + wy then yv.getLsbD (n - 1 - wx)
  else false

private def mkAssign {wx wy : Nat} (xv : BitVec wx) (yv : BitVec wy) : BVExpr.Assignment :=
  Lean.RArray.branch 1 (.leaf ⟨xv⟩) (.leaf ⟨yv⟩)

private def sampleVals (w : Nat) : List (BitVec w) :=
  let raw : List Nat :=
    [0, 1, 2, 5, 0x55, 0xAA, 0x1234, 0x5555, 0xAAAA, 0x5555555555555555, 0xAAAAAAAAAAAAAAAA]
  let extra : List (BitVec w) :=
    if w == 0 then [BitVec.ofNat w 0]
    else
      [ 0#w, 1#w, BitVec.allOnes w, BitVec.allOnes w - 1#w,
        BitVec.ofNat w (1 <<< (w - 1)), BitVec.ofNat w ((1 <<< (w - 1)) - 1) ]
  (extra ++ raw.map (BitVec.ofNat w)).eraseDups

private def samplePairs (wx wy : Nat) : List (BitVec wx × BitVec wy) :=
  let xs := sampleVals wx
  let ys := sampleVals wy
  xs.flatMap fun x => ys.map fun y => (x, y)

private def checkBvOp {wx wy outW : Nat} (fnName : Sym) (as : List Ty)
    (mkArgs : BitVec 32 → BitVec 32 → Tup Val as) (expr : BVExpr outW) : Bool :=
  match initAigSliceMem wx wy with
  | none => false
  | some (m0, numAtoms) =>
    let args := mkArgs 0#32 (BitVec.ofNat 32 wx)
    match interpModule linkedAigOpsCoreModule 500000 fnName as [i32] args m0 with
    | .ok (outOffBV, ()) m1 =>
      match readMemU32 m1 (hdrAddr + 120), readMemU32 m1 (hdrAddr + 112),
          readAig m1 numAtoms with
      | some 0, some litsLen, some g =>
        let outOff := outOffBV.toNat
        if outOff + outW != litsLen.toNat || !aigWfB g then false
        else
          match readU32Slice m1 litsAddr outOff outW with
          | none => false
          | some outLits =>
            (samplePairs wx wy).all fun (xv, yv) =>
              let vals := g.evalNodes (atomEnv xv yv)
              let expected := BVExpr.eval (mkAssign xv yv) expr
              (List.range outW).all fun i =>
                Ref.Aig.evalLitIn vals (outLits.getD i 0) == expected.getLsbD i
      | _, _, _ => false
    | _ => false

private def checkPredOp {wx wy : Nat} (fnName : Sym) (as : List Ty)
    (mkArgs : BitVec 32 → BitVec 32 → Tup Val as) (pred : BVPred) : Bool :=
  match initAigSliceMem wx wy with
  | none => false
  | some (m0, numAtoms) =>
    let args := mkArgs 0#32 (BitVec.ofNat 32 wx)
    match interpModule linkedAigOpsCoreModule 500000 fnName as [i32] args m0 with
    | .ok (outLitBV, ()) m1 =>
      match readMemU32 m1 (hdrAddr + 120), readAig m1 numAtoms with
      | some 0, some g =>
        let outLit := UInt32.ofBitVec outLitBV
        if !aigWfB g || !((outLit >>> 1).toNat < g.A + 1 + g.nodes.size) then false
        else
          (samplePairs wx wy).all fun (xv, yv) =>
            let vals := g.evalNodes (atomEnv xv yv)
            let expected := BVPred.eval (mkAssign xv yv) pred
            Ref.Aig.evalLitIn vals outLit == expected
      | _, _ => false
    | _ => false

/-! ## 1. Differential Tests Across `w = 0, 1, 4, 8, 16, 64` for All Phase-A `S3` Ops -/

private def testUnaryNot (w : Nat) : Bool :=
  checkBvOp (wx := w) (wy := 0) (outW := w) "bv_blast_not" [i64, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, BitVec.ofNat 32 w, ()))
    (.un .not (.var 0))

private def testBinOp (w : Nat) (fnName : Sym) (bop : BVBinOp) : Bool :=
  checkBvOp (wx := w) (wy := w) (outW := w) fnName [i64, i32, i32, i32]
    (fun aOff bOff => (hdrAddr, aOff, bOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0) bop (.var 1))

private def testPredBin (w : Nat) (fnName : Sym) (pred : BVBinPred) : Bool :=
  checkPredOp (wx := w) (wy := w) fnName [i64, i32, i32, i32]
    (fun aOff bOff => (hdrAddr, aOff, bOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0 : BVExpr w) pred (.var 1))

private def testGetLsbD (w idx : Nat) : Bool :=
  checkPredOp (wx := w) (wy := 0) "bv_blast_get_lsb_d" [i64, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, BitVec.ofNat 32 w, BitVec.ofNat 32 idx, ()))
    (.getLsbD (.var 0 : BVExpr w) idx)

private def testExtract (aw start len : Nat) : Bool :=
  checkBvOp (wx := aw) (wy := 0) (outW := len) "bv_blast_extract" [i64, i32, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, BitVec.ofNat 32 aw, BitVec.ofNat 32 start,
      BitVec.ofNat 32 len, ()))
    (.extract start len (.var 0 : BVExpr aw))

private def testAppend (lw rw : Nat) : Bool :=
  checkBvOp (wx := lw) (wy := rw) (outW := lw + rw) "bv_blast_append" [i64, i32, i32, i32, i32]
    (fun lOff rOff => (hdrAddr, lOff, BitVec.ofNat 32 lw, rOff, BitVec.ofNat 32 rw, ()))
    (.append (.var 0 : BVExpr lw) (.var 1 : BVExpr rw) rfl)

#guard [0, 1, 4, 8, 16, 64].all testUnaryNot
#guard [0, 1, 4, 8, 16, 64].all (fun w => testBinOp w "bv_blast_and" .and)
#guard [0, 1, 4, 8, 16, 64].all (fun w => testBinOp w "bv_blast_or" .or)
#guard [0, 1, 4, 8, 16, 64].all (fun w => testBinOp w "bv_blast_xor" .xor)
#guard [0, 1, 4, 8, 16, 64].all (fun w => testBinOp w "bv_blast_add" .add)
#guard [0, 1, 4, 8, 16, 64].all (fun w => testPredBin w "bv_blast_eq" .eq)
#guard [0, 1, 4, 8, 16, 64].all (fun w => testPredBin w "bv_blast_ult" .ult)

#guard ([0, 1, 4, 8, 16, 64].all fun w =>
  [0, 1, w / 2, w - 1, w, w + 1, 0xFFFFFFFF].all fun idx => testGetLsbD w idx)

#guard
  let widths := [0, 1, 4, 8, 16, 64]
  widths.all fun aw =>
    widths.all fun len =>
      [0, 1, aw / 2, aw - 1, aw, aw + 5, 0xFFFFFFF0].all fun start =>
        testExtract aw start len

#guard
  [(0, 0), (0, 1), (1, 0), (0, 8), (8, 0), (1, 1), (1, 4), (4, 1),
   (4, 4), (8, 8), (1, 16), (16, 1), (16, 16), (1, 64), (64, 1), (64, 64)].all
    fun (lw, rw) => testAppend lw rw

/-! ## 2. Aliasing (`a_off == b_off`), Constant-Folding, and Error/Overflow Edge Cases -/

private def testAliasOps (w : Nat) : Bool :=
  let okAnd := checkBvOp (wx := w) (wy := 0) (outW := w) "bv_blast_and" [i64, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, aOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0) .and (.var 0))
  let okAdd := checkBvOp (wx := w) (wy := 0) (outW := w) "bv_blast_add" [i64, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, aOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0) .add (.var 0))
  let okEq := checkPredOp (wx := w) (wy := 0) "bv_blast_eq" [i64, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, aOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0 : BVExpr w) .eq (.var 0))
  let okUlt := checkPredOp (wx := w) (wy := 0) "bv_blast_ult" [i64, i32, i32, i32]
    (fun aOff _ => (hdrAddr, aOff, aOff, BitVec.ofNat 32 w, ()))
    (.bin (.var 0 : BVExpr w) .ult (.var 0))
  okAnd && okAdd && okEq && okUlt

#guard [0, 1, 8, 64].all testAliasOps

private def testConstFoldSlice : Bool :=
  let xv : BitVec 8 := 0xA5#8
  let yv : BitVec 8 := 0x3C#8
  let xl := (List.range 8).map fun j => if xv.getLsbD j then (1 : UInt32) else 0
  let yl := (List.range 8).map fun j => if yv.getLsbD j then (1 : UInt32) else 0
  match initAigSliceMem 8 8 (some xl) (some yl) with
  | none => false
  | some (m0, numAtoms) =>
    let addOk := match interpModule linkedAigOpsCoreModule 50000 "bv_blast_add"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 8#32, 8#32, ()) m0 with
      | .ok (outOff, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readAig m1 numAtoms,
            readU32Slice m1 litsAddr outOff.toNat 8 with
        | some 0, some g, some outLits =>
          g.nodes.size == 0 &&
          (List.range 8).all fun i =>
            g.evalLit (fun _ => false) (outLits.getD i 0) == (xv + yv).getLsbD i
        | _, _, _ => false
      | _ => false
    let ultOk := match interpModule linkedAigOpsCoreModule 50000 "bv_blast_ult"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 8#32, 8#32, ()) m0 with
      | .ok (lit, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readAig m1 numAtoms with
        | some 0, some g =>
          g.nodes.size == 0 && g.evalLit (fun _ => false) (UInt32.ofBitVec lit) == xv.ult yv
        | _, _ => false
      | _ => false
    let ultRevOk := match interpModule linkedAigOpsCoreModule 50000 "bv_blast_ult"
        [i64, i32, i32, i32] [i32] (hdrAddr, 8#32, 0#32, 8#32, ()) m0 with
      | .ok (lit, ()) m1 =>
        match readMemU32 m1 (hdrAddr + 120), readAig m1 numAtoms with
        | some 0, some g =>
          g.nodes.size == 0 && g.evalLit (fun _ => false) (UInt32.ofBitVec lit) == yv.ult xv
        | _, _ => false
      | _ => false
    addOk && ultOk && ultRevOk

#guard testConstFoldSlice

private def testErrorAndOverflowGuards : Bool :=
  match initAigSliceMem 4 4 with
  | none => false
  | some (m0, _) =>
    -- 1. Slice out-of-bounds (`a_off + w > lits_len`)
    let oobOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_not"
        [i64, i32, i32] [i32] (hdrAddr, 6#32, 4#32, ()) m0 with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 2. `u32` addition wraparound in `a_off + w` (`0xFFFFFFFE + 4`)
    let wrapSliceOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_eq"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0xFFFFFFFE#32, 0#32, 4#32, ()) m0 with
      | .ok (0#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 3. `bv_blast_append` total width overflow (`lw + rw >= 2^32`)
    let mLenFake := storeMem (storeMem m0 i32 (hdrAddr + 116) 0xFFFFFFFF#32)
      i32 (hdrAddr + 112) 0xFFFFFFFE#32
    let appendOvOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_append"
        [i64, i32, i32, i32, i32] [i32]
        (hdrAddr, 0#32, 0x80000000#32, 0#32, 0x80000000#32, ()) mLenFake with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 4. `lits_cap` exhausted on output allocation
    let mSmallLits := storeMem m0 i32 (hdrAddr + 116) 8#32
    let litsOomOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_add"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 4#32, ()) mSmallLits with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 5. `aig_cap` exhausted inside gate creation
    let mSmallAig := storeMem m0 i32 (hdrAddr + 104) 9#32
    let aigOomOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_ult"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 4#32, ()) mSmallAig with
      | .ok (0#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 6. Invalid bitwise opcode in `bv_blast_bin_bitwise`
    let badOpOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_bin_bitwise"
        [i64, i32, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 4#32, 99#32, ()) m0 with
      | .ok (0xFFFFFFFF#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    -- 7. `h->oom != 0` on entry short-circuits cleanly
    let mPreOom := storeMem m0 i32 (hdrAddr + 120) 1#32
    let preOomOk := match interpModule linkedAigOpsCoreModule 5000 "bv_blast_get_lsb_d"
        [i64, i32, i32, i32] [i32] (hdrAddr, 0#32, 4#32, 0#32, ()) mPreOom with
      | .ok (0#32, ()) m1 => readMemU32 m1 (hdrAddr + 120) == some 1
      | _ => false
    oobOk && wrapSliceOk && appendOvOk && litsOomOk && aigOomOk && badOpOk && preOomOk

#guard testErrorAndOverflowGuards

/-! ## 3. Single-Line `#print axioms` Audit (`<= std3`, `< 115c`) -/

theorem audit_ops_core_wf : ∀ f ∈ OpsCore.opsCoreFns, f.Wf := OpsCore.opsCoreFns_wf
theorem audit_ops_core_acyclic : OpsCore.opsCoreModule.checkAcyclic = true :=
  OpsCore.opsCore_checkAcyclic

#print axioms audit_ops_core_wf
#print axioms audit_ops_core_acyclic

end LeanQbeTest.T.BitblastOpsCoreTest
