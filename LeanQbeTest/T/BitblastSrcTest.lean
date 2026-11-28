/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.InterpKissat
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Examples.Bitblast.Src.Header
import LeanQbe.T.Examples.Bitblast.Src.Full
import LeanQbe.T.Examples.Bitblast.Ref.BVProg
import LeanQbe.T.Examples.Bitblast.Ref.Tseitin
import LeanQbeTest.T.BitblastRefTest

meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Full
meta import LeanQbe.T.Examples.Bitblast.Ref.BVProg
meta import LeanQbe.T.Examples.Bitblast.Ref.Tseitin
meta import LeanQbeTest.T.BitblastRefTest

/-!
# Verification Tests & Axiom Audit for `Bitblast.Src` (`S2b`)

Tests C0 `bv_validate`, `bv_mk_and`, `bv_lits_*`, `bv_coi_mark`, `bv_dimacs_write`, and
`bv_solve_bytes` (linked against `Kissat.Plain` via `interpModule`) on:
1. Valid and malformed `BVP1` inputs (`bv_validate`)
2. AIG folding, commutative HT deduplication, untrusted HT collision rejection, and OOM
3. COI backward sweep & exact byte-for-byte DIMACS emission vs `Bitblast.Ref.Tseitin`
4. End-to-end `bv_solve_bytes` on trivial UNSAT, trivial SAT (`BV_TRIVIAL_SAT_MAGIC`), non-trivial
   gate/`eq`/`getLsbD`/`ite` UNSAT and SAT formulas, unaligned pointers, and malformed `BVP1`
5. Single-line `#print axioms` audit (`<= std3`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BitblastSrcTest

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Bitblast
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Full

private def linkedPlainBitblastModule : Module :=
  { fns := Plain.plainModule.fns ++ bitblastModule.fns
    externs := []
    exits := [] }

#guard linkedPlainBitblastModule.checkAcyclic == true

private def readMemBytes (m : Mem 64) (addr : BitVec 64) (len : Nat) : Option (List UInt8) :=
  go len 0 []
where
  go : Nat → Nat → List UInt8 → Option (List UInt8)
    | 0, _, acc => some acc.reverse
    | n + 1, off, acc =>
      match loadVal m i8 (addr + BitVec.ofNat 64 off) with
      | some b => go n (off + 1) (UInt8.ofBitVec b :: acc)
      | none => none

private def readMemU32 (m : Mem 64) (addr : BitVec 64) : Option UInt32 :=
  match loadVal m i32 addr with
  | some v => some (UInt32.ofBitVec v)
  | none => none

private def readMemU64 (m : Mem 64) (addr : BitVec 64) : Option UInt64 :=
  match loadVal m i64 addr with
  | some v => some (UInt64.ofBitVec v)
  | none => none

private def runValidateWords (ws : List Nat) : Option Bool :=
  let bs := BVProg.wordsToBytesLE ws
  let ptr : BitVec 64 := 0x1000#64
  let m0 : Mem 64 := bs.At ptr
  match interpFunc linkedPlainBitblastModule 100000 Validate.bv_validate_body
      (ptr, BitVec.ofNat 64 bs.length, ()) m0 with
  | .ok (res, ()) _ => some res
  | _ => none

/-! ## 1. `bv_validate` Valid & Malformed `BVP1` Tests -/

#guard runValidateWords BitblastRefTest.smallWs == some true
#guard runValidateWords BitblastRefTest.wideDepWs == some true
#guard runValidateWords BitblastRefTest.dag120Ws == some true

-- Null / short / unaligned length / bad magic / bad version / n_nodes == 0 / root >= n_nodes
#guard match interpFunc linkedPlainBitblastModule 1000 Validate.bv_validate_body
    (0#64, 32#64, ()) default with
  | .ok (false, ()) _ => true | _ => false
#guard match interpFunc linkedPlainBitblastModule 1000 Validate.bv_validate_body
    (0x1000#64, 28#64, ()) ((List.replicate 28 0).At 0x1000#64) with
  | .ok (false, ()) _ => true | _ => false
#guard match interpFunc linkedPlainBitblastModule 1000 Validate.bv_validate_body
    (0x1000#64, 33#64, ()) ((List.replicate 33 0).At 0x1000#64) with
  | .ok (false, ()) _ => true | _ => false
#guard runValidateWords [0x12345678, 1, 0, 1, 0, 0, 0, 0, 25, 1, 1, 0, 0] == some false
#guard runValidateWords [0x31505642, 2, 0, 1, 0, 0, 0, 0, 25, 1, 1, 0, 0] == some false
#guard runValidateWords [0x31505642, 1, 0, 0, 0, 0, 0, 0] == some false
#guard runValidateWords [0x31505642, 1, 0, 1, 0, 1, 0, 0, 25, 1, 1, 0, 0] == some false
-- Trailing extra word (prog_len mismatch)
#guard runValidateWords [0x31505642, 1, 0, 1, 0, 0, 0, 0, 25, 1, 1, 0, 0, 0] == some false
-- atom_base overflow check (two vars summing >= 2^28)
#guard runValidateWords
  [0x31505642, 1, 2, 1, 0, 0, 0, 0, 0, 0x08000000, 1, 0x08000000, 25, 1, 1, 0, 0] == some false
-- cwords out-of-bounds
#guard runValidateWords [0x31505642, 1, 0, 2, 1, 1, 0, 0, 0, 1, 33, 0, 0, 0, 24, 1, 0, 0, 0] ==
  some false
-- Non-topological self-reference, width mismatch, bool/bv mismatch, invalid opcode, bv root
#guard runValidateWords [0x31505642, 1, 0, 1, 0, 0, 0, 0, 26, 1, 0, 0, 0] == some false
#guard runValidateWords
  [0x31505642, 1, 1, 2, 0, 1, 0, 0, 0, 4, 0, 8, 0, 0, 0, 24, 1, 0, 0, 0] == some false
#guard runValidateWords
  [0x31505642, 1, 1, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 26, 1, 0, 0, 0] == some false
#guard runValidateWords [0x31505642, 1, 0, 1, 0, 0, 0, 0, 32, 1, 0, 0, 0] == some false
#guard runValidateWords [0x31505642, 1, 1, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0] == some false
#guard runValidateWords [0x31505642, 1, 0, 1, 0, 0, 0, 0, 25, 1, 2, 0, 0] == some false

/-! ## 2. `bv_mk_and`, Untrusted HT Collision Check, and `bv_lits_*` Tests -/

private def mkSyntheticHdrMem (aigCap htMask litsCap numAtoms : Nat)
    (aigEntries : List Nat := []) : Mem 64 :=
  let hdrPtr : BitVec 64 := 0x1000#64
  let aigPtr : BitVec 64 := 0x1100#64
  let htPtr : BitVec 64 := 0x2000#64
  let litsPtr : BitVec 64 := 0x2400#64
  let marksPtr : BitVec 64 := 0x2800#64
  let totalBytes := 0x3000 - 0x1000
  let m0 : Mem 64 := (List.replicate totalBytes 0).At hdrPtr
  let m1 := storeMem m0 i64 (hdrPtr + 0) 0x1000#64
  let m2 := storeMem m1 i64 (hdrPtr + 8) 0x3000#64
  let m3 := storeMem m2 i64 (hdrPtr + 24) aigPtr
  let m4 := storeMem m3 i64 (hdrPtr + 32) htPtr
  let m5 := storeMem m4 i64 (hdrPtr + 56) litsPtr
  let m6 := storeMem m5 i64 (hdrPtr + 64) marksPtr
  let m7 := storeMem m6 i32 (hdrPtr + 96) (BitVec.ofNat 32 numAtoms)
  let m8 := storeMem m7 i32 (hdrPtr + 100) (BitVec.ofNat 32 (numAtoms + 1 + aigEntries.length))
  let m9 := storeMem m8 i32 (hdrPtr + 104) (BitVec.ofNat 32 aigCap)
  let m10 := storeMem m9 i32 (hdrPtr + 108) (BitVec.ofNat 32 htMask)
  let m11 := storeMem m10 i32 (hdrPtr + 116) (BitVec.ofNat 32 litsCap)
  (aigEntries.zipIdx).foldl (fun acc (v, idx) =>
    storeMem acc i64 (aigPtr + BitVec.ofNat 64 (8 * (numAtoms + 1 + idx))) (BitVec.ofNat 64 v)) m11

private def testMkAndAndUntrustedHt : Bool :=
  let hdrPtr : BitVec 64 := 0x1000#64
  let m0 := mkSyntheticHdrMem 8 7 16 2
  -- Fold rules
  let r0 := interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 0#32, 4#32, ()) m0
  let r1 := interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 1#32, 5#32, ()) m0
  let r2 := interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 4#32, 4#32, ()) m0
  let r3 := interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 4#32, 5#32, ()) m0
  let foldOk := match r0, r1, r2, r3 with
    | .ok (x0, ()) _, .ok (x1, ()) _, .ok (x2, ()) _, .ok (x3, ()) _ =>
      x0 == 0#32 && x1 == 5#32 && x2 == 4#32 && x3 == 0#32
    | _, _, _, _ => false
  -- Create gate (2, 4) -> lit 6 (node 3), then test commutative HT hit (4, 2) -> lit 6
  let g1 := interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 2#32, 4#32, ()) m0
  let commOk := match g1 with
    | .ok (lit1, ()) m1 =>
      match interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body
          (hdrPtr, 4#32, 2#32, ()) m1 with
      | .ok (lit2, ()) m2 =>
        lit1 == 6#32 && lit2 == 6#32 && readMemU32 m2 (hdrPtr + 100) == some 4
      | _ => false
    | _ => false
  -- Poison every HT slot with bogus node indices (0, 2, 99) -> dynamic check rejects them!
  let mBadHt := (List.range 8).foldl (fun acc s =>
    storeMem acc i32 (0x2000#64 + BitVec.ofNat 64 (4 * s)) (if s % 2 == 0 then 2#32 else 99#32)) m0
  let untrustedHtOk :=
    match interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 2#32, 4#32, ())
        mBadHt with
    | .ok (lit, ()) m2 => lit == 6#32 && readMemU32 m2 (hdrPtr + 100) == some 4
    | _ => false
  -- OOM check when aig_len == aig_cap
  let mFull := mkSyntheticHdrMem 3 7 16 2
  let oomOk :=
    match interpFunc linkedPlainBitblastModule 5000 Aig.bv_mk_and_body (hdrPtr, 2#32, 4#32, ())
        mFull with
    | .ok (lit, ()) m2 => lit == 0#32 && readMemU32 m2 (hdrPtr + 120) == some 1
    | _ => false
  foldOk && commOk && untrustedHtOk && oomOk

#guard testMkAndAndUntrustedHt

private def testLitsPool : Bool :=
  let hdrPtr : BitVec 64 := 0x1000#64
  let m0 := mkSyntheticHdrMem 8 7 8 2
  match interpFunc linkedPlainBitblastModule 1000 Aig.bv_lits_alloc_body (hdrPtr, 5#32, ()) m0 with
  | .ok (o1, ()) m1 =>
    match interpFunc linkedPlainBitblastModule 1000 Aig.bv_lits_mark_body (hdrPtr, ()) m1 with
    | .ok (mk1, ()) m2 =>
      match interpFunc linkedPlainBitblastModule 1000 Aig.bv_lits_alloc_body
          (hdrPtr, 4#32, ()) m2 with
      | .ok (oomOff, ()) m3 =>
        let oomOk := oomOff == 0xFFFFFFFF#32 && readMemU32 m3 (hdrPtr + 120) == some 1
        let mReset := storeMem m2 i32 (hdrPtr + 120) 0#32
        match interpFunc linkedPlainBitblastModule 1000 Aig.bv_lits_alloc_body
            (hdrPtr, 3#32, ()) mReset with
        | .ok (o2, ()) m4 =>
          match interpFunc linkedPlainBitblastModule 1000 Aig.bv_lits_release_body
              (hdrPtr, mk1, ()) m4 with
          | .ok _ m5 =>
            o1 == 0#32 && mk1 == 5#32 && oomOk && o2 == 5#32 &&
              readMemU32 m5 (hdrPtr + 112) == some 5
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

#guard testLitsPool

/-! ## 3. `bv_coi_mark` and `bv_dimacs_write` Exact Parity with `Bitblast.Ref.Tseitin` -/

private def sampleAigRef : Aig :=
  { A := 2, nodes := #[(2, 4), (3, 5), (6, 4)] }

private def sampleAigPacked : List Nat :=
  [2 + (4 <<< 32), 3 + (5 <<< 32), 6 + (4 <<< 32)]

private def testCoiAndDimacsParity : Bool :=
  let hdrPtr : BitVec 64 := 0x1000#64
  let marksPtr : BitVec 64 := 0x2800#64
  let m0 := mkSyntheticHdrMem 16 7 16 2 sampleAigPacked
  match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_coi_mark_body
      (hdrPtr, 10#32, ()) m0 with
  | .ok _ m1 =>
    let marksOk :=
      match readMemBytes m1 marksPtr 6 with
      | some bs =>
        bs.map (fun b => b != 0) == (Tseitin.coiMark sampleAigRef 10).toList
      | none => false
    let dimacs10Ok :=
      match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_dimacs_write_body
          (hdrPtr, 10#32, ()) m1 with
      | .ok (true, ()) m2 =>
        match readMemU64 m2 (hdrPtr + 72), readMemU32 m2 (hdrPtr + 124) with
        | some dstart, some dlen =>
          readMemBytes m2 (BitVec.ofNat 64 dstart.toNat) dlen.toNat ==
            some (encodeDimacs (Tseitin.tseitin sampleAigRef (Tseitin.coiMark sampleAigRef 10) 10))
        | _, _ => false
      | _ => false
    let dimacs0Ok :=
      match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_dimacs_write_body
          (hdrPtr, 0#32, ()) m1 with
      | .ok (true, ()) m2 =>
        match readMemU64 m2 (hdrPtr + 72), readMemU32 m2 (hdrPtr + 124) with
        | some dstart, some dlen =>
          readMemBytes m2 (BitVec.ofNat 64 dstart.toNat) dlen.toNat ==
            some (encodeDimacs (Tseitin.tseitin sampleAigRef (Tseitin.coiMark sampleAigRef 0) 0))
        | _, _ => false
      | _ => false
    -- OOM when work_end leaves < 12 bytes
    let mTiny := storeMem m1 i64 (hdrPtr + 8) (0x1000#64 + 132#64)
    let dimacsOomOk :=
      match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_dimacs_write_body
          (hdrPtr, 0#32, ()) mTiny with
      | .ok (false, ()) m2 => readMemU32 m2 (hdrPtr + 120) == some 1
      | _ => false
    marksOk && dimacs10Ok && dimacs0Ok && dimacsOomOk
  | _ => false

#guard testCoiAndDimacsParity

-- ITE gadget parity (`detectIte` skips intermediate ANDs and emits 4 clauses instead of 9).
private def sampleIteAigRef : Aig :=
  { A := 3, nodes := #[(2, 5), (3, 7), (9, 11)] }

private def sampleIteAigPacked : List Nat :=
  [2 + (5 <<< 32), 3 + (7 <<< 32), 9 + (11 <<< 32)]

private def testIteCoiAndDimacsParity : Bool :=
  let hdrPtr : BitVec 64 := 0x1000#64
  let marksPtr : BitVec 64 := 0x2800#64
  let m0 := mkSyntheticHdrMem 16 7 16 3 sampleIteAigPacked
  match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_coi_mark_body
      (hdrPtr, 12#32, ()) m0 with
  | .ok _ m1 =>
    let marksOk :=
      match readMemBytes m1 marksPtr 7 with
      | some bs =>
        bs.map (fun b => b != 0) == (Tseitin.coiMark sampleIteAigRef 12).toList
      | none => false
    let dimacsOk :=
      match interpFunc linkedPlainBitblastModule 50000 Tseitin.bv_dimacs_write_body
          (hdrPtr, 12#32, ()) m1 with
      | .ok (true, ()) m2 =>
        match readMemU64 m2 (hdrPtr + 72), readMemU32 m2 (hdrPtr + 124) with
        | some dstart, some dlen =>
          readMemBytes m2 (BitVec.ofNat 64 dstart.toNat) dlen.toNat ==
            some (encodeDimacs
              (Tseitin.tseitin sampleIteAigRef (Tseitin.coiMark sampleIteAigRef 12) 12))
        | _, _ => false
      | _ => false
    marksOk && dimacsOk
  | _ => false

#guard testIteCoiAndDimacsParity

-- `bv_init_workspace` hash-table sizing (`ht_slots >= 2 * aig_cap`, power-of-2) + quadratic probe.
private def testWorkspaceHtSizing : Bool :=
  let progPtr : BitVec 64 := 0x1000#64
  let workPtr : BitVec 64 := 0x2000#64
  let workCap : Nat := 16384
  let progBytes := BVProg.wordsToBytesLE BitblastRefTest.smallWs
  let padGap := workPtr.toNat - (progPtr.toNat + progBytes.length)
  let m0 : Mem 64 := (progBytes ++ List.replicate padGap 0 ++ List.replicate workCap 0).At progPtr
  match interpFunc linkedPlainBitblastModule 200000 Driver.bv_init_workspace_body
      (workPtr, workPtr, BitVec.ofNat 64 workCap, progPtr, ()) m0 with
  | .ok (true, ()) m1 =>
    match readMemU32 m1 (workPtr + 104), readMemU32 m1 (workPtr + 108) with
    | some aigCap, some htMask =>
      let htSlots := htMask.toNat + 1
      htSlots >= 2 * aigCap.toNat && (htSlots &&& htMask.toNat) == 0 && aigCap.toNat > 0
    | _, _ => false
  | _ => false

#guard testWorkspaceHtSizing

/-! ## 4. End-to-End `bv_solve_bytes` Linked with `Kissat.Plain` via `interpModule` -/

private def runSolveExpr (e : BVLogicalExpr) (progPtr workPtr : BitVec 64) (workCap : Nat)
    (fuel : UInt64 := 500000) : Option (UInt64 × Option UInt64) :=
  match BVProg.encode e with
  | none => none
  | some ws =>
    let progBytes := BVProg.wordsToBytesLE ws
    let total := (workPtr.toNat - progPtr.toNat) + workCap
    let padGap := workPtr.toNat - (progPtr.toNat + progBytes.length)
    let initBytes := progBytes ++ List.replicate padGap 0 ++ List.replicate workCap 0
    if initBytes.length != total then none
    else
      let m0 : Mem 64 := initBytes.At progPtr
      let args : Tup Val [i64, i64, i64, i64, i64] :=
        (progPtr, BitVec.ofNat 64 progBytes.length, workPtr, BitVec.ofNat 64 workCap, fuel, ())
      match interpModule linkedPlainBitblastModule 800000 "bv_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] args m0 with
      | .ok (r, ()) m' =>
        let pad := (8 - (workPtr.toNat % 8)) % 8
        let magic := readMemU64 m' (workPtr + BitVec.ofNat 64 pad)
        some (UInt64.ofBitVec r, magic)
      | _ => none

-- Trivial UNSAT (`const false`, `not (x == x)`)
#guard runSolveExpr (.const false) 0x1000#64 0x2000#64 4096 == some (20, some 0x2000)
#guard runSolveExpr (.not (.literal (.bin (.var 0 : BVExpr 4) .eq (.var 0 : BVExpr 4))))
  0x1000#64 0x2000#64 4096 == some (20, some 0x2000)

-- Trivial SAT (`const true`, `not (const false)`, `gate .or (.const true) ...`)
#guard match runSolveExpr (.const true) 0x1000#64 0x2000#64 4096 with
  | some (10, some m) => m == UInt64.ofBitVec bvTrivialSatMagic
  | _ => false
#guard match runSolveExpr
    (.gate .or (.not (.const false)) (.literal (.getLsbD (.var 0 : BVExpr 4) 0)))
    0x1000#64 0x2000#64 4096 with
  | some (10, some m) => m == UInt64.ofBitVec bvTrivialSatMagic
  | _ => false

-- Non-trivial UNSAT using `var`, `const`, `eq`, `getLsbD`, `not`, `gate .and/.xor/.beq/.or`, `ite`
private def nonTrivGateUnsat : BVLogicalExpr :=
  let x : BVExpr 2 := .var 0
  let y : BVExpr 2 := .var 1
  let c1 := .literal (.bin x .eq (.const 1#2))
  let c2 := .literal (.bin y .eq (.const 2#2))
  let c3 := .literal (.bin x .eq y)
  .gate .and c1 (.gate .and c2 c3)

private def nonTrivIteUnsat : BVLogicalExpr :=
  let x : BVExpr 2 := .var 0
  let b0 := .literal (.getLsbD x 0)
  let b1 := .literal (.getLsbD x 1)
  let eq3 := .literal (.bin x .eq (.const 3#2))
  .gate .and (.ite b0 eq3 (.const false)) (.gate .and (.not b1) (.gate .beq b0 (.const true)))

#guard (runSolveExpr nonTrivGateUnsat 0x1000#64 0x2000#64 8192).map (·.1) == some 20
#guard (runSolveExpr nonTrivIteUnsat 0x1000#64 0x2000#64 8192).map (·.1) == some 20

-- Non-trivial UNSAT with unaligned `prog_ptr` and `work_ptr`
#guard (runSolveExpr nonTrivGateUnsat 0x1001#64 0x2003#64 8192).map (·.1) == some 20

-- Non-trivial SAT using `var`, `const`, `not`, `eq`, `gate .xor`
private def nonTrivGateSat : BVLogicalExpr :=
  let x : BVExpr 4 := .var 0
  let nx : BVExpr 4 := .un .not x
  .gate .and (.literal (.bin nx .eq (.const 0xA#4))) (.literal (.getLsbD x 0))

#guard (runSolveExpr nonTrivGateSat 0x1000#64 0x2000#64 8192).map (·.1) == some 10

-- Malformed BVP1 passed to `bv_solve_bytes` cleanly returns 0
#guard match interpModule linkedPlainBitblastModule 10000 "bv_solve_bytes"
    [i64, i64, i64, i64, i64] [i64]
    (0x1000#64, 32#64, 0x2000#64, 4096#64, 1000#64, ())
    ((List.replicate 8192 0).At 0x1000#64) with
  | .ok (0#64, ()) _ => true
  | _ => false

/-! ## 4b. All-32-Opcode `BVExpr.eval` vs `bv_solve_bytes` Parity Suite -/

private def checkEvalParity (e : BVLogicalExpr) (assign : BVExpr.Assignment)
    (vars : List (Nat × (w : Nat) × BitVec w)) : Bool :=
  let eqs := vars.foldl (fun acc ⟨id, w, v⟩ =>
    BVLogicalExpr.gate .and acc (.literal (.bin (.var id : BVExpr w) .eq (.const v))))
    (.const true)
  let query := BVLogicalExpr.gate .and eqs (if e.eval assign then .not e else e)
  (runSolveExpr query 0x1000#64 0x4000#64 65536 400000).map (·.1) == some 20

private def mkAssign4 (v0 v1 : BitVec 4) (v2 : BitVec 3) : BVExpr.Assignment :=
  Lean.RArray.branch 1 (.leaf ⟨v0⟩) (.branch 2 (.leaf ⟨v1⟩) (.leaf ⟨v2⟩))

private def all32OpChecks : Bool :=
  let x : BVExpr 4 := .var 0
  let y : BVExpr 4 := .var 1
  let s : BVExpr 3 := .var 2
  let a := mkAssign4 0xB#4 0x5#4 2#3
  let vs : List (Nat × (w : Nat) × BitVec w) := [(0, ⟨4, 0xB#4⟩), (1, ⟨4, 0x5#4⟩), (2, ⟨3, 2#3⟩)]
  let a0 := mkAssign4 0xB#4 0#4 2#3
  let vs0 : List (Nat × (w : Nat) × BitVec w) := [(0, ⟨4, 0xB#4⟩), (1, ⟨4, 0#4⟩), (2, ⟨3, 2#3⟩)]
  let pEq {w : Nat} (e : BVExpr w) (v : BitVec w) : BVLogicalExpr :=
    .literal (.bin e .eq (.const v))
  let ops : List BVLogicalExpr :=
    [ pEq x (x.eval a)
    , pEq (.const 0xD#4) 0xD#4
    , pEq (.extract 1 2 x) ((BVExpr.extract 1 2 x).eval a)
    , pEq (.bin x .and y) ((BVExpr.bin x .and y).eval a)
    , pEq (.bin x .or y) ((BVExpr.bin x .or y).eval a)
    , pEq (.bin x .xor y) ((BVExpr.bin x .xor y).eval a)
    , pEq (.bin x .add y) ((BVExpr.bin x .add y).eval a)
    , pEq (.bin x .mul y) ((BVExpr.bin x .mul y).eval a)
    , pEq (.bin x .udiv y) ((BVExpr.bin x .udiv y).eval a)
    , pEq (.bin x .umod y) ((BVExpr.bin x .umod y).eval a)
    , pEq (.un .not x) ((BVExpr.un .not x).eval a)
    , pEq (.un (.rotateLeft 1) x) ((BVExpr.un (.rotateLeft 1) x).eval a)
    , pEq (.un (.rotateRight 1) x) ((BVExpr.un (.rotateRight 1) x).eval a)
    , pEq (.un (.arithShiftRightConst 1) x) ((BVExpr.un (.arithShiftRightConst 1) x).eval a)
    , pEq (.un .reverse x) ((BVExpr.un .reverse x).eval a)
    , pEq (.un .clz x) ((BVExpr.un .clz x).eval a)
    , pEq (.un .cpop x) ((BVExpr.un .cpop x).eval a)
    , pEq (.append x y rfl) ((BVExpr.append x y rfl).eval a)
    , pEq (.replicate 2 x rfl) ((BVExpr.replicate 2 x rfl).eval a)
    , pEq (.shiftLeft x s) ((BVExpr.shiftLeft x s).eval a)
    , pEq (.shiftRight x s) ((BVExpr.shiftRight x s).eval a)
    , pEq (.arithShiftRight x s) ((BVExpr.arithShiftRight x s).eval a)
    , .literal (.bin x .ult y)
    , .literal (.bin y .ult x)
    , .literal (.getLsbD x 3)
    , .literal (.getLsbD x 7)
    , .const true
    , .not (.const false)
    , .gate .and (.literal (.bin y .ult x)) (.literal (.getLsbD x 0))
    , .gate .xor (.literal (.bin y .ult x)) (.literal (.getLsbD x 2))
    , .gate .beq (.literal (.bin y .ult x)) (.literal (.getLsbD x 3))
    , .gate .or (.literal (.bin x .ult y)) (.literal (.getLsbD x 1))
    , .ite (.literal (.getLsbD x 3)) (.literal (.bin y .ult x)) (.const false) ]
  let div0 : List BVLogicalExpr :=
    [ pEq (.bin x .udiv y) ((BVExpr.bin x .udiv y).eval a0)
    , pEq (.bin x .umod y) ((BVExpr.bin x .umod y).eval a0) ]
  ops.all (fun e => checkEvalParity e a vs) && div0.all (fun e => checkEvalParity e a0 vs0)

#guard all32OpChecks

-- Real symbolic 32-op UNSAT & SAT identities (not just fixed-assignment)
private def symAddCommUnsat : BVLogicalExpr :=
  let x : BVExpr 4 := .var 0; let y : BVExpr 4 := .var 1
  .not (.literal (.bin (.bin x .add y) .eq (.bin y .add x)))

private def symMulCommUnsat : BVLogicalExpr :=
  let x : BVExpr 3 := .var 0; let y : BVExpr 3 := .var 1
  .not (.literal (.bin (.bin x .mul y) .eq (.bin y .mul x)))

private def symDivModUnsat : BVLogicalExpr :=
  let x : BVExpr 3 := .var 0; let y : BVExpr 3 := .var 1
  let lhs := BVExpr.bin (.bin (.bin x .udiv y) .mul y) .add (.bin x .umod y)
  .not (.literal (.bin lhs .eq x))

private def symCpopRevUnsat : BVLogicalExpr :=
  let x : BVExpr 4 := .var 0
  .not (.literal (.bin (.un .cpop x) .eq (.un .cpop (.un .reverse x))))

#guard (runSolveExpr symAddCommUnsat 0x1000#64 0x4000#64 65536 500000).map (·.1) == some 20
#guard (runSolveExpr symMulCommUnsat 0x1000#64 0x4000#64 65536 500000).map (·.1) == some 20
#guard (runSolveExpr symDivModUnsat 0x1000#64 0x4000#64 65536 800000).map (·.1) == some 20
#guard (runSolveExpr symCpopRevUnsat 0x1000#64 0x4000#64 65536 500000).map (·.1) == some 20

/-! ## 5. Single-Line `#print axioms` Audit (`<= std3`, `< 115c`) -/

theorem audit_validate_wf : ∀ f ∈ Validate.fns, f.Wf := Validate.fns_wf
theorem audit_aig_wf : ∀ f ∈ Aig.fns, f.Wf := Aig.fns_wf
theorem audit_tseitin_wf : ∀ f ∈ Tseitin.fns, f.Wf := Tseitin.fns_wf
theorem audit_driver_wf : ∀ f ∈ Driver.fns, f.Wf := Driver.fns_wf
theorem audit_mod_wf : ∀ f ∈ bitblastModule.fns, f.Wf := bitblastModule_wf
theorem audit_acyclic : bitblastModule.checkAcyclic = true := bitblastModule_checkAcyclic

#print axioms audit_validate_wf
#print axioms audit_aig_wf
#print axioms audit_tseitin_wf
#print axioms audit_driver_wf
#print axioms audit_mod_wf
#print axioms audit_acyclic

end LeanQbeTest.T.BitblastSrcTest
