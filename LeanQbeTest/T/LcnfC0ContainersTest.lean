module

import LeanQbe.T.InterpKissat
import LeanQbe.T.LeanLCNF.LcnfC0Containers
import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof
import LeanQbe.T.LeanLCNF.LcnfC0Rt
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.LeanLCNF.LcnfC0Containers
meta import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof
meta import LeanQbe.T.LeanLCNF.LcnfC0Rt
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Runtime Execution, Printing & Axiom Audit for `LcnfC0Containers` (Milestone R2 Part 1)

Exercises `rtR2Mod` and the combined `rtR0R2Mod` module across:
1. `checkAcyclic`, `PrintCpp.ppTModule`, and `PrintQbe.module`.
2. Concrete `interpModule rtR0R2Mod` execution covering all 14 public R2 targets (`ByteArray`
   tag `248` / `m_other = 1`, `Array` tag `246`, COW exclusive vs shared copy, growth, and
   `lcnf_oob` / `lcnf_panic` exits).
3. Strict `std3` `#print axioms` audit of `rtR2Mod_moduleOk`, all 14 `*_sound` theorems, and all
   8 concrete `Mem 64` non-vacuity theorems (`XPost := False`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LcnfC0ContainersTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF

meta def rtR0R2Mod : Module :=
  { fns := rtR0Mod.fns ++ rtR2Mod.fns, externs := [], exits := ["lcnf_panic"] }

meta def rdU8 (m : Mem 64) (a : BitVec 64) : UInt8 :=
  (m.get? a).getD 0

meta def rdU32 (m : Mem 64) (a : BitVec 64) : BitVec 32 :=
  let b0 := BitVec.ofNat 32 (rdU8 m a).toNat
  let b1 := BitVec.ofNat 32 (rdU8 m (a + 1#64)).toNat
  let b2 := BitVec.ofNat 32 (rdU8 m (a + 2#64)).toNat
  let b3 := BitVec.ofNat 32 (rdU8 m (a + 3#64)).toNat
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

meta def rdU64 (m : Mem 64) (a : BitVec 64) : BitVec 64 :=
  let lo := BitVec.zeroExtend 64 (rdU32 m a)
  let hi := BitVec.zeroExtend 64 (rdU32 m (a + 4#64))
  lo ||| (hi <<< 32)

meta def rdBytes (m : Mem 64) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => rdU8 m (a + BitVec.ofNat 64 i)

meta def rdU64List (m : Mem 64) (a : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map fun i => rdU64 m (a + BitVec.ofNat 64 (8 * i))

meta def runOk (fn : Sym) (as : List Ty) (args : Tup Val as) (m : Mem 64) :
    Option (BitVec 64 × Mem 64) :=
  match interpModule rtR0R2Mod 50000 fn as [i64] args m with
  | .ok (r, ()) m' => some (r, m')
  | _ => none

meta def run1 (fn : Sym) (a1 : BitVec 64) (m : Mem 64) : Option (BitVec 64 × Mem 64) :=
  runOk fn [i64] (a1, ()) m

meta def run2 (fn : Sym) (a1 a2 : BitVec 64) (m : Mem 64) : Option (BitVec 64 × Mem 64) :=
  runOk fn [i64, i64] (a1, a2, ()) m

meta def run3 (fn : Sym) (a1 a2 a3 : BitVec 64) (m : Mem 64) : Option (BitVec 64 × Mem 64) :=
  runOk fn [i64, i64, i64] (a1, a2, a3, ()) m

meta def run4 (fn : Sym) (a1 a2 a3 a4 : BitVec 64) (m : Mem 64) : Option (BitVec 64 × Mem 64) :=
  runOk fn [i64, i64, i64, i64] (a1, a2, a3, a4, ()) m

meta def run5 (fn : Sym) (a1 a2 a3 a4 a5 : BitVec 64) (m : Mem 64) :
    Option (BitVec 64 × Mem 64) :=
  runOk fn [i64, i64, i64, i64, i64] (a1, a2, a3, a4, a5, ()) m

meta def isPanic2 (fn : Sym) (a1 a2 : BitVec 64) (m : Mem 64) (code : BitVec 64) : Bool :=
  match interpModule rtR0R2Mod 50000 fn [i64, i64] [i64] (a1, a2, ()) m with
  | .exit "lcnf_panic" (as := [.bits 64, .bits 64]) (rt, c, ()) _ => rt == nvRtAddr && c == code
  | _ => false

meta def isPanic5 (fn : Sym) (a1 a2 a3 a4 a5 : BitVec 64) (m : Mem 64)
    (code : BitVec 64) : Bool :=
  match interpModule rtR0R2Mod 50000 fn [i64, i64, i64, i64, i64] [i64]
      (a1, a2, a3, a4, a5, ()) m with
  | .exit "lcnf_panic" (as := [.bits 64, .bits 64]) (rt, c, ()) _ => rt == nvRtAddr && c == code
  | _ => false

/-! ## 1. Acyclicity & C++ / QBE Printer Checks -/

#guard rtR2Mod.fns.length == 22
#guard rtR2Mod.checkAcyclic
#guard rtR0R2Mod.checkAcyclic
#guard (PrintCpp.ppTModule rtR2Mod).isOk
#guard (PrintQbe.module rtR2Mod).isOk
#guard (PrintCpp.ppTModule rtR0R2Mod).isOk
#guard (PrintQbe.module rtR0R2Mod).isOk

/-! ## 2. `lcnf_oob` & `ByteArray` (`tag 248`, `m_other = 1`) Execution Tests -/

#guard
  let m0 := nvR2RtBytes.At nvRtAddr
  (run2 "lcnf_oob" nvRtAddr 3#64 m0).map (·.1) == some 3#64 &&
  (run2 "lcnf_oob" nvRtAddr 0#64 m0).map (·.1) == some 0#64 &&
  (match run2 "lcnf_oob" nvRtAddr nvBa1Addr nvBaSlabMem with
   | some (r, m1) => r == nvBa1Addr && rdU32 m1 nvBa1Addr == 2#32
   | none => false) &&
  isPanic2 "lcnf_ba_mk_empty" nvRtAddr ((1#64 <<< 61) ||| 1#64) m0 2#64

#guard
  let m0 := nvR2RtBytes.At nvRtAddr
  match run1 "lcnf_ba_empty" nvRtAddr m0 with
  | none => false
  | some (p0, m1) =>
    match run1 "lcnf_ba_empty" nvRtAddr m1 with
    | none => false
    | some (p1, m2) =>
      p0 != 0#64 && p0 == p1 &&
      rdU32 m1 p0 == 0#32 &&
      rdU8 m1 (p0 + 7#64) == 248 &&
      rdU64 m1 (p0 + 8#64) == 0#64 &&
      rdU64 m1 (p0 + 16#64) == 0#64 &&
      rdU64 m1 (nvRtAddr + 33544#64) == p0 &&
      rdU64 m2 (nvRtAddr + 33544#64) == p0

#guard
  let m0 := nvR2RtBytes.At nvRtAddr
  match run2 "lcnf_ba_mk_empty" nvRtAddr 5#64 m0 with
  | none => false
  | some (b0, m1) =>
    match run3 "lcnf_ba_push" nvRtAddr b0 10#64 m1 with
    | none => false
    | some (b1, m2) =>
      match run3 "lcnf_ba_push" nvRtAddr b1 20#64 m2 with
      | none => false
      | some (b2, m3) =>
        match run3 "lcnf_ba_push" nvRtAddr b2 30#64 m3 with
        | none => false
        | some (b3, m4) =>
          b1 == b0 && b2 == b0 && b3 != b0 &&
          rdU64 m4 (b3 + 8#64) == 3#64 &&
          rdBytes m4 (b3 + 24#64) 3 == [10, 20, 30]

#guard
  match run2 "lcnf_ba_mk" nvRtAddr nvArr1Addr nvArrSlabMem with
  | none => false
  | some (ba, m1) =>
    ba != 0#64 &&
    rdU32 m1 ba == 1#32 &&
    rdU8 m1 (ba + 7#64) == 248 &&
    rdU64 m1 (ba + 8#64) == 2#64 &&
    rdBytes m1 (ba + 24#64) 2 == [1, 2]

#guard
  (run4 "lcnf_ba_get" nvRtAddr nvBa1Addr 1#64 1#64 nvBaSlabMem).map (·.1) == some 66#64 &&
  (run4 "lcnf_ba_get" nvRtAddr nvBa1Addr 1#64 0#64 nvBaSlabMem).map (·.1) == some 65#64 &&
  (run4 "lcnf_ba_get" nvRtAddr nvBa1Addr 5#64 1#64 nvBaSlabMem).map (·.1) == some 0#64

#guard
  match run5 "lcnf_ba_set" nvRtAddr nvBa1Addr 1#64 90#64 1#64 nvBaSlabMem with
  | none => false
  | some (r1, m1) =>
    match run5 "lcnf_ba_set" nvRtAddr nvBa2Addr 0#64 88#64 1#64 m1 with
    | none => false
    | some (r2, m2) =>
      let rOob := (run5 "lcnf_ba_set" nvRtAddr r1 9#64 1#64 1#64 m2).map (·.1)
      r1 == nvBa1Addr && r2 != nvBa2Addr &&
      rdBytes m1 (r1 + 24#64) 2 == [65, 90] &&
      rdU32 m2 nvBa2Addr == 1#32 &&
      rdBytes m2 (nvBa2Addr + 24#64) 2 == [65, 66] &&
      rdU32 m2 r2 == 1#32 &&
      rdBytes m2 (r2 + 24#64) 2 == [88, 66] &&
      (run4 "lcnf_ba_cmp_op" nvRtAddr 0#64 nvBa1Addr nvBa2Addr m2).map (·.1) == some 0#64 &&
      (run4 "lcnf_ba_cmp_op" nvRtAddr 0#64 nvBa1Addr nvBa1Addr m2).map (·.1) == some 1#64 &&
      (run4 "lcnf_ba_cmp_op" nvRtAddr 1#64 nvBa2Addr r1 m2).map (·.1) == some 1#64 &&
      (run4 "lcnf_ba_cmp_op" nvRtAddr 2#64 nvBa2Addr r1 m2).map (·.1) == some 0#64 &&
      (run4 "lcnf_ba_cmp_op" nvRtAddr 2#64 r1 nvBa2Addr m2).map (·.1) == some 2#64 &&
      rOob == some r1

#guard
  match run3 "lcnf_ba_push" nvRtAddr nvBa2Addr 67#64 nvBaSlabMem with
  | none => false
  | some (r, m1) =>
    r != nvBa2Addr &&
    rdU32 m1 nvBa2Addr == 1#32 &&
    rdBytes m1 (nvBa2Addr + 24#64) 2 == [65, 66] &&
    rdU32 m1 r == 1#32 &&
    rdU64 m1 (r + 8#64) == 3#64 &&
    rdBytes m1 (r + 24#64) 3 == [65, 66, 67]

/-! ## 3. `Array` (`tag 246`) Execution Tests -/

#guard
  let m0 := nvR2RtBytes.At nvRtAddr
  match run2 "lcnf_array_mk_empty" nvRtAddr 3#64 m0 with
  | none => false
  | some (a0, m1) =>
    match run3 "lcnf_array_push" nvRtAddr a0 11#64 m1 with
    | none => false
    | some (a1, m2) =>
      match run3 "lcnf_array_push" nvRtAddr a1 13#64 m2 with
      | none => false
      | some (a2, m3) =>
        a0 != 0#64 && a1 == a0 && a2 != a0 &&
        rdU32 m3 a2 == 1#32 &&
        rdU8 m3 (a2 + 7#64) == 246 &&
        rdU64 m3 (a2 + 8#64) == 2#64 &&
        rdU64List m3 (a2 + 24#64) 2 == [11#64, 13#64]

#guard
  (run5 "lcnf_array_get" nvRtAddr 1#64 nvArr1Addr 1#64 3#64 nvArrSlabMem).map (·.1) ==
    some 5#64 &&
  (run5 "lcnf_array_get" nvRtAddr 1#64 nvArr1Addr 1#64 1#64 nvArrSlabMem).map (·.1) ==
    some 3#64 &&
  (run5 "lcnf_array_get" nvRtAddr 1#64 nvArr1Addr 5#64 1#64 nvArrSlabMem).map (·.1) ==
    some 1#64 &&
  (run5 "lcnf_array_get" nvRtAddr 0#64 nvArr1Addr 5#64 1#64 nvArrSlabMem).map (·.1) ==
    some 0#64 &&
  (match run5 "lcnf_array_get" nvRtAddr nvArr2Addr nvArr1Addr 5#64 1#64 nvArrSlabMem with
   | some (r, m1) => r == nvArr2Addr && rdU32 m1 nvArr2Addr == 2#32
   | none => false) &&
  (match run5 "lcnf_array_get" nvRtAddr nvArr2Addr nvArr1Addr 5#64 0#64 nvArrSlabMem with
   | some (r, m1) => r == nvArr2Addr && rdU32 m1 nvArr2Addr == 3#32
   | none => false)

#guard
  match run5 "lcnf_array_set" nvRtAddr nvArr1Addr 1#64 9#64 1#64 nvArrSlabMem with
  | none => false
  | some (a1, m1) =>
    match run5 "lcnf_array_set" nvRtAddr nvArr2Addr 0#64 11#64 1#64 m1 with
    | none => false
    | some (a2, m2) =>
      a1 == nvArr1Addr && a2 != nvArr2Addr &&
      rdU64List m2 (a1 + 24#64) 2 == [3#64, 9#64] &&
      rdU32 m2 nvArr2Addr == 1#32 &&
      rdU64List m2 (nvArr2Addr + 24#64) 2 == [3#64, 5#64] &&
      rdU64List m2 (a2 + 24#64) 2 == [11#64, 5#64]

#guard
  match run3 "lcnf_array_push" nvRtAddr nvArr2Addr 7#64 nvArrSlabMem with
  | none => false
  | some (r, m1) =>
    r != nvArr2Addr &&
    rdU32 m1 nvArr2Addr == 1#32 &&
    rdU64List m1 (nvArr2Addr + 24#64) 2 == [3#64, 5#64] &&
    rdU64 m1 (r + 8#64) == 3#64 &&
    rdU64List m1 (r + 24#64) 3 == [3#64, 5#64, 7#64]

#guard
  match run2 "lcnf_array_pop" nvRtAddr nvArr1Addr nvArrSlabMem with
  | none => false
  | some (a1, m1) =>
    match run2 "lcnf_array_pop" nvRtAddr nvArr2Addr m1 with
    | none => false
    | some (a2, m2) =>
      a1 == nvArr1Addr && a2 != nvArr2Addr &&
      rdU64 m2 (a1 + 8#64) == 1#64 &&
      rdU64 m2 (a1 + 24#64) == 3#64 &&
      rdU32 m2 nvArr2Addr == 1#32 &&
      rdU64 m2 (nvArr2Addr + 8#64) == 2#64 &&
      rdU64 m2 (a2 + 8#64) == 1#64 &&
      rdU64 m2 (a2 + 24#64) == 3#64

#guard
  match run5 "lcnf_array_swap" nvRtAddr nvArr1Addr 1#64 3#64 1#64 nvArrSlabMem with
  | none => false
  | some (a1, m1) =>
    match run5 "lcnf_array_swap" nvRtAddr nvArr2Addr 1#64 3#64 1#64 m1 with
    | none => false
    | some (a2, m2) =>
      let rSafe := (run5 "lcnf_array_swap" nvRtAddr a1 1#64 9#64 1#64 m2).map (·.1)
      a1 == nvArr1Addr && a2 != nvArr2Addr &&
      rdU64List m2 (a1 + 24#64) 2 == [5#64, 3#64] &&
      rdU32 m2 nvArr2Addr == 1#32 &&
      rdU64List m2 (nvArr2Addr + 24#64) 2 == [3#64, 5#64] &&
      rdU64List m2 (a2 + 24#64) 2 == [5#64, 3#64] &&
      rSafe == some a1 &&
      isPanic5 "lcnf_array_swap" nvRtAddr a1 1#64 9#64 0#64 m2 7#64

/-! ## 4. Strict `std3` Axiom Audits -/

#print axioms rtR2Mod_moduleOk
#print axioms lcnf_oob_sound
#print axioms lcnf_ba_empty_sound
#print axioms lcnf_ba_mk_empty_sound
#print axioms lcnf_ba_mk_sound
#print axioms lcnf_ba_get_sound
#print axioms lcnf_ba_set_sound
#print axioms lcnf_ba_push_sound
#print axioms lcnf_ba_cmp_op_sound
#print axioms lcnf_array_mk_empty_sound
#print axioms lcnf_array_get_sound
#print axioms lcnf_array_set_sound
#print axioms lcnf_array_push_sound
#print axioms lcnf_array_pop_sound
#print axioms lcnf_array_swap_sound
#print axioms nv_lcnf_ba_empty
#print axioms nv_lcnf_ba_push_excl
#print axioms nv_lcnf_ba_push_shared
#print axioms nv_lcnf_ba_set_excl
#print axioms nv_lcnf_ba_get_and_cmp
#print axioms nv_lcnf_array_push_excl
#print axioms nv_lcnf_array_push_shared
#print axioms nv_lcnf_array_ops_and_oob

end LeanQbeTest.T.LcnfC0ContainersTest
