module

public import LeanQbe.T.InterpKissat
public import LeanQbe.T.LeanLCNF.LcnfC0Ffi
public import LeanQbe.T.LeanLCNF.LcnfC0FfiSpec
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof1
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof2
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.LeanLCNF.LcnfC0Ffi
meta import LeanQbe.T.LeanLCNF.LcnfC0FfiSpec
meta import LeanQbe.T.LeanLCNF.LcnfC0FfiProof1
meta import LeanQbe.T.LeanLCNF.LcnfC0FfiProof2
meta import LeanQbe.T.LeanLCNF.LcnfC0FfiProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Verification & Interpreter Tests for `LcnfC0Ffi` (`Shard F2`)

* Structural and emission checks on `ffiMod` and `rtC0WithFfiMod` (`PrintCpp`, `PrintQbe`).
* Pure sentineled-`Nat` (`natOfBytesS` / `bytesOfNatS`) boundary `#guard` checks:
  empty `[]`, trailing `0x00` bytes, `L=7` tagged boundary, `L=8` boxed boundary, `L=32`
  multi-limb payloads, and invalid non-sentineled `Nat` rejection (`0`, `2`, `0xff`, `0x200`).
* Executable `interpModule rtC0WithFfiMod` tests on `nvFfiMem` exercising top-down `s_end`
  carve/reclaim, non-aborting OOM, invalid-input rejection, `L<=7` vs `L>=8` sentineled `Nat`
  marshaling, and full `ByteArray -> Nat -> ByteArray` round-trips.
* Strict `std3` `#print axioms` audits across all F2 modules.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LcnfC0FfiTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Structural & Codegen Checks (`ffiMod`, `rtC0WithFfiMod`) -/

#guard ffiMod.checkAcyclic
#guard ffiMod.fns.length == 15
#guard ffiMod.exits.isEmpty
#guard ffiMod.fns.all (fun fn => fn.as.length ≤ 6)
#guard rtC0WithFfiMod.checkAcyclic
#guard (PrintCpp.ppTModule ffiMod).isOk
#guard (PrintQbe.module ffiMod).isOk
#guard (PrintCpp.ppTModule rtC0WithFfiMod).isOk

/-! ## 2. Pure Sentineled-`Nat` Math (`natOfBytesS` / `bytesOfNatS`) -/

#guard natOfBytesS [] == 1
#guard bytesOfNatS 1 == some []
#guard natOfBytesS [0] == 256
#guard bytesOfNatS 256 == some [0]
#guard natOfBytesS [0, 0, 0] == 2 ^ 24
#guard bytesOfNatS (2 ^ 24) == some [0, 0, 0]
#guard natOfBytesS [1, 2, 0, 0] == 1 + 2 * 256 + 2 ^ 32
#guard bytesOfNatS (1 + 2 * 256 + 2 ^ 32) == some [1, 2, 0, 0]

#guard
  let bs7z := List.replicate 7 (0 : UInt8)
  let bs7f := List.replicate 7 (0xff : UInt8)
  let bs7m : List UInt8 := [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0x00]
  natOfBytesS bs7z == 2 ^ 56 &&
  bytesOfNatS (2 ^ 56) == some bs7z &&
  natOfBytesS bs7f == 2 ^ 57 - 1 &&
  bytesOfNatS (2 ^ 57 - 1) == some bs7f &&
  bytesOfNatS (natOfBytesS bs7m) == some bs7m

#guard
  let bs8z := List.replicate 8 (0 : UInt8)
  let bs8f := List.replicate 8 (0xff : UInt8)
  natOfBytesS bs8z == 2 ^ 64 &&
  bytesOfNatS (2 ^ 64) == some bs8z &&
  natOfBytesS bs8f == 2 ^ 65 - 1 &&
  bytesOfNatS (2 ^ 65 - 1) == some bs8f

#guard
  let bs32 := (List.range 32).map (fun i => UInt8.ofNat (i * 17 + 1))
  let bs32z := List.replicate 32 (0 : UInt8)
  bytesOfNatS (natOfBytesS bs32) == some bs32 &&
  natOfBytesS bs32z == 2 ^ 256 &&
  bytesOfNatS (2 ^ 256) == some bs32z

#guard bytesOfNatS 0 == none
#guard bytesOfNatS 2 == none
#guard bytesOfNatS 0xff == none
#guard bytesOfNatS 0x100 == some [0]
#guard bytesOfNatS 0x200 == none
#guard !isValidNatBytesS 0 && isValidNatBytesS 1 && !isValidNatBytesS 0x200
#guard sentinelByteIdx 1#64 == 0
#guard sentinelByteIdx (1#64 <<< 56) == 7
#guard sentinelByteIdx 0x01deadbeef#64 == 4
#guard sentinelByteIdx 0#64 == 8
#guard sentinelByteIdx 2#64 == 8

/-! ## 3. Executable `interpModule rtC0WithFfiMod` Tests on `nvFfiMem` -/

private def run1 (name : Sym) (a0 : BitVec 64) (m : Mem 64) : Option (BitVec 64 × Mem 64) :=
  match interpModule rtC0WithFfiMod 100000 name [i64] [i64] (a0, ()) m with
  | .ok (r, ()) m' => some (r, m')
  | _ => none

private def run2 (name : Sym) (a0 a1 : BitVec 64) (m : Mem 64) :
    Option (BitVec 64 × Mem 64) :=
  match interpModule rtC0WithFfiMod 100000 name [i64, i64] [i64] (a0, a1, ()) m with
  | .ok (r, ()) m' => some (r, m')
  | _ => none

private def run2Void (name : Sym) (a0 a1 : BitVec 64) (m : Mem 64) : Option (Mem 64) :=
  match interpModule rtC0WithFfiMod 100000 name [i64, i64] [] (a0, a1, ()) m with
  | .ok () m' => some m'
  | _ => none

private def run3 (name : Sym) (a0 a1 a2 : BitVec 64) (m : Mem 64) :
    Option (BitVec 64 × Mem 64) :=
  match interpModule rtC0WithFfiMod 100000 name [i64, i64, i64] [i64] (a0, a1, a2, ()) m with
  | .ok (r, ()) m' => some (r, m')
  | _ => none

private def writeBytes (a : BitVec 64) : List UInt8 → Mem 64 → Mem 64
  | [], m => m
  | b :: bs, m => writeBytes (a + 1#64) bs (m.insert a b)

private def rdU8 (m : Mem 64) (a : BitVec 64) : UInt8 :=
  (loadVal m i8 a).map (fun x => UInt8.ofNat x.toNat) |>.getD 0

private def rdU32 (m : Mem 64) (a : BitVec 64) : BitVec 32 :=
  (loadVal m i32 a).getD 0#32

private def rdU64 (m : Mem 64) (a : BitVec 64) : BitVec 64 :=
  (loadVal m i64 a).getD 0#64

private def rdBytes (m : Mem 64) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => rdU8 m (a + BitVec.ofNat 64 i)

private def rdFfiOkVal (m : Mem 64) (okP : BitVec 64) : Option (BitVec 64) :=
  if okP != 0#64 && (okP &&& 1#64) == 0#64 &&
      rdU32 m okP == 1#32 && rdU8 m (okP + 7#64) == 0 then
    some (rdU64 m (okP + 8#64))
  else none

-- Top-down `s_end` carve (64B), `ByteArray` wrap inside carved arena, and 100% reclaim.
#guard
  match run2 "lcnf_ffi_carve_scratch" nvFfiBase 64#64 nvFfiMem with
  | none => false
  | some (wptr, m1) =>
    let end1 := (run1 "lcnf_ffi_get_end" nvFfiBase m1).map (·.1)
    let m1s := writeBytes wptr [10, 20, 30] m1
    match run3 "lcnf_ffi_ba_wrap_ok" nvFfiBase wptr 3#64 m1s with
    | none => false
    | some (okP, m2) =>
      match rdFfiOkVal m2 okP with
      | none => false
      | some ba =>
        match run2Void "lcnf_ffi_restore_scratch" nvFfiBase nvFfiScr m2 with
        | none => false
        | some m3 =>
          let end3 := (run1 "lcnf_ffi_get_end" nvFfiBase m3).map (·.1)
          wptr == nvFfiScr - 64#64 &&
          end1 == some (nvFfiScr - 64#64) &&
          rdU8 m3 (ba + 7#64) == 248 &&
          rdU64 m3 (ba + 8#64) == 3#64 &&
          rdBytes m3 (ba + 24#64) 3 == [10, 20, 30] &&
          end3 == some nvFfiScr

-- Non-aborting OOM and invalid-input guards (never trigger `lcnf_panic`).
#guard
  let oomCarve := run2 "lcnf_ffi_carve_scratch" nvFfiBase 512#64 nvFfiMem
  let oomBaWrap := run3 "lcnf_ffi_ba_wrap_ok" nvFfiBase nvFfiScr 248#64 nvFfiMem
  let oomNat := run3 "lcnf_ffi_nat_of_bytes" nvFfiBase nvFfiScr 248#64 nvFfiMem
  let oomNatWrap := run3 "lcnf_ffi_nat_wrap_ok" nvFfiBase nvFfiScr 248#64 nvFfiMem
  let inv0 := (run2 "lcnf_ffi_nat_s_to_ba" nvFfiBase 1#64 nvFfiMem).map (·.1)
  let inv2 := (run2 "lcnf_ffi_nat_s_to_ba" nvFfiBase 5#64 nvFfiMem).map (·.1)
  let inv512 := (run2 "lcnf_ffi_nat_s_to_ba" nvFfiBase 0x401#64 nvFfiMem).map (·.1)
  let lenInv := (run1 "lcnf_ffi_nat_bytes_len" 1#64 nvFfiMem).map (·.1)
  oomCarve.map (·.1) == some 0#64 &&
  oomBaWrap.map (·.1) == some ffiResOomWord &&
  oomNat.map (·.1) == some 0#64 &&
  oomNatWrap.map (·.1) == some ffiResOomWord &&
  inv0 == some ffiResInvalidInputWord &&
  inv2 == some ffiResInvalidInputWord &&
  inv512 == some ffiResInvalidInputWord &&
  lenInv == some ffiInvalidLen

-- Sentineled `Nat`: `L=0`, `L=3`, `L=7` tagged vs `L=8`, `L=32` zero-copy boxed `MPZ`.
#guard
  let r0 := (run3 "lcnf_ffi_nat_of_bytes" nvFfiBase nvFfiScr 0#64 nvFfiMem).map (·.1)
  let l0 := (run1 "lcnf_ffi_nat_bytes_len" 3#64 nvFfiMem).map (·.1)
  let m3 := writeBytes nvFfiScr [0, 0, 0] nvFfiMem
  let r3 := (run3 "lcnf_ffi_nat_of_bytes" nvFfiBase nvFfiScr 3#64 m3).map (·.1)
  let l3 := r3.bind fun n3 => (run1 "lcnf_ffi_nat_bytes_len" n3 m3).map (·.1)
  let bs7 := List.replicate 7 (0xff : UInt8)
  let m7 := writeBytes nvFfiScr bs7 nvFfiMem
  let r7 := (run3 "lcnf_ffi_nat_of_bytes" nvFfiBase nvFfiScr 7#64 m7).map (·.1)
  let l7 := r7.bind fun n7 => (run1 "lcnf_ffi_nat_bytes_len" n7 m7).map (·.1)
  r0 == some 3#64 && l0 == some 0#64 &&
  r3 == some (BitVec.ofNat 64 (2 * (2 ^ 24) + 1)) && l3 == some 3#64 &&
  r7 == some (BitVec.ofNat 64 (2 * (2 ^ 57 - 1) + 1)) && l7 == some 7#64

#guard
  let bs8 := List.replicate 8 (0 : UInt8)
  let m8 := writeBytes (nvFfiScr + 64#64) bs8 nvFfiMem
  let ok8 := match run3 "lcnf_ffi_nat_of_bytes" nvFfiBase (nvFfiScr + 64#64) 8#64 m8 with
    | some (p8, m8') =>
      let l8 := (run1 "lcnf_ffi_nat_bytes_len" p8 m8').map (·.1)
      let ptr8 := (run2 "lcnf_ffi_nat_bytes_ptr" nvFfiBase p8 m8').map (·.1)
      p8 != 0#64 && (p8 &&& 1#64) == 0#64 &&
      rdU8 m8' (p8 + 7#64) == 250 &&
      rdU32 m8' (p8 + 12#64) == 2#32 &&
      l8 == some 8#64 && ptr8 == some (p8 + 16#64) &&
      rdBytes m8' (p8 + 16#64) 9 == bs8 ++ [1]
    | none => false
  let bs32 := (List.range 32).map (fun i => UInt8.ofNat (i * 11 + 3))
  let m32 := writeBytes (nvFfiScr + 64#64) bs32 nvFfiMem
  let ok32 := match run3 "lcnf_ffi_nat_of_bytes" nvFfiBase (nvFfiScr + 64#64) 32#64 m32 with
    | some (p32, m32') =>
      let l32 := (run1 "lcnf_ffi_nat_bytes_len" p32 m32').map (·.1)
      let ptr32 := (run2 "lcnf_ffi_nat_bytes_ptr" nvFfiBase p32 m32').map (·.1)
      p32 != 0#64 && (p32 &&& 1#64) == 0#64 &&
      rdU8 m32' (p32 + 7#64) == 250 &&
      rdU32 m32' (p32 + 12#64) == 5#32 &&
      l32 == some 32#64 && ptr32 == some (p32 + 16#64) &&
      rdBytes m32' (p32 + 16#64) 33 == bs32 ++ [1]
    | none => false
  ok8 && ok32

-- End-to-end `ByteArray -> Nat -> ByteArray` round-trips across tagged and boxed boundaries.
private def checkBaNatRoundTrip (bs : List UInt8) : Bool :=
  let src := nvFfiScr + 64#64
  let m0 := writeBytes src bs nvFfiMem
  match run3 "lcnf_ffi_ba_of_bytes" nvFfiBase src (BitVec.ofNat 64 bs.length) m0 with
  | none => false
  | some (ba1, m1) =>
    match run2 "lcnf_ffi_ba_to_nat_s" nvFfiBase ba1 m1 with
    | none => false
    | some (ok1, m2) =>
      match rdFfiOkVal m2 ok1 with
      | none => false
      | some natVal =>
        let lenChk := (run1 "lcnf_ffi_nat_bytes_len" natVal m2).map (·.1)
        match run2 "lcnf_ffi_nat_s_to_ba" nvFfiBase natVal m2 with
        | none => false
        | some (ok2, m3) =>
          match rdFfiOkVal m3 ok2 with
          | none => false
          | some ba2 =>
            lenChk == some (BitVec.ofNat 64 bs.length) &&
            rdU8 m3 (ba2 + 7#64) == 248 &&
            rdU64 m3 (ba2 + 8#64) == BitVec.ofNat 64 bs.length &&
            rdBytes m3 (ba2 + 24#64) bs.length == bs

#guard checkBaNatRoundTrip []
#guard checkBaNatRoundTrip [0]
#guard checkBaNatRoundTrip [0, 0, 0]
#guard checkBaNatRoundTrip [0xde, 0xad, 0xbe, 0x00]
#guard checkBaNatRoundTrip (List.replicate 7 0xff)
#guard checkBaNatRoundTrip (List.replicate 8 0)
#guard checkBaNatRoundTrip [1, 0, 2, 0, 3, 0, 4, 0xff]
#guard checkBaNatRoundTrip ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 5)))

/-! ## 4. Strict `std3` Axiom Audits -/

#print axioms ffiMod_fns_wf
#print axioms ffiMod_sysv_args_le_6
#print axioms bytesOfNatS_natOfBytesS
#print axioms natOfBytesS_lt_2p63_iff
#print axioms rtC0Inv_carve_top_split
#print axioms rtC0Inv_restore_top_merge
#print axioms lcnf_ffi_get_end_wp
#print axioms lcnf_ffi_carve_scratch_wp
#print axioms lcnf_ffi_restore_scratch_wp
#print axioms lcnf_ffi_ba_of_bytes_wp
#print axioms lcnf_ffi_ba_wrap_ok_wp
#print axioms lcnf_ffi_nat_of_bytes_wp
#print axioms lcnf_ffi_nat_bytes_len_wp
#print axioms lcnf_ffi_nat_bytes_ptr_wp
#print axioms lcnf_ffi_nat_wrap_ok_wp
#print axioms lcnf_ffi_ba_to_nat_s_wp
#print axioms lcnf_ffi_nat_s_to_ba_wp
#print axioms ffiMod_moduleOk
#print axioms rtC0WithFfiMod_moduleOk
#print axioms rtMpzNatCanon_iff_bnMpzNatCanon
#print axioms nvFfiMem_ok
#print axioms nv_ffi_carve_ba_reclaim
#print axioms nv_ffi_oom_no_abort
#print axioms nv_ffi_nat_tagged_and_boxed
#print axioms nv_ffi_ba_to_nat_to_ba

end LeanQbeTest.T.LcnfC0FfiTest
