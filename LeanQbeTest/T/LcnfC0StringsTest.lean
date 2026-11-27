module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof
public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.LcnfC0Strings
meta import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
meta import LeanQbe.T.LeanLCNF.LcnfC0StringsProof
meta import LeanQbe.T.LeanLCNF.Lower
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Verification & Execution Tests for `LcnfC0Strings` (R2b + `lcnf_clo_under`)

* Structural checks on `rtR2bMod` (`19` functions, acyclicity, zero duplicate names)
* `Lower.rtCalls` coverage audit: `rtR0Mod` + `rtR2Mod` + `rtR2bMod` cover all `32/38`
  non-bignum/non-float runtime calls (including all `13` R2b calls and `lcnf_clo_under`)
* `PrintCpp.ppTModule` and `PrintQbe.module` emission checks
* Executable `interpModule` tests across all `13` R2b runtime functions and `lcnf_clo_under`
* Standard axiom audit (`[propext, Classical.choice, Quot.sound]`) across `rtR2bMod_moduleOk`,
  all `13` `lcnf_*_sound`, `nv_*` non-vacuity witnesses, and `rtC0Env_clo_under_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0StringsTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-- Combined R0 + R2 + R2b module for standalone concrete interpreter execution (R2b calls R2's
`r2_*` RC/memcpy/alloc helpers). -/
def rtR0R2bMod : Module :=
  { fns := rtR0Mod.fns ++ rtR2Mod.fns ++ rtR2bMod.fns, externs := [], exits := ["lcnf_panic"] }

/-- Combined R0 + R2 + R2b runtime module covering all non-bignum/non-float `Lower.rtCalls`. -/
def rtR0R2R2bMod : Module :=
  { fns := rtR0Mod.fns ++ rtR2Mod.fns ++ rtR2bMod.fns,
    externs := [], exits := ["lcnf_panic"] }

#guard rtR2bMod.fns.length == 19
#guard rtR2bMod.checkAcyclic
#guard rtR0R2bMod.checkAcyclic
#guard rtR0R2R2bMod.checkAcyclic
#guard (rtR2bMod.fns.map (·.name)).Nodup
#guard (rtR0R2R2bMod.fns.map (·.name)).Nodup
#guard (PrintCpp.ppTModule rtR2bMod).isOk
#guard (PrintCpp.ppTModule rtR0R2bMod).isOk
#guard (PrintQbe.module rtR2bMod).isOk
#guard (PrintQbe.module rtR0R2bMod).isOk

#guard
  let syms := rtCalls.map (·.1)
  let haveFns := rtR0R2R2bMod.fns.map (·.name)
  syms.filter (fun s => !haveFns.contains s) ==
    ["lcnf_nat_slow", "lcnf_nat_alloc", "lcnf_float_bin", "lcnf_float_un",
     "lcnf_float_of_sci", "lcnf_int_op"]

/-! ## Executable `interpModule` Functional & Panic Checks -/

private def readCstr (m : Mem 64) (s : BitVec 64) : Option (List UInt8) := do
  let szWord ← loadVal m i64 (s + 8#64)
  let sz := szWord.toNat - 1
  let mut out : List UInt8 := []
  for i in List.range sz do
    let b ← loadVal m i8 (s + 32#64 + BitVec.ofNat 64 i)
    out := out ++ [UInt8.ofNat b.toNat]
  let nul ← loadVal m i8 (s + 32#64 + BitVec.ofNat 64 sz)
  if nul == 0#8 then some out else none

def checkCharOpAndStrAlloc : Bool :=
  let c0 := interpModule rtR0R2bMod 5000 "lcnf_char_op" [i64, i64, i64] [i64]
    (nvRtAddr, 0#64, boxNat 0x03b1, ()) nvStrSlabMem
  let cSurr := interpModule rtR0R2bMod 5000 "lcnf_char_op" [i64, i64, i64] [i64]
    (nvRtAddr, 0#64, boxNat 0xd800, ()) nvStrSlabMem
  let c1 := interpModule rtR0R2bMod 5000 "lcnf_char_op" [i64, i64, i64] [i64]
    (nvRtAddr, 1#64, 0x1f600#64, ()) nvStrSlabMem
  let s0 := interpModule rtR0R2bMod 5000 "lcnf_str_alloc" [i64, i64, i64] [i64]
    (nvRtAddr, 4#64, 3#64, ()) (nvR2RtBytes.At nvRtAddr)
  match c0, cSurr, c1, s0 with
  | .ok (r0, ()) _, .ok (rs, ()) _, .ok (r1, ()) _, .ok (sp, ()) m1 =>
    r0 == 0x03b1#64 && rs == 0#64 && r1 == boxNat 4 &&
    loadVal m1 i64 (sp + 8#64) == some 5#64 &&
    loadVal m1 i64 (sp + 16#64) == some 5#64 &&
    loadVal m1 i64 (sp + 24#64) == some 3#64 &&
    loadVal m1 i8 (sp + 36#64) == some 0#8
  | _, _, _, _ => false

def checkStringPushAppendCmpPos : Bool :=
  match interpModule rtR0R2bMod 10000 "lcnf_string_push" [i64, i64, i64] [i64]
      (nvRtAddr, nvStr1Addr, 0x03b1#64, ()) nvStrSlabMem with
  | .ok (sPush, ()) m1 =>
    let pushOk := sPush == nvStr1Addr &&
      readCstr m1 sPush == some [65, 66, 0xce, 0xb1] &&
      loadVal m1 i64 (sPush + 24#64) == some 3#64
    let cmpOk :=
      match interpModule rtR0R2bMod 10000 "lcnf_string_cmp_op" [i64, i64, i64, i64] [i64]
          (nvRtAddr, 1#64, nvStr1Addr, nvStr2Addr, ()) nvStrSlabMem with
      | .ok (ltv, ()) _ => ltv == 1#64
      | _ => false
    let posOk :=
      match interpModule rtR0R2bMod 10000 "lcnf_string_pos_op" [i64, i64, i64, i64, i64] [i64]
          (nvRtAddr, 0#64, sPush, boxNat 2, 0#64, ()) m1,
        interpModule rtR0R2bMod 10000 "lcnf_string_pos_op" [i64, i64, i64, i64, i64] [i64]
          (nvRtAddr, 3#64, sPush, boxNat 1, boxNat 4, ()) m1 with
      | .ok (cp, ()) _, .ok (subP, ()) m2 =>
        cp == 0x03b1#64 && readCstr m2 subP == some [66, 0xce, 0xb1] &&
        loadVal m2 i64 (subP + 24#64) == some 2#64
      | _, _ => false
    let appOk :=
      match interpModule rtR0R2bMod 10000 "lcnf_string_append" [i64, i64, i64] [i64]
          (nvRtAddr, sPush, nvStr2Addr, ()) m1 with
      | .ok (sApp, ()) m3 =>
        readCstr m3 sApp == some [65, 66, 0xce, 0xb1, 65, 67] &&
        loadVal m3 i64 (sApp + 24#64) == some 5#64
      | _ => false
    pushOk && cmpOk && posOk && appOk
  | _ => false

def checkRoundTripListArrayBa : Bool :=
  let roundOk :=
    match interpModule rtR0R2bMod 20000 "lcnf_string_to_list" [i64, i64] [i64]
        (nvRtAddr, nvStr1Addr, ()) nvStrSlabMem with
    | .ok (lst1, ()) m1 =>
      match interpModule rtR0R2bMod 20000 "lcnf_array_mk" [i64, i64] [i64]
          (nvRtAddr, lst1, ()) m1 with
      | .ok (arr1, ()) m2 =>
        let arrOk := loadVal m2 i64 (arr1 + 8#64) == some 2#64 &&
          loadVal m2 i64 (arr1 + 24#64) == some (boxNat 65) &&
          loadVal m2 i64 (arr1 + 32#64) == some (boxNat 66)
        match interpModule rtR0R2bMod 20000 "lcnf_array_to_list" [i64, i64] [i64]
            (nvRtAddr, arr1, ()) m2 with
        | .ok (lst2, ()) m3 =>
          match interpModule rtR0R2bMod 20000 "lcnf_string_mk" [i64, i64] [i64]
              (nvRtAddr, lst2, ()) m3 with
          | .ok (strOut, ()) m4 =>
            arrOk && readCstr m4 strOut == some [65, 66] &&
            loadVal m4 i64 (strOut + 24#64) == some 2#64
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  let baOk :=
    match interpModule rtR0R2bMod 20000 "lcnf_ba_data" [i64, i64] [i64]
        (nvRtAddr, nvBa1Addr, ()) nvBaSlabMem with
    | .ok (baArr, ()) m1 =>
      loadVal m1 i64 (baArr + 8#64) == some 2#64 &&
      loadVal m1 i64 (baArr + 24#64) == some (boxNat 65) &&
      loadVal m1 i64 (baArr + 32#64) == some (boxNat 66)
    | _ => false
  let repOk :=
    match interpModule rtR0R2bMod 20000 "lcnf_array_replicate" [i64, i64, i64] [i64]
        (nvRtAddr, boxNat 2, 7#64, ()) (nvR2RtBytes.At nvRtAddr) with
    | .ok (repArr, ()) m1 =>
      loadVal m1 i64 (repArr + 8#64) == some 2#64 &&
      loadVal m1 i64 (repArr + 24#64) == some 7#64 &&
      loadVal m1 i64 (repArr + 32#64) == some 7#64
    | _ => false
  roundOk && baOk && repOk

def checkNatToStrAndCloUnder : Bool :=
  let zOk :=
    match interpModule rtR0R2bMod 10000 "lcnf_nat_to_str" [i64, i64] [i64]
        (nvRtAddr, 1#64, ()) (nvR2RtBytes.At nvRtAddr) with
    | .ok (sz, ()) m1 => readCstr m1 sz == some [48]
    | _ => false
  let bOk :=
    match interpModule rtR0R2bMod 10000 "lcnf_nat_to_str" [i64, i64] [i64]
        (nvRtAddr, boxNat 42, ()) (nvR2RtBytes.At nvRtAddr) with
    | .ok (sb, ()) m1 => readCstr m1 sb == some [52, 50]
    | _ => false
  let mOk :=
    match interpModule rtR0R2bMod 30000 "lcnf_nat_to_str" [i64, i64] [i64]
        (nvRtAddr, nvStr1Addr, ()) nvMpzSlabMem with
    | .ok (sm, ()) m1 => readCstr m1 sm == some [55]
    | _ => false
  let cloOk :=
    match interpModule rtR0R2bMod 10000 "lcnf_clo_under" [i64, i64, i64] [i64]
        (nvRtAddr, nvStr1Addr, 1#64, ()) nvCloSlabMem with
    | .ok (c, ()) m1 =>
      loadVal m1 i64 (c + 8#64) == some 1024#64 &&
      loadVal m1 i64 (c + 16#64) == some (cloMetaWord 2 2) &&
      loadVal m1 i64 (c + 24#64) == some 1#64
    | _ => false
  zOk && bOk && mOk && cloOk

private def isPanicCode {rs : List Ty} (code : BitVec 64) : InterpResult rs → Bool
  | .exit "lcnf_panic" (as := as) xs _ =>
    if h : as = [i64, i64] then (h ▸ xs).2.1 == code else false
  | _ => false

def checkPanics : Bool :=
  let p1 := isPanicCode 1#64 (interpModule rtR0R2bMod 5000 "lcnf_char_op" [i64, i64, i64] [i64]
    (nvRtAddr, 9#64, 0#64, ()) (nvR2RtBytes.At nvRtAddr))
  let p2 := isPanicCode 2#64 (interpModule rtR0R2bMod 5000 "lcnf_str_alloc" [i64, i64, i64] [i64]
    (nvRtAddr, BitVec.ofNat 64 strMaxCap, 0#64, ()) (nvR2RtBytes.At nvRtAddr))
  p1 && p2

#guard checkCharOpAndStrAlloc
#guard checkStringPushAppendCmpPos
#guard checkRoundTripListArrayBa
#guard checkNatToStrAndCloUnder
#guard checkPanics

#print axioms rtR2bMod_allFns_wf
#print axioms rtR2bMod_tableImpl
#print axioms rtR2bMod_moduleOk
#print axioms rtR2bMod_fn_sound
#print axioms lcnf_str_alloc_sound
#print axioms lcnf_char_op_sound
#print axioms lcnf_string_push_sound
#print axioms lcnf_string_append_sound
#print axioms lcnf_string_cmp_op_sound
#print axioms lcnf_string_pos_op_sound
#print axioms lcnf_string_to_list_sound
#print axioms lcnf_string_mk_sound
#print axioms lcnf_ba_data_sound
#print axioms lcnf_array_mk_sound
#print axioms lcnf_array_to_list_sound
#print axioms lcnf_array_replicate_sound
#print axioms lcnf_nat_to_str_sound
#print axioms rtC0Env_clo_under_wp
#print axioms nv_lcnf_char_op
#print axioms nv_lcnf_str_alloc
#print axioms nv_lcnf_string_push
#print axioms nv_lcnf_string_append
#print axioms nv_lcnf_string_cmp_op
#print axioms nv_lcnf_string_pos_op
#print axioms nv_lcnf_string_to_list
#print axioms nv_lcnf_string_mk
#print axioms nv_lcnf_ba_data
#print axioms nv_lcnf_array_mk
#print axioms nv_lcnf_array_to_list
#print axioms nv_lcnf_array_replicate
#print axioms nv_lcnf_nat_to_str_zero
#print axioms nv_lcnf_nat_to_str_boxed
#print axioms nv_lcnf_nat_to_str_mpz
#print axioms nv_lcnf_clo_under

end LeanQbeTest.T.LcnfC0StringsTest
