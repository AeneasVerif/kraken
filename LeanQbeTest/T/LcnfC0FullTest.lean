module

public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.LeanLCNF.Demo
public import LeanQbe.T.LeanLCNF.Coverage
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.PrintCpp
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0FullProof
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp

/-!
# Verification & Integration Tests for `LcnfC0Full` (Unified R0 + R1 + R2 + R2b Pure-C0 Runtime)

* Structural `#guard`s on `rtC0CoreMod`: `80` functions, `0` externs, `exits = ["lcnf_panic"]`,
  `35/38` `Lower.rtCalls` coverage, `LcnfC0FullRt.sizeof == 33688`, `checkAcyclic`, `symsNodup`.
* Linked `Demo` (`0` externs) and `Coverage` (`3` float externs) `PrintCpp` emission checks.
* Cross-module `interpModule rtC0CoreMod` chains exercising R0 + R1 + R2 + R2b together.
* Standard-axiom `#print axioms` audit across all headline `LcnfC0Full` and `LcnfC0FullProof`
  theorems.
* `main <dir>`: emits `rt_c0_core.hpp`, `demo_with_rt_c0.hpp`, and `cov_with_rt_c0.hpp` for
  end-to-end C++/C99/C11 ASan+UBSan differential execution against the `lean` oracle.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0FullTest

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. Structural & Linked-Module Checks -/

def demoTfs : List TFlatFn := (lowerModule Demo.lcnfProgram).toOption.getD []
def covTfs : List TFlatFn := (lowerModule Coverage.covProgram).toOption.getD []
def demoLinkedMod : Module := linkLcnfWithRtC0 demoTfs false
def covLinkedMod : Module := linkLcnfWithRtC0 covTfs true

def modSyms (m : Module) : List String :=
  m.fns.map (·.name) ++ m.externs.map (·.name) ++ m.exits

#guard LcnfC0FullRt.sizeof == 33688
#guard rtC0CoreMod.fns.length == 80
#guard rtC0CoreMod.externs.isEmpty
#guard rtC0CoreMod.exits == ["lcnf_panic"]
#guard rtC0CoreMod.checkAcyclic
#guard rtC0WithFloatExternsMod.checkAcyclic
#guard (rtC0CoreMod.fns.map (·.name)).Nodup
#guard symsNodup (modSyms rtC0CoreMod)
#guard rtCalls.length == 38
#guard rtC0CoreImplementedCalls.length == 35
#guard rtC0CoreMissingCalls == ["lcnf_float_bin", "lcnf_float_un", "lcnf_float_of_sci"]
#guard (PrintCpp.ppTModule rtC0CoreMod).isOk

#guard (lowerModule Demo.lcnfProgram).isOk
#guard demoLinkedMod.externs.isEmpty
#guard demoLinkedMod.exits == ["lcnf_panic"]
#guard (demoLinkedMod.fns.map (·.name)).Nodup
#guard symsNodup (modSyms demoLinkedMod)
#guard (PrintCpp.ppTModule demoLinkedMod).isOk

#guard (lowerModule Coverage.covProgram).isOk
#guard covLinkedMod.externs.map (·.name) ==
  ["lcnf_float_bin", "lcnf_float_un", "lcnf_float_of_sci"]
#guard (covLinkedMod.fns.map (·.name)).Nodup
#guard symsNodup (modSyms covLinkedMod)
#guard (PrintCpp.ppTModule covLinkedMod).isOk

/-! ## 2. Cross-Module `interpModule rtC0CoreMod` Chains -/

private def readCstr (m : Mem 64) (s : BitVec 64) : Option (List UInt8) := do
  let szWord ← loadVal m i64 (s + 8#64)
  let sz := szWord.toNat - 1
  let mut out : List UInt8 := []
  for i in List.range sz do
    let b ← loadVal m i8 (s + 32#64 + BitVec.ofNat 64 i)
    out := out ++ [UInt8.ofNat b.toNat]
  let nul ← loadVal m i8 (s + 32#64 + BitVec.ofNat 64 sz)
  if nul == 0#8 then some out else none

private def asciiBytes (s : String) : List UInt8 :=
  s.toUTF8.toList

/-- Cross-module chain 1 (`R1 → R2b → R0`):
`lcnf_nat_slow` (`add` of 2-limb MPZs `[2^64-1, 1] + [5, 2] = 4 + 4*2^64 = 73786976294838206468`)
followed by `lcnf_nat_to_str` (formatting the R1 MPZ to decimal UTF-8 and releasing the MPZ via
R0 `lcnf_dec_ref_cold` → `lcnf_free_obj`), then freeing the string via R0 `lcnf_dec_ref_cold`. -/
def checkChainR1ToR2bToR0 : Bool :=
  match interpModule rtC0CoreMod 40000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
      (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
  | .ok (sumMpz, ()) m1 =>
    let mpzOk := (sumMpz &&& 1#64) == 0#64 &&
      loadVal m1 i64 (sumMpz + 16#64) == some 4#64 &&
      loadVal m1 i64 (sumMpz + 24#64) == some 4#64
    match interpModule rtC0CoreMod 80000 "lcnf_nat_to_str" [i64, i64] [i64]
        (nvBnRtBase, sumMpz, ()) m1 with
    | .ok (strP, ()) m2 =>
      let want := asciiBytes "73786976294838206468"
      let strOk := readCstr m2 strP == some want &&
        loadVal m2 i64 (strP + 24#64) == some 20#64
      match interpModule rtC0CoreMod 20000 "lcnf_dec_ref_cold" [i64, i64] []
          (nvBnRtBase, strP, ()) m2 with
      | .ok () m3 =>
        let liveOk := loadVal m3 i64 (nvBnRtBase + BitVec.ofNat 64 rtLiveOff) == some 0#64
        mpzOk && strOk && liveOk
      | _ => false
    | _ => false
  | _ => false

/-- Cross-module chain 2 (`R2b → R2 → R0`):
`lcnf_nat_to_str(42)` → `lcnf_string_to_list` → `lcnf_array_mk` → R2 `lcnf_array_push` (`'!'`)
→ R2 `lcnf_array_swap` (`0, 2`) → R2 `lcnf_array_pop` → R0 `lcnf_dec_ref_cold`. -/
def checkChainR2bToR2ToR0 : Bool :=
  match interpModule rtC0CoreMod 20000 "lcnf_nat_to_str" [i64, i64] [i64]
      (nvBnRtBase, boxNat 42, ()) nvBnMem with
  | .ok (s42, ()) m1 =>
    match interpModule rtC0CoreMod 20000 "lcnf_string_to_list" [i64, i64] [i64]
        (nvBnRtBase, s42, ()) m1 with
    | .ok (lst, ()) m2 =>
      match interpModule rtC0CoreMod 20000 "lcnf_array_mk" [i64, i64] [i64]
          (nvBnRtBase, lst, ()) m2 with
      | .ok (arr1, ()) m3 =>
        match interpModule rtC0CoreMod 20000 "lcnf_array_push" [i64, i64, i64] [i64]
            (nvBnRtBase, arr1, boxNat 33, ()) m3 with
        | .ok (arr2, ()) m4 =>
          match interpModule rtC0CoreMod 20000 "lcnf_array_swap" [i64, i64, i64, i64, i64] [i64]
              (nvBnRtBase, arr2, boxNat 0, boxNat 2, 0#64, ()) m4 with
          | .ok (arr3, ()) m5 =>
            let swapOk := loadVal m5 i64 (arr3 + 8#64) == some 3#64 &&
              loadVal m5 i64 (arr3 + 24#64) == some (boxNat 33) &&
              loadVal m5 i64 (arr3 + 32#64) == some (boxNat 50) &&
              loadVal m5 i64 (arr3 + 40#64) == some (boxNat 52)
            match interpModule rtC0CoreMod 20000 "lcnf_array_pop" [i64, i64] [i64]
                (nvBnRtBase, arr3, ()) m5 with
            | .ok (arr4, ()) m6 =>
              let popOk := loadVal m6 i64 (arr4 + 8#64) == some 2#64
              match interpModule rtC0CoreMod 20000 "lcnf_dec_ref_cold" [i64, i64] []
                  (nvBnRtBase, arr4, ()) m6 with
              | .ok () _ => swapOk && popOk
              | _ => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- Cross-module chain 3 (`R2 → R2b → R0`):
`lcnf_ba_empty` (marks empty ByteArray persistent via R0) → `lcnf_ba_push` (`65`, `66`) →
R2b `lcnf_ba_data` → verify resulting `Array` `[boxNat 65, boxNat 66]`. -/
def checkChainBaToData : Bool :=
  match interpModule rtC0CoreMod 20000 "lcnf_ba_empty" [i64] [i64] (nvBnRtBase, ()) nvBnMem with
  | .ok (ba0, ()) m1 =>
    match interpModule rtC0CoreMod 20000 "lcnf_ba_push" [i64, i64, i64] [i64]
        (nvBnRtBase, ba0, 65#64, ()) m1 with
    | .ok (ba1, ()) m2 =>
      match interpModule rtC0CoreMod 20000 "lcnf_ba_push" [i64, i64, i64] [i64]
          (nvBnRtBase, ba1, 66#64, ()) m2 with
      | .ok (ba2, ()) m3 =>
        match interpModule rtC0CoreMod 20000 "lcnf_ba_data" [i64, i64] [i64]
            (nvBnRtBase, ba2, ()) m3 with
        | .ok (arr, ()) m4 =>
          loadVal m4 i64 (arr + 8#64) == some 2#64 &&
          loadVal m4 i64 (arr + 24#64) == some (boxNat 65) &&
          loadVal m4 i64 (arr + 32#64) == some (boxNat 66)
        | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- Cross-module chain 4 (`R2b → R0`):
`lcnf_str_alloc(0, 0)` → `lcnf_array_replicate(3, s)` (bumps `s.rc` from `1` to `3`) →
`lcnf_dec_ref_cold(arr)` (frees `arr` and decrements `s` 3 times, freeing `s` too). -/
def checkChainReplicateDec : Bool :=
  match interpModule rtC0CoreMod 20000 "lcnf_str_alloc" [i64, i64, i64] [i64]
      (nvBnRtBase, 0#64, 0#64, ()) nvBnMem with
  | .ok (s, ()) m1 =>
    match interpModule rtC0CoreMod 20000 "lcnf_array_replicate" [i64, i64, i64] [i64]
        (nvBnRtBase, boxNat 3, s, ()) m1 with
    | .ok (arr, ()) m2 =>
      let rcOk := loadVal m2 i32 s == some 3#32 &&
        loadVal m2 i64 (arr + 8#64) == some 3#64
      match interpModule rtC0CoreMod 20000 "lcnf_dec_ref_cold" [i64, i64] []
          (nvBnRtBase, arr, ()) m2 with
      | .ok () m3 =>
        let liveOk := loadVal m3 i64 (nvBnRtBase + BitVec.ofNat 64 rtLiveOff) == some 0#64
        rcOk && liveOk
      | _ => false
    | _ => false
  | _ => false

#guard checkChainR1ToR2bToR0
#guard checkChainR2bToR2ToR0
#guard checkChainBaToData
#guard checkChainReplicateDec

/-! ## 3. Standard-Axiom Audit -/

#print axioms LcnfC0FullRt_sizeof_eq
#print axioms LcnfC0FullRt_offsets_ok
#print axioms rtC0CoreMod_checkAcyclic
#print axioms rtC0CoreMod_symsNodup
#print axioms rtC0CoreMod_allFns_wf
#print axioms rtC0CoreMod_rtCalls_counts
#print axioms rtC0CoreMod_rtCalls_sigs_match
#print axioms LcnfC0FullInv_eq_bigNumRtInv
#print axioms rtR1Env_le_rtC0CoreEnv
#print axioms rtR2Env_le_rtC0CoreEnv
#print axioms rtR2bEnv_le_rtC0CoreEnv
#print axioms rtC0CoreMod_tableImpl
#print axioms rtC0CoreMod_moduleOk
#print axioms rtC0CoreMod_fn_sound
#print axioms nvFullMem_ok
#print axioms nv_full_nat_add_carry
#print axioms nv_full_nat_to_str_boxed
#print axioms nv_full_str_alloc_then_array_replicate
#print axioms nv_full_ba_empty
#print axioms nv_full_dec_ref_cold

/-! ## 4. Artifact Generator for End-to-End Differential Execution -/

def generateArtifacts (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "rt_c0_core.hpp") (← IO.ofExcept (PrintCpp.ppTModule rtC0CoreMod))
  let dTfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
  IO.FS.writeFile (outDir / "demo_with_rt_c0.hpp")
    (← IO.ofExcept (PrintCpp.ppTModule (linkLcnfWithRtC0 dTfs false)))
  let cTfs ← IO.ofExcept (lowerModule Coverage.covProgram)
  IO.FS.writeFile (outDir / "cov_with_rt_c0.hpp")
    (← IO.ofExcept (PrintCpp.ppTModule (linkLcnfWithRtC0 cTfs true)))

end LeanQbeTest.T.LcnfC0FullTest

public def main (args : List String) : IO Unit :=
  LeanQbeTest.T.LcnfC0FullTest.generateArtifacts (args.headD "lcnf-c0-full-out")
