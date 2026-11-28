module

import LeanQbe.T.InterpKissat
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Examples.Kissat.Plain1
import LeanQbe.T.Examples.Kissat.PlainLemmas
import LeanQbe.T.Examples.Kissat.Src.Full
import Kraken.Mem

meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.Src.Full

/-!
# Tests and Soundness Audit for Kissat IL Executable Interpreter

This module validates the verified, fuel-indexed Lean executable interpreter for Kissat IL
(`LeanQbe.T.InterpKissat`):
1. Compile-time `#guard` execution checks on mathematical routines (`plain_isqrt`, `plain_ilog10`),
2. Compile-time `#guard` execution checks on end-to-end SAT / UNSAT DIMACS payloads across
   `Plain` (59 fns) and `Src.Full.kissatModule` (418 fns),
3. Standalone audit restatements of all headline interpreter soundness theorems (`interpFlat_sound`,
   `interpModule_sound`, `interpModule_not_ub`, `interpModule_ok_witness`, `ModuleOk.env_sound`),
4. `#print axioms` assertions verifying that the entire semantic and operational verification
   rests strictly upon standard Lean axioms (`std3`, `0` `sorry`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

section

namespace LeanQbe.T.InterpKissatTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Kissat.Src.Full
open Kraken

/-! ## 1. Headline Soundness Theorems Audit -/

/-- Audit: `interpFlat_sound` is an established theorem depending on std3 axioms. -/
theorem audit_interpFlat_sound :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      (fuel : Nat) {rs : List Ty} (Q : Post rs) (X : XPost)
      (ls_i : List (GroupFrame rs)) (ls_d : List ((ts : List Ty) × Cont ts))
      (vs : List ((t : Ty) × Val t)) (tf : TFlat rs) (m : Mem 64),
      FramesRel M fuel Q X ls_i ls_d →
      wp Γ Q X (denote Val Cont tf vs ls_d) m →
      InterpOk Q X (interpFlat M fuel ls_i vs tf m) :=
  interpFlat_sound

/-- Audit: `interpFunc_sound` relates `Func.wp` directly to reified function execution. -/
theorem audit_interpFunc_sound :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      {as rs : List Ty} (f : Func as rs) (args : Tup Val as) (m : Mem 64)
      (Q : Post rs) (X : XPost) (hf : f.Wf),
      Func.wp Γ f args m Q X → ∀ (fuel : Nat),
      InterpOk Q X (interpFunc M fuel f args m) :=
  interpFunc_sound

/-- Audit: `interpFn_sound` relates `Func.wp` directly to top-level `Fn` execution. -/
theorem audit_interpFn_sound :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      (fn : Fn) (args : Tup Val fn.as) (m : Mem 64)
      (Q : Post fn.rs) (X : XPost) (hfn : fn.Wf),
      Func.wp Γ fn.body args m Q X → ∀ (fuel : Nat),
      InterpOk Q X (interpFn M fuel fn args m) :=
  interpFn_sound

/-- Audit: `interpModule_sound` relates `Func.wp` to whole-module interpreter execution. -/
theorem audit_interpModule_sound :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
      (Q : Post rs) (X : XPost) (fnBody : Func as rs),
      lookupFn M entry as rs = some fnBody →
      fnBody.Wf → Func.wp Γ fnBody args m Q X → ∀ (fuel : Nat),
      InterpOk Q X (interpModule M fuel entry as rs args m) :=
  fun M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel =>
    interpModule_sound M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel

/-- Audit: `interpModule_not_ub` proves execution never encounters UB under `wp`. -/
theorem audit_interpModule_not_ub :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
      (Q : Post rs) (X : XPost) (fnBody : Func as rs),
      lookupFn M entry as rs = some fnBody →
      fnBody.Wf → Func.wp Γ fnBody args m Q X → ∀ (fuel : Nat),
      interpModule M fuel entry as rs args m ≠ .ub :=
  fun M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel =>
    interpModule_not_ub M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel

/-- Audit: `interpModule_ok_witness` proves `.ok` results satisfy the postcondition `Q`. -/
theorem audit_interpModule_ok_witness :
    ∀ (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
      (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
      (Q : Post rs) (X : XPost) (fnBody : Func as rs),
      lookupFn M entry as rs = some fnBody →
      fnBody.Wf → Func.wp Γ fnBody args m Q X →
      ∀ (fuel : Nat) (res : Tup Val rs) (m' : Mem 64),
      interpModule M fuel entry as rs args m = .ok res m' →
      Q res m' :=
  fun M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel res m' hrun =>
    interpModule_ok_witness M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel res m' hrun

/-- Audit: `ModuleOk.env_sound` establishes a closed verified module's sound environment. -/
theorem audit_moduleOk_env_sound :
    ∀ {Γ : Env} {M : Module}, ModuleOk Γ M → M.externs = [] →
      ModuleEnvSound (Env.ofModule M Γ) M :=
  ModuleOk.env_sound

#print axioms audit_interpFlat_sound
#print axioms audit_interpFunc_sound
#print axioms audit_interpFn_sound
#print axioms audit_interpModule_sound
#print axioms audit_interpModule_not_ub
#print axioms audit_interpModule_ok_witness
#print axioms audit_moduleOk_env_sound

/-! ## 2. Executable Smoke Tests: Arithmetic & Control Flow -/

#guard match interpFunc plainModule 1000 Plain.plain_isqrt_body (100#64, ()) default with
  | .ok (r, ()) _ => r == 10#64
  | _ => false

#guard match interpFunc plainModule 1000 Plain.plain_isqrt_body (1000000#64, ()) default with
  | .ok (r, ()) _ => r == 1000#64
  | _ => false

#guard match interpFunc plainModule 1000 Plain.plain_ilog10_body (1000#64, ()) default with
  | .ok (r, ()) _ => r == 4#64
  | _ => false

#guard match interpFunc plainModule 1000 Plain.plain_ilog10_body (999#64, ()) default with
  | .ok (r, ()) _ => r == 3#64
  | _ => false

/-! ## 3. Executable Smoke Tests: Plain Kissat SAT / UNSAT Execution -/

private def testPlainUnsat : Bool :=
  let mUnsat : Mem 64 := (plainPayload plainNvUnsatBytes).At plainNvCnfPtr
  let argsUnsat := (plainNvCnfPtr, BitVec.ofNat 64 plainNvUnsatBytes.length,
                    plainNvWorkPtr plainNvUnsatBytes, 2048#64, 16#64, ())
  match interpFunc plainModule 200000 Plain.kissat_solve_bytes_body argsUnsat mUnsat with
  | .ok (r, ()) _ => r == 20#64
  | _ => false

private def testPlainSat : Bool :=
  let mSat : Mem 64 := (plainPayload plainNvSatBytes).At plainNvCnfPtr
  let argsSat := (plainNvCnfPtr, BitVec.ofNat 64 plainNvSatBytes.length,
                  plainNvWorkPtr plainNvSatBytes, 2048#64, 16#64, ())
  match interpFunc plainModule 200000 Plain.kissat_solve_bytes_body argsSat mSat with
  | .ok (r, ()) _ => r == 10#64
  | _ => false

#guard testPlainUnsat
#guard testPlainSat

/-! ## 4. Executable Smoke Tests: `Src.Full.kissatModule` (418 fns) UNSAT / SAT Execution -/

private def srcFullCnfPtr : BitVec 64 := 0x1000#64
private def srcFullWorkLen : Nat := 8192

/-- Concrete UNSAT DIMACS `"p cnf 1 2\n1 0\n-1 0\n"` (`19` bytes). -/
private def srcFullUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Concrete SAT DIMACS `"p cnf 2 1\n1 2 0\n"` (`16` bytes). -/
private def srcFullSatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 49, 32, 50, 32, 48, 10]

private def runSrcFull (cnfBytes : List UInt8) : Option (BitVec 64) :=
  let m : Mem 64 := (cnfBytes ++ List.replicate srcFullWorkLen 0).At srcFullCnfPtr
  let workPtr := srcFullCnfPtr + BitVec.ofNat 64 cnfBytes.length
  let args : Tup Val [i64, i64, i64, i64, i64] :=
    (srcFullCnfPtr, BitVec.ofNat 64 cnfBytes.length,
     workPtr, BitVec.ofNat 64 srcFullWorkLen, 16#64, ())
  match interpModule Src.Full.kissatModule 300000 "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64] args m with
  | .ok (r, ()) _ => some r
  | _ => none

private def testSrcFullUnsat : Bool :=
  runSrcFull srcFullUnsatBytes == some 20#64

private def testSrcFullSat : Bool :=
  runSrcFull srcFullSatBytes == some 10#64

#guard testSrcFullUnsat
#guard testSrcFullSat

end LeanQbe.T.InterpKissatTest
