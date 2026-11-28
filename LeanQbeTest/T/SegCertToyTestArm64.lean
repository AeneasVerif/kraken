/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainCertSeg
import LeanQbe.T.MainCertInline
import LeanQbe.T.MainCertFlat
import LeanQbe.T.Arm64.TargLemmas
import LeanQbeTest.T.SegCertToyTest
import LeanQbeTest.T.SegCertToy.Build.Arm64.Full
meta import Lean
meta import LeanQbe.T.MainCertInline
import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbeTest.T.SegCertToy.SrcFull

/-!
# Gate G1 AAPCS64 Arm64 End-to-End Soundness & Legacy Parity (`SegCertToyTestArm64`)

Verifies the 3-segment declarative `Build/Arm64/Full.fullCert` (including `Exports` isolation
and name-keyed `fn_cert!` `S2/ToyMix2`) end-to-end on `armTarget`:
1. Arbitrary-`Host` `FnSpec` and closed `armInit` `Eventually` (`X0 = toyMainVal x y`).
2. Kernel `rfl` byte-for-byte parity of `code` and `bounds` vs legacy `inline_mod!` +
   `compile_linked_chunks!` over `toyModule.optInlinePolicy toyPolicy`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SegCertToyTestArm64

open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.SegCertToy LeanQbeTest.T.SegCertToyTest

theorem toyModule_legalSig_arm64 : LegalSigAll armLegalTarget SrcFull.toyModule.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Arbitrary-`Host` `FnSpec` for every source function via `LinkedCert.ofSegs` + `inlinePlan`. -/
theorem toy_arm64_fnspec [hh : Host] (k₀ : Nat)
    (hc : Build.Arm64.Full.fullCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ SrcFull.toyModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (toyEnv f.name f.as f.rs)
        (Build.Arm64.Full.fullCert.bound f.name) 0 :=
  Build.Arm64.Full.fullCert.fnSpec_noExit_of_legalSigAll_inlinePlan
    hh toyEnv k₀ hc hu toyModule_ok toyModule_legalSig_arm64 hf (toyEnv_noExit f)

/-- Closed `armInit` `Eventually` theorem for `toy_main(x, y)` on the 3-segment certificate. -/
theorem toy_main_arm64_eventually (x y : BitVec 64) :
    Eventually (armTarget.mach.step Build.Arm64.Full.fullCert.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = toyMainVal x y)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64])
          (Build.Arm64.Full.fullCert.bound "toy_main") [] (x, y, ()))
        (armTarget.mach.labelAddr Build.Arm64.Full.fullCert.host "toy_main")) :=
  Build.Arm64.Full.fullCert.eventually_ret1_i64_inlinePlan armInit toyEnv toyModule_ok
    (f := Src3.fnToyMain)
    (by simp [SrcFull.toyModule, SrcFull.toyFns, Src3.fns])
    rfl rfl rfl (toyEnv_noExit Src3.fnToyMain)
    [] (x, y, ()) (toyMainVal x y) (by decide) (by decide)
    (Q := fun r _ => r = (toyMainVal x y, ())) rfl (fun _ _ h => h)

/-- Concrete witness: `toy_main(10, 20)` terminates with `X0 = 68`. -/
theorem toy_main_arm64_68 :
    Eventually (armTarget.mach.step Build.Arm64.Full.fullCert.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 68#64)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64])
          (Build.Arm64.Full.fullCert.bound "toy_main") [] (10#64, 20#64, ()))
        (armTarget.mach.labelAddr Build.Arm64.Full.fullCert.host "toy_main")) :=
  toy_main_arm64_eventually 10#64 20#64

/-! ## Legacy `optInlinePolicy` + `compile_linked_chunks!` Kernel Parity -/

inline_mod! legacyInlMod SrcFull.toyModule SrcFull.toyPolicy

compile_linked_chunks! legacyArm64Cert
  armTarget armLayout armLegalTarget armLabelClean legacyInlMod 1 (flat := true)

theorem arm64_seg_vs_legacy_code_eq :
    Build.Arm64.Full.fullCert.code = legacyArm64Cert.code := rfl

theorem arm64_seg_vs_legacy_bounds_eq :
    Build.Arm64.Full.fullCert.bounds = legacyArm64Cert.bounds := rfl

end LeanQbeTest.T.SegCertToyTestArm64
