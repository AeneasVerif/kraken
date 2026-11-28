/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.SegCertToyTest
public import LeanQbeTest.T.SegCertToy.Build.Amd64.Full
meta import Lean
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeTest.T.SegCertToy.SrcFull

/-!
# Gate G1 SysV x64 End-to-End Soundness & Legacy Parity (`SegCertToyTestX64`)

Verifies the 3-segment declarative `Build/Amd64/Full.fullCert` (including `Exports` isolation
and name-keyed `fn_cert!` `S2/ToyMix2`) end-to-end on `x64Target`:
1. Arbitrary-`Host` `FnSpec` and closed `x64Init` `Eventually` (`rax = toyMainVal x y`).
2. Kernel `rfl` byte-for-byte parity of `code` and `bounds` vs legacy `inline_mod!` +
   `compile_linked_chunks!` over `toyModule.optInlinePolicy toyPolicy`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToyTestX64

open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.SegCertToy LeanQbeTest.T.SegCertToyTest

theorem toyModule_legalSig_x64 : LegalSigAll x64LegalTarget SrcFull.toyModule.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Arbitrary-`Host` `FnSpec` for every source function via `LinkedCert.ofSegs` + `inlinePlan`. -/
theorem toy_x64_fnspec [hh : Host] (k₀ : Nat)
    (hc : Build.Amd64.Full.fullCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ SrcFull.toyModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (toyEnv f.name f.as f.rs)
        (Build.Amd64.Full.fullCert.bound f.name) 0 :=
  Build.Amd64.Full.fullCert.fnSpec_noExit_of_legalSigAll_inlinePlan
    hh toyEnv k₀ hc hu toyModule_ok toyModule_legalSig_x64 hf (toyEnv_noExit f)

/-- Closed `x64Init` `Eventually` theorem for `toy_main(x, y)` on the 3-segment certificate. -/
theorem toy_main_x64_eventually (x y : BitVec 64) :
    Eventually (x64Target.mach.step Build.Amd64.Full.fullCert.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = toyMainVal x y)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64])
          (Build.Amd64.Full.fullCert.bound "toy_main") [] (x, y, ()))
        (x64Target.mach.labelAddr Build.Amd64.Full.fullCert.host "toy_main")) :=
  Build.Amd64.Full.fullCert.eventually_ret1_i64_inlinePlan x64Init toyEnv toyModule_ok
    (f := Src3.fnToyMain)
    (by simp [SrcFull.toyModule, SrcFull.toyFns, Src3.fns])
    rfl rfl rfl (toyEnv_noExit Src3.fnToyMain)
    [] (x, y, ()) (toyMainVal x y) (by decide) (by decide)
    (Q := fun r _ => r = (toyMainVal x y, ())) rfl (fun _ _ h => h)

/-- Concrete witness: `toy_main(10, 20)` terminates with `rax = 68`. -/
theorem toy_main_x64_68 :
    Eventually (x64Target.mach.step Build.Amd64.Full.fullCert.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 68#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64])
          (Build.Amd64.Full.fullCert.bound "toy_main") [] (10#64, 20#64, ()))
        (x64Target.mach.labelAddr Build.Amd64.Full.fullCert.host "toy_main")) :=
  toy_main_x64_eventually 10#64 20#64

/-! ## Legacy `optInlinePolicy` + `compile_linked_chunks!` Kernel Parity -/

inline_mod! legacyInlMod SrcFull.toyModule SrcFull.toyPolicy

compile_linked_chunks! legacyX64Cert
  x64Target x64Layout x64LegalTarget x64LabelClean legacyInlMod 1 (flat := true)

theorem x64_seg_vs_legacy_code_eq :
    Build.Amd64.Full.fullCert.code = legacyX64Cert.code := rfl

theorem x64_seg_vs_legacy_bounds_eq :
    Build.Amd64.Full.fullCert.bounds = legacyX64Cert.bounds := rfl

end LeanQbeTest.T.SegCertToyTestX64
