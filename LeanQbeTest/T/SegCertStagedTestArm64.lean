/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainCertSeg
import LeanQbe.T.MainCertFlat
import LeanQbe.T.Arm64.TargLemmas
import LeanQbeTest.T.SegCertToy.Build.Inl.S2
import LeanQbeTest.T.SegCertToy.Build.Arm64.S2.ToyMix2
import LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2
meta import Lean
meta import LeanQbe.T.MainCertSegElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2

/-!
# Staged `fn_cert!` & Singleton `seg_cert!` on AAPCS64 Arm64 (`SegCertStagedTestArm64`)

Verifies `(staged := true)` on `S2.toy_mix2` via both `fn_cert!` and singleton `seg_cert!`,
confirming exact kernel `rfl` parity with the unstaged `Build/Arm64/S2/ToyMix2.cert` and `<= std3`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SegCertStagedTestArm64

open LeanQbe.T LeanQbe.T.Arm64
open scoped LeanQbe.T

fn_cert! stagedFnCert armTarget armLayout armLegalTarget armLabelClean
  LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.flat.f1
  (hints := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.hint_toy_mix2)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2) (maxBound := 2048)
  (pruneExt := true) (staged := true)

noncomputable def mix2Fns : List Fn :=
  [LeanQbeTest.T.SegCertToy.Build.Inl.S2.inl.flat.f1.toFn]

meta def mix2Hints : List armIsa.Hints :=
  [LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.hint_toy_mix2]

seg_cert! stagedSegCert armTarget armLayout armLegalTarget armLabelClean
  mix2Fns
  (hints := mix2Hints)
  (ext := LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2) (maxBound := 2048)
  (pruneExt := true) (staged := true)

/-- Exact kernel `rfl` code parity between staged `fn_cert!` and unstaged `ToyMix2.cert`. -/
theorem staged_fn_code_eq :
    (linkCompiledList armLayout armLabelClean
      LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2
      stagedFnCert.chunks (by rfl)).code =
    (linkCompiledList armLayout armLabelClean
      LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2
      LeanQbeTest.T.SegCertToy.Build.Arm64.S2.ToyMix2.cert.chunks (by rfl)).code := rfl

/-- Exact kernel `rfl` code parity between staged `seg_cert!` and unstaged `ToyMix2.cert`. -/
theorem staged_seg_code_eq :
    (linkCompiledList armLayout armLabelClean
      LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2
      stagedSegCert.chunks (by rfl)).code =
    (linkCompiledList armLayout armLabelClean
      LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2.ext_toy_mix2
      LeanQbeTest.T.SegCertToy.Build.Arm64.S2.ToyMix2.cert.chunks (by rfl)).code := rfl

end LeanQbeTest.T.SegCertStagedTestArm64
