/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityInlData
public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcp
meta import LeanQbe.T.Examples.Kissat.FullFidelityCong
meta import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep7
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlData
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlBase
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParity
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Codegen, Printer, & 4-ISA Legalization Guards for `FullFidelity*` (`KissatFidelityCodegenTest`)

Centralizes all `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal`/`isLegal` `#guard` checks moved out
of the Kissat C0/Assembly/InlData modules under the `N1` `meta import` firewall, so edits to
`PrintCpp`/`PrintQbe`/`Legal` never invalidate downstream Gate-2 certificate caches.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityCodegenTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep3
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep5
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.FullFidelityInl
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

private def exceptStrEq (a b : Except String String) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | _, _ => false

/-! ## 1. `FullFidelityInlData` Zero-Scan Equivalence Guards -/

#guard fidInlBase.siteCounts.isEmpty && fidInlBase.loopCounts.isEmpty
#guard exceptStrEq (PrintQbe.module fidInlMod) (PrintQbe.module fidInlChunkMod)
#guard exceptStrEq (PrintCpp.ppTModule fidInlMod) (PrintCpp.ppTModule fidInlChunkMod)

/-! ## 2. Step 1..7 Assembly `PrintCpp`, `PrintQbe`, & 4-ISA `Fn.legal` Guards -/

#guard (PrintCpp.ppTModule fidStep1Module).isOk
#guard (PrintQbe.module fidStep1Module).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidSweepRepls.map (Fn.legal .x64AVX512))).isOk
#guard fidSweepRepls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSweepRepls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSweepRepls.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidStep2Module).isOk
#guard (PrintQbe.module fidStep2Module).isOk
#guard (PrintCpp.ppModule (fidStep2NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep2NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep2NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep2NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep2NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep2NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep2NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep2NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidStep3Module).isOk
#guard (PrintQbe.module fidStep3Module).isOk
#guard (PrintCpp.ppModule (fidStep3NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep3NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep3NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep3NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep3NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep3NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep3NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep3NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidStep4Module).isOk
#guard (PrintQbe.module fidStep4Module).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep4NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep4NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep4NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep4NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep4NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidStep5Module).isOk
#guard (PrintQbe.module fidStep5Module).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep5NewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidStep5NewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidStep5NewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidStep5NewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidStep5NewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidModule).isOk
#guard (PrintQbe.module fidModule).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidNewFns.map (Fn.legal .x64AVX512))).isOk
#guard fidNewFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidNewFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidNewFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidNewFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidStep7Module).isOk
#guard (PrintQbe.module fidStep7Module).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (FullFidelityStep7.fidStep7Fns.map (Fn.legal .x64AVX512))).isOk
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard FullFidelityStep7.fidStep7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. Standalone Layer & `FullM8CoreParity` Printer & Legalization Guards -/

#guard (PrintCpp.ppTModule fidBcpModule).isOk
#guard (PrintQbe.module fidBcpModule).isOk
#guard fidBcp_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidBcp_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidBcp_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidBcp_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard (PrintCpp.ppTModule fidCongModule).isOk
#guard (PrintQbe.module fidCongModule).isOk
#guard (PrintCpp.ppModule (fidCongFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidCongFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidCongFns.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule (fidCongFns.map (Fn.legal .x64AVX2))).isOk
#guard fidCongFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidCongFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidCongFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard fidCongFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule (fidVivK6Fns.map (Fn.legal .x64AVX2))).isOk
#guard fidVivK6Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidVivK6Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

#guard (PrintCpp.ppTModule m8CoreParityModule).isOk
#guard (PrintQbe.module m8CoreParityModule).isOk
#guard (PrintCpp.ppModule (m8CoreParityFns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (m8CoreParityFns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (m8CoreParityFns.map (Fn.legal .x64AVX512))).isOk
#guard (PrintCpp.ppModule (m8CoreParityFns.map (Fn.legal .x64AVX2))).isOk
#guard m8CoreParityFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m8CoreParityFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m8CoreParityFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m8CoreParityFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbeTest.T.KissatFidelityCodegenTest

end
