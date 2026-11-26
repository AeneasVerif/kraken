/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbeTest.T.CertFlatDecodeFixture
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Arm64.Targ

/-!
# AAPCS64 Arm64 Flat vs Legacy Certificate Parity Test (`CompileFlatCertArm64Test`)

Arm64 companion to `CompileFlatCertTest` (zero `Kraken.X64`/`Amd64` imports): certifies N7's
`CertFlatDecodeFixture` twice — `(flat := false)` and `(flat := true)` — on `Arm64` (`armTarget`),
verifying exact kernel and literal equality of `code`, `bounds`, `exportedExt`, and
`eval_prefix_ext!`, noncomputable flat declarations, and `≤ std3` axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CompileFlatCertArm64Test

open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbeTest.T.CertFlatDecodeFixture

/-- Submodule slice `[0, 2)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev slice1Mod : Module := { fns := fixFns.take 2 }

/-- Submodule slice `[2, 6)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev slice2Mod : Module := { fns := fixFns.drop 2 }

eval_prefix_ext! armAllExtLegacy armTarget armLegalTarget fixFns (flat := false)
eval_prefix_ext! armAllExtFlat armTarget armLegalTarget fixFns (flat := true)

eval_prefix_ext! armSlice2ExtLegacy armTarget armLegalTarget (fixFns.take 2)
  (pruneFor := slice2Mod.fns) (flat := false)
eval_prefix_ext! armSlice2ExtFlat armTarget armLegalTarget (fixFns.take 2)
  (pruneFor := slice2Mod.fns) (flat := true)

#guard armAllExtLegacy == armAllExtFlat
#guard armSlice2ExtLegacy == armSlice2ExtFlat

compile_linked_chunks! armCert1Legacy armTarget armLayout armLegalTarget armLabelClean
  slice1Mod 1 (compileExt := true) (pruneExt := true) (flat := false)
compile_linked_chunks! armCert1Flat armTarget armLayout armLegalTarget armLabelClean
  slice1Mod 1 (compileExt := true) (pruneExt := true) (flat := true)

compile_linked_chunks! armCert2Legacy armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 1 (ext := armSlice2ExtLegacy) (compileExt := true) (pruneExt := true) (flat := false)
compile_linked_chunks! armCert2Flat armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 1 (ext := armSlice2ExtFlat) (compileExt := true) (pruneExt := true) (flat := true)

#guard armCert1Legacy.exportedExt == armCert1Flat.exportedExt
#guard armCert2Legacy.exportedExt == armCert2Flat.exportedExt

theorem arm_cert1_code_eq : armCert1Legacy.code = armCert1Flat.code := rfl
theorem arm_cert1_bounds_eq : armCert1Legacy.bounds = armCert1Flat.bounds := rfl
theorem arm_cert2_code_eq : armCert2Legacy.code = armCert2Flat.code := rfl
theorem arm_cert2_bounds_eq : armCert2Legacy.bounds = armCert2Flat.bounds := rfl

noncomputable def armCertFullFlat :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean fixMod [] [] 0 2048 :=
  armCert1Flat.append armCert2Flat (by exact (List.take_append_drop 2 fixMod.fns).symm) rfl

noncomputable def armCertOptFlat :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (fixSrcMod.optInlinePolicy fixPol) [] [] 0 2048 :=
  armCertFullFlat.castModule fixMod.eq

section MetaChecks

meta section

open Lean Meta

private def checkCertPair (legacyPfx flatPfx : Name) (nChunks : Nat) : MetaM Unit := do
  let env ← getEnv
  let flatAux := flatPfx ++ `aux
  let legAux := legacyPfx ++ `aux
  for nm in [flatAux ++ `flatFns, flatAux ++ `fns_flat_eq] do
    if !env.contains nm then
      throwError "missing flat cert declaration '{nm}'"
  if !Lean.isNoncomputable env (flatAux ++ `flatFns) then
    throwError "expected '{flatAux ++ `flatFns}' to be noncomputable"
  if env.contains (legAux ++ `flatFns) then
    throwError "legacy cert '{legacyPfx}' unexpectedly emitted flatFns"
  for i in [:nChunks] do
    let flatDef := flatAux ++ Name.mkSimple s!"c{i}_flat"
    let cmFlat := flatAux ++ Name.mkSimple s!"c{i}_cm_flat"
    if !env.contains flatDef || !env.contains cmFlat then
      throwError "missing flat chunk declarations for {flatPfx} chunk {i}"
    if !Lean.isNoncomputable env flatDef then
      throwError "expected '{flatDef}' to be noncomputable"
    if env.contains (legAux ++ Name.mkSimple s!"c{i}_cm_flat") then
      throwError "legacy cert '{legacyPfx}' unexpectedly emitted c{i}_cm_flat"
    for suffix in ["code", "bounds"] do
      let lNm := legAux ++ Name.mkSimple s!"c{i}_{suffix}"
      let fNm := flatAux ++ Name.mkSimple s!"c{i}_{suffix}"
      let some lVal := (env.find? lNm).bind (·.value?)
        | throwError "missing value for '{lNm}'"
      let some fVal := (env.find? fNm).bind (·.value?)
        | throwError "missing value for '{fNm}'"
      if lVal != fVal then
        throwError "literal mismatch between '{lNm}' and '{fNm}'"

#eval show MetaM Unit from do
  checkCertPair ``armCert1Legacy ``armCert1Flat 2
  checkCertPair ``armCert2Legacy ``armCert2Flat 4

end

end MetaChecks

#print axioms armCert1Flat
#print axioms armCert2Flat
#print axioms armCertFullFlat
#print axioms armCertOptFlat
#print axioms arm_cert1_code_eq
#print axioms arm_cert2_code_eq

end LeanQbeTest.T.CompileFlatCertArm64Test
