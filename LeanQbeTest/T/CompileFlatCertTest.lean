/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.CertFlatDecodeFixture
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ

/-!
# SysV x64 Flat vs Legacy Certificate Parity Test (`CompileFlatCertTest`)

Certifies N7's `CertFlatDecodeFixture` twice — `(flat := false)` and `(flat := true)` — on
`Amd64` (`x64Target`; see `CompileFlatCertArm64Test` for the AArch64 companion), verifying:
1. Exact kernel `rfl` and syntactic literal equality of `code`, `bounds`, `exportedExt`, and
   `eval_prefix_ext!` between legacy PHOAS and first-order flat kernel paths (`0` asm diff).
2. Flat-path declarations (`flatFns`, `fns_flat_eq`, `c{i}_flat`, `c{i}_cm_flat`) are emitted with
   `compile := false` (`noncomputable`) on `(flat := true)` and absent on `(flat := false)`.
3. Trap T5: `(flat := true)` fails closed on unmaterialized modules (`fixSrcMod`).
4. `#print axioms` stays within `std3` (`0` `native_decide` / `Lean.ofReduceBool` / unsafe).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CompileFlatCertTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbeTest.T.CertFlatDecodeFixture

/-- Submodule slice `[0, 2)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev slice1Mod : Module := { fns := fixFns.take 2 }

/-- Submodule slice `[2, 6)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev slice2Mod : Module := { fns := fixFns.drop 2 }

eval_prefix_ext! x64AllExtLegacy x64Target x64LegalTarget fixFns (flat := false)
eval_prefix_ext! x64AllExtFlat x64Target x64LegalTarget fixFns (flat := true)

eval_prefix_ext! x64Slice2ExtLegacy x64Target x64LegalTarget (fixFns.take 2)
  (pruneFor := slice2Mod.fns) (flat := false)
eval_prefix_ext! x64Slice2ExtFlat x64Target x64LegalTarget (fixFns.take 2)
  (pruneFor := slice2Mod.fns) (flat := true)

#guard x64AllExtLegacy == x64AllExtFlat
#guard x64Slice2ExtLegacy == x64Slice2ExtFlat

compile_linked_chunks! x64Cert1Legacy x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 1 (compileExt := true) (pruneExt := true) (flat := false)
compile_linked_chunks! x64Cert1Flat x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 1 (compileExt := true) (pruneExt := true) (flat := true)

compile_linked_chunks! x64Cert2Legacy x64Target x64Layout x64LegalTarget x64LabelClean
  slice2Mod 1 (ext := x64Slice2ExtLegacy) (compileExt := true) (pruneExt := true) (flat := false)
compile_linked_chunks! x64Cert2Flat x64Target x64Layout x64LegalTarget x64LabelClean
  slice2Mod 1 (ext := x64Slice2ExtFlat) (compileExt := true) (pruneExt := true) (flat := true)

#guard x64Cert1Legacy.exportedExt == x64Cert1Flat.exportedExt
#guard x64Cert2Legacy.exportedExt == x64Cert2Flat.exportedExt

theorem x64_cert1_code_eq : x64Cert1Legacy.code = x64Cert1Flat.code := rfl
theorem x64_cert1_bounds_eq : x64Cert1Legacy.bounds = x64Cert1Flat.bounds := rfl
theorem x64_cert2_code_eq : x64Cert2Legacy.code = x64Cert2Flat.code := rfl
theorem x64_cert2_bounds_eq : x64Cert2Legacy.bounds = x64Cert2Flat.bounds := rfl

noncomputable def x64CertFullFlat :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean fixMod [] [] 0 2048 :=
  x64Cert1Flat.append x64Cert2Flat (by exact (List.take_append_drop 2 fixMod.fns).symm) rfl

noncomputable def x64CertOptFlat :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (fixSrcMod.optInlinePolicy fixPol) [] [] 0 2048 :=
  x64CertFullFlat.castModule fixMod.eq

section MetaChecks

meta section

open Lean Elab Command Meta

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
  checkCertPair ``x64Cert1Legacy ``x64Cert1Flat 2
  checkCertPair ``x64Cert2Legacy ``x64Cert2Flat 4

#eval show TermElabM Unit from do
  -- Trap T5: `(flat := true)` must fail loudly on unmaterialized `fixSrcMod`.
  let opts : CertOptions := { flatT? := some (← `(true)) }
  let failed ← try
    let _ ← elabAndEvalChunks (← `(x64Target)) (← `(x64Layout)) (← `(x64LegalTarget))
      (← `(x64LabelClean)) (← `(fixSrcMod)) 1 opts
    pure false
  catch _ => pure true
  if !failed then
    throwError "expected (flat := true) on unmaterialized fixSrcMod to throw"
  let pOpts : PrefixExtOptions := { flatT? := some (← `(true)) }
  let pFailed ← try
    let _ ← elabAndEvalPrefixExt (← `(x64Target)) (← `(x64LegalTarget)) (← `(fixSrcMod.fns)) pOpts
    pure false
  catch _ => pure true
  if !pFailed then
    throwError "expected eval_prefix_ext! (flat := true) on unmaterialized fixSrcMod.fns to throw"

end

end MetaChecks

#print axioms x64Cert1Flat
#print axioms x64Cert2Flat
#print axioms x64CertFullFlat
#print axioms x64CertOptFlat
#print axioms x64_cert1_code_eq
#print axioms x64_cert2_code_eq

end LeanQbeTest.T.CompileFlatCertTest
