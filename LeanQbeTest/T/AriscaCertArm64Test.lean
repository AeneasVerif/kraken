/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Arisca.Build.Flat
import LeanQbe.T.Examples.Arisca.Build.CertCommon
import LeanQbe.T.Arm64.AriscaCert
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.PrintAlign
meta import LeanQbe.T.Examples.Arisca.Src.Module

/-!
# ARiSCA AAPCS64 Arm64 `LinkedCert` Smoke, `emitAsm`, & Axiom Audit (`AriscaCertArm64Test`)

Kept separate from `AriscaCertX64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.

Verifies `44`-fn module invariants, executable AArch64 assembly emission (`Driver.emitAsm`)
covering key ARiSCA entry/core labels, kernel `bounds.length = 44`, exact stack bound `624` for
`arisca_check_bytes`, and strict `<= std3` `#print axioms`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.AriscaCertArm64Test

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.AriscaCert
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build
open LeanQbe.T.Examples.Arisca.Build.CertCommon

#guard ariscaModule.fns.length == 44
#guard ariscaModule.externs.isEmpty
#guard ariscaModule.exits.isEmpty
#guard ariscaModule.checkAcyclic == true

#guard
  match Driver.compileFns armIsa armLegalTarget ariscaModule.fns with
  | .ok ds =>
    let s := Driver.emitAsm toAsm ariscaModule.fns ds
    s.contains "arisca_check_bytes:" &&
    s.contains "ar_check_main:" &&
    s.contains "ar_apply:" &&
    s.contains "ar_parse_aig:" &&
    s.contains "ar_do_gate:"
  | .error _ => false

section

theorem audit_flat_eq : ariscaFlatMod = ariscaModule :=
  ariscaFlatMod_eq

theorem audit_bounds_len : ariscaArm64Cert.bounds.length = 44 :=
  ariscaArm64_bounds_len

theorem audit_entry_bound : ariscaArm64Cert.bound "arisca_check_bytes" = 624 :=
  ariscaArm64_entry_bound

theorem audit_maxBound_le : ariscaArm64Cert.bound "arisca_check_bytes" ≤ 2048 :=
  ariscaArm64_bound_le_max "arisca_check_bytes"

#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64Cert
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_compileModule
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_checkLit
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_checkCompile
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_supportsSource
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_legalSigAll
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_bounds_len
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_bounds_le
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_entry_bound
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_module_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_host_module_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_entry_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_host_entry_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_entry_eventually_of_moduleOk
#print axioms LeanQbe.T.Arm64.AriscaCert.ariscaArm64_entry_run_ret1_of_moduleOk

end

end LeanQbeTest.T.AriscaCertArm64Test
