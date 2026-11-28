/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Build.Flat
public import LeanQbe.T.Examples.Arisca.Build.CertCommon
public import LeanQbe.T.Amd64.AriscaCert
public meta import LeanQbe.T.Driver
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.PrintAsm0
public meta import LeanQbe.T.Examples.Arisca.Src.Module

/-!
# ARiSCA SysV x86-64 `LinkedCert` Smoke, `emitAsm`, & Axiom Audit (`AriscaCertX64Test`)

Kept separate from `AriscaCertArm64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.

Verifies `44`-fn module invariants, executable AT&T assembly emission (`Driver.emitAsm`) covering
key ARiSCA entry/core labels, kernel `bounds.length = 44`, exact stack bound `656` for
`arisca_check_bytes`, and strict `<= std3` `#print axioms`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.AriscaCertX64Test

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.AriscaCert
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build
open LeanQbe.T.Examples.Arisca.Build.CertCommon

#guard ariscaModule.fns.length == 44
#guard ariscaModule.externs.isEmpty
#guard ariscaModule.exits.isEmpty
#guard ariscaModule.checkAcyclic == true

#guard
  match Driver.compileFns x64Isa x64LegalTarget ariscaModule.fns with
  | .ok ds =>
    let s := Driver.emitAsm printAsm0 ariscaModule.fns ds
    s.contains "arisca_check_bytes:" &&
    s.contains "ar_check_main:" &&
    s.contains "ar_apply:" &&
    s.contains "ar_parse_aig:" &&
    s.contains "ar_do_gate:"
  | .error _ => false

public section

theorem audit_flat_eq : ariscaFlatMod = ariscaModule :=
  ariscaFlatMod_eq

theorem audit_bounds_len : ariscaX64Cert.bounds.length = 44 :=
  ariscaX64_bounds_len

theorem audit_entry_bound : ariscaX64Cert.bound "arisca_check_bytes" = 656 :=
  ariscaX64_entry_bound

theorem audit_maxBound_le : ariscaX64Cert.bound "arisca_check_bytes" ≤ 2048 :=
  ariscaX64_bound_le_max "arisca_check_bytes"

#print axioms LeanQbe.T.Examples.Arisca.Build.ariscaFlatMod_fns_eq
#print axioms LeanQbe.T.Examples.Arisca.Build.ariscaFlatMod_eq
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64Cert
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_compileModule
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_checkLit
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_checkCompile
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_supportsSource
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_legalSigAll
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_bounds_len
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_bounds_le
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_entry_bound
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_module_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_host_module_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_entry_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_host_entry_fnSpec_of_moduleOk
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_entry_eventually_of_moduleOk
#print axioms LeanQbe.T.Amd64.AriscaCert.ariscaX64_entry_run_ret1_of_moduleOk

end

end LeanQbeTest.T.AriscaCertX64Test
