/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Bitblast.Build.Flat
import LeanQbeTest.T.BitblastCertCommon
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintAsm0
meta import LeanQbeTest.T.BitblastCertX64

/-!
# Bitblast + KissatPlain SysV x86-64 Certificate Audit & Sanity (`BitblastCertX64Test`)

Kept separate from `BitblastCertArm64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.

Verifies `123`-fn linked module invariants, kernel `bounds.length = 123`, executable AT&T
assembly lowering of `bitblastModule`, and strict `<= std3` `#print axioms` across
`BitblastCertCommon`, `Bitblast.Build.Flat`, and `BitblastCertX64`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.BitblastCertX64Test

open LeanQbe.T LeanQbe.T.Amd64
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertCommon
open LeanQbeTest.T.BitblastCertX64

#guard bitblastLinkedMod.fns.length == 123
#guard bitblastLinkedMod.externs.isEmpty
#guard bitblastLinkedMod.exits.isEmpty
#guard bitblastLinkedMod.checkAcyclic == true
#guard nvSlabBytes.length == 4148
#guard (LeanQbe.T.Examples.Bitblast.Ref.BVProg.parse nvProgBytes).isSome

#guard
  match Driver.compileFns x64Isa x64LegalTarget bitblastModule.fns with
  | .ok ds =>
    let s := Driver.emitAsm printAsm0 bitblastModule.fns ds
    s.contains "bv_solve_bytes:" && s.contains "kissat_solve_bytes"
  | .error _ => false

theorem audit_flat_eq : bitblastFlatMod = bitblastModule :=
  bitblastFlatMod_eq

theorem audit_bounds_len : bitblastX64Cert.bounds.length = 123 :=
  bitblastX64Cert.bounds_length.trans rfl

theorem audit_maxBound_le : bitblastX64Cert.bound "bv_solve_bytes" ≤ 2048 :=
  bitblastX64Cert.bound_le_max "bv_solve_bytes"

#print axioms LeanQbe.T.Examples.Bitblast.Build.bitblastFlatMod_fns_eq
#print axioms LeanQbe.T.Examples.Bitblast.Build.bitblastFlatMod_eq
#print axioms LeanQbeTest.T.BitblastCertCommon.kissatSolveBytesUnsatSpec_refines_plain
#print axioms LeanQbeTest.T.BitblastCertCommon.bitblastLinkedEnv_sound
#print axioms LeanQbeTest.T.BitblastCertCommon.bitblastLinkedEnv_moduleOk
#print axioms LeanQbeTest.T.BitblastCertCommon.nvSlab_trivialUnsat
#print axioms LeanQbeTest.T.BitblastCertCommon.nvSlab_sep
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64Cert
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_legalSigAll
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_bv_solve_bytes_fnSpec
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_host_bv_solve_bytes_fnSpec
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_bv_solve_bytes_unsat_sound
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_host_bv_solve_bytes_unsat_sound
#print axioms LeanQbeTest.T.BitblastCertX64.bitblastX64_nv_unsat_run

end LeanQbeTest.T.BitblastCertX64Test
