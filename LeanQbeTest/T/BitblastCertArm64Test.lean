/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Bitblast.Build.Flat
import LeanQbeTest.T.BitblastCertCommon
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.PrintAlign
meta import LeanQbeTest.T.BitblastCertArm64

/-!
# Bitblast + KissatPlain AAPCS64 Arm64 Certificate Audit & Sanity (`BitblastCertArm64Test`)

Kept separate from `BitblastCertX64Test.lean` so `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` remain strictly isolated in separate Lean modules.

Verifies `123`-fn linked module invariants, kernel `bounds.length = 123`, executable AArch64
assembly lowering of `bitblastModule`, and strict `<= std3` `#print axioms` across
`BitblastCertArm64`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.BitblastCertArm64Test

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertCommon
open LeanQbeTest.T.BitblastCertArm64

#guard
  match Driver.compileFns armIsa armLegalTarget bitblastModule.fns with
  | .ok ds =>
    let s := Driver.emitAsm toAsm bitblastModule.fns ds
    s.contains "bv_solve_bytes:" && s.contains "kissat_solve_bytes"
  | .error _ => false

theorem audit_bounds_len : bitblastArm64Cert.bounds.length = 123 :=
  bitblastArm64Cert.bounds_length.trans rfl

theorem audit_maxBound_le : bitblastArm64Cert.bound "bv_solve_bytes" ≤ 2048 :=
  bitblastArm64Cert.bound_le_max "bv_solve_bytes"

#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64Cert
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_legalSigAll
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_bv_solve_bytes_fnSpec
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_host_bv_solve_bytes_fnSpec
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_bv_solve_bytes_unsat_sound
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_host_bv_solve_bytes_unsat_sound
#print axioms LeanQbeTest.T.BitblastCertArm64.bitblastArm64_nv_unsat_run

end LeanQbeTest.T.BitblastCertArm64Test
