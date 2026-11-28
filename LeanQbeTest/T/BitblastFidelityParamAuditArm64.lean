/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.BitblastFidelityParam

/-!
# Bitblast + `KissatUnsatPkg` Tier-1 Parameterized Audit: AAPCS64 Arm64 (`std3`)

Audits every Tier-1 parameterized Arm64 theorem in `LeanQbe.T.Arm64.BitblastFidelityParam`
against `[propext, Classical.choice, Quot.sound]` (`0` `Kissat.Full*`, `0` `*Cert*`, `0` x64).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastFidelityParamAuditArm64

open LeanQbe.T.Arm64.BitblastFidelityParam

abbrev ax_compile_optInline := @bitblast_fid_arm64_unsat_of_compile_optInline
abbrev ax_compile := @bitblast_fid_arm64_unsat_of_compile
abbrev ax_fnSpec_cert := @bitblast_fid_arm64_fnSpec_of_cert
abbrev ax_unsat_cert := @bitblast_fid_arm64_unsat_of_cert
abbrev ax_nv_cert := @bitblast_fid_arm64_nv_unsat_run_of_cert

#print axioms ax_compile_optInline
#print axioms ax_compile
#print axioms ax_fnSpec_cert
#print axioms ax_unsat_cert
#print axioms ax_nv_cert

end LeanQbeTest.T.BitblastFidelityParamAuditArm64
