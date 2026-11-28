/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Amd64.BitblastFidelityParam

/-!
# Bitblast + `KissatUnsatPkg` Tier-1 Parameterized Audit: SysV x64 (`std3`)

Audits every Tier-1 parameterized x64 theorem in `LeanQbe.T.Amd64.BitblastFidelityParam`
against `[propext, Classical.choice, Quot.sound]` (`0` `Kissat.Full*`, `0` `*Cert*`, `0` Arm64).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BitblastFidelityParamAuditX64

open LeanQbe.T.Amd64.BitblastFidelityParam

abbrev ax_compile_optInline := @bitblast_fid_x64_unsat_of_compile_optInline
abbrev ax_compile := @bitblast_fid_x64_unsat_of_compile
abbrev ax_fnSpec_cert := @bitblast_fid_x64_fnSpec_of_cert
abbrev ax_unsat_cert := @bitblast_fid_x64_unsat_of_cert
abbrev ax_nv_cert := @bitblast_fid_x64_nv_unsat_run_of_cert

#print axioms ax_compile_optInline
#print axioms ax_compile
#print axioms ax_fnSpec_cert
#print axioms ax_unsat_cert
#print axioms ax_nv_cert

end LeanQbeTest.T.BitblastFidelityParamAuditX64
