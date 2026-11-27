/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof
public meta import LeanQbeTest.T.LcnfC0FfiPilotCertArm64

/-!
# Shard `F3` AArch64 Certificate Sanity & Strict `std3` Axiom Audit (`LcnfC0FfiPilotArm64Test`)

Kept separate from `LcnfC0FfiPilotTest.lean` because `Kraken.X64.Syntax` and
`Kraken.AArch64.Syntax` cannot be imported in the same Lean module.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.LcnfC0FfiPilotArm64Test

open LeanQbe.T.Arm64
open LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

#guard pilotTailMod.fns.length == 26 && !pilotTailMod.externs.isEmpty
#guard pilotLinkedMod.fns.length == 165 && pilotLinkedMod.externs.isEmpty

#print axioms pilotArm64Cert_bounds_len
#print axioms pilotArm64_legalSigAll
#print axioms pilotArm64InitMem_entry
#print axioms pilotArm64_checkSatBA_fnSpec
#print axioms pilotArm64_checkSatNat_fnSpec
#print axioms pilotArm64_xorBA_fnSpec
#print axioms pilotArm64_xorNat_fnSpec
#print axioms pilotArm64_solveXorBA_fnSpec
#print axioms pilotArm64_checkSatBA_unsat_run
#print axioms pilotArm64_checkSatBA_sat_run
#print axioms pilotArm64_checkSatBA_oom_run
#print axioms pilotArm64_checkSatNat_mpz_unsat_run
#print axioms pilotArm64_checkSatNat_tagged_run
#print axioms pilotArm64_checkSatNat_oom_run
#print axioms pilotArm64_xorBA_ok_run
#print axioms pilotArm64_xorBA_oom_run
#print axioms pilotArm64_xorNat_tagged_ok_run
#print axioms pilotArm64_xorNat_mpz_ok_run
#print axioms pilotArm64_xorNat_oom_run
#print axioms pilotArm64_solveXorBA_unsat_run
#print axioms pilotArm64_solveXorBA_oom_run

end LeanQbeTest.T.LcnfC0FfiPilotArm64Test
