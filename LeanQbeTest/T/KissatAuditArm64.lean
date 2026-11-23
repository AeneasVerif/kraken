module

public import LeanQbeTest.T.KissatM5AuditArm64
public import LeanQbeTest.T.KissatM5SoundAuditArm64

/-!
# Kissat audit, part 3: AAPCS64 AArch64 machine-code theorems

This file is the active top-level AAPCS64 AArch64 Kissat machine-code audit entry point. It is
the exact AArch64 mirror of `KissatAuditX64.lean`, re-exporting the active **`D-Full M5`**
(`LeanQbe.T.Arm64.KissatM5`, `270` functions, `InlinePolicy.b5`) theorem suite from
`LeanQbeTest.T.KissatM5AuditArm64` and `LeanQbeTest.T.KissatM5SoundAuditArm64`
(`audit_m5_arm_fnspec`, `audit_m5_arm_unsat`, `audit_m5_arm_sound`, `audit_m5_arm_nv`,
`audit_m5_arm_nv_closed`, `audit_m5_arm_sat_fnspec`, `audit_m5_arm_model`, `audit_m5_arm_sat_sound`,
`audit_m5_arm_model_only`, and `audit_m5_arm_sound_only`).

`KissatAuditX64.lean` is the x86-64 mirror, and `KissatAuditSpec.lean` audits `parseDimacs`,
`CNF.Unsat`, `CNF.Sat`, and generic source-level solver invariants.

## Active vs. legacy solver status

* **`D-Full M5`** (`LeanQbe.T.Arm64.KissatM5`, `270` functions): **active** native build,
  **SAT (`10`) and UNSAT (`20`)** soundness + both arbitrary-host and closed concrete-host
  (`kissatM5_compiled_arm64.host`) non-vacuity, unconditional.
* Retired machine-code theorems live under `LeanQbeLegacyTest/` (checked when `INCLUDE_LEGACY=1`):
  **`D-Full`** (`166` fns) and **`D-Full M2 Fast`** (`196` fns) in
  `LeanQbeLegacyTest/KissatLegacyAuditArm64.lean`; **`D-Plain`** (`59` fns) and **`D-Full M3`**
  (`204` fns) in `LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean`; **`D-Full M4`** (`231` fns)
  in `LeanQbeLegacyTest/KissatM4LegacyAuditArm64.lean`.
-/

set_option autoImplicit false

public section

#print axioms audit_m5_arm_fnspec
#print axioms audit_m5_arm_unsat
#print axioms audit_m5_arm_sound
#print axioms audit_m5_arm_nv
#print axioms audit_m5_arm_nv_closed
#print axioms audit_m5_arm_sat_fnspec
#print axioms audit_m5_arm_model
#print axioms audit_m5_arm_sat_sound
#print axioms audit_m5_arm_model_only
#print axioms audit_m5_arm_sound_only
