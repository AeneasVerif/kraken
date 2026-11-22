module

public import LeanQbeTest.T.KissatM4AuditArm64

/-!
# Kissat audit, part 3: AAPCS64 AArch64 machine-code theorems

This file is the active top-level AAPCS64 AArch64 Kissat machine-code audit entry point. It is
the exact AArch64 mirror of `KissatAuditX64.lean`, re-exporting the active **`D-Full M4`**
(`LeanQbe.T.Arm64.KissatM4`, `231` functions) theorem suite from `LeanQbeTest.T.KissatM4AuditArm64`
(`audit_m4_arm_fnspec`, `audit_m4_arm_unsat`, `audit_m4_arm_sound`, `audit_m4_arm_nv`, and
`audit_m4_arm_nv_closed`).

`KissatAuditX64.lean` is the x86-64 mirror, and `KissatAuditSpec.lean` audits `parseDimacs`,
`CNF.Unsat`, `CNF.Sat`, and generic source-level solver invariants.

## Active vs. legacy solver status

* **`D-Full M4`** (`LeanQbe.T.Arm64.KissatM4`, `231` functions): **active** flagship native build,
  **UNSAT (`20`)** soundness + both arbitrary-host and closed concrete-host
  (`kissatM4_compiled_arm64.host`) non-vacuity, unconditional.
* Retired machine-code theorems live under `LeanQbeLegacyTest/` (checked when `INCLUDE_LEGACY=1`):
  **`D-Full`** (`166` fns) and **`D-Full M2 Fast`** (`196` fns) in
  `LeanQbeLegacyTest/KissatLegacyAuditArm64.lean`; **`D-Plain`** (`59` fns) and **`D-Full M3`**
  (`204` fns) in `LeanQbeLegacyTest/KissatM3PlainLegacyAuditArm64.lean`.
-/

set_option autoImplicit false

public section

#print axioms audit_m4_arm_fnspec
#print axioms audit_m4_arm_unsat
#print axioms audit_m4_arm_sound
#print axioms audit_m4_arm_nv
#print axioms audit_m4_arm_nv_closed
