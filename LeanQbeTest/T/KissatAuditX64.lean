module

public import LeanQbeTest.T.KissatM5AuditX64
public import LeanQbeTest.T.KissatM5SoundAuditX64

/-!
# Kissat audit, part 2: SysV x86-64 machine-code theorems

This file is the active top-level SysV x86-64 Kissat machine-code audit entry point. It
re-exports the active **`D-Full M5`** (`LeanQbe.T.Amd64.KissatM5`, `270` functions,
`InlinePolicy.b5`) theorem suite from `LeanQbeTest.T.KissatM5AuditX64` and
`LeanQbeTest.T.KissatM5SoundAuditX64` (`audit_m5_x64_fnspec`, `audit_m5_x64_unsat`,
`audit_m5_x64_sound`, `audit_m5_x64_nv`, `audit_m5_x64_nv_closed`, `audit_m5_x64_sat_fnspec`,
`audit_m5_x64_model`, `audit_m5_x64_sat_sound`, `audit_m5_x64_model_only`, and
`audit_m5_x64_sound_only`).

`KissatAuditArm64.lean` is the AArch64 mirror, and `KissatAuditSpec.lean` audits `parseDimacs`,
`CNF.Unsat`, `CNF.Sat`, and generic source-level solver invariants.

## Active vs. legacy solver status

* **`D-Full M5`** (`LeanQbe.T.Amd64.KissatM5`, `270` functions): **active** native build,
  **SAT (`10`) and UNSAT (`20`)** soundness + both arbitrary-host and closed concrete-host
  (`kissatM5_compiled_x64.host`) non-vacuity, unconditional.
* Retired machine-code theorems live under `LeanQbeLegacyTest/` (checked when `INCLUDE_LEGACY=1`):
  **`D-Full`** (`166` fns) and **`D-Full M2 Fast`** (`196` fns) in
  `LeanQbeLegacyTest/KissatLegacyAuditX64.lean`; **`D-Plain`** (`59` fns) and **`D-Full M3`**
  (`204` fns) in `LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean`; **`D-Full M4`** (`231` fns)
  in `LeanQbeLegacyTest/KissatM4LegacyAuditX64.lean`.
-/

set_option autoImplicit false

public section

#print axioms audit_m5_x64_fnspec
#print axioms audit_m5_x64_unsat
#print axioms audit_m5_x64_sound
#print axioms audit_m5_x64_nv
#print axioms audit_m5_x64_nv_closed
#print axioms audit_m5_x64_sat_fnspec
#print axioms audit_m5_x64_model
#print axioms audit_m5_x64_sat_sound
#print axioms audit_m5_x64_model_only
#print axioms audit_m5_x64_sound_only
