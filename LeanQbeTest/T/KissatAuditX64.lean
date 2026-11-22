module

public import LeanQbeTest.T.KissatM4AuditX64

/-!
# Kissat audit, part 2: SysV x86-64 machine-code theorems

This file is the active top-level SysV x86-64 Kissat machine-code audit entry point. It
re-exports the active **`D-Full M4`** (`LeanQbe.T.Amd64.KissatM4`, `231` functions) theorem suite
from `LeanQbeTest.T.KissatM4AuditX64` (`audit_m4_x64_fnspec`, `audit_m4_x64_unsat`,
`audit_m4_x64_sound`, `audit_m4_x64_nv`, and `audit_m4_x64_nv_closed`).

`KissatAuditArm64.lean` is the AArch64 mirror, and `KissatAuditSpec.lean` audits `parseDimacs`,
`CNF.Unsat`, `CNF.Sat`, and generic source-level solver invariants.

## Active vs. legacy solver status

* **`D-Full M4`** (`LeanQbe.T.Amd64.KissatM4`, `231` functions): **active** flagship native build,
  **UNSAT (`20`)** soundness + both arbitrary-host and closed concrete-host
  (`kissatM4_compiled_x64.host`) non-vacuity, unconditional.
* Retired machine-code theorems live under `LeanQbeLegacyTest/` (checked when `INCLUDE_LEGACY=1`):
  **`D-Full`** (`166` fns) and **`D-Full M2 Fast`** (`196` fns) in
  `LeanQbeLegacyTest/KissatLegacyAuditX64.lean`; **`D-Plain`** (`59` fns) and **`D-Full M3`**
  (`204` fns) in `LeanQbeLegacyTest/KissatM3PlainLegacyAuditX64.lean`.
-/

set_option autoImplicit false

public section

#print axioms audit_m4_x64_fnspec
#print axioms audit_m4_x64_unsat
#print axioms audit_m4_x64_sound
#print axioms audit_m4_x64_nv
#print axioms audit_m4_x64_nv_closed
