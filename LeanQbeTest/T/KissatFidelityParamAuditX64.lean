/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatFidelityParam

/-!
# KissatFidelity (`Src.Full.kissatModule`, `418` fns) Parameterized Audit: SysV x64 (`std3`)

Audits every parameterized x64 theorem in `LeanQbe.T.Amd64.KissatFidelityParam`
(`Src.Full.kissatModule`, `418` fns) against `[propext, Classical.choice, Quot.sound]`
(`0` `Kissat.Full*`, `0` `*Cert*`, `0` `*Inl*`, `0` Arm64).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityParamAuditX64

open LeanQbe.T.Amd64.KissatFidelityParam

abbrev ax_fnspec_compile := @fid_module_fnspec_x64_of_compile
abbrev ax_fnspec_compile_maxB := @fid_module_fnspec_x64_maxB_of_compile
abbrev ax_solve_compile := @fid_solve_bytes_unsat_x64_of_compile
abbrev ax_correct_compile := @kissat_fid_x64_unsat_correct_of_compile
abbrev ax_nv_compile := @kissat_fid_x64_unsat_nonvacuous_of_compile
abbrev ax_run_compile := @kissat_fid_x64_run_unsat_of_compile
abbrev ax_fnspec_cert := @fid_module_fnspec_of_cert
abbrev ax_solve_cert := @fid_solve_bytes_unsat_x64_of_cert
abbrev ax_solve_maxB_cert := @fid_solve_bytes_unsat_x64_maxB_of_cert
abbrev ax_correct_cert := @kissat_fid_x64_unsat_correct_of_cert
abbrev ax_correct_maxB_cert := @kissat_fid_x64_unsat_correct_maxB_of_cert
abbrev ax_nv_cert := @kissat_fid_x64_unsat_nonvacuous_of_cert
abbrev ax_nv_maxB_cert := @kissat_fid_x64_unsat_nonvacuous_maxB_of_cert
abbrev ax_run_cert := @kissat_fid_x64_run_unsat_of_cert
abbrev ax_run_maxB_cert := @kissat_fid_x64_run_unsat_maxB_of_cert

#print axioms ax_fnspec_compile
#print axioms ax_fnspec_compile_maxB
#print axioms ax_solve_compile
#print axioms ax_correct_compile
#print axioms ax_nv_compile
#print axioms ax_run_compile
#print axioms ax_fnspec_cert
#print axioms ax_solve_cert
#print axioms ax_solve_maxB_cert
#print axioms ax_correct_cert
#print axioms ax_correct_maxB_cert
#print axioms ax_nv_cert
#print axioms ax_nv_maxB_cert
#print axioms ax_run_cert
#print axioms ax_run_maxB_cert

end LeanQbeTest.T.KissatFidelityParamAuditX64
