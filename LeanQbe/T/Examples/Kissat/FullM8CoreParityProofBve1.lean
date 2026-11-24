/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveGates0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveGates1
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6a0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6a
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6b0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6b
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6c0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6c
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveBce
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveVar

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 BVE Proof Hub (`Bve1`)

Public re-export hub for all 24 sharded `FullM8CoreParity` Rank #8 BVE / Kitten `Func.wp` proofs:
- `Bve0`: shared specs, helpers, `full_bve_var_key_m7_m8_wp`.
- `BveGates0`: `full_bve_find_equiv_m8_wp`, `full_bve_find_and_m8_wp`.
- `BveGates1`: `full_bve_match_tern_m8_wp`, `full_bve_find_ite_side_m8_wp`,
  `full_bve_find_ite_m8_wp`, `full_bve_find_xor_m8_wp`.
- `BveK6a0`: `full_k6_watch_m8_wp`, `full_k6_assign_m8_wp`, `full_k6_mtf_m8_wp`,
  `full_k6_backtrack_m8_wp`, `full_k6_ana_cl_m8_wp`.
- `BveK6a`: `full_k6_core_m8_wp`.
- `BveK6b0` / `BveK6b`: `full_k6_prop_m8_wp`, `full_k6_analyze_m8_wp`, `full_k6_solve_m8_wp`.
- `BveK6c0` / `BveK6c`: `full_k6_extract_and_solve_m8_wp`, `full_bve_def_k6_m8_wp`,
  `full_bve_gates_m8_wp`.
- `BveBce`: `full_bve_bce_side_m8_wp`, `full_bve_heap_push_m7_m8_wp`, `full_elim_bve_fid_m8_wp`.
- `BveVar`: `full_bve_var_m7_m8_wp`, `full_bve_var_m8_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
