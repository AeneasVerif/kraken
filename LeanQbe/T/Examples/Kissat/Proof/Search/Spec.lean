/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Solver

/-!
# Canonical Specifications for `Kissat.Src.Search` (`Proof.Search.Spec`)

Pure specification definitions (`0` theorems, `0` `meta`, `0` `deps`, `0` SAT model machinery)
covering all `5` functions in `Src.Search.fns`:
- `preprocessSpec` (`full_preprocess_m6`)
- `simplifySpec` (`full_simplify_m6`)
- `searchSpec` (`full_search_m6`)
- `solveBytesSeededSpec` (`kissat_solve_bytes_seeded`)
- `Solver.solveBytesSpec` (`kissat_solve_bytes`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- `M6Hdr`-threaded preprocessing specification for `full_preprocess_m6(h)`. -/
@[expose] def preprocessSpec : Spec [i64] [i64] :=
  M6HdrCfgContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    pre := fun c _ext s () F0 =>
      FullSparseInv c F0 s ∧ s.core.cur_level = 0
    post := fun _c _ext s () F0 (r, ()) c' _ext' s' =>
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (r = 20#64 → F0.Unsat) ∧
      (r = 1#64 → FullSparseInv c' F0 s' ∧ s'.core.cur_level = 0) ∧
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap)
  }

/-- `M6Hdr`-threaded in-processing simplification specification for `full_simplify_m6`. -/
@[expose] def simplifySpec : Spec [i64, .bool, .bool] [i64] :=
  M6HdrCfgContract.toSpec (extraArgs := [.bool, .bool]) (rs := [i64]) (W := CNF Nat) {
    pre := fun c _ext s _ F0 =>
      FullSparseInv c F0 s
    post := fun _c _ext s _ F0 (r, ()) _c' _ext' s' =>
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (r = 20#64 → F0.Unsat) ∧
      (r = 1#64 → FullSparseInv _c' F0 s' ∧ s'.core.cur_level = 0)
  }

/-- `M6Hdr`-threaded CDCL search specification for `full_search_m6(h)`. -/
@[expose] def searchSpec : Spec [i64] [i64] :=
  M6HdrCfgContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    pre := fun c _ext s () F0 =>
      FullSparseInv c F0 s ∧ s.core.cur_level = 0
    post := fun _c _ext _s () F0 (r, ()) c' _ext' s' =>
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → F0.Unsat) ∧
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap)
  }

/-- Seeded end-to-end UNSAT-only solver specification for `kissat_solve_bytes_seeded`. -/
@[expose] def solveBytesSeededSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  FnContract.toSpec (W := List UInt8 × Nat) (W' := Unit) {
    pre := fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, _seed, ()) (cnfBytes, wlen) =>
      Solver.SolveBytesPre cnf_ptr cnf_len work_ptr work_len cnfBytes wlen
    mem := fun (cnf_ptr, _, work_ptr, _, _, _, ()) (cnfBytes, wlen) =>
      Solver.solveBytesMem cnf_ptr work_ptr cnfBytes wlen
    post := fun (cnf_ptr, _, work_ptr, _, fuel, _, ()) (cnfBytes, wlen) (r, ()) () =>
      Solver.SolveBytesPost cnfBytes cnf_ptr work_ptr fuel wlen r
    postMem := fun (cnf_ptr, _, work_ptr, _, _, _, ()) (cnfBytes, wlen) _ () =>
      Solver.solveBytesMem cnf_ptr work_ptr cnfBytes wlen
  }

/-- Canonical specification table for `Src.Search.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_preprocess_m6", [i64], [i64], preprocessSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], simplifySpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], searchSpec, true⟩
  , ⟨"kissat_solve_bytes_seeded",
      [i64, i64, i64, i64, i64, i64], [i64], solveBytesSeededSpec, true⟩
  , ⟨"kissat_solve_bytes",
      [i64, i64, i64, i64, i64], [i64], Solver.solveBytesSpec, true⟩ ]

end LeanQbe.T.Examples.Kissat.Proof.Search.Spec
