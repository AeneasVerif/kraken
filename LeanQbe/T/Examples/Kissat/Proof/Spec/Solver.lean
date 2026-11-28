/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Dimacs
public import LeanQbe.T.Examples.Kissat.Src.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Top-Level UNSAT-Only Solver Specification (`Proof.Spec.Solver`)

Pure specification definitions (`0` theorems, `0` `meta`, `0` `deps`, `0` SAT model machinery):
defines `SolveBytesPre`, `solveBytesMem`, `UnitUnsatForced`, `SolveBytesPost`, and the single
canonical UNSAT-only + deterministic `UnitUnsatTrace` non-vacuity contract `solveBytesSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec.Solver

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-- Byte-buffer & workspace-region bounds precondition shared by `kissat_solve_bytes` and
`kissat_solve_bytes_seeded`. -/
@[expose] def SolveBytesPre (cnf_ptr cnf_len work_ptr work_len : BitVec 64)
    (cnfBytes : List UInt8) (wlen : Nat) : Prop :=
  cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
  work_len = BitVec.ofNat 64 wlen ∧
  cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
  work_ptr.toNat + wlen < 2 ^ 64

/-- Spatial footprint of `kissat_solve_bytes`: read-only input `bytes` plus mutable caller
workspace `region`, preserved and restored on return. -/
@[expose] def solveBytesMem (cnf_ptr work_ptr : BitVec 64)
    (cnfBytes : List UInt8) (wlen : Nat) : Mem 64 → Prop :=
  bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen

/-- Deterministic level-0 unit-contradiction non-vacuity trigger: whenever input/workspace
are non-null with nonzero fuel and sufficient workspace (`3,456 B` M6 header + fixed arrays +
clauses + slack) and the input admits a `UnitUnsatTrace`, the solver MUST return `20#64`. -/
@[expose] def UnitUnsatForced (cnfBytes : List UInt8)
    (cnf_ptr work_ptr fuel : BitVec 64) (wlen : Nat) : Prop :=
  ∃ mv nc i0,
    cnf_ptr ≠ 0#64 ∧ work_ptr ≠ 0#64 ∧ 0 < fuel.toNat ∧
    fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen ∧
    i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) ∧
    UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc

/-- Canonical UNSAT-only postcondition for `kissat_solve_bytes` and `kissat_solve_bytes_seeded`:
- return code domain `{0, 10, 20}`,
- UNSAT soundness (`r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`),
- deterministic non-vacuity (`UnitUnsatForced → r = 20#64`),
- UNSAT-only soundness (no SAT model extraction). -/
@[expose] def SolveBytesPost (cnfBytes : List UInt8)
    (cnf_ptr work_ptr fuel : BitVec 64) (wlen : Nat) (r : BitVec 64) : Prop :=
  (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
  (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
  (UnitUnsatForced cnfBytes cnf_ptr work_ptr fuel wlen → r = 20#64)

/-- ONE canonical UNSAT-only + deterministic `UnitUnsatTrace` NV + workspace-restore contract
for `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_len, fuel)`. -/
@[expose] def solveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  FnContract.toSpec (W := List UInt8 × Nat) (W' := Unit) {
    pre := fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) (cnfBytes, wlen) =>
      SolveBytesPre cnf_ptr cnf_len work_ptr work_len cnfBytes wlen
    mem := fun (cnf_ptr, _, work_ptr, _, _, ()) (cnfBytes, wlen) =>
      solveBytesMem cnf_ptr work_ptr cnfBytes wlen
    post := fun (cnf_ptr, _, work_ptr, _, fuel, ()) (cnfBytes, wlen) (r, ()) () =>
      SolveBytesPost cnfBytes cnf_ptr work_ptr fuel wlen r
    postMem := fun (cnf_ptr, _, work_ptr, _, _, ()) (cnfBytes, wlen) _ () =>
      solveBytesMem cnf_ptr work_ptr cnfBytes wlen
  }

end LeanQbe.T.Examples.Kissat.Proof.Spec.Solver
