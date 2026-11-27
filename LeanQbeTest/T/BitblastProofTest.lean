/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Full
public import LeanQbe.T.Examples.Bitblast.Proof.Validate
public import LeanQbe.T.Examples.Bitblast.Proof.Aig
public import LeanQbe.T.Examples.Bitblast.Proof.Tseitin0
public import LeanQbe.T.Examples.Bitblast.Proof.Tseitin
public import LeanQbe.T.Examples.Bitblast.Proof.Driver
public import LeanQbe.T.Examples.Kissat.PlainSpec
public meta import LeanQbe.T.Examples.Bitblast.Proof.Full

/-!
# Smoke Tests & Axiom Audit for `Bitblast.Proof` (`S2c`)

Verifies concrete `Mem 64` non-vacuity (`nvProgBytes`), `BVProg.parse` parity, and single-line
`#print axioms` (`<= std3`, `< 115c`) for `bitblast_moduleOk`, `bv_solve_bytes_unsat_wp`,
`nv_bv_solve_bytes_unsat`, and core component WP theorems (`Validate`, `Aig`, `Tseitin`, `Driver`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastProofTest

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof

#guard nvProgBytes.length == 52
#guard BVProg.parse nvProgBytes == some (.const false)
#guard bitblastModule.fns.length == 30
#guard bitblastSpecTable.length == 31

/-- `kissatSolveBytesUnsatSpec` refines `plainSolveBytesSpec` for `S2d` linking. -/
theorem kissatSolveBytesUnsatSpec_refines_plain :
    ∀ {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost},
      kissatSolveBytesUnsatSpec xs m Q X →
      LeanQbe.T.Examples.Kissat.Plain.plainSolveBytesSpec xs m Q X := by
  rintro ⟨cnfPtr, cnfLen, workPtr, workCap, _fuel, ⟨⟩⟩ m Q _X
    ⟨cnfBytes, R, hcl, hcfit, hwfit, hm, hQ⟩
  exact ⟨cnfBytes, workCap.toNat, R, by simp [← hcl], by simp,
    hcfit, hwfit, hm, fun r m' _ hr20 _ hm' => hQ r m' hm' hr20⟩

#print axioms kissatSolveBytesUnsatSpec_refines_plain
#print axioms bitblast_moduleOk
#print axioms bv_solve_bytes_unsat_wp
#print axioms nv_bv_solve_bytes_unsat
#print axioms nvProgBytes_valid
#print axioms nvProgBytes_trivialUnsat
#print axioms nvMem_ok
#print axioms bv_validate_wp
#print axioms bv_mk_and_wp
#print axioms bv_coi_mark_wp
#print axioms bv_dimacs_write_wp
#print axioms bv_solve_bytes_wp

end LeanQbeTest.T.BitblastProofTest
