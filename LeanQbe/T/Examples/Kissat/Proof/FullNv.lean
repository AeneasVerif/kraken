/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Full

/-!
# Concrete `8,192 B` `Mem 64` UNSAT Non-Vacuity for `Proof.Full` (`Proof.FullNv`)

Establishes concrete `Mem 64` UNSAT non-vacuity (`r = 20#64`, `nvM6UnsatCnf.Unsat`, restored
workspace, `XPost := False`, `<= std3`) for `Src.Search.kissat_solve_bytes_body` inside the
full `418`-function `fullEnv` / `Src.Full.kissatModule` via `Proof.Spec.fid_unsat_nv_of_fn`
and canonical `Proof.Spec.Solver.solveBytesSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.FullNv

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Full
open Kraken.Bedrock2.Test

public section

/-- Concrete `8,192 B` `Mem 64` UNSAT non-vacuity (`r = 20#64`, `nvM6UnsatCnf.Unsat`,
`XPost := False`) for `Src.Search.kissat_solve_bytes_body` inside `fullEnv` (`418` fns). -/
theorem full_unsat_nv :
    Func.wp fullEnv Src.Search.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of_fn full_moduleOk fullSolveBytesFn_mem
    (fun _ _ _ _ h => fullEnv_solve_bytes_of h)

/-- `6,144 B` workspace (`m6NvWorkLen` / `m6NvPayload`) UNSAT non-vacuity variant for
closed-host ABI tests inside `fullEnv`. -/
theorem fullM6_unsat_nv :
    Func.wp fullEnv Src.Search.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
      ((m6NvPayload nvM6UnsatBytes).At nvM6CnfPtr)
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr m6NvWorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem fullSolveBytesFn_mem
  have hfn := (full_moduleOk.fnsOk pre _ post hsplit).2.2
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp)
        ((m6NvPayload nvM6UnsatBytes).At nvM6CnfPtr) := by
    rw [Std.ExtHashMap.sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
    exact m6NvPayload_sep nvM6UnsatBytes hcb_len
  refine hfn _ _ _ (fun _ _ _ _ => False) (fullEnv_solve_bytes_of ?_)
  unfold Solver.solveBytesSpec
  refine FnContract.intro (nvM6UnsatBytes, m6NvWorkLen) emp
    ⟨rfl, rfl, by decide, by decide⟩ hm0 ?_
  rintro ⟨r, ⟨⟩⟩ ⟨⟩ m' ⟨_, _, htr⟩ hm'
  have hr20 := htr ⟨1, 2, 9, by decide, by decide, by decide, m6Nv_unsat_bound, by decide,
    nvM6Unsat_header, nvM6Unsat_unitTrace⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.FullNv
