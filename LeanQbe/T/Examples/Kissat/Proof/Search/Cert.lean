/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Search.Wp2

/-!
# Segment Certificate for `Src.Search` (`Proof.Search.Cert`)

Assembles `cert : SegCert Spec.deps Src.Search.fns Spec.specs` and discharges the
non-vacuous UNSAT and SAT soundness witnesses (`cert_unsat_nv`, `cert_sat_nv`)
for `kissat_solve_bytes_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Src.Search
open LeanQbe.T.Examples.Kissat.Proof.Spec

theorem cert : SegCert Spec.deps Src.Search.fns Spec.specs := by
  intro Γ hdeps hSat
  have hSimp := Spec.has_full_simplify_m6 hSat
  have hPrep := Spec.has_full_preprocess_m6 hSat
  have hSearch := Spec.has_full_search_m6 hSat
  have hSeeded := Spec.has_kissat_solve_bytes_seeded hSat
  exact ⟨full_preprocess_m6_wp hdeps,
    ⟨full_simplify_m6_wp hdeps,
      ⟨full_search_m6_wp hdeps hSimp,
        ⟨kissat_solve_bytes_seeded_wp hdeps hPrep hSearch,
          ⟨kissat_solve_bytes_wp hSeeded, trivial⟩⟩⟩⟩⟩

theorem cert_unsat_nv {Γ : Env} (hSat : Γ.Sat Spec.specs) :
    Func.wp Γ kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hImpl := kissat_solve_bytes_wp (Spec.has_kissat_solve_bytes_seeded hSat)
  exact fullM6_unsat_nv Γ kissat_solve_bytes_body (fun a m Q X hs => hImpl.2 a m Q X hs)

theorem cert_sat_nv {Γ : Env} (hSat : Γ.Sat Spec.specs) :
    Func.wp Γ kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
            (r = 10#64 → ¬nvM6SatCnf.Unsat ∧
              ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
                CNF.Sat (readModelFromWorkM6 M nvM6SatWorkPtr) nvM6SatCnf) ∧
            (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hImpl := kissat_solve_bytes_wp (Spec.has_kissat_solve_bytes_seeded hSat)
  refine fullM6_sat_nv Γ kissat_solve_bytes_body (fun a m Q X hs => ?_)
  rcases a with ⟨p0, p1, p2, p3, p4, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hfc, hfw, hm, hk⟩ := hs
  exact hImpl.2 (p0, p1, p2, p3, p4, ()) m Q X
    ⟨cnfBytes, wlen, R, hcl, hwl, hfc, hfw, hm,
      fun r m' hr h20 h10 _ hm' => hk r m' hr h20 h10 hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Search
