/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Search.Wp2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1

/-!
# Segment Certificate for `Src.Search` (`Proof.Search.Cert`)

Defines `deps` (`searchDeps`), table metadata (`specs_sigs`, `specs_nodup`, `specs_noExit`),
`cert : SegCert deps Src.Search.fns Spec.specs`, and concrete UNSAT non-vacuity (`cert_unsat_nv`)
for `kissat_solve_bytes_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Src.Search
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Combined upstream specification table across the `19` `Proof.*.Spec` callees of
`Src.Search.fns` (`165` distinct symbols). -/
@[expose] def deps : List SpecEntry := searchDeps

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Search.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem preprocessSpec_xfree : Spec.preprocessSpec.XFree := by
  unfold Spec.preprocessSpec; exact M6HdrCfgContract.toSpec_xfree _

private theorem simplifySpec_xfree : Spec.simplifySpec.XFree := by
  unfold Spec.simplifySpec; exact M6HdrCfgContract.toSpec_xfree _

private theorem searchSpec_xfree : Spec.searchSpec.XFree := by
  unfold Spec.searchSpec; exact M6HdrCfgContract.toSpec_xfree _

private theorem solveBytesSeededSpec_xfree : Spec.solveBytesSeededSpec.XFree := by
  unfold Spec.solveBytesSeededSpec; exact FnContract.toSpec_xfree _

theorem cert : SegCert deps Src.Search.fns Spec.specs := by
  intro Γ hdeps hSat
  have hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec :=
    SpecTable.has_at hSat 1 rfl simplifySpec_xfree
  have hPrep : Γ.Has "full_preprocess_m6" Spec.preprocessSpec :=
    SpecTable.has_at hSat 0 rfl preprocessSpec_xfree
  have hSearch : Γ.Has "full_search_m6" Spec.searchSpec :=
    SpecTable.has_at hSat 2 rfl searchSpec_xfree
  have hSeeded : Γ.Has "kissat_solve_bytes_seeded" Spec.solveBytesSeededSpec :=
    SpecTable.has_at hSat 3 rfl solveBytesSeededSpec_xfree
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
  have hSeeded : Γ.Has "kissat_solve_bytes_seeded" Spec.solveBytesSeededSpec :=
    SpecTable.has_at hSat 3 rfl solveBytesSeededSpec_xfree
  have hImpl := kissat_solve_bytes_wp hSeeded
  exact fullM6_unsat_nv Γ kissat_solve_bytes_body (fun a m Q X hs => hImpl.2 a m Q X hs)

end LeanQbe.T.Examples.Kissat.Proof.Search
