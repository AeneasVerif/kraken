/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM7Basic
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM7And
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM7Ite
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM7Xor
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM8Equiv
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM8And
import LeanQbe.T.Examples.Kissat.Proof.Gates.WpM8Ite

/-!
# Kissat Gates Segment Certificate (`CanonicalEnv` + `SegCert`)

Assembles all `13` `CanonicalEnv` `Func.wp` theorems for `LeanQbe.T.Examples.Kissat.Src.Gates.fns`
into:
- `allFns_wf : AllFns Fn.Wf Gates.fns`
- `cert : SegCert [] Gates.fns specs`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Gates

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | f :: _, h => ⟨h f (.head _), allFns_of_forall fun g hg => h g (.tail _ hg)⟩

public section

/-- Every function in `Src.Gates.fns` is well-formed (`Func.Wf`). -/
theorem allFns_wf : AllFns Fn.Wf Gates.fns :=
  allFns_of_forall Gates.fns_wf

/-- Canonical `SegCert` for all `13` functions of `Src.Gates.fns` (`0` externs). -/
theorem cert : SegCert [] Gates.fns specs := by
  intro Γ _ hSat
  simp only [Gates.fns, Gates.gates_fns, specs, TableImpl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_bve_find_equiv_m7_wp Γ)
  · exact SpecEntry.Impl.of (full_bve_find_and_m7_wp Γ)
  · exact SpecEntry.Impl.of (full_bve_get_tern_m7_wp Γ)
  · exact SpecEntry.Impl.of (full_bve_match_tern_m7_wp Γ)
  · exact SpecEntry.Impl.of
      (full_bve_find_ite_side_m7_wp Γ
        (has_full_bve_get_tern_m7 hSat) (has_full_bve_match_tern_m7 hSat))
  · exact SpecEntry.Impl.of
      (full_bve_find_ite_m7_wp Γ (has_full_bve_find_ite_side_m7 hSat))
  · exact SpecEntry.Impl.of (full_bve_xor_pat_m7_wp Γ)
  · exact SpecEntry.Impl.of
      (full_bve_find_xor_m7_wp Γ (has_full_bve_xor_pat_m7 hSat))
  · exact SpecEntry.Impl.of (full_bve_find_equiv_m8_wp Γ)
  · exact SpecEntry.Impl.of (full_bve_find_and_m8_wp Γ)
  · exact SpecEntry.Impl.of (full_bve_match_tern_m8_wp Γ)
  · exact SpecEntry.Impl.of
      (full_bve_find_ite_side_m8_wp Γ
        (has_full_bve_get_tern_m7 hSat) (has_full_bve_match_tern_m8 hSat))
  · exact SpecEntry.Impl.of
      (full_bve_find_ite_m8_wp Γ (has_full_bve_find_ite_side_m8 hSat))

end

end LeanQbe.T.Examples.Kissat.Proof.Gates
