/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Wp1
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Wp2
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Dimacs` (`Proof.Dimacs.Cert`)

Establishes `SegCert [] Src.Dimacs.fns Dimacs.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dimacs

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Dimacs

/-- Canonical segment certificate for `Kissat.Src.Dimacs` (`9` functions, `deps = []`). -/
theorem cert : SegCert ([] : List SpecEntry) Src.Dimacs.fns Spec.specs := fun Γ _ hSat => by
  have hWs := Spec.has_kissat_is_ws hSat
  have hDig := Spec.has_kissat_is_digit hSat
  have hSkip := Spec.has_kissat_skip_ws_comments hSat
  have hWs1 := Spec.has_kissat_skip_ws1 hSat
  have hNat := Spec.has_kissat_read_nat hSat
  have hHdr := Spec.has_kissat_parse_header hSat
  have hLit := Spec.has_kissat_next_lit hSat
  refine ⟨⟨⟨rfl, rfl, rfl⟩, kissat_is_ws_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_is_digit_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_skip_ws_comments_wp Γ hWs⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_skip_ws1_wp Γ hWs⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_read_nat_wp Γ hWs hDig⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_parse_header_wp Γ hSkip hWs1 hNat⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_next_lit_wp Γ hSkip hNat⟩,
    ⟨⟨rfl, rfl, rfl⟩, kissat_check_model_wp Γ hHdr hLit hSkip⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_skip_cl_wp Γ hLit⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Dimacs