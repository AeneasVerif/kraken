/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Wp
public import LeanQbe.T.Examples.Kissat.Src.Arena
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Arena` (`Proof.Arena.Cert`)

Establishes `SegCert [] Src.Arena.fns Arena.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Arena

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Arena

/-- Canonical segment certificate for `Kissat.Src.Arena` (`2` functions, `deps = []`). -/
theorem cert : SegCert ([] : List SpecEntry) Src.Arena.fns Spec.specs := fun Γ _ _ => by
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_arena_next_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_alloc_cl_wp Γ⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Arena
