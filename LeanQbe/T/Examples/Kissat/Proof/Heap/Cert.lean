/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Wp
public import LeanQbe.T.Examples.Kissat.Src.Heap
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Heap` (`Proof.Heap.Cert`)

Establishes `SegCert [] Src.Heap.fns Heap.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Heap

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Heap

/-- Canonical segment certificate for `Kissat.Src.Heap` (`4` functions, `deps = []`). -/
theorem cert : SegCert ([] : List SpecEntry) Src.Heap.fns Spec.specs := fun Γ _ hSat => by
  have hUp := Spec.has_full_heap_up hSat
  have hDown := Spec.has_full_heap_down hSat
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_heap_up_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_heap_down_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_heap_push_wp Γ hUp⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_heap_pop_wp Γ hDown⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Heap
