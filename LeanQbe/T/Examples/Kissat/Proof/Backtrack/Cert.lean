/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Wp1
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Wp2
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Src.Backtrack
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Backtrack` (`Proof.Backtrack.Cert`)

Establishes `SegCert Heap.Spec.specs Src.Backtrack.fns Backtrack.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Backtrack

/-- Canonical segment certificate for `Kissat.Src.Backtrack` (`6` functions, `deps = Heap`). -/
theorem cert : SegCert Spec.deps Src.Backtrack.fns Spec.specs := fun Γ hDeps hSat => by
  have hHeapPush := Heap.Spec.has_full_heap_push hDeps
  have hAssignLvl := Spec.has_full_assign_lvl hSat
  have hSave := Spec.has_full_save_target_best hSat
  have hRaw := Spec.has_full_backtrack_raw_m5 hSat
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_assign_lvl_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_assign_wp Γ hAssignLvl⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_save_target_best_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backtrack_raw_m5_wp Γ hSave hHeapPush⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backtrack_wp Γ hSave hRaw⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backtrack_ac_fid_wp Γ hSave hRaw⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Backtrack
