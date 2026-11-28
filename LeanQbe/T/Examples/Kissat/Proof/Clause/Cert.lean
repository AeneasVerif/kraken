/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Wp1
public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Clause` (`Proof.Clause.Cert`)

Establishes `SegCert Clause.Spec.deps Src.Clause.fns Clause.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Clause

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Clause

/-- Canonical segment certificate for `Kissat.Src.Clause` (`4` functions,
`deps = Arena ++ Backtrack ++ Watch`). -/
theorem cert : SegCert Spec.deps Src.Clause.fns Spec.specs := fun Γ hDeps hSat => by
  have hAllocCl := Arena.Spec.has_full_alloc_cl hDeps.left.left
  have hAssignLvl := Backtrack.Spec.has_full_assign_lvl hDeps.left.right
  have hBacktrack := Backtrack.Spec.has_full_backtrack hDeps.left.right
  have hWatchPush := Watch.Spec.has_full_watch_push hDeps.right
  have hWatchPop := Watch.Spec.has_full_watch_pop_c0 hDeps.right
  have hHasBin := Watch.Spec.has_full_has_bin hDeps.right
  have hAddBinM6 := Spec.has_full_add_bin_m6 hSat
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_add_clause_wp Γ hAllocCl hWatchPush hWatchPop⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_add_bin_m6_wp Γ hHasBin hWatchPush hAssignLvl⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_add_bin_wp Γ hAddBinM6⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_add_unit_wp Γ hBacktrack hAssignLvl⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Clause
