/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Src.Learn
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpDetNewLevel
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLit
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpEagerSub
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpLearnClause

/-!
# Segment Certificate for `Kissat.Src.Learn` (`Proof.Learn.Cert`)

Establishes `SegCert Learn.Spec.deps Src.Learn.fns Learn.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

/-- Canonical segment certificate for `Kissat.Src.Learn` (`4` functions). -/
theorem cert : SegCert Spec.deps Src.Learn.fns Spec.specs := fun Γ hDeps hSat => by
  have hBtSpecs := hDeps.left.left.left
  have hClauseSpecs := hDeps.left.left.right
  have hReduceSpecs := hDeps.left.right
  have hWatchSpecs := hDeps.right
  have hDnl := Spec.has_full_det_new_level hSat
  have hEsub := Spec.has_full_eager_subsume hSat
  have hBt := Backtrack.Spec.has_full_backtrack_ac_fid hBtSpecs
  have hAsgn := Backtrack.Spec.has_full_assign_lvl hBtSpecs
  have hAddCl := Clause.Spec.has_full_add_clause hClauseSpecs
  have hRedM6 := Reduce.Spec.has_full_reduce_m6 hReduceSpecs
  have hRedPurge := Reduce.Spec.has_full_reduce_purge_c0 hReduceSpecs
  have hDefrag := Watch.Spec.has_full_wstack_defrag hWatchSpecs
  have hUnw := Watch.Spec.has_full_unwatch_large hWatchSpecs
  have hPush := Watch.Spec.has_full_watch_push hWatchSpecs
  unfold Src.Learn.fns Spec.specs
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_det_new_level_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_one_lit_confl_wp Γ hDefrag hDnl hBt hAsgn hUnw hPush⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_eager_subsume_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩,
      full_learn_clause_m6_wp Γ hBt hAsgn hDnl hDefrag hRedM6 hRedPurge hAddCl hEsub⟩,
    trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Learn
