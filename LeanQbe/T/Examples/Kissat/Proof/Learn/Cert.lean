/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Learn
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpDetNewLevel
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLit
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpEagerSub
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpLearnClause

/-!
# Segment Certificate for `Kissat.Src.Learn` (`Proof.Learn.Cert`)

Establishes `SegCert deps Src.Learn.fns Learn.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lib

/-- Canonical upstream specification dependencies for `Src.Learn.fns` (`8` externs across
`Backtrack`, `Clause`, `Reduce`, `Watch`). -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Clause.Spec.specs ++ Reduce.Spec.specs ++ Watch.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Learn.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ Spec.specs, e.noExit = true := by
  intro e he
  simp only [Spec.specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

/-- Canonical segment certificate for `Kissat.Src.Learn` (`4` functions). -/
theorem cert : SegCert deps Src.Learn.fns Spec.specs := fun Γ hDeps hSat => by
  have hBtSpecs := hDeps.left.left.left
  have hClauseSpecs := hDeps.left.left.right
  have hReduceSpecs := hDeps.left.right
  have hWatchSpecs := hDeps.right
  have hDnl : Γ.Has "full_det_new_level" Spec.detNewLevelSpec :=
    SpecTable.has_at hSat 0 rfl (by unfold Spec.detNewLevelSpec; exact FullContract.toSpec_xfree _)
  have hEsub : Γ.Has "full_eager_subsume" Spec.eagerSubsumeSpec :=
    SpecTable.has_at hSat 2 rfl (by unfold Spec.eagerSubsumeSpec; exact FullContract.toSpec_xfree _)
  have hBt := Backtrack.Spec.has_full_backtrack_ac_fid hBtSpecs
  have hAsgn := Backtrack.Spec.has_full_assign_lvl hBtSpecs
  have hAddCl := Clause.Spec.has_full_add_clause hClauseSpecs
  have hRedM6 : Γ.Has "full_reduce_m6" Reduce.Spec.reduceSpec :=
    SpecTable.has_at hReduceSpecs 3 rfl
      (by unfold Reduce.Spec.reduceSpec; exact M6HdrCfgContract.toSpec_xfree _)
  have hRedPurge : Γ.Has "full_reduce_purge_c0" Reduce.Spec.reducePurgeSpec :=
    SpecTable.has_at hReduceSpecs 4 rfl
      (by unfold Reduce.Spec.reducePurgeSpec; exact M6HdrContract.toSpec_xfree _)
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
