/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Dense
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Dense.WpOccEnter
import LeanQbe.T.Examples.Kissat.Proof.Dense.WpRebuild
import LeanQbe.T.Examples.Kissat.Proof.Dense.WpDenseProp
import LeanQbe.T.Examples.Kissat.Proof.Dense.WpFlushUnits
import LeanQbe.T.Examples.Kissat.Proof.Dense.WpWatchLarge

/-!
# Segment Certificate for `Kissat.Src.Dense` (`Proof.Dense.Cert`)

Establishes `cert : SegCert Spec.deps Src.Dense.fns Spec.specs` on `CanonicalEnv`
covering all `10` functions in `Src.Dense.fns` (`0` legacy imports, `0` `@[expose]` on
theorems, lemmas, or sections).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Dense

public section

/-- Canonical segment certificate for `Kissat.Src.Dense` (`10` functions). -/
theorem cert : SegCert Spec.deps Src.Dense.fns Spec.specs := by
  intro Γ hDeps hSat
  simp only [Spec.deps, Env.Sat.append_iff] at hDeps
  rcases hDeps with ⟨⟨⟨⟨⟨hAr, hBk⟩, hCl⟩, hCol⟩, hPs⟩, hWa⟩
  have hArenaNext := Arena.Spec.has_full_arena_next hAr
  have hAssign := Backtrack.Spec.has_full_assign_lvl hBk
  have hBacktrack := Backtrack.Spec.has_full_backtrack hBk
  have hAddUnit := Clause.Spec.has_full_add_unit hCl
  have hLitRank := Collect.Spec.has_full_lit_rank_m6 hCol
  have hSweepBins := Collect.Spec.has_full_sweep_bins hCol
  have hSweep := Collect.Spec.has_full_arena_sweep hCol
  have hProp := PropSearch.Spec.has_full_propagate hPs
  have hFlush := PropSearch.Spec.has_full_flush_trail hPs
  have hWatchPush := Watch.Spec.has_full_watch_push_m6 hWa
  have hWatchPushFull := Watch.Spec.has_full_watch_push hWa
  have hSort := Watch.Spec.has_full_sort_bin_watches_fid hWa
  have hEx := Spec.has_full_enter_dense_ex_fid hSat
  have hNosort := Spec.has_full_rebuild_watches_nosort_fid hSat
  have hPropLit := Spec.has_full_m6_dense_prop_lit hSat
  have hPropUnit := Spec.has_full_dense_prop_unit_m7 hSat
  exact
    ⟨ SpecEntry.Impl.of (full_dense_occ_cnt_fid_wp Γ)
    , SpecEntry.Impl.of
        (full_enter_dense_ex_fid_wp Γ hBacktrack hFlush hSweep hProp hSweepBins hWatchPushFull
          hArenaNext)
    , SpecEntry.Impl.of (full_enter_dense_wp Γ hEx)
    , SpecEntry.Impl.of (full_rebuild_watches_nosort_fid_wp Γ hSweep hProp)
    , SpecEntry.Impl.of (full_rebuild_watches_wp Γ hNosort hSort)
    , SpecEntry.Impl.of (full_m6_dense_prop_lit_wp Γ hAssign)
    , SpecEntry.Impl.of (full_m6_dense_prop_wp Γ hPropLit)
    , SpecEntry.Impl.of (full_dense_prop_unit_m7_wp Γ hAddUnit)
    , SpecEntry.Impl.of (full_dense_flush_units_m7_wp Γ hPropUnit)
    , SpecEntry.Impl.of (full_watch_large_clauses_fid_wp Γ hArenaNext hLitRank hWatchPush)
    , trivial
    ⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Dense
