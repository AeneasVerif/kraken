/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpMarkRank
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpSweepBins
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpRewatch
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpSweepCopy
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpMoveRed0
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpMoveRed1
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpMoveRed2
import LeanQbe.T.Examples.Kissat.Proof.Collect.WpSweep

/-!
# Canonical Segment Certificate for `Kissat.Src.Collect` (`Proof.Collect.Cert`)

Assembles `Proof.Collect.cert : SegCert Spec.deps Src.Collect.fns Spec.specs` from the 15 canonical
WP proofs across `WpMarkRank`, `WpSweepBins`, `WpRewatch`, `WpSweepCopy`, `WpMoveRed0..2`, and
`WpSweep`, together with upstream `Arena`/`Backtrack`/`Watch` capability tables (`0` legacy
imports, `public section` only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

private theorem has_full_arena_sweep_m6_step13 {Γ : Env} (h : Γ.Sat Spec.specs) :
    Γ.Has "full_arena_sweep_m6" Spec.step13ArenaSweepSpec :=
  Env.Sat.has h
    (List.getElem_mem (l := Spec.specs) (n := 11) (by decide))
    (Spec.specs_xfree _ (List.getElem_mem (l := Spec.specs) (n := 11) (by decide)))

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Collect.fns`. -/
theorem cert : SegCert Spec.deps Src.Collect.fns Spec.specs := by
  intro Γ hdeps hrows
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left
  have hAssignLvl := Backtrack.Spec.has_full_assign_lvl hdeps.left.right
  have hDefragM6 := Watch.Spec.has_full_wstack_defrag_m6 hdeps.right
  have hDefrag := Watch.Spec.has_full_wstack_defrag hdeps.right
  have hPushM6 := Watch.Spec.has_full_watch_push_m6 hdeps.right
  have hPush := Watch.Spec.has_full_watch_push hdeps.right
  have hPop := Watch.Spec.has_full_watch_pop_c0 hdeps.right
  have hLitRank := Spec.has_full_lit_rank_m6 hrows
  have hSweepBinsRange := Spec.has_full_sweep_bins_range_m6 hrows
  have hRewatchRange := Spec.has_full_rewatch_range_m6 hrows
  have hRewatchArenaM6 := Spec.has_full_rewatch_arena_m6 hrows
  have hSweepBinsM6cf := Spec.has_full_sweep_bins_m6cf hrows
  have hSweepCopy := Spec.has_full_sweep_copy hrows
  have hMovePass2 := Spec.has_full_move_red_pass2_m6 hrows
  have hMoveEndBuf := Spec.has_full_move_red_end_buf_m6 hrows
  have hMoveRedEnd := Spec.has_full_move_red_end_m6 hrows
  have hArenaSweepM6 := has_full_arena_sweep_m6_step13 hrows
  have hMarkReasonsM6 := Spec.has_full_mark_reasons_m6 hrows
  unfold Src.Collect.fns Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_lit_rank_m6_wp Γ)
  · exact SpecEntry.Impl.of (full_sweep_bins_range_m6_wp Γ hDefragM6)
  · exact SpecEntry.Impl.of (full_rewatch_range_m6_wp Γ hLitRank hPushM6)
  · exact SpecEntry.Impl.of (full_rewatch_arena_m6_wp Γ hRewatchRange)
  · exact SpecEntry.Impl.of (full_sweep_bins_m6cf_wp Γ hDefrag)
  · exact SpecEntry.Impl.of (full_sweep_bins_wp Γ hSweepBinsM6cf)
  · exact SpecEntry.Impl.of (full_sweep_copy_wp Γ hAssignLvl hPush hPop)
  · exact SpecEntry.Impl.of (full_rewatch_arena_wp Γ hRewatchArenaM6)
  · exact SpecEntry.Impl.of (full_move_red_pass2_m6_wp Γ)
  · exact SpecEntry.Impl.of (full_move_red_end_buf_m6_wp Γ hMovePass2)
  · exact SpecEntry.Impl.of (full_move_red_end_m6_wp Γ hMoveEndBuf)
  · exact SpecEntry.Impl.of
      (full_arena_sweep_m6_wp Γ hSweepBinsRange hArenaNext hSweepCopy hMoveRedEnd hRewatchRange)
  · exact SpecEntry.Impl.of (full_mark_reasons_m6_wp Γ)
  · exact SpecEntry.Impl.of (full_arena_sweep_wp Γ hArenaSweepM6)
  · exact SpecEntry.Impl.of (full_mark_reasons_wp Γ hMarkReasonsM6)

end LeanQbe.T.Examples.Kissat.Proof.Collect
