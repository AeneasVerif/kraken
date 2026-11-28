/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Compact.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpBins
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpArena
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpVars
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpHeur
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpCompact

/-!
# Segment Certificate for `Kissat.Src.Compact` (`Proof.Compact.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`Compact.cert : SegCert deps Src.Compact.fns Spec.specs` from all `13` canonical `Func.wp` proofs
(`0` legacy imports, `0` SAT model proofs, `noExit = true`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

public section

/-- Upstream specification table dependencies for `Src.Compact.fns`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Collect.Spec.specs ++ PropSearch.Spec.specs ++ Watch.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Compact.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

/-- Canonical segment certificate covering all `13` functions of `Kissat.Src.Compact`. -/
theorem cert : SegCert deps Src.Compact.fns Spec.specs := fun Γ hdeps hrows => by
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left.left
  have hRewatch := Collect.Spec.has_full_rewatch_arena hdeps.left.left.right
  have hFlushTrail := PropSearch.Spec.has_full_flush_trail hdeps.left.right
  have hDefrag := Watch.Spec.has_full_wstack_defrag hdeps.right
  have hWatchPush := Watch.Spec.has_full_watch_push hdeps.right
  have hFl : Γ.Has "full_compact_flush" Spec.compactFlushSpec :=
    SpecTable.has_at hrows 1 rfl
      (by unfold Spec.compactFlushSpec; exact M6HdrContract.toSpec_xfree _)
  have hMk : Γ.Has "full_compact_mark_live" Spec.compactMarkLiveSpec :=
    SpecTable.has_at hrows 2 rfl
      (by unfold Spec.compactMarkLiveSpec; exact FullContract.toSpec_xfree _)
  have hMp : Γ.Has "full_compact_assign_map" Spec.compactAssignMapSpec :=
    SpecTable.has_at hrows 3 rfl
      (by unfold Spec.compactAssignMapSpec; exact FullContract.toSpec_xfree _)
  have hRe : Γ.Has "full_compact_record_ext" Spec.compactRecordExtSpec :=
    SpecTable.has_at hrows 4 rfl
      (by unfold Spec.compactRecordExtSpec; exact FullContract.toSpec_xfree _)
  have hBn : Γ.Has "full_compact_bins" Spec.compactBinsSpec :=
    SpecTable.has_at hrows 5 rfl
      (by unfold Spec.compactBinsSpec; exact FullContract.toSpec_xfree _)
  have hAr : Γ.Has "full_compact_arena" Spec.compactArenaSpec :=
    SpecTable.has_at hrows 6 rfl
      (by unfold Spec.compactArenaSpec; exact FullContract.toSpec_xfree _)
  have hVr : Γ.Has "full_compact_vars" Spec.compactVarsSpec :=
    SpecTable.has_at hrows 7 rfl
      (by unfold Spec.compactVarsSpec; exact FullCfgContract.toSpec_xfree _)
  have hSiftQ : Γ.Has "full_compact_sift_q" Spec.compactSiftQSpec :=
    SpecTable.has_at hrows 8 rfl
      (by unfold Spec.compactSiftQSpec; exact FnContract.toSpec_xfree _)
  have hVm : Γ.Has "full_compact_vmtf" Spec.compactHeurSpec :=
    SpecTable.has_at hrows 9 rfl
      (by unfold Spec.compactHeurSpec; exact FullContract.toSpec_xfree _)
  have hSiftH : Γ.Has "full_compact_sift_h" Spec.compactSiftHSpec :=
    SpecTable.has_at hrows 10 rfl
      (by unfold Spec.compactSiftHSpec; exact FnContract.toSpec_xfree _)
  have hHp : Γ.Has "full_compact_heap" Spec.compactHeurSpec :=
    SpecTable.has_at hrows 11 rfl
      (by unfold Spec.compactHeurSpec; exact FullContract.toSpec_xfree _)
  unfold Src.Compact.fns Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_compact_needed_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_flush_wp Γ hFlushTrail)
  · exact SpecEntry.Impl.of (full_compact_mark_live_wp Γ hArenaNext)
  · exact SpecEntry.Impl.of (full_compact_assign_map_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_record_ext_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_bins_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_arena_wp Γ hArenaNext hWatchPush)
  · exact SpecEntry.Impl.of (full_compact_vars_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_sift_q_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_vmtf_wp Γ hSiftQ)
  · exact SpecEntry.Impl.of (full_compact_sift_h_wp Γ)
  · exact SpecEntry.Impl.of (full_compact_heap_wp Γ hSiftH)
  · exact SpecEntry.Impl.of
      (full_compact_wp Γ hFl hMk hMp hRe hBn hDefrag hAr hVr hVm hHp hRewatch)

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
