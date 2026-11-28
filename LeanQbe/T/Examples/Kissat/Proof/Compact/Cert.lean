/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Compact.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpBins
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpArena
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpVars
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpHeur
import LeanQbe.T.Examples.Kissat.Proof.Compact.WpCompact

/-!
# Segment Certificate for `Kissat.Src.Compact` (`Proof.Compact.Cert`)

Assembles `Proof.Compact.cert : SegCert Spec.deps Src.Compact.fns Spec.specs` from all `13`
canonical `Func.wp` proofs (`Wp0`, `WpBins`, `WpArena`, `WpVars`, `WpHeur`, `WpCompact`) and
upstream `Proof.{Arena,Collect,PropSearch,Watch}.Spec` capability projections (`0` legacy imports,
`0` SAT model proofs, `noExit = true`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

public section

/-- Canonical segment certificate covering all `13` functions of `Kissat.Src.Compact`. -/
theorem cert : SegCert Spec.deps Src.Compact.fns Spec.specs := fun Γ hdeps hrows => by
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left.left
  have hRewatch := Collect.Spec.has_full_rewatch_arena hdeps.left.left.right
  have hFlushTrail := PropSearch.Spec.has_full_flush_trail hdeps.left.right
  have hDefrag := Watch.Spec.has_full_wstack_defrag hdeps.right
  have hWatchPush := Watch.Spec.has_full_watch_push hdeps.right
  have hFl := Compact.Spec.has_full_compact_flush hrows
  have hMk := Compact.Spec.has_full_compact_mark_live hrows
  have hMp := Compact.Spec.has_full_compact_assign_map hrows
  have hRe := Compact.Spec.has_full_compact_record_ext hrows
  have hBn := Compact.Spec.has_full_compact_bins hrows
  have hAr := Compact.Spec.has_full_compact_arena hrows
  have hVr := Compact.Spec.has_full_compact_vars hrows
  have hSiftQ := Compact.Spec.has_full_compact_sift_q hrows
  have hVm := Compact.Spec.has_full_compact_vmtf hrows
  have hSiftH := Compact.Spec.has_full_compact_sift_h hrows
  have hHp := Compact.Spec.has_full_compact_heap hrows
  unfold Src.Compact.fns Compact.Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_needed_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_flush_wp Γ hFlushTrail⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_mark_live_wp Γ hArenaNext⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_assign_map_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_record_ext_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_bins_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_arena_wp Γ hArenaNext hWatchPush⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_vars_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_sift_q_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_vmtf_wp Γ hSiftQ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_sift_h_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_compact_heap_wp Γ hSiftH⟩
  · exact ⟨⟨rfl, rfl, rfl⟩,
      full_compact_wp Γ hFl hMk hMp hRe hBn hDefrag hAr hVr hVm hHp hRewatch⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
