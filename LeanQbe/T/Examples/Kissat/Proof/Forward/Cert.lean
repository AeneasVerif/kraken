/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp1b
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp1c
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp2a
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp2b
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp3
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp4

/-!
# Canonical Segment Certificate for `Kissat.Src.Forward` (`Proof.Forward.Cert`)

Assembles `Proof.Forward.cert : SegCert Spec.deps Src.Forward.fns Spec.specs` from the canonical
per-function WP proofs (`Wp0`..`Wp4`) and upstream `Proof.*` capability tables (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Forward.fns` (`9` fns). -/
theorem cert : SegCert Spec.deps Src.Forward.fns Spec.specs := by
  intro Γ hdeps hrows
  have hArena := hdeps.left.left.left.left
  have hWatch := hdeps.left.left.left.right
  have hClause := hdeps.left.left.right
  have hCollect := hdeps.left.right
  have hDense := hdeps.right
  have hArenaNext := Arena.Spec.has_full_arena_next hArena
  have hDefrag := Watch.Spec.has_full_wstack_defrag hWatch
  have hWatchPush := Watch.Spec.has_full_watch_push hWatch
  have hUnwatch := Watch.Spec.has_full_unwatch_large hWatch
  have hAddBin := Clause.Spec.has_full_add_bin hClause
  have hAddUnit := Clause.Spec.has_full_add_unit hClause
  have hSweepBins := Collect.Spec.has_full_sweep_bins hCollect
  have hOcc := Dense.Spec.has_full_dense_occ_cnt_fid hDense
  have hFlushUnits := Dense.Spec.has_full_dense_flush_units_m7 hDense
  have hDedup := Spec.has_full_fwd_dedup_bins hrows
  have hFlushLarge := Spec.has_full_fwd_flush_large_m7 hrows
  have hReconnect := Spec.has_full_fwd_reconnect_irred_m7 hrows
  have hScanLit := Spec.has_full_fwd_scan_lit_m7 hrows
  have hCheckCl := Spec.has_full_fwd_check_cl_m7 hrows
  have hConnectSub := Spec.has_full_fwd_connect_subsumer_m7 hrows
  have hCollectSort := Spec.has_full_fwd_collect_sort_m7 hrows
  unfold Src.Forward.fns Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_fwd_dedup_bins_wp Γ hAddUnit)
  · exact SpecEntry.Impl.of (full_fwd_flush_large_m7_wp Γ hDefrag)
  · exact SpecEntry.Impl.of (full_dense_bin_roundtrip_fid_wp Γ hFlushLarge hSweepBins hWatchPush)
  · exact SpecEntry.Impl.of (full_fwd_reconnect_irred_m7_wp Γ hFlushLarge hArenaNext hWatchPush)
  · exact SpecEntry.Impl.of (full_fwd_scan_lit_m7_wp Γ hOcc)
  · exact SpecEntry.Impl.of
      (full_fwd_check_cl_m7_wp Γ hScanLit hUnwatch hAddUnit hAddBin hFlushUnits)
  · exact SpecEntry.Impl.of (full_fwd_connect_subsumer_m7_wp Γ hOcc hWatchPush)
  · exact SpecEntry.Impl.of (full_fwd_collect_sort_m7_wp Γ hArenaNext)
  · exact SpecEntry.Impl.of
      (full_forward_sub_m7_wp Γ hDedup hFlushUnits hCollectSort hFlushLarge hCheckCl hConnectSub
        hArenaNext hReconnect)

end LeanQbe.T.Examples.Kissat.Proof.Forward
