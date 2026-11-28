/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpCore
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpSimplify
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpCommit
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpDeduce
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpCounts
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpInst
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpFinish
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpClause
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpCollect
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpSortFid
import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpTop

/-!
# Canonical Segment Certificate for `Kissat.Src.Vivify` (`Kissat.Proof.Vivify.Cert`)

Proves `cert : SegCert Spec.deps Src.Vivify.fns Spec.specs` across all `28` functions of
`Kissat.Src.Vivify` via `Env.Sat.{left,right}`, upstream `*.Spec.has_*`, `Spec.has_*`, and
`SpecEntry.Impl.of`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec

theorem cert : SegCert Spec.deps Src.Vivify.fns Spec.specs := by
  intro Γ hdeps hrows
  have hWatchDep := hdeps.right
  have hTiersDep := hdeps.left.right
  have hPropDep := hdeps.left.left.right
  have hClauseDep := hdeps.left.left.left.right
  have hBtDep := hdeps.left.left.left.left.right
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left.left.left.left
  have hAssign := Backtrack.Spec.has_full_assign hBtDep
  have hBacktrack := Backtrack.Spec.has_full_backtrack hBtDep
  have hAddBin := Clause.Spec.has_full_add_bin_m6 hClauseDep
  have hAddUnit := Clause.Spec.has_full_add_unit hClauseDep
  have hPropIgn := PropSearch.Spec.has_full_propagate_ignore hPropDep
  have hProp := PropSearch.Spec.has_full_propagate hPropDep
  have hSync := Tiers.Spec.has_m6_hdr_sync_legacy_tiers hTiersDep
  have hGetTier1 := Tiers.Spec.has_m6_hdr_get_tier1 hTiersDep
  have hGetTier2 := Tiers.Spec.has_m6_hdr_get_tier2 hTiersDep
  have hDelaying := Tiers.Spec.has_m6_hdr_delaying hTiersDep
  have hBump := Tiers.Spec.has_m6_hdr_bump_delay hTiersDep
  have hReduce := Tiers.Spec.has_m6_hdr_reduce_delay hTiersDep
  have hGetWm := Tiers.Spec.has_m6_hdr_get_watermark_ro hTiersDep
  have hWatchPush := Watch.Spec.has_full_watch_push hWatchDep
  have hUnwatch := Watch.Spec.has_full_unwatch_large hWatchDep
  have hUnreason := has_full_viv_unreason_m6 hrows
  have hWatchRank := has_full_viv_watch_rank_m6 hrows
  have hBestWatch := has_full_viv_best_watch_m6 hrows
  have hSimplify := has_full_viv_simplify_m6 hrows
  have hCommit := has_full_viv_commit_m6 hrows
  have hMarkGarb := has_full_viv_mark_garb_m6 hrows
  have hSubBin := has_full_viv_subsumes_bin_m6 hrows
  have hSubCl := has_full_viv_subsumes_cl_m6 hrows
  have hPromote := has_full_viv_recompute_promote_fid hrows
  have hDeduce := has_full_viv_deduce_m6 hrows
  have hBestImpl := has_full_viv_best_implied_m6 hrows
  have hReest := has_full_viv_reestablish_m6 hrows
  have hInstChk := has_full_viv_inst_check_m6 hrows
  have hInst := has_full_viv_inst_m6 hrows
  have hFinish := has_full_viv_finish_m6 hrows
  have hSift := has_full_viv_sift_counts_m6 hrows
  have hSortCounts := has_full_viv_sort_counts_m6 hrows
  have hHasL0 := has_full_viv_has_l0_m6 hrows
  have hL0Simp := has_full_viv_l0_simp_m6 hrows
  have hReuse := has_full_viv_reuse_prefix_m6 hrows
  have hClause := has_full_viv_clause_m6 hrows
  have hTierMatch := has_full_viv_tier_match_m6 hrows
  have hClearTier := has_full_viv_clear_tier_m6 hrows
  have hCollect := has_full_viv_collect_fid hrows
  have hSort2 := has_full_viv_sort2_fid hrows
  have hSortFid := has_full_viv_sort_fid hrows
  have hVivTier := has_full_vivify_tier_m6_hdr hrows
  exact
    ⟨ SpecEntry.Impl.of (full_viv_unreason_m6_wp Γ hBacktrack)
    , SpecEntry.Impl.of (full_viv_watch_rank_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_best_watch_m6_wp Γ hWatchRank)
    , SpecEntry.Impl.of (full_viv_simplify_m6_wp Γ hUnwatch hAddUnit hAddBin hWatchPush)
    , SpecEntry.Impl.of
        (full_viv_commit_m6_wp Γ hBacktrack hUnwatch hAddUnit hAddBin hWatchPush hUnreason
          hBestWatch)
    , SpecEntry.Impl.of (full_viv_mark_garb_m6_wp Γ hUnreason hUnwatch)
    , SpecEntry.Impl.of (full_viv_subsumes_bin_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_subsumes_cl_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_recompute_promote_fid_wp Γ)
    , SpecEntry.Impl.of (full_viv_deduce_m6_wp Γ hPromote hSubBin hSubCl)
    , SpecEntry.Impl.of (full_viv_best_implied_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_reestablish_m6_wp Γ hBacktrack)
    , SpecEntry.Impl.of (full_viv_inst_check_m6_wp Γ)
    , SpecEntry.Impl.of
        (full_viv_inst_m6_wp Γ hBacktrack hAssign hPropIgn hDeduce hInstChk hCommit)
    , SpecEntry.Impl.of
        (full_viv_finish_m6_wp Γ hDeduce hMarkGarb hBacktrack hCommit hReest hInst)
    , SpecEntry.Impl.of (full_viv_sift_counts_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_sort_counts_m6_wp Γ hSift)
    , SpecEntry.Impl.of (full_viv_has_l0_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_l0_simp_m6_wp Γ hHasL0 hBacktrack hSimplify)
    , SpecEntry.Impl.of (full_viv_reuse_prefix_m6_wp Γ hBacktrack)
    , SpecEntry.Impl.of
        (full_viv_clause_m6_wp Γ hL0Simp hSortCounts hReuse hBestImpl hAssign hPropIgn
          hBacktrack hFinish)
    , SpecEntry.Impl.of (full_viv_tier_match_m6_wp Γ)
    , SpecEntry.Impl.of (full_viv_clear_tier_m6_wp Γ hTierMatch hArenaNext)
    , SpecEntry.Impl.of (full_viv_collect_fid_wp Γ hTierMatch hArenaNext)
    , SpecEntry.Impl.of (full_viv_sort2_fid_wp Γ)
    , SpecEntry.Impl.of (full_viv_sort_fid_wp Γ hSort2)
    , SpecEntry.Impl.of
        (full_vivify_tier_m6_hdr_wp Γ hCollect hSortFid hClearTier hClause hBacktrack hProp
          hGetWm hArenaNext)
    , SpecEntry.Impl.of
        (full_vivify_m6_hdr_wp Γ hVivTier hGetTier1 hGetTier2 hGetWm hSync hBump hReduce
          hDelaying hBacktrack)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Vivify
