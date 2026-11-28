/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpAnalyzeLitClear
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpAnalyzeRsn
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce3
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsBin
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsLarge2b

/-!
# Canonical Segment Certificate for `Kissat.Src.Deduce` (`Kissat.Proof.Deduce.Cert`)

Proves `cert : SegCert Spec.deps Src.Deduce.fns Spec.specs` over the `Arena`, `Tiers`,
and `Watch` dependency contracts.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec

theorem cert : SegCert Spec.deps Deduce.fns Spec.specs := by
  intro Γ hdeps hrows
  obtain ⟨hAT, hWatch⟩ := Env.Sat.append_iff.mp hdeps
  obtain ⟨hArena, hTiers⟩ := Env.Sat.append_iff.mp hAT
  have hNext := Arena.Spec.has_full_arena_next hArena
  have hRec := Tiers.Spec.has_m6_hdr_record_used hTiers
  have hDefrag := Watch.Spec.has_full_wstack_defrag hWatch
  have hUnw := Watch.Spec.has_full_unwatch_large hWatch
  have hPush := Watch.Spec.has_full_watch_push hWatch
  have hLit := has_full_analyze_lit hrows
  have hRsn := has_full_analyze_rsn_m6_hdr hrows
  have hClr := has_full_clear_ana hrows
  have hLarge := has_full_otfs_large hrows
  have hBin := has_full_otfs_bin hrows
  have hSub := has_full_otfs_subsume hrows
  exact
    ⟨ SpecEntry.Impl.of (full_analyze_lit_wp Γ)
    , SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_wp Γ hLit hRec)
    , SpecEntry.Impl.of (full_clear_ana_wp Γ)
    , SpecEntry.Impl.of (full_otfs_large_wp Γ hDefrag hUnw hPush)
    , SpecEntry.Impl.of (full_otfs_bin_wp Γ hNext hDefrag hUnw hPush)
    , SpecEntry.Impl.of (full_otfs_subsume_wp Γ)
    , SpecEntry.Impl.of (full_deduce_1uip_m6_hdr_wp Γ hLit hRsn hClr hLarge hBin hSub)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Deduce
