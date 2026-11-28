/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Src.Analyze
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit1
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpRestore
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpReasons
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpAnalyzeCore
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpAnalyze

/-!
# Segment Certificate for `Kissat.Src.Analyze` (`Proof.Analyze.Cert`)

Establishes `SegCert Analyze.Spec.deps Src.Analyze.fns Analyze.Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

/-- Canonical segment certificate for `Kissat.Src.Analyze` (`5` functions). -/
theorem cert : SegCert Spec.deps Src.Analyze.fns Spec.specs := fun Γ hDeps hSat => by
  have hBtSpecs := hDeps.left.left.left.left.left.left
  have hBumpSpecs := hDeps.left.left.left.left.left.right
  have hDeduceSpecs := hDeps.left.left.left.left.right
  have hLearnSpecs := hDeps.left.left.left.right
  have hLimitsSpecs := hDeps.left.left.right
  have hMinSpecs := hDeps.left.right
  have hTiersSpecs := hDeps.right
  have hBt := Backtrack.Spec.has_full_backtrack_ac_fid hBtSpecs
  have hAsgn := Backtrack.Spec.has_full_assign_lvl hBtSpecs
  have hBumpMode := Bump.Spec.has_full_bump_analyzed_mode_fid hBumpSpecs
  have hClear := Deduce.Spec.has_full_clear_ana hDeduceSpecs
  have hDeduce := Deduce.Spec.has_full_deduce_1uip_m6_hdr hDeduceSpecs
  have hOneLit := Learn.Spec.has_full_one_lit_confl hLearnSpecs
  have hLearn := Learn.Spec.has_full_learn_clause_m6 hLearnSpecs
  have hTick := Helpers.has_full_tick_rel hLimitsSpecs
  have hEma := Helpers.has_full_ema_update hLimitsSpecs
  have hMinShrink := Helpers.has_full_min_shrink hMinSpecs
  have hUpdTier := Tiers.Spec.has_m6_hdr_update_tier_limits hTiersSpecs
  have hDrUpd := Tiers.Spec.has_m6_hdr_dr_update hTiersSpecs
  have hDelay := Tiers.Spec.has_m6_hdr_delaying hTiersSpecs
  have hDrAllow := Tiers.Spec.has_m6_hdr_dr_allow hTiersSpecs
  have hBumpDelay := Tiers.Spec.has_m6_hdr_bump_delay hTiersSpecs
  have hRedDelay := Tiers.Spec.has_m6_hdr_reduce_delay hTiersSpecs
  have hFailed := Spec.has_full_ana_failed_lit_m6_hdr hSat
  have hRestore := Spec.has_full_restore_bump_ana_mode_fid hSat
  have hReasons := Spec.has_full_analyze_reasons_fid hSat
  have hAnaCore := Spec.has_full_analyze_core_m6 hSat
  unfold Src.Analyze.fns Spec.specs
  refine ⟨⟨⟨rfl, rfl, rfl⟩,
      WpFailedLit.full_ana_failed_lit_m6_hdr_wp Γ hClear hBumpMode hBt hAsgn hTick hEma⟩,
    ⟨⟨rfl, rfl, rfl⟩, WpRestore.full_restore_bump_ana_mode_fid_wp Γ hBumpMode hClear⟩,
    ⟨⟨rfl, rfl, rfl⟩,
      WpReasons.full_analyze_reasons_fid_wp Γ hDelay hDrAllow hBumpDelay hRedDelay⟩,
    ⟨⟨rfl, rfl, rfl⟩, ?_⟩,
    ⟨⟨rfl, rfl, rfl⟩, ?_⟩,
    trivial⟩
  · dsimp only [Src.Analyze.full_analyze_core_m6, SpecEntry.eff]
    exact fun xs m Q X he => full_analyze_core_m6_wp Γ hOneLit hFailed hDeduce hUpdTier hRestore
      hMinShrink hReasons hTick hEma hLearn hBumpMode hClear xs m Q X
      (Proof.Spec.m6HdrAnalyzeSpec_monoX he)
  · dsimp only [Src.Analyze.full_analyze_m6_hdr, SpecEntry.eff]
    exact fun xs m Q X he => full_analyze_m6_hdr_wp Γ hDrUpd hAnaCore xs m Q X
      (Proof.Spec.m6HdrAnalyzeSpec_monoX he)

end LeanQbe.T.Examples.Kissat.Proof.Analyze
