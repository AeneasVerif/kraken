/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Analyze
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit1
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpRestore
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpReasons
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpAnalyzeCore
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpAnalyze

/-!
# Segment Certificate for `Kissat.Src.Analyze` (`Proof.Analyze.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and establishes
`cert : SegCert deps Src.Analyze.fns Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Canonical upstream specification dependencies for `Src.Analyze.fns` (`16` externs across
`Backtrack`, `Bump`, `Deduce`, `Learn`, `Limits`, `Minimize`, `Tiers`). -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Bump.Spec.specs ++ Deduce.Spec.specs ++
  Learn.Spec.specs ++ Limits.Spec.specs ++ Minimize.Spec.specs ++
  Tiers.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Analyze.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

/-- Canonical segment certificate for `Kissat.Src.Analyze` (`5` functions). -/
theorem cert : SegCert deps Src.Analyze.fns Spec.specs := fun Γ hDeps hSat => by
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
  have hOneLit := SpecTable.has_at hLearnSpecs 1 rfl
    (by unfold Learn.Spec.oneLitConflSpec; exact FullContract.toSpec_xfree _)
  have hLearn := SpecTable.has_at hLearnSpecs 3 rfl
    (by unfold Learn.Spec.learnClauseSpec; exact M6HdrContract.toSpec_xfree _)
  have hTick := Helpers.has_full_tick_rel hLimitsSpecs
  have hEma := Helpers.has_full_ema_update hLimitsSpecs
  have hMinShrink := Helpers.has_full_min_shrink hMinSpecs
  have hUpdTier := Tiers.Spec.has_m6_hdr_update_tier_limits hTiersSpecs
  have hDrUpd := Tiers.Spec.has_m6_hdr_dr_update hTiersSpecs
  have hDelay := Tiers.Spec.has_m6_hdr_delaying hTiersSpecs
  have hDrAllow := Tiers.Spec.has_m6_hdr_dr_allow hTiersSpecs
  have hBumpDelay := Tiers.Spec.has_m6_hdr_bump_delay hTiersSpecs
  have hRedDelay := Tiers.Spec.has_m6_hdr_reduce_delay hTiersSpecs
  have hFailed := SpecTable.has_at hSat 0 rfl
    (by unfold Spec.anaFailedLitSpec; exact M6HdrContract.toSpec_xfree _)
  have hRestore := SpecTable.has_at hSat 1 rfl
    (by unfold Spec.restoreBumpAnaModeSpec; exact M6HdrContract.toSpec_xfree _)
  have hReasons := SpecTable.has_at hSat 2 rfl
    (by unfold Spec.analyzeReasonsSpec; exact M6HdrContract.toSpec_xfree _)
  have hAnaCore := SpecTable.has_at hSat 3 rfl
    (by unfold Spec.analyzeSpec; exact M6HdrContract.toSpec_xfree _)
  exact
    ⟨ SpecEntry.Impl.of (WpFailedLit.full_ana_failed_lit_m6_hdr_wp Γ hClear hBumpMode hBt hAsgn
        hTick hEma)
    , SpecEntry.Impl.of (WpRestore.full_restore_bump_ana_mode_fid_wp Γ hBumpMode hClear)
    , SpecEntry.Impl.of (WpReasons.full_analyze_reasons_fid_wp Γ hDelay hDrAllow hBumpDelay
        hRedDelay)
    , SpecEntry.Impl.of (full_analyze_core_m6_wp Γ hOneLit hFailed hDeduce hUpdTier hRestore
        hMinShrink hReasons hTick hEma hLearn hBumpMode hClear)
    , SpecEntry.Impl.of (full_analyze_m6_hdr_wp Γ hDrUpd hAnaCore)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Analyze
