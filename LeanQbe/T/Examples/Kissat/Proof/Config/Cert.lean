/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Config.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Config
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Config.Wp

/-!
# Canonical Segment Certificate for `Kissat.Src.Config` (`Kissat.Proof.Config.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and
`cert : SegCert deps Src.Config.fns Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Config

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Config
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.Config.Spec

/-- Upstream specification dependencies for `Src.Config.fns`. -/
@[expose] def deps : List SpecEntry := Tiers.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Config.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem getSpec_xfree : Spec.getSpec.XFree := by
  unfold Spec.getSpec; exact M6HdrContract.toSpec_xfree _

private theorem presetSetSpec_xfree : Spec.presetSetSpec.XFree := by
  unfold Spec.presetSetSpec; exact M6HdrContract.toSpec_xfree _

theorem cert : SegCert deps Src.Config.fns Spec.specs := by
  intro Γ hdeps hrows
  have hGetWm := has_m6_hdr_get_watermark hdeps
  have hSetWm := has_m6_hdr_set_watermark hdeps
  have hGet := SpecTable.has_at hrows 5 rfl getSpec_xfree
  have hDef := SpecTable.has_at hrows 10 rfl presetSetSpec_xfree
  have hPlain := SpecTable.has_at hrows 11 rfl presetSetSpec_xfree
  have hBasic := SpecTable.has_at hrows 12 rfl presetSetSpec_xfree
  have hSat := SpecTable.has_at hrows 13 rfl presetSetSpec_xfree
  have hUnsat := SpecTable.has_at hrows 14 rfl presetSetSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (kissat_config_mask_default_wp Γ)
    , SpecEntry.Impl.of (kissat_config_mask_plain_wp Γ)
    , SpecEntry.Impl.of (kissat_config_mask_basic_wp Γ)
    , SpecEntry.Impl.of (kissat_config_mask_sat_wp Γ)
    , SpecEntry.Impl.of (kissat_config_mask_unsat_wp Γ)
    , SpecEntry.Impl.of (kissat_config_get_wp Γ hGetWm)
    , SpecEntry.Impl.of (kissat_config_flag_wp Γ hGet)
    , SpecEntry.Impl.of (kissat_config_stable_wp Γ hGet)
    , SpecEntry.Impl.of (kissat_config_target_wp Γ hGet)
    , SpecEntry.Impl.of (kissat_config_restartint_wp Γ hGet)
    , SpecEntry.Impl.of (kissat_config_default_wp Γ hSetWm)
    , SpecEntry.Impl.of (kissat_config_plain_wp Γ hSetWm)
    , SpecEntry.Impl.of (kissat_config_basic_wp Γ hSetWm)
    , SpecEntry.Impl.of (kissat_config_sat_wp Γ hSetWm)
    , SpecEntry.Impl.of (kissat_config_unsat_wp Γ hSetWm)
    , SpecEntry.Impl.of (kissat_config_has_id_wp Γ)
    , SpecEntry.Impl.of (kissat_set_configuration_wp Γ hDef hPlain hBasic hSat hUnsat)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Config
