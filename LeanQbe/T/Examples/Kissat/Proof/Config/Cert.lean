/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Config.Spec
public import LeanQbe.T.Examples.Kissat.Src.Config
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Config.Wp

/-!
# Canonical Segment Certificate for `Kissat.Src.Config` (`Kissat.Proof.Config.Cert`)

Proves `cert : SegCert Tiers.Spec.specs Src.Config.fns Spec.specs` via `Tiers.Spec.has_*`,
`Config.Spec.has_*`, and `SpecEntry.Impl.of`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Config

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Config
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.Config.Spec

theorem cert : SegCert Tiers.Spec.specs Src.Config.fns Spec.specs := by
  intro Γ hdeps hrows
  have hGetWm := has_m6_hdr_get_watermark hdeps
  have hSetWm := has_m6_hdr_set_watermark hdeps
  have hGet := has_kissat_config_get hrows
  have hDef := has_kissat_config_default hrows
  have hPlain := has_kissat_config_plain hrows
  have hBasic := has_kissat_config_basic hrows
  have hSat := has_kissat_config_sat hrows
  have hUnsat := has_kissat_config_unsat hrows
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
