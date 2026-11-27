/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Tiers.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Tiers.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Tiers` (`Kissat.Proof.Tiers.Cert`)

Proves `cert : SegCert Float64.Spec.specs Src.Tiers.fns Spec.specs` via `Env.Sat.has`,
`Spec.has_*`, and `SpecEntry.Impl.of`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Tiers

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Tiers
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec

theorem cert : SegCert Float64.Spec.specs Src.Tiers.fns Spec.specs := by
  intro Γ hdeps hrows
  have hAdd : Γ.Has "f64u_add" f64uPure2Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 2) (by decide))
      f64uPure2Spec_xfree
  have hSub : Γ.Has "f64u_sub" f64uPure2Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 3) (by decide))
      f64uPure2Spec_xfree
  have hMul : Γ.Has "f64u_mul" f64uPure2Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
      f64uPure2Spec_xfree
  have hDiv : Γ.Has "f64u_div" f64uPure2Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 5) (by decide))
      f64uPure2Spec_xfree
  have hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 7) (by decide))
      f64uPure1Spec_xfree
  have hTo : Γ.Has "f64u_to_u64" f64uPure1Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      f64uPure1Spec_xfree
  have hInit := has_m6_hdr_init hrows
  have hEnsure := has_m6_ext_ensure_init hrows
  have hSync := has_m6_hdr_sync_legacy_tiers hrows
  have hMode := has_m6_hdr_recompute_tiers_mode hrows
  have hRecomp := has_m6_hdr_recompute_tiers hrows
  have hDrInit := has_m6_hdr_dr_init hrows
  exact
    ⟨ SpecEntry.Impl.of (m6_hdr_init_wp Γ)
    , SpecEntry.Impl.of (m6_ext_ensure_init_wp Γ hInit)
    , SpecEntry.Impl.of (m6_hdr_add_ticks_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_sync_legacy_tiers_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_mode_wp Γ hEnsure hSync hFrom hMul hTo)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_wp Γ hMode)
    , SpecEntry.Impl.of (m6_hdr_update_tier_limits_wp Γ hEnsure hRecomp)
    , SpecEntry.Impl.of (m6_hdr_record_used_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_get_tier1_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_get_tier2_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_delaying_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_bump_delay_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_reduce_delay_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_get_watermark_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_set_watermark_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_dr_init_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_dr_update_wp Γ hDrInit hFrom hAdd hSub hMul)
    , SpecEntry.Impl.of (m6_hdr_dr_allow_wp Γ hEnsure hSub hDiv)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Tiers
