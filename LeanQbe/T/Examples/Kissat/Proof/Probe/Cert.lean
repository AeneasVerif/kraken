/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Probe.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Probe.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Probe` (`Proof.Probe.Cert`)

Proves `cert : SegCert Spec.deps Src.Probe.fns Spec.specs` cleanly over upstream
`Spec.specs` with zero legacy imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Probe

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Probe
open LeanQbe.T.Examples.Kissat.Proof.Probe.Spec

theorem cert : SegCert Spec.deps Src.Probe.fns Spec.specs := by
  intro Γ hdeps hrows
  have hTiers := hdeps.left.left.left.left.left.left.left.left.left.left.left.left
  have hInternal := hdeps.left.left.left.left.left.left.left.left.left.left.left.right
  have hDense := hdeps.left.left.left.left.left.left.left.left.left.left.right
  have hCong := hdeps.left.left.left.left.left.left.left.left.left.right
  have hFwd := hdeps.left.left.left.left.left.left.left.left.right
  have hSubst := hdeps.left.left.left.left.left.left.left.right
  have hBone := hdeps.left.left.left.left.left.left.right
  have hSweep := hdeps.left.left.left.left.left.right
  have hFact := hdeps.left.left.left.left.right
  have hViv := hdeps.left.left.left.right
  have hTrans := hdeps.left.left.right
  have hF64 := hdeps.left.right
  have hLim := hdeps.right
  have hProbeDt := has_full_probe_dticks_m6_hdr hrows
  have hDelay := Tiers.Spec.has_m6_hdr_delaying hTiers
  have hRedD := Tiers.Spec.has_m6_hdr_reduce_delay hTiers
  have hBumpD := Tiers.Spec.has_m6_hdr_bump_delay hTiers
  have hGetWm := Tiers.Spec.has_m6_hdr_get_watermark hTiers
  have hSetWm := Tiers.Spec.has_m6_hdr_set_watermark hTiers
  have hUpdCls := Internal.Spec.has_full_update_classify_fid hInternal
  have hEnter := Dense.Spec.has_full_enter_dense hDense
  have hEnterEx := Dense.Spec.has_full_enter_dense_ex_fid hDense
  have hCongD := Congruence.Spec.has_full_congruence_dense hCong
  have hBinRt := Forward.Spec.has_full_dense_bin_roundtrip_fid hFwd
  have hReb := Dense.Spec.has_full_rebuild_watches_nosort_fid hDense
  have hSubstS := Substitute.Spec.has_full_substitute hSubst
  have hBoneS := Backbone.Spec.has_full_backbone_m6 hBone
  have hSweepD := Sweep.Spec.has_full_sweep_dense_m6 hSweep
  have hHasFact := Factor.Spec.has_full_has_factor_cands_fid hFact
  have hFactS := Factor.Spec.has_full_factor hFact
  have hVivS := Vivify.Spec.has_full_vivify_m6_hdr hViv
  have hTransS := Transitive.Spec.has_full_transitive_m6 hTrans
  have hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
    Env.Sat.has hF64 (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
      Float64.Spec.f64uPure2Spec_xfree
  have hToU64 : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec :=
    Env.Sat.has hF64 (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      Float64.Spec.f64uPure1Spec_xfree
  have hNlogpown : Γ.Has "f64u_nlogpown" Float64.Spec.f64uPure2Spec :=
    Env.Sat.has hF64 (List.getElem_mem (l := Float64.Spec.specs) (n := 11) (by decide))
      Float64.Spec.f64uPure2Spec_xfree
  have hScaleM5 : Γ.Has "full_scale_delta_m5" Limits.Spec.schedScaleDeltaSpec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 3) (by decide))
      Limits.Spec.schedScaleDeltaSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_probe_dticks_m6_hdr_wp Γ hGetWm)
    , SpecEntry.Impl.of (full_probe_m6_wp Γ hProbeDt hDelay hRedD hBumpD hGetWm hSetWm
        hUpdCls hEnter hEnterEx hCongD hBinRt hReb hSubstS hBoneS hSweepD hHasFact hFactS
        hVivS hTransS hNlogpown hMul hToU64 hScaleM5)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Probe
