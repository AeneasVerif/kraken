/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Limits.Wp

/-!
# Canonical Segment Certificate for `Kissat.Src.Limits` (`Kissat.Proof.Limits.Cert`)

Proves `cert : SegCert Float64.Spec.specs Src.Limits.fns Spec.specs` via `Env.Sat.has`
and `SpecEntry.Impl.of`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Limits

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Limits
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec

theorem cert : SegCert Float64.Spec.specs Src.Limits.fns Spec.specs := by
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
  have hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 7) (by decide))
      f64uPure1Spec_xfree
  have hTo : Γ.Has "f64u_to_u64" f64uPure1Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      f64uPure1Spec_xfree
  have hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec :=
    Env.Sat.has hdeps (List.getElem_mem (l := Float64.Spec.specs) (n := 10) (by decide))
      f64uPure1Spec_xfree
  have hMax : Γ.Has "full_max_u64" schedMaxU64Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 8) (by decide))
      schedMaxU64Spec_xfree
  have hGet : Γ.Has "full_m7_get64" m7Get64Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 11) (by decide))
      m7Get64Spec_xfree
  have hSet : Γ.Has "full_m7_set64" m7Set64Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 12) (by decide))
      m7Set64Spec_xfree
  have hInit : Γ.Has "full_m7_state_init" step13M7StateInitSpec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 13) (by decide))
      step13M7StateInitSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_isqrt_wp Γ)
    , SpecEntry.Impl.of (full_ilog10_wp Γ)
    , SpecEntry.Impl.of (full_tick_rel_wp Γ)
    , SpecEntry.Impl.of (full_scale_delta_m5_wp Γ hLog hSub hMul hAdd hFrom hTo)
    , SpecEntry.Impl.of (full_ema_update_wp Γ hFrom hAdd hSub hMul)
    , SpecEntry.Impl.of (full_scale_delta_wp Γ hLog hSub hMul hAdd hFrom hTo)
    , SpecEntry.Impl.of (full_fill_u64_m7_wp Γ)
    , SpecEntry.Impl.of (full_sort_u32_wp Γ)
    , SpecEntry.Impl.of (full_max_u64_wp Γ)
    , SpecEntry.Impl.of (full_elim_dticks_wp Γ hMax)
    , SpecEntry.Impl.of (full_lcg_next_m7_wp Γ)
    , SpecEntry.Impl.of (full_m7_get64_wp Γ)
    , SpecEntry.Impl.of (full_m7_set64_wp Γ)
    , SpecEntry.Impl.of (full_m7_state_init_wp Γ hGet hSet)
    , SpecEntry.Impl.of (full_ema_swap_m7_wp Γ hInit hGet hSet)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Limits
