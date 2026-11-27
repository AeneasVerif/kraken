/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Src.Float64
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Float64.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Float64.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Float64` (`Kissat.Proof.Float64.Cert`)

Proves `cert : SegCert [] Src.Float64.fns Spec.specs` via `Env.Sat.has`, `TableImpl`,
and `has_f64uMsb64_to_pure`, plus signature/name sanity projections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Float64

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Float64
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec

theorem cert : SegCert [] Src.Float64.fns Spec.specs := by
  intro Γ _ hrows
  have hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 0) (by decide))
      f64uMsb64Spec_xfree
  have hMsbP : Γ.Has "f64u_msb64" f64uPure1Spec := has_f64uMsb64_to_pure hMsb
  have hPack : Γ.Has "f64u_round_pack" f64uPure2Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 1) (by decide))
      f64uPure2Spec_xfree
  have hMul : Γ.Has "f64u_mul" f64uPure2Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 4) (by decide))
      f64uPure2Spec_xfree
  have hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 7) (by decide))
      f64uPure1Spec_xfree
  have hMul128 : Γ.Has "u64_mul128" u64Mul128Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 9) (by decide))
      u64Mul128Spec_xfree
  have hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec :=
    Env.Sat.has hrows (List.getElem_mem (l := Spec.specs) (n := 10) (by decide))
      f64uPure1Spec_xfree
  exact
    ⟨ SpecEntry.Impl.of (f64u_msb64_wp Γ)
    , SpecEntry.Impl.of (f64u_round_pack_wp Γ hMsbP)
    , SpecEntry.Impl.of (f64u_add_wp Γ hPack)
    , SpecEntry.Impl.of (f64u_sub_wp Γ hPack)
    , SpecEntry.Impl.of (f64u_mul_wp Γ hMsbP hPack)
    , SpecEntry.Impl.of (f64u_div_wp Γ hMsbP hPack)
    , SpecEntry.Impl.of (f64u_inv_u64_wp Γ hMsb hPack)
    , SpecEntry.Impl.of (f64u_from_u64_wp Γ hMsbP)
    , SpecEntry.Impl.of (f64u_to_u64_wp Γ)
    , SpecEntry.Impl.of (u64_mul128_wp Γ)
    , SpecEntry.Impl.of (f64u_log10_u64_wp Γ hMsbP hPack hMul128)
    , SpecEntry.Impl.of (f64u_nlogpown_wp Γ hLog hMul hFrom)
    , SpecEntry.Impl.of (m6_wm4_get_wp Γ)
    , SpecEntry.Impl.of (m6_wm4_set_wp Γ)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Float64
