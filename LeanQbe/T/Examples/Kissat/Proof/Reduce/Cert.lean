/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpLessSift
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduce
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpPurge

/-!
# Segment Certificate for `Src.Reduce` (`Proof.Reduce.Cert`)

Assembles `SegCert Spec.deps Src.Reduce.fns Spec.specs` from the canonical WP
proofs in `WpLessSift`, `WpSort`, `WpReduce`, and `WpPurge`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open LeanQbe.T LeanQbe.T.Examples.Kissat

/-- Canonical segment certificate for `Src.Reduce.fns`. -/
theorem cert : SegCert Spec.deps Src.Reduce.fns Spec.specs := by
  intro Γ hDeps hRows
  have hPropSat : Γ.Sat PropSearch.Spec.specs := hDeps.right
  have hCmpSat : Γ.Sat Compact.Spec.specs := hDeps.left.right
  have hCollSat : Γ.Sat Collect.Spec.specs := hDeps.left.left.right
  have hTiersSat : Γ.Sat Tiers.Spec.specs := hDeps.left.left.left.right
  have hLimSat : Γ.Sat Limits.Spec.specs := hDeps.left.left.left.left.right
  have hIntSat : Γ.Sat Internal.Spec.specs := hDeps.left.left.left.left.left.right
  have hF64Sat : Γ.Sat Float64.Spec.specs := hDeps.left.left.left.left.left.left.right
  have hBtSat : Γ.Sat Backtrack.Spec.specs := hDeps.left.left.left.left.left.left.left.right
  have hArenaSat : Γ.Sat Arena.Spec.specs := hDeps.left.left.left.left.left.left.left.left
  have hLess := Spec.has_full_red_less hRows
  have hSift := Spec.has_full_red_sift hRows
  have hSort := Spec.has_full_sort_reds hRows
  have hIsqrt : Γ.Has "full_isqrt" Proof.Spec.fullIsqrtSpec :=
    hLimSat.has
      (e := { name := "full_isqrt", as := [i64], rs := [i64],
              spec := Proof.Spec.fullIsqrtSpec, noExit := true })
      (by simp [Limits.Spec.specs]) Limits.Spec.fullIsqrtSpec_xfree
  have hLog10 : Γ.Has "f64u_log10_u64" Float64.Spec.f64uPure1Spec :=
    hF64Sat.has
      (e := { name := "f64u_log10_u64", as := [i64], rs := [i64],
              spec := Float64.Spec.f64uPure1Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure1Spec_xfree
  have hDiv : Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec :=
    hF64Sat.has
      (e := { name := "f64u_div", as := [i64, i64], rs := [i64],
              spec := Float64.Spec.f64uPure2Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure2Spec_xfree
  have hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec :=
    hF64Sat.has
      (e := { name := "f64u_sub", as := [i64, i64], rs := [i64],
              spec := Float64.Spec.f64uPure2Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure2Spec_xfree
  have hFromU : Γ.Has "f64u_from_u64" Float64.Spec.f64uPure1Spec :=
    hF64Sat.has
      (e := { name := "f64u_from_u64", as := [i64], rs := [i64],
              spec := Float64.Spec.f64uPure1Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure1Spec_xfree
  have hMul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
    hF64Sat.has
      (e := { name := "f64u_mul", as := [i64, i64], rs := [i64],
              spec := Float64.Spec.f64uPure2Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure2Spec_xfree
  have hToU : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec :=
    hF64Sat.has
      (e := { name := "f64u_to_u64", as := [i64], rs := [i64],
              spec := Float64.Spec.f64uPure1Spec, noExit := true })
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure1Spec_xfree
  have hBtk := Backtrack.Spec.has_full_backtrack hBtSat
  have hProp := PropSearch.Spec.has_full_propagate hPropSat
  have hCmpNeed := Compact.Spec.has_full_compact_needed hCmpSat
  have hRec := Tiers.Spec.has_m6_hdr_recompute_tiers hTiersSat
  have hMark := Collect.Spec.has_full_mark_reasons hCollSat
  have hNext := Arena.Spec.has_full_arena_next hArenaSat
  have hSweep := Collect.Spec.has_full_arena_sweep_s13 hCollSat
  have hCmp := Compact.Spec.has_full_compact hCmpSat
  have hWm := Tiers.Spec.has_m6_hdr_set_watermark hTiersSat
  have hFid := Internal.Spec.has_full_update_classify_fid hIntSat
  dsimp [TableImpl, List.brecOn, Src.Reduce.fns, Src.Reduce.reduce_fns, Spec.specs]
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_red_less_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_red_sift_wp Γ hLess⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_sort_reds_wp Γ hSift⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_reduce_m6_wp Γ hIsqrt hBtk hProp hCmpNeed hRec hMark hNext hSort
      hLog10 hDiv hSub hFromU hMul hToU hSweep hCmp hWm hFid⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_reduce_purge_c0_wp Γ hBtk hProp hMark hSweep hNext⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Reduce
