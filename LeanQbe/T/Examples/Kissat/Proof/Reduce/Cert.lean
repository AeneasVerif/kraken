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
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpLessSift
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduce
import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpPurge

/-!
# Segment Certificate for `Src.Reduce` (`Proof.Reduce.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`Reduce.cert : SegCert deps Src.Reduce.fns Spec.specs` from the canonical WP proofs in
`WpLessSift`, `WpSort`, `WpReduce`, and `WpPurge`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open LeanQbe.T LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Upstream specification table dependencies for `Src.Reduce.fns`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Float64.Spec.specs ++ Internal.Spec.specs ++
    Limits.Spec.specs ++ Tiers.Spec.specs ++ Collect.Spec.specs ++ Compact.Spec.specs ++
    PropSearch.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Reduce.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

/-- Canonical segment certificate for `Src.Reduce.fns`. -/
theorem cert : SegCert deps Src.Reduce.fns Spec.specs := by
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
  have hLess : Γ.Has "full_red_less" Spec.redLessSpec :=
    SpecTable.has_at hRows 0 rfl (by unfold Spec.redLessSpec; exact FnContract.toSpec_xfree _)
  have hSift : Γ.Has "full_red_sift" Spec.redSiftSpec :=
    SpecTable.has_at hRows 1 rfl (by unfold Spec.redSiftSpec; exact FnContract.toSpec_xfree _)
  have hSort : Γ.Has "full_sort_reds" Spec.sortRedsSpec :=
    SpecTable.has_at hRows 2 rfl (by unfold Spec.sortRedsSpec; exact FullContract.toSpec_xfree _)
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
  have hCmpNeed : Γ.Has "full_compact_needed" Compact.Spec.compactNeededSpec :=
    SpecTable.has_at hCmpSat 0 rfl
      (by unfold Compact.Spec.compactNeededSpec; exact FullContract.toSpec_xfree _)
  have hRec := Tiers.Spec.has_m6_hdr_recompute_tiers hTiersSat
  have hMark := Collect.Spec.has_full_mark_reasons hCollSat
  have hNext := Arena.Spec.has_full_arena_next hArenaSat
  have hSweep := Collect.Spec.has_full_arena_sweep_s13 hCollSat
  have hCmp : Γ.Has "full_compact" Compact.Spec.compactSpec :=
    SpecTable.has_at hCmpSat 12 rfl
      (by unfold Compact.Spec.compactSpec; exact M6HdrCfgContract.toSpec_xfree _)
  have hWm := Tiers.Spec.has_m6_hdr_set_watermark hTiersSat
  have hFid := Internal.Spec.has_full_update_classify_fid hIntSat
  dsimp [TableImpl, List.brecOn, Src.Reduce.fns, Src.Reduce.reduce_fns, Spec.specs]
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_red_less_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_red_sift_wp Γ hLess⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_sort_reds_wp Γ hSift⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_reduce_m6_wp Γ hIsqrt hBtk hProp hCmpNeed hRec hMark hNext hSort
      hLog10 hDiv hSub hFromU hMul hToU hSweep hCmp hWm hFid⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_reduce_purge_c0_wp Γ hBtk hProp hMark hSweep hNext⟩,
    trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Reduce
