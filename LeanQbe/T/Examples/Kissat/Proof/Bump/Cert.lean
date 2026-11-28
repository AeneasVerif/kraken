/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Bump.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Bump.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Bump.WpBump

/-!
# Segment Certificate for `Kissat.Src.Bump` (`Proof.Bump.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`Bump.cert : SegCert deps Src.Bump.fns Spec.specs` (`0` legacy imports, `0` SAT model proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Canonical upstream specification dependencies for `Src.Bump.fns`. -/
@[expose] def deps : List SpecEntry :=
  Float64.Spec.specs ++ Heap.Spec.specs ++ Tiers.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Bump.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem has_f64u_add {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_add" Float64.Spec.f64uPure2Spec :=
  SpecTable.has_at h.left.left 2 rfl Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_mul {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
  SpecTable.has_at h.left.left 4 rfl Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_div {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec :=
  SpecTable.has_at h.left.left 5 rfl Float64.Spec.f64uPure2Spec_xfree

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Bump.fns`. -/
theorem cert : SegCert deps Src.Bump.fns Spec.specs := fun Γ hdeps hrows => by
  have hAdd := has_f64u_add hdeps
  have hMul := has_f64u_mul hdeps
  have hDiv := has_f64u_div hdeps
  have hHeap := Heap.Spec.has_full_heap_up hdeps.left.right
  have hDel := Tiers.Spec.has_m6_hdr_delaying hdeps.right
  have hDr := Tiers.Spec.has_m6_hdr_dr_allow hdeps.right
  have hBumpD := Tiers.Spec.has_m6_hdr_bump_delay hdeps.right
  have hRedD := Tiers.Spec.has_m6_hdr_reduce_delay hdeps.right
  have hRescM6 : Γ.Has "full_rescale_m6" Spec.rescaleSpec :=
    SpecTable.has_at hrows 0 rfl (by unfold Spec.rescaleSpec; exact FullContract.toSpec_xfree _)
  have hResc : Γ.Has "full_rescale" Spec.rescaleSpec :=
    SpecTable.has_at hrows 1 rfl (by unfold Spec.rescaleSpec; exact FullContract.toSpec_xfree _)
  have hBumpVar : Γ.Has "full_bump_var" Spec.bumpVarSpec :=
    SpecTable.has_at hrows 2 rfl (by unfold Spec.bumpVarSpec; exact FullContract.toSpec_xfree _)
  have hDecay : Γ.Has "full_bump_decay" Spec.rescaleSpec :=
    SpecTable.has_at hrows 3 rfl (by unfold Spec.rescaleSpec; exact FullContract.toSpec_xfree _)
  have hRen : Γ.Has "full_queue_renumber" Spec.queueRenumberSpec :=
    SpecTable.has_at hrows 4 rfl
      (by unfold Spec.queueRenumberSpec; exact FullContract.toSpec_xfree _)
  have hMtf : Γ.Has "full_queue_mtf" Spec.queueMtfSpec :=
    SpecTable.has_at hrows 5 rfl (by unfold Spec.queueMtfSpec; exact FullContract.toSpec_xfree _)
  have hAnaSift : Γ.Has "full_ana_sift_m6" Spec.anaSiftSpec :=
    SpecTable.has_at hrows 6 rfl (by unfold Spec.anaSiftSpec; exact FnContract.toSpec_xfree _)
  have hSortAna : Γ.Has "full_sort_ana_qs_m6" Spec.sortAnaQsSpec :=
    SpecTable.has_at hrows 7 rfl (by unfold Spec.sortAnaQsSpec; exact FullContract.toSpec_xfree _)
  unfold Src.Bump.fns Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_rescale_m6_wp Γ hMul hDiv)
  · exact SpecEntry.Impl.of (full_rescale_wp Γ hRescM6)
  · exact SpecEntry.Impl.of (full_bump_var_wp Γ hAdd hHeap hResc)
  · exact SpecEntry.Impl.of (full_bump_decay_wp Γ hMul hResc)
  · exact SpecEntry.Impl.of (full_queue_renumber_wp Γ)
  · exact SpecEntry.Impl.of (full_queue_mtf_wp Γ hRen)
  · exact SpecEntry.Impl.of (full_ana_sift_m6_wp Γ)
  · exact SpecEntry.Impl.of (full_sort_ana_qs_m6_wp Γ hAnaSift)
  · exact SpecEntry.Impl.of
      (full_bump_analyzed_mode_fid_wp Γ hDel hDr hBumpD hRedD hSortAna hMtf hBumpVar hDecay)

end LeanQbe.T.Examples.Kissat.Proof.Bump
