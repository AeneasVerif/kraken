/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Bump.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Bump.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Bump.WpBump
import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec

/-!
# Canonical Segment Certificate for `Src.Bump`

Assembles `Bump.Cert.cert : SegCert Bump.Spec.deps Src.Bump.fns Bump.Spec.specs`
from the per-function canonical WP proofs (`0` legacy `Full*` imports, `0` SAT model proofs).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

private theorem has_f64u_add {Γ : Env} (h : Γ.Sat Bump.Spec.deps) :
    Γ.Has "f64u_add" Float64.Spec.f64uPure2Spec :=
  h.left.left.has (.tail _ (.tail _ (.head _))) Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_mul {Γ : Env} (h : Γ.Sat Bump.Spec.deps) :
    Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
  h.left.left.has (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_div {Γ : Env} (h : Γ.Sat Bump.Spec.deps) :
    Γ.Has "f64u_div" Float64.Spec.f64uPure2Spec :=
  h.left.left.has (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    Float64.Spec.f64uPure2Spec_xfree

public section

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Bump.fns`. -/
theorem cert : SegCert Bump.Spec.deps Src.Bump.fns Bump.Spec.specs := by
  intro Γ hdeps hrows
  have hAdd := has_f64u_add hdeps
  have hMul := has_f64u_mul hdeps
  have hDiv := has_f64u_div hdeps
  have hHeap := Heap.Spec.has_full_heap_up hdeps.left.right
  have hDel := Tiers.Spec.has_m6_hdr_delaying hdeps.right
  have hDr := Tiers.Spec.has_m6_hdr_dr_allow hdeps.right
  have hBumpD := Tiers.Spec.has_m6_hdr_bump_delay hdeps.right
  have hRedD := Tiers.Spec.has_m6_hdr_reduce_delay hdeps.right
  unfold Src.Bump.fns Bump.Spec.specs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => full_rescale_m6_wp Γ hMul hDiv xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_rescale_wp Γ (Bump.Spec.has_full_rescale_m6 hrows) xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_bump_var_wp Γ hAdd hHeap (Bump.Spec.has_full_rescale hrows) xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_bump_decay_wp Γ hMul (Bump.Spec.has_full_rescale hrows) xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => full_queue_renumber_wp Γ xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_queue_mtf_wp Γ (Bump.Spec.has_full_queue_renumber hrows) xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => full_ana_sift_m6_wp Γ xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_sort_ana_qs_m6_wp Γ (Bump.Spec.has_full_ana_sift_m6 hrows) xs m Q X h⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      full_bump_analyzed_mode_fid_wp Γ hDel hDr hBumpD hRedD
        (Bump.Spec.has_full_sort_ana_qs_m6 hrows) (Bump.Spec.has_full_queue_mtf hrows)
        (Bump.Spec.has_full_bump_var hrows) (Bump.Spec.has_full_bump_decay hrows)
        xs m Q X h⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
