/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
import LeanQbe.T.Examples.Kissat.Proof.Reorder.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Reorder.Wp2

/-!
# Canonical Segment Certificate for `Kissat.Src.Reorder` (`Proof.Reorder.Cert`)

Assembles `Proof.Reorder.cert : SegCert Spec.deps Src.Reorder.fns Spec.specs` from the three
canonical WP proofs (`full_reorder_sift_fid_wp`, `full_reorder_queue_m7_wp`, `full_reorder_m6_wp`)
and upstream `Proof.*` capability tables (`0` legacy imports, `0` `@[expose]` on
theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof

private theorem has_f64u_add {Γ : Env} (h : Γ.Sat Spec.deps) :
    Γ.Has "f64u_add" Float64.Spec.f64uPure2Spec :=
  Env.Sat.has h.left.left.left
    (List.getElem_mem (l := Float64.Spec.specs) (n := 2) (by decide))
    Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_mul {Γ : Env} (h : Γ.Sat Spec.deps) :
    Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
  Env.Sat.has h.left.left.left
    (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
    Float64.Spec.f64uPure2Spec_xfree

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Reorder.fns`. -/
theorem cert : SegCert Spec.deps Src.Reorder.fns Spec.specs := by
  intro Γ hdeps hrows
  have hAdd := has_f64u_add hdeps
  have hMul := has_f64u_mul hdeps
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left.right
  have hRescale := Bump.Spec.has_full_rescale hdeps.left.right
  have hHeapUp := Heap.Spec.has_full_heap_up hdeps.right
  have hSift := Spec.has_full_reorder_sift_fid hrows
  have hQueue := Spec.has_full_reorder_queue_m7 hrows
  unfold Src.Reorder.fns Spec.specs
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_reorder_sift_fid_wp Γ)
  · exact SpecEntry.Impl.of
      (full_reorder_queue_m7_wp Γ hAdd hMul hArenaNext hRescale hHeapUp hSift)
  · exact SpecEntry.Impl.of (full_reorder_m6_wp Γ hQueue)

end LeanQbe.T.Examples.Kissat.Proof.Reorder
