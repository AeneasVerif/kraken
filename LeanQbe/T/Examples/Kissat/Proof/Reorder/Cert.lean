/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Reorder.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Reorder.Wp2

/-!
# Canonical Segment Certificate for `Kissat.Src.Reorder` (`Proof.Reorder.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`Proof.Reorder.cert : SegCert deps Src.Reorder.fns Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- External specifications required by `Kissat.Src.Reorder`. -/
@[expose] def deps : List SpecEntry :=
  Float64.Spec.specs ++ Arena.Spec.specs ++ Bump.Spec.specs ++ Heap.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Reorder.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem siftSpec_xfree : Spec.siftSpec.XFree := by
  unfold Spec.siftSpec; exact FnContract.toSpec_xfree _

private theorem queueSpec_xfree : Spec.queueSpec.XFree := by
  unfold Spec.queueSpec; exact FullContract.toSpec_xfree _

private theorem has_f64u_add {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_add" Float64.Spec.f64uPure2Spec :=
  SpecTable.has_at h.left.left.left 2 rfl Float64.Spec.f64uPure2Spec_xfree

private theorem has_f64u_mul {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec :=
  SpecTable.has_at h.left.left.left 4 rfl Float64.Spec.f64uPure2Spec_xfree

private theorem has_full_rescale {Γ : Env} (h : Γ.Sat Bump.Spec.specs) :
    Γ.Has "full_rescale" fullRescaleSpec := by
  have hNew : Γ.Has "full_rescale" Bump.Spec.rescaleSpec :=
    SpecTable.has_at h 1 rfl (by unfold Bump.Spec.rescaleSpec; exact FullContract.toSpec_xfree _)
  rintro ⟨h0, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hNew (c.hdr, ()) m Q X (FullContract.intro (w := ()) hlen trivial hm ?_)
  rintro ⟨⟩ s' m' hlen' ⟨hcore, hmod⟩ hm'
  exact hQ () s' m' hcore hlen'
    ⟨⟨ScratchModifies.get_of_not_mem hmod (f := .last_learned) (by decide),
      ScratchModifies.get_of_not_mem hmod (f := .extend_len) (by decide)⟩,
     ScratchModifies.get_of_not_mem hmod (f := .work_stk1) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .work_stk2) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .tarjan_mark) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .scratch_buf) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .ant_sz) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .res_sz) (by decide),
     ScratchModifies.get_of_not_mem hmod (f := .sim_sig) (by decide)⟩ hm'

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Reorder.fns`. -/
theorem cert : SegCert deps Src.Reorder.fns Spec.specs := by
  intro Γ hdeps hrows
  have hAdd := has_f64u_add hdeps
  have hMul := has_f64u_mul hdeps
  have hArenaNext := Arena.Spec.has_full_arena_next hdeps.left.left.right
  have hRescale := has_full_rescale hdeps.left.right
  have hHeapUp := Heap.Spec.has_full_heap_up hdeps.right
  have hSift := SpecTable.has_at hrows 0 rfl siftSpec_xfree
  have hQueue := SpecTable.has_at hrows 1 rfl queueSpec_xfree
  unfold Src.Reorder.fns Spec.specs
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_reorder_sift_fid_wp Γ)
  · exact SpecEntry.Impl.of
      (full_reorder_queue_m7_wp Γ hAdd hMul hArenaNext hRescale hHeapUp hSift)
  · exact SpecEntry.Impl.of (full_reorder_m6_wp Γ hQueue)

end LeanQbe.T.Examples.Kissat.Proof.Reorder
