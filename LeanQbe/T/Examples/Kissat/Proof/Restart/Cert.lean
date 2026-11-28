/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Restart.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Restart.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Restart` (`Proof.Restart.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`cert : SegCert deps Src.Restart.fns Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Restart

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Restart

/-- External specifications required by `Kissat.Src.Restart`. -/
@[expose] def deps : List SpecEntry :=
  Proof.Backtrack.Spec.specs ++ Proof.Decide.Spec.specs ++ Proof.Float64.Spec.specs ++
  Proof.Heap.Spec.specs ++ Proof.Limits.Spec.specs ++ Proof.Tiers.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Restart.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

/-- Canonical segment certificate for `Kissat.Src.Restart` (`3` functions). -/
theorem cert : SegCert deps Src.Restart.fns Spec.specs := by
  intro Γ hdeps _
  have hBk : Γ.Sat Proof.Backtrack.Spec.specs := hdeps.left.left.left.left.left
  have hDec : Γ.Sat Proof.Decide.Spec.specs := hdeps.left.left.left.left.right
  have hFl : Γ.Sat Proof.Float64.Spec.specs := hdeps.left.left.left.right
  have hHp : Γ.Sat Proof.Heap.Spec.specs := hdeps.left.left.right
  have hLim : Γ.Sat Proof.Limits.Spec.specs := hdeps.left.right
  have hTr : Γ.Sat Proof.Tiers.Spec.specs := hdeps.right
  have hBacktrack := Proof.Backtrack.Spec.has_full_backtrack hBk
  have hRandecLvl := SpecTable.has_at hDec 1 rfl
    (by unfold Decide.Spec.randecVarLvlSpec; exact FullContract.toSpec_xfree _)
  have hNextDec := SpecTable.has_at hDec 0 rfl
    (by unfold Decide.Spec.nextDecVarSpec; exact FullContract.toSpec_xfree _)
  have hHeapUp := Proof.Heap.Spec.has_full_heap_up hHp
  have hHeapDown := Proof.Heap.Spec.has_full_heap_down hHp
  have hHeapPush := Proof.Heap.Spec.has_full_heap_push hHp
  have hDrInit := Proof.Tiers.Spec.has_m6_hdr_dr_init hTr
  have hSub := SpecTable.has_at hFl 3 rfl f64uPure2Spec_xfree
  have hMul := SpecTable.has_at hFl 4 rfl f64uPure2Spec_xfree
  have hTo := SpecTable.has_at hFl 8 rfl f64uPure1Spec_xfree
  have hLog := SpecTable.has_at hFl 10 rfl f64uPure1Spec_xfree
  have hNlog := SpecTable.has_at hFl 11 rfl f64uPure2Spec_xfree
  have hWm4GetRaw := SpecTable.has_at hFl 12 rfl m6Wm4GetSpec_xfree
  have hWm4Get : Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]) :=
    Float64.Spec.has_m6Wm4Get_to_w2a hWm4GetRaw
  have hWm4Set := SpecTable.has_at hFl 13 rfl m6Wm4SetSpec_xfree
  have hIlog := SpecTable.has_at hLim 1 rfl fullIlog10Spec_xfree
  have hGet64 := SpecTable.has_at hLim 11 rfl m7Get64Spec_xfree
  have hSet64 := SpecTable.has_at hLim 12 rfl m7Set64Spec_xfree
  have hEmaSwap := SpecTable.has_at hLim 14 rfl step13EmaSwapSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_restart_due_wp Γ hSub hMul hLog hTo)
    , SpecEntry.Impl.of (full_restart_wp Γ hRandecLvl hNextDec hBacktrack)
    , SpecEntry.Impl.of (full_switch_mode_m7_wp Γ hWm4Get hWm4Set hHeapUp hHeapDown hHeapPush
        hNlog hTo hEmaSwap hDrInit hIlog hGet64 hSet64 hLog hMul)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Restart
