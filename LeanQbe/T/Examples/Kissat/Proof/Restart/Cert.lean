/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Restart.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Restart.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Restart` (`Proof.Restart.Cert`)

Assembles `cert : SegCert Spec.deps Src.Restart.fns Spec.specs` from the three canonical WP
proofs (`full_restart_due_wp`, `full_restart_wp`, `full_switch_mode_m7_wp`) and upstream
`Proof.*` capability tables (`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Restart

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Restart

/-- Canonical segment certificate for `Kissat.Src.Restart` (`3` functions). -/
theorem cert : SegCert Spec.deps Src.Restart.fns Spec.specs := by
  intro Γ hdeps _
  have hBk : Γ.Sat Proof.Backtrack.Spec.specs := hdeps.left.left.left.left.left
  have hDec : Γ.Sat Proof.Decide.Spec.specs := hdeps.left.left.left.left.right
  have hFl : Γ.Sat Proof.Float64.Spec.specs := hdeps.left.left.left.right
  have hHp : Γ.Sat Proof.Heap.Spec.specs := hdeps.left.left.right
  have hLim : Γ.Sat Proof.Limits.Spec.specs := hdeps.left.right
  have hTr : Γ.Sat Proof.Tiers.Spec.specs := hdeps.right
  have hBacktrack := Proof.Backtrack.Spec.has_full_backtrack hBk
  have hRandecLvl := Proof.Decide.Spec.has_full_randec_var_lvl_fid hDec
  have hNextDec := Proof.Decide.Spec.has_full_next_dec_var hDec
  have hHeapUp := Proof.Heap.Spec.has_full_heap_up hHp
  have hHeapDown := Proof.Heap.Spec.has_full_heap_down hHp
  have hHeapPush := Proof.Heap.Spec.has_full_heap_push hHp
  have hDrInit := Proof.Tiers.Spec.has_m6_hdr_dr_init hTr
  have hSub : Γ.Has "f64u_sub" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 3) (by decide))
      f64uPure2Spec_xfree
  have hMul : Γ.Has "f64u_mul" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
      f64uPure2Spec_xfree
  have hTo : Γ.Has "f64u_to_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      f64uPure1Spec_xfree
  have hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 10) (by decide))
      f64uPure1Spec_xfree
  have hNlog : Γ.Has "f64u_nlogpown" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 11) (by decide))
      f64uPure2Spec_xfree
  have hWm4GetRaw : Γ.Has "m6_wm4_get" m6Wm4GetSpec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 12) (by decide))
      m6Wm4GetSpec_xfree
  have hWm4Get : Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]) :=
    Float64.Spec.has_m6Wm4Get_to_w2a hWm4GetRaw
  have hWm4Set : Γ.Has "m6_wm4_set" (m6HdrW2aSpec [i64] []) :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 13) (by decide))
      m6Wm4SetSpec_xfree
  have hIlog : Γ.Has "full_ilog10" fullIlog10Spec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 1) (by decide))
      fullIlog10Spec_xfree
  have hGet64 : Γ.Has "full_m7_get64" m7Get64Spec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 11) (by decide))
      m7Get64Spec_xfree
  have hSet64 : Γ.Has "full_m7_set64" m7Set64Spec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 12) (by decide))
      m7Set64Spec_xfree
  have hEmaSwap : Γ.Has "full_ema_swap_m7" step13EmaSwapSpec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 14) (by decide))
      step13EmaSwapSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_restart_due_wp Γ hSub hMul hLog hTo)
    , SpecEntry.Impl.of (full_restart_wp Γ hRandecLvl hNextDec hBacktrack)
    , SpecEntry.Impl.of (full_switch_mode_m7_wp Γ hWm4Get hWm4Set hHeapUp hHeapDown hHeapPush
        hNlog hTo hEmaSwap hDrInit hIlog hGet64 hSet64 hLog hMul)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Restart
