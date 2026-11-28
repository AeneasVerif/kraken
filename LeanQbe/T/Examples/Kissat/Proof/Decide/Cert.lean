/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp2

/-!
# Canonical Segment Certificate for `Kissat.Src.Decide` (`Proof.Decide.Cert`)

Establishes `cert : SegCert Spec.deps Src.Decide.fns Spec.specs` using `CanonicalEnv`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Decide
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec

/-- Canonical segment certificate for `Kissat.Src.Decide` (`5` functions). -/
theorem cert : SegCert Spec.deps Src.Decide.fns Spec.specs := by
  intro Γ hdeps hSat
  have hBk : Γ.Sat Backtrack.Spec.specs := hdeps.left.left.left.left
  have hFl : Γ.Sat Float64.Spec.specs := hdeps.left.left.left.right
  have hHp : Γ.Sat Heap.Spec.specs := hdeps.left.left.right
  have hLim : Γ.Sat Limits.Spec.specs := hdeps.left.right
  have hTr : Γ.Sat Tiers.Spec.specs := hdeps.right
  have hAssign := Backtrack.Spec.has_full_assign hBk
  have hPop := Heap.Spec.has_full_heap_pop hHp
  have hDrInit := Tiers.Spec.has_m6_hdr_dr_init hTr
  have hMul : Γ.Has "f64u_mul" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
      f64uPure2Spec_xfree
  have hTo : Γ.Has "f64u_to_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      f64uPure1Spec_xfree
  have hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 10) (by decide))
      f64uPure1Spec_xfree
  have hLcg : Γ.Has "full_lcg_next_m7" m7LcgNextSpec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 10) (by decide))
      m7LcgNextSpec_xfree
  have hGet64 : Γ.Has "full_m7_get64" m7Get64Spec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 11) (by decide))
      m7Get64Spec_xfree
  have hSet64 : Γ.Has "full_m7_set64" m7Set64Spec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 12) (by decide))
      m7Set64Spec_xfree
  have hInit : Γ.Has "full_m7_state_init" step13M7StateInitSpec :=
    Env.Sat.has hLim (List.getElem_mem (l := Limits.Spec.specs) (n := 13) (by decide))
      step13M7StateInitSpec_xfree
  have hNextDec := Spec.has_full_next_dec_var hSat
  have hRandecLvl := Spec.has_full_randec_var_lvl_fid hSat
  have hRandec := Spec.has_full_randec_var_m7 hSat
  have hDecide := Spec.has_full_decide_m7 hSat
  exact
    ⟨ SpecEntry.Impl.of (full_next_dec_var_wp Γ hPop)
    , SpecEntry.Impl.of (full_randec_var_lvl_fid_wp Γ hInit hGet64 hSet64 hLog hMul hTo hLcg)
    , SpecEntry.Impl.of (full_randec_var_m7_wp Γ hRandecLvl)
    , SpecEntry.Impl.of (full_decide_m7_wp Γ hRandec hNextDec hAssign)
    , SpecEntry.Impl.of (m6_hdr_decide_fid_wp Γ hDecide hDrInit)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Decide
