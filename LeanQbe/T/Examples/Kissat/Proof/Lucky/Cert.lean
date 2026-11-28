/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Lucky` (`Proof.Lucky.Cert`)

Establishes `cert : SegCert Spec.deps Src.Lucky.fns Spec.specs` using `CanonicalEnv`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Lucky
open LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec

/-- Canonical segment certificate for `Kissat.Src.Lucky` (`4` functions). -/
theorem cert : SegCert Spec.deps Src.Lucky.fns Spec.specs := by
  intro Γ hdeps hSat
  have hAr : Γ.Sat Arena.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inl (Or.inl he)))
  have hBk : Γ.Sat Backtrack.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inl (Or.inr he)))
  have hPr : Γ.Sat PropSearch.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inr he))
  have hAn : Γ.Sat Analyze.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inr he)
  have hOrd := Spec.has_full_lucky_ord_fid hSat
  have hScan := Spec.has_full_lucky_scan hSat
  have hPolar := Spec.has_full_lucky_polar_m7 hSat
  have hAssign := Backtrack.Spec.has_full_assign hBk
  have hBt := Backtrack.Spec.has_full_backtrack hBk
  have hProp := PropSearch.Spec.has_full_propagate hPr
  have hAna := Analyze.Spec.has_full_analyze_m6_hdr hAn
  have hNext := Arena.Spec.has_full_arena_next hAr
  exact
    ⟨ SpecEntry.Impl.of (full_lucky_ord_fid_wp Γ)
    , SpecEntry.Impl.of (full_lucky_scan_wp Γ hOrd hAssign hBt hProp hAna)
    , SpecEntry.Impl.of (full_lucky_polar_m7_wp Γ hNext)
    , SpecEntry.Impl.of (full_lucky_late_m7_wp Γ hPolar hScan hAssign hBt hProp)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Lucky
