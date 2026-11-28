/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Kitten
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpLeaf
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpInit
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAddClause
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpBtFlip
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAddLive
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpPropagate
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAnaClause
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAnalyze
import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpSolve

/-!
# Canonical Segment Certificate for `Kissat.Src.Kitten` (`Kissat.Proof.Kitten.Cert`)

Proves `cert : SegCert Spec.deps Src.Kitten.fns Spec.specs` (`14` C0 functions, `0` externs)
against `Kissat.Src.Kitten.fns` via `Spec.has_full_*` and `SpecEntry.Impl.of`.
Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas; `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Kitten`
    (`14` fns, `0` externs). -/
theorem cert : SegCert Spec.deps Src.Kitten.fns Spec.specs := by
  intro Γ _ hrows
  have hMaxV := has_full_m6_max_v hrows
  have hAddTicks := has_full_k6_add_ticks hrows
  have hWatch := has_full_k6_watch hrows
  have hAssign := has_full_k6_assign hrows
  have hMtf := has_full_k6_mtf hrows
  have hBt := has_full_k6_backtrack hrows
  have hProp := has_full_k6_propagate hrows
  have hAnaCl := has_full_k6_ana_clause hrows
  have hAna := has_full_k6_analyze hrows
  exact
    ⟨ SpecEntry.Impl.of (full_m6_max_v_wp Γ)
    , SpecEntry.Impl.of (full_k6_add_ticks_wp Γ)
    , SpecEntry.Impl.of (full_k6_init_wp Γ hMaxV)
    , SpecEntry.Impl.of (full_k6_watch_wp Γ)
    , SpecEntry.Impl.of (full_k6_assign_wp Γ)
    , SpecEntry.Impl.of (full_k6_add_clause_wp Γ hMaxV hAssign hAddTicks hWatch)
    , SpecEntry.Impl.of (full_k6_mtf_wp Γ)
    , SpecEntry.Impl.of (full_k6_backtrack_wp Γ)
    , SpecEntry.Impl.of (full_k6_propagate_wp Γ)
    , SpecEntry.Impl.of (full_k6_ana_clause_wp Γ)
    , SpecEntry.Impl.of (full_k6_analyze_wp Γ hAnaCl hBt hMtf hWatch hAssign)
    , SpecEntry.Impl.of (full_k6_solve_wp Γ hMaxV hBt hAssign hProp hAna)
    , SpecEntry.Impl.of (full_k6_flip_wp Γ hMaxV hAddTicks)
    , SpecEntry.Impl.of (full_k512_add_live_m6_wp Γ hMaxV hBt hAssign hWatch hProp)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
