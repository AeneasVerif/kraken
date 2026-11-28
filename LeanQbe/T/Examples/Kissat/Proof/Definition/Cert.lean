/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Basic
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Prop
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Analyze
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Solve
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Core
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7DefK6
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Gates
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidProp
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidAnalyze
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidSolve
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidCore
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidCert
import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidGates

/-!
# Canonical Segment Certificate for `Kissat.Src.Definition` (`Proof.Definition.Cert`)

Proves `cert : SegCert Spec.deps Src.Definition.fns Spec.specs` (`26` C0 functions, `0` externs)
against `Src.Definition.fns` via `Spec.has_*` and `SpecEntry.Impl.of`.
Zero legacy `Full*` imports; zero `@[expose]` on theorems/sections; `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Definition`
    (`26` fns, `0` externs). -/
theorem cert : SegCert Spec.deps Src.Definition.fns Spec.specs := by
  intro Γ hdeps hrows
  have hBt : Γ.Sat Proof.Backtrack.Spec.specs := hdeps.left.left
  have hGates : Γ.Sat Proof.Gates.specs := hdeps.left.right
  have hKit : Γ.Sat Proof.Kitten.Spec.specs := hdeps.right
  have gate := fun (k : Nat) (hk : k < Proof.Gates.specs.length)
      (hx : Proof.Gates.specs[k].spec.XFree) =>
    Env.Sat.has hGates (List.getElem_mem hk) hx
  have hEqM7 := gate 0 (by decide) Proof.Gates.fullBveFindEquivM7Spec_xfree
  have hAndM7 := gate 1 (by decide) Proof.Gates.fullBveFindAndM7Spec_xfree
  have hIteM7 := gate 5 (by decide) Proof.Gates.fullBveFindIteM7Spec_xfree
  have hXorM7 := gate 7 (by decide) Proof.Gates.fullBveFindXorM7Spec_xfree
  have hEqM8 := gate 8 (by decide) Proof.Gates.m8BveFindEquivSpec_xfree
  have hAndM8 := gate 9 (by decide) Proof.Gates.m8BveFindAndSpec_xfree
  have hIteM8 := gate 12 (by decide) Proof.Gates.m8BveFindIteSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_k6_watch_m7_wp Γ)
    , SpecEntry.Impl.of (full_k6_assign_m7_wp Γ)
    , SpecEntry.Impl.of (full_k6_mtf_m7_wp Γ)
    , SpecEntry.Impl.of (full_k6_backtrack_m7_wp Γ)
    , SpecEntry.Impl.of (full_k6_prop_m7_wp Γ hrows)
    , SpecEntry.Impl.of (full_k6_ana_cl_m7_wp Γ)
    , SpecEntry.Impl.of (full_k6_analyze_m7_wp Γ hrows)
    , SpecEntry.Impl.of (full_k6_solve_m7_wp Γ hrows)
    , SpecEntry.Impl.of (full_k6_core_m7_wp Γ)
    , SpecEntry.Impl.of
        (full_bve_def_k6_m7_wp Γ
          (has_full_k6_watch_m7 hrows) (has_full_k6_solve_m7 hrows) (has_full_k6_core_m7 hrows))
    , SpecEntry.Impl.of
        (full_bve_gates_m7_wp Γ hEqM7 hAndM7 hIteM7 hXorM7 (has_full_bve_def_k6_m7 hrows))
    , SpecEntry.Impl.of (full_bve_k6_mv_fid_wp Γ)
    , SpecEntry.Impl.of (full_fid_k6_add_ticks_wp Γ)
    , SpecEntry.Impl.of (full_k6_watch_fid_wp Γ)
    , SpecEntry.Impl.of (full_k6_assign_fid_wp Γ)
    , SpecEntry.Impl.of (full_k6_mtf_fid_wp Γ)
    , SpecEntry.Impl.of (full_k6_backtrack_fid_wp Γ)
    , SpecEntry.Impl.of
        (full_k6_prop_fid_wp Γ (has_full_fid_k6_add_ticks hrows) (has_full_k6_assign_fid hrows))
    , SpecEntry.Impl.of (full_k6_ana_cl_fid_wp Γ)
    , SpecEntry.Impl.of
        (full_k6_analyze_fid_wp Γ
          (has_full_k6_ana_cl_fid hrows) (has_full_k6_backtrack_fid hrows)
          (has_full_k6_mtf_fid hrows) (has_full_k6_watch_fid hrows) (has_full_k6_assign_fid hrows))
    , SpecEntry.Impl.of
        (full_k6_solve_fid_wp Γ
          (has_full_k6_backtrack_fid hrows) (has_full_k6_assign_fid hrows)
          (has_full_k6_prop_fid hrows) (has_full_k6_analyze_fid hrows))
    , SpecEntry.Impl.of (full_k6_core_fid_wp Γ)
    , SpecEntry.Impl.of
        (full_k6_extract_and_solve_fid_wp Γ
          (has_full_bve_k6_mv_fid hrows) (has_full_k6_watch_fid hrows)
          (has_full_k6_solve_fid hrows) (has_full_k6_core_fid hrows))
    , SpecEntry.Impl.of
        (full_bve_certify_unit_fid_wp Γ
          (Proof.Kitten.Spec.has_full_m6_max_v hKit)
          (Proof.Kitten.Spec.has_full_k6_init hKit)
          (Proof.Kitten.Spec.has_full_k6_add_clause hKit)
          (Proof.Kitten.Spec.has_full_k6_solve hKit)
          (Proof.Backtrack.Spec.has_full_assign_lvl hBt))
    , SpecEntry.Impl.of
        (full_bve_def_k6_fid_wp Γ
          (has_full_bve_k6_mv_fid hrows)
          (has_full_k6_extract_and_solve_fid hrows)
          (has_full_bve_certify_unit_fid hrows))
    , SpecEntry.Impl.of
        (full_bve_gates_fid_wp Γ hEqM8 hAndM8 hIteM8 (has_full_bve_def_k6_fid hrows))
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Definition
