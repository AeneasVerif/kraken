/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Walk.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Walk.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Walk.Wp2a
import LeanQbe.T.Examples.Kissat.Proof.Walk.Wp2b
import LeanQbe.T.Examples.Kissat.Proof.Walk.Wp3

/-!
# Canonical Segment Certificate for `Kissat.Src.Walk` (`Proof.Walk.Cert`)

Establishes `cert : SegCert Spec.deps Src.Walk.fns Spec.specs` using `CanonicalEnv`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Walk
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

/-- Canonical segment certificate for `Kissat.Src.Walk` (`13` functions). -/
theorem cert : SegCert Spec.deps Src.Walk.fns Spec.specs := by
  intro Γ hdeps hSat
  have hAr : Γ.Sat Arena.Spec.specs := hdeps.left.left.left.left.left.left
  have hBk : Γ.Sat Backtrack.Spec.specs := hdeps.left.left.left.left.left.right
  have hDec : Γ.Sat Decide.Spec.specs := hdeps.left.left.left.left.right
  have hDen : Γ.Sat Dense.Spec.specs := hdeps.left.left.left.right
  have hFl : Γ.Sat Float64.Spec.specs := hdeps.left.left.right
  have hFwd : Γ.Sat Forward.Spec.specs := hdeps.left.right
  have hProp : Γ.Sat PropSearch.Spec.specs := hdeps.right
  have hArenaNext := Arena.Spec.has_full_arena_next hAr
  have hAssign := Backtrack.Spec.has_full_assign hBk
  have hBacktrack := Backtrack.Spec.has_full_backtrack hBk
  have hNextDec := Decide.Spec.has_full_next_dec_var hDec
  have hWatchLarge := Dense.Spec.has_full_watch_large_clauses_fid hDen
  have hAdd : Γ.Has "f64u_add" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 2) (by decide))
      f64uPure2Spec_xfree
  have hSub : Γ.Has "f64u_sub" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 3) (by decide))
      f64uPure2Spec_xfree
  have hMul : Γ.Has "f64u_mul" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 4) (by decide))
      f64uPure2Spec_xfree
  have hDiv : Γ.Has "f64u_div" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 5) (by decide))
      f64uPure2Spec_xfree
  have hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 7) (by decide))
      f64uPure1Spec_xfree
  have hTo : Γ.Has "f64u_to_u64" f64uPure1Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 8) (by decide))
      f64uPure1Spec_xfree
  have hNlog : Γ.Has "f64u_nlogpown" f64uPure2Spec :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 11) (by decide))
      f64uPure2Spec_xfree
  have hRoundtrip := Forward.Spec.has_full_dense_bin_roundtrip_fid hFwd
  have hPropBey := PropSearch.Spec.has_full_propagate_beyond_m7 hProp
  have hCbInv := Spec.has_full_walk_cb_inv_m7 hSat
  have hEffort := Spec.has_full_walk_effort_m7 hSat
  have hInitVals := Spec.has_full_walk_init_vals_m7 hSat
  have hCollect := Spec.has_full_walk_collect_m7 hSat
  have hBuildOcc := Spec.has_full_walk_build_occ_m7 hSat
  have hBreak := Spec.has_full_walk_break_m7 hSat
  have hPick := Spec.has_full_walk_pick_m7 hSat
  have hFlip := Spec.has_full_walk_flip_m7 hSat
  have hSaveMin := Spec.has_full_walk_save_min_m7 hSat
  have hWalkM7 := Spec.has_full_walk_m7 hSat
  have hWarmup := Spec.has_full_warmup_m7 hSat
  have hWalk := Spec.has_full_walk hSat
  exact
    ⟨ SpecEntry.Impl.of (full_walk_cb_inv_m7_wp Γ hAdd hSub hMul hDiv hFrom)
    , SpecEntry.Impl.of (full_walk_effort_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_init_vals_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_collect_m7_wp Γ hArenaNext)
    , SpecEntry.Impl.of (full_walk_build_occ_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_break_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_pick_m7_wp Γ hAdd hMul hFrom hBreak)
    , SpecEntry.Impl.of (full_walk_flip_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_save_min_m7_wp Γ)
    , SpecEntry.Impl.of (full_walk_m7_wp Γ hRoundtrip hWatchLarge hInitVals hCollect hCbInv
        hBuildOcc hEffort hPick hFlip hSaveMin)
    , SpecEntry.Impl.of (full_warmup_m7_wp Γ hNextDec hAssign hPropBey hBacktrack)
    , SpecEntry.Impl.of (full_walk_wp Γ hWarmup hWalkM7)
    , SpecEntry.Impl.of (full_rephase_wp Γ hBacktrack hWalk hNlog hTo)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Walk
