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
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
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

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and establishes
`cert : SegCert deps Src.Walk.fns Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Walk
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

/-- Canonical upstream specs imported by `Src.Walk` (`14` externs). -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Decide.Spec.specs ++
    Dense.Spec.specs ++ Float64.Spec.specs ++ Forward.Spec.specs ++
    PropSearch.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Walk.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem cbInvSpec_xfree : Spec.cbInvSpec.XFree := by
  unfold Spec.cbInvSpec; exact FullContract.toSpec_xfree _

private theorem effortSpec_xfree : Spec.effortSpec.XFree := by
  unfold Spec.effortSpec readOnly; exact FullContract.toSpec_xfree _

private theorem initValsSpec_xfree : Spec.initValsSpec.XFree := by
  unfold Spec.initValsSpec scratchOnly; exact FullContract.toSpec_xfree _

private theorem collectSpec_xfree : Spec.collectSpec.XFree := by
  unfold Spec.collectSpec scratchOnly; exact FullContract.toSpec_xfree _

private theorem buildOccSpec_xfree : Spec.buildOccSpec.XFree := by
  unfold Spec.buildOccSpec; exact FullContract.toSpec_xfree _

private theorem breakSpec_xfree : Spec.breakSpec.XFree := by
  unfold Spec.breakSpec readOnly; exact FullContract.toSpec_xfree _

private theorem pickSpec_xfree : Spec.pickSpec.XFree := by
  unfold Spec.pickSpec; exact FullContract.toSpec_xfree _

private theorem flipSpec_xfree : Spec.flipSpec.XFree := by
  unfold Spec.flipSpec; exact FullContract.toSpec_xfree _

private theorem saveMinSpec_xfree : Spec.saveMinSpec.XFree := by
  unfold Spec.saveMinSpec scratchOnly; exact FullContract.toSpec_xfree _

private theorem walkCoreSpec_xfree : Spec.walkCoreSpec.XFree := by
  unfold Spec.walkCoreSpec; exact FullContract.toSpec_xfree _

private theorem walkSpec_xfree : Spec.walkSpec.XFree := by
  unfold Spec.walkSpec; exact M6HdrContract.toSpec_xfree _

/-- Canonical segment certificate for `Kissat.Src.Walk` (`13` functions). -/
theorem cert : SegCert deps Src.Walk.fns Spec.specs := by
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
  have hAdd := SpecTable.has_at hFl 2 rfl f64uPure2Spec_xfree
  have hSub := SpecTable.has_at hFl 3 rfl f64uPure2Spec_xfree
  have hMul := SpecTable.has_at hFl 4 rfl f64uPure2Spec_xfree
  have hDiv := SpecTable.has_at hFl 5 rfl f64uPure2Spec_xfree
  have hFrom := SpecTable.has_at hFl 7 rfl f64uPure1Spec_xfree
  have hTo := SpecTable.has_at hFl 8 rfl f64uPure1Spec_xfree
  have hNlog := SpecTable.has_at hFl 11 rfl f64uPure2Spec_xfree
  have hRoundtrip := Forward.Spec.has_full_dense_bin_roundtrip_fid hFwd
  have hPropBey := PropSearch.Spec.has_full_propagate_beyond_m7 hProp
  have hCbInv := SpecTable.has_at hSat 0 rfl cbInvSpec_xfree
  have hEffort := SpecTable.has_at hSat 1 rfl effortSpec_xfree
  have hInitVals := SpecTable.has_at hSat 2 rfl initValsSpec_xfree
  have hCollect := SpecTable.has_at hSat 3 rfl collectSpec_xfree
  have hBuildOcc := SpecTable.has_at hSat 4 rfl buildOccSpec_xfree
  have hBreak := SpecTable.has_at hSat 5 rfl breakSpec_xfree
  have hPick := SpecTable.has_at hSat 6 rfl pickSpec_xfree
  have hFlip := SpecTable.has_at hSat 7 rfl flipSpec_xfree
  have hSaveMin := SpecTable.has_at hSat 8 rfl saveMinSpec_xfree
  have hWalkM7 := SpecTable.has_at hSat 9 rfl walkCoreSpec_xfree
  have hWarmup := SpecTable.has_at hSat 10 rfl walkSpec_xfree
  have hWalk := SpecTable.has_at hSat 11 rfl walkSpec_xfree
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
