/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Pure Specifications for `Kissat.Src.Walk` (`13` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Walk.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Walk Table Invariant & Scratch Prefix Preservation -/

/-- Table-length invariant established by `full_walk_cb_inv_m7` (`tbl[1080] ≤ 1080`) and
required by `full_walk_pick_m7` so `tbl[b]` stays strictly inside `scratch_buf[0 ..< 2160)`. -/
@[expose] def WalkTblExpsOk (s : FullState) : Prop :=
  (((s.scratch.scratch_buf[2160]?.getD 0#32).setWidth 64) |||
    (((s.scratch.scratch_buf[2161]?.getD 0#32).setWidth 64) <<< 32)).toNat ≤ 1080

/-- Preservation of the `u64` exponential-table prefix `scratch_buf[0 ..< 2200)`. -/
@[expose] def WalkScrPrefixPres (s s' : FullState) : Prop :=
  ∀ j < 2200, s'.scratch.scratch_buf[j]? = s.scratch.scratch_buf[j]?

/-! ## 2. Local Contract Shorthands -/

/-- Read-only `FullMem` contract (`s' = s`). -/
@[expose] def readOnly (extraArgs rs : List Ty) : FullContract extraArgs rs PUnit where
  pre  := fun _ _ _ _ => True
  post := fun _ s _ _ _ s' => s' = s

/-- Scratch-only `FullMem` contract preserving `core` and extension scratch. -/
@[expose] def scratchOnly (extraArgs rs : List Ty) : FullContract extraArgs rs PUnit where
  pre  := fun _ _ _ _ => True
  post := fun _ s _ _ _ s' => CorePres s s' ∧ ScratchModifies.extPres s s'

/-! ## 3. Canonical Per-Function Contracts (`12` distinct defs for `13` functions) -/

/-- `full_walk_cb_inv_m7`: populates `tbl[0..1082]` in `scratch_buf` and establishes
`WalkTblExpsOk` whenever `r ≠ 0`. -/
@[expose] def cbInvSpec : Spec [i64, i64, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i64, i64]) (rs := [i64]) (W := PUnit) {
    pre  := fun _ _ _ _ => True
    post := fun _ s _ _ (r, ()) s' =>
      CorePres s s' ∧ ScratchModifies.extPres s s' ∧ (r ≠ 0#64 → WalkTblExpsOk s')
  }

/-- `full_walk_effort_m7`: read-only tick-effort calculation. -/
@[expose] def effortSpec : Spec [i64, i64] [i64] :=
  (readOnly [i64] [i64]).toSpec

/-- `full_walk_init_vals_m7`: initializes `walk_vals` and `walk_best` in `scratch`. -/
@[expose] def initValsSpec : Spec [i64] [] :=
  (scratchOnly [] []).toSpec

/-- `full_walk_collect_m7`: collects unsatisfied/active clauses into `scratch_buf[2200..]`. -/
@[expose] def collectSpec : Spec [i64] [i64] :=
  (scratchOnly [] [i64]).toSpec

/-- `full_walk_build_occ_m7`: preserves `scratch_buf[0 ..< 2200)` and returns `ulen ≤ ncl`. -/
@[expose] def buildOccSpec : Spec [i64, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i64]) (rs := [i64]) (W := PUnit) {
    pre  := fun _ _ _ _ => True
    post := fun _ s (ncl, ()) _ (r, ()) s' =>
      CorePres s s' ∧ ScratchModifies.extPres s s' ∧
      WalkScrPrefixPres s s' ∧ r.toNat ≤ ncl.toNat
  }

/-- `full_walk_break_m7`: read-only break-count computation. -/
@[expose] def breakSpec : Spec [i64, i32, i64] [i32] :=
  (readOnly [i32, i64] [i32]).toSpec

/-- `full_walk_pick_m7`: requires & preserves `WalkTblExpsOk` while selecting a literal. -/
@[expose] def pickSpec : Spec [i64, i32, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i32, i64]) (rs := [i64]) (W := PUnit) {
    pre  := fun _ s _ _ => WalkTblExpsOk s
    post := fun _ s _ _ _ s' =>
      CorePres s s' ∧ ScratchModifies.extPres s s' ∧ WalkTblExpsOk s'
  }

/-- `full_walk_flip_m7`: preserves `scratch_buf[0..<2200)` and bounds `(r &&& 0xFFFFFFFF) ≤ ncl`. -/
@[expose] def flipSpec : Spec [i64, i32, i64, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i32, i64, i64]) (rs := [i64]) (W := PUnit) {
    pre  := fun _ _ _ _ => True
    post := fun _ s (_, ncl, _, ()) _ (r, ()) s' =>
      CorePres s s' ∧ ScratchModifies.extPres s s' ∧
      WalkScrPrefixPres s s' ∧ (r &&& 0xFFFFFFFF#64).toNat ≤ ncl.toNat
  }

/-- `full_walk_save_min_m7`: updates best/target phases and `best_assigned` in `scratch`. -/
@[expose] def saveMinSpec : Spec [i64, i64, .bool] [] :=
  (scratchOnly [i64, .bool] []).toSpec

/-- `full_walk_m7`: `FullSparseInv`-preserving inner WalkSAT run (binary watch roundtrip and
large-clause watch reconnection). -/
@[expose] def walkCoreSpec : Spec [i64] [] :=
  FullContract.toSpec (extraArgs := []) (rs := []) (W := CNF Nat) {
    pre  := fun c s () F0 => FullSparseInv c F0 s
    post := fun c s () F0 () s' =>
      FullSparseInv c F0 s' ∧ FullArenaPermEq s.core s'.core ∧
      s'.core.cur_vars = s.core.cur_vars ∧ s'.core.cur_level = s.core.cur_level ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ s'.core.probing = s.core.probing ∧
      ScratchModifies.extPres s s'
  }

/-- Deduplicated `FullM6HdrMem`-threaded contract shared by `full_warmup_m7` and `full_walk`. -/
@[expose] def walkSpec : Spec [i64] [] :=
  M6HdrContract.toSpec (extraArgs := []) (rs := []) (W := CNF Nat) {
    extFrame := .any
    pre  := fun c _ s () F0 => FullSparseInv c F0 s
    post := fun c _ s () F0 () _ s' =>
      FullSparseInv c F0 s' ∧ FullArenaPermEq s.core s'.core ∧
      s'.core.cur_vars = s.core.cur_vars ∧ s'.core.cur_level = s.core.cur_level ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (s.core.probing = 0#64 → s'.core.probing = 0#64) ∧
      ScratchModifies.extPres s s'
  }

/-- `full_rephase`: `FullM6HdrMem`-threaded rephase scheduling phase resets, `full_walk`,
and `full_backtrack`. -/
@[expose] def rephaseSpec : Spec [i64] [] :=
  M6HdrContract.toSpec (extraArgs := []) (rs := []) (W := CNF Nat) {
    extFrame := .any
    pre  := fun c _ s () F0 => FullSparseInv c F0 s
    post := fun c _ s () F0 () _ s' =>
      FullSparseInv c F0 s' ∧ FullArenaPermEq s.core s'.core ∧
      (s.scratch.stable ≠ 0#64 → s'.core.cur_level = 0) ∧
      s'.core.cur_level ≤ s.core.cur_level ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      ScratchModifies.extPres s s'
  }

/-! ## 4. Canonical `13`-Row Specification Table -/

/-- Canonical spec table aligned 1:1 with `Src.Walk.fns` (`13` functions). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_walk_cb_inv_m7",    [i64, i64, i64],      [i64], cbInvSpec,    true⟩
  , ⟨"full_walk_effort_m7",    [i64, i64],           [i64], effortSpec,   true⟩
  , ⟨"full_walk_init_vals_m7", [i64],                [],    initValsSpec, true⟩
  , ⟨"full_walk_collect_m7",   [i64],                [i64], collectSpec,  true⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64],           [i64], buildOccSpec, true⟩
  , ⟨"full_walk_break_m7",     [i64, i32, i64],      [i32], breakSpec,    true⟩
  , ⟨"full_walk_pick_m7",      [i64, i32, i64],      [i64], pickSpec,     true⟩
  , ⟨"full_walk_flip_m7",      [i64, i32, i64, i64], [i64], flipSpec,     true⟩
  , ⟨"full_walk_save_min_m7",  [i64, i64, .bool],    [],    saveMinSpec,  true⟩
  , ⟨"full_walk_m7",           [i64],                [],    walkCoreSpec, true⟩
  , ⟨"full_warmup_m7",         [i64],                [],    walkSpec,     true⟩
  , ⟨"full_walk",              [i64],                [],    walkSpec,     true⟩
  , ⟨"full_rephase",           [i64],                [],    rephaseSpec,  true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
