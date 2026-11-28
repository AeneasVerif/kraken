/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Pure Specifications for `Kissat.Src.Reorder` (`3` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Reorder.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec

open Std.Sat
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Fixed-length `u64` array view (`n` elements) for `tarjan_mark` / `tarjan_reach` during sift. -/
abbrev Arr64 (n : Nat) := { xs : List (BitVec 64) // xs.length = n }

/-- Variant of `FullMem` viewing `tarjan_mark` and `tarjan_reach` as `max_vars`-length `u64`
arrays (`wl`, `wr`) during `full_reorder_sift_fid`. -/
@[expose] def ReorderMem (c : FullCfg) (s : FullState) (wl wr : Arr64 c.max_vars) :
    Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
    s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

/-- Boundedness of `wsort[0 ..< n)` variable indices below `cur_vars`. -/
@[expose] def WsortBounded (wsort : List (BitVec 32)) (n cv : Nat) : Prop :=
  ∀ i < n, (wsort[i]?.getD 0#32).toNat < cv

/-- Input witness packaging `ReorderMem` state for `full_reorder_sift_fid`. -/
structure SiftWitness where
  c  : FullCfg
  s  : FullState
  wl : Arr64 c.max_vars
  wr : Arr64 c.max_vars

/-- `full_reorder_sift_fid`: in-place heap-sift over `wsort[0 ..< n)` preserving `wsort[n ..)`
and `WsortBounded` under `ReorderMem`. -/
@[expose] def siftSpec : Spec [i64, i64, i64] [] :=
  FnContract.toSpec (W := SiftWitness) (W' := List (BitVec 32)) {
    pre := fun (h, _start, n, ()) w =>
      h = w.c.hdr ∧ w.s.LengthsOk w.c ∧
      WsortBounded w.s.scratch.wsort n.toNat w.s.core.cur_vars
    mem := fun _ w => ReorderMem w.c w.s w.wl w.wr
    post := fun (_, _, n, ()) w () ws' =>
      ws'.length = w.s.scratch.wsort.length ∧
      WsortBounded ws' n.toNat w.s.core.cur_vars ∧
      (∀ j, n.toNat ≤ j → ws'[j]? = w.s.scratch.wsort[j]?)
    postMem := fun _ w () ws' =>
      ReorderMem w.c { w.s with scratch := { w.s.scratch with wsort := ws' } } w.wl w.wr
  }

/-- `full_reorder_queue_m7`: rebuilds the VMTF decision queue without altering `core` or
extension scratch (`last_learned`, `extend_len`). -/
@[expose] def queueSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := PUnit) {
    pre  := fun _ _ () _ => True
    post := fun _ s () _ _ s' => CorePres s s' ∧ ScratchModifies.extPres s s'
  }

/-- `full_reorder_m6`: `FullSparseInv`-preserving variable-order refresh, exposing `cur_level`
and `fuel` equality for `full_simplify` / `full_search` plus `FullArenaPermEq`. -/
@[expose] def reorderSpec : Spec [i64, i64] [i64] :=
  FullContract.toSpec (extraArgs := [i64]) (rs := [i64]) (W := CNF Nat) {
    pre  := fun c s _ F0 => FullSparseInv c F0 s
    post := fun c s _ F0 _ s' =>
      FullSparseInv c F0 s' ∧ FullArenaPermEq s.core s'.core ∧
      s'.core.cur_level = s.core.cur_level ∧ s'.core.fuel = s.core.fuel
  }

/-- Canonical `3`-row specification table aligned 1:1 with `Src.Reorder.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_reorder_sift_fid", [i64, i64, i64], [],    siftSpec,    true⟩
  , ⟨"full_reorder_queue_m7", [i64],           [i64], queueSpec,   true⟩
  , ⟨"full_reorder_m6",       [i64, i64],      [i64], reorderSpec, true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
