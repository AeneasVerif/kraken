/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Kissat Canonical `Spec` Table for `Src.Reorder` (`Proof.Reorder.Spec`)

Canonical `Env` contracts and `CanonicalEnv` `SpecEntry` list (`specs`) for the `3` functions in
`Src.Reorder.fns` (`full_reorder_sift_fid`, `full_reorder_queue_m7`, `full_reorder_m6`), depending
strictly on `Float64.Spec.specs ++ Arena.Spec.specs ++ Bump.Spec.specs ++ Heap.Spec.specs` with
`0` legacy imports and `0` SAT model proofs.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. `ReorderMem`, `WsortBounded` & Canonical Contracts for `Src.Reorder` -/

/-- Fixed-length `u64` array view (`n` elements). -/
abbrev Arr64 (n : Nat) := { xs : List (BitVec 64) // xs.length = n }

/-- Variant of `FullMem` viewing `tarjan_mark` and `tarjan_reach` as `max_vars`-length `u64`
arrays (`wl`, `wr`). -/
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

/-- Boundedness of `wsort[0 ..< n)` indices below `cur_vars`. -/
@[expose] def WsortBounded (wsort : List (BitVec 32)) (n cv : Nat) : Prop :=
  ∀ i < n, (wsort[i]?.getD 0#32).toNat < cv

/-- Canonical sift helper specification for `full_reorder_sift_fid` over `ReorderMem`. -/
@[expose] def fullReorderSiftFidSpec : Spec [i64, i64, i64] [] :=
  fun (h, _start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (wl wr : Arr64 c.max_vars) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      WsortBounded s.scratch.wsort n.toNat s.core.cur_vars ∧
      (ReorderMem c s wl wr ⋆ R) m ∧
      ∀ (ws' : List (BitVec 32)) (m' : Mem 64),
        ws'.length = s.scratch.wsort.length →
        WsortBounded ws' n.toNat s.core.cur_vars →
        (∀ j, n.toNat ≤ j → ws'[j]? = s.scratch.wsort[j]?) →
        let s' := { s with scratch := { s.scratch with wsort := ws' } }
        (ReorderMem c s' wl wr ⋆ R) m' → Q () m'

theorem fullReorderSiftFidSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullReorderSiftFidSpec xs m Q X) :
    fullReorderSiftFidSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem fullReorderSiftFidSpec_xfree : fullReorderSiftFidSpec.XFree := by xfree

/-- Canonical `fullSafetySlice` contract for `full_reorder_queue_m7`. -/
@[expose] def fullReorderQueueSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

theorem fullReorderQueueSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fullReorderQueueSpec xs m Q X) :
    fullReorderQueueSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullReorderQueueSpec_xfree : fullReorderQueueSpec.XFree := by xfree

/-- Canonical `FullSparseInv`-preserving contract for `full_reorder_m6`, exposing
`cur_level` and `fuel` preservation for `full_simplify` / `full_search`. -/
@[expose] def fullReorderM6Spec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_level = s.core.cur_level → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullReorderM6Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fullReorderM6Spec xs m Q X) :
    fullReorderM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullReorderM6Spec_xfree : fullReorderM6Spec.XFree := by xfree

/-! ## 2. Canonical `SpecEntry` Table & `Env.Sat` Projections -/

/-- External specifications required by `Kissat.Src.Reorder`. -/
@[expose] def deps : List SpecEntry :=
  Float64.Spec.specs ++ Arena.Spec.specs ++ Bump.Spec.specs ++ Heap.Spec.specs

/-- Canonical `SpecEntry` list matching `Src.Reorder.fns` order 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_reorder_sift_fid", [i64, i64, i64], [], fullReorderSiftFidSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], fullReorderQueueSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], fullReorderM6Spec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Reorder.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact fullReorderSiftFidSpec_xfree
  · exact fullReorderQueueSpec_xfree
  · exact fullReorderM6Spec_xfree

theorem has_full_reorder_sift_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_reorder_sift_fid" fullReorderSiftFidSpec :=
  Env.Sat.has h List.mem_cons_self fullReorderSiftFidSpec_xfree

theorem has_full_reorder_queue_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_reorder_queue_m7" fullReorderQueueSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullReorderQueueSpec_xfree

theorem has_full_reorder_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_reorder_m6" fullReorderM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullReorderM6Spec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
