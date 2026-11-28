/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Dense
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header

/-!
# Canonical Specification Table for `Kissat.Src.Dense` (`Proof.Dense.Spec`)

Canonical flat-`Env` (`SegCert`) UNSAT-sound `Spec` definitions, `deps`, `Spec.XFree`
proofs, `specs` table matching `Src.Dense.fns` `1:1` (`noExit := true`, `10` rows),
table invariants, and `Env.Sat.has` projections (`0` legacy imports, `0` `@[expose]` on
theorems, lemmas, or sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Function `Spec` Contracts (`10` fns in `Src.Dense.fns`) -/

/-- `full_dense_occ_cnt_fid`: read-only watch occurrence counter capped at `cap + 1`. -/
@[expose] def fullDenseOccCntSpec : Spec [i64, i32, i64] [i64] := fun (h, lit, _cap, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

/-- `full_enter_dense_ex_fid`: parameterized `enter_dense(h, connect_large)` over
`FullM6HdrMem` (`full_flush_trail` / `full_propagate`). -/
@[expose] def fullEnterDenseExM6Spec : Spec [i64, .bool] [.bool] :=
  fun (h, connect_large, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      (s.core.dense_mode ≠ 0#64 → s.core.oom = 0#64) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ok : Bool) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        FullM6HdrCfgOk c → M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (ok = true → FullDenseInv c F0 s' ∧
          (connect_large = false → s'.core.cur_level = 0 ∧ s'.core.dense_mode ≠ 0#64)) →
        (ok = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_enter_dense`: `FullM6HdrMem`-threaded `full_enter_dense_ex_fid(h, true)`. -/
@[expose] def fullEnterDenseM6Spec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (s.core.dense_mode ≠ 0#64 → s.core.oom = 0#64) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrCfgOk c → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_rebuild_watches_nosort_fid` & `full_rebuild_watches`: `FullM6HdrMem`-threaded
rebuild from dense occurrence lists back to sparse 2WL watches (`full_propagate`). -/
@[expose] def fullRebuildWatchesM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullDenseInv c F0 s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- `full_m6_dense_prop_lit`: dense unit propagation for a single assigned literal. -/
@[expose] def fullDensePropLitSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_m6_dense_prop`: dense trail propagation preserving `glue_used` and sweep scratch. -/
@[expose] def fullDensePropSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = true ↔ s'.core.inconsistent = 0#64) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_dense_prop_unit_m7`: dense level-0 unit propagation for a single literal,
marking satisfied large clauses `PH_GARB` while preserving BVE/forward scratch buffers. -/
@[expose] def fullDensePropUnitSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_dense_flush_units_m7`: flushes all pending level-0 trail units in dense mode. -/
@[expose] def fullDenseFlushUnitsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_watch_large_clauses_fid`: ranks large arena clauses and attaches 2WL watches. -/
@[expose] def fullWatchLargeClausesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. Upstream Dependencies, `Spec.XFree` Proofs & Canonical `SpecEntry` Table -/

/-- Upstream capability table imported by `Src.Dense`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Clause.Spec.specs ++
  Collect.Spec.specs ++ PropSearch.Spec.specs ++ Watch.Spec.specs

theorem fullDenseOccCntSpec_xfree : Spec.XFree fullDenseOccCntSpec := by xfree

theorem fullEnterDenseExM6Spec_xfree : Spec.XFree fullEnterDenseExM6Spec := by xfree

theorem fullEnterDenseM6Spec_xfree : Spec.XFree fullEnterDenseM6Spec := by xfree

theorem fullRebuildWatchesM6Spec_xfree : Spec.XFree fullRebuildWatchesM6Spec := by xfree

theorem fullDensePropLitSpec_xfree : Spec.XFree fullDensePropLitSpec := by xfree

theorem fullDensePropSpec_xfree : Spec.XFree fullDensePropSpec := by xfree

theorem fullDensePropUnitSpec_xfree : Spec.XFree fullDensePropUnitSpec := by xfree

theorem fullDenseFlushUnitsSpec_xfree : Spec.XFree fullDenseFlushUnitsSpec := by xfree

theorem fullWatchLargeClausesSpec_xfree : Spec.XFree fullWatchLargeClausesSpec := by xfree

/-- Canonical `SpecEntry` table matching `Src.Dense.fns` `1:1` (`10` rows). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_dense_occ_cnt_fid", [i64, i32, i64], [i64], fullDenseOccCntSpec, true⟩
  , ⟨"full_enter_dense_ex_fid", [i64, .bool], [.bool], fullEnterDenseExM6Spec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseM6Spec, true⟩
  , ⟨"full_rebuild_watches_nosort_fid", [i64], [i64], fullRebuildWatchesM6Spec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesM6Spec, true⟩
  , ⟨"full_m6_dense_prop_lit", [i64, i32], [.bool], fullDensePropLitSpec, true⟩
  , ⟨"full_m6_dense_prop", [i64], [.bool], fullDensePropSpec, true⟩
  , ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], fullDensePropUnitSpec, true⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsSpec, true⟩
  , ⟨"full_watch_large_clauses_fid", [i64], [], fullWatchLargeClausesSpec, true⟩ ]

theorem specs_sigs :
    specs.map SpecEntry.sig = Src.Dense.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullDenseOccCntSpec_xfree
  · exact fullEnterDenseExM6Spec_xfree
  · exact fullEnterDenseM6Spec_xfree
  · exact fullRebuildWatchesM6Spec_xfree
  · exact fullRebuildWatchesM6Spec_xfree
  · exact fullDensePropLitSpec_xfree
  · exact fullDensePropSpec_xfree
  · exact fullDensePropUnitSpec_xfree
  · exact fullDenseFlushUnitsSpec_xfree
  · exact fullWatchLargeClausesSpec_xfree

/-! ## 3. `Env.Sat.has` Projections (`10` fns) -/

theorem has_full_dense_occ_cnt_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_dense_occ_cnt_fid" fullDenseOccCntSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullDenseOccCntSpec_xfree

theorem has_full_enter_dense_ex_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_enter_dense_ex_fid" fullEnterDenseExM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullEnterDenseExM6Spec_xfree

theorem has_full_enter_dense {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_enter_dense" fullEnterDenseM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullEnterDenseM6Spec_xfree

theorem has_full_rebuild_watches_nosort_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rebuild_watches_nosort_fid" fullRebuildWatchesM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullRebuildWatchesM6Spec_xfree

theorem has_full_rebuild_watches {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rebuild_watches" fullRebuildWatchesM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullRebuildWatchesM6Spec_xfree

theorem has_full_m6_dense_prop_lit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_dense_prop_lit" fullDensePropLitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fullDensePropLitSpec_xfree

theorem has_full_m6_dense_prop {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_dense_prop" fullDensePropSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide))
    fullDensePropSpec_xfree

theorem has_full_dense_prop_unit_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_dense_prop_unit_m7" fullDensePropUnitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide))
    fullDensePropUnitSpec_xfree

theorem has_full_dense_flush_units_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_dense_flush_units_m7" fullDenseFlushUnitsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide))
    fullDenseFlushUnitsSpec_xfree

theorem has_full_watch_large_clauses_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_watch_large_clauses_fid" fullWatchLargeClausesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide))
    fullWatchLargeClausesSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
