/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof1
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof2
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof3
public import LeanQbe.T.Examples.Kissat.FullM7Splice
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `FullM7Fidelity` Core Module Assembly & `FullM7` Splice (`FullM7FidelityCoreProof`)

M1-clean UNSAT-only assembly module (`public section`, `0` `@[expose]`, `0` `@[local]`, `0`
`import all`, `XPost := False`, `0` SAT proofs):
1. Standalone `32`-row `fidCoreSpecTable` (`9` functions + `23` externs, all `noExit = true`),
   `fidCoreEnv`, `fidCore_tableImpl`, and `fidCore_moduleOk`.
2. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) on `fidCoreEnv` (`nvFidCore_reorder`,
   `nvFidCore_reorder_queue`, `nvFidCore_walk`).
3. Canonical `fidCorePatchFns` / `fidCorePatchBefores` / `fidCorePatchRows` /
   `fidCorePatchRowBefores` exports (`FullM7Splice.patchFns`/`patchRows`-ready) plus local
   transparent `fidPatchFns`/`fidPatchRows` lift onto `FullM7.m7Module` (`fidCorePatchedModule`
   with `412` functions), unconditional `fidCorePatched_acyclic`, `fidCorePatched_moduleOk`,
   `fidCorePatched_solve_bytes_sound`, and concrete `Mem 64` `fidCorePatched_unsat_nv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open Kraken.Bedrock2.Test

private theorem fidRowMem {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ tbl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → Env.ofTable tbl nm as bs xs m Q X :=
  fun xs m Q X hs => Env.ofTable_of_mem hmem hnd (by
    dsimp only [SpecEntry.eff]; simp only [ite_true]; exact hno xs m Q X hs)

private theorem envOfTable_elim : ∀ {tbl : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost},
    Env.ofTable tbl f as bs xs m Q X →
    ∃ e ∈ tbl, ∃ (_ : e.name = f) (has : e.as = as) (hrs : e.rs = bs),
      e.cast has hrs xs m Q X
  | [], _, _, _, _, _, _, _, h => False.elim h
  | e :: es, _, _, _, _, _, _, _, h => by
    rcases h with ⟨⟨rfl, rfl, rfl⟩, hs⟩ | ⟨_, hs⟩
    · exact ⟨e, List.mem_cons_self, rfl, rfl, rfl, hs⟩
    · obtain ⟨e', he', hnm, has, hrs, hs'⟩ := envOfTable_elim hs
      exact ⟨e', List.mem_cons_of_mem e he', hnm, has, hrs, hs'⟩

/-! ## 1. Standalone `32`-Row `fidCoreSpecTable`, `fidCoreEnv`, & `fidCore_moduleOk` -/

section StandaloneModuleOk

private def fidCoreDefRows : List SpecEntry :=
  [ ⟨"full_min_shrink_fid", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩
  , ⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool], fidBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands_fid", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩
  , ⟨"full_bva_filter_row_fid", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩
  , ⟨"full_reorder_sift_fid", [i64, i64, i64], [], fidReorderSiftSpec, true⟩
  , ⟨"full_reorder_queue_fid", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_reorder_fid", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_elim_bve_fid", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_walk_fid", [i64], [], Full.fullWalkSpec, true⟩ ]

private def fidCoreExtRows : List SpecEntry :=
  [ ⟨"full_sort_tmp", [i64], [], FullM7AnalyzeSort.m7SortTmpSpec, true⟩
  , ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.m6MinLitDfsSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool],
      FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
      FullM6BveFwd.fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m7", [i64, i64], [i32], FullM6BveFwd.fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64],
      FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.m7InitValsSpec, true⟩
  , ⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.m7CollectSpec, true⟩
  , ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], FullM7Walk.m7CbInvSpec, true⟩
  , ⟨"full_walk_init_table_m7", [i64, i64], [], FullM7Walk.m7InitTableSpec, true⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], FullM7Walk.m7BuildOccSpec, true⟩
  , ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩
  , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], FullM7Walk.m7PickSpec, true⟩
  , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], FullM7Walk.m7FlipSpec, true⟩
  , ⟨"full_walk_save_min_m7", [i64, i64, .bool], [], FullM7Walk.m7SaveMinSpec, true⟩
  , ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ ]

/-- Closed `32`-row specification table for `fidCoreModule` (`9` defined functions + `23`
external callees, all `noExit = true`). -/
def fidCoreSpecTable : List SpecEntry := fidCoreDefRows ++ fidCoreExtRows

theorem fidCoreSpecTable_length : fidCoreSpecTable.length = 32 := by rfl

theorem fidCoreSpecTable_sigs :
    fidCoreSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidCoreModule.fns.map Fn.sig ++ fidCoreModule.externs.map Extern.sig := by rfl

theorem fidCoreSpecTable_nodup : (fidCoreSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidCoreSpecTable.map SpecEntry.name =
      fidCoreModule.fns.map Fn.name ++ fidCoreModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem fidCoreSpecTable_noExit : ∀ e ∈ fidCoreSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : fidCoreSpecTable.all (·.noExit) = true) e he

/-- Closed environment induced by `fidCoreSpecTable`. -/
def fidCoreEnv : Env := Env.ofTable fidCoreSpecTable

theorem fidCoreEnv_noExit : ∀ f as bs xs m Q X X',
    fidCoreEnv f as bs xs m Q X → fidCoreEnv f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ h => env_ofTable_noExit_all (by rfl) _ _ _ _ _ _ _ h

private theorem fidCoreEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : fidCoreSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : fidCoreEnv e.name e.as e.rs xs m Q X :=
  env_ofTable_row_at hidx fidCoreSpecTable_nodup hs

private theorem fidRowImpl {Γ : Env} {fn : Fn} {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hn : nm = fn.name) (ha : as = fn.as) (hr : bs = fn.rs)
    (hwp : ∀ xs m Q X, sp xs m Q X → Func.wp Γ (ha ▸ hr ▸ fn.body) xs m Q X) :
    SpecEntry.Impl Γ fn ⟨nm, as, bs, sp, true⟩ := by
  subst hn ha hr
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs => ?_⟩
  dsimp only [SpecEntry.cast, SpecEntry.eff] at hs
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m (hwp xs m Q _ hs)

/-- Closed `TableImpl` certifying all `9` functions of `fidCoreModule` against
`fidCoreSpecTable`. -/
theorem fidCore_tableImpl : TableImpl fidCoreEnv fidCoreFns fidCoreSpecTable := by
  let erX (i : Nat) (n : Sym) (as bs : List Ty) (sp : Spec as bs)
      (h : fidCoreSpecTable[i]? = some (⟨n, as, bs, sp, true⟩ : SpecEntry))
      (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
      ∀ xs m Q X, sp xs m Q X → fidCoreEnv n as bs xs m Q X :=
    fidRowMem fidCoreSpecTable_nodup n as bs sp (List.mem_of_getElem? h) hno
  let erSt := erX 9 "full_sort_tmp" [i64] [] _ rfl
    (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h)
  let erSb := erX 11 "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] _ rfl
    (fun _ _ _ _ h => FullM6MinShrink.m6ShrinkBlkBoolSpec_monoX h)
  let erDfs := erX 12 "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] _ rfl
    (fun _ _ _ _ h => FullM6MinShrink.m6MinLitDfsSpec_monoX h)
  refine tableImpl_cons
      (fidRowImpl rfl rfl rfl (full_min_shrink_fid_wp fidCoreEnv erSt
        (erX 10 "full_min_mark" [i64, i32, i8] [] _ rfl (fun _ _ _ _ h => h)) erDfs erSb))
    (tableImpl_cons
      (fidRowImpl rfl rfl rfl (full_bva_match_large_fid_wp fidCoreEnv))
      (tableImpl_cons
        (fidRowImpl rfl rfl rfl (full_bva_scan_cands_fid_wp fidCoreEnv))
        (tableImpl_cons
          (fidRowImpl rfl rfl rfl (full_bva_filter_row_fid_wp fidCoreEnv
            (erX 1 "full_bva_match_large_fid" [i64, i32, i32, i32] [.bool] _ rfl
              (fun _ _ _ _ h => fidBvaMatchLargeSpec_monoX h))))
          (tableImpl_cons
            (fidRowImpl rfl rfl rfl (full_reorder_sift_fid_wp fidCoreEnv))
            (tableImpl_cons
              (fidRowImpl rfl rfl rfl (full_reorder_queue_fid_wp fidCoreEnv
                (erX 13 "full_arena_next" [i64, i32] [i32] _ rfl (fun _ _ _ _ h => h))
                (erX 14 "full_rescale" [i64] [] _ rfl (fun _ _ _ _ h => h))
                (erX 15 "full_heap_up" [i64, i32] [] _ rfl (fun _ _ _ _ h => h))
                (erX 4 "full_reorder_sift_fid" [i64, i64, i64] [] _ rfl
                  (fun _ _ _ _ h => fidReorderSiftSpec_monoX h))))
              (tableImpl_cons
                (fidRowImpl rfl rfl rfl (full_reorder_fid_wp fidCoreEnv
                  (erX 16 "full_reorder_queue_m7" [i64] [i64] _ rfl
                    (fun _ _ _ _ h => h))))
                (tableImpl_cons
                  (fidRowImpl rfl rfl rfl (full_elim_bve_fid_wp fidCoreEnv
                    (erX 17 "full_dense_flush_units_m7" [i64] [.bool] _ rfl
                      FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
                    (erX 18 "full_bve_heap_push_m7" [i64, i64, i32] [i64] _ rfl
                      FullM6BveFwd.fullBveHeapPushM6Spec_noExit)
                    (erX 19 "full_bve_heap_pop_m7" [i64, i64] [i32] _ rfl
                      FullM6BveFwd.fullBveHeapPopM6Spec_noExit)
                    (erX 20 "full_bve_collect_nbrs_m7" [i64, i32] [i64] _ rfl
                      (fun _ _ _ _ h => h))
                    (erX 21 "full_bve_var_m7" [i64, i32] [i64] _ rfl
                      (fun _ _ _ _ h => h))))
                  (tableImpl_cons
                    (fidRowImpl rfl rfl rfl (full_walk_fid_wp fidCoreEnv
                      (erX 22 "full_walk_init_vals_m7" [i64] [] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7InitValsSpec_noExit h))
                      (erX 23 "full_walk_collect_m7" [i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7CollectSpec_noExit h))
                      (erX 24 "full_walk_cb_inv_m7" [i64, i64, i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7CbInvSpec_noExit h))
                      (erX 25 "full_walk_init_table_m7" [i64, i64] [] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7InitTableSpec_noExit h))
                      (erX 26 "full_walk_build_occ_m7" [i64, i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7BuildOccSpec_noExit h))
                      (erX 27 "full_walk_effort_m7" [i64, i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7EffortSpec_noExit h))
                      (erX 28 "full_walk_pick_m7" [i64, i32, i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7PickSpec_noExit h))
                      (erX 29 "full_walk_flip_m7" [i64, i32, i64, i64] [i64] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7FlipSpec_noExit h))
                      (erX 30 "full_walk_save_min_m7" [i64, i64, .bool] [] _ rfl
                        (fun _ _ _ _ h => FullM7Walk.m7SaveMinSpec_noExit h))
                      (erX 31 "full_rng_next" [i64] [i64] _ rfl
                        (fun _ _ _ _ h => h))))
                    (tableImpl_nil fidCoreEnv fidCoreExtRows)))))))))

/-- Closed `ModuleOk` for `fidCoreModule` (`9` defined functions + `23` externs). -/
theorem fidCore_moduleOk : ModuleOk fidCoreEnv fidCoreModule :=
  Env.ofTable_moduleOk fidCore_acyclic (allFns_of_mem fidCore_fns_wf) fidCore_tableImpl

end StandaloneModuleOk

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity on `fidCoreEnv` (`XPost := False`, `0` SAT) -/

section ConcreteNonVacuity

private theorem nvFidCore_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : fidCoreSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩) (pre post : List Fn) (fn : Fn)
    (hsplit : fidCoreFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp fidCoreEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody; let ⟨_, _, hwp⟩ := fidCore_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (fidCoreEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q (fun _ _ _ _ => False) hs)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_reorder_queue_fid` on
`nvM4TernaryMem`. -/
theorem nvFidCore_reorder_queue :
    Func.wp fidCoreEnv full_reorder_queue_fid_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s' : FullState,
        s'.core = nvM4TernaryState.core ∧ s'.LengthsOk nvM4TernaryCfg ∧
        FullExtScratchPres nvM4TernaryState s' ∧ nvM4TernaryF0.Unsat ∧
        FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  refine nvFidCore_wp 5 rfl (fidCoreFns.take 5) (fidCoreFns.drop 6) fidCoreFns[5]
    rfl rfl rfl rfl full_reorder_queue_fid_body rfl (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem _ ?_
  refine ⟨nvM4TernaryCfg, nvM4TernaryState, emp, rfl, nvM4Ternary_lengths, hm, ?_⟩
  intro _ s' m' hcore hlen hext hm'
  rw [sep_emp] at hm'
  exact ⟨s', hcore, hlen, hext, nvM4TernaryF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_reorder_fid` on `nvM4TernaryMem`. -/
theorem nvFidCore_reorder :
    Func.wp fidCoreEnv full_reorder_fid_body (nvM4TernaryCfg.hdr, 10#64, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s' : FullState,
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        FullArenaPermEq nvM4TernaryState.core s'.core ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  refine nvFidCore_wp 6 rfl (fidCoreFns.take 6) (fidCoreFns.drop 7) fidCoreFns[6]
    rfl rfl rfl rfl full_reorder_fid_body rfl (nvM4TernaryCfg.hdr, 10#64, ()) nvM4TernaryMem _ ?_
  refine ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryState, emp, rfl,
    nvM4Ternary_invW.toSparse, hm, ?_⟩
  intro _ s' m' hsp hperm _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨s', hsp, hperm, nvM4TernaryF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_walk_fid` on `nvM4TernaryMem`. -/
theorem nvFidCore_walk :
    Func.wp fidCoreEnv full_walk_fid_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun _ m' => ∃ s' : FullState,
        s'.LengthsOk nvM4TernaryCfg ∧ nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  refine nvFidCore_wp 8 rfl (fidCoreFns.take 8) (fidCoreFns.drop 9) fidCoreFns[8]
    rfl rfl rfl rfl full_walk_fid_body rfl (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem _ ?_
  refine ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryState, emp, rfl,
    nvM4Ternary_invW.toSparse.1, hm, ?_⟩
  intro _ _ m' _ hlen _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨_, hlen, nvM4TernaryF0_unsat, hm'⟩

end ConcreteNonVacuity

/-! ## 3. Transparent Local `fidPatch*` Combinators (`0` Edits to `FullM7Splice`) -/

section FidPatchHelpers

/-- Helper functions queued immediately before `f.name` (transparent twin of
`FullM7Splice.patchInsAt`). -/
def fidPatchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  (befores.filterMap fun (a, hs) => if a == f.name then some hs else none).flatten

/-- Helper rows queued immediately before `e.name` (transparent twin of
`FullM7Splice.patchRowInsAt`). -/
def fidPatchRowInsAt (befores : List (Sym × List SpecEntry)) (e : SpecEntry) : List SpecEntry :=
  (befores.filterMap fun (a, rs) => if a == e.name then some rs else none).flatten

/-- Simultaneous function replacement + helper insertion (matches `FullM7Splice.patchFns`). -/
def fidPatchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => fidPatchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

/-- Simultaneous row replacement + helper-row insertion (matches `FullM7Splice.patchRows`). -/
def fidPatchRows (repls : List SpecEntry) (befores : List (Sym × List SpecEntry))
    (tbl : List SpecEntry) : List SpecEntry :=
  tbl.flatMap fun e =>
    fidPatchRowInsAt befores e ++ [(repls.find? (·.name == e.name)).getD e]

private theorem fn_find_nm_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

private theorem row_find_nm_eq {repls : List SpecEntry} {e r : SpecEntry}
    (h : repls.find? (fun x => x.name == e.name) = some r) : r.name = e.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : SpecEntry => x.name == e.name) h)

private theorem mem_fidPatchInsAt {befores : List (Sym × List Fn)} {g fn : Fn}
    (h : fn ∈ fidPatchInsAt befores g) : ∃ hs, (g.name, hs) ∈ befores ∧ fn ∈ hs := by
  unfold fidPatchInsAt at h
  rcases List.mem_flatten.mp h with ⟨hs, hhs, hfn⟩
  rcases List.mem_filterMap.mp hhs with ⟨⟨a, hs0⟩, hm, hif⟩
  cases hcmp : (a == g.name)
  · simp [hcmp] at hif
  · have ha : a = g.name := beq_iff_eq.mp hcmp
    subst ha; simp at hif; subst hif; exact ⟨hs0, hm, hfn⟩

private theorem mem_fidPatchRowInsAt {befores : List (Sym × List SpecEntry)} {e₀ e : SpecEntry}
    (h : e ∈ fidPatchRowInsAt befores e₀) : ∃ rs, (e₀.name, rs) ∈ befores ∧ e ∈ rs := by
  unfold fidPatchRowInsAt at h
  rcases List.mem_flatten.mp h with ⟨rs, hrs, he⟩
  rcases List.mem_filterMap.mp hrs with ⟨⟨a, rs0⟩, hm, hif⟩
  cases hcmp : (a == e₀.name)
  · simp [hcmp] at hif
  · have ha : a = e₀.name := beq_iff_eq.mp hcmp
    subst ha; simp at hif; subst hif; exact ⟨rs0, hm, he⟩

private theorem fidPatchFns_mem_of_ne {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs : List Fn} {g : Fn} (hg : g ∈ fs) (hne : ∀ r ∈ repls, r.name ≠ g.name) :
    g ∈ fidPatchFns repls befores fs := by
  refine List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ ?_⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact List.mem_singleton_self _
  | some r => exact absurd (fn_find_nm_eq h) (hne r (List.mem_of_find?_eq_some h))

private theorem fidPatchRows_ins_mem {repls : List SpecEntry}
    {befores : List (Sym × List SpecEntry)} {tbl : List SpecEntry} {a : Sym}
    {rs : List SpecEntry} {e₀ r : SpecEntry} (hb : (a, rs) ∈ befores) (he : e₀ ∈ tbl)
    (hna : a = e₀.name) (hr : r ∈ rs) : r ∈ fidPatchRows repls befores tbl := by
  refine List.mem_flatMap.mpr ⟨e₀, he, List.mem_append_left _ ?_⟩
  refine List.mem_flatten.mpr ⟨rs, List.mem_filterMap.mpr ⟨(a, rs), hb, ?_⟩, hr⟩
  simp [hna]

private theorem fidPatchFns_wf {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf)
    (hi : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf) :
    ∀ f ∈ fidPatchFns repls befores fs, f.Wf := by
  intro fn hfn
  rcases List.mem_flatMap.mp hfn with ⟨g, hg, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_fidPatchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hi (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | none => exact hfs g hg
    | some r => exact hr r (List.mem_of_find?_eq_some h)

private theorem fidPatchRows_noExit {repls tbl : List SpecEntry}
    {befores : List (Sym × List SpecEntry)} (ht : tbl.all SpecEntry.noExit = true)
    (hr : repls.all SpecEntry.noExit = true)
    (hi : ∀ p ∈ befores, p.2.all SpecEntry.noExit = true) :
    (fidPatchRows repls befores tbl).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at ht hr ⊢
  intro e he
  rcases List.mem_flatMap.mp he with ⟨e₀, he₀, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_fidPatchRowInsAt h_ins with ⟨rs, hm, he_rs⟩
    exact (List.all_eq_true.mp (hi (e₀.name, rs) hm)) e he_rs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == e₀.name) with
    | none => exact ht e₀ he₀
    | some r => exact hr r (List.mem_of_find?_eq_some h)

private theorem fidPatchRows_sigs {replsR : List SpecEntry}
    {beforesR : List (Sym × List SpecEntry)} {replsF : List Fn}
    {beforesF : List (Sym × List Fn)} :
    ∀ (tbl : List SpecEntry) (fs : List Fn),
    tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
    (∀ r ∈ replsR, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs)) →
    (∀ r ∈ replsF, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ e ∈ tbl, ∀ f ∈ fs, e.name = f.name →
      (fidPatchRowInsAt beforesR e).map (fun r => (r.name, r.as, r.rs)) =
        (fidPatchInsAt beforesF f).map Fn.sig) →
    (fidPatchRows replsR beforesR tbl).map (fun e => (e.name, e.as, e.rs)) =
      (fidPatchFns replsF beforesF fs).map Fn.sig
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp at h
  | e :: ts, f :: fs, hsig, hsr, hsf, hins => by
    simp only [List.map_cons, List.cons.injEq] at hsig
    rcases hsig with ⟨hef, hts⟩
    have hnm : e.name = f.name := congrArg Prod.fst hef
    have hsr_r : ∀ r ∈ replsR, ∀ e' ∈ ts, r.name = e'.name →
        (r.name, r.as, r.rs) = (e'.name, e'.as, e'.rs) :=
      fun r hr e' he' => hsr r hr e' (List.mem_cons_of_mem e he')
    have hsf_r : ∀ r ∈ replsF, ∀ f' ∈ fs, r.name = f'.name → r.sig = f'.sig :=
      fun r hr f' hf' => hsf r hr f' (List.mem_cons_of_mem f hf')
    have hins_r : ∀ e' ∈ ts, ∀ f' ∈ fs, e'.name = f'.name →
        (fidPatchRowInsAt beforesR e').map (fun r => (r.name, r.as, r.rs)) =
          (fidPatchInsAt beforesF f').map Fn.sig :=
      fun e' he' f' hf' => hins e' (List.mem_cons_of_mem e he') f' (List.mem_cons_of_mem f hf')
    have hrow : ((replsR.find? (fun x => x.name == e.name)).getD e).name = e.name ∧
        (((replsR.find? (fun x => x.name == e.name)).getD e).as,
          ((replsR.find? (fun x => x.name == e.name)).getD e).rs) = (e.as, e.rs) := by
      cases h : replsR.find? (fun x => x.name == e.name) with
      | none => exact ⟨rfl, rfl⟩
      | some r =>
        dsimp only [Option.getD]
        have heq := hsr r (List.mem_of_find?_eq_some h) e List.mem_cons_self (row_find_nm_eq h)
        exact ⟨congrArg Prod.fst heq, Prod.ext (congrArg (fun p => p.2.1) heq)
          (congrArg (fun p => p.2.2) heq)⟩
    have hfn : ((replsF.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : replsF.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsf r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fn_find_nm_eq h)
    have ih := fidPatchRows_sigs (replsR := replsR) (beforesR := beforesR)
      (replsF := replsF) (beforesF := beforesF) ts fs hts hsr_r hsf_r hins_r
    unfold fidPatchRows fidPatchFns at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil]
    rw [hins e List.mem_cons_self f List.mem_cons_self hnm, ih]
    have hsigr : (((replsR.find? (fun x => x.name == e.name)).getD e).name,
        ((replsR.find? (fun x => x.name == e.name)).getD e).as,
        ((replsR.find? (fun x => x.name == e.name)).getD e).rs) =
        ((replsF.find? (fun x => x.name == f.name)).getD f).sig := by
      rw [hfn, ← hef]
      exact Prod.ext hrow.1 hrow.2
    rw [hsigr]

private theorem fidPatchFns_names_map {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (fidPatchFns repls befores fs).map Fn.name =
      fs.flatMap fun f => (fidPatchInsAt befores f).map Fn.name ++ [f.name] := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    have hsig_r : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hname : ((repls.find? (fun x => x.name == f.name)).getD f).name = f.name := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r => exact fn_find_nm_eq h
    unfold fidPatchFns at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [hname, ih hsig_r]

private theorem fidPatchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hnd : (fs.map Fn.name).Nodup)
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hinsNd : ∀ f ∈ fs, ((fidPatchInsAt befores f).map Fn.name).Nodup)
    (hinsDisj : ∀ f ∈ fs, ∀ h ∈ fidPatchInsAt befores f, h.name ∉ fs.map Fn.name)
    (hinsPair : ∀ f₁ ∈ fs, ∀ f₂ ∈ fs, f₁.name ≠ f₂.name →
      ∀ h ∈ fidPatchInsAt befores f₁, h.name ∉ (fidPatchInsAt befores f₂).map Fn.name) :
    ((fidPatchFns repls befores fs).map Fn.name).Nodup := by
  rw [fidPatchFns_names_map hsig]
  clear hsig repls
  induction fs with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hinsNd_r : ∀ g ∈ rest, ((fidPatchInsAt befores g).map Fn.name).Nodup :=
      fun g hg => hinsNd g (List.mem_cons_of_mem f hg)
    have hinsDisj_r : ∀ g ∈ rest, ∀ h ∈ fidPatchInsAt befores g, h.name ∉ rest.map Fn.name :=
      fun g hg h hh hm => hinsDisj g (List.mem_cons_of_mem f hg) h hh
        (by simp [List.mem_cons, hm])
    have hinsPair_r : ∀ g₁ ∈ rest, ∀ g₂ ∈ rest, g₁.name ≠ g₂.name →
        ∀ h ∈ fidPatchInsAt befores g₁, h.name ∉ (fidPatchInsAt befores g₂).map Fn.name :=
      fun g₁ hg₁ g₂ hg₂ => hinsPair g₁ (List.mem_cons_of_mem f hg₁)
        g₂ (List.mem_cons_of_mem f hg₂)
    have hrest_nd := ih hnd.2 hinsNd_r hinsDisj_r hinsPair_r
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨⟨hinsNd f List.mem_cons_self, by simp, ?_⟩, hrest_nd, ?_⟩
    · intro x hx y hy hxy
      subst hxy
      simp only [List.mem_singleton] at hy; subst hy
      rcases List.mem_map.mp hx with ⟨h, hh, hnm⟩
      exact hinsDisj f List.mem_cons_self h hh (by simp [List.mem_cons, hnm])
    · intro x hx y hy hxy
      subst hxy
      rcases List.mem_flatMap.mp hy with ⟨g, hg, hy_g⟩
      have hne_fg : f.name ≠ g.name := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hg)
      rcases List.mem_append.mp hx with hx_ins | hx_f
      · rcases List.mem_map.mp hx_ins with ⟨h, hh, rfl⟩
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · exact hinsPair f List.mem_cons_self g (List.mem_cons_of_mem f hg) hne_fg h hh hy_ins
        · simp only [List.mem_singleton] at hy_gname
          exact hinsDisj f List.mem_cons_self h hh
            (by simp [List.mem_cons, hy_gname, List.mem_map_of_mem hg])
      · simp only [List.mem_singleton] at hx_f; subst hx_f
        rcases List.mem_append.mp hy_g with hy_ins | hy_gname
        · rcases List.mem_map.mp hy_ins with ⟨h, hh, hnm⟩
          exact hinsDisj g (List.mem_cons_of_mem f hg) h hh (by simp [List.mem_cons, hnm])
        · simp only [List.mem_singleton] at hy_gname
          exact hne_fg hy_gname

private theorem checkFnsCallsOk_fidPatch (exits : List Sym) (extSigs : List SigEntry)
    (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (origSeen : List Fn) (seen : List SigEntry) (fs : List Fn),
    (∀ g ∈ origSeen, g.sig ∈ seen) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (origSeen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post, fs = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((origSeen ++ pre).map Fn.sig) (fidPatchInsAt befores f) = true) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        ((origSeen ++ pre).map Fn.sig ++ (fidPatchInsAt befores f).map Fn.sig ++ extSigs)
        exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen (fidPatchFns repls befores fs) = true
  | _, _, [], _, _, _, _, _ => rfl
  | origSeen, seen, f :: rest, hsub, hchk, hsig, hins, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    unfold fidPatchFns
    simp only [List.flatMap_cons]
    have hsig_rest : ∀ r ∈ repls, ∀ g ∈ rest, r.name = g.name → r.sig = g.sig :=
      fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg)
    have hins_rest : ∀ pre g post, rest = pre ++ g :: post →
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs
          (((origSeen ++ [f]) ++ pre).map Fn.sig) (fidPatchInsAt befores g) = true := by
      intro pre g post hsplit; rw [List.append_assoc]
      exact hins (f :: pre) g post (by rw [hsplit]; rfl)
    have hrepl_rest : ∀ pre g post r, rest = pre ++ g :: post → r ∈ repls → r.name = g.name →
        r.checkCallsOk
          (((origSeen ++ [f]) ++ pre).map Fn.sig ++
            (fidPatchInsAt befores g).map Fn.sig ++ extSigs)
          exits = true := by
      intro pre g post r hsplit hr hnm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hrepl (f :: pre) g post r (by rw [hsplit]; rfl) hr hnm
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        dsimp only [Option.getD]
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fn_find_nm_eq h)
    have hsub_ext : ∀ s ∈ origSeen.map Fn.sig ++ extSigs, s ∈ seen ++ extSigs := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · rcases List.mem_map.mp hs1 with ⟨g, hg, rfl⟩
        exact List.mem_append_left _ (hsub g hg)
      · exact List.mem_append_right _ hs2
    have h_ins_ok : LeanQbe.T.Module.checkFnsCallsOk exits extSigs seen
        (fidPatchInsAt befores f) = true := by
      have h0 := hins [] f rest rfl
      simp only [List.append_nil] at h0
      exact checkFnsCallsOk_mono hsub_ext h0
    have h_mid_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        ((seen ++ (fidPatchInsAt befores f).map Fn.sig) ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none =>
        refine fn_checkCallsOk_mono (fun s hs => ?_) hchk.1
        rcases List.mem_append.mp (hsub_ext s hs) with hs1 | hs2
        · exact List.mem_append_left _ (List.mem_append_left _ hs1)
        · exact List.mem_append_right _ hs2
      | some r =>
        have h0 := hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (fn_find_nm_eq h)
        simp only [List.append_nil] at h0
        refine fn_checkCallsOk_mono (fun s hs => ?_) h0
        rcases List.mem_append.mp hs with hs1 | hs2
        · rcases List.mem_append.mp hs1 with hs1a | hs1b
          · rcases List.mem_map.mp hs1a with ⟨g, hg, rfl⟩
            exact List.mem_append_left _ (List.mem_append_left _ (hsub g hg))
          · exact List.mem_append_left _ (List.mem_append_right _ hs1b)
        · exact List.mem_append_right _ hs2
    rw [List.append_assoc, checkFnsCallsOk_append, h_ins_ok, Bool.true_and,
      checkFnsCallsOk_append, LeanQbe.T.Module.checkFnsCallsOk, h_mid_ok]
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.true_and, List.map_singleton,
      List.append_assoc]
    have hsub_next : ∀ g ∈ origSeen ++ [f],
        g.sig ∈ seen ++ ((fidPatchInsAt befores f).map Fn.sig ++
          [((repls.find? (fun x => x.name == f.name)).getD f).sig]) := by
      intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact List.mem_append_left _ (hsub g hg1)
      · simp only [List.mem_singleton] at hg2; subst hg2
        exact List.mem_append_right _ (List.mem_append_right _ (by simp [hhead_sig]))
    have hchk2 :
        LeanQbe.T.Module.checkFnsCallsOk exits extSigs ((origSeen ++ [f]).map Fn.sig) rest =
          true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    exact checkFnsCallsOk_fidPatch exits extSigs repls befores (origSeen ++ [f])
      (seen ++ ((fidPatchInsAt befores f).map Fn.sig ++
        [((repls.find? (fun x => x.name == f.name)).getD f).sig]))
      rest hsub_next hchk2 hsig_rest hins_rest hrepl_rest

private theorem fidPatchModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((fidPatchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig) (fidPatchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (fidPatchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := fidPatchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨listNodup_iff.mpr hnd, ?_⟩
  exact checkFnsCallsOk_fidPatch M.exits (M.externs.map Extern.sig) repls befores [] [] M.fns
    (fun _ h => nomatch h) hM.2 hsig hins hrepl

private theorem fidPatchModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := fidPatchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hiWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    (hCallee : ∀ f as bs,
      (f, as, bs) ∈ M.fns.map Fn.sig ++ M.externs.map Extern.sig →
      ∀ xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X)
    (hiWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ' h.name h.as h.rs xs m Q X → Func.wp Γ' h.body xs m Q X) :
    ModuleOk Γ' { M with fns := fidPatchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk
    (fidPatchFns_wf hwfOrig hrWf hiWf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · rcases mem_fidPatchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hiWp (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | some r =>
      intro xs m Q X hspec
      exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
    | none =>
      intro xs m Q X hspec
      rcases hFnWp g hg h with hNew | hPull
      · exact hNew xs m Q X hspec
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
        have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
        exact wp_env_agree_of_callsOk
          (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
          hcallsG
          (fun f as bs hmem' => hCallee f as bs (by
            rcases List.mem_append.mp hmem' with hs | hs
            · exact List.mem_append_left _ (by
                rw [hsplit, List.map_append]; exact List.mem_append_left _ hs)
            · exact List.mem_append_right _ hs))
          m (hwpG xs m Q X (hPull xs m Q X hspec))

end FidPatchHelpers

/-! ## 4. Canonical `patchFns` / `patchRows` Exports & `412`-Fn `FullM7` Splice -/

section M7SpliceSection

/-- Canonical `7`-row replacement table preserving EXACT existing `FullM7Proof.m7SpecTable`
`Spec`s (`0` spec changes). -/
def fidCorePatchRows : List SpecEntry :=
  [ ⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩ ]

/-- Helper `SpecEntry` insertion list for `FullM7Splice.patchRows`, matching
`fidCorePatchBefores`. -/
def fidCorePatchRowBefores : List (Sym × List SpecEntry) :=
  [ ("full_bva_filter_row",
      [⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool],
          fidBvaMatchLargeSpec, true⟩])
  , ("full_reorder_queue_m7",
      [⟨"full_reorder_sift_fid", [i64, i64, i64], [], fidReorderSiftSpec, true⟩]) ]

/-- `412`-function `FullM7` module list patched with all `7` Target A Core functions + `2`
inserted helpers. -/
def fidCorePatchedFns : List Fn :=
  fidPatchFns fidCorePatchFns fidCorePatchBefores m7Fns

/-- Patched `412`-function `FullM7` module (`externs := []`, `exits := []`). -/
def fidCorePatchedModule : LeanQbe.T.Module :=
  { m7Module with fns := fidCorePatchedFns }

/-- `412`-row patched specification table aligned 1-to-1 with `fidCorePatchedFns`. -/
def fidCorePatchedSpecTable (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  fidPatchRows fidCorePatchRows fidCorePatchRowBefores (m7SpecTable tBve solveSpec)

/-- `2`-row specification table for the inserted helpers (`full_bva_match_large_fid` and
`full_reorder_sift_fid`). -/
def fidCoreInsRows : List SpecEntry :=
  [ ⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool], fidBvaMatchLargeSpec, true⟩
  , ⟨"full_reorder_sift_fid", [i64, i64, i64], [], fidReorderSiftSpec, true⟩ ]

theorem fidCoreInsRows_nodup : (fidCoreInsRows.map SpecEntry.name).Nodup := by decide

/-- Closed `Env` for `fidCorePatchedModule` combining `fidCoreInsRows` (`2` inserted helpers)
with `FullM7Proof.mkM7Env` (`410` `FullM7` rows including the `7` preserved `Spec`s). -/
def mkFidCorePatchedEnv (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) : Env :=
  fun f as bs xs m Q X =>
    Env.ofTable fidCoreInsRows f as bs xs m Q X ∨
      (f ≠ "full_bva_match_large_fid" ∧ f ≠ "full_reorder_sift_fid" ∧
        mkM7Env tBve solveSpec f as bs xs m Q X)

/-- `tBve` rows required by `full_elim_bve_fid` (complementing `M7BveAllTblSpecs tBve`). -/
structure FidCoreBveCallees (tBve : List SpecEntry) : Prop where
  denseFlush :
    (⟨"full_dense_flush_units_m7", [i64], [.bool],
      FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩ : SpecEntry) ∈ tBve
  bveVar :
    (⟨"full_bve_var_m7", [i64, i32], [i64],
      FullFastBveBudgets.fullBveVarDefSpec, true⟩ : SpecEntry) ∈ tBve
  bvePush :
    (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
      FullM6BveFwd.fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈ tBve
  bvePop :
    (⟨"full_bve_heap_pop_m7", [i64, i64], [i32],
      FullM6BveFwd.fullBveHeapPopM6Spec, true⟩ : SpecEntry) ∈ tBve
  bveNbrs :
    (⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64],
      FullM3CongBva.m3ElimCollectNbrsSpec, true⟩ : SpecEntry) ∈ tBve
  elimBve :
    (⟨"full_elim_bve_m7", [i64, i64], [i64],
      FullM3CongBva.m3ElimBveSpec, true⟩ : SpecEntry) ∈ tBve

/-- Untouched `Part 1`/`Part 2`/`Part 3` rows inside `m7SpecTable tBve solveSpec` whose segment
definitions are `private` in `FullM7Transport0..2`. -/
structure FidCoreM7BridgeRows (tbl : List SpecEntry) : Prop where
  heapUp :
    (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈ tbl
  minMark :
    (⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩ : SpecEntry) ∈ tbl
  sortTmp :
    (⟨"full_sort_tmp", [i64], [], FullM7AnalyzeSort.m7SortTmpSpec, true⟩ : SpecEntry) ∈ tbl
  minLitDfs :
    (⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.m6MinLitDfsSpec, true⟩ : SpecEntry) ∈ tbl
  shrinkBlkBool :
    (⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.m6ShrinkBlkBoolSpec, true⟩ : SpecEntry) ∈ tbl
  walkInitVals :
    (⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.m7InitValsSpec, true⟩ : SpecEntry) ∈ tbl
  walkCollect :
    (⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.m7CollectSpec, true⟩ : SpecEntry) ∈ tbl
  walkCbInv :
    (⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64],
      FullM7Walk.m7CbInvSpec, true⟩ : SpecEntry) ∈ tbl
  walkInitTable :
    (⟨"full_walk_init_table_m7", [i64, i64], [],
      FullM7Walk.m7InitTableSpec, true⟩ : SpecEntry) ∈ tbl
  walkBuildOcc :
    (⟨"full_walk_build_occ_m7", [i64, i64], [i64],
      FullM7Walk.m7BuildOccSpec, true⟩ : SpecEntry) ∈ tbl
  walkEffort :
    (⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩ : SpecEntry) ∈ tbl
  walkPick :
    (⟨"full_walk_pick_m7", [i64, i32, i64], [i64],
      FullM7Walk.m7PickSpec, true⟩ : SpecEntry) ∈ tbl
  walkFlip :
    (⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64],
      FullM7Walk.m7FlipSpec, true⟩ : SpecEntry) ∈ tbl
  walkSaveMin :
    (⟨"full_walk_save_min_m7", [i64, i64, .bool], [],
      FullM7Walk.m7SaveMinSpec, true⟩ : SpecEntry) ∈ tbl
  walkM7 :
    (⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩ : SpecEntry) ∈ tbl
  bvaScanCands :
    (⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩ : SpecEntry) ∈ tbl
  bvaFilterRow :
    (⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩ : SpecEntry) ∈ tbl

/-! ### Exact `m7Fns` Index & Signature Metadata (`0` Full-Body Unfolding) -/

private theorem m7_p1_10 : m7FnsPart1[10]?.map Fn.sig =
    some ("full_rng_next", [i64], [i64]) := by t_kernel_rfl
private theorem m7_p1_11 : m7FnsPart1[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := by t_kernel_rfl
private theorem m7_p1_19 : m7FnsPart1[19]?.map Fn.sig =
    some ("full_heap_up", [i64, i32], []) := by t_kernel_rfl
private theorem m7_p1_24 : m7FnsPart1[24]?.map Fn.sig =
    some ("full_rescale", [i64], []) := by t_kernel_rfl
private theorem m7_p2_12 : m7FnsPart2[12]?.map Fn.sig =
    some ("full_min_mark", [i64, i32, i8], []) := by t_kernel_rfl
private theorem m7_p2_17 : m7FnsPart2[17]?.map Fn.sig =
    some ("full_sort_tmp", [i64], []) := by t_kernel_rfl
private theorem m7_p2_18 : m7FnsPart2[18]?.map Fn.sig =
    some ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) := by t_kernel_rfl
private theorem m7_p2_21 : m7FnsPart2[21]?.map Fn.sig =
    some ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool]) := by t_kernel_rfl
private theorem m7_p2_23 : m7FnsPart2[23]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := by t_kernel_rfl
private theorem m7_p2_42 : m7FnsPart2[42]?.map Fn.sig =
    some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_43 : m7FnsPart2[43]?.map Fn.sig =
    some ("full_walk_init_table_m7", [i64, i64], []) := by t_kernel_rfl
private theorem m7_p2_44 : m7FnsPart2[44]?.map Fn.sig =
    some ("full_walk_effort_m7", [i64, i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_45 : m7FnsPart2[45]?.map Fn.sig =
    some ("full_walk_init_vals_m7", [i64], []) := by t_kernel_rfl
private theorem m7_p2_46 : m7FnsPart2[46]?.map Fn.sig =
    some ("full_walk_collect_m7", [i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_47 : m7FnsPart2[47]?.map Fn.sig =
    some ("full_walk_build_occ_m7", [i64, i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_49 : m7FnsPart2[49]?.map Fn.sig =
    some ("full_walk_pick_m7", [i64, i32, i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_50 : m7FnsPart2[50]?.map Fn.sig =
    some ("full_walk_flip_m7", [i64, i32, i64, i64], [i64]) := by t_kernel_rfl
private theorem m7_p2_51 : m7FnsPart2[51]?.map Fn.sig =
    some ("full_walk_save_min_m7", [i64, i64, .bool], []) := by t_kernel_rfl
private theorem m7_p2_52 : m7FnsPart2[52]?.map Fn.sig =
    some ("full_walk_m7", [i64], []) := by t_kernel_rfl
private theorem m7_p3_26 : m7FnsPart3[26]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := by t_kernel_rfl
private theorem m7_p3_62 : m7FnsPart3[62]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem m7_p3_69 : m7FnsPart3[69]?.map Fn.sig =
    some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32]) := by t_kernel_rfl
private theorem m7_p3_71 : m7FnsPart3[71]?.map Fn.sig =
    some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]) := by t_kernel_rfl
private theorem m7_p3_92 : m7FnsPart3[92]?.map Fn.sig =
    some ("full_reorder_queue_m7", [i64], [i64]) := by t_kernel_rfl
private theorem m7_p3_93 : m7FnsPart3[93]?.map Fn.sig =
    some ("full_reorder_m6", [i64, i64], [i64]) := by t_kernel_rfl
private theorem m7_p3_104 : m7FnsPart3[104]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := by t_kernel_rfl
private theorem m7_p3_105 : m7FnsPart3[105]?.map Fn.sig =
    some ("full_bve_heap_pop_m7", [i64, i64], [i32]) := by t_kernel_rfl
private theorem m7_p3_106 : m7FnsPart3[106]?.map Fn.sig =
    some ("full_bve_collect_nbrs_m7", [i64, i32], [i64]) := by t_kernel_rfl
private theorem m7_p3_107 : m7FnsPart3[107]?.map Fn.sig =
    some ("full_elim_bve_m7", [i64, i64], [i64]) := by t_kernel_rfl

private theorem m7_cidx_10 : m7Fns[10]?.map Fn.sig =
    some ("full_rng_next", [i64], [i64]) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_10
private theorem m7_cidx_11 : m7Fns[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_11
private theorem m7_cidx_19 : m7Fns[19]?.map Fn.sig =
    some ("full_heap_up", [i64, i32], []) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_19
private theorem m7_cidx_24 : m7Fns[24]?.map Fn.sig =
    some ("full_rescale", [i64], []) := by
  rw [m7_get_p1 (by decide)]; exact m7_p1_24
private theorem m7_cidx_124 : m7Fns[124]?.map Fn.sig =
    some ("full_min_mark", [i64, i32, i8], []) := by
  rw [show (124 : Nat) = 112 + 12 by rfl, m7_get_p2 (by decide)]; exact m7_p2_12
private theorem m7_cidx_129 : m7Fns[129]?.map Fn.sig =
    some ("full_sort_tmp", [i64], []) := by
  rw [show (129 : Nat) = 112 + 17 by rfl, m7_get_p2 (by decide)]; exact m7_p2_17
private theorem m7_cidx_130 : m7Fns[130]?.map Fn.sig =
    some ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) := by
  rw [show (130 : Nat) = 112 + 18 by rfl, m7_get_p2 (by decide)]; exact m7_p2_18
private theorem m7_cidx_133 : m7Fns[133]?.map Fn.sig =
    some ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool]) := by
  rw [show (133 : Nat) = 112 + 21 by rfl, m7_get_p2 (by decide)]; exact m7_p2_21
private theorem m7_cidx_135 : m7Fns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := by
  rw [show (135 : Nat) = 112 + 23 by rfl, m7_get_p2 (by decide)]; exact m7_p2_23
private theorem m7_cidx_154 : m7Fns[154]?.map Fn.sig =
    some ("full_walk_cb_inv_m7", [i64, i64, i64], [i64]) := by
  rw [show (154 : Nat) = 112 + 42 by rfl, m7_get_p2 (by decide)]; exact m7_p2_42
private theorem m7_cidx_155 : m7Fns[155]?.map Fn.sig =
    some ("full_walk_init_table_m7", [i64, i64], []) := by
  rw [show (155 : Nat) = 112 + 43 by rfl, m7_get_p2 (by decide)]; exact m7_p2_43
private theorem m7_cidx_156 : m7Fns[156]?.map Fn.sig =
    some ("full_walk_effort_m7", [i64, i64], [i64]) := by
  rw [show (156 : Nat) = 112 + 44 by rfl, m7_get_p2 (by decide)]; exact m7_p2_44
private theorem m7_cidx_157 : m7Fns[157]?.map Fn.sig =
    some ("full_walk_init_vals_m7", [i64], []) := by
  rw [show (157 : Nat) = 112 + 45 by rfl, m7_get_p2 (by decide)]; exact m7_p2_45
private theorem m7_cidx_158 : m7Fns[158]?.map Fn.sig =
    some ("full_walk_collect_m7", [i64], [i64]) := by
  rw [show (158 : Nat) = 112 + 46 by rfl, m7_get_p2 (by decide)]; exact m7_p2_46
private theorem m7_cidx_159 : m7Fns[159]?.map Fn.sig =
    some ("full_walk_build_occ_m7", [i64, i64], [i64]) := by
  rw [show (159 : Nat) = 112 + 47 by rfl, m7_get_p2 (by decide)]; exact m7_p2_47
private theorem m7_cidx_161 : m7Fns[161]?.map Fn.sig =
    some ("full_walk_pick_m7", [i64, i32, i64], [i64]) := by
  rw [show (161 : Nat) = 112 + 49 by rfl, m7_get_p2 (by decide)]; exact m7_p2_49
private theorem m7_cidx_162 : m7Fns[162]?.map Fn.sig =
    some ("full_walk_flip_m7", [i64, i32, i64, i64], [i64]) := by
  rw [show (162 : Nat) = 112 + 50 by rfl, m7_get_p2 (by decide)]; exact m7_p2_50
private theorem m7_cidx_163 : m7Fns[163]?.map Fn.sig =
    some ("full_walk_save_min_m7", [i64, i64, .bool], []) := by
  rw [show (163 : Nat) = 112 + 51 by rfl, m7_get_p2 (by decide)]; exact m7_p2_51
private theorem m7_cidx_164 : m7Fns[164]?.map Fn.sig =
    some ("full_walk_m7", [i64], []) := by
  rw [show (164 : Nat) = 112 + 52 by rfl, m7_get_p2 (by decide)]; exact m7_p2_52
private theorem m7_cidx_302 : m7Fns[302]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := by
  rw [show (302 : Nat) = 276 + 26 by rfl, m7_get_p3]; exact m7_p3_26
private theorem m7_cidx_338 : m7Fns[338]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := by
  rw [show (338 : Nat) = 276 + 62 by rfl, m7_get_p3]; exact m7_p3_62
private theorem m7_cidx_345 : m7Fns[345]?.map Fn.sig =
    some ("full_bva_scan_cands", [i64, i32, i32, i64], [i32]) := by
  rw [show (345 : Nat) = 276 + 69 by rfl, m7_get_p3]; exact m7_p3_69
private theorem m7_cidx_347 : m7Fns[347]?.map Fn.sig =
    some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]) := by
  rw [show (347 : Nat) = 276 + 71 by rfl, m7_get_p3]; exact m7_p3_71
private theorem m7_cidx_368 : m7Fns[368]?.map Fn.sig =
    some ("full_reorder_queue_m7", [i64], [i64]) := by
  rw [show (368 : Nat) = 276 + 92 by rfl, m7_get_p3]; exact m7_p3_92
private theorem m7_cidx_369 : m7Fns[369]?.map Fn.sig =
    some ("full_reorder_m6", [i64, i64], [i64]) := by
  rw [show (369 : Nat) = 276 + 93 by rfl, m7_get_p3]; exact m7_p3_93
private theorem m7_cidx_380 : m7Fns[380]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := by
  rw [show (380 : Nat) = 276 + 104 by rfl, m7_get_p3]; exact m7_p3_104
private theorem m7_cidx_381 : m7Fns[381]?.map Fn.sig =
    some ("full_bve_heap_pop_m7", [i64, i64], [i32]) := by
  rw [show (381 : Nat) = 276 + 105 by rfl, m7_get_p3]; exact m7_p3_105
private theorem m7_cidx_382 : m7Fns[382]?.map Fn.sig =
    some ("full_bve_collect_nbrs_m7", [i64, i32], [i64]) := by
  rw [show (382 : Nat) = 276 + 106 by rfl, m7_get_p3]; exact m7_p3_106
private theorem m7_cidx_383 : m7Fns[383]?.map Fn.sig =
    some ("full_elim_bve_m7", [i64, i64], [i64]) := by
  rw [show (383 : Nat) = 276 + 107 by rfl, m7_get_p3]; exact m7_p3_107

private theorem m7Fns_not_mem_bml : "full_bva_match_large_fid" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_bva_match_large_fid" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

private theorem m7Fns_not_mem_sift : "full_reorder_sift_fid" ∉ m7Fns.map Fn.name := by
  have hc : (m7Fns.map Fn.name).contains "full_reorder_sift_fid" = false := by t_kernel_rfl
  exact fun hm => absurd hm (by simpa using hc)

private theorem fidCorePatch_sigs :
    ∀ r ∈ fidCorePatchFns, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f135, _, hs135⟩ := sig_of_map_idx m7_cidx_135
  obtain ⟨f164, _, hs164⟩ := sig_of_map_idx m7_cidx_164
  obtain ⟨f345, _, hs345⟩ := sig_of_map_idx m7_cidx_345
  obtain ⟨f347, _, hs347⟩ := sig_of_map_idx m7_cidx_347
  obtain ⟨f368, _, hs368⟩ := sig_of_map_idx m7_cidx_368
  obtain ⟨f369, _, hs369⟩ := sig_of_map_idx m7_cidx_369
  obtain ⟨f383, _, hs383⟩ := sig_of_map_idx m7_cidx_383
  intro r hr f hf hnm
  simp only [fidCorePatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs135.symm))
    subst this; exact hs135.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs345.symm))
    subst this; exact hs345.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs347.symm))
    subst this; exact hs347.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs368.symm))
    subst this; exact hs368.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs369.symm))
    subst this; exact hs369.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs383.symm))
    subst this; exact hs383.symm
  · have := fn_eq_of_mem_idx m7_names_nodup hf ‹_› (hnm.symm.trans (congrArg Prod.fst hs164.symm))
    subst this; exact hs164.symm

private theorem fidPatchInsAt_filter_eq {a b : Sym} {v : List Fn}
    (hb : (a == b) = true) :
    (if a == b then some v else none) = some v := by
  rw [hb]; rfl

private theorem fidPatchInsAt_filter_ne {a b : Sym} {v : List Fn}
    (hb : (a == b) = false) :
    (if a == b then some v else none) = none := by
  rw [hb]; rfl

private theorem fidCorePatch_insAt_name_cases (f : Fn) :
    fidPatchInsAt fidCorePatchBefores f = [] ∨
      (f.name = "full_bva_filter_row" ∧
        fidPatchInsAt fidCorePatchBefores f = [fidBvaMatchLargeFidFn]) ∨
      (f.name = "full_reorder_queue_m7" ∧
        fidPatchInsAt fidCorePatchBefores f = [fidReorderSiftFidFn]) := by
  by_cases h1 : f.name = "full_bva_filter_row"
  · right; left
    refine ⟨h1, ?_⟩
    unfold fidPatchInsAt; dsimp only [fidCorePatchBefores]; rw [h1]; rfl
  · by_cases h2 : f.name = "full_reorder_queue_m7"
    · right; right
      refine ⟨h2, ?_⟩
      unfold fidPatchInsAt; dsimp only [fidCorePatchBefores]; rw [h2]; rfl
    · left
      have hb1 : ("full_bva_filter_row" == f.name) = false := beq_false_of_ne (Ne.symm h1)
      have hb2 : ("full_reorder_queue_m7" == f.name) = false := beq_false_of_ne (Ne.symm h2)
      unfold fidPatchInsAt; dsimp only [fidCorePatchBefores]
      rw [List.filterMap_cons, fidPatchInsAt_filter_ne hb1,
        List.filterMap_cons, fidPatchInsAt_filter_ne hb2]
      rfl

theorem fidCorePatchedFns_names_nodup : (fidCorePatchedFns.map Fn.name).Nodup := by
  refine fidPatchFns_names_nodup m7_names_nodup fidCorePatch_sigs ?_ ?_ ?_
  · intro f _
    rcases fidCorePatch_insAt_name_cases f with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  · intro f _ h hh
    rcases fidCorePatch_insAt_name_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [h0] at hh; cases hh
    · rw [h1, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_bml
    · rw [h2, List.mem_singleton] at hh; subst hh; exact m7Fns_not_mem_sift
  · intro f₁ _ f₂ _ hne h hh hm
    rcases fidCorePatch_insAt_name_cases f₁ with h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
    · rw [h1] at hh; cases hh
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases fidCorePatch_insAt_name_cases f₂ with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩
      · rw [h2] at hm; cases hm
      · exact hne (he1.trans he2.symm)
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
    · rw [hp1, List.mem_singleton] at hh; subst hh
      rcases fidCorePatch_insAt_name_cases f₂ with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩
      · rw [h2] at hm; cases hm
      · rw [hp2] at hm; simp only [List.map_singleton, List.mem_singleton] at hm
        exact absurd hm.symm (by decide)
      · exact hne (he1.trans he2.symm)

/-- Unconditional `checkAcyclic = true` for the `412`-function `fidCorePatchedModule`. -/
theorem fidCorePatched_acyclic : fidCorePatchedModule.checkAcyclic = true := by
  obtain ⟨f135, hf135, hs135⟩ := sig_of_map_idx m7_cidx_135
  obtain ⟨f164, hf164, hs164⟩ := sig_of_map_idx m7_cidx_164
  obtain ⟨f345, hf345, hs345⟩ := sig_of_map_idx m7_cidx_345
  obtain ⟨f347, hf347, hs347⟩ := sig_of_map_idx m7_cidx_347
  obtain ⟨f368, hf368, hs368⟩ := sig_of_map_idx m7_cidx_368
  obtain ⟨f369, hf369, hs369⟩ := sig_of_map_idx m7_cidx_369
  obtain ⟨f383, hf383, hs383⟩ := sig_of_map_idx m7_cidx_383
  obtain ⟨g10, hg10, hsg10⟩ := sig_of_map_idx m7_cidx_10
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx m7_cidx_11
  obtain ⟨g19, hg19, hsg19⟩ := sig_of_map_idx m7_cidx_19
  obtain ⟨g24, hg24, hsg24⟩ := sig_of_map_idx m7_cidx_24
  obtain ⟨g124, hg124, hsg124⟩ := sig_of_map_idx m7_cidx_124
  obtain ⟨g129, hg129, hsg129⟩ := sig_of_map_idx m7_cidx_129
  obtain ⟨g130, hg130, hsg130⟩ := sig_of_map_idx m7_cidx_130
  obtain ⟨g133, hg133, hsg133⟩ := sig_of_map_idx m7_cidx_133
  obtain ⟨g154, hg154, hsg154⟩ := sig_of_map_idx m7_cidx_154
  obtain ⟨g155, hg155, hsg155⟩ := sig_of_map_idx m7_cidx_155
  obtain ⟨g156, hg156, hsg156⟩ := sig_of_map_idx m7_cidx_156
  obtain ⟨g157, hg157, hsg157⟩ := sig_of_map_idx m7_cidx_157
  obtain ⟨g158, hg158, hsg158⟩ := sig_of_map_idx m7_cidx_158
  obtain ⟨g159, hg159, hsg159⟩ := sig_of_map_idx m7_cidx_159
  obtain ⟨g161, hg161, hsg161⟩ := sig_of_map_idx m7_cidx_161
  obtain ⟨g162, hg162, hsg162⟩ := sig_of_map_idx m7_cidx_162
  obtain ⟨g163, hg163, hsg163⟩ := sig_of_map_idx m7_cidx_163
  obtain ⟨g302, hg302, hsg302⟩ := sig_of_map_idx m7_cidx_302
  obtain ⟨g338, hg338, hsg338⟩ := sig_of_map_idx m7_cidx_338
  obtain ⟨g380, hg380, hsg380⟩ := sig_of_map_idx m7_cidx_380
  obtain ⟨g381, hg381, hsg381⟩ := sig_of_map_idx m7_cidx_381
  obtain ⟨g382, hg382, hsg382⟩ := sig_of_map_idx m7_cidx_382
  refine fidPatchModule_checkAcyclic (M := m7Module) (repls := fidCorePatchFns)
    (befores := fidCorePatchBefores) ?_ m7_acyclic fidCorePatch_sigs ?_ ?_
  · have hnd := fidCorePatchedFns_names_nodup
    unfold fidCorePatchedFns at hnd
    simpa only [m7Module, List.map_nil, List.append_nil] using hnd
  · intro pre f post _
    rcases fidCorePatch_insAt_name_cases f with h0 | ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [h0]; rfl
    · rw [h1]
      have hb : fidBvaMatchLargeFidFn.checkCallsOk [] m7Module.exits = true := by rfl
      have hm := fn_checkCallsOk_mono
        (a₂ := pre.map Fn.sig ++ m7Module.externs.map Extern.sig)
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [hm]; rfl
    · rw [h2]
      have hb : fidReorderSiftFidFn.checkCallsOk [] m7Module.exits = true := by rfl
      have hm := fn_checkCallsOk_mono
        (a₂ := pre.map Fn.sig ++ m7Module.externs.map Extern.sig)
        (fun _ h => False.elim (List.not_mem_nil h)) hb
      dsimp only [LeanQbe.T.Module.checkFnsCallsOk]
      rw [hm]; rfl
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    simp only [fidCorePatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hn0 : f.name = f135.name := hnm.symm.trans (congrArg Prod.fst hs135.symm)
      have hc : fidMinShrinkM6Fn.checkCallsOk
          [ ("full_sort_tmp", [i64], [])
          , ("full_min_mark", [i64, i32, i8], [])
          , ("full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool])
          , ("full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hsg129 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf135 hn0 hg129 (by decide)
      · exact hsg124 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf135 hn0 hg124 (by decide)
      · exact hsg133 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf135 hn0 hg133 (by decide)
      · exact hsg130 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf135 hn0 hg130 (by decide)
    · have hc : fidBvaScanCandsFn.checkCallsOk [] [] = true := by rfl
      exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h)) hc
    · have hn0 : f.name = "full_bva_filter_row" := hnm.symm
      have hp : fidPatchInsAt fidCorePatchBefores f = [fidBvaMatchLargeFidFn] := by
        unfold fidPatchInsAt; dsimp only [fidCorePatchBefores]; rw [hn0]; rfl
      have hc : fidBvaFilterRowFn.checkCallsOk
          [("full_bva_match_large_fid", [i64, i32, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact List.mem_append_right _ (by rw [hp]; simp [fidBvaMatchLargeFidFn, Fn.sig])
    · have hn0 : f.name = f368.name := hnm.symm.trans (congrArg Prod.fst hs368.symm)
      have hfnm : f.name = "full_reorder_queue_m7" := hnm.symm
      have hp : fidPatchInsAt fidCorePatchBefores f = [fidReorderSiftFidFn] := by
        unfold fidPatchInsAt; dsimp only [fidCorePatchBefores]; rw [hfnm]; rfl
      have hc : fidReorderQueueM7Fn.checkCallsOk
          [ ("full_arena_next", [i64, i32], [i32])
          , ("full_rescale", [i64], [])
          , ("full_heap_up", [i64, i32], [])
          , ("full_reorder_sift_fid", [i64, i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _
          (hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf368 hn0 hg11 (by decide))
      · exact List.mem_append_left _
          (hsg24 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf368 hn0 hg24 (by decide))
      · exact List.mem_append_left _
          (hsg19 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf368 hn0 hg19 (by decide))
      · exact List.mem_append_right _ (by rw [hp]; simp [fidReorderSiftFidFn, Fn.sig])
    · have hn0 : f.name = f369.name := hnm.symm.trans (congrArg Prod.fst hs369.symm)
      have hc : fidReorderM6Fn.checkCallsOk
          [("full_reorder_queue_m7", [i64], [i64])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hs368 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf369 hn0 hf368 (by decide)
    · have hn0 : f.name = f383.name := hnm.symm.trans (congrArg Prod.fst hs383.symm)
      have hc : fidElimBveM7Fn.checkCallsOk
          [ ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_bve_heap_push_m7", [i64, i64, i32], [i64])
          , ("full_bve_heap_pop_m7", [i64, i64], [i32])
          , ("full_bve_collect_nbrs_m7", [i64, i32], [i64])
          , ("full_bve_var_m7", [i64, i32], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact hsg302 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf383 hn0 hg302 (by decide)
      · exact hsg380 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf383 hn0 hg380 (by decide)
      · exact hsg381 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf383 hn0 hg381 (by decide)
      · exact hsg382 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf383 hn0 hg382 (by decide)
      · exact hsg338 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf383 hn0 hg338 (by decide)
    · have hn0 : f.name = f164.name := hnm.symm.trans (congrArg Prod.fst hs164.symm)
      have hc : fidWalkM7Fn.checkCallsOk
          [ ("full_walk_init_vals_m7", [i64], [])
          , ("full_walk_collect_m7", [i64], [i64])
          , ("full_walk_cb_inv_m7", [i64, i64, i64], [i64])
          , ("full_walk_init_table_m7", [i64, i64], [])
          , ("full_walk_build_occ_m7", [i64, i64], [i64])
          , ("full_walk_effort_m7", [i64, i64], [i64])
          , ("full_walk_pick_m7", [i64, i32, i64], [i64])
          , ("full_walk_flip_m7", [i64, i32, i64, i64], [i64])
          , ("full_walk_save_min_m7", [i64, i64, .bool], [])
          , ("full_rng_next", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => List.mem_append_left _ ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg157 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg157 (by decide)
      · exact hsg158 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg158 (by decide)
      · exact hsg154 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg154 (by decide)
      · exact hsg155 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg155 (by decide)
      · exact hsg159 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg159 (by decide)
      · exact hsg156 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg156 (by decide)
      · exact hsg161 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg161 (by decide)
      · exact hsg162 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg162 (by decide)
      · exact hsg163 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg163 (by decide)
      · exact hsg10 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf164 hn0 hg10 (by decide)

private theorem fidPatchFns_length_sum (repls : List Fn) (befores : List (Sym × List Fn)) :
    ∀ (fs : List Fn),
    (fidPatchFns repls befores fs).length =
      fs.length + (fs.map (fun f => (fidPatchInsAt befores f).length)).sum
  | [] => rfl
  | f :: fs => by
    unfold fidPatchFns
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    have ih := fidPatchFns_length_sum repls befores fs
    unfold fidPatchFns at ih; rw [ih]; omega

theorem fidCorePatchedFns_length : fidCorePatchedFns.length = 412 := by
  have hsum : (m7Fns.map (fun f => (fidPatchInsAt fidCorePatchBefores f).length)).sum = 2 := by
    t_kernel_rfl
  unfold fidCorePatchedFns
  rw [fidPatchFns_length_sum, m7Fns_length, hsum]

private theorem fidPatchRowInsAt_filter_ne {a b : Sym} {v : List SpecEntry}
    (hb : (a == b) = false) :
    (if a == b then some v else none) = none := by
  rw [hb]; rfl

private theorem fidCorePatch_rowInsAt_name_cases (e : SpecEntry) :
    fidPatchRowInsAt fidCorePatchRowBefores e = [] ∨
      (e.name = "full_bva_filter_row" ∧
        fidPatchRowInsAt fidCorePatchRowBefores e =
          [⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool],
              fidBvaMatchLargeSpec, true⟩]) ∨
      (e.name = "full_reorder_queue_m7" ∧
        fidPatchRowInsAt fidCorePatchRowBefores e =
          [⟨"full_reorder_sift_fid", [i64, i64, i64], [], fidReorderSiftSpec, true⟩]) := by
  by_cases h1 : e.name = "full_bva_filter_row"
  · right; left
    refine ⟨h1, ?_⟩
    unfold fidPatchRowInsAt; dsimp only [fidCorePatchRowBefores]; rw [h1]; rfl
  · by_cases h2 : e.name = "full_reorder_queue_m7"
    · right; right
      refine ⟨h2, ?_⟩
      unfold fidPatchRowInsAt; dsimp only [fidCorePatchRowBefores]; rw [h2]; rfl
    · left
      have hb1 : ("full_bva_filter_row" == e.name) = false := beq_false_of_ne (Ne.symm h1)
      have hb2 : ("full_reorder_queue_m7" == e.name) = false := beq_false_of_ne (Ne.symm h2)
      unfold fidPatchRowInsAt; dsimp only [fidCorePatchRowBefores]
      rw [List.filterMap_cons, fidPatchRowInsAt_filter_ne hb1,
        List.filterMap_cons, fidPatchRowInsAt_filter_ne hb2]
      rfl

private theorem sig_eq_of_name_eq_m7 (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ∀ r ∈ fidCorePatchRows, ∀ e ∈ m7SpecTable tBve solveSpec,
      r.name = e.name → (r.name, r.as, r.rs) = (e.name, e.as, e.rs) := by
  have hsigs := m7SpecTable_sigs tBve solveSpec hBveSigs
  intro r hr e he hnm
  obtain ⟨k, hk_lt, hkeq⟩ := List.mem_iff_getElem.mp he
  have hk_fn : k < m7Fns.length := by
    have hl := congrArg List.length hsigs
    simp only [List.length_map] at hl; omega
  have hsig_k : (e.name, e.as, e.rs) = m7Fns[k].sig := by
    have hget := congrArg (·[k]?) hsigs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk_lt,
      List.getElem?_eq_getElem hk_fn, Option.map_some, Option.some.injEq] at hget
    simpa [hkeq] using hget
  have hf_mem : m7Fns[k] ∈ m7Fns := List.getElem_mem hk_fn
  rcases List.mem_iff_getElem.mp hr with ⟨j, hj, rfl⟩
  have hrl : fidCorePatchRows.length = 7 := rfl
  have hfl : fidCorePatchFns.length = 7 := rfl
  have hjf : j < fidCorePatchFns.length := by omega
  have hr_fn : fidCorePatchFns[j].sig =
      (fidCorePatchRows[j].name, fidCorePatchRows[j].as, fidCorePatchRows[j].rs) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hf_r : fidCorePatchFns[j] ∈ fidCorePatchFns := List.getElem_mem hjf
  have hr_name : (fidCorePatchFns[j]).name = m7Fns[k].name := by
    have hn1 : (fidCorePatchFns[j]).sig.1 = fidCorePatchRows[j].name := congrArg Prod.fst hr_fn
    exact hn1.trans (hnm.trans (congrArg Prod.fst hsig_k))
  have hfsig := fidCorePatch_sigs _ hf_r _ hf_mem hr_name
  exact hr_fn.symm.trans (hfsig.trans hsig_k.symm)

theorem fidCorePatchedSpecTable_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (fidCorePatchedSpecTable tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      fidCorePatchedFns.map Fn.sig := by
  refine fidPatchRows_sigs (m7SpecTable tBve solveSpec) m7Fns
    (m7SpecTable_sigs tBve solveSpec hBveSigs)
    (sig_eq_of_name_eq_m7 tBve solveSpec hBveSigs) fidCorePatch_sigs ?_
  intro e _ f _ hnm
  rcases fidCorePatch_rowInsAt_name_cases e with h1 | ⟨he1, hp1⟩ | ⟨he1, hp1⟩
  · rcases fidCorePatch_insAt_name_cases f with h2 | ⟨he2, _⟩ | ⟨he2, _⟩
    · rw [h1, h2]; rfl
    · exfalso
      have heeq : e.name = "full_bva_filter_row" := hnm.trans he2
      unfold fidPatchRowInsAt at h1; dsimp only [fidCorePatchRowBefores] at h1
      rw [heeq] at h1; cases h1
    · exfalso
      have heeq : e.name = "full_reorder_queue_m7" := hnm.trans he2
      unfold fidPatchRowInsAt at h1; dsimp only [fidCorePatchRowBefores] at h1
      rw [heeq] at h1; cases h1
  · rcases fidCorePatch_insAt_name_cases f with h2 | ⟨_, hp2⟩ | ⟨he2, _⟩
    · exfalso
      have hfeq : f.name = "full_bva_filter_row" := hnm.symm.trans he1
      unfold fidPatchInsAt at h2; dsimp only [fidCorePatchBefores] at h2
      rw [hfeq] at h2; cases h2
    · rw [hp1, hp2]; rfl
    · exfalso; exact absurd (he1.symm.trans (hnm.trans he2)) (by decide)
  · rcases fidCorePatch_insAt_name_cases f with h2 | ⟨he2, _⟩ | ⟨_, hp2⟩
    · exfalso
      have hfeq : f.name = "full_reorder_queue_m7" := hnm.symm.trans he1
      unfold fidPatchInsAt at h2; dsimp only [fidCorePatchBefores] at h2
      rw [hfeq] at h2; cases h2
    · exfalso; exact absurd (he1.symm.trans (hnm.trans he2)) (by decide)
    · rw [hp1, hp2]; rfl

theorem fidCorePatchedSpecTable_nodup (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ((fidCorePatchedSpecTable tBve solveSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (fidCorePatchedSpecTable_sigs tBve solveSpec hBveSigs)
  simp only [List.map_map, Function.comp_def, Fn.sig] at hm
  exact hm ▸ fidCorePatchedFns_names_nodup

theorem fidCorePatchedSpecTable_noExit (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    (fidCorePatchedSpecTable tBve solveSpec).all SpecEntry.noExit = true := by
  refine fidPatchRows_noExit (m7SpecTable_noExit tBve solveSpec hBveNoExit) (by rfl) ?_
  intro p hp
  simp only [fidCorePatchRowBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> rfl

private theorem m7SpecTable_ne_ins {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {e : SpecEntry} (he : e ∈ m7SpecTable tBve solveSpec) :
    e.name ≠ "full_bva_match_large_fid" ∧ e.name ≠ "full_reorder_sift_fid" := by
  have hs := congrArg (List.map Prod.fst) (m7SpecTable_sigs tBve solveSpec hBveSigs)
  simp only [List.map_map, Function.comp_def, Fn.sig] at hs
  have hmem : e.name ∈ m7Fns.map Fn.name :=
    hs ▸ List.mem_map_of_mem (f := SpecEntry.name) he
  exact ⟨fun h => m7Fns_not_mem_bml (h ▸ hmem), fun h => m7Fns_not_mem_sift (h ▸ hmem)⟩

private theorem elimFidPatched_of_m7 {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {e : SpecEntry} (he : e ∈ m7SpecTable tBve solveSpec)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : mkFidCorePatchedEnv tBve solveSpec e.name e.as e.rs xs m Q X) :
    e.eff xs m Q X := by
  rcases h with h_ins | ⟨_, _, h_m7⟩
  · exfalso
    rcases envOfTable_elim h_ins with ⟨e₀, he₀, hnm, _, _, _⟩
    have hne := m7SpecTable_ne_ins hBveSigs he
    simp only [fidCoreInsRows, List.mem_cons, List.not_mem_nil, or_false] at he₀
    rcases he₀ with rfl | rfl
    · exact absurd hnm.symm hne.1
    · exact absurd hnm.symm hne.2
  · exact mkM7Env_elim_of_mem he (m7SpecTable_nodup tBve solveSpec hBveSigs) h_m7

/-- `ModuleOk` for `fidCorePatchedModule` (`412` fns = `FullM7.m7Module` patched with all `7`
Target A Core replacements + `2` inserted helpers), preserving `m7SpecTable` `Spec`s cleanly. -/
theorem fidCorePatched_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve solveSpec)) :
    ModuleOk (mkFidCorePatchedEnv tBve solveSpec) fidCorePatchedModule := by
  have hm := mkM7Env_moduleOk tBve solveSpec hWeaken hSolveMonoX
    hBveSigs hBveNoExit hBveSpecs hBveOk
  have hndM := m7SpecTable_nodup tBve solveSpec hBveSigs
  have hc1 := m7Part1Callees_of_sub (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2p := m7Part2PfxCallees_of_sub (m7SpecTable_part2_mem (tBve := tBve)
    (solveSpec := solveSpec))
  have hc3p := m7Part3PfxCallees_of_sub (m7SpecTable_part3Pfx_mem (tBve := tBve)
    (solveSpec := solveSpec))
  let Γ' := mkFidCorePatchedEnv tBve solveSpec
  let rowMX (f : Sym) (as bs : List Ty) (sp : Spec as bs)
      (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec)
      (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
      ∀ xs m Q X, sp xs m Q X → Γ' f as bs xs m Q X :=
    let hne := m7SpecTable_ne_ins hBveSigs hmem
    fun xs m Q X hs => Or.inr ⟨hne.1, hne.2,
      mkM7Env_row_mem hndM f as bs sp hmem hno xs m Q X hs⟩
  have hBml : ∀ xs m Q X, fidBvaMatchLargeSpec xs m Q X →
      Γ' "full_bva_match_large_fid" [i64, i32, i32, i32] [.bool] xs m Q X :=
    fun xs m Q X h => Or.inl (fidRowMem fidCoreInsRows_nodup _ _ _ _
      List.mem_cons_self (fun _ _ _ _ hx => fidBvaMatchLargeSpec_monoX hx) xs m Q X h)
  have hSift : ∀ xs m Q X, fidReorderSiftSpec xs m Q X →
      Γ' "full_reorder_sift_fid" [i64, i64, i64] [] xs m Q X :=
    fun xs m Q X h => Or.inl (fidRowMem fidCoreInsRows_nodup _ _ _ _
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ _ _ _ hx => fidReorderSiftSpec_monoX hx) xs m Q X h)
  have hMinShrink : ∀ a m Q X, Γ' "full_min_shrink_m6" [i64] [] a m Q X →
      Func.wp Γ' full_min_shrink_fid_body a m Q X := by
    intro a m Q X hs
    have hsp := elimFidPatched_of_m7 hBveSigs hc2p.minShrinkM6 hs
    dsimp only [SpecEntry.eff] at hsp
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (full_min_shrink_fid_wp Γ'
        (rowMX _ _ _ _ hBridge.sortTmp
          (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h))
        (rowMX _ _ _ _ hBridge.minMark (fun _ _ _ _ h => h))
        (rowMX _ _ _ _ hBridge.minLitDfs
          (fun _ _ _ _ h => FullM6MinShrink.m6MinLitDfsSpec_monoX h))
        (rowMX _ _ _ _ hBridge.shrinkBlkBool
          (fun _ _ _ _ h => FullM6MinShrink.m6ShrinkBlkBoolSpec_monoX h))
        a m Q _ hsp)
  refine fidPatchModule_moduleOk hm fidCorePatched_acyclic fidCorePatchFns_wf
    fidCorePatchBefores_wf ?_ ?_ ?_ ?_
  · intro f as bs hf xs m Q X h
    simp only [m7Module, List.map_nil, List.append_nil] at hf
    have hfn : f ∈ m7Fns.map Fn.name := by
      rcases List.mem_map.mp hf with ⟨g, hg, hsig⟩
      have hgn : g.name = f := congrArg Prod.fst hsig
      rw [← hgn]; exact List.mem_map_of_mem hg
    exact Or.inr ⟨fun hn => m7Fns_not_mem_bml (hn ▸ hfn),
      fun hn => m7Fns_not_mem_sift (hn ▸ hfn), h⟩
  · intro g hg _
    refine Or.inr fun xs m Q X h => ?_
    rcases h with h_ins | ⟨_, _, h_m7⟩
    · exfalso
      rcases envOfTable_elim h_ins with ⟨e₀, he₀, hnm, _, _, _⟩
      simp only [fidCoreInsRows, List.mem_cons, List.not_mem_nil, or_false] at he₀
      rcases he₀ with rfl | rfl
      · exact m7Fns_not_mem_bml (by
          dsimp only at hnm; rw [hnm]; exact List.mem_map_of_mem hg)
      · exact m7Fns_not_mem_sift (by
          dsimp only at hnm; rw [hnm]; exact List.mem_map_of_mem hg)
    · exact h_m7
  · intro r hr xs m Q X hs
    simp only [fidCorePatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hMinShrink xs m Q X hs
    · have hsp := elimFidPatched_of_m7 hBveSigs hBridge.bvaScanCands hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_bva_scan_cands_fid_wp Γ' xs m Q _ hsp)
    · have hsp := elimFidPatched_of_m7 hBveSigs hBridge.bvaFilterRow hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_bva_filter_row_fid_wp Γ' hBml xs m Q _ hsp)
    · have hsp := elimFidPatched_of_m7 hBveSigs hc3p.reorderQueueM7 hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_reorder_queue_fid_wp Γ'
          (rowMX _ _ _ _ hc1.arenaNext (fun _ _ _ _ h => h))
          (rowMX _ _ _ _ (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.rescale)
            (fun _ _ _ _ h => h))
          (rowMX _ _ _ _ hBridge.heapUp (fun _ _ _ _ h => h)) hSift xs m Q _ hsp)
    · have hsp := elimFidPatched_of_m7 hBveSigs
        (m7SpecTable_pfx_mem _ m7OrchPfxRows_specs.reorderM6) hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_reorder_fid_wp Γ'
          (rowMX _ _ _ _ hc3p.reorderQueueM7 (fun _ _ _ _ h => h)) xs m Q _ hsp)
    · have hsp := elimFidPatched_of_m7 hBveSigs
        (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.elimBve) hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_elim_bve_fid_wp Γ'
          (rowMX _ _ _ _ (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.denseFlush)
            FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
          (rowMX _ _ _ _ (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.bvePush)
            FullM6BveFwd.fullBveHeapPushM6Spec_noExit)
          (rowMX _ _ _ _ (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.bvePop)
            FullM6BveFwd.fullBveHeapPopM6Spec_noExit)
          (rowMX _ _ _ _ (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.bveNbrs)
            (fun _ _ _ _ h => h))
          (rowMX _ _ _ _ (m7SpecTable_tBve_mem hBveSigs _ hCoreBve.bveVar)
            (fun _ _ _ _ h => h))
          xs m Q _ hsp)
    · have hsp := elimFidPatched_of_m7 hBveSigs hBridge.walkM7 hs
      dsimp only [SpecEntry.eff] at hsp
      exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
        (full_walk_fid_wp Γ'
          (rowMX _ _ _ _ hBridge.walkInitVals
            (fun _ _ _ _ h => FullM7Walk.m7InitValsSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkCollect
            (fun _ _ _ _ h => FullM7Walk.m7CollectSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkCbInv
            (fun _ _ _ _ h => FullM7Walk.m7CbInvSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkInitTable
            (fun _ _ _ _ h => FullM7Walk.m7InitTableSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkBuildOcc
            (fun _ _ _ _ h => FullM7Walk.m7BuildOccSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkEffort
            (fun _ _ _ _ h => FullM7Walk.m7EffortSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkPick
            (fun _ _ _ _ h => FullM7Walk.m7PickSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkFlip
            (fun _ _ _ _ h => FullM7Walk.m7FlipSpec_noExit h))
          (rowMX _ _ _ _ hBridge.walkSaveMin
            (fun _ _ _ _ h => FullM7Walk.m7SaveMinSpec_noExit h))
          (rowMX _ _ _ _ hc1.rngNext (fun _ _ _ _ h => h)) xs m Q _ hsp)
  · intro p hp h hh xs m Q X hs
    simp only [fidCorePatchBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [List.mem_singleton] at hh <;> subst hh
    · rcases hs with h_ins | ⟨hne, _, _⟩
      · have hsp := env_ofTable_elim_of_mem List.mem_cons_self fidCoreInsRows_nodup h_ins
        dsimp only [SpecEntry.eff] at hsp
        exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
          (full_bva_match_large_fid_wp Γ' xs m Q _ hsp)
      · exact False.elim (hne rfl)
    · rcases hs with h_ins | ⟨_, hne, _⟩
      · have hsp := env_ofTable_elim_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
          fidCoreInsRows_nodup h_ins
        dsimp only [SpecEntry.eff] at hsp
        exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
          (full_reorder_sift_fid_wp Γ' xs m Q _ hsp)
      · exact False.elim (hne rfl)

theorem fidCorePatched_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ fidCorePatchedModule.fns :=
  fidPatchFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => by
    simp only [fidCorePatchFns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem fidCorePatched_solveBytes_row
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : solveSpec a m Q X) :
    mkFidCorePatchedEnv tBve solveSpec "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64] a m Q X :=
  Or.inr ⟨by decide, by decide,
    (mkM7Env_solve_bytes_iff tBve solveSpec hBveSigs).mpr (hSolveMonoX a m Q X _ hs)⟩

/-- Top-level `kissat_solve_bytes` soundness for the `412`-function `fidCorePatchedModule` (`7`
Target A Core replacements + `2` helpers spliced into `FullM7.m7Module`). -/
theorem fidCorePatched_solve_bytes_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve fullM6SolveBytesSpec))
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkFidCorePatchedEnv tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  spliceModule_solve_bytes_sound
    (fidCorePatched_moduleOk tBve fullM6SolveBytesSpec
      (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
      (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk hCoreBve hBridge)
    fidCorePatched_solveBytes_mem
    (fun _ _ _ _ hs =>
      fidCorePatched_solveBytes_row tBve fullM6SolveBytesSpec hBveSigs
        (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h) hs)
    hcfit hwfit hm

/-- Concrete deterministic UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for the
`412`-function `fidCorePatchedModule`. -/
theorem fidCorePatched_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve)
    (hCoreBve : FidCoreBveCallees tBve)
    (hBridge : FidCoreM7BridgeRows (m7SpecTable tBve fullM6SolveBytesCoreModelSpec)) :
    Func.wp (mkFidCorePatchedEnv tBve fullM6SolveBytesCoreModelSpec)
      FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  spliceModule_unsat_nv
    (fidCorePatched_moduleOk tBve fullM6SolveBytesCoreModelSpec
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk hCoreBve hBridge)
    fidCorePatched_solveBytes_mem
    (fun _ _ _ _ hs =>
      fidCorePatched_solveBytes_row tBve fullM6SolveBytesCoreModelSpec hBveSigs
        (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h) hs)

end M7SpliceSection

end LeanQbe.T.Examples.Kissat.FullM7FidelityCore