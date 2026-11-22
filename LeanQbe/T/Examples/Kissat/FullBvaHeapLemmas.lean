module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Examples.Kissat.FullBvaHeapCommitSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas1
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas2
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas4a
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas4b
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas4
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas5
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas6
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Max-Degree Binary Heap Factoring — Packaging & Non-Vacuity

Re-exports per-function `Func.wp` proofs from parallel shards `FullBvaHeapLemmas{1..6,4a,4b}`,
assembles `full_bva_commit_wp`, `bvaHeapSpecTable`, `bvaHeapEnv`,
`bvaHeap_moduleOk : ModuleOk bvaHeapEnv bvaHeapModule`, and concrete `Mem 64` UNSAT non-vacuity.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics
open FullBvaHeapHelpers
open FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-- Closed `Func.wp` contract for `full_bva_commit` assembled from parallel commit sub-proofs. -/
theorem full_bva_commit_wp (Γ : Env)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullBvaCommitSpec args m Q X →
      Func.wp Γ full_bva_commit_body args m Q X :=
  full_bva_commit_wp_of Γ hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
    (fun {_ _} => commit_del_loop_wp hDelBin hUnwatch)
    (fun {_ _} => commit_large_top_wp hAllocCl hWPush)
    (fun {_ _} => commit_tail_wp hAddBin)

/-! ## 5. Closed `bvaHeapEnv` & `bvaHeap_moduleOk` -/

/-- Specification table matching `bvaHeap_fns` (`13` rows) plus the `6` canonical `Full` externs
(`full_alloc_cl`, `full_wstack_defrag`, `full_watch_push`, `full_unwatch_large`, `full_add_bin`,
`full_delete_binary`). -/
@[expose] def bvaHeapSpecTable : List SpecEntry :=
  [ ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], fullBvaHop3Spec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], fullBvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], fullBvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], fullBvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  ]

/-- Closed specification environment for `bvaHeapModule`. -/
@[expose] def bvaHeapEnv : Env := Env.ofTable bvaHeapSpecTable

theorem bvaHeapSpecTable_names_nodup : (bvaHeapSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem bvaHeapSpecTable_noExit : ∀ e ∈ bvaHeapSpecTable, e.noExit = true := by
  intro e he
  have hall : bvaHeapSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem bvaHeapEnv_noExit :
    ∀ f as bs xs m Q X X', bvaHeapEnv f as bs xs m Q X → bvaHeapEnv f as bs xs m Q X' :=
  Env.ofTable_noExit bvaHeapSpecTable_noExit

private theorem bvaHeapEnv_mem {e : SpecEntry} (he : e ∈ bvaHeapSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : e.spec xs m Q (fun _ _ _ _ => False)) : bvaHeapEnv e.name e.as e.rs xs m Q X := by
  have hno := bvaHeapSpecTable_noExit e he
  exact Env.ofTable_of_mem he bvaHeapSpecTable_names_nodup
    (by simp only [SpecEntry.eff, hno, ↓reduceIte]; exact h)

private theorem bvaHeap_allFns_wf : AllFns Fn.Wf bvaHeapModule.fns :=
  ⟨full_init_fresh_var_wf, full_bva_hop1_wf, full_bva_hop2_wf, full_bva_hop3_wf,
   full_bva_match_large_wf, full_bva_scan_cands_wf, full_bva_pick_cand_wf,
   full_bva_filter_row_wf, full_bva_commit_wf, full_bva_try_lit_wf,
   full_fheap_up_wf, full_fheap_down_wf, full_factor_wf, trivial⟩

/-- Closed `ModuleOk` theorem for all `13` 3-hop BVA & binary-heap factoring functions in
`bvaHeapModule`, parameterized over `full_bva_commit_wp`. -/
theorem bvaHeap_moduleOk_of_commit
    (hCommitWp : ∀ (Γ : Env),
      (∀ xs m Q X, fullWstackDefragSpec xs m Q X → Γ "full_wstack_defrag" [i64] [] xs m Q X) →
      (∀ xs m Q X, fullInitFreshVarHeapSpec xs m Q X →
        Γ "full_init_fresh_var" [i64, i32] [] xs m Q X) →
      (∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X) →
      (∀ xs m Q X, fullAllocClSpec xs m Q X →
        Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X) →
      (∀ xs m Q X, fullWatchPushSpec xs m Q X →
        Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X) →
      (∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
        Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X) →
      (∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
        Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X) →
      ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
        Func.wp Γ full_bva_commit_body xs m Q X) :
    ModuleOk bvaHeapEnv bvaHeapModule := by
  refine Env.ofTable_moduleOk bvaHeap_acyclic bvaHeap_allFns_wf ?_
  have hInit : ∀ xs m Q X, fullInitFreshVarHeapSpec xs m Q X →
      bvaHeapEnv "full_init_fresh_var" [i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_init_fresh_var", [i64, i32], [],
      fullInitFreshVarHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop1 : ∀ xs m Q X, fullBvaHop1Spec xs m Q X →
      bvaHeapEnv "full_bva_hop1" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop1", [i64, i32, i32], [i64],
      fullBvaHop1Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop2 : ∀ xs m Q X, fullBvaHop2Spec xs m Q X →
      bvaHeapEnv "full_bva_hop2" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop2", [i64, i32, i32], [i64],
      fullBvaHop2Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop3 : ∀ xs m Q X, fullBvaHop3Spec xs m Q X →
      bvaHeapEnv "full_bva_hop3" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop3", [i64, i32, i32], [i64],
      fullBvaHop3Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hMatch : ∀ xs m Q X, fullBvaMatchLargeSpec xs m Q X →
      bvaHeapEnv "full_bva_match_large" [i64, i32, i32, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      fullBvaMatchLargeSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hScan : ∀ xs m Q X, fullBvaScanCandsSpec xs m Q X →
      bvaHeapEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      fullBvaScanCandsSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hPick : ∀ xs m Q X, fullBvaPickCandSpec xs m Q X →
      bvaHeapEnv "full_bva_pick_cand" [i64, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
      fullBvaPickCandSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hFilter : ∀ xs m Q X, fullBvaFilterRowSpec xs m Q X →
      bvaHeapEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32],
      [i32], fullBvaFilterRowSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hCommit : ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
      bvaHeapEnv "full_bva_commit" [i64, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      fullBvaCommitSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hTryLit : ∀ xs m Q X, fullBvaTryLitHeapSpec xs m Q X →
      bvaHeapEnv "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hUp : ∀ xs m Q X, fullFheapUpSpec xs m Q X →
      bvaHeapEnv "full_fheap_up" [i64, i64, i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDown : ∀ xs m Q X, fullFheapDownSpec xs m Q X →
      bvaHeapEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
      fullFheapDownSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hAllocCl : ∀ xs m Q X, fullAllocClSpec xs m Q X →
      bvaHeapEnv "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64],
      fullAllocClSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      bvaHeapEnv "full_wstack_defrag" [i64] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_wstack_defrag", [i64], [],
      fullWstackDefragSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hWPush : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      bvaHeapEnv "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      fullWatchPushSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hUnwatch : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      bvaHeapEnv "full_unwatch_large" [i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_unwatch_large", [i64, i32, i32], [],
      fullUnwatchLargeSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hAddBin : ∀ xs m Q X, fullAddBinSpec xs m Q X →
      bvaHeapEnv "full_add_bin" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_add_bin", [i64, i32, i32], [i64],
      fullAddBinSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      bvaHeapEnv "full_delete_binary" [i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_delete_binary", [i64, i32, i32], [],
      fullDeleteBinarySpec, true⟩) (by simp [bvaHeapSpecTable]) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_init_fresh_var_heap_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_hop1_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_hop2_wp bvaHeapEnv hHop1)
  · exact SpecEntry.Impl.of (full_bva_hop3_wp bvaHeapEnv hHop2)
  · exact SpecEntry.Impl.of (full_bva_match_large_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_scan_cands_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_pick_cand_wp bvaHeapEnv hHop3)
  · exact SpecEntry.Impl.of (full_bva_filter_row_wp bvaHeapEnv hMatch)
  · exact SpecEntry.Impl.of (hCommitWp bvaHeapEnv hDefrag hInit hAddBin hAllocCl
      hWPush hDelBin hUnwatch)
  · exact SpecEntry.Impl.of (full_bva_try_lit_wp bvaHeapEnv hScan hPick hFilter hCommit)
  · exact SpecEntry.Impl.of (full_fheap_up_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_fheap_down_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_factor_wp bvaHeapEnv hUp hDown hTryLit)

/-- Closed unconditional `ModuleOk` theorem for all `13` 3-hop BVA & binary-heap factoring
functions in `bvaHeapModule` against canonical `FullSpec2`/`FullSpec3` external contracts. -/
theorem bvaHeap_moduleOk : ModuleOk bvaHeapEnv bvaHeapModule :=
  bvaHeap_moduleOk_of_commit full_bva_commit_wp

/-! ## 6. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

section ConcreteUnsatNonVacuity

/-- Concrete dense-mode UNSAT state (`dense_mode = 1`, `inconsistent = 1`) on `nvOneLitCfg`
for the UNSAT formula `nvOneLitF0 = {(x0), (¬x0)}`. -/
@[expose] def nvBvaDenseState : FullState :=
  { nvOneLitState with
    core := { nvOneLitState.core with dense_mode := 1#64, inconsistent := 1#64 } }

/-- Concrete `1756`-byte arena image encoding `nvOneLitCfg` and `nvBvaDenseState`. -/
@[expose] def nvBvaDenseBytes : List UInt8 :=
  (bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvOneLitCfg nvBvaDenseState)) ++
    nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++ nvBlockWvec ++ nvBlockTail

/-- Concrete `Mem 64` heap mapped at `nvOneLitCfg.hdr` (`0x1000#64`). -/
@[expose] def nvBvaDenseMem : Mem 64 := nvBvaDenseBytes.At nvOneLitCfg.hdr

theorem nvBvaDenseBytes_length : nvBvaDenseBytes.length = 1756 := by
  simp only [nvBvaDenseBytes, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec,
    nvBlockTail, nvBvaDenseState, nvOneLitState, nvOneLitScratch, List.length_append,
    List.length_replicate, bytesOf_length, bytes64_length, Full.hdrTailWords_length,
    List.length_cons, List.length_nil]
  decide

private theorem array64_unique {a : BitVec 64} {xs : List (BitVec 64)} {m1 m2 : Mem 64}
    (h1 : array64 a xs m1) (h2 : array64 a xs m2) : m1 = m2 := by
  induction xs generalizing a m1 m2 with
  | nil => exact h1.trans h2.symm
  | cons x xs ih =>
    obtain ⟨p1, q1, rfl, _, hp1, hq1⟩ := h1
    obtain ⟨p2, q2, rfl, _, hp2, hq2⟩ := h2
    rw [hp1.symm.trans hp2, ih hq1 hq2]

private theorem union_cancel_left {m1 m2 m2' : Mem 64}
    (hu : m1.union m2 = m1.union m2') (hd1 : m1.inter m2 = ∅) (hd2 : m1.inter m2' = ∅) :
    m2 = m2' := by
  apply ExtHashMap.ext_getElem?; intro k
  have h1 := congrArg (·[k]?) hu; simp only [union_eq, getElem?_union] at h1
  have d1 := eq_empty_iff_forall_not_mem.mp hd1 k
  have d2 := eq_empty_iff_forall_not_mem.mp hd2 k
  simp only [inter_eq, mem_inter_iff] at d1 d2
  cases hm1 : m1[k]? with
  | none => simpa only [hm1, Option.or_none] using h1
  | some _ =>
    have hmem : k ∈ m1 := mem_iff_isSome_getElem?.mpr (by simp [hm1])
    have hn1 : m2[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d1 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    have hn2 : m2'[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d2 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    rw [hn1, hn2]

theorem nvBvaDenseMem_ok : FullMem nvOneLitCfg nvBvaDenseState nvBvaDenseMem := by
  let c := nvOneLitCfg; let s := nvBvaDenseState
  let bHdr0 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c nvOneLitState)
  let bHdr1 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c s)
  let bRest := nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++
    nvBlockWvec ++ nvBlockTail
  have hhdr_len0 : bHdr0.length = 1152 := by
    simp only [bHdr0, List.length_append, bytes64_length, Full.hdrTailWords_length]; decide
  have hrest_len : bRest.length = 604 := by
    simp only [bRest, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec,
      nvBlockTail, nvOneLitState, nvOneLitScratch, List.length_append, List.length_replicate,
      bytesOf_length, bytes64_length, List.length_cons, List.length_nil]
    decide
  have hHdr0 : bHdr0.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) (bHdr0.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hHdr1 : bHdr1.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (bHdr1.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hmem0 : FullMem c nvOneLitState ((bHdr0 ++ bRest).At c.hdr) := by
    have h0 := nvOneLitMem_ok
    unfold nvOneLitMem nvOneLitBytes nvBlockHdr at h0
    simpa only [bHdr0, bRest, List.append_assoc] using h0
  have hsep0 : ((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) ⋆
      (FullCoreArrays c nvOneLitState.core ⋆ FullScratchArrays c nvOneLitState.scratch ⋆ c.pad))
      ((bHdr0 ++ bRest).At c.hdr) := by
    unfold FullMem at hmem0; exact sep_ac hmem0
  have hEqRest : (FullCoreArrays c nvOneLitState.core ⋆
      FullScratchArrays c nvOneLitState.scratch ⋆ c.pad) (bRest.At (c.hdr + 1152#64)) := by
    have hsplit := congrFun (Mem.At_append_sep bHdr0 bRest c.hdr (by omega))
      ((bHdr0 ++ bRest).At c.hdr)
    have hm12 := hsplit.mp rfl
    obtain ⟨m1, m2, huni, hdisj, ⟨a1, b1, rfl, _, ha1, hb1⟩, hm2⟩ := hsep0
    obtain ⟨m1', m2', huni', hdisj', rfl, rfl⟩ := hm12
    obtain ⟨a0, b0, h0_eq, _, ha0, hb0⟩ := hHdr0.2
    have ha_eq : a1 = a0 := array64_unique (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) ha1 ha0
    have hb_eq : b1 = b0 :=
      array64_unique (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) hb1 hb0
    have hm1_eq : a1.union b1 = bHdr0.At c.hdr := by rw [ha_eq, hb_eq, h0_eq]
    rw [hm1_eq] at huni hdisj
    have hm2_eq : m2 = bRest.At (c.hdr + BitVec.ofNat 64 bHdr0.length) :=
      union_cancel_left (huni.trans huni'.symm) hdisj hdisj'
    rw [hm2_eq, hhdr_len0] at hm2; exact hm2
  have hfin := nv_join_pair hHdr1 ⟨hrest_len, hEqRest⟩ (by decide) (by decide)
  have hfin' : FullMem c s ((bHdr1 ++ bRest).At c.hdr) := by
    unfold FullMem; exact sep_ac hfin.2
  simpa only [nvBvaDenseMem, nvBvaDenseBytes, bHdr1, bRest, List.append_assoc] using hfin'

theorem nvBvaDense_invW :
    FullDenseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvBvaDenseState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvBvaDenseState.core.cur_vars = 1 := rfl
  have hte : nvBvaDenseState.core.trail_end = 1 := rfl
  have hcl : nvBvaDenseState.core.cur_level = 0 := rfl
  have hdm : nvBvaDenseState.core.dense_mode ≠ 0#64 := by decide
  have hrefs : fullArenaClauseRefsCore nvBvaDenseState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvBvaDenseState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvBvaDenseState, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvBvaDenseState, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvBvaDenseState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun _ => nvDeduceF0_unsat
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvBvaDenseState, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨⟨{ nvOneLit_lengths.core_ok with vals_len := nvOneLit_lengths.core_ok.vals_len },
      nvOneLit_lengths.scratch_ok⟩, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvBvaDenseState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl, hdm⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvBvaDenseState = [] := rfl; simp [this] at hr

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_factor`. -/
theorem nv_bva_factor :
    Func.wp bvaHeapEnv full_factor_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hUp : ∀ xs m Q X, fullFheapUpSpec xs m Q X →
      bvaHeapEnv "full_fheap_up" [i64, i64, i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDown : ∀ xs m Q X, fullFheapDownSpec xs m Q X →
      bvaHeapEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
      fullFheapDownSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hTryLit : ∀ xs m Q X, fullBvaTryLitHeapSpec xs m Q X →
      bvaHeapEnv "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_factor_wp bvaHeapEnv hUp hDown hTryLit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, hm,
      fun r s' m' hd _ _ hr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_try_lit`. -/
theorem nv_bva_try_lit :
    Func.wp bvaHeapEnv full_bva_try_lit_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hScan : ∀ xs m Q X, fullBvaScanCandsSpec xs m Q X →
      bvaHeapEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      fullBvaScanCandsSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hPick : ∀ xs m Q X, fullBvaPickCandSpec xs m Q X →
      bvaHeapEnv "full_bva_pick_cand" [i64, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
      fullBvaPickCandSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hFilter : ∀ xs m Q X, fullBvaFilterRowSpec xs m Q X →
      bvaHeapEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32],
      [i32], fullBvaFilterRowSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hCommit : ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
      bvaHeapEnv "full_bva_commit" [i64, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      fullBvaCommitSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_try_lit_wp bvaHeapEnv hScan hPick hFilter hCommit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, by decide, hm,
      fun _ s' m' hd _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_init_fresh_var`. -/
theorem nv_bva_init_fresh_var :
    Func.wp bvaHeapEnv full_init_fresh_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun () m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ s'.core.vals[0]?.getD 1#8 = 0#8 ∧
        s'.core.vals[1]?.getD 1#8 = 0#8 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_init_fresh_var_heap_wp bvaHeapEnv _ _ _ _
    ⟨nvOneLitCfg, nvBvaDenseState, emp, rfl, nvBvaDense_invW.1, by decide, hm,
      fun _ _ _ _ _ _ _ _ m' hlen _ _ _ _ _ _ hv0 hv1 _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hv0, hv1, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop3`. -/
theorem nv_bva_hop3 :
    Func.wp bvaHeapEnv full_bva_hop3_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hHop2 : ∀ xs m Q X, fullBvaHop2Spec xs m Q X →
      bvaHeapEnv "full_bva_hop2" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop2", [i64, i32, i32], [i64],
      fullBvaHop2Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_hop3_wp bvaHeapEnv hHop2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW,
      by decide, hm, fun _ _ _ _ _ _ m' hnl hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_scan_cands`. -/
theorem nv_bva_scan_cands :
    Func.wp bvaHeapEnv full_bva_scan_cands_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 2#64, ()) nvBvaDenseMem
      (fun (n, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ n.toNat ≤ 2 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_bva_scan_cands_wp bvaHeapEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl, nvBvaDense_invW.1,
      nvBvaDense_invW.2.1, nvBvaDense_invW.2.2.2.1, nvBvaDense_invW.2.2.2.2.1,
      nvBvaDense_invW.2.2.2.2.2.1, nvBvaDense_invW.2.2.2.2.2.2, by decide,
      fun l hl => by rw [nvBvaDense_invW.2.2.1.2 l hl]; decide,
      by decide, by decide, fun _ h => by simp at h, hm,
      fun n _ _ _ m' hlen hn _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hn, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_pick_cand`. -/
theorem nv_bva_pick_cand :
    Func.wp bvaHeapEnv full_bva_pick_cand_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hHop3 : ∀ xs m Q X, fullBvaHop3Spec xs m Q X →
      bvaHeapEnv "full_bva_hop3" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop3", [i64, i32, i32], [i64],
      fullBvaHop3Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_pick_cand_wp bvaHeapEnv hHop3 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW,
      by decide, by decide, fun _ h => by simp at h, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullBvaHeap
