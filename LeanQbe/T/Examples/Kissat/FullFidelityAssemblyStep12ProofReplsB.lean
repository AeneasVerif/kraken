/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofAgree
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofReplsA
import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof0
import LeanQbe.T.Examples.Kissat.FullFidelityStep12CProof
import LeanQbe.T.Examples.Kissat.FullFidelityStep12ProofPurgeDel
import LeanQbe.T.Examples.Kissat.FullM6S15Bridge
import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0

/-!
# Kissat Fidelity Step 12 Replacement & Before Proofs — Part B
(`FullFidelityAssemblyStep12ProofReplsB`)

Per-function `(callsOk, impl)` obligations for:
- Step-12B (`12` repls + `3` befores, with `full_backbone_m6_s12b_del_impl` S1.5 bridge)
- Step-12C (`4` repls + `3` befores, with `full_reduce_purge_c0_del_wp` and
  `renameFuncCalls pr3BtAcMap` on `fid12LearnClauseM6Fn`)
- Step-12A (`5` direct repls)
plus `patchInsAt_fidStep12_cases` (`< 1,000` LOC, `0` `@[expose]` on thms/lemmas, `0` `import all`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityStep11
open LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
open LeanQbe.T.Examples.Kissat.FullFidelityStep12A
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-12B Replacements (`12`) -/

theorem fid12_ok_12b {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fidStep12BRepls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fidStep12BRepls_wf r hr, ?_, ?_⟩
  · simp only [fidStep12BRepls, fidStep12BCongRepls, fidStep12BBveFwdRepls, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine fid12_replCallsOk_at hpreM full_cong_extract_s12b_callsOk fun d hd => ?_
      simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_selfBefore hf0
    · refine fid12_replCallsOk_at hpreM full_cong_and_match_s12b_callsOk fun d hd => ?_
      simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_base hfs hf0 252
    · exact fid12_replCallsOk_at hpreM full_cong_enq_var_s12b_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM full_cong_eval_gate_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 252
      · exact fid12_dep_base hfs hf0 258
      · exact fid12_dep_base hfs hf0 255
      · exact fid12_dep_base hfs hf0 256
      · exact fid12_dep_base hfs hf0 270
      · exact fid12_dep_base hfs hf0 271
      · exact fid12_dep_base hfs hf0 272
    · refine fid12_replCallsOk_at hpreM full_cong_worklist_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_base hfs hf0 252
      · exact fid12_dep_base hfs hf0 273
    · refine fid12_replCallsOk_at hpreM full_congruence_dense_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 267
      · exact fid12_dep_base hfs hf0 268
      · exact fid12_dep_base hfs hf0 291
      · exact fid12_dep_before (ins := fidStep12BCongExtractFromFn) hfs hf0 269
          ("full_cong_extract", [i64, i64, i64], [i64])
          (hins := Or.inr ⟨[fidStep12BCongExtractAndClauseFn, fidStep12BCongExtractFromFn], rfl,
            List.mem_cons_of_mem _ List.mem_cons_self⟩)
      · exact fid12_dep_base hfs hf0 275
      · exact fid12_dep_base hfs hf0 278
    · exact fid12_replCallsOk_at hpreM full_backbone_sched_m6_s12b_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM full_backbone_m6_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 40
      · exact fid12_dep_base hfs hf0 90
      · exact fid12_dep_base hfs hf0 189
      · exact fid12_dep_base hfs hf0 231
      · exact fid12_dep_base hfs hf0 232
      · exact fid12_dep_base hfs hf0 237
      · exact fid12_dep_base hfs hf0 233
    · refine fid12_replCallsOk_at hpreM full_dense_prop_unit_m7_s12b_callsOk fun d hd => ?_
      simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_base hfs hf0 189
    · refine fid12_replCallsOk_at hpreM full_forward_sub_m7_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 353
      · exact fid12_dep_base hfs hf0 355
      · exact fid12_dep_base hfs hf0 361
      · exact fid12_dep_base hfs hf0 356
      · exact fid12_dep_base hfs hf0 359
      · exact fid12_dep_base hfs hf0 360
      · exact fid12_dep_base hfs hf0 11
      · exact fid12_dep_base hfs hf0 357
    · refine fid12_replCallsOk_at hpreM full_bve_commit_res_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 12
      · exact fid12_dep_base hfs hf0 19
      · exact fid12_dep_base hfs hf0 186
      · exact fid12_dep_base hfs hf0 189
    · refine fid12_replCallsOk_at hpreM full_bve_var_m7_s12b_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 363
      · exact fid12_dep_base hfs hf0 390
      · exact fid12_dep_base hfs hf0 387
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 188
      · exact fid12_dep_base hfs hf0 421
      · exact fid12_dep_base hfs hf0 385
      · exact fid12_dep_base hfs hf0 386
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 18
      · exact fid12_dep_base hfs hf0 389
      · exact fid12_dep_base hfs hf0 355
  · simp only [fidStep12BRepls, fidStep12BCongRepls, fidStep12BBveFwdRepls, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongExtractFn.name) =
          some fidStep12BReplRows[0] := rfl
      exact (full_cong_extract_s12b_impl fidStep12Env
        (fid12_frontRow 54 "full_cong_extract_from_fid" step12BCongExtractFromSpec)).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongAndMatchFn.name) =
          some fidStep12BReplRows[1] := rfl
      exact (full_cong_and_match_s12b_impl fidStep12Env fid12_congFind).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongEnqVarFn.name) =
          some fidStep12BReplRows[2] := rfl
      exact (full_cong_enq_var_s12b_impl fidStep12Env).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongEvalGateFn.name) =
          some fidStep12BReplRows[3] := rfl
      exact (full_cong_eval_gate_s12b_impl fidStep12Env fid12_congFind fid12_sortU32
        fid12_congUnitFold fid12_congEquivFold
        (fid12_frontRow 27 "full_cong_and_match" step12BCongAndMatchSpec) fid12_congXorMatch
        (fid12_frontRow 28 "full_cong_enq_var" step12BCongEnqVarSpec)).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongWorklistFn.name) =
          some fidStep12BReplRows[4] := rfl
      exact (full_cong_worklist_s12b_impl fidStep12Env fid12_congFind
        (fid12_frontRow 29 "full_cong_eval_gate" step12BCongEvalGateSpec)).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BCongruenceDenseFn.name) =
          some fidStep12BReplRows[5] := rfl
      exact (full_congruence_dense_s12b_impl fidStep12Env fid12_congExtractBinaries
        fid12_congFindUnitsEquivs fid12_congExtractIteAll
        (fid12_frontRow 54 "full_cong_extract_from_fid" step12BCongExtractFromSpec)
        (fid12_frontRow 30 "full_cong_worklist" step12BCongWorklistSpec) fid12_congFwdSubsume).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BBackboneSchedM6Fn.name) =
          some fidStep12BReplRows[6] := rfl
      exact (full_backbone_sched_m6_s12b_impl fidStep12Env).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BBackboneM6Fn.name) =
          some fidStep12BReplRows[7] := rfl
      exact (full_backbone_m6_s12b_del_impl fidStep12Env
        (fid12_frontRow 17 "full_backtrack" fullBacktrackSpec)
        (s15_to_propagateDel fid12_propagate) fid12_addUnit fid12_prioritizeBinariesM6
        (fid12_frontRow 32 "full_backbone_sched_m6" fullBackboneSchedM6Spec)
        fid12_backboneRoundM6 fid12_backboneKeepM6).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BDensePropUnitM7Fn.name) =
          some fidStep12BReplRows[8] := rfl
      exact (full_dense_prop_unit_m7_s12b_impl fidStep12Env fid12_addUnit).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BForwardSubM7Fn.name) =
          some fidStep12BReplRows[9] := rfl
      exact (full_forward_sub_m7_s12b_impl fidStep12Env fid12_fwdDedupBins fid12_denseFlushUnitsM7
        fid12_fwdCollectSortM7 fid12_fwdFlushLargeM7 fid12_fwdCheckClM7 fid12_fwdConnectSubsumerM7
        fid12_arenaNext fid12_fwdReconnectIrredM7).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BBveCommitResFn.name) =
          some fidStep12BReplRows[10] := rfl
      exact (full_bve_commit_res_s12b_impl fidStep12Env fid12_allocCl fid12_watchPush fid12_addBin
        fid12_addUnit).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12BBveVarM7Fn.name) =
          some fidStep12BReplRows[11] := rfl
      exact (full_bve_var_m7_s12b_impl fidStep12Env fid12_bveCollectM7 fid12_bveExtNeed
        fid12_bveWeaken (fid12_frontRow 55 "full_bve_weaken_unit_fid" fullBveWeakenTmkSpec)
        fid12_setInactive fid12_bveGatesFid fid12_bveGatesM7 fid12_bveResolvePair fid12_assignLvl
        fid12_wstackDefrag (fid12_frontRow 36 "full_bve_commit_res" fullBveCommitResTmkSpec)
        fid12_denseFlushUnitsM7).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

/-! ## 2. Step-12C (`4`) & Step-12A (`5`) Replacements -/

private theorem fid12LearnClauseM6_callsOk :
    fid12LearnClauseM6Fn.checkCallsOk
      [ ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_det_new_level", [i64, i64], [i64])
      , ("full_wstack_defrag", [i64], [])
      , ("full_reduce_m6", [i64, .bool], [i64])
      , ("full_reduce_purge_c0", [i64], [i64])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64])
      , ("full_eager_subsume", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

theorem fid12_ok_12c {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fid12Step12CRepls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fid12Step12CRepls_wf r hr, ?_, ?_⟩
  · simp only [fid12Step12CRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine fid12_replCallsOk_at hpreM fid12c_addClause_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 12
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 19
    · refine fid12_replCallsOk_at hpreM fid12c_sweepCopy_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_before hfs hf0 41 ("full_add_clause", [i64, i32, i32, .bool], [i64])
          (hins := Or.inl rfl)
      · exact fid12_dep_base hfs hf0 19
    · refine fid12_replCallsOk_at hpreM fid12LearnClauseM6_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_before hfs hf0 124 ("full_ana_failed_lit_m6_hdr", [i64], [i64])
          (hins := Or.inl rfl)
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 147
      · exact fid12_dep_base hfs hf0 18
      · exact fid12_dep_base hfs hf0 115
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 41
      · exact fid12_dep_base hfs hf0 149
    · refine fid12_replCallsOk_at hpreM fid12c_vivSortCountsM6_callsOk fun d hd => ?_
      simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_selfBefore hf0
  · simp only [fid12Step12CRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12CAddClauseFn.name) =
          some fidStep12CReplRows[0] := rfl
      exact (fid12c_add_clause_impl fidStep12Env fid12_allocCl fid12_watchPush
        (fid12_frontRow 56 "full_watch_pop_c0" FullM7V2Robust.fullWatchPopC0Spec rfl
          (fun _ _ _ _ h => FullM7V2Robust.fullWatchPopC0Spec_monoX h))).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12CSweepCopyFn.name) =
          some fidStep12CReplRows[1] := rfl
      exact (fid12c_sweep_copy_impl fidStep12Env fid12_assignLvl fid12_watchPush
        (fid12_frontRow 56 "full_watch_pop_c0" FullM7V2Robust.fullWatchPopC0Spec rfl
          (fun _ _ _ _ h => FullM7V2Robust.fullWatchPopC0Spec_monoX h))).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid12LearnClauseM6Fn.name) =
          some fidStep12CReplRows[2] := rfl
      exact (SpecEntry.Impl.of (func_wp_of_renameFuncCalls pr3BtAcMap
        FullFidelityStep12C.full_learn_clause_m6_body full_learn_clause_m6_step12c_wf fidStep12Env
        (full_learn_clause_m6_step12c_wp _
          (fid12_frontRow 52 "full_backtrack_ac_fid" fullBacktrackSpec) fid12_assignLvl
          fid12_detNewLevel fid12_wstackDefrag fid12_reduceM6
          (fid12_frontRow 57 "full_reduce_purge_c0" FullM7V2Robust.fullReducePurgeC0Spec rfl
            (fun _ _ _ _ h => FullM7V2Robust.fullReducePurgeC0Spec_monoX h))
          (fid12_frontRow 38 "full_add_clause" fullAddClauseSpec) fid12_eagerSubsume))).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12CVivSortCountsM6Fn.name) =
          some fidStep12CReplRows[3] := rfl
      exact (fid12c_viv_sort_counts_m6_impl fidStep12Env
        (fid12_frontRow 58 "full_viv_sift_counts_m6" fullVivSiftCountsM6Spec rfl
          (fun _ _ _ _ h => fullVivSiftCountsM6Spec_monoX h))).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fid12_ok_12a {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fidStep12ARepls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fidStep12ARepls_wf r hr, ?_, ?_⟩
  · simp only [fidStep12ARepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact fid12_replCallsOk_at hpreM full_trans_sort_m6_s12a_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM full_m6_sweep_sim_s12a_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 316
      · exact fid12_dep_base hfs hf0 335
      · exact fid12_dep_base hfs hf0 333
      · exact fid12_dep_base hfs hf0 336
    · refine fid12_replCallsOk_at hpreM full_m6_sweep_vars_s12a_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 316
      · exact fid12_dep_base hfs hf0 331
      · exact fid12_dep_base hfs hf0 350
      · exact fid12_dep_base hfs hf0 348
    · refine fid12_replCallsOk_at hpreM full_factor_s12a_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 429
      · exact fid12_dep_base hfs hf0 434
      · exact fid12_dep_base hfs hf0 431
      · exact fid12_dep_base hfs hf0 432
      · exact fid12_dep_base hfs hf0 441
      · exact fid12_dep_base hfs hf0 444
    · refine fid12_replCallsOk_at hpreM full_probe_m6_s12a_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 494
      · exact fid12_dep_base hfs hf0 32
      · exact fid12_dep_base hfs hf0 33
      · exact fid12_dep_base hfs hf0 230
      · exact fid12_dep_base hfs hf0 248
      · exact fid12_dep_base hfs hf0 68
      · exact fid12_dep_base hfs hf0 292
      · exact fid12_dep_base hfs hf0 250
      · exact fid12_dep_base hfs hf0 72
      · exact fid12_dep_base hfs hf0 73
      · exact fid12_dep_base hfs hf0 70
      · exact fid12_dep_base hfs hf0 69
      · exact fid12_dep_base hfs hf0 352
      · exact fid12_dep_base hfs hf0 247
      · exact fid12_dep_base hfs hf0 238
      · exact fid12_dep_base hfs hf0 241
      · exact fid12_dep_base hfs hf0 445
      · exact fid12_dep_base hfs hf0 249
  · simp only [fidStep12ARepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12ATransSortFn.name) =
          some FullFidelityStep12A.fidStep12AReplRows[0] := rfl
      exact (full_trans_sort_m6_s12a_impl fidStep12Env).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12ASweepSimFn.name) =
          some FullFidelityStep12A.fidStep12AReplRows[1] := rfl
      exact (full_m6_sweep_sim_s12a_impl fidStep12Env fid12_m6MaxV fid12_m6SweepSolve
        fid12_m6SweepRefineSig fid12_m6SweepFlipRound).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12ASweepVarsFn.name) =
          some FullFidelityStep12A.fidStep12AReplRows[2] := rfl
      exact (full_m6_sweep_vars_s12a_impl fidStep12Env fid12_m6MaxV fid12_m6DenseProp
        fid12_m6CollectCands fid12_m6SweepVar).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12AFactorFn.name) =
          some FullFidelityStep12A.fidStep12AReplRows[3] := rfl
      exact (full_factor_s12a_impl fidStep12Env fid12_bvaStepsCap fid12_bvaConnectClauses
        fid12_fheapUp fid12_fheapDown fid12_bvaTryLit fid12_bvaUpdLitFid).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12AProbeFn.name) =
          some FullFidelityStep12A.fidStep12AReplRows[4] := rfl
      exact (full_probe_m6_s12a_impl fidStep12Env fid12_probeDticksM6Hdr fid12_log10Q16M7
        fid12_scaleDeltaM5 fid12_vivifyM6Hdr fid12_enterDense fid12_hdrDelaying
        (fid12_frontRow 31 "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
        fid12_rebuildWatchesNosort fid12_hdrGetWatermark fid12_hdrSetWatermark
        fid12_hdrReduceDelay fid12_hdrBumpDelay fid12_sweepDenseM6 fid12_substitute
        (fid12_frontRow 33 "full_backbone_m6" fullBackboneSpec) fid12_transitiveM6
        (fid12_frontRow 45 "full_factor" fullFactorHeapSpec) fid12_sortBinWatches).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

/-! ## 3. `Part B` Befores (`6`) & `patchInsAt_fidStep12_cases` -/

theorem fid12_ok_before_B {fn : Fn} {bPre bPost iPre pre : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hcases :
      (f0.name = "full_cong_extract" ∧ fn = fidStep12BCongExtractAndClauseFn) ∨
      (f0.name = "full_cong_extract" ∧ iPre = [fidStep12BCongExtractAndClauseFn] ∧
        fn = fidStep12BCongExtractFromFn) ∨
      (f0.name = "full_bve_var_m7" ∧ fn = fidStep12BBveWeakenUnitFn) ∨
      (f0.name = "full_add_clause" ∧ fn = fidStep12CWatchPopFn) ∨
      (f0.name = "full_learn_clause_m6" ∧ fn = fidStep12CReducePurgeFn) ∨
      (f0.name = "full_viv_sort_counts_m6" ∧ fn = fidStep12CVivSiftCountsM6Fn))
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++ iPre).map Fn.sig →
      s ∈ pre.map Fn.sig) :
    fn.Wf ∧
    fn.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X,
      fidStep12Env fn.name fn.as fn.rs xs m Q X → Func.wp fidStep12Env fn.body xs m Q X := by
  rcases hcases with ⟨hf0, rfl⟩ | ⟨hf0, rfl, rfl⟩ | ⟨hf0, rfl⟩ |
      ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩
  · refine ⟨fidStep12BBefores_wf _ (by simp [fidStep12BBefores, fidStep12BCongBefores]),
      fid12_befCallsOk_at hpreM full_cong_extract_and_clause_fid_s12b_callsOk
        (fun _ hd => nomatch hd), fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find?
        (·.name == fidStep12BCongExtractAndClauseFn.name) = some fidStep12BBeforeRows[0] := rfl
    exact (full_cong_extract_and_clause_fid_s12b_impl fidStep12Env).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep12BBefores_wf _ (by simp [fidStep12BBefores, fidStep12BCongBefores]),
      fid12_befCallsOk_at hpreM full_cong_extract_from_fid_s12b_callsOk (fun d hd => ?_),
      fun xs m Q X hlk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_befBase hfs hf0 11
      · exact fid12_dep_befBase hfs hf0 265
      · rw [List.map_append, List.mem_append]
        exact Or.inr (List.mem_map_of_mem List.mem_cons_self)
      · exact fid12_dep_befBase hfs hf0 264
      · exact fid12_dep_befBase hfs hf0 263
    · have hfind : fidStep12Bundle.frontTable.find?
          (·.name == fidStep12BCongExtractFromFn.name) = some fidStep12BBeforeRows[1] := rfl
      exact (full_cong_extract_from_fid_s12b_impl fidStep12Env fid12_arenaNext fid12_congCountBins
        (fid12_frontRow 53 "full_cong_extract_and_clause_fid" step12BCongExtractAndClauseSpec)
        fid12_congTryXorIte fid12_congExtractXorK).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep12BBefores_wf _ (by simp [fidStep12BBefores, fidStep12BBveFwdBefores]),
      fid12_befCallsOk_at hpreM full_bve_weaken_unit_fid_s12b_callsOk (fun d hd => ?_),
      fun xs m Q X hlk => ?_⟩
    · simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_befBase hfs hf0 187
    · have hfind : fidStep12Bundle.frontTable.find?
          (·.name == fidStep12BBveWeakenUnitFn.name) = some fidStep12BBeforeRows[2] := rfl
      exact (full_bve_weaken_unit_fid_s12b_impl fidStep12Env fid12_deleteBinary).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep12CBefores_wf _ (by simp [fidStep12CBefores]),
      fid12_befCallsOk_at hpreM fid12c_watchPop_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12CWatchPopFn.name) =
        some fidStep12CBeforeRows[0] := rfl
    exact (fid12c_watch_pop_c0_impl fidStep12Env).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep12CBefores_wf _ (by simp [fidStep12CBefores]),
      fid12_befCallsOk_at hpreM fid12c_reducePurge_callsOk (fun d hd => ?_),
      fun xs m Q X hlk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_befBase hfs hf0 11
      · exact fid12_dep_befBase hfs hf0 40
      · exact fid12_dep_befBase hfs hf0 90
      · exact fid12_dep_befBase hfs hf0 108
      · exact fid12_dep_befBase hfs hf0 109
    · have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep12CReducePurgeFn.name) =
          some fidStep12CBeforeRows[1] := rfl
      have hspec : FullM7V2Robust.fullReducePurgeC0Spec xs m Q (fun _ _ _ _ => False) :=
        env_ofTable_find?_of_append hfind rfl rfl hlk
      rcases xs with ⟨h, ⟨⟩⟩
      exact full_reduce_purge_c0_del_wp fidStep12Env
        (fid12_frontRow 17 "full_backtrack" fullBacktrackSpec)
        (s15_to_propagateDel fid12_propagate) fid12_markReasons fid12_arenaNext
        fid12_arenaSweep h m Q X
          (FullM7V2Robust.fullReducePurgeC0Spec_elim
            (FullM7V2Robust.fullReducePurgeC0Spec_monoX hspec))
  · refine ⟨fidStep12CBefores_wf _ (by simp [fidStep12CBefores]),
      fid12_befCallsOk_at hpreM fid12c_vivSiftCountsM6_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find?
        (·.name == fidStep12CVivSiftCountsM6Fn.name) = some fidStep12CBeforeRows[2] := rfl
    exact (fid12c_viv_sift_counts_m6_impl fidStep12Env).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem patchInsAt_fidStep12_cases {f0 fn : Fn} {iPre iPost : List Fn}
    (hi : patchInsAt fidStep12Befores f0 = iPre ++ fn :: iPost) :
    (f0.name = "full_ingest_cl" ∧ fn = fidStep11ActivateLitFn) ∨
    (f0.name = "full_parse_body_m6" ∧ fn = fidStep11TumbleFinishFn) ∨
    (f0.name = "full_extend" ∧ fn = fidStep11ExtendCoreFn) ∨
    (f0.name = "full_extend" ∧ fn = fidStep11UnpermFn) ∨
    (f0.name = "full_lucky_scan" ∧ fn = fidStep11LuckyOrdFn) ∨
    (f0.name = "full_ana_failed_lit_m6_hdr" ∧ fn = fid11BacktrackAcFn) ∨
    (f0.name = "full_cong_extract" ∧ fn = fidStep12BCongExtractAndClauseFn) ∨
    (f0.name = "full_cong_extract" ∧ iPre = [fidStep12BCongExtractAndClauseFn] ∧
      fn = fidStep12BCongExtractFromFn) ∨
    (f0.name = "full_bve_var_m7" ∧ fn = fidStep12BBveWeakenUnitFn) ∨
    (f0.name = "full_add_clause" ∧ fn = fidStep12CWatchPopFn) ∨
    (f0.name = "full_learn_clause_m6" ∧ fn = fidStep12CReducePurgeFn) ∨
    (f0.name = "full_viv_sort_counts_m6" ∧ fn = fidStep12CVivSiftCountsM6Fn) := by
  unfold patchInsAt fidStep12Befores fidStep11TumBefores fidStep12BBefores fidStep12CBefores
    fidStep12BCongBefores fidStep12BBveFwdBefores at hi
  simp only [List.cons_append, List.nil_append, List.find?] at hi
  by_cases h1 : ("full_ingest_cl" == f0.name) = true
  · simp [h1] at hi
    cases iPre with
    | nil => simp at hi; exact Or.inl ⟨(beq_iff_eq.mp h1).symm, hi.1.symm⟩
    | cons _ _ => simp at hi
  · simp only [h1] at hi
    by_cases h2 : ("full_parse_body_m6" == f0.name) = true
    · simp [h2] at hi
      cases iPre with
      | nil => simp at hi; exact Or.inr (Or.inl ⟨(beq_iff_eq.mp h2).symm, hi.1.symm⟩)
      | cons _ _ => simp at hi
    · simp only [h2] at hi
      by_cases h3 : ("full_extend" == f0.name) = true
      · simp [h3] at hi
        cases iPre with
        | nil =>
          simp at hi; exact Or.inr (Or.inr (Or.inl ⟨(beq_iff_eq.mp h3).symm, hi.1.symm⟩))
        | cons x xs =>
          cases xs with
          | nil =>
            simp at hi
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(beq_iff_eq.mp h3).symm, hi.2.1.symm⟩)))
          | cons _ _ => simp at hi
      · simp only [h3] at hi
        by_cases h4 : ("full_lucky_scan" == f0.name) = true
        · simp [h4] at hi
          cases iPre with
          | nil =>
            simp at hi
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(beq_iff_eq.mp h4).symm, hi.1.symm⟩))))
          | cons _ _ => simp at hi
        · simp only [h4] at hi
          by_cases h5 : ("full_ana_failed_lit_m6_hdr" == f0.name) = true
          · simp [h5] at hi
            cases iPre with
            | nil =>
              simp at hi
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(beq_iff_eq.mp h5).symm, hi.1.symm⟩)))))
            | cons _ _ => simp at hi
          · simp only [h5] at hi
            by_cases h6 : ("full_cong_extract" == f0.name) = true
            · simp [h6] at hi
              cases iPre with
              | nil =>
                simp at hi
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨(beq_iff_eq.mp h6).symm, hi.1.symm⟩))))))
              | cons x xs =>
                cases xs with
                | nil =>
                  simp at hi
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨(beq_iff_eq.mp h6).symm, congrArg List.singleton hi.1.symm, hi.2.1.symm⟩)))))))
                | cons _ _ => simp at hi
            · simp only [h6] at hi
              by_cases h7 : ("full_bve_var_m7" == f0.name) = true
              · simp [h7] at hi
                cases iPre with
                | nil =>
                  simp at hi
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨(beq_iff_eq.mp h7).symm, hi.1.symm⟩))))))))
                | cons _ _ => simp at hi
              · simp only [h7] at hi
                by_cases h8 : ("full_add_clause" == f0.name) = true
                · simp [h8] at hi
                  cases iPre with
                  | nil =>
                    simp at hi
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inl ⟨(beq_iff_eq.mp h8).symm, hi.1.symm⟩)))))))))
                  | cons _ _ => simp at hi
                · simp only [h8] at hi
                  by_cases h9 : ("full_learn_clause_m6" == f0.name) = true
                  · simp [h9] at hi
                    cases iPre with
                    | nil =>
                      simp at hi
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨(beq_iff_eq.mp h9).symm, hi.1.symm⟩))))))))))
                    | cons _ _ => simp at hi
                  · simp only [h9] at hi
                    by_cases h10 : ("full_viv_sort_counts_m6" == f0.name) = true
                    · simp [h10] at hi
                      cases iPre with
                      | nil =>
                        simp at hi
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inr (Or.inr ⟨(beq_iff_eq.mp h10).symm, hi.1.symm⟩))))))))))
                      | cons _ _ => simp at hi
                    · simp only [h10] at hi; cases iPre <;> simp at hi

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

end
