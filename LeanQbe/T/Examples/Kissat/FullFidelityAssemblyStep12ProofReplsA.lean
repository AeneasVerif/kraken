/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofAgree
import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice0
import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof
import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofAnalyze
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofFailed
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofMin
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofMode
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofRsn
import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofViv
import LeanQbe.T.Examples.Kissat.FullFidelityStep12ProofLuckyS15
import LeanQbe.T.Examples.Kissat.FullFidelityStep12ProofVivDel
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofParse
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
import LeanQbe.T.Examples.Kissat.FullM6S15Bridge

/-!
# Kissat Fidelity Step 12 Replacement & Before Proofs — Part A
(`FullFidelityAssemblyStep12ProofReplsA`)

Per-function `(callsOk, impl)` obligations for:
- Rewired `full_cong_work_step` (`1`)
- Step-11 PR 1 repls (`8`, with `renameFuncCalls pr3BtAcMap` on `fid12AnaFailedLitM6HdrFn` and
  `renameFuncCalls fid12PreprocessLuckyMap` on `fid12PreprocessM6Fn`)
- Tumble (`6` repls + `5` befores, with S1.5 / Del BCP bridges)
- Step-11 PR 3 (`11` repls + `1` before, with `fid11_viv_clause_m6_del_wp`)
(`< 1,000` LOC, `0` `@[expose]` on thms/lemmas, `0` `import all`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open LeanQbe.T.Examples.Kissat.FullFidelityStep11
open LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Shared `callsOk` Dependency Helpers -/

theorem fid12_replCallsOk_at {fn : Fn} {deps : List SigEntry}
    {bPre pre : List Fn} {f0 : Fn}
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig)
    (hchk : fn.checkCallsOk deps [] = true)
    (hdeps : ∀ d ∈ deps,
      d ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
        patchInsAt fidStep12Befores f0).map Fn.sig) :
    fn.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig)
      fidStep12Module.exits :=
  fidStep12_callsOk_of hchk fun d hd => hpreM d (hdeps d hd)

theorem fid12_befCallsOk_at {fn : Fn} {deps : List SigEntry}
    {bPre iPre pre : List Fn}
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++ iPre).map Fn.sig →
      s ∈ pre.map Fn.sig)
    (hchk : fn.checkCallsOk deps [] = true)
    (hdeps : ∀ d ∈ deps,
      d ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++ iPre).map Fn.sig) :
    fn.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig)
      fidStep12Module.exits :=
  fidStep12_callsOk_of hchk fun d hd => hpreM d (hdeps d hd)

theorem fid12_dep_base {bPre bPost : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {tgt : Sym} (hf0 : f0.name = tgt) (j : Nat) {d : SigEntry}
    (hchk : (fidStep10_step12_sigPairs.find? (·.2.1 == tgt)).elim false
      (fun s => (fidStep10_step12_sigPairs.find? (·.1 == j)).elim false
        (fun dj => decide (dj.1 < s.1) && (dj.2 == d))) = true := by decide) :
    d ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig := by
  let ⟨hd, hlt⟩ := fidStep12_slot_lt_of hfs hf0 j hchk
  rw [List.map_append, List.mem_append]
  exact Or.inl (fidStep12_base_sig_in_patch hfs hd hlt)

theorem fid12_dep_befBase {bPre bPost iPre : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {tgt : Sym} (hf0 : f0.name = tgt) (j : Nat) {d : SigEntry}
    (hchk : (fidStep10_step12_sigPairs.find? (·.2.1 == tgt)).elim false
      (fun s => (fidStep10_step12_sigPairs.find? (·.1 == j)).elim false
        (fun dj => decide (dj.1 < s.1) && (dj.2 == d))) = true := by decide) :
    d ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++ iPre).map Fn.sig := by
  let ⟨hd, hlt⟩ := fidStep12_slot_lt_of hfs hf0 j hchk
  rw [List.map_append, List.mem_append]
  exact Or.inl (fidStep12_base_sig_in_patch hfs hd hlt)

theorem fid12_dep_before {bPre bPost : List Fn} {f0 ins : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    {tgt : Sym} (hf0 : f0.name = tgt) (j : Nat) (s : SigEntry)
    (hchk : (fidStep10_step12_sigPairs.find? (·.2.1 == tgt)).elim false
      (fun s0 => (fidStep10_step12_sigPairs.find? (·.1 == j)).elim false
        (fun dj => decide (dj.1 < s0.1) && (dj.2 == s))) = true := by decide)
    (hins : fidStep12Befores.find? (·.1 == s.1) = some (s.1, [ins]) ∨
      ∃ ps, fidStep12Befores.find? (·.1 == s.1) = some (s.1, ps) ∧ ins ∈ ps) :
    ins.sig ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig := by
  let ⟨hs, hlt⟩ := fidStep12_slot_lt_of hfs hf0 j hchk
  rw [List.map_append, List.mem_append]
  exact Or.inl (fidStep12_before_sig_in_patch hfs hs hlt hins)

theorem fid12_dep_selfBefore {bPre : List Fn} {f0 : Fn} {tgt : Sym} {d : SigEntry}
    (hf0 : f0.name = tgt)
    (hchk : ((fidStep12Befores.find? (·.1 == tgt)).elim [] Prod.snd).any
      (·.sig == d) = true := by decide) :
    d ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig := by
  rw [List.map_append, List.mem_append]; right
  unfold patchInsAt
  rw [hf0]
  cases hfd : fidStep12Befores.find? (·.1 == tgt) with
  | none => simp [hfd] at hchk
  | some p =>
    simp only [hfd, Option.elim_some, List.any_eq_true, beq_iff_eq] at hchk
    obtain ⟨g, hg, hgs⟩ := hchk
    simp [← hgs, List.mem_map_of_mem hg]

/-! ## 2. Local `checkCallsOk` for Rewired & PR 1 Replacements -/

private theorem workStep12_callsOk :
    full_cong_work_step.checkCallsOk
      [ ("full_cong_find", [i64, i32], [i32])
      , ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem analyzeRsnM6Hdr12_callsOk :
    fidStep11AnalyzeRsnM6HdrFn.checkCallsOk
      [ ("full_analyze_lit", [i64, i32, i32], [.bool])
      , ("m6_hdr_record_used", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem anaFailedLitM6Hdr12_callsOk :
    fid12AnaFailedLitM6HdrFn.checkCallsOk
      [ ("full_clear_ana", [i64], [])
      , ("full_bump_analyzed_m6_hdr", [i64], [])
      , ("full_backtrack_ac_fid", [i64, i64], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_ema_update", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem minShrinkM6_12_callsOk :
    fidStep11MinShrinkM6Fn.checkCallsOk
      [ ("full_sort_tmp", [i64], [])
      , ("full_min_mark", [i64, i32, i8], [])
      , ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool])
      , ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]) ] [] = true := by
  t_kernel_rfl

private theorem analyze12_callsOk :
    fidStep11AnalyzeFn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_deduce_1uip", [i64], [i64])
      , ("full_restore_bump_ana_m5", [i64], [])
      , ("full_min_shrink", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem analyzeCoreM6_12_callsOk :
    fidStep11AnalyzeCoreM6Fn.checkCallsOk
      [ ("full_one_lit_confl", [i64], [i64])
      , ("full_ana_failed_lit_m6_hdr", [i64], [i64])
      , ("full_deduce_1uip_m6_hdr", [i64], [i64])
      , ("full_restore_bump_ana_m6_hdr", [i64], [])
      , ("full_min_shrink_m6", [i64], [])
      , ("full_tick_rel", [i64], [])
      , ("full_ema_update", [i64, i64], [])
      , ("full_learn_clause_m6", [i64, i64], [i64]) ] [] = true := by
  t_kernel_rfl

private theorem vivifyTierM6Hdr12_callsOk :
    fidStep11VivifyTierM6HdrFn.checkCallsOk
      [ ("full_backtrack", [i64, i64], [])
      , ("full_viv_collect_fid", [i64, i64], [i64])
      , ("full_viv_count_fid", [i64, i64], [])
      , ("full_viv_sort_fid", [i64, i64], [])
      , ("full_viv_clause_m6", [i64, i32], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem switchModeM7_12_callsOk :
    fidStep11SwitchModeM7Fn.checkCallsOk
      [ ("full_ilog10", [i64], [i64])
      , ("full_heap_down", [i64, i32], [])
      , ("full_ema_swap_m7", [i64, i64, i64], [])
      , ("full_log10_q16_m7", [i64], [i64])
      , ("full_m7_get64", [i64, i64], [i64])
      , ("full_m7_set64", [i64, i64, i64], []) ] [] = true := by
  t_kernel_rfl

private theorem preprocessM6_12_callsOk :
    fid12PreprocessM6Fn.checkCallsOk
      [ ("full_propagate", [i64], [i64])
      , ("full_arena_sweep", [i64], [i64])
      , ("full_lucky_late_m7", [i64], [i64])
      , ("full_compact_needed", [i64], [.bool])
      , ("full_compact", [i64], [i64])
      , ("full_scale_delta_m5", [i64, i64], [i64])
      , ("full_probe_m6", [i64, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Rewired `full_cong_work_step` & PR 1 (`8`) Obligations -/

theorem fid12_ok_congWorkStep {bPre bPost pre : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost) (hf0 : f0.name = "full_cong_work_step")
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig)
    (hwf0 : f0.Wf) :
    full_cong_work_step.Wf ∧
    full_cong_work_step.callsOk
      (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env full_cong_work_step.name full_cong_work_step.as
      full_cong_work_step.rs xs m Q X → Func.wp fidStep12Env full_cong_work_step.body xs m Q X := by
  have heq : f0 = full_cong_work_step :=
    fidStep10_workStep_eq (hfs ▸ List.mem_append_right _ List.mem_cons_self) hf0
  refine ⟨heq ▸ hwf0, fid12_replCallsOk_at hpreM workStep12_callsOk (fun d hd => ?_),
    fun xs m Q X hlk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact fid12_dep_base hfs hf0 252
    · exact fid12_dep_base hfs hf0 273
  · have hfind : fidStep12Bundle.frontTable.find? (·.name == full_cong_work_step.name) =
        some fidStep12BRewireRows[0] := rfl
    exact (SpecEntry.Impl.of (workStep_wp_of_inactive_eval fidStep12Env fid12_congFind
      (fun hIn => fid12_frontRow 29 "full_cong_eval_gate" step12BCongEvalGateSpec rfl
        (fun _ _ _ _ h => h) _ _ _ _ (m6CongEvalGateSpec_inactive_to_step12B hIn)))).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fid12_ok_pr1 {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fid12Pr1Repls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fid12Pr1Repls_wf r hr, ?_, ?_⟩
  · simp only [fid12Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine fid12_replCallsOk_at hpreM analyzeRsnM6Hdr12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_base hfs hf0 116
      · exact fid12_dep_base hfs hf0 65
    · refine fid12_replCallsOk_at hpreM anaFailedLitM6Hdr12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 119
      · exact fid12_dep_base hfs hf0 122
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 34
    · refine fid12_replCallsOk_at hpreM minShrinkM6_12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 133
      · exact fid12_dep_base hfs hf0 128
      · exact fid12_dep_base hfs hf0 139
      · exact fid12_dep_base hfs hf0 141
    · refine fid12_replCallsOk_at hpreM analyze12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 148
      · exact fid12_dep_base hfs hf0 145
      · exact fid12_dep_base hfs hf0 155
      · exact fid12_dep_base hfs hf0 144
      · exact fid12_dep_base hfs hf0 30
      · exact fid12_dep_base hfs hf0 34
      · exact fid12_dep_base hfs hf0 150
    · refine fid12_replCallsOk_at hpreM analyzeCoreM6_12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 148
      · exact fid12_dep_base hfs hf0 124
      · exact fid12_dep_base hfs hf0 146
      · exact fid12_dep_base hfs hf0 123
      · exact fid12_dep_base hfs hf0 142
      · exact fid12_dep_base hfs hf0 30
      · exact fid12_dep_base hfs hf0 34
      · exact fid12_dep_base hfs hf0 157
    · refine fid12_replCallsOk_at hpreM vivifyTierM6Hdr12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 40
      · exact fid12_dep_base hfs hf0 225
      · exact fid12_dep_base hfs hf0 226
      · exact fid12_dep_base hfs hf0 228
      · exact fid12_dep_base hfs hf0 217
      · exact fid12_dep_base hfs hf0 90
      · exact fid12_dep_base hfs hf0 223
    · refine fid12_replCallsOk_at hpreM switchModeM7_12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 9
      · exact fid12_dep_base hfs hf0 21
      · exact fid12_dep_base hfs hf0 492
      · exact fid12_dep_base hfs hf0 32
      · exact fid12_dep_base hfs hf0 481
      · exact fid12_dep_base hfs hf0 482
    · refine fid12_replCallsOk_at hpreM preprocessM6_12_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 90
      · exact fid12_dep_base hfs hf0 108
      · exact fid12_dep_base hfs hf0 488
      · exact fid12_dep_base hfs hf0 446
      · exact fid12_dep_base hfs hf0 458
      · exact fid12_dep_base hfs hf0 33
      · exact fid12_dep_base hfs hf0 496
  · simp only [fid12Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11AnalyzeRsnM6HdrFn.name) =
          some fid12Pr1Rows[0] := rfl
      exact (SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_step11_wp fidStep12Env fid12_analyzeLit
        fid12_hdrRecordUsed)).2 xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid12AnaFailedLitM6HdrFn.name) =
          some fid12Pr1Rows[1] := rfl
      exact (SpecEntry.Impl.of (func_wp_of_renameFuncCalls pr3BtAcMap
        FullFidelityStep11.full_ana_failed_lit_m6_hdr_body full_ana_failed_lit_m6_hdr_step11_wf
        fidStep12Env (full_ana_failed_lit_m6_hdr_step11_wp _ fid12_clearAna
          fid12_bumpAnalyzedM6Hdr (fid12_frontRow 52 "full_backtrack_ac_fid" fullBacktrackSpec)
          fid12_assignLvl fid12_emaUpdate))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11MinShrinkM6Fn.name) =
          some fid12Pr1Rows[2] := rfl
      exact (SpecEntry.Impl.of (full_min_shrink_m6_step11_wp fidStep12Env fid12_sortTmp
        fid12_minMark fid12_minLitDfsM8 fid12_shrinkBlkBoolM8)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11AnalyzeFn.name) =
          some fid12Pr1Rows[3] := rfl
      exact (SpecEntry.Impl.of (full_analyze_step11_wp fidStep12Env
        (fid12_frontRow 20 "full_one_lit_confl" fullOneLitConflSpec) fid12_deduce1uip
        fid12_restoreBumpAnaM5 fid12_minShrink fid12_tickRel fid12_emaUpdate
        (fid12_frontRow 21 "full_learn_clause" fullLearnClauseSpec))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11AnalyzeCoreM6Fn.name) =
          some fid12Pr1Rows[4] := rfl
      exact (SpecEntry.Impl.of (full_analyze_core_m6_step11_s11_wp fidStep12Env
        (fid12_frontRow 20 "full_one_lit_confl" fullOneLitConflSpec)
        (fid12_frontRow 2 "full_ana_failed_lit_m6_hdr" (m6aAnaFailedLitSpecP M6ExtW2bPres) rfl
          (fun _ _ _ _ h => m6aAnaFailedLitSpecP_monoXP h))
        (fid12_frontRow 19 "full_deduce_1uip_m6_hdr" FullFidelityStep11.s11Deduce1uipHdrSpec rfl
          (fun _ _ _ _ h => FullFidelityStep11.s11Deduce1uipHdrSpec_monoX h))
        fid12_restoreBumpAnaM6Hdr
        (fid12_frontRow 3 "full_min_shrink_m6" m8MinShrinkSpec rfl
          (fun _ _ _ _ h => m8MinShrinkSpec_monoX h))
        fid12_tickRel fid12_emaUpdate
        (fid12_frontRow 40 "full_learn_clause_m6" FullFidelityStep10.step10LearnClauseM6Spec rfl
          (fun _ _ _ _ h => FullFidelityStep10.step10LearnClauseM6Spec_monoX h)))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11VivifyTierM6HdrFn.name) =
          some fid12Pr1Rows[5] := rfl
      exact (SpecEntry.Impl.of (full_vivify_tier_m6_hdr_step11_wp fidStep12Env
        (fid12_frontRow 17 "full_backtrack" fullBacktrackSpec)
        (fun ⟨h, tm, ()⟩ m0 Q0 X0 hs => by
          rcases FullFidelityStep11.fid11VivCollectSpec_elim hs with
            ⟨c, F0, s, R, rfl, hsp, hm, hq⟩
          exact fid12_frontRow 22 "full_viv_collect_fid" FullFidelityVivFlag.fid11VivCollectSpec rfl
            (fun _ _ _ _ h0 => FullFidelityVivFlag.fid11VivCollectSpec_monoX h0)
            (c.hdr, tm, ()) m0 Q0 X0 (FullFidelityVivFlag.fid11VivCollectSpec_intro rfl hsp hm hq))
        fid12_vivCountFid
        (fid12_frontRow 24 "full_viv_sort_fid" fullVivSortFidSpec rfl
          (fun _ _ _ _ h => fullVivSortFidSpec_monoX h))
        (fid12_frontRow 25 "full_viv_clause_m6" fullVivClauseM6Spec) fid12_propagate
        fid12_vivClearTierM6)).2 xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11SwitchModeM7Fn.name) =
          some fid12Pr1Rows[6] := rfl
      exact (SpecEntry.Impl.of (full_switch_mode_m7_step11_wp fidStep12Env fid12_ilog10
        fid12_heapDown fid12_emaSwapM7 fid12_log10Q16M7 fid12_m7Get64 fid12_m7Set64)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid12PreprocessM6Fn.name) =
          some fid12Pr1Rows[7] := rfl
      exact (SpecEntry.Impl.of (func_wp_of_renameFuncCalls fid12PreprocessLuckyMap
        FullFidelityStep11.full_preprocess_m6_body full_preprocess_m6_step11_wf fidStep12Env
        (full_preprocess_m6_step11_wp _ fid12_propagate fid12_arenaSweep fid12_luckyLateCanon
          fid12_compactNeeded fid12_compact fid12_scaleDeltaM5
          (fid12_frontRow 46 "full_probe_m6" m6ProbeSpec rfl
            (fun _ _ _ _ h => m6ProbeSpec_monoX h))))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)

/-! ## 4. Tumble Replacements (`6`) -/

theorem fid12_ok_tum {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fidStep11TumRepls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fidStep11TumRepls_wf r hr, ?_, ?_⟩
  · simp only [fidStep11TumRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fid12_replCallsOk_at hpreM fidStep11ZeroTables2_callsOk fun _ hd => nomatch hd
    · exact fid12_replCallsOk_at hpreM fidStep11InitHdr_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM fidStep11IngestCl_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 6
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 41
    · refine fid12_replCallsOk_at hpreM fidStep11ParseBodyM6_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 2
      · exact fid12_dep_base hfs hf0 78
      · exact fid12_dep_base hfs hf0 79
      · exact fid12_dep_base hfs hf0 90
      · exact fid12_dep_selfBefore hf0
    · refine fid12_replCallsOk_at hpreM fidStep11Extend_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_selfBefore hf0
    · refine fid12_replCallsOk_at hpreM fidStep11LuckyScan_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_selfBefore hf0
      · exact fid12_dep_base hfs hf0 37
      · exact fid12_dep_base hfs hf0 90
      · exact fid12_dep_base hfs hf0 40
      · exact fid12_dep_base hfs hf0 156
  · simp only [fidStep11TumRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11ZeroTables2Fn.name) =
          some fidStep11TumReplRows[0] := rfl
      exact (SpecEntry.Impl.of (fidStep11ZeroTables2_impl fidStep12Env)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11InitHdrFn.name) =
          some fidStep11TumReplRows[1] := rfl
      exact (SpecEntry.Impl.of (fidStep11InitHdr_impl fidStep12Env)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11IngestClFn.name) =
          some fidStep11TumReplRows[2] := rfl
      exact (SpecEntry.Impl.of (fidStep11IngestCl_impl fidStep12Env fid12_kissatNextLit
        (fid12_frontRow 47 "full_activate_lit_fid" fullActivateLitFidSpec) fid12_assignLvl
        (fid12_frontRow 38 "full_add_clause" fullAddClauseSpec))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11ParseBodyM6Fn.name) =
          some fidStep11TumReplRows[3] := rfl
      exact (SpecEntry.Impl.of (full_parse_body_tum_del_wp fidStep12Env fid12_skipCl
        (fid12_frontRow 11 "full_ingest_cl" fullIngestClTumSpec)
        (s15_to_propagateDel fid12_propagate) fid12_kissatSkipWsComments
        (fid12_frontRow 48 "full_tumble_finish_fid" fullTumbleFinishFidSpec))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11ExtendFn.name) =
          some fidStep11TumReplRows[4] := rfl
      exact (SpecEntry.Impl.of (fidStep11Extend_impl fidStep12Env
        (fid12_frontRow 49 "full_extend_core_fid" fullExtendSpec)
        (fid12_frontRow 50 "full_unperm_fid" fullUnpermFidSpec))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11LuckyScanFn.name) =
          some fidStep11TumReplRows[5] := rfl
      exact (SpecEntry.Impl.of (full_lucky_scan_tum_s15_wp fidStep12Env
        (fid12_frontRow 51 "full_lucky_ord_fid" fullLuckyOrdFidSpec) fid12_assign
        (fid12_frontRow 17 "full_backtrack" fullBacktrackSpec) fid12_propagate
        (fid12_frontRow 4 "full_analyze" fullAnalyzeSpec))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)

/-! ## 5. Step-11 PR 3 Replacements (`11`) & `Part A` Befores (`6`) -/

theorem fid12_ok_pr3 {r : Fn} {bPre bPost pre : List Fn} {f0 : Fn}
    (hr : r ∈ fid12Pr3Repls) (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hf0 : f0.name = r.name)
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++
      patchInsAt fidStep12Befores f0).map Fn.sig → s ∈ pre.map Fn.sig) :
    r.Wf ∧
    r.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X, fidStep12Env r.name r.as r.rs xs m Q X → Func.wp fidStep12Env r.body xs m Q X := by
  refine ⟨fid12Pr3Repls_wf r hr, ?_, ?_⟩
  · simp only [fid12Pr3Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine fid12_replCallsOk_at hpreM pr3_sweepCone_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 316
      · exact fid12_dep_base hfs hf0 318
      · exact fid12_dep_base hfs hf0 321
    · exact fid12_replCallsOk_at hpreM pr3_saveTargetBest_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM pr3_backtrack_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_base hfs hf0 38
      · exact fid12_dep_base hfs hf0 39
    · refine fid12_replCallsOk_at hpreM pr3_deduce1uipM6_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 116
      · exact fid12_dep_base hfs hf0 117
      · exact fid12_dep_base hfs hf0 119
      · exact fid12_dep_base hfs hf0 125
      · exact fid12_dep_base hfs hf0 126
      · exact fid12_dep_base hfs hf0 127
    · refine fid12_replCallsOk_at hpreM pr3_deduce1uipM6Hdr_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 116
      · exact fid12_dep_base hfs hf0 118
      · exact fid12_dep_base hfs hf0 119
      · exact fid12_dep_base hfs hf0 125
      · exact fid12_dep_base hfs hf0 126
      · exact fid12_dep_base hfs hf0 127
    · refine fid12_replCallsOk_at hpreM pr3_oneLitConfl_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 18
      · exact fid12_dep_base hfs hf0 147
      · exact fid12_dep_before hfs hf0 124 ("full_ana_failed_lit_m6_hdr", [i64], [i64])
          (hins := Or.inl rfl)
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 82
      · exact fid12_dep_base hfs hf0 19
    · refine fid12_replCallsOk_at hpreM pr3_learnClause_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_before hfs hf0 124 ("full_ana_failed_lit_m6_hdr", [i64], [i64])
          (hins := Or.inl rfl)
      · exact fid12_dep_base hfs hf0 36
      · exact fid12_dep_base hfs hf0 147
      · exact fid12_dep_base hfs hf0 18
      · exact fid12_dep_base hfs hf0 114
      · exact fid12_dep_base hfs hf0 41
      · exact fid12_dep_base hfs hf0 149
    · refine fid12_replCallsOk_at hpreM pr3_vivCollectFid_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_base hfs hf0 11
      · exact fid12_dep_base hfs hf0 218
    · exact fid12_replCallsOk_at hpreM pr3_vivSort2Fid_callsOk fun _ hd => nomatch hd
    · refine fid12_replCallsOk_at hpreM pr3_vivSortFid_callsOk fun d hd => ?_
      simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_base hfs hf0 227
    · refine fid12_replCallsOk_at hpreM pr3_vivClauseM6_callsOk fun d hd => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fid12_dep_base hfs hf0 215
      · exact fid12_dep_base hfs hf0 213
      · exact fid12_dep_base hfs hf0 216
      · exact fid12_dep_base hfs hf0 208
      · exact fid12_dep_base hfs hf0 37
      · exact fid12_dep_base hfs hf0 89
      · exact fid12_dep_base hfs hf0 40
      · exact fid12_dep_base hfs hf0 212
  · simp only [fid12Pr3Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11SweepConeFn.name) =
          some fidStep11Pr3ReplRows[0] := rfl
      exact (fid11_sweep_cone_impl fidStep12Env fid12_m6MaxV fid12_k6Init fid12_k6AddClause).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11SaveTargetBestFn.name) =
          some fidStep11Pr3ReplRows[1] := rfl
      exact (fid11_save_target_best_impl fidStep12Env).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11BacktrackFn.name) =
          some fidStep11Pr3ReplRows[2] := rfl
      exact (fid11_backtrack_impl fidStep12Env fid12_backtrackRawM5
        (fid12_frontRow 16 "full_save_target_best" fullSaveTargetBestSpec)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11Deduce1uipM6Fn.name) =
          some fidStep11Pr3ReplRows[3] := rfl
      exact (fid11_deduce_1uip_m6_impl fidStep12Env fid12_analyzeLit fid12_analyzeRsn fid12_clearAna
        fid12_otfsLarge fid12_otfsBin fid12_otfsSubsume).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11Deduce1uipM6HdrFn.name) =
          some ⟨"full_deduce_1uip_m6_hdr", [i64], [i64],
            FullFidelityStep11.s11Deduce1uipHdrSpec, true⟩ := rfl
      exact (SpecEntry.Impl.of (fid11_deduce_1uip_m6_hdr_s11_wp fidStep12Env fid12_analyzeLit
        (fid12_frontRow 1 "full_analyze_rsn_m6_hdr" m6AnalyzeRsnHdrSpec rfl
          (fun _ _ _ _ h => m6AnalyzeRsnHdrSpec_monoX h))
        fid12_clearAna fid12_otfsLarge fid12_otfsBin fid12_otfsSubsume)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11OneLitConflFn.name) =
          some fidStep11Pr3ReplRows[5] := rfl
      exact (fid11_one_lit_confl_impl fidStep12Env fid12_wstackDefrag fid12_detNewLevel
        (fid12_frontRow 52 "full_backtrack_ac_fid" fullBacktrackSpec) fid12_assignLvl
        fid12_unwatchLarge fid12_watchPush).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11LearnClauseFn.name) =
          some fidStep11Pr3ReplRows[6] := rfl
      exact (fid11_learn_clause_impl fidStep12Env
        (fid12_frontRow 52 "full_backtrack_ac_fid" fullBacktrackSpec) fid12_assignLvl
        fid12_detNewLevel fid12_wstackDefrag fid12_reduce
        (fid12_frontRow 38 "full_add_clause" fullAddClauseSpec) fid12_eagerSubsume).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11VivCollectFidFn.name) =
          some fidStep11Pr3ReplRows[8] := rfl
      exact (fid11_viv_collect_fid_impl fidStep12Env fid12_arenaNext fid12_vivTierMatchM6).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11VivSort2FidFn.name) =
          some fidStep11Pr3ReplRows[9] := rfl
      exact (fid11_viv_sort2_fid_impl fidStep12Env).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11VivSortFidFn.name) =
          some fidStep11Pr3ReplRows[10] := rfl
      exact (fid11_viv_sort_fid_impl fidStep12Env
        (fid12_frontRow 23 "full_viv_sort2_fid" fullVivSort2FidSpec rfl
          (fun _ _ _ _ h => fullVivSort2FidSpec_monoX h))).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)
    · intro xs m Q X hlk
      have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11VivClauseM6Fn.name) =
          some fidStep11Pr3ReplRows[11] := rfl
      exact (SpecEntry.Impl.of (fid11_viv_clause_m6_del_wp fidStep12Env fid12_vivL0SimpM6
        (fid12_frontRow 41 "full_viv_sort_counts_m6" fullVivSortCountsM6Spec)
        fid12_vivReusePrefixM6 fid12_vivBestImpliedM6 fid12_assign
        (s15_to_propagateIgnoreDel fid12_propagateIgnore)
        (fid12_frontRow 17 "full_backtrack" fullBacktrackSpec) fid12_vivFinishM6)).2 xs m Q X
        (env_ofTable_find?_of_append hfind rfl rfl hlk)

theorem fid12_ok_before_A {fn : Fn} {bPre bPost iPre pre : List Fn} {f0 : Fn}
    (hfs : fidStep10Module.fns = bPre ++ f0 :: bPost)
    (hcases :
      (f0.name = "full_ingest_cl" ∧ fn = fidStep11ActivateLitFn) ∨
      (f0.name = "full_parse_body_m6" ∧ fn = fidStep11TumbleFinishFn) ∨
      (f0.name = "full_extend" ∧ fn = fidStep11ExtendCoreFn) ∨
      (f0.name = "full_extend" ∧ fn = fidStep11UnpermFn) ∨
      (f0.name = "full_lucky_scan" ∧ fn = fidStep11LuckyOrdFn) ∨
      (f0.name = "full_ana_failed_lit_m6_hdr" ∧ fn = fid11BacktrackAcFn))
    (hpreM : ∀ s, s ∈ (patchFns fidStep12Repls fidStep12Befores bPre ++ iPre).map Fn.sig →
      s ∈ pre.map Fn.sig) :
    fn.Wf ∧
    fn.callsOk (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits ∧
    ∀ xs m Q X,
      fidStep12Env fn.name fn.as fn.rs xs m Q X → Func.wp fidStep12Env fn.body xs m Q X := by
  rcases hcases with ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩
  · refine ⟨fidStep11TumBefores_wf _ (by simp [fidStep11TumBefores]),
      fid12_befCallsOk_at hpreM fidStep11ActivateLit_callsOk fun d hd => ?_,
      fun xs m Q X hlk => ?_⟩
    · simp only [List.mem_singleton] at hd; rw [hd]
      exact fid12_dep_befBase hfs hf0 22
    · have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11ActivateLitFn.name) =
          some fidStep11TumBeforeRows[0] := rfl
      exact (SpecEntry.Impl.of (fidStep11ActivateLit_impl fidStep12Env fid12_heapPush)).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep11TumBefores_wf _ (by simp [fidStep11TumBefores]),
      fid12_befCallsOk_at hpreM fidStep11TumbleFinish_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11TumbleFinishFn.name) =
        some fidStep11TumBeforeRows[1] := rfl
    exact (SpecEntry.Impl.of (fidStep11TumbleFinish_impl fidStep12Env)).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep11TumBefores_wf _ (by simp [fidStep11TumBefores]),
      fid12_befCallsOk_at hpreM fidStep11ExtendCore_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11ExtendCoreFn.name) =
        some fidStep11TumBeforeRows[2] := rfl
    exact (SpecEntry.Impl.of (fidStep11ExtendCore_impl fidStep12Env)).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep11TumBefores_wf _ (by simp [fidStep11TumBefores]),
      fid12_befCallsOk_at hpreM fidStep11Unperm_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11UnpermFn.name) =
        some fidStep11TumBeforeRows[3] := rfl
    exact (SpecEntry.Impl.of (fidStep11Unperm_impl fidStep12Env)).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fidStep11TumBefores_wf _ (by simp [fidStep11TumBefores]),
      fid12_befCallsOk_at hpreM fidStep11LuckyOrd_callsOk (fun _ hd => nomatch hd),
      fun xs m Q X hlk => ?_⟩
    have hfind : fidStep12Bundle.frontTable.find? (·.name == fidStep11LuckyOrdFn.name) =
        some fidStep11TumBeforeRows[4] := rfl
    exact (SpecEntry.Impl.of (fidStep11LuckyOrd_impl fidStep12Env)).2
      xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)
  · refine ⟨fid11_backtrack_ac_wf,
      fid12_befCallsOk_at hpreM pr3_backtrackAc_callsOk fun d hd => ?_,
      fun xs m Q X hlk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact fid12_dep_befBase hfs hf0 38
      · exact fid12_dep_befBase hfs hf0 39
    · have hfind : fidStep12Bundle.frontTable.find? (·.name == fid11BacktrackAcFn.name) =
          some fidStep11Pr3BeforeRows[0] := rfl
      exact (fid11_backtrack_ac_impl fidStep12Env fid12_backtrackRawM5
        (fid12_frontRow 16 "full_save_target_best" fullSaveTargetBestSpec)).2
        xs m Q X (env_ofTable_find?_of_append hfind rfl rfl hlk)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

end
