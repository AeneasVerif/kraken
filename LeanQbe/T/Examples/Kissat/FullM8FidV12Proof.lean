/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullM8CongWorklistProof
public import LeanQbe.T.Examples.Kissat.FullM8FidV12AnaFailedProof
public import LeanQbe.T.Examples.Kissat.FullM8FidV12AnalyzeProof
public import LeanQbe.T.Examples.Kissat.FullM8FidV12MiscProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyPart1
import all LeanQbe.T.Examples.Kissat.FullM7Transport0
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM7Proof
import all LeanQbe.T.Examples.Kissat.FullM7
import all LeanQbe.T.Examples.Kissat.FullM6CongSubst
import all LeanQbe.T.Examples.Kissat.FullM6Transport0
import all LeanQbe.T.Examples.Kissat.FullM6Transport1
import all LeanQbe.T.Examples.Kissat.FullM6OrchProof2
import all LeanQbe.T.Examples.Kissat.FullM6Orch
import all LeanQbe.T.Examples.Kissat.FullM3CongBva
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullSpec
import all LeanQbe.T.Examples.Kissat.FullSpec1
import all LeanQbe.T.Examples.Kissat.FullSpec2
import all LeanQbe.T.Examples.Kissat.FullSpec3
import all LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import all LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
import all LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
import all LeanQbe.T.Examples.Kissat.FullM7CongIteProof1

/-!
# Closed `ModuleOk` & End-to-End `kissat_solve_bytes` Proof for `FullM8FidV12`

Constructs `m8FidV12Env` over `m7FidelityEnv` (upgrading only `full_cong_enq_var`,
`full_cong_eval_gate`, and `full_cong_worklist` to allow `occ_bkt ≤ 8192`), proves
`m8FidV12_moduleOk : ModuleOk m8FidV12Env m8FidV12Module` via `spliceModule_moduleOk`,
and derives `m8FidV12_solve_bytes_sound`, `m8FidV12_solve_bytes_host_sound`, and
`m8FidV12_unsat_nv` (`XPost := False`, `0` sorry, `std3` axioms only).
-/

namespace LeanQbe.T.Examples.Kissat.FullM8FidV12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Splice

public section

/-! ## 1. Closed `m8FidV12Env` Extending `m7FidelityEnv` -/

/-- Closed environment extending `m7FidelityEnv` with the `occ_bkt ≤ 8192` specs for
`full_cong_enq_var`, `full_cong_eval_gate`, and `full_cong_worklist` (`V2c`). -/
inductive M8FidV12Env (Γ : Env) : Env where
  | base : ∀ {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64}
      {Q : Post bs} {X : XPost},
      Γ f as bs xs m Q X → M8FidV12Env Γ f as bs xs m Q X
  | enqVar : ∀ a m Q X, m8CongEnqVarSpec a m Q X →
      M8FidV12Env Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X
  | evalGate : ∀ a m Q X, m8CongEvalGateSpec a m Q X →
      M8FidV12Env Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X
  | worklist : ∀ a m Q X, m8CongWorklistSpec a m Q X →
      M8FidV12Env Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X

/-- Closed environment for `m8FidV12Module`. -/
@[expose] def m8FidV12Env : Env := M8FidV12Env m7FidelityEnv

private theorem list_nodup_name_eq {α : Type _} (name : α → Sym) {xs : List α}
    (hnd : (xs.map name).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hnm : name x = name y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with hxa | hx <;> rcases hy with hya | hy
    · exact hxa.trans hya.symm
    · rw [hxa] at hnm
      exact absurd (hnm ▸ List.mem_map.mpr ⟨y, hy, rfl⟩) hnd.1
    · rw [hya] at hnm
      exact absurd (hnm.symm ▸ List.mem_map.mpr ⟨x, hx, rfl⟩) hnd.1
    · exact ih hnd.2 hx hy

private theorem ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (ofTable_name_mem h)

private theorem m8ExtraRows_nodup : (mfExtraRows.map SpecEntry.name).Nodup := by
  show ([ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
    , "full_has_bin", "full_min_mark", "full_ana_sift_m6", "full_sort_ana_qs_m6"
    , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp"
    , "full_min_lit_dfs_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6"
    , "full_walk_cb_inv_m7", "full_walk_init_table_m7", "full_walk_effort_m7"
    , "full_walk_init_vals_m7", "full_walk_collect_m7", "full_walk_build_occ_m7"
    , "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7", "full_walk_save_min_m7"
    , "full_warmup_m7", "full_add_bin_m6"
    , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
    , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
    , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
    , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
    , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
    , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
    , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
    , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
    , "full_viv_clear_tier_m6"
    , "full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7"
    , "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"
    , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ] :
      List String).Nodup
  decide

/-! ## 2. Lookup & Elimination Helpers Between `m7FidelityEnv` and `m8FidV12Env` -/

private theorem fid_row {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (idx : Nat)
    (hmem : m7FidBaseTable[idx]? = some ⟨f, as, bs, sp, true⟩ := by rfl)
    (hnx : f ∉ mfExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m8FidV12Env f as bs xs m Q X :=
  fun xs m Q X h =>
    M8FidV12Env.base (M7FidelityEnv.base hnx
      (m7FidBase_row_mem (List.mem_of_getElem? hmem) hno xs m Q X h))

private theorem fid_mem {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hnx : f ∉ mfExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m8FidV12Env f as bs xs m Q X :=
  fun xs m Q X h =>
    M8FidV12Env.base (M7FidelityEnv.base hnx (m7FidBase_row_mem hmem hno xs m Q X h))

private theorem extra_row {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (idx : Nat)
    (hmem : mfExtraRows[idx]? = some ⟨f, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m8FidV12Env f as bs xs m Q X :=
  fun xs m Q X h =>
    M8FidV12Env.base (M7FidelityEnv.extra
      (Env.ofTable_of_mem (List.mem_of_getElem? hmem) m8ExtraRows_nodup (by
        dsimp only [SpecEntry.eff]
        simp only [ite_true]
        exact hno xs m Q X h)))

private theorem m8Fid_elim {nm : Sym} {as rs : List Ty} {sp : Spec as rs}
    (hmem : (⟨nm, as, rs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : m8FidV12Env nm as rs xs m Q X)
    (hne1 : nm ≠ "full_cong_enq_var" := by decide)
    (hne2 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne3 : nm ≠ "full_cong_worklist" := by decide)
    (hnotEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide) :
    sp xs m Q (fun _ _ _ _ => False) := by
  have hf : m7FidelityEnv nm as rs xs m Q X := by
    cases h with
    | base hb => exact hb
    | enqVar => exact absurd rfl hne1
    | evalGate => exact absurd rfl hne2
    | worklist => exact absurd rfl hne3
  cases hf with
  | base _ hbase =>
    have heff := m7FidBase_elim_of_mem hmem hbase
    dsimp only [SpecEntry.eff] at heff
    simpa only [ite_true] using heff
  | extra hextra =>
    exact absurd (ofTable_name_mem hextra) hnotEx

private theorem m7FnsPart2_cong_mem {g : Fn}
    (hg : g ∈ (FullM6CongSubst.m6CongSubst_fns.drop 5).take 17) :
    g ∈ FullM7.m7FnsPart2 := by
  unfold FullM7.m7FnsPart2
  iterate 3 apply List.mem_append_left
  exact List.mem_append_right _ hg

private theorem cong17_to_m7Fid {g : Fn}
    (hg : g ∈ (FullM6CongSubst.m6CongSubst_fns.drop 5).take 17)
    (hNotFid : ∀ r ∈ m7FidRepls, r.name ≠ g.name) :
    g ∈ m7FidelityFns := by
  have hm7 : g ∈ FullM7.m7Fns := by
    unfold FullM7.m7Fns
    exact List.mem_append_left _ (List.mem_append_right _ (m7FnsPart2_cong_mem hg))
  exact mfPatchFns_mem_of_ne hm7 hNotFid

private theorem m7Fid_enqVar_mem :
    FullM6CongSubst.full_cong_enq_var ∈ m7FidelityFns :=
  cong17_to_m7Fid (List.mem_of_getElem? (i := 12) rfl) fun r hr => by
    have hnm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
    intro heq
    rw [heq] at hnm
    exact absurd hnm (by decide)

private theorem m7Fid_evalGate_mem :
    FullM6CongSubst.full_cong_eval_gate ∈ m7FidelityFns :=
  cong17_to_m7Fid (List.mem_of_getElem? (i := 13) rfl) fun r hr => by
    have hnm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
    intro heq
    rw [heq] at hnm
    exact absurd hnm (by decide)

private theorem m7Fid_worklist_mem :
    FullM6CongSubst.full_cong_worklist ∈ m7FidelityFns :=
  cong17_to_m7Fid (List.mem_of_getElem? (i := 15) rfl) fun r hr => by
    have hnm : r.name ∈ m7FidRepls.map Fn.name := List.mem_map.mpr ⟨r, hr, rfl⟩
    intro heq
    rw [heq] at hnm
    exact absurd hnm (by decide)

/-! ## 3. Closed `ModuleOk` for `m8FidV12Module` -/

private theorem m8_eval_gate_wp_closed {xs : Tup Val [i64, i64, i64, i64, i32, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m8CongEvalGateSpec xs m Q X) :
    Func.wp m8FidV12Env FullM6CongSubst.full_cong_eval_gate_body xs m Q X :=
  full_cong_eval_gate_m8_wp m8FidV12Env
    (fid_row 238) (fid_row 244) (fid_row 241) (fid_row 242) (fid_row 255) (fid_row 256)
    (fun _ _ _ _ h => M8FidV12Env.enqVar _ _ _ _ h)
    xs m Q X hs

private theorem m8_worklist_wp_closed {xs : Tup Val [i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m8CongWorklistSpec xs m Q X) :
    Func.wp m8FidV12Env FullM6CongSubst.full_cong_worklist_body xs m Q X :=
  full_cong_worklist_m8_wp m8FidV12Env
    (fid_row 238)
    (fun _ _ _ _ h => M8FidV12Env.evalGate _ _ _ _ h)
    xs m Q X hs

private theorem m8_ana_failed_wp_closed {xs : Tup Val m8AnaFailedLitM6HdrFn.as}
    {m : Mem 64} {Q : Post m8AnaFailedLitM6HdrFn.rs} {X : XPost}
    (hs : m8FidV12Env m8AnaFailedLitM6HdrFn.name m8AnaFailedLitM6HdrFn.as
      m8AnaFailedLitM6HdrFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8AnaFailedLitM6HdrFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_ana_failed_lit_m6_hdr_wp m8FidV12Env
      (fid_row 115)
      (extra_row 54 (hno := fun _ _ _ _ h => FullM6OrchAdapters.m6aBumpAnalyzedSpec_monoX h))
      (fid_row 39) (fid_row 35) (fid_row 33) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 120) rfl) hs))

private theorem m8_analyze_wp_closed {xs : Tup Val m8AnalyzeFn.as}
    {m : Mem 64} {Q : Post m8AnalyzeFn.rs} {X : XPost}
    (hs : m8FidV12Env m8AnalyzeFn.name m8AnalyzeFn.as m8AnalyzeFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8AnalyzeFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_analyze_wp m8FidV12Env
      (fid_row 141) (fid_row 138) (fid_row 148)
      (fid_row 137 (hno := fun _ _ _ _ h => FullM7SpecBridges.m7MinShrinkSpec_monoX h))
      (fid_row 29) (fid_row 33) (fid_row 143) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 149) rfl) hs))

private theorem m8_analyze_core_wp_closed {xs : Tup Val m8AnalyzeCoreM6Fn.as}
    {m : Mem 64} {Q : Post m8AnalyzeCoreM6Fn.rs} {X : XPost}
    (hs : m8FidV12Env m8AnalyzeCoreM6Fn.name m8AnalyzeCoreM6Fn.as
      m8AnalyzeCoreM6Fn.rs xs m Q X) :
    Func.wp m8FidV12Env m8AnalyzeCoreM6Fn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_analyze_core_m6_wp m8FidV12Env
      (fid_row 141)
      (fid_row 120 (hno := fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
      (fid_row 139 (hno := fun _ _ _ _ h => FullM7Proof.m7Deduce1uipHdrSpec_monoX h))
      (fid_row 119 (hno := fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
      (fid_row 135 (hno := fun _ _ _ _ h => FullM7SpecBridges.m7MinShrinkSpec_monoX h))
      (fid_row 29) (fid_row 33) (fid_row 143) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 150) rfl) hs))

private theorem m8_restart_due_wp_closed {xs : Tup Val m8RestartDueFn.as}
    {m : Mem 64} {Q : Post m8RestartDueFn.rs} {X : XPost}
    (hs : m8FidV12Env m8RestartDueFn.name m8RestartDueFn.as m8RestartDueFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8RestartDueFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_restart_due_wp m8FidV12Env (fid_row 9) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 170) rfl) hs))

private theorem m8_enter_dense_wp_closed {xs : Tup Val m8EnterDenseFn.as}
    {m : Mem 64} {Q : Post m8EnterDenseFn.rs} {X : XPost}
    (hs : m8FidV12Env m8EnterDenseFn.name m8EnterDenseFn.as m8EnterDenseFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8EnterDenseFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_enter_dense_wp m8FidV12Env
      (fid_row 39) (fid_row 106) (fid_row 86) (fid_row 96)
      (fid_row 18) (fid_row 104) (fid_row 11) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 236) rfl) hs))

private theorem m8_cong_try_xor_ite_wp_closed {xs : Tup Val m8CongTryXorIteFn.as}
    {m : Mem 64} {Q : Post m8CongTryXorIteFn.rs} {X : XPost}
    (hs : m8FidV12Env m8CongTryXorIteFn.name m8CongTryXorIteFn.as
      m8CongTryXorIteFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8CongTryXorIteFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_cong_try_xor_ite_wp m8FidV12Env (fid_row 243) (fid_row 246) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 249) rfl) hs))

private theorem m8_congruence_dense_wp_closed {xs : Tup Val m8CongruenceDenseFn.as}
    {m : Mem 64} {Q : Post m8CongruenceDenseFn.rs} {X : XPost}
    (hs : m8FidV12Env m8CongruenceDenseFn.name m8CongruenceDenseFn.as
      m8CongruenceDenseFn.rs xs m Q X) :
    Func.wp m8FidV12Env m8CongruenceDenseFn.body xs m Q X :=
  wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_congruence_dense_wp m8FidV12Env
      (fid_row 252) (fid_row 253) (fid_row 254) (fid_row 274)
      (fun _ _ _ _ h => M8FidV12Env.worklist _ _ _ _ h)
      (fid_row 261) xs m Q _
      (m8Fid_elim (List.mem_of_getElem? (i := 275) rfl) hs))

private theorem m8_switch_mode_wp_closed {xs : Tup Val m8SwitchModeM7Fn.as}
    {m : Mem 64} {Q : Post m8SwitchModeM7Fn.rs} {X : XPost}
    (hs : m8FidV12Env m8SwitchModeM7Fn.name m8SwitchModeM7Fn.as m8SwitchModeM7Fn.rs xs m Q X) :
    Func.wp m8FidV12Env m8SwitchModeM7Fn.body xs m Q X := by
  have hmemSw :
      (⟨"full_switch_mode_m7", [i64], [], FullM7Search.m7SwitchModeSpec, true⟩ : SpecEntry) ∈
        m7FidBaseTable :=
    m7FidBase_part3Pfx_mem _ (by
      unfold m7FidRowsPart3Pfx; (iterate 25 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 13) rfl))
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_switch_mode_m7_wp m8FidV12Env
      (fid_row 9) (fid_row 20)
      (fid_mem m7FidBase_emaSwap_mem)
      (fid_row 31)
      (fid_mem m7FidBase_m7Set64_mem) xs m Q _
      (m8Fid_elim hmemSw hs))

private theorem m8_preprocess_wp_closed {xs : Tup Val m8PreprocessM6Fn.as}
    {m : Mem 64} {Q : Post m8PreprocessM6Fn.rs} {X : XPost}
    (hs : m8FidV12Env m8PreprocessM6Fn.name m8PreprocessM6Fn.as m8PreprocessM6Fn.rs xs m Q X) :
    Func.wp m8FidV12Env m8PreprocessM6Fn.body xs m Q X := by
  have hmemPre :
      (⟨"full_preprocess_m6", [i64], [i64], FullM6.fullM6PreprocessSpec, true⟩ : SpecEntry) ∈
        m7FidBaseTable :=
    m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 19) rfl)
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (hf : False) => hf.elim) _ m
    (m8_preprocess_m6_wp m8FidV12Env
      (fun _ _ _ _ h =>
        FullM7Proof.m7_fullPropagate_to_bcpS15 (fid_row 86) _ _ _ _ h)
      (fid_row 104) (fid_row 184) (extra_row 52)
      (fid_mem (m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem).compact)
      (fid_row 32)
      (fid_mem m7FidBase_probeM6_mem
        (hno := fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h))
      xs m Q _ (m8Fid_elim hmemPre hs))

private theorem m8Fid_base_of_ne {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hne1 : nm ≠ "full_cong_enq_var") (hne2 : nm ≠ "full_cong_eval_gate")
    (hne3 : nm ≠ "full_cong_worklist")
    (h : m8FidV12Env nm as bs xs m Q X) :
    m7FidelityEnv nm as bs xs m Q X := by
  cases h with
  | base hb => exact hb
  | enqVar => exact absurd rfl hne1
  | evalGate => exact absurd rfl hne2
  | worklist => exact absurd rfl hne3

private theorem m8Fid_enqVar_wp_of_env {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : m8FidV12Env nm as bs xs m Q X) (hnm : nm = "full_cong_enq_var")
    (has : as = [i64, i64, i32]) (hbs : bs = [])
    (hBase : m7FidelityEnv nm as bs xs m Q X →
      Func.wp m8FidV12Env FullM6CongSubst.full_cong_enq_var_body (has ▸ xs) m (hbs ▸ Q) X) :
    Func.wp m8FidV12Env FullM6CongSubst.full_cong_enq_var_body (has ▸ xs) m (hbs ▸ Q) X := by
  cases h with
  | base hb => exact hBase hb
  | enqVar _ _ _ _ hsp => exact full_cong_enq_var_m8_wp m8FidV12Env _ m _ X hsp
  | evalGate => exact absurd hnm (by decide)
  | worklist => exact absurd hnm (by decide)

private theorem m8Fid_evalGate_wp_of_env {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : m8FidV12Env nm as bs xs m Q X) (hnm : nm = "full_cong_eval_gate")
    (has : as = [i64, i64, i64, i64, i32, i64]) (hbs : bs = [i64])
    (hBase : m7FidelityEnv nm as bs xs m Q X →
      Func.wp m8FidV12Env FullM6CongSubst.full_cong_eval_gate_body (has ▸ xs) m (hbs ▸ Q) X) :
    Func.wp m8FidV12Env FullM6CongSubst.full_cong_eval_gate_body (has ▸ xs) m (hbs ▸ Q) X := by
  cases h with
  | base hb => exact hBase hb
  | evalGate _ _ _ _ hsp => exact m8_eval_gate_wp_closed hsp
  | enqVar => exact absurd hnm (by decide)
  | worklist => exact absurd hnm (by decide)

private theorem m8Fid_worklist_wp_of_env {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : m8FidV12Env nm as bs xs m Q X) (hnm : nm = "full_cong_worklist")
    (has : as = [i64, i64, i64, i64]) (hbs : bs = [i64])
    (hBase : m7FidelityEnv nm as bs xs m Q X →
      Func.wp m8FidV12Env FullM6CongSubst.full_cong_worklist_body (has ▸ xs) m (hbs ▸ Q) X) :
    Func.wp m8FidV12Env FullM6CongSubst.full_cong_worklist_body (has ▸ xs) m (hbs ▸ Q) X := by
  cases h with
  | base hb => exact hBase hb
  | worklist _ _ _ _ hsp => exact m8_worklist_wp_closed hsp
  | enqVar => exact absurd hnm (by decide)
  | evalGate => exact absurd hnm (by decide)

/-- Closed `ModuleOk m8FidV12Env m8FidV12Module` proof across all `413` functions (`0` sorry). -/
theorem m8FidV12_moduleOk : ModuleOk m8FidV12Env m8FidV12Module := by
  refine spliceModule_moduleOk m7Fidelity_moduleOk m8FidV12_acyclic m8FidV12Repls_wf
    (fun _ _ _ _ _ _ _ h => M8FidV12Env.base h) ?_ ?_
  · intro g hg _hnone
    by_cases h1 : g.name = "full_cong_enq_var"
    · refine Or.inl ?_
      have hge := list_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg m7Fid_enqVar_mem h1
      subst g
      intro xs m Q X hs
      dsimp only [FullM6CongSubst.full_cong_enq_var] at xs Q hs ⊢
      refine m8Fid_enqVar_wp_of_env hs rfl rfl rfl fun hb => ?_
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Fid_enqVar_mem
      exact wp_env_mono (fun _ _ _ _ _ _ _ => M8FidV12Env.base) _ m
        ((m7Fidelity_moduleOk.fnsOk pre _ post hsplit).2.2 xs m Q X hb)
    · by_cases h2 : g.name = "full_cong_eval_gate"
      · refine Or.inl ?_
        have hge := list_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg m7Fid_evalGate_mem h2
        subst g
        intro xs m Q X hs
        dsimp only [FullM6CongSubst.full_cong_eval_gate] at xs Q hs ⊢
        refine m8Fid_evalGate_wp_of_env hs rfl rfl rfl fun hb => ?_
        obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Fid_evalGate_mem
        exact wp_env_mono (fun _ _ _ _ _ _ _ => M8FidV12Env.base) _ m
          ((m7Fidelity_moduleOk.fnsOk pre _ post hsplit).2.2 xs m Q X hb)
      · by_cases h3 : g.name = "full_cong_worklist"
        · refine Or.inl ?_
          have hge := list_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg m7Fid_worklist_mem h3
          subst g
          intro xs m Q X hs
          dsimp only [FullM6CongSubst.full_cong_worklist] at xs Q hs ⊢
          refine m8Fid_worklist_wp_of_env hs rfl rfl rfl fun hb => ?_
          obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Fid_worklist_mem
          exact wp_env_mono (fun _ _ _ _ _ _ _ => M8FidV12Env.base) _ m
            ((m7Fidelity_moduleOk.fnsOk pre _ post hsplit).2.2 xs m Q X hb)
        · exact Or.inr (fun _ _ _ _ hs => m8Fid_base_of_ne h1 h2 h3 hs)
  · intro r hr xs m Q X hs
    simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m8_ana_failed_wp_closed hs
    · exact m8_analyze_wp_closed hs
    · exact m8_analyze_core_wp_closed hs
    · exact m8_restart_due_wp_closed hs
    · exact m8_enter_dense_wp_closed hs
    · exact m8_cong_try_xor_ite_wp_closed hs
    · exact m8_congruence_dense_wp_closed hs
    · exact m8_switch_mode_wp_closed hs
    · exact m8_preprocess_wp_closed hs

/-! ## 4. End-to-End `kissat_solve_bytes` Soundness & UNSAT Non-Vacuity (`V12`) -/

/-- Membership of `kissat_solve_bytes` in `m8FidV12Module.fns`. -/
theorem m8FidV12_solveBytes_mem : FullM6Orch.m6oSolveBytesFn ∈ m8FidV12Module.fns :=
  spliceFns_mem_of_ne m7Fidelity_solveBytes_mem fun r hr => by
    simp only [m8FidV12Repls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- End-to-end byte-level soundness of `m8FidV12Module`'s `kissat_solve_bytes`
(`XPost := False`, `0` SAT model proof obligation). -/
theorem m8FidV12_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8FidV12Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8FidV12_solveBytes_mem
  have hfn := (m8FidV12_moduleOk.fnsOk pre _ post hsplit).2.2
  exact hfn _ m _ _ (M8FidV12Env.base (m7FidelityEnv_solve_bytes
    (m7FidSolveBytesSpec_intro hcfit hwfit hm fun r m' hdom h20 _ hm' => ⟨hdom, ⟨h20, hm'⟩⟩)))

/-- Host-frame corollary for `m8FidV12_solve_bytes_sound`. -/
theorem m8FidV12_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost : (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `m8FidV12Module`. -/
theorem m8FidV12_unsat_nv :
    Func.wp m8FidV12Env FullM6Orch.kissat_solve_bytes_body
      (FullM6.nvM6CnfPtr, BitVec.ofNat 64 FullM6.nvM6UnsatBytes.length,
        FullM6.nvM6UnsatWorkPtr, BitVec.ofNat 64 FullM6.nvM6WorkLen, 16#64, ())
      FullM6.nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ FullM6.nvM6UnsatCnf.Unsat ∧
          (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
            region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8FidV12_solveBytes_mem
  have hfn := (m8FidV12_moduleOk.fnsOk pre _ post hsplit).2.2
  have hm0 :
      (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
        region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen ⋆ Std.ExtHashMap.emp)
        FullM6.nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact FullM6.nvM6UnsatInitMem_sep
  exact hfn _ FullM6.nvM6UnsatInitMem _ _
    (M8FidV12Env.base (m7FidelityEnv_solve_bytes
      (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 fun r m' _ _ htr hm' => by
        have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) FullM6.nvM6_unsat_bound
          (by decide) FullM6.nvM6Unsat_header FullM6.nvM6Unsat_unitTrace
        exact ⟨hr20, FullM6.nvM6UnsatCnf_unsat, by
          simpa only [Std.ExtHashMap.sep_emp] using hm'⟩)))

end

end LeanQbe.T.Examples.Kissat.FullM8FidV12
