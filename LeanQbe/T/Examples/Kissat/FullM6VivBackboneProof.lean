module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4c

/-!
# Kissat Wave-2 `PR-W2C` (`RC-20, RC-21`) — Closed `ModuleOk` & Concrete `Mem 64` UNSAT NV

Closes the standalone Wave-2 `PR-W2C` verification suite (`FullM6VivBackbone.lean`,
`FullM6VivBackboneProof{0,1,2a,2b,3a,3b,4a,4b,4c}.lean`, `FullM6VivBackboneProof.lean`;
`0` edits to existing files, `0` custom axioms, `XPost := False`, `0` SAT model proofs):

1. Canonical adapter `full_probe_assume_pair_m6_canon_wp` certifying
   `Full.fullProbeAssumePairSpec` under canonical `Full.fullBacktrackSpec`.
2. Closed `55`-row `m6VivBackboneSpecTable` (`40` owned `_m6` functions + `15` canonical
   externs, all `noExit = true`), `m6VivBackboneSpecTable_nodup`, `m6VivBackboneEnv`, all `40`
   `SpecEntry.Impl` witnesses, and unconditional
   **`m6VivBackbone_moduleOk : ModuleOk m6VivBackboneEnv m6VivBackboneModule`**.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `nvM6F0.Unsat`) on a concrete
   `2588`-byte heap (`nvM6SparseMem`) with UNSAT formula `{(x0), (¬x0)}` and live 3-literal
   arena clause `[x0, x1, x2]` for all `8` headline entrypoints (`full_vivify_m6`,
   `full_backbone_m6`, `full_transitive_m6`, `full_probe_assume_pair_m6`, `full_add_bin_m6`,
   `full_init_fresh_var_m6`, `full_prioritize_binaries_m6`, `full_viv_clause_m6`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Bridge for `full_probe_assume_pair_m6` -/

section ProbeCanonBridge

private theorem m6_otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m6_backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hpr hcl' hps hsc htrl' hvl hw_w hw_o hm' => ?_⟩
  have hshrk : sc'.shrink_stk = s.scratch.shrink_stk := by
    rcases hsc with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hpr hcl' hps hshrk htrl'
    (fun ⟨F0, Fc, hwo⟩ => hvl ⟨F0, Fc, hwo.elim Or.inl (Or.inr ∘ m6_otfs_to_canon)⟩)
    hw_w (fun F0 Fc ho hlt => hw_o F0 Fc (m6_otfs_to_canon ho) hlt) hm'

/-- Canonical `Full.fullProbeAssumePairSpec` certification for `full_probe_assume_pair_m6` under
canonical `Full.fullBacktrackSpec`. -/
theorem full_probe_assume_pair_m6_canon_wp (Γ : Env)
    (hAssign : ∀ args m Q X, Full.fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProbeProp : ∀ args m Q X, FullProbeTransSpecs.fullProbePropExtSpec args m Q X →
      Γ "full_probe_prop" [i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAnalyze : ∀ args m Q X, FullProbeTransSpecs.fullAnalyze20Spec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hPropagate : ∀ args m Q X, Full.fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hFlushHbr : ∀ args m Q X, FullProbeTransSpecs.fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hAddUnit : ∀ args m Q X, Full.fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Func.wp Γ full_probe_assume_pair_m6_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine full_probe_assume_pair_m6_wp Γ hAssign hProbeProp (m6_backtrack_adapter hBacktrack)
    hAnalyze hPropagate hFlushHbr hAddUnit (c.hdr, lit, ()) m Q X
    ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, ⟨ho.1, m6_otfs_to_canon ho.2.1, ho.2.2⟩⟩)
    hcv hfu hr hm'

end ProbeCanonBridge

/-! ## 2. Closed `55`-Row `m6VivBackboneSpecTable`, `m6VivBackboneEnv`, & `ModuleOk` -/

section ModuleOkSection

/-- Closed `55`-row specification table (`40` Wave-2 `PR-W2C` functions + `15` canonical externs,
all `noExit = true`). Headline entrypoints carry exact canonical drop-in specs:
`full_add_bin_m6` (`Full.fullAddBinSpec` / `fullAddBinM6Spec`), `full_init_fresh_var_m6`
(`Full.fullInitFreshVarSpec`), `full_probe_assume_pair_m6` (`Full.fullProbeAssumePairSpec`),
`full_vivify_m6` (`FullFastBveBudgets.fullVivifyFastSpec`), `full_backbone_m6`
(`FullM3Backbone.fullBackboneSpec`), and `full_transitive_m6`
(`FullFastBveBudgets.fullTransitiveFastSpec`). -/
@[expose] def m6VivBackboneSpecTable : List SpecEntry :=
  [ ⟨"full_add_bin_m6", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩
  , ⟨"full_init_fresh_var_m6", [i64, i32], [], Full.fullInitFreshVarSpec, true⟩
  , ⟨"full_probe_assume_pair_m6", [i64, i32], [i64], Full.fullProbeAssumePairSpec, true⟩
  , ⟨"full_viv_unreason_m6", [i64, i32], [], fullVivUnreasonM6Spec, true⟩
  , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64], fullVivWatchRankM6Spec, true⟩
  , ⟨"full_viv_best_watch_m6", [i64, i32], [], fullVivBestWatchM6Spec, true⟩
  , ⟨"full_viv_simplify_m6", [i64, i32], [i64], fullVivSimplifyM6Spec, true⟩
  , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], fullVivCommitM6Spec, true⟩
  , ⟨"full_viv_mark_garb_m6", [i64, i32], [], fullVivMarkGarbM6Spec, true⟩
  , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool], fullVivSubsumesBinM6Spec, true⟩
  , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool], fullVivSubsumesClM6Spec, true⟩
  , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], fullVivDeduceM6Spec, true⟩
  , ⟨"full_viv_best_implied_m6", [i64, i32], [i32], fullVivBestImpliedM6Spec, true⟩
  , ⟨"full_viv_reestablish_m6", [i64, i32], [], fullVivReestablishM6Spec, true⟩
  , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool], fullVivInstCheckM6Spec, true⟩
  , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], fullVivInstM6Spec, true⟩
  , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64], fullVivFinishM6Spec, true⟩
  , ⟨"full_viv_sort_counts_m6", [i64, i32], [], fullVivSortCountsM6Spec, true⟩
  , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], fullVivHasL0M6Spec, true⟩
  , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], fullVivL0SimpM6Spec, true⟩
  , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [], fullVivReusePrefixM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩
  , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], fullVivTierMatchM6Spec, true⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64], fullVivCollectM6Spec, true⟩
  , ⟨"full_viv_count_m6", [i64, i64], [], fullVivCountM6Spec, true⟩
  , ⟨"full_viv_keys_m6", [i64, i64], [], fullVivKeysM6Spec, true⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], [], fullVivSortSchedM6Spec, true⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩
  , ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
  , ⟨"full_prioritize_binaries_m6", [i64], [.bool], fullPrioritizeBinariesM6Spec, true⟩
  , ⟨"full_backbone_sched_m6", [i64], [i64], fullBackboneSchedM6Spec, true⟩
  , ⟨"full_backbone_keep_m6", [i64, i64], [], fullBackboneKeepM6Spec, true⟩
  , ⟨"full_backbone_unwind_m6", [i64, i64, i64], [], fullBackboneUnwindM6Spec, true⟩
  , ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool], fullBackbonePropM6Spec, true⟩
  , ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32], fullBackboneAnalyzeM6Spec, true⟩
  , ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64], fullBackboneRoundM6Spec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], fullTransLitM6Spec, true⟩
  , ⟨"full_trans_sort_m6", [i64, i64], [], fullTransSortM6Spec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_probe_prop", [i64], [i64], FullProbeTransSpecs.fullProbePropExtSpec, true⟩
  , ⟨"full_probe_flush_hbr", [i64, i64], [i64], FullProbeTransSpecs.fullProbeFlushHbrSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], FullProbeTransSpecs.fullAnalyze20Spec, true⟩ ]

theorem m6VivBackboneSpecTable_length : m6VivBackboneSpecTable.length = 55 := rfl

theorem m6VivBackboneSpecTable_nodup : (m6VivBackboneSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m6VivBackboneSpecTable_noExit : ∀ e ∈ m6VivBackboneSpecTable, e.noExit = true := by
  intro e he
  have hall : m6VivBackboneSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m6VivBackboneModule_noExit : m6VivBackboneModule.exits = [] := rfl

/-- Closed environment for `m6VivBackboneModule` (`40` Wave-2 functions + `15` externs). -/
def m6VivBackboneEnv : Env := Env.ofTable m6VivBackboneSpecTable

theorem m6VivBackboneEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6VivBackboneEnv f as bs xs m Q X → m6VivBackboneEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6VivBackboneSpecTable_noExit

private theorem m6VivBackboneEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6VivBackboneSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6VivBackboneEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem
      m6VivBackboneSpecTable_nodup (hno xs m Q X hs)

theorem m6_add_bin_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_add_bin_m6", [i64, i32, i32], [i64], full_add_bin_m6_body⟩
      ⟨"full_add_bin_m6", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_add_bin_m6_ext_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_init_fresh_var_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_init_fresh_var_m6", [i64, i32], [], full_init_fresh_var_m6_body⟩
      ⟨"full_init_fresh_var_m6", [i64, i32], [], Full.fullInitFreshVarSpec, true⟩ :=
  SpecEntry.Impl.of (full_init_fresh_var_m6_wp m6VivBackboneEnv)

theorem m6_probe_assume_pair_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_probe_assume_pair_m6", [i64, i32], [i64], full_probe_assume_pair_m6_body⟩
      ⟨"full_probe_assume_pair_m6", [i64, i32], [i64], Full.fullProbeAssumePairSpec, true⟩ :=
  SpecEntry.Impl.of (full_probe_assume_pair_m6_canon_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_unreason_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_unreason_m6", [i64, i32], [], full_viv_unreason_m6_body⟩
      ⟨"full_viv_unreason_m6", [i64, i32], [], fullVivUnreasonM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_unreason_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_watch_rank_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_watch_rank_m6", [i64, i32], [i64], full_viv_watch_rank_m6_body⟩
      ⟨"full_viv_watch_rank_m6", [i64, i32], [i64], fullVivWatchRankM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_watch_rank_m6_wp m6VivBackboneEnv)

theorem m6_viv_best_watch_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_best_watch_m6", [i64, i32], [], full_viv_best_watch_m6_body⟩
      ⟨"full_viv_best_watch_m6", [i64, i32], [], fullVivBestWatchM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_best_watch_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_simplify_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_simplify_m6", [i64, i32], [i64], full_viv_simplify_m6_body⟩
      ⟨"full_viv_simplify_m6", [i64, i32], [i64], fullVivSimplifyM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_simplify_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_commit_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], full_viv_commit_m6_body⟩
      ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], fullVivCommitM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_commit_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_mark_garb_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_mark_garb_m6", [i64, i32], [], full_viv_mark_garb_m6_body⟩
      ⟨"full_viv_mark_garb_m6", [i64, i32], [], fullVivMarkGarbM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_mark_garb_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_subsumes_bin_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool], full_viv_subsumes_bin_m6_body⟩
      ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool], fullVivSubsumesBinM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_subsumes_bin_m6_wp m6VivBackboneEnv)

theorem m6_viv_subsumes_cl_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool], full_viv_subsumes_cl_m6_body⟩
      ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool], fullVivSubsumesClM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_subsumes_cl_m6_wp m6VivBackboneEnv)

theorem m6_viv_deduce_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], full_viv_deduce_m6_body⟩
      ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], fullVivDeduceM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_deduce_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_best_implied_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_best_implied_m6", [i64, i32], [i32], full_viv_best_implied_m6_body⟩
      ⟨"full_viv_best_implied_m6", [i64, i32], [i32], fullVivBestImpliedM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_best_implied_m6_wp m6VivBackboneEnv)

theorem m6_viv_reestablish_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_reestablish_m6", [i64, i32], [], full_viv_reestablish_m6_body⟩
      ⟨"full_viv_reestablish_m6", [i64, i32], [], fullVivReestablishM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_reestablish_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_inst_check_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool], full_viv_inst_check_m6_body⟩
      ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool], fullVivInstCheckM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_inst_check_m6_wp m6VivBackboneEnv)

theorem m6_viv_inst_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], full_viv_inst_m6_body⟩
      ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], fullVivInstM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_inst_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_finish_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64], full_viv_finish_m6_body⟩
      ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
        fullVivFinishM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_finish_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_sort_counts_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_sort_counts_m6", [i64, i32], [], full_viv_sort_counts_m6_body⟩
      ⟨"full_viv_sort_counts_m6", [i64, i32], [], fullVivSortCountsM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_sort_counts_m6_wp m6VivBackboneEnv)

theorem m6_viv_has_l0_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], full_viv_has_l0_m6_body⟩
      ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], fullVivHasL0M6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_has_l0_m6_wp m6VivBackboneEnv)

theorem m6_viv_l0_simp_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], full_viv_l0_simp_m6_body⟩
      ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], fullVivL0SimpM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_l0_simp_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_reuse_prefix_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [], full_viv_reuse_prefix_m6_body⟩
      ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [], fullVivReusePrefixM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_reuse_prefix_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_clause_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_clause_m6", [i64, i32], [i64], full_viv_clause_m6_body⟩
      ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_clause_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_tier_match_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], full_viv_tier_match_m6_body⟩
      ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], fullVivTierMatchM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_tier_match_m6_wp m6VivBackboneEnv)

theorem m6_viv_collect_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_collect_m6", [i64, i64], [i64], full_viv_collect_m6_body⟩
      ⟨"full_viv_collect_m6", [i64, i64], [i64], fullVivCollectM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_collect_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_viv_count_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_count_m6", [i64, i64], [], full_viv_count_m6_body⟩
      ⟨"full_viv_count_m6", [i64, i64], [], fullVivCountM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_count_m6_wp m6VivBackboneEnv)

theorem m6_viv_keys_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_keys_m6", [i64, i64], [], full_viv_keys_m6_body⟩
      ⟨"full_viv_keys_m6", [i64, i64], [], fullVivKeysM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_keys_m6_wp m6VivBackboneEnv)

theorem m6_viv_sort_sched_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_sort_sched_m6", [i64, i64], [], full_viv_sort_sched_m6_body⟩
      ⟨"full_viv_sort_sched_m6", [i64, i64], [], fullVivSortSchedM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_sort_sched_m6_wp m6VivBackboneEnv)

theorem m6_viv_clear_tier_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_viv_clear_tier_m6", [i64, i64], [], full_viv_clear_tier_m6_body⟩
      ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_clear_tier_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_vivify_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_vivify_m6", [i64, i64, i64], [i64], full_vivify_m6_body⟩
      ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩ :=
  SpecEntry.Impl.of (full_vivify_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_prioritize_binaries_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_prioritize_binaries_m6", [i64], [.bool], full_prioritize_binaries_m6_body⟩
      ⟨"full_prioritize_binaries_m6", [i64], [.bool], fullPrioritizeBinariesM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_prioritize_binaries_m6_wp m6VivBackboneEnv)

theorem m6_backbone_sched_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_sched_m6", [i64], [i64], full_backbone_sched_m6_body⟩
      ⟨"full_backbone_sched_m6", [i64], [i64], fullBackboneSchedM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_sched_m6_wp m6VivBackboneEnv)

theorem m6_backbone_keep_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_keep_m6", [i64, i64], [], full_backbone_keep_m6_body⟩
      ⟨"full_backbone_keep_m6", [i64, i64], [], fullBackboneKeepM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_keep_m6_wp m6VivBackboneEnv)

theorem m6_backbone_unwind_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_unwind_m6", [i64, i64, i64], [], full_backbone_unwind_m6_body⟩
      ⟨"full_backbone_unwind_m6", [i64, i64, i64], [], fullBackboneUnwindM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_unwind_m6_wp m6VivBackboneEnv)

theorem m6_backbone_prop_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool], full_backbone_prop_m6_body⟩
      ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool], fullBackbonePropM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_prop_m6_wp m6VivBackboneEnv)

theorem m6_backbone_analyze_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32], full_backbone_analyze_m6_body⟩
      ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32],
        fullBackboneAnalyzeM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_analyze_m6_wp m6VivBackboneEnv)

theorem m6_backbone_round_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64], full_backbone_round_m6_body⟩
      ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64], fullBackboneRoundM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_round_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_backbone_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_backbone_m6", [i64, i64], [i64], full_backbone_m6_body⟩
      ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩ :=
  SpecEntry.Impl.of (full_backbone_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_trans_lit_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], full_trans_lit_m6_body⟩
      ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], fullTransLitM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_trans_lit_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6_trans_sort_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_trans_sort_m6", [i64, i64], [], full_trans_sort_m6_body⟩
      ⟨"full_trans_sort_m6", [i64, i64], [], fullTransSortM6Spec, true⟩ :=
  SpecEntry.Impl.of (full_trans_sort_m6_wp m6VivBackboneEnv)

theorem m6_transitive_impl :
    SpecEntry.Impl m6VivBackboneEnv
      ⟨"full_transitive_m6", [i64, i64], [i64], full_transitive_m6_body⟩
      ⟨"full_transitive_m6", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩ :=
  SpecEntry.Impl.of (full_transitive_m6_wp m6VivBackboneEnv
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h))
    (m6VivBackboneEnv_row (by simp [m6VivBackboneSpecTable]) (fun _ _ _ _ h => h)))

theorem m6VivBackbone_allFns_wf : AllFns Fn.Wf m6VivBackboneModule.fns :=
  ⟨full_add_bin_m6_wf, full_init_fresh_var_m6_wf, full_probe_assume_pair_m6_wf,
    full_viv_unreason_m6_wf, full_viv_watch_rank_m6_wf, full_viv_best_watch_m6_wf,
    full_viv_simplify_m6_wf, full_viv_commit_m6_wf, full_viv_mark_garb_m6_wf,
    full_viv_subsumes_bin_m6_wf, full_viv_subsumes_cl_m6_wf, full_viv_deduce_m6_wf,
    full_viv_best_implied_m6_wf, full_viv_reestablish_m6_wf, full_viv_inst_check_m6_wf,
    full_viv_inst_m6_wf, full_viv_finish_m6_wf, full_viv_sort_counts_m6_wf,
    full_viv_has_l0_m6_wf, full_viv_l0_simp_m6_wf, full_viv_reuse_prefix_m6_wf,
    full_viv_clause_m6_wf, full_viv_tier_match_m6_wf, full_viv_collect_m6_wf,
    full_viv_count_m6_wf, full_viv_keys_m6_wf, full_viv_sort_sched_m6_wf,
    full_viv_clear_tier_m6_wf, full_vivify_m6_wf, full_prioritize_binaries_m6_wf,
    full_backbone_sched_m6_wf, full_backbone_keep_m6_wf, full_backbone_unwind_m6_wf,
    full_backbone_prop_m6_wf, full_backbone_analyze_m6_wf, full_backbone_round_m6_wf,
    full_backbone_m6_wf, full_trans_lit_m6_wf, full_trans_sort_m6_wf, full_transitive_m6_wf,
    trivial⟩

theorem m6VivBackbone_tableImpl :
    TableImpl m6VivBackboneEnv m6VivBackboneModule.fns m6VivBackboneSpecTable :=
  ⟨m6_add_bin_impl, m6_init_fresh_var_impl, m6_probe_assume_pair_impl,
    m6_viv_unreason_impl, m6_viv_watch_rank_impl, m6_viv_best_watch_impl,
    m6_viv_simplify_impl, m6_viv_commit_impl, m6_viv_mark_garb_impl,
    m6_viv_subsumes_bin_impl, m6_viv_subsumes_cl_impl, m6_viv_deduce_impl,
    m6_viv_best_implied_impl, m6_viv_reestablish_impl, m6_viv_inst_check_impl,
    m6_viv_inst_impl, m6_viv_finish_impl, m6_viv_sort_counts_impl,
    m6_viv_has_l0_impl, m6_viv_l0_simp_impl, m6_viv_reuse_prefix_impl,
    m6_viv_clause_impl, m6_viv_tier_match_impl, m6_viv_collect_impl,
    m6_viv_count_impl, m6_viv_keys_impl, m6_viv_sort_sched_impl,
    m6_viv_clear_tier_impl, m6_vivify_impl, m6_prioritize_binaries_impl,
    m6_backbone_sched_impl, m6_backbone_keep_impl, m6_backbone_unwind_impl,
    m6_backbone_prop_impl, m6_backbone_analyze_impl, m6_backbone_round_impl,
    m6_backbone_impl, m6_trans_lit_impl, m6_trans_sort_impl, m6_transitive_impl, trivial⟩

/-- Unconditional `ModuleOk` certifying all `40` Wave-2 `PR-W2C` functions under the closed
`55`-row `m6VivBackboneEnv`. -/
theorem m6VivBackbone_moduleOk : ModuleOk m6VivBackboneEnv m6VivBackboneModule :=
  Env.ofTable_moduleOk m6VivBackbone_acyclic m6VivBackbone_allFns_wf m6VivBackbone_tableImpl

end ModuleOkSection

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `nvM6F0.Unsat`) -/

section ConcreteNonVacuity

/-- Minimal UNSAT formula `{(x0), (¬x0)}` over variables `{0, 1, 2}`. -/
def nvM6F0 : CNF Nat := cnfOfClauses [[0], [1]]

theorem nvM6F0_unsat : nvM6F0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM6F0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM6F0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `FullCfg` (`hdr = 0x1000#64`, `avail = 2588`, `max_vars = 3`, `arena_cap = 6`,
`wcap = 1`, `scratch_cap = 128`, `slack = 0`). -/
@[expose] def nvM6Cfg : FullCfg where
  hdr := 0x1000#64
  avail := 2588
  mv := 3
  max_vars := 3
  bva_cap := 0
  nc := 2
  arena_cap := 6
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 128
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

private def nvM6Scratch : FullScratch where
  heap_len := 0
  scinc := 0#64
  rel_period := 0#64
  rel_limit := 0#64
  rel_wait := 0#64
  rel_u := 0#64
  rel_v := 0#64
  rel_trigger := 0#64
  conflicts := 0#64
  learned_lits := 0#64
  min_removed := 0#64
  delayed_len := 0
  stable := 0#64
  switched := 0#64
  mode_count := 0#64
  mode_confl_lim := 0#64
  mode_tick_lim := 0#64
  mode_saved_ticks := 0#64
  search_ticks := 0#64
  q_first := 0#64
  q_last := 0#64
  q_search_idx := 0#64
  q_search_stamp := 0#64
  q_cur_stamp := 0#64
  target_assigned := 0#64
  best_assigned := 0#64
  rephase_limit := 0#64
  rephased := 0#64
  reduce_limit := 0#64
  reductions := 0#64
  tier1 := 2#64
  tier2 := 6#64
  restarts := 0#64
  restart_limit := 0#64
  ema_fast_biased := 0#64
  ema_fast_exp := 0#64
  ema_slow_biased := 0#64
  ema_slow_exp := 0#64
  extend_len := 0
  rng_state := 1#64
  chrono_levels := 0#64
  otfs_cnt := 0#64
  eager_sub_cnt := 0#64
  probe_limit := 0#64
  probings := 0#64
  elim_limit := 0#64
  eliminations := 0#64
  elim_bound := 0#64
  iterating := 0#64
  hbr_cnt := 0#64
  trans_cnt := 0#64
  viv_cnt := 0#64
  subst_cnt := 0#64
  cong_cnt := 0#64
  sweep_cnt := 0#64
  bve_cnt := 0#64
  bce_cnt := 0#64
  bva_cnt := 0#64
  walk_cnt_stat := 0#64
  fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64
  ant_sz := 0#64
  res_sz := 0#64
  walk_vals := List.replicate 6 0#8
  phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8
  phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8
  heap := List.replicate 3 0#32
  pos := List.replicate 3 0#32
  shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0#32
  q_next := List.replicate 3 0#32
  q_stamp := List.replicate 3 0#32
  wsort := List.replicate 6 0#32
  work_stk1 := List.replicate 6 0#32
  work_stk2 := List.replicate 6 0#32
  tarjan_mark := List.replicate 6 0#32
  tarjan_reach := List.replicate 6 0#32
  score := List.replicate 3 0#64
  sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := List.replicate 128 0#32

/-- Concrete sparse-mode UNSAT state with 1 live 3-literal arena clause `[x0, x1, x2]` at
`cref = 0` and cleared `last_learned[0..15] = 0xFFFFFFFFu`. -/
def nvM6SparseState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 3, unassigned := 3#64
      arena_len := 6, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 1#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 100#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := List.replicate 6 0#8
      lit_mark := List.replicate 6 0#8
      mrk := List.replicate 3 0#8
      flags := List.replicate 3 1#32
      lvl := List.replicate 3 0#32
      rsns := List.replicate 3 0xFFFFFFFF#32
      trl := List.replicate 3 0#32
      trail_pos := List.replicate 3 0#32
      tmp := [0#32, 2#32, 4#32]
      min_clr := List.replicate 3 0#32
      frame_trail := List.replicate 4 0#32
      frame_dec := List.replicate 4 0#32
      wvec := List.replicate 12 0#32
      repr := List.replicate 6 0#32
      min_stk := List.replicate 8 0#32
      arena := [0#32, 0#32, 3#32, 0#32, 2#32, 4#32]
      wstk := [0#32] }
  scratch := nvM6Scratch

private def nvM6BlockHdr : List UInt8 :=
  bytes64 [3#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM6Cfg nvM6SparseState)

private def nvM6BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM6SparseState.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM6SparseState.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM6SparseState.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM6SparseState.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM6SparseState.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM6SparseState.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM6SparseState.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM6SparseState.scratch.walk_best ++ List.replicate 5 0)

private def nvM6BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM6SparseState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.trail_pos ++ List.replicate 4 0)

private def nvM6BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM6SparseState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.scratch.shrink_stk ++ List.replicate 4 0)

private def nvM6BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM6SparseState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM6SparseState.core.frame_dec ++ List.replicate 0 0)

private def nvM6BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM6SparseState.core.wvec ++
  bytesOf (t := i32) nvM6SparseState.core.repr ++
  bytesOf (t := i32) nvM6SparseState.scratch.wsort ++
  bytesOf (t := i32) nvM6SparseState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM6SparseState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM6SparseState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM6SparseState.scratch.tarjan_reach ++
  bytes64 nvM6SparseState.scratch.score ++
  bytes64 nvM6SparseState.scratch.sim_sig

private def nvM6BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM6SparseState.core.min_stk ++
  bytesOf (t := i32) nvM6SparseState.scratch.glue_used ++
  bytesOf (t := i32) nvM6SparseState.scratch.last_learned ++
  bytesOf (t := i32) nvM6SparseState.core.arena ++
  bytesOf (t := i32) nvM6SparseState.core.wstk ++
  bytesOf (t := i32) nvM6SparseState.scratch.delayed ++
  bytesOf (t := i32) nvM6SparseState.scratch.red_refs ++
  bytesOf (t := i32) nvM6SparseState.scratch.extend_stk ++
  bytesOf (t := i32) nvM6SparseState.scratch.scratch_buf ++
  List.replicate 0 0

private def nvM6Bytes : List UInt8 :=
  nvM6BlockHdr ++ nvM6BlockBytes ++ nvM6BlockU32A ++ nvM6BlockU32B ++
  nvM6BlockU32C ++ nvM6BlockWvec ++ nvM6BlockTail

/-- Concrete `2588`-byte sparse-mode `Mem 64` heap mapped at `nvM6Cfg.hdr` (`0x1000#64`). -/
def nvM6SparseMem : Mem 64 := nvM6Bytes.At nvM6Cfg.hdr

private theorem m6_nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem m6_nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
    m6_nv_sep_append (by rw [bytesOf_length, hn])
      (by rw [bytesOf_length, List.length_replicate]; omega)
      (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem m6_nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem m6_nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem m6_nv_join {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], m6_nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem m6_nv_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem m6_nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem m6_nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

theorem nvM6SparseMem_ok : FullMem nvM6Cfg nvM6SparseState nvM6SparseMem := by
  let c := nvM6Cfg
  let s := nvM6SparseState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv3 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv6 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv16 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hHdr : nvM6BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM6BlockHdr.At c.hdr) :=
    m6_nv_join
      (m6_nv_arr64_p (a := c.hdr) (xs := [3#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (m6_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvM6BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM6BlockBytes.At c.pVals) := by
    have h1 := m6_nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide)
    have h2 := m6_nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2 rfl
      (by decide)
    have h3 := m6_nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2 rfl
      (by decide)
    have h4 := m6_nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide)
    have h5 := m6_nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5 rfl
      (by decide)
    have h6 := m6_nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 3 5
      rfl (by decide)
    have h7 := m6_nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5 rfl
      (by decide)
    have h8 := m6_nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_reorg (m6_nv_join h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => m6_nv_zip4 hm
    have h12345 := m6_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m6_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m6_nv_join h123456 h7 (by decide) (by decide)
    have hall := m6_nv_join h1234567 h8 (by decide) (by decide)
    exact m6_nv_reorg hall fun _ hm => by
      have hfin := m6_nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv6, hmv3]; simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM6BlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM6BlockU32A.At c.pFlags) := by
    have h1 := m6_nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4 rfl (by decide)
    have h2 := m6_nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide)
    have h3 := m6_nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4 rfl (by decide)
    have h4 := m6_nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide)
    have h5 := m6_nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4 rfl
      (by decide)
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_join h123 h4 (by decide) (by decide)
    exact m6_nv_reorg (m6_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv12]; exact sep_ac hm
  have hU32B : nvM6BlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM6BlockU32B.At c.pTmp) := by
    have h1 := m6_nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide)
    have h2 := m6_nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4 rfl (by decide)
    have h3 := m6_nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide)
    have h4 := m6_nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4 rfl
      (by decide)
    have h5 := m6_nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4 rfl
      (by decide)
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_join h123 h4 (by decide) (by decide)
    exact m6_nv_reorg (m6_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv12]; exact sep_ac hm
  have hU32C : nvM6BlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM6BlockU32C.At c.pQPrev) := by
    have h1 := m6_nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4 rfl
      (by decide)
    have h2 := m6_nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4 rfl
      (by decide)
    have h3 := m6_nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4 rfl
      (by decide)
    have h4 := m6_nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0 rfl
      (by decide)
    have h5 := m6_nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0 rfl
      (by decide)
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_join h123 h4 (by decide) (by decide)
    exact m6_nv_reorg (m6_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv12, hmv16]; exact sep_ac hm
  have hWvec : nvM6BlockWvec.length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM6BlockWvec.At c.pWvec) := by
    have h1 := m6_nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide)
    have h2 := m6_nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide)
    have h3 := m6_nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide)
    have h4 := m6_nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24 rfl
      (by decide)
    have h5 := m6_nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24 rfl
      (by decide)
    have h6 := m6_nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24 rfl
      (by decide)
    have h7 := m6_nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24 rfl
      (by decide)
    have h8 := m6_nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide)
    have h9 := m6_nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide)
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_join h123 h4 (by decide) (by decide)
    have h12345 := m6_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m6_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m6_nv_join h123456 h7 (by decide) (by decide)
    have h12345678 := m6_nv_join h1234567 h8 (by decide) (by decide)
    exact m6_nv_reorg (m6_nv_join h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM6BlockTail.length = 892 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM6BlockTail.At c.pMinStk) := by
    have h1 := m6_nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide)
    have h2 := m6_nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := m6_nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := m6_nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := m6_nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := m6_nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := m6_nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := m6_nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := m6_nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 512 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := m6_nv_join h1 h2 (by decide) (by decide)
    have h123 := m6_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m6_nv_join h123 h4 (by decide) (by decide)
    have h12345 := m6_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m6_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m6_nv_join h123456 h7 (by decide) (by decide)
    have h12345678 := m6_nv_join h1234567 h8 (by decide) (by decide)
    have h123456789 := m6_nv_join h12345678 h9 (by decide) (by decide)
    exact m6_nv_reorg (m6_nv_join h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := m6_nv_join hHdr hBytes (by decide) (by decide)
  have h02 := m6_nv_join h01 hU32A (by decide) (by decide)
  have h03 := m6_nv_join h02 hU32B (by decide) (by decide)
  have h04 := m6_nv_join h03 hU32C (by decide) (by decide)
  have h05 := m6_nv_join h04 hWvec (by decide) (by decide)
  exact (m6_nv_reorg (m6_nv_join h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

private theorem nvM6_entails_cons0 (tl : List Nat) :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause (0 :: tl)) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 ⊢
  obtain ⟨lit, hm, heq⟩ := h0
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvM6_lengths : nvM6SparseState.LengthsOk nvM6Cfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvM6_witness : FullWitnessInv nvM6Cfg nvM6F0 [[0], [1]] nvM6SparseState.core := by
  let k := nvM6SparseState.core
  have hrefs : fullArenaClauseRefsCore k = [0] := by
    unfold fullArenaClauseRefsCore; dsimp only [k]; decide
  have hwat : ModeWatchesInv [[0], [1]] k := by
    unfold ModeWatchesInv
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · dsimp only [k, nvM6SparseState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · dsimp only [k, nvM6SparseState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [fullWatchSizeCore, k, nvM6SparseState] at hp
    · dsimp only [k, nvM6SparseState] at h1
      rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [fullWatchSizeCore, k, nvM6SparseState] at hp
    · dsimp only [k, nvM6SparseState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 3 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inr (by decide),
        fun r hr => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          exact ⟨by decide, by decide, by decide, by decide, Or.inl (by decide)⟩,
        fun r hr hsh => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          exact absurd (by decide) hsh,
        fun r hr _ l hl => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
          rw [hlits] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl <;> decide,
        fun r hr _ => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
          rw [hlits]; exact nvM6_entails_cons0 [2, 4]⟩
      watches := hwat
      cur_level_le := Nat.le_refl 0
      trail_lits_lt := fun _ hi => by cases hi
      trail_vars_nodup := fun _ _ hi => by cases hi
      vals_domain := fun l hl => by
        dsimp only [nvM6SparseState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl rfl
      vals_true_iff := fun l hl => by
        dsimp only [nvM6SparseState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by cases hi)⟩
      vals_false_iff := fun l hl => by
        dsimp only [nvM6SparseState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by cases hi)⟩
      lvl_le := fun _ hi => by cases hi
      dec_earliest := fun _ _ hi => by cases hi
      levels_inhabited := fun _ h1 h2 => by dsimp only [nvM6SparseState] at h2; omega
      level0_sound := fun _ hi => by cases hi
      trail_pos_inv := fun _ hi => by cases hi
      level0_rsn_none := fun _ hi => by cases hi
      frame_trail_lt := fun L hL => by
        dsimp only [nvM6SparseState] at hL; obtain rfl : L = 0 := by omega
        exact Nat.le_refl 0
      frame_trail_mono := fun L1 L2 hL12 hL2 => by
        dsimp only [nvM6SparseState] at hL2
        obtain rfl : L2 = 0 := by omega
        obtain rfl : L1 = 0 := by omega
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ h1 h2 => by dsimp only [nvM6SparseState] at h2; omega
      frame_dec_lt := fun _ h1 h2 => by dsimp only [nvM6SparseState] at h2; omega
      reason_inv := fun _ hi => by cases hi
      reason_lit_mem := fun _ hi => by cases hi }

private theorem nvM6_marks : FullLitMarksClear nvM6Cfg nvM6SparseState := by
  refine ⟨fun v hv => ?_, fun l hl => ?_⟩
  · dsimp only [nvM6Cfg] at hv
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl
  · dsimp only [nvM6Cfg] at hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem nvM6_nodup : FullArenaVarsNodup nvM6SparseState := by
  intro r hr _
  have hrefs : fullArenaClauseRefs nvM6SparseState = [0] := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; decide
  rw [hrefs, List.mem_singleton] at hr; subst hr; decide

private theorem nvM6_ext : FullExtScratchOk nvM6Cfg nvM6SparseState :=
  ⟨FullLastLearnedWf.of_cleared fun i hi => by
    simp only [nvM6SparseState, nvM6Scratch, List.getElem?_replicate, show i < 16 by omega,
      ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

theorem nvM6Sparse_invW : FullSparseInvW nvM6Cfg nvM6F0 [[0], [1]] nvM6SparseState :=
  ⟨nvM6_lengths, nvM6_witness, nvM6_marks, nvM6_nodup, nvM6_ext, rfl⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_vivify_m6`. -/
theorem nv_m6_vivify :
    Func.wp m6VivBackboneEnv full_vivify_m6_body (nvM6Cfg.hdr, 0#64, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_vivify_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, nvM6SparseState, emp, rfl, nvM6Sparse_invW.toSparse, hm,
      fun r s' m' hsp _ _ hnz _ hr _ hm' => by
        obtain ⟨hcl0, hpr0⟩ := hnz (by decide)
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hpr0, hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_backbone_m6`. -/
theorem nv_m6_backbone :
    Func.wp m6VivBackboneEnv full_backbone_m6_body (nvM6Cfg.hdr, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_backbone_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, nvM6SparseState, emp, rfl, nvM6Sparse_invW.toSparse, hm,
      fun r s' m' hsp hcl0 hpr0 _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hpr0, hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_transitive_m6`. -/
theorem nv_m6_transitive :
    Func.wp m6VivBackboneEnv full_transitive_m6_body (nvM6Cfg.hdr, 10#64, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_transitive_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, nvM6SparseState, emp, rfl, nvM6Sparse_invW.toSparse, hm,
      fun r s' m' hsp hcl0 hpr0 _ _ hr _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨s', hsp, hcl0 rfl, hpr0 rfl, hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_assume_pair_m6`. -/
theorem nv_m6_probe_assume_pair :
    Func.wp m6VivBackboneEnv full_probe_assume_pair_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_probe_assume_pair_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, nvM6SparseState, emp, rfl, nvM6Sparse_invW.toSparse, rfl, by decide, rfl, hm,
      fun r s' m' _ _ _ _ hr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_add_bin_m6`. -/
theorem nv_m6_add_bin :
    Func.wp m6VivBackboneEnv full_add_bin_m6_body (nvM6Cfg.hdr, 0#32, 2#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullWitnessInv nvM6Cfg nvM6F0 [[0], [1]] s'.core ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_add_bin_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, [[0], [1]], nvM6SparseState, emp, rfl, nvM6_lengths, nvM6_witness, rfl,
      fun _ _ => nvM6_entails_cons0 [2], hm,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' _ hw hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hw, hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_init_fresh_var_m6`. -/
theorem nv_m6_init_fresh_var :
    Func.wp m6VivBackboneEnv full_init_fresh_var_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun () m' => ∃ s', s'.LengthsOk nvM6Cfg ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_init_fresh_var_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6SparseState, emp, rfl, nvM6_lengths, by decide, hm,
      fun _ _ _ _ _ _ _ _ m' hlen _ _ _ _ _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_prioritize_binaries_m6`. -/
theorem nv_m6_prioritize_binaries :
    Func.wp m6VivBackboneEnv full_prioritize_binaries_m6_body (nvM6Cfg.hdr, ()) nvM6SparseMem
      (fun (_ok, ()) m' => ∃ s',
        FullSparseInvW nvM6Cfg nvM6F0 [[0], [1]] s' ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_prioritize_binaries_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, [[0], [1]], nvM6SparseState, emp, rfl, nvM6Sparse_invW, hm,
      fun _ _ _ m' hsp hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hsp, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clause_m6`. -/
theorem nv_m6_viv_clause :
    Func.wp m6VivBackboneEnv full_viv_clause_m6_body (nvM6Cfg.hdr, 0#32, ()) nvM6SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM6Cfg nvM6F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM6F0.Unsat ∧ FullMem nvM6Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM6Cfg nvM6SparseState ⋆ emp) nvM6SparseMem := by
    rw [sep_emp]; exact nvM6SparseMem_ok
  exact m6_viv_clause_impl.2 _ _ _ _
    ⟨nvM6Cfg, nvM6F0, [[0], [1]], nvM6SparseState, emp, rfl, nvM6Sparse_invW,
      List.mem_singleton.mpr rfl, hm,
      fun r s' m' hsp _ _ _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM6F0_unsat, hm'⟩⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
