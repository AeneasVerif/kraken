module

public import LeanQbe.T.Examples.Kissat.FullM5OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
import LeanQbe.T.Examples.Kissat.DimacsLemmas
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas3
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` M5 Orchestration Proofs (`FullM5OrchProof`, `19/19` Functions & Top-Level NV)

Completes standalone certification of `PR-W1E` (`FullM5Orch` covering `RC-14` & `RC-15`) on
`m5/w1e-orch-prep`:
1. Parametric `(Γ : Env)` `Func.wp` proofs for the remaining `4` M5 orchestrators:
   - `full_preprocess_m5_wp` (`full_lucky`, no eager confl-0 `full_eliminate`, initial compact,
     uncapped `full_scale_delta_m5` limits) against `FullM4.m4PreprocessSpec`.
   - `full_simplify_m5_wp` (no redundant `full_reduce` / `full_reorder`) against
     `FullM4.m4SimplifySpec`.
   - `full_search_m5_wp` (`search.c:195-224` dispatch, linear `10k` reorder cadence, no startup
     warmup) against `FullM4.m4SearchSpec`.
   - `kissat_solve_bytes_m5_core_wp` & `kissat_solve_bytes_m5_wp` against `Full.fullSolveBytesSpec`.
2. Closed `70`-row specification table `m5OrchSpecTable` (`19` owned `_m5` fns + `51` canonical
   externs), `mkM5OrchEnv`, `m5OrchEnv`, `m5OrchUnsatEnv`, and `m5Orch_moduleOk`.
3. Headline UNSAT soundness `m5Orch_solve_bytes_correct` and concrete `Mem 64` UNSAT non-vacuity
   `m5Orch_unsat_nonvacuous` (`XPost := False`, `4096`-byte workspace, `fuel = 16`, `0` SAT proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `70`-Row `m5OrchSpecTable`, `mkM5OrchEnv`, & Structural Lemmas -/

section SpecTable

/-- Closed `70`-row specification table aligned 1-to-1 with `m5Orch_fns ++ m5OrchExterns`
(`19` owned M5 functions + `51` canonical externs, all `noExit`). -/
def m5OrchSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  [ ⟨"full_calc_ext_cap_m5", [i64], [i64], fullCalcExtCapM5Spec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], fullCalcScrCapM5Spec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  , ⟨"full_probe_dticks_m5", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  , ⟨"full_elim_dticks_m5", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  , ⟨"full_trans_lit_m5", [i64, i32], [.bool], Full.fullTransLitSpec, true⟩
  , ⟨"full_transitive_m5", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  , ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64], fullVivifyTierM5Spec, true⟩
  , ⟨"full_vivify_m5", [i64], [i64], m5VivifySpec, true⟩
  , ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_probe_tail_m5", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  , ⟨"full_reduce_m5", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  , ⟨"full_reorder_m5", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_probe_m5", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  , ⟨"full_eliminate_m5", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  , ⟨"full_simplify_m5", [i64, .bool, .bool], [i64], FullM4.m4SimplifySpec, true⟩
  , ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  , ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], Full.fullInitArenasSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩
  , ⟨"full_zero_tables1", [i64], [], Full.fullZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], Full.fullZeroTables2Spec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  , ⟨"full_switch_mode", [i64], [], Full.fullSwitchModeSpec, true⟩
  , ⟨"full_rephase", [i64], [], Full.fullRephaseSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  , ⟨"full_decide", [i64], [i64], Full.fullDecideSpec, true⟩
  , ⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩
  , ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], Full.fullLuckySpec, true⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  , ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], FullM4Sweep.m4SweepVarSpec, true⟩
  , ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  , ⟨"full_viv_collect_m4", [i64, i64], [i64], FullM4VivBce.fullVivCollectM4Spec, true⟩
  , ⟨"full_viv_keys_m4", [i64, i64], [], FullM4VivBce.fullVivKeysM4Spec, true⟩
  , ⟨"full_viv_sort_sched_m4", [i64, i64], [], FullM4VivBce.fullVivSortSchedM4Spec, true⟩
  , ⟨"full_viv_clause_m4", [i64, i32], [i64], FullM4VivBce.fullVivClauseM4Spec, true⟩
  , ⟨"full_viv_clear_tier_m4", [i64, i64], [], FullM4VivBce.fullVivClearTierM4Spec, true⟩
  , ⟨"full_reorder_queue", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
  , ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
  ]

def mkM5OrchEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m5OrchSpecTable mainSpec)

/-- Closed UNSAT-only environment for `FullM5Orch.m5OrchModule`. -/
def m5OrchEnv : Env := mkM5OrchEnv fullSolveBytesSpec

/-- Closed concrete UNSAT non-vacuity environment for `FullM5Orch.m5OrchModule`. -/
def m5OrchUnsatEnv : Env := mkM5OrchEnv fullUnsatWitnessSpec

theorem m5OrchSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m5OrchSpecTable mainSpec, e.noExit = true := by
  intro e he
  have hall : (m5OrchSpecTable mainSpec).all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5OrchSpecTable_sigs (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m5OrchSpecTable mainSpec).map (fun e => (e.name, e.as, e.rs)) = m5OrchModule.sigs := by
  t_kernel_rfl

theorem m5OrchSpecTable_length (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m5OrchSpecTable mainSpec).length = 70 := by
  have hs := congrArg List.length (m5OrchSpecTable_sigs mainSpec)
  have hl : m5OrchModule.sigs.length = 70 := by t_kernel_rfl
  simpa only [List.length_map, hl] using hs

theorem m5OrchSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m5OrchSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (m5OrchSpecTable_sigs mainSpec)
  simp only [List.map_map, Function.comp_def, Module.sigs, List.map_append, Fn.sig,
    Extern.sig] at hm
  have hchk := m5Orch_acyclic
  simp only [m5OrchModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := Module.namesNodup_of_checkNamesNodup hchk.1
  change ((m5OrchSpecTable mainSpec).map SpecEntry.name) = m5OrchModule.names at hm
  rw [hm]; exact hnd

theorem mkM5OrchEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m5OrchSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM5OrchEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m5OrchSpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem m5_ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

theorem mkM5OrchEnv_row_elim {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m5OrchSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : e.noExit = true := by rfl) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} (hs : mkM5OrchEnv mainSpec e.name e.as e.rs xs m Q X) :
    e.spec xs m Q (fun _ _ _ _ => False) := by
  have heff := (m5_ofTable_iff_of_mem (List.mem_of_getElem? hi)
    (m5OrchSpecTable_nodup mainSpec)).mp hs
  simpa only [SpecEntry.eff, hno, ↓reduceIte] using heff

theorem mkM5OrchEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM5OrchEnv mainSpec f as bs xs m Q X → mkM5OrchEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m5OrchSpecTable_noExit mainSpec)

end SpecTable

/-! ## 2. Invariant Helpers & Remaining Orchestrator Proofs (`preprocess`, `simplify`, `search`) -/

section OrchestratorProofs

open scoped Full.FullArenaTactics

private theorem m5_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m5_sparseInv_of_same_arena {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hcore : FullCoreInv c F0 s')
    (hal : s'.core.arena_len = s.core.arena_len) (ha : s'.core.arena = s.core.arena)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) (hpres : FullExtScratchPres s s') :
    FullSparseInv c F0 s' := by
  refine ⟨hcore, ⟨fun v hv => by rw [hmrk]; exact h.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact h.2.1.2 l hl⟩,
    fun ref href hng => ?_, ?_, by rw [hdm]; exact h.2.2.2.2⟩
  · have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hal, ha]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact h.2.2.1 ref href hng
  · exact h.2.2.2.1.of_pres hpres fun ref href => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at href ⊢; rwa [hal, ha]

private theorem m5_sparseInv_of_perm_core {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hcore : FullCoreInv c F0 s')
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) (hpres : FullExtScratchPres s s') :
    FullSparseInv c F0 s' := by
  refine ⟨hcore, ⟨fun v hv => by rw [hmrk]; exact h.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact h.2.1.2 l hl⟩,
    fun ref href hng => ?_, ?_, by rw [hdm]; exact h.2.2.2.2⟩
  · have href0 : ref ∈ fullArenaClauseRefs s := by
      change ref ∈ fullArenaClauseRefsCore s.core; rw [← hperm.2.1]; exact href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (h.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact h.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem m5_sparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s) (hlen : s'.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s'.core) (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) (hpres : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' :=
  ⟨hlen, hw, ⟨fun v hv => by rw [hmrk]; exact h.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact h.2.2.1.2 l hl⟩,
    fun ref href hng => by
      have href0 : ref ∈ fullArenaClauseRefs s := by
        change ref ∈ fullArenaClauseRefsCore s.core; rw [← hperm.2.1]; exact href
      obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
      exact (hp.map (· / 2)).nodup_iff.mpr (h.2.2.2.1 ref href0 (hgb.symm.trans hng)),
    h.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href,
    by rw [hdm]; exact h.2.2.2.2.2⟩

private theorem m5_sparseInv_after_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullSparseInvW c F0 F_cur s)
    (hlen : s'.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s'.core)
    (hpres : FullExtScratchPres s s')
    (hal : s'.core.arena_len = s.core.arena_len) (ha : s'.core.arena = s.core.arena)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen, hw,
    ⟨fun v hv => by rw [hmrk]; exact h.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact h.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans h.2.2.2.2.2⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact h.2.2.2.1 ref href hng
  · exact h.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [ha, hal]; exact href

private theorem wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) :
    wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

/-- Parametric `Func.wp` theorem for `full_preprocess_m5` (`full_lucky`, initial compact, no
eager conflict-0 `full_eliminate`, uncapped `full_scale_delta_m5`) against
`FullM4.m4PreprocessSpec`. -/
theorem full_preprocess_m5_wp (Γ : Env)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, Full.fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hCNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hComp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X →
      Γ "full_probe_m5" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_m5_body
  c0_hsteps; c0_call hProp
  refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    m5_sparseInvW_of_perm hspW hlen1 hw1 hperm1 rfl rfl rfl ⟨rfl, rfl⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1
      (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 (Or.inl rfl) hfu1
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 (Or.inl rfl) hfu1
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
      c0_hsplit
      · c0_hsteps
        exact hQ 10#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths
          (Or.inr (Or.inr (Or.inl rfl))) hfu2 (fun h => by cases h)
          (fun h => by cases h) (fun _ => hinv2.2.2.2.1.2) hm2
      c0_hsteps; c0_call hLucky; refine ⟨c, F0, s2, R, rfl, hinv2, hcl2, hm2, ?_⟩
      intro lk s3 m3 hlen3 hlk_dom hfu3 _ hlu3 hsp3 hext3 hm3
      c0_hsplit
      · c0_hsteps
        have h20 : lk = 20#64 := hc; subst h20
        exact hQ 20#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3
          (Or.inr (Or.inr (Or.inr rfl))) (by omega) (fun _ => hlu3 rfl)
          (fun h => by cases h) (fun h => by cases h) hm3
      c0_hsplit
      · c0_hsteps
        have h10 : lk = 10#64 := hc; subst h10
        exact hQ 10#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3
          (Or.inr (Or.inr (Or.inl rfl))) (by omega) (fun h => by cases h)
          (fun h => by cases h) (fun _ => hext3 rfl) hm3
      have hlk02 : lk = 0#64 ∨ lk = 2#64 := by
        rcases hlk_dom with h0 | h2 | h10 | h20
        · exact Or.inl h0
        · exact Or.inr h2
        · exact absurd h10 ‹_›
        · exact absurd h20 ‹_›
      obtain ⟨hinv3, hcl3⟩ := hsp3 hlk02
      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps_nogrp
      · exact hQ 20#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3
          (Or.inr (Or.inr (Or.inr rfl))) hfu3'
          (fun _ => hinv3.inconsistent_unsat hc) (fun h => by cases h)
          (fun h => by cases h) hm3
      · exact hQ 0#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 (Or.inl rfl) hfu3'
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 c s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 (Or.inl rfl) hfu3'
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm3
      refine wp_join_state0 (α := FullCfg × FullState)
        (fun ⟨c4, s4⟩ m4 => FullM4Compact.FullCfgCompat c c4 ∧ FullSparseInv c4 F0 s4 ∧
          s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullMem c4 s4 ⋆ R) m4)
        (fun _ ⟨c4, s4⟩ m4 ⟨hcomp4, hinv4, hcl4, hfu4, hm4⟩ => by
          have hch4 : c4.hdr = c.hdr := hcomp4.hdr
          rw [← hch4]
          c0_hsteps
          · exact hQ 20#64 c4 s4 m4 hcomp4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu4
              (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h)
              (fun h => by cases h) hm4
          · exact hQ 0#64 c4 s4 m4 hcomp4 hinv4.lengths (Or.inl rfl) hfu4
              (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm4
          · exact hQ 10#64 c4 s4 m4 hcomp4 hinv4.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu4
              (fun h => by cases h) (fun h => by cases h) (fun _ => hinv4.2.2.2.1.2) hm4
          · c0_call hScale; refine ⟨c4, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
            intro plim1
            c0_hsteps
            let s4a : FullState :=
              { s4 with scratch := { s4.scratch with probe_limit := plim1 } }
            have hinv4a : FullSparseInv c4 F0 s4a :=
              m5_sparseInv_with_scratch_keep hinv4 { hinv4.lengths.scratch_ok with } rfl rfl
            c0_call hScale; refine ⟨c4, s4a, R, rfl, hinv4a.lengths, hm, ?_⟩
            intro elim1
            c0_hsteps
            let s4b : FullState :=
              { s4a with scratch := { s4a.scratch with elim_limit := elim1 } }
            have hinv4b : FullSparseInv c4 F0 s4b :=
              m5_sparseInv_with_scratch_keep hinv4a { hinv4a.lengths.scratch_ok with } rfl rfl
            c0_call hProbe; refine ⟨c4, F0, s4b, R, rfl, hinv4b, hcl4, hm, ?_⟩
            intro rp s5 m5 hlen5 hfu5 hrp_dom hup5 hsp5 hm5
            dsimp only [s4b, s4a] at hfu5
            have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
            c0_hsteps_nogrp
            · exact hQ 20#64 c4 s5 m5 hcomp4 hlen5 (Or.inr (Or.inr (Or.inr rfl))) hfu5'
                (fun _ => hup5 hc) (fun h => by cases h) (fun h => by cases h) hm5
            · exact hQ 20#64 c4 s5 m5 hcomp4 hlen5 (Or.inr (Or.inr (Or.inr rfl))) hfu5'
                (fun _ => (hsp5 (hrp_dom.resolve_right ‹_›)).1.inconsistent_unsat hc)
                (fun h => by cases h) (fun h => by cases h) hm5
            · exact hQ 0#64 c4 s5 m5 hcomp4 hlen5 (Or.inl rfl) hfu5'
                (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm5
            · exact hQ 0#64 c4 s5 m5 hcomp4 hlen5 (Or.inl rfl) hfu5'
                (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm5
            obtain ⟨hinv5, hcl5⟩ := hsp5 (hrp_dom.resolve_right ‹_›)
            refine wp_join_state0 (α := FullCfg × FullState)
              (fun ⟨c6, s6⟩ m6 => FullM4Compact.FullCfgCompat c c6 ∧
                FullSparseInv c6 F0 s6 ∧ s6.core.cur_level = 0 ∧
                s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c6 s6 ⋆ R) m6)
              (fun _ ⟨c6, s6⟩ m6 ⟨hcomp6, hinv6, hcl6, hfu6, hm6⟩ => by
                have hch6 : c6.hdr = c4.hdr := hcomp6.hdr.trans hcomp4.hdr.symm
                rw [← hch6]
                c0_hsteps
                · exact hQ 20#64 c6 s6 m6 hcomp6 hinv6.lengths (Or.inr (Or.inr (Or.inr rfl)))
                    hfu6 (fun _ => hinv6.inconsistent_unsat hc) (fun h => by cases h)
                    (fun h => by cases h) hm6
                · exact hQ 0#64 c6 s6 m6 hcomp6 hinv6.lengths (Or.inl rfl) hfu6
                    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm6
                · exact hQ 10#64 c6 s6 m6 hcomp6 hinv6.lengths (Or.inr (Or.inr (Or.inl rfl)))
                    hfu6 (fun h => by cases h) (fun h => by cases h)
                    (fun _ => hinv6.2.2.2.1.2) hm6
                · c0_call hScale; refine ⟨c6, s6, R, rfl, hinv6.lengths, hm6, ?_⟩
                  intro plim2
                  c0_hsteps
                  let s6a : FullState :=
                    { s6 with scratch := { s6.scratch with probe_limit := plim2 } }
                  have hinv6a : FullSparseInv c6 F0 s6a :=
                    m5_sparseInv_with_scratch_keep hinv6 { hinv6.lengths.scratch_ok with } rfl rfl
                  c0_call hScale; refine ⟨c6, s6a, R, rfl, hinv6a.lengths, hm, ?_⟩
                  intro elim2
                  c0_hsteps
                  let s6b : FullState :=
                    { s6a with scratch := { s6a.scratch with elim_limit := elim2 } }
                  have hinv6b : FullSparseInv c6 F0 s6b :=
                    m5_sparseInv_with_scratch_keep hinv6a
                      { hinv6a.lengths.scratch_ok with } rfl rfl
                  exact hQ 1#64 c6 s6b _ hcomp6 hinv6b.lengths (Or.inr (Or.inl rfl)) hfu6
                    (fun h => by cases h) (fun _ => ⟨hinv6b, hcl6⟩)
                    (fun h => by cases h) hm)
              (fun Jc2 hJc2 => by
                c0_call hCNeed
                refine ⟨c4, s5, R, rfl, hlen5, by omega, hm5, ?_⟩
                intro need2 _
                c0_hsplit
                · c0_hsteps; c0_call hComp; refine ⟨c4, F0, s5, R, rfl, hinv5, hm5, ?_⟩
                  intro cr c6 s6 m6 hcomp6 hinv6 hcr_dom _ hfu6 hu6 hcl6 hm6
                  c0_hsteps
                  · exact hQ 20#64 c6 s6 m6 (hcomp4.trans hcomp6) hinv6.lengths
                      (Or.inr (Or.inr (Or.inr rfl))) (by omega) (fun _ => hu6 hc)
                      (fun h => by cases h) (fun h => by cases h) hm6
                  · exact hQ 0#64 c6 s6 m6 (hcomp4.trans hcomp6) hinv6.lengths
                      (Or.inl rfl) (by omega) (fun h => by cases h) (fun h => by cases h)
                      (fun h => by cases h) hm6
                  · exact hJc2 (c6, s6) m6 ⟨hcomp4.trans hcomp6, hinv6, hcl6 hc, by omega, hm6⟩
                · c0_hsteps
                  exact hJc2 (c4, s5) m5 ⟨hcomp4, hinv5, hcl5, hfu5', hm5⟩))
        (fun Jc1 hJc1 => by
          c0_call hCNeed
          refine ⟨c, s3, R, rfl, hlen3, by omega, hm3, ?_⟩
          intro need1 _
          c0_hsplit
          · c0_hsteps; c0_call hComp; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
            intro cr c4 s4 m4 hcomp4 hinv4 hcr_dom _ hfu4 hu4 hcl4 hm4
            c0_hsteps
            · exact hQ 20#64 c4 s4 m4 hcomp4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl)))
                (by omega) (fun _ => hu4 hc) (fun h => by cases h) (fun h => by cases h) hm4
            · exact hQ 0#64 c4 s4 m4 hcomp4 hinv4.lengths (Or.inl rfl)
                (by omega) (fun h => by cases h) (fun h => by cases h)
                (fun h => by cases h) hm4
            · exact hJc1 (c4, s4) m4 ⟨hcomp4, hinv4, hcl4 hc, by omega, hm4⟩
          · c0_hsteps
            exact hJc1 (c, s3) m3 ⟨FullM4Compact.FullCfgCompat.refl c, hinv3, hcl3, hfu3', hm3⟩))
    (fun Ju hJu => by
      c0_hsplit
      · c0_hsteps; c0_call hSweep
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1.1, hspW1.2.1, hspW1.2.2.2.1, hspW1.2.2.2.2.2,
          fun hpos => by omega, hm1, ?_⟩
        intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc1a m1a s1a
          hlen1a _ hext1a _ hll1a hw1a hnd1a _ _ _ hsr2 _ hm1a
        have hspW1a : FullSparseInvW c F0 F_cur s1a :=
          ⟨hlen1a, hw1a, hspW1.2.2.1, hnd1a,
           ⟨hll1a, hext1a.symm ▸ hspW1.2.2.2.2.1.2⟩, hspW1.2.2.2.2.2⟩
        have hcl1a : s1a.core.cur_level = 0 := hcl1
        c0_hsteps
        · exact hQ 20#64 c s1a m1a (FullM4Compact.FullCfgCompat.refl c) hlen1a
            (Or.inr (Or.inr (Or.inr rfl))) hfu1 (fun _ => (hsr2 hc).2)
            (fun h => by cases h) (fun h => by cases h) hm1a
        c0_call hProp
        refine ⟨c, F0, F_cur, s1a, R, rfl, hspW1a.1, hspW1a.2.1, hspW1a.2.2.2.2.2, hm1a, ?_⟩
        intro pr1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1b _ _ _ _ _ _ _ _ m1b s1b
          hlen1b hw1b _ hperm1b hfl1b _ _ hpr1b_1 _ _ hm1b
        have hspW1b : FullSparseInvW c F0 F_cur s1b :=
          m5_sparseInvW_of_perm hspW1a hlen1b hw1b hperm1b rfl rfl rfl ⟨rfl, rfl⟩
        have hfu1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1a.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
          dsimp only [s1b]; omega
        c0_hsteps
        · exact hQ 20#64 c s1b m1b (FullM4Compact.FullCfgCompat.refl c) hlen1b
            (Or.inr (Or.inr (Or.inr rfl))) hfu1b
            (fun _ => level0_unsat_of_conflict_okW (s := s1b) hw1b hcl1a (hpr1b_1 hc).2.2)
            (fun h => by cases h) (fun h => by cases h) hm1b
        have hspW1c : FullSparseInvW c F0 F_cur
            { s1b with core := { s1b.core with unflushed := 0#64 } } :=
          ⟨⟨{ hspW1b.1.core_ok with }, hspW1b.1.scratch_ok⟩,
           { hspW1b.2.1 with
             arena := { hspW1b.2.1.arena with len_ok := hspW1b.2.1.arena.len_ok }
             watches := hspW1b.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
           hspW1b.2.2.1, hspW1b.2.2.2.1, hspW1b.2.2.2.2.1, hspW1b.2.2.2.2.2⟩
        exact hJu _ _ ⟨hspW1c.toSparse, hcl1a, hfu1b, hm⟩
      · c0_hsteps; exact hJu s1 m1 ⟨hspW1.toSparse, hcl1, hfu1, hm1⟩)

/-- Parametric `Func.wp` theorem for `full_simplify_m5` (no `full_reduce` / `full_reorder`)
against `FullM4.m4SimplifySpec`. -/
theorem full_simplify_m5_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProbe : ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X →
      Γ "full_probe_m5" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_m5" [i64, .bool] [i64] a m Q X)
    (hCNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hComp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4SimplifySpec a m Q X → Func.wp Γ full_simplify_m5_body a m Q X := by
  rintro ⟨h, do_probe, do_elim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_cur0, hw0⟩ := hinv.exists_witness
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
    have := hinv.lengths.core_ok.cur_vars_le; have := fullInv_max_vars_lt32 c; omega
  unfold Func.wp full_simplify_m5_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0, hfu0, hm0⟩ => by
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
          s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
        (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.lengths hfu1
              (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm1
          c0_hsplit
          · c0_hsteps
            exact hQ 0#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.lengths hfu1
              (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm1
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
              s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
            (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
              c0_hsteps_nogrp
              · exact hQ 20#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths hfu2
                  (Or.inr (Or.inr rfl)) (fun _ => hinv2.inconsistent_unsat hc)
                  (fun h => by cases h) hm2
              · exact hQ 0#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths hfu2
                  (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm2
              refine wp_join_state0 (α := FullCfg × FullState)
                (fun ⟨c3, s3⟩ m3 => FullM4Compact.FullCfgCompat c c3 ∧ FullSparseInv c3 F0 s3 ∧
                  s3.core.cur_level = 0 ∧ s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c3 s3 ⋆ R) m3)
                (fun _ ⟨c3, s3⟩ m3 ⟨hcomp3, hinv3, hcl3, hfu3, hm3⟩ => by
                  have hch3 : c3.hdr = c.hdr := hcomp3.hdr
                  rw [← hch3]
                  c0_hsteps
                  · exact hQ 20#64 c3 s3 m3 hcomp3 hinv3.lengths hfu3 (Or.inr (Or.inr rfl))
                      (fun _ => hinv3.inconsistent_unsat hc) (fun h => by cases h) hm3
                  · exact hQ 0#64 c3 s3 m3 hcomp3 hinv3.lengths hfu3 (Or.inl rfl)
                      (fun h => by cases h) (fun h => by cases h) hm3
                  · exact hQ 1#64 c3 s3 m3 hcomp3 hinv3.lengths hfu3 (Or.inr (Or.inl rfl))
                      (fun h => by cases h) (fun _ => ⟨hinv3, hcl3⟩) hm3)
                (fun Jc hJc => by
                  c0_call hCNeed
                  refine ⟨c, s2, R, rfl, hinv2.lengths, by omega, hm2, ?_⟩
                  intro need _
                  c0_hsplit
                  · c0_hsteps; c0_call hComp; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                    intro cr c3 s3 m3 hcomp3 hinv3 hcr_dom _ hfu3 hu3 hcl3 hm3
                    c0_hsteps
                    · exact hQ 20#64 c3 s3 m3 hcomp3 hinv3.lengths (by omega)
                        (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun h => by cases h) hm3
                    · exact hQ 0#64 c3 s3 m3 hcomp3 hinv3.lengths (by omega)
                        (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm3
                    · exact hJc (c3, s3) m3 ⟨hcomp3, hinv3, hcl3 hc, by omega, hm3⟩
                  · c0_hsteps
                    exact hJc (c, s2) m2
                      ⟨FullM4Compact.FullCfgCompat.refl c, hinv2, hcl2, hfu2, hm2⟩))
            (fun Je hJe => by
              c0_hsplit
              · c0_hsteps; c0_call hElim; refine ⟨c, F0, s1, R, rfl, hinv1, hcl1, hm1, ?_⟩
                intro re s2 m2 hinv2 hcl2 hfu2 _ hue2 hm2; c0_hsteps
                · exact hQ 20#64 c s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.lengths
                    (by omega) (Or.inr (Or.inr rfl)) (fun _ => hue2 hc)
                    (fun h => by cases h) hm2
                exact hJe s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
              · c0_hsteps; exact hJe s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
        (fun Jp hJp => by
          c0_hsplit
          · c0_hsteps; c0_call hProbe; refine ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, ?_⟩
            intro rp s1 m1 hlen1 hfu1 hrp_dom hup1 hsp1 hm1; c0_hsteps
            · exact hQ 20#64 c s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 (by omega)
                (Or.inr (Or.inr rfl)) (fun _ => hup1 hc) (fun h => by cases h) hm1
            obtain ⟨hinv1, hcl1⟩ := hsp1 (hrp_dom.resolve_right hc)
            exact hJp s1 m1 ⟨hinv1, hcl1, by omega, hm1⟩
          · c0_hsteps; exact hJp s0 m0 ⟨hinv0, hcl0, hfu0, hm0⟩))
    (fun Jbt hJbt => by
      c0_hsplit
      · c0_hsteps; c0_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, fun _ => by
          have := hw0.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
          have := hinv.lengths.core_ok.cur_vars_le; omega,
          hw0.2.1.trail_lits_lt, hm, ?_⟩
        intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
        have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
        have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
        have hsp1 := m5_sparseInv_after_backtrack0 hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
        c0_hsteps; exact hJbt s1 m1 ⟨hsp1.toSparse, hl01, Nat.le_refl _, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have : ¬ 0 < s.core.cur_level % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt hcl_lt64] at this; omega
        c0_hsteps; exact hJbt s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

private def m5SearchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

/-- Parametric `Func.wp` theorem for `full_search_m5` (`search.c:195-224` dispatch, linear
`10k` reorder cadence, no startup warmup) against `FullM4.m4SearchSpec`. -/
theorem full_search_m5_wp (Γ : Env)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, Full.fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hRed : ∀ a m Q X, Full.fullReduceSpec a m Q X → Γ "full_reduce_m5" [i64, .bool] [i64] a m Q X)
    (hSw : ∀ a m Q X, Full.fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hRdue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hReord : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m5" [i64, i64] [i64] a m Q X)
    (hReph : ∀ a m Q X, Full.fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hSimp : ∀ a m Q X, FullM4.m4SimplifySpec a m Q X →
      Γ "full_simplify_m5" [i64, .bool, .bool] [i64] a m Q X)
    (hDec : ∀ a m Q X, Full.fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4SearchSpec a m Q X → Func.wp Γ full_search_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_search_m5_body
  c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
    (fun p => m5SearchVariant p.2.2)
    (fun ⟨_, cc, st⟩ ml =>
      FullM4Compact.FullCfgCompat c cc ∧ FullSparseInv cc F0 st ∧ (FullMem cc st ⋆ R) ml)
    (fun _ hL => by
      c0_hsteps; exact hL (10000#64, c, s) m ⟨FullM4Compact.FullCfgCompat.refl c, hinv, hm⟩)
    (fun _ ⟨rlim, cc, st⟩ ml ⟨hcc, hst, hml⟩ ih => ?_)
  have hch_cc : cc.hdr = c.hdr := hcc.hdr
  rw [← hch_cc]
  c0_hsplit
  rotate_left; · cases hc
  c0_hsteps
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  obtain ⟨F_cur, hspW⟩ := hst.exists_witness
  c0_call hProp; refine ⟨cc, F0, F_cur, st, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hml, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s3
    hlen3 hw3 _ hperm3 hfu3 hpr_dom hpr0 hpr1 _ _ hm3
  have hspW3 : FullSparseInvW cc F0 F_cur s3 :=
    m5_sparseInvW_of_perm hspW hlen3 hw3 hperm3 rfl rfl rfl ⟨rfl, rfl⟩
  c0_hsteps
  · exact hQ 0#64 cc s3 m3 hcc hlen3 (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm3
  · obtain ⟨hfu3_lt, _, hconf3⟩ := hpr1 hc
    c0_call hAna; refine ⟨cc, F0, F_cur, s3, R, rfl, hspW3, hconf3, hm3, ?_⟩
    intro ast s4 m4 hlen4 _ _ hfu4 _ hua4 _ hsp4 hm4
    c0_hsteps_nogrp
    · exact hQ 20#64 cc s4 m4 hcc hlen4 (Or.inr (Or.inr rfl))
        (fun _ => hua4 hc) (fun h => by cases h) hm4
    · exact hQ 0#64 cc s4 m4 hcc hlen4 (Or.inl rfl)
        (fun h => by cases h) (fun h => by cases h) hm4
    have hspW4 : FullSparseInvW cc F0 F_cur s4 := (hsp4 hc).1
    have hinv4 : FullSparseInv cc F0 s4 := hspW4.toSparse
    have hfu4_lt : s4.core.fuel.toNat < st.core.fuel.toNat := by dsimp only [s3] at hfu4; omega
    let ContInv : BitVec 64 × FullCfg × FullState → Mem 64 → Prop :=
      fun ⟨_, c8, s8⟩ m8 => FullM4Compact.FullCfgCompat c c8 ∧ FullSparseInv c8 F0 s8 ∧
        s8.core.fuel.toNat < st.core.fuel.toNat ∧ (FullMem c8 s8 ⋆ R) m8
    let ContInv0 : FullCfg × FullState → Mem 64 → Prop :=
      fun ⟨c8, s8⟩ m8 => ContInv (rlim, c8, s8) m8
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun v => (v, ())) (fun _ => True) ?_ ?_
    · intro _ mode_due _
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
      · intro _ ⟨r8, c8, s8⟩ m8 ⟨hc8, hinv8, _, hm8⟩
        c0_hsteps
        have hv_lt : m5SearchVariant s8 < m5SearchVariant st := by
          unfold m5SearchVariant; split <;> split <;> omega
        exact ih (r8, c8, s8) m8 hv_lt ⟨hc8, hinv8, hm8⟩
      · intro Jr1 hJr1
        c0_hsplit
        · c0_hsteps; c0_call hRed
          refine ⟨cc, F0, F_cur, s4, R, rfl, hspW4, hm4, ?_⟩
          intro rr s5 m5 hsp5 hrr_dom _ hfu5 _ _ _ _ hur5 _ _ hm5
          c0_hsteps
          · exact hQ 20#64 cc s5 m5 hcc hsp5.1 (Or.inr (Or.inr rfl))
              (fun _ => hur5 hc) (fun h => by cases h) hm5
          · exact hQ 0#64 cc s5 m5 hcc hsp5.1 (Or.inl rfl)
              (fun h => by cases h) (fun h => by cases h) hm5
          exact hJr1 (rlim, cc, s5) m5 ⟨hcc, hsp5.toSparse, by omega, hm5⟩
        · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
          · intro _ p mp hp; c0_hsteps; exact hJr1 p mp hp
          · intro Jr2 hJr2
            c0_hsplit
            · c0_hsteps; c0_call hSw; refine ⟨cc, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
              intro ⟨⟩ s5 m5 hcore5 hlen5 hpres5 hm5
              dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
              have hinv5 : FullSparseInv cc F0 s5 := hinv4.of_safetySlice hlen5 hcore5 hpres5.1
              have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
                have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
                rw [heq]; exact hfu4_lt
              c0_hsteps; exact hJr2 (rlim, cc, s5) m5 ⟨hcc, hinv5, hfu5, hm5⟩
            · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
              · intro _ p mp hp; c0_hsteps; exact hJr2 p mp hp
              · intro Jr3 hJr3
                c0_hsteps; c0_call hRdue; refine ⟨cc, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
                intro ⟨rd, ⟨⟩⟩ s4r m4r hcore4r hlen4r ⟨_, hpres4r⟩ hm4r
                dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm4r
                have hinv4r : FullSparseInv cc F0 s4r :=
                  hinv4.of_safetySlice hlen4r hcore4r hpres4r
                have hfu4r : s4r.core.fuel.toNat < st.core.fuel.toNat := by
                  have heq : s4r.core = s4.core := fullCoreState_agrees_with_scratch hcore4r
                  rw [heq]; exact hfu4_lt
                c0_hsplit
                · c0_hsteps; c0_call hRst
                  refine ⟨cc, F0, s4r, R, rfl, hinv4r.1, hm4r, ?_⟩
                  intro _ _ _ _ _ _ _ _ _ _ m5 s5 hcore5 _ hpres5 hm5
                  have hinv5 : FullSparseInv cc F0 s5 :=
                    m5_sparseInv_of_same_arena hinv4r hcore5 rfl rfl rfl rfl rfl hpres5
                  c0_hsteps; exact hJr3 (rlim, cc, s5) m5 ⟨hcc, hinv5, hfu4r, hm5⟩
                · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState)
                    Prod.fst ContInv ?_ ?_
                  · intro _ p mp hp; c0_hsteps; exact hJr3 p mp hp
                  · intro Jr4 hJr4
                    c0_hsplit
                    · c0_hsteps; c0_call hReord
                      refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                      intro _ s5 m5 hinv5 _ _ hfu5 hm5
                      c0_hsteps
                      exact hJr4 (s4r.scratch.conflicts + 10000#64, cc, s5) m5
                        ⟨hcc, hinv5, by rw [hfu5]; exact hfu4r, hm5⟩
                    · refine wp_join_state0 ContInv0 ?_ ?_
                      · intro _ ⟨c8, s8⟩ m8 h8; c0_hsteps; exact hJr4 (rlim, c8, s8) m8 h8
                      · intro Jr5 hJr5
                        c0_hsplit
                        · c0_hsteps; c0_call hReph
                          refine ⟨cc, F0, s4r, R, rfl, hinv4r.1, hm4r, ?_⟩
                          intro _ _ _ _ _ _ _ _ _ _ m5 s5 hcore5 hfu5 hpres5 hm5
                          have hinv5 : FullSparseInv cc F0 s5 :=
                            m5_sparseInv_of_same_arena hinv4r hcore5 rfl rfl rfl rfl rfl hpres5
                          c0_hsteps
                          exact hJr5 (cc, s5) m5
                            ⟨hcc, hinv5, by dsimp only [s5]; omega, hm5⟩
                        · refine wp_join_state0 ContInv0 ?_ ?_
                          · intro _ p mp hp; c0_hsteps; exact hJr5 p mp hp
                          · intro Jr6 hJr6
                            c0_hsplit
                            · c0_hsteps; c0_call hSimp
                              refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                              intro sr c5 s5 m5 hcomp5 hlen5 hfu5 _ hus5 hsp5 hm5
                              have hc5 := hcc.trans hcomp5
                              c0_hsteps
                              · exact hQ 20#64 c5 s5 m5 hc5 hlen5 (Or.inr (Or.inr rfl))
                                  (fun _ => hus5 hc) (fun h => by cases h) hm5
                              · exact hQ 0#64 c5 s5 m5 hc5 hlen5 (Or.inl rfl)
                                  (fun h => by cases h) (fun h => by cases h) hm5
                              exact hJr6 (c5, s5) m5 ⟨hc5, (hsp5 hc).1, by omega, hm5⟩
                            · c0_hsteps
                              · c0_call hSimp
                                refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                                intro sr c5 s5 m5 hcomp5 hlen5 hfu5 _ hus5 hsp5 hm5
                                have hc5 := hcc.trans hcomp5
                                c0_hsteps
                                · exact hQ 20#64 c5 s5 m5 hc5 hlen5 (Or.inr (Or.inr rfl))
                                    (fun _ => hus5 hc) (fun h => by cases h) hm5
                                · exact hQ 0#64 c5 s5 m5 hc5 hlen5 (Or.inl rfl)
                                    (fun h => by cases h) (fun h => by cases h) hm5
                                exact hJr6 (c5, s5) m5 ⟨hc5, (hsp5 hc).1, by omega, hm5⟩
                              · exact hJr6 (cc, s4r) m4r ⟨hcc, hinv4r, hfu4r, hm4r⟩
    · intro _ hJmd; c0_hsteps <;> exact hJmd _ trivial
  · exact hQ 10#64 cc s3 m3 hcc hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hspW3.2.2.2.2.1.2) hm3
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_dom with h0 | h1 | h2
      · exact h0
      · exact absurd h1 (by assumption)
      · exact absurd h2 (by assumption)
    obtain ⟨hprop3, _, hfu3_lt_if⟩ := hpr0 hpr_eq0
    have hinv3 : FullSparseInv cc F0 s3 := hspW3.toSparse
    c0_call hDec; refine ⟨cc, F0, s3, R, rfl, hinv3.1, hm3, ?_⟩
    intro dr _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s4 hcore4 hpres4 hdr_dom _ hd1 hm4
    have hinv4 : FullSparseInv cc F0 s4 :=
      m5_sparseInv_of_same_arena hinv3 hcore4 rfl rfl rfl rfl rfl hpres4
    c0_hsteps
    · exact hQ 10#64 cc s4 m4 hcc hinv4.lengths (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hinv4.2.2.2.1.2) hm4
    · exact hQ 0#64 cc s4 m4 hcc hinv4.lengths (Or.inl rfl) (fun h => by cases h)
        (fun h => by cases h) hm4
    · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
      have hte4 : s4.core.trail_end = s3.core.trail_end + 1 := (hd1 hdr1).2
      have hv_lt : m5SearchVariant s4 < m5SearchVariant st := by
        have hfu3' : s3.core.fuel.toNat ≤ st.core.fuel.toNat := hfu3
        have hprop3' : s3.core.propagated = s3.core.trail_end := hprop3
        have hne4 : s4.core.propagated ≠ s4.core.trail_end := by
          change s3.core.propagated ≠ s4.core.trail_end; omega
        have hle_st := hst.lengths.core_ok.propagated_le
        have hfu4 : s4.core.fuel = s3.core.fuel := rfl
        unfold m5SearchVariant
        simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
        by_cases heq_st : st.core.propagated = st.core.trail_end
        · simp only [heq_st, ↓reduceIte]; omega
        · simp only [heq_st, ↓reduceIte, Nat.add_zero]
          have hlt_f : s3.core.fuel.toNat < st.core.fuel.toNat := hfu3_lt_if (by omega)
          omega
      exact ih (rlim, cc, s4) m4 hv_lt ⟨hcc, hinv4, hm4⟩

end OrchestratorProofs

/-! ## 3. Top-Level `kissat_solve_bytes_m5`, `m5Orch_moduleOk`, & Concrete `Mem 64` NV -/

section TopAndNonVacuity

open scoped Full.FullArenaTactics

private theorem m5_parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact m5_parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem m5_parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact m5_parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem m5_bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem m5_alignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem m5_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem m5_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply m5_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

private def M5CheckRest (c : FullCfg) (s : FullState) (bva_bv : BitVec 64) : Mem 64 → Prop :=
  array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

private theorem m5_arr8 {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) (f : Mem 64) (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem m5_arr32 (m : Nat) {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem m5_arr64 (m : Nat) {a : BitVec 64} {xs : List (BitVec 64)} {n : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem m5_checkModel_post_to_region {c : FullCfg} {s : FullState}
    {bva_bv mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ (M5CheckRest c s bva_bv ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap
  have hd := c.hdel; have hred := c.hred; have hext := c.hext; have hscr := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound at *
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have h1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆
          array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) ⋆
        ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
            array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
            array (t := i8) c.pLitMark s.core.lit_mark) ⋆
          (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
            array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
            array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
            array (t := i8) c.pWalkBest s.scratch.walk_best)) ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆
        (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
          array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
          array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆
        (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          array (t := i32) c.pFrameDec s.core.frame_dec) ⋆
        (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
          array (t := i32) c.pWsort s.scratch.wsort ⋆
          array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
          array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
          array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
          array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
          array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) ⋆
        (array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
          array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
          array (t := i32) c.pDelayed s.scratch.delayed ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
        c.pad)) m := by
    unfold M5CheckRest FullCoreU32A FullCoreU32B FullCoreDynArrs FullScratchArrays
      FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs FullScrDynArrs at hm
    exact sep_ac hm
  have hHead : ∀ k,
      (dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) k →
      (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) k :=
    sep_mono2 (fun _ hb => dimacsState_to_region hb)
      (m5_arr64 1120 (by rw [List.length_set, Full.hdrTailWords_length])
        (by decide) (by decide))
  have hB : ∀ k,
      ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
          array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          array (t := i8) c.pLitMark s.core.lit_mark) ⋆
        (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
          array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          array (t := i8) c.pWalkBest s.scratch.walk_best)) k →
      ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
          region c.pLitMark (2 * c.max_vars)) ⋆
        (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
          region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
          region c.pWalkBest c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (fun x (hb : bytes c.pVals (s.core.vals.map UInt8.ofBitVec) x) => by
            have hb' := bytes_to_region hb; simpa [hc.vals_len] using hb')
          (m5_arr8 hs.walk_vals_len (by omega)))
        (m5_arr8 hc.lit_mark_len (by omega)))
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sep_mono2 (m5_arr8 hc.mrk_len (by omega))
              (m5_arr8 hs.phases_len (by omega)))
            (m5_arr8 hs.phases_target_len (by omega)))
          (m5_arr8 hs.phases_best_len (by omega)))
        (m5_arr8 hs.walk_best_len (by omega)))
  have hU1 : ∀ k,
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) k →
      (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
        region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
        region c.pTrailPos (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m5_arr32 (4 * c.max_vars) hc.flags_len rfl (by omega))
            (m5_arr32 (4 * c.max_vars) hc.lvl_len rfl (by omega)))
          (m5_arr32 (4 * c.max_vars) hc.rsns_len rfl (by omega)))
        (m5_arr32 (4 * c.max_vars) hc.trl_len rfl (by omega)))
      (m5_arr32 (4 * c.max_vars) hc.trail_pos_len rfl (by omega))
  have hU2 : ∀ k,
      (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) k →
      (region c.pTmp (4 * c.max_vars) ⋆ region c.pHeap (4 * c.max_vars) ⋆
        region c.pPos (4 * c.max_vars) ⋆ region c.pMinClr (4 * c.max_vars) ⋆
        region c.pShrinkStk (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m5_arr32 (4 * c.max_vars) hc.tmp_len_arr rfl (by omega))
            (m5_arr32 (4 * c.max_vars) hs.heap_len_arr rfl (by omega)))
          (m5_arr32 (4 * c.max_vars) hs.pos_len rfl (by omega)))
        (m5_arr32 (4 * c.max_vars) hc.min_clr_len_arr rfl (by omega)))
      (m5_arr32 (4 * c.max_vars) hs.shrink_stk_len rfl (by omega))
  have hU3 : ∀ k,
      (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec) k →
      (region c.pQPrev (4 * c.max_vars) ⋆ region c.pQNext (4 * c.max_vars) ⋆
        region c.pQStamp (4 * c.max_vars) ⋆ region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
        region c.pFrameDec (4 * (c.max_vars + 1))) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (m5_arr32 (4 * c.max_vars) hs.q_prev_len rfl (by omega))
            (m5_arr32 (4 * c.max_vars) hs.q_next_len rfl (by omega)))
          (m5_arr32 (4 * c.max_vars) hs.q_stamp_len rfl (by omega)))
        (m5_arr32 (4 * (c.max_vars + 1)) hc.frame_trail_len rfl (by omega)))
      (m5_arr32 (4 * (c.max_vars + 1)) hc.frame_dec_len rfl (by omega))
  have hT1 : ∀ k,
      (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
        array (t := i32) c.pWsort s.scratch.wsort ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) k →
      (region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2 (m5_arr32 (16 * c.max_vars) hc.wvec_len (by omega) (by omega))
                    (m5_arr32 (8 * c.max_vars) hc.repr_len (by omega) (by omega)))
                  (m5_arr32 (8 * c.max_vars) hs.wsort_len (by omega) (by omega)))
                (m5_arr32 (8 * c.max_vars) hs.work_stk1_len (by omega) (by omega)))
              (m5_arr32 (8 * c.max_vars) hs.work_stk2_len (by omega) (by omega)))
            (m5_arr32 (8 * c.max_vars) hs.tarjan_mark_len (by omega) (by omega)))
          (m5_arr32 (8 * c.max_vars) hs.tarjan_reach_len (by omega) (by omega)))
        (m5_arr64 (8 * c.max_vars) hs.score_len rfl (by omega)))
      (m5_arr64 (8 * c.max_vars) hs.sim_sig_len rfl (by omega))
  have hT2 : ∀ k,
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
        array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
        array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
        array (t := i32) c.pDelayed s.scratch.delayed ⋆
        array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
        array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf) k →
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2
                    (m5_arr32 (8 * c.minDepth) hc.min_stk_len
                      (by unfold FullCfg.minDepth; omega) (by unfold FullCfg.minDepth; omega))
                    (m5_arr32 256 hs.glue_used_len (by decide) (by decide)))
                  (m5_arr32 64 hs.last_learned_len (by decide) (by decide)))
                (m5_arr32 (4 * c.arena_cap) hc.arena_len_arr rfl (by omega)))
              (m5_arr32 (4 * c.wcap) hc.wstk_len_arr rfl (by omega)))
            (m5_arr32 (12 * c.delayed_cap) hs.delayed_len_arr (by omega) (by omega)))
          (m5_arr32 (4 * c.red_cap) hs.red_refs_len rfl (by omega)))
        (m5_arr32 (4 * c.extend_cap) hs.extend_stk_len rfl (by omega)))
      (m5_arr32 (4 * c.scratch_cap) hs.scratch_buf_len rfl (by omega))
  have h2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m :=
    sep_mono_r (fun _ h => c.regions_to_avail h)
      (sep_mono_r
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2 (sep_mono2 (sep_mono2 hHead hB) hU1) hU2)
                hU3)
              hT1)
            hT2)
          (fun _ hb => hb))
        h1)
  exact sep_ac h2

private theorem m5_solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c0 c2 : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hcompat : FullM4Compact.FullCfgCompat c0 c2)
    (hch_ptr : c0.hdr = hdr_ptr)
    (hch : c0.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c0.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c2) (hext3 : s3.scratch.extend_len ≤ c2.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c2 s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.store (t := i64) (Arg.var (BitVec.ofNat 64 c0.mv)) (Arg.var hdr_ptr)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 768, ())⟩
        fun p_mx => Expr.load i64 (Arg.var p_mx.fst) fun ld_mx =>
        Expr.let_ ⟨OpCode.sub i64, (Arg.var ld_mx, Arg.var (BitVec.ofNat 64 c0.mv), ())⟩
          fun p_bva => Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 784, ())⟩
            fun p_bva_addr => Expr.store (t := i64) (Arg.var p_bva.fst) (Arg.var p_bva_addr.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 64, ())⟩
                fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
                Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
                  (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v,
                   Arg.var (BitVec.ofNat 64 c0.mv), ())
                fun p2 => Expr.group (sig := [[i64]])
                  (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
                  fun Jr => Expr.let_
                    ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p2.fst, Arg.imm 1, ())⟩
                    fun p3 => Expr.jnz (Arg.var p3.fst)
                      (Expr.jump Jr.fst (Arg.imm 10, ()))
                      (Expr.jump Jr.fst (Arg.imm 0, ()))))) m3 := by
  dsimp only
  have hch2 : c2.hdr = hdr_ptr := hcompat.hdr.trans hch_ptr
  rw [← hch2]
  c0_call hExt
  refine ⟨c2, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [Full.fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [Full.fullExtendSlice, SafetySlice.ofMask] at hm4
  have hm4_f : (FullMem c2 s4 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  refine wp_store_sep (FullM4Compact.full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm4_f) ?_
  intro m4_1 hm4_1
  c0_step
  refine wp_load_of (FullM4Compact.full_load_max_vars_mid hm4_1) ?_
  c0_step
  let bva_bv : BitVec 64 := BitVec.ofNat 64 c2.max_vars - BitVec.ofNat 64 c0.mv
  have hmid_arr : (array64 (c2.hdr + 32) (Full.hdrTailWords c2 s4) ⋆
      (dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
          s4.core.d_cur s4.core.d_val ⋆
        FullCoreArrays c2 s4.core ⋆ FullScratchArrays c2 s4.scratch ⋆ c2.pad ⋆
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_1 := by
    unfold FullM4Compact.FullMemShrinkMid at hm4_1; exact sep_ac hm4_1
  obtain ⟨hst_bva_ok, hm4_bva⟩ := store_array64 (i := 94) bva_bv
    (by rw [Full.hdrTailWords_length]; decide) hmid_arr
  have hptr784 : c2.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c2.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr784] at hst_bva_ok hm4_bva
  refine wp_store_sep ⟨hst_bva_ok, hm4_bva⟩ ?_
  intro m4_2 hm4_2
  c0_step
  have hget4 := loadVal_array64 (i := 4)
    (by rw [List.length_set, Full.hdrTailWords_length]; decide) hm4_2
  rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64 by decide,
    List.getElem_set_ne (by decide)] at hget4
  have hpv4 : (Full.hdrTailWords c2 s4)[4]'(by rw [Full.hdrTailWords_length]; decide) =
      c2.pVals := rfl
  rw [hpv4] at hget4
  refine wp_load_of hget4 ?_
  have hmv0_bd := c0.hmv; have hmx0_bd := c0.hmaxv; have hbva0 := c0.hbva
  unfold dimacsBound at hmv0_bd hmx0_bd
  have hm4_2_b : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
        s4.core.d_cur s4.core.d_val ⋆
      bytes c2.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
      (M5CheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_2 := by
    have ha1 : (array (t := i8) c2.pVals s4.core.vals ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (M5CheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      unfold M5CheckRest FullCoreArrays FullCoreByteArrs at *; exact sep_ac hm4_2
    have hm2x : c2.max_vars < 2 * dimacsBound := c2.hmaxv
    unfold dimacsBound at hm2x
    have ha2 : (bytes c2.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (M5CheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      refine sep_mono (fun _ hf => ?_) ha1
      have hbytes := array_eq_bytesOf (t := i8) c2.pVals s4.core.vals
        (by simp [Ty.bytes, Ty.size, i8, hlen4.core_ok.vals_len]; omega) hf
      rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
    exact sep_ac ha2
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 c2.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, s4.core.vals.map UInt8.ofBitVec, c0.mv,
    M5CheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by have := hcompat.max_vars; simp [hlen4.core_ok.vals_len]; omega,
    by have := c2.hmaxv; unfold dimacsBound at this; simp [hlen4.core_ok.vals_len]; omega,
    by simpa [sep_assoc] using hm4_2_b, ?_⟩
  intro ok mv' nc' cur' val' m5 _ hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    m5_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca, ← hcompat.hdr, ← hcompat.avail]
      exact m5_checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  refine wp_join_group (ts := [i64])
    (fun (res_v, ()) m6 => (res_v = 0#64 ∨ res_v = 10#64) ∧ m6 = m5)
    (fun _ ⟨res_v, ⟨⟩⟩ m6 ⟨hres_v, hm6⟩ => by
      rw [hm6]; c0_hsteps; exact hRet res_v m5 hres_v hm5_reg)
    (fun Jr hJr => by
      c0_hsteps
      · exact hJr (10#64, ()) m5 ⟨Or.inr rfl, rfl⟩
      · exact hJr (0#64, ()) m5 ⟨Or.inl rfl, rfl⟩)

/-- Parametric `Func.wp` theorem for `kissat_solve_bytes_m5` against `Full.fullSolveBytesCoreSpec`.
-/
theorem kissat_solve_bytes_m5_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Γ "full_preprocess_m5" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      Γ "full_search_m5" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullSolveBytesCoreSpec a m Q X →
      Func.wp Γ kissat_solve_bytes_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_m5_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ _ hf => by rw [hf0] at hf; simp at hf) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ hcp => absurd hcp0 hcp) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ hwp => absurd hwp0 hwp) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, m5_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [m5_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [m5_alignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hw_small => ?_, fun hw_ge_not => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun mv nc _ _ _ _ hsz _ _ _ => by unfold fullFixedBytes at hsz; omega) hm
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := m5_alignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' hfail; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      m5_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h)
      (fun mv nc i0 _ _ _ hsz _ hhdr _ => by
        have hlt := hfail mv nc (cnfBytes.drop i0) hhdr; rw [hav_toNat] at hlt; omega) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    have hvals_take : s0.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
      have hbva := c.hbva; rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 huns_tr hm1; c0_hsteps
    · rcases hpb_dom with rfl | h1 | rfl
      · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) ?_
          (m5_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut); cases h20
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (m5_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := m5_parseDimacs_vars_pos hparse
      have hnot_ut : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc → False := by
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        rw [hc] at h20; cases h20
      have hm1_load :
          (FullMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m1 := sep_ac hm1
      have hload_mv : loadVal m1 i64 (work_ptr + ((8 - (work_ptr &&& 7)) &&& 7)) =
          some (BitVec.ofNat 64 c.mv) := by
        rw [hhdr_bv, ← hch]
        exact FullArenaTactics.load_full_mv hm1_load
      refine wp_load_of hload_mv ?_
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp c2 s2 m2 hcomp2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      have hch2 : c2.hdr = hdr_addr := hcomp2.hdr.trans hch
      have hca2 : c2.avail = availNat := hcomp2.avail.trans hca
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (m5_merge_arena hwfit (by omega) hch2 hca2 hlen2 (sep_ac hm2))
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
        (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
          p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
          (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, cr, sr⟩ mr ⟨hcompr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          have hchr : cr.hdr = hdr_addr := hcompr.hdr.trans hch
          have hcar : cr.avail = availNat := hcompr.avail.trans hca
          c0_hsteps
          · exact m5_solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hcompr
              hch_ptr (by rw [← hpad_bv]; exact hch_ptr) hca hlen_r (hrv_ext hc) hmr
              fun res m_end hres hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 =>
                    (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
                  hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
              (m5_merge_arena hwfit (by omega) hchr hcar hlen_r hmr))
        (fun Jr hJr => by
          c0_hsplit
          · c0_hsteps
            exact hJr (10#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inr (Or.inl rfl), (fun h => by cases h),
              (fun _ => hpp10 hc), sep_ac hm2⟩
          · c0_hsteps_nogrp
            refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
              (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
                p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
                (p.1 = 20#64 → cnf.Unsat) ∧
                (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ p mr hp => by c0_hsteps; exact hJr p mr hp)
              (fun Jr2 hJr2 => by
                c0_hsplit
                · c0_hsteps
                  exact hJr2 (0#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inl rfl,
                    (fun h => by cases h), (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_hsteps; rw [hhdr_bv, ← hch2]; c0_call hSearch
                  refine ⟨c2, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    rfl, hinv2, hcl2, hm2, ?_⟩
                  intro r3 c3 s3 m3 hcomp3 hlen3 hr3_dom hur3 hext3 hm3; c0_hsteps
                  exact hJr2 (r3, c3, s3) m3 ⟨hcomp2.trans hcomp3, hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hur3 h20), hext3, sep_ac hm3⟩))

theorem kissat_solve_bytes_m5_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Γ "full_preprocess_m5" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      Γ "full_search_m5" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesSpec a m Q X →
      Func.wp Γ kissat_solve_bytes_m5_body a m Q X :=
  fun _ _ _ _ h => kissat_solve_bytes_m5_core_wp Γ hInit hParse hPre hSearch hExt hCheck
    _ _ _ _ (fullSolveBytesCoreSpec_of_spec h)

private theorem m5Orch_fns_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → Full.fullSolveBytesCoreSpec a m Q X) :
    ∀ fn ∈ m5OrchModule.fns, ∀ xs m Q X,
      mkM5OrchEnv mainSpec fn.name fn.as fn.rs xs m Q X →
        Func.wp (mkM5OrchEnv mainSpec) fn.body xs m Q X := by
  let Γ := mkM5OrchEnv mainSpec
  let h0 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 0
    ⟨"full_calc_ext_cap_m5", [i64], [i64], fullCalcExtCapM5Spec, true⟩
    (hno := fullCalcExtCapM5Spec_noExit)
  let h1 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 1
    ⟨"full_calc_scr_cap_m5", [i64], [i64], fullCalcScrCapM5Spec, true⟩
    (hno := fullCalcScrCapM5Spec_noExit)
  let h5 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 5
    ⟨"full_trans_lit_m5", [i64, i32], [.bool], Full.fullTransLitSpec, true⟩
  let h6 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 6
    ⟨"full_transitive_m5", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  let h7 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 7
    ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64], fullVivifyTierM5Spec, true⟩
    (hno := fullVivifyTierM5Spec_noExit)
  let h8 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_vivify_m5", [i64], [i64], m5VivifySpec, true⟩
    (hno := m5VivifySpec_noExit)
  let h9 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 9
    ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  let h10 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 10
    ⟨"full_probe_tail_m5", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  let h11 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_reduce_m5", [i64, .bool], [i64], Full.fullReduceSpec, true⟩
  let h12 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_reorder_m5", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  let h13 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 13
    ⟨"full_probe_m5", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  let h14 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_eliminate_m5", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  let h15 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  let h16 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 16
    ⟨"full_simplify_m5", [i64, .bool, .bool], [i64], FullM4.m4SimplifySpec, true⟩
  let h17 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 17
    ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩
  let h2 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 2
    ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  let h3 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 3
    ⟨"full_probe_dticks_m5", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  let h4 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 4
    ⟨"full_elim_dticks_m5", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  let h19 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 19
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h20 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 20
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let h21 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 21
    ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  let h22 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 22
    ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  let h23 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 23
    ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  let h24 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 24
    ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  let h25 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 25
    ⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩
  let h26 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 26
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩
  let h27 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], Full.fullInitArenasSpec, true⟩
  let h28 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩
  let h29 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 29
    ⟨"full_zero_tables1", [i64], [], Full.fullZeroTables1Spec, true⟩
  let h30 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_zero_tables2", [i64], [], Full.fullZeroTables2Spec, true⟩
  let h31 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 31
    ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  let h32 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 32
    ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  let h33 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 33
    ⟨"full_switch_mode", [i64], [], Full.fullSwitchModeSpec, true⟩
  let h34 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 34
    ⟨"full_rephase", [i64], [], Full.fullRephaseSpec, true⟩
  let h35 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 35
    ⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩
  let h36 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 36
    ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let h37 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 37
    ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  let h38 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 38
    ⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩
  let h39 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 39
    ⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  let h40 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 40
    ⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩
  let h41 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 41
    ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  let h42 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 42
    ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  let h43 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 43
    ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  let h44 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 44
    ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
  let h45 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 45
    ⟨"full_decide", [i64], [i64], Full.fullDecideSpec, true⟩
  let h46 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 46
    ⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩
  let h47 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 47
    ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩
  let h48 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_lucky", [i64], [i64], Full.fullLuckySpec, true⟩
  let h49 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩
  let h50 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 50
    ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  let h51 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 51
    ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  let h52 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 52
    ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  let h53 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 53
    ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  let h54 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 54
    ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  let h55 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 55
    ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], FullM4Sweep.m4SweepVarSpec, true⟩
  let h56 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  let h57 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  let h58 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 58
    ⟨"full_viv_collect_m4", [i64, i64], [i64], FullM4VivBce.fullVivCollectM4Spec, true⟩
  let h59 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 59
    ⟨"full_viv_keys_m4", [i64, i64], [], FullM4VivBce.fullVivKeysM4Spec, true⟩
  let h60 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 60
    ⟨"full_viv_sort_sched_m4", [i64, i64], [], FullM4VivBce.fullVivSortSchedM4Spec, true⟩
  let h61 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_viv_clause_m4", [i64, i32], [i64], FullM4VivBce.fullVivClauseM4Spec, true⟩
  let h62 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 62
    ⟨"full_viv_clear_tier_m4", [i64, i64], [], FullM4VivBce.fullVivClearTierM4Spec, true⟩
  let h63 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 63
    ⟨"full_reorder_queue", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  let h64 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 64
    ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  let h65 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 65
    ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  let h66 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 66
    ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  let h67 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 67
    ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩
  let h68 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 68
    ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
  let h69 := mkM5OrchEnv_row_at (mainSpec := mainSpec) 69
    ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
  intro fn hfn xs m Q X hs
  change fn ∈ m5Orch_fns at hfn
  simp only [m5Orch_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact wp_noExit_lift (full_calc_ext_cap_m5_wp Γ xs m Q _
      (mkM5OrchEnv_row_elim 0 ⟨"full_calc_ext_cap_m5", [i64], [i64], fullCalcExtCapM5Spec, true⟩
        rfl rfl hs))
  · exact wp_noExit_lift (full_calc_scr_cap_m5_wp Γ xs m Q _
      (mkM5OrchEnv_row_elim 1 ⟨"full_calc_scr_cap_m5", [i64], [i64], fullCalcScrCapM5Spec, true⟩
        rfl rfl hs))
  · exact wp_noExit_lift (full_init_state_m5_wp Γ h19 h25 h26 h0 h1 h27 h28 h29 h30 xs m Q _
      (mkM5OrchEnv_row_elim 2 ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        Full.fullInitStateSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_probe_dticks_m5_wp Γ h24 xs m Q _
      (mkM5OrchEnv_row_elim 3 ⟨"full_probe_dticks_m5", [i64, .bool], [i64],
        FullFastSched.schedProbeDticksSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_elim_dticks_m5_wp Γ h24 xs m Q _
      (mkM5OrchEnv_row_elim 4 ⟨"full_elim_dticks_m5", [i64, .bool], [i64],
        FullFastSched.schedElimDticksSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_trans_lit_m5_wp Γ h49 h50 xs m Q _
      (mkM5OrchEnv_row_elim 5 ⟨"full_trans_lit_m5", [i64, i32], [.bool],
        Full.fullTransLitSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_transitive_m5_wp Γ h36 h5 h37 h43 xs m Q _
      (mkM5OrchEnv_row_elim 6 ⟨"full_transitive_m5", [i64, i64], [i64],
        FullFastBveBudgets.fullTransitiveFastSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_vivify_tier_m5_wp Γ h36 h58 h59 h60 h61 h37 h62 xs m Q _
      (mkM5OrchEnv_row_elim 7 ⟨"full_vivify_tier_m5", [i64, i64, i64, i64], [i64],
        fullVivifyTierM5Spec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_vivify_m5_wp Γ h36 h7 xs m Q _
      (mkM5OrchEnv_row_elim 8 ⟨"full_vivify_m5", [i64], [i64], m5VivifySpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_sweep_dense_m5_wp Γ h55 xs m Q _
      (mkM5OrchEnv_row_elim 9 ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64],
        FullDefSweep.fullSweepDenseSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_probe_tail_m5_wp Γ h56 h6 h23 h57 h8 xs m Q _
      (mkM5OrchEnv_row_elim 10 ⟨"full_probe_tail_m5", [i64, i64], [i64],
        FullFastSched.schedProbeTailSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_reduce_m5_wp Γ h21 h22 h41 h38 h39 h40 h36 h37 h42 xs m Q _
      (mkM5OrchEnv_row_elim 11 ⟨"full_reduce_m5", [i64, .bool], [i64],
        Full.fullReduceSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_reorder_m5_wp Γ h63 xs m Q _
      (mkM5OrchEnv_row_elim 12 ⟨"full_reorder_m5", [i64, i64], [i64],
        FullM4.m4ReorderSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_probe_m5_wp Γ h3 h22 h32 h52 h54 h9 h53 h51 h10 xs m Q _
      (mkM5OrchEnv_row_elim 13 ⟨"full_probe_m5", [i64, .bool], [i64],
        FullFastSched.schedProbeSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_eliminate_m5_wp Γ h4 h22 h32 h52 h64 h23 h65 h66 h53 h67 xs m Q _
      (mkM5OrchEnv_row_elim 14 ⟨"full_eliminate_m5", [i64, .bool], [i64],
        FullFastSched.schedEliminateSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_preprocess_m5_wp Γ h37 h42 h48 h68 h69 h32 h13 xs m Q _
      (mkM5OrchEnv_row_elim 15 ⟨"full_preprocess_m5", [i64], [i64],
        FullM4.m4PreprocessSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_simplify_m5_wp Γ h36 h13 h14 h68 h69 xs m Q _
      (mkM5OrchEnv_row_elim 16 ⟨"full_simplify_m5", [i64, .bool, .bool], [i64],
        FullM4.m4SimplifySpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (full_search_m5_wp Γ h37 h44 h11 h33 h35 h46 h12 h34 h16 h45 xs m Q _
      (mkM5OrchEnv_row_elim 17 ⟨"full_search_m5", [i64], [i64],
        FullM4.m4SearchSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (kissat_solve_bytes_m5_core_wp Γ h2 h31 h15 h17 h47 h20 xs m Q _
      (hweaken xs m Q _ (mkM5OrchEnv_row_elim 18
        ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ rfl rfl hs)))

/-- Unconditional `ModuleOk` for `m5OrchModule` parameterized by `mainSpec`. -/
theorem mkM5OrchEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → Full.fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM5OrchEnv mainSpec) m5OrchModule :=
  Module.moduleOk_of_checkAcyclic m5Orch_acyclic m5Orch_fns_wf (m5Orch_fns_wp mainSpec hweaken)

/-- Unconditional closed `ModuleOk` for `m5OrchEnv` on all `19/19` owned `_m5` functions and
`51` canonical externs (`0` SAT/model proofs). -/
theorem m5Orch_moduleOk : ModuleOk m5OrchEnv m5OrchModule :=
  mkM5OrchEnv_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional closed `ModuleOk` for `m5OrchUnsatEnv` (`XPost := False` NV env). -/
theorem m5OrchUnsatEnv_moduleOk : ModuleOk m5OrchUnsatEnv m5OrchModule :=
  mkM5OrchEnv_moduleOk fullUnsatWitnessSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

/-- Headline UNSAT-only soundness of `kissat_solve_bytes_m5` under `m5OrchEnv`. -/
theorem m5Orch_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5OrchEnv kissat_solve_bytes_m5_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  kissat_solve_bytes_m5_wp m5OrchEnv
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 2
      ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 31
      ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 15
      ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 17
      ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 47
      ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullSolveBytesSpec) 20
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under `m5OrchUnsatEnv`:
`kissat_solve_bytes_m5` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes`
with `4096`-byte workspace and `fuel = 16`. -/
theorem m5Orch_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5OrchUnsatEnv kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  kissat_solve_bytes_m5_core_wp m5OrchUnsatEnv
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 2
      ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 31
      ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 15
      ⟨"full_preprocess_m5", [i64], [i64], FullM4.m4PreprocessSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 17
      ⟨"full_search_m5", [i64], [i64], FullM4.m4SearchSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 47
      ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩)
    (mkM5OrchEnv_row_at (mainSpec := fullUnsatWitnessSpec) 20
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

end TopAndNonVacuity

end LeanQbe.T.Examples.Kissat.FullM5Orch
