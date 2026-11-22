module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0b
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2e
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Closed `ModuleOk` & Non-Vacuity

Top-level umbrella proof module for `m6/cong-subst-worklist` (`RC-25`, UNSAT-only):
1. Publicly re-exports `FullM6CongSubst` and all `23` parametric `(Γ : Env)` `Func.wp` proofs
   across `FullM6CongSubstProof{0,0b,1a,1b,2a,2b,2b2,2c,2d,2e}`.
2. Closes the `39`-row `m6CongSubstSpecTable` (`23` owned M6 functions + `16` canonical external
   callees, all `noExit = true`), `m6CongSubstEnv`, and `m6CongSubst_moduleOk`.
3. Proves concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on `nvOneLitMem`
   (sparse: `full_tarjan_scc`, `full_substitute`) and `nvBvaDenseMem` (dense:
   `full_congruence_dense`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test

/-! ## 1. Closed `39`-Row `m6CongSubstSpecTable`, `m6CongSubstEnv`, and `ModuleOk` -/

/-- Closed `39`-row specification table for `m6CongSubstModule` (`23` owned M6 congruence &
substitute functions + `16` canonical external callees, all `noExit = true`). -/
@[expose] public def m6CongSubstSpecTable : List SpecEntry :=
  [ ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩
  , ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  , ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  , ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], m6CongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], m6CongEmitXorSpec, true⟩
  , ⟨"full_cong_has_clause_k", [i64, i32], [.bool], m6CongHasClauseKSpec, true⟩
  , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64], m6CongExtractXorKSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], m6CongTryXorIteSpec, true⟩
  , ⟨"full_cong_count_bins", [i64], [], m6CongCountBinsSpec, true⟩
  , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], m6CongEbMatchSpec, true⟩
  , ⟨"full_cong_extract_binaries", [i64, i64], [i64], m6CongExtractBinariesSpec, true⟩
  , ⟨"full_cong_find_units_equivs", [i64], [i64], m6CongFindUnitsEquivsSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], m6CongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m6CongAndMatchSpec, true⟩
  , ⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec, true⟩
  , ⟨"full_cong_enq_var", [i64, i64, i32], [], m6CongEnqVarSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m6CongEvalGateSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m6CongWorkStepSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m6CongWorklistSpec, true⟩
  , ⟨"full_cong_fwd_subsume", [i64, i64], [i64], m6CongFwdSubsumeSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  , ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  , ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩ ]

public theorem m6CongSubstSpecTable_nodup : (m6CongSubstSpecTable.map SpecEntry.name).Nodup := by
  decide

public theorem m6CongSubstSpecTable_noExit :
    ∀ e ∈ m6CongSubstSpecTable, e.noExit = true := by
  intro e he
  simp only [m6CongSubstSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment for `m6CongSubstModule`. -/
@[expose] public def m6CongSubstEnv : Env := Env.ofTable m6CongSubstSpecTable

public theorem m6CongSubstEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6CongSubstEnv f as bs xs m Q X → m6CongSubstEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6CongSubstSpecTable_noExit

private theorem m6Env_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6CongSubstSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m6CongSubstEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m6CongSubstSpecTable_nodup
      (hno xs m Q X hs)

private theorem m6Env_arenaNext_cong :
    ∀ xs m Q X, FullCongSpecs.fullArenaNextSpec xs m Q X →
      m6CongSubstEnv "full_arena_next" [i64, i32] [i32] xs m Q X :=
  m6Env_row (sp := fullArenaNextSpec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)

private theorem m6Env_hasBin_cong :
    ∀ xs m Q X, FullCongSpecs.fullHasBinSpec xs m Q X →
      m6CongSubstEnv "full_has_bin" [i64, i32, i32] [.bool] xs m Q X :=
  m6Env_row (sp := fullHasBinSpec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)

private theorem m6Env_congFind_cong :
    ∀ xs m Q X, FullCongSpecs.fullCongFindSpec xs m Q X →
      m6CongSubstEnv "full_cong_find" [i64, i32] [i32] xs m Q X :=
  m6Env_row (sp := fullCongFindSpec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)

private theorem m6Env_hasTernary_cong :
    ∀ xs m Q X, FullCongSpecs.fullHasTernarySpec xs m Q X →
      m6CongSubstEnv "full_has_ternary" [i64, i32, i32, i32] [.bool] xs m Q X :=
  m6Env_row (sp := fullHasTernarySpec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)

private theorem m6Env_sortU32_cong :
    ∀ xs m Q X, FullCongSpecs.fullSortU32Spec xs m Q X →
      m6CongSubstEnv "full_sort_u32" [i64, i32] [] xs m Q X :=
  m6Env_row (sp := fullSortU32Spec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)

private theorem m6Env_addBin_cong :
    ∀ xs m Q X, FullCongSpecs.fullAddBinSpec xs m Q X →
      m6CongSubstEnv "full_add_bin" [i64, i32, i32] [i64] xs m Q X := by
  have hAdd := m6Env_row (nm := "full_add_bin") (as := [i64, i32, i32]) (bs := [i64])
    (sp := fullAddBinSpec) (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, _ha, _hb, hent, hm, hQ⟩
  refine hAdd _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, fun _ _ => hent, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ws' wl' wu' nb' om' inc' ph' wso' m'
      hlen' hw' _ h20 _ hm' =>
      hQ r _ m' hlen' hw' hcl0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun h => (h20 h).2) hm'⟩

public theorem m6_tarjan_scc_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_tarjan_scc", [i64], [i64], full_tarjan_scc_body⟩
      ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccSpec, true⟩ :=
  SpecEntry.Impl.of (full_tarjan_scc_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_subst_rewrite_bins_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_subst_rewrite_bins", [i64], [.bool], full_subst_rewrite_bins_body⟩
      ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩ :=
  SpecEntry.Impl.of (full_subst_rewrite_bins_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_subst_rewrite_ar_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_subst_rewrite_ar", [i64], [.bool], full_subst_rewrite_ar_body⟩
      ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩ :=
  SpecEntry.Impl.of (full_subst_rewrite_ar_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_substitute_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_substitute", [i64], [i64], full_substitute_body⟩
      ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩ :=
  SpecEntry.Impl.of (full_substitute_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_merge_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_merge", [i64, i32, i32], [.bool], full_cong_merge_body⟩
      ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_merge_wp m6CongSubstEnv m6Env_congFind_cong m6Env_addBin_cong)

public theorem m6_cong_extract_ite_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], full_cong_extract_ite_body⟩
      ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], m6CongExtractIteSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_extract_ite_wp m6CongSubstEnv m6Env_hasTernary_cong)

public theorem m6_cong_emit_xor_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], full_cong_emit_xor_body⟩
      ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], m6CongEmitXorSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_emit_xor_wp m6CongSubstEnv)

public theorem m6_cong_has_clause_k_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_has_clause_k", [i64, i32], [.bool], full_cong_has_clause_k_body⟩
      ⟨"full_cong_has_clause_k", [i64, i32], [.bool], m6CongHasClauseKSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_has_clause_k_wp m6CongSubstEnv)

public theorem m6_cong_extract_xor_k_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64], full_cong_extract_xor_k_body⟩
      ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64], m6CongExtractXorKSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_extract_xor_k_wp m6CongSubstEnv m6Env_sortU32_cong
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_try_xor_ite_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], full_cong_try_xor_ite_body⟩
      ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
        m6CongTryXorIteSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_try_xor_ite_wp m6CongSubstEnv m6Env_hasTernary_cong
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_count_bins_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_count_bins", [i64], [], full_cong_count_bins_body⟩
      ⟨"full_cong_count_bins", [i64], [], m6CongCountBinsSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_count_bins_wp m6CongSubstEnv)

public theorem m6_cong_eb_match_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], full_cong_eb_match_body⟩
      ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], m6CongEbMatchSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_eb_match_wp m6CongSubstEnv m6Env_hasBin_cong)

public theorem m6_cong_extract_binaries_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_extract_binaries", [i64, i64], [i64], full_cong_extract_binaries_body⟩
      ⟨"full_cong_extract_binaries", [i64, i64], [i64], m6CongExtractBinariesSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_extract_binaries_wp m6CongSubstEnv
    m6Env_arenaNext_cong m6Env_hasBin_cong m6Env_addBin_cong
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_find_units_equivs_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_find_units_equivs", [i64], [i64], full_cong_find_units_equivs_body⟩
      ⟨"full_cong_find_units_equivs", [i64], [i64], m6CongFindUnitsEquivsSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_find_units_equivs_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_extract_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_extract", [i64, i64, i64], [i64], full_cong_extract_body⟩
      ⟨"full_cong_extract", [i64, i64, i64], [i64], m6CongExtractSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_extract_wp m6CongSubstEnv m6Env_arenaNext_cong m6Env_hasBin_cong
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_and_match_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_and_match", [i64, i32, i32], [.bool], full_cong_and_match_body⟩
      ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m6CongAndMatchSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_and_match_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_xor_match_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_xor_match", [i64, i32, i32], [i32], full_cong_xor_match_body⟩
      ⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_xor_match_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_enq_var_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_enq_var", [i64, i64, i32], [], full_cong_enq_var_body⟩
      ⟨"full_cong_enq_var", [i64, i64, i32], [], m6CongEnqVarSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_enq_var_wp m6CongSubstEnv)

public theorem m6_cong_eval_gate_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], full_cong_eval_gate_body⟩
      ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m6CongEvalGateSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_eval_gate_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_work_step_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], full_cong_work_step_body⟩
      ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m6CongWorkStepSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_work_step_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_worklist_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], full_cong_worklist_body⟩
      ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m6CongWorklistSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_worklist_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_cong_fwd_subsume_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_cong_fwd_subsume", [i64, i64], [i64], full_cong_fwd_subsume_body⟩
      ⟨"full_cong_fwd_subsume", [i64, i64], [i64], m6CongFwdSubsumeSpec, true⟩ :=
  SpecEntry.Impl.of (full_cong_fwd_subsume_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6_congruence_dense_impl :
    SpecEntry.Impl m6CongSubstEnv
      ⟨"full_congruence_dense", [i64, i64], [i64], full_congruence_dense_body⟩
      ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩ :=
  SpecEntry.Impl.of (full_congruence_dense_wp m6CongSubstEnv
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h))
    (m6Env_row (by simp [m6CongSubstSpecTable]) (fun _ _ _ _ h => h)))

public theorem m6CongSubst_allFns_wf : AllFns Fn.Wf m6CongSubstModule.fns :=
  ⟨full_tarjan_scc_wf, full_subst_rewrite_bins_wf, full_subst_rewrite_ar_wf,
    full_substitute_wf, full_cong_merge_wf, full_cong_extract_ite_wf, full_cong_emit_xor_wf,
    full_cong_has_clause_k_wf, full_cong_extract_xor_k_wf, full_cong_try_xor_ite_wf,
    full_cong_count_bins_wf, full_cong_eb_match_wf, full_cong_extract_binaries_wf,
    full_cong_find_units_equivs_wf, full_cong_extract_wf, full_cong_and_match_wf,
    full_cong_xor_match_wf, full_cong_enq_var_wf, full_cong_eval_gate_wf,
    full_cong_work_step_wf, full_cong_worklist_wf, full_cong_fwd_subsume_wf,
    full_congruence_dense_wf, trivial⟩

public theorem m6CongSubst_tableImpl :
    TableImpl m6CongSubstEnv m6CongSubstModule.fns m6CongSubstSpecTable :=
  ⟨m6_tarjan_scc_impl, m6_subst_rewrite_bins_impl, m6_subst_rewrite_ar_impl,
    m6_substitute_impl, m6_cong_merge_impl, m6_cong_extract_ite_impl, m6_cong_emit_xor_impl,
    m6_cong_has_clause_k_impl, m6_cong_extract_xor_k_impl, m6_cong_try_xor_ite_impl,
    m6_cong_count_bins_impl, m6_cong_eb_match_impl, m6_cong_extract_binaries_impl,
    m6_cong_find_units_equivs_impl, m6_cong_extract_impl, m6_cong_and_match_impl,
    m6_cong_xor_match_impl, m6_cong_enq_var_impl, m6_cong_eval_gate_impl,
    m6_cong_work_step_impl, m6_cong_worklist_impl, m6_cong_fwd_subsume_impl,
    m6_congruence_dense_impl, trivial⟩

/-- Headline closed `ModuleOk` certifying all `23` M6 congruence closure & 2-round substitute
functions in `m6CongSubstModule` under `m6CongSubstEnv` (`0` gaps, `0` SAT proofs). -/
public theorem m6CongSubst_moduleOk : ModuleOk m6CongSubstEnv m6CongSubstModule :=
  Env.ofTable_moduleOk m6CongSubst_acyclic m6CongSubst_allFns_wf m6CongSubst_tableImpl

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNonVacuity

private theorem nvM6F0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM6_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
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
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvOneLitState = [] := rfl; simp [this] at hr

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_tarjan_scc`. -/
public theorem nv_m6_tarjan_scc :
    Func.wp m6CongSubstEnv full_tarjan_scc_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m6_tarjan_scc_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvM6_sparseW, rfl, hm,
      fun r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m' hsp _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hsp, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_substitute`. -/
public theorem nv_m6_substitute :
    Func.wp m6CongSubstEnv full_substitute_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact m6_substitute_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvM6_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM6F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_congruence_dense`. -/
public theorem nv_m6_congruence_dense :
    Func.wp m6CongSubstEnv full_congruence_dense_body (nvOneLitCfg.hdr, 1000#64, ())
      nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m6_congruence_dense_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, hm,
      fun r s' m' hd _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvM6F0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6CongSubst