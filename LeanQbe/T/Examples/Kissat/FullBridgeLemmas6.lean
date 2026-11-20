module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullSubstLemmas
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas
public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Shards 12–14 (`Stage 4`)

Adapts three landed Stage-4 shards onto canonical `FullSpec2` / `FullSpec3` contracts (`10` fns):
- Part 4 (`FullSubstLemmas`, `4 / 4` clean canonical): `full_subst_elim_vars`,
  `full_subst_rewrite_bins`, `full_subst_rewrite_ar`, `full_substitute`.
- Part 5 (`FullBveVarLemmas`, `3 / 3` clean canonical): `full_bve_ext_need`,
  `full_bve_commit_res`, `full_bve_var`.
- Part 6 (`FullDenseWatchLemmas`, `3` fns): `full_reduce`, `full_enter_dense`,
  `full_rebuild_watches`. All `3` target contracts and `7` callees (`fullIsqrtSpec`,
  `fullIlog10Spec`, `fullArenaNextSpec`, `fullRecomputeTiersSpec`, `fullMarkReasonsSpec`,
  `fullBacktrackSpec`, `fullWatchPushSpec`) bridge cleanly onto canonical `FullSpec2` / `FullSpec3`;
  the remaining `4` callee hypotheses await `FullSpec2` updates aligning them with
  `FullDenseWatchSpecs`:
  - `FullDenseWatchSpecs.fullSortRedsSpec` (`sc'.work_stk2 = s.scratch.work_stk2`)
  - `FullDenseWatchSpecs.fullPropagateSpec` (`FullConflictInv`, requiring `confl_type = 2#64`)
  - `FullDenseWatchSpecs.fullSweepBinsSpec` (`wusable := 0#64` and `DenseWatchesInv`)
  - `FullDenseWatchSpecs.fullArenaSweepSpec` (`0 < s.core.cur_level` trail/vals preservation
    including on `r = 3#64` OOM)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## Part 4: `FullSubstLemmas` (`4` fns, `4 / 4` canonical) -/

section Part4

private theorem fullBacktrackSpec_of_subst {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullSubstSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htl_lt, htrl_lt, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htl_lt, htrl_lt, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hprop hcl hps hsh htrl hbv hwt hot hm' => ?_⟩
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hprop hcl hps hsh htrl
    (fun ⟨F0, F_cur, hinv⟩ =>
      hbv ⟨F0, F_cur, Or.inl (hinv.elim id id)⟩)
    hwt
    (fun F0 F_cur hw hlt => hot F0 F_cur hw.toOtfs hlt)
    hm'

theorem full_subst_elim_vars_bridge_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSubstElimVarsSpec a m Q X → Func.wp Γ full_subst_elim_vars_body a m Q X :=
  full_subst_elim_vars_wp Γ hAddUnit hProp hExtPush2 hSetInact

theorem full_subst_rewrite_bins_bridge_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Func.wp Γ full_subst_rewrite_bins_body a m Q X :=
  full_subst_rewrite_bins_wp Γ hAddUnit hAddBin

theorem full_subst_rewrite_ar_bridge_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteArSpec a m Q X → Func.wp Γ full_subst_rewrite_ar_body a m Q X :=
  full_subst_rewrite_ar_wp Γ hArenaNext hAddUnit hAddBin

theorem full_substitute_bridge_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTarjan : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X)
    (hElimVars : ∀ a m Q X, fullSubstElimVarsSpec a m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] a m Q X)
    (hRewriteBins : ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] a m Q X)
    (hRewriteAr : ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_body a m Q X :=
  full_substitute_wp Γ (fullBacktrackSpec_of_subst hBacktrack) hTarjan hElimVars
    hRewriteBins hRewriteAr hArenaSweep hProp

end Part4

/-! ## Part 5: `FullBveVarLemmas` (`3` fns, `3 / 3` canonical) -/

section Part5

private theorem resBuf_to_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullResBufOkW F_cur s r_end p) : FullBveVarSpecs.FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem resBuf_of_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem bveAddUnit_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf hof hm' => ?_⟩
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    { s.scratch with
      phases := phases', target_assigned := ta', best_assigned := ba',
      phases_target := pt', phases_best := pb', heap := hp', pos := ps',
      heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
    m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hltf hof hm'

private theorem bveSetInactive_adapter {Γ : Env}
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hSetInact _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  split
  · exact hQ s.core.flags s.core.unassigned m hlen.core_ok.flags_len hm
  · exact hQ

private theorem bveCommitRes_adapter {Γ : Env}
    (hCommitRes : ∀ a m Q X, fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, hbuf, hm, hQ⟩
  exact hCommitRes _ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, resBuf_of_bve hbuf, hm, hQ⟩

private theorem bveTryBce_adapter {Γ : Env}
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk_lit, cr, opp_off, opp_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr, hoff, hopp, hm, hQ⟩
  rcases hdense with ⟨hlen, hw, hlm, hnd, hext, hcl0, hdm⟩
  refine hTryBce _ m Q X ⟨c, s, R, rfl, hlen, hlm, hoff, hcr, hopp, hm,
    fun blk lm' tmp' m' hlen' hlm' hm' => ?_⟩
  have hw' : FullWitnessInv c F0 F_cur
      { s.core with lit_mark := lm', tmp := tmp' } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact hQ blk lm' tmp' m' ⟨hlen', hw', hlm', hnd, hext, hcl0, hdm⟩ hm'

private theorem bveWeaken_adapter {Γ : Env}
    (hWeaken : ∀ a m Q X, fullBveWeakenSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveWeakenSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcnt, hok, hm, hQ⟩
  refine hWeaken _ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcnt, hok, hm,
    fun ok wvec' wstk' wlen' wu' nb' arena' ag' ext' exlen' m' hdense' hrefs hm' => ?_⟩
  exact hQ ok _ m' hdense' rfl rfl rfl hrefs hm'

theorem full_bve_ext_need_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveExtNeedSpec a m Q X → Func.wp Γ full_bve_ext_need_body a m Q X :=
  full_bve_ext_need_wp Γ

theorem full_bve_commit_res_bridge_wp (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveCommitResSpec a m Q X → Func.wp Γ full_bve_commit_res_body a m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, hbuf, hm, hQ⟩
  exact full_bve_commit_res_wp Γ hAlloc hWPush hAddBin (bveAddUnit_adapter hAddUnit) _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, resBuf_to_bve hbuf, hm, hQ⟩

theorem full_bve_var_bridge_wp (Γ : Env)
    (hCollect : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGates : ∀ a m Q X, fullBveGatesSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X)
    (hResolve : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCommitRes : ∀ a m Q X, fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveVarSpec a m Q X → Func.wp Γ full_bve_var_body a m Q X :=
  full_bve_var_wp Γ hCollect hExtNeed (bveWeaken_adapter hWeaken)
    (bveSetInactive_adapter hSetInact) hGates hResolve (bveCommitRes_adapter hCommitRes)
    (bveTryBce_adapter hTryBce) hExtPush2 hDelBin hExtPushCl

end Part5

/-! ## Part 6: `FullDenseWatchLemmas` (`3` fns) -/

section Part6

private theorem dwIsqrt_adapter {Γ : Env}
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullIsqrtSpec a m Q X →
      Γ "full_isqrt" [i64] [i64] a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  exact hIsqrt _ m Q X fun r hsq _ _ => hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq)

private theorem dwRecomputeTiers_adapter {Γ : Env}
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hRecomp _ m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hcore hlen' hpres hm' => ?_⟩
  rcases s' with ⟨c', sc'⟩
  change c' = s.core at hcore
  subst hcore
  exact hQ sc' m' hlen'.scratch_ok hpres.1.1 hpres.1.2 hpres.2.2.1 hm'

private theorem dwMarkReasons_adapter {Γ : Env}
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X := by
  rintro ⟨h, set_flag, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine hMarkRsn _ m Q X ⟨c, F0, s, R, rfl, ⟨hlen, F_cur, hw⟩, hm,
    fun arena' m' hrefs hcl hrm hcore' hm' => ?_⟩
  rcases hcore' with ⟨hlen', F_cur', hw_any⟩
  let s' : FullState := { s with core := { s.core with arena := arena' } }
  have har' : FullArenaClausesInv c F_cur s'.core :=
    { len_ok := hw_any.arena.len_ok
      refs_wf := fun r hr => hw_any.arena.refs_wf r hr
      shrk_term := fun r hr hsh => hw_any.arena.shrk_term r hr hsh
      lits_lt := fun r hr hng => by
        have h0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
        have h1 := hcl r h0
        change fullArenaClauseGarb s' r = false at hng
        rw [h1.2.1] at hng
        change ∀ l ∈ fullArenaClauseLits s' r, l < 2 * s'.core.cur_vars
        rw [h1.2.2]
        exact hw.arena.lits_lt r h0 hng
      entails := fun r hr hng => by
        have h0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
        have h1 := hcl r h0
        change fullArenaClauseGarb s' r = false at hng
        rw [h1.2.1] at hng
        change (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLits s' r))
        rw [h1.2.2]
        exact hw.arena.entails r h0 hng }
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := har'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
        change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change (s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) at hne
        by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · simpa [s', hb] using hrs
        · simp only [s', hb, ↓reduceIte] at hrs ⊢
          have h1 := hcl _ hrs.1
          refine ⟨?_, ?_, ?_⟩
          · change _ ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hrs.1
          · change fullArenaClauseGarb s' _ = false; rw [h1.2.1]; exact hrs.2.1
          · change ∀ q ∈ fullArenaClauseLits s' _, _; rw [h1.2.2]; exact hrs.2.2
      reason_lit_mem := fun idx hidx hne hlg => by
        have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne
        have hrs := hw.reason_inv idx hidx hne0
        have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hb] at hrs
        have h1 := hcl _ hrs.1
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLits s' _
        rw [h1.2.2]
        exact hw.reason_lit_mem idx hidx hne hlg }
  exact hQ arena' m' hlen' hrefs hcl hrm hw' hm'

private theorem dwBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hle, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_bd : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  have htg_bd : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
    intro _; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd, hw.trail_lits_lt, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' _ _ hcl' hps _ _ _ hwt _ hm' => ?_⟩
  have hmin : cl' = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
  subst hmin
  exact hQ vals' lvl' rsns' trl' tp' te' prop' unass' sc' m'
    hlen' (hwt F0 F_cur hw hle) hps.1.1 hps.1.2 hps.2.2.1 hm'

private theorem dwWatchPush_adapter {Γ : Env}
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  refine hWPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT hF hm' => ?_⟩
  exact hQ ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT (fun hf => (hF hf).1) hm'

theorem full_reduce_bridge_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, FullDenseWatchSpecs.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, FullDenseWatchSpecs.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullReduceSpec a m Q X → Func.wp Γ full_reduce_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hspW, hm, hQ⟩
  rcases hspW with ⟨hlen, hw, hlm, hnd, hext, hdm⟩
  refine full_reduce_wp Γ (dwIsqrt_adapter hIsqrt) hIlog10 hArenaNext
    (dwRecomputeTiers_adapter hRecomp) (dwMarkReasons_adapter hMarkRsn)
    hSortReds (dwBacktrack_adapter hBacktrack) hProp hSweep _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm,
      fun r s' m' hsp' hw' hr hu hoom hcl hfl hcv htmp htpl _ _ _ _ _ _ hws2 hpos hm' => ?_⟩
  exact hQ r s' m'
    ⟨hsp'.1.lengths, hw', hsp'.2.1, hsp'.2.2.1, hsp'.2.2.2.1, hsp'.2.2.2.2⟩
    hr hcl hfl hcv htmp htpl hws2 hu hoom (fun _ => hpos) hm'

theorem full_enter_dense_bridge_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, FullDenseWatchSpecs.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, FullDenseWatchSpecs.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  rcases hsp.exists_witness with ⟨F_cur, hlen, hw, hlm, hnd, hext, _⟩
  exact full_enter_dense_wp Γ (dwBacktrack_adapter hBacktrack) hSweepBins
    (dwWatchPush_adapter hWatchPush) hSweep hArenaNext _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm,
      fun ok s' m' _ _ _ _ _ hcl0 hfl _ _ _ _ _ hd hf hm' =>
        hQ ok s' m' hcl0 hfl hd hf hm'⟩

theorem full_rebuild_watches_bridge_wp (Γ : Env)
    (hSweep : ∀ a m Q X, FullDenseWatchSpecs.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Func.wp Γ full_rebuild_watches_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdn, hm, hQ⟩
  rcases hdn with ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hext, hcl0, _⟩
  exact full_rebuild_watches_wp Γ hSweep hProp _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hcl0, hm,
      fun r s' m' hsp' _ hcl0' hr hu hfl _ _ _ _ _ hm' =>
        hQ r s' m' hsp' hcl0' hfl hr hu hm'⟩

end Part6

end LeanQbe.T.Examples.Kissat.Full
