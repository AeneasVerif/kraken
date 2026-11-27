module

public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
meta import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
import LeanQbe.T.Logic.MemLemmas

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullFastBveBudgets` (M2)

1. Executable `#guard` checks on `fastBveBudgets_fns` (`7` upgraded functions), names & signatures,
   `fastBveBudgetsExterns` (`21` externs), `fastBveBudgetsModule.checkAcyclic`, and the `28`-row
   `fastBveBudgetsSpecTable`.
2. Short root-namespace audit theorems + single-line `#print axioms` (every
   `depends on axioms: [...]` output on one complete line) on all exported `Func.Wf`, acyclicity,
   gate soundness, UNSAT-only `Func.wp`, `SpecEntry.Impl`, `ModuleOk`, and concrete `Mem 64`
   UNSAT non-vacuity theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatFastBveBudgetsTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets

/-! ## 1. Executable `#guard` sanity checks -/

#guard fastBveBudgets_fns.length == 7
#guard fastBveBudgetsExterns.length == 21
#guard fastBveBudgetsModule.checkAcyclic == true
#guard fastBveBudgetsSpecTable.length == 28
#guard fastBveBudgets_fns.map Fn.name ==
  [ "full_init_hdr", "full_probe_run", "full_transitive", "full_vivify",
    "full_tarjan_scc", "full_forward_sub", "full_bve_var" ]
#guard (fastBveBudgets_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_init_hdr", 4, 0), ("full_probe_run", 2, 1), ("full_transitive", 2, 1),
    ("full_vivify", 3, 1), ("full_tarjan_scc", 1, 1), ("full_forward_sub", 2, 1),
    ("full_bve_var", 2, 1) ]
#guard (fastBveBudgetsSpecTable.all fun e => e.noExit) == true

end LeanQbeTest.T.KissatFastBveBudgetsTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets

theorem fbb_fns_wf : ∀ f ∈ fastBveBudgets_fns, f.Wf := fastBveBudgets_fns_wf

theorem fbb_acyclic : fastBveBudgetsModule.checkAcyclic = true := fastBveBudgets_acyclic

theorem fbb_gate_iff {v : Nat} {Rest U P N : List (List Nat)} {pg ng : Nat → Bool}
    (h1 : ∀ cl ∈ Rest, ∀ l ∈ cl, l / 2 ≠ v)
    (h2 : ∀ C ∈ P, ∀ l ∈ C, l / 2 ≠ v) (h3 : ∀ D ∈ N, ∀ l ∈ D, l / 2 ≠ v)
    (h4 : ∀ cl ∈ U, (cnfOfClauses Rest).EntailsClause (cnfClause cl))
    (h5 : (cnfOfClauses (U ++
      ((List.range P.length).filterMap fun i => if pg i then some (P[i]?.getD []) else none) ++
      ((List.range N.length).filterMap fun j =>
        if ng j then some (N[j]?.getD []) else none))).Unsat) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    (cnfOfClauses (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))).Unsat ↔ (cnfOfClauses (Rest ++ Res)).Unsat :=
  bve_gate_pg_ng_unsat_iff h1 h2 h3 h4 h5

theorem fbb_gate_ext {F0 : CNF Nat} {cur_vars v : Nat} {Rest P N : List (List Nat)}
    {pg ng : Nat → Bool}
    (hExt : ExtUnsatSound F0 cur_vars (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    ExtUnsatSound F0 cur_vars (Rest ++ Res) :=
  bve_gate_pg_ng_extUnsatSound hExt

theorem fbb_init_wp (Γ : Env) :
    ∀ a m Q X, fullFastInitHdrSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_init_hdr_body a m Q X :=
  fast_init_hdr_wp Γ

theorem fbb_init_canon (Γ : Env) :
    ∀ a m Q X, Full.fullInitHdrSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_init_hdr_body a m Q X :=
  fast_init_hdr_canon_wp Γ

theorem fbb_probe_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAp : ∀ a m Q X, fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullProbeRunFastSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_probe_run_body a m Q X :=
  fast_probe_run_wp Γ hBt hAp

theorem fbb_trans_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hLit : ∀ a m Q X, fullTransLitSpec a m Q X → Γ "full_trans_lit" [i64, i32] [.bool] a m Q X)
    (hPr : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hDf : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_transitive_body a m Q X :=
  fast_transitive_wp Γ hBt hLit hPr hDf

theorem fbb_viv_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hNx : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hVc : ∀ a m Q X, fullVivClauseSpec a m Q X → Γ "full_viv_clause" [i64, i32] [i64] a m Q X)
    (hPr : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_vivify_body a m Q X :=
  fast_vivify_wp Γ hBt hNx hVc hPr

theorem fbb_scc_wp (Γ : Env)
    (hPop : ∀ a m Q X, Full.fullTarjanPopSccSpec a m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTarjanSccFastSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_tarjan_scc_body a m Q X :=
  fast_tarjan_scc_wp Γ hPop

theorem fbb_scc_canon (Γ : Env)
    (hPop : ∀ a m Q X, Full.fullTarjanPopSccSpec a m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullTarjanSccSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_tarjan_scc_body a m Q X :=
  fast_tarjan_scc_canon_wp Γ hPop

theorem fbb_fwd_wp (Γ : Env)
    (hDd : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hNx : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hCk : ∀ a m Q X, fullFwdCheckClSpec a m Q X →
      Γ "full_fwd_check_cl" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_forward_sub_body a m Q X :=
  fast_forward_sub_wp Γ hDd hNx hCk

theorem fbb_bve_wp (Γ : Env)
    (hCo : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hEn : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWk : ∀ a m Q X, fullBveWeakenSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSi : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGt : ∀ a m Q X, fullBveGatesSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X)
    (hRp : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCr : ∀ a m Q X, fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hTb : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hE2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDb : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hEc : ∀ a m Q X, fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullBveVarSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_bve_var_body a m Q X :=
  fast_bve_var_wp Γ hCo hEn hWk hSi hGt hRp hCr hTb hE2 hDb hEc

theorem fbb_bve_def_wp (Γ : Env)
    (hCo : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hEn : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWk : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSi : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGt : ∀ a m Q X, fullBveGatesDefFastSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X)
    (hRp : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCr : ∀ a m Q X, fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hTb : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hE2 : ∀ a m Q X, fullExtendPush2TmkSpec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDb : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hEc : ∀ a m Q X, fullExtendPushClTmkSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Func.wp Γ FullFastBveBudgets.full_bve_var_body a m Q X :=
  fast_bve_var_def_wp Γ hCo hEn hWk hSi hGt hRp hCr hTb hE2 hDb hEc

theorem fbb_env_noExit :
    ∀ f as bs xs m Q X X',
      fastBveBudgetsEnv f as bs xs m Q X → fastBveBudgetsEnv f as bs xs m Q X' :=
  fastBveBudgetsEnv_noExit

theorem fbb_moduleOk : ModuleOk fastBveBudgetsEnv fastBveBudgetsModule :=
  fastBveBudgets_moduleOk

theorem fbb_nv_init :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_init_hdr_body
      (nvOneLitCfg.hdr, 1#64, 1#64, 100#64, ()) nvInitHdrMem
      (fun () m' => ∃ s',
        s'.scratch.probe_limit = 2000#64 ∧ s'.scratch.elim_limit = 5000#64 ∧
        array64 (nvOneLitCfg.hdr + 32) (Full.hdrTailWords nvOneLitCfg s') m')
      (fun _ _ _ _ => False) :=
  nv_fast_init_hdr

theorem fbb_nv_probe :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_probe_run_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_probe_run

theorem fbb_nv_trans :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_transitive_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_transitive

theorem fbb_nv_viv :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_vivify_body
      (nvOneLitCfg.hdr, 0#64, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_vivify

theorem fbb_nv_scc :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_tarjan_scc_body
      (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧ TmkZero s' ∧ nvOneLitF0.Unsat ∧
        (∀ l < 2 * nvOneLitState.core.cur_vars,
          s'.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
          s'.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_tarjan_scc

theorem fbb_nv_fwd :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_forward_sub_body
      (nvOneLitCfg.hdr, 10#64, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_forward_sub

theorem fbb_nv_fwd20 :
    let Γ20 : Env := fun f as bs xs m Q X =>
      if f = "full_fwd_dedup_bins" then
        ∃ (_ : as = [i64]) (h2 : bs = [.bool]), Q (h2 ▸ (false, ())) m
      else fastBveBudgetsEnv f as bs xs m Q X
    Func.wp Γ20 FullFastBveBudgets.full_forward_sub_body
      (nvOneLitCfg.hdr, 10#64, ()) nvDenseUnsatMem
      (fun (r, ()) m' => r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg nvDenseUnsatState m')
      (fun _ _ _ _ => False) :=
  nv_fast_forward_sub_unsat20

theorem fbb_nv_bve :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_bve_var

theorem fbb_nv_bve_def :
    let Γdef : Env := fun f as bs xs m Q X =>
      if f = "full_bve_gates" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = []),
          fullBveGatesDefFastSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_weaken" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = [.bool]),
          fullBveWeakenTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_commit_res" then
        ∃ (h1 : as = [i64, i64, i64]) (h2 : bs = [i64]),
          fullBveCommitResTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push2" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPush2TmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push_cl" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPushClTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else fastBveBudgetsEnv f as bs xs m Q X
    Func.wp Γdef FullFastBveBudgets.full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_bve_var_def

#print axioms fbb_fns_wf
#print axioms fbb_acyclic
#print axioms fbb_gate_iff
#print axioms fbb_gate_ext
#print axioms fbb_init_wp
#print axioms fbb_init_canon
#print axioms fbb_probe_wp
#print axioms fbb_trans_wp
#print axioms fbb_viv_wp
#print axioms fbb_scc_wp
#print axioms fbb_scc_canon
#print axioms fbb_fwd_wp
#print axioms fbb_bve_wp
#print axioms fbb_bve_def_wp
#print axioms fbb_env_noExit
#print axioms fbb_moduleOk
#print axioms fbb_nv_init
#print axioms fbb_nv_probe
#print axioms fbb_nv_trans
#print axioms fbb_nv_viv
#print axioms fbb_nv_scc
#print axioms fbb_nv_fwd
#print axioms fbb_nv_fwd20
#print axioms fbb_nv_bve
#print axioms fbb_nv_bve_def

end AxiomAudit
