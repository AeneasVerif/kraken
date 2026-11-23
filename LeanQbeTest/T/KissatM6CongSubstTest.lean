module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstLemmas
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6CongSubst
meta import LeanQbe.T.Examples.Kissat.FullM6CongSubstLemmas
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Splice Parity, Backend Guards, and Axiom Audit for Kissat M6 Congruence &
Substitute (`FullM6CongSubst`, UNSAT-only)

1. Executable `#guard` checks on `m6CongSubstModule` (`23` fns + `16` externs, `0` exits),
   `checkAcyclic = true`, `m6CongSubstSpecTable` (`39` rows), exact signature parity and closed
   `242`-fn acyclicity when splicing all `23` M6 functions (`spliceM6CongSubst FullM4.m4Fns`) into
   `FullM4.m4Fns`, `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and
   `x64AVX2`.
2. Audit-ready restated headline theorems for `m6CongSubst_fns_wf`, `m6CongSubst_acyclic`, key
   parametric `Func.wp` proofs (`full_tarjan_scc`, `full_subst_rewrite_{bins,ar}`,
   `full_substitute`, `full_cong_extract_binaries`, `full_cong_find_units_equivs`,
   `full_cong_eval_gate`, `full_cong_work_step`, `full_cong_worklist`,
   `full_cong_fwd_subsume`, `full_congruence_dense`), closed `39`-row `m6CongSubst_moduleOk`, and
   concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on `nvOneLitMem` and
   `nvBvaDenseMem`.
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

namespace M6CsAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3CongBva
  (m3CongUnitFoldSpec m3CongEquivFoldSpec m3CongruenceDenseSpec)
open LeanQbe.T.Examples.Kissat.FullBvaHeap (nvBvaDenseMem)
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks, `FullM4` Splice Parity & Backend Compilation Guards -/

private def m6SplicedFns : List Fn := spliceM6CongSubst FullM4.m4Fns

private def m6SplicedM4Module : LeanQbe.T.Module :=
  { fns := m6SplicedFns, externs := [], exits := [] }

#guard m6CongSubstModule.checkAcyclic == true
#guard m6CongSubstModule.exits.isEmpty
#guard m6CongSubst_fns.length == 23
#guard m6CongSubstExterns.length == 16
#guard m6CongSubstSpecTable.length == 39
#guard m6CongSubst_fns.all (fun h =>
  match FullM4.m4Fns.find? (fun f => f.name == h.name) with
  | some f => f.as == h.as && f.rs == h.rs
  | none => true)
#guard m6CongSubst_fns.all (fun h => m6SplicedFns.any (fun f => f.name == h.name))
#guard (m6SplicedFns.map Fn.name).Nodup
#guard m6SplicedFns.length == 242
#guard m6SplicedM4Module.checkAcyclic == true
#guard (ppTModule m6CongSubstModule).isOk
#guard (PrintQbe.module m6CongSubstModule).isOk
#guard (ppModule (m6CongSubst_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6CongSubst_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6CongSubst_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m6CongSubst_fns` (`23` functions) is well-formed. -/
public theorem m6cs_wf : ∀ f ∈ m6CongSubst_fns, f.Wf :=
  m6CongSubst_fns_wf

/-- Standalone M6 congruence/substitute module `m6CongSubstModule` passes `checkAcyclic = true`. -/
public theorem m6cs_acyc : m6CongSubstModule.checkAcyclic = true :=
  m6CongSubst_acyclic

/-- `full_tarjan_scc` (single-pass `wvec` Tarjan SCC) satisfies canonical
`Full.fullTarjanSccSpec`. -/
public theorem m6cs_tarjan_scc_wp (Γ : Env)
    (hPop : ∀ a m Q X, fullTarjanPopSccSpec a m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTarjanSccSpec a m Q X →
      Func.wp Γ FullM6CongSubst.full_tarjan_scc_body a m Q X :=
  full_tarjan_scc_wp Γ hPop

/-- `full_subst_rewrite_bins` satisfies canonical `Full.fullSubstRewriteBinsSpec`. -/
public theorem m6cs_subst_bins_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Func.wp Γ FullM6CongSubst.full_subst_rewrite_bins_body a m Q X :=
  full_subst_rewrite_bins_wp Γ hAddUnit hAddBin

/-- `full_subst_rewrite_ar` satisfies canonical `Full.fullSubstRewriteArSpec`. -/
public theorem m6cs_subst_ar_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Func.wp Γ FullM6CongSubst.full_subst_rewrite_ar_body a m Q X :=
  full_subst_rewrite_ar_wp Γ hArenaNext hAddUnit hAddBin

/-- `full_substitute` (2-round fixpoint substitution) satisfies canonical
`Full.fullSubstituteSpec`. -/
public theorem m6cs_substitute_wp (Γ : Env)
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
    ∀ a m Q X, fullSubstituteSpec a m Q X →
      Func.wp Γ FullM6CongSubst.full_substitute_body a m Q X :=
  full_substitute_wp Γ hBacktrack hTarjan hElimVars hRewriteBins hRewriteAr hArenaSweep hProp

/-- `full_cong_extract_binaries` (`negbincount`-filtered ternary binary resolution) satisfies
`m6CongExtractBinariesSpec`. -/
public theorem m6cs_cong_extract_bins_wp (Γ : Env)
    (hNext : ∀ a m Q X, FullCongSpecs.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hHasBin : ∀ a m Q X, FullCongSpecs.fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, FullCongSpecs.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hCountBins : ∀ a m Q X, m6CongCountBinsSpec a m Q X →
      Γ "full_cong_count_bins" [i64] [] a m Q X)
    (hEbMatch : ∀ a m Q X, m6CongEbMatchSpec a m Q X →
      Γ "full_cong_eb_match" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Func.wp Γ full_cong_extract_binaries_body a m Q X :=
  full_cong_extract_binaries_wp Γ hNext hHasBin hAddBin hCountBins hEbMatch

/-- `full_cong_find_units_equivs` (dense binary unit & equivalence sweep) satisfies
`m6CongFindUnitsEquivsSpec`. -/
public theorem m6cs_cong_find_ue_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hEquivFold : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Func.wp Γ full_cong_find_units_equivs_body a m Q X :=
  full_cong_find_units_equivs_wp Γ hAddUnit hEquivFold

/-- `full_cong_eval_gate` (`arity <= 31` AND, `arity 2..4` XOR, normalized ITE) satisfies
`m6CongEvalGateSpec`. -/
public theorem m6cs_cong_eval_gate_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X → Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnit : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquiv : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hAndMatch : ∀ a m Q X, m6CongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X)
    (hXorMatch : ∀ a m Q X, m6CongXorMatchSpec a m Q X →
      Γ "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X)
    (hEnq : ∀ a m Q X, m6CongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, m6CongEvalGateSpec a m Q X → Func.wp Γ full_cong_eval_gate_body a m Q X :=
  full_cong_eval_gate_wp Γ hFind hSort hUnit hEquiv hAndMatch hXorMatch hEnq

/-- `full_cong_worklist` (FIFO occurrence-list worklist in `scratch_buf`) satisfies
`m6CongWorklistSpec`. -/
public theorem m6cs_cong_worklist_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hEval : ∀ a m Q X, m6CongEvalGateSpec a m Q X →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, m6CongWorklistSpec a m Q X → Func.wp Γ full_cong_worklist_body a m Q X :=
  full_cong_worklist_wp Γ hFind hEval

/-- `full_cong_fwd_subsume` (dense forward subsumption modulo `repr`) satisfies
`m6CongFwdSubsumeSpec`. -/
public theorem m6cs_cong_fwd_subsume_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X → Func.wp Γ full_cong_fwd_subsume_body a m Q X :=
  full_cong_fwd_subsume_wp Γ hNext hFind hAddUnit

/-- `full_congruence_dense` satisfies canonical `FullM3CongBva.m3CongruenceDenseSpec`. -/
public theorem m6cs_congruence_dense_wp (Γ : Env)
    (hExtBin : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m6CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m6CongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X → Func.wp Γ full_congruence_dense_body a m Q X :=
  full_congruence_dense_wp Γ hExtBin hFindUE hExtract hWork hFwdSub

/-- Closed `39`-row `ModuleOk` certifying `m6CongSubstModule` under `m6CongSubstEnv`. -/
public theorem m6cs_mod_ok : ModuleOk m6CongSubstEnv m6CongSubstModule :=
  m6CongSubst_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_tarjan_scc`. -/
public theorem m6cs_nv_tarjan :
    Func.wp m6CongSubstEnv FullM6CongSubst.full_tarjan_scc_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_tarjan_scc

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_substitute`. -/
public theorem m6cs_nv_subst :
    Func.wp m6CongSubstEnv FullM6CongSubst.full_substitute_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_substitute

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_congruence_dense`. -/
public theorem m6cs_nv_cong :
    Func.wp m6CongSubstEnv full_congruence_dense_body (nvOneLitCfg.hdr, 1000#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_congruence_dense

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m6cs_wf
#print axioms m6cs_acyc
#print axioms m6cs_tarjan_scc_wp
#print axioms m6cs_subst_bins_wp
#print axioms m6cs_subst_ar_wp
#print axioms m6cs_substitute_wp
#print axioms m6cs_cong_extract_bins_wp
#print axioms m6cs_cong_find_ue_wp
#print axioms m6cs_cong_eval_gate_wp
#print axioms m6cs_cong_worklist_wp
#print axioms m6cs_cong_fwd_subsume_wp
#print axioms m6cs_congruence_dense_wp
#print axioms m6cs_mod_ok
#print axioms m6cs_nv_tarjan
#print axioms m6cs_nv_subst
#print axioms m6cs_nv_cong

end M6CsAudit