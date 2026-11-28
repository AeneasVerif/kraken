/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Congruence
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpCore
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpXor0
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpXor1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpBin0
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpBin1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpExtractFid
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpExtractFid1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpMatch
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpMatch1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEnqVar
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpWorklist1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpSubsume0
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpFwdSubsume
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpIte0a
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpIte0b
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpIte1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpDense

/-!
# Canonical Segment Certificate for `Kissat.Src.Congruence` (`Kissat.Proof.Congruence.Cert`)

Proves `cert : SegCert Spec.deps Src.Congruence.fns Spec.specs` (`32` C0 functions)
against `Kissat.Src.Congruence.fns` via `Spec.has_full_cong_*` and `SpecEntry.Impl.of`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Congruence`
    (`32` fns, `Spec.deps` = `Arena ++ Clause ++ Limits ++ Watch`). -/
theorem cert : SegCert Spec.deps Src.Congruence.fns Spec.specs := by
  intro Γ hdeps hrows
  have hArena : Γ.Sat Arena.Spec.specs := hdeps.left.left.left
  have hClause : Γ.Sat Clause.Spec.specs := hdeps.left.left.right
  have hLimits : Γ.Sat Limits.Spec.specs := hdeps.left.right
  have hWatch : Γ.Sat Watch.Spec.specs := hdeps.right
  have hNext := Arena.Spec.has_full_arena_next hArena
  have hAddBin := Clause.Spec.has_full_add_bin hClause
  have hAddUnit := Clause.Spec.has_full_add_unit hClause
  have hSort : Γ.Has "full_sort_u32" Proof.Spec.fullSortU32Spec :=
    Env.Sat.has hLimits (List.getElem_mem (l := Limits.Spec.specs) (n := 7) (by decide))
      Limits.Spec.fullSortU32Spec_xfree
  have hHasBin := Watch.Spec.has_full_has_bin hWatch
  have hHasTern := Watch.Spec.has_full_has_ternary hWatch
  have hFind := has_full_cong_find hrows
  have hMerge := has_full_cong_merge hrows
  have hMark := has_full_cong_mark_trail hrows
  have hUnit := has_full_cong_unit_fold hrows
  have hEquiv := has_full_cong_equiv_fold hrows
  have hEmitXor := has_full_cong_emit_xor hrows
  have hHasClK := has_full_cong_has_clause_k hrows
  have hEmitXor4 := has_full_cong_emit_xor4 hrows
  have hExtractXorK := has_full_cong_extract_xor_k hrows
  have hTryXorIte := has_full_cong_try_xor_ite hrows
  have hCountBins := has_full_cong_count_bins hrows
  have hEb := has_full_cong_eb_match hrows
  have hBin := has_full_cong_extract_binaries hrows
  have hUnits := has_full_cong_find_units_equivs hrows
  have hExtAnd := has_full_cong_extract_and_clause_fid hrows
  have hFid := has_full_cong_extract_from_fid hrows
  have hAndMatch := has_full_cong_and_match hrows
  have hXorMatch := has_full_cong_xor_match hrows
  have hEnq := has_full_cong_enq_var hrows
  have hEval := has_full_cong_eval_gate hrows
  have hWkl := has_full_cong_worklist hrows
  have hSiftPairs := has_full_cong_sift_pairs_fid hrows
  have hSortPairs := has_full_cong_sort_pairs_fid hrows
  have hFwd := has_full_cong_fwd_subsume hrows
  have hU64Sift := has_full_cong_u64_sift_m7 hrows
  have hU64Sort := has_full_cong_u64_sort_m7 hrows
  have hBs := has_full_cong_bsearch_u64_m7 hrows
  have hCopy := has_full_cong_copy_condbin_m7 hrows
  have hExtCe := has_full_cong_extract_condeq_m7 hrows
  have hMergeCe := has_full_cong_merge_condeq_m7 hrows
  have hIte := has_full_cong_extract_ite_all_m7 hrows
  exact
    ⟨ SpecEntry.Impl.of (full_cong_find_wp Γ)
    , SpecEntry.Impl.of (full_cong_merge_wp Γ hFind hAddBin)
    , SpecEntry.Impl.of (full_cong_mark_trail_wp Γ hFind)
    , SpecEntry.Impl.of (full_cong_unit_fold_wp Γ hAddUnit hMark)
    , SpecEntry.Impl.of (full_cong_equiv_fold_wp Γ hFind hMerge hAddUnit hMark)
    , SpecEntry.Impl.of (full_cong_emit_xor_wp Γ)
    , SpecEntry.Impl.of (full_cong_has_clause_k_wp Γ)
    , SpecEntry.Impl.of (full_cong_emit_xor4_wp Γ)
    , SpecEntry.Impl.of (full_cong_extract_xor_k_wp Γ hHasClK hEmitXor4 hSort)
    , SpecEntry.Impl.of (full_cong_try_xor_ite_wp Γ hHasTern hEmitXor)
    , SpecEntry.Impl.of (full_cong_count_bins_wp Γ)
    , SpecEntry.Impl.of (full_cong_eb_match_wp Γ hHasBin)
    , SpecEntry.Impl.of (full_cong_extract_binaries_wp Γ hCountBins hNext hEb hHasBin hAddBin)
    , SpecEntry.Impl.of (full_cong_find_units_equivs_wp Γ hAddUnit hEquiv)
    , SpecEntry.Impl.of (full_cong_extract_and_clause_fid_wp (Γ := Γ))
    , SpecEntry.Impl.of
        (full_cong_extract_from_fid_wp hNext hCountBins hExtAnd hTryXorIte hExtractXorK)
    , SpecEntry.Impl.of (full_cong_and_match_wp hFind)
    , SpecEntry.Impl.of (full_cong_xor_match_wp hFind hSort)
    , SpecEntry.Impl.of (full_cong_enq_var_wp Γ)
    , SpecEntry.Impl.of
        (full_cong_eval_gate_wp Γ hSort hFind hUnit hEquiv hAndMatch hXorMatch hEnq)
    , SpecEntry.Impl.of (full_cong_worklist_wp Γ hFind hEval)
    , SpecEntry.Impl.of (full_cong_sift_pairs_fid_wp Γ)
    , SpecEntry.Impl.of (full_cong_sort_pairs_fid_wp Γ hSiftPairs)
    , SpecEntry.Impl.of (full_cong_fwd_subsume_wp Γ hNext hAddUnit hFind hSortPairs)
    , SpecEntry.Impl.of (full_cong_u64_sift_m7_wp Γ)
    , SpecEntry.Impl.of (full_cong_u64_sort_m7_wp Γ hU64Sift)
    , SpecEntry.Impl.of (full_cong_bsearch_u64_m7_wp Γ)
    , SpecEntry.Impl.of (full_cong_copy_condbin_m7_wp Γ hU64Sort)
    , SpecEntry.Impl.of (full_cong_extract_condeq_m7_wp Γ hBs hU64Sort)
    , SpecEntry.Impl.of (full_cong_merge_condeq_m7_wp Γ)
    , SpecEntry.Impl.of (full_cong_extract_ite_all_m7_wp Γ hCopy hExtCe hMergeCe)
    , SpecEntry.Impl.of (full_congruence_dense_wp Γ hBin hUnits hIte hFid hWkl hFwd)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Congruence
end
