/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Src.Sweep
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpCands
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpCone
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpDriver
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpDriver0
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpDriver1
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpEls0
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpEls1
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpPart0
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpPart1
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpSim

/-!
# Canonical Segment Certificate for `Kissat.Src.Sweep` (`Kissat.Proof.Sweep.Cert`)

Proves `cert : SegCert Spec.deps Src.Sweep.fns Spec.specs` (`20` C0 functions)
against `Kissat.Src.Sweep.fns` on flat `CanonicalEnv`.
Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas/sections; `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec

/-- Canonical segment certificate for `LeanQbe.T.Examples.Kissat.Src.Sweep` (`20` fns). -/
theorem cert : SegCert Spec.deps Src.Sweep.fns Spec.specs := by
  intro Γ hdeps hrows
  have hKitten : Γ.Sat Kitten.Spec.specs := hdeps.left.left.left.left
  have hClause : Γ.Sat Clause.Spec.specs := hdeps.left.left.left.right
  have hCong : Γ.Sat Congruence.Spec.specs := hdeps.left.left.right
  have hWatch : Γ.Sat Watch.Spec.specs := hdeps.left.right
  have hDense : Γ.Sat Dense.Spec.specs := hdeps.right
  -- Upstream capabilities
  have hMaxV := Kitten.Spec.has_full_m6_max_v hKitten
  have hInit := Kitten.Spec.has_full_k6_init hKitten
  have hAddClHw := Kitten.Spec.has_full_k6_add_clause_hw hKitten
  have hK6Solve := Kitten.Spec.has_full_k6_solve hKitten
  have hK6Flip := Kitten.Spec.has_full_k6_flip hKitten
  have hAddLive := Kitten.Spec.has_full_k512_add_live_m6 hKitten
  have hAddUnit := Clause.Spec.has_full_add_unit hClause
  have hAddBin := Clause.Spec.has_full_add_bin hClause
  have hFind := Congruence.Spec.has_full_cong_find hCong
  have hWatchPush := Watch.Spec.has_full_watch_push hWatch
  have hOccCnt := Dense.Spec.has_full_dense_occ_cnt_fid hDense
  have hDenseProp := Dense.Spec.has_full_m6_dense_prop hDense
  -- Intra-segment capabilities
  have hCone := has_full_m6_sweep_cone hrows
  have hRefineSig := has_full_m6_sweep_refine_sig hrows
  have hRand := has_full_m6_sweep_rand_phases hrows
  have hSwpSolve := has_full_m6_sweep_solve hrows
  have hFlipR := has_full_m6_sweep_flip_round hrows
  have hSim := has_full_m6_sweep_sim hrows
  have hRearm := has_full_m6_sweep_rearm hrows
  have hBuildPht := has_full_m6_sweep_build_pht hrows
  have hExtractPht := has_full_m6_extract_pht hrows
  have hRefinePart := has_full_m6_refine_partition hrows
  have hUnits := has_full_m6_sweep_units hrows
  have hClasses := has_full_m6_sweep_classes hrows
  have hElsAr := has_full_m6_els_ar hrows
  have hElsLit := has_full_m6_els_lit hrows
  have hDenseEls := has_full_m6_dense_els hrows
  have hSweepVar := has_full_m6_sweep_var hrows
  have hCandSift := has_full_m6_cand_sift hrows
  have hCollectCands := has_full_m6_collect_cands hrows
  have hSweepVars := has_full_m6_sweep_vars hrows
  exact
    ⟨ SpecEntry.Impl.of (full_m6_sweep_cone_wp Γ hMaxV hInit hAddClHw)
    , SpecEntry.Impl.of (full_m6_sweep_refine_sig_wp Γ hMaxV)
    , SpecEntry.Impl.of (full_m6_sweep_rand_phases_wp Γ hMaxV)
    , SpecEntry.Impl.of (full_m6_sweep_solve_wp Γ hRand hK6Solve)
    , SpecEntry.Impl.of (full_m6_sweep_flip_round_wp Γ hMaxV hK6Flip)
    , SpecEntry.Impl.of (full_m6_sweep_sim_wp Γ hMaxV hSwpSolve hRefineSig hFlipR)
    , SpecEntry.Impl.of (full_m6_sweep_rearm_wp Γ)
    , SpecEntry.Impl.of (full_m6_sweep_build_pht_wp Γ hMaxV)
    , SpecEntry.Impl.of (full_m6_extract_pht_wp Γ hMaxV)
    , SpecEntry.Impl.of (full_m6_refine_partition_wp Γ hMaxV)
    , SpecEntry.Impl.of
        (full_m6_sweep_units_wp Γ hMaxV hK6Flip hRefineSig hSwpSolve hAddUnit hAddLive hRearm)
    , SpecEntry.Impl.of
        (full_m6_sweep_classes_wp Γ hMaxV hBuildPht hExtractPht hK6Flip hRefineSig hRefinePart
          hSwpSolve hAddLive hRearm)
    , SpecEntry.Impl.of (full_m6_els_ar_wp Γ hFind hWatchPush hAddUnit hAddBin)
    , SpecEntry.Impl.of (full_m6_els_lit_wp Γ hAddUnit hAddBin hElsAr)
    , SpecEntry.Impl.of (full_m6_dense_els_wp Γ hFind hAddUnit hElsLit hAddBin hDenseProp)
    , SpecEntry.Impl.of (full_m6_sweep_var_wp Γ hMaxV hFind hCone hSim hUnits hClasses hDenseEls)
    , SpecEntry.Impl.of (full_m6_cand_sift_wp Γ)
    , SpecEntry.Impl.of (full_m6_collect_cands_wp Γ hOccCnt hCandSift)
    , SpecEntry.Impl.of
        (full_m6_sweep_vars_wp Γ hMaxV hDenseProp hOccCnt hCollectCands hSweepVar hFind)
    , SpecEntry.Impl.of (full_sweep_dense_m6_wp Γ hMaxV hSweepVars)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
