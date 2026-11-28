/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Analyze` (`5` C0 Functions)

Pure declarative specifications (`0` theorems, `0` tactics, `0` cross-subsystem `Spec` imports)
aligned 1:1 with `Src.Analyze.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Per-Function Specifications (`4` Distinct Specs for `5` C0 Functions) -/

/-- `full_ana_failed_lit_m6_hdr(h)`: chronological failed-literal conflict analysis over a cut
trail, preserving W2b `M6HdrExt` words. -/
@[expose] def anaFailedLitSpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (W := CNF Nat × List (List Nat) × Nat)
    { extFrame := .w2aOnly
      pre := fun c _ s () (F0, F_cur, cut) =>
        FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s
      post := fun c _ s () (F0, F_cur, _) (r, ()) _ s' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel = s.core.fuel ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) ∧
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') ∧
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) }

/-- `full_restore_bump_ana_mode_fid(h, allow_reasons)`: bumps analyzed variables and clears
`min_clr_len` outside probing, modifying only `mrk`/`min_clr_len`/`repr` in `core`. -/
@[expose] def restoreBumpAnaModeSpec : Spec [i64, .bool] [] :=
  M6HdrContract.toSpec (W := Unit)
    { extFrame := .w2aOnly
      pre := fun c _ s _ () => FullMrkZero c s
      post := fun c _ s _ () () _ s' =>
        s'.core = { s.core with
          mrk := s'.core.mrk, min_clr_len := s'.core.min_clr_len, repr := s'.core.repr } ∧
        FullMrkZero c s' ∧
        (s.core.probing = 0#64 → s'.core.min_clr_len = 0) ∧
        (s.core.probing ≠ 0#64 → s'.core.min_clr_len = s.core.min_clr_len) ∧
        ScratchModifies.extPres s s' ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 }

/-- `full_analyze_reasons_fid(h)`: optional reason-side variable bumping with delay control,
modifying only `mrk`/`min_clr_len` in `core`. -/
@[expose] def analyzeReasonsSpec : Spec [i64] [] :=
  M6HdrContract.toSpec (W := Unit)
    { extFrame := .w2aOnly
      pre := fun c _ s () () => FullMrkZero c s
      post := fun c _ s () () () _ s' =>
        s'.core = { s.core with mrk := s'.core.mrk, min_clr_len := s'.core.min_clr_len } ∧
        FullMrkZero c s' ∧
        (s.core.probing = 0#64 → s'.core.min_clr_len ≤ s.core.cur_vars ∧
          ∀ k < s'.core.min_clr_len, (s'.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (s.core.probing ≠ 0#64 → s'.core.min_clr_len = s.core.min_clr_len) ∧
        ScratchModifies.extPres s s' ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 }

/-- Shared canonical contract for `full_analyze_core_m6(h)` and `full_analyze_m6_hdr(h)`:
1-UIP conflict analysis with tier-limit and decision-rate updates (`0`: OTFS/OOM, `1`: learned &
backtracked to lower level, `20`: `F0.Unsat`). -/
@[expose] def analyzeSpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (W := CNF Nat × List (List Nat))
    { extFrame := .any
      pre := fun c _ s () (F0, F_cur) =>
        FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s
      post := fun c _ s () (F0, F_cur) (r, ()) _ s' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) ∧
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') ∧
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) }

/-- Canonical specification table aligned 1:1 with `Src.Analyze.fns` (`5` entries). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_ana_failed_lit_m6_hdr",     [i64],        [i64], anaFailedLitSpec,       true⟩
  , ⟨"full_restore_bump_ana_mode_fid", [i64, .bool], [],    restoreBumpAnaModeSpec, true⟩
  , ⟨"full_analyze_reasons_fid",       [i64],        [],    analyzeReasonsSpec,     true⟩
  , ⟨"full_analyze_core_m6",           [i64],        [i64], analyzeSpec,            true⟩
  , ⟨"full_analyze_m6_hdr",            [i64],        [i64], analyzeSpec,            true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
