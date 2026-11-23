module

public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM6Hdr
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15
public import LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullM6MinShrink
public import LeanQbe.T.Examples.Kissat.FullM6WalkParse
public import LeanQbe.T.Examples.Kissat.FullM6WatchGc
public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullM6CongSubst
public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullM7Reorder
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
public import LeanQbe.T.Examples.Kissat.FullM6Orch
meta import LeanQbe.T.Examples.Kissat.FullM5
meta import LeanQbe.T.Examples.Kissat.FullM6Hdr
meta import LeanQbe.T.Examples.Kissat.FullM6BcpS15
meta import LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
meta import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
meta import LeanQbe.T.Examples.Kissat.FullM6MinShrink
meta import LeanQbe.T.Examples.Kissat.FullM6WalkParse
meta import LeanQbe.T.Examples.Kissat.FullM6WatchGc
meta import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
meta import LeanQbe.T.Examples.Kissat.FullM6CongSubst
meta import LeanQbe.T.Examples.Kissat.FullM6BveFwd
meta import LeanQbe.T.Examples.Kissat.FullM7Reorder
meta import LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
meta import LeanQbe.T.Examples.Kissat.FullM6Orch
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat `D-Full` Unified `M6.0` Solver (`FullM6`)

Splices all `382` `M6.0` functions in strict topological call order (`externs := []`,
`exits := []`), integrating all ready Wave-2/3 modules (`FullM6Hdr`, `FullM6BcpS15`,
`FullM6BvaNoHops`, `FullM6CompactFlush`, `FullM6MinShrink`, `FullM6WalkParse`, `FullM6WatchGc`,
`FullM6VivBackbone`, `FullM6CongSubst`, `FullM6BveFwd`), `FullM7Reorder`, `FullM6OrchAdapters`,
and `FullM6Orch`:

- Zero duplicates, zero backward calls, `m6Module.checkAcyclic = true`.
- Strict `FullMem` vs `FullM6HdrMem` boundary isolation (`0` cross-boundary calls from
  `FullMem`-only entrypoints `full_init_state`, `full_recompute_tiers`, `full_reduce`,
  `full_elim_dticks`, `full_analyze_rsn`, `full_analyze`, `full_min_shrink`,
  `full_deduce_1uip`, `full_eliminate_m6`, `full_extend`, `kissat_check_model`, `full_lucky`,
  `full_compact`).
- Verified against `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` / `isLegal` guards.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

/-! ## 1. Canonical Rename `Fn` Handles -/

def m6CanonicalReduceFn : Fn :=
  ⟨"full_reduce", [i64, .bool], [i64], FullM5Orch.full_reduce_m5_body⟩

def m6CanonicalOtfsBinFn : Fn :=
  ⟨"full_otfs_bin", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_bin_m5_body⟩

def m6CanonicalProbeAssumePairFn : Fn :=
  ⟨"full_probe_assume_pair", [i64, i32], [i64], FullM6VivBackbone.full_probe_assume_pair_m6_body⟩

def m6CanonicalElimDticksFn : Fn :=
  ⟨"full_elim_dticks", [i64, .bool], [i64], FullM5Orch.full_elim_dticks_m5_body⟩

/-! ## 2. Spliced `M6.0` Function List (`382` Functions) -/

/-- Part 1 (`0..111`, `112` fns): `Dimacs` through `full_reduce_m6`. -/
def m6FnsPart1 : List Fn :=
  FullM5.m5Fns.take 14 ++
  FullM6WatchGc.m6WatchGc_fns.take 3 ++
  [ FullM6Orch.m6oWstackDefragFn, FullM6Orch.m6oWatchPushFn ] ++
  (FullM5.m5Fns.drop 16).take 4 ++
  FullM6WalkParse.m6WalkParse_fns.take 1 ++
  [ FullM6Orch.m6oRescaleFn ] ++
  (FullM5.m5Fns.drop 21).take 8 ++
  [ FullM6OrchAdapters.m6aScaleDeltaFn ] ++
  (FullM5.m5Fns.drop 29).take 17 ++
  FullM6Hdr.m6Hdr_fns.take 24 ++
  (FullM5.m5Fns.drop 46).take 2 ++
  (FullM5.m5Fns.drop 49).take 3 ++
  FullM6BcpS15.m6BcpS15_fns ++
  [ FullM6OrchAdapters.m6aPropLitRawFn
  , FullM6OrchAdapters.m6aPropagateIgnoreFn
  , FullM6OrchAdapters.m6aPropagateFn ] ++
  (FullM6WalkParse.m6WalkParse_fns.drop 1).take 1 ++
  [ FullM6Orch.m6oParseBodyFn ] ++
  (FullM5.m5Fns.drop 57).take 1 ++
  (FullM6WatchGc.m6WatchGc_fns.drop 3).take 2 ++
  (FullM6WatchGc.m6WatchGc_fns.drop 6).take 2 ++
  [ FullM6Orch.m6oLitRankFn ] ++
  (FullM6CompactFlush.m6CompactFlush_fns.drop 1).take 1 ++
  [ FullM6Orch.m6oSweepBinsFn ] ++
  (FullM5.m5Fns.drop 64).take 1 ++
  [ FullM6Orch.m6oRewatchArenaFn ] ++
  (FullM6WatchGc.m6WatchGc_fns.drop 8).take 5 ++
  [ FullM6Orch.m6oArenaSweepFn, FullM6Orch.m6oMarkReasonsFn ] ++
  FullM6CompactFlush.m6CompactFlush_fns.take 1 ++
  (FullM5.m5Fns.drop 59).take 3 ++
  [ m6CanonicalReduceFn, FullM6Orch.m6oReduceM6Fn ]

/-- Part 2 (`112..255`, `144` fns): `full_analyze_lit` through `full_congruence_dense`. -/
def m6FnsPart2 : List Fn :=
  (FullM5.m5Fns.drop 69).take 2 ++
  [ FullM6Orch.m6oAnalyzeRsnM6HdrFn ] ++
  (FullM5.m5Fns.drop 71).take 1 ++
  (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2 ++
  [ FullM6OrchAdapters.m6aBumpAnalyzedM6HdrFn
  , FullM6OrchAdapters.m6aRestoreBumpAnaM6HdrFn
  , FullM6OrchAdapters.m6aAnaFailedLitM6HdrFn ] ++
  (FullM5.m5Fns.drop 74).take 1 ++
  [ m6CanonicalOtfsBinFn ] ++
  (FullM5.m5Fns.drop 76).take 2 ++
  (FullM5.m5Fns.drop 79).take 3 ++
  (FullM6MinShrink.m6MinShrink_fns.drop 8).take 7 ++
  [ FullM6Orch.m6oMinShrinkFn
  , FullM6Orch.m6oDeduce1uipFn
  , FullM6Orch.m6oDeduce1uipM6HdrFn ] ++
  (FullM5.m5Fns.drop 85).take 2 ++
  (FullM5.m5Fns.drop 88).take 2 ++
  (FullM5.m5Fns.drop 72).take 2 ++
  (FullM5.m5Fns.drop 90).take 1 ++
  [ FullM6Orch.m6oAnalyzeCoreM6Fn, FullM6OrchAdapters.m6aAnalyzeM6HdrFn ] ++
  (FullM5.m5Fns.drop 91).take 1 ++
  (FullM6Hdr.m6Hdr_fns.drop 24).take 1 ++
  (FullM5.m5Fns.drop 93).take 1 ++
  (FullM6WalkParse.m6WalkParse_fns.drop 2).take 9 ++
  [ FullM6Orch.m6oWalkFn
  , FullM6OrchAdapters.m6aRephaseM6HdrFn
  , FullM6Orch.m6oEmaSwapM6Fn
  , FullM6Orch.m6oSwitchModeM6Fn ] ++
  (FullM5.m5Fns.drop 100).take 2 ++
  [ FullM6CompactFlush.m6cfExtendPush2Fn, FullM6CompactFlush.m6cfExtendPushClFn ] ++
  (FullM5.m5Fns.drop 104).take 3 ++
  FullM6VivBackbone.m6VivBackbone_fns.take 1 ++
  [ FullM6OrchAdapters.m6aAddBinFn ] ++
  (FullM5.m5Fns.drop 108).take 10 ++
  [ m6CanonicalProbeAssumePairFn ] ++
  (FullM5.m5Fns.drop 119).take 1 ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 26 ++
  [ FullM6OrchAdapters.m6aVivifyTierM6HdrFn, FullM6OrchAdapters.m6aVivifyM6HdrFn ] ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 29).take 11 ++
  (FullM5.m5Fns.drop 139).take 1 ++
  FullM6CongSubst.m6CongSubst_fns.take 1 ++
  (FullM5.m5Fns.drop 141).take 1 ++
  (FullM6CongSubst.m6CongSubst_fns.drop 1).take 3 ++
  [ FullM6CompactFlush.m6cfEnterDenseFn ] ++
  (FullM5.m5Fns.drop 146).take 1 ++
  (FullM5.m5Fns.drop 162).take 1 ++
  (FullM6CongSubst.m6CongSubst_fns.drop 4).take 1 ++
  (FullM5.m5Fns.drop 170).take 3 ++
  (FullM5.m5Fns.drop 164).take 2 ++
  FullM6CongSubst.m6CongSubst_fns.drop 5

/-- Part 3 (`256..381`, `126` fns): `FullM4Sweep` through `kissat_solve_bytes`. -/
def m6FnsPart3 : List Fn :=
  (FullM5.m5Fns.drop 178).take 23 ++
  [ FullM6Orch.m6oSweepDenseM6Fn ] ++
  (FullM5.m5Fns.drop 201).take 1 ++
  FullM6BveFwd.m6BveFwd_fns.take 10 ++
  (FullM5.m5Fns.drop 147).take 15 ++
  (FullM5.m5Fns.drop 206).take 6 ++
  (FullM6BveFwd.m6BveFwd_fns.drop 10).take 5 ++
  (FullM5.m5Fns.drop 204).take 1 ++
  (FullM5.m5Fns.drop 213).take 5 ++
  (FullM6BveFwd.m6BveFwd_fns.drop 15).take 1 ++
  [ FullM6OrchAdapters.m6aBveVarFn, FullM6OrchAdapters.m6aForwardSubFn ] ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 1).take 1 ++
  [ FullM6OrchAdapters.m6aInitFreshVarFn ] ++
  (FullM5.m5Fns.drop 220).take 5 ++
  FullM6BvaNoHops.m6BvaNoHopsFns ++
  (FullM5.m5Fns.drop 226).take 6 ++
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ] ++
  (FullM5.m5Fns.drop 235).take 10 ++
  FullM7Reorder.m7ReorderFns ++
  [ FullM6Orch.m6oReorderM6Fn ] ++
  (FullM5.m5Fns.drop 248).take 6 ++
  [ m6CanonicalElimDticksFn ] ++
  FullM6BveFwd.m6BveFwd_fns.drop 16 ++
  [ FullM6OrchAdapters.m6aProbeDticksM6HdrFn
  , FullM6Orch.m6oProbeTailM6Fn
  , FullM6Orch.m6oProbeM6Fn
  , FullM6Orch.m6oPreprocessM6Fn
  , FullM6Orch.m6oSimplifyM6Fn
  , FullM6Orch.m6oSearchM6Fn
  , FullM6Orch.m6oSolveBytesM6Fn
  , FullM6Orch.m6oPreprocessFn
  , FullM6Orch.m6oSearchFn
  , FullM6Orch.m6oSolveBytesFn ]

/-- Unified `M6.0` solver function list (`382` functions in topological order). -/
def m6Fns : List Fn :=
  m6FnsPart1 ++ m6FnsPart2 ++ m6FnsPart3

/-- Closed unified `M6.0` solver module (`externs := []`, `exits := []`). -/
def m6Module : LeanQbe.T.Module :=
  { fns := m6Fns, externs := [], exits := [] }

/-! ## 3. Well-Formedness, Length & Acyclicity Proofs -/

private theorem wf_one {f : Fn} (h : f.Wf) : ∀ g ∈ [f], g.Wf := by
  intro g hg
  rcases List.mem_singleton.mp hg with rfl
  exact h

private theorem wf_cons {f : Fn} {l : List Fn} (hf : f.Wf) (hl : ∀ g ∈ l, g.Wf) :
    ∀ g ∈ f :: l, g.Wf := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hl g hg

private theorem wf_app {l₁ l₂ : List Fn} (h₁ : ∀ f ∈ l₁, f.Wf) (h₂ : ∀ f ∈ l₂, f.Wf) :
    ∀ f ∈ l₁ ++ l₂, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h₁ f hf
  · exact h₂ f hf

private theorem wf_take {l : List Fn} (n : Nat) (hl : ∀ f ∈ l, f.Wf) :
    ∀ f ∈ l.take n, f.Wf := fun f hf => hl f (List.mem_of_mem_take hf)

private theorem wf_drop {l : List Fn} (n : Nat) (hl : ∀ f ∈ l, f.Wf) :
    ∀ f ∈ l.drop n, f.Wf := fun f hf => hl f (List.mem_of_mem_drop hf)

private theorem m6CanonicalReduce_wf : m6CanonicalReduceFn.Wf :=
  FullM5Orch.full_reduce_m5_wf

private theorem m6CanonicalOtfsBin_wf : m6CanonicalOtfsBinFn.Wf :=
  FullM5Otfs.full_otfs_bin_m5_wf

private theorem m6CanonicalProbeAssumePair_wf : m6CanonicalProbeAssumePairFn.Wf :=
  FullM6VivBackbone.full_probe_assume_pair_m6_wf

private theorem m6CanonicalElimDticks_wf : m6CanonicalElimDticksFn.Wf :=
  FullM5Orch.full_elim_dticks_m5_wf

private theorem m6FnsPart1_wf : ∀ f ∈ m6FnsPart1, f.Wf := by
  unfold m6FnsPart1
  repeat' (first
    | exact FullM6BcpS15.m6BcpS15_fns_wf
    | apply wf_app)
  · exact wf_take _ FullM5.m5Fns_wf
  · exact wf_take _ FullM6WatchGc.m6WatchGc_fns_wf
  · exact wf_cons FullM6Orch.full_wstack_defrag_wf (wf_one FullM6Orch.full_watch_push_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6WalkParse.m6WalkParse_fns_wf
  · exact wf_one FullM6Orch.full_rescale_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6OrchAdapters.full_scale_delta_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6Hdr.m6Hdr_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_prop_lit_raw_wf
      (wf_cons FullM6OrchAdapters.full_propagate_ignore_wf
        (wf_one FullM6OrchAdapters.full_propagate_wf))
  · exact wf_take _ (wf_drop _ FullM6WalkParse.m6WalkParse_fns_wf)
  · exact wf_one FullM6Orch.full_parse_body_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_one FullM6Orch.full_lit_rank_wf
  · exact wf_take _ (wf_drop _ FullM6CompactFlush.m6CompactFlush_fns_wf)
  · exact wf_one FullM6Orch.full_sweep_bins_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_rewatch_arena_wf
  · exact wf_take _ (wf_drop _ FullM6WatchGc.m6WatchGc_fns_wf)
  · exact wf_cons FullM6Orch.full_arena_sweep_wf (wf_one FullM6Orch.full_mark_reasons_wf)
  · exact wf_take _ FullM6CompactFlush.m6CompactFlush_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons m6CanonicalReduce_wf (wf_one FullM6Orch.full_reduce_m6_wf)

private theorem m6FnsPart2_wf : ∀ f ∈ m6FnsPart2, f.Wf := by
  unfold m6FnsPart2
  repeat' apply wf_app
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_analyze_rsn_m6_hdr_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6MinShrink.m6MinShrink_fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_bump_analyzed_m6_hdr_wf
      (wf_cons FullM6OrchAdapters.full_restore_bump_ana_m6_hdr_wf
        (wf_one FullM6OrchAdapters.full_ana_failed_lit_m6_hdr_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one m6CanonicalOtfsBin_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6MinShrink.m6MinShrink_fns_wf)
  · exact wf_cons FullM6Orch.full_min_shrink_wf
      (wf_cons FullM6Orch.full_deduce_1uip_wf (wf_one FullM6Orch.full_deduce_1uip_m6_hdr_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6Orch.full_analyze_core_m6_wf
      (wf_one FullM6OrchAdapters.full_analyze_m6_hdr_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6Hdr.m6Hdr_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6WalkParse.m6WalkParse_fns_wf)
  · exact wf_cons FullM6Orch.full_walk_wf
      (wf_cons FullM6OrchAdapters.full_rephase_m6_hdr_wf
        (wf_cons FullM6Orch.full_ema_swap_m6_wf (wf_one FullM6Orch.full_switch_mode_m6_wf)))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6CompactFlush.full_extend_push2_m6cf_wf
      (wf_one FullM6CompactFlush.full_extend_push_cl_m6cf_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6VivBackbone.m6VivBackbone_fns_wf
  · exact wf_one FullM6OrchAdapters.full_add_bin_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one m6CanonicalProbeAssumePair_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6VivBackbone.m6VivBackbone_fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_vivify_tier_m6_hdr_wf
      (wf_one FullM6OrchAdapters.full_vivify_m6_hdr_wf)
  · exact wf_take _ (wf_drop _ FullM6VivBackbone.m6VivBackbone_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6CongSubst.m6CongSubst_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf)
  · exact wf_one FullM6CompactFlush.full_enter_dense_m6cf_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_drop _ FullM6CongSubst.m6CongSubst_fns_wf

private theorem m6FnsPart3_wf : ∀ f ∈ m6FnsPart3, f.Wf := by
  unfold m6FnsPart3
  repeat' (first
    | exact FullM6BvaNoHops.m6BvaNoHopsFns_wf
    | exact FullM7Reorder.m7ReorderFns_wf
    | apply wf_app)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_sweep_dense_m6_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ FullM6BveFwd.m6BveFwd_fns_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6BveFwd.m6BveFwd_fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM6BveFwd.m6BveFwd_fns_wf)
  · exact wf_cons FullM6OrchAdapters.full_bve_var_wf (wf_one FullM6OrchAdapters.full_forward_sub_wf)
  · exact wf_take _ (wf_drop _ FullM6VivBackbone.m6VivBackbone_fns_wf)
  · exact wf_one FullM6OrchAdapters.full_init_fresh_var_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_cons FullM6CompactFlush.full_compact_needed_m6cf_wf
      (wf_cons FullM6CompactFlush.full_compact_flush_m6cf_wf
        (wf_one FullM6CompactFlush.full_compact_mark_live_m6cf_wf))
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one FullM6Orch.full_reorder_m6_wf
  · exact wf_take _ (wf_drop _ FullM5.m5Fns_wf)
  · exact wf_one m6CanonicalElimDticks_wf
  · exact wf_drop _ FullM6BveFwd.m6BveFwd_fns_wf
  · exact wf_cons FullM6OrchAdapters.full_probe_dticks_m6_hdr_wf
      (wf_cons FullM6Orch.full_probe_tail_m6_wf
        (wf_cons FullM6Orch.full_probe_m6_wf
          (wf_cons FullM6Orch.full_preprocess_m6_wf
            (wf_cons FullM6Orch.full_simplify_m6_wf
              (wf_cons FullM6Orch.full_search_m6_wf
                (wf_cons FullM6Orch.kissat_solve_bytes_m6_wf
                  (wf_cons FullM6Orch.full_preprocess_wf
                    (wf_cons FullM6Orch.full_search_wf
                      (wf_one FullM6Orch.kissat_solve_bytes_wf)))))))))

theorem m6Fns_wf : ∀ f ∈ m6Fns, f.Wf :=
  wf_app (wf_app m6FnsPart1_wf m6FnsPart2_wf) m6FnsPart3_wf

theorem m6Fns_length : m6Fns.length = 382 := by
  t_kernel_rfl

theorem m6_acyclic : m6Module.checkAcyclic = true := by
  t_kernel_rfl

/-! ## 4. Compile-Time `#guard` Verification (Boundary, PrintCpp, PrintQbe, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

mutual
  private def exprCalls {rs : List Ty} :
      Expr (fun _ => Unit) (fun _ => Unit) rs → List Sym
    | .let_ _ k => exprCalls (k (Tup.units _))
    | .load _ _ k => exprCalls (k ())
    | .store _ _ k => exprCalls k
    | .call f _ k => f :: exprCalls (k (Tup.units _))
    | .jnz _ t e => exprCalls t ++ exprCalls e
    | .jump _ _ => []
    | .ret _ => []
    | .exit f _ => [f]
    | .hlt => []
    | .group bodies k =>
        blocksCalls (bodies (Tup.units _)) ++ exprCalls (k (Tup.units _))

  private def blocksCalls {rs : List Ty} :
      {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → List Sym
    | [], .nil => []
    | _ :: _, .cons b bs => exprCalls (b (Tup.units _)) ++ blocksCalls bs
end

private def fnCalls (fn : Fn) : List Sym :=
  (exprCalls (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))).eraseDups

private def m6HdrSet : List Sym :=
  (FullM6Hdr.m6Hdr_fns.take 25).map Fn.name ++
  [ "full_reduce_m6", "full_analyze_rsn_m6_hdr", "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
  , "full_deduce_1uip_m6_hdr", "full_analyze_core_m6", "full_analyze_m6_hdr"
  , "full_rephase_m6_hdr", "full_ema_swap_m6", "full_switch_mode_m6"
  , "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr", "full_probe_dticks_m6_hdr"
  , "full_probe_tail_m6", "full_probe_m6", "full_preprocess_m6"
  , "full_simplify_m6", "full_search_m6", "kissat_solve_bytes_m6"
  , "full_preprocess", "full_search", "kissat_solve_bytes" ]

private def fullMemRoots : List Sym :=
  [ "full_init_state", "full_recompute_tiers", "full_reduce", "full_elim_dticks"
  , "full_analyze_rsn", "full_analyze", "full_min_shrink", "full_deduce_1uip"
  , "full_eliminate_m6", "full_extend", "kissat_check_model", "full_lucky", "full_compact" ]

private def fullMemReach : List Sym :=
  m6Fns.reverse.foldl (fun acc fn =>
    if acc.contains fn.name then (fnCalls fn ++ acc).eraseDups else acc) fullMemRoots

#guard m6Fns.length == 382
#guard (m6Fns.map Fn.name).eraseDups.length == 382
#guard m6Module.checkAcyclic
#guard !(fullMemReach.any m6HdrSet.contains)

#guard (ppTModule m6Module).isOk
#guard (PrintQbe.module m6Module).isOk
#guard (ppModule (m6Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .x64AVX2))).isOk
#guard m6Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m6Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m6Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m6Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM6
