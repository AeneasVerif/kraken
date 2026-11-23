/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Transport0
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof
public import LeanQbe.T.Examples.Kissat.FullM7BumpProof
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof
public import LeanQbe.T.Examples.Kissat.FullM7CongHashProof
public import LeanQbe.T.Examples.Kissat.FullM7CongIteProof1
public import LeanQbe.T.Examples.Kissat.FullM6Transport1
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof2
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof3
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2d
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` Unified `M7` Part 2 (`112..275`, `FullM7Transport1`)

Assembles `m7RowsPart2 tPfx` aligned 1-to-1 with `FullM7.m7FnsPart2` (`164` functions), defines
`M7Part2Callees` and the pre-wired gap hypothesis contract `M7GapHyp` (`FullM7SpecBridges`:
`sortTmp` Gap B + `rephase` Gap A), and certifies `[112..274]` plus parameterized `[275]`
(`full_congruence_dense`, discharged in `FullM7OrchProof0`) using canonical
`Full.fullPropagateSpec` (zero `S1.5` drift), plain `public section`, and `0` `@[expose]` tags.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7

/-! ## 1. Gap-A `m7RephaseSpec`, `M7GapHyp`, & Cross-Part Part 2 Callees -/

/-- Gap-A `full_rephase` contract for `FullM7AnalyzeSort.m7RephaseFn` calling `"full_walk"` at
`Full.fullWarmupSpec` (`FullM7.lean:229`). Matches `FullM7SpecBridges.m7RephaseWarmupSpec`. -/
def m7RephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      FullSparseInv c F0
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      FullArenaPermEq s.core
        { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', frame_trail := ftrl',
                      frame_dec := fdec', trail_end := te', propagated := prop',
                      cur_level := cl', probing := prob', unassigned := unass',
                      unflushed := unfl', wvec := wvec', arena := arena',
                      wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' } →
      (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
      fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      (s.core.probing = 0#64 → prob' = 0#64) →
      (FullMem c
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } ⋆ R) m' → Q () m'

theorem m7RephaseSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      FullSparseInv c F0
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      FullArenaPermEq s.core
        { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', frame_trail := ftrl',
                      frame_dec := fdec', trail_end := te', propagated := prop',
                      cur_level := cl', probing := prob', unassigned := unass',
                      unflushed := unfl', wvec := wvec', arena := arena',
                      wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' } →
      (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
      fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      (s.core.probing = 0#64 → prob' = 0#64) →
      (FullMem c
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } ⋆ R) m' → Q () m') :
    m7RephaseSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

theorem m7RephaseSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m7RephaseSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
        FullSparseInv c F0
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } →
        FullArenaPermEq s.core
          { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                        trl := trl', trail_pos := tp', frame_trail := ftrl',
                        frame_dec := fdec', trail_end := te', propagated := prop',
                        cur_level := cl', probing := prob', unassigned := unass',
                        unflushed := unfl', wvec := wvec', arena := arena',
                        wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                        confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                        confl_lit1 := c1', oom := oom' } →
        (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
        fuel'.toNat ≤ s.core.fuel.toNat →
        FullExtScratchPres s
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } →
        (s.core.probing = 0#64 → prob' = 0#64) →
        (FullMem c
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } ⋆ R) m' → Q () m' := hs

theorem m7RephaseSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m7RephaseSpec xs m Q X) : m7RephaseSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- Parametric pre-wired hypotheses for the two in-flight `FullM7SpecBridges` spec gaps
(`@m7-spec-bridges`, `#69`). Zero `sorry`/`axiom`. -/
structure M7GapHyp (Γ : Env) : Prop where
  sortTmp : ∀ a m Q X, Full.fullSortTmpSpec a m Q X →
    Func.wp Γ FullM7AnalyzeSort.full_sort_tmp_m7_body a m Q X
  rephase : ∀ a m Q X, m7RephaseSpec a m Q X →
    Func.wp Γ FullM7AnalyzeSort.full_rephase_m7_body a m Q X

/-- Cross-part Part 2 row memberships required by Part 3 (`FullM7Transport2`) and the `5`-fn tail
(`FullM7OrchProof0`). -/
structure M7Part2Callees (tbl : List SpecEntry) : Prop where
  analyzeM6 : (⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tbl
  nextDecVar : (⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ :
    SpecEntry) ∈ tbl
  rephase : (⟨"full_rephase", [i64], [], m7RephaseSpec, true⟩ : SpecEntry) ∈ tbl
  restartDue : (⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩ :
    SpecEntry) ∈ tbl
  restart : (⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩ : SpecEntry) ∈ tbl
  extendPush2 : (⟨"full_extend_push2", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈ tbl
  extendPushCl : (⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ : SpecEntry) ∈ tbl
  extend : (⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩ : SpecEntry) ∈ tbl
  addBin : (⟨"full_add_bin", [i64, i32, i32], [i64],
    FullM6VivBackbone.fullAddBinM6Spec, true⟩ : SpecEntry) ∈ tbl
  deleteBinary : (⟨"full_delete_binary", [i64, i32, i32], [],
    Full.fullDeleteBinarySpec, true⟩ : SpecEntry) ∈ tbl
  setInactive : (⟨"full_set_inactive", [i64, i32, i32], [],
    Full.fullSetInactiveSpec, true⟩ : SpecEntry) ∈ tbl
  addUnit : (⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ : SpecEntry) ∈ tbl
  luckyScan : (⟨"full_lucky_scan", [i64, .bool, .bool], [i64],
    Full.fullLuckyScanSpec, true⟩ : SpecEntry) ∈ tbl
  enterDense : (⟨"full_enter_dense", [i64], [.bool],
    FullFastSched.schedEnterDenseSpec, true⟩ : SpecEntry) ∈ tbl
  rebuildWatches : (⟨"full_rebuild_watches", [i64], [i64],
    Full.fullRebuildWatchesSpec, true⟩ : SpecEntry) ∈ tbl

/-! ## 2. Part 2 Segment Rows (`164` Entries) -/

private def p2AnalyzeLitRows : List SpecEntry := (fullBaseTable.drop 62).take 1
private def p2AnalyzeRsnRows : List SpecEntry :=
  [⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩]
private def p2ClearAnaRows : List SpecEntry := (fullBaseTable.drop 64).take 1
private def p2MinShrink0Rows : List SpecEntry :=
  [ ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], FullM6MinShrink.m6AnaSiftSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.m6SortAnaQsSpec, true⟩ ]
private def p2Adp46Rows : List SpecEntry :=
  [ ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], [], m6aRestoreBumpAnaSpec, true⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], m6aAnaFailedLitSpec, true⟩ ]
private def p2OtfsRows : List SpecEntry :=
  [ ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩ ]
private def p2MinMarkRows : List SpecEntry := (fullBaseTable.drop 69).take 1
private def p2TmpLessRows : List SpecEntry := (fullBaseTable.drop 71).take 1
private def p2SortTmpM7Rows : List SpecEntry :=
  [ ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [],
      Full.FullMinSpecs.fullSortTmpSiftSpec, true⟩
  , ⟨"full_sort_tmp_sift_m7", [i64, i64, i64, i64, i64], [],
      Full.FullMinSpecs.fullSortTmpSiftSpec, true⟩
  , ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [],
      FullM7AnalyzeSort.m7SortTmpHeapSpec, true⟩
  , ⟨"full_sort_tmp", [i64], [], Full.fullSortTmpSpec, true⟩ ]
private def p2MinShrink1Rows : List SpecEntry :=
  [ ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.m6MinLitDfsSpec, true⟩
  , ⟨"full_min_lit_m6", [i64, i32], [.bool], Full.fullMinLitSpec, true⟩
  , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [], Full.fullShrinkBlkSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ ]
private def p2DetNewLevelRows : List SpecEntry := (fullBaseTable.drop 77).take 1
private def p2OneLitConflRows : List SpecEntry :=
  [⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩]
private def p2Learn2Rows : List SpecEntry :=
  [ ⟨"full_eager_subsume", [i64, i64], [], Full.fullEagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩ ]
private def p2M7BumpRows : List SpecEntry :=
  [ ⟨"full_bump_sift_m7", [i64, i64, i64], [], FullM7Bump.m7BumpSiftSpec, true⟩
  , ⟨"full_bump_sort_stamps_m7", [i64, i64], [], FullM7Bump.m7BumpSortStampsSpec, true⟩
  , ⟨"full_bump_reasons_m7", [i64], [], FullM7Bump.m7BumpReasonsSpec, true⟩
  , ⟨"full_bump_analyzed", [i64], [], Full.fullBumpAnalyzedSpec, true⟩ ]
private def p2RestoreBumpAnaM5Rows : List SpecEntry :=
  [⟨"full_restore_bump_ana_m5", [i64], [], FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩]
private def p2AnalyzeM5Rows : List SpecEntry :=
  [⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩]
private def p2Adp7Rows : List SpecEntry :=
  [⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩]
private def p2NextDecVarRows : List SpecEntry := (fullBaseTable.drop 83).take 1
private def p2HdrDecideRows : List SpecEntry :=
  [⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩]
private def p2M7Walk13Rows : List SpecEntry :=
  [ ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], FullM7Walk.m7CbInvSpec, true⟩
  , ⟨"full_walk_init_table_m7", [i64, i64], [], FullM7Walk.m7InitTableSpec, true⟩
  , ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩
  , ⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.m7InitValsSpec, true⟩
  , ⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.m7CollectSpec, true⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], FullM7Walk.m7BuildOccSpec, true⟩
  , ⟨"full_walk_break_m7", [i64, i32, i64], [i32], FullM7Walk.m7BreakSpec, true⟩
  , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], FullM7Walk.m7PickSpec, true⟩
  , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], FullM7Walk.m7FlipSpec, true⟩
  , ⟨"full_walk_save_min_m7", [i64, i64, .bool], [], FullM7Walk.m7SaveMinSpec, true⟩
  , ⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩
  , ⟨"full_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_walk_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩ ]
private def p2WalkCanonRows : List SpecEntry :=
  [ ⟨"full_warmup", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩ ]
private def p2RephaseM7Rows : List SpecEntry :=
  [⟨"full_rephase", [i64], [], m7RephaseSpec, true⟩]
private def p2RestartDueRows : List SpecEntry :=
  [⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩]
private def p2RestartRows : List SpecEntry := (fullBaseTable.drop 93).take 1
private def p2CfExtendPush2Rows : List SpecEntry :=
  [⟨"full_extend_push2", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩]
private def p2CfExtendPushClRows : List SpecEntry :=
  [⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩]
private def p2ExtendRows : List SpecEntry :=
  [⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩]
private def p2HasBinRows : List SpecEntry := (fullBaseTable.drop 97).take 1
private def p2DelBinSideRows : List SpecEntry := (fullBaseTable.drop 99).take 1
private def p2AddBinM6Rows : List SpecEntry := FullM6VivBackbone.m6VivBackboneSpecTable.take 1
private def p2Adp9Rows : List SpecEntry :=
  [⟨"full_add_bin", [i64, i32, i32], [i64], FullM6VivBackbone.fullAddBinM6Spec, true⟩]
private def p2DelBinToLuckyRows : List SpecEntry :=
  [ ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], Full.fullSetInactiveSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩
  , ⟨"full_lucky_polar", [i64], [i64], Full.fullLuckyPolarSpec, true⟩
  , ⟨"full_lucky", [i64], [i64], Full.fullLuckySpec, true⟩ ]
private def p2HbrDomRows : List SpecEntry :=
  [⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩]
private def p2ProbePropLitRows : List SpecEntry :=
  [⟨"full_probe_prop_lit", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩]
private def p2ProbePair2Rows : List SpecEntry :=
  [ ⟨"full_probe_prop", [i64], [i64], Full.fullProbePropSpec, true⟩
  , ⟨"full_probe_flush_hbr", [i64, i64], [i64], Full.fullProbeFlushHbrSpec, true⟩ ]
private def p2ProbeAssumePairRows : List SpecEntry :=
  [⟨"full_probe_assume_pair", [i64, i32], [i64], Full.fullProbeAssumePairSpec, true⟩]
private def p2ProbeRunRows : List SpecEntry :=
  [⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩]
private def p2VivBb1Rows : List SpecEntry :=
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 26
private def p2Adp1011Rows : List SpecEntry :=
  [ ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩ ]
private def p2VivBb2Rows : List SpecEntry :=
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 29).take 11
private def p2TarjanPopSccRows : List SpecEntry := (fullBaseTable.drop 120).take 1
private def p2TarjanSccRows : List SpecEntry :=
  [⟨"full_tarjan_scc", [i64], [i64], Full.fullTarjanSccSpec, true⟩]
private def p2SubstElimVarsRows : List SpecEntry := (fullBaseTable.drop 122).take 1
private def p2SubstRewriteRows : List SpecEntry :=
  [ ⟨"full_subst_rewrite_bins", [i64], [.bool], Full.fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], Full.fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩ ]
private def p2CfEnterDenseRows : List SpecEntry :=
  [⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩]
private def p2RebuildWatchesRows : List SpecEntry := (fullBaseTable.drop 127).take 1
private def p2CongFindRows : List SpecEntry := (fullBaseTable.drop 128).take 1
private def p2CongMergeRows : List SpecEntry :=
  [⟨"full_cong_merge", [i64, i32, i32], [.bool], Full.fullCongMergeSpec, true⟩]
private def p2CongBva3Rows : List SpecEntry := FullM3CongBva.m3SpecTable.take 3
private def p2HasTernaryRows : List SpecEntry :=
  [⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], Full.fullHasTernarySpec, true⟩]
private def p2SortU32Rows : List SpecEntry :=
  [⟨"full_sort_u32", [i64, i32], [], Full.fullSortU32Spec, true⟩]
private def p2CongDense17Rows : List SpecEntry :=
  [ ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
      FullM6CongSubst.m6CongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
      FullM6CongSubst.m6CongEmitXorSpec, true⟩
  , ⟨"full_cong_has_clause_k", [i64, i32], [.bool], FullM6CongSubst.m6CongHasClauseKSpec, true⟩
  , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64],
      FullM6CongSubst.m6CongExtractXorKSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      FullM6CongSubst.m6CongTryXorIteSpec, true⟩
  , ⟨"full_cong_count_bins", [i64], [], FullM6CongSubst.m6CongCountBinsSpec, true⟩
  , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
      FullM6CongSubst.m6CongEbMatchSpec, true⟩
  , ⟨"full_cong_extract_binaries", [i64, i64], [i64],
      FullM6CongSubst.m6CongExtractBinariesSpec, true⟩
  , ⟨"full_cong_find_units_equivs", [i64], [i64],
      FullM6CongSubst.m6CongFindUnitsEquivsSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM6CongSubst.m6CongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM6CongSubst.m6CongAndMatchSpec, true⟩
  , ⟨"full_cong_xor_match", [i64, i32, i32], [i32], FullM6CongSubst.m6CongXorMatchSpec, true⟩
  , ⟨"full_cong_enq_var", [i64, i64, i32], [], FullM6CongSubst.m6CongEnqVarSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
      FullM6CongSubst.m6CongEvalGateSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM6CongSubst.m6CongWorkStepSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], FullM6CongSubst.m6CongWorklistSpec, true⟩
  , ⟨"full_cong_fwd_subsume", [i64, i64], [i64], FullM6CongSubst.m6CongFwdSubsumeSpec, true⟩ ]
private def p2CongHashRows : List SpecEntry :=
  [ ⟨"full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64], FullM7CongHash.m7CongHtHashEntSpec, true⟩
  , ⟨"full_cong_ht_init_m7", [i64, i64, i64, i64], [i64], FullM7CongHash.m7CongHtInitSpec, true⟩
  , ⟨"full_cong_ht_grow_m7", [i64, i64], [i64], FullM7CongHash.m7CongHtGrowSpec, true⟩
  , ⟨"full_cong_ht_grow_clear_m7", [i64, i64], [i64],
      FullM7CongHash.m7CongHtGrowClearSpec, true⟩
  , ⟨"full_cong_ht_lookup_m7", [i64, i64, i32, i32], [i32],
      FullM7CongHash.m7CongHtLookupSpec, true⟩
  , ⟨"full_cong_ht_insert_m7", [i64, i64, i32], [i32], FullM7CongHash.m7CongHtInsertSpec, true⟩ ]
private def p2CongIteRows : List SpecEntry :=
  [ ⟨"full_cong_u64_sift_m7", [i64, i64, i64], [], FullM7CongIte.m7U64SiftSpec, true⟩
  , ⟨"full_cong_u64_sort_m7", [i64, i64], [], FullM7CongIte.m7U64SortSpec, true⟩
  , ⟨"full_cong_bsearch_u64_m7", [i64, i64, i64, i64], [.bool],
      FullM7CongIte.m7BsearchU64Spec, true⟩
  , ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64],
      FullM7CongIte.m7CopyCondbinSpec, true⟩
  , ⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64],
      FullM7CongIte.m7ExtractCondeqSpec, true⟩
  , ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
      FullM7CongIte.m7MergeCondeqM6Spec, true⟩
  , ⟨"full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32],
      FullM7CongIte.m7ExtractIteAllM6Spec, true⟩ ]
private def p2CongDenseEndRows : List SpecEntry :=
  [⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩]

/-- Part 2 specification rows (`112..275`, `164` entries) matching `FullM7.m7FnsPart2`. -/
def m7RowsPart2 (tPfx : List SpecEntry) : List SpecEntry :=
  p2AnalyzeLitRows ++ (p2AnalyzeRsnRows ++ ((tPfx.drop 10).take 1 ++ (p2ClearAnaRows ++
  (p2MinShrink0Rows ++ (p2Adp46Rows ++ (p2OtfsRows ++ (p2MinMarkRows ++ (p2TmpLessRows ++
  (p2SortTmpM7Rows ++ (p2MinShrink1Rows ++ ((tPfx.drop 11).take 3 ++ (p2DetNewLevelRows ++
  (p2OneLitConflRows ++ (p2Learn2Rows ++ (p2M7BumpRows ++ (p2RestoreBumpAnaM5Rows ++
  (p2AnalyzeM5Rows ++ ((tPfx.drop 14).take 1 ++ (p2Adp7Rows ++ (p2NextDecVarRows ++
  (p2HdrDecideRows ++ (p2M7Walk13Rows ++ (p2WalkCanonRows ++ (p2RephaseM7Rows ++
  (p2RestartDueRows ++ (p2RestartRows ++ (p2CfExtendPush2Rows ++ (p2CfExtendPushClRows ++
  (p2ExtendRows ++ (p2HasBinRows ++ (p2DelBinSideRows ++ (p2AddBinM6Rows ++ (p2Adp9Rows ++
  (p2DelBinToLuckyRows ++ (p2HbrDomRows ++ (p2ProbePropLitRows ++ (p2ProbePair2Rows ++
  (p2ProbeAssumePairRows ++ (p2ProbeRunRows ++ (p2VivBb1Rows ++ (p2Adp1011Rows ++
  (p2VivBb2Rows ++ (p2TarjanPopSccRows ++ (p2TarjanSccRows ++ (p2SubstElimVarsRows ++
  (p2SubstRewriteRows ++ (p2CfEnterDenseRows ++ (p2RebuildWatchesRows ++ (p2CongFindRows ++
  (p2CongMergeRows ++ (p2CongBva3Rows ++ (p2HasTernaryRows ++ (p2SortU32Rows ++
  (p2CongDense17Rows ++ (p2CongHashRows ++ (p2CongIteRows ++
    p2CongDenseEndRows))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-! ## 3. Part 2 Function Decomposition, Signatures & `noExit` Metadata -/

private def p2AnalyzeLitFns : List Fn := (FullM5.m5Fns.drop 69).take 1
private def p2AnalyzeRsnFns : List Fn := (FullM5.m5Fns.drop 70).take 1
private def p2ClearAnaFns : List Fn := (FullM5.m5Fns.drop 71).take 1
private def p2MinShrink0Fns : List Fn := (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2
private def p2Adp46Fns : List Fn :=
  [m6aBumpAnalyzedM6HdrFn, m6aRestoreBumpAnaM6HdrFn, m6aAnaFailedLitM6HdrFn]
private def p2OtfsFns : List Fn :=
  (FullM5.m5Fns.drop 74).take 1 ++ [m6CanonicalOtfsBinFn] ++ (FullM5.m5Fns.drop 76).take 1
private def p2MinMarkFns : List Fn := (FullM5.m5Fns.drop 77).take 1
private def p2TmpLessFns : List Fn := (FullM5.m5Fns.drop 79).take 1
private def p2SortTmpM7Fns : List Fn :=
  [ FullM7AnalyzeSort.m7SortTmpSiftFn ] ++ FullM7AnalyzeSort.m7AnalyzeSort_fns.take 1 ++
  [ FullM7AnalyzeSort.m7SortTmpHeapFn, FullM7AnalyzeSort.m7SortTmpFn ]
private def p2MinShrink1Fns : List Fn := (FullM6MinShrink.m6MinShrink_fns.drop 8).take 7
private def p2DetNewLevelFns : List Fn := (FullM5.m5Fns.drop 85).take 1
private def p2OneLitConflFns : List Fn := (FullM5.m5Fns.drop 86).take 1
private def p2Learn2Fns : List Fn := (FullM5.m5Fns.drop 88).take 2
private def p2M7BumpFns : List Fn :=
  (FullM7Bump.m7BumpFns.drop 3).take 3 ++ [FullM7Bump.m7BumpAnalyzedFn]
private def p2RestoreBumpAnaM5Fns : List Fn := (FullM5.m5Fns.drop 73).take 1
private def p2AnalyzeM5Fns : List Fn := (FullM5.m5Fns.drop 90).take 1
private def p2Adp7Fns : List Fn := [m6aAnalyzeM6HdrFn]
private def p2NextDecVarFns : List Fn := (FullM5.m5Fns.drop 91).take 1
private def p2HdrDecideFns : List Fn := (FullM6Hdr.m6Hdr_fns.drop 24).take 1
private def p2M7Walk13Fns : List Fn := FullM7Walk.m7WalkFns
private def p2WalkCanonFns : List Fn := [m7WarmupCanonFn, m7WalkCanonFn]
private def p2RephaseM7Fns : List Fn := [FullM7AnalyzeSort.m7RephaseFn]
private def p2RestartDueFns : List Fn := (FullM5.m5Fns.drop 100).take 1
private def p2RestartFns : List Fn := (FullM5.m5Fns.drop 101).take 1
private def p2CfExtendPush2Fns : List Fn := [FullM6CompactFlush.m6cfExtendPush2Fn]
private def p2CfExtendPushClFns : List Fn := [FullM6CompactFlush.m6cfExtendPushClFn]
private def p2ExtendFns : List Fn := (FullM5.m5Fns.drop 104).take 1
private def p2HasBinFns : List Fn := (FullM5.m5Fns.drop 105).take 1
private def p2DelBinSideFns : List Fn := (FullM5.m5Fns.drop 106).take 1
private def p2AddBinM6Fns : List Fn := FullM6VivBackbone.m6VivBackbone_fns.take 1
private def p2Adp9Fns : List Fn := [m6aAddBinFn]
private def p2DelBinToLuckyFns : List Fn := (FullM5.m5Fns.drop 108).take 6
private def p2HbrDomFns : List Fn := (FullM5.m5Fns.drop 114).take 1
private def p2ProbePropLitFns : List Fn := (FullM5.m5Fns.drop 115).take 1
private def p2ProbePair2Fns : List Fn := (FullM5.m5Fns.drop 116).take 2
private def p2ProbeAssumePairFns : List Fn := [m6CanonicalProbeAssumePairFn]
private def p2ProbeRunFns : List Fn := (FullM5.m5Fns.drop 119).take 1
private def p2VivBb1Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 26
private def p2Adp1011Fns : List Fn := [m6aVivifyTierM6HdrFn, m6aVivifyM6HdrFn]
private def p2VivBb2Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 29).take 11
private def p2TarjanPopSccFns : List Fn := (FullM5.m5Fns.drop 139).take 1
private def p2TarjanSccFns : List Fn := FullM6CongSubst.m6CongSubst_fns.take 1
private def p2SubstElimVarsFns : List Fn := (FullM5.m5Fns.drop 141).take 1
private def p2SubstRewriteFns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 1).take 3
private def p2CfEnterDenseFns : List Fn := [FullM6CompactFlush.m6cfEnterDenseFn]
private def p2RebuildWatchesFns : List Fn := (FullM5.m5Fns.drop 146).take 1
private def p2CongFindFns : List Fn := (FullM5.m5Fns.drop 162).take 1
private def p2CongMergeFns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 4).take 1
private def p2CongBva3Fns : List Fn := (FullM5.m5Fns.drop 170).take 3
private def p2HasTernaryFns : List Fn := (FullM5.m5Fns.drop 164).take 1
private def p2SortU32Fns : List Fn := [FullM7AnalyzeSort.m7SortU32Fn]
private def p2CongDense17Fns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 5).take 17
private def p2CongHashFns : List Fn := FullM7CongHash.m7CongHashFns
private def p2CongIteFns : List Fn := FullM7CongIte.m7CongIteFns
private def p2CongDenseEndFns : List Fn := [m7CongruenceDenseFn]

private def p2FnsSeg : List Fn :=
  p2AnalyzeLitFns ++ (p2AnalyzeRsnFns ++ ((m7OrchPfxFns.drop 10).take 1 ++ (p2ClearAnaFns ++
  (p2MinShrink0Fns ++ (p2Adp46Fns ++ (p2OtfsFns ++ (p2MinMarkFns ++ (p2TmpLessFns ++
  (p2SortTmpM7Fns ++ (p2MinShrink1Fns ++ ((m7OrchPfxFns.drop 11).take 3 ++ (p2DetNewLevelFns ++
  (p2OneLitConflFns ++ (p2Learn2Fns ++ (p2M7BumpFns ++ (p2RestoreBumpAnaM5Fns ++
  (p2AnalyzeM5Fns ++ ((m7OrchPfxFns.drop 14).take 1 ++ (p2Adp7Fns ++ (p2NextDecVarFns ++
  (p2HdrDecideFns ++ (p2M7Walk13Fns ++ (p2WalkCanonFns ++ (p2RephaseM7Fns ++
  (p2RestartDueFns ++ (p2RestartFns ++ (p2CfExtendPush2Fns ++ (p2CfExtendPushClFns ++
  (p2ExtendFns ++ (p2HasBinFns ++ (p2DelBinSideFns ++ (p2AddBinM6Fns ++ (p2Adp9Fns ++
  (p2DelBinToLuckyFns ++ (p2HbrDomFns ++ (p2ProbePropLitFns ++ (p2ProbePair2Fns ++
  (p2ProbeAssumePairFns ++ (p2ProbeRunFns ++ (p2VivBb1Fns ++ (p2Adp1011Fns ++
  (p2VivBb2Fns ++ (p2TarjanPopSccFns ++ (p2TarjanSccFns ++ (p2SubstElimVarsFns ++
  (p2SubstRewriteFns ++ (p2CfEnterDenseFns ++ (p2RebuildWatchesFns ++ (p2CongFindFns ++
  (p2CongMergeFns ++ (p2CongBva3Fns ++ (p2HasTernaryFns ++ (p2SortU32Fns ++
  (p2CongDense17Fns ++ (p2CongHashFns ++ (p2CongIteFns ++
    p2CongDenseEndFns))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem p2Fns_eq : m7FnsPart2 = p2FnsSeg := by
  unfold FullM7.m7FnsPart2 p2FnsSeg
  rw [m7OrchPfxFns_eq]
  t_kernel_rfl

theorem m7RowsPart2_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig) :
    (m7RowsPart2 tPfx).map (fun e => (e.name, e.as, e.rs)) = m7FnsPart2.map Fn.sig := by
  have s01 : p2AnalyzeLitRows.map (fun e => (e.name, e.as, e.rs)) = p2AnalyzeLitFns.map Fn.sig :=
    by t_kernel_rfl
  have s02 : p2AnalyzeRsnRows.map (fun e => (e.name, e.as, e.rs)) = p2AnalyzeRsnFns.map Fn.sig :=
    by t_kernel_rfl
  have s03 : p2ClearAnaRows.map (fun e => (e.name, e.as, e.rs)) = p2ClearAnaFns.map Fn.sig :=
    by t_kernel_rfl
  have s04 : p2MinShrink0Rows.map (fun e => (e.name, e.as, e.rs)) = p2MinShrink0Fns.map Fn.sig :=
    by t_kernel_rfl
  have s05 : p2Adp46Rows.map (fun e => (e.name, e.as, e.rs)) = p2Adp46Fns.map Fn.sig := by
    t_kernel_rfl
  have s06 : p2OtfsRows.map (fun e => (e.name, e.as, e.rs)) = p2OtfsFns.map Fn.sig := by
    t_kernel_rfl
  have s07 : p2MinMarkRows.map (fun e => (e.name, e.as, e.rs)) = p2MinMarkFns.map Fn.sig := by
    t_kernel_rfl
  have s08 : p2TmpLessRows.map (fun e => (e.name, e.as, e.rs)) = p2TmpLessFns.map Fn.sig := by
    t_kernel_rfl
  have s09 : p2SortTmpM7Rows.map (fun e => (e.name, e.as, e.rs)) = p2SortTmpM7Fns.map Fn.sig :=
    by t_kernel_rfl
  have s10 : p2MinShrink1Rows.map (fun e => (e.name, e.as, e.rs)) = p2MinShrink1Fns.map Fn.sig :=
    by t_kernel_rfl
  have s11 : p2DetNewLevelRows.map (fun e => (e.name, e.as, e.rs)) =
      p2DetNewLevelFns.map Fn.sig := by t_kernel_rfl
  have s12 : p2OneLitConflRows.map (fun e => (e.name, e.as, e.rs)) =
      p2OneLitConflFns.map Fn.sig := by t_kernel_rfl
  have s13 : p2Learn2Rows.map (fun e => (e.name, e.as, e.rs)) = p2Learn2Fns.map Fn.sig := by
    t_kernel_rfl
  have s14 : p2M7BumpRows.map (fun e => (e.name, e.as, e.rs)) = p2M7BumpFns.map Fn.sig := by
    t_kernel_rfl
  have s15 : p2RestoreBumpAnaM5Rows.map (fun e => (e.name, e.as, e.rs)) =
      p2RestoreBumpAnaM5Fns.map Fn.sig := by t_kernel_rfl
  have s16 : p2AnalyzeM5Rows.map (fun e => (e.name, e.as, e.rs)) = p2AnalyzeM5Fns.map Fn.sig :=
    by t_kernel_rfl
  have s17 : p2Adp7Rows.map (fun e => (e.name, e.as, e.rs)) = p2Adp7Fns.map Fn.sig := by
    t_kernel_rfl
  have s18 : p2NextDecVarRows.map (fun e => (e.name, e.as, e.rs)) =
      p2NextDecVarFns.map Fn.sig := by t_kernel_rfl
  have s19 : p2HdrDecideRows.map (fun e => (e.name, e.as, e.rs)) = p2HdrDecideFns.map Fn.sig :=
    by t_kernel_rfl
  have s20 : p2M7Walk13Rows.map (fun e => (e.name, e.as, e.rs)) = p2M7Walk13Fns.map Fn.sig := by
    t_kernel_rfl
  have s21 : p2WalkCanonRows.map (fun e => (e.name, e.as, e.rs)) = p2WalkCanonFns.map Fn.sig :=
    by t_kernel_rfl
  have s22 : p2RephaseM7Rows.map (fun e => (e.name, e.as, e.rs)) = p2RephaseM7Fns.map Fn.sig :=
    by t_kernel_rfl
  have s23 : p2RestartDueRows.map (fun e => (e.name, e.as, e.rs)) =
      p2RestartDueFns.map Fn.sig := by t_kernel_rfl
  have s24 : p2RestartRows.map (fun e => (e.name, e.as, e.rs)) = p2RestartFns.map Fn.sig := by
    t_kernel_rfl
  have s25 : p2CfExtendPush2Rows.map (fun e => (e.name, e.as, e.rs)) =
      p2CfExtendPush2Fns.map Fn.sig := by t_kernel_rfl
  have s26 : p2CfExtendPushClRows.map (fun e => (e.name, e.as, e.rs)) =
      p2CfExtendPushClFns.map Fn.sig := by t_kernel_rfl
  have s27 : p2ExtendRows.map (fun e => (e.name, e.as, e.rs)) = p2ExtendFns.map Fn.sig := by
    t_kernel_rfl
  have s28 : p2HasBinRows.map (fun e => (e.name, e.as, e.rs)) = p2HasBinFns.map Fn.sig := by
    t_kernel_rfl
  have s29 : p2DelBinSideRows.map (fun e => (e.name, e.as, e.rs)) =
      p2DelBinSideFns.map Fn.sig := by t_kernel_rfl
  have s30 : p2AddBinM6Rows.map (fun e => (e.name, e.as, e.rs)) = p2AddBinM6Fns.map Fn.sig := by
    t_kernel_rfl
  have s31 : p2Adp9Rows.map (fun e => (e.name, e.as, e.rs)) = p2Adp9Fns.map Fn.sig := by
    t_kernel_rfl
  have s32 : p2DelBinToLuckyRows.map (fun e => (e.name, e.as, e.rs)) =
      p2DelBinToLuckyFns.map Fn.sig := by t_kernel_rfl
  have s33 : p2HbrDomRows.map (fun e => (e.name, e.as, e.rs)) = p2HbrDomFns.map Fn.sig := by
    t_kernel_rfl
  have s34 : p2ProbePropLitRows.map (fun e => (e.name, e.as, e.rs)) =
      p2ProbePropLitFns.map Fn.sig := by t_kernel_rfl
  have s35 : p2ProbePair2Rows.map (fun e => (e.name, e.as, e.rs)) =
      p2ProbePair2Fns.map Fn.sig := by t_kernel_rfl
  have s36 : p2ProbeAssumePairRows.map (fun e => (e.name, e.as, e.rs)) =
      p2ProbeAssumePairFns.map Fn.sig := by t_kernel_rfl
  have s37 : p2ProbeRunRows.map (fun e => (e.name, e.as, e.rs)) = p2ProbeRunFns.map Fn.sig := by
    t_kernel_rfl
  have s38 : p2VivBb1Rows.map (fun e => (e.name, e.as, e.rs)) = p2VivBb1Fns.map Fn.sig := by
    t_kernel_rfl
  have s39 : p2Adp1011Rows.map (fun e => (e.name, e.as, e.rs)) = p2Adp1011Fns.map Fn.sig := by
    t_kernel_rfl
  have s40 : p2VivBb2Rows.map (fun e => (e.name, e.as, e.rs)) = p2VivBb2Fns.map Fn.sig := by
    t_kernel_rfl
  have s41 : p2TarjanPopSccRows.map (fun e => (e.name, e.as, e.rs)) =
      p2TarjanPopSccFns.map Fn.sig := by t_kernel_rfl
  have s42 : p2TarjanSccRows.map (fun e => (e.name, e.as, e.rs)) = p2TarjanSccFns.map Fn.sig :=
    by t_kernel_rfl
  have s43 : p2SubstElimVarsRows.map (fun e => (e.name, e.as, e.rs)) =
      p2SubstElimVarsFns.map Fn.sig := by t_kernel_rfl
  have s44 : p2SubstRewriteRows.map (fun e => (e.name, e.as, e.rs)) =
      p2SubstRewriteFns.map Fn.sig := by t_kernel_rfl
  have s45 : p2CfEnterDenseRows.map (fun e => (e.name, e.as, e.rs)) =
      p2CfEnterDenseFns.map Fn.sig := by t_kernel_rfl
  have s46 : p2RebuildWatchesRows.map (fun e => (e.name, e.as, e.rs)) =
      p2RebuildWatchesFns.map Fn.sig := by t_kernel_rfl
  have s47 : p2CongFindRows.map (fun e => (e.name, e.as, e.rs)) = p2CongFindFns.map Fn.sig := by
    t_kernel_rfl
  have s48 : p2CongMergeRows.map (fun e => (e.name, e.as, e.rs)) = p2CongMergeFns.map Fn.sig :=
    by t_kernel_rfl
  have s49 : p2CongBva3Rows.map (fun e => (e.name, e.as, e.rs)) = p2CongBva3Fns.map Fn.sig := by
    t_kernel_rfl
  have s50 : p2HasTernaryRows.map (fun e => (e.name, e.as, e.rs)) =
      p2HasTernaryFns.map Fn.sig := by t_kernel_rfl
  have s51 : p2SortU32Rows.map (fun e => (e.name, e.as, e.rs)) = p2SortU32Fns.map Fn.sig := by
    t_kernel_rfl
  have s52 : p2CongDense17Rows.map (fun e => (e.name, e.as, e.rs)) =
      p2CongDense17Fns.map Fn.sig := by t_kernel_rfl
  have s53 : p2CongHashRows.map (fun e => (e.name, e.as, e.rs)) = p2CongHashFns.map Fn.sig := by
    t_kernel_rfl
  have s54 : p2CongIteRows.map (fun e => (e.name, e.as, e.rs)) = p2CongIteFns.map Fn.sig := by
    t_kernel_rfl
  have s55 : p2CongDenseEndRows.map (fun e => (e.name, e.as, e.rs)) =
      p2CongDenseEndFns.map Fn.sig := by t_kernel_rfl
  rw [p2Fns_eq]
  simp only [m7RowsPart2, p2FnsSeg, List.map_append, s01, s02, s03, s04, s05, s06, s07, s08,
    s09, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
    s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44,
    s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, pfx21Slice_sigs hsig]

theorem m7RowsPart2_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) :
    (m7RowsPart2 tPfx).all SpecEntry.noExit = true := by
  have n01 : p2AnalyzeLitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p2AnalyzeRsnRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p2ClearAnaRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p2MinShrink0Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p2Adp46Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p2OtfsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p2MinMarkRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p2TmpLessRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p2SortTmpM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p2MinShrink1Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p2DetNewLevelRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p2OneLitConflRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p2Learn2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p2M7BumpRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p2RestoreBumpAnaM5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p2AnalyzeM5Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p2Adp7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p2NextDecVarRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p2HdrDecideRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p2M7Walk13Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p2WalkCanonRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p2RephaseM7Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n23 : p2RestartDueRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n24 : p2RestartRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n25 : p2CfExtendPush2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n26 : p2CfExtendPushClRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n27 : p2ExtendRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n28 : p2HasBinRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n29 : p2DelBinSideRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n30 : p2AddBinM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n31 : p2Adp9Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n32 : p2DelBinToLuckyRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n33 : p2HbrDomRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n34 : p2ProbePropLitRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n35 : p2ProbePair2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n36 : p2ProbeAssumePairRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n37 : p2ProbeRunRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n38 : p2VivBb1Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n39 : p2Adp1011Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n40 : p2VivBb2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n41 : p2TarjanPopSccRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n42 : p2TarjanSccRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n43 : p2SubstElimVarsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n44 : p2SubstRewriteRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n45 : p2CfEnterDenseRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n46 : p2RebuildWatchesRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n47 : p2CongFindRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n48 : p2CongMergeRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n49 : p2CongBva3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n50 : p2HasTernaryRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n51 : p2SortU32Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n52 : p2CongDense17Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n53 : p2CongHashRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n54 : p2CongIteRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n55 : p2CongDenseEndRows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m7RowsPart2, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10, n11,
    n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30,
    n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49,
    n50, n51, n52, n53, n54, n55, pfx21Slice_noExit hno, Bool.and_self]

theorem m7Part2Callees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart2 tPfx, e ∈ tbl) : M7Part2Callees tbl := by
  have sub_adp7 : ∀ e ∈ p2Adp7Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 19 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ndv : ∀ e ∈ p2NextDecVarRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 20 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_reph : ∀ e ∈ p2RephaseM7Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 24 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_rstd : ∀ e ∈ p2RestartDueRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 25 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_rst : ∀ e ∈ p2RestartRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 26 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ep2 : ∀ e ∈ p2CfExtendPush2Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 27 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_epc : ∀ e ∈ p2CfExtendPushClRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 28 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ext : ∀ e ∈ p2ExtendRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 29 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_adp9 : ∀ e ∈ p2Adp9Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 33 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_dbl : ∀ e ∈ p2DelBinToLuckyRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 34 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ed : ∀ e ∈ p2CfEnterDenseRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 47 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_reb : ∀ e ∈ p2RebuildWatchesRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 48 apply List.mem_append_right); exact List.mem_append_left _ h)
  exact ⟨ sub_adp7 _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_ndv _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_reph _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_rstd _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_rst _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_ep2 _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_epc _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_ext _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_adp9 _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_dbl _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_dbl _ (List.mem_of_getElem? (i := 1) rfl)
    , sub_dbl _ (List.mem_of_getElem? (i := 2) rfl)
    , sub_dbl _ (List.mem_of_getElem? (i := 3) rfl)
    , sub_ed _ (List.mem_of_getElem? (i := 0) rfl)
    , sub_reb _ (List.mem_of_getElem? (i := 0) rfl) ⟩

/-! ## 4. Part 2 Segment `TableImpl` Proofs -/

private theorem p2SortTmpM7_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2SortTmpM7Rows, e ∈ tbl) (hGap : M7GapHyp (Env.ofTable tbl)) :
    TableImpl (Env.ofTable tbl) p2SortTmpM7Fns p2SortTmpM7Rows := by
  have hfn : p2SortTmpM7Fns =
      [ ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [],
          FullM7AnalyzeSort.full_sort_tmp_sift_m7_body⟩
      , ⟨"full_sort_tmp_sift_m7", [i64, i64, i64, i64, i64], [],
          FullM7AnalyzeSort.full_sort_tmp_sift_m7_body⟩
      , ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [],
          FullM7AnalyzeSort.full_sort_tmp_heap_m7_body⟩
      , ⟨"full_sort_tmp", [i64], [], FullM7AnalyzeSort.full_sort_tmp_m7_body⟩ ] := by t_kernel_rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p2SortTmpM7Rows
  exact ⟨ SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_heap_m7_wp (Env.ofTable tbl)
        (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of hGap.sortTmp, trivial ⟩

private theorem p2MinShrink1_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2MinShrink1Rows, e ∈ tbl)
    (hMark : (⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hSortTmp : (⟨"full_sort_tmp", [i64], [], Full.fullSortTmpSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAnaLit : (⟨"full_analyze_lit", [i64, i32, i32], [.bool],
      Full.fullAnalyzeLitSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAnaRsn : (⟨"full_analyze_rsn", [i64, i32, i32], [.bool],
      Full.fullAnalyzeRsnSpec, true⟩ : SpecEntry) ∈ tbl)
    (hClear : (⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩ : SpecEntry) ∈ tbl)
    (hOtfsL : (⟨"full_otfs_large", [i64, i32, i32], [.bool],
      Full.fullOtfsLargeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hOtfsB : (⟨"full_otfs_bin", [i64, i32, i32], [.bool],
      Full.fullOtfsBinSpec, true⟩ : SpecEntry) ∈ tbl)
    (hOtfsS : (⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [],
      Full.fullOtfsSubsumeSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2MinShrink1Fns p2MinShrink1Rows := by
  have hfn : p2MinShrink1Fns =
      [ ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
          FullM6MinShrink.full_min_lit_dfs_m6_body⟩
      , ⟨"full_min_lit_m6", [i64, i32], [.bool], FullM6MinShrink.full_min_lit_m6_body⟩
      , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool],
          FullM6MinShrink.full_shrink_lower_m6_body⟩
      , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
          FullM6MinShrink.full_shrink_blk_bool_m6_body⟩
      , ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [],
          FullM6MinShrink.full_shrink_blk_m6_body⟩
      , ⟨"full_min_shrink_m6", [i64], [], FullM6MinShrink.full_min_shrink_m6_body⟩
      , ⟨"full_deduce_1uip_m6", [i64], [i64], FullM6MinShrink.full_deduce_1uip_m6_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rDfs := er 0 rfl (fun _ _ _ _ h => FullM6MinShrink.m6MinLitDfsSpec_monoX h)
  have rLow := er 2 rfl (fun _ _ _ _ h => h)
  have rBlkB := er 3 rfl (fun _ _ _ _ h => FullM6MinShrink.m6ShrinkBlkBoolSpec_monoX h)
  have rMrk := envRow_mem hnd _ _ _ _ hMark
  rw [hfn]; unfold p2MinShrink1Rows
  exact ⟨ SpecEntry.Impl.of (FullM6MinShrink.full_min_lit_dfs_m6_wp (Env.ofTable tbl) rMrk)
    , SpecEntry.Impl.of (FullM6MinShrink.full_min_lit_m6_wp (Env.ofTable tbl) rDfs)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_lower_m6_wp (Env.ofTable tbl) rMrk rDfs)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_blk_bool_m6_wp (Env.ofTable tbl) rLow rMrk)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_blk_m6_wp (Env.ofTable tbl) rBlkB)
    , SpecEntry.Impl.of (FullM6MinShrink.full_min_shrink_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSortTmp) rMrk rDfs rBlkB)
    , SpecEntry.Impl.of (FullM6MinShrink.full_deduce_1uip_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAnaLit) (envRow_mem hnd _ _ _ _ hAnaRsn)
        (envRow_mem hnd _ _ _ _ hClear) (envRow_mem hnd _ _ _ _ hOtfsL)
        (envRow_mem hnd _ _ _ _ hOtfsB) (envRow_mem hnd _ _ _ _ hOtfsS)), trivial ⟩

private theorem p2M7Bump_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2M7BumpRows, e ∈ tbl)
    (hBumpVar : (⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDecay : (⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ : SpecEntry) ∈ tbl)
    (hQmtf : (⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2M7BumpFns p2M7BumpRows := by
  have hfn : p2M7BumpFns =
      [ ⟨"full_bump_sift_m7", [i64, i64, i64], [], FullM7Bump.full_bump_sift_m7_body⟩
      , ⟨"full_bump_sort_stamps_m7", [i64, i64], [], FullM7Bump.full_bump_sort_stamps_m7_body⟩
      , ⟨"full_bump_reasons_m7", [i64], [], FullM7Bump.full_bump_reasons_m7_body⟩
      , ⟨"full_bump_analyzed", [i64], [], FullM7Bump.full_bump_analyzed_m7_body⟩ ] := by
    t_kernel_rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p2M7BumpRows
  exact ⟨ SpecEntry.Impl.of (FullM7Bump.full_bump_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Bump.full_bump_sort_stamps_m7_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ => FullM7Bump.m7BumpSiftSpec_noExit)))
    , SpecEntry.Impl.of (FullM7Bump.full_bump_reasons_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Bump.full_bump_analyzed_m7_wp (Env.ofTable tbl)
        (er 2 rfl (fun _ _ _ _ => FullM7Bump.m7BumpReasonsSpec_noExit))
        (er 1 rfl (fun _ _ _ _ => FullM7Bump.m7BumpSortStampsSpec_noExit))
        (envRow_mem hnd _ _ _ _ hBumpVar) (envRow_mem hnd _ _ _ _ hDecay)
        (envRow_mem hnd _ _ _ _ hQmtf)), trivial ⟩

private theorem p2M7Walk13_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2M7Walk13Rows, e ∈ tbl)
    (hRng : (⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNDV : (⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hAsg : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2M7Walk13Fns p2M7Walk13Rows := by
  have hfn : p2M7Walk13Fns =
      [ ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], FullM7Walk.full_walk_cb_inv_m7_body⟩
      , ⟨"full_walk_init_table_m7", [i64, i64], [], FullM7Walk.full_walk_init_table_m7_body⟩
      , ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.full_walk_effort_m7_body⟩
      , ⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.full_walk_init_vals_m7_body⟩
      , ⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.full_walk_collect_m7_body⟩
      , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], FullM7Walk.full_walk_build_occ_m7_body⟩
      , ⟨"full_walk_break_m7", [i64, i32, i64], [i32], FullM7Walk.full_walk_break_m7_body⟩
      , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], FullM7Walk.full_walk_pick_m7_body⟩
      , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], FullM7Walk.full_walk_flip_m7_body⟩
      , ⟨"full_walk_save_min_m7", [i64, i64, .bool], [], FullM7Walk.full_walk_save_min_m7_body⟩
      , ⟨"full_walk_m7", [i64], [], FullM7Walk.full_walk_m7_body⟩
      , ⟨"full_warmup_m7", [i64], [], FullM7Walk.full_warmup_m7_body⟩
      , ⟨"full_walk_warmup_m7", [i64], [], FullM7Walk.full_walk_warmup_m7_body⟩ ] := by t_kernel_rfl
  have er := envRowAt hnd hown
  rw [hfn]; unfold p2M7Walk13Rows
  exact ⟨ SpecEntry.Impl.of (FullM7Walk.full_walk_cb_inv_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_init_table_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_effort_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_init_vals_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_collect_m7_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_build_occ_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_break_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_pick_m7_wp (Env.ofTable tbl)
        (er 6 rfl (fun _ _ _ _ h => FullM7Walk.m7BreakSpec_noExit h))
        (envRow_mem hnd _ _ _ _ hRng))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_flip_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_save_min_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_m7_wp (Env.ofTable tbl)
        (er 3 rfl (fun _ _ _ _ h => FullM7Walk.m7InitValsSpec_noExit h))
        (er 4 rfl (fun _ _ _ _ h => FullM7Walk.m7CollectSpec_noExit h))
        (er 0 rfl (fun _ _ _ _ h => FullM7Walk.m7CbInvSpec_noExit h))
        (er 1 rfl (fun _ _ _ _ h => FullM7Walk.m7InitTableSpec_noExit h))
        (er 5 rfl (fun _ _ _ _ h => FullM7Walk.m7BuildOccSpec_noExit h))
        (er 2 rfl (fun _ _ _ _ h => FullM7Walk.m7EffortSpec_noExit h))
        (er 7 rfl (fun _ _ _ _ h => FullM7Walk.m7PickSpec_noExit h))
        (er 8 rfl (fun _ _ _ _ h => FullM7Walk.m7FlipSpec_noExit h))
        (er 9 rfl (fun _ _ _ _ h => FullM7Walk.m7SaveMinSpec_noExit h)))
    , SpecEntry.Impl.of (FullM7Walk.full_warmup_m7_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNDV) (envRow_mem hnd _ _ _ _ hAsg)
        (envRow_mem hnd _ _ _ _ hProp) (envRow_mem hnd _ _ _ _ hBt))
    , SpecEntry.Impl.of (FullM7Walk.full_walk_warmup_m7_wp (Env.ofTable tbl)
        (er 11 rfl (fun _ _ _ _ h => h)) (er 10 rfl (fun _ _ _ _ h => h))), trivial ⟩

private theorem p2CongDense17_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2CongDense17Rows, e ∈ tbl)
    (hTern : (⟨"full_has_ternary", [i64, i32, i32, i32], [.bool],
      Full.fullHasTernarySpec, true⟩ : SpecEntry) ∈ tbl)
    (hSortU : (⟨"full_sort_u32", [i64, i32], [], Full.fullSortU32Spec, true⟩ : SpecEntry) ∈ tbl)
    (hHb : (⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hAb : (⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAu : (⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ : SpecEntry) ∈ tbl)
    (hUf : (⟨"full_cong_unit_fold", [i64, i32, i32], [i64],
      FullM3CongBva.m3CongUnitFoldSpec, true⟩ : SpecEntry) ∈ tbl)
    (hEf : (⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩ : SpecEntry) ∈ tbl)
    (hCf : (⟨"full_cong_find", [i64, i32], [i32], Full.fullCongFindSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2CongDense17Fns p2CongDense17Rows := by
  have hfn : p2CongDense17Fns =
      [ ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
          FullM6CongSubst.full_cong_extract_ite_body⟩
      , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
          FullM6CongSubst.full_cong_emit_xor_body⟩
      , ⟨"full_cong_has_clause_k", [i64, i32], [.bool],
          FullM6CongSubst.full_cong_has_clause_k_body⟩
      , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64],
          FullM6CongSubst.full_cong_extract_xor_k_body⟩
      , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
          FullM6CongSubst.full_cong_try_xor_ite_body⟩
      , ⟨"full_cong_count_bins", [i64], [], FullM6CongSubst.full_cong_count_bins_body⟩
      , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
          FullM6CongSubst.full_cong_eb_match_body⟩
      , ⟨"full_cong_extract_binaries", [i64, i64], [i64],
          FullM6CongSubst.full_cong_extract_binaries_body⟩
      , ⟨"full_cong_find_units_equivs", [i64], [i64],
          FullM6CongSubst.full_cong_find_units_equivs_body⟩
      , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM6CongSubst.full_cong_extract_body⟩
      , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM6CongSubst.full_cong_and_match_body⟩
      , ⟨"full_cong_xor_match", [i64, i32, i32], [i32], FullM6CongSubst.full_cong_xor_match_body⟩
      , ⟨"full_cong_enq_var", [i64, i64, i32], [], FullM6CongSubst.full_cong_enq_var_body⟩
      , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
          FullM6CongSubst.full_cong_eval_gate_body⟩
      , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM6CongSubst.full_cong_work_step_body⟩
      , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], FullM6CongSubst.full_cong_worklist_body⟩
      , ⟨"full_cong_fwd_subsume", [i64, i64], [i64],
          FullM6CongSubst.full_cong_fwd_subsume_body⟩ ] := by t_kernel_rfl
  have er := envRowAt hnd hown
  have rTern := envRow_mem hnd _ _ _ _ hTern; have rSortU := envRow_mem hnd _ _ _ _ hSortU
  have rHb := envRow_mem hnd _ _ _ _ hHb; have rNext := envRow_mem hnd _ _ _ _ hNext
  have rCf := envRow_mem hnd _ _ _ _ hCf; have r0 := er 0 rfl (fun _ _ _ _ h => h)
  have r5 := er 5 rfl (fun _ _ _ _ h => h); have r13 := er 13 rfl (fun _ _ _ _ h => h)
  rw [hfn]; unfold p2CongDense17Rows
  exact ⟨ SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_ite_wp (Env.ofTable tbl) rTern)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_emit_xor_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_has_clause_k_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_xor_k_wp (Env.ofTable tbl)
        rSortU (er 2 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_try_xor_ite_wp (Env.ofTable tbl)
        rTern (er 1 rfl (fun _ _ _ _ h => h)) r0)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_count_bins_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_eb_match_wp (Env.ofTable tbl) rHb)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_binaries_wp (Env.ofTable tbl)
        rNext rHb (m6_add_bin_to_cong (envRow_mem hnd _ _ _ _ hAb)) r5
        (er 6 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_find_units_equivs_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAu) (envRow_mem hnd _ _ _ _ hEf))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_wp (Env.ofTable tbl)
        rNext rHb r5 (er 4 rfl (fun _ _ _ _ h => h)) (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_and_match_wp (Env.ofTable tbl) rCf)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_xor_match_wp (Env.ofTable tbl) rCf rSortU)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_enq_var_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_eval_gate_wp (Env.ofTable tbl)
        rCf rSortU (envRow_mem hnd _ _ _ _ hUf) (envRow_mem hnd _ _ _ _ hEf)
        (er 10 rfl (fun _ _ _ _ h => h)) (er 11 rfl (fun _ _ _ _ h => h))
        (er 12 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_work_step_wp (Env.ofTable tbl) rCf r13)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_worklist_wp (Env.ofTable tbl) rCf r13)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_fwd_subsume_wp (Env.ofTable tbl)
        rNext rCf (envRow_mem hnd _ _ _ _ hAu)), trivial ⟩

private theorem p2CongHash_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2CongHashRows, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2CongHashFns p2CongHashRows := by
  have hfn : p2CongHashFns =
      [ ⟨"full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64],
          FullM7CongHash.full_cong_ht_hash_ent_m7_body⟩
      , ⟨"full_cong_ht_init_m7", [i64, i64, i64, i64], [i64],
          FullM7CongHash.full_cong_ht_init_m7_body⟩
      , ⟨"full_cong_ht_grow_m7", [i64, i64], [i64], FullM7CongHash.full_cong_ht_grow_m7_body⟩
      , ⟨"full_cong_ht_grow_clear_m7", [i64, i64], [i64],
          FullM7CongHash.full_cong_ht_grow_clear_m7_body⟩
      , ⟨"full_cong_ht_lookup_m7", [i64, i64, i32, i32], [i32],
          FullM7CongHash.full_cong_ht_lookup_m7_body⟩
      , ⟨"full_cong_ht_insert_m7", [i64, i64, i32], [i32],
          FullM7CongHash.full_cong_ht_insert_m7_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have r0 := er 0 rfl FullM7CongHash.m7CongHtHashEntSpec_noExit
  have r2 := er 2 rfl FullM7CongHash.m7CongHtGrowSpec_noExit
  rw [hfn]; unfold p2CongHashRows
  exact ⟨ SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_hash_ent_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_init_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_grow_m7_wp (Env.ofTable tbl) r0)
    , SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_grow_clear_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_lookup_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongHash.full_cong_ht_insert_m7_wp (Env.ofTable tbl) r2 r0)
    , trivial ⟩

private theorem p2CongIte_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2CongIteRows, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2CongIteFns p2CongIteRows := by
  have hfn : p2CongIteFns =
      [ ⟨"full_cong_u64_sift_m7", [i64, i64, i64], [], FullM7CongIte.full_cong_u64_sift_m7_body⟩
      , ⟨"full_cong_u64_sort_m7", [i64, i64], [], FullM7CongIte.full_cong_u64_sort_m7_body⟩
      , ⟨"full_cong_bsearch_u64_m7", [i64, i64, i64, i64], [.bool],
          FullM7CongIte.full_cong_bsearch_u64_m7_body⟩
      , ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64],
          FullM7CongIte.full_cong_copy_condbin_m7_body⟩
      , ⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64],
          FullM7CongIte.full_cong_extract_condeq_m7_body⟩
      , ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
          FullM7CongIte.full_cong_merge_condeq_m7_body⟩
      , ⟨"full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32],
          FullM7CongIte.full_cong_extract_ite_all_m7_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have r0 := er 0 rfl (fun _ _ _ _ => FullM7CongIte.m7U64SiftSpec_noExit)
  have r1 := er 1 rfl (fun _ _ _ _ => FullM7CongIte.m7U64SortSpec_noExit)
  have r2 := er 2 rfl (fun _ _ _ _ => FullM7CongIte.m7BsearchU64Spec_noExit)
  have r3 := er 3 rfl (fun _ _ _ _ => FullM7CongIte.m7CopyCondbinSpec_noExit)
  have r4 := er 4 rfl (fun _ _ _ _ => FullM7CongIte.m7ExtractCondeqSpec_noExit)
  have r5 := er 5 rfl (fun _ _ _ _ => FullM7CongIte.m7MergeCondeqM6Spec_noExit)
  rw [hfn]; unfold p2CongIteRows
  exact ⟨ SpecEntry.Impl.of (FullM7CongIte.full_cong_u64_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongIte.full_cong_u64_sort_m7_wp (Env.ofTable tbl) r0)
    , SpecEntry.Impl.of (FullM7CongIte.full_cong_bsearch_u64_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7CongIte.full_cong_copy_condbin_m7_wp (Env.ofTable tbl) r1)
    , SpecEntry.Impl.of (FullM7CongIte.full_cong_extract_condeq_m7_wp (Env.ofTable tbl) r1 r2)
    , SpecEntry.Impl.of (FullM7CongIte.full_cong_merge_condeq_m7_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of
        (FullM7CongIte.full_cong_extract_ite_all_m7_m6_wp (Env.ofTable tbl) r3 r4 r5)
    , trivial ⟩

private theorem p2VivBb1_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2VivBb1Rows, e ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hUnw : (⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hAu : (⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAb6 : (⟨"full_add_bin_m6", [i64, i32, i32], [i64],
      FullM6VivBackbone.fullAddBinM6Spec, true⟩ : SpecEntry) ∈ tbl)
    (hWp : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAsg : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPIgn : (⟨"full_propagate_ignore", [i64, i64], [i64],
      Full.fullPropagateIgnoreSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p2VivBb1Fns p2VivBb1Rows := by
  have hfn : p2VivBb1Fns =
      [ ⟨"full_viv_unreason_m6", [i64, i32], [], FullM6VivBackbone.full_viv_unreason_m6_body⟩
      , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64],
          FullM6VivBackbone.full_viv_watch_rank_m6_body⟩
      , ⟨"full_viv_best_watch_m6", [i64, i32], [], FullM6VivBackbone.full_viv_best_watch_m6_body⟩
      , ⟨"full_viv_simplify_m6", [i64, i32], [i64], FullM6VivBackbone.full_viv_simplify_m6_body⟩
      , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64],
          FullM6VivBackbone.full_viv_commit_m6_body⟩
      , ⟨"full_viv_mark_garb_m6", [i64, i32], [], FullM6VivBackbone.full_viv_mark_garb_m6_body⟩
      , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_subsumes_bin_m6_body⟩
      , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_subsumes_cl_m6_body⟩
      , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32],
          FullM6VivBackbone.full_viv_deduce_m6_body⟩
      , ⟨"full_viv_best_implied_m6", [i64, i32], [i32],
          FullM6VivBackbone.full_viv_best_implied_m6_body⟩
      , ⟨"full_viv_reestablish_m6", [i64, i32], [],
          FullM6VivBackbone.full_viv_reestablish_m6_body⟩
      , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_inst_check_m6_body⟩
      , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], FullM6VivBackbone.full_viv_inst_m6_body⟩
      , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
          FullM6VivBackbone.full_viv_finish_m6_body⟩
      , ⟨"full_viv_sort_counts_m6", [i64, i32], [],
          FullM6VivBackbone.full_viv_sort_counts_m6_body⟩
      , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], FullM6VivBackbone.full_viv_has_l0_m6_body⟩
      , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], FullM6VivBackbone.full_viv_l0_simp_m6_body⟩
      , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [],
          FullM6VivBackbone.full_viv_reuse_prefix_m6_body⟩
      , ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.full_viv_clause_m6_body⟩
      , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
          FullM6VivBackbone.full_viv_tier_match_m6_body⟩
      , ⟨"full_viv_collect_m6", [i64, i64], [i64], FullM6VivBackbone.full_viv_collect_m6_body⟩
      , ⟨"full_viv_count_m6", [i64, i64], [], FullM6VivBackbone.full_viv_count_m6_body⟩
      , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.full_viv_keys_m6_body⟩
      , ⟨"full_viv_sort_sched_m6", [i64, i64], [], FullM6VivBackbone.full_viv_sort_sched_m6_body⟩
      , ⟨"full_viv_clear_tier_m6", [i64, i64], [], FullM6VivBackbone.full_viv_clear_tier_m6_body⟩
      , ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullM6VivBackbone.full_vivify_m6_body⟩ ] := rfl
  have er := envRowAt hnd hown
  have rBt := envRow_mem hnd _ _ _ _ hBt; have rUnw := envRow_mem hnd _ _ _ _ hUnw
  have rAu := envRow_mem hnd _ _ _ _ hAu; have rAb6 := envRow_mem hnd _ _ _ _ hAb6
  have rWp := envRow_mem hnd _ _ _ _ hWp; have rAsg := envRow_mem hnd _ _ _ _ hAsg
  have rPI := m7_fullPropagateIgn_to_del (envRow_mem hnd _ _ _ _ hPIgn)
  have rNext := envRow_mem hnd _ _ _ _ hNext
  have r0 := er 0 rfl (fun _ _ _ _ h => h); have r2 := er 2 rfl (fun _ _ _ _ h => h)
  have r4 := er 4 rfl (fun _ _ _ _ h => h); have r8 := er 8 rfl (fun _ _ _ _ h => h)
  have r19 := er 19 rfl (fun _ _ _ _ h => h)
  rw [hfn]; unfold p2VivBb1Rows
  exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_viv_unreason_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_watch_rank_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_watch_m6_wp (Env.ofTable tbl)
        (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_simplify_m6_wp (Env.ofTable tbl)
        rUnw rAu rAb6 rWp)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_commit_m6_wp (Env.ofTable tbl)
        rBt rUnw rAu rAb6 rWp r0 r2)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_mark_garb_m6_wp (Env.ofTable tbl) r0 rUnw)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_bin_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_cl_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_deduce_m6_wp (Env.ofTable tbl)
        (er 6 rfl (fun _ _ _ _ h => h)) (er 7 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_implied_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reestablish_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_check_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_m6_del_wp (Env.ofTable tbl)
        rBt rAsg rPI r8 (er 11 rfl (fun _ _ _ _ h => h)) r4)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_finish_m6_wp (Env.ofTable tbl)
        r8 (er 5 rfl (fun _ _ _ _ h => h)) rBt r4 (er 10 rfl (fun _ _ _ _ h => h))
        (er 12 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_counts_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_has_l0_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_l0_simp_m6_wp (Env.ofTable tbl)
        (er 15 rfl (fun _ _ _ _ h => h)) rBt (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reuse_prefix_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clause_m6_del_wp (Env.ofTable tbl)
        (er 16 rfl (fun _ _ _ _ h => h)) (er 14 rfl (fun _ _ _ _ h => h))
        (er 17 rfl (fun _ _ _ _ h => h)) (er 9 rfl (fun _ _ _ _ h => h)) rAsg rPI rBt
        (er 13 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_tier_match_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_collect_m6_wp (Env.ofTable tbl) rNext r19)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_count_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_keys_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_sched_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clear_tier_m6_wp (Env.ofTable tbl) rNext r19)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_vivify_m6_del_wp (Env.ofTable tbl)
        rBt (er 20 rfl (fun _ _ _ _ h => h)) (er 21 rfl (fun _ _ _ _ h => h))
        (er 22 rfl (fun _ _ _ _ h => h)) (er 23 rfl (fun _ _ _ _ h => h))
        (er 18 rfl (fun _ _ _ _ h => h))
        (m7_fullPropagate_to_del (envRow_mem hnd _ _ _ _ hProp))
        (er 24 rfl (fun _ _ _ _ h => h))), trivial ⟩

private theorem p2VivBb2_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p2VivBb2Rows, e ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAu : (⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ : SpecEntry) ∈ tbl)
    (hDbs : (⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩ :
      SpecEntry) ∈ tbl)
    (hDef : (⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p2VivBb2Fns p2VivBb2Rows := by
  have hfn : p2VivBb2Fns =
      [ ⟨"full_prioritize_binaries_m6", [i64], [.bool],
          FullM6VivBackbone.full_prioritize_binaries_m6_body⟩
      , ⟨"full_backbone_sched_m6", [i64], [i64], FullM6VivBackbone.full_backbone_sched_m6_body⟩
      , ⟨"full_backbone_keep_m6", [i64, i64], [], FullM6VivBackbone.full_backbone_keep_m6_body⟩
      , ⟨"full_backbone_unwind_m6", [i64, i64, i64], [],
          FullM6VivBackbone.full_backbone_unwind_m6_body⟩
      , ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool],
          FullM6VivBackbone.full_backbone_prop_m6_body⟩
      , ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32],
          FullM6VivBackbone.full_backbone_analyze_m6_body⟩
      , ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64],
          FullM6VivBackbone.full_backbone_round_m6_body⟩
      , ⟨"full_backbone_m6", [i64, i64], [i64], FullM6VivBackbone.full_backbone_m6_body⟩
      , ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], FullM6VivBackbone.full_trans_lit_m6_body⟩
      , ⟨"full_trans_sort_m6", [i64, i64], [], FullM6VivBackbone.full_trans_sort_m6_body⟩
      , ⟨"full_transitive_m6", [i64, i64], [i64], FullM6VivBackbone.full_transitive_m6_body⟩ ] :=
    rfl
  have er := envRowAt hnd hown
  have rBt := envRow_mem hnd _ _ _ _ hBt
  have rProp := m7_fullPropagate_to_del (envRow_mem hnd _ _ _ _ hProp)
  have rAu := envRow_mem hnd _ _ _ _ hAu; have r0 := er 0 rfl (fun _ _ _ _ h => h)
  rw [hfn]; unfold p2VivBb2Rows
  exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_prioritize_binaries_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_sched_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_keep_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_unwind_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_prop_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_analyze_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_round_m6_wp (Env.ofTable tbl)
        (er 4 rfl (fun _ _ _ _ h => h)) (er 5 rfl (fun _ _ _ _ h => h))
        (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_m6_del_wp (Env.ofTable tbl)
        rBt rProp rAu r0 (er 1 rfl (fun _ _ _ _ h => h)) (er 6 rfl (fun _ _ _ _ h => h))
        (er 2 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_trans_lit_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDbs) rAu)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_trans_sort_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_transitive_m6_del_wp (Env.ofTable tbl)
        rBt r0 (er 9 rfl (fun _ _ _ _ h => h)) (er 8 rfl (fun _ _ _ _ h => h)) rProp
        (envRow_mem hnd _ _ _ _ hDef)), trivial ⟩

private theorem p2RebuildWatches_impl {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hSwp : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p2RebuildWatchesFns p2RebuildWatchesRows := by
  have hfn : p2RebuildWatchesFns =
      [⟨"full_rebuild_watches", [i64], [i64], Full.full_rebuild_watches_body⟩] := by
    t_kernel_rfl
  have hrow : p2RebuildWatchesRows =
      [⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩] := rfl
  rw [hfn, hrow]
  have rSw := envRow_mem hnd _ _ _ _ hSwp
  have hwp := Full.full_rebuild_watches_wp (Env.ofTable tbl)
    (by
      rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm, hQ⟩
      exact rSw (c.hdr, ()) m Q X
        ⟨c, F0, Fc, s, R, rfl, hlen, hw, hnd0, hdm, hrm, hm,
          fun r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm' =>
            hQ r va fl lv rs tr tp te un uf wv ws ar al wl wu fr ni nr nb oo sc m'
              hl' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'⟩)
    (m7_fullPropagate_to_dw (envRow_mem hnd _ _ _ _ hProp))
  refine ⟨SpecEntry.Impl.of ?_, trivial⟩
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdn, hm, hQ⟩
  rcases hdn with ⟨⟨hlen, Fc, hw⟩, hlm, hnd0, hext, hcl0, _⟩
  exact hwp (c.hdr, ()) m Q X ⟨c, F0, Fc, s, R, rfl, hlen, hw, hlm, hnd0, hext, hcl0, hm,
    fun r s' m' hsp' _ hcl0' hr hu hfl _ _ _ _ _ hm' =>
      hQ r s' m' hsp' hcl0' hfl hr hu hm'⟩

/-- `AllFns Fn.Wf` for all `164` functions of `FullM7.m7FnsPart2`. -/
theorem m7FnsPart2_wf : AllFns Fn.Wf m7FnsPart2 :=
  FullM6Transport.allFns_of_mem fun f hf => FullM7.m7Fns_wf f (by
    unfold FullM7.m7Fns; exact List.mem_append_left _ (List.mem_append_right _ hf))

/-- Certifies all `164` functions of `FullM7.m7FnsPart2` against `m7RowsPart2 tPfx` in
`Env.ofTable tbl`, parameterized over `hGap : M7GapHyp` and `hCongDense` (discharged in
`FullM7OrchProof0`). -/
theorem m7RowsPart2_tableImpl {tPfx tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : m7OrchPfxFns.length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hc1 : M7Part1Callees tbl)
    (hGap : M7GapHyp (Env.ofTable tbl))
    (hCongDense : ∀ xs m Q X, FullM3CongBva.m3CongruenceDenseSpec xs m Q X →
      Func.wp (Env.ofTable tbl) FullM7.full_congruence_dense_body xs m Q X)
    (hOwn : ∀ e ∈ m7RowsPart2 tPfx, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7FnsPart2 (m7RowsPart2 tPfx) := by
  have hc2 := m7Part2Callees_of_sub hOwn
  have sub_alit : ∀ e ∈ p2AnalyzeLitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; exact List.mem_append_left _ h)
  have sub_arsn : ∀ e ∈ p2AnalyzeRsnRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; apply List.mem_append_right; exact List.mem_append_left _ h)
  have sub_ca : ∀ e ∈ p2ClearAnaRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 3 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ms0 : ∀ e ∈ p2MinShrink0Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 4 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_adp46 : ∀ e ∈ p2Adp46Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 5 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_otfs : ∀ e ∈ p2OtfsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 6 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_mm : ∀ e ∈ p2MinMarkRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 7 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_tl : ∀ e ∈ p2TmpLessRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 8 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_stm7 : ∀ e ∈ p2SortTmpM7Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ms1 : ∀ e ∈ p2MinShrink1Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_dnl : ∀ e ∈ p2DetNewLevelRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 12 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_olc : ∀ e ∈ p2OneLitConflRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 13 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_lrn : ∀ e ∈ p2Learn2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 14 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_m7ba : ∀ e ∈ p2M7BumpRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 15 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_rba : ∀ e ∈ p2RestoreBumpAnaM5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 16 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ana : ∀ e ∈ p2AnalyzeM5Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 17 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ndv : ∀ e ∈ p2NextDecVarRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 20 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wlk13 : ∀ e ∈ p2M7Walk13Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 22 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_rst : ∀ e ∈ p2RestartRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 26 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_hb : ∀ e ∈ p2HasBinRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 30 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_dbs : ∀ e ∈ p2DelBinSideRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 31 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ab6 : ∀ e ∈ p2AddBinM6Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 32 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_dbl : ∀ e ∈ p2DelBinToLuckyRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 34 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_hbr : ∀ e ∈ p2HbrDomRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 35 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ppl : ∀ e ∈ p2ProbePropLitRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 36 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_pp2 : ∀ e ∈ p2ProbePair2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 37 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_pap : ∀ e ∈ p2ProbeAssumePairRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 38 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bb1 : ∀ e ∈ p2VivBb1Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 40 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_adp1011 : ∀ e ∈ p2Adp1011Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 41 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bb2 : ∀ e ∈ p2VivBb2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 42 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_tpop : ∀ e ∈ p2TarjanPopSccRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 43 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_tscc : ∀ e ∈ p2TarjanSccRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 44 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_selim : ∀ e ∈ p2SubstElimVarsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 45 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_srew : ∀ e ∈ p2SubstRewriteRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 46 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cfind : ∀ e ∈ p2CongFindRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 49 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cmrg : ∀ e ∈ p2CongMergeRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 50 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cbva3 : ∀ e ∈ p2CongBva3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 51 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_su32 : ∀ e ∈ p2SortU32Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 53 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cd17 : ∀ e ∈ p2CongDense17Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 54 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cht : ∀ e ∈ p2CongHashRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 55 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cite : ∀ e ∈ p2CongIteRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart2; (iterate 56 apply List.mem_append_right); exact List.mem_append_left _ h)
  have rDef := htPfx _ hPfxSpecs.wstackDefrag
  have rWp := htPfx _ hPfxSpecs.watchPush
  have rSwpBins := htPfx _ hPfxSpecs.sweepBins
  have rArSwp := htPfx _ hPfxSpecs.arenaSweep
  have rMinShr := htPfx _ hPfxSpecs.minShrink
  have rDed1uip := htPfx _ hPfxSpecs.deduce1uip
  have rAnaCore := envRow_mem hnd _ _ _ _ (htPfx _ hPfxSpecs.analyzeCoreM6)
    (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have rAnaLit := sub_alit _ (List.mem_of_getElem? (i := 0) rfl)
  have rAnaRsn := sub_arsn _ (List.mem_of_getElem? (i := 0) rfl)
  have rClearAna := sub_ca _ (List.mem_of_getElem? (i := 0) rfl)
  have rSortAna := sub_ms0 _ (List.mem_of_getElem? (i := 1) rfl)
  have rBumpAna := sub_adp46 _ (List.mem_of_getElem? (i := 0) rfl)
  have rOtfsL := sub_otfs _ (List.mem_of_getElem? (i := 0) rfl)
  have rOtfsB := sub_otfs _ (List.mem_of_getElem? (i := 1) rfl)
  have rOtfsS := sub_otfs _ (List.mem_of_getElem? (i := 2) rfl)
  have rMinMark := sub_mm _ (List.mem_of_getElem? (i := 0) rfl)
  have rSortTmp := sub_stm7 _ (List.mem_of_getElem? (i := 3) rfl)
  have rDet := sub_dnl _ (List.mem_of_getElem? (i := 0) rfl)
  have rOneLit := sub_olc _ (List.mem_of_getElem? (i := 0) rfl)
  have rLrnCl := sub_lrn _ (List.mem_of_getElem? (i := 1) rfl)
  have rBumpM7 := sub_m7ba _ (List.mem_of_getElem? (i := 3) rfl)
  have rRstBump := sub_rba _ (List.mem_of_getElem? (i := 0) rfl)
  have rAnaM5 := sub_ana _ (List.mem_of_getElem? (i := 0) rfl)
  have rHb := sub_hb _ (List.mem_of_getElem? (i := 0) rfl)
  have rDbs := sub_dbs _ (List.mem_of_getElem? (i := 0) rfl)
  have rAddBinM6 := sub_ab6 _ (List.mem_of_getElem? (i := 0) rfl)
  have rHbr := sub_hbr _ (List.mem_of_getElem? (i := 0) rfl)
  have rPpl := sub_ppl _ (List.mem_of_getElem? (i := 0) rfl)
  have rPp := sub_pp2 _ (List.mem_of_getElem? (i := 0) rfl)
  have rFh := sub_pp2 _ (List.mem_of_getElem? (i := 1) rfl)
  have rPap := sub_pap _ (List.mem_of_getElem? (i := 0) rfl)
  have rVivCollect := sub_bb1 _ (List.mem_of_getElem? (i := 20) rfl)
  have rVivCount := sub_bb1 _ (List.mem_of_getElem? (i := 21) rfl)
  have rVivKeys := sub_bb1 _ (List.mem_of_getElem? (i := 22) rfl)
  have rVivSort := sub_bb1 _ (List.mem_of_getElem? (i := 23) rfl)
  have rVivClause := sub_bb1 _ (List.mem_of_getElem? (i := 18) rfl)
  have rVivClear := sub_bb1 _ (List.mem_of_getElem? (i := 24) rfl)
  have rVivTier := sub_adp1011 _ (List.mem_of_getElem? (i := 0) rfl)
  have rTpop := sub_tpop _ (List.mem_of_getElem? (i := 0) rfl)
  have rTscc := sub_tscc _ (List.mem_of_getElem? (i := 0) rfl)
  have rElim := sub_selim _ (List.mem_of_getElem? (i := 0) rfl)
  have rCfind := sub_cfind _ (List.mem_of_getElem? (i := 0) rfl)
  have rCmrg := sub_cmrg _ (List.mem_of_getElem? (i := 0) rfl)
  have rUf := sub_cbva3 _ (List.mem_of_getElem? (i := 1) rfl)
  have rEf := sub_cbva3 _ (List.mem_of_getElem? (i := 2) rfl)
  have rSu32 := sub_su32 _ (List.mem_of_getElem? (i := 0) rfl)
  have rHtern : (⟨"full_has_ternary", [i64, i32, i32, i32], [.bool],
      Full.fullHasTernarySpec, true⟩ : SpecEntry) ∈ tbl := hOwn _ (by
    unfold m7RowsPart2; (iterate 52 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7OrchPfxFns.drop off).take n) ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      ((m7OrchPfxFns.drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have i_alit := (fullSliceTransport 62 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_alit
    (fun _ h => nomatch h)).2
  have i_arsn : TableImpl (Env.ofTable tbl) p2AnalyzeRsnFns p2AnalyzeRsnRows :=
    m7_oneImpl rfl rfl (FullM5HeurCore.full_analyze_rsn_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rAnaLit))
  have i_ca := (fullSliceTransport 64 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_ca
    (fun _ h => nomatch h)).2
  have i_ms0 : TableImpl (Env.ofTable tbl) p2MinShrink0Fns p2MinShrink0Rows := by
    have hfn : p2MinShrink0Fns =
        [ ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], FullM6MinShrink.full_ana_sift_m6_body⟩
        , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.full_sort_ana_qs_m6_body⟩ ] :=
      rfl
    have r0 := envRowAt hnd sub_ms0 0 rfl (fun _ _ _ _ h => FullM6MinShrink.m6AnaSiftSpec_monoX h)
    rw [hfn]; unfold p2MinShrink0Rows
    exact ⟨ SpecEntry.Impl.of (FullM6MinShrink.full_ana_sift_m6_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullM6MinShrink.full_sort_ana_qs_m6_wp (Env.ofTable tbl) r0), trivial ⟩
  have i_adp46 : TableImpl (Env.ofTable tbl) p2Adp46Fns p2Adp46Rows := by
    have rBa := envRow_mem hnd _ _ _ _ rBumpAna (fun _ _ _ _ h => m6aBumpAnalyzedSpec_monoX h)
    have rCa := envRow_mem hnd _ _ _ _ rClearAna
    unfold p2Adp46Fns p2Adp46Rows
    exact ⟨ SpecEntry.Impl.of (full_bump_analyzed_m6_hdr_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc1.hdrDrAllow (fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h))
          (envRow_mem hnd _ _ _ _ rSortAna
            (fun _ _ _ _ h => FullM6MinShrink.m6SortAnaQsSpec_monoX h))
          (envRow_mem hnd _ _ _ _ hc1.bumpVar) (envRow_mem hnd _ _ _ _ hc1.queueMtf)
          (envRow_mem hnd _ _ _ _ hc1.bumpDecay))
      , SpecEntry.Impl.of (full_restore_bump_ana_m6_hdr_wp (Env.ofTable tbl) rBa rCa)
      , SpecEntry.Impl.of (full_ana_failed_lit_m6_hdr_wp (Env.ofTable tbl) rCa rBa
          (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ hc1.assignLvl))
      , trivial ⟩
  have i_otfs : TableImpl (Env.ofTable tbl) p2OtfsFns p2OtfsRows := by
    have hfn : p2OtfsFns =
        [ ⟨"full_otfs_large", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_large_body⟩
        , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_bin_m5_body⟩
        , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [],
            FullM5HeurCore.full_otfs_subsume_m5_body⟩ ] := by t_kernel_rfl
    rw [hfn]; unfold p2OtfsRows
    exact ⟨ SpecEntry.Impl.of (FullM5Otfs.full_otfs_large_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ rDef) (envRow_mem hnd _ _ _ _ hc1.unwatchLarge)
          (envRow_mem hnd _ _ _ _ rWp))
      , SpecEntry.Impl.of (FullM5Otfs.full_otfs_bin_m5_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc1.arenaNext) (envRow_mem hnd _ _ _ _ rDef)
          (envRow_mem hnd _ _ _ _ hc1.unwatchLarge) (envRow_mem hnd _ _ _ _ rWp))
      , SpecEntry.Impl.of (FullM5HeurCore.full_otfs_subsume_m5_wp (Env.ofTable tbl)), trivial ⟩
  have i_mm := (fullSliceTransport 69 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_mm
    (fun _ h => nomatch h)).2
  have i_tl := (fullSliceTransport 71 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_tl
    (fun _ h => nomatch h)).2
  have i_stm7 := p2SortTmpM7_impl hnd sub_stm7 hGap
  have i_ms1 := p2MinShrink1_impl hnd sub_ms1 rMinMark rSortTmp rAnaLit rAnaRsn rClearAna rOtfsL
    rOtfsB rOtfsS
  have i_dnl := (fullSliceTransport 77 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_dnl
    (fun _ h => nomatch h)).2
  have i_olc : TableImpl (Env.ofTable tbl) p2OneLitConflFns p2OneLitConflRows :=
    m7_oneImpl rfl rfl (FullM5Otfs.full_one_lit_confl_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rDef) (envRow_mem hnd _ _ _ _ rDet)
      (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ hc1.assignLvl)
      (envRow_mem hnd _ _ _ _ hc1.unwatchLarge) (envRow_mem hnd _ _ _ _ rWp))
  have i_lrn : TableImpl (Env.ofTable tbl) p2Learn2Fns p2Learn2Rows := by
    have hfn : p2Learn2Fns =
        [ ⟨"full_eager_subsume", [i64, i64], [], FullM5HeurCore.full_eager_subsume_m5_body⟩
        , ⟨"full_learn_clause", [i64, i64], [i64], FullM5HeurCore.full_learn_clause_m5_body⟩ ] :=
      by t_kernel_rfl
    rw [hfn]; unfold p2Learn2Rows
    exact ⟨ SpecEntry.Impl.of (FullM5HeurCore.full_eager_subsume_m5_wp (Env.ofTable tbl))
      , SpecEntry.Impl.of (FullM5HeurCore.full_learn_clause_m5_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ hc1.assignLvl)
          (envRow_mem hnd _ _ _ _ rDet) (envRow_mem hnd _ _ _ _ rDef)
          (envRow_mem hnd _ _ _ _ hc1.reduce) (envRow_mem hnd _ _ _ _ hc1.addClause)
          (envRowAt hnd sub_lrn 0 rfl (fun _ _ _ _ h => h))), trivial ⟩
  have i_m7ba := p2M7Bump_impl hnd sub_m7ba hc1.bumpVar hc1.bumpDecay hc1.queueMtf
  have i_rba : TableImpl (Env.ofTable tbl) p2RestoreBumpAnaM5Fns p2RestoreBumpAnaM5Rows :=
    m7_oneImpl rfl rfl (FullM5HeurCore.full_restore_bump_ana_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rBumpM7) (envRow_mem hnd _ _ _ _ rClearAna))
  have i_ana : TableImpl (Env.ofTable tbl) p2AnalyzeM5Fns p2AnalyzeM5Rows :=
    m7_oneImpl rfl rfl (FullM5HeurCore.full_analyze_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rOneLit) (envRow_mem hnd _ _ _ _ rDed1uip)
      (envRow_mem hnd _ _ _ _ rRstBump) (envRow_mem hnd _ _ _ _ rMinShr)
      (envRow_mem hnd _ _ _ _ hc1.tickRel) (envRow_mem hnd _ _ _ _ hc1.emaUpdate)
      (envRow_mem hnd _ _ _ _ rLrnCl))
  have i_adp7 : TableImpl (Env.ofTable tbl) p2Adp7Fns p2Adp7Rows :=
    m7_oneImpl rfl rfl (full_analyze_m6_hdr_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.hdrUpdateTier (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
      (envRow_mem hnd _ _ _ _ hc1.hdrDrUpdate (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)) rAnaCore)
  have i_ndv := (fullSliceTransport 83 1
    [⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩]
    (by t_kernel_rfl) (m7_mem1 (fullRow_at 19 _)) hnd sub_ndv (m7_mem1 hc1.heapPop)).2
  have i_hdec : TableImpl (Env.ofTable tbl) p2HdrDecideFns p2HdrDecideRows :=
    m7_oneImpl rfl rfl (FullM6Hdr.m6_hdr_decide_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc2.nextDecVar) (envRow_mem hnd _ _ _ _ hc1.assign)
      (envRow_mem hnd _ _ _ _ hc1.hdrDrInit (fun _ _ _ _ h => FullM6Hdr.m6HdrDrMutSpec_monoX h)))
  have i_wlk13 := p2M7Walk13_impl hnd sub_wlk13 hc1.rngNext hc1.arenaNext hc2.nextDecVar
    hc1.assign hc1.propagate hc1.backtrack
  have i_wlkc : TableImpl (Env.ofTable tbl) p2WalkCanonFns p2WalkCanonRows := by
    have hfn : p2WalkCanonFns =
        [ ⟨"full_warmup", [i64], [], FullM7Walk.full_warmup_m7_body⟩
        , ⟨"full_walk", [i64], [], FullM7Walk.full_walk_warmup_m7_body⟩ ] := rfl
    have er := envRowAt hnd sub_wlk13
    rw [hfn]; unfold p2WalkCanonRows
    exact ⟨ SpecEntry.Impl.of (FullM7Walk.full_warmup_m7_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc2.nextDecVar) (envRow_mem hnd _ _ _ _ hc1.assign)
          (envRow_mem hnd _ _ _ _ hc1.propagate) (envRow_mem hnd _ _ _ _ hc1.backtrack))
      , SpecEntry.Impl.of (FullM7Walk.full_walk_warmup_m7_wp (Env.ofTable tbl)
          (er 11 rfl (fun _ _ _ _ h => h)) (er 10 rfl (fun _ _ _ _ h => h))), trivial ⟩
  have i_reph : TableImpl (Env.ofTable tbl) p2RephaseM7Fns p2RephaseM7Rows :=
    m7_oneImpl rfl rfl hGap.rephase
  have i_rstd : TableImpl (Env.ofTable tbl) p2RestartDueFns p2RestartDueRows :=
    m7_oneImpl rfl rfl (FullM5Sched.full_restart_due_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.ilog10))
  have i_rst := (fullSliceTransport 93 1
    [ ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
    , ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ ]
    (by t_kernel_rfl) (m7_memC (fullRow_at 30 _) (m7_mem1 (fullRow_at 83 _)))
    hnd sub_rst (m7_memC hc1.backtrack (m7_mem1 hc2.nextDecVar))).2
  have i_ep2 : TableImpl (Env.ofTable tbl) p2CfExtendPush2Fns p2CfExtendPush2Rows :=
    m7_oneImpl rfl rfl (FullM6CompactFlush.full_extend_push2_m6cf_tmk_wp (Env.ofTable tbl))
  have i_epc : TableImpl (Env.ofTable tbl) p2CfExtendPushClFns p2CfExtendPushClRows :=
    m7_oneImpl rfl rfl (FullM6CompactFlush.full_extend_push_cl_m6cf_tmk_wp (Env.ofTable tbl))
  have i_ext : TableImpl (Env.ofTable tbl) p2ExtendFns p2ExtendRows :=
    m7_oneImpl rfl rfl (FullM4.m4_extend_wp (Env.ofTable tbl))
  have i_hb := (fullSliceTransport 97 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_hb
    (fun _ h => nomatch h)).2
  have i_dbs := (fullSliceTransport 99 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_dbs
    (fun _ h => nomatch h)).2
  have i_ab6 : TableImpl (Env.ofTable tbl) p2AddBinM6Fns p2AddBinM6Rows :=
    m7_oneImpl rfl rfl (FullM6VivBackbone.full_add_bin_m6_ext_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rHb) (envRow_mem hnd _ _ _ _ hc1.assignLvl)
      (envRow_mem hnd _ _ _ _ rWp))
  have i_adp9 : TableImpl (Env.ofTable tbl) p2Adp9Fns p2Adp9Rows :=
    m7_oneImpl rfl rfl (full_add_bin_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ rAddBinM6))
  have i_dbl := (fullSliceTransport 100 6
    [ ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
    , ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩
    , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
    , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
    , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
    , ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩ ]
    (by t_kernel_rfl)
    (m7_memC (fullRow_at 11 _) <| m7_memC (fullRow_at 27 _) <| m7_memC (fullRow_at 28 _) <|
      m7_memC (fullRow_at 30 _) <| m7_memC (fullRow_at 49 _) <| m7_memC (fullRow_at 82 _) <|
      m7_mem1 (fullRow_at 99 _))
    hnd sub_dbl
    (m7_memC hc1.arenaNext <| m7_memC hc1.assignLvl <| m7_memC hc1.assign <|
      m7_memC hc1.backtrack <| m7_memC hc1.propagate <| m7_memC rAnaM5 <| m7_mem1 rDbs)).2
  have i_hbr : TableImpl (Env.ofTable tbl) p2HbrDomFns p2HbrDomRows :=
    m7_oneImpl rfl rfl (FullM5Hbr.full_hbr_dom_m5_wp (Env.ofTable tbl))
  have i_ppl : TableImpl (Env.ofTable tbl) p2ProbePropLitFns p2ProbePropLitRows :=
    m7_oneImpl rfl rfl (FullM5ProbeProp.full_probe_prop_lit_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.findRepl) (envRow_mem hnd _ _ _ _ rWp)
      (envRow_mem hnd _ _ _ _ rHbr) (envRow_mem hnd _ _ _ _ hc1.assignLvl))
  have i_pp2 := (fullSliceTransport 108 2
    [ ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
    , ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩
    , ⟨"full_probe_prop_lit", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩ ]
    (by t_kernel_rfl)
    (m7_memC (fullRow_at 49 _) <| m7_memC (fullRow_at 98 _) <| m7_mem1 (fullRow_at 107 _))
    hnd sub_pp2 (m7_memC hc1.propagate <| m7_memC hc2.addBin <| m7_mem1 rPpl)).2
  have i_pap : TableImpl (Env.ofTable tbl) p2ProbeAssumePairFns p2ProbeAssumePairRows :=
    m7_oneImpl rfl rfl (FullM6VivBackbone.full_probe_assume_pair_m6_canon_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.assign) (envRow_mem hnd _ _ _ _ rPp)
      (envRow_mem hnd _ _ _ _ hc1.backtrack) (m6_analyze_to_20 (envRow_mem hnd _ _ _ _ rAnaM5))
      (envRow_mem hnd _ _ _ _ hc1.propagate) (envRow_mem hnd _ _ _ _ rFh)
      (envRow_mem hnd _ _ _ _ hc2.addUnit))
  have i_prun : TableImpl (Env.ofTable tbl) p2ProbeRunFns p2ProbeRunRows :=
    m7_oneImpl rfl rfl (FullM3Backbone.m3_probe_run_cursor_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ rPap))
  have i_bb1 := p2VivBb1_impl hnd sub_bb1 hc1.backtrack hc1.unwatchLarge hc2.addUnit
    rAddBinM6 rWp hc1.assign hc1.propagateIgn hc1.arenaNext hc1.propagate
  have i_adp1011 : TableImpl (Env.ofTable tbl) p2Adp1011Fns p2Adp1011Rows := by
    have rBt := envRow_mem hnd _ _ _ _ hc1.backtrack
    unfold p2Adp1011Fns p2Adp1011Rows
    exact ⟨ SpecEntry.Impl.of (full_vivify_tier_m6_hdr_wp (Env.ofTable tbl) rBt
          (envRow_mem hnd _ _ _ _ rVivCollect) (envRow_mem hnd _ _ _ _ rVivCount)
          (envRow_mem hnd _ _ _ _ rVivKeys) (envRow_mem hnd _ _ _ _ rVivSort)
          (envRow_mem hnd _ _ _ _ rVivClause)
          (m7_fullPropagate_to_bcpS15 (envRow_mem hnd _ _ _ _ hc1.propagate))
          (envRow_mem hnd _ _ _ _ rVivClear))
      , SpecEntry.Impl.of (full_vivify_m6_hdr_wp (Env.ofTable tbl) rBt
          (envRow_mem hnd _ _ _ _ hc1.hdrSyncLegacy (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
          (envRow_mem hnd _ _ _ _ hc1.hdrGetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
          (envRow_mem hnd _ _ _ _ rVivTier (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)))
      , trivial ⟩
  have i_bb2 := p2VivBb2_impl hnd sub_bb2 hc1.backtrack hc1.propagate hc2.addUnit rDbs rDef
  have i_tpop := (fullSliceTransport 120 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    sub_tpop (fun _ h => nomatch h)).2
  have i_tscc : TableImpl (Env.ofTable tbl) p2TarjanSccFns p2TarjanSccRows :=
    m7_oneImpl rfl rfl (FullM6CongSubst.full_tarjan_scc_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rTpop))
  have i_selim : TableImpl (Env.ofTable tbl) p2SubstElimVarsFns p2SubstElimVarsRows :=
    m7_oneImpl rfl rfl (Full.full_subst_elim_vars_bridge_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc2.addUnit) (envRow_mem hnd _ _ _ _ hc1.propagate)
      (m6_extend_push2_tmk_to_canon (envRow_mem hnd _ _ _ _ hc2.extendPush2))
      (envRow_mem hnd _ _ _ _ hc2.setInactive))
  have i_srew : TableImpl (Env.ofTable tbl) p2SubstRewriteFns p2SubstRewriteRows := by
    have hfn : p2SubstRewriteFns =
        [ ⟨"full_subst_rewrite_bins", [i64], [.bool], FullM6CongSubst.full_subst_rewrite_bins_body⟩
        , ⟨"full_subst_rewrite_ar", [i64], [.bool], FullM6CongSubst.full_subst_rewrite_ar_body⟩
        , ⟨"full_substitute", [i64], [i64], FullM6CongSubst.full_substitute_body⟩ ] := rfl
    have er := envRowAt hnd sub_srew
    have rAuM := envRow_mem hnd _ _ _ _ hc2.addUnit
    have rAb := m6_add_bin_m6_to_canon (envRow_mem hnd _ _ _ _ hc2.addBin)
    rw [hfn]; unfold p2SubstRewriteRows
    exact ⟨ SpecEntry.Impl.of (FullM6CongSubst.full_subst_rewrite_bins_wp (Env.ofTable tbl)
          rAuM rAb)
      , SpecEntry.Impl.of (FullM6CongSubst.full_subst_rewrite_ar_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc1.arenaNext) rAuM rAb)
      , SpecEntry.Impl.of (FullM6CongSubst.full_substitute_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ rTscc)
          (envRow_mem hnd _ _ _ _ rElim) (er 0 rfl (fun _ _ _ _ h => h))
          (er 1 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ rArSwp)
          (envRow_mem hnd _ _ _ _ hc1.propagate)), trivial ⟩
  have i_ed : TableImpl (Env.ofTable tbl) p2CfEnterDenseFns p2CfEnterDenseRows :=
    m7_oneImpl rfl rfl (FullM6CompactFlush.full_enter_dense_m6cf_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc1.backtrack) (envRow_mem hnd _ _ _ _ hc1.flushTrail)
      (envRow_mem hnd _ _ _ _ rSwpBins) (envRow_mem hnd _ _ _ _ rWp)
      (envRow_mem hnd _ _ _ _ rArSwp) (envRow_mem hnd _ _ _ _ hc1.arenaNext))
  have i_reb := p2RebuildWatches_impl hnd rArSwp hc1.propagate
  have i_cfind := (fullSliceTransport 128 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    sub_cfind (fun _ h => nomatch h)).2
  have i_cmrg : TableImpl (Env.ofTable tbl) p2CongMergeFns p2CongMergeRows :=
    m7_oneImpl rfl rfl (FullM6CongSubst.full_cong_merge_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rCfind) (m6_add_bin_to_cong (envRow_mem hnd _ _ _ _ hc2.addBin)))
  have i_cbva3 := (modTakeSliceTransport FullM3CongBva.m3_moduleOk FullM3CongBva.m3SpecTable_nodup
    (by t_kernel_rfl) 0 3 (by decide)
    [ FullM3CongBva.m3SpecTable[11]'(by decide)
    , FullM3CongBva.m3SpecTable[12]'(by decide)
    , FullM3CongBva.m3SpecTable[14]'(by decide) ]
    (by t_kernel_rfl)
    (m7_memC (List.getElem_mem _) (m7_memC (List.getElem_mem _) (m7_mem1 (List.getElem_mem _))))
    hnd sub_cbva3 (m7_memC rCfind (m7_memC rCmrg (m7_mem1 hc2.addUnit)))).2
  have i_htern : TableImpl (Env.ofTable tbl) p2HasTernaryFns p2HasTernaryRows :=
    m7_oneImpl rfl rfl (FullM4InprocHot.full_has_ternary_m4_wp (Env.ofTable tbl))
  have i_su32 : TableImpl (Env.ofTable tbl) p2SortU32Fns p2SortU32Rows :=
    m7_oneImpl rfl rfl (FullM7AnalyzeSort.full_sort_u32_m7_canonical_wp (Env.ofTable tbl))
  have i_cd17 := p2CongDense17_impl hnd sub_cd17 rHtern rSu32 rHb hc1.arenaNext hc2.addBin
    hc2.addUnit rUf rEf rCfind
  have i_cht := p2CongHash_impl hnd sub_cht
  have i_cite := p2CongIte_impl hnd sub_cite
  have i_cdend : TableImpl (Env.ofTable tbl) p2CongDenseEndFns p2CongDenseEndRows :=
    m7_oneImpl rfl rfl hCongDense
  rw [p2Fns_eq]; unfold p2FnsSeg m7RowsPart2
  refine tableImpl_append rfl i_alit (tableImpl_append rfl i_arsn ?_)
  refine tableImpl_append (hlen_p 10 1) (ps 10 1) (tableImpl_append rfl i_ca ?_)
  refine tableImpl_append rfl i_ms0 (tableImpl_append rfl i_adp46 ?_)
  refine tableImpl_append rfl i_otfs (tableImpl_append rfl i_mm (tableImpl_append rfl i_tl ?_))
  refine tableImpl_append rfl i_stm7 (tableImpl_append rfl i_ms1 (tableImpl_append (hlen_p 11 3)
    (ps 11 3) ?_))
  refine tableImpl_append rfl i_dnl (tableImpl_append rfl i_olc (tableImpl_append rfl i_lrn ?_))
  refine tableImpl_append rfl i_m7ba (tableImpl_append rfl i_rba (tableImpl_append rfl i_ana ?_))
  refine tableImpl_append (hlen_p 14 1) (ps 14 1) (tableImpl_append rfl i_adp7 ?_)
  refine tableImpl_append rfl i_ndv (tableImpl_append rfl i_hdec (tableImpl_append rfl i_wlk13 ?_))
  refine tableImpl_append rfl i_wlkc (tableImpl_append rfl i_reph (tableImpl_append rfl i_rstd ?_))
  refine tableImpl_append rfl i_rst (tableImpl_append rfl i_ep2 (tableImpl_append rfl i_epc ?_))
  refine tableImpl_append rfl i_ext (tableImpl_append rfl i_hb (tableImpl_append rfl i_dbs ?_))
  refine tableImpl_append rfl i_ab6 (tableImpl_append rfl i_adp9 (tableImpl_append rfl i_dbl ?_))
  refine tableImpl_append rfl i_hbr (tableImpl_append rfl i_ppl (tableImpl_append rfl i_pp2 ?_))
  refine tableImpl_append rfl i_pap (tableImpl_append rfl i_prun (tableImpl_append rfl i_bb1 ?_))
  refine tableImpl_append rfl i_adp1011 (tableImpl_append rfl i_bb2 ?_)
  refine tableImpl_append rfl i_tpop (tableImpl_append rfl i_tscc (tableImpl_append rfl i_selim ?_))
  refine tableImpl_append rfl i_srew (tableImpl_append rfl i_ed (tableImpl_append rfl i_reb ?_))
  refine tableImpl_append rfl i_cfind (tableImpl_append rfl i_cmrg ?_)
  refine tableImpl_append rfl i_cbva3 (tableImpl_append rfl i_htern ?_)
  refine tableImpl_append rfl i_su32 (tableImpl_append rfl i_cd17 (tableImpl_append rfl i_cht ?_))
  exact tableImpl_append rfl i_cite i_cdend

/-- Part 2 row memberships required by the `5`-fn orchestration tail (`FullM7OrchProof0`). -/
structure M7Part2TailCallees (tbl : List SpecEntry) : Prop where
  analyzeM6 : (⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tbl
  restartDue :
    (⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩ : SpecEntry) ∈ tbl
  restart : (⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩ : SpecEntry) ∈ tbl
  rephase : (⟨"full_rephase", [i64], [], m7RephaseSpec, true⟩ : SpecEntry) ∈ tbl
  hdrDecide :
    (⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ : SpecEntry) ∈ tbl
  extend : (⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩ : SpecEntry) ∈ tbl

theorem m7Part2TailCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart2 tPfx, e ∈ tbl) : M7Part2TailCallees tbl := by
  refine ⟨ hsub _ ?_, hsub _ ?_, hsub _ ?_, hsub _ ?_, hsub _ ?_, hsub _ ?_ ⟩
  · unfold m7RowsPart2; (iterate 19 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_cons_self
  · unfold m7RowsPart2; (iterate 25 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_cons_self
  · unfold m7RowsPart2; (iterate 26 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_of_getElem? (i := 0) rfl
  · unfold m7RowsPart2; (iterate 24 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_cons_self
  · unfold m7RowsPart2; (iterate 21 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_cons_self
  · unfold m7RowsPart2; (iterate 29 apply List.mem_append_right); apply List.mem_append_left
    exact List.mem_cons_self

/-- Congruence dense `[275]` callee memberships in `tbl` needed by `FullM7OrchProof0`. -/
structure M7Part2CongCallees (tbl : List SpecEntry) : Prop where
  extBin : (⟨"full_cong_extract_binaries", [i64, i64], [i64],
    FullM6CongSubst.m6CongExtractBinariesSpec, true⟩ : SpecEntry) ∈ tbl
  findUE : (⟨"full_cong_find_units_equivs", [i64], [i64],
    FullM6CongSubst.m6CongFindUnitsEquivsSpec, true⟩ : SpecEntry) ∈ tbl
  extract : (⟨"full_cong_extract", [i64, i64, i64], [i64],
    FullM6CongSubst.m6CongExtractSpec, true⟩ : SpecEntry) ∈ tbl
  iteAll : (⟨"full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32],
    FullM7CongIte.m7ExtractIteAllM6Spec, true⟩ : SpecEntry) ∈ tbl
  work : (⟨"full_cong_worklist", [i64, i64, i64, i64], [i64],
    FullM6CongSubst.m6CongWorklistSpec, true⟩ : SpecEntry) ∈ tbl
  fwdSub : (⟨"full_cong_fwd_subsume", [i64, i64], [i64],
    FullM6CongSubst.m6CongFwdSubsumeSpec, true⟩ : SpecEntry) ∈ tbl

theorem m7Part2CongCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart2 tPfx, e ∈ tbl) : M7Part2CongCallees tbl := by
  have sub_cd17 : ∀ e ∈ p2CongDense17Rows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 54 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_cite : ∀ e ∈ p2CongIteRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart2; (iterate 56 apply List.mem_append_right); exact List.mem_append_left _ h)
  exact ⟨ sub_cd17 _ (List.mem_of_getElem? (i := 7) rfl)
    , sub_cd17 _ (List.mem_of_getElem? (i := 8) rfl)
    , sub_cd17 _ (List.mem_of_getElem? (i := 9) rfl)
    , sub_cite _ (List.mem_of_getElem? (i := 6) rfl)
    , sub_cd17 _ (List.mem_of_getElem? (i := 15) rfl)
    , sub_cd17 _ (List.mem_of_getElem? (i := 16) rfl) ⟩

theorem m7RowsPart2_tPfx_mem {tPfx : List SpecEntry} {i : Nat}
    (h10 : 10 ≤ i) (hi : i < 15) (hit : i < tPfx.length) :
    tPfx[i] ∈ m7RowsPart2 tPfx := by
  unfold m7RowsPart2
  rcases Nat.lt_or_ge i 11 with h11 | h11
  · (iterate 2 apply List.mem_append_right); apply List.mem_append_left
    exact m7_mem_drop_take_of_lt tPfx h10 h11 hit
  · rcases Nat.lt_or_ge i 14 with h14 | h14
    · (iterate 11 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tPfx h11 h14 hit
    · (iterate 18 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tPfx h14 (by omega) hit

end LeanQbe.T.Examples.Kissat.FullM7Proof
