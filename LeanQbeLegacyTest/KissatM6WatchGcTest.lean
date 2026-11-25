module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6WatchGc
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification and Axiom Audit for Kissat M6 Watch-GC Slice

1. Executable `#guard` checks on `m6WatchGc_fns` (`17` overrides) and `m6WatchGcExterns` (`8`
   externs), signature parity, `checkAcyclic`, `PrintCpp`, `PrintQbe`, and `Legal` lowering
   across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. Direct `Func.Wf`, closed `ModuleOk` (`m6WatchGc_moduleOk`), `noExit` (`m6WatchGc_noExit`),
   and canonical `Func.wp` certification (`full_wstack_defrag_m6_wp`, `full_watch_push_m6_wp`,
   `full_lit_rank_m6_wp`, `full_sweep_bins_m6_wp`, `full_rewatch_arena_m6_wp`,
   `full_arena_sweep_m6_wp`, `full_mark_reasons_m6_wp`, `full_flush_trail_m6_wp`,
   `full_parse_body_m6_wp`, `full_extend_push2_m6_wp`, `full_extend_push_cl_m6_wp`).
3. Concrete `Mem 64` UNSAT soundness/non-vacuity (`nv_m6_watch_gc_sound`, `XPost := False`).
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM6WatchGcTest

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6WatchGc

#guard m6WatchGc_fns.length == 17
#guard m6WatchGcExterns.length == 8
#guard full_wstack_radix_sort_m6.name == "full_wstack_radix_sort_m6"
#guard full_wstack_radix_sort_m6.as == [i64, i64, i64, i64, i64, i64]
#guard full_wstack_radix_sort_m6.rs == []
#guard full_wstack_defrag_m6.name == "full_wstack_defrag_m6"
#guard full_wstack_defrag_m6.as == [i64]
#guard full_wstack_defrag_m6.rs == []
#guard full_watch_push_m6.name == "full_watch_push_m6"
#guard full_watch_push_m6.as == [i64, i32, i32, i32, i32]
#guard full_watch_push_m6.rs == [.bool]
#guard full_lit_rank_m6.name == "full_lit_rank_m6"
#guard full_lit_rank_m6.as == [i64, i64, i32]
#guard full_lit_rank_m6.rs == [i64]
#guard full_sweep_bins_range_m6.name == "full_sweep_bins_range_m6"
#guard full_sweep_bins_range_m6.as == [i64, i64]
#guard full_sweep_bins_range_m6.rs == []
#guard full_sweep_bins_m6.name == "full_sweep_bins_m6"
#guard full_sweep_bins_m6.as == [i64]
#guard full_sweep_bins_m6.rs == []
#guard full_rewatch_range_m6.name == "full_rewatch_range_m6"
#guard full_rewatch_range_m6.as == [i64, i64, i64]
#guard full_rewatch_range_m6.rs == [.bool]
#guard full_rewatch_arena_m6.name == "full_rewatch_arena_m6"
#guard full_rewatch_arena_m6.as == [i64, i64]
#guard full_rewatch_arena_m6.rs == [.bool]
#guard full_move_red_pass2_m6.name == "full_move_red_pass2_m6"
#guard full_move_red_pass2_m6.as == [i64, i64, i64, i64, i64]
#guard full_move_red_pass2_m6.rs == []
#guard full_move_red_end_buf_m6.name == "full_move_red_end_buf_m6"
#guard full_move_red_end_buf_m6.as == [i64, i64, i64, i64]
#guard full_move_red_end_buf_m6.rs == []
#guard full_move_red_end_m6.name == "full_move_red_end_m6"
#guard full_move_red_end_m6.as == [i64, i64, i64]
#guard full_move_red_end_m6.rs == []
#guard full_arena_sweep_m6.name == "full_arena_sweep_m6"
#guard full_arena_sweep_m6.as == [i64]
#guard full_arena_sweep_m6.rs == [i64]
#guard full_mark_reasons_m6.name == "full_mark_reasons_m6"
#guard full_mark_reasons_m6.as == [i64, .bool]
#guard full_mark_reasons_m6.rs == []
#guard full_flush_trail_m6.name == "full_flush_trail_m6"
#guard full_flush_trail_m6.as == [i64]
#guard full_flush_trail_m6.rs == [i64]
#guard full_parse_body_m6.name == "full_parse_body_m6"
#guard full_parse_body_m6.as == [i64, i64]
#guard full_parse_body_m6.rs == [i64]
#guard full_extend_push2_m6.name == "full_extend_push2_m6"
#guard full_extend_push2_m6.as == [i64, i32, i32]
#guard full_extend_push2_m6.rs == [.bool]
#guard full_extend_push_cl_m6.name == "full_extend_push_cl_m6"
#guard full_extend_push_cl_m6.as == [i64, i32, i32]
#guard full_extend_push_cl_m6.rs == [.bool]
#guard m6WatchGcModule.checkAcyclic == true
#guard (ppTModule m6WatchGcModule).isOk
#guard (PrintQbe.module m6WatchGcModule).isOk
#guard (ppModule (m6WatchGc_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6WatchGc_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6WatchGc_fns.map (Fn.legal .x64AVX2))).isOk

theorem m6WatchGc_fns_wf_ok : ∀ f ∈ m6WatchGc_fns, f.Wf :=
  m6WatchGc_fns_wf

theorem m6WatchGc_acyclic_ok : m6WatchGcModule.checkAcyclic = true :=
  m6WatchGc_acyclic

theorem m6WatchGc_noExit_ok :
    ∀ f as bs xs m Q X X',
      m6WatchGcEnv f as bs xs m Q X → m6WatchGcEnv f as bs xs m Q X' :=
  m6WatchGc_noExit

theorem m6WatchGc_moduleOk_ok : ModuleOk m6WatchGcEnv m6WatchGcModule :=
  m6WatchGc_moduleOk

theorem nv_m6_watch_gc_sound_ok :
    Func.wp m6WatchGcEnv full_flush_trail_m6_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m6_watch_gc_sound

theorem full_wstack_defrag_m6_ok (Γ : Env)
    (hSift : ∀ a m Q X, fullWsortSiftSpec a m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] a m Q X)
    (hRadix : ∀ a m Q X, fullWstackRadixSortSpec a m Q X →
      Γ "full_wstack_radix_sort_m6" [i64, i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X → Func.wp Γ full_wstack_defrag_m6_body a m Q X :=
  full_wstack_defrag_m6_wp Γ hSift hRadix

theorem full_watch_push_m6_ok (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    ∀ a m Q X, fullWatchPushSpec a m Q X → Func.wp Γ full_watch_push_m6_body a m Q X :=
  full_watch_push_m6_wp Γ hDefrag

theorem full_lit_rank_m6_ok (Γ : Env) :
    ∀ a m Q X, fullLitRankSpec a m Q X → Func.wp Γ full_lit_rank_m6_body a m Q X :=
  full_lit_rank_m6_wp Γ

theorem full_sweep_bins_m6_ok (Γ : Env)
    (hRange : ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Γ "full_sweep_bins_range_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_m6_body a m Q X :=
  full_sweep_bins_m6_wp Γ hRange

theorem full_rewatch_arena_m6_ok (Γ : Env)
    (hRange : ∀ a m Q X, fullRewatchRangeSpec a m Q X →
      Γ "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X → Func.wp Γ full_rewatch_arena_m6_body a m Q X :=
  full_rewatch_arena_m6_wp Γ hRange

theorem full_arena_sweep_m6_ok (Γ : Env)
    (hSweepB : ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Γ "full_sweep_bins_range_m6" [i64, i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hCopy : ∀ a m Q X, fullSweepCopySpec a m Q X →
      Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X)
    (hMove : ∀ a m Q X, fullMoveRedEndSpec a m Q X →
      Γ "full_move_red_end_m6" [i64, i64, i64] [] a m Q X)
    (hRewatch : ∀ a m Q X, fullRewatchRangeSpec a m Q X →
      Γ "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullArenaSweepSpec a m Q X → Func.wp Γ full_arena_sweep_m6_body a m Q X :=
  full_arena_sweep_m6_wp Γ hSweepB hNext hCopy hMove hRewatch

theorem full_mark_reasons_m6_ok (Γ : Env) :
    ∀ a m Q X, fullMarkReasonsSpec a m Q X → Func.wp Γ full_mark_reasons_m6_body a m Q X :=
  full_mark_reasons_m6_wp Γ

theorem full_flush_trail_m6_ok (Γ : Env)
    (hBack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullFlushTrailSpec a m Q X → Func.wp Γ full_flush_trail_m6_body a m Q X :=
  full_flush_trail_m6_wp Γ hBack hProp

theorem full_parse_body_m6_ok (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X →
      Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, m6IngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_m6_body a m Q X :=
  full_parse_body_m6_wp Γ hSkip hIngest hProp hSwc

theorem full_extend_push2_m6_ok (Γ : Env) :
    ∀ a m Q X, fullExtendPush2Spec a m Q X → Func.wp Γ full_extend_push2_m6_body a m Q X :=
  full_extend_push2_m6_wp Γ

theorem full_extend_push_cl_m6_ok (Γ : Env) :
    ∀ a m Q X, fullExtendPushClSpec a m Q X → Func.wp Γ full_extend_push_cl_m6_body a m Q X :=
  full_extend_push_cl_m6_wp Γ

end LeanQbeLegacyTest.KissatM6WatchGcTest

abbrev m6wg_fns_wf := @LeanQbeLegacyTest.KissatM6WatchGcTest.m6WatchGc_fns_wf_ok
abbrev m6wg_acyc := @LeanQbeLegacyTest.KissatM6WatchGcTest.m6WatchGc_acyclic_ok
abbrev m6wg_noex := @LeanQbeLegacyTest.KissatM6WatchGcTest.m6WatchGc_noExit_ok
abbrev m6wg_mod := @LeanQbeLegacyTest.KissatM6WatchGcTest.m6WatchGc_moduleOk_ok
abbrev m6wg_nv := @LeanQbeLegacyTest.KissatM6WatchGcTest.nv_m6_watch_gc_sound_ok
abbrev m6wg_defrag := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_wstack_defrag_m6_ok
abbrev m6wg_push := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_watch_push_m6_ok
abbrev m6wg_rank := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_lit_rank_m6_ok
abbrev m6wg_bins := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_sweep_bins_m6_ok
abbrev m6wg_rewatch := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_rewatch_arena_m6_ok
abbrev m6wg_sweep := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_arena_sweep_m6_ok
abbrev m6wg_reasons := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_mark_reasons_m6_ok
abbrev m6wg_flush := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_flush_trail_m6_ok
abbrev m6wg_parse := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_parse_body_m6_ok
abbrev m6wg_ext2 := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_extend_push2_m6_ok
abbrev m6wg_extcl := @LeanQbeLegacyTest.KissatM6WatchGcTest.full_extend_push_cl_m6_ok

#print axioms m6wg_fns_wf
#print axioms m6wg_acyc
#print axioms m6wg_noex
#print axioms m6wg_mod
#print axioms m6wg_nv
#print axioms m6wg_defrag
#print axioms m6wg_push
#print axioms m6wg_rank
#print axioms m6wg_bins
#print axioms m6wg_rewatch
#print axioms m6wg_sweep
#print axioms m6wg_reasons
#print axioms m6wg_flush
#print axioms m6wg_parse
#print axioms m6wg_ext2
#print axioms m6wg_extcl
