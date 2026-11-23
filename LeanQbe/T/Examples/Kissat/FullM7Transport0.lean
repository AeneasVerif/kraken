/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM6Transport0
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof3
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6S15Bridge
public import LeanQbe.T.Examples.Kissat.FullM7BumpProof
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM7SpecBridges
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` Unified `M7` Part 1 (`0..111`, `FullM7Transport0`)

Assembles `m7RowsPart1 tPfx` aligned 1-to-1 with `FullM7.m7FnsPart1`, defines the `21`-fn
`FullM6Orch` prefix contract `M7OrchPfxTblSpecs` (`m7OrchPfxFns`), `M7Part1Callees`, and the
explicit in-flight `FullM7BcpHot` hypothesis structure `M7BcpHotHyp` (`0` `sorry`/`axiom`), and
certifies all `112` functions of Part 1 (`Dimacs` through `full_reduce_m6`) in `Env.ofTable tbl`,
with plain `public section` and `0` `@[expose]` tags.
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
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6S15Bridge
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7

/-! ## 1. `M7` Orchestrator Prefix (`21` fns), Callee & `FullM7BcpHot` Contracts -/

/-- Exact `21`-function `FullM6Orch` prefix present in `FullM7.m7Fns` (drops `[15..17]`:
`full_walk`, `full_ema_swap_m6`, `full_switch_mode_m6`). -/
def m7OrchPfxFns : List Fn :=
  m6Orch_fns.take 15 ++ (m6Orch_fns.drop 18).take 6

theorem m7OrchPfxFns_eq :
    m7OrchPfxFns =
      [ m6oWstackDefragFn, m6oWatchPushFn, m6oRescaleFn, m6oParseBodyFn, m6oLitRankFn
      , m6oSweepBinsFn, m6oRewatchArenaFn, m6oArenaSweepFn, m6oMarkReasonsFn, m6oReduceM6Fn
      , m6oAnalyzeRsnM6HdrFn, m6oMinShrinkFn, m6oDeduce1uipFn, m6oDeduce1uipM6HdrFn
      , m6oAnalyzeCoreM6Fn, m6oSweepDenseM6Fn, m6oReorderM6Fn, m6oProbeTailM6Fn, m6oProbeM6Fn
      , m6oPreprocessM6Fn, m6oSimplifyM6Fn ] := by
  t_kernel_rfl

/-- Exact `SpecEntry` rows required on `tPfx` (`21` rows matching `m7OrchPfxFns`). -/
structure M7OrchPfxTblSpecs (tPfx : List SpecEntry) : Prop where
  wstackDefrag :
    (⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈ tPfx
  watchPush :
    (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tPfx
  rescale :
    (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tPfx
  parseBody :
    (⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩ : SpecEntry) ∈ tPfx
  litRank :
    (⟨"full_lit_rank", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tPfx
  sweepBins :
    (⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩ : SpecEntry) ∈ tPfx
  rewatchArena :
    (⟨"full_rewatch_arena", [i64, i64], [.bool],
      Full.fullRewatchArenaSpec, true⟩ : SpecEntry) ∈ tPfx
  arenaSweep :
    (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈ tPfx
  markReasons :
    (⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈ tPfx
  reduceM6 :
    (⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩ : SpecEntry) ∈ tPfx
  minShrink :
    (⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ : SpecEntry) ∈ tPfx
  deduce1uip :
    (⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ : SpecEntry) ∈ tPfx
  analyzeCoreM6 :
    (⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩ : SpecEntry) ∈ tPfx
  reorderM6 :
    (⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩ : SpecEntry) ∈ tPfx
  preprocessM6 :
    (⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩ : SpecEntry) ∈ tPfx
  simplifyM6 :
    (⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ : SpecEntry) ∈ tPfx

/-- Cross-part Part 1 row memberships required by Part 2, Part 3, and the `5`-fn tail. -/
structure M7Part1Callees (tbl : List SpecEntry) : Prop where
  isqrt : (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈ tbl
  ilog10 : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl
  rngNext : (⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ : SpecEntry) ∈ tbl
  arenaNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
    tbl
  allocCl : (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ :
    SpecEntry) ∈ tbl
  heapPop : (⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩ : SpecEntry) ∈ tbl
  heapDown : (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈ tbl
  bumpVar : (⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ : SpecEntry) ∈ tbl
  bumpDecay : (⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ : SpecEntry) ∈ tbl
  queueMtf : (⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ : SpecEntry) ∈ tbl
  tickRel : (⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩ : SpecEntry) ∈ tbl
  log10Q16 : (⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩ : SpecEntry) ∈
    tbl
  log10Q16M7 : (⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.m7Log10Q16Spec, true⟩ :
    SpecEntry) ∈ tbl
  scaleDeltaM5 : (⟨"full_scale_delta_m5", [i64, i64], [i64],
    FullFastSched.schedScaleDeltaSpec, true⟩ : SpecEntry) ∈ tbl
  emaUpdate : (⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩ : SpecEntry) ∈
    tbl
  assignLvl : (⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ :
    SpecEntry) ∈ tbl
  assign : (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl
  backtrackRaw : (⟨"full_backtrack_raw_m5", [i64, i64], [],
    FullM5HeurCore.fullBacktrackRawSpec, true⟩ : SpecEntry) ∈ tbl
  backtrack : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl
  addClause : (⟨"full_add_clause", [i64, i32, i32, .bool], [i64],
    Full.fullAddClauseSpec, true⟩ : SpecEntry) ∈ tbl
  hdrSyncLegacy : (⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrUpdateTier : (⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrGetWm : (⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩ :
    SpecEntry) ∈ tbl
  hdrSetWm : (⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩ :
    SpecEntry) ∈ tbl
  hdrDrInit : (⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩ : SpecEntry) ∈ tbl
  hdrDrUpdate : (⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩ : SpecEntry) ∈ tbl
  hdrDrAllow : (⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩ : SpecEntry) ∈ tbl
  findRepl : (⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩ : SpecEntry) ∈
    tbl
  unwatchLarge : (⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ :
    SpecEntry) ∈ tbl
  propIgnoreHot : (⟨"full_propagate_ignore_hot", [i64, i64], [i64],
    Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩ : SpecEntry) ∈ tbl
  scaleDelta : (⟨"full_scale_delta", [i64, i64], [i64],
    FullFastSched.schedScaleDeltaSpec, true⟩ : SpecEntry) ∈ tbl
  propagateIgn : (⟨"full_propagate_ignore", [i64, i64], [i64],
    Full.fullPropagateIgnoreSpec, true⟩ : SpecEntry) ∈ tbl
  propagate : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl
  flushTrail : (⟨"full_flush_trail", [i64], [i64],
    FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl
  reduce : (⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩ : SpecEntry) ∈ tbl

/-- Canonical spec for `full_prop_lit_ovf_hot` matching `FullM7BcpHotProof0`. -/
def m7PropLitOvfHotSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, cref, ()) m Q X => Full.fullWatchPushSpec (h, lit, w0, cref, 2#32, ()) m Q X

/-- Canonical spec for `full_prop_chrono_hot` matching `FullM7BcpHotProof0`. -/
def m7PropChronoHotSpec : Spec [i64, i64] [.bool] :=
  fun (h, t0, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (st0 : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ st0.LengthsOk c ∧ FullWitnessInv c F0 F_cur st0.core ∧
      st0.core.dense_mode = 0#64 ∧ t0.toNat ≤ st0.core.trail_end ∧
      (FullMem c st0 ⋆ R) m ∧
      ∀ (ok : Bool) wvec' arena' wstk' wlen' wu' oom' wsort' m',
        let st' : FullState :=
          { core :=
              { st0.core with
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', oom := oom' }
            scratch := { st0.scratch with wsort := wsort' } }
        st'.LengthsOk c → FullWitnessInv c F0 F_cur st'.core →
        Full.FullPropDecSpecs.FullArenaPermEq st0.core st'.core →
        (ok = true → oom' = st0.core.oom) →
        (ok = false → oom' = 1#64) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-- Pre-parameterized hypothesis bundle over the remaining `FullM7BcpHot` proofs (`@m7-4`). -/
structure M7BcpHotHyp (Γ : Env) : Prop where
  propChronoHot : ∀ a m Q X, m7PropChronoHotSpec a m Q X →
    Func.wp Γ FullM7BcpHot.full_prop_chrono_hot_body a m Q X
  propIgnoreHot : ∀ a m Q X, Full.FullPropDecSpecs.fullPropagateIgnoreSpec a m Q X →
    Func.wp Γ FullM7BcpHot.full_propagate_ignore_hot_body a m Q X

/-! ## 2. Cross-Module Spec Bridges -/

private theorem m7_scale_delta_fff_ne0 {f_abs : BitVec 64} (hf_le : f_abs.toNat ≤ 983040) :
    ((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64 ≠ 0#64 := by
  have hmul9 : (9#64 * f_abs).toNat = 9 * f_abs.toNat := by bv_omega
  have hsq_le : 9 * f_abs.toNat * f_abs.toNat ≤ 9 * 983040 * 983040 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 9 hf_le) hf_le
  have hsq_lt : 9 * f_abs.toNat * f_abs.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hsq_le (by decide)
  have hsq : (9#64 * f_abs * f_abs).toNat = 9 * f_abs.toNat * f_abs.toNat := by
    rw [BitVec.toNat_mul, hmul9, Nat.mod_eq_of_lt hsq_lt]
  have h17 : ∀ v : BitVec 64, (v >>> 17#64).toNat = v.toNat / 2 ^ 17 := by
    intro v; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hshr : ((9#64 * f_abs * f_abs) >>> 17#64).toNat ≤ 66355200 := by
    rw [h17, hsq]
    exact Nat.le_trans (Nat.div_le_div_right hsq_le) (by decide)
  have hsum_lt : ((9#64 * f_abs * f_abs) >>> 17#64).toNat + 1638400 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right hshr 1638400) (by decide)
  intro h0
  have htn := congrArg BitVec.toNat h0
  rw [BitVec.toNat_add, show (1638400#64).toNat = 1638400 from rfl, Nat.mod_eq_of_lt hsum_lt] at htn
  change _ = 0 at htn
  omega

/-- Direct `FullFastSched.schedScaleDeltaSpec` WP proof for `FullM7Bump.full_scale_delta_m7_body`
from `FullM7Search.m7Log10Q16Spec`. -/
theorem m7_scale_delta_sched_wp (Γ : Env)
    (hLog : ∀ a m Q X, FullM7Search.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Func.wp Γ FullM7Bump.full_scale_delta_m7_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ mem Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp FullM7Bump.full_scale_delta_m7_body
  c0_hsteps_nogrp
  · exact hQ 0#64
  · refine wp_join_group (ts := [i64]) (fun _ m1 => mem = m1) ?_ ?_
    · rintro _ ⟨clauses, ⟨⟩⟩ _ rfl
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ m1 => mem = m1) ?_ ?_
      · rintro _ ⟨arg, ⟨⟩⟩ _ rfl
        c0_hsteps_nogrp
        c0_call hLog
        refine FullM7Search.m7Log10Q16Spec_of fun l _ _ => ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (l1, ()) m1 => mem = m1 ∧ 65536 ≤ l1.toNat) ?_ ?_
        · rintro _ ⟨l1, ⟨⟩⟩ _ ⟨rfl, hl1'⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (l2, ()) m1 => mem = m1 ∧ 65536 ≤ l2.toNat ∧ l2.toNat ≤ 1310720) ?_ ?_
          · rintro _ ⟨l2, ⟨⟩⟩ _ ⟨rfl, hl2a, hl2b⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (f_abs, ()) m1 => mem = m1 ∧ f_abs.toNat ≤ 983040) ?_ ?_
            · rintro _ ⟨f_abs, ⟨⟩⟩ _ ⟨rfl, hfa⟩
              have hne0 := m7_scale_delta_fff_ne0 hfa
              have heq_f : (((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64) =
                  ((9 * f_abs * f_abs) >>> OfNat.ofNat 17 + 1638400 : BitVec 64) := rfl
              rw [heq_f] at hne0
              c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
              dsimp only
              generalize ((9 * f_abs * f_abs) >>> OfNat.ofNat 17 + 1638400 : BitVec 64) = fff
                at hne0 ⊢
              c0_step; c0_step
              · c0_steps; exact hQ _
              · c0_step
                · refine wp_jnz_of (fun _ => by c0_steps; exact hQ _)
                    (fun _ => by c0_steps; exact hQ _)
                · c0_steps; exact hQ _
            · intro _ hJf
              c0_hsteps_nogrp
              · refine hJf (_, ()) mem ⟨rfl, ?_⟩
                have hle : (327680 : BitVec 64).toNat ≤ l2.toNat := by assumption
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
                have h32 : (327680 : BitVec 64).toNat = 327680 := by decide
                rw [h32] at hle ⊢; omega
              · refine hJf (_, ()) mem ⟨rfl, ?_⟩
                have hlt : ¬ (327680 : BitVec 64).toNat ≤ l2.toNat := by assumption
                have hle : l2.toNat ≤ (327680 : BitVec 64).toNat := Nat.le_of_not_le hlt
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
                have h32 : (327680 : BitVec 64).toNat = 327680 := by decide
                rw [h32] at hle ⊢; omega
          · intro _ hJl2
            c0_hsteps_nogrp
            · exact hJl2 (1310720#64, ()) mem ⟨rfl, by decide, by decide⟩
            · exact hJl2 (l1, ()) mem ⟨rfl, hl1', Nat.le_of_not_lt (by assumption)⟩
        · intro _ hJl1
          c0_hsteps_nogrp
          · exact hJl1 (65536#64, ()) mem ⟨rfl, by decide⟩
          · exact hJl1 (l, ()) mem ⟨rfl, Nat.le_of_not_lt (by assumption)⟩
      · intro _ hJa; c0_hsteps_nogrp <;> exact hJa (_, ()) mem rfl
    · intro _ hJc; c0_hsteps_nogrp <;> exact hJc (_, ()) mem rfl

/-- Bridge `FullM6BcpS15.fullBcpS15Spec` onto stronger canonical `Full.fullPropagateSpec`. -/
theorem m7_fullPropagate_to_bcpS15 {Γ : Env} {f : Sym}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBcpS15Spec a m Q X → Γ f [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  exact hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hr h0 h1 h2 hnoop hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap (fun _ => rfl) hfl hr h0 h1 h2 hnoop hm'⟩

/-- Bridge `Full.fullPropagateDelSpec` onto stronger canonical `Full.fullPropagateSpec`. -/
theorem m7_fullPropagate_to_del {Γ : Env} {f : Sym}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullPropagateDelSpec a m Q X → Γ f [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  exact hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hr h0 h1 h2 hnoop hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap hfl hr h0 h1 h2 hnoop hm'⟩

/-- Bridge `Full.fullPropagateSpec` callers onto `Full.FullDenseWatchSpecs.fullPropagateSpec`. -/
theorem m7_fullPropagate_to_dw {Γ : Env} {f : Sym}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X :=
  s15_to_dwPropagate (m7_fullPropagate_to_bcpS15 hProp)

/-- Bridge `Full.fullPropagateSpec` callers onto `Full.FullLuckySpecs.fullPropagateSpec`. -/
theorem m7_fullPropagate_to_lucky {Γ : Env} {f : Sym}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, FullLuckySpecs.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X :=
  s15_to_luckyPropagate (m7_fullPropagate_to_bcpS15 hProp)

/-- Bridge `Full.fullPropagateIgnoreDelSpec` onto stronger `Full.fullPropagateIgnoreSpec`. -/
theorem m7_fullPropagateIgn_to_del {Γ : Env} {f : Sym}
    (hIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ f [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X →
      Γ f [i64, i64] [i64] a m Q X := by
  rintro ⟨h, ig, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  exact hIgn _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph m'
        hlen' hw' htr hap hfl hr h0 h1 h2 hnoop hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph
        s.scratch.delayed m' hlen' hw' htr hap hfl hr h0 h1 h2 hnoop hm'⟩

theorem pfx21Slice_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (off n : Nat) :
    ((tPfx.drop off).take n).map (fun e => (e.name, e.as, e.rs)) =
      ((m7OrchPfxFns.drop off).take n).map Fn.sig := by
  simp only [List.map_take, List.map_drop, hsig]

theorem pfx21Slice_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) (off n : Nat) :
    ((tPfx.drop off).take n).all SpecEntry.noExit = true := by
  rw [List.all_eq_true] at hno ⊢
  intro e he
  exact hno e (List.mem_of_mem_drop (List.mem_of_mem_take he))

theorem m7_bool_all_append {α : Type _} {p : α → Bool} {l1 l2 : List α}
    (h1 : l1.all p = true) (h2 : l2.all p = true) : (l1 ++ l2).all p = true := by
  simp only [List.all_append, h1, h2, Bool.and_self]

theorem m7_list_len_of_map {α β : Type _} {f : α → β} {l1 : List α} {l2 : List β}
    (h : l1.map f = l2) : l1.length = l2.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1

theorem m7_oneImpl {tbl : List SpecEntry} {fs : List Fn} {rs : List SpecEntry}
    {nm : Sym} {as bs : List Ty} {body : Func as bs} {sp : Spec as bs}
    (hfn : fs = [⟨nm, as, bs, body⟩]) (hrs : rs = [⟨nm, as, bs, sp, true⟩])
    (hwp : ∀ xs m Q X, sp xs m Q X → Func.wp (Env.ofTable tbl) body xs m Q X) :
    TableImpl (Env.ofTable tbl) fs rs := by
  subst hfn hrs
  exact ⟨SpecEntry.Impl.of hwp, trivial⟩

theorem m7_mem1 {α : Type _} {a : α} {l : List α} (h : a ∈ l) : ∀ e ∈ [a], e ∈ l :=
  fun _ he => by cases List.mem_singleton.mp he; exact h

theorem m7_memC {α : Type _} {a : α} {xs l : List α} (h : a ∈ l)
    (hs : ∀ e ∈ xs, e ∈ l) : ∀ e ∈ a :: xs, e ∈ l :=
  fun _ he => by rcases List.mem_cons.mp he with rfl | hx; exact h; exact hs _ hx

/-! ## 3. Part 1 Segment Rows (`112` Entries) -/

private def p1DimacsIsqrtIlogRows : List SpecEntry := fullBaseTable.take 10
private def p1RngNextRows : List SpecEntry :=
  [⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩]
private def p1Full1ArenaRows : List SpecEntry := (fullBaseTable.drop 11).take 3
private def p1WatchGc0Rows : List SpecEntry :=
  [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullWstackRadixSortSpec, true⟩
  , ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩ ]
private def p1HeapRows : List SpecEntry := (fullBaseTable.drop 16).take 4
private def p1RescaleM6Rows : List SpecEntry :=
  [⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩]
private def p1BumpSchedRows : List SpecEntry :=
  [⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩] ++
  ((fullBaseTable.drop 22).take 3 ++
  ([⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩] ++
  FullM5Sched.m5SchedSpecTable.take 1))
private def p1M7BumpSchedRows : List SpecEntry :=
  [ ⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.m7Log10Q16Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩ ] ++
  ((FullM5Sched.m5SchedSpecTable.drop 2).take 1 ++
  [⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩])
private def p1InitAssignRows : List SpecEntry :=
  (fullBaseTable.drop 27).take 2 ++
  ([ ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩
   , ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
   , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ] ++
  ((fullBaseTable.drop 31).take 5 ++
  ([⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] ++
  ((fullBaseTable.drop 37).take 1 ++
  ([ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
   , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] ++
  ((fullBaseTable.drop 40).take 1 ++
  [ ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩ ]))))))
private def p1Hdr0ExactRows : List SpecEntry :=
  [ ⟨"full_m6_hdr_sizeof", [], [i64], m6HdrSizeofSpec, true⟩
  , ⟨"full_m6_ext_sizeof", [], [i64], m6ExtSizeofSpec, true⟩
  , ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_hdr_reset", [i64], [], m6HdrResetSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool], m6HdrExtReadySpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitExactSpec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reset_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_add_ticks", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩ ]
private def p1ParseHelpersRows : List SpecEntry := (fullBaseTable.drop 42).take 2
private def p1PropHelpersRows : List SpecEntry :=
  (fullBaseTable.drop 45).take 2 ++
  [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩]
private def p1BcpHotRows : List SpecEntry :=
  [ ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool], m7PropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool], m7PropChronoHotSpec, true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_bcp_hot", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ]
private def p1ParseBodyM6Rows : List SpecEntry :=
  [⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩]
private def p1RecomputeTiersRows : List SpecEntry := (fullBaseTable.drop 50).take 1
private def p1WatchGc1Rows : List SpecEntry :=
  [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_range_m6", [i64, i64], [], FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ ]
private def p1WatchGc2Rows : List SpecEntry :=
  [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], FullM6WatchGc.fullRewatchRangeSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩ ]
private def p1SweepBinsM6cfRows : List SpecEntry :=
  [⟨"full_sweep_bins_m6cf", [i64], [], Full.fullSweepBinsSpec, true⟩]
private def p1SweepCopyRows : List SpecEntry := (fullBaseTable.drop 58).take 1
private def p1WatchGc3Rows : List SpecEntry :=
  [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedPass2Spec, true⟩
  , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedEndBufSpec, true⟩
  , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.fullMoveRedEndSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ ]
private def p1FlushTrailRows : List SpecEntry :=
  [⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩]
private def p1RedsRows : List SpecEntry := (fullBaseTable.drop 52).take 3
private def p1ReduceRows : List SpecEntry :=
  [⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩]

/-- Part 1 rows (`0..111`, `112` entries) aligned 1-to-1 with `FullM7.m7FnsPart1`. -/
def m7RowsPart1 (tPfx : List SpecEntry) : List SpecEntry :=
  p1DimacsIsqrtIlogRows ++ (p1RngNextRows ++ (p1Full1ArenaRows ++ (p1WatchGc0Rows ++
  ((tPfx.drop 0).take 2 ++ (p1HeapRows ++ (p1RescaleM6Rows ++ ((tPfx.drop 2).take 1 ++
  (p1BumpSchedRows ++ (p1M7BumpSchedRows ++ (p1InitAssignRows ++ (p1Hdr0ExactRows ++
  (p1ParseHelpersRows ++ (p1PropHelpersRows ++ (p1BcpHotRows ++ (p1ParseBodyM6Rows ++
  ((tPfx.drop 3).take 1 ++ (p1RecomputeTiersRows ++ (p1WatchGc1Rows ++ (p1WatchGc2Rows ++
  ((tPfx.drop 4).take 1 ++ (p1SweepBinsM6cfRows ++ ((tPfx.drop 5).take 1 ++ (p1SweepCopyRows ++
  ((tPfx.drop 6).take 1 ++ (p1WatchGc3Rows ++ ((tPfx.drop 7).take 2 ++ (p1FlushTrailRows ++
  (p1RedsRows ++ (p1ReduceRows ++ (tPfx.drop 9).take 1)))))))))))))))))))))))))))))

/-! ## 4. Part 1 Function Decomposition & Metadata -/

private def p1DimacsIsqrtIlogFns : List Fn := Full.fullFns.take 10
private def p1RngNextFns : List Fn := [FullM7Bump.m7RngNextFn]
private def p1Full1ArenaFns : List Fn := (Full.fullFns.drop 11).take 3
private def p1WatchGc0Fns : List Fn := FullM6WatchGc.m6WatchGc_fns.take 3
private def p1HeapFns : List Fn := (Full.fullFns.drop 16).take 4
private def p1RescaleM6Fns : List Fn := FullM6WalkParse.m6WalkParse_fns.take 1
private def p1BumpSchedFns : List Fn :=
  [FullM4Bump.m4BumpVarFn] ++ ((Full.fullFns.drop 22).take 3 ++
  ([FullM3VivChrono.m3TickRelFn] ++ FullM5Sched.m5Sched_fns.take 1))
private def p1M7BumpSchedFns : List Fn :=
  [m7Log10Q16CanonFn, m7ScaleDeltaM5Fn] ++
  ((FullM5Sched.m5Sched_fns.drop 2).take 1 ++ [FullM7Bump.m7ScaleDeltaFn])
private def p1InitAssignFns : List Fn :=
  (Full.fullFns.drop 27).take 2 ++
  ([ FullM5HeurCore.m5SaveTargetBestFn
   , FullM5HeurCore.m5BacktrackRawFn
   , FullM5HeurCore.m5BacktrackFn ] ++
  ((Full.fullFns.drop 31).take 5 ++
  (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  ((Full.fullFns.drop 37).take 1 ++
  (FullM5Orch.m5Orch_fns.take 2 ++
  ((Full.fullFns.drop 40).take 1 ++
  ((FullM5Orch.m5Orch_fns.drop 2).take 1 ++
  [FullM5.m5InitStateFwdFn])))))))
private def p1Hdr0Fns : List Fn := FullM6Hdr.m6HdrModule.fns.take 24
private def p1ParseHelpersFns : List Fn := (Full.fullFns.drop 42).take 2
private def p1PropHelpersFns : List Fn :=
  (Full.fullFns.drop 45).take 2 ++ FullM5Otfs.m5Otfs_fns.take 1
private def p1BcpHotFns : List Fn :=
  FullM7BcpHot.m7BcpHot_fns ++ [FullM7BcpHot.m7PropIgnoreFn, FullM7.m7PropCanonFn]
private def p1ParseBodyM6Fns : List Fn := (FullM6WalkParse.m6WalkParse_fns.drop 1).take 1
private def p1RecomputeTiersFns : List Fn := (Full.fullFns.drop 50).take 1
private def p1WatchGc1Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 3).take 2
private def p1WatchGc2Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 6).take 2
private def p1SweepBinsM6cfFns : List Fn := (FullM6CompactFlush.m6CompactFlush_fns.drop 1).take 1
private def p1SweepCopyFns : List Fn := (Full.fullFns.drop 58).take 1
private def p1WatchGc3Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 8).take 5
private def p1FlushTrailFns : List Fn := [FullM6CompactFlush.m6cfFlushTrailFn]
private def p1RedsFns : List Fn := (Full.fullFns.drop 52).take 3
private def p1ReduceFns : List Fn := [m6CanonicalReduceFn]

private def p1FnsSeg : List Fn :=
  p1DimacsIsqrtIlogFns ++ (p1RngNextFns ++ (p1Full1ArenaFns ++ (p1WatchGc0Fns ++
  ((m7OrchPfxFns.drop 0).take 2 ++ (p1HeapFns ++ (p1RescaleM6Fns ++ ((m7OrchPfxFns.drop 2).take 1 ++
  (p1BumpSchedFns ++ (p1M7BumpSchedFns ++ (p1InitAssignFns ++ (p1Hdr0Fns ++
  (p1ParseHelpersFns ++ (p1PropHelpersFns ++ (p1BcpHotFns ++ (p1ParseBodyM6Fns ++
  ((m7OrchPfxFns.drop 3).take 1 ++ (p1RecomputeTiersFns ++ (p1WatchGc1Fns ++ (p1WatchGc2Fns ++
  ((m7OrchPfxFns.drop 4).take 1 ++ (p1SweepBinsM6cfFns ++ ((m7OrchPfxFns.drop 5).take 1 ++
  (p1SweepCopyFns ++ ((m7OrchPfxFns.drop 6).take 1 ++ (p1WatchGc3Fns ++
  ((m7OrchPfxFns.drop 7).take 2 ++ (p1FlushTrailFns ++ (p1RedsFns ++ (p1ReduceFns ++
  (m7OrchPfxFns.drop 9).take 1)))))))))))))))))))))))))))))

private theorem p1Fns_eq : m7FnsPart1 = p1FnsSeg := by t_kernel_rfl

theorem m7RowsPart1_sigs {tPfx : List SpecEntry}
    (hsig : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig) :
    (m7RowsPart1 tPfx).map (fun e => (e.name, e.as, e.rs)) = m7FnsPart1.map Fn.sig := by
  have h01 : p1DimacsIsqrtIlogRows.map (fun e => (e.name, e.as, e.rs)) =
      p1DimacsIsqrtIlogFns.map Fn.sig := by t_kernel_rfl
  have h02 : p1RngNextRows.map (fun e => (e.name, e.as, e.rs)) =
      p1RngNextFns.map Fn.sig := by t_kernel_rfl
  have h03 : p1Full1ArenaRows.map (fun e => (e.name, e.as, e.rs)) =
      p1Full1ArenaFns.map Fn.sig := by t_kernel_rfl
  have h04 : p1WatchGc0Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1WatchGc0Fns.map Fn.sig := by t_kernel_rfl
  have h05 : p1HeapRows.map (fun e => (e.name, e.as, e.rs)) = p1HeapFns.map Fn.sig := by
    t_kernel_rfl
  have h06 : p1RescaleM6Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1RescaleM6Fns.map Fn.sig := by t_kernel_rfl
  have h07 : p1BumpSchedRows.map (fun e => (e.name, e.as, e.rs)) =
      p1BumpSchedFns.map Fn.sig := by t_kernel_rfl
  have h08 : p1M7BumpSchedRows.map (fun e => (e.name, e.as, e.rs)) =
      p1M7BumpSchedFns.map Fn.sig := by t_kernel_rfl
  have h09 : p1InitAssignRows.map (fun e => (e.name, e.as, e.rs)) =
      p1InitAssignFns.map Fn.sig := by t_kernel_rfl
  have h10 : p1Hdr0ExactRows.map (fun e => (e.name, e.as, e.rs)) =
      p1Hdr0Fns.map Fn.sig := by t_kernel_rfl
  have h11 : p1ParseHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1ParseHelpersFns.map Fn.sig := by t_kernel_rfl
  have h12 : p1PropHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1PropHelpersFns.map Fn.sig := by t_kernel_rfl
  have h13 : p1BcpHotRows.map (fun e => (e.name, e.as, e.rs)) =
      p1BcpHotFns.map Fn.sig := by t_kernel_rfl
  have h14 : p1ParseBodyM6Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1ParseBodyM6Fns.map Fn.sig := by t_kernel_rfl
  have h15 : p1RecomputeTiersRows.map (fun e => (e.name, e.as, e.rs)) =
      p1RecomputeTiersFns.map Fn.sig := by t_kernel_rfl
  have h16 : p1WatchGc1Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1WatchGc1Fns.map Fn.sig := by t_kernel_rfl
  have h17 : p1WatchGc2Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1WatchGc2Fns.map Fn.sig := by t_kernel_rfl
  have h18 : p1SweepBinsM6cfRows.map (fun e => (e.name, e.as, e.rs)) =
      p1SweepBinsM6cfFns.map Fn.sig := by t_kernel_rfl
  have h19 : p1SweepCopyRows.map (fun e => (e.name, e.as, e.rs)) =
      p1SweepCopyFns.map Fn.sig := by t_kernel_rfl
  have h20 : p1WatchGc3Rows.map (fun e => (e.name, e.as, e.rs)) =
      p1WatchGc3Fns.map Fn.sig := by t_kernel_rfl
  have h21 : p1FlushTrailRows.map (fun e => (e.name, e.as, e.rs)) =
      p1FlushTrailFns.map Fn.sig := by t_kernel_rfl
  have h22 : p1RedsRows.map (fun e => (e.name, e.as, e.rs)) = p1RedsFns.map Fn.sig := by
    t_kernel_rfl
  have h23 : p1ReduceRows.map (fun e => (e.name, e.as, e.rs)) = p1ReduceFns.map Fn.sig := by
    t_kernel_rfl
  rw [p1Fns_eq]
  unfold m7RowsPart1 p1FnsSeg
  simp only [List.map_append]
  rw [h01, h02, h03, h04, pfx21Slice_sigs hsig 0 2, h05, h06, pfx21Slice_sigs hsig 2 1,
    h07, h08, h09, h10, h11, h12, h13, h14, pfx21Slice_sigs hsig 3 1, h15, h16, h17,
    pfx21Slice_sigs hsig 4 1, h18, pfx21Slice_sigs hsig 5 1, h19, pfx21Slice_sigs hsig 6 1, h20,
    pfx21Slice_sigs hsig 7 2, h21, h22, h23, pfx21Slice_sigs hsig 9 1]

theorem m7RowsPart1_noExit {tPfx : List SpecEntry}
    (hno : tPfx.all SpecEntry.noExit = true) :
    (m7RowsPart1 tPfx).all SpecEntry.noExit = true := by
  have n01 : p1DimacsIsqrtIlogRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n02 : p1RngNextRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n03 : p1Full1ArenaRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n04 : p1WatchGc0Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n05 : p1HeapRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n06 : p1RescaleM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n07 : p1BumpSchedRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n08 : p1M7BumpSchedRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n09 : p1InitAssignRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n10 : p1Hdr0ExactRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n11 : p1ParseHelpersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n12 : p1PropHelpersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n13 : p1BcpHotRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n14 : p1ParseBodyM6Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n15 : p1RecomputeTiersRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n16 : p1WatchGc1Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n17 : p1WatchGc2Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n18 : p1SweepBinsM6cfRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n19 : p1SweepCopyRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n20 : p1WatchGc3Rows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n21 : p1FlushTrailRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n22 : p1RedsRows.all SpecEntry.noExit = true := by t_kernel_rfl
  have n23 : p1ReduceRows.all SpecEntry.noExit = true := by t_kernel_rfl
  simp only [m7RowsPart1, List.all_append, n01, n02, n03, n04, n05, n06, n07, n08, n09, n10, n11,
    n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, pfx21Slice_noExit hno,
    Bool.and_self]

theorem m7Part1Callees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart1 tPfx, e ∈ tbl) : M7Part1Callees tbl := by
  have sub_dim : ∀ e ∈ p1DimacsIsqrtIlogRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; exact List.mem_append_left _ h)
  have sub_rng : ∀ e ∈ p1RngNextRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; apply List.mem_append_right; exact List.mem_append_left _ h)
  have sub_ar : ∀ e ∈ p1Full1ArenaRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 2 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_heap : ∀ e ∈ p1HeapRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 5 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bump : ∀ e ∈ p1BumpSchedRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 8 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_m7bs : ∀ e ∈ p1M7BumpSchedRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_init : ∀ e ∈ p1InitAssignRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_hdr0 : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 11 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_prph : ∀ e ∈ p1PropHelpersRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 13 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bcp : ∀ e ∈ p1BcpHotRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 14 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_flsh : ∀ e ∈ p1FlushTrailRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 27 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_red : ∀ e ∈ p1ReduceRows, e ∈ tbl := fun _ h => hsub _ (by
    unfold m7RowsPart1; (iterate 29 apply List.mem_append_right); exact List.mem_append_left _ h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_dim _ (List.mem_of_getElem? (i := 8) rfl)
  · exact sub_dim _ (List.mem_of_getElem? (i := 9) rfl)
  · exact sub_rng _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_ar _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_ar _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_heap _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_heap _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_bump _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_m7bs _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_m7bs _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_m7bs _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_init _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 7) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 10) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 18) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 19) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 21) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 22) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 23) rfl)
  · exact sub_prph _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_prph _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_m7bs _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_flsh _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_red _ (List.mem_of_getElem? (i := 0) rfl)

/-! ## 5. Part 1 Segment `TableImpl` Proofs -/

private theorem m3_tick_zip_p :
    ∀ p ∈ List.zip [FullM3VivChrono.m3TickRelFn]
        [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩],
      p.1 ∈ FullM3VivChrono.m3Module.fns ∧
      p.2 ∈ FullM3VivChrono.m3SpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
  subst hp
  exact ⟨List.mem_of_getElem? (i := 0) rfl, List.mem_of_getElem? (i := 0) rfl, rfl, rfl, rfl⟩

private theorem m5Sched1_zip_p :
    ∀ p ∈ List.zip (FullM5Sched.m5Sched_fns.take 1) (FullM5Sched.m5SchedSpecTable.take 1),
      p.1 ∈ FullM5Sched.m5SchedModule.fns ∧ p.2 ∈ FullM5Sched.m5SchedSpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  have hz := modSub_drop_take (M1 := FullM5Sched.m5SchedModule)
    (t1 := FullM5Sched.m5SchedSpecTable.take 6) rfl (off := 0) (n := 1)
  have hdt : (FullM5Sched.m5SchedModule.fns.drop 0).take 1 =
      FullM5Sched.m5Sched_fns.take 1 := rfl
  have hst : ((FullM5Sched.m5SchedSpecTable.take 6).drop 0).take 1 =
      FullM5Sched.m5SchedSpecTable.take 1 := by
    rw [List.drop_zero, List.take_take]; rfl
  intro p hp
  rw [← hdt, ← hst] at hp
  obtain ⟨h1, h2, hn, ha, hrs⟩ := hz.2 p hp
  exact ⟨h1, List.mem_of_mem_take h2, hn, ha, hrs⟩

private theorem m5SchedEma_zip_p :
    ∀ p ∈ List.zip ((FullM5Sched.m5Sched_fns.drop 2).take 1)
        ((FullM5Sched.m5SchedSpecTable.drop 2).take 1),
      p.1 ∈ FullM5Sched.m5SchedModule.fns ∧ p.2 ∈ FullM5Sched.m5SchedSpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  have hz := modSub_drop_take (M1 := FullM5Sched.m5SchedModule)
    (t1 := FullM5Sched.m5SchedSpecTable.take 6) rfl (off := 2) (n := 1)
  have hdt : (FullM5Sched.m5SchedModule.fns.drop 2).take 1 =
      (FullM5Sched.m5Sched_fns.drop 2).take 1 := rfl
  have hst : ((FullM5Sched.m5SchedSpecTable.take 6).drop 2).take 1 =
      (FullM5Sched.m5SchedSpecTable.drop 2).take 1 := by
    rw [List.drop_take, List.take_take]; rfl
  intro p hp
  rw [← hdt, ← hst] at hp
  obtain ⟨h1, h2, hn, ha, hrs⟩ := hz.2 p hp
  exact ⟨h1, List.mem_of_mem_take h2, hn, ha, hrs⟩

private theorem m5SchedSpecTable_nodup :
    (FullM5Sched.m5SchedSpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem p1BumpSched_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1BumpSchedRows, e ∈ tbl)
    (hUp : (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRes : (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1BumpSchedFns p1BumpSchedRows := by
  have h1 : SpecEntry.Impl (Env.ofTable tbl) FullM4Bump.m4BumpVarFn
      ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ :=
    SpecEntry.Impl.of (FullM4Bump.full_bump_var_m4_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hUp) (envRow_mem hnd _ _ _ _ hRes))
  have h2 := (fullSliceTransport 22 3 [⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩]
    (by t_kernel_rfl) (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact fullRow_at 20 _)
    hnd (fun _ h => hown _ (by
      unfold p1BumpSchedRows; apply List.mem_append_right; exact List.mem_append_left _ h))
    (m7_mem1 hRes)).2
  have h3 := (modSubTransport FullM3VivChrono.m3_moduleOk FullM3VivChrono.m3SpecTable_nodup
    (fs := [FullM3VivChrono.m3TickRelFn])
    (sub_tbl := [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩]) (extRows := [])
    rfl m3_tick_zip_p (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact hown _ (by unfold p1BumpSchedRows; iterate 2 apply List.mem_append_right
                       exact List.mem_append_left _ List.mem_cons_self))
    (fun _ h => nomatch h)).2
  have h4 := (modSubTransport FullM5Sched.m5Sched_moduleOk m5SchedSpecTable_nodup
    (extRows := []) rfl m5Sched1_zip_p
    (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (by
      unfold p1BumpSchedRows
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))))
    (fun _ h => nomatch h)).2
  exact tableImpl_append rfl ⟨h1, trivial⟩
    (tableImpl_append rfl h2 (tableImpl_append rfl h3 h4))

private theorem p1M7BumpSched_impl {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1M7BumpSchedRows, e ∈ tbl)
    (hLog : (⟨"full_log10_q16_m7", [i64], [i64],
      FullM7Search.m7Log10Q16Spec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1M7BumpSchedFns p1M7BumpSchedRows := by
  have rLog := envRow_mem hnd _ _ _ _ hLog (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h)
  have hLogImpl : TableImpl (Env.ofTable tbl) [m7Log10Q16CanonFn]
      [⟨"full_log10_q16_m7", [i64], [i64], FullM7Search.m7Log10Q16Spec, true⟩] :=
    m7_oneImpl rfl rfl (FullM7Search.full_log10_q16_m7_wp (Env.ofTable tbl))
  have hSdM5Impl : TableImpl (Env.ofTable tbl) [m7ScaleDeltaM5Fn]
      [⟨"full_scale_delta_m5", [i64, i64], [i64],
        FullFastSched.schedScaleDeltaSpec, true⟩] :=
    m7_oneImpl rfl rfl (m7_scale_delta_sched_wp (Env.ofTable tbl) rLog)
  have hEma := (modSubTransport FullM5Sched.m5Sched_moduleOk m5SchedSpecTable_nodup
    (extRows := []) rfl m5SchedEma_zip_p
    (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (by
      unfold p1M7BumpSchedRows
      apply List.mem_append_right
      exact List.mem_append_left _ h))
    (fun _ h => nomatch h)).2
  have hSdImpl : TableImpl (Env.ofTable tbl) [FullM7Bump.m7ScaleDeltaFn]
      [⟨"full_scale_delta", [i64, i64], [i64],
        FullFastSched.schedScaleDeltaSpec, true⟩] :=
    m7_oneImpl rfl rfl (m7_scale_delta_sched_wp (Env.ofTable tbl) rLog)
  exact tableImpl_append rfl ⟨hLogImpl.1, hSdM5Impl.1, trivial⟩
    (tableImpl_append rfl hEma hSdImpl)

private theorem p1InitAssign_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1InitAssignRows, e ∈ tbl)
    (hHdr : (⟨"kissat_parse_header", [i64, i64, i64], [.bool],
      kissatParseHeaderSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAlloc : (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64],
      Full.fullAllocClSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hHeapPush : (⟨"full_heap_push", [i64, i32], [], Full.fullHeapPushSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1InitAssignFns p1InitAssignRows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), p1InitAssignRows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hs0 := (fullSliceTransport 27 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (by unfold p1InitAssignRows; exact List.mem_append_left _ h))
    (fun _ h => nomatch h)).2
  have hSave : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5SaveTargetBestFn
      ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_save_target_best_m5_wp (Env.ofTable tbl))
  have hBtRaw : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackRawFn
      ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_raw_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 2 _ rfl)) (envRow_mem hnd _ _ _ _ hHeapPush))
  have hBt : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackFn
      ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 3 _ rfl)) (envRow_mem hnd _ _ _ _ (hm 2 _ rfl)))
  have hs1 := (fullSliceTransport 31 5
    [ ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩
    , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩ ]
    (by t_kernel_rfl)
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact fullRow_at 12 _
      · exact fullRow_at 15 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; (iterate 2 apply List.mem_append_right)
      exact List.mem_append_left _ h))
    (m7_memC hAlloc (m7_mem1 hPush))).2
  have hInitHdr : TableImpl (Env.ofTable tbl) (FullFastBveBudgets.fastBveBudgets_fns.take 1)
      [⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] := by
    have heq : FullFastBveBudgets.fastBveBudgets_fns.take 1 =
        [⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.full_init_hdr_body⟩] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullFastBveBudgets.fast_init_hdr_canon_wp (Env.ofTable tbl)),
      trivial⟩
  have hs2 := (fullSliceTransport 37 1
    [⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 34 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; (iterate 4 apply List.mem_append_right)
      exact List.mem_append_left _ h))
    (m7_mem1 (hm 8 _ rfl))).2
  have hCaps : TableImpl (Env.ofTable tbl) (FullM5Orch.m5Orch_fns.take 2)
      [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
      , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] := by
    have heq : FullM5Orch.m5Orch_fns.take 2 =
        [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.full_calc_ext_cap_m5_body⟩
        , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.full_calc_scr_cap_m5_body⟩ ] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullM5Orch.full_calc_ext_cap_m5_wp (Env.ofTable tbl)),
      SpecEntry.Impl.of (FullM5Orch.full_calc_scr_cap_m5_wp (Env.ofTable tbl)), trivial⟩
  have hs3 := (fullSliceTransport 40 1
    [⟨"full_init_ptrs", [i64, i64, i64], [], Full.fullInitPtrsSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 35 _)
    hnd (fun _ h => hown _ (by
      unfold p1InitAssignRows; (iterate 6 apply List.mem_append_right)
      exact List.mem_append_left _ h))
    (m7_mem1 (hm 9 _ rfl))).2
  have hInitStM5 : TableImpl (Env.ofTable tbl) ((FullM5Orch.m5Orch_fns.drop 2).take 1)
      [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        Full.fullInitStateSpec, true⟩] := by
    have heq : (FullM5Orch.m5Orch_fns.drop 2).take 1 =
        [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
          FullM5Orch.full_init_state_m5_body⟩] := rfl
    rw [heq]
    refine ⟨SpecEntry.Impl.of (FullM5Orch.full_init_state_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hHdr) (envRow_mem hnd _ _ _ _ (hm 8 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 11 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 12 _ rfl) FullM5Orch.fullCalcExtCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 13 _ rfl) FullM5Orch.fullCalcScrCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 14 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 10 _ rfl)) (envRow_mem hnd _ _ _ _ (hm 6 _ rfl))
      (envRow_mem hnd _ _ _ _ (hm 7 _ rfl))), trivial⟩
  have hInitSt : SpecEntry.Impl (Env.ofTable tbl) FullM5.m5InitStateFwdFn
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5.m5_init_state_fwd_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 15 _ rfl)))
  unfold p1InitAssignFns p1InitAssignRows
  refine tableImpl_append rfl hs0 (tableImpl_append rfl ⟨hSave, hBtRaw, hBt, trivial⟩ ?_)
  refine tableImpl_append rfl hs1 (tableImpl_append rfl hInitHdr ?_)
  refine tableImpl_append rfl hs2 (tableImpl_append rfl hCaps ?_)
  exact tableImpl_append rfl hs3 (tableImpl_append rfl hInitStM5 ⟨hInitSt, trivial⟩)

private theorem p1Hdr0_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl)
    (hInitSt : (⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      Full.fullInitStateSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1Hdr0Fns p1Hdr0ExactRows := by
  have hfn : p1Hdr0Fns =
      [ ⟨"full_m6_hdr_sizeof", [], [i64], full_m6_hdr_sizeof_body⟩
      , ⟨"full_m6_ext_sizeof", [], [i64], full_m6_ext_sizeof_body⟩
      , ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
      , ⟨"m6_hdr_reset", [i64], [], m6_hdr_reset_body⟩
      , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
      , ⟨"m6_hdr_ext_ready", [i64], [.bool], m6_hdr_ext_ready_body⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], full_m6_mem_init_body⟩
      , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6_hdr_sync_legacy_tiers_body⟩
      , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6_hdr_recompute_tiers_mode_body⟩
      , ⟨"m6_hdr_recompute_tiers", [i64], [], m6_hdr_recompute_tiers_body⟩
      , ⟨"m6_hdr_update_tier_limits", [i64], [], m6_hdr_update_tier_limits_body⟩
      , ⟨"m6_hdr_record_used", [i64, i64], [], m6_hdr_record_used_body⟩
      , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6_hdr_get_tier1_body⟩
      , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6_hdr_get_tier2_body⟩
      , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6_hdr_delaying_body⟩
      , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6_hdr_bump_delay_body⟩
      , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6_hdr_reduce_delay_body⟩
      , ⟨"m6_hdr_reset_delay", [i64, i64], [], m6_hdr_reset_delay_body⟩
      , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6_hdr_get_watermark_body⟩
      , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6_hdr_set_watermark_body⟩
      , ⟨"m6_hdr_add_ticks", [i64, i64], [], m6_hdr_add_ticks_body⟩
      , ⟨"m6_hdr_dr_init", [i64], [], m6_hdr_dr_init_body⟩
      , ⟨"m6_hdr_dr_update", [i64], [], m6_hdr_dr_update_body⟩
      , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6_hdr_dr_allow_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1Hdr0ExactRows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have h_init := envRow_mem hnd _ _ _ _ (hm 2 _ rfl) (fun _ _ _ _ h => m6HdrInitSpec_monoX h)
  have h_ens := envRow_mem hnd _ _ _ _ (hm 4 _ rfl) (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have h_sync := envRow_mem hnd _ _ _ _ (hm 7 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_mode := envRow_mem hnd _ _ _ _ (hm 8 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_rec := envRow_mem hnd _ _ _ _ (hm 9 _ rfl) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have h_dr := envRow_mem hnd _ _ _ _ (hm 21 _ rfl) (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)
  have h_ist := envRow_mem hnd _ _ _ _ hInitSt
  rw [hfn]; unfold p1Hdr0ExactRows
  exact ⟨ SpecEntry.Impl.of (full_m6_hdr_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (full_m6_ext_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (m6_hdr_init_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (m6_hdr_reset_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (m6_ext_ensure_init_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (m6_hdr_ext_ready_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (full_m6_mem_init_exact_wp (Env.ofTable tbl) h_ist h_init)
    , SpecEntry.Impl.of (m6_hdr_sync_legacy_tiers_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_mode_wp (Env.ofTable tbl) h_ens h_sync)
    , SpecEntry.Impl.of (m6_hdr_recompute_tiers_wp (Env.ofTable tbl) h_mode)
    , SpecEntry.Impl.of (m6_hdr_update_tier_limits_wp (Env.ofTable tbl) h_ens h_rec)
    , SpecEntry.Impl.of (m6_hdr_record_used_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_tier1_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_tier2_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_delaying_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_bump_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_reduce_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_reset_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_get_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_set_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_add_ticks_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_dr_init_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (m6_hdr_dr_update_wp (Env.ofTable tbl) h_dr)
    , SpecEntry.Impl.of (m6_hdr_dr_allow_wp (Env.ofTable tbl) h_ens), trivial ⟩

private theorem m7_prop_lit_ovf_hot_wp (Γ : Env)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m7PropLitOvfHotSpec args m Q X →
      Func.wp Γ FullM7BcpHot.full_prop_lit_ovf_hot_body args m Q X := by
  rintro ⟨h, rw, w0, cref, ⟨⟩⟩ m Q X hsp
  unfold Func.wp FullM7BcpHot.full_prop_lit_ovf_hot_body
  c0_hsteps_nogrp
  exact wp_call_of_spec _ _ (hPush _ _ _ _ hsp)

private theorem m7_pdConflOkW_to_conflict {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullPropDecSpecs.FullConflOkW F_cur s.core) : FullConflictOkW F_cur s := by
  rcases h with ⟨ht, h0, h1, hent, hf0, hf1⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hf0, hf1, hent⟩
  · exact Or.inr hr

private theorem m7_pdTrailExt_to_canon {k1 k2 : FullCoreState}
    (h : Full.FullPropDecSpecs.FullTrailExt k1 k2) : FullTrailExt k1 k2 :=
  ⟨h.te_ge, h.trl_pref, h.lvl_pres⟩

private theorem m7_pdArenaPerm_to_canon {k1 k2 : FullCoreState} (hal : k2.arena_len = k1.arena_len)
    (h : Full.FullPropDecSpecs.FullArenaPermEq k1 k2) : FullArenaPermEq k1 k2 :=
  ⟨hal, h.1, h.2⟩

private theorem m7_prop_ignore_canon_of_pd_wp (Γ : Env)
    (hPd : ∀ args m Q X, Full.FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ FullM7BcpHot.full_propagate_ignore_hot_body args m Q X) :
    ∀ args m Q X, Full.fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ FullM7BcpHot.full_propagate_ignore_hot_body args m Q X := by
  rintro ⟨h, ign, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine hPd _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hfl' hr
    hr0 hr1 hr2 hnoop hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw'
    (m7_pdTrailExt_to_canon htr') (m7_pdArenaPerm_to_canon rfl hperm') hfl' hr hr0
    (fun h1 => let ⟨hf, ho, hc, hign, _⟩ := hr1 h1
      ⟨hf, ho, m7_pdConflOkW_to_conflict hc, hign⟩) hr2 hnoop hm'

private theorem m7_propagate_wrap_wp {Γ : Env}
    (hIgn : ∀ args m Q X, Full.FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, Full.fullPropagateSpec args m Q X →
      Func.wp Γ FullM7BcpHot.full_bcp_hot_body args m Q X := by
  rw [show FullM7BcpHot.full_bcp_hot_body =
      fun _ _ ⟨v, ()⟩ =>
        Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore_hot"
          (Arg.var v, Arg.imm (t := i64) 0xFFFFFFFF#64, ())
          (fun ⟨x, ()⟩ => Expr.ret (Arg.var x, ())) by t_kernel_rfl]
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  unfold Func.wp
  refine wp_call_of_spec _ _ (hIgn _ m _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩)
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr' hperm' hfl' hr hr0 hr1 hr2 hnoop hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw'
    (m7_pdTrailExt_to_canon htr') (m7_pdArenaPerm_to_canon rfl hperm') hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hc, _, _⟩ := hr1 h1; ⟨hf, ho, m7_pdConflOkW_to_conflict hc⟩)
    hr2 hnoop hm'

private theorem p1BcpHot_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hBcp : M7BcpHotHyp (Env.ofTable tbl))
    (hIgnHot : (⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1BcpHotFns p1BcpHotRows := by
  have hfn : p1BcpHotFns =
      [ ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
          FullM7BcpHot.full_prop_lit_ovf_hot_body⟩
      , ⟨"full_prop_chrono_hot", [i64, i64], [.bool], FullM7BcpHot.full_prop_chrono_hot_body⟩
      , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
          FullM7BcpHot.full_propagate_ignore_hot_body⟩
      , ⟨"full_bcp_hot", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩
      , ⟨"full_propagate_ignore", [i64, i64], [i64], FullM7BcpHot.full_propagate_ignore_hot_body⟩
      , ⟨"full_propagate", [i64], [i64], FullM7BcpHot.full_bcp_hot_body⟩ ] := by t_kernel_rfl
  have hIgn := envRow_mem hnd _ _ _ _ hIgnHot
  rw [hfn]; unfold p1BcpHotRows
  exact ⟨ SpecEntry.Impl.of (m7_prop_lit_ovf_hot_wp (Env.ofTable tbl)
          (envRow_mem hnd _ _ _ _ hPush))
    , SpecEntry.Impl.of hBcp.propChronoHot
    , SpecEntry.Impl.of hBcp.propIgnoreHot
    , SpecEntry.Impl.of (m7_propagate_wrap_wp hIgn)
    , SpecEntry.Impl.of (m7_prop_ignore_canon_of_pd_wp (Env.ofTable tbl) hBcp.propIgnoreHot)
    , SpecEntry.Impl.of (m7_propagate_wrap_wp hIgn), trivial ⟩

private theorem p1WatchGc0_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc0Rows, e ∈ tbl)
    (hSift : (⟨"full_wsort_sift", [i64, i64, i64, i64], [],
      Full.fullWsortSiftSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc0Fns p1WatchGc0Rows := by
  have hfn : p1WatchGc0Fns =
      [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_wstack_radix_sort_m6_body⟩
      , ⟨"full_wstack_defrag_m6", [i64], [], FullM6WatchGc.full_wstack_defrag_m6_body⟩
      , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
          FullM6WatchGc.full_watch_push_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc0Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hRad := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullWstackRadixSortSpec_xirrel h)
  have hDef := envRow_mem hnd _ _ _ _ (hm 1 _ rfl)
  rw [hfn]; unfold p1WatchGc0Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_wstack_radix_sort_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_wstack_defrag_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSift) hRad)
    , SpecEntry.Impl.of (FullM6WatchGc.full_watch_push_m6_wp (Env.ofTable tbl) hDef), trivial ⟩

private theorem p1WatchGc1_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDefrag : (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc1Fns p1WatchGc1Rows := by
  have hfn : p1WatchGc1Fns =
      [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], FullM6WatchGc.full_lit_rank_m6_body⟩
      , ⟨"full_sweep_bins_range_m6", [i64, i64], [],
          FullM6WatchGc.full_sweep_bins_range_m6_body⟩ ] := rfl
  rw [hfn]; unfold p1WatchGc1Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_lit_rank_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_sweep_bins_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDefrag)), trivial ⟩

private theorem p1WatchGc2_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc2Rows, e ∈ tbl)
    (hRank : (⟨"full_lit_rank_m6", [i64, i64, i32], [i64],
      Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc2Fns p1WatchGc2Rows := by
  have hfn : p1WatchGc2Fns =
      [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_range_m6_body⟩
      , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_arena_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc2Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hRng := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)
  rw [hfn]; unfold p1WatchGc2Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hRank) (envRow_mem hnd _ _ _ _ hPush))
    , SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_arena_m6_wp (Env.ofTable tbl) hRng), trivial ⟩

private theorem p1WatchGc3_impl {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ p1WatchGc3Rows, e ∈ tbl)
    (hSwR : (⟨"full_sweep_bins_range_m6", [i64, i64], [],
      FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRewR : (⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
      FullM6WatchGc.fullRewatchRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hCopy : (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64],
      Full.fullSweepCopySpec, true⟩ : SpecEntry) ∈ tbl) :
    TableImpl (Env.ofTable tbl) p1WatchGc3Fns p1WatchGc3Rows := by
  have hfn : p1WatchGc3Fns =
      [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_pass2_m6_body⟩
      , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_end_buf_m6_body⟩
      , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.full_move_red_end_m6_body⟩
      , ⟨"full_arena_sweep_m6", [i64], [i64], FullM6WatchGc.full_arena_sweep_m6_body⟩
      , ⟨"full_mark_reasons_m6", [i64, .bool], [],
          FullM6WatchGc.full_mark_reasons_m6_body⟩ ] := rfl
  have hm : ∀ (i : Nat) (e : SpecEntry), p1WatchGc3Rows[i]? = some e → e ∈ tbl :=
    fun _ _ h => hown _ (List.mem_of_getElem? h)
  have hP2 := envRow_mem hnd _ _ _ _ (hm 0 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedPass2Spec_xirrel h)
  have hBuf := envRow_mem hnd _ _ _ _ (hm 1 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndBufSpec_xirrel h)
  have hMre := envRow_mem hnd _ _ _ _ (hm 2 _ rfl)
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndSpec_xirrel h)
  rw [hfn]; unfold p1WatchGc3Rows
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_move_red_pass2_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_buf_m6_wp (Env.ofTable tbl) hP2)
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_m6_wp (Env.ofTable tbl) hBuf)
    , SpecEntry.Impl.of (FullM6WatchGc.full_arena_sweep_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSwR
          (fun _ _ _ _ h => FullM6WatchGc.fullSweepBinsRangeSpec_xirrel h))
        (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hCopy) hMre
        (envRow_mem hnd _ _ _ _ hRewR
          (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)))
    , SpecEntry.Impl.of (FullM6WatchGc.full_mark_reasons_m6_wp (Env.ofTable tbl)), trivial ⟩

private theorem p1Reduce_m7_impl {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hIsqrt : (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈ tbl)
    (hIlog : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hRec : (⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hMrk : (⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hSort : (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl) :
    TableImpl (Env.ofTable tbl) p1ReduceFns p1ReduceRows :=
  m7_oneImpl rfl rfl (FullM5Orch.full_reduce_m5_wp (Env.ofTable tbl)
    (envRow_mem hnd _ _ _ _ hIsqrt) (envRow_mem hnd _ _ _ _ hIlog)
    (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hRec)
    (envRow_mem hnd _ _ _ _ hMrk) (envRow_mem hnd _ _ _ _ hSort)
    (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hProp)
    (envRow_mem hnd _ _ _ _ hSweep))

/-- `AllFns Fn.Wf` for all `112` functions of `FullM7.m7FnsPart1`. -/
theorem m7FnsPart1_wf : AllFns Fn.Wf m7FnsPart1 :=
  FullM6Transport.allFns_of_mem fun f hf => FullM7.m7Fns_wf f (by
    unfold FullM7.m7Fns; exact List.mem_append_left _ (List.mem_append_left _ hf))

/-- Certifies all `112` functions of `FullM7.m7FnsPart1` against `m7RowsPart1 tPfx` in
`Env.ofTable tbl`. -/
theorem m7RowsPart1_tableImpl {tPfx tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPfxLen : m7OrchPfxFns.length = tPfx.length)
    (hPfxOk : TableImpl (Env.ofTable tbl) m7OrchPfxFns tPfx)
    (htPfx : ∀ e ∈ tPfx, e ∈ tbl)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hBcpHot : M7BcpHotHyp (Env.ofTable tbl))
    (hOwn : ∀ e ∈ m7RowsPart1 tPfx, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7FnsPart1 (m7RowsPart1 tPfx) := by
  have hc := m7Part1Callees_of_sub hOwn
  have sub_dim : ∀ e ∈ p1DimacsIsqrtIlogRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; exact List.mem_append_left _ h)
  have sub_ar : ∀ e ∈ p1Full1ArenaRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 2 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wg0 : ∀ e ∈ p1WatchGc0Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 3 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_heap : ∀ e ∈ p1HeapRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 5 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bump : ∀ e ∈ p1BumpSchedRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 8 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_m7bs : ∀ e ∈ p1M7BumpSchedRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_init : ∀ e ∈ p1InitAssignRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_hdr0 : ∀ e ∈ p1Hdr0ExactRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 11 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ph : ∀ e ∈ p1ParseHelpersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 12 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_prph : ∀ e ∈ p1PropHelpersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 13 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_rec : ∀ e ∈ p1RecomputeTiersRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 17 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wg1 : ∀ e ∈ p1WatchGc1Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 18 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wg2 : ∀ e ∈ p1WatchGc2Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 19 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_copy : ∀ e ∈ p1SweepCopyRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 23 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wg3 : ∀ e ∈ p1WatchGc3Rows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 25 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_reds : ∀ e ∈ p1RedsRows, e ∈ tbl := fun _ h => hOwn _ (by
    unfold m7RowsPart1; (iterate 28 apply List.mem_append_right); exact List.mem_append_left _ h)
  have rSift := sub_ar _ (List.mem_of_getElem? (i := 2) rfl)
  have rWs := sub_dim _ (List.mem_of_getElem? (i := 2) rfl)
  have rHdr := sub_dim _ (List.mem_of_getElem? (i := 5) rfl)
  have rNLit := sub_dim _ (List.mem_of_getElem? (i := 6) rfl)
  have rHUp := sub_heap _ (List.mem_of_getElem? (i := 0) rfl)
  have rHPush := sub_heap _ (List.mem_of_getElem? (i := 2) rfl)
  have rInitSt := sub_init _ (List.mem_of_getElem? (i := 16) rfl)
  have rSkip := sub_ph _ (List.mem_of_getElem? (i := 0) rfl)
  have rIng := sub_ph _ (List.mem_of_getElem? (i := 1) rfl)
  have rRec := sub_rec _ (List.mem_of_getElem? (i := 0) rfl)
  have rWDefM6 := sub_wg0 _ (List.mem_of_getElem? (i := 1) rfl)
  have rWPshM6 := sub_wg0 _ (List.mem_of_getElem? (i := 2) rfl)
  have rRankM6 := sub_wg1 _ (List.mem_of_getElem? (i := 0) rfl)
  have rSwRM6 := sub_wg1 _ (List.mem_of_getElem? (i := 1) rfl)
  have rRewRM6 := sub_wg2 _ (List.mem_of_getElem? (i := 0) rfl)
  have rCopy := sub_copy _ (List.mem_of_getElem? (i := 0) rfl)
  have rSortReds := sub_reds _ (List.mem_of_getElem? (i := 2) rfl)
  have rWPush := htPfx _ hPfxSpecs.watchPush
  have rWDefrag := htPfx _ hPfxSpecs.wstackDefrag
  have rRescale := htPfx _ hPfxSpecs.rescale
  have rMrkRsn := htPfx _ hPfxSpecs.markReasons
  have rArSwp := htPfx _ hPfxSpecs.arenaSweep
  have ps : ∀ off n,
      TableImpl (Env.ofTable tbl) ((m7OrchPfxFns.drop off).take n) ((tPfx.drop off).take n) :=
    tableImpl_drop_take hPfxLen hPfxOk
  have hlen_p : ∀ (off n : Nat),
      ((m7OrchPfxFns.drop off).take n).length = ((tPfx.drop off).take n).length := by
    intro off n; simp [hPfxLen]
  have i_dim := (fullSliceTransport 0 10 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_dim
    (fun _ h => nomatch h)).2
  have i_rng : TableImpl (Env.ofTable tbl) p1RngNextFns p1RngNextRows :=
    m7_oneImpl rfl rfl (FullM7Bump.m7RngNextFn_wp (Env.ofTable tbl))
  have i_ar := (fullSliceTransport 11 3 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_ar
    (fun _ h => nomatch h)).2
  have i_wg0 := p1WatchGc0_impl hnd sub_wg0 rSift
  have i_heap := (fullSliceTransport 16 4 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_heap
    (fun _ h => nomatch h)).2
  have i_resM6 : TableImpl (Env.ofTable tbl) p1RescaleM6Fns p1RescaleM6Rows :=
    m7_oneImpl rfl rfl (FullM6WalkParse.full_rescale_m6_wp (Env.ofTable tbl))
  have i_bump := p1BumpSched_impl hnd sub_bump rHUp rRescale
  have i_m7bs := p1M7BumpSched_impl hnd sub_m7bs hc.log10Q16M7
  have i_init := p1InitAssign_impl hnd sub_init rHdr hc.allocCl rWPush rHPush
  have i_hdr0 := p1Hdr0_impl hnd sub_hdr0 rInitSt
  have i_ph := (fullSliceTransport 42 2
    [ ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
    , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], Full.fullAddClauseSpec, true⟩ ]
    (by t_kernel_rfl)
    (m7_memC (fullRow_at 6 _) (m7_memC (fullRow_at 27 _) (m7_mem1 (fullRow_at 31 _))))
    hnd sub_ph (m7_memC rNLit (m7_memC hc.assignLvl (m7_mem1 hc.addClause)))).2
  have i_prph : TableImpl (Env.ofTable tbl) p1PropHelpersFns p1PropHelpersRows := by
    have hs := (fullSliceTransport 45 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
      (fun _ h => sub_prph _ (List.mem_append_left _ h)) (fun _ h => nomatch h)).2
    have hu : TableImpl (Env.ofTable tbl) (FullM5Otfs.m5Otfs_fns.take 1)
        [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩] :=
      m7_oneImpl rfl rfl (FullM5Otfs.full_unwatch_large_wp (Env.ofTable tbl))
    exact tableImpl_append rfl hs hu
  have i_bcp := p1BcpHot_impl hnd hBcpHot hc.propIgnoreHot rWPush
  have i_pbM6 : TableImpl (Env.ofTable tbl) p1ParseBodyM6Fns p1ParseBodyM6Rows :=
    m7_oneImpl rfl rfl (FullM6WalkParse.full_parse_body_m6_del_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rSkip) (envRow_mem hnd _ _ _ _ rIng)
      (m7_fullPropagate_to_del (envRow_mem hnd _ _ _ _ hc.propagate))
      (envRow_mem hnd _ _ _ _ rWs))
  have i_rec := (fullSliceTransport 50 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_rec
    (fun _ h => nomatch h)).2
  have i_wg1 := p1WatchGc1_impl hnd rWDefM6
  have i_wg2 := p1WatchGc2_impl hnd sub_wg2 rRankM6 rWPshM6
  have i_swb : TableImpl (Env.ofTable tbl) p1SweepBinsM6cfFns p1SweepBinsM6cfRows :=
    m7_oneImpl rfl rfl (FullM6CompactFlush.full_sweep_bins_m6cf_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ rWDefrag))
  have i_copy := (fullSliceTransport 58 1
    [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ]
    (by t_kernel_rfl) (m7_memC (fullRow_at 15 _) (m7_mem1 (fullRow_at 27 _)))
    hnd sub_copy (m7_memC rWPush (m7_mem1 hc.assignLvl))).2
  have i_wg3 := p1WatchGc3_impl hnd sub_wg3 rSwRM6 rRewRM6 hc.arenaNext rCopy
  have i_flsh : TableImpl (Env.ofTable tbl) p1FlushTrailFns p1FlushTrailRows :=
    m7_oneImpl rfl rfl (FullM6CompactFlush.full_flush_trail_del_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hc.backtrack)
      (m7_fullPropagate_to_del (envRow_mem hnd _ _ _ _ hc.propagate)))
  have i_reds := (fullSliceTransport 52 3 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd sub_reds
    (fun _ h => nomatch h)).2
  have i_red := p1Reduce_m7_impl hnd hc.isqrt hc.ilog10 hc.arenaNext rRec rMrkRsn rSortReds
    hc.backtrack hc.propagate rArSwp
  rw [p1Fns_eq]; unfold p1FnsSeg m7RowsPart1
  refine tableImpl_append rfl i_dim (tableImpl_append rfl i_rng (tableImpl_append rfl i_ar ?_))
  refine tableImpl_append rfl i_wg0 (tableImpl_append (hlen_p 0 2) (ps 0 2) ?_)
  refine tableImpl_append rfl i_heap (tableImpl_append rfl i_resM6 ?_)
  refine tableImpl_append (hlen_p 2 1) (ps 2 1) (tableImpl_append rfl i_bump ?_)
  refine tableImpl_append rfl i_m7bs (tableImpl_append rfl i_init (tableImpl_append rfl i_hdr0 ?_))
  refine tableImpl_append rfl i_ph (tableImpl_append rfl i_prph (tableImpl_append rfl i_bcp ?_))
  refine tableImpl_append rfl i_pbM6 (tableImpl_append (hlen_p 3 1) (ps 3 1) ?_)
  refine tableImpl_append rfl i_rec (tableImpl_append rfl i_wg1 (tableImpl_append rfl i_wg2 ?_))
  refine tableImpl_append (hlen_p 4 1) (ps 4 1) (tableImpl_append rfl i_swb ?_)
  refine tableImpl_append (hlen_p 5 1) (ps 5 1) (tableImpl_append rfl i_copy ?_)
  refine tableImpl_append (hlen_p 6 1) (ps 6 1) (tableImpl_append rfl i_wg3 ?_)
  refine tableImpl_append (hlen_p 7 2) (ps 7 2) (tableImpl_append rfl i_flsh ?_)
  refine tableImpl_append rfl i_reds (tableImpl_append rfl i_red ?_)
  exact ps 9 1

theorem m7_mem_drop_take_of_lt {α : Type _} (xs : List α) {off n i : Nat}
    (hoff : off ≤ i) (hin : i < off + n) (hit : i < xs.length) :
    xs[i] ∈ (xs.drop off).take n := by
  have hj : i - off < ((xs.drop off).take n).length := by
    rw [List.length_take, List.length_drop]; omega
  have hget : ((xs.drop off).take n)[i - off]'hj = xs[i]'hit := by
    rw [List.getElem_take, List.getElem_drop]; congr 1; omega
  rw [← hget]; exact List.getElem_mem hj

theorem m7RowsPart1_tPfx_mem {tPfx : List SpecEntry} {i : Nat}
    (hi : i < 10) (hit : i < tPfx.length) :
    tPfx[i] ∈ m7RowsPart1 tPfx := by
  unfold m7RowsPart1
  rcases Nat.lt_or_ge i 2 with h02 | h2
  · (iterate 4 apply List.mem_append_right); apply List.mem_append_left
    simpa [List.drop_zero] using m7_mem_drop_take_of_lt tPfx (Nat.zero_le _) h02 hit
  · rcases Nat.lt_or_ge i 3 with h23 | h3
    · (iterate 7 apply List.mem_append_right); apply List.mem_append_left
      exact m7_mem_drop_take_of_lt tPfx h2 h23 hit
    · rcases Nat.lt_or_ge i 4 with h34 | h4
      · (iterate 16 apply List.mem_append_right); apply List.mem_append_left
        exact m7_mem_drop_take_of_lt tPfx h3 h34 hit
      · rcases Nat.lt_or_ge i 5 with h45 | h5
        · (iterate 20 apply List.mem_append_right); apply List.mem_append_left
          exact m7_mem_drop_take_of_lt tPfx h4 h45 hit
        · rcases Nat.lt_or_ge i 6 with h56 | h6
          · (iterate 22 apply List.mem_append_right); apply List.mem_append_left
            exact m7_mem_drop_take_of_lt tPfx h5 h56 hit
          · rcases Nat.lt_or_ge i 7 with h67 | h7
            · (iterate 24 apply List.mem_append_right); apply List.mem_append_left
              exact m7_mem_drop_take_of_lt tPfx h6 h67 hit
            · rcases Nat.lt_or_ge i 9 with h79 | h9
              · (iterate 26 apply List.mem_append_right); apply List.mem_append_left
                exact m7_mem_drop_take_of_lt tPfx h7 h79 hit
              · (iterate 30 apply List.mem_append_right)
                exact m7_mem_drop_take_of_lt tPfx h9 (by omega) hit

theorem m7Part1TailCallees_of_sub {tPfx tbl : List SpecEntry}
    (hsub : ∀ e ∈ m7RowsPart1 tPfx, e ∈ tbl) :
    (⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
      fullM6MemInitExactSpec, true⟩ : SpecEntry) ∈ tbl ∧
    (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩ : SpecEntry) ∈ tbl := by
  have hmi : p1Hdr0ExactRows[6]? = some
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64],
        fullM6MemInitExactSpec, true⟩ := rfl
  have hck : p1DimacsIsqrtIlogRows[7]? = some
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
        kissatCheckModelExactSpec, true⟩ := rfl
  exact ⟨ hsub _ (by
      unfold m7RowsPart1; (iterate 11 apply List.mem_append_right); apply List.mem_append_left
      exact List.mem_of_getElem? hmi)
    , hsub _ (by
      unfold m7RowsPart1; apply List.mem_append_left; exact List.mem_of_getElem? hck) ⟩

end LeanQbe.T.Examples.Kissat.FullM7Proof
