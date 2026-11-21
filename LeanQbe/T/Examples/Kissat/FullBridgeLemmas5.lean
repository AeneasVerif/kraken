module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas
public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Shards 9–11 (`Stage 4`)

Bridges all `18` functions across three landed Stage-4 shards directly onto canonical
`FullSpec2` / `FullSpec3` contracts (`18 / 18` clean, zero gaps):
- Part 1 (`FullWalkExtLemmas`, `11` fns): `full_bump_analyzed`, `full_next_dec_var`,
  `full_walk_collect`, `full_walk_cl_sat`, `full_walk_pick_lit`, `full_walk`, `full_switch_mode`,
  `full_restart_due`, `full_extend_push2`, `full_extend_push_cl`, `full_extend`.
- Part 2 (`FullSweepFwdLemmas`, `4` fns): `full_sweep_add_cl`, `full_sweep_cone`,
  `full_sweep_dpll`, `full_sweep_refine`.
- Part 3 (`FullLuckyLemmas`, `3` fns): `full_lucky_polar`, `full_lucky_scan`, `full_lucky`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## Part 1: `FullWalkExtLemmas` (`11` fns) -/

section Part1

theorem full_bump_analyzed_bridge_wp (Γ : Env)
    (hBump : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X → Func.wp Γ full_bump_analyzed_body a m Q X :=
  full_bump_analyzed_wp Γ hBump hMtf hDecay

theorem full_next_dec_var_bridge_wp (Γ : Env)
    (hPop : ∀ a m Q X, fullHeapPopSpec a m Q X → Γ "full_heap_pop" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullNextDecVarSpec a m Q X → Func.wp Γ full_next_dec_var_body a m Q X :=
  full_next_dec_var_wp Γ hPop

theorem full_walk_collect_bridge_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullWalkCollectSpec a m Q X → Func.wp Γ full_walk_collect_body a m Q X :=
  full_walk_collect_wp Γ hArenaNext

theorem full_walk_cl_sat_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullWalkClSatSpec a m Q X → Func.wp Γ full_walk_cl_sat_body a m Q X :=
  full_walk_cl_sat_wp Γ

theorem full_walk_pick_lit_bridge_wp (Γ : Env)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullWalkPickLitSpec a m Q X → Func.wp Γ full_walk_pick_lit_body a m Q X :=
  full_walk_pick_lit_wp Γ hRng

theorem full_walk_bridge_wp (Γ : Env)
    (hCollect : ∀ a m Q X, fullWalkCollectSpec a m Q X → Γ "full_walk_collect" [i64] [i64] a m Q X)
    (hClSat : ∀ a m Q X, fullWalkClSatSpec a m Q X →
      Γ "full_walk_cl_sat" [i64, i64, i64] [.bool] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, fullWalkPickLitSpec a m Q X →
      Γ "full_walk_pick_lit" [i64, i64, i64] [i32] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_body a m Q X :=
  full_walk_wp Γ hCollect hClSat hRng hPick

theorem full_switch_mode_bridge_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_body a m Q X :=
  full_switch_mode_wp Γ hDown hIlog

theorem full_restart_due_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullRestartDueSpec a m Q X → Func.wp Γ full_restart_due_body a m Q X :=
  full_restart_due_wp Γ

theorem full_extend_push2_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2Spec a m Q X → Func.wp Γ full_extend_push2_body a m Q X :=
  full_extend_push2_wp Γ

theorem full_extend_push_cl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClSpec a m Q X → Func.wp Γ full_extend_push_cl_body a m Q X :=
  full_extend_push_cl_wp Γ

theorem full_extend_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullExtendSpec a m Q X → Func.wp Γ full_extend_body a m Q X :=
  full_extend_wp Γ

end Part1

/-! ## Part 2: `FullSweepFwdLemmas` (`4` fns) -/

section Part2

theorem full_sweep_add_cl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSweepAddClSpec a m Q X → Func.wp Γ full_sweep_add_cl_body a m Q X :=
  full_sweep_add_cl_wp Γ

theorem full_sweep_cone_bridge_wp (Γ : Env)
    (hAddCl : ∀ a m Q X, fullSweepAddClSpec a m Q X →
      Γ "full_sweep_add_cl" [i64, i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSweepConeSpec a m Q X → Func.wp Γ full_sweep_cone_body a m Q X :=
  full_sweep_cone_wp Γ hAddCl

theorem full_sweep_dpll_bridge_wp (Γ : Env)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSweepDpllSpec a m Q X → Func.wp Γ full_sweep_dpll_body a m Q X :=
  full_sweep_dpll_wp Γ hRng

theorem full_sweep_refine_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSweepRefineSpec a m Q X → Func.wp Γ full_sweep_refine_body a m Q X :=
  full_sweep_refine_wp Γ

end Part2

/-! ## Part 3: `FullLuckyLemmas` (`3` fns) -/

section Part3

theorem full_lucky_polar_bridge_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullLuckyPolarSpec a m Q X → Func.wp Γ full_lucky_polar_body a m Q X :=
  full_lucky_polar_wp Γ hNext

theorem full_lucky_scan_bridge_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullLuckyScanSpec a m Q X → Func.wp Γ full_lucky_scan_body a m Q X :=
  full_lucky_scan_wp Γ hAssign hBt hProp hAna

theorem full_lucky_bridge_wp (Γ : Env)
    (hPolar : ∀ a m Q X, fullLuckyPolarSpec a m Q X →
      Γ "full_lucky_polar" [i64] [i64] a m Q X)
    (hScan : ∀ a m Q X, fullLuckyScanSpec a m Q X →
      Γ "full_lucky_scan" [i64, .bool, .bool] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullLuckySpec a m Q X → Func.wp Γ full_lucky_body a m Q X :=
  full_lucky_wp Γ hPolar hScan hAssign hBt hProp

end Part3

end LeanQbe.T.Examples.Kissat.Full
