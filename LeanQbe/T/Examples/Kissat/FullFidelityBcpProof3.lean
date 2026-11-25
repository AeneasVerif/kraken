/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof1
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof
public import LeanQbe.T.Examples.Kissat.FullM7HotWatchPushProof
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProofWatch
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Delayed-Watch BCP Bundle Base, `full_bcp_hot` S15 Bridge, & Delayed NV State
(`FullFidelityBcpProof3`)

Plain `public section` (`0` `@[expose]`, `0` `public import all`, `std3` axioms only):
1. `fidWatchPushWrapFn`: minimal forwarding bridge `"full_watch_push"` → `"full_watch_push_m6"`
   connecting `FullM7BcpHot` callers (`full_prop_lit_ovf_hot`, `full_prop_chrono_hot`,
   `full_prop_flush_del_fid`) directly to `FullM6WatchGc` / `FullM7HotWatchPush`.
2. Closed BCP-level flat `Env.ofTable` base module (`fidBcpHotPushBaseMod`,
   `fidBcpHotPushBaseSpecTable`, `fidBcpHotPushBaseEnv`, `fidBcpHotPushBase_moduleOk`).
3. `full_bcp_hot_s15_wp`: proves `FullM7BcpHot.full_bcp_hot_body` against
   `FullM6BcpS15.fullBcpS15Spec` given `full_propagate_ignore_hot : fullPropagateIgnoreS15Spec`.
4. Concrete `Mem 64` non-bailout (`delayed_cap = 1 > 0`) witness states (`nvDelayedState`,
   `nvFlushDelState`) with verified `FullMem`, `LengthsOk`, `FullWitnessInv`, and
   `DelayedWatchesOk` invariants on the UNSAT 3-var instance `[[1, 3, 4], [0], [2], [3, 5]]`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6WatchGc
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
open Kraken.Bedrock2.Test

/-! ## 1. `full_watch_push` Connector & `full_bcp_hot` `S15` Wrapper -/

kissat_c0! fid_watch_push_wrap "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;
typedef struct { KissatDimacs d; } FullHdr;
extern bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  return full_watch_push_m6(h, lit, w0, w1, cnt);
}
"

/-- Canonical `"full_watch_push"` wrapper delegating directly to `"full_watch_push_m6"`. -/
def fidWatchPushWrapFn : Fn :=
  ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], full_watch_push_body⟩

theorem full_watch_push_wrap_wf : Func.Wf full_watch_push_body := by t_wf_reify

theorem fidWatchPushWrapFn_wf : fidWatchPushWrapFn.Wf := full_watch_push_wrap_wf

theorem fid_watch_push_wrap_wp (Γ : Env)
    (hM6 : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Func.wp Γ full_watch_push_body a m Q X := by
  intro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X hPre
  unfold Func.wp full_watch_push_body
  c0_hsteps
  c0_call hM6
  exact hPre

/-- Certifies `FullM7BcpHot.full_bcp_hot_body` against `FullM6BcpS15.fullBcpS15Spec` when
`"full_propagate_ignore_hot"` satisfies `FullM6BcpS15.fullPropagateIgnoreS15Spec`. -/
theorem full_bcp_hot_s15_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, FullM6BcpS15.fullPropagateIgnoreS15Spec args m Q X →
      Γ "full_propagate_ignore_hot" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, FullM6BcpS15.fullBcpS15Spec args m Q X →
      Func.wp Γ FullM7BcpHot.full_bcp_hot_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  unfold Func.wp FullM7BcpHot.full_bcp_hot_body
  c0_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
      hlen' hw' htr' hperm' hdel0 hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  c0_hsteps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hw' htr' hperm' hdel0 hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hc, _⟩ := hr1 h1; ⟨hf, ho, hc⟩)
    hr2 hnoop hm'

/-! ## 2. Closed BCP-Level Flat `Env.ofTable` Base Module (`fidBcpHotPushBaseMod`) -/

/-- Canonical `"full_watch_push_m6"` (`FullM6WatchGc`) function handle in the pre-patch base. -/
def m6WatchPushFn : Fn :=
  ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
    FullM6WatchGc.full_watch_push_m6_body⟩

/-- Pre-patch BCP+WatchPush flat base module (`6` defined fns, `3` externs, `0` exits). -/
def fidBcpHotPushBaseMod : LeanQbe.T.Module :=
  { fns := [m6WatchPushFn, fidWatchPushWrapFn] ++ FullM7BcpHot.m7BcpHot_fns
  , externs :=
      [ ⟨"full_wstack_defrag_m6", [i64], []⟩
      , ⟨"full_wstack_defrag", [i64], []⟩
      , ⟨"full_unwatch_large", [i64, i32, i32], []⟩ ]
  , exits := [] }

/-- `9`-row specification table for `fidBcpHotPushBaseMod` (`6` fns + `3` externs). -/
def fidBcpHotPushBaseSpecTable : List SpecEntry :=
  [ ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool], FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_bcp_hot", [i64], [i64], Full.FullPropDecSpecs.fullPropagateSpec, true⟩
  , ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ]

def fidBcpHotPushBaseEnv : Env := Env.ofTable fidBcpHotPushBaseSpecTable

theorem fidBcpHotPushBaseSpecTable_nodup :
    (fidBcpHotPushBaseSpecTable.map SpecEntry.name).Nodup := by
  show (["full_watch_push_m6", "full_watch_push", "full_prop_lit_ovf_hot",
    "full_prop_chrono_hot", "full_propagate_ignore_hot", "full_bcp_hot",
    "full_wstack_defrag_m6", "full_wstack_defrag", "full_unwatch_large"] : List String).Nodup
  decide

theorem fidBcpHotPushBase_acyclic : fidBcpHotPushBaseMod.checkAcyclic = true := by
  t_kernel_rfl

theorem fidBcpHotPushBase_fns_wf : AllFns Fn.Wf fidBcpHotPushBaseMod.fns := by
  have hm7 := FullM7BcpHot.m7BcpHot_fns_wf
  refine ⟨FullM6WatchGc.full_watch_push_m6_wf, fidWatchPushWrapFn_wf, ?_⟩
  exact ⟨hm7 _ (by simp [FullM7BcpHot.m7BcpHot_fns, FullM7BcpHot.full_m7_bcp_hot_fns]),
    hm7 _ (by simp [FullM7BcpHot.m7BcpHot_fns, FullM7BcpHot.full_m7_bcp_hot_fns]),
    hm7 _ (by simp [FullM7BcpHot.m7BcpHot_fns, FullM7BcpHot.full_m7_bcp_hot_fns]),
    hm7 _ (by simp [FullM7BcpHot.m7BcpHot_fns, FullM7BcpHot.full_m7_bcp_hot_fns]), trivial⟩

private theorem baseEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : fidBcpHotPushBaseSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → fidBcpHotPushBaseEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) fidBcpHotPushBaseSpecTable_nodup (hno xs m Q X h)

theorem fidBcpHotPushBase_tableImpl :
    TableImpl fidBcpHotPushBaseEnv fidBcpHotPushBaseMod.fns fidBcpHotPushBaseSpecTable := by
  let hPushM6 := baseEnv_row_at 0
    ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hPush := baseEnv_row_at 1
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hOvf := baseEnv_row_at 2
    ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  let hChrono := baseEnv_row_at 3
    ⟨"full_prop_chrono_hot", [i64, i64], [.bool], FullM7BcpHot.fullPropChronoHotSpec, true⟩
  let hIgn := baseEnv_row_at 4
    ⟨"full_propagate_ignore_hot", [i64, i64], [i64],
      Full.FullPropDecSpecs.fullPropagateIgnoreSpec, true⟩
  let hDefM6 := baseEnv_row_at 6
    ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  let hDef := baseEnv_row_at 7
    ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  let hUnw := baseEnv_row_at 8
    ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  exact ⟨.of (FullM6WatchGc.full_watch_push_m6_wp fidBcpHotPushBaseEnv hDefM6),
    ⟨.of (fid_watch_push_wrap_wp fidBcpHotPushBaseEnv hPushM6),
    ⟨.of (FullM7BcpHot.full_prop_lit_ovf_hot_wp fidBcpHotPushBaseEnv hPush),
    ⟨.of (FullM7BcpHot.full_prop_chrono_hot_wp fidBcpHotPushBaseEnv hDef hUnw hPush),
    ⟨.of (FullM7BcpHot.full_propagate_ignore_hot_wp fidBcpHotPushBaseEnv hOvf hChrono),
    ⟨.of (FullM7BcpHot.full_bcp_hot_wp fidBcpHotPushBaseEnv hIgn), trivial⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for the pre-patch BCP + WatchPush base module under flat `Env.ofTable`. -/
theorem fidBcpHotPushBase_moduleOk :
    ModuleOk fidBcpHotPushBaseEnv fidBcpHotPushBaseMod :=
  Env.ofTable_moduleOk fidBcpHotPushBase_acyclic fidBcpHotPushBase_fns_wf
    fidBcpHotPushBase_tableImpl

/-! ## 3. Concrete `Mem 64` Non-Bailout (`delayed_cap = 1`) UNSAT & Flush Witness States -/

/-- UNSAT 3-var CNF `[[1, 3, 4], [0], [2], [3, 5]]` (`(~x0 | ~x1 | x2) & x0 & x1 & (~x1 | ~x2)`). -/
def nvDelayedF0 : CNF Nat := cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]

theorem nvDelayedF0_unsat : nvDelayedF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hs := CNF.sat_iff_all_mem_sat.mp hα
  have hc0 : (cnfClause [0]).Sat α :=
    hs _ (CNF.Internal.mem_iff.mpr (by simp [nvDelayedF0, cnfOfClauses]))
  have hc2 : (cnfClause [2]).Sat α :=
    hs _ (CNF.Internal.mem_iff.mpr (by simp [nvDelayedF0, cnfOfClauses]))
  have hc134 : (cnfClause [1, 3, 4]).Sat α :=
    hs _ (CNF.Internal.mem_iff.mpr (by simp [nvDelayedF0, cnfOfClauses]))
  have hc35 : (cnfClause [3, 5]).Sat α :=
    hs _ (CNF.Internal.mem_iff.mpr (by simp [nvDelayedF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc0 hc2 hc134 hc35
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := hc0
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc2
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc134
  obtain ⟨⟨v3, p3⟩, hm3, he3⟩ := hc35
  rw [mem_cnfClause_iff] at hm0 hm1 hm2 hm3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm0 hm1 hm2 hm3
  have hα0 : α 0 = true := by
    cases p0 <;> simp [litOfLiteral, mkLit] at hm0
    obtain rfl : v0 = 0 := by omega
    exact he0
  have hα1 : α 1 = true := by
    cases p1 <;> simp [litOfLiteral, mkLit] at hm1
    · omega
    · obtain rfl : v1 = 1 := by omega
      exact he1
  have hα2T : α 2 = true := by
    cases p2 <;> simp [litOfLiteral, mkLit] at hm2
    · rcases hm2 with h | h | h
      · obtain rfl : v2 = 0 := by omega
        dsimp only at he2; rw [he2] at hα0; cases hα0
      · obtain rfl : v2 = 1 := by omega
        dsimp only at he2; rw [he2] at hα1; cases hα1
      · omega
    · rcases hm2 with h | h | h
      · omega
      · omega
      · obtain rfl : v2 = 2 := by omega
        exact he2
  cases p3 <;> simp [litOfLiteral, mkLit] at hm3
  · rcases hm3 with h | h
    · obtain rfl : v3 = 1 := by omega
      dsimp only at he3; rw [he3] at hα1; cases hα1
    · obtain rfl : v3 = 2 := by omega
      dsimp only at he3; rw [he3] at hα2T; cases hα2T
  · omega

/-- Concrete `FullCfg` with `max_vars = 3`, `arena_cap = 6`, `wcap = 8`, `delayed_cap = 1`
(`avail = 2116`, `slack = 0`) exercising non-zero `h->delayed` buffering & linear flush. -/
def nvDelayedCfg : FullCfg where
  hdr := 0x1000#64
  avail := 2116
  mv := 3
  max_vars := 3
  bva_cap := 0
  nc := 4
  arena_cap := 6
  wcap := 8
  delayed_cap := 1
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

private def nvDelScratchBase : FullScratch where
  heap_len := 0
  scinc := 1#64
  rel_period := 0#64
  rel_limit := 0#64
  rel_wait := 0#64
  rel_u := 0#64
  rel_v := 0#64
  rel_trigger := 0#64
  conflicts := 0#64
  learned_lits := 0#64
  min_removed := 0#64
  delayed_len := 0
  stable := 0#64
  switched := 0#64
  mode_count := 0#64
  mode_confl_lim := 0#64
  mode_tick_lim := 0#64
  mode_saved_ticks := 0#64
  search_ticks := 0#64
  q_first := 0#64
  q_last := 0#64
  q_search_idx := 0#64
  q_search_stamp := 0#64
  q_cur_stamp := 0#64
  target_assigned := 0#64
  best_assigned := 0#64
  rephase_limit := 0#64
  rephased := 0#64
  reduce_limit := 0#64
  reductions := 0#64
  tier1 := 1#64
  tier2 := 2#64
  restarts := 0#64
  restart_limit := 0#64
  ema_fast_biased := 0#64
  ema_fast_exp := 0#64
  ema_slow_biased := 0#64
  ema_slow_exp := 0#64
  extend_len := 0
  rng_state := 1#64
  chrono_levels := 0#64
  otfs_cnt := 0#64
  eager_sub_cnt := 0#64
  probe_limit := 0#64
  probings := 0#64
  elim_limit := 0#64
  eliminations := 0#64
  elim_bound := 0#64
  iterating := 0#64
  hbr_cnt := 0#64
  trans_cnt := 0#64
  viv_cnt := 0#64
  subst_cnt := 0#64
  cong_cnt := 0#64
  sweep_cnt := 0#64
  bve_cnt := 0#64
  bce_cnt := 0#64
  bva_cnt := 0#64
  walk_cnt_stat := 0#64
  fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64
  ant_sz := 0#64
  res_sz := 0#64
  walk_vals := List.replicate 6 0#8
  phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8
  phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8
  heap := List.replicate 3 0#32
  pos := List.replicate 3 0#32
  shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0#32
  q_next := List.replicate 3 0#32
  q_stamp := List.replicate 3 0#32
  wsort := List.replicate 6 0#32
  work_stk1 := List.replicate 6 0#32
  work_stk2 := List.replicate 6 0#32
  tarjan_mark := List.replicate 6 0#32
  tarjan_reach := List.replicate 6 0#32
  score := List.replicate 3 0#64
  sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0#32
  delayed := [0#32, 0#32, 0#32]
  red_refs := []
  extend_stk := []
  scratch_buf := []

private def nvDelCoreBase : FullCoreState where
  d_cur := 0#64
  d_val := 0#64
  cur_vars := 3
  unassigned := 1#64
  arena_len := 6
  wlen := 6
  wusable := 0#64
  arena_garbage := 0#64
  first_reducible := 6#64
  num_irred := 1#64
  num_redundant := 0#64
  num_binary := 1#64
  unflushed := 0#64
  probing := 0#64
  trail_end := 2
  propagated := 0
  cur_level := 0
  fuel := 10#64
  confl_ref := 0xFFFFFFFF#64
  confl_type := 0#64
  confl_lit0 := 0#64
  confl_lit1 := 0#64
  tmp_cnt := 0
  tmp_len := 0
  min_clr_len := 0
  min_clr_full := 0#64
  oom := 0#64
  dense_mode := 0#64
  inconsistent := 0#64
  vals := [1#8, 0xFF#8, 1#8, 0xFF#8, 0#8, 0#8]
  lit_mark := List.replicate 6 0#8
  mrk := List.replicate 3 0#8
  flags := [0#32, 0#32, 1#32]
  lvl := [0#32, 0#32, 0#32]
  rsns := [0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32]
  trl := [0#32, 2#32, 0#32]
  trail_pos := [0#32, 1#32, 0#32]
  tmp := List.replicate 3 0#32
  min_clr := List.replicate 3 0#32
  frame_trail := [0#32, 0#32, 0#32, 0#32]
  frame_dec := [0#32, 0#32, 0#32, 0#32]
  wvec := [0#32, 0#32, 1#32, 2#32, 0#32, 0#32, 3#32, 3#32, 0#32, 0#32, 0#32, 0#32]
  repr := List.replicate 6 0#32
  min_stk := List.replicate 8 0#32
  arena := [0#32, 2#32, 3#32, 1#32, 3#32, 4#32]
  wstk := [0#32, 3#32, 0#32, 1#32, 0#32, 0x80000005#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32]

/-- Concrete initial state before `full_bcp_hot` on `nvDelayedF0` with `delayed_cap = 1`:
`x0 = T, x1 = T` on trail, `lit 1` (`~x0`) watches clause `[1, 3, 4]` with unassigned repl `4`. -/
def nvDelayedState : FullState where
  core := nvDelCoreBase
  scratch := nvDelScratchBase

/-- Concrete mid-scan flush state before `full_prop_flush_del_fid(h, 3#64)` with
`delayed = [4#32, 3#32, 0#32]` (`dlen = 1`, `skip_lit = 1`) and swapped clause `[3, 4, 1]`. -/
def nvFlushDelState : FullState where
  core :=
    { nvDelCoreBase with
      wusable := 2#64
      wvec := [0#32, 0#32, 1#32, 0#32, 0#32, 0#32, 3#32, 3#32, 0#32, 0#32, 0#32, 0#32]
      arena := [0#32, 2#32, 3#32, 3#32, 4#32, 1#32] }
  scratch := { nvDelScratchBase with delayed := [4#32, 3#32, 0#32] }

private def nvDelBlockHdr (s : FullState) : List UInt8 :=
  bytes64 [3#64, 4#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvDelayedCfg s)

private def nvDelBlockBytes (s : FullState) : List UInt8 :=
  (bytesOf (t := i8) s.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) s.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) s.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) s.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) s.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) s.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) s.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) s.scratch.walk_best ++ List.replicate 5 0)

private def nvDelBlockU32A (s : FullState) : List UInt8 :=
  (bytesOf (t := i32) s.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.trail_pos ++ List.replicate 4 0)

private def nvDelBlockU32B (s : FullState) : List UInt8 :=
  (bytesOf (t := i32) s.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.scratch.shrink_stk ++ List.replicate 4 0)

private def nvDelBlockU32C (s : FullState) : List UInt8 :=
  (bytesOf (t := i32) s.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) s.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) s.core.frame_dec ++ List.replicate 0 0)

private def nvDelBlockWvec (s : FullState) : List UInt8 :=
  bytesOf (t := i32) s.core.wvec ++
  bytesOf (t := i32) s.core.repr ++
  bytesOf (t := i32) s.scratch.wsort ++
  bytesOf (t := i32) s.scratch.work_stk1 ++
  bytesOf (t := i32) s.scratch.work_stk2 ++
  bytesOf (t := i32) s.scratch.tarjan_mark ++
  bytesOf (t := i32) s.scratch.tarjan_reach ++
  bytes64 s.scratch.score ++
  bytes64 s.scratch.sim_sig

private def nvDelBlockTail (s : FullState) : List UInt8 :=
  bytesOf (t := i32) s.core.min_stk ++
  bytesOf (t := i32) s.scratch.glue_used ++
  bytesOf (t := i32) s.scratch.last_learned ++
  bytesOf (t := i32) s.core.arena ++
  bytesOf (t := i32) s.core.wstk ++
  bytesOf (t := i32) s.scratch.delayed ++
  bytesOf (t := i32) s.scratch.red_refs ++
  bytesOf (t := i32) s.scratch.extend_stk ++
  bytesOf (t := i32) s.scratch.scratch_buf ++
  List.replicate 0 0

private def nvDelStateBytes (s : FullState) : List UInt8 :=
  nvDelBlockHdr s ++ nvDelBlockBytes s ++ nvDelBlockU32A s ++ nvDelBlockU32B s ++
  nvDelBlockU32C s ++ nvDelBlockWvec s ++ nvDelBlockTail s

def nvDelayedMem : Mem 64 := (nvDelStateBytes nvDelayedState).At nvDelayedCfg.hdr
def nvFlushDelMem : Mem 64 := (nvDelStateBytes nvFlushDelState).At nvDelayedCfg.hdr

private theorem nvDel_fullMem_of {s : FullState}
    (hs : s = nvDelayedState ∨ s = nvFlushDelState) :
    FullMem nvDelayedCfg s ((nvDelStateBytes s).At nvDelayedCfg.hdr) := by
  let c := nvDelayedCfg
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : Full.u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu16 : Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv3 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv6 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv16 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hlen_vals : s.core.vals.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wvals : s.scratch.walk_vals.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_lm : s.core.lit_mark.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_mrk : s.core.mrk.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ph : s.scratch.phases.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_pht : s.scratch.phases_target.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_phb : s.scratch.phases_best.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wb : s.scratch.walk_best.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_fl : s.core.flags.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_lvl : s.core.lvl.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_rsn : s.core.rsns.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_trl : s.core.trl.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_tp : s.core.trail_pos.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_tmp : s.core.tmp.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_hp : s.scratch.heap.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_pos : s.scratch.pos.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_mc : s.core.min_clr.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ss : s.scratch.shrink_stk.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_qp : s.scratch.q_prev.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_qn : s.scratch.q_next.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_qs : s.scratch.q_stamp.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ft : s.core.frame_trail.length = 4 := by rcases hs with rfl | rfl <;> rfl
  have hlen_fd : s.core.frame_dec.length = 4 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wv : s.core.wvec.length = 12 := by rcases hs with rfl | rfl <;> rfl
  have hlen_rp : s.core.repr.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ws : s.scratch.wsort.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wk1 : s.scratch.work_stk1.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wk2 : s.scratch.work_stk2.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_tm : s.scratch.tarjan_mark.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_tr : s.scratch.tarjan_reach.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_sc : s.scratch.score.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ssg : s.scratch.sim_sig.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ms : s.core.min_stk.length = 8 := by rcases hs with rfl | rfl <;> rfl
  have hlen_gu : s.scratch.glue_used.length = 64 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ll : s.scratch.last_learned.length = 16 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ar : s.core.arena.length = 6 := by rcases hs with rfl | rfl <;> rfl
  have hlen_wstk : s.core.wstk.length = 8 := by rcases hs with rfl | rfl <;> rfl
  have hlen_del : s.scratch.delayed.length = 3 := by rcases hs with rfl | rfl <;> rfl
  have hlen_red : s.scratch.red_refs.length = 0 := by rcases hs with rfl | rfl <;> rfl
  have hlen_ext : s.scratch.extend_stk.length = 0 := by rcases hs with rfl | rfl <;> rfl
  have hlen_sb : s.scratch.scratch_buf.length = 0 := by rcases hs with rfl | rfl <;> rfl
  have hd_cur : s.core.d_cur = 0#64 := by rcases hs with rfl | rfl <;> rfl
  have hd_val : s.core.d_val = 0#64 := by rcases hs with rfl | rfl <;> rfl
  have hHdr : (nvDelBlockHdr s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((nvDelBlockHdr s).At c.hdr) := by
    rw [hd_cur, hd_val]
    exact Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [3#64, 4#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : (nvDelBlockBytes s).length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        ((nvDelBlockBytes s).At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2
      (by rw [hlen_vals]; decide) (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2
      (by rw [hlen_wvals]; decide) (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2
      (by rw [hlen_lm]; decide) (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5
      (by rw [hlen_mrk]; decide) (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5
      (by rw [hlen_ph]; decide) (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 3 5 (by rw [hlen_pht]; decide) (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5
      (by rw [hlen_phb]; decide) (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5
      (by rw [hlen_wb]; decide) (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv6, hmv3]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : (nvDelBlockU32A s).length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        ((nvDelBlockU32A s).At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4
      (by rw [hlen_fl]; decide) (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4
      (by rw [hlen_lvl]; decide) (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4
      (by rw [hlen_rsn]; decide) (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4
      (by rw [hlen_trl]; decide) (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4
      (by rw [hlen_tp]; decide) (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv12]; exact sep_ac hm
  have hU32B : (nvDelBlockU32B s).length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        ((nvDelBlockU32B s).At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4
      (by rw [hlen_tmp]; decide) (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4
      (by rw [hlen_hp]; decide) (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4
      (by rw [hlen_pos]; decide) (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4
      (by rw [hlen_mc]; decide) (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      12 4 (by rw [hlen_ss]; decide) (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv12]; exact sep_ac hm
  have hU32C : (nvDelBlockU32C s).length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        ((nvDelBlockU32C s).At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4
      (by rw [hlen_qp]; decide) (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4
      (by rw [hlen_qn]; decide) (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4
      (by rw [hlen_qs]; decide) (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0
      (by rw [hlen_ft]; decide) (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0
      (by rw [hlen_fd]; decide) (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu16, hmv12, hmv16]; exact sep_ac hm
  have hWvec : (nvDelBlockWvec s).length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        ((nvDelBlockWvec s).At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48
      (by rw [hlen_wv]; decide) (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24
      (by rw [hlen_rp]; decide) (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24
      (by rw [hlen_ws]; decide) (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24
      (by rw [hlen_wk1]; decide) (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24
      (by rw [hlen_wk2]; decide) (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24
      (by rw [hlen_tm]; decide) (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24
      (by rw [hlen_tr]; decide) (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24
      (by rw [hlen_sc]) (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24
      (by rw [hlen_ssg]) (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : (nvDelBlockTail s).length = 420 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvDelBlockTail s).At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32
      (by rw [hlen_ms]; decide) (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256
      (by rw [hlen_gu]; decide) (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64
      (by rw [hlen_ll]; decide) (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24
      (by rw [hlen_ar]; decide) (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 32
      (by rw [hlen_wstk]; decide) (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 12
      (by rw [hlen_del]; decide) (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0
      (by rw [hlen_red]; decide) (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0
      (by rw [hlen_ext]; decide) (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0
      (by rw [hlen_sb]; decide) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨[], by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide))
      fun _ hm => by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Full.nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvDelayedMem_ok : FullMem nvDelayedCfg nvDelayedState nvDelayedMem :=
  nvDel_fullMem_of (Or.inl rfl)

theorem nvFlushDelMem_ok : FullMem nvDelayedCfg nvFlushDelState nvFlushDelMem :=
  nvDel_fullMem_of (Or.inr rfl)

theorem nvDelayed_lengths : nvDelayedState.LengthsOk nvDelayedCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, by decide, by decide, by decide, by decide,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem nvFlushDel_lengths : nvFlushDelState.LengthsOk nvDelayedCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, by decide, by decide, by decide, by decide,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvDel_entails_list {cl : List Nat}
    (hcl : cl ∈ [[1, 3, 4], [0], [2], [3, 5]]) :
    (cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by
    simp only [cnfOfClauses, List.mem_toArray, List.mem_map]; exact ⟨cl, hcl, rfl⟩))

private theorem nvDel_entails_134 :
    (cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]).EntailsClause (cnfClause [1, 3, 4]) :=
  nvDel_entails_list (by simp)

private theorem nvDel_entails_35 :
    (cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]).EntailsClause (cnfClause [3, 5]) :=
  nvDel_entails_list (by simp)

private theorem nvDel_entails_1 :
    (cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]).EntailsClause (cnfClause [0]) :=
  nvDel_entails_list (by simp)

private theorem nvDel_entails_2 :
    (cnfOfClauses [[1, 3, 4], [0], [2], [3, 5]]).EntailsClause (cnfClause [2]) :=
  nvDel_entails_list (by simp)

theorem nvDelayed_witness :
    FullWitnessInv nvDelayedCfg nvDelayedF0 [[1, 3, 4], [0], [2], [3, 5]]
      nvDelayedState.core := by
  have hrefs : fullArenaClauseRefsCore nvDelayedState.core = [0] := by
    unfold fullArenaClauseRefsCore nvDelayedState nvDelCoreBase; decide
  have hcv : nvDelayedState.core.cur_vars = 3 := rfl
  have hte : nvDelayedState.core.trail_end = 2 := rfl
  have hcl : nvDelayedState.core.cur_level = 0 := rfl
  have hdm : nvDelayedState.core.dense_mode = 0#64 := rfl
  have hwat : Full.ModeWatchesInv [[1, 3, 4], [0], [2], [3, 5]] nvDelayedState.core := by
    unfold Full.ModeWatchesInv; rw [ite_eq_left hdm]
    refine Full.WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) (fun l hl => ?_)
    · rw [hcv] at hl
      unfold fullWatchOffCore fullWatchSizeCore nvDelayedState nvDelCoreBase
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; revert hp; unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
      · unfold fullWatchOffCore nvDelayedState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
      · unfold fullWatchOffCore nvDelayedState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
    · rw [hcv] at h1 h2
      rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (by omega : l2 = 0 ∨ l2 = 1 ∨ l2 = 2 ∨ l2 = 3 ∨ l2 = 4 ∨ l2 = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact absurd rfl hne) <;>
        (try (exfalso; revert hp1
              unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide)) <;>
        (try (exfalso; revert hp2
              unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide)) <;>
        (unfold fullWatchOffCore fullWatchSizeCore nvDelayedState nvDelCoreBase; decide)
    · rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact Full.WatchSliceOk.empty
      · have ho1 : fullWatchOffCore nvDelayedState.core 1 = 1 := by
          unfold fullWatchOffCore nvDelayedState nvDelCoreBase; decide
        have hs1 : fullWatchSizeCore nvDelayedState.core 1 = 2 := by
          unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
        rw [ho1, hs1]
        exact .large (w0 := 3#32) (cref := 0#32)
          (by unfold nvDelayedState nvDelCoreBase; decide)
          (by unfold nvDelayedState nvDelCoreBase; decide)
          (by decide) (by decide) (by rw [hrefs]; decide) .empty
      · exact Full.WatchSliceOk.empty
      · have ho3 : fullWatchOffCore nvDelayedState.core 3 = 3 := by
          unfold fullWatchOffCore nvDelayedState nvDelCoreBase; decide
        have hs3 : fullWatchSizeCore nvDelayedState.core 3 = 3 := by
          unfold fullWatchSizeCore nvDelayedState nvDelCoreBase; decide
        rw [ho3, hs3]
        exact .large (w0 := 1#32) (cref := 0#32)
          (by unfold nvDelayedState nvDelCoreBase; decide)
          (by unfold nvDelayedState nvDelCoreBase; decide)
          (by decide) (by decide) (by rw [hrefs]; decide)
          (.bin (w0 := 0x80000005#32)
            (by unfold nvDelayedState nvDelCoreBase; decide)
            (by decide) (by decide) (by decide) nvDel_entails_35 .empty)
      · exact Full.WatchSliceOk.empty
      · exact Full.WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 3 [[1, 3, 4], [0], [2], [3, 5]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inr (by decide), fun r hr => by
          rw [hrefs] at hr; simp only [List.mem_singleton] at hr; subst hr
          refine ⟨by decide, by decide, by decide, by decide, ?_⟩
          unfold nvDelayedState nvDelCoreBase; decide,
        fun r hr hsh => by
          rw [hrefs] at hr; simp only [List.mem_singleton] at hr; subst hr
          exact absurd rfl hsh,
        fun r hr _ => by
          rw [hrefs] at hr; simp only [List.mem_singleton] at hr; subst hr
          intro l hl; revert l hl; unfold fullArenaClauseLitsCore nvDelayedState nvDelCoreBase
          decide,
        fun r hr _ => by
          rw [hrefs] at hr; simp only [List.mem_singleton] at hr; subst hr
          exact nvDel_entails_134⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      trail_vars_nodup := fun i j hi hj heq => by
        rw [hte] at hi hj
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · rfl
        · exfalso; revert heq; unfold nvDelayedState nvDelCoreBase; decide
        · exfalso; revert heq; unfold nvDelayedState nvDelCoreBase; decide
        · rfl
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          (unfold nvDelayedState nvDelCoreBase; decide)
      vals_true_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          constructor <;> intro h
        · exact ⟨0, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · exact ⟨1, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          constructor <;> intro h
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · exact ⟨0, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · exact ⟨1, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
        · cases h
        · rcases h with ⟨i, hi, h⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases h
      lvl_le := fun i hi => by
        rw [hte] at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact Nat.zero_le _
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          exact absurd hpos.1 (by decide)
      levels_inhabited := fun L _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact nvDel_entails_1
        · exact nvDel_entails_2
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := by omega
        unfold nvDelayedState nvDelCoreBase; decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := by omega
        obtain rfl : L2 = 0 := by omega
        unfold nvDelayedState nvDelCoreBase; decide
      frame_trail_before_lt := fun L _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne }

theorem nvFlushDel_watchLayout : WatchStackLayout nvFlushDelState.core :=
  ⟨fun l hl => by
      have hcv : nvFlushDelState.core.cur_vars = 3 := rfl
      rw [hcv] at hl
      unfold fullWatchOffCore fullWatchSizeCore nvFlushDelState nvDelCoreBase
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide,
   fun l hl hp => by
      have hcv : nvFlushDelState.core.cur_vars = 3 := rfl
      rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; revert hp; unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
      · unfold fullWatchOffCore nvFlushDelState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
      · exfalso; revert hp; unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide,
   fun l1 l2 h1 h2 hne hp1 hp2 => by
      have hcv : nvFlushDelState.core.cur_vars = 3 := rfl
      rw [hcv] at h1 h2
      rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (by omega : l2 = 0 ∨ l2 = 1 ∨ l2 = 2 ∨ l2 = 3 ∨ l2 = 4 ∨ l2 = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact absurd rfl hne) <;>
        (try (exfalso; revert hp1
              unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide)) <;>
        (exfalso; revert hp2
         unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide),
   fun l hl k hk => by
      have hcv : nvFlushDelState.core.cur_vars = 3 := rfl
      rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · have hs : fullWatchSizeCore nvFlushDelState.core 0 = 0 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 0 at hk; omega
      · have hs : fullWatchSizeCore nvFlushDelState.core 1 = 0 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 1 at hk; omega
      · have hs : fullWatchSizeCore nvFlushDelState.core 2 = 0 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 2 at hk; omega
      · have hs : fullWatchSizeCore nvFlushDelState.core 3 = 3 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        have ho : fullWatchOffCore nvFlushDelState.core 3 = 3 := by
          unfold fullWatchOffCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 3 at hk
        change nvFlushDelState.core.wstk[fullWatchOffCore nvFlushDelState.core 3 + k]? ≠ _
        rw [ho]; rw [hs] at hk
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
          (unfold nvFlushDelState nvDelCoreBase; decide)
      · have hs : fullWatchSizeCore nvFlushDelState.core 4 = 0 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 4 at hk; omega
      · have hs : fullWatchSizeCore nvFlushDelState.core 5 = 0 := by
          unfold fullWatchSizeCore nvFlushDelState nvDelCoreBase; decide
        change k < fullWatchSizeCore nvFlushDelState.core 5 at hk; omega⟩

theorem nvFlushDel_delayedOk :
    DelayedWatchesOk nvFlushDelState.core nvFlushDelState.scratch.delayed 1 1 := by
  unfold DelayedWatchesOk
  intro j hj
  obtain rfl : j = 0 := by omega
  have hrefs : fullArenaClauseRefsCore nvFlushDelState.core = [0] := by
    unfold fullArenaClauseRefsCore nvFlushDelState nvDelCoreBase; decide
  rw [hrefs]
  dsimp only [nvFlushDelState, nvDelScratchBase, nvDelCoreBase]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simp

/-- Parametric concrete `Mem 64` non-bailout (`delayed_cap = 1`, `di = 3`) delayed-watch flush NV
(`XPost := False`): executes `full_prop_flush_del_fid_body` on `nvFlushDelMem` for any `Γ`
implementing `"full_watch_push" : Full.fullWatchPushSpec`, returning `ok` cleanly with updated
`wvec`/`wstk`/`wlen`/`wusable` and preserving `LengthsOk`, `WatchStackLayout`, & `FullMem`. -/
theorem nv_fid_flush_del_of_env (Γ : Env)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    Func.wp Γ full_prop_flush_del_fid_body (nvDelayedCfg.hdr, 3#64, ()) nvFlushDelMem
      (fun (_ok, ()) m' =>
        nvDelayedF0.Unsat ∧
        ∃ wvec' wstk' wlen' wu' wsort',
          let st' : FullState :=
            { nvFlushDelState with
              core := { nvFlushDelState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
              scratch := { nvFlushDelState.scratch with wsort := wsort' } }
          st'.LengthsOk nvDelayedCfg ∧ WatchStackLayout st'.core ∧
          FullMem nvDelayedCfg st' m')
      (fun _ _ _ _ => False) :=
  full_prop_flush_del_fid_wp Γ hPush _ _ _ _
    (fidPropFlushDelSpec_of (c := nvDelayedCfg) (F_cur := [[1, 3, 4], [0], [2], [3, 5]])
      (st := nvFlushDelState) (R := emp) (dlen := 1) (skip_lit := 1)
      nvFlushDel_lengths nvFlushDel_watchLayout (by decide) (by decide)
      nvFlushDel_delayedOk (by rw [sep_emp]; exact nvFlushDelMem_ok)
      fun _ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' _ _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨nvDelayedF0_unsat, wvec', wstk', wlen', wu', wsort', hlen', hlay', hm'⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityBcp

end
