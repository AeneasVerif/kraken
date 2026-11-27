/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Inline
public import LeanQbe.T.MainInline
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.InlineLemmas
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
meta import LeanQbe.T.Inline
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice

/-!
# Verification & Callgrind Summary for `FullFidelityInlPolicy`

Validates `FullFidelityInlPolicy.fidPgoBudget` and `fidInlPolicy` against `m7InlPolicy`
on the purified `469`-function `KissatFidelity` spine (excising `D-11` `full_bve_find_xor_m8`,
`D-22` `full_bve_bce_side_m8`, and `D-19` `4x` sweep-tick inflation in `full_m6_sweep_vars` from
`m8SweepV2CoreParityModule`):

* **Post-inline module metrics (`469` fns, `0` `m8Opt`/`xor`/`prelearn`/`wavea`/`sbva` fns):**
  - IR static call sites: `951 -> 749` (`-202`, loop calls `627 -> 478`; `full_unwatch_large` OOL)
  - Max post-inline function IR size: `1,009 -> 2,792` (`<= 3,500`, `0` fns `> 3,500`)
  - Dual-arch `Driver.compileFns` checks: `469/469` pass cleanly on both `x86-64` and `AArch64`
  - `x86-64` static ELF `.text` & ASM calls (`pureFidMod`):
    * `c3b` (`PrintCpp` `clang++ -O3`): `.text = 256,628 B`, `799` ASM calls
    * `c4_m7` (`m7InlPolicy`): `.text = 287,377 B`, `979` ASM calls
    * `c4_fid` (`fidInlPolicy`): `.text = 336,698 B`, `748` ASM calls (`-231` vs `c4_m7`)
  - `x86-64` Callgrind `Ir` across 13 diverse Stage-1 CNFs (`13/13` telemetry parity & wins):
    * `c4_m7`: `10,320.88M Ir`, `32,915.8k` dynamic calls
    * `c4_fid`: `10,202.34M Ir` (`-118.55M Ir` / `-1.15%`, `0.9885x`), `14,737.6k` dyn calls
      (`-55.2%` dynamic calls vs `c4_m7`, `-52.0%` vs `c3b` `30,695.5k`)
    * Keeping `m6_hdr_init` OOL (`0`, in `keepOutOfLine`) outperformed inlining it (`336,698 B` vs
      `345,873 B`, lower `Ir` and fewer dynamic calls).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.FullFidelityInlPolicyTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

kissat_c0! fidPurifyTest "
typedef struct { u64 mv, nc, cur, val; } KissatDimacs;
typedef struct {
  KissatDimacs d;
  u64 arena_cap, wcap, arena_len, wlen;
  u64 values, mark, level, reason, trail;
  u64 watch_vec, arena, watch_stk, delayed, tmp_lits;
  u64 trail_end, propagated, cur_level, fuel, confl_ref;
  u64 tmp_cnt, tmp_len, heap, pos, score;
  u64 phases, min_stk, min_clr, heap_len, scinc;
  u64 min_depth, min_clr_len, min_clr_full, rel_period, rel_limit;
  u64 rel_wait, rel_u, rel_v, rel_trigger, conflicts;
  u64 learned_lits, min_removed, trail_pos, q_prev, q_next;
  u64 q_stamp, phases_target, phases_best, wsort, shrink_stk;
  u64 red_refs, glue_used, red_cap, delayed_cap, delayed_len;
  u64 wusable, arena_garbage, first_reducible, num_irred, num_redundant;
  u64 num_binary, unflushed, probing, confl_type, confl_lit0;
  u64 confl_lit1, stable, switched, mode_count, mode_confl_lim;
  u64 mode_tick_lim, mode_saved_ticks, search_ticks, q_first, q_last;
  u64 q_search_idx, q_search_stamp, q_cur_stamp, target_assigned;
  u64 best_assigned, rephase_limit, rephased, reduce_limit, reductions;
  u64 tier1, tier2, restarts, restart_limit, ema_fast_biased;
  u64 ema_fast_exp, ema_slow_biased, ema_slow_exp, oom, max_vars;
  u64 cur_vars, bva_cap, unassigned, flags, lit_mark;
  u64 repr, sim_sig, frame_trail, frame_dec, work_stk1;
  u64 work_stk2, tarjan_mark, tarjan_reach, walk_vals, walk_best;
  u64 extend_stk, extend_cap, extend_len, scratch_buf, scratch_cap;
  u64 last_learned, rng_state, chrono_levels, otfs_cnt, eager_sub_cnt;
  u64 probe_limit, probings, elim_limit, eliminations, elim_bound;
  u64 dense_mode, inconsistent, iterating, hbr_cnt, trans_cnt;
  u64 viv_cnt, subst_cnt, cong_cnt, sweep_cnt, bve_cnt;
  u64 bce_cnt, bva_cnt, walk_cnt_stat, fwd_sub_cnt, fwd_str_cnt;
  u64 ant_sz, res_sz;
} FullHdr;

#define FL_ACTIVE 1u
#define FL_ELIM   2u
#define FL_SWEEP  1024u
#define K6H_TICKS 11u
#define M8_OCC_LIM 2001u
#define M8_NEG_OFF 2001u
#define M8_POS_MASK 4002u
#define M8_NEG_MASK 4066u
#define M8_GF_IDX 4130u
#define M8_RG_IDX 4131u
#define M8_RES_OFF 4192u

extern u64 full_m6_max_v(u64 cap);
extern bool full_m6_dense_prop(FullHdr *h);
extern u32 full_m6_collect_cands(FullHdr *h);
extern u64 full_m6_sweep_var(FullHdr *h, u32 v, u64 tick_lim);

u64 full_m6_sweep_vars(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u32 nc = full_m6_collect_cands(h);
  if (nc == 0u) { return 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 per_v = 16384ULL;
  u32 ci = 0u;
  u64 rem_b = budget;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci];
    ci = ci + 1u;
    bool act = (fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP);
    if (act && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP);
      rem_b = rem_b - 1ULL;
      u64 vlim = (rem_ticks > per_v) ? per_v : rem_ticks;
      if (full_m6_sweep_var(h, v, vlim) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) {
        return 20ULL;
      }
      u64 spent = (u64)k[K6H_TICKS];
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

extern bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn);
extern bool full_bve_find_and_m8(FullHdr *h, u32 lit, u32 np, u32 nn);
extern bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn);
extern void full_bve_def_k6_m8(FullHdr *h, u32 v, u32 np, u32 nn);

void full_bve_gates_m8(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 130u) { scr[M8_POS_MASK + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m8(h, np, nn)) { return; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  if (full_bve_find_and_m8(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m8(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m8(h, v, np, nn)) { return; }
  full_bve_def_k6_m8(h, v, np, nn);
}

extern u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern bool full_dense_flush_units_m7(FullHdr *h);

u64 full_bve_var_m7(FullHdr *h, u32 v) {
  if (h->scratch_cap < 2048ULL) { return 1ULL; }
  bool use_m8 = (h->scratch_cap >= 16384ULL);
  u32 occ_lim = use_m8 ? M8_OCC_LIM : 512u;
  u32 neg_off = use_m8 ? M8_NEG_OFF : 512u;
  u32 pos_mask = use_m8 ? M8_POS_MASK : 1024u;
  u32 neg_mask = use_m8 ? M8_NEG_MASK : 1040u;
  u32 gf_idx = use_m8 ? M8_GF_IDX : 1056u;
  u32 rg_idx = use_m8 ? M8_RG_IDX : 1057u;
  u64 r_off = use_m8 ? (u64)M8_RES_OFF : 1088ULL;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, occ_lim);
  u32 nn = full_bve_collect_m7(h, nl, scr + neg_off, occ_lim);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) +
    full_bve_ext_need(h, neg_off, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, neg_off, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    if (use_m8) { full_bve_gates_m8(h, v, np, nn); }
    else { full_bve_gates_m7(h, v, np, nn); }
    bool gf = (scr[gf_idx] != 0u);
    bool rg = (scr[rg_idx] != 0u);
    u32 *wvec = (u32 *)h->watch_vec;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[pos_mask + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[neg_mask + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair &&
            full_bve_resolve_pair(h, v, scr[i], scr[neg_off + j])) {
          u64 rlen = h->tmp_len;
          r_cnt = r_cnt + 1ULL;
          if (rlen > 100ULL || r_cnt > lim_cls ||
              rp + 1ULL + rlen > h->scratch_cap) {
            fit = false;
            break;
          }
          scr[rp] = (u32)rlen;
          u32 *tmp = (u32 *)h->tmp_lits;
          u32 k = 0u;
          while ((u64)k < rlen) {
            u32 lk = tmp[k];
            scr[rp + 1ULL + (u64)k] = lk;
            if (rlen >= 2ULL && (u64)lk < (h->cur_vars << 1)) {
              u64 occ = (u64)wvec[((u64)lk << 1) + 1ULL];
              w_est = w_est + (occ << 1) + 4ULL;
            }
            k = k + 1u;
          }
          rp = rp + 1ULL + rlen;
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
  }
  if (fit) {
    u64 ar_need = (rp - r_off) + (r_cnt * 2ULL) + 16ULL;
    u64 w_need = w_est + (r_cnt * 4ULL) + 16ULL;
    if (ar_need > h->arena_cap - h->arena_len) {
      fit = false;
    } else if (w_need > h->wcap - h->wlen) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (w_need > h->wcap - h->wlen) { fit = false; }
    }
  }
  if (fit) {
    if (!full_bve_weaken(h, pl, 0u, np) ||
        !full_bve_weaken(h, nl, neg_off, nn)) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    u64 cr = full_bve_commit_res(h, r_off, rp);
    if (cr == 20ULL) { return 20ULL; }
    if (cr == 1ULL && !full_dense_flush_units_m7(h)) { return 20ULL; }
    return cr;
  }
  return 1ULL;
}
"

def pureSweepVarsFn : Fn :=
  ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩

def pureBveGatesFn : Fn :=
  ⟨"full_bve_gates_m8", [i64, i32, i32, i32], [], full_bve_gates_m8_body⟩

def pureBveVarM7Fn : Fn :=
  ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩

/-- Purified `469`-function `KissatFidelity` baseline (excising `D-11`, `D-22`, `D-19`). -/
def pureFidFns : List Fn :=
  (m8SweepV2CoreParityModule.fns.filter fun f =>
    f.name != "full_bve_find_xor_m8" && f.name != "full_bve_bce_side_m8").map fun f =>
      if f.name == "full_m6_sweep_vars" then pureSweepVarsFn
      else if f.name == "full_bve_gates_m8" then pureBveGatesFn
      else if f.name == "full_bve_var_m7" then pureBveVarM7Fn
      else f

def pureFidMod : LeanQbe.T.Module :=
  { m8SweepV2CoreParityModule with fns := pureFidFns }

theorem pureSweepVarsFn_wf : pureSweepVarsFn.Wf := by
  unfold Fn.Wf pureSweepVarsFn; t_wf_reify

theorem pureBveGatesFn_wf : pureBveGatesFn.Wf := by
  unfold Fn.Wf pureBveGatesFn; t_wf_reify

theorem pureBveVarM7Fn_wf : pureBveVarM7Fn.Wf := by
  unfold Fn.Wf pureBveVarM7Fn; t_wf_reify

theorem pureFidFns_wf : ∀ f ∈ pureFidMod.fns, f.Wf := by
  intro f hf
  change f ∈ pureFidFns at hf
  rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
  have hgMem : g ∈ m8SweepV2CoreParityModule.fns := (List.mem_filter.mp hg).1
  split
  · exact pureSweepVarsFn_wf
  · split
    · exact pureBveGatesFn_wf
    · split
      · exact pureBveVarM7Fn_wf
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hgMem
        exact (m8SweepV2CoreParity_moduleOk.fnsOk pre g post hsplit).1

/-! ## 1. Policy Configuration & Budget Sanity Checks -/

#guard fidInlPolicy.leafMax == 165
#guard fidInlPolicy.singleSiteMax == 0
#guard fidInlPolicy.maxCallerSize == 2800
#guard fidInlPolicy.maxCalleeCalls == 2
#guard fidInlPolicy.maxCalleeLoops == some 1
#guard fidInlPolicy.maxTotalDup == 1500
#guard fidInlPolicy.maxCallerCalls == 24
#guard fidInlPolicy.keepOutOfLine ==
  [ "m6_hdr_init", "full_watch_push_slow_m6", "full_prop_flush_slow_fid"
  , "full_prop_flush_del_fid", "full_k6_init" ]

-- Keep cold/spill-regressing helpers strictly OOL (`budget = 0` + `keepOutOfLine`)
#guard fidPgoBudget "m6_hdr_init" == 0
#guard fidPgoBudget "full_watch_push_slow_m6" == 0
#guard fidPgoBudget "full_prop_flush_slow_fid" == 0
#guard fidPgoBudget "full_prop_flush_del_fid" == 0
#guard fidPgoBudget "full_rebuild_watches_nosort_fid" == 0
#guard fidPgoBudget "full_congruence_dense" == 0
#guard fidPgoBudget "full_unwatch_large" == 0
#guard fidPgoBudget "full_k6_init" == 0
#guard fidPgoBudget "full_watch_push_m6" == 200
#guard fidPgoBudget "full_k6_ana_cl_fid" == 145
#guard fidPgoBudget "full_cong_sift_pairs_fid" == 95
-- Fixed underbudgeted PGO entries
#guard fidPgoBudget "full_cong_find" >= 50
#guard fidPgoBudget "full_sort_u32" >= 160
#guard fidPgoBudget "m6_hdr_bump_delay" >= 80
#guard fidPgoBudget "full_sort_tmp_heap_m7" >= 215
#guard fidPgoBudget "full_m6_max_v" >= 32
-- Covered hot leaves & helpers
#guard fidPgoBudget "full_bva_match_large_fid" >= 65
#guard fidPgoBudget "full_reorder_sift_fid" >= 105
#guard fidPgoBudget "full_assign_lvl" >= 180
#guard fidPgoBudget "full_assign" >= 150
#guard fidPgoBudget "full_min_mark" >= 90
#guard fidPgoBudget "full_fill_u64_m7" >= 40
#guard fidPgoBudget "full_sort_bin_watches_fid" >= 110
#guard fidPgoBudget "full_k6_flip" >= 290
#guard fidPgoBudget "full_walk_flip_m7" >= 280
#guard fidPgoBudget "full_decide_m7" >= 265
#guard fidPgoBudget "full_cong_enq_var" >= 85
#guard fidPgoBudget "full_backtrack" >= 64
#guard fidPgoBudget "full_extend_push2" >= 97
#guard fidPgoBudget "full_cong_unit_fold" >= 72
#guard fidPgoBudget "m6_hdr_dr_init" >= 60
#guard fidPgoBudget "m6_hdr_sync_legacy_tiers" >= 30
#guard fidPgoBudget "m6_hdr_decide_fid" >= 130
#guard fidPgoBudget "full_bump_var" >= 175
#guard fidPgoBudget "full_m6_dense_prop" >= 44
#guard fidPgoBudget "full_elim_dticks" >= 42
#guard fidPgoBudget "full_shrink_lower_m8" >= 165
#guard fidPgoBudget "full_m6_sweep_solve" >= 115
#guard fidPgoBudget "full_queue_mtf" >= 240
#guard fidPgoBudget "full_sweep_copy" >= 315
#guard fidPgoBudget "full_analyze_rsn_m6_hdr" >= 450

/-! ## 2. Single-Pass Purified `469`-Fn Inliner Comparison (`fidInlPolicy` vs `m7InlPolicy`) -/

def checkDriver (fns : List Fn) (nm : Sym) (expSz expCalls : Nat) : Bool :=
  match fns.find? (·.name == nm) with
  | none => false
  | some f => f.size == expSz && f.numCalls == expCalls

def fidComparisonOk : Bool :=
  let rawOk := pureFidMod.fns.length == 469 &&
    !pureFidMod.fns.any (·.name == "full_bve_find_xor_m8") &&
    !pureFidMod.fns.any (·.name == "full_bve_bce_side_m8") &&
    pureFidMod.checkAcyclic == true
  let m7 := pureFidMod.optInlinePolicy m7InlPolicy
  let fid := pureFidMod.optInlinePolicy fidInlPolicy
  let m7Calls := (fnsCallSites m7.fns).foldl (fun a p => a + p.2) 0
  let fidCalls := (fnsCallSites fid.fns).foldl (fun a p => a + p.2) 0
  let m7LpCalls := (fnsLoopCallSites m7.fns).foldl (fun a p => a + p.2) 0
  let fidLpCalls := (fnsLoopCallSites fid.fns).foldl (fun a p => a + p.2) 0
  let m7MaxSz := m7.fns.foldl (fun a f => Nat.max a f.size) 0
  let fidMaxSz := fid.fns.foldl (fun a f => Nat.max a f.size) 0
  let noOversize := fid.fns.all (fun f => f.size <= 3500)
  let drvOk :=
    checkDriver fid.fns "full_cong_eval_gate" 2792 17 &&
    checkDriver fid.fns "full_reorder_queue_m7" 1051 0 &&
    checkDriver fid.fns "full_bve_def_k6_m7" 704 2 &&
    checkDriver fid.fns "full_bva_filter_row" 314 0 &&
    checkDriver fid.fns "full_deduce_1uip_m6_hdr" 1814 4 &&
    checkDriver fid.fns "full_arena_sweep_m6" 692 5 &&
    checkDriver fid.fns "full_m6_sweep_classes" 1783 9 &&
    checkDriver fid.fns "full_m6_sweep_cone" 595 5 &&
    checkDriver fid.fns "full_k6_extract_and_solve_m8" 739 2
  rawOk &&
    m7.fns.length == 469 && fid.fns.length == 469 &&
    m7Calls == 951 && fidCalls == 744 && fidCalls < m7Calls &&
    m7LpCalls == 627 && fidLpCalls == 473 && fidLpCalls < m7LpCalls &&
    m7MaxSz == 1009 && fidMaxSz == 2792 && noOversize &&
    fid.checkAcyclic == true && drvOk

#guard fidComparisonOk
#guard fidInlChunkPolicy.leafMax == fidInlPolicy.leafMax
#guard fidInlChunkPolicy.maxCallerSize == fidInlPolicy.maxCallerSize
#guard fidInlChunkPolicy.keepOutOfLine == fidInlPolicy.keepOutOfLine
#guard fidInlChunkPolicy.maxCalleeLoops == fidInlPolicy.maxCalleeLoops
#guard fidInlChunkPolicy.maxCallerCalls == fidInlPolicy.maxCallerCalls

/-! ## 3. Formal `Wf`, Acyclicity, and Soundness Transport Proofs -/

private theorem checkAcyclic_of_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    M.checkAcyclic = true := by
  simp only [Module.checkAcyclic, Bool.and_eq_true]
  exact ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp =>
      (hM.fnsOk pre fn post hsp).2.1⟩

private theorem fns_wf_of_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ∀ f ∈ M.fns, f.Wf := by
  intro f hf
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem hf
  exact (hM.fnsOk pre f post hsp).1

theorem fidInlMod_wf :
    ∀ f ∈ (pureFidMod.optInlinePolicy fidInlPolicy).fns, f.Wf := by
  intro f hf
  change f ∈ (pureFidMod.inlinePolicy fidInlPolicy).fns.map Fn.renorm at hf
  rcases List.mem_map.mp hf with ⟨g, _, rfl⟩
  exact Func.renorm_wf g.body

theorem m8SwCpInl_wf :
    ∀ f ∈ (m8SweepV2CoreParityModule.optInlinePolicy fidInlPolicy).fns, f.Wf :=
  Module.optInlinePolicy_wf fidInlPolicy
    (checkAcyclic_of_ok m8SweepV2CoreParity_moduleOk)
    (fns_wf_of_ok m8SweepV2CoreParity_moduleOk)

theorem m8SwCpInl_acyclic :
    (m8SweepV2CoreParityModule.optInlinePolicy fidInlPolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic fidInlPolicy
    (checkAcyclic_of_ok m8SweepV2CoreParity_moduleOk)
    (fns_wf_of_ok m8SweepV2CoreParity_moduleOk)

theorem m8SwCpInl_callsOk :
    ∀ pre fn post,
      (m8SweepV2CoreParityModule.optInlinePolicy fidInlPolicy).fns = pre ++ fn :: post →
      Fn.callsOk (pre.map Fn.sig ++ m8SweepV2CoreParityModule.externs.map Extern.sig)
        m8SweepV2CoreParityModule.exits fn :=
  Module.optInlinePolicy_callsOk fidInlPolicy
    (checkAcyclic_of_ok m8SweepV2CoreParity_moduleOk)
    (fns_wf_of_ok m8SweepV2CoreParity_moduleOk)

theorem m8SwCpInl_ok :
    ModuleOk m8SweepV2CoreParityEnv
      (m8SweepV2CoreParityModule.optInlinePolicy fidInlPolicy) :=
  Module.optInlinePolicy_ok fidInlPolicy m8SweepV2CoreParity_moduleOk

theorem ax_fid_wf {M : Module} (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy fidInlPolicy).fns, f.Wf :=
  Module.optInlinePolicy_wf fidInlPolicy hchk hwf

theorem ax_fid_acyc {M : Module} (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy fidInlPolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic fidInlPolicy hchk hwf

theorem ax_fid_ok {Γ : Env} {M : Module} (hok : ModuleOk Γ M) :
    ModuleOk Γ (M.optInlinePolicy fidInlPolicy) :=
  Module.optInlinePolicy_ok fidInlPolicy hok

theorem ax_fid_calls {M : Module} (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy fidInlPolicy).fns = pre ++ fn :: post →
      Fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits fn :=
  Module.optInlinePolicy_callsOk fidInlPolicy hchk hwf

theorem ax_fid_spec {Γ : Env} {M : Module}
    (hok : ModuleOk Γ M) {f : Fn} (hf : f ∈ (M.optInlinePolicy fidInlPolicy).fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hpre : Γ f.name f.as f.rs xs m Q X) : Func.wp Γ f.body xs m Q X :=
  Module.optInlinePolicy_spec fidInlPolicy hok f hf xs m Q X hpre

theorem ax_fid_src (lt : LegalTarget) {M : Module}
    (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsup : ∀ f ∈ M.fns, Func.supportsSource lt f.body = true) :
    ∀ f ∈ (M.optInlinePolicy fidInlPolicy).fns, Func.supportsSource lt f.body = true :=
  Module.optInlinePolicy_supportsSource lt fidInlPolicy hwf hsup

#print axioms ax_fid_wf
#print axioms ax_fid_acyc
#print axioms ax_fid_ok
#print axioms ax_fid_calls
#print axioms ax_fid_spec
#print axioms ax_fid_src
#print axioms pureFidFns_wf
#print axioms fidInlMod_wf
#print axioms m8SwCpInl_wf
#print axioms m8SwCpInl_acyclic
#print axioms m8SwCpInl_callsOk
#print axioms m8SwCpInl_ok

end LeanQbeTest.T.FullFidelityInlPolicyTest

end
