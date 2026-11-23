module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Hot-Loop Optimization for `full_bva_hop1` & `full_bva_hop2` (`FullM7HotHop1`)

Additive, bit-identical C0 hot-loop optimization targeting Kissat's `#1` compiler-gap hotspot
`full_bva_hop1` (`m7Hop1Fn`) and its caller `full_bva_hop2` (`m7Hop2Fn`), preserving exact
`FullHdr` layout (`144` `u64` words) and `FullBvaHeap` contracts (`0` changes to `Full1..6*`):

1. **Scalarize `h->ant_sz` (`full_bva_hop1_m7`)**: caches `u64 ant = h->ant_sz;` after the
   `s1[sidx] != 0ULL` early return, decrements the local register variable inside the nested
   loops, and writes `h->ant_sz = ant;` once after the `sgn` loop exits.
2. **Sink cold cache-update locals (`full_bva_hop1_m7`, `full_bva_hop2_m7`)**: moves `st1`/`st2`
   and `cv = h->cur_vars` out of function entry into the post-loop `if (ant > 0ULL)` /
   `if (h->ant_sz > 0ULL)` memo-store block, freeing `2` callee-saved GPRs across the hot loops.
3. **Inner clause-scan LSR & selectivity reorder (`full_bva_hop1_m7`)**: replaces `(u64)cr + 3ULL
   + (u64)k` indexing with non-wrapping `u64 ci = (u64)cr + 3ULL; u64 cend = ci + (u64)sz` and
   checks `(ol >> 1) == dst_idx` before `ol != sl`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7HotHop1

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7HotHop1 "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;

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
  u64 q_search_idx, q_search_stamp, q_cur_stamp, target_assigned, best_assigned;
  u64 rephase_limit, rephased, reduce_limit, reductions, tier1;
  u64 tier2, restarts, restart_limit, ema_fast_biased, ema_fast_exp;
  u64 ema_slow_biased, ema_slow_exp, oom;
  u64 max_vars, cur_vars, bva_cap, unassigned;
  u64 flags, lit_mark, repr, sim_sig;
  u64 frame_trail, frame_dec, work_stk1, work_stk2;
  u64 tarjan_mark, tarjan_reach, walk_vals, walk_best;
  u64 extend_stk, extend_cap, extend_len;
  u64 scratch_buf, scratch_cap, last_learned;
  u64 rng_state, chrono_levels, otfs_cnt, eager_sub_cnt;
  u64 probe_limit, probings, elim_limit, eliminations;
  u64 elim_bound, dense_mode, inconsistent, iterating;
  u64 hbr_cnt, trans_cnt, viv_cnt, subst_cnt;
  u64 cong_cnt, sweep_cnt, bve_cnt, bce_cnt;
  u64 bva_cnt, walk_cnt_stat, fwd_sub_cnt, fwd_str_cnt;
  u64 ant_sz, res_sz;
} FullHdr;

#define PH_GARB 0x00080000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern u64 full_bva_hop1(FullHdr *h, u32 src_lit, u32 dst_idx);

u64 full_bva_hop1_m7(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1;
  u64 *s1 = (u64 *)h->repr;
  if (s1[sidx] != 0ULL) { return s1[sidx] - 1ULL; }
  u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u64 ant = h->ant_sz;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 sgn = 0u;
  while (sgn < 2u && ant > 0ULL) {
    u32 sl = (sidx << 1) | sgn;
    u64 off = (u64)wvec[(u64)sl << 1];
    u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
    u64 p = off;
    while (p < end && ant > 0ULL) {
      ant = ant - 1ULL;
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        if (((w0 & PW_LIT_MASK) >> 1) == dst_idx) { res = res + 1ULL; }
      } else if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
          u32 sz = ar[(u64)cr + 2ULL];
          u64 ci = (u64)cr + 3ULL;
          u64 cend = ci + (u64)sz;
          while (ci < cend) {
            u32 ol = ar[ci];
            if ((ol >> 1) == dst_idx && ol != sl) { res = res + 1ULL; }
            ci = ci + 1ULL;
          }
        }
      }
    }
    sgn = sgn + 1u;
  }
  h->ant_sz = ant;
  if (ant > 0ULL) {
    u32 *st1 = (u32 *)h->min_clr;
    u64 cv = h->cur_vars;
    if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
    s1[sidx] = res + 1ULL;
    if (h->tmp_cnt < cv) { st1[h->tmp_cnt] = sidx; h->tmp_cnt = h->tmp_cnt + 1ULL; }
  }
  return res;
}

u64 full_bva_hop2_m7(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1;
  u64 *s2 = (u64 *)h->sim_sig;
  if (s2[sidx] != 0ULL) { return s2[sidx] - 1ULL; }
  u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 sgn = 0u;
  while (sgn < 2u && h->ant_sz > 0ULL) {
    u32 sl = (sidx << 1) | sgn;
    u64 off = (u64)wvec[(u64)sl << 1];
    u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
    u64 p = off;
    while (p < end && h->ant_sz > 0ULL) {
      h->ant_sz = h->ant_sz - 1ULL;
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        res = res + full_bva_hop1(h, w0 & PW_LIT_MASK, dst_idx);
      } else if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
          u32 sz = ar[(u64)cr + 2ULL];
          u32 k = 0u;
          while (k < sz && h->ant_sz > 0ULL) {
            u32 ol = ar[(u64)cr + 3ULL + (u64)k];
            if (ol != sl) { res = res + full_bva_hop1(h, ol, dst_idx); }
            k = k + 1u;
          }
        }
      }
    }
    sgn = sgn + 1u;
  }
  if (h->ant_sz > 0ULL) {
    u32 *st2 = (u32 *)h->shrink_stk;
    u64 cv = h->cur_vars;
    if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
    s2[sidx] = res + 1ULL;
    if (h->tmp_len < cv) { st2[h->tmp_len] = sidx; h->tmp_len = h->tmp_len + 1ULL; }
  }
  return res;
}
"

/-- Drop-in `Fn` handle preserving the canonical `"full_bva_hop1"` symbol name. -/
def m7Hop1Fn : Fn :=
  ⟨"full_bva_hop1", [i64, i32, i32], [i64], full_bva_hop1_m7_body⟩

/-- Drop-in `Fn` handle preserving the canonical `"full_bva_hop2"` symbol name. -/
def m7Hop2Fn : Fn :=
  ⟨"full_bva_hop2", [i64, i32, i32], [i64], full_bva_hop2_m7_body⟩

/-- Closed `2`-function list (`[m7Hop1Fn, m7Hop2Fn]`) in topological callee-first order. -/
def m7HotHop1Fns : List Fn :=
  [m7Hop1Fn, m7Hop2Fn]

/-- Standalone closed module (`2` functions, `0` externs, `0` exits). -/
def m7HotHop1Module : LeanQbe.T.Module :=
  { fns := m7HotHop1Fns, externs := [], exits := [] }

/-- Reconcile `FullM7HotHop1` overrides cleanly into a larger Kissat `Fn` list. -/
def spliceM7HotHop1Fns (fns : List Fn) : List Fn :=
  fns.map fun f =>
    if f.name = "full_bva_hop1" then m7Hop1Fn
    else if f.name = "full_bva_hop2" then m7Hop2Fn
    else f

theorem full_bva_hop1_m7_wf : Func.Wf full_bva_hop1_m7_body := by t_wf_reify
theorem full_bva_hop2_m7_wf : Func.Wf full_bva_hop2_m7_body := by t_wf_reify

theorem m7Hop1Fn_wf : m7Hop1Fn.Wf := full_bva_hop1_m7_wf
theorem m7Hop2Fn_wf : m7Hop2Fn.Wf := full_bva_hop2_m7_wf

theorem m7HotHop1Fns_wf : ∀ f ∈ m7HotHop1Fns, f.Wf := by
  intro f hf
  simp only [m7HotHop1Fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact m7Hop1Fn_wf
  · exact m7Hop2Fn_wf

theorem m7HotHop1_fns_wf : ∀ f ∈ m7HotHop1_fns, f.Wf := by
  intro f hf
  simp only [m7HotHop1_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact full_bva_hop1_m7_wf
  · exact full_bva_hop2_m7_wf

theorem m7HotHop1_acyclic : m7HotHop1Module.checkAcyclic = true := by
  t_kernel_rfl

theorem spliceM7HotHop1Fns_wf {fns : List Fn} (h : ∀ f ∈ fns, f.Wf) :
    ∀ f ∈ spliceM7HotHop1Fns fns, f.Wf := by
  intro g hg
  simp only [spliceM7HotHop1Fns, List.mem_map] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  split
  · exact m7Hop1Fn_wf
  · split
    · exact m7Hop2Fn_wf
    · exact h f hf

end LeanQbe.T.Examples.Kissat.FullM7HotHop1

end
