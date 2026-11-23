module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Hot-Loop Optimization: `full_has_ternary` (`FullM7HotTernary`)

Purely additive C0 hot-loop optimization of `FullM4InprocHot.full_has_ternary_m4` (exact
same `Full.fullHasTernarySpec` contract, `0` edits to existing `FullM4InprocHot*` files,
bit-identical return value on all inputs):
1. Hoists `bool distinct = (a != b) && (a != c) && (b != c);` before the `while (p < end)`
   watch loop.
2. Replaces the 4 loop-carried `bool` locals (`ha`, `hb`, `hc`, `sat`) and 5-way `&&` exit
   check with a single integer `u32 mask = 0u;` (`1 | 2 | 4` bitmask, `8u` poison on break)
   and LSR clause pointer `u64 ci = (u64)cr + 3ULL; u64 cend = ci + (u64)sz;`:
   - Reads `vals[l]` once into `i8 lv = vals[l];`
   - Breaks immediately on `lv > (i8)0`, `nf > 3u`, or `hit == 0u && distinct`
   - Tests `if (nf == 3u && mask == 7u) { return true; }` after the inner loop.
3. Exports drop-in `m7HasTernaryFn` (symbol `"full_has_ternary"`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7HotTernary

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7HotTernary "
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

bool full_has_ternary_m7(FullHdr *h, u32 a, u32 b, u32 c) {
  i8 *vals = (i8 *)h->values;
  if (vals[a] != (i8)0) { return false; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 scan = a;
  u32 min_sz = wvec[((u64)a << 1) + 1ULL];
  if ((u64)b < nlits) {
    if (vals[b] != (i8)0) { return false; }
    u32 b_sz = wvec[((u64)b << 1) + 1ULL];
    if (b_sz < min_sz) { scan = b; min_sz = b_sz; }
  }
  if ((u64)c < nlits) {
    if (vals[c] != (i8)0) { return false; }
    u32 c_sz = wvec[((u64)c << 1) + 1ULL];
    if (c_sz < min_sz) { scan = c; min_sz = c_sz; }
  }
  if (min_sz == 0u) { return false; }
  bool distinct = (a != b) && (a != c) && (b != c);
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)scan << 1];
  u64 end = off + (u64)min_sz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { continue; }
    u32 nf = 0u;
    u32 mask = 0u;
    u64 ci = (u64)cr + 3ULL;
    u64 cend = ci + (u64)sz;
    while (ci < cend) {
      u32 l = ar[ci]; ci = ci + 1ULL;
      i8 lv = vals[l];
      if (lv > (i8)0) { mask = 8u; break; }
      if (lv == (i8)0) {
        nf = nf + 1u;
        if (nf > 3u) { mask = 8u; break; }
        u32 hit = 0u;
        if (l == a) { hit = 1u; }
        if (l == b) { hit = hit | 2u; }
        if (l == c) { hit = hit | 4u; }
        if (hit == 0u && distinct) { mask = 8u; break; }
        mask = mask | hit;
      }
    }
    if (nf == 3u && mask == 7u) { return true; }
  }
  return false;
}
"

/-- Standalone `m7HotTernary` module (`1` function, `0` externs, `0` exits). -/
def m7HotTernaryModule : LeanQbe.T.Module :=
  { fns := m7HotTernary_fns, externs := [], exits := [] }

theorem full_has_ternary_m7_wf : Func.Wf full_has_ternary_m7_body := by t_wf_reify

theorem m7HotTernary_fns_wf : ∀ f ∈ m7HotTernary_fns, f.Wf := by
  simp only [m7HotTernary_fns, List.mem_singleton, forall_eq]
  exact full_has_ternary_m7_wf

theorem m7HotTernary_acyclic : m7HotTernaryModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Drop-in `Fn` handle preserving `"full_has_ternary"` (`[i64, i32, i32, i32] -> [.bool]`). -/
def m7HasTernaryFn : Fn :=
  ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], full_has_ternary_m7_body⟩

theorem m7HasTernaryFn_wf : m7HasTernaryFn.Wf := full_has_ternary_m7_wf

end LeanQbe.T.Examples.Kissat.FullM7HotTernary
