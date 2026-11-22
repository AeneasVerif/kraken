module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M6.0` Orchestrator & Forwarding Wrappers (`FullM6Orch`)

Defines all `29` `M6.0` orchestration and canonical forwarding C0 functions (`m6Orch_fns`):

1. **Canonical Forwarding Wrappers (`16` fns):**
   `full_wstack_defrag`, `full_watch_push`, `full_rescale`, `full_parse_body`, `full_lit_rank`,
   `full_sweep_bins` (-> `full_sweep_bins_m6cf`), `full_rewatch_arena`, `full_arena_sweep`,
   `full_mark_reasons`, `full_min_shrink`, `full_deduce_1uip`, `full_walk` (-> `full_walk_m6`),
   `full_sweep_dense_m6` (-> `full_sweep_dense_m5` for `M6.0`), `full_preprocess`, `full_search`,
   `kissat_solve_bytes`.
2. **Clean `M6Hdr` & Bugfixed `M6.0` Functions (`13` fns):**
   - `full_reduce_m6`: direct `M6Hdr` reduce calling `m6_hdr_recompute_tiers` (not
     `full_recompute_tiers`) and recording `M6_WM_REDUCE_CONFL`/`M6_WM_REDUCE_TICKS`.
   - `full_analyze_rsn_m6_hdr`, `full_deduce_1uip_m6_hdr`, `full_analyze_core_m6`: zero `gu[gi]++`
     writes into `h->glue_used` (only `m6_hdr_record_used`).
   - `full_ema_swap_m6`, `full_switch_mode_m6`: persistent per-mode EMA `averages[0]/[1]` in
     `h->glue_used[36..55]`.
   - `full_reorder_m6`: focused-only guard (`h->stable == 0ULL`) delegating to
     `full_reorder_queue_m7`.
   - `full_probe_tail_m6`, `full_probe_m6`: `full_backbone_m6` on both initial and non-initial
     branches, `M6_DELAY_*` congruence/sweep gates, `M6_WM_PROBE_TICKS` watermark.
   - `full_preprocess_m6`, `full_simplify_m6`, `full_search_m6`, `kissat_solve_bytes_m6`
     (`full_m6_mem_init` at `work_base`, `3,456 B` `FullM6Hdr`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6Orch "
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

#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_ACTIVE             1u

#define M6_HDR_TOTAL_BYTES    3456ULL

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL

#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL
#define M6_WM_FOCUSED_TICKS   6ULL
#define M6_WM_STABLE_TICKS    7ULL

extern void full_wstack_defrag_m6(FullHdr *h);
extern bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_rescale_m6(FullHdr *h);
extern u64 full_parse_body_m6(FullHdr *h, u64 cnf_end);
extern u64 full_lit_rank_m6(i8 *vals, u32 *lvl, u32 l);
extern void full_sweep_bins_m6cf(FullHdr *h);
extern bool full_rewatch_arena_m6(FullHdr *h, u64 dst);
extern u64 full_arena_sweep_m6(FullHdr *h);
extern void full_mark_reasons_m6(FullHdr *h, bool set_flag);
extern void full_min_shrink_m6(FullHdr *h);
extern u64 full_deduce_1uip_m6(FullHdr *h);
extern void full_walk_m6(FullHdr *h);
extern u64 full_sweep_dense_m5(FullHdr *h, u64 budget, u64 tick_lim);

extern u64 full_isqrt(u64 x);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void m6_hdr_recompute_tiers(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_sort_reds(FullHdr *h, u64 n);
extern u64 full_ilog10(u64 x);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern void m6_hdr_record_used(FullHdr *h, u64 glue);
extern void full_clear_ana(FullHdr *h);
extern bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip);
extern void full_otfs_subsume(FullHdr *h, u32 nc, u64 oct, u64 ocr, bool to_bin);
extern bool full_otfs_large(FullHdr *h, u32 cref, u32 uip);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_ana_failed_lit_m6_hdr(FullHdr *h);
extern void full_restore_bump_ana_m6_hdr(FullHdr *h);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern u64 full_learn_clause(FullHdr *h, u64 glue);
extern bool m6_hdr_ext_ready(FullHdr *h);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64 full_log10_q16(u64 x);
extern u64 full_reorder_queue_m7(FullHdr *h);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);
extern u64 full_transitive_m6(FullHdr *h, u64 tick_lim);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool full_enter_dense(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_rebuild_watches(FullHdr *h);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern u64 full_substitute(FullHdr *h);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_lucky(FullHdr *h);
extern bool full_compact_needed(FullHdr *h);
extern u64 full_compact(FullHdr *h);
extern u64 full_eliminate_m6(FullHdr *h, bool initial);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern void full_rephase_m6_hdr(FullHdr *h);
extern u64 m6_hdr_decide(FullHdr *h);
extern u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end, u64 work_base, u64 avail, u64 fuel);
extern void full_extend(FullHdr *h);
extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max);

void full_wstack_defrag(FullHdr *h) {
  full_wstack_defrag_m6(h);
}

bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  return full_watch_push_m6(h, lit, w0, w1, cnt);
}

void full_rescale(FullHdr *h) {
  full_rescale_m6(h);
}

u64 full_parse_body(FullHdr *h, u64 cnf_end) {
  return full_parse_body_m6(h, cnf_end);
}

u64 full_lit_rank(i8 *vals, u32 *lvl, u32 l) {
  return full_lit_rank_m6(vals, lvl, l);
}

void full_sweep_bins(FullHdr *h) {
  full_sweep_bins_m6cf(h);
}

bool full_rewatch_arena(FullHdr *h, u64 dst) {
  return full_rewatch_arena_m6(h, dst);
}

u64 full_arena_sweep(FullHdr *h) {
  return full_arena_sweep_m6(h);
}

void full_mark_reasons(FullHdr *h, bool set_flag) {
  full_mark_reasons_m6(h, set_flag);
}

u64 full_reduce_m6(FullHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  h->reduce_limit = h->conflicts + 1000ULL * full_isqrt(h->reductions);
  u64 ret = 1ULL;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { ret = 20ULL; }
    else if (pr != 0ULL) { ret = 0ULL; }
    else { h->unflushed = 0ULL; }
  }
  if (ret == 1ULL) {
    m6_hdr_recompute_tiers(h);
    full_mark_reasons(h, true);
    u32 *ar = (u32 *)h->arena;
    u32 *rr = (u32 *)h->red_refs;
    u64 rc = 0ULL; u64 p = 0ULL;
    u64 t1 = h->tier1; u64 t2 = h->tier2;
    while (p < h->arena_len) {
      u32 hdr = ar[p]; u32 n = full_arena_next(h, (u32)p);
      if ((hdr & PH_RED) != 0u && (hdr & PH_GARB) == 0u) {
        u32 old_u = (hdr >> 27) & 31u;
        if (old_u > 0u) { ar[p] = (hdr & 0x07FFFFFFu) | ((old_u - 1u) << 27); }
        if ((hdr & PH_RSN) == 0u) {
          u64 glue = (u64)(hdr & PH_GLUE_MASK);
          bool keep = (glue <= t1 && old_u > 0u) || (glue <= t2 && old_u >= 30u);
          if (!keep && rc < h->red_cap) { rr[rc] = (u32)p; rc = rc + 1ULL; }
        }
      }
      p = (u64)n;
    }
    if (rc > 0ULL) {
      full_sort_reds(h, rc);
      u64 logv = full_ilog10(h->reductions + 9ULL);
      u64 target = (rc * (900ULL - (400ULL / logv))) / 1000ULL;
      u64 i = 0ULL;
      while (i < target && i < rc) {
        u64 cref = (u64)rr[i]; u32 hdr = ar[cref];
        if ((hdr & PH_GARB) == 0u) {
          ar[cref] = hdr | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[cref + 2ULL];
        }
        i = i + 1ULL;
      }
    }
    if (force || (h->unflushed == 0ULL &&
        (h->arena_garbage * 4ULL >= h->arena_len ||
         h->arena_len * 5ULL >= h->arena_cap * 4ULL))) {
      while (true) {
        u64 sr = full_arena_sweep(h);
        if (sr == 2ULL) { ret = 20ULL; break; }
        if (sr == 3ULL) { ret = 0ULL; break; }
        if (sr == 0ULL) { break; }
        u64 pr = full_propagate(h);
        if (pr == 1ULL) { ret = 20ULL; break; }
        if (pr != 0ULL) { ret = 0ULL; break; }
        h->unflushed = 0ULL;
      }
    } else { full_mark_reasons(h, false); }
  }
  m6_hdr_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  m6_hdr_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  return ret;
}

bool full_analyze_rsn_m6_hdr(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > 1ULL) {
      u64 lim = glue - 1ULL;
      if (lim > h->tier2) { lim = h->tier2; }
      if (lim > 32ULL) { lim = 32ULL; }
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    m6_hdr_record_used(h, glue);
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

void full_min_shrink(FullHdr *h) {
  full_min_shrink_m6(h);
}

u64 full_deduce_1uip(FullHdr *h) {
  return full_deduce_1uip_m6(h);
}

u64 full_deduce_1uip_m6_hdr(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn_m6_hdr(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  if (!seed_ok || h->tmp_cnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (h->tmp_cnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= h->cur_vars) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      h->tmp_cnt = h->tmp_cnt - 1ULL;
      if (h->tmp_cnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn_m6_hdr(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      if (h->res_sz > 0ULL) { h->res_sz = h->res_sz - 1ULL; }
      if (h->ant_sz >= 3ULL && h->res_sz < h->ant_sz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (h->ant_sz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_analyze_core_m6(FullHdr *h) {
  u32 *lvl = (u32 *)h->level; u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL; u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) { return 1ULL; }
    if (ol == 2ULL) { return 0ULL; }
    if (h->cur_level == 1ULL) { return full_ana_failed_lit_m6_hdr(h); }
    u64 dst = full_deduce_1uip_m6_hdr(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) {
      h->conflicts = h->conflicts + 1ULL;
      if (h->probing == 0ULL) {
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) { tmp[0] = (u32)h->confl_lit0; h->tmp_len = 1ULL; }
          else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                   3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL]; h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_m6_hdr(h);
      }
      continue;
    }
    full_min_shrink_m6(h);
    if (h->probing == 0ULL) { full_restore_bump_ana_m6_hdr(h); full_tick_rel(h); }
    u64 glue = 1ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    return full_learn_clause(h, glue);
  }
  return 0ULL;
}

void full_walk(FullHdr *h) {
  full_walk_m6(h);
}

void full_ema_swap_m6(FullHdr *h, u64 old_m, u64 new_m) {
  u32 *gu = (u32 *)h->glue_used;
  u64 magic = ((u64)gu[36]) | (((u64)gu[37]) << 32);
  u64 init_exp = 1ULL << 32;
  if (magic != 0x4D37534541524348ULL) {
    gu[36] = (u32)0x4D37534541524348ULL; gu[37] = (u32)(0x4D37534541524348ULL >> 32);
    gu[38] = (u32)(1ULL << (old_m & 1ULL)); gu[39] = 0u;
    gu[40] = 0u; gu[41] = 0u; gu[42] = (u32)init_exp; gu[43] = (u32)(init_exp >> 32);
    gu[44] = 0u; gu[45] = 0u; gu[46] = (u32)init_exp; gu[47] = (u32)(init_exp >> 32);
    gu[48] = 0u; gu[49] = 0u; gu[50] = (u32)init_exp; gu[51] = (u32)(init_exp >> 32);
    gu[52] = 0u; gu[53] = 0u; gu[54] = (u32)init_exp; gu[55] = (u32)(init_exp >> 32);
  }
  u64 ob = ((old_m & 1ULL) == 0ULL) ? 40ULL : 48ULL;
  gu[ob]       = (u32)h->ema_fast_biased; gu[ob + 1ULL] = (u32)(h->ema_fast_biased >> 32);
  gu[ob + 2ULL] = (u32)h->ema_fast_exp;    gu[ob + 3ULL] = (u32)(h->ema_fast_exp >> 32);
  gu[ob + 4ULL] = (u32)h->ema_slow_biased; gu[ob + 5ULL] = (u32)(h->ema_slow_biased >> 32);
  gu[ob + 6ULL] = (u32)h->ema_slow_exp;    gu[ob + 7ULL] = (u32)(h->ema_slow_exp >> 32);
  u64 mask = (((u64)gu[38]) | (((u64)gu[39]) << 32)) | (1ULL << (old_m & 1ULL));
  u64 nb = ((new_m & 1ULL) == 0ULL) ? 40ULL : 48ULL;
  u64 bit = 1ULL << (new_m & 1ULL);
  if ((mask & bit) != 0ULL) {
    h->ema_fast_biased = ((u64)gu[nb])       | (((u64)gu[nb + 1ULL]) << 32);
    h->ema_fast_exp    = ((u64)gu[nb + 2ULL]) | (((u64)gu[nb + 3ULL]) << 32);
    h->ema_slow_biased = ((u64)gu[nb + 4ULL]) | (((u64)gu[nb + 5ULL]) << 32);
    h->ema_slow_exp    = ((u64)gu[nb + 6ULL]) | (((u64)gu[nb + 7ULL]) << 32);
  } else {
    h->ema_fast_biased = 0ULL; h->ema_fast_exp = init_exp;
    h->ema_slow_biased = 0ULL; h->ema_slow_exp = init_exp;
    mask = mask | bit;
  }
  gu[38] = (u32)mask; gu[39] = (u32)(mask >> 32);
}

void full_switch_mode_m6(FullHdr *h) {
  u64 old_m = 0ULL;
  u64 new_m = 1ULL;
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    old_m = 0ULL;
    new_m = 1ULL;
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    if (m6_hdr_ext_ready(h)) {
      u64 ft = m6_hdr_get_watermark(h, M6_WM_FOCUSED_TICKS);
      m6_hdr_set_watermark(h, M6_WM_FOCUSED_TICKS, ft + dticks);
    }
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    i8 *vals = (i8 *)h->values;
    u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL;
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        hp[n] = (u32)v;
        ps[v] = (u32)n;
        n = n + 1ULL;
      } else {
        ps[v] = 0xFFFFFFFFu;
      }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    if (m6_hdr_ext_ready(h)) {
      u64 st = m6_hdr_get_watermark(h, M6_WM_STABLE_TICKS);
      m6_hdr_set_watermark(h, M6_WM_STABLE_TICKS, st + dticks);
    }
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16(cc + 9ULL);
    u64 l2 = (q * q) >> 16;
    u64 l4 = (l2 * l2) >> 16;
    u64 scaled = 0ULL;
    if (cnt <= 1000000ULL) {
      scaled = (1000ULL * cnt * l4) >> 16;
    } else {
      u64 clim = (cnt > 100000000ULL) ? 100000000ULL : cnt;
      scaled = ((1000ULL * clim) >> 16) * l4;
    }
    h->mode_confl_lim = h->conflicts + scaled;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  full_ema_swap_m6(h, old_m, new_m);
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 1ULL) ? (d10 - 1ULL) : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
  }
}

u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim) {
  return full_sweep_dense_m5(h, budget, tick_lim);
}

u64 full_reorder_m6(FullHdr *h, u64 budget) {
  if (h->stable != 0ULL) { return 0ULL; }
  return full_reorder_queue_m7(h);
}

u64 full_probe_tail_m6(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL &&
      full_backbone_m6(h, dticks * 4ULL + 65536ULL) == 20ULL) {
    return 20ULL;
  }
  u64 tr_lim = (dticks / 50ULL) + 100000ULL;
  if (h->num_binary > 0ULL && full_transitive_m6(h, tr_lim) == 20ULL) { return 20ULL; }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  if (full_vivify_m6_hdr(h) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, 100ULL * h->probings * logp);
  }
  u64 round = 0ULL;
  while (round < 2ULL) {
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if ((h->cong_cnt > cb) && (h->cong_cnt - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
      }
      if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
        u64 sb = h->sweep_cnt;
        if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        if ((h->sweep_cnt > sb) && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
        }
      }
      if (full_rebuild_watches(h) == 20ULL) {
        m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
        return 20ULL;
      }
    } else if (h->inconsistent != 0ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->unassigned >= before_unass) { break; }
    round = round + 1ULL;
  }
  if (!initial) {
    if (full_probe_tail_m6(h, dticks) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, dticks * 4ULL + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  if ((h->num_irred <= 4096ULL || h->eliminations > 0ULL) && full_enter_dense(h)) {
    u64 fbud = full_min_u64(initial ? 512ULL : (64ULL + (dticks >> 9)), 1024ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_preprocess_m6(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  u64 lk = full_lucky(h);
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  if (full_probe_m6(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta_m5(h, 100ULL);
  h->elim_limit = full_scale_delta_m5(h, 500ULL);
  return 1ULL;
}

u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (do_probe && full_probe_m6(h, false) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (do_elim && full_eliminate_m6(h, false) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (full_compact_needed(h)) {
    u64 cr = full_compact(h);
    if (cr == 20ULL) { return 20ULL; }
    if (cr != 1ULL) { return 0ULL; }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  return 1ULL;
}

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
      bool mode_due = (h->stable == 0ULL)
        ? (h->conflicts >= h->mode_confl_lim)
        : (h->search_ticks >= h->mode_tick_lim);
      if (h->conflicts >= h->reduce_limit) {
        u64 rr = full_reduce_m6(h, false);
        if (rr == 20ULL) { return 20ULL; }
        if (rr != 1ULL) { return 0ULL; }
      } else if (mode_due) {
        full_switch_mode_m6(h);
      } else if (full_restart_due(h) != 0ULL) {
        full_restart(h);
      } else if (h->stable == 0ULL && h->conflicts >= reorder_limit) {
        reorder_limit = h->conflicts + 10000ULL;
        full_reorder_m6(h, 256ULL);
      } else if (h->conflicts >= h->rephase_limit) {
        full_rephase_m6_hdr(h);
      } else if (h->conflicts >= h->probe_limit) {
        u64 sr = full_simplify_m6(h, true, false);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      } else if (h->conflicts >= h->elim_limit) {
        u64 sr = full_simplify_m6(h, false, true);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      }
    } else {
      if (h->unassigned == 0ULL) { return 10ULL; }
      if (m6_hdr_decide(h) == 0ULL) { return (h->unassigned == 0ULL) ? 10ULL : 0ULL; }
    }
  }
}

u64 kissat_solve_bytes_m6(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + M6_HDR_TOTAL_BYTES) { return 0ULL; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  u64 hdr_addr = full_m6_mem_init(cnf_ptr, cnf_end, work_base, avail, fuel);
  if (hdr_addr == 0ULL) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 orig_mv = h->d.mv;
  u64 pp = full_preprocess_m6(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = (pp == 10ULL) ? 10ULL : ((pp == 0ULL) ? 0ULL : full_search_m6(h));
  if (r == 10ULL) {
    full_extend(h);
    h->d.mv = orig_mv;
    h->bva_cap = h->max_vars - orig_mv;
    u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, orig_mv);
    return (ok == 1ULL) ? 10ULL : 0ULL;
  }
  return r;
}

u64 full_preprocess(FullHdr *h) {
  return full_preprocess_m6(h);
}

u64 full_search(FullHdr *h) {
  return full_search_m6(h);
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  return kissat_solve_bytes_m6(cnf_ptr, cnf_len, work_ptr, work_cap, fuel);
}
"

/-- External callee signatures referenced by `m6Orch_fns`. -/
def m6OrchExterns : List Extern :=
  [ ⟨"full_wstack_defrag_m6", [i64], []⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_rescale_m6", [i64], []⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64]⟩
  , ⟨"full_lit_rank_m6", [i64, i64, i32], [i64]⟩
  , ⟨"full_sweep_bins_m6cf", [i64], []⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool]⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64]⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], []⟩
  , ⟨"full_min_shrink_m6", [i64], []⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64]⟩
  , ⟨"full_walk_m6", [i64], []⟩
  , ⟨"full_sweep_dense_m5", [i64, i64, i64], [i64]⟩
  , ⟨"full_isqrt", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_sort_reds", [i64, i64], []⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"m6_hdr_record_used", [i64, i64], []⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], []⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool]⟩
  , ⟨"full_one_lit_confl", [i64], [i64]⟩
  , ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64]⟩
  , ⟨"full_restore_bump_ana_m6_hdr", [i64], []⟩
  , ⟨"full_tick_rel", [i64], []⟩
  , ⟨"full_ema_update", [i64, i64], []⟩
  , ⟨"full_learn_clause", [i64, i64], [i64]⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool]⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_log10_q16", [i64], [i64]⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_probe_run", [i64, i64], [i64]⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64]⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_lucky", [i64], [i64]⟩
  , ⟨"full_compact_needed", [i64], [.bool]⟩
  , ⟨"full_compact", [i64], [i64]⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64]⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64]⟩
  , ⟨"full_restart_due", [i64], [i64]⟩
  , ⟨"full_restart", [i64], []⟩
  , ⟨"full_rephase_m6_hdr", [i64], []⟩
  , ⟨"m6_hdr_decide", [i64], [i64]⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]⟩
  , ⟨"full_extend", [i64], []⟩
  , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64]⟩ ]

/-- Standalone `M6.0` orchestration module (`29` functions + `65` externs, `0` exits). -/
def m6OrchModule : LeanQbe.T.Module :=
  { fns := m6Orch_fns, externs := m6OrchExterns, exits := [] }

/-- Individual function handles matching `m6Orch_fns` order (`29` fns). -/
def m6oWstackDefragFn : Fn := ⟨"full_wstack_defrag", [i64], [], full_wstack_defrag_body⟩
def m6oWatchPushFn : Fn :=
  ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], full_watch_push_body⟩
def m6oRescaleFn : Fn := ⟨"full_rescale", [i64], [], full_rescale_body⟩
def m6oParseBodyFn : Fn := ⟨"full_parse_body", [i64, i64], [i64], full_parse_body_body⟩
def m6oLitRankFn : Fn := ⟨"full_lit_rank", [i64, i64, i32], [i64], full_lit_rank_body⟩
def m6oSweepBinsFn : Fn := ⟨"full_sweep_bins", [i64], [], full_sweep_bins_body⟩
def m6oRewatchArenaFn : Fn :=
  ⟨"full_rewatch_arena", [i64, i64], [.bool], full_rewatch_arena_body⟩
def m6oArenaSweepFn : Fn := ⟨"full_arena_sweep", [i64], [i64], full_arena_sweep_body⟩
def m6oMarkReasonsFn : Fn := ⟨"full_mark_reasons", [i64, .bool], [], full_mark_reasons_body⟩
def m6oReduceM6Fn : Fn := ⟨"full_reduce_m6", [i64, .bool], [i64], full_reduce_m6_body⟩
def m6oAnalyzeRsnM6HdrFn : Fn :=
  ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], full_analyze_rsn_m6_hdr_body⟩
def m6oMinShrinkFn : Fn := ⟨"full_min_shrink", [i64], [], full_min_shrink_body⟩
def m6oDeduce1uipFn : Fn := ⟨"full_deduce_1uip", [i64], [i64], full_deduce_1uip_body⟩
def m6oDeduce1uipM6HdrFn : Fn :=
  ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], full_deduce_1uip_m6_hdr_body⟩
def m6oAnalyzeCoreM6Fn : Fn :=
  ⟨"full_analyze_core_m6", [i64], [i64], full_analyze_core_m6_body⟩
def m6oWalkFn : Fn := ⟨"full_walk", [i64], [], full_walk_body⟩
def m6oEmaSwapM6Fn : Fn :=
  ⟨"full_ema_swap_m6", [i64, i64, i64], [], full_ema_swap_m6_body⟩
def m6oSwitchModeM6Fn : Fn := ⟨"full_switch_mode_m6", [i64], [], full_switch_mode_m6_body⟩
def m6oSweepDenseM6Fn : Fn :=
  ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], full_sweep_dense_m6_body⟩
def m6oReorderM6Fn : Fn := ⟨"full_reorder_m6", [i64, i64], [i64], full_reorder_m6_body⟩
def m6oProbeTailM6Fn : Fn := ⟨"full_probe_tail_m6", [i64, i64], [i64], full_probe_tail_m6_body⟩
def m6oProbeM6Fn : Fn := ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩
def m6oPreprocessM6Fn : Fn := ⟨"full_preprocess_m6", [i64], [i64], full_preprocess_m6_body⟩
def m6oSimplifyM6Fn : Fn :=
  ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], full_simplify_m6_body⟩
def m6oSearchM6Fn : Fn := ⟨"full_search_m6", [i64], [i64], full_search_m6_body⟩
def m6oSolveBytesM6Fn : Fn :=
  ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_m6_body⟩
def m6oPreprocessFn : Fn := ⟨"full_preprocess", [i64], [i64], full_preprocess_body⟩
def m6oSearchFn : Fn := ⟨"full_search", [i64], [i64], full_search_body⟩
def m6oSolveBytesFn : Fn :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_body⟩

theorem full_wstack_defrag_wf : Func.Wf full_wstack_defrag_body := by t_wf_reify
theorem full_watch_push_wf : Func.Wf full_watch_push_body := by t_wf_reify
theorem full_rescale_wf : Func.Wf full_rescale_body := by t_wf_reify
theorem full_parse_body_wf : Func.Wf full_parse_body_body := by t_wf_reify
theorem full_lit_rank_wf : Func.Wf full_lit_rank_body := by t_wf_reify
theorem full_sweep_bins_wf : Func.Wf full_sweep_bins_body := by t_wf_reify
theorem full_rewatch_arena_wf : Func.Wf full_rewatch_arena_body := by t_wf_reify
theorem full_arena_sweep_wf : Func.Wf full_arena_sweep_body := by t_wf_reify
theorem full_mark_reasons_wf : Func.Wf full_mark_reasons_body := by t_wf_reify
theorem full_reduce_m6_wf : Func.Wf full_reduce_m6_body := by t_wf_reify
theorem full_analyze_rsn_m6_hdr_wf : Func.Wf full_analyze_rsn_m6_hdr_body := by t_wf_reify
theorem full_min_shrink_wf : Func.Wf full_min_shrink_body := by t_wf_reify
theorem full_deduce_1uip_wf : Func.Wf full_deduce_1uip_body := by t_wf_reify
theorem full_deduce_1uip_m6_hdr_wf : Func.Wf full_deduce_1uip_m6_hdr_body := by t_wf_reify
theorem full_analyze_core_m6_wf : Func.Wf full_analyze_core_m6_body := by t_wf_reify
theorem full_walk_wf : Func.Wf full_walk_body := by t_wf_reify
theorem full_ema_swap_m6_wf : Func.Wf full_ema_swap_m6_body := by t_wf_reify
theorem full_switch_mode_m6_wf : Func.Wf full_switch_mode_m6_body := by t_wf_reify
theorem full_sweep_dense_m6_wf : Func.Wf full_sweep_dense_m6_body := by t_wf_reify
theorem full_reorder_m6_wf : Func.Wf full_reorder_m6_body := by t_wf_reify
theorem full_probe_tail_m6_wf : Func.Wf full_probe_tail_m6_body := by t_wf_reify
theorem full_probe_m6_wf : Func.Wf full_probe_m6_body := by t_wf_reify
theorem full_preprocess_m6_wf : Func.Wf full_preprocess_m6_body := by t_wf_reify
theorem full_simplify_m6_wf : Func.Wf full_simplify_m6_body := by t_wf_reify
theorem full_search_m6_wf : Func.Wf full_search_m6_body := by t_wf_reify
theorem kissat_solve_bytes_m6_wf : Func.Wf kissat_solve_bytes_m6_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify
theorem full_search_wf : Func.Wf full_search_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

theorem m6Orch_fns_wf : ∀ f ∈ m6Orch_fns, f.Wf := by
  simp only [m6Orch_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_wstack_defrag_wf, full_watch_push_wf, full_rescale_wf, full_parse_body_wf,
    full_lit_rank_wf, full_sweep_bins_wf, full_rewatch_arena_wf, full_arena_sweep_wf,
    full_mark_reasons_wf, full_reduce_m6_wf, full_analyze_rsn_m6_hdr_wf, full_min_shrink_wf,
    full_deduce_1uip_wf, full_deduce_1uip_m6_hdr_wf, full_analyze_core_m6_wf, full_walk_wf,
    full_ema_swap_m6_wf, full_switch_mode_m6_wf, full_sweep_dense_m6_wf, full_reorder_m6_wf,
    full_probe_tail_m6_wf, full_probe_m6_wf, full_preprocess_m6_wf, full_simplify_m6_wf,
    full_search_m6_wf, kissat_solve_bytes_m6_wf, full_preprocess_wf, full_search_wf,
    kissat_solve_bytes_wf⟩

theorem m6Orch_acyclic : m6OrchModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6Orch

