module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M6.0` Orchestrator Clean Adapters (`FullM6OrchAdapters`)

Option B standalone C0 adapter module containing the `16` clean `M6.0` adapter / repointed
functions copied from `FullM6Merge` (excluding the `6` superseded or unfixed definitions
replaced directly by `FullM6Orch`):

1. `full_scale_delta` -> `full_scale_delta_m5`
2. `full_prop_lit_raw`, `full_propagate_ignore`, `full_propagate` (`FullM6BcpS15`)
3. `full_bump_analyzed_m6_hdr`, `full_restore_bump_ana_m6_hdr`, `full_ana_failed_lit_m6_hdr`
4. `full_analyze_m6_hdr`, `full_rephase_m6_hdr`
5. `full_add_bin`, `full_vivify_tier_m6_hdr`, `full_vivify_m6_hdr`
6. `full_bve_var`, `full_forward_sub`, `full_init_fresh_var`
7. `full_probe_dticks_m6_hdr`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6OrchAdapters "
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

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define FL_ACTIVE             1u

#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REPHASE_TICKS   4ULL

extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern bool full_prop_lit_raw_s15(FullHdr *h, u32 lit, u64 ignore_ref);
extern u64 full_propagate_ignore_s15(FullHdr *h, u64 ignore_ref);
extern u64 full_bcp_s15(FullHdr *h);
extern bool m6_hdr_dr_allow(FullHdr *h);
extern void full_sort_ana_qs_m6(FullHdr *h, u64 n);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_clear_ana(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void m6_hdr_update_tier_limits(FullHdr *h);
extern void m6_hdr_dr_update(FullHdr *h);
extern u64 full_analyze_core_m6(FullHdr *h);
extern void full_walk(FullHdr *h);
extern u64 full_log10_q16(u64 x);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_add_bin_m6(FullHdr *h, u32 a, u32 b);
extern u64 full_viv_collect_m6(FullHdr *h, u64 tier_mode);
extern void full_viv_count_m6(FullHdr *h, u64 bn);
extern void full_viv_keys_m6(FullHdr *h, u64 bn);
extern void full_viv_sort_sched_m6(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cref);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern u64 full_bve_var_m6(FullHdr *h, u32 v);
extern u64 full_forward_sub_m6(FullHdr *h, u64 budget);
extern void full_init_fresh_var_m6(FullHdr *h, u32 fv);

u64 full_scale_delta(FullHdr *h, u64 delta) {
  return full_scale_delta_m5(h, delta);
}

bool full_prop_lit_raw(FullHdr *h, u32 lit, u64 ignore_ref) {
  return full_prop_lit_raw_s15(h, lit, ignore_ref);
}

u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref) {
  return full_propagate_ignore_s15(h, ignore_ref);
}

u64 full_propagate(FullHdr *h) {
  return full_bcp_s15(h);
}

void full_bump_analyzed_m6_hdr(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  if (m6_hdr_dr_allow(h)) {
    u64 lim = saved * 10ULL;
    u64 i = 0ULL;
    u64 tlen = h->tmp_len;
    if (tlen > cv) { tlen = cv; }
    while (i < tlen && h->min_clr_len <= lim) {
      u32 uv = tmp[i] >> 1;
      u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
      if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
          mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
          h->min_clr_len = h->min_clr_len + 1ULL;
        }
      } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
        u32 sz = ar[(u64)rsn + 2ULL];
        if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
          u32 j = 0u;
          while (j < sz && h->min_clr_len <= lim) {
            u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
            if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
              mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
            j = j + 1u;
          }
        }
      }
      i = i + 1ULL;
    }
    if (h->min_clr_len > lim) {
      while (h->min_clr_len > saved) {
        h->min_clr_len = h->min_clr_len - 1ULL;
        u32 rv = ana[h->min_clr_len];
        if ((u64)rv < cv) { mrk[rv] = (u8)0; }
      }
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL && cnt <= cv) {
    full_sort_ana_qs_m6(h, cnt);
  }
  u64 k = 0ULL;
  while (k < cnt) {
    u32 bv = ana[k];
    if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
      full_bump_var(h, bv);
      if (h->stable == 0ULL) { full_queue_mtf(h, bv); }
    }
    k = k + 1ULL;
  }
  full_bump_decay(h);
}

void full_restore_bump_ana_m6_hdr(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u64 cv = h->cur_vars;
  u64 ana_n = h->res_sz;
  if (ana_n > cv) { ana_n = cv; }
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u64 w = 0ULL;
  u64 k = 0ULL;
  while (k < ana_n) {
    u32 av = ana[k];
    if ((u64)av < cv && mrk[av] == (u8)0) {
      mrk[av] = (u8)1;
      ana[w] = av;
      w = w + 1ULL;
    }
    k = k + 1ULL;
  }
  u64 tlen = h->tmp_len;
  if (tlen <= cv) {
    u64 ti = 0ULL;
    while (ti < tlen) {
      u32 tv = tmp[ti] >> 1;
      if ((u64)tv < cv && lvl[tv] > 0u && mrk[tv] == (u8)0 && w < cv) {
        mrk[tv] = (u8)1;
        ana[w] = tv;
        w = w + 1ULL;
      }
      ti = ti + 1ULL;
    }
  }
  h->min_clr_len = w;
  if (w > 0ULL) {
    full_bump_analyzed_m6_hdr(h);
    full_clear_ana(h);
  }
}

u64 full_ana_failed_lit_m6_hdr(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (h->cur_level != 1ULL || cv == 0ULL) { return 0ULL; }
  u32 *fdec = (u32 *)h->frame_dec;
  u32 failed = fdec[1];
  u32 fv = failed >> 1;
  u32 not_failed = failed ^ 1u;
  if ((u64)fv >= cv) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  if (vals[failed] <= (i8)0 || lvl[fv] != 1u || rsns[fv] != 0xFFFFFFFFu) {
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *ar = (u32 *)h->arena;
  u32 *ana = (u32 *)h->work_stk1;
  h->min_clr_len = 0ULL;
  u64 unres = 0ULL;
  u64 ucnt = 0ULL;
  bool done = false;
  if (h->confl_type == 1ULL) {
    u32 c0 = (u32)h->confl_lit0; u32 c1 = (u32)h->confl_lit1;
    if (c0 == not_failed || c1 == not_failed) { done = true; }
    else {
      u32 v0 = c0 >> 1; u32 v1 = c1 >> 1;
      if ((u64)v0 >= cv || (u64)v1 >= cv) { return 0ULL; }
      if (lvl[v0] > 0u && mrk[v0] == (u8)0) {
        mrk[v0] = (u8)1; ana[h->min_clr_len] = v0; h->min_clr_len = h->min_clr_len + 1ULL;
        unres = unres + 1ULL;
      }
      if (lvl[v1] > 0u && mrk[v1] == (u8)0) {
        mrk[v1] = (u8)1; ana[h->min_clr_len] = v1; h->min_clr_len = h->min_clr_len + 1ULL;
        unres = unres + 1ULL;
      }
    }
  } else {
    u32 cr = (u32)h->confl_ref;
    if ((u64)cr + 3ULL > h->arena_len) { return 0ULL; }
    u32 csz = ar[(u64)cr + 2ULL];
    if ((u64)cr + 3ULL + (u64)csz > h->arena_len) { return 0ULL; }
    u32 i = 0u;
    while (i < csz) {
      u32 lit = ar[(u64)cr + 3ULL + (u64)i];
      if (lit == not_failed) { done = true; break; }
      u32 lv = lit >> 1;
      if ((u64)lv >= cv) { full_clear_ana(h); return 0ULL; }
      if (lvl[lv] > 0u && mrk[lv] == (u8)0) {
        mrk[lv] = (u8)1;
        if (h->min_clr_len < cv) {
          ana[h->min_clr_len] = lv; h->min_clr_len = h->min_clr_len + 1ULL;
        }
        unres = unres + 1ULL;
      }
      i = i + 1u;
    }
  }
  u64 t = h->trail_end;
  u32 unit = 0xFFFFFFFFu;
  bool err = false;
  while (!done && !err) {
    u32 lit = 0xFFFFFFFFu;
    while (true) {
      if (t == 0ULL) { err = true; break; }
      t = t - 1ULL;
      u32 tl = trl[t]; u32 tv = tl >> 1;
      if ((u64)tv >= cv) { err = true; break; }
      if (mrk[tv] != (u8)0) { lit = tl; break; }
    }
    if (err || lit == 0xFFFFFFFFu) { err = true; break; }
    if (unres == 1ULL) {
      unit = lit ^ 1u;
      if (ucnt < cv) { tmp[ucnt] = unit; ucnt = ucnt + 1ULL; }
      else { err = true; break; }
    }
    u32 rsn = rsns[lit >> 1];
    if (rsn == 0xFFFFFFFFu) { err = true; break; }
    if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      if (ot == not_failed) { done = true; break; }
      u32 ov = ot >> 1;
      if ((u64)ov >= cv) { err = true; break; }
      if (lvl[ov] > 0u && mrk[ov] == (u8)0) {
        mrk[ov] = (u8)1;
        if (h->min_clr_len < cv) {
          ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
        }
        unres = unres + 1ULL;
      }
    } else {
      if ((u64)rsn + 3ULL > h->arena_len) { err = true; break; }
      u32 rsz = ar[(u64)rsn + 2ULL];
      if (rsz < 3u || (u64)rsn + 3ULL + (u64)rsz > h->arena_len) { err = true; break; }
      u32 j = 0u;
      while (j < rsz) {
        u32 ot = ar[(u64)rsn + 3ULL + (u64)j];
        if (ot != lit) {
          if (ot == not_failed) { done = true; break; }
          u32 ov = ot >> 1;
          if ((u64)ov >= cv) { err = true; break; }
          if (lvl[ov] > 0u && mrk[ov] == (u8)0) {
            mrk[ov] = (u8)1;
            if (h->min_clr_len < cv) {
              ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
            }
            unres = unres + 1ULL;
          }
        }
        j = j + 1u;
      }
    }
    if (done || err) { break; }
    if (unres == 0ULL) { err = true; break; }
    unres = unres - 1ULL;
  }
  if (err) { full_clear_ana(h); return 0ULL; }
  if (ucnt >= cv) { full_clear_ana(h); return 0ULL; }
  tmp[ucnt] = not_failed; ucnt = ucnt + 1ULL;
  h->tmp_len = ucnt;
  full_bump_analyzed_m6_hdr(h);
  full_clear_ana(h);
  full_backtrack(h, 0ULL);
  u64 k = 0ULL;
  while (k < ucnt) {
    u32 u = tmp[k];
    if (vals[u] < (i8)0) { return 20ULL; }
    if (vals[u] == (i8)0) { full_assign_lvl(h, u, 0xFFFFFFFFu, 0u); }
    k = k + 1ULL;
  }
  h->conflicts = h->conflicts + 1ULL;
  h->learned_lits = h->learned_lits + 1ULL;
  h->iterating = 1ULL;
  return 1ULL;
}

u64 full_analyze_m6_hdr(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  if (h->probing == 0ULL) {
    m6_hdr_update_tier_limits(h);
    m6_hdr_dr_update(h);
  }
  return full_analyze_core_m6(h);
}

void full_rephase_m6_hdr(FullHdr *h) {
  if (h->stable == 0ULL) {
    h->rephase_limit = h->mode_confl_lim;
    return;
  }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  h->rephased = h->rephased + 1ULL;
  u64 sel = h->rephased & 3ULL;
  u64 cv = h->cur_vars;
  i8 *ph = (i8 *)h->phases;
  i8 *pt = (i8 *)h->phases_target;
  i8 *pb = (i8 *)h->phases_best;
  if (sel == 0ULL) {
    u64 k = 0ULL;
    while (k < cv) {
      if (pb[k] != (i8)0) { ph[k] = pb[k]; }
      k = k + 1ULL;
    }
    h->best_assigned = 0ULL;
  } else if (sel == 1ULL) {
    full_walk(h);
  } else if (sel == 2ULL) {
    u64 k = 0ULL;
    while (k < cv) { ph[k] = (i8)1; k = k + 1ULL; }
  } else {
    u64 k = 0ULL;
    while (k < cv) { ph[k] = (i8)(-1); k = k + 1ULL; }
  }
  u64 k2 = 0ULL;
  while (k2 < cv) { pt[k2] = ph[k2]; k2 = k2 + 1ULL; }
  h->target_assigned = 0ULL;
  u64 n = h->rephased;
  u64 nc = (n < 1000000000000ULL) ? n : 1000000000000ULL;
  u64 q = full_log10_q16(nc + 9ULL);
  u64 l2 = (q * q) >> 16;
  u64 l3 = (l2 * q) >> 16;
  u64 scaled = 0ULL;
  if (n <= 1000000ULL) {
    scaled = (1000ULL * n * l3) >> 16;
  } else {
    u64 nlim = (n > 100000000ULL) ? 100000000ULL : n;
    scaled = ((1000ULL * nlim) >> 16) * l3;
  }
  h->rephase_limit = h->conflicts + scaled;
  m6_hdr_set_watermark(h, M6_WM_REPHASE_TICKS, h->search_ticks);
}

u64 full_add_bin(FullHdr *h, u32 a, u32 b) {
  return full_add_bin_m6(h, a, b);
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m6(h, tier_mode);
  full_viv_count_m6(h, bn);
  full_viv_keys_m6(h, bn);
  full_viv_sort_sched_m6(h, bn);
  u64 res = 1ULL;
  u64 bi = 0ULL;
  u64 spent = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         spent < tick_lim) {
    u32 cr = rr[bi * 3ULL];
    u32 sz = ar[(u64)cr + 2ULL];
    spent = spent + 512ULL + ((u64)sz << 5);
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m6(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m6(h, tier_mode);
  }
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  m6_hdr_sync_legacy_tiers(h);
  u64 start = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start > last_p) ? (start - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  if (h->num_redundant == 0ULL) {
    return full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, total);
  }
  if (full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL) == 20ULL) {
    return 20ULL;
  }
  if (full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL) == 20ULL) {
    return 20ULL;
  }
  if (full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, total / 10ULL) == 20ULL) {
    return 20ULL;
  }
  return full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, (total * 3ULL) / 10ULL);
}

u64 full_bve_var(FullHdr *h, u32 v) {
  return full_bve_var_m6(h, v);
}

u64 full_forward_sub(FullHdr *h, u64 budget) {
  return full_forward_sub_m6(h, budget);
}

void full_init_fresh_var(FullHdr *h, u32 fv) {
  full_init_fresh_var_m6(h, fv);
}

u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 raw = (h->search_ticks > last_p) ? (h->search_ticks - last_p) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + clauses) * 8ULL) : raw;
  return (dticks > 10000000ULL) ? dticks : 10000000ULL;
}
"

/-- External callee signatures referenced by `m6OrchAdapters_fns` (`30` externs). -/
def m6OrchAdaptersExterns : List Extern :=
  [ ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool]⟩
  , ⟨"full_propagate_ignore_s15", [i64, i64], [i64]⟩
  , ⟨"full_bcp_s15", [i64], [i64]⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool]⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], []⟩
  , ⟨"full_bump_var", [i64, i32], []⟩
  , ⟨"full_queue_mtf", [i64, i32], []⟩
  , ⟨"full_bump_decay", [i64], []⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], []⟩
  , ⟨"m6_hdr_dr_update", [i64], []⟩
  , ⟨"full_analyze_core_m6", [i64], [i64]⟩
  , ⟨"full_walk", [i64], []⟩
  , ⟨"full_log10_q16", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"full_add_bin_m6", [i64, i32, i32], [i64]⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64]⟩
  , ⟨"full_viv_count_m6", [i64, i64], []⟩
  , ⟨"full_viv_keys_m6", [i64, i64], []⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], []⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64]⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], []⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], []⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩
  , ⟨"full_bve_var_m6", [i64, i32], [i64]⟩
  , ⟨"full_forward_sub_m6", [i64, i64], [i64]⟩
  , ⟨"full_init_fresh_var_m6", [i64, i32], []⟩ ]

/-- Standalone `M6.0` clean adapter module (`16` functions + `30` externs, `0` exits). -/
def m6OrchAdaptersModule : LeanQbe.T.Module :=
  { fns := m6OrchAdapters_fns, externs := m6OrchAdaptersExterns, exits := [] }

/-- Individual function handles matching `m6OrchAdapters_fns` order (`16` fns). -/
def m6aScaleDeltaFn : Fn := ⟨"full_scale_delta", [i64, i64], [i64], full_scale_delta_body⟩
def m6aPropLitRawFn : Fn :=
  ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], full_prop_lit_raw_body⟩
def m6aPropagateIgnoreFn : Fn :=
  ⟨"full_propagate_ignore", [i64, i64], [i64], full_propagate_ignore_body⟩
def m6aPropagateFn : Fn := ⟨"full_propagate", [i64], [i64], full_propagate_body⟩
def m6aBumpAnalyzedM6HdrFn : Fn :=
  ⟨"full_bump_analyzed_m6_hdr", [i64], [], full_bump_analyzed_m6_hdr_body⟩
def m6aRestoreBumpAnaM6HdrFn : Fn :=
  ⟨"full_restore_bump_ana_m6_hdr", [i64], [], full_restore_bump_ana_m6_hdr_body⟩
def m6aAnaFailedLitM6HdrFn : Fn :=
  ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], full_ana_failed_lit_m6_hdr_body⟩
def m6aAnalyzeM6HdrFn : Fn :=
  ⟨"full_analyze_m6_hdr", [i64], [i64], full_analyze_m6_hdr_body⟩
def m6aRephaseM6HdrFn : Fn :=
  ⟨"full_rephase_m6_hdr", [i64], [], full_rephase_m6_hdr_body⟩
def m6aAddBinFn : Fn := ⟨"full_add_bin", [i64, i32, i32], [i64], full_add_bin_body⟩
def m6aVivifyTierM6HdrFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩
def m6aVivifyM6HdrFn : Fn :=
  ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_body⟩
def m6aBveVarFn : Fn := ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_body⟩
def m6aForwardSubFn : Fn := ⟨"full_forward_sub", [i64, i64], [i64], full_forward_sub_body⟩
def m6aInitFreshVarFn : Fn :=
  ⟨"full_init_fresh_var", [i64, i32], [], full_init_fresh_var_body⟩
def m6aProbeDticksM6HdrFn : Fn :=
  ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], full_probe_dticks_m6_hdr_body⟩

theorem full_scale_delta_wf : Func.Wf full_scale_delta_body := by t_wf_reify
theorem full_prop_lit_raw_wf : Func.Wf full_prop_lit_raw_body := by t_wf_reify
theorem full_propagate_ignore_wf : Func.Wf full_propagate_ignore_body := by t_wf_reify
theorem full_propagate_wf : Func.Wf full_propagate_body := by t_wf_reify
theorem full_bump_analyzed_m6_hdr_wf : Func.Wf full_bump_analyzed_m6_hdr_body := by t_wf_reify
theorem full_restore_bump_ana_m6_hdr_wf :
    Func.Wf full_restore_bump_ana_m6_hdr_body := by t_wf_reify
theorem full_ana_failed_lit_m6_hdr_wf :
    Func.Wf full_ana_failed_lit_m6_hdr_body := by t_wf_reify
theorem full_analyze_m6_hdr_wf : Func.Wf full_analyze_m6_hdr_body := by t_wf_reify
theorem full_rephase_m6_hdr_wf : Func.Wf full_rephase_m6_hdr_body := by t_wf_reify
theorem full_add_bin_wf : Func.Wf full_add_bin_body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_wf : Func.Wf full_vivify_tier_m6_hdr_body := by t_wf_reify
theorem full_vivify_m6_hdr_wf : Func.Wf full_vivify_m6_hdr_body := by t_wf_reify
theorem full_bve_var_wf : Func.Wf full_bve_var_body := by t_wf_reify
theorem full_forward_sub_wf : Func.Wf full_forward_sub_body := by t_wf_reify
theorem full_init_fresh_var_wf : Func.Wf full_init_fresh_var_body := by t_wf_reify
theorem full_probe_dticks_m6_hdr_wf : Func.Wf full_probe_dticks_m6_hdr_body := by t_wf_reify

theorem m6OrchAdapters_fns_wf : ∀ f ∈ m6OrchAdapters_fns, f.Wf := by
  simp only [m6OrchAdapters_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_scale_delta_wf, full_prop_lit_raw_wf, full_propagate_ignore_wf, full_propagate_wf,
    full_bump_analyzed_m6_hdr_wf, full_restore_bump_ana_m6_hdr_wf,
    full_ana_failed_lit_m6_hdr_wf, full_analyze_m6_hdr_wf, full_rephase_m6_hdr_wf,
    full_add_bin_wf, full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf, full_bve_var_wf,
    full_forward_sub_wf, full_init_fresh_var_wf, full_probe_dticks_m6_hdr_wf⟩

theorem m6OrchAdapters_acyclic : m6OrchAdaptersModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
