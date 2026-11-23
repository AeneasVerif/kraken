module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave-2 `PR-W2E-lite`: Irred-First GC, 75% Watch Defrag + Radix Sort,
Binary Dedup, Level-0 Trail Flush, Parse-Time Unit BCP, & Root-False Extend Push

Standalone drop-in overrides certifying against canonical `Full` / `FullM4` specs
with zero `FullHdr` changes (`144` words frozen):
1. `full_wstack_defrag_m6` + `full_wstack_radix_sort_m6`: zero empty `wvec` offsets,
   sorted fast path, 256-bucket LSB radix sort with `max_off` early exit and
   `full_wsort_sift` fallback.
2. `full_watch_push_m6`: proactive defrag at `wlen * 4 >= wcap * 3` (`75%`).
3. `full_lit_rank_m6`: tie-break satisfied literals by `~lvl[l >> 1]`.
4. `full_sweep_bins_range_m6` & `full_sweep_bins_m6`: `wsort`-stamped binary watch
   deduplication + fixed-binary deletion + defrag. A binary is deleted for a root-satisfied
   literal always, but for a root-falsified literal only once the trail is fully propagated
   (`propagated >= trail_end`): otherwise the other literal may not be implied yet and the
   deletion would lose the clause (the M6 Stage-1 model-check regression).
5. `full_rewatch_range_m6` & `full_rewatch_arena_m6`, `full_move_red_end_buf_m6` &
   `full_move_red_end_m6`, `full_arena_sweep_m6`: partial sweep skipping verified
   irredundant prefix, irredundant-before-redundant partitioning updating live
   `first_reducible` and `reason`, and range rewatch.
6. `full_mark_reasons_m6`: level-0 skip + `frame_trail[1]` lower bound.
7. `full_flush_trail_m6`: level-0 backtrack/propagate/unflushed reset.
8. `full_parse_body_m6`: parse-time unit BCP preserving `fuel` and `oom = 0`.
9. `full_extend_push2_m6` & `full_extend_push_cl_m6`: root-false literal skipping with
   `RC-01` overflow-safe capacity bounds.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6WatchGc "
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
#define PH_RSN 0x00200000u
#define PH_RED 0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define EXT_BLK_FLAG 0x80000000u

extern void full_wsort_sift(u32 *wvec, u32 *ws, u64 start, u64 n);
extern u32 full_arena_next(FullHdr *h, u32 p);
extern u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_ingest_cl(FullHdr *h, u64 cnf_end);
extern bool full_skip_cl(u64 cnf_end, KissatDimacs *d);
extern u64 kissat_skip_ws_comments(u64 cur, u64 cnf_end);

void full_wstack_radix_sort_m6(u32 *wvec, u32 *ws, u32 *tmp, u32 *cnt,
                               u64 n, u64 max_off) {
  u64 shift = 0ULL;
  while (shift < 32ULL && (max_off >> shift) != 0ULL) {
    u64 b = 0ULL;
    while (b < 256ULL) { cnt[b] = 0u; b = b + 1ULL; }
    u64 j = 0ULL;
    while (j < n) {
      u32 lit = ws[j];
      u64 bkt = ((u64)wvec[(u64)lit << 1] >> shift) & 255ULL;
      cnt[bkt] = cnt[bkt] + 1u;
      j = j + 1ULL;
    }
    u64 sum = 0ULL;
    b = 0ULL;
    while (b < 256ULL) {
      u64 c = (u64)cnt[b];
      cnt[b] = (u32)sum;
      sum = sum + c;
      b = b + 1ULL;
    }
    j = 0ULL;
    while (j < n) {
      u32 lit = ws[j];
      u64 bkt = ((u64)wvec[(u64)lit << 1] >> shift) & 255ULL;
      u64 pos = (u64)cnt[bkt];
      cnt[bkt] = (u32)(pos + 1ULL);
      tmp[pos] = lit;
      j = j + 1ULL;
    }
    j = 0ULL;
    while (j < n) { ws[j] = tmp[j]; j = j + 1ULL; }
    shift = shift + 8ULL;
  }
}

void full_wstack_defrag_m6(FullHdr *h) {
  if (h->wlen <= 1ULL) { h->wusable = 0ULL; return; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u64 n = 0ULL;
  u64 l = 0ULL;
  u64 max_off = 0ULL;
  u64 prev_off = 0ULL;
  bool sorted = true;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    if (wvec[(l << 1) + 1ULL] == 0u) {
      wvec[l << 1] = 0u;
    } else {
      if (off < prev_off) { sorted = false; }
      prev_off = off;
      if (off > max_off) { max_off = off; }
      ws[n] = (u32)l;
      n = n + 1ULL;
    }
    l = l + 1ULL;
  }
  if (n == 0ULL) { wstk[0] = 0u; h->wlen = 1ULL; h->wusable = 0ULL; return; }
  if (!sorted && n > 1ULL) {
    if ((n << 1) + 256ULL <= (h->max_vars << 1)) {
      full_wstack_radix_sort_m6(wvec, ws, ws + n, ws + (n << 1), n, max_off);
    } else if (h->wcap - h->wlen >= n + 256ULL) {
      full_wstack_radix_sort_m6(wvec, ws, wstk + h->wlen, wstk + h->wlen + n,
                                n, max_off);
    } else {
      u64 start = n >> 1;
      while (start > 0ULL) {
        start = start - 1ULL; full_wsort_sift(wvec, ws, start, n);
      }
      u64 end = n - 1ULL;
      while (end > 0ULL) {
        u32 tmp = ws[0]; ws[0] = ws[end]; ws[end] = tmp;
        full_wsort_sift(wvec, ws, 0ULL, end);
        end = end - 1ULL;
      }
    }
  }
  u64 p = 1ULL;
  u64 i = 0ULL;
  while (i < n) {
    u32 lit = ws[i];
    u64 off = (u64)wvec[(u64)lit << 1];
    u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    if (off != p) {
      u64 k = 0ULL;
      while (k < sz) { wstk[p + k] = wstk[off + k]; k = k + 1ULL; }
      wvec[(u64)lit << 1] = (u32)p;
    }
    p = p + sz;
    i = i + 1ULL;
  }
  h->wlen = p;
  h->wusable = 0ULL;
}

bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  if (h->wlen == 0ULL) {
    if (wcap < 1ULL) { return false; }
    wstk[0] = 0u; h->wlen = 1ULL;
  }
  if (h->wlen * 4ULL >= wcap * 3ULL && h->wusable * 4ULL >= h->wlen) {
    full_wstack_defrag_m6(h);
  }
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen && h->wusable > 0ULL) { full_wstack_defrag_m6(h); }
    if (c > wcap - h->wlen) { return false; }
    u64 pos = h->wlen;
    wstk[pos] = w0;
    if (cnt == 2u) { wstk[pos + 1ULL] = w1; }
    wvec[(u64)lit << 1] = (u32)pos;
    wvec[((u64)lit << 1) + 1ULL] = cnt;
    h->wlen = pos + c;
    return true;
  }
  u64 end = off + sz;
  if (end == h->wlen && c <= wcap - h->wlen) {
    wstk[end] = w0;
    if (cnt == 2u) { wstk[end + 1ULL] = w1; }
    wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
    h->wlen = end + c;
    return true;
  }
  if (end + c <= h->wlen && wstk[end] == 0xFFFFFFFFu &&
      (cnt == 1u || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
    wstk[end] = w0;
    if (cnt == 2u) { wstk[end + 1ULL] = w1; }
    wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
    if (h->wusable >= c) { h->wusable = h->wusable - c; }
    return true;
  }
  u64 ncap = (sz == 0ULL) ? 2ULL : (sz << 1);
  if (ncap < sz + c) { ncap = sz + c; }
  if (ncap > wcap - h->wlen) {
    if (h->wusable > 0ULL) {
      full_wstack_defrag_m6(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k]; wstk[off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wstk[dst + sz] = w0;
  if (cnt == 2u) { wstk[dst + sz + 1ULL] = w1; }
  k = sz + c;
  while (k < ncap) { wstk[dst + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[(u64)lit << 1] = (u32)dst;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
  h->wusable = h->wusable + sz + (ncap - (sz + c));
  h->wlen = dst + ncap;
  return true;
}

u64 full_lit_rank_m6(i8 *vals, u32 *lvl, u32 l) {
  i8 v = vals[l];
  if (v > (i8)0) { return 0x200000000ULL | (u64)(~lvl[l >> 1]); }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[l >> 1];
}

void full_sweep_bins_range_m6(FullHdr *h, u64 keep_large_before) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *seen = (u32 *)h->wsort;
  bool prop_done = (h->propagated >= h->trail_end);
  u64 s0 = 0ULL;
  while (s0 < nlits) { seen[s0] = 0xFFFFFFFFu; s0 = s0 + 1ULL; }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    bool lfix = (lvl[l >> 1] == 0u &&
      (vals[l] > (i8)0 || (prop_done && vals[l] < (i8)0)));
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool ofix = ((u64)ot < nlits && lvl[ot >> 1] == 0u &&
          (vals[ot] > (i8)0 || (prop_done && vals[ot] < (i8)0)));
        if (lfix || ofix) {
          if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else if (!lfix) {
          if ((u64)ot < nlits && seen[ot] == (u32)l) {
            if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
              h->num_binary = h->num_binary - 1ULL;
            }
          } else {
            if ((u64)ot < nlits) { seen[ot] = (u32)l; }
            wstk[q] = w0; q = q + 1ULL;
          }
        }
        p = p + 1ULL;
      } else {
        if (p + 1ULL < end) {
          u32 cr = wstk[p + 1ULL];
          if (keep_large_before > 0ULL && (u64)cr < keep_large_before) {
            wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL;
          }
        }
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off);
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag_m6(h);
}

void full_sweep_bins_m6(FullHdr *h) {
  full_sweep_bins_range_m6(h, 0ULL);
}

bool full_rewatch_range_m6(FullHdr *h, u64 start, u64 dst) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool at_root = (h->cur_level == 0ULL);
  u64 p = start;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    if (!at_root && sz >= 3u) {
      u32 i0 = 0u; u64 r0 = full_lit_rank_m6(vals, lvl, ar[p + 3ULL]);
      u32 i = 1u;
      while (i < sz) {
        u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r0) { r0 = rk; i0 = i; }
        i = i + 1u;
      }
      if (i0 != 0u) {
        u32 t = ar[p + 3ULL]; ar[p + 3ULL] = ar[p + 3ULL + (u64)i0];
        ar[p + 3ULL + (u64)i0] = t;
      }
      u32 i1 = 1u; u64 r1 = full_lit_rank_m6(vals, lvl, ar[p + 4ULL]);
      i = 2u;
      while (i < sz) {
        u64 rk = full_lit_rank_m6(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r1) { r1 = rk; i1 = i; }
        i = i + 1u;
      }
      if (i1 != 1u) {
        u32 t = ar[p + 4ULL]; ar[p + 4ULL] = ar[p + 3ULL + (u64)i1];
        ar[p + 3ULL + (u64)i1] = t;
      }
    }
    ar[p + 1ULL] = 2u;
    u32 l0 = ar[p + 3ULL]; u32 l1 = ar[p + 4ULL];
    if (!full_watch_push_m6(h, l0, l1 & PW_LIT_MASK, (u32)p, 2u) ||
        !full_watch_push_m6(h, l1, l0 & PW_LIT_MASK, (u32)p, 2u)) {
      h->oom = 1ULL; return false;
    }
    p = p + 3ULL + (u64)sz;
  }
  return true;
}

bool full_rewatch_arena_m6(FullHdr *h, u64 dst) {
  return full_rewatch_range_m6(h, 0ULL, dst);
}

void full_move_red_pass2_m6(FullHdr *h, u64 mid, u64 rlen, u64 dst, u32 *buf) {
  u32 *ar = (u32 *)h->arena;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 rpos = 0ULL;
  while (rpos < rlen) {
    u32 hdr = buf[rpos];
    u32 sz = buf[rpos + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    u64 od = mid + rpos;
    u64 k = 0ULL;
    while (k < clen) { ar[od + k] = buf[rpos + k]; k = k + 1ULL; }
    if ((hdr & PH_RSN) != 0u) {
      u32 v = buf[rpos + 1ULL];
      if ((u64)v < cv) { rsns[v] = (u32)od; }
    }
    ar[od] = hdr & (~PH_RSN);
    ar[od + 1ULL] = 2u;
    rpos = rpos + clen;
  }
  h->first_reducible = (mid < dst) ? mid : 0xFFFFFFFFULL;
}

void full_move_red_end_buf_m6(FullHdr *h, u64 first_red, u64 dst, u32 *buf) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 src = first_red;
  u64 idst = first_red;
  u64 rlen = 0ULL;
  while (src < dst) {
    u32 hdr = ar[src];
    u32 sz = ar[src + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    if ((hdr & PH_RED) != 0u) {
      u64 k = 0ULL;
      while (k < clen) { buf[rlen + k] = ar[src + k]; k = k + 1ULL; }
      if ((hdr & PH_RSN) != 0u) {
        u32 i = 0u;
        bool found = false;
        while (i < sz) {
          u32 lit = ar[src + 3ULL + (u64)i]; u32 v = lit >> 1;
          if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
            buf[rlen + 1ULL] = v; found = true; break;
          }
          i = i + 1u;
        }
        if (!found) { buf[rlen] = hdr & (~PH_RSN); }
      }
      rlen = rlen + clen;
    } else {
      if (idst != src) {
        u64 k = 0ULL;
        while (k < clen) { ar[idst + k] = ar[src + k]; k = k + 1ULL; }
        if ((hdr & PH_RSN) != 0u) {
          u32 i = 0u;
          while (i < sz) {
            u32 lit = ar[idst + 3ULL + (u64)i]; u32 v = lit >> 1;
            if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
              rsns[v] = (u32)idst; break;
            }
            i = i + 1u;
          }
        }
      }
      ar[idst] = hdr & (~PH_RSN);
      idst = idst + clen;
    }
    src = src + clen;
  }
  full_move_red_pass2_m6(h, idst, rlen, dst, buf);
}

void full_move_red_end_m6(FullHdr *h, u64 first_red, u64 dst) {
  u32 *ar = (u32 *)h->arena;
  u64 p = first_red;
  u64 red_words = 0ULL;
  while (p < dst) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    u64 clen = 3ULL + (u64)sz;
    if ((hdr & PH_RED) != 0u) { red_words = red_words + clen; }
    p = p + clen;
  }
  if (red_words == 0ULL) { h->first_reducible = 0xFFFFFFFFULL; return; }
  if (red_words <= h->scratch_cap) {
    full_move_red_end_buf_m6(h, first_red, dst, (u32 *)h->scratch_buf);
    return;
  }
  if (dst + red_words <= h->arena_cap) {
    full_move_red_end_buf_m6(h, first_red, dst, ar + dst);
    return;
  }
  p = first_red;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    ar[p] = ar[p] & (~PH_RSN);
    p = p + 3ULL + (u64)sz;
  }
  h->first_reducible = first_red;
}

u64 full_arena_sweep_m6(FullHdr *h) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *rsns = (u32 *)h->reason;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  bool at_root = (h->cur_level == 0ULL);
  u64 start = 0ULL;
  u64 pre_irred = 0ULL;
  if (!at_root && h->unflushed == 0ULL && h->first_reducible > 0ULL &&
      h->first_reducible < alen) {
    u64 fp = h->first_reducible;
    u64 p = 0ULL;
    u64 cnt = 0ULL;
    bool pre_ok = true;
    while (p < fp) {
      if (p + 3ULL > fp) { pre_ok = false; break; }
      u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
      if ((hdr & (PH_GARB | PH_SHRK | PH_RED)) != 0u || sz < 3u ||
          p + 3ULL + (u64)sz > fp) {
        pre_ok = false; break;
      }
      p = p + 3ULL + (u64)sz;
      cnt = cnt + 1ULL;
    }
    if (pre_ok && p == fp) {
      start = fp;
      pre_irred = cnt;
      u64 cp = 0ULL;
      while (cp < fp) {
        u32 sz = ar[cp + 2ULL];
        ar[cp] = ar[cp] & (~PH_RSN);
        cp = cp + 3ULL + (u64)sz;
      }
    }
  }
  full_sweep_bins_range_m6(h, start);
  u64 src = start;
  u64 dst = start;
  u64 first_red = 0xFFFFFFFFULL;
  u64 irred = pre_irred;
  u64 redd = 0ULL;
  bool has_irred_after_red = false;
  bool unsat = false;
  bool new_unit = false;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src]; u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)full_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u ||
        src + 3ULL + (u64)old_sz > alen) {
      src = nsrc; continue;
    }
    u64 st = full_sweep_copy(h, src, dst, old_sz, at_root);
    if (st == 0xFFFFFFFEULL) { unsat = true; break; }
    if (st == 0xFFFFFFFDULL) { break; }
    if (st == 1ULL) { new_unit = true; src = nsrc; continue; }
    if (st == 0xFFFFFFFFULL) { src = nsrc; continue; }
    u32 new_sz = (u32)st;
    u32 nhdr = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst] = nhdr;
    ar[dst + 1ULL] = 2u;
    ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RSN) != 0u) {
      u32 i = 0u;
      while (i < new_sz) {
        u32 lit = ar[dst + 3ULL + (u64)i]; u32 v = lit >> 1;
        if ((u64)v < cv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
          rsns[v] = (u32)dst;
          if (!at_root && (first_red != 0xFFFFFFFFULL || (hdr & PH_RED) != 0u)) {
            ar[dst] = nhdr | PH_RSN;
          }
          break;
        }
        i = i + 1u;
      }
    }
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else {
      if (first_red != 0xFFFFFFFFULL) { has_irred_after_red = true; }
      irred = irred + 1ULL;
    }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  if (!unsat && h->oom == 0ULL && has_irred_after_red && first_red < dst) {
    full_move_red_end_m6(h, first_red, dst);
  } else {
    h->first_reducible = first_red;
    if (!at_root && first_red < dst) {
      u64 cp = first_red;
      while (cp < dst) {
        u32 sz = ar[cp + 2ULL];
        ar[cp] = ar[cp] & (~PH_RSN);
        cp = cp + 3ULL + (u64)sz;
      }
    }
  }
  h->arena_len = dst;
  h->arena_garbage = 0ULL;
  h->num_irred = irred;
  h->num_redundant = redd;
  u32 *ll = (u32 *)h->last_learned;
  u64 li = 0ULL;
  while (li < 16ULL) { ll[li] = 0xFFFFFFFFu; li = li + 1ULL; }
  if (unsat) { return 2ULL; }
  if (h->oom != 0ULL) { return 3ULL; }
  if (!full_rewatch_range_m6(h, start, dst)) { return 3ULL; }
  return new_unit ? 1ULL : 0ULL;
}

void full_mark_reasons_m6(FullHdr *h, bool set_flag) {
  if (h->cur_level == 0ULL) { return; }
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u32 *ftrl = (u32 *)h->frame_trail;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  u64 i = (u64)ftrl[1];
  while (i < h->trail_end) {
    u32 v = trl[i] >> 1;
    if ((u64)v < cv && lvl[v] > 0u) {
      u32 r = rsns[v];
      if (r < 0x80000000u && (u64)r + 3ULL <= alen) {
        if (set_flag) { ar[r] = ar[r] | PH_RSN; }
        else { ar[r] = ar[r] & (~PH_RSN); }
      }
    }
    i = i + 1ULL;
  }
}

u64 full_flush_trail_m6(FullHdr *h) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  u64 pr = full_propagate(h);
  if (pr == 1ULL) { h->inconsistent = 1ULL; return 20ULL; }
  if (pr != 0ULL) { return 0ULL; }
  h->unflushed = 0ULL;
  return 1ULL;
}

u64 full_parse_body_m6(FullHdr *h, u64 cnf_end) {
  u64 nb0 = h->num_binary;
  bool unsat_seen = false;
  bool oom_seen = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!full_skip_cl(cnf_end, &h->d)) { return 0ULL; }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 st = full_ingest_cl(h, cnf_end);
      if (st == 0ULL) { return 0ULL; }
      if (st == 2ULL) { unsat_seen = true; }
      else if (st == 3ULL) { oom_seen = true; }
      else if (h->propagated < h->trail_end &&
               (h->arena_len > 0ULL || h->num_binary != nb0)) {
        u64 sfuel = h->fuel;
        u64 pr = full_propagate(h);
        h->fuel = sfuel;
        if (pr == 1ULL) { unsat_seen = true; }
        else if (pr == 2ULL && h->oom != 0ULL) {
          h->oom = 0ULL; oom_seen = true;
        }
      }
    }
    i = i + 1ULL;
  }
  if (oom_seen) { return 0ULL; }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) { return 0ULL; }
  if (unsat_seen) { return 20ULL; }
  return 1ULL;
}

bool full_extend_push2_m6(FullHdr *h, u32 blk_lit, u32 other) {
  u64 nlits = h->cur_vars << 1;
  u32 ot = other & PW_LIT_MASK;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool skip_ot = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
  u64 need = skip_ot ? 1ULL : 2ULL;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = blk_lit | EXT_BLK_FLAG;
  if (!skip_ot) { ext[p + 1ULL] = ot; }
  h->extend_len = p + need;
  return true;
}

bool full_extend_push_cl_m6(FullHdr *h, u32 blk_lit, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 sz = ar[(u64)cref + 2ULL];
  if ((u64)cref + 3ULL + (u64)sz > h->arena_len) { return false; }
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 bl = blk_lit & PW_LIT_MASK;
  u64 keep = 0ULL;
  u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl) {
      if (!((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
        keep = keep + 1ULL;
      }
    }
    i = i + 1u;
  }
  u64 need = 1ULL + keep;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = bl | EXT_BLK_FLAG;
  p = p + 1ULL;
  i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl) {
      if (!((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
        ext[p] = lit; p = p + 1ULL;
      }
    }
    i = i + 1u;
  }
  h->extend_len = p;
  return true;
}
"

/-- External callee signatures referenced by `m6WatchGc_fns`. -/
def m6WatchGcExterns : List Extern :=
  [ ⟨"full_wsort_sift", [i64, i64, i64, i64], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64]⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool]⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64]⟩
  ]

def m6WatchGcModule : LeanQbe.T.Module :=
  { fns := m6WatchGc_fns, externs := m6WatchGcExterns, exits := [] }

theorem full_wstack_radix_sort_m6_wf : Func.Wf full_wstack_radix_sort_m6_body := by
  t_wf_reify

theorem full_wstack_defrag_m6_wf : Func.Wf full_wstack_defrag_m6_body := by
  t_wf_reify

theorem full_watch_push_m6_wf : Func.Wf full_watch_push_m6_body := by
  t_wf_reify

theorem full_lit_rank_m6_wf : Func.Wf full_lit_rank_m6_body := by
  t_wf_reify

theorem full_sweep_bins_range_m6_wf : Func.Wf full_sweep_bins_range_m6_body := by
  t_wf_reify

theorem full_sweep_bins_m6_wf : Func.Wf full_sweep_bins_m6_body := by
  t_wf_reify

theorem full_rewatch_range_m6_wf : Func.Wf full_rewatch_range_m6_body := by
  t_wf_reify

theorem full_rewatch_arena_m6_wf : Func.Wf full_rewatch_arena_m6_body := by
  t_wf_reify

theorem full_move_red_pass2_m6_wf : Func.Wf full_move_red_pass2_m6_body := by
  t_wf_reify

theorem full_move_red_end_buf_m6_wf : Func.Wf full_move_red_end_buf_m6_body := by
  t_wf_reify

theorem full_move_red_end_m6_wf : Func.Wf full_move_red_end_m6_body := by
  t_wf_reify

theorem full_arena_sweep_m6_wf : Func.Wf full_arena_sweep_m6_body := by
  t_wf_reify

theorem full_mark_reasons_m6_wf : Func.Wf full_mark_reasons_m6_body := by
  t_wf_reify

theorem full_flush_trail_m6_wf : Func.Wf full_flush_trail_m6_body := by
  t_wf_reify

theorem full_parse_body_m6_wf : Func.Wf full_parse_body_m6_body := by
  t_wf_reify

theorem full_extend_push2_m6_wf : Func.Wf full_extend_push2_m6_body := by
  t_wf_reify

theorem full_extend_push_cl_m6_wf : Func.Wf full_extend_push_cl_m6_body := by
  t_wf_reify

theorem m6WatchGc_fns_wf : ∀ f ∈ m6WatchGc_fns, f.Wf := by
  simp only [m6WatchGc_fns, List.mem_cons, List.not_mem_nil, or_false]
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · exact full_wstack_radix_sort_m6_wf
  · exact full_wstack_defrag_m6_wf
  · exact full_watch_push_m6_wf
  · exact full_lit_rank_m6_wf
  · exact full_sweep_bins_range_m6_wf
  · exact full_sweep_bins_m6_wf
  · exact full_rewatch_range_m6_wf
  · exact full_rewatch_arena_m6_wf
  · exact full_move_red_pass2_m6_wf
  · exact full_move_red_end_buf_m6_wf
  · exact full_move_red_end_m6_wf
  · exact full_arena_sweep_m6_wf
  · exact full_mark_reasons_m6_wf
  · exact full_flush_trail_m6_wf
  · exact full_parse_body_m6_wf
  · exact full_extend_push2_m6_wf
  · exact full_extend_push_cl_m6_wf

theorem m6WatchGc_acyclic : m6WatchGcModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6WatchGc
