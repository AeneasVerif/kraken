module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` CDCL + Inprocessing SAT Solver in C0 — Part 1 (`Stage 4`)

Low-level primitives for `LeanQbe.T.Examples.Kissat.Full`:
1. `FullHdr` (`PlainHdr`-compatible 96-word prefix + `max_vars`/`cur_vars`/`bva_cap`,
   `flags`, `lit_mark`, `repr`, `sim_sig`, `frame_trail`/`frame_dec`, `walk_*`,
   `extend_stk`, `scratch_buf`, `last_learned`, and inprocessing counters).
2. `COMPACT` `ward` 32-bit word arena, contiguous `u32` watch stack (`full_wstack_defrag`,
   `full_watch_push`), EVSIDS binary heap + VMTF doubly-linked queue, reluctant & EMA.
3. Chronological-aware `full_assign_lvl` / `full_backtrack` (`frame_trail` compaction),
   DIMACS body parser, and 2WL propagation (`full_prop_lit`, `full_propagate`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! full1 "
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

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d);

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_VIV  0x00100000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_ELIM    2u
#define FL_SUBST   4u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_FACT_P  32u
#define FL_FACT_N  64u
#define FL_BONE0   128u
#define FL_BONE1   256u
#define FL_TRANS   512u
#define FL_SWEEP   1024u

u64 full_isqrt(u64 x) {
  if (x <= 1ULL) { return x; }
  u64 r = 0ULL;
  u64 bit = 1ULL << 62;
  while (bit > x) { bit = bit >> 2; }
  while (bit != 0ULL) {
    if (x >= r + bit) {
      x = x - (r + bit);
      r = (r >> 1) + bit;
    } else {
      r = r >> 1;
    }
    bit = bit >> 2;
  }
  return (r == 0ULL) ? 1ULL : r;
}

u64 full_ilog10(u64 x) {
  u64 r = 1ULL;
  u64 p = 10ULL;
  while (x >= p && r < 19ULL) {
    r = r + 1ULL;
    p = p * 10ULL;
  }
  return r;
}

u64 full_rng_next(FullHdr *h) {
  u64 x = h->rng_state;
  if (x == 0ULL) { x = 0x9E3779B97F4A7C15ULL; }
  x = x ^ (x >> 12);
  x = x ^ (x << 25);
  x = x ^ (x >> 27);
  h->rng_state = x;
  return x * 2685821657736338717ULL;
}

u32 full_arena_next(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u64 alen = h->arena_len;
  if ((u64)cref + 3ULL > alen) { return (u32)alen; }
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  u64 p = (u64)cref + 3ULL + (u64)sz;
  if (p > alen) { return (u32)alen; }
  if ((hdr & PH_SHRK) != 0u) {
    while (p < alen && ar[p] != 0xFFFFFFFFu) { p = p + 1ULL; }
    if (p < alen) { p = p + 1ULL; }
  }
  return (u32)p;
}

u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red) {
  u64 need = 3ULL + (u64)sz;
  if (need > h->arena_cap - h->arena_len) { return 0xFFFFFFFFULL; }
  u64 cref = h->arena_len;
  h->arena_len = cref + need;
  u32 *ar = (u32 *)h->arena;
  u32 g = (glue > PH_GLUE_MASK) ? PH_GLUE_MASK : glue;
  ar[cref] = g | (red ? PH_RED : 0u);
  ar[cref + 1ULL] = 2u;
  ar[cref + 2ULL] = sz;
  return cref;
}

void full_wsort_sift(u32 *wvec, u32 *ws, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cl = ws[ch];
    u32 co = wvec[(u64)cl << 1];
    if (ch + 1ULL < n) {
      u32 sl = ws[ch + 1ULL];
      u32 so = wvec[(u64)sl << 1];
      if (so > co) { ch = ch + 1ULL; co = so; }
    }
    u32 rl = ws[root];
    if (wvec[(u64)rl << 1] >= co) { break; }
    ws[root] = ws[ch];
    ws[ch] = rl;
    root = ch;
  }
}

void full_wstack_defrag(FullHdr *h) {
  if (h->wlen <= 1ULL) { h->wusable = 0ULL; return; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u64 n = 0ULL;
  u64 l = 0ULL;
  while (l < nlits) {
    if (wvec[(l << 1) + 1ULL] == 0u) { wvec[l << 1] = 0u; }
    else { ws[n] = (u32)l; n = n + 1ULL; }
    l = l + 1ULL;
  }
  if (n == 0ULL) { wstk[0] = 0u; h->wlen = 1ULL; h->wusable = 0ULL; return; }
  if (n > 1ULL) {
    u64 start = n >> 1;
    while (start > 0ULL) { start = start - 1ULL; full_wsort_sift(wvec, ws, start, n); }
    u64 end = n - 1ULL;
    while (end > 0ULL) {
      u32 tmp = ws[0]; ws[0] = ws[end]; ws[end] = tmp;
      full_wsort_sift(wvec, ws, 0ULL, end);
      end = end - 1ULL;
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

bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) { return false; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  if (h->wlen == 0ULL) {
    if (wcap < 1ULL) { return false; }
    wstk[0] = 0u; h->wlen = 1ULL;
  }
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen && h->wusable > 0ULL) { full_wstack_defrag(h); }
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
      full_wstack_defrag(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k]; wstk[off + k] = 0xFFFFFFFFu; k = k + 1ULL;
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

void full_heap_up(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  if ((u64)p >= h->heap_len || h->heap_len > h->cur_vars || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (p > 0u) {
    u32 pp = (p - 1u) >> 1;
    u32 pv = hp[pp];
    if ((u64)pv >= h->cur_vars || sc[pv] >= vsc) { break; }
    hp[p] = pv; ps[pv] = p; p = pp;
  }
  hp[p] = v; ps[v] = p;
}

void full_heap_down(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  u64 hlen = h->heap_len;
  if ((u64)p >= hlen || hlen > h->cur_vars || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (true) {
    u64 cp = ((u64)p << 1) + 1ULL;
    if (cp >= hlen) { break; }
    u32 cv = hp[cp];
    if ((u64)cv >= h->cur_vars) { break; }
    u64 csc = sc[cv];
    u64 sp = cp + 1ULL;
    if (sp < hlen) {
      u32 sv = hp[sp];
      if ((u64)sv < h->cur_vars && sc[sv] > csc) { cp = sp; cv = sv; csc = sc[sv]; }
    }
    if (csc <= vsc) { break; }
    hp[p] = cv; ps[cv] = p; p = (u32)cp;
  }
  hp[p] = v; ps[v] = p;
}

void full_heap_push(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  if (ps[v] != 0xFFFFFFFFu || h->heap_len >= h->cur_vars) { return; }
  u32 idx = (u32)h->heap_len;
  h->heap_len = h->heap_len + 1ULL;
  hp[idx] = v; ps[v] = idx;
  full_heap_up(h, v);
}

u64 full_heap_pop(FullHdr *h) {
  if (h->heap_len == 0ULL || h->heap_len > h->cur_vars) { return 0xFFFFFFFFULL; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 top = hp[0];
  u64 nlen = h->heap_len - 1ULL;
  h->heap_len = nlen;
  u32 last = hp[nlen];
  if ((u64)top < h->cur_vars) { ps[top] = 0xFFFFFFFFu; }
  if (nlen > 0ULL && (u64)last < h->cur_vars) {
    hp[0] = last; ps[last] = 0u; full_heap_down(h, last);
  }
  if ((u64)top >= h->cur_vars) { return 0xFFFFFFFFULL; }
  return (u64)top;
}

void full_rescale(FullHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  while (v < cv) { sc[v] = sc[v] >> 28ULL; v = v + 1ULL; }
  h->scinc = h->scinc >> 28ULL;
  if (h->scinc < (1ULL << 20)) { h->scinc = 1ULL << 20; }
}

void full_bump_var(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u64 *sc = (u64 *)h->score;
  u64 cur = sc[v];
  u64 inc = h->scinc;
  u64 nsc = (cur > (1ULL << 61) || inc > (1ULL << 61)) ? (1ULL << 60) : (cur + inc);
  sc[v] = nsc;
  full_heap_up(h, v);
  if (nsc >= (1ULL << 60)) { full_rescale(h); }
}

void full_bump_decay(FullHdr *h) {
  u64 inc = h->scinc;
  if (inc < (1ULL << 20)) { inc = 1ULL << 20; }
  if (inc >= (1ULL << 56)) { full_rescale(h); inc = h->scinc; }
  u64 ninc = (inc * 20ULL) / 19ULL;
  h->scinc = ninc;
  if (ninc >= (1ULL << 56)) { full_rescale(h); }
}

void full_queue_renumber(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 st = 0u;
  u64 cur = h->q_first;
  u64 steps = 0ULL;
  while (cur < cv && steps < cv) {
    st = st + 1u;
    qs[cur] = st;
    cur = (u64)qn[cur];
    steps = steps + 1ULL;
  }
  h->q_cur_stamp = (u64)st;
  if (h->q_search_idx < cv) { h->q_search_stamp = (u64)qs[h->q_search_idx]; }
}

void full_queue_mtf(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv || (u64)v == h->q_last) { return; }
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  i8 *vals = (i8 *)h->values;
  if (vals[(u64)v << 1] != (i8)0 && (u64)v == h->q_search_idx) {
    u32 pv = qp[v];
    if ((u64)pv < cv) { h->q_search_idx = (u64)pv; h->q_search_stamp = (u64)qs[pv]; }
    else {
      u32 nv = qn[v];
      if ((u64)nv < cv) { h->q_search_idx = (u64)nv; h->q_search_stamp = (u64)qs[nv]; }
    }
  }
  u32 pv = qp[v];
  u32 nv = qn[v];
  qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu;
  if ((u64)pv >= cv) { h->q_first = (u64)nv; } else { qn[pv] = nv; }
  if ((u64)nv >= cv) { h->q_last = (u64)pv; } else { qp[nv] = pv; }
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last; h->q_last = (u64)v;
  if ((u64)old_last >= cv) { h->q_first = (u64)v; } else { qn[old_last] = v; }
  if (h->q_cur_stamp >= 0xFFFFFFFFULL) { full_queue_renumber(h); }
  else { h->q_cur_stamp = h->q_cur_stamp + 1ULL; qs[v] = (u32)h->q_cur_stamp; }
  if (vals[(u64)v << 1] == (i8)0) {
    h->q_search_idx = (u64)v; h->q_search_stamp = (u64)qs[v];
  }
}

void full_tick_rel(FullHdr *h) {
  if (h->rel_period == 0ULL || h->rel_trigger != 0ULL) { return; }
  if (h->rel_wait > 0ULL) { h->rel_wait = h->rel_wait - 1ULL; }
  if (h->rel_wait > 0ULL) { return; }
  u64 u = h->rel_u;
  u64 v = h->rel_v;
  if (u == 0ULL || v == 0ULL) { u = 1ULL; v = 1ULL; }
  if ((u & (0ULL - u)) == v) { u = u + 1ULL; v = 1ULL; } else { v = v << 1ULL; }
  if (v == 0ULL || v > (1ULL << 30) || h->rel_period > (1ULL << 30)) { u = 1ULL; v = 1ULL; }
  u64 wait = v * h->rel_period;
  if (h->rel_limit > 0ULL && wait > h->rel_limit) { u = 1ULL; v = 1ULL; wait = h->rel_period; }
  h->rel_trigger = 1ULL; h->rel_wait = wait; h->rel_u = u; h->rel_v = v;
}

void full_ema_update(FullHdr *h, u64 glue) {
  u64 g = (glue > 16383ULL) ? 16383ULL : glue;
  u64 ys = g << 24;
  u64 fb = h->ema_fast_biased;
  if (ys >= fb) { fb = fb + ((ys - fb) / 33ULL); } else { fb = fb - ((fb - ys) / 33ULL); }
  h->ema_fast_biased = fb;
  u64 fe = h->ema_fast_exp;
  if (fe > 0ULL) { u64 df = fe / 33ULL; h->ema_fast_exp = (df == 0ULL) ? 0ULL : (fe - df); }
  u64 sb = h->ema_slow_biased;
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  h->ema_slow_biased = sb;
  u64 se = h->ema_slow_exp;
  if (se > 0ULL) { u64 ds = se / 100000ULL; h->ema_slow_exp = (ds == 0ULL) ? 0ULL : (se - ds); }
}

void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl) {
  u32 v = lit >> 1;
  if ((u64)v >= h->cur_vars || h->trail_end >= h->max_vars) { return; }
  i8 *vals = (i8 *)h->values;
  if (vals[lit] != (i8)0) { return; }
  i8 *ph = (i8 *)h->phases;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  vals[lit] = (i8)1;
  vals[lit ^ 1u] = (i8)(-1);
  if ((fl[v] & FL_ACTIVE) != 0u && h->unassigned > 0ULL) {
    h->unassigned = h->unassigned - 1ULL;
  }
  if (h->probing == 0ULL) {
    ph[v] = ((lit & 1u) != 0u) ? (i8)(-1) : (i8)1;
  }
  lvl[v] = alvl;
  if (alvl == 0u) {
    rsns[v] = 0xFFFFFFFFu;
    fl[v] = fl[v] & (~FL_ACTIVE);
    h->unflushed = h->unflushed + 1ULL;
  } else {
    rsns[v] = rsn;
  }
  tpos[v] = (u32)h->trail_end;
  trl[h->trail_end] = lit;
  h->trail_end = h->trail_end + 1ULL;
}

void full_assign(FullHdr *h, u32 lit, u32 rsn) {
  full_assign_lvl(h, lit, rsn, (u32)h->cur_level);
}

void full_save_target_best(FullHdr *h) {
  if (h->probing != 0ULL || h->stable == 0ULL) { return; }
  i8 *vals = (i8 *)h->values;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 assigned = h->trail_end;
  if (assigned > h->target_assigned) {
    h->target_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) { ptgt[k] = vals[k << 1]; k = k + 1ULL; }
  }
  if (assigned > h->best_assigned) {
    h->best_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) { pbst[k] = vals[k << 1]; k = k + 1ULL; }
  }
}

void full_backtrack(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  full_save_target_best(h);
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail;
  u64 cv = h->cur_vars;
  u64 q = (u64)ftrl[target_lvl + 1ULL];
  if (q > h->trail_end) { q = h->trail_end; }
  u64 q_start = q;
  u64 p = q;
  while (p < h->trail_end) {
    u32 lit = trl[p];
    u32 v = lit >> 1;
    if ((u64)v < cv && (u64)lvl[v] <= target_lvl) {
      trl[q] = lit; tpos[v] = (u32)q; q = q + 1ULL;
    } else if ((u64)v < cv) {
      vals[lit] = (i8)0; vals[lit ^ 1u] = (i8)0;
      lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
      if ((fl[v] & FL_ACTIVE) != 0u) { h->unassigned = h->unassigned + 1ULL; }
      if (h->stable != 0ULL) { full_heap_push(h, v); }
      else if ((u64)qs[v] > h->q_search_stamp) {
        h->q_search_idx = (u64)v; h->q_search_stamp = (u64)qs[v];
      }
    }
    p = p + 1ULL;
  }
  h->trail_end = q;
  if (h->propagated > q_start) { h->propagated = q_start; }
  if (h->propagated > q) { h->propagated = q; }
  h->cur_level = target_lvl;
}

u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red) {
  u32 *tmp = (u32 *)h->tmp_lits;
  if (len == 2u) {
    u32 b0 = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (tmp[0] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, tmp[0], b0, 0u, 1u) ||
        !full_watch_push(h, tmp[1], b1, 0u, 1u)) {
      return 0xFFFFFFFFULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFEULL;
  }
  if (len < 3u) { return 0xFFFFFFFFULL; }
  u64 cref = full_alloc_cl(h, len, glue, red);
  if (cref == 0xFFFFFFFFULL) { return 0xFFFFFFFFULL; }
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < len) { ar[cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
  if (!full_watch_push(h, tmp[0], tmp[1] & PW_LIT_MASK, (u32)cref, 2u) ||
      !full_watch_push(h, tmp[1], tmp[0] & PW_LIT_MASK, (u32)cref, 2u)) {
    ar[cref] = ar[cref] | PH_GARB;
    return 0xFFFFFFFFULL;
  }
  if (red) {
    h->num_redundant = h->num_redundant + 1ULL;
    if (h->first_reducible == 0xFFFFFFFFULL) { h->first_reducible = cref; }
  } else {
    h->num_irred = h->num_irred + 1ULL;
  }
  return cref;
}

void full_zero_tables1(FullHdr *h) {
  u64 mx = h->max_vars;
  u64 nlits = mx << 1;
  i8 *vals = (i8 *)h->values;
  i8 *wvals = (i8 *)h->walk_vals;
  u8 *lmrk = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach;
  u64 i = 0ULL;
  while (i < nlits) {
    vals[i] = (i8)0; wvals[i] = (i8)0; lmrk[i] = (u8)0;
    wvec[i << 1] = 0u; wvec[(i << 1) + 1ULL] = 0u;
    repr[i] = (u32)i; tmk[i] = 0u; trc[i] = 0u;
    i = i + 1ULL;
  }
  u32 *wstk = (u32 *)h->watch_stk;
  if (h->wcap > 0ULL) { wstk[0] = 0u; }
  u32 *mstk = (u32 *)h->min_stk;
  u64 mcnt = h->min_depth << 1;
  u64 k = 0ULL;
  while (k < mcnt) { mstk[k] = 0u; k = k + 1ULL; }
  u32 *gu = (u32 *)h->glue_used;
  k = 0ULL;
  while (k < 64ULL) { gu[k] = 0u; k = k + 1ULL; }
  u32 *ll = (u32 *)h->last_learned;
  k = 0ULL;
  while (k < 16ULL) { ll[k] = 0xFFFFFFFFu; k = k + 1ULL; }
}

void full_zero_tables2(FullHdr *h) {
  u64 mv = h->d.mv;
  u64 mx = h->max_vars;
  u8 *mrk = (u8 *)h->mark;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  u64 *sc = (u64 *)h->score;
  u64 *sig = (u64 *)h->sim_sig;
  u64 v = 0ULL;
  u32 all_c = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_FACT_P | FL_FACT_N |
              FL_BONE0 | FL_BONE1 | FL_TRANS | FL_SWEEP;
  while (v < mx) {
    mrk[v] = (u8)0; ph[v] = (i8)1; ptgt[v] = (i8)0; pbst[v] = (i8)0; wbst[v] = (i8)1;
    lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
    ftrl[v] = 0u; fdec[v] = 0xFFFFFFFFu; sc[v] = 0ULL; sig[v] = 0ULL;
    if (v < mv) {
      fl[v] = all_c; hp[v] = (u32)v; ps[v] = (u32)v; qs[v] = (u32)(v + 1ULL);
      qp[v] = (v == 0ULL) ? 0xFFFFFFFFu : (u32)(v - 1ULL);
      qn[v] = (v + 1ULL >= mv) ? 0xFFFFFFFFu : (u32)(v + 1ULL);
    } else {
      fl[v] = 0u; hp[v] = 0u; ps[v] = 0xFFFFFFFFu;
      qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu; qs[v] = 0u;
    }
    v = v + 1ULL;
  }
  ftrl[mx] = 0u; fdec[mx] = 0xFFFFFFFFu;
}

u64 full_fixed_bytes(u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vals_b = (nlits + 7ULL) & (~7ULL);
  u64 mark_b = (max_v + 7ULL) & (~7ULL);
  u64 u32_b = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  return (u64)sizeof(FullHdr) + 320ULL + (vals_b * 3ULL) + (mark_b * 5ULL) +
         (u32_b * 15ULL) + (nlits << 3) + (max_v << 6) + (mdepth << 3);
}

void full_init_ptrs(FullHdr *h, u64 hdr_addr, u64 max_v) {
  u64 nlits = max_v << 1;
  u64 vb = (nlits + 7ULL) & (~7ULL);
  u64 mb = (max_v + 7ULL) & (~7ULL);
  u64 ub = (((max_v + 1ULL) << 2) + 7ULL) & (~7ULL);
  u64 u64b = max_v << 3;
  u64 mdepth = (max_v + 1ULL < 1000ULL) ? (max_v + 1ULL) : 1000ULL;
  u64 base = hdr_addr + (u64)sizeof(FullHdr);
  h->values = base; base = base + vb;
  h->walk_vals = base; base = base + vb;
  h->lit_mark = base; base = base + vb;
  h->mark = base; base = base + mb;
  h->phases = base; base = base + mb;
  h->phases_target = base; base = base + mb;
  h->phases_best = base; base = base + mb;
  h->walk_best = base; base = base + mb;
  h->flags = base; base = base + ub;
  h->level = base; base = base + ub;
  h->reason = base; base = base + ub;
  h->trail = base; base = base + ub;
  h->trail_pos = base; base = base + ub;
  h->tmp_lits = base; base = base + ub;
  h->heap = base; base = base + ub;
  h->pos = base; base = base + ub;
  h->min_clr = base; base = base + ub;
  h->shrink_stk = base; base = base + ub;
  h->q_prev = base; base = base + ub;
  h->q_next = base; base = base + ub;
  h->q_stamp = base; base = base + ub;
  h->frame_trail = base; base = base + ub;
  h->frame_dec = base; base = base + ub;
  h->watch_vec = base; base = base + (nlits << 3);
  h->repr = base; base = base + u64b;
  h->wsort = base; base = base + u64b;
  h->work_stk1 = base; base = base + u64b;
  h->work_stk2 = base; base = base + u64b;
  h->tarjan_mark = base; base = base + u64b;
  h->tarjan_reach = base; base = base + u64b;
  h->score = base; base = base + u64b;
  h->sim_sig = base; base = base + u64b;
  h->min_stk = base; base = base + (mdepth << 3);
  h->glue_used = base; base = base + 256ULL;
  h->last_learned = base; base = base + 64ULL;
  h->arena = base;
  h->min_depth = mdepth;
}

void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = mv;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = mv; h->scinc = 1ULL << 28;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL; h->rel_limit = 1048576ULL; h->rel_wait = 1024ULL;
  h->rel_u = 1ULL; h->rel_v = 1ULL; h->rel_trigger = 0ULL;
  h->conflicts = 0ULL; h->learned_lits = 0ULL; h->min_removed = 0ULL;
  h->stable = 0ULL; h->switched = 0ULL; h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL; h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL; h->search_ticks = 0ULL;
  h->q_first = (mv == 0ULL) ? 0xFFFFFFFFULL : 0ULL;
  h->q_last = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_idx = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_stamp = mv; h->q_cur_stamp = mv;
  h->target_assigned = 0ULL; h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL; h->rephased = 0ULL;
  h->reduce_limit = 1000ULL; h->reductions = 0ULL;
  h->tier1 = 2ULL; h->tier2 = 6ULL;
  h->restarts = 0ULL; h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 1ULL << 24;
  h->oom = 0ULL; h->extend_len = 0ULL;
  h->rng_state = 0x9E3779B97F4A7C15ULL ^ (mv + 1ULL);
  h->chrono_levels = 100ULL; h->otfs_cnt = 0ULL; h->eager_sub_cnt = 0ULL;
  h->probe_limit = 500ULL; h->probings = 0ULL;
  h->elim_limit = 1500ULL; h->eliminations = 0ULL; h->elim_bound = 0ULL;
  h->dense_mode = 0ULL; h->inconsistent = 0ULL; h->iterating = 0ULL;
  h->hbr_cnt = 0ULL; h->trans_cnt = 0ULL; h->viv_cnt = 0ULL; h->subst_cnt = 0ULL;
  h->cong_cnt = 0ULL; h->sweep_cnt = 0ULL; h->bve_cnt = 0ULL; h->bce_cnt = 0ULL;
  h->bva_cnt = 0ULL; h->walk_cnt_stat = 0ULL; h->fwd_sub_cnt = 0ULL; h->fwd_str_cnt = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
}

u64 full_calc_max_v(u64 avail, u64 mv, u64 nc, u64 f0) {
  u64 rem0 = avail - f0;
  u64 bva_cap = 0ULL;
  if (mv >= 2ULL && rem0 > nc * 48ULL + 8192ULL) {
    u64 cand = (mv >> 1) + 16ULL;
    if (cand > 4096ULL) { cand = 4096ULL; }
    u64 max_bva = (rem0 - nc * 48ULL - 4096ULL) / 2688ULL;
    bva_cap = (cand < max_bva) ? cand : max_bva;
  }
  u64 max_v = mv + bva_cap;
  u64 fixed = full_fixed_bytes(max_v);
  if (avail < fixed || avail - fixed < nc * 40ULL + 136ULL) { return mv; }
  return max_v;
}

u64 full_calc_ext_cap(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = rem >> 5;
  if (c > 131072ULL) { c = 131072ULL; }
  return c & (~1ULL);
}

u64 full_calc_scr_cap(u64 rem) {
  if (rem < 8192ULL) { return 0ULL; }
  u64 c = (rem >= 16384ULL) ? (rem >> 4) : (rem >> 5);
  if (c > 32768ULL) { c = 32768ULL; }
  return c & (~1ULL);
}

void full_init_arenas(FullHdr *h, u64 hdr_addr, u64 max_v, u64 avail_dyn) {
  u64 del_bytes = h->delayed_cap * 12ULL;
  u64 ext_cap = h->extend_cap;
  u64 tp = avail_dyn >> 3;
  u64 ap = (tp * 3ULL) / 5ULL;
  if (ap > 134217727ULL) { ap = 134217727ULL; }
  u64 rp = (ap + 5ULL) / 6ULL;
  u64 wp = tp - ap - rp;
  if (wp > 134217727ULL) { wp = 134217727ULL; }
  full_init_ptrs(h, hdr_addr, max_v);
  u64 base = h->arena + (ap << 3);
  h->watch_stk = base; base = base + (wp << 3);
  h->delayed = base; base = base + del_bytes;
  h->red_refs = base; base = base + (rp << 3);
  h->extend_stk = base; base = base + (ext_cap << 2);
  h->scratch_buf = base;
  h->arena_cap = ap << 1; h->wcap = wp << 1; h->red_cap = rp << 1;
}

bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  FullHdr *h = (FullHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) { return false; }
  u64 mv = h->d.mv; u64 nc = h->d.nc; u64 f0 = full_fixed_bytes(mv);
  if (avail < f0 || avail - f0 < nc * 40ULL + 136ULL) { return false; }
  u64 max_v = full_calc_max_v(avail, mv, nc, f0);
  u64 rem = avail - full_fixed_bytes(max_v);
  u64 del_cap = (rem >= 524288ULL) ? 4096ULL : 8ULL;
  u64 del_bytes = del_cap * 12ULL;
  u64 ext_cap = full_calc_ext_cap(rem);
  u64 scr_cap = full_calc_scr_cap(rem);
  u64 dyn = del_bytes + (ext_cap << 2) + (scr_cap << 2);
  if (rem < dyn + nc * 40ULL + 136ULL) { ext_cap = 0ULL; scr_cap = 0ULL; dyn = del_bytes; }
  h->delayed_cap = del_cap; h->extend_cap = ext_cap; h->scratch_cap = scr_cap;
  full_init_arenas(h, hdr_addr, max_v, rem - dyn);
  full_init_hdr(h, mv, max_v, fuel);
  full_zero_tables1(h);
  full_zero_tables2(h);
  return true;
}

bool full_skip_cl(u64 cnf_end, KissatDimacs *d) {
  while (true) {
    u64 st = kissat_next_lit(cnf_end, d);
    if (st == 0ULL) { return false; }
    if (st == 1ULL) { return true; }
  }
}

u64 full_ingest_cl(FullHdr *h, u64 cnf_end) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u8 *mrk = (u8 *)h->mark;
  i8 *vals = (i8 *)h->values;
  u32 tlen = 0u;
  bool taut = false;
  bool err = false;
  while (true) {
    u64 st = kissat_next_lit(cnf_end, &h->d);
    if (st == 0ULL) { err = true; break; }
    if (st == 1ULL) { break; }
    u32 lit = (u32)h->d.val;
    u32 v = lit >> 1;
    if ((u64)v >= h->d.mv) { err = true; break; }
    u8 ptag = (u8)((lit & 1u) + 1u);
    u8 m = mrk[v];
    if (m == (u8)0) {
      if ((u64)tlen >= h->d.mv) { err = true; break; }
      mrk[v] = ptag; tmp[tlen] = lit; tlen = tlen + 1u;
    } else if (m != ptag) {
      taut = true;
    }
  }
  u32 k = 0u;
  while (k < tlen) {
    u32 kv = tmp[k] >> 1;
    if ((u64)kv < h->d.mv) { mrk[kv] = (u8)0; }
    k = k + 1u;
  }
  if (err) { return 0ULL; }
  if (taut) { return 1ULL; }
  u32 keep = 0u;
  u32 i = 0u;
  while (i < tlen) {
    u32 l = tmp[i];
    i8 lv = vals[l];
    if (lv > (i8)0) { return 1ULL; }
    if (lv == (i8)0) { tmp[keep] = l; keep = keep + 1u; }
    i = i + 1u;
  }
  if (keep == 0u) { return 2ULL; }
  if (keep == 1u) { full_assign_lvl(h, tmp[0], 0xFFFFFFFFu, 0u); return 1ULL; }
  u64 cid = full_add_clause(h, keep, 0u, false);
  if (cid == 0xFFFFFFFFULL) { return 3ULL; }
  return 1ULL;
}

u64 full_parse_body(FullHdr *h, u64 cnf_end) {
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
    }
    i = i + 1ULL;
  }
  if (oom_seen) { return 0ULL; }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) { return 0ULL; }
  if (unsat_seen) { return 20ULL; }
  return 1ULL;
}

u64 full_find_repl(FullHdr *h, u64 cref) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 nlits = h->cur_vars << 1;
  u32 sz = ar[cref + 2ULL];
  u32 srch = ar[cref + 1ULL];
  if (srch < 2u || srch >= sz) { srch = 2u; }
  u32 r = srch;
  while (r < sz) {
    u32 cand = ar[cref + 3ULL + (u64)r];
    if ((u64)cand < nlits && vals[cand] >= (i8)0) { ar[cref + 1ULL] = r; return (u64)r; }
    r = r + 1u;
  }
  r = 2u;
  while (r < srch) {
    u32 cand = ar[cref + 3ULL + (u64)r];
    if ((u64)cand < nlits && vals[cand] >= (i8)0) { ar[cref + 1ULL] = r; return (u64)r; }
    r = r + 1u;
  }
  return 0xFFFFFFFFULL;
}

u32 full_assign_level(FullHdr *h, u32 cref, u32 forced_lit) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 sz = ar[(u64)cref + 2ULL];
  u32 res = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if (l != forced_lit) {
      u32 lv = lvl[l >> 1];
      if (lv > res) { res = lv; }
    }
    i = i + 1u;
  }
  return res;
}

bool full_prop_lit(FullHdr *h, u32 lit, u64 ignore_ref) {
  u32 not_lit = lit ^ 1u;
  u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u64 off = (u64)wvec[(u64)not_lit << 1];
  u64 sz = (u64)wvec[((u64)not_lit << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u64 p = off;
  u64 q = off;
  u64 end = off + sz;
  bool confl = false;
  u32 bin_rsn = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
  h->search_ticks = h->search_ticks + 1ULL;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
      u32 other = w0 & PW_LIT_MASK;
      if ((u64)other >= nlits) { continue; }
      i8 ov = vals[other];
      if (ov > (i8)0) { continue; }
      if (ov < (i8)0) {
        h->confl_type = 1ULL; h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)other; h->confl_ref = 0xFFFFFFFFULL;
        confl = true; break;
      }
      full_assign_lvl(h, other, bin_rsn, lvl[not_lit >> 1]);
      continue;
    }
    if (p >= end) { break; }
    u32 cref = wstk[p]; p = p + 1ULL;
    u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      wstk[q] = w0; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
    }
    if ((u64)cref + 3ULL > h->arena_len) { continue; }
    h->search_ticks = h->search_ticks + 1ULL;
    u32 hdr = ar[cref]; u32 csz = ar[(u64)cref + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u || (u64)cref + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
    if (l0 == not_lit) { ar[(u64)cref + 3ULL] = l1; ar[(u64)cref + 4ULL] = not_lit; l0 = l1; }
    else if (l1 != not_lit) { continue; }
    u32 other = l0;
    if ((u64)other >= nlits) { continue; }
    i8 ov = vals[other];
    if (ov > (i8)0) {
      wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
    }
    u64 ri = full_find_repl(h, (u64)cref);
    if (ri != 0xFFFFFFFFULL) {
      u32 repl = ar[(u64)cref + 3ULL + ri];
      ar[(u64)cref + 4ULL] = repl; ar[(u64)cref + 3ULL + ri] = not_lit;
      u64 pr = p - off; u64 qr = q - off; u64 er = end - off;
      bool pok = full_watch_push(h, repl, other & PW_LIT_MASK, cref, 2u);
      off = (u64)wvec[(u64)not_lit << 1]; p = off + pr; q = off + qr; end = off + er;
      if (!pok) {
        ar[(u64)cref + 4ULL] = not_lit; ar[(u64)cref + 3ULL + ri] = repl;
        wstk[q] = w0; wstk[q + 1ULL] = cref; q = q + 2ULL;
        h->oom = 1ULL; confl = true; break;
      }
      continue;
    }
    wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL;
    if ((u64)cref == ignore_ref) { continue; }
    if (ov < (i8)0) {
      h->confl_type = 2ULL; h->confl_ref = (u64)cref; confl = true; break;
    }
    full_assign_lvl(h, other, cref, full_assign_level(h, cref, other));
  }
  while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  return !confl;
}

u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 2ULL; }
    h->fuel = h->fuel - 1ULL;
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    if (!full_prop_lit(h, lit, ignore_ref)) {
      if (h->oom != 0ULL) { return 2ULL; }
      return 1ULL;
    }
  }
  return 0ULL;
}

u64 full_propagate(FullHdr *h) {
  return full_propagate_ignore(h, 0xFFFFFFFFULL);
}

void full_recompute_tiers(FullHdr *h) {
  u32 *gu = (u32 *)h->glue_used;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < 64ULL) { total = total + (u64)gu[g]; g = g + 1ULL; }
  u64 t1 = 2ULL;
  u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total + 1ULL) >> 1;
    u64 lim2 = (total * 9ULL + 9ULL) / 10ULL;
    u64 acc = 0ULL;
    bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < 64ULL) {
      acc = acc + (u64)gu[g];
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1; h->tier2 = t2;
}

void full_mark_reasons(FullHdr *h, bool set_flag) {
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  u64 i = 0ULL;
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

bool full_red_less(u32 *ar, u32 a, u32 b) {
  u32 ga = ar[a] & PH_GLUE_MASK;
  u32 gb = ar[b] & PH_GLUE_MASK;
  if (ga != gb) { return ga > gb; }
  return ar[a + 2u] > ar[b + 2u];
}

void full_red_sift(u32 *ar, u32 *rr, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    if (ch + 1ULL < n && !full_red_less(ar, rr[ch + 1ULL], rr[ch])) { ch = ch + 1ULL; }
    if (!full_red_less(ar, rr[root], rr[ch])) { break; }
    u32 t = rr[root]; rr[root] = rr[ch]; rr[ch] = t;
    root = ch;
  }
}

void full_sort_reds(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 start = n >> 1;
  while (start > 0ULL) { start = start - 1ULL; full_red_sift(ar, rr, start, n); }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = rr[0]; rr[0] = rr[end]; rr[end] = t;
    full_red_sift(ar, rr, 0ULL, end);
    end = end - 1ULL;
  }
}

u64 full_lit_rank(i8 *vals, u32 *lvl, u32 l) {
  i8 v = vals[l];
  if (v > (i8)0) { return 0x200000000ULL; }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[l >> 1];
}

void full_unwatch_large(FullHdr *h, u32 lit, u32 cref) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz == 0ULL) { return; }
  u64 p = off;
  u64 q = off;
  u64 end = off + sz;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
    } else if (p < end) {
      u32 cr = wstk[p]; p = p + 1ULL;
      if (cr != cref) { wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL; }
    }
  }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
}

void full_sweep_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    bool lfix = (lvl[l >> 1] == 0u && vals[l] != (i8)0);
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool ofix = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] != (i8)0);
        if (lfix || ofix) {
          if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else if (!lfix) {
          wstk[q] = w0; q = q + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off);
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag(h);
}

u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u64 cv = h->cur_vars;
  if (!at_root) {
    u32 i = 0u;
    while (i < old_sz) { ar[dst + 3ULL + (u64)i] = ar[src + 3ULL + (u64)i]; i = i + 1u; }
    return (u64)old_sz;
  }
  u32 new_sz = 0u;
  u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[src + 3ULL + (u64)i];
    u32 v = lit >> 1;
    if ((u64)v < cv && lvl[v] == 0u && vals[lit] != (i8)0) {
      if (vals[lit] > (i8)0) { return 0xFFFFFFFFULL; }
    } else {
      ar[dst + 3ULL + (u64)new_sz] = lit;
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  if (new_sz == 0u) { return 0xFFFFFFFEULL; }
  if (new_sz == 1u) {
    u32 ulit = ar[dst + 3ULL];
    if (vals[ulit] < (i8)0) { return 0xFFFFFFFEULL; }
    if (vals[ulit] == (i8)0) { full_assign_lvl(h, ulit, 0xFFFFFFFFu, 0u); return 1ULL; }
    return 0xFFFFFFFFULL;
  }
  if (new_sz == 2u) {
    u32 l0 = ar[dst + 3ULL]; u32 l1 = ar[dst + 4ULL];
    u32 b0 = (l1 & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (l0 & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, l0, b0, 0u, 1u) || !full_watch_push(h, l1, b1, 0u, 1u)) {
      h->oom = 1ULL; return 0xFFFFFFFDULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFFULL;
  }
  return (u64)new_sz;
}
"

def full1Module : LeanQbe.T.Module :=
  { fns := dimacs_fns ++ full1_fns, externs := [], exits := [] }

theorem full_isqrt_wf : Func.Wf full_isqrt_body := by t_wf_reify
theorem full_ilog10_wf : Func.Wf full_ilog10_body := by t_wf_reify
theorem full_rng_next_wf : Func.Wf full_rng_next_body := by t_wf_reify
theorem full_arena_next_wf : Func.Wf full_arena_next_body := by t_wf_reify
theorem full_alloc_cl_wf : Func.Wf full_alloc_cl_body := by t_wf_reify
theorem full_wsort_sift_wf : Func.Wf full_wsort_sift_body := by t_wf_reify
theorem full_wstack_defrag_wf : Func.Wf full_wstack_defrag_body := by t_wf_reify
theorem full_watch_push_wf : Func.Wf full_watch_push_body := by t_wf_reify
theorem full_heap_up_wf : Func.Wf full_heap_up_body := by t_wf_reify
theorem full_heap_down_wf : Func.Wf full_heap_down_body := by t_wf_reify
theorem full_heap_push_wf : Func.Wf full_heap_push_body := by t_wf_reify
theorem full_heap_pop_wf : Func.Wf full_heap_pop_body := by t_wf_reify
theorem full_rescale_wf : Func.Wf full_rescale_body := by t_wf_reify
theorem full_bump_var_wf : Func.Wf full_bump_var_body := by t_wf_reify
theorem full_bump_decay_wf : Func.Wf full_bump_decay_body := by t_wf_reify
theorem full_queue_renumber_wf : Func.Wf full_queue_renumber_body := by t_wf_reify
theorem full_queue_mtf_wf : Func.Wf full_queue_mtf_body := by t_wf_reify
theorem full_tick_rel_wf : Func.Wf full_tick_rel_body := by t_wf_reify
theorem full_ema_update_wf : Func.Wf full_ema_update_body := by t_wf_reify
theorem full_assign_lvl_wf : Func.Wf full_assign_lvl_body := by t_wf_reify
theorem full_assign_wf : Func.Wf full_assign_body := by t_wf_reify
theorem full_save_target_best_wf : Func.Wf full_save_target_best_body := by t_wf_reify
theorem full_backtrack_wf : Func.Wf full_backtrack_body := by t_wf_reify
theorem full_add_clause_wf : Func.Wf full_add_clause_body := by t_wf_reify
theorem full_zero_tables1_wf : Func.Wf full_zero_tables1_body := by t_wf_reify
theorem full_zero_tables2_wf : Func.Wf full_zero_tables2_body := by t_wf_reify
theorem full_fixed_bytes_wf : Func.Wf full_fixed_bytes_body := by t_wf_reify
theorem full_init_ptrs_wf : Func.Wf full_init_ptrs_body := by t_wf_reify
theorem full_init_hdr_wf : Func.Wf full_init_hdr_body := by t_wf_reify
theorem full_calc_max_v_wf : Func.Wf full_calc_max_v_body := by t_wf_reify
theorem full_calc_ext_cap_wf : Func.Wf full_calc_ext_cap_body := by t_wf_reify
theorem full_calc_scr_cap_wf : Func.Wf full_calc_scr_cap_body := by t_wf_reify
theorem full_init_arenas_wf : Func.Wf full_init_arenas_body := by t_wf_reify
theorem full_init_state_wf : Func.Wf full_init_state_body := by t_wf_reify
theorem full_skip_cl_wf : Func.Wf full_skip_cl_body := by t_wf_reify
theorem full_ingest_cl_wf : Func.Wf full_ingest_cl_body := by t_wf_reify
theorem full_parse_body_wf : Func.Wf full_parse_body_body := by t_wf_reify
theorem full_find_repl_wf : Func.Wf full_find_repl_body := by t_wf_reify
theorem full_assign_level_wf : Func.Wf full_assign_level_body := by t_wf_reify
theorem full_prop_lit_wf : Func.Wf full_prop_lit_body := by t_wf_reify
theorem full_propagate_ignore_wf : Func.Wf full_propagate_ignore_body := by t_wf_reify
theorem full_propagate_wf : Func.Wf full_propagate_body := by t_wf_reify
theorem full_recompute_tiers_wf : Func.Wf full_recompute_tiers_body := by t_wf_reify
theorem full_mark_reasons_wf : Func.Wf full_mark_reasons_body := by t_wf_reify
theorem full_red_less_wf : Func.Wf full_red_less_body := by t_wf_reify
theorem full_red_sift_wf : Func.Wf full_red_sift_body := by t_wf_reify
theorem full_sort_reds_wf : Func.Wf full_sort_reds_body := by t_wf_reify
theorem full_lit_rank_wf : Func.Wf full_lit_rank_body := by t_wf_reify
theorem full_unwatch_large_wf : Func.Wf full_unwatch_large_body := by t_wf_reify
theorem full_sweep_bins_wf : Func.Wf full_sweep_bins_body := by t_wf_reify
theorem full_sweep_copy_wf : Func.Wf full_sweep_copy_body := by t_wf_reify

theorem full1_fns_wf : ∀ f ∈ full1_fns, f.Wf := by
  simp only [full1_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_isqrt_wf, full_ilog10_wf, full_rng_next_wf, full_arena_next_wf,
    full_alloc_cl_wf, full_wsort_sift_wf, full_wstack_defrag_wf, full_watch_push_wf,
    full_heap_up_wf, full_heap_down_wf, full_heap_push_wf, full_heap_pop_wf,
    full_rescale_wf, full_bump_var_wf, full_bump_decay_wf, full_queue_renumber_wf,
    full_queue_mtf_wf, full_tick_rel_wf, full_ema_update_wf, full_assign_lvl_wf,
    full_assign_wf, full_save_target_best_wf, full_backtrack_wf, full_add_clause_wf,
    full_zero_tables1_wf, full_zero_tables2_wf, full_fixed_bytes_wf, full_init_ptrs_wf,
    full_init_hdr_wf, full_calc_max_v_wf, full_calc_ext_cap_wf, full_calc_scr_cap_wf,
    full_init_arenas_wf, full_init_state_wf, full_skip_cl_wf, full_ingest_cl_wf,
    full_parse_body_wf, full_find_repl_wf, full_assign_level_wf, full_prop_lit_wf,
    full_propagate_ignore_wf, full_propagate_wf, full_recompute_tiers_wf,
    full_mark_reasons_wf, full_red_less_wf, full_red_sift_wf, full_sort_reds_wf,
    full_lit_rank_wf, full_unwatch_large_wf, full_sweep_bins_wf, full_sweep_copy_wf⟩

theorem full1_acyclic : full1Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full
