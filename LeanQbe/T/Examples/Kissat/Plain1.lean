module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0.Elab

/-!
# Kissat `D-Plain` (`--plain`) CDCL SAT Solver in C0 — Part 1 (`Stage 3`)

Low-level primitives for `LeanQbe.T.Examples.Kissat.Plain`:
1. `COMPACT` `ward` 32-bit word arena (`plain_arena_next`, `plain_alloc_cl`), packed clause header
   (`glue` LBD, `garbage`, `reason`, `redundant`, `shrunk`, `used`), `searched`, `size`, `lits[]`.
2. Contiguous `u32` watch stack `vectors` (`plain_wstack_defrag`, `plain_watch_push`) with tagged
   binary watches (`bit 31 = 1`) and 2-word blocking-literal large watches (`bit 31 = 0`).
3. Dual VSIDS binary max-heap (`heap`/`pos`/`score`) + VMTF doubly-linked queue (`q_prev`/`q_next`/
   `q_stamp`), `saved`/`target`/`best` `phases`, reluctant doubling, and pure-`u64` Q24 glucose EMA.
4. `plain_assign`, `plain_backtrack`, `plain_add_clause`, `plain_zero_tables`, `plain_init_state`,
   `plain_skip_cl`, `plain_ingest_cl`, and `plain_parse_body`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

local elab "kissat_c0! " pfx:ident src:str : command =>
  elabC0Module (some pfx.getId) src.getString (forceExpose := true) (emitModule := false)

kissat_c0! plain1 "
typedef struct {
  u64 mv;
  u64 nc;
  u64 cur;
  u64 val;
} KissatDimacs;

typedef struct {
  KissatDimacs d;
  u64 arena_cap;
  u64 wcap;
  u64 arena_len;
  u64 wlen;
  u64 values;
  u64 mark;
  u64 level;
  u64 reason;
  u64 trail;
  u64 watch_vec;
  u64 arena;
  u64 watch_stk;
  u64 delayed;
  u64 tmp_lits;
  u64 trail_end;
  u64 propagated;
  u64 cur_level;
  u64 fuel;
  u64 confl_ref;
  u64 tmp_cnt;
  u64 tmp_len;
  u64 heap;
  u64 pos;
  u64 score;
  u64 phases;
  u64 min_stk;
  u64 min_clr;
  u64 heap_len;
  u64 scinc;
  u64 min_depth;
  u64 min_clr_len;
  u64 min_clr_full;
  u64 rel_period;
  u64 rel_limit;
  u64 rel_wait;
  u64 rel_u;
  u64 rel_v;
  u64 rel_trigger;
  u64 conflicts;
  u64 learned_lits;
  u64 min_removed;
  u64 trail_pos;
  u64 q_prev;
  u64 q_next;
  u64 q_stamp;
  u64 phases_target;
  u64 phases_best;
  u64 wsort;
  u64 shrink_stk;
  u64 red_refs;
  u64 glue_used;
  u64 red_cap;
  u64 delayed_cap;
  u64 delayed_len;
  u64 wusable;
  u64 arena_garbage;
  u64 first_reducible;
  u64 num_irred;
  u64 num_redundant;
  u64 num_binary;
  u64 unflushed;
  u64 probing;
  u64 confl_type;
  u64 confl_lit0;
  u64 confl_lit1;
  u64 stable;
  u64 switched;
  u64 mode_count;
  u64 mode_confl_lim;
  u64 mode_tick_lim;
  u64 mode_saved_ticks;
  u64 search_ticks;
  u64 q_first;
  u64 q_last;
  u64 q_search_idx;
  u64 q_search_stamp;
  u64 q_cur_stamp;
  u64 target_assigned;
  u64 best_assigned;
  u64 rephase_limit;
  u64 rephased;
  u64 reduce_limit;
  u64 reductions;
  u64 tier1;
  u64 tier2;
  u64 restarts;
  u64 restart_limit;
  u64 ema_fast_biased;
  u64 ema_fast_exp;
  u64 ema_slow_biased;
  u64 ema_slow_exp;
  u64 oom;
} PlainHdr;

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d);

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

u64 plain_isqrt(u64 x) {
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

u64 plain_ilog10(u64 x) {
  u64 r = 1ULL;
  u64 p = 10ULL;
  while (x >= p && r < 19ULL) {
    r = r + 1ULL;
    p = p * 10ULL;
  }
  return r;
}

u32 plain_arena_next(PlainHdr *h, u32 cref) {
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

u64 plain_alloc_cl(PlainHdr *h, u32 sz, u32 glue, bool red) {
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

void plain_wstack_defrag(PlainHdr *h) {
  u64 wlen = h->wlen;
  if (wlen <= 1ULL) {
    h->wusable = 0ULL;
    return;
  }
  u64 nlits = h->d.mv << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u64 n = 0ULL;
  u64 l = 0ULL;
  while (l < nlits) {
    u32 sz = wvec[(l << 1) + 1ULL];
    if (sz == 0u) {
      wvec[l << 1] = 0u;
    } else {
      ws[n] = (u32)l;
      n = n + 1ULL;
    }
    l = l + 1ULL;
  }
  if (n == 0ULL) {
    wstk[0] = 0u;
    h->wlen = 1ULL;
    h->wusable = 0ULL;
    return;
  }
  if (n > 1ULL) {
    u64 start = n >> 1;
    while (start > 0ULL) {
      start = start - 1ULL;
      u64 root = start;
      while (true) {
        u64 child = (root << 1) + 1ULL;
        if (child >= n) { break; }
        u32 cl = ws[child];
        u32 co = wvec[(u64)cl << 1];
        if (child + 1ULL < n) {
          u32 sl = ws[child + 1ULL];
          u32 so = wvec[(u64)sl << 1];
          if (so > co) { child = child + 1ULL; co = so; }
        }
        u32 rl = ws[root];
        if (wvec[(u64)rl << 1] >= co) { break; }
        ws[root] = ws[child];
        ws[child] = rl;
        root = child;
      }
    }
    u64 end = n - 1ULL;
    while (end > 0ULL) {
      u32 tmp = ws[0];
      ws[0] = ws[end];
      ws[end] = tmp;
      u64 root = 0ULL;
      while (true) {
        u64 child = (root << 1) + 1ULL;
        if (child >= end) { break; }
        u32 cl = ws[child];
        u32 co = wvec[(u64)cl << 1];
        if (child + 1ULL < end) {
          u32 sl = ws[child + 1ULL];
          u32 so = wvec[(u64)sl << 1];
          if (so > co) { child = child + 1ULL; co = so; }
        }
        u32 rl = ws[root];
        if (wvec[(u64)rl << 1] >= co) { break; }
        ws[root] = ws[child];
        ws[child] = rl;
        root = child;
      }
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
      while (k < sz) {
        wstk[p + k] = wstk[off + k];
        k = k + 1ULL;
      }
      wvec[(u64)lit << 1] = (u32)p;
    }
    p = p + sz;
    i = i + 1ULL;
  }
  h->wlen = p;
  h->wusable = 0ULL;
}

bool plain_watch_push(PlainHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->d.mv << 1) || (cnt != 1u && cnt != 2u)) { return false; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  if (h->wlen == 0ULL) {
    if (wcap < 1ULL) { return false; }
    wstk[0] = 0u;
    h->wlen = 1ULL;
  }
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen) {
      if (h->wusable > 0ULL) { plain_wstack_defrag(h); }
      if (c > wcap - h->wlen) { return false; }
    }
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
      plain_wstack_defrag(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k];
    wstk[off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wstk[dst + sz] = w0;
  if (cnt == 2u) { wstk[dst + sz + 1ULL] = w1; }
  k = sz + c;
  while (k < ncap) {
    wstk[dst + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wvec[(u64)lit << 1] = (u32)dst;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
  h->wusable = h->wusable + sz + (ncap - (sz + c));
  h->wlen = dst + ncap;
  return true;
}

void plain_heap_up(PlainHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  if ((u64)p >= h->heap_len || h->heap_len > h->d.mv || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (p > 0u) {
    u32 pp = (p - 1u) >> 1;
    u32 pv = hp[pp];
    if ((u64)pv >= h->d.mv) { break; }
    if (sc[pv] >= vsc) { break; }
    hp[p] = pv;
    ps[pv] = p;
    p = pp;
  }
  hp[p] = v;
  ps[v] = p;
}

void plain_heap_down(PlainHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  u64 hlen = h->heap_len;
  if ((u64)p >= hlen || hlen > h->d.mv || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (true) {
    u64 cp = ((u64)p << 1) + 1ULL;
    if (cp >= hlen) { break; }
    u32 cv = hp[cp];
    if ((u64)cv >= h->d.mv) { break; }
    u64 csc = sc[cv];
    u64 sp = cp + 1ULL;
    if (sp < hlen) {
      u32 sv = hp[sp];
      if ((u64)sv < h->d.mv && sc[sv] > csc) {
        cp = sp;
        cv = sv;
        csc = sc[sv];
      }
    }
    if (csc <= vsc) { break; }
    hp[p] = cv;
    ps[cv] = p;
    p = (u32)cp;
  }
  hp[p] = v;
  ps[v] = p;
}

void plain_heap_push(PlainHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  if (ps[v] != 0xFFFFFFFFu || h->heap_len >= h->d.mv) { return; }
  u32 idx = (u32)h->heap_len;
  h->heap_len = h->heap_len + 1ULL;
  hp[idx] = v;
  ps[v] = idx;
  plain_heap_up(h, v);
}

u64 plain_heap_pop(PlainHdr *h) {
  if (h->heap_len == 0ULL || h->heap_len > h->d.mv) { return 0xFFFFFFFFULL; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 top = hp[0];
  u64 nlen = h->heap_len - 1ULL;
  h->heap_len = nlen;
  u32 last = hp[nlen];
  if ((u64)top < h->d.mv) { ps[top] = 0xFFFFFFFFu; }
  if (nlen > 0ULL && (u64)last < h->d.mv) {
    hp[0] = last;
    ps[last] = 0u;
    plain_heap_down(h, last);
  }
  if ((u64)top >= h->d.mv) { return 0xFFFFFFFFULL; }
  return (u64)top;
}

void plain_rescale(PlainHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 mv = h->d.mv;
  u64 v = 0ULL;
  while (v < mv) {
    sc[v] = sc[v] >> 28ULL;
    v = v + 1ULL;
  }
  h->scinc = h->scinc >> 28ULL;
  if (h->scinc < (1ULL << 20)) { h->scinc = 1ULL << 20; }
}

void plain_bump_var(PlainHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u64 *sc = (u64 *)h->score;
  u64 cur = sc[v];
  u64 inc = h->scinc;
  u64 nsc = (cur > (1ULL << 61) || inc > (1ULL << 61)) ? (1ULL << 60) : (cur + inc);
  sc[v] = nsc;
  plain_heap_up(h, v);
  if (nsc >= (1ULL << 60)) { plain_rescale(h); }
}

void plain_bump_decay(PlainHdr *h) {
  u64 inc = h->scinc;
  if (inc < (1ULL << 20)) { inc = 1ULL << 20; }
  if (inc >= (1ULL << 56)) {
    plain_rescale(h);
    inc = h->scinc;
  }
  u64 ninc = (inc * 20ULL) / 19ULL;
  h->scinc = ninc;
  if (ninc >= (1ULL << 56)) { plain_rescale(h); }
}

void plain_queue_mtf(PlainHdr *h, u32 v) {
  u64 mv = h->d.mv;
  if ((u64)v >= mv || (u64)v == h->q_last) { return; }
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  i8 *vals = (i8 *)h->values;
  if (vals[(u64)v << 1] != (i8)0 && (u64)v == h->q_search_idx) {
    u32 pv = qp[v];
    if ((u64)pv < mv) {
      h->q_search_idx = (u64)pv;
      h->q_search_stamp = (u64)qs[pv];
    } else {
      u32 nv = qn[v];
      if ((u64)nv < mv) {
        h->q_search_idx = (u64)nv;
        h->q_search_stamp = (u64)qs[nv];
      }
    }
  }
  u32 pv = qp[v];
  u32 nv = qn[v];
  qp[v] = 0xFFFFFFFFu;
  qn[v] = 0xFFFFFFFFu;
  if ((u64)pv >= mv) { h->q_first = (u64)nv; }
  else { qn[pv] = nv; }
  if ((u64)nv >= mv) { h->q_last = (u64)pv; }
  else { qp[nv] = pv; }
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last;
  h->q_last = (u64)v;
  if ((u64)old_last >= mv) { h->q_first = (u64)v; }
  else { qn[old_last] = v; }
  if (h->q_cur_stamp >= 0xFFFFFFFFULL) {
    u32 st = 0u;
    u64 cur = h->q_first;
    u64 steps = 0ULL;
    while (cur < mv && steps < mv) {
      st = st + 1u;
      qs[cur] = st;
      cur = (u64)qn[cur];
      steps = steps + 1ULL;
    }
    h->q_cur_stamp = (u64)st;
    if (h->q_search_idx < mv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  } else {
    h->q_cur_stamp = h->q_cur_stamp + 1ULL;
    qs[v] = (u32)h->q_cur_stamp;
  }
  if (vals[(u64)v << 1] == (i8)0) {
    h->q_search_idx = (u64)v;
    h->q_search_stamp = (u64)qs[v];
  }
}

void plain_tick_rel(PlainHdr *h) {
  if (h->rel_period == 0ULL || h->rel_trigger != 0ULL) { return; }
  if (h->rel_wait > 0ULL) { h->rel_wait = h->rel_wait - 1ULL; }
  if (h->rel_wait > 0ULL) { return; }
  u64 u = h->rel_u;
  u64 v = h->rel_v;
  if (u == 0ULL || v == 0ULL) { u = 1ULL; v = 1ULL; }
  if ((u & (0ULL - u)) == v) {
    u = u + 1ULL;
    v = 1ULL;
  } else {
    v = v << 1ULL;
  }
  if (v == 0ULL || v > (1ULL << 30) || h->rel_period > (1ULL << 30)) {
    u = 1ULL;
    v = 1ULL;
  }
  u64 wait = v * h->rel_period;
  if (h->rel_limit > 0ULL && wait > h->rel_limit) {
    u = 1ULL;
    v = 1ULL;
    wait = h->rel_period;
  }
  h->rel_trigger = 1ULL;
  h->rel_wait = wait;
  h->rel_u = u;
  h->rel_v = v;
}

void plain_ema_update(PlainHdr *h, u64 glue) {
  u64 g = (glue > 16383ULL) ? 16383ULL : glue;
  u64 ys = g << 24;
  u64 fb = h->ema_fast_biased;
  if (ys >= fb) { fb = fb + ((ys - fb) / 33ULL); }
  else { fb = fb - ((fb - ys) / 33ULL); }
  h->ema_fast_biased = fb;
  u64 fe = h->ema_fast_exp;
  if (fe > 0ULL) {
    u64 df = fe / 33ULL;
    h->ema_fast_exp = (df == 0ULL) ? 0ULL : (fe - df);
  }
  u64 sb = h->ema_slow_biased;
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  h->ema_slow_biased = sb;
  u64 se = h->ema_slow_exp;
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    h->ema_slow_exp = (ds == 0ULL) ? 0ULL : (se - ds);
  }
}

void plain_assign(PlainHdr *h, u32 lit, u32 rsn) {
  u32 v = lit >> 1;
  if ((u64)v >= h->d.mv || h->trail_end >= h->d.mv) { return; }
  i8 *vals = (i8 *)h->values;
  i8 *ph = (i8 *)h->phases;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  vals[lit] = (i8)1;
  vals[lit ^ 1u] = (i8)-1;
  if (h->probing == 0ULL) {
    ph[v] = ((lit & 1u) != 0u) ? (i8)(-1) : (i8)1;
  }
  lvl[v] = (u32)h->cur_level;
  if (h->cur_level == 0ULL) {
    rsns[v] = 0xFFFFFFFFu;
    h->unflushed = h->unflushed + 1ULL;
  } else {
    rsns[v] = rsn;
  }
  tpos[v] = (u32)h->trail_end;
  trl[h->trail_end] = lit;
  h->trail_end = h->trail_end + 1ULL;
}

void plain_backtrack(PlainHdr *h, u64 target_lvl) {
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *qs = (u32 *)h->q_stamp;
  u64 mv = h->d.mv;
  if (h->probing == 0ULL && h->stable != 0ULL) {
    i8 *ptgt = (i8 *)h->phases_target;
    i8 *pbst = (i8 *)h->phases_best;
    if (h->trail_end > h->target_assigned) {
      h->target_assigned = h->trail_end;
      u64 k = 0ULL;
      while (k < mv) { ptgt[k] = vals[k << 1]; k = k + 1ULL; }
    }
    if (h->trail_end > h->best_assigned) {
      h->best_assigned = h->trail_end;
      u64 k = 0ULL;
      while (k < mv) { pbst[k] = vals[k << 1]; k = k + 1ULL; }
    }
  }
  u64 te = h->trail_end;
  while (te > 0ULL) {
    u32 lit = trl[te - 1ULL];
    u32 v = lit >> 1;
    if ((u64)lvl[v] <= target_lvl) { break; }
    vals[lit] = (i8)0;
    vals[lit ^ 1u] = (i8)0;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    if (h->stable != 0ULL) {
      plain_heap_push(h, v);
    } else if ((u64)v < mv && (u64)qs[v] > h->q_search_stamp) {
      h->q_search_idx = (u64)v;
      h->q_search_stamp = (u64)qs[v];
    }
    te = te - 1ULL;
  }
  h->trail_end = te;
  if (h->propagated > te) { h->propagated = te; }
  h->cur_level = target_lvl;
}

u64 plain_add_clause(PlainHdr *h, u32 len, u32 glue, bool red) {
  u32 *tmp = (u32 *)h->tmp_lits;
  if (len == 2u) {
    u32 b0 = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (tmp[0] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!plain_watch_push(h, tmp[0], b0, 0u, 1u) ||
        !plain_watch_push(h, tmp[1], b1, 0u, 1u)) {
      return 0xFFFFFFFFULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFEULL;
  }
  if (len < 3u) { return 0xFFFFFFFFULL; }
  u64 cref = plain_alloc_cl(h, len, glue, red);
  if (cref == 0xFFFFFFFFULL) { return 0xFFFFFFFFULL; }
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < len) {
    ar[cref + 3ULL + (u64)i] = tmp[i];
    i = i + 1u;
  }
  if (!plain_watch_push(h, tmp[0], tmp[1] & PW_LIT_MASK, (u32)cref, 2u) ||
      !plain_watch_push(h, tmp[1], tmp[0] & PW_LIT_MASK, (u32)cref, 2u)) {
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

void plain_zero_tables(PlainHdr *h) {
  u64 mv = h->d.mv;
  u64 nlits = mv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 i = 0ULL;
  while (i < nlits) {
    vals[i] = (i8)0;
    wvec[i << 1] = 0u;
    wvec[(i << 1) + 1ULL] = 0u;
    i = i + 1ULL;
  }
  u32 *wstk = (u32 *)h->watch_stk;
  if (h->wcap > 0ULL) { wstk[0] = 0u; }
  u8 *mrk = (u8 *)h->mark;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *mclr = (u32 *)h->min_clr;
  u32 *sstk = (u32 *)h->shrink_stk;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u64 *sc = (u64 *)h->score;
  u64 v = 0ULL;
  while (v < mv) {
    mrk[v] = (u8)0;
    ph[v] = (i8)1;
    ptgt[v] = (i8)0;
    pbst[v] = (i8)0;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    tmp[v] = 0u;
    hp[v] = (u32)v;
    ps[v] = (u32)v;
    mclr[v] = 0u;
    sstk[v] = 0u;
    tpos[v] = 0u;
    qp[v] = (v == 0ULL) ? 0xFFFFFFFFu : (u32)(v - 1ULL);
    qn[v] = (v + 1ULL >= mv) ? 0xFFFFFFFFu : (u32)(v + 1ULL);
    qs[v] = (u32)(v + 1ULL);
    sc[v] = 0ULL;
    v = v + 1ULL;
  }
  u32 *mstk = (u32 *)h->min_stk;
  u64 mcnt = h->min_depth << 1;
  u64 k = 0ULL;
  while (k < mcnt) {
    mstk[k] = 0u;
    k = k + 1ULL;
  }
  u32 *gu = (u32 *)h->glue_used;
  k = 0ULL;
  while (k < 64ULL) {
    gu[k] = 0u;
    k = k + 1ULL;
  }
}

bool plain_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  PlainHdr *h = (PlainHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) { return false; }
  u64 mv = h->d.mv;
  u64 nc = h->d.nc;
  u64 nlits = mv << 1;
  u64 vals_bytes = (nlits + 7ULL) & (~7ULL);
  u64 mark_bytes = (mv + 7ULL) & (~7ULL);
  u64 u32_var_bytes = ((mv << 2) + 7ULL) & (~7ULL);
  u64 u64_var_bytes = mv << 3;
  u64 wvec_bytes = nlits << 3;
  u64 mdepth = (mv + 1ULL < 1000ULL) ? (mv + 1ULL) : 1000ULL;
  u64 mstk_bytes = mdepth << 3;
  u64 hdr_sz = (u64)sizeof(PlainHdr);
  u64 fixed = hdr_sz + 256ULL + vals_bytes + (mark_bytes << 2) + (u32_var_bytes * 12ULL) +
              wvec_bytes + u64_var_bytes + u64_var_bytes + mstk_bytes;
  if (avail < fixed) { return false; }
  u64 rem = avail - fixed;
  if (rem < nc * 40ULL + 136ULL) { return false; }
  u64 del_cap = (rem >= 524288ULL) ? 4096ULL : 8ULL;
  u64 del_bytes = del_cap * 12ULL;
  u64 total_pairs = (rem - del_bytes) >> 3;
  u64 arena_pairs = (total_pairs * 3ULL) / 5ULL;
  if (arena_pairs > 134217727ULL) { arena_pairs = 134217727ULL; }
  u64 red_pairs = (arena_pairs + 5ULL) / 6ULL;
  u64 w_pairs = total_pairs - arena_pairs - red_pairs;
  if (w_pairs > 134217727ULL) { w_pairs = 134217727ULL; }
  u64 arena_cap = arena_pairs << 1;
  u64 red_cap = red_pairs << 1;
  u64 wcap = w_pairs << 1;
  u64 base = hdr_addr + hdr_sz;
  h->values = base; base = base + vals_bytes;
  h->mark = base; base = base + mark_bytes;
  h->phases = base; base = base + mark_bytes;
  h->phases_target = base; base = base + mark_bytes;
  h->phases_best = base; base = base + mark_bytes;
  h->level = base; base = base + u32_var_bytes;
  h->reason = base; base = base + u32_var_bytes;
  h->trail = base; base = base + u32_var_bytes;
  h->trail_pos = base; base = base + u32_var_bytes;
  h->tmp_lits = base; base = base + u32_var_bytes;
  h->heap = base; base = base + u32_var_bytes;
  h->pos = base; base = base + u32_var_bytes;
  h->min_clr = base; base = base + u32_var_bytes;
  h->shrink_stk = base; base = base + u32_var_bytes;
  h->q_prev = base; base = base + u32_var_bytes;
  h->q_next = base; base = base + u32_var_bytes;
  h->q_stamp = base; base = base + u32_var_bytes;
  h->watch_vec = base; base = base + wvec_bytes;
  h->wsort = base; base = base + u64_var_bytes;
  h->score = base; base = base + u64_var_bytes;
  h->min_stk = base; base = base + mstk_bytes;
  h->glue_used = base; base = base + 256ULL;
  h->arena = base; base = base + (arena_cap << 2);
  h->watch_stk = base; base = base + (wcap << 2);
  h->delayed = base; base = base + del_bytes;
  h->red_refs = base;
  h->arena_cap = arena_cap;
  h->wcap = wcap;
  h->red_cap = red_cap;
  h->delayed_cap = del_cap;
  h->delayed_len = 0ULL;
  h->arena_len = 0ULL;
  h->wlen = 1ULL;
  h->wusable = 0ULL;
  h->arena_garbage = 0ULL;
  h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL;
  h->num_redundant = 0ULL;
  h->num_binary = 0ULL;
  h->unflushed = 0ULL;
  h->probing = 0ULL;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->fuel = fuel;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  h->confl_lit0 = 0ULL;
  h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL;
  h->tmp_len = 0ULL;
  h->heap_len = mv;
  h->scinc = 1ULL << 28;
  h->min_depth = mdepth;
  h->min_clr_len = 0ULL;
  h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL;
  h->rel_limit = 1048576ULL;
  h->rel_wait = 1024ULL;
  h->rel_u = 1ULL;
  h->rel_v = 1ULL;
  h->rel_trigger = 0ULL;
  h->conflicts = 0ULL;
  h->learned_lits = 0ULL;
  h->min_removed = 0ULL;
  h->stable = 0ULL;
  h->switched = 0ULL;
  h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL;
  h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL;
  h->search_ticks = 0ULL;
  h->q_first = (mv == 0ULL) ? 0xFFFFFFFFULL : 0ULL;
  h->q_last = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_idx = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_stamp = mv;
  h->q_cur_stamp = mv;
  h->target_assigned = 0ULL;
  h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL;
  h->rephased = 0ULL;
  h->reduce_limit = 1000ULL;
  h->reductions = 0ULL;
  h->tier1 = 2ULL;
  h->tier2 = 6ULL;
  h->restarts = 0ULL;
  h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL;
  h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL;
  h->ema_slow_exp = 1ULL << 24;
  h->oom = 0ULL;
  plain_zero_tables(h);
  return true;
}

bool plain_skip_cl(u64 cnf_end, KissatDimacs *d) {
  while (true) {
    u64 st = kissat_next_lit(cnf_end, d);
    if (st == 0ULL) { return false; }
    if (st == 1ULL) { return true; }
  }
}

u64 plain_ingest_cl(PlainHdr *h, u64 cnf_end) {
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
      mrk[v] = ptag;
      tmp[tlen] = lit;
      tlen = tlen + 1u;
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
    if (lv == (i8)0) {
      tmp[keep] = l;
      keep = keep + 1u;
    }
    i = i + 1u;
  }
  if (keep == 0u) { return 2ULL; }
  if (keep == 1u) {
    plain_assign(h, tmp[0], 0xFFFFFFFFu);
    return 1ULL;
  }
  u64 cid = plain_add_clause(h, keep, 0u, false);
  if (cid == 0xFFFFFFFFULL) { return 3ULL; }
  return 1ULL;
}

u64 plain_parse_body(PlainHdr *h, u64 cnf_end) {
  bool unsat_seen = false;
  bool oom_seen = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!plain_skip_cl(cnf_end, &h->d)) { return 0ULL; }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 st = plain_ingest_cl(h, cnf_end);
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

u64 plain_find_repl(PlainHdr *h, u64 cref) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 nlits = h->d.mv << 1;
  u32 sz = ar[cref + 2ULL];
  u32 srch = ar[cref + 1ULL];
  if (srch < 2u || srch >= sz) { srch = 2u; }
  u32 r = srch;
  while (r < sz) {
    u32 cand = ar[cref + 3ULL + (u64)r];
    if ((u64)cand < nlits && vals[cand] >= (i8)0) {
      ar[cref + 1ULL] = r;
      return (u64)r;
    }
    r = r + 1u;
  }
  r = 2u;
  while (r < srch) {
    u32 cand = ar[cref + 3ULL + (u64)r];
    if ((u64)cand < nlits && vals[cand] >= (i8)0) {
      ar[cref + 1ULL] = r;
      return (u64)r;
    }
    r = r + 1u;
  }
  return 0xFFFFFFFFULL;
}

bool plain_prop_lit(PlainHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u;
  u64 nlits = h->d.mv << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
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
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0;
      q = q + 1ULL;
      u32 other = w0 & PW_LIT_MASK;
      if ((u64)other >= nlits) { continue; }
      i8 ov = vals[other];
      if (ov > (i8)0) { continue; }
      if (ov < (i8)0) {
        h->confl_type = 1ULL;
        h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)other;
        h->confl_ref = 0xFFFFFFFFULL;
        confl = true;
        break;
      }
      plain_assign(h, other, bin_rsn);
      continue;
    }
    if (p >= end) { break; }
    u32 cref = wstk[p];
    p = p + 1ULL;
    u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      wstk[q] = w0;
      wstk[q + 1ULL] = cref;
      q = q + 2ULL;
      continue;
    }
    if ((u64)cref + 3ULL > h->arena_len) { continue; }
    h->search_ticks = h->search_ticks + 1ULL;
    u32 hdr = ar[cref];
    u32 csz = ar[(u64)cref + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u ||
        (u64)cref + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    u32 l0 = ar[(u64)cref + 3ULL];
    u32 l1 = ar[(u64)cref + 4ULL];
    if (l0 == not_lit) {
      ar[(u64)cref + 3ULL] = l1;
      ar[(u64)cref + 4ULL] = not_lit;
      l0 = l1;
    } else if (l1 != not_lit) {
      continue;
    }
    u32 other = l0;
    if ((u64)other >= nlits) { continue; }
    i8 ov = vals[other];
    if (ov > (i8)0) {
      wstk[q] = other & PW_LIT_MASK;
      wstk[q + 1ULL] = cref;
      q = q + 2ULL;
      continue;
    }
    u64 ri = plain_find_repl(h, (u64)cref);
    if (ri != 0xFFFFFFFFULL) {
      u32 repl = ar[(u64)cref + 3ULL + ri];
      ar[(u64)cref + 4ULL] = repl;
      ar[(u64)cref + 3ULL + ri] = not_lit;
      u64 p_rel = p - off;
      u64 q_rel = q - off;
      u64 end_rel = end - off;
      bool pok = plain_watch_push(h, repl, other & PW_LIT_MASK, cref, 2u);
      off = (u64)wvec[(u64)not_lit << 1];
      p = off + p_rel;
      q = off + q_rel;
      end = off + end_rel;
      if (!pok) {
        ar[(u64)cref + 4ULL] = not_lit;
        ar[(u64)cref + 3ULL + ri] = repl;
        wstk[q] = w0;
        wstk[q + 1ULL] = cref;
        q = q + 2ULL;
        h->oom = 1ULL;
        confl = true;
        break;
      }
      continue;
    }
    wstk[q] = other & PW_LIT_MASK;
    wstk[q + 1ULL] = cref;
    q = q + 2ULL;
    if (ov < (i8)0) {
      h->confl_type = 2ULL;
      h->confl_ref = (u64)cref;
      confl = true;
      break;
    }
    plain_assign(h, other, cref);
  }
  while (p < end) {
    wstk[q] = wstk[p];
    q = q + 1ULL;
    p = p + 1ULL;
  }
  u64 k = q;
  while (k < end) {
    wstk[k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  return !confl;
}

u64 plain_propagate(PlainHdr *h) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 2ULL; }
    h->fuel = h->fuel - 1ULL;
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    if (!plain_prop_lit(h, lit)) {
      if (h->oom != 0ULL) { return 2ULL; }
      return 1ULL;
    }
  }
  return 0ULL;
}

void plain_recompute_tiers(PlainHdr *h) {
  u32 *gu = (u32 *)h->glue_used;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < 64ULL) {
    total = total + (u64)gu[g];
    g = g + 1ULL;
  }
  u64 t1 = 2ULL;
  u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total + 1ULL) >> 1;
    u64 lim2 = (total * 9ULL + 9ULL) / 10ULL;
    u64 acc = 0ULL;
    bool got1 = false;
    bool got2 = false;
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
  h->tier1 = t1;
  h->tier2 = t2;
}

void plain_mark_reasons(PlainHdr *h, bool set_flag) {
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u64 mv = h->d.mv;
  u64 alen = h->arena_len;
  u64 i = 0ULL;
  while (i < h->trail_end) {
    u32 v = trl[i] >> 1;
    if ((u64)v < mv && lvl[v] > 0u) {
      u32 r = rsns[v];
      if (r < 0x80000000u && (u64)r + 3ULL <= alen) {
        if (set_flag) { ar[r] = ar[r] | PH_RSN; }
        else { ar[r] = ar[r] & (~PH_RSN); }
      }
    }
    i = i + 1ULL;
  }
}

bool plain_red_less(u32 *ar, u32 a, u32 b) {
  u32 ga = ar[a] & PH_GLUE_MASK;
  u32 gb = ar[b] & PH_GLUE_MASK;
  if (ga != gb) { return ga > gb; }
  return ar[a + 2u] > ar[b + 2u];
}

void plain_sort_reds(PlainHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    u64 root = start;
    while (true) {
      u64 ch = (root << 1) + 1ULL;
      if (ch >= n) { break; }
      if (ch + 1ULL < n && !plain_red_less(ar, rr[ch + 1ULL], rr[ch])) {
        ch = ch + 1ULL;
      }
      if (!plain_red_less(ar, rr[root], rr[ch])) { break; }
      u32 t = rr[root]; rr[root] = rr[ch]; rr[ch] = t;
      root = ch;
    }
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = rr[0]; rr[0] = rr[end]; rr[end] = t;
    u64 root = 0ULL;
    while (true) {
      u64 ch = (root << 1) + 1ULL;
      if (ch >= end) { break; }
      if (ch + 1ULL < end && !plain_red_less(ar, rr[ch + 1ULL], rr[ch])) {
        ch = ch + 1ULL;
      }
      if (!plain_red_less(ar, rr[root], rr[ch])) { break; }
      u32 t2 = rr[root]; rr[root] = rr[ch]; rr[ch] = t2;
      root = ch;
    }
    end = end - 1ULL;
  }
}
"

def plain1Module : LeanQbe.T.Module :=
  { fns := dimacs_fns ++ plain1_fns, externs := [], exits := [] }

theorem plain_isqrt_wf : Func.Wf plain_isqrt_body := by t_wf_reify
theorem plain_ilog10_wf : Func.Wf plain_ilog10_body := by t_wf_reify
theorem plain_arena_next_wf : Func.Wf plain_arena_next_body := by t_wf_reify
theorem plain_alloc_cl_wf : Func.Wf plain_alloc_cl_body := by t_wf_reify
theorem plain_wstack_defrag_wf : Func.Wf plain_wstack_defrag_body := by t_wf_reify
theorem plain_watch_push_wf : Func.Wf plain_watch_push_body := by t_wf_reify
theorem plain_heap_up_wf : Func.Wf plain_heap_up_body := by t_wf_reify
theorem plain_heap_down_wf : Func.Wf plain_heap_down_body := by t_wf_reify
theorem plain_heap_push_wf : Func.Wf plain_heap_push_body := by t_wf_reify
theorem plain_heap_pop_wf : Func.Wf plain_heap_pop_body := by t_wf_reify
theorem plain_rescale_wf : Func.Wf plain_rescale_body := by t_wf_reify
theorem plain_bump_var_wf : Func.Wf plain_bump_var_body := by t_wf_reify
theorem plain_bump_decay_wf : Func.Wf plain_bump_decay_body := by t_wf_reify
theorem plain_queue_mtf_wf : Func.Wf plain_queue_mtf_body := by t_wf_reify
theorem plain_tick_rel_wf : Func.Wf plain_tick_rel_body := by t_wf_reify
theorem plain_ema_update_wf : Func.Wf plain_ema_update_body := by t_wf_reify
theorem plain_assign_wf : Func.Wf plain_assign_body := by t_wf_reify
theorem plain_backtrack_wf : Func.Wf plain_backtrack_body := by t_wf_reify
theorem plain_add_clause_wf : Func.Wf plain_add_clause_body := by t_wf_reify
theorem plain_zero_tables_wf : Func.Wf plain_zero_tables_body := by t_wf_reify
theorem plain_init_state_wf : Func.Wf plain_init_state_body := by t_wf_reify
theorem plain_skip_cl_wf : Func.Wf plain_skip_cl_body := by t_wf_reify
theorem plain_ingest_cl_wf : Func.Wf plain_ingest_cl_body := by t_wf_reify
theorem plain_parse_body_wf : Func.Wf plain_parse_body_body := by t_wf_reify
theorem plain_find_repl_wf : Func.Wf plain_find_repl_body := by t_wf_reify
theorem plain_prop_lit_wf : Func.Wf plain_prop_lit_body := by t_wf_reify
theorem plain_propagate_wf : Func.Wf plain_propagate_body := by t_wf_reify
theorem plain_tiers_wf : Func.Wf plain_recompute_tiers_body := by t_wf_reify
theorem plain_mark_rsns_wf : Func.Wf plain_mark_reasons_body := by t_wf_reify
theorem plain_red_less_wf : Func.Wf plain_red_less_body := by t_wf_reify
theorem plain_sort_reds_wf : Func.Wf plain_sort_reds_body := by t_wf_reify

theorem plain1_fns_wf : ∀ f ∈ plain1_fns, f.Wf := by
  intro f hf
  simp only [plain1_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact plain_isqrt_wf
  · exact plain_ilog10_wf
  · exact plain_arena_next_wf
  · exact plain_alloc_cl_wf
  · exact plain_wstack_defrag_wf
  · exact plain_watch_push_wf
  · exact plain_heap_up_wf
  · exact plain_heap_down_wf
  · exact plain_heap_push_wf
  · exact plain_heap_pop_wf
  · exact plain_rescale_wf
  · exact plain_bump_var_wf
  · exact plain_bump_decay_wf
  · exact plain_queue_mtf_wf
  · exact plain_tick_rel_wf
  · exact plain_ema_update_wf
  · exact plain_assign_wf
  · exact plain_backtrack_wf
  · exact plain_add_clause_wf
  · exact plain_zero_tables_wf
  · exact plain_init_state_wf
  · exact plain_skip_cl_wf
  · exact plain_ingest_cl_wf
  · exact plain_parse_body_wf
  · exact plain_find_repl_wf
  · exact plain_prop_lit_wf
  · exact plain_propagate_wf
  · exact plain_tiers_wf
  · exact plain_mark_rsns_wf
  · exact plain_red_less_wf
  · exact plain_sort_reds_wf

theorem plain1_acyclic : plain1Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Plain
