module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Core+` CDCL SAT Solver in C0 (`Stage 2`)

Self-contained C0 extension of `X1` (`Solver.lean`) in `LeanQbe.T.Examples.Kissat.CorePlus`,
exposing `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_len, fuel) -> 20 | 10 | 0`:

* `20`: UNSAT (validated DIMACS with empty clause, level-0 conflict, or empty 1UIP learned clause).
* `10`: SAT (only returned after mandatory `kissat_check_model` passes over `[cnf_ptr, cnf_end)`).
* `0`:  UNKNOWN (fuel exhausted, workspace too small, or invalid DIMACS).

Adds Kissat Stage-2 search heuristics and iterative minimization over the `X1` arena layout:
1. Iterative recursive clause minimization (`kissat_minimize_lit` / `kissat_minimize_clause`) with
   `SEEN` (bit 0), `REMOVABLE` (bit 1), `POISONED` (bit 2) flags in `mrk[]`, explicit DFS stack
   `min_stk` (`min_depth <= 1000`), and `min_clr` tracking for O(clr_len) mark reset.
2. Pure-`u64` fixed-point EVSIDS binary max-heap (`heap[]`, `pos[]`, `score[]`) with monotonic
   shift rescaling (`>> 28ULL`) and deterministic scan fallback in `kissat_decide`.
3. Phase saving (`phases[]`) and Luby/reluctant doubling restarts (`rel_*`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! coreplus "
typedef struct {
  u64 mv;
  u64 nc;
  u64 cur;
  u64 val;
} KissatDimacs;

typedef struct {
  u32 off;
  u32 size;
  u32 searched;
  u32 pad;
} KissatClause;

typedef struct {
  KissatDimacs d;
  u64 max_clauses;
  u64 lit_cap;
  u64 lit_len;
  u64 num_clauses;
  u64 values;
  u64 mark;
  u64 level;
  u64 reason;
  u64 trail;
  u64 watch_head;
  u64 clauses;
  u64 watch_next;
  u64 lit_pool;
  u64 tmp_lits;
  u64 trail_end;
  u64 propagated;
  u64 cur_level;
  u64 fuel;
  u64 confl_cid;
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
} CorePlusHdr;

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d);
extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d,
                              i8 *vals, u64 mv_max);

void kissat_heap_sift_up(CorePlusHdr *h, u32 v) {
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

void kissat_heap_sift_down(CorePlusHdr *h, u32 v) {
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

void kissat_heap_push(CorePlusHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  if (ps[v] != 0xFFFFFFFFu || h->heap_len >= h->d.mv) { return; }
  u32 idx = (u32)h->heap_len;
  h->heap_len = h->heap_len + 1ULL;
  hp[idx] = v;
  ps[v] = idx;
  kissat_heap_sift_up(h, v);
}

u64 kissat_heap_pop_max(CorePlusHdr *h) {
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
    kissat_heap_sift_down(h, last);
  }
  if ((u64)top >= h->d.mv) { return 0xFFFFFFFFULL; }
  return (u64)top;
}

void kissat_rescale_scores(CorePlusHdr *h) {
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

void kissat_bump_var(CorePlusHdr *h, u32 v) {
  if ((u64)v >= h->d.mv) { return; }
  u64 *sc = (u64 *)h->score;
  u64 cur = sc[v];
  u64 inc = h->scinc;
  u64 nsc = (cur > (1ULL << 61) || inc > (1ULL << 61)) ? (1ULL << 60) : (cur + inc);
  sc[v] = nsc;
  kissat_heap_sift_up(h, v);
  if (nsc >= (1ULL << 60)) { kissat_rescale_scores(h); }
}

void kissat_bump_decay(CorePlusHdr *h) {
  u64 inc = h->scinc;
  if (inc < (1ULL << 20)) { inc = 1ULL << 20; }
  if (inc >= (1ULL << 56)) {
    kissat_rescale_scores(h);
    inc = h->scinc;
  }
  u64 ninc = (inc * 20ULL) / 19ULL;
  h->scinc = ninc;
  if (ninc >= (1ULL << 56)) { kissat_rescale_scores(h); }
}

void kissat_tick_reluctant(CorePlusHdr *h) {
  if (h->rel_period == 0ULL || h->rel_trigger != 0ULL) { return; }
  if (h->rel_wait > 0ULL) { h->rel_wait = h->rel_wait - 1ULL; }
  if (h->rel_wait > 0ULL) { return; }
  u64 u = h->rel_u;
  u64 v = h->rel_v;
  if (u == 0ULL || v == 0ULL) {
    u = 1ULL;
    v = 1ULL;
  }
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

void kissat_assign(CorePlusHdr *h, u32 lit, u32 rsn) {
  u32 v = lit >> 1;
  if ((u64)v >= h->d.mv || h->trail_end >= h->d.mv) {
    return;
  }
  i8 *vals = (i8 *)h->values;
  i8 *ph = (i8 *)h->phases;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  vals[lit] = (i8)1;
  vals[lit ^ 1u] = (i8)-1;
  ph[v] = ((lit & 1u) != 0u) ? (i8)(-1) : (i8)1;
  lvl[v] = (u32)h->cur_level;
  rsns[v] = rsn;
  trl[h->trail_end] = lit;
  h->trail_end = h->trail_end + 1ULL;
}

void kissat_add_watch(CorePlusHdr *h, u32 w, u32 lit) {
  if ((u64)lit >= (h->d.mv << 1) || (u64)w >= (h->max_clauses << 1)) {
    return;
  }
  u32 *wh = (u32 *)h->watch_head;
  u32 *wn = (u32 *)h->watch_next;
  wn[w] = wh[lit];
  wh[lit] = w;
}

u64 kissat_add_clause(CorePlusHdr *h, u32 len) {
  if (h->num_clauses >= h->max_clauses || (u64)len > h->lit_cap - h->lit_len) {
    return 0xFFFFFFFFULL;
  }
  u32 cid = (u32)h->num_clauses;
  h->num_clauses = h->num_clauses + 1ULL;
  u32 off = (u32)h->lit_len;
  h->lit_len = h->lit_len + (u64)len;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lpool = (u32 *)h->lit_pool;
  u32 i = 0u;
  while (i < len) {
    lpool[(u64)off + (u64)i] = tmp[i];
    i = i + 1u;
  }
  KissatClause *cls = (KissatClause *)h->clauses;
  cls[cid].off = off;
  cls[cid].size = len;
  cls[cid].searched = 2u;
  cls[cid].pad = 0u;
  if (len >= 2u) {
    kissat_add_watch(h, cid << 1, tmp[0]);
    kissat_add_watch(h, (cid << 1) | 1u, tmp[1]);
  }
  return (u64)cid;
}

void kissat_backtrack(CorePlusHdr *h, u64 target_lvl) {
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u64 te = h->trail_end;
  while (te > 0ULL) {
    u32 lit = trl[te - 1ULL];
    u32 v = lit >> 1;
    if ((u64)lvl[v] <= target_lvl) {
      break;
    }
    vals[lit] = (i8)0;
    vals[lit ^ 1u] = (i8)0;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    kissat_heap_push(h, v);
    te = te - 1ULL;
  }
  h->trail_end = te;
  if (h->propagated > te) {
    h->propagated = te;
  }
  h->cur_level = target_lvl;
}

void kissat_zero_tables(CorePlusHdr *h) {
  u64 mv = h->d.mv;
  u64 num_lits = mv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *wh = (u32 *)h->watch_head;
  u64 i = 0ULL;
  while (i < num_lits) {
    vals[i] = (i8)0;
    wh[i] = 0xFFFFFFFFu;
    i = i + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  i8 *ph = (i8 *)h->phases;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *mclr = (u32 *)h->min_clr;
  u64 *sc = (u64 *)h->score;
  u64 v = 0ULL;
  while (v < mv) {
    mrk[v] = (u8)0;
    ph[v] = (i8)1;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    tmp[v] = 0u;
    hp[v] = (u32)v;
    ps[v] = (u32)v;
    mclr[v] = 0u;
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
}

bool kissat_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  CorePlusHdr *h = (CorePlusHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) {
    return false;
  }
  u64 mv = h->d.mv;
  u64 nc = h->d.nc;
  u64 num_lits = mv << 1;
  u64 vals_bytes = (num_lits + 7ULL) & (~7ULL);
  u64 mark_bytes = (mv + 7ULL) & (~7ULL);
  u64 u32_var_bytes = ((mv << 2) + 7ULL) & (~7ULL);
  u64 u64_var_bytes = mv << 3;
  u64 wh_bytes = ((num_lits << 2) + 7ULL) & (~7ULL);
  u64 mdepth = (mv + 1ULL < 1000ULL) ? (mv + 1ULL) : 1000ULL;
  u64 mstk_bytes = mdepth << 3;
  u64 hdr_sz = (u64)sizeof(CorePlusHdr);
  u64 fixed = hdr_sz + vals_bytes + (mark_bytes << 1) + (u32_var_bytes * 7ULL) +
              u64_var_bytes + wh_bytes + mstk_bytes;
  if (avail < fixed) {
    return false;
  }
  u64 rem = avail - fixed;
  u64 min_cls = nc * 24ULL;
  if (rem < min_cls) {
    return false;
  }
  u64 extra = (rem - min_cls) >> 6;
  u64 max_c = nc + extra;
  if (max_c > 268435455ULL) {
    max_c = 268435455ULL;
  }
  u64 cls_bytes = max_c * 24ULL;
  u64 lcap = (rem - cls_bytes) >> 2;
  if (lcap > 268435455ULL) {
    lcap = 268435455ULL;
  }
  u64 base = hdr_addr + hdr_sz;
  h->values = base;
  base = base + vals_bytes;
  h->mark = base;
  base = base + mark_bytes;
  h->phases = base;
  base = base + mark_bytes;
  h->level = base;
  base = base + u32_var_bytes;
  h->reason = base;
  base = base + u32_var_bytes;
  h->trail = base;
  base = base + u32_var_bytes;
  h->tmp_lits = base;
  base = base + u32_var_bytes;
  h->heap = base;
  base = base + u32_var_bytes;
  h->pos = base;
  base = base + u32_var_bytes;
  h->min_clr = base;
  base = base + u32_var_bytes;
  h->score = base;
  base = base + u64_var_bytes;
  h->watch_head = base;
  base = base + wh_bytes;
  h->min_stk = base;
  base = base + mstk_bytes;
  h->clauses = base;
  h->watch_next = base + (max_c << 4);
  h->lit_pool = base + cls_bytes;
  h->max_clauses = max_c;
  h->lit_cap = lcap;
  h->lit_len = 0ULL;
  h->num_clauses = 0ULL;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->fuel = fuel;
  h->confl_cid = 0xFFFFFFFFULL;
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
  kissat_zero_tables(h);
  return true;
}

bool kissat_skip_clause_syntax(u64 cnf_end, KissatDimacs *d) {
  while (true) {
    u64 st = kissat_next_lit(cnf_end, d);
    if (st == 0ULL) {
      return false;
    }
    if (st == 1ULL) {
      return true;
    }
  }
}

u64 kissat_ingest_clause(CorePlusHdr *h, u64 cnf_end) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u8 *mrk = (u8 *)h->mark;
  i8 *vals = (i8 *)h->values;
  u32 tlen = 0u;
  bool taut = false;
  bool err = false;
  while (true) {
    u64 st = kissat_next_lit(cnf_end, &h->d);
    if (st == 0ULL) {
      err = true;
      break;
    }
    if (st == 1ULL) {
      break;
    }
    u32 lit = (u32)h->d.val;
    u32 v = lit >> 1;
    if ((u64)v >= h->d.mv) {
      err = true;
      break;
    }
    u8 ptag = (u8)((lit & 1u) + 1u);
    u8 m = mrk[v];
    if (m == (u8)0) {
      if ((u64)tlen >= h->d.mv) {
        err = true;
        break;
      }
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
    if ((u64)kv < h->d.mv) {
      mrk[kv] = (u8)0;
    }
    k = k + 1u;
  }
  if (err) {
    return 0ULL;
  }
  if (taut) {
    return 1ULL;
  }
  u32 keep = 0u;
  u32 i = 0u;
  while (i < tlen) {
    u32 l = tmp[i];
    i8 lv = vals[l];
    if (lv > (i8)0) {
      return 1ULL;
    }
    if (lv == (i8)0) {
      tmp[keep] = l;
      keep = keep + 1u;
    }
    i = i + 1u;
  }
  if (keep == 0u) {
    return 2ULL;
  }
  if (keep == 1u) {
    kissat_assign(h, tmp[0], 0xFFFFFFFFu);
    return 1ULL;
  }
  u64 cid = kissat_add_clause(h, keep);
  if (cid == 0xFFFFFFFFULL) {
    return 3ULL;
  }
  return 1ULL;
}

u64 kissat_parse_body(CorePlusHdr *h, u64 cnf_end) {
  bool unsat_seen = false;
  bool oom_seen = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!kissat_skip_clause_syntax(cnf_end, &h->d)) {
        return 0ULL;
      }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 st = kissat_ingest_clause(h, cnf_end);
      if (st == 0ULL) {
        return 0ULL;
      }
      if (st == 2ULL) {
        unsat_seen = true;
      } else if (st == 3ULL) {
        oom_seen = true;
      }
    }
    i = i + 1ULL;
  }
  if (oom_seen) {
    return 0ULL;
  }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) {
    return 0ULL;
  }
  if (unsat_seen) {
    return 20ULL;
  }
  return 1ULL;
}

u32 kissat_find_repl(i8 *vals, u32 *lits, u32 sz, u32 srch, u64 n_lits) {
  u32 r = srch;
  while (r < sz) {
    u32 cand = lits[r];
    if ((u64)cand < n_lits && vals[cand] >= (i8)0) {
      return r;
    }
    r = r + 1u;
  }
  r = 2u;
  while (r < srch) {
    u32 cand = lits[r];
    if ((u64)cand < n_lits && vals[cand] >= (i8)0) {
      return r;
    }
    r = r + 1u;
  }
  return 0xFFFFFFFFu;
}

u64 kissat_propagate_lit(CorePlusHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u;
  u64 n_lits = h->d.mv << 1;
  if ((u64)not_lit >= n_lits) {
    return 0xFFFFFFFFULL;
  }
  u32 *wh = (u32 *)h->watch_head;
  u32 *wn = (u32 *)h->watch_next;
  KissatClause *cls = (KissatClause *)h->clauses;
  u32 *lpool = (u32 *)h->lit_pool;
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) {
    return 0xFFFFFFFFULL;
  }
  u32 prev = 0xFFFFFFFFu;
  u32 w = wh[not_lit];
  u64 steps = 0ULL;
  u64 max_steps = (h->num_clauses << 1) + 1ULL;
  while (w != 0xFFFFFFFFu && steps < max_steps) {
    steps = steps + 1ULL;
    u32 cid = w >> 1;
    u32 slot = w & 1u;
    if ((u64)cid >= h->num_clauses) {
      break;
    }
    u32 next_w = wn[w];
    KissatClause *c = cls + cid;
    u32 sz = c->size;
    u32 off = c->off;
    bool bad_cl = sz < 2u || (u64)off > h->lit_len || (u64)sz > h->lit_len - (u64)off;
    u32 *lits = lpool + off;
    if (bad_cl || (lits[0] != not_lit && lits[1] != not_lit) || lits[slot] != not_lit) {
      if (prev == 0xFFFFFFFFu) {
        wh[not_lit] = next_w;
      } else {
        wn[prev] = next_w;
      }
      wn[w] = 0xFFFFFFFFu;
      w = next_w;
      continue;
    }
    u32 other = lits[slot ^ 1u];
    if ((u64)other >= n_lits) {
      break;
    }
    i8 oval = vals[other];
    if (oval > (i8)0) {
      prev = w;
      w = next_w;
      continue;
    }
    u32 srch = c->searched;
    if (srch < 2u || srch > sz) {
      srch = 2u;
    }
    u32 r = kissat_find_repl(vals, lits, sz, srch, n_lits);
    if (r != 0xFFFFFFFFu) {
      u32 repl = lits[r];
      c->searched = r;
      lits[slot] = repl;
      lits[r] = not_lit;
      if (prev == 0xFFFFFFFFu) {
        wh[not_lit] = next_w;
      } else {
        wn[prev] = next_w;
      }
      wn[w] = wh[repl];
      wh[repl] = w;
      w = next_w;
      continue;
    }
    if (oval < (i8)0) {
      return (u64)cid;
    }
    kissat_assign(h, other, cid);
    prev = w;
    w = next_w;
  }
  return 0xFFFFFFFFULL;
}

u64 kissat_propagate(CorePlusHdr *h) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end) {
    if (h->fuel == 0ULL) {
      return 2ULL;
    }
    h->fuel = h->fuel - 1ULL;
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    u64 confl = kissat_propagate_lit(h, lit);
    if (confl != 0xFFFFFFFFULL) {
      h->confl_cid = confl;
      return 1ULL;
    }
  }
  return 0ULL;
}

bool kissat_analyze_clause(CorePlusHdr *h, u32 cid, u32 skip_var) {
  if ((u64)cid >= h->num_clauses) {
    return false;
  }
  KissatClause *cls = (KissatClause *)h->clauses;
  KissatClause *c = cls + cid;
  u64 off = (u64)c->off;
  u64 sz = (u64)c->size;
  if (off > h->lit_len || sz > h->lit_len - off) {
    return false;
  }
  u32 *lpool = (u32 *)h->lit_pool;
  u32 *lits = lpool + off;
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 cur_lvl = (u32)h->cur_level;
  u64 i = 0ULL;
  while (i < sz) {
    u32 l = lits[i];
    u32 v = l >> 1;
    if ((u64)v >= h->d.mv) {
      return false;
    }
    if (v != skip_var && mrk[v] == (u8)0) {
      u32 vlvl = lvl[v];
      if (vlvl > cur_lvl) {
        return false;
      } else if (vlvl > 0u) {
        if (vlvl == cur_lvl) {
          mrk[v] = (u8)1;
          h->tmp_cnt = h->tmp_cnt + 1ULL;
        } else {
          if (h->tmp_len >= h->d.mv) {
            return false;
          }
          mrk[v] = (u8)1;
          tmp[h->tmp_len] = l;
          h->tmp_len = h->tmp_len + 1ULL;
        }
      }
    }
    i = i + 1ULL;
  }
  return true;
}

void kissat_clear_marks(CorePlusHdr *h, u64 trail_from) {
  u8 *mrk = (u8 *)h->mark;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *trl = (u32 *)h->trail;
  u64 mv = h->d.mv;
  u64 i = 1ULL;
  while (i < h->tmp_len) {
    u32 v = tmp[i] >> 1;
    if ((u64)v < mv) {
      mrk[v] = (u8)0;
    }
    i = i + 1ULL;
  }
  u64 j = trail_from;
  while (j < h->trail_end) {
    u32 tv = trl[j] >> 1;
    if ((u64)tv < mv) {
      mrk[tv] = (u8)0;
    }
    j = j + 1ULL;
  }
}

void kissat_min_mark(CorePlusHdr *h, u32 v, u8 tag) {
  u64 mv = h->d.mv;
  if ((u64)v >= mv) { return; }
  u8 *mrk = (u8 *)h->mark;
  if (mrk[v] != (u8)0) { return; }
  mrk[v] = tag;
  if (h->min_clr_len < mv) {
    u32 *mclr = (u32 *)h->min_clr;
    mclr[h->min_clr_len] = v;
    h->min_clr_len = h->min_clr_len + 1ULL;
  } else {
    h->min_clr_full = 1ULL;
  }
}

bool kissat_minimize_lit(CorePlusHdr *h, u32 root_lit) {
  u64 mv = h->d.mv;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= mv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  u32 r0 = rsns[root_v];
  if (r0 == 0xFFFFFFFFu || (u64)r0 >= h->num_clauses) { return false; }
  KissatClause *cls = (KissatClause *)h->clauses;
  KissatClause *c0 = cls + r0;
  u64 off0 = (u64)c0->off;
  u64 sz0 = (u64)c0->size;
  if (off0 > h->lit_len || sz0 > h->lit_len - off0) { return false; }
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *lpool = (u32 *)h->lit_pool;
  u32 *stk = (u32 *)h->min_stk;
  stk[0] = root_v;
  stk[1] = 0u;
  u64 sp = 0ULL;
  bool ok = false;
  u64 steps = 0ULL;
  u64 max_steps = (h->lit_len + mv) * 4ULL + 64ULL;
  while (steps < max_steps) {
    steps = steps + 1ULL;
    u32 v = stk[sp << 1];
    u32 pos = stk[(sp << 1) + 1ULL];
    if ((u64)v >= mv) { break; }
    u32 rcid = rsns[v];
    if (rcid == 0xFFFFFFFFu || (u64)rcid >= h->num_clauses) { break; }
    KissatClause *c = cls + rcid;
    u64 off = (u64)c->off;
    u64 sz = (u64)c->size;
    if (off > h->lit_len || sz > h->lit_len - off) { break; }
    if ((u64)pos < sz) {
      stk[(sp << 1) + 1ULL] = pos + 1u;
      u32 l = lpool[off + (u64)pos];
      u32 u = l >> 1;
      if ((u64)u >= mv) { break; }
      if (u == v || lvl[u] == 0u) { continue; }
      u8 mu = mrk[u];
      if ((mu & (u8)2) != (u8)0) { continue; }
      if ((mu & (u8)4) != (u8)0) { break; }
      u32 ur = rsns[u];
      if (ur == 0xFFFFFFFFu || (u64)ur >= h->num_clauses) {
        kissat_min_mark(h, u, (u8)4);
        break;
      }
      KissatClause *uc = cls + ur;
      u64 uoff = (u64)uc->off;
      u64 usz = (u64)uc->size;
      if (uoff > h->lit_len || usz > h->lit_len - uoff || sp + 1ULL >= h->min_depth) { break; }
      sp = sp + 1ULL;
      stk[sp << 1] = u;
      stk[(sp << 1) + 1ULL] = 0u;
      continue;
    }
    if (sp == 0ULL) { ok = true; break; }
    kissat_min_mark(h, v, (u8)2);
    sp = sp - 1ULL;
  }
  if (!ok) {
    u64 j = 1ULL;
    while (j <= sp) {
      kissat_min_mark(h, stk[j << 1], (u8)4);
      j = j + 1ULL;
    }
    return false;
  }
  return true;
}

void kissat_minimize_clause(CorePlusHdr *h) {
  u64 mv = h->d.mv;
  u64 tlen = h->tmp_len;
  h->conflicts = h->conflicts + 1ULL;
  if (tlen <= 1ULL || tlen > mv) {
    h->learned_lits = h->learned_lits + tlen;
    return;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  h->min_clr_len = 0ULL;
  h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < tlen) {
    kissat_min_mark(h, tmp[i] >> 1, (u8)2);
    i = i + 1ULL;
  }
  u64 keep = 1ULL;
  u64 k = 1ULL;
  while (k < tlen) {
    u32 lit = tmp[k];
    if (!kissat_minimize_lit(h, lit)) {
      tmp[keep] = lit;
      keep = keep + 1ULL;
    }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL;
    while (v < mv) {
      mrk[v] = (u8)0;
      v = v + 1ULL;
    }
  } else {
    u32 *mclr = (u32 *)h->min_clr;
    u64 clen = h->min_clr_len;
    u64 z = 0ULL;
    while (z < clen) {
      u32 cv = mclr[z];
      if ((u64)cv < mv) {
        mrk[cv] = (u8)0;
      }
      z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL;
  h->min_clr_full = 0ULL;
  h->tmp_len = keep;
  h->min_removed = h->min_removed + (tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

u64 kissat_analyze(CorePlusHdr *h, u64 confl_cid) {
  if (h->cur_level == 0ULL) {
    return 20ULL;
  }
  h->tmp_cnt = 0ULL;
  h->tmp_len = 1ULL;
  if (!kissat_analyze_clause(h, (u32)confl_cid, 0xFFFFFFFFu)) {
    kissat_clear_marks(h, 0ULL);
    return 0ULL;
  }
  if (h->tmp_cnt == 0ULL) {
    kissat_clear_marks(h, 0ULL);
    if (h->tmp_len == 1ULL) {
      return 20ULL;
    }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  i8 *vals = (i8 *)h->values;
  u32 cur_lvl = (u32)h->cur_level;
  u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu;
  while (h->tmp_cnt > 0ULL) {
    if (idx == 0ULL) {
      kissat_clear_marks(h, 0ULL);
      return 0ULL;
    }
    idx = idx - 1ULL;
    u32 p = trl[idx];
    u32 pv = p >> 1;
    if ((u64)pv >= h->d.mv) {
      kissat_clear_marks(h, 0ULL);
      return 0ULL;
    }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      kissat_bump_var(h, pv);
      h->tmp_cnt = h->tmp_cnt - 1ULL;
      if (h->tmp_cnt == 0ULL) {
        uip_lit = p ^ 1u;
        break;
      }
      u32 rcid = rsns[pv];
      if (rcid == 0xFFFFFFFFu || !kissat_analyze_clause(h, rcid, pv)) {
        kissat_clear_marks(h, 0ULL);
        return 0ULL;
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) {
    kissat_clear_marks(h, 0ULL);
    return 0ULL;
  }
  tmp[0] = uip_lit;
  kissat_clear_marks(h, idx);
  u64 bi = 1ULL;
  while (bi < h->tmp_len) {
    kissat_bump_var(h, tmp[bi] >> 1);
    bi = bi + 1ULL;
  }
  kissat_bump_decay(h);
  kissat_minimize_clause(h);
  kissat_tick_reluctant(h);
  if (h->tmp_len == 1ULL) {
    kissat_backtrack(h, 0ULL);
    if (vals[uip_lit] != (i8)0) {
      return 0ULL;
    }
    kissat_assign(h, uip_lit, 0xFFFFFFFFu);
    return 1ULL;
  }
  u64 max_idx = 1ULL;
  u64 max_lvl = (u64)lvl[tmp[1] >> 1];
  u64 k = 2ULL;
  while (k < h->tmp_len) {
    u64 klvl = (u64)lvl[tmp[k] >> 1];
    if (klvl > max_lvl) {
      max_lvl = klvl;
      max_idx = k;
    }
    k = k + 1ULL;
  }
  if (max_lvl >= (u64)cur_lvl) {
    max_lvl = (u64)cur_lvl - 1ULL;
  }
  u32 w1 = tmp[1];
  tmp[1] = tmp[max_idx];
  tmp[max_idx] = w1;
  kissat_backtrack(h, max_lvl);
  u64 new_cid = kissat_add_clause(h, (u32)h->tmp_len);
  if (new_cid == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) {
    return 0ULL;
  }
  kissat_assign(h, uip_lit, (u32)new_cid);
  return 1ULL;
}

u64 kissat_decide(CorePlusHdr *h) {
  i8 *vals = (i8 *)h->values;
  i8 *ph = (i8 *)h->phases;
  u32 *hp = (u32 *)h->heap;
  u64 mv = h->d.mv;
  u64 chosen = 0xFFFFFFFFFFFFFFFFULL;
  while (h->heap_len > 0ULL && h->heap_len <= mv) {
    u32 top = hp[0];
    if ((u64)top >= mv) {
      break;
    }
    if (vals[(u64)top << 1] == (i8)0) {
      chosen = (u64)top;
      break;
    }
    kissat_heap_pop_max(h);
  }
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) {
    u64 v = 0ULL;
    while (v < mv) {
      if (vals[v << 1] == (i8)0) {
        chosen = v;
        break;
      }
      v = v + 1ULL;
    }
  }
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) {
    return 0ULL;
  }
  h->cur_level = h->cur_level + 1ULL;
  u32 lit = (ph[chosen] < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  kissat_assign(h, lit, 0xFFFFFFFFu);
  return 1ULL;
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_len, u64 fuel) {
  if (fuel == 0ULL) {
    return 0ULL;
  }
  if (cnf_len > (~0ULL) - cnf_ptr || work_len > (~0ULL) - work_ptr) {
    return 0ULL;
  }
  u64 mis = work_ptr & 7ULL;
  u64 pad = (mis == 0ULL) ? 0ULL : (8ULL - mis);
  if (work_len < pad + (u64)sizeof(CorePlusHdr)) {
    return 0ULL;
  }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_len - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!kissat_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) {
    return 0ULL;
  }
  CorePlusHdr *h = (CorePlusHdr *)hdr_addr;
  u64 pst = kissat_parse_body(h, cnf_end);
  if (pst == 0ULL) {
    return 0ULL;
  }
  if (pst == 20ULL) {
    return 20ULL;
  }
  u64 res = 0ULL;
  while (true) {
    u64 pr = kissat_propagate(h);
    if (pr == 2ULL) {
      res = 0ULL;
      break;
    }
    if (pr == 1ULL) {
      if (h->cur_level == 0ULL) {
        res = 20ULL;
        break;
      }
      u64 ast = kissat_analyze(h, h->confl_cid);
      if (ast == 20ULL) {
        res = 20ULL;
        break;
      }
      if (ast != 1ULL) {
        res = 0ULL;
        break;
      }
    } else {
      if (h->fuel == 0ULL) {
        res = 0ULL;
        break;
      }
      h->fuel = h->fuel - 1ULL;
      if (h->trail_end < h->d.mv && h->cur_level > 0ULL && h->rel_trigger != 0ULL) {
        h->rel_trigger = 0ULL;
        kissat_backtrack(h, 0ULL);
      } else {
        u64 dst = kissat_decide(h);
        if (dst == 0ULL) {
          u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, h->d.mv);
          res = (ok == 1ULL) ? 10ULL : 0ULL;
          break;
        }
      }
    }
  }
  return res;
}
"

/-- Combined callee-first function list (`Dimacs` + `CorePlus`). -/
def coreplusFns : List Fn :=
  dimacs_fns ++ coreplus_fns

/-- Combined zero-exit acyclic `Module` for the Kissat `D-Core+` C0 SAT solver. -/
def coreplusModule : LeanQbe.T.Module :=
  { fns := coreplusFns, externs := [], exits := [] }

theorem kissat_heap_sift_up_wf : Func.Wf kissat_heap_sift_up_body := by t_wf_reify
theorem kissat_heap_sift_down_wf : Func.Wf kissat_heap_sift_down_body := by t_wf_reify
theorem kissat_heap_push_wf : Func.Wf kissat_heap_push_body := by t_wf_reify
theorem kissat_heap_pop_max_wf : Func.Wf kissat_heap_pop_max_body := by t_wf_reify
theorem kissat_rescale_scores_wf : Func.Wf kissat_rescale_scores_body := by t_wf_reify
theorem kissat_bump_var_wf : Func.Wf kissat_bump_var_body := by t_wf_reify
theorem kissat_bump_decay_wf : Func.Wf kissat_bump_decay_body := by t_wf_reify
theorem kissat_tick_reluctant_wf : Func.Wf kissat_tick_reluctant_body := by t_wf_reify
theorem kissat_assign_wf : Func.Wf kissat_assign_body := by t_wf_reify
theorem kissat_add_watch_wf : Func.Wf kissat_add_watch_body := by t_wf_reify
theorem kissat_add_clause_wf : Func.Wf kissat_add_clause_body := by t_wf_reify
theorem kissat_backtrack_wf : Func.Wf kissat_backtrack_body := by t_wf_reify
theorem kissat_zero_tables_wf : Func.Wf kissat_zero_tables_body := by t_wf_reify
theorem kissat_init_state_wf : Func.Wf kissat_init_state_body := by t_wf_reify
theorem kissat_skip_clause_syntax_wf : Func.Wf kissat_skip_clause_syntax_body := by t_wf_reify
theorem kissat_ingest_clause_wf : Func.Wf kissat_ingest_clause_body := by t_wf_reify
theorem kissat_parse_body_wf : Func.Wf kissat_parse_body_body := by t_wf_reify
theorem kissat_find_repl_wf : Func.Wf kissat_find_repl_body := by t_wf_reify
theorem kissat_propagate_lit_wf : Func.Wf kissat_propagate_lit_body := by t_wf_reify
theorem kissat_propagate_wf : Func.Wf kissat_propagate_body := by t_wf_reify
theorem kissat_analyze_clause_wf : Func.Wf kissat_analyze_clause_body := by t_wf_reify
theorem kissat_clear_marks_wf : Func.Wf kissat_clear_marks_body := by t_wf_reify
theorem kissat_min_mark_wf : Func.Wf kissat_min_mark_body := by t_wf_reify
theorem kissat_minimize_lit_wf : Func.Wf kissat_minimize_lit_body := by t_wf_reify
theorem kissat_minimize_clause_wf : Func.Wf kissat_minimize_clause_body := by t_wf_reify
theorem kissat_analyze_wf : Func.Wf kissat_analyze_body := by t_wf_reify
theorem kissat_decide_wf : Func.Wf kissat_decide_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

/-- All 28 solver functions in `coreplus_fns` satisfy `Fn.Wf`. -/
theorem coreplus_fns_wf : ∀ f ∈ coreplus_fns, f.Wf := by
  intro f hf
  simp only [coreplus_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact kissat_heap_sift_up_wf
  · exact kissat_heap_sift_down_wf
  · exact kissat_heap_push_wf
  · exact kissat_heap_pop_max_wf
  · exact kissat_rescale_scores_wf
  · exact kissat_bump_var_wf
  · exact kissat_bump_decay_wf
  · exact kissat_tick_reluctant_wf
  · exact kissat_assign_wf
  · exact kissat_add_watch_wf
  · exact kissat_add_clause_wf
  · exact kissat_backtrack_wf
  · exact kissat_zero_tables_wf
  · exact kissat_init_state_wf
  · exact kissat_skip_clause_syntax_wf
  · exact kissat_ingest_clause_wf
  · exact kissat_parse_body_wf
  · exact kissat_find_repl_wf
  · exact kissat_propagate_lit_wf
  · exact kissat_propagate_wf
  · exact kissat_analyze_clause_wf
  · exact kissat_clear_marks_wf
  · exact kissat_min_mark_wf
  · exact kissat_minimize_lit_wf
  · exact kissat_minimize_clause_wf
  · exact kissat_analyze_wf
  · exact kissat_decide_wf
  · exact kissat_solve_bytes_wf

/-- Every function in `coreplusFns` (`dimacs_fns ++ coreplus_fns`) satisfies `Fn.Wf`. -/
theorem coreplusFns_wf : ∀ f ∈ coreplusFns, f.Wf := by
  intro f hf
  simp only [coreplusFns, List.mem_append] at hf
  rcases hf with hd | hs
  · exact dimacsFns_wf f hd
  · exact coreplus_fns_wf f hs

/-- Combined acyclic module certificate (`coreplusModule.checkAcyclic = true`). -/
theorem coreplus_acyclic : coreplusModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.CorePlus
