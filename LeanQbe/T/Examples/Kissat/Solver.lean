module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Min` (`--basic --lucky=0`) CDCL SAT Solver in C0

Self-contained C0 port of Kissat `D-Min` (`reduce=0, minimize=0, shrink=0, restart=0, lucky=0`)
exposing `kissat_solve_bytes(cnf_ptr, cnf_len, work_ptr, work_len, fuel) -> 20 | 10 | 0`:

* `20`: UNSAT (validated DIMACS with empty clause, level-0 conflict, or empty 1UIP learned clause).
* `10`: SAT (only returned after mandatory `kissat_check_model` passes over `[cnf_ptr, cnf_end)`).
* `0`:  UNKNOWN (fuel exhausted, workspace `[work_ptr, work_ptr + work_len)` too small, or invalid
      DIMACS). Zero `.exit` calls (`exits = []`), zero UB, and `[cnf_ptr, cnf_end)` is read-only.

Implements literal encoding `2*(v-1)` / `2*(v-1)+1`, flat bounded arena layout, deduplication &
tautology elimination (`Core.pruneClause`), 2-watched literals with stale-watch guard & safe
unlink, 1UIP conflict analysis with bounds and trail-start guards, deterministic decision
selection, and mandatory SAT guard `kissat_check_model`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open LeanQbe.T
open LeanQbe.T.Frontend.C0

kissat_c0! solver "
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
} KissatHdr;

extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d);
extern u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d);
extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d,
                              i8 *vals, u64 mv_max);

void kissat_assign(KissatHdr *h, u32 lit, u32 rsn) {
  u32 v = lit >> 1;
  if ((u64)v >= h->d.mv || h->trail_end >= h->d.mv) {
    return;
  }
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  vals[lit] = (i8)1;
  vals[lit ^ 1u] = (i8)-1;
  lvl[v] = (u32)h->cur_level;
  rsns[v] = rsn;
  trl[h->trail_end] = lit;
  h->trail_end = h->trail_end + 1ULL;
}

void kissat_add_watch(KissatHdr *h, u32 w, u32 lit) {
  if ((u64)lit >= (h->d.mv << 1) || (u64)w >= (h->max_clauses << 1)) {
    return;
  }
  u32 *wh = (u32 *)h->watch_head;
  u32 *wn = (u32 *)h->watch_next;
  wn[w] = wh[lit];
  wh[lit] = w;
}

u64 kissat_add_clause(KissatHdr *h, u32 len) {
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

void kissat_backtrack(KissatHdr *h, u64 target_lvl) {
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
    te = te - 1ULL;
  }
  h->trail_end = te;
  if (h->propagated > te) {
    h->propagated = te;
  }
  h->cur_level = target_lvl;
}

void kissat_zero_tables(KissatHdr *h) {
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
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 v = 0ULL;
  while (v < mv) {
    mrk[v] = (u8)0;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    tmp[v] = 0u;
    v = v + 1ULL;
  }
}

bool kissat_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel) {
  KissatHdr *h = (KissatHdr *)hdr_addr;
  if (!kissat_parse_header(cnf_ptr, cnf_end, &h->d)) {
    return false;
  }
  u64 mv = h->d.mv;
  u64 nc = h->d.nc;
  u64 num_lits = mv << 1;
  u64 vals_bytes = (num_lits + 7ULL) & (~7ULL);
  u64 mark_bytes = (mv + 7ULL) & (~7ULL);
  u64 u32_var_bytes = ((mv << 2) + 7ULL) & (~7ULL);
  u64 wh_bytes = ((num_lits << 2) + 7ULL) & (~7ULL);
  u64 hdr_sz = (u64)sizeof(KissatHdr);
  u64 fixed = hdr_sz + vals_bytes + mark_bytes + (u32_var_bytes << 2) + wh_bytes;
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
  h->level = base;
  base = base + u32_var_bytes;
  h->reason = base;
  base = base + u32_var_bytes;
  h->trail = base;
  base = base + u32_var_bytes;
  h->tmp_lits = base;
  base = base + u32_var_bytes;
  h->watch_head = base;
  base = base + wh_bytes;
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

u64 kissat_ingest_clause(KissatHdr *h, u64 cnf_end) {
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

u64 kissat_parse_body(KissatHdr *h, u64 cnf_end) {
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

u64 kissat_propagate_lit(KissatHdr *h, u32 lit) {
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
      /* G1 + G2: drop stale or invalid watch safely */
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
      /* G2: safe unlink from not_lit and prepend to repl */
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

u64 kissat_propagate(KissatHdr *h) {
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

bool kissat_analyze_clause(KissatHdr *h, u32 cid, u32 skip_var) {
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
        /* Skip vlvl == 0 root-level literals so mrk[v] never leaks dirty. */
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

void kissat_clear_marks(KissatHdr *h, u64 trail_from) {
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

u64 kissat_analyze(KissatHdr *h, u64 confl_cid) {
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

u64 kissat_decide(KissatHdr *h) {
  i8 *vals = (i8 *)h->values;
  u64 mv = h->d.mv;
  u64 v = 0ULL;
  while (v < mv) {
    if (vals[v << 1] == (i8)0) {
      h->cur_level = h->cur_level + 1ULL;
      u32 lit = (u32)((v << 1) | 1ULL);
      kissat_assign(h, lit, 0xFFFFFFFFu);
      return 1ULL;
    }
    v = v + 1ULL;
  }
  return 0ULL;
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
  if (work_len < pad + (u64)sizeof(KissatHdr)) {
    return 0ULL;
  }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_len - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!kissat_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) {
    return 0ULL;
  }
  KissatHdr *h = (KissatHdr *)hdr_addr;
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
      u64 dst = kissat_decide(h);
      if (dst == 0ULL) {
        u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, h->d.mv);
        res = (ok == 1ULL) ? 10ULL : 0ULL;
        break;
      }
    }
  }
  return res;
}
"

/-- Combined callee-first function list (`Dimacs` + `Solver`). -/
def kissatFns : List Fn :=
  dimacs_fns ++ solver_fns

/-- Combined zero-exit acyclic `Module` for the Kissat `D-Min` C0 SAT solver. -/
def kissatModule : LeanQbe.T.Module :=
  { fns := kissatFns, externs := [], exits := [] }

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
theorem kissat_analyze_wf : Func.Wf kissat_analyze_body := by t_wf_reify
theorem kissat_decide_wf : Func.Wf kissat_decide_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

/-- All 17 solver functions in `solver_fns` satisfy `Fn.Wf`. -/
theorem solverFns_wf : ∀ f ∈ solver_fns, f.Wf := by
  intro f hf
  simp only [solver_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
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
  · exact kissat_analyze_wf
  · exact kissat_decide_wf
  · exact kissat_solve_bytes_wf

/-- Every function in `kissatFns` (`dimacs_fns ++ solver_fns`) satisfies `Fn.Wf`. -/
theorem kissatFns_wf : ∀ f ∈ kissatFns, f.Wf := by
  intro f hf
  simp only [kissatFns, List.mem_append] at hf
  rcases hf with hd | hs
  · exact dimacsFns_wf f hd
  · exact solverFns_wf f hs

/-- Combined acyclic module certificate (`kissatModule.checkAcyclic = true`). -/
theorem kissatModule_checkAcyclic : kissatModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat
