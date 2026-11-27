/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 DIMACS Clause Ingestion & Tumble Activation (`Src/Parse.lean`)

Mirrors upstream `kissat/src/parse.c` (`5` live functions, DAG level `L3`):
- `full_activate_lit_fid` (R4: `kissat_activate_literal`)
- `full_ingest_cl` (R4: `kissat_parse_clause`)
- `full_tumble_finish_fid` (R4: `kissat_tumble_finish`)
- `full_parse_body_m6` (R4: `kissat_parse_dimacs_body_impl`)
- `full_parse_body` (R4: `kissat_parse_dimacs_body`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Parse

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! parse "
#include \"kissat_internal.h\"

extern u64 f64u_sub(u64 a, u64 b);
extern u64 f64u_inv_u64(u64 k);
extern void full_heap_push(FullHdr *h, u32 v);
extern u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern bool full_skip_cl(u64 cnf_end, KissatDimacs *d);
extern u64 full_propagate(FullHdr *h);
extern u64 kissat_skip_ws_comments(u64 p, u64 end);
extern void full_wstack_defrag(FullHdr *h);

void full_activate_lit_fid(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *fl = (u32 *)h->flags;
  if ((fl[v] & FL_ACTIVE) != 0u) { return; }
  u32 all_c = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_FACT_P | FL_FACT_N |
              FL_BONE0 | FL_BONE1 | FL_TRANS | FL_SWEEP;
  fl[v] = fl[v] | all_c;
  h->unassigned = h->unassigned + 1ULL;
  u32 *gu = (u32 *)h->glue_used;
  u32 k = gu[TUM_GU_ACTIVATED];
  if (k < 0xFFFFFFFFu) { k = k + 1u; }
  gu[TUM_GU_ACTIVATED] = k;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 old_last = (u32)h->q_last;
  qp[v] = old_last;
  qn[v] = 0xFFFFFFFFu;
  h->q_last = (u64)v;
  if ((u64)old_last >= cv) {
    h->q_first = (u64)v;
  } else {
    qn[old_last] = v;
  }
  h->q_cur_stamp = h->q_cur_stamp + 1ULL;
  qs[v] = (u32)h->q_cur_stamp;
  h->q_search_idx = (u64)v;
  h->q_search_stamp = (u64)qs[v];
  u64 *sc = (u64 *)h->score;
  u64 k64 = (u64)k;
  sc[v] = f64u_sub(0x3FF0000000000000ULL, f64u_inv_u64(k64));
  if (h->stable != 0ULL) { full_heap_push(h, v); }
}

u64 full_ingest_cl(FullHdr *h, u64 cnf_end) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u8 *mrk = (u8 *)h->mark;
  i8 *vals = (i8 *)h->values;
  u32 *fd = (u32 *)h->frame_dec;
  bool tum = (h->extend_cap > h->d.mv);
  u32 tlen = 0u;
  bool taut = false;
  bool err = false;
  while (true) {
    u64 st = kissat_next_lit(cnf_end, &h->d);
    if (st == 0ULL) { err = true; break; }
    if (st == 1ULL) { break; }
    u32 lit = (u32)h->d.val;
    u32 ev = lit >> 1;
    if ((u64)ev >= h->d.mv) { err = true; break; }
    u32 v = ev;
    if (tum) {
      u32 iv = fd[ev];
      if (iv == 0xFFFFFFFFu) {
        u64 nxt = h->extend_len;
        if (nxt >= h->d.mv) { err = true; break; }
        iv = (u32)nxt;
        fd[ev] = iv;
        h->extend_len = nxt + 1ULL;
      }
      v = iv;
      lit = (iv << 1) | (lit & 1u);
    }
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
  u32 a = 0u;
  while (a < keep) {
    full_activate_lit_fid(h, tmp[a] >> 1);
    a = a + 1u;
  }
  if (keep == 0u) { return 2ULL; }
  if (keep == 1u) { full_assign_lvl(h, tmp[0], 0xFFFFFFFFu, 0u); return 1ULL; }
  u64 cid = full_add_clause(h, keep, 0u, false);
  if (cid == 0xFFFFFFFFULL) { return 3ULL; }
  return 1ULL;
}

void full_tumble_finish_fid(FullHdr *h) {
  if (h->extend_cap <= h->d.mv) { return; }
  u32 *fd = (u32 *)h->frame_dec;
  u32 *ext = (u32 *)h->extend_stk;
  u64 mv = h->d.mv;
  u64 e = 0ULL;
  while (e < mv) {
    u32 iv = fd[e];
    ext[e + 1ULL] = (iv == 0xFFFFFFFFu) ? EXT_UNMAPPED : iv;
    fd[e] = 0xFFFFFFFFu;
    e = e + 1ULL;
  }
  ext[0] = EXT_BLK_FLAG | EXT_PERM_FLAG | (u32)mv;
  h->extend_len = mv + 1ULL;
}

u64 full_parse_body_m6(FullHdr *h, u64 cnf_end) {
  u32 *gu = (u32 *)h->glue_used;
  gu[TUM_GU_ACTIVATED] = 0u;
  if (h->extend_cap > h->d.mv) {
    u32 *fd = (u32 *)h->frame_dec;
    u64 mv = h->d.mv;
    u64 e = 0ULL;
    while (e < mv) {
      fd[e] = 0xFFFFFFFFu;
      e = e + 1ULL;
    }
    h->extend_len = 0ULL;
  }
  bool unsat_seen = false;
  bool oom_seen = false;
  bool has_cl = false;
  u64 i = 0ULL;
  while (i < h->d.nc) {
    if (unsat_seen) {
      if (!full_skip_cl(cnf_end, &h->d)) { return 0ULL; }
    } else if (oom_seen) {
      return 0ULL;
    } else {
      u64 old_te = h->trail_end;
      u64 st = full_ingest_cl(h, cnf_end);
      if (st == 0ULL) { return 0ULL; }
      if (st == 2ULL) { unsat_seen = true; }
      else if (st == 3ULL) { oom_seen = true; }
      else {
        if (h->trail_end == old_te) { has_cl = true; }
        if (has_cl && h->propagated < h->trail_end) {
          u64 saved_fuel = h->fuel;
          u64 saved_ticks = h->search_ticks;
          u64 pr = full_propagate(h);
          h->fuel = saved_fuel;
          h->search_ticks = saved_ticks;
          if (pr == 1ULL) { unsat_seen = true; }
          else if (pr == 2ULL) { h->oom = 0ULL; oom_seen = true; }
        }
      }
    }
    i = i + 1ULL;
  }
  if (oom_seen) { return 0ULL; }
  h->d.cur = kissat_skip_ws_comments(h->d.cur, cnf_end);
  if (h->d.cur != cnf_end) { return 0ULL; }
  full_tumble_finish_fid(h);
  if (unsat_seen) { return 20ULL; }
  full_wstack_defrag(h);
  return 1ULL;
}

u64 full_parse_body(FullHdr *h, u64 cnf_end) {
  return full_parse_body_m6(h, cnf_end);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Parse
