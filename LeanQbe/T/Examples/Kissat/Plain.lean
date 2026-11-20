module

public import LeanQbe.T.Examples.Kissat.Plain1

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Plain` (`--plain`) C0 Solver — Part 2 (`Plain2` + `kissat_solve_bytes`)

Implements propagation with blocking-literal large watches + inline binary watches,
reason marking & tier-aware `reduce` / `collect` compaction GC, VSIDS/VMTF dual-mode
search (`stable` vs `focused`), `best`/`target`/`saved` rephasing, reluctant Luby &
Q24-EMA restarts, `lucky` pre-search probing, binary/large `shrink` + `minimize`,
and `kissat_solve_bytes`.
-/

namespace LeanQbe.T.Examples.Kissat.Plain

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! plain2 "
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

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d,
                              i8 *vals, u64 mv_max);
extern u64 plain_isqrt(u64 x);
extern u64 plain_ilog10(u64 x);
extern u32 plain_arena_next(PlainHdr *h, u32 cref);
extern void plain_wstack_defrag(PlainHdr *h);
extern bool plain_watch_push(PlainHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void plain_heap_down(PlainHdr *h, u32 v);
extern void plain_heap_push(PlainHdr *h, u32 v);
extern u64 plain_heap_pop(PlainHdr *h);
extern void plain_bump_var(PlainHdr *h, u32 v);
extern void plain_bump_decay(PlainHdr *h);
extern void plain_queue_mtf(PlainHdr *h, u32 v);
extern void plain_tick_rel(PlainHdr *h);
extern void plain_ema_update(PlainHdr *h, u64 glue);
extern void plain_assign(PlainHdr *h, u32 lit, u32 rsn);
extern void plain_backtrack(PlainHdr *h, u64 target_lvl);
extern u64 plain_add_clause(PlainHdr *h, u32 len, u32 glue, bool red);
extern bool plain_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);
extern u64 plain_parse_body(PlainHdr *h, u64 cnf_end);
extern u64 plain_propagate(PlainHdr *h);
extern void plain_recompute_tiers(PlainHdr *h);
extern void plain_mark_reasons(PlainHdr *h, bool set_flag);
extern void plain_sort_reds(PlainHdr *h, u64 n);

u64 plain_lit_rank(i8 *vals, u32 *lvl, u32 l) {
  i8 v = vals[l];
  if (v > (i8)0) { return 0x200000000ULL; }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[l >> 1];
}

u64 plain_sweep(PlainHdr *h) {
  u64 mv = h->d.mv;
  u64 nlits = mv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  bool at_root = (h->cur_level == 0ULL);
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    bool lfix = (lvl[l >> 1] == 0u && vals[l] != (i8)0);
    if (sz == 0ULL) {
      l = l + 1ULL;
      continue;
    }
    if (lfix) {
      u64 p = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
          p = p + 1ULL;
        } else {
          p = p + 2ULL;
        }
      }
      u64 k = off;
      while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
      wvec[(l << 1) + 1ULL] = 0u;
      h->wusable = h->wusable + sz;
    } else {
      u64 p = off;
      u64 q = off;
      u64 end = off + sz;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          bool ofix = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] != (i8)0);
          if (ofix) {
            if ((u64)l < (u64)ot && h->num_binary > 0ULL) {
              h->num_binary = h->num_binary - 1ULL;
            }
          } else {
            wstk[q] = w0;
            q = q + 1ULL;
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
    }
    l = l + 1ULL;
  }
  plain_wstack_defrag(h);
  u64 alen = h->arena_len;
  u64 src = 0ULL;
  u64 dst = 0ULL;
  u64 first_red = 0xFFFFFFFFULL;
  u64 irred = 0ULL;
  u64 redd = 0ULL;
  bool unsat = false;
  bool new_unit = false;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src];
    u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)plain_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u || src + 3ULL + (u64)old_sz > alen) {
      src = nsrc;
      continue;
    }
    u32 new_sz = 0u;
    if (at_root) {
      bool sat = false;
      u32 i = 0u;
      while (i < old_sz) {
        u32 lit = ar[src + 3ULL + (u64)i];
        u32 v = lit >> 1;
        if ((u64)v < mv && lvl[v] == 0u && vals[lit] != (i8)0) {
          if (vals[lit] > (i8)0) { sat = true; break; }
        } else {
          ar[dst + 3ULL + (u64)new_sz] = lit;
          new_sz = new_sz + 1u;
        }
        i = i + 1u;
      }
      if (sat) { src = nsrc; continue; }
      if (new_sz == 0u) { unsat = true; break; }
      if (new_sz == 1u) {
        u32 ulit = ar[dst + 3ULL];
        if (vals[ulit] < (i8)0) { unsat = true; break; }
        if (vals[ulit] == (i8)0) {
          plain_assign(h, ulit, 0xFFFFFFFFu);
          new_unit = true;
        }
        src = nsrc;
        continue;
      }
      if (new_sz == 2u) {
        u32 l0 = ar[dst + 3ULL];
        u32 l1 = ar[dst + 4ULL];
        u32 b0 = (l1 & PW_LIT_MASK) | PW_BIN_FLAG;
        u32 b1 = (l0 & PW_LIT_MASK) | PW_BIN_FLAG;
        if (!plain_watch_push(h, l0, b0, 0u, 1u) ||
            !plain_watch_push(h, l1, b1, 0u, 1u)) {
          h->oom = 1ULL;
          break;
        }
        h->num_binary = h->num_binary + 1ULL;
        src = nsrc;
        continue;
      }
    } else {
      u32 i = 0u;
      while (i < old_sz) {
        ar[dst + 3ULL + (u64)i] = ar[src + 3ULL + (u64)i];
        i = i + 1u;
      }
      new_sz = old_sz;
    }
    ar[dst] = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst + 1ULL] = 2u;
    ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RSN) != 0u) {
      u32 i = 0u;
      while (i < new_sz) {
        u32 lit = ar[dst + 3ULL + (u64)i];
        u32 v = lit >> 1;
        if ((u64)v < mv && vals[lit] > (i8)0 && (u64)rsns[v] == src) {
          rsns[v] = (u32)dst;
          break;
        }
        i = i + 1u;
      }
    }
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else {
      irred = irred + 1ULL;
    }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  h->arena_len = dst;
  h->arena_garbage = 0ULL;
  h->first_reducible = first_red;
  h->num_irred = irred;
  h->num_redundant = redd;
  if (unsat) { return 2ULL; }
  if (h->oom != 0ULL) { return 3ULL; }
  u64 p = 0ULL;
  while (p < dst) {
    u32 sz = ar[p + 2ULL];
    if (!at_root && sz >= 3u) {
      u32 i0 = 0u;
      u64 r0 = plain_lit_rank(vals, lvl, ar[p + 3ULL]);
      u32 i = 1u;
      while (i < sz) {
        u64 rk = plain_lit_rank(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r0) { r0 = rk; i0 = i; }
        i = i + 1u;
      }
      if (i0 != 0u) {
        u32 t = ar[p + 3ULL]; ar[p + 3ULL] = ar[p + 3ULL + (u64)i0];
        ar[p + 3ULL + (u64)i0] = t;
      }
      u32 i1 = 1u;
      u64 r1 = plain_lit_rank(vals, lvl, ar[p + 4ULL]);
      i = 2u;
      while (i < sz) {
        u64 rk = plain_lit_rank(vals, lvl, ar[p + 3ULL + (u64)i]);
        if (rk > r1) { r1 = rk; i1 = i; }
        i = i + 1u;
      }
      if (i1 != 1u) {
        u32 t = ar[p + 4ULL]; ar[p + 4ULL] = ar[p + 3ULL + (u64)i1];
        ar[p + 3ULL + (u64)i1] = t;
      }
    }
    ar[p + 1ULL] = 2u;
    u32 l0 = ar[p + 3ULL];
    u32 l1 = ar[p + 4ULL];
    if (!plain_watch_push(h, l0, l1 & PW_LIT_MASK, (u32)p, 2u) ||
        !plain_watch_push(h, l1, l0 & PW_LIT_MASK, (u32)p, 2u)) {
      h->oom = 1ULL;
      return 3ULL;
    }
    p = p + 3ULL + (u64)sz;
  }
  return new_unit ? 1ULL : 0ULL;
}

u64 plain_reduce(PlainHdr *h, bool force) {
  h->reductions = h->reductions + 1ULL;
  u64 delta = 1000ULL * plain_isqrt(h->reductions);
  h->reduce_limit = h->conflicts + delta;
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { plain_backtrack(h, 0ULL); }
    u64 pr = plain_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  plain_recompute_tiers(h);
  plain_mark_reasons(h, true);
  u32 *ar = (u32 *)h->arena;
  u32 *rr = (u32 *)h->red_refs;
  u64 rc = 0ULL;
  u64 alen = h->arena_len;
  u64 p = 0ULL;
  u64 t1 = h->tier1;
  u64 t2 = h->tier2;
  while (p < alen) {
    u32 hdr = ar[p];
    u32 n = plain_arena_next(h, (u32)p);
    if ((hdr & PH_RED) != 0u && (hdr & PH_GARB) == 0u) {
      u32 old_u = (hdr >> 27) & 31u;
      if (old_u > 0u) {
        u32 nhdr = (hdr & 0x07FFFFFFu) | ((old_u - 1u) << 27);
        ar[p] = nhdr;
      }
      if ((hdr & PH_RSN) == 0u) {
        u64 glue = (u64)(hdr & PH_GLUE_MASK);
        bool keep = (glue <= t1 && old_u > 0u) || (glue <= t2 && old_u >= 30u);
        if (!keep && rc < h->red_cap) {
          rr[rc] = (u32)p;
          rc = rc + 1ULL;
        }
      }
    }
    p = (u64)n;
  }
  if (rc > 0ULL) {
    plain_sort_reds(h, rc);
    u64 logv = plain_ilog10(h->reductions + 9ULL);
    u64 pct10 = 900ULL - (400ULL / logv);
    u64 target = (rc * pct10) / 1000ULL;
    u64 i = 0ULL;
    while (i < target && i < rc) {
      u64 cref = (u64)rr[i];
      u32 hdr = ar[cref];
      if ((hdr & PH_GARB) == 0u) {
        ar[cref] = hdr | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[cref + 2ULL];
      }
      i = i + 1ULL;
    }
  }
  if (force || h->unflushed == 0ULL &&
      (h->arena_garbage * 4ULL >= h->arena_len ||
       h->arena_len * 5ULL >= h->arena_cap * 4ULL)) {
    while (true) {
      u64 sr = plain_sweep(h);
      if (sr == 2ULL) { return 20ULL; }
      if (sr == 3ULL) { return 0ULL; }
      if (sr == 0ULL) { break; }
      u64 pr = plain_propagate(h);
      if (pr == 1ULL) { return 20ULL; }
      if (pr != 0ULL) { return 0ULL; }
      h->unflushed = 0ULL;
    }
  } else {
    plain_mark_reasons(h, false);
  }
  return 1ULL;
}

bool plain_analyze_lit(PlainHdr *h, u32 l, u32 skip_var) {
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 cur_lvl = (u32)h->cur_level;
  u32 v = l >> 1;
  if ((u64)v >= h->d.mv) { return false; }
  if (v != skip_var && mrk[v] == (u8)0) {
    u32 vlvl = lvl[v];
    if (vlvl > cur_lvl) { return false; }
    if (vlvl > 0u) {
      mrk[v] = (u8)1;
      if (vlvl == cur_lvl) {
        h->tmp_cnt = h->tmp_cnt + 1ULL;
      } else {
        if (h->tmp_len >= h->d.mv) { return false; }
        tmp[h->tmp_len] = l;
        h->tmp_len = h->tmp_len + 1ULL;
      }
    }
  }
  return true;
}

bool plain_analyze_rsn(PlainHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    u32 ot = rsn & PW_LIT_MASK;
    return plain_analyze_lit(h, ot, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    u32 *gu = (u32 *)h->glue_used;
    u64 gi = (glue > 63ULL) ? 63ULL : glue;
    if (gu[gi] < 0xFFFFFFFFu) { gu[gi] = gu[gi] + 1u; }
    u32 new_u = (glue <= h->tier2) ? 31u : 1u;
    u32 old_u = (hdr >> 27) & 31u;
    if (new_u > old_u) {
      ar[rsn] = (hdr & 0x07FFFFFFu) | (new_u << 27);
    }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!plain_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

void plain_clear_marks(PlainHdr *h, u64 trail_from) {
  u8 *mrk = (u8 *)h->mark;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *trl = (u32 *)h->trail;
  u64 mv = h->d.mv;
  u64 i = 1ULL;
  while (i < h->tmp_len) {
    u32 v = tmp[i] >> 1;
    if ((u64)v < mv) { mrk[v] = (u8)0; }
    i = i + 1ULL;
  }
  u64 j = trail_from;
  while (j < h->trail_end) {
    u32 tv = trl[j] >> 1;
    if ((u64)tv < mv) { mrk[tv] = (u8)0; }
    j = j + 1ULL;
  }
}

void plain_min_mark(PlainHdr *h, u32 v, u8 tag) {
  u64 mv = h->d.mv;
  if ((u64)v >= mv) { return; }
  u8 *mrk = (u8 *)h->mark;
  if ((mrk[v] & tag) != (u8)0) { return; }
  if (mrk[v] == (u8)0) {
    if (h->min_clr_len < mv) {
      u32 *mclr = (u32 *)h->min_clr;
      mclr[h->min_clr_len] = v;
      h->min_clr_len = h->min_clr_len + 1ULL;
    } else {
      h->min_clr_full = 1ULL;
    }
  }
  mrk[v] = mrk[v] | tag;
}

bool plain_min_lit(PlainHdr *h, u32 root_lit) {
  u64 mv = h->d.mv;
  u32 root_v = root_lit >> 1;
  if ((u64)root_v >= mv || h->min_depth == 0ULL) { return false; }
  u32 *rsns = (u32 *)h->reason;
  if (rsns[root_v] == 0xFFFFFFFFu) { return false; }
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena;
  u32 *stk = (u32 *)h->min_stk;
  stk[0] = root_v;
  stk[1] = 0u;
  u64 sp = 0ULL;
  bool ok = false;
  u64 steps = 0ULL;
  u64 max_steps = (h->arena_len + mv) * 4ULL + 64ULL;
  while (steps < max_steps) {
    steps = steps + 1ULL;
    u32 v = stk[sp << 1];
    u32 pos = stk[(sp << 1) + 1ULL];
    if ((u64)v >= mv) { break; }
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) { break; }
    u32 sz = 0u;
    bool is_bin = ((rsn & PW_BIN_FLAG) != 0u);
    if (is_bin) {
      sz = 1u;
    } else {
      if ((u64)rsn + 3ULL > h->arena_len) { break; }
      sz = ar[(u64)rsn + 2ULL];
      if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { break; }
    }
    if (pos < sz) {
      stk[(sp << 1) + 1ULL] = pos + 1u;
      u32 l = is_bin ? (rsn & PW_LIT_MASK) : ar[(u64)rsn + 3ULL + (u64)pos];
      u32 u = l >> 1;
      if ((u64)u >= mv) { break; }
      if (u == v || lvl[u] == 0u) { continue; }
      u8 mu = mrk[u];
      if ((mu & (u8)2) != (u8)0) { continue; }
      if ((mu & (u8)4) != (u8)0) { break; }
      u32 ur = rsns[u];
      if (ur == 0xFFFFFFFFu) {
        plain_min_mark(h, u, (u8)4);
        break;
      }
      if (sp + 1ULL >= h->min_depth) { break; }
      sp = sp + 1ULL;
      stk[sp << 1] = u;
      stk[(sp << 1) + 1ULL] = 0u;
      continue;
    }
    if (sp == 0ULL) { ok = true; break; }
    plain_min_mark(h, v, (u8)2);
    sp = sp - 1ULL;
  }
  if (!ok) {
    u64 j = 1ULL;
    while (j <= sp) {
      plain_min_mark(h, stk[j << 1], (u8)4);
      j = j + 1ULL;
    }
    return false;
  }
  return true;
}

bool plain_tmp_less(u32 *lvl, u32 *tpos, u32 a, u32 b) {
  u32 va = a >> 1;
  u32 vb = b >> 1;
  u32 la = lvl[va];
  u32 lb = lvl[vb];
  if (la != lb) { return la < lb; }
  return tpos[va] < tpos[vb];
}

void plain_sort_tmp(PlainHdr *h) {
  u64 tlen = h->tmp_len;
  if (tlen <= 2ULL) { return; }
  u64 n = tlen - 1ULL;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *tpos = (u32 *)h->trail_pos;
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    u64 root = start;
    while (true) {
      u64 ch = (root << 1) + 1ULL;
      if (ch >= n) { break; }
      if (ch + 1ULL < n && plain_tmp_less(lvl, tpos, tmp[1ULL + ch], tmp[2ULL + ch])) {
        ch = ch + 1ULL;
      }
      if (!plain_tmp_less(lvl, tpos, tmp[1ULL + root], tmp[1ULL + ch])) { break; }
      u32 t = tmp[1ULL + root]; tmp[1ULL + root] = tmp[1ULL + ch]; tmp[1ULL + ch] = t;
      root = ch;
    }
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = tmp[1ULL]; tmp[1ULL] = tmp[1ULL + end]; tmp[1ULL + end] = t;
    u64 root = 0ULL;
    while (true) {
      u64 ch = (root << 1) + 1ULL;
      if (ch >= end) { break; }
      if (ch + 1ULL < end && plain_tmp_less(lvl, tpos, tmp[1ULL + ch], tmp[2ULL + ch])) {
        ch = ch + 1ULL;
      }
      if (!plain_tmp_less(lvl, tpos, tmp[1ULL + root], tmp[1ULL + ch])) { break; }
      u32 t2 = tmp[1ULL + root]; tmp[1ULL + root] = tmp[1ULL + ch]; tmp[1ULL + ch] = t2;
      root = ch;
    }
    end = end - 1ULL;
  }
}

void plain_shrink_blk(PlainHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *sstk = (u32 *)h->shrink_stk;
  u32 *ar = (u32 *)h->arena;
  u64 mv = h->d.mv;
  u64 open = end_b - beg;
  u64 slen = 0ULL;
  u64 k = beg;
  while (k < end_b) {
    u32 v = tmp[k] >> 1;
    mrk[v] = mrk[v] | (u8)8;
    sstk[slen] = v;
    slen = slen + 1ULL;
    k = k + 1ULL;
  }
  bool failed = false;
  u32 uip = 0xFFFFFFFFu;
  u64 t = max_tr;
  while (!failed) {
    while (true) {
      if (t >= h->trail_end) { failed = true; break; }
      u32 lit = trl[t];
      if ((mrk[lit >> 1] & (u8)8) != (u8)0) { uip = lit; break; }
      if (t == 0ULL) { failed = true; break; }
      t = t - 1ULL;
    }
    if (failed) { break; }
    if (t > 0ULL) { t = t - 1ULL; }
    if (open == 1ULL) { break; }
    u32 uv = uip >> 1;
    u32 rsn = rsns[uv];
    if (rsn == 0xFFFFFFFFu) { failed = true; break; }
    if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      u32 ov = ot >> 1;
      if ((u64)ov < mv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
        if (lvl[ov] < blvl) {
          if ((mrk[ov] & (u8)2) == (u8)0) {
            if ((mrk[ov] & (u8)4) != (u8)0 || !plain_min_lit(h, ot)) {
              plain_min_mark(h, ov, (u8)4);
              failed = true;
            } else {
              plain_min_mark(h, ov, (u8)2);
            }
          }
        } else if (slen < mv) {
          mrk[ov] = mrk[ov] | (u8)8;
          sstk[slen] = ov;
          slen = slen + 1ULL;
          open = open + 1ULL;
        } else {
          failed = true;
        }
      }
    } else {
      if ((u64)rsn + 3ULL > h->arena_len) { failed = true; break; }
      u32 csz = ar[(u64)rsn + 2ULL];
      if (csz < 3u || (u64)rsn + 3ULL + (u64)csz > h->arena_len) { failed = true; break; }
      u32 i = 0u;
      while (i < csz) {
        u32 ot = ar[(u64)rsn + 3ULL + (u64)i];
        u32 ov = ot >> 1;
        if (ot != uip && (u64)ov < mv && lvl[ov] > 0u && (mrk[ov] & (u8)8) == (u8)0) {
          if (lvl[ov] < blvl) {
            if ((mrk[ov] & (u8)2) == (u8)0) {
              if ((mrk[ov] & (u8)4) != (u8)0 || !plain_min_lit(h, ot)) {
                plain_min_mark(h, ov, (u8)4);
                failed = true;
                break;
              } else {
                plain_min_mark(h, ov, (u8)2);
              }
            }
          } else if (slen < mv) {
            mrk[ov] = mrk[ov] | (u8)8;
            sstk[slen] = ov;
            slen = slen + 1ULL;
            open = open + 1ULL;
          } else {
            failed = true;
            break;
          }
        }
        i = i + 1u;
      }
    }
    if (failed) { break; }
    open = open - 1ULL;
  }
  if (failed || uip == 0xFFFFFFFFu) {
    u64 i = 0ULL;
    while (i < slen) {
      u32 sv = sstk[i];
      mrk[sv] = mrk[sv] & (u8)0xF7;
      i = i + 1ULL;
    }
    return;
  }
  u32 not_uip = uip ^ 1u;
  k = beg;
  while (k < end_b) {
    tmp[k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  tmp[beg] = not_uip;
  u64 i = 0ULL;
  while (i < slen) {
    u32 sv = sstk[i];
    mrk[sv] = mrk[sv] & (u8)0xF7;
    plain_min_mark(h, sv, (u8)2);
    i = i + 1ULL;
  }
}

void plain_min_shrink(PlainHdr *h) {
  u64 mv = h->d.mv;
  u64 tlen = h->tmp_len;
  h->conflicts = h->conflicts + 1ULL;
  if (tlen <= 1ULL || tlen > mv) {
    h->learned_lits = h->learned_lits + tlen;
    return;
  }
  plain_sort_tmp(h);
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *tpos = (u32 *)h->trail_pos;
  h->min_clr_len = 0ULL;
  h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < tlen) {
    plain_min_mark(h, tmp[i] >> 1, (u8)2);
    i = i + 1ULL;
  }
  u64 end_b = tlen;
  while (end_b > 1ULL) {
    u64 beg = end_b - 1ULL;
    u32 blvl = lvl[tmp[beg] >> 1];
    u64 max_tr = (u64)tpos[tmp[beg] >> 1];
    while (beg > 1ULL && lvl[tmp[beg - 1ULL] >> 1] == blvl) {
      beg = beg - 1ULL;
      u64 tp = (u64)tpos[tmp[beg] >> 1];
      if (tp > max_tr) { max_tr = tp; }
    }
    if (end_b - beg == 1ULL) {
      if (plain_min_lit(h, tmp[beg])) { tmp[beg] = 0xFFFFFFFFu; }
    } else {
      plain_shrink_blk(h, beg, end_b, blvl, max_tr);
    }
    end_b = beg;
  }
  u64 keep = 1ULL;
  u64 k = 1ULL;
  while (k < tlen) {
    if (tmp[k] != 0xFFFFFFFFu) {
      tmp[keep] = tmp[k];
      keep = keep + 1ULL;
    }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL;
    while (v < mv) { mrk[v] = (u8)0; v = v + 1ULL; }
  } else {
    u32 *mclr = (u32 *)h->min_clr;
    u64 z = 0ULL;
    while (z < h->min_clr_len) {
      u32 cv = mclr[z];
      if ((u64)cv < mv) { mrk[cv] = (u8)0; }
      z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL;
  h->min_clr_full = 0ULL;
  h->tmp_len = keep;
  h->min_removed = h->min_removed + (tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

u64 plain_analyze(PlainHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  h->tmp_cnt = 0ULL;
  h->tmp_len = 1ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = plain_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              plain_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else {
    seed_ok = plain_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  if (!seed_ok) { plain_clear_marks(h, 0ULL); return 0ULL; }
  if (h->tmp_cnt == 0ULL) {
    plain_clear_marks(h, 0ULL);
    if (h->tmp_len == 1ULL) { return 20ULL; }
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
    if (idx == 0ULL) { plain_clear_marks(h, 0ULL); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx];
    u32 pv = p >> 1;
    if ((u64)pv >= h->d.mv) { plain_clear_marks(h, 0ULL); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      plain_bump_var(h, pv);
      plain_queue_mtf(h, pv);
      h->tmp_cnt = h->tmp_cnt - 1ULL;
      if (h->tmp_cnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv];
      if (!plain_analyze_rsn(h, rsn, pv)) { plain_clear_marks(h, 0ULL); return 0ULL; }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { plain_clear_marks(h, 0ULL); return 0ULL; }
  tmp[0] = uip_lit;
  plain_clear_marks(h, idx);
  u64 bi = 1ULL;
  while (bi < h->tmp_len) {
    u32 bv = tmp[bi] >> 1;
    plain_bump_var(h, bv);
    plain_queue_mtf(h, bv);
    bi = bi + 1ULL;
  }
  plain_bump_decay(h);
  plain_min_shrink(h);
  plain_tick_rel(h);
  u64 glue = 1ULL;
  u32 last_lvl = 0u;
  u64 gi = 1ULL;
  while (gi < h->tmp_len) {
    u32 gl = lvl[tmp[gi] >> 1];
    if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
    gi = gi + 1ULL;
  }
  plain_ema_update(h, glue);
  if (h->tmp_len == 1ULL) {
    plain_backtrack(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    plain_assign(h, uip_lit, 0xFFFFFFFFu);
    return 1ULL;
  }
  u64 max_idx = h->tmp_len - 1ULL;
  u64 max_lvl = (u64)lvl[tmp[max_idx] >> 1];
  if (max_lvl >= (u64)cur_lvl) { max_lvl = (u64)cur_lvl - 1ULL; }
  u32 w1 = tmp[1];
  tmp[1] = tmp[max_idx];
  tmp[max_idx] = w1;
  plain_backtrack(h, max_lvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap ||
      h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { plain_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = plain_reduce(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = plain_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  plain_assign(h, uip_lit, rsn);
  return 1ULL;
}

u64 plain_decide(PlainHdr *h) {
  i8 *vals = (i8 *)h->values;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u32 *hp = (u32 *)h->heap;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qs = (u32 *)h->q_stamp;
  u64 mv = h->d.mv;
  u64 chosen = 0xFFFFFFFFFFFFFFFFULL;
  if (h->stable != 0ULL) {
    while (h->heap_len > 0ULL && h->heap_len <= mv) {
      u32 top = hp[0];
      if ((u64)top >= mv) { break; }
      if (vals[(u64)top << 1] == (i8)0) { chosen = (u64)top; break; }
      plain_heap_pop(h);
    }
  } else {
    u64 cur = h->q_search_idx;
    u64 steps = 0ULL;
    while (cur < mv && steps < mv) {
      if (vals[cur << 1] == (i8)0) { chosen = cur; break; }
      cur = (u64)qp[cur];
      steps = steps + 1ULL;
    }
    if (cur < mv) {
      h->q_search_idx = cur;
      h->q_search_stamp = (u64)qs[cur];
    } else {
      cur = h->q_last;
      steps = 0ULL;
      while (cur < mv && steps < mv) {
        if (vals[cur << 1] == (i8)0) { chosen = cur; break; }
        cur = (u64)qp[cur];
        steps = steps + 1ULL;
      }
      if (cur < mv) {
        h->q_search_idx = cur;
        h->q_search_stamp = (u64)qs[cur];
      }
    }
  }
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) {
    u64 v = 0ULL;
    while (v < mv) {
      if (vals[v << 1] == (i8)0) { chosen = v; break; }
      v = v + 1ULL;
    }
  }
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) { return 0ULL; }
  h->cur_level = h->cur_level + 1ULL;
  i8 dph = ph[chosen];
  if (h->stable != 0ULL && ptgt[chosen] != (i8)0) { dph = ptgt[chosen]; }
  u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  plain_assign(h, lit, 0xFFFFFFFFu);
  return 1ULL;
}

void plain_rephase(PlainHdr *h) {
  plain_backtrack(h, 0ULL);
  h->rephased = h->rephased + 1ULL;
  u64 sel = (h->rephased - 1ULL) % 4ULL;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 mv = h->d.mv;
  u64 k = 0ULL;
  if (sel == 0ULL || sel == 2ULL) {
    while (k < mv) {
      if (pbst[k] != (i8)0) { ph[k] = pbst[k]; }
      k = k + 1ULL;
    }
    h->best_assigned = 0ULL;
  } else if (sel == 1ULL) {
    while (k < mv) { ph[k] = (i8)(-1); k = k + 1ULL; }
  } else {
    while (k < mv) { ph[k] = (i8)1; k = k + 1ULL; }
  }
  k = 0ULL;
  while (k < mv) { ptgt[k] = ph[k]; k = k + 1ULL; }
  h->target_assigned = 0ULL;
  u64 lg = plain_ilog10(h->rephased + 2ULL);
  h->rephase_limit = h->conflicts + 1000ULL + (100ULL * h->rephased * lg);
}

void plain_switch_mode(PlainHdr *h) {
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    h->stable = 1ULL;
    u64 dticks = h->search_ticks - h->mode_saved_ticks;
    if (dticks < 1000ULL) { dticks = 1000ULL; }
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 mv = h->d.mv;
    i8 *vals = (i8 *)h->values;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL;
    u64 v = 0ULL;
    while (v < mv) {
      if (vals[v << 1] == (i8)0) {
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
    while (s > 0ULL) {
      s = s - 1ULL;
      plain_heap_down(h, hp[s]);
    }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    h->stable = 0ULL;
    u64 mv = h->d.mv;
    u64 cnt = (h->switched + 2ULL) >> 1;
    u64 lg = plain_ilog10(cnt + 2ULL);
    h->mode_confl_lim = h->conflicts + 1000ULL * cnt * lg;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < mv) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  h->ema_fast_biased = 0ULL;
  h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL;
  h->ema_slow_exp = 1ULL << 24;
  h->restart_limit = h->conflicts + 1ULL;
}

u64 plain_restart_due(PlainHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) {
      h->rel_trigger = 0ULL;
      return 1ULL;
    }
    return 0ULL;
  }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  u64 scale = 1ULL << 24;
  u64 fd = scale - h->ema_fast_exp;
  u64 sd = scale - h->ema_slow_exp;
  if (fd <= 256ULL || sd <= 256ULL) { return 0ULL; }
  u64 fval = h->ema_fast_biased / (fd >> 8);
  u64 sval = h->ema_slow_biased / (sd >> 8);
  if (fval * 100ULL > sval * 110ULL) {
    h->restart_limit = h->conflicts + 1ULL;
    return 1ULL;
  }
  return 0ULL;
}

u64 plain_lucky_scan(PlainHdr *h, bool pos_mode, bool fwd) {
  u64 mv = h->d.mv;
  i8 *vals = (i8 *)h->values;
  u64 i = 0ULL;
  while (i < mv) {
    u64 v = fwd ? i : (mv - 1ULL - i);
    if (vals[v << 1] == (i8)0) {
      if (h->fuel == 0ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
      h->fuel = h->fuel - 1ULL;
      u32 lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
      h->cur_level = h->cur_level + 1ULL;
      plain_assign(h, lit, 0xFFFFFFFFu);
      u64 pr = plain_propagate(h);
      if (pr == 2ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) {
        if (h->cur_level > 1ULL) {
          plain_backtrack(h, h->cur_level - 1ULL);
          if (h->fuel == 0ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
          h->fuel = h->fuel - 1ULL;
          h->cur_level = h->cur_level + 1ULL;
          plain_assign(h, lit ^ 1u, 0xFFFFFFFFu);
          u64 pr2 = plain_propagate(h);
          if (pr2 == 2ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
          if (pr2 == 1ULL) { plain_backtrack(h, 0ULL); return 0ULL; }
        } else {
          u64 ast = plain_analyze(h);
          if (ast == 20ULL) { return 20ULL; }
          if (ast != 1ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
          u64 pr3 = plain_propagate(h);
          if (pr3 == 1ULL) { return 20ULL; }
          if (pr3 == 2ULL) { plain_backtrack(h, 0ULL); return 2ULL; }
        }
      }
    }
    i = i + 1ULL;
  }
  return 10ULL;
}

u64 plain_lucky(PlainHdr *h) {
  u64 mv = h->d.mv;
  i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 alen = h->arena_len;
  h->probing = 1ULL;
  bool has_all_neg = false;
  bool has_all_pos = false;
  u64 p = 0ULL;
  while (p < alen && (!has_all_neg || !has_all_pos)) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)plain_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u && sz >= 3u) {
      bool any_pos = false;
      bool any_neg = false;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        if (vals[l] >= (i8)0) {
          if ((l & 1u) == 0u) { any_pos = true; } else { any_neg = true; }
        }
        k = k + 1u;
      }
      if (!any_pos) { has_all_neg = true; }
      if (!any_neg) { has_all_pos = true; }
    }
    p = np;
  }
  u64 v = 0ULL;
  while (v < mv && (!has_all_neg || !has_all_pos)) {
    if (vals[v << 1] == (i8)0) {
      u32 nl = (u32)((v << 1) | 1ULL);
      u64 off = (u64)wvec[(u64)nl << 1];
      u64 end = off + (u64)wvec[((u64)nl << 1) + 1ULL];
      while (off < end && !has_all_neg) {
        u32 w0 = wstk[off];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((ot & 1u) != 0u && vals[ot] >= (i8)0) { has_all_neg = true; }
          off = off + 1ULL;
        } else { off = off + 2ULL; }
      }
      u32 pl = (u32)(v << 1);
      off = (u64)wvec[(u64)pl << 1];
      end = off + (u64)wvec[((u64)pl << 1) + 1ULL];
      while (off < end && !has_all_pos) {
        u32 w0 = wstk[off];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((ot & 1u) == 0u && vals[ot] >= (i8)0) { has_all_pos = true; }
          off = off + 1ULL;
        } else { off = off + 2ULL; }
      }
    }
    v = v + 1ULL;
  }
  if (!has_all_neg || !has_all_pos) {
    bool set_pos = !has_all_neg;
    v = 0ULL;
    while (v < mv) {
      if (vals[v << 1] == (i8)0) {
        if (h->fuel == 0ULL) { plain_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL; }
        h->fuel = h->fuel - 1ULL;
        h->cur_level = h->cur_level + 1ULL;
        plain_assign(h, set_pos ? (u32)(v << 1) : ((u32)(v << 1) | 1u), 0xFFFFFFFFu);
        u64 pr = plain_propagate(h);
        if (pr != 0ULL) { plain_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL; }
      }
      v = v + 1ULL;
    }
    h->probing = 0ULL;
    return 10ULL;
  }
  u64 r = plain_lucky_scan(h, false, true);
  if (r == 0ULL) { r = plain_lucky_scan(h, true, true); }
  if (r == 0ULL) { r = plain_lucky_scan(h, false, false); }
  if (r == 0ULL) { r = plain_lucky_scan(h, true, false); }
  h->probing = 0ULL;
  return r;
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_end_arg, u64 work_ptr, u64 work_len, u64 fuel) {
  if (fuel == 0ULL) { return 0ULL; }
  u64 cnf_len = cnf_end_arg;
  if (cnf_len > (~0ULL) - cnf_ptr || work_len > (~0ULL) - work_ptr) { return 0ULL; }
  u64 mis = work_ptr & 7ULL;
  u64 pad = (mis == 0ULL) ? 0ULL : (8ULL - mis);
  if (work_len < pad + (u64)sizeof(PlainHdr)) { return 0ULL; }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_len - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!plain_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) { return 0ULL; }
  PlainHdr *h = (PlainHdr *)hdr_addr;
  u64 pst = plain_parse_body(h, cnf_end);
  if (pst == 0ULL) { return 0ULL; }
  if (pst == 20ULL) { return 20ULL; }
  u64 pr0 = plain_propagate(h);
  if (pr0 == 2ULL) { return 0ULL; }
  if (pr0 == 1ULL) { return 20ULL; }
  if (h->trail_end < h->d.mv && h->fuel > 0ULL) {
    u64 lr = plain_lucky(h);
    if (lr == 20ULL) { return 20ULL; }
    if (lr == 2ULL || h->oom != 0ULL) { return 0ULL; }
    if (lr == 10ULL) {
      u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, h->d.mv);
      return (ok == 1ULL) ? 10ULL : 0ULL;
    }
  }
  u64 res = 0ULL;
  while (true) {
    u64 pr = plain_propagate(h);
    if (pr == 2ULL) { res = 0ULL; break; }
    if (pr == 1ULL) {
      if (h->cur_level == 0ULL) { res = 20ULL; break; }
      u64 ast = plain_analyze(h);
      if (ast == 20ULL) { res = 20ULL; break; }
      if (ast != 1ULL || h->oom != 0ULL) { res = 0ULL; break; }
    } else {
      if (h->fuel == 0ULL) { res = 0ULL; break; }
      h->fuel = h->fuel - 1ULL;
      if (h->trail_end < h->d.mv) {
        plain_switch_mode(h);
        if (h->num_redundant > 0ULL && h->conflicts >= h->reduce_limit) {
          u64 rr = plain_reduce(h, false);
          if (rr == 20ULL) { res = 20ULL; break; }
          if (rr != 1ULL) { res = 0ULL; break; }
        } else if (h->stable != 0ULL && h->conflicts > h->rephase_limit) {
          plain_rephase(h);
        } else if (plain_restart_due(h) != 0ULL) {
          h->restarts = h->restarts + 1ULL;
          plain_backtrack(h, 0ULL);
        } else {
          u64 dst = plain_decide(h);
          if (dst == 0ULL) {
            u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d,
                                        (i8 *)h->values, h->d.mv);
            res = (ok == 1ULL) ? 10ULL : 0ULL;
            break;
          }
        }
      } else {
        u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, h->d.mv);
        res = (ok == 1ULL) ? 10ULL : 0ULL;
        break;
      }
    }
  }
  return res;
}
"

/-- Combined callee-first function list (`Dimacs` + `plain1` + `plain2`). -/
def plainFns : List Fn :=
  dimacs_fns ++ plain1_fns ++ plain2_fns

/-- Combined zero-exit acyclic `Module` for the Kissat `D-Plain` (`--plain`) C0 SAT solver. -/
def plainModule : LeanQbe.T.Module :=
  { fns := plainFns, externs := [], exits := [] }

theorem plain_lit_rank_wf : Func.Wf plain_lit_rank_body := by t_wf_reify
theorem plain_sweep_wf : Func.Wf plain_sweep_body := by t_wf_reify
theorem plain_reduce_wf : Func.Wf plain_reduce_body := by t_wf_reify
theorem plain_ana_lit_wf : Func.Wf plain_analyze_lit_body := by t_wf_reify
theorem plain_ana_rsn_wf : Func.Wf plain_analyze_rsn_body := by t_wf_reify
theorem plain_clear_mrk_wf : Func.Wf plain_clear_marks_body := by t_wf_reify
theorem plain_min_mark_wf : Func.Wf plain_min_mark_body := by t_wf_reify
theorem plain_min_lit_wf : Func.Wf plain_min_lit_body := by t_wf_reify
theorem plain_tmp_less_wf : Func.Wf plain_tmp_less_body := by t_wf_reify
theorem plain_sort_tmp_wf : Func.Wf plain_sort_tmp_body := by t_wf_reify
theorem plain_shrink_blk_wf : Func.Wf plain_shrink_blk_body := by t_wf_reify
theorem plain_min_shrk_wf : Func.Wf plain_min_shrink_body := by t_wf_reify
theorem plain_analyze_wf : Func.Wf plain_analyze_body := by t_wf_reify
theorem plain_decide_wf : Func.Wf plain_decide_body := by t_wf_reify
theorem plain_rephase_wf : Func.Wf plain_rephase_body := by t_wf_reify
theorem plain_switch_mode_wf : Func.Wf plain_switch_mode_body := by t_wf_reify
theorem plain_restart_due_wf : Func.Wf plain_restart_due_body := by t_wf_reify
theorem plain_lucky_scan_wf : Func.Wf plain_lucky_scan_body := by t_wf_reify
theorem plain_lucky_wf : Func.Wf plain_lucky_body := by t_wf_reify
theorem kissat_solve_bytes_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

/-- All 20 functions in `plain2_fns` satisfy `Fn.Wf`. -/
theorem plain2_fns_wf : ∀ f ∈ plain2_fns, f.Wf := by
  intro f hf
  simp only [plain2_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plain_lit_rank_wf
  · exact plain_sweep_wf
  · exact plain_reduce_wf
  · exact plain_ana_lit_wf
  · exact plain_ana_rsn_wf
  · exact plain_clear_mrk_wf
  · exact plain_min_mark_wf
  · exact plain_min_lit_wf
  · exact plain_tmp_less_wf
  · exact plain_sort_tmp_wf
  · exact plain_shrink_blk_wf
  · exact plain_min_shrk_wf
  · exact plain_analyze_wf
  · exact plain_decide_wf
  · exact plain_rephase_wf
  · exact plain_switch_mode_wf
  · exact plain_restart_due_wf
  · exact plain_lucky_scan_wf
  · exact plain_lucky_wf
  · exact kissat_solve_bytes_wf

/-- Every function in `plainFns` (`dimacs_fns ++ plain1_fns ++ plain2_fns`) satisfies `Fn.Wf`. -/
theorem plainFns_wf : ∀ f ∈ plainFns, f.Wf := by
  intro f hf
  simp only [plainFns, List.mem_append] at hf
  rcases hf with (hd | hp1) | hp2
  · exact dimacsFns_wf f hd
  · exact plain1_fns_wf f hp1
  · exact plain2_fns_wf f hp2

/-- Combined acyclic module certificate (`plainModule.checkAcyclic = true`). -/
theorem plain_acyclic : plainModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Plain
