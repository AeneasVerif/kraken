module

public import LeanQbe.T.Examples.Kissat.Full2
meta import LeanQbe.T.Examples.Kissat.Full2
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Wave 4I: ProbSAT Local Search (`walk.c`) & Full Warmup (`warmup.c`)

Strictly additive `T4/T3 -> T1` Kissat 4.0.4 fidelity upgrade over `Full2` (`full_walk*`,
`full_warmup`) and `FullM6WalkParse` (`0` edits to frozen `Full1..6*`):
1. **`full_walk_cb_inv_m7` + `full_walk_init_table_m7` (`src/walk.c:cbvals`):** full 6-node
   piecewise-linear `cbvals` fit `(0, 2.00)-(3, 2.50)-(4, 2.85)-(5, 3.70)-(6, 5.10)-(7, 7.40)`
   toggled with `cb = 2.00` by `walk_cnt_stat & 1`, precomputing monotone `Q30` exponential table
   `scores[0..31]` (`0` `double`/`pow`, `O(1)` lookup in `pick_literal`).
2. **`full_walk_effort_m7` (`V3b_walk_eff` + `SET_EFFORT_LIMIT`):** combines `V3b` adaptive flip
   scaling `clamp(2 * ncl, 256, 4096)` with upstream `dticks / 20` `walk_steps` budget (`[500k,
   40M]`).
3. **O(1) incremental ProbSAT local search (`full_walk_collect_m7`, `full_walk_build_occ_m7`,
   `full_walk_break_m7`, `full_walk_pick_m7`, `full_walk_flip_m7`, `full_walk_trail_push_m7`,
   `full_walk_save_min_m7`, `full_walk_m7`):**
   - Stores `scores[0..31]`, entries, `sat_cnt`, `unsat_pos`, `unsat_list`, and CSR `occ_pool` in
     `scratch_buf` (`32 + 5 * ncl + tot_occ <= scratch_cap`), with CSR index tables in
     `tarjan_mark` / `tarjan_reach` and candidate scores/flipped trail in `work_stk1` / `work_stk2`
     / `wsort`.
   - Removes forced deterministic `0`-break override; uses full `Q30` roulette weights, round-robin
     `flips % ulen` unsat picking, `target`/`phases` import, and suffix-preserving
     `save_walker_trail`.
4. **Full warmup (`full_warmup_m7`, `full_walk_warmup_m7`):** preserves `ph[v]` saving without
   setting `probing = 1` during decisions, propagates all trail literals beyond conflicts, and
   restores `cur_level = 0`, `probing`, and `search_ticks` cleanly.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Walk

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full

kissat_c0! m7Walk "
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

#define PH_GARB      0x00080000u
#define PH_RED       0x00400000u
#define PW_BIN_FLAG  0x80000000u
#define PW_LIT_MASK  0x7FFFFFFFu
#define FL_ACTIVE    1u

extern u64 full_rng_next(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern u64 full_propagate(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);

u64 full_walk_cb_inv_m7(FullHdr *h, u64 ncl, u64 tot_lits) {
  if ((h->walk_cnt_stat & 1ULL) == 0ULL || ncl == 0ULL) {
    return 32768ULL;
  }
  u64 occ = (tot_lits > 0x0000FFFFFFFFFFFFULL) ? 0x0000FFFFFFFFFFFFULL : tot_lits;
  u64 avg = (occ << 16) / ncl;
  u64 cb = 2000ULL;
  if (avg < 196608ULL) {
    cb = 2000ULL + (500ULL * avg) / 196608ULL;
  } else if (avg < 262144ULL) {
    cb = 2500ULL + ((350ULL * (avg - 196608ULL)) >> 16);
  } else if (avg < 327680ULL) {
    cb = 2850ULL + ((850ULL * (avg - 262144ULL)) >> 16);
  } else if (avg < 393216ULL) {
    cb = 3700ULL + ((1400ULL * (avg - 327680ULL)) >> 16);
  } else {
    u64 ex = avg - 393216ULL;
    if (ex > 2621440ULL) { ex = 2621440ULL; }
    cb = 5100ULL + ((2300ULL * ex) >> 16);
  }
  if (cb < 2000ULL) { cb = 2000ULL; }
  u64 inv = (65536000ULL + (cb >> 1)) / cb;
  if (inv == 0ULL) { inv = 1ULL; }
  if (inv > 32768ULL) { inv = 32768ULL; }
  return inv;
}

void full_walk_init_table_m7(FullHdr *h, u64 inv_q16) {
  if (h->scratch_cap < 32ULL) { return; }
  u64 iq = (inv_q16 > 32768ULL) ? 32768ULL : inv_q16;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 sc = 1ULL << 30;
  u64 i = 0ULL;
  while (i < 32ULL) {
    scr[i] = (u32)sc;
    sc = (sc * iq) >> 16;
    if (sc < 1ULL) { sc = 1ULL; }
    i = i + 1ULL;
  }
}

u64 full_walk_effort_m7(FullHdr *h, u64 max_flips) {
  u64 st = h->search_ticks;
  u64 mt = h->mode_saved_ticks;
  u64 dt = (st > mt) ? (st - mt) : 0ULL;
  u64 eff = 40000000ULL;
  if (dt <= 800000000ULL) { eff = dt / 20ULL; }
  u64 mf = (max_flips > 4096ULL) ? 4096ULL : max_flips;
  u64 flr = mf * 2048ULL;
  if (flr < 500000ULL) { flr = 500000ULL; }
  if (eff < flr) { eff = flr; }
  if (eff > 40000000ULL) { eff = 40000000ULL; }
  return eff;
}

void full_walk_init_vals_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv > h->max_vars) { cv = h->max_vars; }
  i8 *vals = (i8 *)h->values;
  i8 *wvals = (i8 *)h->walk_vals;
  i8 *wbest = (i8 *)h->walk_best;
  i8 *ph = (i8 *)h->phases;
  i8 *pt = (i8 *)h->phases_target;
  u32 *fl = (u32 *)h->flags;
  u32 *trc = (u32 *)h->tarjan_reach;
  u64 v = 0ULL;
  while (v < cv) {
    i8 rv = vals[v << 1];
    i8 p = (i8)1;
    if (rv != (i8)0) {
      p = rv;
    } else if ((fl[v] & FL_ACTIVE) != 0u) {
      p = ph[v];
      if (h->stable != 0ULL && h->target_assigned > 0ULL && pt[v] != (i8)0) {
        p = pt[v];
      }
      if (p == (i8)0) { p = (i8)1; }
    }
    wvals[v << 1] = p;
    wvals[(v << 1) | 1ULL] = (p < (i8)0) ? (i8)1 : (i8)(-1);
    wbest[v] = p;
    v = v + 1ULL;
  }
  u64 two_v = cv << 1;
  u64 l = 0ULL;
  while (l < two_v) {
    trc[l] = 0u;
    l = l + 1ULL;
  }
}

u64 full_walk_collect_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 scap = h->scratch_cap;
  if (cv == 0ULL || cv > h->max_vars || scap < 64ULL) { return 0ULL; }
  u64 two_v = cv << 1;
  u64 wlen = h->wlen;
  u64 alen = h->arena_len;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ncl = 0ULL;
  u64 tot_lits = 0ULL;
  bool full = false;
  u64 lit0 = 0ULL;
  while (lit0 < two_v && !full) {
    if (vals[lit0] <= (i8)0) {
      u64 off = (u64)wvec[lit0 << 1];
      u64 sz = (u64)wvec[(lit0 << 1) + 1ULL];
      if (off <= wlen && sz <= wlen - off) {
        u64 end = off + sz;
        u64 k = off;
        while (k < end && !full) {
          u32 w0 = wstk[k];
          k = k + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 lit1 = w0 & PW_LIT_MASK;
            if ((u64)lit1 < two_v && lit0 < (u64)lit1 && vals[lit1] <= (i8)0 &&
                (vals[lit0] == (i8)0 || vals[lit1] == (i8)0)) {
              if (ncl + 1ULL > scap || tot_lits + 2ULL > scap ||
                  32ULL + 5ULL * (ncl + 1ULL) + tot_lits + 2ULL > scap) {
                full = true;
              } else {
                scr[32ULL + (ncl << 1)] = (u32)lit0 | PW_BIN_FLAG;
                scr[32ULL + (ncl << 1) + 1ULL] = lit1;
                ncl = ncl + 1ULL;
                tot_lits = tot_lits + 2ULL;
              }
            }
          } else {
            if (k < end) { k = k + 1ULL; }
          }
        }
      }
    }
    lit0 = lit0 + 1ULL;
  }
  u64 cref = 0ULL;
  while (cref + 3ULL <= alen && !full) {
    u32 hdr = ar[cref];
    u32 csz = ar[cref + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && csz >= 3u && (u64)csz <= alen &&
        cref + 3ULL + (u64)csz <= alen) {
      bool rsat = false;
      bool has_un = false;
      u32 j = 0u;
      while (j < csz) {
        u32 lit = ar[cref + 3ULL + (u64)j];
        if ((u64)lit < two_v) {
          i8 rv = vals[lit];
          if (rv > (i8)0) { rsat = true; break; }
          if (rv == (i8)0) { has_un = true; }
        }
        j = j + 1u;
      }
      if (!rsat && has_un) {
        if ((u64)csz > scap || ncl + 1ULL > scap || tot_lits + (u64)csz > scap ||
            32ULL + 5ULL * (ncl + 1ULL) + tot_lits + (u64)csz > scap) {
          full = true;
        } else {
          scr[32ULL + (ncl << 1)] = (u32)cref;
          scr[32ULL + (ncl << 1) + 1ULL] = 0u;
          ncl = ncl + 1ULL;
          tot_lits = tot_lits + (u64)csz;
        }
      }
    }
    u64 nc = (u64)full_arena_next(h, (u32)cref);
    if (nc <= cref) { break; }
    cref = nc;
  }
  return ((ncl & 0xFFFFFFFFULL) << 32) | (tot_lits & 0xFFFFFFFFULL);
}

u64 full_walk_build_occ_m7(FullHdr *h, u64 ncl) {
  u64 cv = h->cur_vars;
  u64 scap = h->scratch_cap;
  u64 alen = h->arena_len;
  if (cv == 0ULL || cv > h->max_vars || ncl == 0ULL || ncl > scap ||
      32ULL + 5ULL * ncl > scap) {
    return 0ULL;
  }
  u64 two_v = cv << 1;
  u64 sat_base = 32ULL + (ncl << 1);
  u64 upos_base = sat_base + ncl;
  u64 unsat_base = upos_base + ncl;
  u64 occ_base = unsat_base + ncl;
  u64 occ_cap = scap - occ_base;
  i8 *vals = (i8 *)h->values;
  i8 *wvals = (i8 *)h->walk_vals;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach;
  u32 *ws = (u32 *)h->wsort;
  u64 ulen = 0ULL;
  u64 c = 0ULL;
  while (c < ncl) {
    u32 w0 = scr[32ULL + (c << 1)];
    u32 w1 = scr[32ULL + (c << 1) + 1ULL];
    u32 sc = 0u;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 l0 = w0 & PW_LIT_MASK;
      u32 l1 = w1;
      if ((u64)l0 < two_v && vals[l0] == (i8)0) {
        trc[l0] = trc[l0] + 1u;
        if (wvals[l0] > (i8)0) { sc = sc + 1u; }
      }
      if ((u64)l1 < two_v && vals[l1] == (i8)0) {
        trc[l1] = trc[l1] + 1u;
        if (wvals[l1] > (i8)0) { sc = sc + 1u; }
      }
    } else if ((u64)w0 + 3ULL <= alen) {
      u32 csz = ar[(u64)w0 + 2ULL];
      if (csz >= 3u && (u64)w0 + 3ULL + (u64)csz <= alen) {
        u32 j = 0u;
        while (j < csz) {
          u32 lit = ar[(u64)w0 + 3ULL + (u64)j];
          if ((u64)lit < two_v && vals[lit] == (i8)0) {
            trc[lit] = trc[lit] + 1u;
            if (wvals[lit] > (i8)0) { sc = sc + 1u; }
          }
          j = j + 1u;
        }
      }
    }
    scr[sat_base + c] = sc;
    if (sc == 0u && ulen < ncl) {
      scr[upos_base + c] = (u32)ulen;
      scr[unsat_base + ulen] = (u32)c;
      ulen = ulen + 1ULL;
    } else {
      scr[upos_base + c] = 0xFFFFFFFFu;
    }
    c = c + 1ULL;
  }
  u64 off = 0ULL;
  u64 l = 0ULL;
  while (l < two_v) {
    u64 cnt = (u64)trc[l];
    if (off > occ_cap) { off = occ_cap; }
    if (cnt > occ_cap - off) {
      cnt = occ_cap - off;
      trc[l] = (u32)cnt;
    }
    tmk[l] = (u32)off;
    ws[l] = (u32)off;
    off = off + cnt;
    l = l + 1ULL;
  }
  c = 0ULL;
  while (c < ncl) {
    u32 w0 = scr[32ULL + (c << 1)];
    u32 w1 = scr[32ULL + (c << 1) + 1ULL];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 l0 = w0 & PW_LIT_MASK;
      u32 l1 = w1;
      if ((u64)l0 < two_v && vals[l0] == (i8)0) {
        u64 wp = (u64)ws[l0];
        u64 lim = (u64)tmk[l0] + (u64)trc[l0];
        if (wp < lim && occ_base + wp < scap) {
          scr[occ_base + wp] = (u32)c;
          ws[l0] = (u32)(wp + 1ULL);
        }
      }
      if ((u64)l1 < two_v && vals[l1] == (i8)0) {
        u64 wp = (u64)ws[l1];
        u64 lim = (u64)tmk[l1] + (u64)trc[l1];
        if (wp < lim && occ_base + wp < scap) {
          scr[occ_base + wp] = (u32)c;
          ws[l1] = (u32)(wp + 1ULL);
        }
      }
    } else if ((u64)w0 + 3ULL <= alen) {
      u32 csz = ar[(u64)w0 + 2ULL];
      if (csz >= 3u && (u64)w0 + 3ULL + (u64)csz <= alen) {
        u32 j = 0u;
        while (j < csz) {
          u32 lit = ar[(u64)w0 + 3ULL + (u64)j];
          if ((u64)lit < two_v && vals[lit] == (i8)0) {
            u64 wp = (u64)ws[lit];
            u64 lim = (u64)tmk[lit] + (u64)trc[lit];
            if (wp < lim && occ_base + wp < scap) {
              scr[occ_base + wp] = (u32)c;
              ws[lit] = (u32)(wp + 1ULL);
            }
          }
          j = j + 1u;
        }
      }
    }
    c = c + 1ULL;
  }
  return ulen;
}

u32 full_walk_break_m7(FullHdr *h, u32 not_lit, u64 ncl) {
  u64 cv = h->cur_vars;
  u64 scap = h->scratch_cap;
  if (cv == 0ULL || cv > h->max_vars || (u64)not_lit >= (cv << 1) ||
      ncl > scap || 32ULL + 5ULL * ncl > scap) {
    return 0u;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 sat_base = 32ULL + (ncl << 1);
  u64 occ_base = 32ULL + 5ULL * ncl;
  u64 off = (u64)tmk[not_lit];
  u64 len = (u64)trc[not_lit];
  if (off > scap - occ_base) { return 0u; }
  if (len > scap - occ_base - off) { len = scap - occ_base - off; }
  u64 k = 0ULL;
  u32 brk = 0u;
  while (k < len) {
    u32 c = scr[occ_base + off + k];
    if ((u64)c < ncl && scr[sat_base + (u64)c] == 1u) { brk = brk + 1u; }
    k = k + 1ULL;
  }
  return brk;
}

u64 full_walk_pick_m7(FullHdr *h, u32 cl_id, u64 ncl) {
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  u64 scap = h->scratch_cap;
  u64 alen = h->arena_len;
  if (cv == 0ULL || cv > mx || ncl == 0ULL || (u64)cl_id >= ncl ||
      ncl > scap || 32ULL + 5ULL * ncl > scap) {
    return 0xFFFFFFFFULL;
  }
  u64 two_v = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *trc = (u32 *)h->tarjan_reach;
  u32 *wk1 = (u32 *)h->work_stk1;
  u32 *wk2 = (u32 *)h->work_stk2;
  u32 w0 = scr[32ULL + ((u64)cl_id << 1)];
  u32 w1 = scr[32ULL + ((u64)cl_id << 1) + 1ULL];
  if ((w0 & PW_BIN_FLAG) != 0u) {
    u32 l0 = w0 & PW_LIT_MASK;
    u32 l1 = w1;
    bool ok0 = ((u64)l0 < two_v && vals[l0] == (i8)0);
    bool ok1 = ((u64)l1 < two_v && vals[l1] == (i8)0);
    if (!ok0 && !ok1) { return 0xFFFFFFFFULL; }
    if (ok0 && !ok1) { return (u64)l0; }
    if (!ok0 && ok1) { return (u64)l1; }
    u32 b0 = full_walk_break_m7(h, l0 ^ 1u, ncl);
    u32 b1 = full_walk_break_m7(h, l1 ^ 1u, ncl);
    u64 s0 = (u64)scr[(b0 < 31u) ? (u64)b0 : 31ULL];
    u64 s1 = (u64)scr[(b1 < 31u) ? (u64)b1 : 31ULL];
    if (s0 == 0ULL) { s0 = 1ULL; }
    if (s1 == 0ULL) { s1 = 1ULL; }
    if (s0 > 0x40000000ULL) { s0 = 0x40000000ULL; }
    if (s1 > 0x40000000ULL) { s1 = 0x40000000ULL; }
    u64 sum = s0 + s1;
    u64 psteps = (u64)trc[l0 ^ 1u] + (u64)trc[l1 ^ 1u];
    if (psteps > 0xFFFFFFFFULL) { psteps = 0xFFFFFFFFULL; }
    u32 chosen = ((full_rng_next(h) % sum) < s0) ? l0 : l1;
    return (psteps << 32) | (u64)chosen;
  }
  if ((u64)w0 + 3ULL > alen) { return 0xFFFFFFFFULL; }
  u32 csz = ar[(u64)w0 + 2ULL];
  if (csz < 3u || (u64)w0 + 3ULL + (u64)csz > alen) { return 0xFFFFFFFFULL; }
  u64 sum = 0ULL;
  u64 stored = 0ULL;
  u64 cnt = 0ULL;
  u64 psteps = 0ULL;
  u32 tail_i = csz;
  u32 last_lit = 0xFFFFFFFFu;
  u32 j = 0u;
  while (j < csz) {
    u32 lit = ar[(u64)w0 + 3ULL + (u64)j];
    if ((u64)lit < two_v && vals[lit] == (i8)0) {
      u32 nlit = lit ^ 1u;
      u32 b = full_walk_break_m7(h, nlit, ncl);
      u32 sc = scr[(b < 31u) ? (u64)b : 31ULL];
      if (sc == 0u) { sc = 1u; }
      if (sc > 0x40000000u) { sc = 0x40000000u; }
      sum = sum + (u64)sc;
      psteps = psteps + (u64)trc[nlit];
      last_lit = lit;
      cnt = cnt + 1ULL;
      if (stored < mx) {
        wk1[stored] = lit;
        wk2[stored] = sc;
        stored = stored + 1ULL;
      } else if (tail_i == csz) {
        tail_i = j;
      }
    }
    j = j + 1u;
  }
  if (cnt == 0ULL || last_lit == 0xFFFFFFFFu) { return 0xFFFFFFFFULL; }
  if (sum == 0ULL) { sum = 1ULL; }
  u64 target = full_rng_next(h) % sum;
  u64 acc = 0ULL;
  u32 chosen = 0xFFFFFFFFu;
  u64 sidx = 0ULL;
  while (sidx < stored) {
    acc = acc + (u64)wk2[sidx];
    if (acc > target) { chosen = wk1[sidx]; break; }
    sidx = sidx + 1ULL;
  }
  if (chosen == 0xFFFFFFFFu && tail_i < csz) {
    u32 k = tail_i;
    while (k < csz) {
      u32 lit = ar[(u64)w0 + 3ULL + (u64)k];
      if ((u64)lit < two_v && vals[lit] == (i8)0) {
        u32 b = full_walk_break_m7(h, lit ^ 1u, ncl);
        u32 sc = scr[(b < 31u) ? (u64)b : 31ULL];
        if (sc == 0u) { sc = 1u; }
        if (sc > 0x40000000u) { sc = 0x40000000u; }
        acc = acc + (u64)sc;
        if (acc > target) { chosen = lit; break; }
      }
      k = k + 1u;
    }
  }
  if (chosen == 0xFFFFFFFFu) { chosen = last_lit; }
  if (psteps > 0xFFFFFFFFULL) { psteps = 0xFFFFFFFFULL; }
  return (psteps << 32) | (u64)chosen;
}

u64 full_walk_flip_m7(FullHdr *h, u32 flip_lit, u64 ncl, u64 ulen) {
  u64 cv = h->cur_vars;
  u64 scap = h->scratch_cap;
  if (cv == 0ULL || cv > h->max_vars || (u64)flip_lit >= (cv << 1) ||
      ncl == 0ULL || ncl > scap || 32ULL + 5ULL * ncl > scap) {
    return (ulen > ncl) ? ncl : ulen;
  }
  i8 *wvals = (i8 *)h->walk_vals;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach;
  u32 not_lit = flip_lit ^ 1u;
  wvals[flip_lit] = (i8)1;
  wvals[not_lit] = (i8)(-1);
  u64 sat_base = 32ULL + (ncl << 1);
  u64 upos_base = sat_base + ncl;
  u64 unsat_base = upos_base + ncl;
  u64 occ_base = unsat_base + ncl;
  u64 cur_u = (ulen > ncl) ? ncl : ulen;
  u64 off_m = (u64)tmk[flip_lit];
  u64 len_m = (u64)trc[flip_lit];
  if (off_m <= scap - occ_base) {
    if (len_m > scap - occ_base - off_m) { len_m = scap - occ_base - off_m; }
    u64 k = 0ULL;
    while (k < len_m) {
      u32 c = scr[occ_base + off_m + k];
      if ((u64)c < ncl) {
        u32 sc = scr[sat_base + (u64)c];
        scr[sat_base + (u64)c] = sc + 1u;
        if (sc == 0u && cur_u > 0ULL && cur_u <= ncl) {
          u32 pos = scr[upos_base + (u64)c];
          if ((u64)pos < cur_u) {
            u32 last_c = scr[unsat_base + cur_u - 1ULL];
            scr[unsat_base + (u64)pos] = last_c;
            if ((u64)last_c < ncl) { scr[upos_base + (u64)last_c] = pos; }
            scr[upos_base + (u64)c] = 0xFFFFFFFFu;
            cur_u = cur_u - 1ULL;
          }
        }
      }
      k = k + 1ULL;
    }
  }
  u64 off_b = (u64)tmk[not_lit];
  u64 len_b = (u64)trc[not_lit];
  if (off_b <= scap - occ_base) {
    if (len_b > scap - occ_base - off_b) { len_b = scap - occ_base - off_b; }
    u64 k = 0ULL;
    while (k < len_b) {
      u32 c = scr[occ_base + off_b + k];
      if ((u64)c < ncl) {
        u32 sc = scr[sat_base + (u64)c];
        if (sc > 0u) {
          sc = sc - 1u;
          scr[sat_base + (u64)c] = sc;
          if (sc == 0u && cur_u < ncl) {
            scr[upos_base + (u64)c] = (u32)cur_u;
            scr[unsat_base + cur_u] = c;
            cur_u = cur_u + 1ULL;
          }
        }
      }
      k = k + 1ULL;
    }
  }
  u64 fsteps = (u64)trc[flip_lit] + (u64)trc[not_lit];
  if (fsteps > 0xFFFFFFFFULL) { fsteps = 0xFFFFFFFFULL; }
  return (fsteps << 32) | (cur_u & 0xFFFFFFFFULL);
}

void full_walk_save_min_m7(FullHdr *h, u64 best_pos, bool trail_ok) {
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  if (cv == 0ULL || cv > mx) { return; }
  u64 limit = (cv >> 2) + 1ULL;
  i8 *vals = (i8 *)h->values;
  i8 *wbest = (i8 *)h->walk_best;
  i8 *ph = (i8 *)h->phases;
  u32 *fl = (u32 *)h->flags;
  u32 *ws = (u32 *)h->wsort;
  if (trail_ok && best_pos > 0ULL) {
    u64 lim = (best_pos > limit) ? limit : best_pos;
    u64 k = 0ULL;
    while (k < lim) {
      u32 bv = ws[k];
      if ((u64)bv < cv) {
        wbest[bv] = (wbest[bv] < (i8)0) ? (i8)1 : (i8)(-1);
      }
      k = k + 1ULL;
    }
  }
  u64 v = 0ULL;
  while (v < cv) {
    if (vals[v << 1] == (i8)0 && (fl[v] & FL_ACTIVE) != 0u) {
      i8 bv = wbest[v];
      if (bv != (i8)0) { ph[v] = bv; }
    }
    v = v + 1ULL;
  }
}

void full_walk_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  u64 scap = h->scratch_cap;
  if (cv == 0ULL || cv > mx || h->fuel == 0ULL || scap < 64ULL) { return; }
  full_walk_init_vals_m7(h);
  u64 col = full_walk_collect_m7(h);
  u64 ncl = col >> 32;
  u64 tot_lits = col & 0xFFFFFFFFULL;
  if (ncl == 0ULL || ncl > scap || 32ULL + 5ULL * ncl > scap) {
    h->walk_cnt_stat = h->walk_cnt_stat + 1ULL;
    return;
  }
  u64 inv_q16 = full_walk_cb_inv_m7(h, ncl, tot_lits);
  full_walk_init_table_m7(h, inv_q16);
  u64 ulen = full_walk_build_occ_m7(h, ncl);
  u64 max_flips = ncl << 1;
  if (max_flips < 256ULL) { max_flips = 256ULL; }
  if (max_flips > 4096ULL) { max_flips = 4096ULL; }
  u64 step_limit = full_walk_effort_m7(h, max_flips);
  u64 limit = (cv >> 2) + 1ULL;
  u64 two_v = cv << 1;
  u64 unsat_base = 32ULL + 4ULL * ncl;
  i8 *wvals = (i8 *)h->walk_vals;
  i8 *wbest = (i8 *)h->walk_best;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ws = (u32 *)h->wsort;
  u64 tlen = 0ULL;
  u64 best_pos = 0ULL;
  u64 best_u = ulen;
  bool trail_ok = true;
  u64 flips = 0ULL;
  u64 walk_steps = 0ULL;
  while (ulen > 0ULL && ulen <= ncl && flips < max_flips &&
         walk_steps < step_limit && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    u64 upos = flips % ulen;
    u32 cl_id = scr[unsat_base + upos];
    if ((u64)cl_id >= ncl) { break; }
    u64 pk = full_walk_pick_m7(h, cl_id, ncl);
    u32 flip_lit = (u32)(pk & 0xFFFFFFFFULL);
    walk_steps = walk_steps + (pk >> 32) + 1ULL;
    if ((u64)flip_lit >= two_v) { flips = flips + 1ULL; continue; }
    u64 fl_ret = full_walk_flip_m7(h, flip_lit, ncl, ulen);
    ulen = fl_ret & 0xFFFFFFFFULL;
    walk_steps = walk_steps + (fl_ret >> 32);
    u32 fv = flip_lit >> 1;
    if (trail_ok) {
      if (tlen >= limit) {
        if (best_pos > 0ULL && best_pos <= tlen && tlen <= limit) {
          u64 k = 0ULL;
          while (k < best_pos) {
            u32 bv = ws[k];
            if ((u64)bv < cv) { wbest[bv] = (wbest[bv] < (i8)0) ? (i8)1 : (i8)(-1); }
            k = k + 1ULL;
          }
          u64 nlen = tlen - best_pos;
          k = 0ULL;
          while (k < nlen) { ws[k] = ws[best_pos + k]; k = k + 1ULL; }
          tlen = nlen;
          best_pos = 0ULL;
        } else {
          trail_ok = false;
          tlen = 0ULL;
          best_pos = 0ULL;
        }
      }
      if (trail_ok && tlen < limit) {
        ws[tlen] = fv;
        tlen = tlen + 1ULL;
      }
    }
    if (ulen < best_u) {
      best_u = ulen;
      if (trail_ok) {
        best_pos = tlen;
      } else {
        u64 k = 0ULL;
        while (k < cv) { wbest[k] = wvals[k << 1]; k = k + 1ULL; }
        best_pos = 0ULL;
        tlen = 0ULL;
        trail_ok = true;
      }
    }
    flips = flips + 1ULL;
  }
  full_walk_save_min_m7(h, best_pos, trail_ok);
  h->walk_cnt_stat = h->walk_cnt_stat + 1ULL;
}

void full_warmup_m7(FullHdr *h) {
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL || h->inconsistent != 0ULL ||
      h->unassigned == 0ULL || h->oom != 0ULL || h->fuel == 0ULL) {
    return;
  }
  u64 cv = h->cur_vars;
  u64 mx = h->max_vars;
  if (cv == 0ULL || cv > mx) { return; }
  u64 saved_ticks = h->search_ticks;
  u64 saved_prob = h->probing;
  i8 *ph = (i8 *)h->phases;
  i8 *pt = (i8 *)h->phases_target;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  u64 steps = 0ULL;
  while (steps < cv && h->unassigned > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u64 chosen = full_next_dec_var(h);
    if (chosen == 0xFFFFFFFFFFFFFFFFULL) { break; }
    i8 dph = ph[chosen];
    if (h->stable != 0ULL && pt[chosen] != (i8)0) { dph = pt[chosen]; }
    u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
    u64 nlvl = h->cur_level + 1ULL;
    if (nlvl > mx) { break; }
    ftrl[nlvl] = (u32)h->trail_end;
    fdec[nlvl] = lit;
    h->cur_level = nlvl;
    full_assign(h, lit, 0xFFFFFFFFu);
    while (h->propagated < h->trail_end && h->oom == 0ULL && h->fuel > 0ULL) {
      u64 pr = full_propagate(h);
      if (pr == 2ULL) { break; }
    }
    steps = steps + 1ULL;
  }
  h->probing = 1ULL;
  full_backtrack(h, 0ULL);
  h->probing = saved_prob;
  h->search_ticks = saved_ticks;
}

void full_walk_warmup_m7(FullHdr *h) {
  full_warmup_m7(h);
  full_walk_m7(h);
}
"

def m7WalkExterns : List Extern :=
  [ ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_next_dec_var", [i64], [i64]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  ]

def m7WalkFns : List Fn := m7Walk_fns

def m7WalkModule : LeanQbe.T.Module :=
  { fns := m7WalkFns, externs := m7WalkExterns, exits := [] }

theorem full_walk_cb_inv_m7_wf : Func.Wf full_walk_cb_inv_m7_body := by t_wf_reify
theorem full_walk_init_table_m7_wf : Func.Wf full_walk_init_table_m7_body := by t_wf_reify
theorem full_walk_effort_m7_wf : Func.Wf full_walk_effort_m7_body := by t_wf_reify
theorem full_walk_init_vals_m7_wf : Func.Wf full_walk_init_vals_m7_body := by t_wf_reify
theorem full_walk_collect_m7_wf : Func.Wf full_walk_collect_m7_body := by t_wf_reify
theorem full_walk_build_occ_m7_wf : Func.Wf full_walk_build_occ_m7_body := by t_wf_reify
theorem full_walk_break_m7_wf : Func.Wf full_walk_break_m7_body := by t_wf_reify
theorem full_walk_pick_m7_wf : Func.Wf full_walk_pick_m7_body := by t_wf_reify
theorem full_walk_flip_m7_wf : Func.Wf full_walk_flip_m7_body := by t_wf_reify
theorem full_walk_save_min_m7_wf : Func.Wf full_walk_save_min_m7_body := by t_wf_reify
theorem full_walk_m7_wf : Func.Wf full_walk_m7_body := by t_wf_reify
theorem full_warmup_m7_wf : Func.Wf full_warmup_m7_body := by t_wf_reify
theorem full_walk_warmup_m7_wf : Func.Wf full_walk_warmup_m7_body := by t_wf_reify

theorem m7WalkFns_wf : ∀ f ∈ m7WalkFns, f.Wf := by
  simp only [m7WalkFns, m7Walk_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_walk_cb_inv_m7_wf, full_walk_init_table_m7_wf, full_walk_effort_m7_wf,
    full_walk_init_vals_m7_wf, full_walk_collect_m7_wf, full_walk_build_occ_m7_wf,
    full_walk_break_m7_wf, full_walk_pick_m7_wf, full_walk_flip_m7_wf,
    full_walk_save_min_m7_wf, full_walk_m7_wf, full_warmup_m7_wf, full_walk_warmup_m7_wf⟩

theorem m7Walk_acyclic : m7WalkModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7Walk
