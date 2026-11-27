/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 13 Shard S4-A: EVSIDS, LSD Radix Bump Sort, Reorder & Lucky

Data-pure C0 module (`0` `*Proof*` imports) defining the `8` S4-A functions (`2` ADD + `6` MOD)
copied verbatim from frozen `step13_v2_frozen_direct.c`:
- **MOD (`6`):** `full_rescale_m6`, `full_bump_var`, `full_bump_decay`, `full_sort_ana_qs_m6`,
  `full_lucky_scan`, `full_reorder_queue_m7`.
- **ADD (`2`):** `full_bump_analyzed_mode_fid`, `full_restore_bump_ana_mode_fid`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S4A "
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

#define FL_ACTIVE             1u
#define PH_GARB               0x00080000u
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern u64  f64u_add(u64 a, u64 b);
extern u64  f64u_mul(u64 a, u64 b);
extern u64  f64u_div(u64 a, u64 b);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_rescale(FullHdr *h);
extern void full_ana_sift_m6(u32 *qs, u32 *ana, u64 cv, u64 start, u64 n);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_clear_ana(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern bool m6_hdr_dr_allow(FullHdr *h);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern u64  full_lucky_ord_fid(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern u64  full_propagate(FullHdr *h);
extern u64  full_analyze_m6_hdr(FullHdr *h);
extern u32  full_arena_next(FullHdr *h, u32 cref);
extern void full_reorder_sift_fid(FullHdr *h, u64 start, u64 n);

void full_rescale_m6(FullHdr *h) {
  u64 *sc = (u64 *)h->score;
  u64 cv = h->cur_vars;
  u64 mx = 0ULL;
  u64 m = 0ULL;
  while (m < cv) { if (sc[m] > mx) { mx = sc[m]; } m = m + 1ULL; }
  u64 inc = h->scinc;
  u64 rescale = (mx > inc) ? mx : inc;
  u64 factor = f64u_div(0x3FF0000000000000ULL, rescale);
  u64 v = 0ULL;
  while (v < cv) { sc[v] = f64u_mul(sc[v], factor); v = v + 1ULL; }
  h->scinc = f64u_mul(inc, factor);
}

void full_bump_var(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u64 *sc = (u64 *)h->score;
  u64 nsc = f64u_add(sc[v], h->scinc);
  sc[v] = nsc;
  if (h->stable != 0ULL) { full_heap_up(h, v); }
  if (nsc > 0x5F18EA1BD2031214ULL) { full_rescale(h); }
}

void full_bump_decay(FullHdr *h) {
  u64 factor = 0x3FF0D79435E50D79ULL; /* 1.0 / (1.0 - 0.05) */
  u64 ninc = f64u_mul(h->scinc, factor);
  h->scinc = ninc;
  if (ninc > 0x5F18EA1BD2031214ULL) { full_rescale(h); }
}

void full_sort_ana_qs_m6(FullHdr *h, u64 n) {
  if (n <= 1ULL) { return; }
  u64 cv = h->cur_vars;
  if (n > cv) { return; }
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ana = (u32 *)h->work_stk1;
  u64 *rk = (u64 *)h->repr;
  u64 *tmp = (u64 *)h->wsort;
  if (n < 32ULL) {
    u64 i = 0ULL;
    while (i < n) {
      u32 a = ana[i];
      u32 q = ((u64)a < cv) ? qs[a] : 0u;
      rk[i] = ((u64)q << 32) | (u64)a;
      i = i + 1ULL;
    }
    i = 1ULL;
    while (i < n) {
      u64 x = rk[i];
      u64 kx = x >> 32;
      u64 j = i;
      while (j > 0ULL && (rk[j - 1ULL] >> 32) > kx) {
        rk[j] = rk[j - 1ULL];
        j = j - 1ULL;
      }
      rk[j] = x;
      i = i + 1ULL;
    }
    i = 0ULL;
    while (i < n) { ana[i] = (u32)rk[i]; i = i + 1ULL; }
    return;
  }
  if (h->scratch_cap >= 512ULL) {
    u64 i = 0ULL;
    while (i < n) {
      u32 a = ana[i];
      u32 q = ((u64)a < cv) ? qs[a] : 0u;
      rk[i] = ((u64)q << 32) | (u64)a;
      i = i + 1ULL;
    }
    u64 *cnt = (u64 *)h->scratch_buf;
    u64 *s_arr = rk;
    u64 *d_arr = tmp;
    u64 shift = 32ULL;
    while (shift < 64ULL) {
      u64 b = 0ULL;
      while (b < 256ULL) { cnt[b] = 0ULL; b = b + 1ULL; }
      u64 lo = 256ULL;
      u64 hi = 0ULL;
      i = 0ULL;
      while (i < n) {
        u64 bv = (s_arr[i] >> shift) & 255ULL;
        cnt[bv] = cnt[bv] + 1ULL;
        if (bv < lo) { lo = bv; }
        if (bv > hi) { hi = bv; }
        i = i + 1ULL;
      }
      if (lo != hi) {
        u64 pos = 0ULL;
        b = 0ULL;
        while (b < 256ULL) {
          u64 c = cnt[b];
          cnt[b] = pos;
          pos = pos + c;
          b = b + 1ULL;
        }
        i = 0ULL;
        while (i < n) {
          u64 x = s_arr[i];
          u64 bv = (x >> shift) & 255ULL;
          u64 p = cnt[bv];
          cnt[bv] = p + 1ULL;
          d_arr[p] = x;
          i = i + 1ULL;
        }
        u64 *sw = s_arr;
        s_arr = d_arr;
        d_arr = sw;
      }
      shift = shift + 8ULL;
    }
    i = 0ULL;
    while (i < n) { ana[i] = (u32)s_arr[i]; i = i + 1ULL; }
    return;
  }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_ana_sift_m6(qs, ana, cv, start, n);
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u32 t = ana[0]; ana[0] = ana[end]; ana[end] = t;
    full_ana_sift_m6(qs, ana, cv, 0ULL, end);
    end = end - 1ULL;
  }
}

void full_bump_analyzed_mode_fid(FullHdr *h, bool allow_reasons) {
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
  if (allow_reasons && !m6_hdr_delaying(h, 0ULL) && m6_hdr_dr_allow(h)) {
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
          h->search_ticks = h->search_ticks + 1ULL;
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
      m6_hdr_bump_delay(h, 0ULL);
    } else {
      m6_hdr_reduce_delay(h, 0ULL);
    }
  }
  u64 cnt = h->min_clr_len;
  if (h->stable == 0ULL) {
    if (cnt <= cv) { full_sort_ana_qs_m6(h, cnt); }
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      k = k + 1ULL;
    }
  } else {
    u64 k = 0ULL;
    while (k < cnt) {
      u32 bv = ana[k];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      k = k + 1ULL;
    }
    full_bump_decay(h);
  }
}

void full_restore_bump_ana_mode_fid(FullHdr *h, bool allow_reasons) {
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
    full_bump_analyzed_mode_fid(h, allow_reasons);
    full_clear_ana(h);
  }
}

u64 full_lucky_scan(FullHdr *h, bool pos_mode, bool fwd) {
  u64 cv = h->cur_vars;
  u64 n = full_lucky_ord_fid(h);
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u32 *ord = (u32 *)h->tarjan_reach;
  u64 i = 0ULL;
  while (i < n) {
    u64 j = fwd ? i : (n - 1ULL - i);
    u64 v = (u64)ord[j];
    if (v < cv && (fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      h->fuel = h->fuel - 1ULL;
      u32 lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
      full_assign(h, lit, 0xFFFFFFFFu);
      u64 pr = full_propagate(h);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) {
        if (h->cur_level > 1ULL) {
          full_backtrack(h, h->cur_level - 1ULL);
          if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          h->fuel = h->fuel - 1ULL;
          nlvl = h->cur_level + 1ULL;
          if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
          ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
          full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
          u64 pr2 = full_propagate(h);
          if (pr2 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          if (pr2 == 1ULL) { full_backtrack(h, 0ULL); return 0ULL; }
        } else {
          u64 ast = full_analyze_m6_hdr(h);
          if (ast == 20ULL) { return 20ULL; }
          if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          u64 pr3 = full_propagate(h);
          if (pr3 == 1ULL) { return 20ULL; }
          if (pr3 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
        }
      }
    }
    i = i + 1ULL;
  }
  return 10ULL;
}

u64 full_reorder_queue_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u64 alen = h->arena_len;
  u64 wlen = h->wlen;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u64 *wl = (u64 *)h->tarjan_mark;
  u64 *wr = (u64 *)h->tarjan_reach;
  u64 w2 = 0x3FF0000000000000ULL;
  u64 z = 0ULL;
  while (z < cv) {
    wl[z] = 0ULL;
    wr[z] = 0ULL;
    z = z + 1ULL;
  }
  u64 p = 0ULL;
  while (p < alen) {
    if (p + 3ULL > alen) { break; }
    u32 hdr = ar[p];
    u32 csz = ar[p + 2ULL];
    u64 clen = (u64)csz;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && clen <= alen - (p + 3ULL)) {
      bool sat = false;
      u64 sz = 0ULL;
      u64 ci = 0ULL;
      while (ci < clen) {
        u32 lit = ar[p + 3ULL + ci];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) { sz = sz + 1ULL; }
        }
        ci = ci + 1ULL;
      }
      if (!sat && sz >= 2ULL) {
        if (sz > 100ULL) { sz = 100ULL; }
        u64 w = (1025ULL - sz) << 52;
        ci = 0ULL;
        while (ci < clen) {
          u32 lit = ar[p + 3ULL + ci];
          if ((u64)lit < nlits) {
            u32 av = lit >> 1;
            if ((lit & 1u) == 0u) { wl[av] = f64u_add(wl[av], w); }
            else { wr[av] = f64u_add(wr[av], w); }
          }
          ci = ci + 1ULL;
        }
      }
    }
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (np <= p) { break; }
    p = np;
  }
  u64 lit = 0ULL;
  while (lit < nlits) {
    u64 lvar = lit >> 1;
    if ((fl[lvar] & FL_ACTIVE) != 0u && vals[lit] == (i8)0) {
      u64 off = (u64)wvec[lit << 1];
      u64 wsz = (u64)wvec[(lit << 1) + 1ULL];
      if (wsz > 0ULL && off < wlen && wsz <= wlen - off) {
        u64 wp = off;
        u64 wend = off + wsz;
        while (wp < wend) {
          u32 w0 = wstk[wp];
          if ((w0 & PW_BIN_FLAG) == 0u) {
            if (wp + 1ULL < wend) { wp = wp + 2ULL; continue; }
            break;
          }
          u32 other = w0 & PW_LIT_MASK;
          if ((u64)other > lit && (u64)other < nlits) {
            u64 ov = (u64)(other >> 1);
            if ((fl[ov] & FL_ACTIVE) != 0u && vals[other] == (i8)0) {
              if ((lit & 1ULL) == 0ULL) { wl[lvar] = f64u_add(wl[lvar], w2); }
              else { wr[lvar] = f64u_add(wr[lvar], w2); }
              if ((other & 1u) == 0u) { wl[ov] = f64u_add(wl[ov], w2); }
              else { wr[ov] = f64u_add(wr[ov], w2); }
            }
          }
          wp = wp + 1ULL;
        }
      }
    }
    lit = lit + 1ULL;
  }
  u64 fv = 0ULL;
  while (fv < cv) {
    u64 a = wl[fv];
    u64 b = wr[fv];
    wl[fv] = (a >= b) ? f64u_add(a, f64u_mul(b, 0x4000000000000000ULL))
                      : f64u_add(b, f64u_mul(a, 0x4000000000000000ULL));
    fv = fv + 1ULL;
  }
  if (h->stable != 0ULL) {
    full_rescale(h);
    u64 *sc = (u64 *)h->score;
    u64 n_s = 0ULL;
    u64 sv = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u) { ws[n_s] = (u32)sv; n_s = n_s + 1ULL; }
      sv = sv + 1ULL;
    }
    if (n_s > 1ULL) {
      u64 s = n_s >> 1;
      while (s > 0ULL) {
        s = s - 1ULL;
        u64 root = s;
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= n_s) { break; }
          u64 best = root;
          u32 bv = ws[best]; u64 bw = wl[bv]; u64 bs = sc[bv];
          u32 cv1 = ws[ch]; u64 cw = wl[cv1]; u64 cs = sc[cv1];
          if (cw > bw || (cw == bw && (cs > bs || (cs == bs && cv1 < bv)))) {
            best = ch; bv = cv1; bw = cw; bs = cs;
          }
          u64 rch = ch + 1ULL;
          if (rch < n_s) {
            u32 rv1 = ws[rch]; u64 rw = wl[rv1]; u64 rs = sc[rv1];
            if (rw > bw || (rw == bw && (rs > bs || (rs == bs && rv1 < bv)))) {
              best = rch; bv = rv1;
            }
          }
          if (best == root) { break; }
          u32 t = ws[root]; ws[root] = bv; ws[best] = t;
          root = best;
        }
      }
      u64 e = n_s;
      while (e > 1ULL) {
        e = e - 1ULL;
        u32 sw = ws[0]; ws[0] = ws[e]; ws[e] = sw;
        u64 root = 0ULL;
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= e) { break; }
          u64 best = root;
          u32 bv = ws[best]; u64 bw = wl[bv]; u64 bs = sc[bv];
          u32 cv1 = ws[ch]; u64 cw = wl[cv1]; u64 cs = sc[cv1];
          if (cw > bw || (cw == bw && (cs > bs || (cs == bs && cv1 < bv)))) {
            best = ch; bv = cv1; bw = cw; bs = cs;
          }
          u64 rch = ch + 1ULL;
          if (rch < e) {
            u32 rv1 = ws[rch]; u64 rw = wl[rv1]; u64 rs = sc[rv1];
            if (rw > bw || (rw == bw && (rs > bs || (rs == bs && rv1 < bv)))) {
              best = rch; bv = rv1;
            }
          }
          if (best == root) { break; }
          u32 t = ws[root]; ws[root] = bv; ws[best] = t;
          root = best;
        }
      }
    }
    u64 rem_s = n_s;
    while (rem_s > 0ULL) {
      rem_s = rem_s - 1ULL;
      u32 idx = ws[rem_s];
      sc[idx] = f64u_add(sc[idx], wl[idx]);
      full_heap_up(h, idx);
    }
    return n_s;
  }
  u64 n = 0ULL;
  u64 av = 0ULL;
  while (av < cv) {
    if ((fl[av] & FL_ACTIVE) != 0u) { ws[n] = (u32)av; n = n + 1ULL; }
    av = av + 1ULL;
  }
  if (n > 1ULL) {
    u64 s = n >> 1;
    while (s > 0ULL) {
      s = s - 1ULL;
      full_reorder_sift_fid(h, s, n);
    }
    u64 e = n;
    while (e > 1ULL) {
      e = e - 1ULL;
      u32 tmp = ws[0];
      ws[0] = ws[e];
      ws[e] = tmp;
      full_reorder_sift_fid(h, 0ULL, e);
    }
  }
  u64 rv = 0ULL;
  while (rv < cv) {
    qp[rv] = 0xFFFFFFFFu;
    qn[rv] = 0xFFFFFFFFu;
    qs[rv] = 0u;
    rv = rv + 1ULL;
  }
  if (n == 0ULL) {
    h->q_first = 0xFFFFFFFFULL;
    h->q_last = 0xFFFFFFFFULL;
    h->q_search_idx = 0xFFFFFFFFULL;
    h->q_cur_stamp = 0ULL;
    h->q_search_stamp = 0ULL;
    return 0ULL;
  }
  u64 sidx = 0xFFFFFFFFULL;
  u64 sstamp = 0ULL;
  u64 qi = 0ULL;
  while (qi < n) {
    u32 cur = ws[qi];
    qp[cur] = (qi > 0ULL) ? ws[qi - 1ULL] : 0xFFFFFFFFu;
    qn[cur] = (qi + 1ULL < n) ? ws[qi + 1ULL] : 0xFFFFFFFFu;
    qs[cur] = (u32)(qi + 1ULL);
    if (vals[(u64)cur << 1] == (i8)0) { sidx = (u64)cur; sstamp = qi + 1ULL; }
    qi = qi + 1ULL;
  }
  h->q_first = (u64)ws[0];
  h->q_last = (u64)ws[n - 1ULL];
  h->q_cur_stamp = n;
  if (sidx >= cv) { sidx = (u64)ws[n - 1ULL]; sstamp = n; }
  h->q_search_idx = sidx;
  h->q_search_stamp = sstamp;
  return n;
}
"

/-! ## 1. Drop-In `Fn` Handles, Replacement & Insertion Lists -/

/-- `full_rescale_m6` replacement (Step-13 `f64u` max-score rescaling). -/
def fidStep13S4RescaleM6Fn : Fn :=
  ⟨"full_rescale_m6", [i64], [], full_rescale_m6_body⟩

/-- `full_bump_var` replacement (Step-13 `f64u_add` score bump). -/
def fidStep13S4BumpVarFn : Fn :=
  ⟨"full_bump_var", [i64, i32], [], full_bump_var_body⟩

/-- `full_bump_decay` replacement (Step-13 `f64u_mul` decay factor). -/
def fidStep13S4BumpDecayFn : Fn :=
  ⟨"full_bump_decay", [i64], [], full_bump_decay_body⟩

/-- `full_sort_ana_qs_m6` replacement (`PERF-R3` insertion + LSD radix + heapsort fallback). -/
def fidStep13S4SortAnaQsM6Fn : Fn :=
  ⟨"full_sort_ana_qs_m6", [i64, i64], [], full_sort_ana_qs_m6_body⟩

/-- `full_bump_analyzed_mode_fid` inserted helper (mode-gated reason bumping). -/
def fidStep13S4BumpAnalyzedModeFidFn : Fn :=
  ⟨"full_bump_analyzed_mode_fid", [i64, .bool], [], full_bump_analyzed_mode_fid_body⟩

/-- `full_restore_bump_ana_mode_fid` inserted helper (mode-gated restore & bump). -/
def fidStep13S4RestoreBumpAnaModeFidFn : Fn :=
  ⟨"full_restore_bump_ana_mode_fid", [i64, .bool], [], full_restore_bump_ana_mode_fid_body⟩

/-- `full_lucky_scan` replacement (Step-13 calls `full_analyze_m6_hdr`). -/
def fidStep13S4LuckyScanFn : Fn :=
  ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], full_lucky_scan_body⟩

/-- `full_reorder_queue_m7` replacement (Step-13 `f64u` clause weights & stable-mode reorder). -/
def fidStep13S4ReorderQueueM7Fn : Fn :=
  ⟨"full_reorder_queue_m7", [i64], [i64], full_reorder_queue_m7_body⟩

/-- Ordered list of the `6` S4-A replacement functions (`0` ABI changes). -/
def fidStep13S4ARepls : List Fn :=
  [ fidStep13S4RescaleM6Fn
  , fidStep13S4BumpVarFn
  , fidStep13S4BumpDecayFn
  , fidStep13S4SortAnaQsM6Fn
  , fidStep13S4LuckyScanFn
  , fidStep13S4ReorderQueueM7Fn ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem fidStep13S4RescaleM6_wf : Func.Wf fidStep13S4RescaleM6Fn.body := by t_wf_reify
theorem fidStep13S4BumpVar_wf : Func.Wf fidStep13S4BumpVarFn.body := by t_wf_reify
theorem fidStep13S4BumpDecay_wf : Func.Wf fidStep13S4BumpDecayFn.body := by t_wf_reify
theorem fidStep13S4SortAnaQsM6_wf : Func.Wf fidStep13S4SortAnaQsM6Fn.body := by t_wf_reify
theorem fidStep13S4BumpAnalyzedModeFid_wf :
    Func.Wf fidStep13S4BumpAnalyzedModeFidFn.body := by t_wf_reify
theorem fidStep13S4RestoreBumpAnaModeFid_wf :
    Func.Wf fidStep13S4RestoreBumpAnaModeFidFn.body := by t_wf_reify
theorem fidStep13S4LuckyScan_wf : Func.Wf fidStep13S4LuckyScanFn.body := by t_wf_reify
theorem fidStep13S4ReorderQueueM7_wf : Func.Wf fidStep13S4ReorderQueueM7Fn.body := by t_wf_reify

theorem fidStep13S4ARepls_wf : ∀ f ∈ fidStep13S4ARepls, f.Wf := by
  intro f hf
  simp only [fidStep13S4ARepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S4RescaleM6_wf
  · exact fidStep13S4BumpVar_wf
  · exact fidStep13S4BumpDecay_wf
  · exact fidStep13S4SortAnaQsM6_wf
  · exact fidStep13S4LuckyScan_wf
  · exact fidStep13S4ReorderQueueM7_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
