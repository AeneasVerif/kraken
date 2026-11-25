/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Upstream 4.0.4 `factor.c` (BVA) Parity (`FullFidelityBva`)

Purely additive C0 drop-in upgrade closing all three upstream Kissat 4.0.4 `src/factor.c` BVA
algorithmic fidelity gaps (`GAP-BVA-01`, `GAP-BVA-02`, `GAP-BVA-03`) with `0` edits to existing
`FullM8*`/`FullM7*` files, `0` `FullHdr` word growth, `0` `M6HdrExt` slot usage, and strictly
zero beyond-upstream heuristics (no 3-hop BFS tie-breaking, no CaDiCaL-FX):

1. **`GAP-BVA-02` (`factorcandrounds = 2` candidate literal peeling, `factor.c:957-1066`):**
   `full_bva_connect_clauses_fid` flushes all dense large watches via `full_fwd_flush_large_m7`,
   counts active binary degrees (`tarjan_mark`) and candidate irredundant `3..5`-lit clause
   degrees (`work_stk1`), runs up to `2` peeling rounds discarding clauses containing any literal
   with `bincount[l] + largecount[l] < 2`, connects only surviving candidates, and records exact
   clause-count watch degrees (`SIZE_WATCHES = num_bin + num_large`) in `h->repr`.
2. **`GAP-BVA-01` (dynamic scratch-scaled factoring matrix & exact `next_factor` priority):**
   `full_bva_steps_cap_fid` scales `sc ∈ {256, 64, 32, 8, 0}` dynamically from `h->scratch_cap`
   (gracefully returning `0` on tiny `scratch_cap < 64` fixtures such as `8,192 B` NV workspaces,
   and packing ragged rows/parent arrays contiguously inside `scratch_buf[4*sc .. scratch_cap)`
   instead of a fixed `256 x 32` table). `full_bva_pick_cand_fid` uses strict upstream
   `factorstructural = 0` `watches_score = deg[lit]` with strict `>` first-seen tie-breaking
   (`factor.c:310-323, 478`). `full_factor_fid` maintains exact-degree `fheap` with upstream
   `update_candidate` removal (`deg[tl] <= 1`) and rescheduling of touched literals up to
   `h->cur_vars << 1`.
3. **`GAP-BVA-03` (upstream `factor.c:1106-1116` tick budget calibration):**
   `full_probe_m6_fid` fixes `factordelay = 4` (`fr <= eliminations + 4` with `unassigned > 0`),
   removes the artificial `<= 8192` budget truncation, and supplies upstream tick budgets
   `initial ? 700_000_000 : (dticks / 20)` (`factoriniticks = 700M`, `factoreffort = 50/1000`).
   `full_bva_scan_cands_fid`, `full_bva_filter_row_fid`, and `full_bva_try_lit_fid` account
   upstream `factor_ticks` (`1 + kissat_cache_lines(n, 4)` + clause derefs) against `h->ant_sz`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fidBva "
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
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u
#define FL_SWEEP              1024u
#define PH_GARB               0x00080000u
#define PH_RED                0x00400000u
#define PH_BVA_Q              0x02000000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_WM_PROBE_TICKS     0ULL

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_fwd_flush_large_m7(FullHdr *h);
extern void full_init_fresh_var(FullHdr *h, u32 fv);

extern u64 full_probe_dticks_m6_hdr(FullHdr *h, bool initial);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_scale_delta_m5(FullHdr *h, u64 delta);
extern u64 full_vivify_m6_hdr(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern bool m6_hdr_delaying(FullHdr *h, u64 kind);
extern u64 full_congruence_dense(FullHdr *h, u64 tick_lim);
extern u64 full_rebuild_watches(FullHdr *h);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 kind);
extern void m6_hdr_bump_delay(FullHdr *h, u64 kind);
extern u64 full_sweep_dense_m6(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_substitute(FullHdr *h);
extern u64 full_probe_tail_m6(FullHdr *h, u64 dticks);
extern u64 full_backbone_m6(FullHdr *h, u64 tick_lim);

u32 full_bva_steps_cap_fid(u64 cap) {
  if (cap >= 8192ULL) { return 256u; }
  if (cap >= 1024ULL) { return 64u; }
  if (cap >= 256ULL) { return 32u; }
  if (cap >= 64ULL) { return 8u; }
  return 0u;
}

u64 full_bva_clines_fid(u64 n) {
  if (n == 0ULL) { return 0ULL; }
  return (n + 31ULL) >> 5;
}

void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p) {
  u32 l = hp[p];
  u32 d = deg[l];
  while (p > 0u) {
    u32 par = (p - 1u) >> 1;
    u32 pl = hp[par];
    if (deg[pl] >= d) { break; }
    hp[p] = pl;
    ps[pl] = p;
    p = par;
  }
  hp[p] = l;
  ps[l] = p;
}

void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n) {
  u32 l = hp[p];
  u32 d = deg[l];
  while (true) {
    u32 lc = (p << 1) + 1u;
    if (lc >= n) { break; }
    u32 best = lc;
    u32 bd = deg[hp[lc]];
    u32 rc = lc + 1u;
    if (rc < n) {
      u32 rd = deg[hp[rc]];
      if (rd > bd) { best = rc; bd = rd; }
    }
    if (d >= bd) { break; }
    u32 bl = hp[best];
    hp[p] = bl;
    ps[bl] = p;
    p = best;
  }
  hp[p] = l;
  ps[l] = p;
}

u32 full_bva_count_lit_deg_fid(FullHdr *h, u32 lit) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 p = off;
  u32 cnt = 0u;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      cnt = cnt + 1u;
    } else if (p < end) {
      p = p + 1ULL;
      cnt = cnt + 1u;
    }
  }
  return cnt;
}

void full_bva_connect_clauses_fid(FullHdr *h) {
  full_fwd_flush_large_m7(h);
  u64 nlits = h->cur_vars << 1;
  u32 *bc = (u32 *)h->tarjan_mark;
  u32 *lc = (u32 *)h->work_stk1;
  u32 *nlc = (u32 *)h->work_stk2;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *deg = (u32 *)h->repr;
  u64 i = 0ULL;
  while (i < nlits) {
    bc[i] = 0u;
    lc[i] = 0u;
    i = i + 1ULL;
  }
  i = 0ULL;
  while (i < nlits) {
    if ((fl[i >> 1] & FL_ACTIVE) != 0u && vals[i] == (i8)0) {
      u64 off = (u64)wvec[i << 1];
      u64 end = off + (u64)wvec[(i << 1) + 1ULL];
      u64 p = off;
      u32 bcnt = 0u;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 other = w0 & PW_LIT_MASK;
          if (vals[other] == (i8)0 && (fl[other >> 1] & FL_ACTIVE) != 0u) {
            if (bcnt < 0xFFFFFFFFu) { bcnt = bcnt + 1u; }
          }
        } else if (p < end) {
          p = p + 1ULL;
        }
      }
      bc[i] = bcnt;
    }
    i = i + 1ULL;
  }
  u64 cands = 0ULL;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
      bool sat = false;
      u32 k = 0u;
      while (k < sz) {
        if (vals[ar[p + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
        k = k + 1u;
      }
      if (!sat) {
        k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (lc[l] < 0xFFFFFFFFu) { lc[l] = lc[l] + 1u; }
          k = k + 1u;
        }
        cands = cands + 1ULL;
      }
    }
    p = np;
  }
  u32 rnd = 0u;
  while (rnd < 2u && cands > 0ULL) {
    i = 0ULL;
    while (i < nlits) { nlc[i] = 0u; i = i + 1ULL; }
    u64 ncands = 0ULL;
    p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
        bool keep = true;
        u32 k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (vals[l] > (i8)0 || (u64)bc[l] + (u64)lc[l] < 2ULL) {
            keep = false; break;
          }
          k = k + 1u;
        }
        if (keep) {
          k = 0u;
          while (k < sz) {
            u32 l = ar[p + 3ULL + (u64)k];
            if (nlc[l] < 0xFFFFFFFFu) { nlc[l] = nlc[l] + 1u; }
            k = k + 1u;
          }
          ncands = ncands + 1ULL;
        }
      }
      p = np;
    }
    i = 0ULL;
    while (i < nlits) { lc[i] = nlc[i]; i = i + 1ULL; }
    if (ncands == cands) { break; }
    cands = ncands;
    rnd = rnd + 1u;
  }
  p = 0ULL;
  while (p < h->arena_len && h->oom == 0ULL) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
      bool keep = true;
      u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        if (vals[l] > (i8)0 || (u64)bc[l] + (u64)lc[l] < 2ULL) {
          keep = false; break;
        }
        k = k + 1u;
      }
      if (keep) {
        k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if (!full_watch_push(h, l, sz & PW_LIT_MASK, (u32)p, 2u)) {
            h->oom = 1ULL;
            break;
          }
          k = k + 1u;
        }
      }
    }
    p = np;
  }
  u64 dl = 0ULL;
  while (dl < nlits) {
    deg[dl] = full_bva_count_lit_deg_fid(h, (u32)dl);
    dl = dl + 1ULL;
  }
}

bool full_bva_match_large_bva_fid(FullHdr *h, u32 cur_cr, u32 next_lit, u32 d_ref) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark;
  u32 sz = ar[(u64)cur_cr + 2ULL];
  if (ar[(u64)d_ref + 2ULL] != sz || (ar[d_ref] & (PH_GARB | PH_RED | PH_BVA_Q)) != 0u) {
    return false;
  }
  u32 j = 0u; bool seen_next = false;
  while (j < sz) {
    u32 dl = ar[(u64)d_ref + 3ULL + (u64)j];
    if ((lm[dl] & (u8)2) == (u8)0) {
      if (dl == next_lit && !seen_next) { seen_next = true; } else { return false; }
    }
    j = j + 1u;
  }
  return seen_next;
}

u32 full_bva_scan_cands(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits) {
  i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *cntd = (u32 *)h->work_stk1;
  u32 *fl = (u32 *)h->flags; u32 *ql = (u32 *)h->work_stk2;
  u32 *deg = (u32 *)h->repr;
  u32 nql = 0u; u32 ncntd = 0u; u32 qi = 0u;
  u64 ticks = 1ULL + full_bva_clines_fid((u64)cur_qn);
  while (qi < cur_qn) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1];
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      u64 qend = qoff + qsz;
      ticks = ticks + 1ULL + full_bva_clines_fid((u64)deg[q]);
      u64 qp = qoff;
      while (qp < qend) {
        u32 nw = wstk[qp];
        if ((nw & PW_BIN_FLAG) != 0u) {
          u32 cand = nw & PW_LIT_MASK;
          if ((u64)cand < init_lits && (lm[cand] & (u8)1) == (u8)0 &&
              (fl[cand >> 1] & FL_ACTIVE) != 0u && vals[cand] == (i8)0) {
            if (cnt[cand] == 0u) {
              if ((u64)ncntd < init_lits) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
            }
            if (cnt[cand] < 0xFFFFFFFFu) { cnt[cand] = cnt[cand] + 1u; }
          }
          qp = qp + 1ULL;
        } else { qp = qp + 2ULL; }
      }
    } else {
      u32 csz = ar[(u64)qw + 2ULL]; u32 min_l = 0xFFFFFFFFu; u32 min_d = 0xFFFFFFFFu;
      u32 fc = 0u; u32 j = 0u;
      ticks = ticks + 1ULL;
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) != (u8)0) { fc = fc + 1u; if (fc > 1u) { break; } }
        else {
          lm[l] = lm[l] | (u8)2;
          u32 d = deg[l];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (fc == 1u && min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1];
        u64 msz = (u64)wvec[((u64)min_l << 1) + 1ULL];
        u64 mend = moff + msz; u64 mp = moff;
        u64 mxv = h->max_vars; u32 nnou = 0u;
        ticks = ticks + 1ULL + full_bva_clines_fid((u64)min_d);
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr == qw) { continue; }
          ticks = ticks + 1ULL;
          if ((ar[dr] & (PH_GARB | PH_RED | PH_BVA_Q)) != 0u ||
              ar[(u64)dr + 2ULL] != csz) { continue; }
          u32 cand = 0xFFFFFFFFu; bool ok = true; u32 dj = 0u;
          while (dj < csz) {
            u32 dl = ar[(u64)dr + 3ULL + (u64)dj]; u8 m = lm[dl];
            if ((m & (u8)2) == (u8)0) {
              if ((m & (u8)5) != (u8)0 || cand != 0xFFFFFFFFu) { ok = false; break; }
              cand = dl;
            }
            dj = dj + 1u;
          }
          if (ok && cand != 0xFFFFFFFFu && (u64)cand < init_lits &&
              (fl[cand >> 1] & FL_ACTIVE) != 0u && vals[cand] == (i8)0) {
            if ((u64)nnou < mxv) {
              lm[cand] = lm[cand] | (u8)4;
              ql[mxv + (u64)nnou] = cand;
              nnou = nnou + 1u;
            }
            if ((u64)nql < mxv) {
              ar[dr] = ar[dr] | PH_BVA_Q;
              ql[nql] = dr;
              nql = nql + 1u;
            }
            if (cnt[cand] == 0u) {
              if ((u64)ncntd < init_lits) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
            }
            if (cnt[cand] < 0xFFFFFFFFu) { cnt[cand] = cnt[cand] + 1u; }
          }
        }
        j = 0u;
        while (j < nnou) {
          u32 cl = ql[mxv + (u64)j]; lm[cl] = lm[cl] & (u8)0xFB; j = j + 1u;
        }
      }
      j = 0u;
      while (j < csz) {
        u32 cj = ar[(u64)qw + 3ULL + (u64)j]; lm[cj] = lm[cj] & (u8)0xFD; j = j + 1u;
      }
    }
    h->ant_sz = (h->ant_sz > ticks) ? (h->ant_sz - ticks) : 0ULL;
    ticks = 0ULL;
    if (h->ant_sz == 0ULL) { break; }
    qi = qi + 1u;
  }
  u32 ci = 0u; while (ci < nql) { ar[ql[ci]] = ar[ql[ci]] & (~PH_BVA_Q); ci = ci + 1u; }
  return ncntd;
}

u32 full_bva_pick_cand(FullHdr *h, u32 ncntd, u32 f0) {
  u32 *deg = (u32 *)h->repr;
  u32 *cnt = (u32 *)h->wsort;
  u32 *cntd = (u32 *)h->work_stk1;
  u32 best_c = 0u;
  u32 best_deg = 0u;
  u32 best_lit = 0xFFFFFFFFu;
  u32 ci = 0u;
  while (ci < ncntd) {
    u32 clit = cntd[ci];
    u32 cc = cnt[clit];
    if (cc >= 2u) {
      if (cc > best_c) {
        best_c = cc;
        best_deg = deg[clit];
        best_lit = clit;
      } else if (cc == best_c) {
        u32 d = deg[clit];
        if (d > best_deg) {
          best_deg = d;
          best_lit = clit;
        }
      }
    }
    ci = ci + 1u;
  }
  ci = 0u;
  while (ci < ncntd) {
    cnt[cntd[ci]] = 0u;
    ci = ci + 1u;
  }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}

u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
                        u32 cur_qn, u32 best_lit) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 *deg = (u32 *)h->repr;
  u32 max_new = par_off - nrow_off;
  u32 new_qn = 0u; u32 qi = 0u;
  u64 ticks = 1ULL + full_bva_clines_fid((u64)cur_qn);
  while (qi < cur_qn && new_qn < max_new) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1];
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      u64 qend = qoff + qsz;
      ticks = ticks + 1ULL + full_bva_clines_fid((u64)deg[q]);
      u64 qp = qoff;
      while (qp < qend) {
        u32 nw = wstk[qp];
        if ((nw & PW_BIN_FLAG) != 0u) {
          if ((nw & PW_LIT_MASK) == best_lit) {
            scr[nrow_off + new_qn] = qw; scr[par_off + new_qn] = qi;
            new_qn = new_qn + 1u; break;
          }
          qp = qp + 1ULL;
        } else { qp = qp + 2ULL; }
      }
    } else {
      u32 csz = ar[(u64)qw + 2ULL]; u32 min_l = 0xFFFFFFFFu; u32 min_d = 0xFFFFFFFFu;
      u32 fc = 0u; u32 j = 0u;
      ticks = ticks + 1ULL;
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) != (u8)0) {
          fc = fc + 1u; if (fc > 1u) { break; }
        } else {
          lm[l] = lm[l] | (u8)2;
          u32 d = deg[l];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (fc == 1u && min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1];
        u64 msz = (u64)wvec[((u64)min_l << 1) + 1ULL];
        u64 mend = moff + msz; u64 mp = moff;
        ticks = ticks + 1ULL + full_bva_clines_fid((u64)min_d);
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr == qw) { continue; }
          ticks = ticks + 1ULL;
          if (full_bva_match_large_bva_fid(h, qw, best_lit, dr)) {
            ar[dr] = ar[dr] | PH_BVA_Q;
            scr[nrow_off + new_qn] = dr; scr[par_off + new_qn] = qi;
            new_qn = new_qn + 1u; break;
          }
        }
      }
      j = 0u;
      while (j < csz) {
        u32 cj = ar[(u64)qw + 3ULL + (u64)j]; lm[cj] = lm[cj] & (u8)0xFD; j = j + 1u;
      }
    }
    qi = qi + 1u;
  }
  u32 ci = 0u;
  while (ci < new_qn) {
    u32 e = scr[nrow_off + ci];
    if ((e & PW_BIN_FLAG) == 0u) { ar[e] = ar[e] & (~PH_BVA_Q); }
    ci = ci + 1u;
  }
  h->ant_sz = (h->ant_sz > ticks) ? (h->ant_sz - ticks) : 0ULL;
  return new_qn;
}

bool full_bva_commit(FullHdr *h, u32 best_k) {
  if (h->oom != 0ULL) { return false; }
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (sc == 0u || best_k >= sc) { return false; }
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 dm = best_k + 1u;
  u32 brow_off = scr[sc + best_k];
  u32 mn = scr[2u * sc + best_k];
  u64 need_ar = 16ULL;
  u64 need_w = (((u64)dm + (u64)mn + 8ULL) << 3);
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 fsz = (u64)wvec[((u64)fs << 1) + 1ULL];
    need_w = need_w + (fsz << 1) + 2ULL;
    si = si + 1u;
  }
  u32 m = 0u;
  while (m < mn) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      need_w = need_w + (qsz << 1) + 2ULL;
    } else {
      u32 csz = ar[(u64)c_top + 2ULL];
      need_ar = need_ar + 3ULL + (u64)csz;
      u32 flit = scr[best_k]; u32 j = 0u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) {
          u64 lsz = (u64)wvec[((u64)l << 1) + 1ULL];
          need_w = need_w + (lsz << 1) + 2ULL;
        }
        j = j + 1u;
      }
    }
    m = m + 1u;
  }
  if (h->cur_vars >= h->max_vars || h->arena_cap < h->arena_len ||
      h->arena_cap - h->arena_len < need_ar) { return false; }
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u32 *deg = (u32 *)h->repr;
  deg[fv << 1] = 0u; deg[(fv << 1) | 1u] = 0u;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  bool ok = true;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | FL_FACT_P | FL_FACT_N;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u64 br = full_add_bin(h, fresh ^ 1u, c_top & PW_LIT_MASK);
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      j = 0u; while (j < tk) { ar[ncr + 3ULL + (u64)j] = tmp[j]; j = j + 1u; }
      j = 0u;
      while (j < tk) {
        if (!full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u)) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        j = j + 1u;
      }
      if (ok) { h->num_irred = h->num_irred + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
    while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
    return false;
  }
  m = 0u;
  while (m < mn) {
    u32 idx = m;
    u32 s = best_k;
    while (true) {
      u32 ro = scr[sc + s];
      u32 cs = scr[ro + idx]; u32 fs = scr[s];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
        fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          fl[dl >> 1] = fl[dl >> 1] | (((dl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      if (s == 0u) { break; }
      u32 po = scr[3u * sc + s];
      idx = scr[po + idx]; s = s - 1u;
    }
    m = m + 1u;
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv) {
  u64 cap = h->scratch_cap;
  u32 sc = full_bva_steps_cap_fid(cap);
  if (h->cur_vars >= h->max_vars || sc == 0u) { return false; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  u8 *counted = (u8 *)h->lit_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  u64 init_lits = (init_cv <= h->cur_vars) ? (init_cv << 1) : (h->cur_vars << 1);
  u32 hdr_sz = sc << 2;
  u32 row0_max = (u32)((cap - (u64)hdr_sz) / 3ULL);
  if (row0_max < 2u) { return false; }
  u64 off0 = (u64)wvec[(u64)f0 << 1];
  u64 sz0 = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 wi = 0ULL;
  u32 r0n = 0u;
  u64 fticks = 0ULL;
  while (wi < sz0 && r0n < row0_max) {
    u32 w0 = wstk[off0 + wi]; wi = wi + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      fticks = fticks + 1ULL;
      u32 other = w0 & PW_LIT_MASK;
      if (vals[other] == (i8)0) {
        scr[hdr_sz + r0n] = w0;
        r0n = r0n + 1u;
      }
    } else if (wi < sz0) {
      u32 cr = wstk[off0 + wi]; wi = wi + 1ULL;
      fticks = fticks + 1ULL;
      u32 csz = arena[(u64)cr + 2ULL];
      u32 cfl = arena[(u64)cr];
      if ((cfl & (PH_GARB | PH_RED)) == 0u && csz >= 3u && csz <= 5u) {
        u32 j = 0u; bool has_f0 = false; bool sat = false;
        while (j < csz) {
          u32 l = arena[(u64)cr + 3ULL + (u64)j];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (l == f0) { has_f0 = true; }
          j = j + 1u;
        }
        if (!sat && has_f0) {
          scr[hdr_sz + r0n] = cr;
          r0n = r0n + 1u;
        }
      }
    }
  }
  h->ant_sz = (h->ant_sz > fticks) ? (h->ant_sz - fticks) : 0ULL;
  if (r0n < 2u) { return false; }
  u64 elim_bound = h->elim_bound;
  scr[0] = f0;
  scr[sc] = hdr_sz;
  scr[2u * sc] = r0n;
  scr[3u * sc] = hdr_sz;
  u32 bump = hdr_sz + r0n;
  counted[f0] = (u8)1;
  u32 step = 1u;
  u32 cur_qn = r0n;
  u32 best_k = 0u;
  u64 best_red = 0ULL;
  while (step < sc && cur_qn >= 2u && h->ant_sz > 0ULL) {
    u32 row_off = scr[sc + step - 1u];
    u32 ncntd = full_bva_scan_cands(h, row_off, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu || h->ant_sz == 0ULL) { break; }
    u32 rem = (u32)(cap - (u64)bump);
    u32 max_new = rem >> 1;
    if (max_new > cur_qn) { max_new = cur_qn; }
    if (max_new < 2u) { break; }
    u32 nrow_off = bump;
    u32 par_off = bump + max_new;
    cur_qn = full_bva_filter_row(h, row_off, nrow_off, par_off, cur_qn, best_lit);
    if (cur_qn < 2u) { break; }
    scr[step] = best_lit;
    scr[sc + step] = nrow_off;
    scr[2u * sc + step] = cur_qn;
    scr[3u * sc + step] = par_off;
    bump = par_off + cur_qn;
    counted[best_lit] = (u8)1;
    step = step + 1u;
    u64 dm = (u64)step;
    u64 mn = (u64)cur_qn;
    u64 prod = dm * mn;
    u64 sum = dm + mn;
    if (prod > sum) {
      u64 red = prod - sum;
      if (red > elim_bound && red > best_red) {
        best_red = red;
        best_k = step - 1u;
      }
    }
  }
  u32 ci = 0u;
  while (ci < step) {
    counted[scr[ci]] = (u8)0;
    ci = ci + 1u;
  }
  if (best_k == 0u) { return false; }
  u32 *touched = (u32 *)h->work_stk2;
  u32 *tmark = (u32 *)h->wsort;
  u64 tlimit = h->cur_vars << 1;
  u64 nt = 0ULL;
  u32 fi = 0u;
  u32 bf_end = best_k + 1u;
  while (fi < bf_end) {
    u32 lit = scr[fi];
    if (tmark[lit] == 0u && nt < tlimit) {
      tmark[lit] = 1u; touched[nt] = lit; nt = nt + 1ULL;
    }
    u32 neg = lit ^ 1u;
    if (tmark[neg] == 0u && nt < tlimit) {
      tmark[neg] = 1u; touched[nt] = neg; nt = nt + 1ULL;
    }
    fi = fi + 1u;
  }
  u32 qn_best = scr[2u * sc + best_k];
  u32 bkey = scr[best_k];
  u32 brow_off = scr[sc + best_k];
  u32 qi = 0u;
  while (qi < qn_best) {
    u32 entry = scr[brow_off + qi]; qi = qi + 1u;
    if ((entry & PW_BIN_FLAG) != 0u) {
      u32 other = entry & PW_LIT_MASK;
      if (tmark[other] == 0u && nt < tlimit) {
        tmark[other] = 1u; touched[nt] = other; nt = nt + 1ULL;
      }
    } else {
      u32 csz = arena[(u64)entry + 2ULL];
      u32 j = 0u;
      while (j < csz) {
        u32 l = arena[(u64)entry + 3ULL + (u64)j];
        if (l != bkey && tmark[l] == 0u && nt < tlimit) {
          tmark[l] = 1u; touched[nt] = l; nt = nt + 1ULL;
        }
        j = j + 1u;
      }
    }
  }
  u64 ti = 0ULL;
  while (ti < nt) { tmark[touched[ti]] = 0u; ti = ti + 1ULL; }
  h->res_sz = nt;
  return full_bva_commit(h, best_k);
}

u64 full_factor(FullHdr *h, u64 budget) {
  u32 sc = full_bva_steps_cap_fid(h->scratch_cap);
  if (h->cur_vars >= h->max_vars || sc == 0u || budget == 0ULL) {
    return 1ULL;
  }
  full_bva_connect_clauses_fid(h);
  if (h->oom != 0ULL) { return 1ULL; }
  h->ant_sz = budget;
  u64 init_cv = h->cur_vars;
  u64 max_nl = h->max_vars << 1;
  u32 *tmark = (u32 *)h->wsort;
  u32 *fheap = (u32 *)h->tarjan_mark;
  u32 *fpos = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  u32 *deg = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u64 zi = 0ULL;
  while (zi < max_nl) {
    tmark[zi] = 0u; fheap[zi] = 0u; fpos[zi] = 0xFFFFFFFFu;
    zi = zi + 1ULL;
  }
  u32 hsz = 0u;
  u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1);
      u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && deg[pl] > 1u) {
        fheap[hsz] = pl; fpos[pl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && deg[nl] > 1u) {
        fheap[hsz] = nl; fpos[nl] = hsz;
        full_fheap_up_fid(fheap, fpos, deg, hsz); hsz = hsz + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hsz > 0u && h->cur_vars < h->max_vars && h->ant_sz > 0ULL && h->oom == 0ULL) {
    u32 f0 = fheap[0];
    hsz = hsz - 1u;
    fpos[f0] = 0xFFFFFFFFu;
    if (hsz > 0u) {
      fheap[0] = fheap[hsz];
      fpos[fheap[0]] = 0u;
      full_fheap_down_fid(fheap, fpos, deg, 0u, hsz);
    }
    u32 fv = f0 >> 1;
    u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u) { continue; }
    if ((fl[fv] & fbit) == 0u) { continue; }
    if (vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit);
    if (deg[f0] <= 1u) { continue; }
    if (full_bva_try_lit(h, f0, init_cv)) {
      u32 *touched = (u32 *)h->work_stk2;
      u64 cur_nl = h->cur_vars << 1;
      u64 nt = h->res_sz;
      u64 n2 = (nt > cur_nl) ? cur_nl : nt;
      u64 di = 0ULL;
      while (di < n2) {
        u32 tl = touched[di];
        if ((u64)tl < cur_nl) {
          deg[tl] = full_bva_count_lit_deg_fid(h, tl);
        }
        di = di + 1ULL;
      }
      u64 tj = 0ULL;
      while (tj < n2) {
        u32 tl = touched[tj];
        if ((u64)tl < cur_nl) {
          u32 p = fpos[tl];
          if (p < hsz) {
            if (deg[tl] <= 1u) {
              hsz = hsz - 1u;
              u32 last = fheap[hsz];
              fpos[last] = 0xFFFFFFFFu;
              if (p < hsz) {
                fpos[tl] = 0xFFFFFFFFu;
                fheap[p] = last;
                fpos[last] = p;
                full_fheap_up_fid(fheap, fpos, deg, p);
                u32 lp = fpos[last];
                if (lp < hsz) {
                  full_fheap_down_fid(fheap, fpos, deg, lp, hsz);
                }
              }
            } else {
              full_fheap_up_fid(fheap, fpos, deg, p);
              u32 p2 = fpos[tl];
              if (p2 < hsz) {
                full_fheap_down_fid(fheap, fpos, deg, p2, hsz);
              }
            }
          } else if ((u64)hsz < cur_nl) {
            u32 tv = tl >> 1;
            u32 tbit = ((tl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
            if ((fl[tv] & FL_ACTIVE) != 0u && (fl[tv] & tbit) != 0u &&
                deg[tl] > 1u && vals[tl] == (i8)0 && p == 0xFFFFFFFFu) {
              fheap[hsz] = tl; fpos[tl] = hsz;
              full_fheap_up_fid(fheap, fpos, deg, hsz);
              hsz = hsz + 1u;
            }
          }
        }
        tj = tj + 1ULL;
      }
    }
  }
  u64 end_nlits = h->cur_vars << 1;
  u64 ci = 0ULL;
  while (ci < end_nlits) {
    fheap[ci] = 0u; fpos[ci] = 0u;
    ci = ci + 1ULL;
  }
  if (h->cur_vars > init_cv) {
    u64 cv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next;
    u32 *qs = (u32 *)h->q_stamp;
    u64 p = h->q_first;
    u64 s = 0ULL;
    while (p < cv && s < cv) {
      s = s + 1ULL;
      qs[p] = (u32)s;
      p = (u64)qn[p];
    }
    h->q_cur_stamp = s;
    if (h->q_search_idx < cv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  return 1ULL;
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks_m6_hdr(h, initial);
  h->probings = h->probings + 1ULL;
  if (!initial) {
    u64 parg = (h->probings > (~0ULL) - 9ULL) ? (~0ULL) : (h->probings + 9ULL);
    u64 qlog = full_log10_q16_m7(parg);
    u64 pc = (h->probings > 100000000ULL) ? 100000000ULL : h->probings;
    u64 nlogp = (100ULL * pc * qlog) >> 16;
    h->probe_limit = h->conflicts + full_scale_delta_m5(h, nlogp);
  }
  u64 max_r = initial ? 1ULL : 2ULL;
  u64 round = 0ULL;
  while (round < max_r) {
    if (!initial && full_vivify_m6_hdr(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    u64 before_unass = h->unassigned;
    if (full_enter_dense(h)) {
      u64 dense_ok = 1ULL;
      if (!m6_hdr_delaying(h, M6_DELAY_CONGRUENCE)) {
        u64 cb = h->cong_cnt;
        if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
          full_rebuild_watches(h);
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
        u64 ca = h->cong_cnt;
        if (ca > cb && (ca - cb) * 1000ULL >= h->unassigned) {
          m6_hdr_reduce_delay(h, M6_DELAY_CONGRUENCE);
        } else {
          m6_hdr_bump_delay(h, M6_DELAY_CONGRUENCE);
        }
        if (ca > cb) {
          if (full_rebuild_watches(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if (!full_enter_dense(h)) {
            if (h->inconsistent != 0ULL) {
              m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
              return 20ULL;
            }
            dense_ok = 0ULL;
          }
        }
      }
      if (dense_ok != 0ULL) {
        if (!m6_hdr_delaying(h, M6_DELAY_SWEEP)) {
          u64 sb = h->sweep_cnt;
          if (full_sweep_dense_m6(h, h->cur_vars, dticks / 10ULL) == 20ULL) {
            full_rebuild_watches(h);
            m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
            return 20ULL;
          }
          if ((h->sweep_cnt > sb) && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
            m6_hdr_reduce_delay(h, M6_DELAY_SWEEP);
          } else {
            m6_hdr_bump_delay(h, M6_DELAY_SWEEP);
          }
        }
        if (full_rebuild_watches(h) == 20ULL) {
          m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
          return 20ULL;
        }
      }
    } else if (h->inconsistent != 0ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
    if (h->unassigned >= before_unass) { break; }
    round = round + 1ULL;
  }
  if (!initial) {
    if (full_probe_tail_m6(h, dticks) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else {
    if (h->num_binary > 0ULL &&
        full_backbone_m6(h, (dticks / 50ULL) + 65536ULL) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  }
  u64 fr = 1ULL;
  u64 fp = 10ULL;
  u64 fa = h->unassigned / 10ULL;
  while (fa >= fp && fr < 19ULL) {
    fr = fr + 1ULL;
    fp = fp * 10ULL;
  }
  u64 fe4 = (h->eliminations > (~0ULL) - 4ULL) ? (~0ULL) : (h->eliminations + 4ULL);
  if (h->unassigned > 0ULL && fr <= fe4 && full_enter_dense(h)) {
    u64 fbud = initial ? 700000000ULL : (dticks / 20ULL);
    full_factor(h, fbud);
    if (full_rebuild_watches(h) == 20ULL) {
      m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
      return 20ULL;
    }
  } else if (h->inconsistent != 0ULL) {
    m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
    return 20ULL;
  }
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}
"

/-! ## 1. `Fn` Handles, Splice Lists & Standalone Module -/

def fidBvaStepsCapFn : Fn :=
  ⟨"full_bva_steps_cap_fid", [i64], [i32], full_bva_steps_cap_fid_body⟩
def fidBvaClinesFn : Fn :=
  ⟨"full_bva_clines_fid", [i64], [i64], full_bva_clines_fid_body⟩
def fidFheapUpFn : Fn :=
  ⟨"full_fheap_up_fid", [i64, i64, i64, i32], [], full_fheap_up_fid_body⟩
def fidFheapDownFn : Fn :=
  ⟨"full_fheap_down_fid", [i64, i64, i64, i32, i32], [], full_fheap_down_fid_body⟩
def fidBvaCountLitDegFn : Fn :=
  ⟨"full_bva_count_lit_deg_fid", [i64, i32], [i32], full_bva_count_lit_deg_fid_body⟩
def fidBvaConnectClausesFn : Fn :=
  ⟨"full_bva_connect_clauses_fid", [i64], [], full_bva_connect_clauses_fid_body⟩
def fidBvaMatchLargeBvaFn : Fn :=
  ⟨"full_bva_match_large_bva_fid", [i64, i32, i32, i32], [.bool], full_bva_match_large_bva_fid_body⟩

def fidBvaScanCandsFn : Fn :=
  ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], full_bva_scan_cands_body⟩
def fidBvaPickCandFn : Fn :=
  ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], full_bva_pick_cand_body⟩
def fidBvaFilterRowFn : Fn :=
  ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], full_bva_filter_row_body⟩
def fidBvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩
def fidBvaTryLitFn : Fn :=
  ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], full_bva_try_lit_body⟩
def fidBvaFactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩
def fidBvaProbeM6Fn : Fn :=
  ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_m6_body⟩

/-- `7` additive Fidelity BVA helpers inserted immediately before `"full_bva_scan_cands"`. -/
def fidBvaHelpers : List Fn :=
  [ fidBvaStepsCapFn, fidBvaClinesFn, fidFheapUpFn, fidFheapDownFn
  , fidBvaCountLitDegFn, fidBvaConnectClausesFn, fidBvaMatchLargeBvaFn ]

/-- `7` canonical Fidelity BVA / probe replacement functions for `PatchModule` splicing. -/
def fidBvaRepls : List Fn :=
  [ fidBvaScanCandsFn, fidBvaPickCandFn, fidBvaFilterRowFn, fidBvaCommitFn
  , fidBvaTryLitFn, fidBvaFactorFn, fidBvaProbeM6Fn ]

/-- Anchor-insertion list for `PatchModule` / `mfPatchFns` (`+7` helpers before
`"full_bva_scan_cands"`). -/
def fidBvaBefores : List (Sym × List Fn) :=
  [ ("full_bva_scan_cands", fidBvaHelpers) ]

/-- Complete `14`-function topological list (canonical symbol names). -/
def fidBvaFns : List Fn :=
  fidBvaHelpers ++ fidBvaRepls

/-- External callee declarations for standalone `FullFidelityBva` verification (`24` externs). -/
def fidBvaExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_fwd_flush_large_m7", [i64], []⟩
  , ⟨"full_init_fresh_var", [i64, i32], []⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64]⟩
  , ⟨"full_log10_q16_m7", [i64], [i64]⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64]⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool]⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], []⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], []⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64]⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64]⟩ ]

/-- Standalone closed module (`14` functions + `24` externs, `0` exits). -/
def fidBvaModule : LeanQbe.T.Module :=
  { fns := fidBvaFns, externs := fidBvaExterns, exits := [] }

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Acyclicity -/

theorem full_bva_steps_cap_fid_wf : Func.Wf full_bva_steps_cap_fid_body := by t_wf_reify
theorem full_bva_clines_fid_wf : Func.Wf full_bva_clines_fid_body := by t_wf_reify
theorem full_fheap_up_fid_wf : Func.Wf full_fheap_up_fid_body := by t_wf_reify
theorem full_fheap_down_fid_wf : Func.Wf full_fheap_down_fid_body := by t_wf_reify
theorem full_bva_count_lit_deg_fid_wf : Func.Wf full_bva_count_lit_deg_fid_body := by t_wf_reify
theorem full_bva_connect_clauses_fid_wf : Func.Wf full_bva_connect_clauses_fid_body := by t_wf_reify
theorem full_bva_match_large_bva_fid_wf : Func.Wf full_bva_match_large_bva_fid_body := by t_wf_reify
theorem full_bva_scan_cands_fid_wf : Func.Wf full_bva_scan_cands_body := by t_wf_reify
theorem full_bva_pick_cand_fid_wf : Func.Wf full_bva_pick_cand_body := by t_wf_reify
theorem full_bva_filter_row_fid_wf : Func.Wf full_bva_filter_row_body := by t_wf_reify
theorem full_bva_commit_fid_wf : Func.Wf full_bva_commit_body := by t_wf_reify
theorem full_bva_try_lit_fid_wf : Func.Wf full_bva_try_lit_body := by t_wf_reify
theorem full_factor_fid_wf : Func.Wf full_factor_body := by t_wf_reify
theorem full_probe_m6_fid_wf : Func.Wf full_probe_m6_body := by t_wf_reify

theorem fidBvaHelpers_wf : ∀ f ∈ fidBvaHelpers, f.Wf := by
  intro f hf
  simp only [fidBvaHelpers, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bva_steps_cap_fid_wf
  · exact full_bva_clines_fid_wf
  · exact full_fheap_up_fid_wf
  · exact full_fheap_down_fid_wf
  · exact full_bva_count_lit_deg_fid_wf
  · exact full_bva_connect_clauses_fid_wf
  · exact full_bva_match_large_bva_fid_wf

theorem fidBvaRepls_wf : ∀ f ∈ fidBvaRepls, f.Wf := by
  intro f hf
  simp only [fidBvaRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bva_scan_cands_fid_wf
  · exact full_bva_pick_cand_fid_wf
  · exact full_bva_filter_row_fid_wf
  · exact full_bva_commit_fid_wf
  · exact full_bva_try_lit_fid_wf
  · exact full_factor_fid_wf
  · exact full_probe_m6_fid_wf

theorem fidBvaFns_wf : ∀ f ∈ fidBvaFns, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact fidBvaHelpers_wf f h1
  · exact fidBvaRepls_wf f h2

theorem fidBva_acyclic : fidBvaModule.checkAcyclic = true := by
  t_kernel_rfl

theorem fidBva_noExit : fidBvaModule.exits = [] := rfl

end LeanQbe.T.Examples.Kissat.FullFidelityBva

end
