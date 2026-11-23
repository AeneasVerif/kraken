module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `FullM7Fidelity` Core Subsystems (`FullM7FidelityCore`)

Purely additive C0 overrides (`0` edits to existing modules) for Target A (`FullM7Fidelity`)
Module 4 (`src/minimize.c`, `src/reorder.c`, `src/factor.c`, `src/eliminate.c`, `src/walk.c`),
matching upstream Kissat 4.0.4:
1. `full_min_shrink_fid` (`shrink=3`): skips Pass 1 in `full_min_shrink_m6` so `mrk | 4` never
   cross-contaminates `full_shrink_lower_m6`.
2. `full_reorder_sift_fid` + `full_reorder_queue_fid` (`reorder.c:176-214`): removes
   `vals[lit] == 0` filter (`P1-6`), inlines the 2-line weight formula, and adds the
   `h->stable != 0ULL` `reorder_stable` branch (`full_rescale` + score scaling + `full_heap_up`).
3. `full_reorder_fid`: guards on `h->cur_level != 0ULL` (instead of `h->stable != 0ULL`) and
   delegates to `full_reorder_queue_m7`.
4. `full_bva_{match_large,scan_cands,filter_row}_fid` (`PH_BVA_Q`): isolates the BVA queue-mark
   bit to `0x02000000u` (bit 25) instead of colliding with vivification's `PH_VIV` (`0x00100000u`).
5. `full_elim_bve_fid` (`eliminaterounds=2`): bounds BVE rounds to `round < 2ULL`.
6. `full_walk_fid`: raises `max_flips = 1000000ULL`, passes `max(ncl, 4096ULL)` to
   `full_walk_effort_m7`, and picks random unsatisfied clauses via `full_rng_next(h) % ulen`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityCore

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fid_core "
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

#define PH_GARB     0x00080000u
#define PH_RED      0x00400000u
#define PH_BVA_Q    0x02000000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE   1u
#define FL_ELIM_C   16u

extern void full_sort_tmp(FullHdr *h);
extern void full_min_mark(FullHdr *h, u32 v, u8 tag);
extern bool full_shrink_blk_bool_m6(FullHdr *h, u64 beg, u64 end_b, u32 blvl, u64 max_tr);
extern bool full_min_lit_dfs_m6(FullHdr *h, u32 lit, bool check_ana, bool top);

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_rescale(FullHdr *h);
extern void full_heap_up(FullHdr *h, u32 v);
extern u64 full_reorder_queue_m7(FullHdr *h);

extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64 full_bve_heap_push_m7(FullHdr *h, u64 hlen, u32 v);
extern u32 full_bve_heap_pop_m7(FullHdr *h, u64 hlen);
extern u64 full_bve_collect_nbrs_m7(FullHdr *h, u32 v);
extern u64 full_bve_var_m7(FullHdr *h, u32 v);

extern void full_walk_init_vals_m7(FullHdr *h);
extern u64 full_walk_collect_m7(FullHdr *h);
extern u64 full_walk_cb_inv_m7(FullHdr *h, u64 ncl, u64 tot_lits);
extern void full_walk_init_table_m7(FullHdr *h, u64 inv_q16);
extern u64 full_walk_build_occ_m7(FullHdr *h, u64 ncl);
extern u64 full_walk_effort_m7(FullHdr *h, u64 ncl);
extern u64 full_walk_pick_m7(FullHdr *h, u32 cl_id, u64 ncl);
extern u64 full_walk_flip_m7(FullHdr *h, u32 flip_lit, u64 ncl, u64 ulen);
extern void full_walk_save_min_m7(FullHdr *h, u64 best_pos, bool trail_ok);
extern u64 full_rng_next(FullHdr *h);

void full_min_shrink_fid(FullHdr *h) {
  u64 cv = h->cur_vars; u64 orig_tlen = h->tmp_len;
  h->conflicts = h->conflicts + 1ULL;
  if (orig_tlen <= 1ULL || orig_tlen > cv) {
    h->learned_lits = h->learned_lits + orig_tlen; return;
  }
  full_sort_tmp(h);
  u32 *tmp = (u32 *)h->tmp_lits; u32 *lvl = (u32 *)h->level; u32 *tpos = (u32 *)h->trail_pos;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  u64 i = 0ULL;
  while (i < orig_tlen) { full_min_mark(h, tmp[i] >> 1, (u8)2); i = i + 1ULL; }
  u64 tlen = orig_tlen;
  u64 beg = 1ULL;
  while (beg < tlen) {
    u32 blvl = lvl[tmp[beg] >> 1]; u64 max_tr = (u64)tpos[tmp[beg] >> 1];
    u64 end_b = beg + 1ULL;
    while (end_b < tlen && lvl[tmp[end_b] >> 1] == blvl) {
      u64 tp = (u64)tpos[tmp[end_b] >> 1];
      if (tp > max_tr) { max_tr = tp; }
      end_b = end_b + 1ULL;
    }
    if (end_b - beg >= 2ULL) {
      if (!full_shrink_blk_bool_m6(h, beg, end_b, blvl, max_tr)) {
        u64 mk2 = beg;
        while (mk2 < end_b) {
          if (full_min_lit_dfs_m6(h, tmp[mk2], false, false)) { tmp[mk2] = 0xFFFFFFFFu; }
          mk2 = mk2 + 1ULL;
        }
      }
    }
    beg = end_b;
  }
  u64 keep = 1ULL; u64 k = 1ULL;
  while (k < tlen) {
    if (tmp[k] != 0xFFFFFFFFu) { tmp[keep] = tmp[k]; keep = keep + 1ULL; }
    k = k + 1ULL;
  }
  u8 *mrk = (u8 *)h->mark;
  if (h->min_clr_full != 0ULL) {
    u64 v = 0ULL; while (v < cv) { mrk[v] = (u8)0; v = v + 1ULL; }
  } else {
    u32 *mclr = (u32 *)h->min_clr; u64 z = 0ULL;
    while (z < h->min_clr_len) {
      u32 z_v = mclr[z]; if ((u64)z_v < cv) { mrk[z_v] = (u8)0; }
      z = z + 1ULL;
    }
  }
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL; h->tmp_len = keep;
  h->min_removed = h->min_removed + (orig_tlen - keep);
  h->learned_lits = h->learned_lits + keep;
}

bool full_bva_match_large_fid(FullHdr *h, u32 cur_cr, u32 next_lit, u32 d_ref) {
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

u32 full_bva_scan_cands_fid(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits) {
  i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *cntd = (u32 *)h->work_stk1; u32 *fl = (u32 *)h->flags;
  u32 *ql = (u32 *)h->work_stk2; u32 nql = 0u; u32 ncntd = 0u; u32 qi = 0u;
  while (qi < cur_qn) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1]; u64 qend = qoff + (u64)wvec[((u64)q << 1) + 1ULL];
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
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) != (u8)0) { fc = fc + 1u; if (fc > 1u) { break; } }
        else {
          lm[l] = lm[l] | (u8)2;
          u32 d = wvec[((u64)l << 1) + 1ULL];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (fc == 1u && min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1]; u64 mend = moff + (u64)min_d; u64 mp = moff;
        u64 mxv = h->max_vars; u32 nnou = 0u;
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr == qw || (ar[dr] & (PH_GARB | PH_RED | PH_BVA_Q)) != 0u ||
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
    qi = qi + 1u;
  }
  u32 ci = 0u; while (ci < nql) { ar[ql[ci]] = ar[ql[ci]] & (~PH_BVA_Q); ci = ci + 1u; }
  return ncntd;
}

u32 full_bva_filter_row_fid(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
                            u32 cur_qn, u32 best_lit) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 new_qn = 0u; u32 qi = 0u;
  while (qi < cur_qn && new_qn < 256u) {
    u32 qw = scr[row_off + qi];
    if ((qw & PW_BIN_FLAG) != 0u) {
      u32 q = qw & PW_LIT_MASK;
      u64 qoff = (u64)wvec[(u64)q << 1]; u64 qend = qoff + (u64)wvec[((u64)q << 1) + 1ULL];
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
      u32 csz = ar[(u64)qw + 2ULL]; u32 min_l = 0xFFFFFFFFu; u32 min_d = 0xFFFFFFFFu; u32 j = 0u;
      while (j < csz) {
        u32 l = ar[(u64)qw + 3ULL + (u64)j];
        if ((lm[l] & (u8)1) == (u8)0) {
          lm[l] = lm[l] | (u8)2;
          u32 d = wvec[((u64)l << 1) + 1ULL];
          if (min_l == 0xFFFFFFFFu || d < min_d) { min_l = l; min_d = d; }
        }
        j = j + 1u;
      }
      if (min_l != 0xFFFFFFFFu) {
        u64 moff = (u64)wvec[(u64)min_l << 1]; u64 mend = moff + (u64)min_d; u64 mp = moff;
        while (mp < mend) {
          u32 mw = wstk[mp]; mp = mp + 1ULL;
          if ((mw & PW_BIN_FLAG) != 0u) { continue; }
          if (mp >= mend) { break; }
          u32 dr = wstk[mp]; mp = mp + 1ULL;
          if (dr != qw && full_bva_match_large_fid(h, qw, best_lit, dr)) {
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
  qi = 0u;
  while (qi < new_qn) {
    u32 dr = scr[nrow_off + qi];
    if ((dr & PW_BIN_FLAG) == 0u) { ar[dr] = ar[dr] & (~PH_BVA_Q); }
    qi = qi + 1u;
  }
  return new_qn;
}

void full_reorder_sift_fid(FullHdr *h, u64 start, u64 n) {
  if (n == 0ULL || start >= n || n > h->cur_vars) { return; }
  u32 *ws = (u32 *)h->wsort;
  u64 *wl = (u64 *)h->tarjan_mark;
  u32 *qs = (u32 *)h->q_stamp;
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 best = root;
    u32 bv = ws[best];
    u64 bw = wl[bv];
    u32 bs = qs[bv];
    u32 cv = ws[child];
    u64 cw = wl[cv];
    u32 cs = qs[cv];
    if (cw > bw || (cw == bw && cs > bs)) { best = child; bv = cv; bw = cw; bs = cs; }
    u64 rch = child + 1ULL;
    if (rch < n) {
      u32 rv = ws[rch];
      u64 rw = wl[rv];
      u32 rs = qs[rv];
      if (rw > bw || (rw == bw && rs > bs)) { best = rch; bv = rv; }
    }
    if (best == root) { break; }
    u32 tmp = ws[root];
    ws[root] = bv;
    ws[best] = tmp;
    root = best;
  }
}

u64 full_reorder_queue_fid(FullHdr *h) {
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
  u64 w2 = 1ULL << 40;
  u64 wcap = 1ULL << 60;
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
      if (!sat && sz >= 2ULL && sz <= 100ULL) {
        u64 w = (sz >= 2ULL && sz <= 42ULL) ? ((1ULL << 40) >> (sz - 2ULL)) : 0ULL;
        if (w > 0ULL) {
          ci = 0ULL;
          while (ci < clen) {
            u32 lit = ar[p + 3ULL + ci];
            if ((u64)lit < nlits) {
              u32 av = lit >> 1;
              if ((lit & 1u) == 0u) {
                u64 cur = wl[av];
                wl[av] = (cur > wcap - w) ? wcap : (cur + w);
              } else {
                u64 cur = wr[av];
                wr[av] = (cur > wcap - w) ? wcap : (cur + w);
              }
            }
            ci = ci + 1ULL;
          }
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
              if ((lit & 1ULL) == 0ULL) {
                u64 c1 = wl[lvar];
                wl[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              } else {
                u64 c1 = wr[lvar];
                wr[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              }
              if ((other & 1u) == 0u) {
                u64 c2 = wl[ov];
                wl[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              } else {
                u64 c2 = wr[ov];
                wr[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              }
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
    wl[fv] = (a >= b) ? (a + (b << 1)) : (b + (a << 1));
    fv = fv + 1ULL;
  }
  if (h->stable != 0ULL) {
    full_rescale(h);
    u64 *sc = (u64 *)h->score;
    u64 sv = 0ULL;
    u64 maxw = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u && wl[sv] > maxw) { maxw = wl[sv]; }
      sv = sv + 1ULL;
    }
    u64 scale_ref = h->scinc;
    if (scale_ref < (1ULL << 20)) { scale_ref = 1ULL << 20; }
    sv = 0ULL;
    while (sv < cv) {
      if ((fl[sv] & FL_ACTIVE) != 0u && wl[sv] > 0ULL) {
        u64 add = (maxw > 0ULL) ? ((wl[sv] >> 20) * (scale_ref >> 20)) : 0ULL;
        if (add > (1ULL << 52)) { add = 1ULL << 52; }
        u64 cur = sc[sv];
        u64 nsc = (cur > (1ULL << 60) - add) ? (1ULL << 60) : (cur + add);
        sc[sv] = nsc;
        full_heap_up(h, (u32)sv);
      }
      sv = sv + 1ULL;
    }
    return cv;
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

u64 full_reorder_fid(FullHdr *h, u64 budget) {
  if (h->cur_level != 0ULL) { return 0ULL; }
  return full_reorder_queue_m7(h);
}

u64 full_elim_bve_fid(FullHdr *h, u64 bve_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *hp = (u32 *)h->work_stk1;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 mv = h->max_vars;
  u32 *mclr = (u32 *)h->min_clr;
  u64 cv0 = h->cur_vars;
  u64 ci = 0ULL;
  while (ci < cv0) { mclr[ci] = 0u; ci = ci + 1ULL; }
  u64 tried = 0ULL;
  u64 hlen = 0ULL;
  bool last_round_elim = false;
  u64 round = 0ULL;
  while (round < 2ULL && tried < bve_lim && h->fuel > 0ULL &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    if (!full_dense_flush_units_m7(h)) { return 20ULL; }
    u64 cv = h->cur_vars;
    u64 i = 0ULL;
    while (i < cv) { hp[mv + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    hlen = 0ULL;
    i = 0ULL;
    while (i < cv) {
      if ((fl[i] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) &&
          vals[i << 1] == (i8)0) {
        hlen = full_bve_heap_push_m7(h, hlen, (u32)i);
      }
      i = i + 1ULL;
    }
    if (hlen == 0ULL) { last_round_elim = false; break; }
    bool round_elim = false;
    while (hlen > 0ULL && tried < bve_lim && h->fuel > 0ULL &&
           h->oom == 0ULL && h->inconsistent == 0ULL) {
      u32 v = full_bve_heap_pop_m7(h, hlen);
      hlen = hlen - 1ULL;
      u64 cv1 = h->cur_vars;
      if (v == 0xFFFFFFFFu || (u64)v >= cv1) { continue; }
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) != (FL_ACTIVE | FL_ELIM_C) ||
          vals[(u64)v << 1] != (i8)0) { continue; }
      fl[v] = fl[v] & (~FL_ELIM_C);
      tried = tried + 1ULL;
      u64 nn = full_bve_collect_nbrs_m7(h, v);
      u64 b0 = h->bve_cnt;
      u64 c0 = h->bce_cnt;
      u64 st = full_bve_var_m7(h, v);
      if (st == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
      if (st == 2ULL) { break; }
      if (h->bve_cnt > b0 || h->bce_cnt > c0) {
        if (h->bve_cnt > b0) { round_elim = true; }
        u64 cv2 = h->cur_vars;
        u64 k = 0ULL;
        while (k < nn) {
          u32 u = nbrs[k];
          if ((u64)u < cv2 && (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
            fl[u] = fl[u] | FL_ELIM_C;
            hlen = full_bve_heap_push_m7(h, hlen, u);
          }
          k = k + 1ULL;
        }
      }
    }
    last_round_elim = round_elim;
    if (!round_elim) { break; }
    round = round + 1ULL;
  }
  if (h->inconsistent == 0ULL) {
    u64 cvf = h->cur_vars;
    bool complete = (hlen == 0ULL && !last_round_elim && h->oom == 0ULL && h->fuel > 0ULL);
    if (complete) {
      u64 cur_b = h->elim_bound;
      if (cur_b < 16ULL) {
        u64 next_b = (cur_b == 0ULL) ? 1ULL : (cur_b << 1);
        if (next_b > 16ULL) { next_b = 16ULL; }
        h->elim_bound = next_b;
        u64 k = 0ULL;
        while (k < cvf) { fl[k] = fl[k] | FL_ELIM_C; k = k + 1ULL; }
      }
    } else {
      u64 k = 0ULL;
      while (k < cvf) { fl[k] = fl[k] & (~FL_ELIM_C); k = k + 1ULL; }
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void full_walk_fid(FullHdr *h) {
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
  u64 init_u = ulen;
  u64 max_flips = 1000000ULL;
  u64 step_limit = full_walk_effort_m7(h, (ncl < 4096ULL) ? 4096ULL : ncl);
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
    u64 upos = full_rng_next(h) % ulen;
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
  if (best_u < init_u) {
    full_walk_save_min_m7(h, best_pos, trail_ok);
  }
  h->walk_cnt_stat = h->walk_cnt_stat + 1ULL;
}
"

/-- Canonical external callee signatures referenced by `fid_core_fns` (`23` externs). -/
def fidCoreExterns : List Extern :=
  [ ⟨"full_sort_tmp", [i64], []⟩
  , ⟨"full_min_mark", [i64, i32, i8], []⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool]⟩
  , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool]⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_rescale", [i64], []⟩
  , ⟨"full_heap_up", [i64, i32], []⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64]⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool]⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64]⟩
  , ⟨"full_bve_heap_pop_m7", [i64, i64], [i32]⟩
  , ⟨"full_bve_collect_nbrs_m7", [i64, i32], [i64]⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64]⟩
  , ⟨"full_walk_init_vals_m7", [i64], []⟩
  , ⟨"full_walk_collect_m7", [i64], [i64]⟩
  , ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64]⟩
  , ⟨"full_walk_init_table_m7", [i64, i64], []⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64], [i64]⟩
  , ⟨"full_walk_effort_m7", [i64, i64], [i64]⟩
  , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64]⟩
  , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64]⟩
  , ⟨"full_walk_save_min_m7", [i64, i64, .bool], []⟩
  , ⟨"full_rng_next", [i64], [i64]⟩ ]

/-- Standalone Target A (`FullM7Fidelity`) Core function list (`9` functions). -/
def fidCoreFns : List Fn := fid_core_fns

/-- Standalone Target A (`FullM7Fidelity`) Core module (`9` functions + `23` externs). -/
def fidCoreModule : LeanQbe.T.Module :=
  { fns := fidCoreFns, externs := fidCoreExterns, exits := [] }

/-- Canonical `Fn` handles matching `FullM7.m7Fns` slots (`FullM7Splice.patchFns` ready). -/
def fidMinShrinkM6Fn : Fn := ⟨"full_min_shrink_m6", [i64], [], full_min_shrink_fid_body⟩
def fidBvaMatchLargeFidFn : Fn :=
  ⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool], full_bva_match_large_fid_body⟩
def fidBvaScanCandsFn : Fn :=
  ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], full_bva_scan_cands_fid_body⟩
def fidBvaFilterRowFn : Fn :=
  ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], full_bva_filter_row_fid_body⟩
def fidReorderSiftFidFn : Fn :=
  ⟨"full_reorder_sift_fid", [i64, i64, i64], [], full_reorder_sift_fid_body⟩
def fidReorderQueueM7Fn : Fn :=
  ⟨"full_reorder_queue_m7", [i64], [i64], full_reorder_queue_fid_body⟩
def fidReorderM6Fn : Fn := ⟨"full_reorder_m6", [i64, i64], [i64], full_reorder_fid_body⟩
def fidElimBveM7Fn : Fn := ⟨"full_elim_bve_m7", [i64, i64], [i64], full_elim_bve_fid_body⟩
def fidWalkM7Fn : Fn := ⟨"full_walk_m7", [i64], [], full_walk_fid_body⟩

/-- Canonical `FullM7Splice.patchFns` replacement list (`7` existing `FullM7.m7Fns` slots). -/
def fidCorePatchFns : List Fn :=
  [ fidMinShrinkM6Fn, fidBvaScanCandsFn, fidBvaFilterRowFn, fidReorderQueueM7Fn
  , fidReorderM6Fn, fidElimBveM7Fn, fidWalkM7Fn ]

/-- Helper insertion list for `FullM7Splice.patchFns`, inserting `full_bva_match_large_fid` before
`"full_bva_filter_row"` and `full_reorder_sift_fid` before `"full_reorder_queue_m7"`. -/
def fidCorePatchBefores : List (Sym × List Fn) :=
  [ ("full_bva_filter_row", [fidBvaMatchLargeFidFn])
  , ("full_reorder_queue_m7", [fidReorderSiftFidFn]) ]

theorem full_min_shrink_fid_wf : Func.Wf full_min_shrink_fid_body := by t_wf_reify
theorem full_bva_match_large_fid_wf : Func.Wf full_bva_match_large_fid_body := by t_wf_reify
theorem full_bva_scan_cands_fid_wf : Func.Wf full_bva_scan_cands_fid_body := by t_wf_reify
theorem full_bva_filter_row_fid_wf : Func.Wf full_bva_filter_row_fid_body := by t_wf_reify
theorem full_reorder_sift_fid_wf : Func.Wf full_reorder_sift_fid_body := by t_wf_reify
theorem full_reorder_queue_fid_wf : Func.Wf full_reorder_queue_fid_body := by t_wf_reify
theorem full_reorder_fid_wf : Func.Wf full_reorder_fid_body := by t_wf_reify
theorem full_elim_bve_fid_wf : Func.Wf full_elim_bve_fid_body := by t_wf_reify
theorem full_walk_fid_wf : Func.Wf full_walk_fid_body := by t_wf_reify

theorem fidCore_fns_wf : ∀ f ∈ fidCoreFns, f.Wf := by
  simp only [fidCoreFns, fid_core_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_min_shrink_fid_wf, full_bva_match_large_fid_wf, full_bva_scan_cands_fid_wf,
    full_bva_filter_row_fid_wf, full_reorder_sift_fid_wf, full_reorder_queue_fid_wf,
    full_reorder_fid_wf, full_elim_bve_fid_wf, full_walk_fid_wf⟩

theorem fidCorePatchFns_wf : ∀ f ∈ fidCorePatchFns, f.Wf := by
  simp only [fidCorePatchFns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_min_shrink_fid_wf, full_bva_scan_cands_fid_wf, full_bva_filter_row_fid_wf,
    full_reorder_queue_fid_wf, full_reorder_fid_wf, full_elim_bve_fid_wf, full_walk_fid_wf⟩

theorem fidCorePatchBefores_wf :
    ∀ p ∈ fidCorePatchBefores, ∀ h ∈ p.2, h.Wf := by
  intro p hp h hh
  simp only [fidCorePatchBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp only [List.mem_singleton] at hh <;> subst hh
  · exact full_bva_match_large_fid_wf
  · exact full_reorder_sift_fid_wf

theorem fidCore_acyclic : fidCoreModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelityCore
