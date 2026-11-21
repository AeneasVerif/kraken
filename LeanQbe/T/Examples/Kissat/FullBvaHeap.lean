module

public import LeanQbe.T.Examples.Kissat.Full
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` 3-Hop Complement-Overlap BVA & Max-Degree Binary Heap Factoring (`C0`)

Additive port of the Stage-5 BVA + max-degree factoring upgrades from
`prototype/kissat-fast-c0:LeanQbe/T/Examples/Kissat/Fast.lean` onto the exact existing
`FullHdr` (`144` `u64` words = `1,152` bytes) and `Full` external callees:

1. `full_init_fresh_var`: initializes a fresh extension variable with `q_last` VMTF placement
   and VSIDS score `0` (no heap push).
2. `full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`: budget-bounded 3-hop structural overlap
   tie-breaking scorer using `h->repr` (`u64[max_vars]`), `h->sim_sig` (`u64[max_vars]`),
   `h->min_clr`, and `h->shrink_stk`.
3. `full_bva_match_large`, `full_bva_scan_cands`, `full_bva_pick_cand`, `full_bva_filter_row`,
   `full_bva_commit`, `full_bva_try_lit`: bounded variable addition over binary and irredundant
   size `3..5` arena clauses, with explicit `f0`-membership validation on large row-0 clauses,
   bounded mark/vivify cleanup, and `wsort` cleanup across defrag/commit.
4. `full_fheap_up`, `full_fheap_down`, `full_factor`: max-degree binary heap factoring driver
   stored in `h->tarjan_mark` / `h->tarjan_reach`.

All `13` functions live in `namespace LeanQbe.T.Examples.Kissat.FullBvaHeap` (zero symbol
collisions with `LeanQbe.T.Examples.Kissat.Full`) and satisfy `Func.Wf` and acyclicity.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! bvaHeap "
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

#define PH_GARB 0x00080000u
#define PH_VIV  0x00100000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_FACT_P  32u
#define FL_FACT_N  64u
#define FL_SWEEP   1024u

extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);

void full_init_fresh_var(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases; u32 *wvec = (u32 *)h->watch_vec; u64 *sc = (u64 *)h->score;
  u64 wb = (u64)fv << 2;
  wvec[wb] = 0u; wvec[wb + 1ULL] = 0u; wvec[wb + 2ULL] = 0u; wvec[wb + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)1; lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu;
  ps[fv] = 0xFFFFFFFFu; sc[fv] = 0ULL;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP | FL_FACT_P | FL_FACT_N;
  u32 ol = (u32)h->q_last; qp[fv] = ol; qn[fv] = 0xFFFFFFFFu;
  if ((u64)ol < h->cur_vars) { qn[ol] = fv; } else { h->q_first = (u64)fv; }
  h->q_last = (u64)fv; h->q_cur_stamp = h->q_cur_stamp + 1ULL; qs[fv] = (u32)h->q_cur_stamp;
  h->unassigned = h->unassigned + 1ULL;
}

u64 full_bva_hop1(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1;
  u64 *s1 = (u64 *)h->repr;
  if (s1[sidx] != 0ULL) { return s1[sidx] - 1ULL; }
  u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u32 *st1 = (u32 *)h->min_clr; u64 cv = h->cur_vars; u32 sgn = 0u;
  while (sgn < 2u && h->ant_sz > 0ULL) {
    u32 sl = (sidx << 1) | sgn;
    u64 off = (u64)wvec[(u64)sl << 1]; u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
    u64 p = off;
    while (p < end && h->ant_sz > 0ULL) {
      h->ant_sz = h->ant_sz - 1ULL;
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        if (((w0 & PW_LIT_MASK) >> 1) == dst_idx) { res = res + 1ULL; }
      } else if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
          u32 sz = ar[(u64)cr + 2ULL]; u32 k = 0u;
          while (k < sz) {
            u32 ol = ar[(u64)cr + 3ULL + (u64)k];
            if (ol != sl && (ol >> 1) == dst_idx) { res = res + 1ULL; }
            k = k + 1u;
          }
        }
      }
    }
    sgn = sgn + 1u;
  }
  if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
  s1[sidx] = res + 1ULL;
  if (h->tmp_cnt < cv) { st1[h->tmp_cnt] = sidx; h->tmp_cnt = h->tmp_cnt + 1ULL; }
  return res;
}

u64 full_bva_hop2(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1; u64 *s2 = (u64 *)h->sim_sig;
  if (s2[sidx] != 0ULL) { return s2[sidx] - 1ULL; }
  u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u32 *st2 = (u32 *)h->shrink_stk; u64 cv = h->cur_vars; u32 sgn = 0u;
  while (sgn < 2u && h->ant_sz > 0ULL) {
    u32 sl = (sidx << 1) | sgn;
    u64 off = (u64)wvec[(u64)sl << 1]; u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
    u64 p = off;
    while (p < end && h->ant_sz > 0ULL) {
      h->ant_sz = h->ant_sz - 1ULL;
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        res = res + full_bva_hop1(h, w0 & PW_LIT_MASK, dst_idx);
      } else if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
          u32 sz = ar[(u64)cr + 2ULL]; u32 k = 0u;
          while (k < sz && h->ant_sz > 0ULL) {
            u32 ol = ar[(u64)cr + 3ULL + (u64)k];
            if (ol != sl) { res = res + full_bva_hop1(h, ol, dst_idx); }
            k = k + 1u;
          }
        }
      }
    }
    sgn = sgn + 1u;
  }
  if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
  s2[sidx] = res + 1ULL;
  if (h->tmp_len < cv) { st2[h->tmp_len] = sidx; h->tmp_len = h->tmp_len + 1ULL; }
  return res;
}

u64 full_bva_hop3(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1; u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  h->ant_sz = 256ULL; h->tmp_cnt = 0ULL; h->tmp_len = 0ULL;
  u32 sgn = 0u;
  while (sgn < 2u && h->ant_sz > 0ULL) {
    u32 sl = (sidx << 1) | sgn;
    u64 off = (u64)wvec[(u64)sl << 1]; u64 end = off + (u64)wvec[((u64)sl << 1) + 1ULL];
    u64 p = off;
    while (p < end && h->ant_sz > 0ULL) {
      h->ant_sz = h->ant_sz - 1ULL;
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        res = res + full_bva_hop2(h, w0 & PW_LIT_MASK, dst_idx);
      } else if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) == 0u) {
          u32 sz = ar[(u64)cr + 2ULL]; u32 k = 0u;
          while (k < sz && h->ant_sz > 0ULL) {
            u32 ol = ar[(u64)cr + 3ULL + (u64)k];
            if (ol != sl) { res = res + full_bva_hop2(h, ol, dst_idx); }
            k = k + 1u;
          }
        }
      }
    }
    sgn = sgn + 1u;
  }
  u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig;
  u32 *st1 = (u32 *)h->min_clr; u32 *st2 = (u32 *)h->shrink_stk;
  u64 i = 0ULL; while (i < h->tmp_cnt) { s1[st1[i]] = 0ULL; i = i + 1ULL; }
  i = 0ULL; while (i < h->tmp_len) { s2[st2[i]] = 0ULL; i = i + 1ULL; }
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL;
  return res;
}

bool full_bva_match_large(FullHdr *h, u32 cur_cr, u32 next_lit, u32 d_ref) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark;
  u32 sz = ar[(u64)cur_cr + 2ULL];
  if (ar[(u64)d_ref + 2ULL] != sz || (ar[d_ref] & (PH_GARB | PH_RED | PH_VIV)) != 0u) {
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
          if (dr == qw || (ar[dr] & (PH_GARB | PH_RED | PH_VIV)) != 0u ||
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
              ar[dr] = ar[dr] | PH_VIV;
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
  u32 ci = 0u; while (ci < nql) { ar[ql[ci]] = ar[ql[ci]] & (~PH_VIV); ci = ci + 1u; }
  return ncntd;
}

u32 full_bva_pick_cand(FullHdr *h, u32 ncntd, u32 f0) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *cnt = (u32 *)h->wsort; u32 *cntd = (u32 *)h->work_stk1;
  u32 best_c = 0u; u32 best_lit = 0xFFFFFFFFu; u32 ties = 0u; u32 ci = 0u;
  while (ci < ncntd) {
    u32 clit = cntd[ci]; u32 cc = cnt[clit];
    if (cc > best_c) { best_c = cc; best_lit = clit; ties = 1u; }
    else if (cc == best_c && cc > 0u) { ties = ties + 1u; }
    ci = ci + 1u;
  }
  if (best_c >= 2u && ties > 1u) {
    u64 best_sc = 0ULL; u32 best_deg = 0u; ci = 0u; u32 f0v = f0 >> 1; u32 tt = 0u;
    while (ci < ncntd && tt < 8u) {
      u32 clit = cntd[ci];
      if (cnt[clit] == best_c) {
        tt = tt + 1u;
        u64 sc = full_bva_hop3(h, clit, f0v);
        u32 deg = wvec[((u64)clit << 1) + 1ULL];
        if (sc > best_sc || (sc == best_sc && deg > best_deg)) {
          best_sc = sc; best_deg = deg; best_lit = clit;
        }
      }
      ci = ci + 1u;
    }
  }
  ci = 0u; while (ci < ncntd) { cnt[cntd[ci]] = 0u; ci = ci + 1u; }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}

u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
                        u32 cur_qn, u32 best_lit) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  u32 new_qn = 0u; u32 qi = 0u;
  while (qi < cur_qn && new_qn < 64u) {
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
          if (dr != qw && full_bva_match_large(h, qw, best_lit, dr)) {
            ar[dr] = ar[dr] | PH_VIV;
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
    if ((dr & PW_BIN_FLAG) == 0u) { ar[dr] = ar[dr] & (~PH_VIV); }
    qi = qi + 1u;
  }
  return new_qn;
}

bool full_bva_commit(FullHdr *h, u32 best_k) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 dm = best_k + 1u; u32 mn = scr[16u + best_k];
  u64 need_ar = (u64)mn * 8ULL + 16ULL; u64 need_w = ((u64)dm + (u64)mn * 5ULL + 8ULL) * 4ULL;
  if (h->cur_vars >= h->max_vars || h->arena_cap - h->arena_len < need_ar) { return false; }
  if (h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap - h->wlen < need_w) {
      u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig; s1[fv] = 0ULL; s2[fv] = 0ULL;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  u32 m = 0u;
  while (m < mn) {
    u32 idx = m; u32 c_top = scr[64u + best_k * 64u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) { full_add_bin(h, fresh ^ 1u, c_top & PW_LIT_MASK); }
    else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr != 0xFFFFFFFFULL) {
        j = 0u; while (j < tk) { ar[ncr + 3ULL + (u64)j] = tmp[j]; j = j + 1u; }
        j = 0u;
        while (j < tk) {
          full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u);
          u32 tv = tmp[j] >> 1;
          fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
          j = j + 1u;
        }
        h->num_irred = h->num_irred + 1ULL;
      }
    }
    u32 s = best_k;
    while (true) {
      u32 cs = scr[64u + s * 64u + idx]; u32 fs = scr[s];
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
      idx = scr[1088u + s * 64u + idx]; s = s - 1u;
    }
    m = m + 1u;
  }
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si]; full_add_bin(h, fresh, fs);
    fl[fs >> 1] = fl[fs >> 1] | FL_FACT_P | FL_FACT_N;
    si = si + 1u;
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < 2304ULL) { return false; }
  i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  if (init_cv > h->cur_vars) { init_cv = h->cur_vars; }
  u32 qn = 0u; u64 off = (u64)wvec[(u64)f0 << 1]; u64 end = off + (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 p = off;
  while (p < end && qn < 64u) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { scr[64u + qn] = w0; qn = qn + 1u; }
    } else if (p < end) {
      u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
      if ((ar[cr] & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 5u) {
        u32 hk = 0u; bool has_f0 = false;
        while (hk < sz) {
          if (ar[(u64)cr + 3ULL + (u64)hk] == f0) { has_f0 = true; break; }
          hk = hk + 1u;
        }
        if (has_f0) { scr[64u + qn] = cr; qn = qn + 1u; }
      }
    }
  }
  if (qn < 2u) { return false; }
  u64 init_lits = init_cv << 1;
  scr[0] = f0; scr[16] = qn; lm[f0] = (u8)1;
  u32 step = 1u; u32 cur_qn = qn; u32 best_k = 0u; u64 best_red = 0ULL;
  while (step < 16u && cur_qn >= 2u) {
    u32 ncntd = full_bva_scan_cands(h, 64u + (step - 1u) * 64u, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu) { break; }
    u32 new_qn = full_bva_filter_row(h, 64u + (step - 1u) * 64u, 64u + step * 64u,
      1088u + step * 64u, cur_qn, best_lit);
    if (new_qn < 2u) { break; }
    scr[step] = best_lit; scr[16u + step] = new_qn; lm[best_lit] = (u8)1;
    u64 dm = (u64)(step + 1u); u64 mn = (u64)new_qn;
    if (dm * mn > dm + mn) {
      u64 red = dm * mn - (dm + mn);
      if (red > h->elim_bound && red > best_red) { best_red = red; best_k = step; }
    }
    cur_qn = new_qn; step = step + 1u;
  }
  u32 si = 0u;
  while (si < step) { lm[scr[si]] = lm[scr[si]] & (u8)0xFE; si = si + 1u; }
  if (best_k == 0u) { return false; }
  return full_bva_commit(h, best_k);
}

void full_fheap_up(u32 *hp, u32 *ps, u32 *wvec, u32 p) {
  u32 l = hp[p]; u32 d = wvec[((u64)l << 1) + 1ULL];
  while (p > 0u) {
    u32 pp = (p - 1u) >> 1; u32 pl = hp[pp];
    if (wvec[((u64)pl << 1) + 1ULL] >= d) { break; }
    hp[p] = pl; ps[pl] = p; p = pp;
  }
  hp[p] = l; ps[l] = p;
}

void full_fheap_down(u32 *hp, u32 *ps, u32 *wvec, u32 p, u32 n) {
  u32 l = hp[p]; u32 d = wvec[((u64)l << 1) + 1ULL];
  while (true) {
    u32 cp = (p << 1) + 1u; if (cp >= n) { break; }
    u32 cl = hp[cp]; u32 cd = wvec[((u64)cl << 1) + 1ULL];
    if (cp + 1u < n) {
      u32 sl = hp[cp + 1u]; u32 sd = wvec[((u64)sl << 1) + 1ULL];
      if (sd > cd) { cp = cp + 1u; cl = sl; cd = sd; }
    }
    if (cd <= d) { break; }
    hp[p] = cl; ps[cl] = p; p = cp;
  }
  hp[p] = l; ps[l] = p;
}

u64 full_factor(FullHdr *h, u64 budget) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < 2304ULL || budget == 0ULL) { return 1ULL; }
  u64 init_cv = h->cur_vars; u64 mx_lits = h->max_vars << 1;
  u32 *cnt = (u32 *)h->wsort; u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig;
  u32 *hp = (u32 *)h->tarjan_mark; u32 *ps = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags; u32 *wvec = (u32 *)h->watch_vec; i8 *vals = (i8 *)h->values;
  u64 i = 0ULL;
  while (i < mx_lits) { cnt[i] = 0u; hp[i] = 0u; ps[i] = 0xFFFFFFFFu; i = i + 1ULL; }
  i = 0ULL; while (i < h->max_vars) { s1[i] = 0ULL; s2[i] = 0ULL; i = i + 1ULL; }
  u32 hlen = 0u; u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1); u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && wvec[((u64)pl << 1) + 1ULL] > 1u) {
        hp[hlen] = pl; ps[pl] = hlen; full_fheap_up(hp, ps, wvec, hlen); hlen = hlen + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && wvec[((u64)nl << 1) + 1ULL] > 1u) {
        hp[hlen] = nl; ps[nl] = hlen; full_fheap_up(hp, ps, wvec, hlen); hlen = hlen + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hlen > 0u && h->cur_vars < h->max_vars && budget > 0ULL && h->oom == 0ULL) {
    u32 f0 = hp[0]; hlen = hlen - 1u; ps[f0] = 0xFFFFFFFFu;
    if (hlen > 0u) {
      hp[0] = hp[hlen]; ps[hp[0]] = 0u; full_fheap_down(hp, ps, wvec, 0u, hlen);
    }
    u32 fv = f0 >> 1; u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u || (fl[fv] & fbit) == 0u || vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit); budget = budget - 1ULL;
    u64 before_cv = h->cur_vars;
    if (full_bva_try_lit(h, f0, before_cv)) {
      u64 check_l = h->cur_vars << 1; u64 ci = 0ULL;
      while (ci < check_l && (u64)hlen < mx_lits) {
        u32 cv_i = (u32)(ci >> 1); u32 cbit = ((ci & 1ULL) != 0ULL) ? FL_FACT_N : FL_FACT_P;
        if ((fl[cv_i] & FL_ACTIVE) != 0u && (fl[cv_i] & cbit) != 0u &&
            wvec[(ci << 1) + 1ULL] > 1u && vals[ci] == (i8)0 && ps[ci] == 0xFFFFFFFFu) {
          hp[hlen] = (u32)ci; ps[ci] = hlen; full_fheap_up(hp, ps, wvec, hlen);
          hlen = hlen + 1u;
        }
        ci = ci + 1ULL;
      }
    }
  }
  i = 0ULL; while (i < (h->cur_vars << 1)) { hp[i] = 0u; ps[i] = 0u; i = i + 1ULL; }
  return 1ULL;
}
"

def bvaHeapModule : LeanQbe.T.Module :=
  { fns := bvaHeap_fns
    externs :=
      [ ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
      , ⟨"full_wstack_defrag", [i64], []⟩
      , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
      , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
      , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
      , ⟨"full_delete_binary", [i64, i32, i32], []⟩ ]
    exits := [] }

theorem full_init_fresh_var_wf : Func.Wf full_init_fresh_var_body := by t_wf_reify
theorem full_bva_hop1_wf : Func.Wf full_bva_hop1_body := by t_wf_reify
theorem full_bva_hop2_wf : Func.Wf full_bva_hop2_body := by t_wf_reify
theorem full_bva_hop3_wf : Func.Wf full_bva_hop3_body := by t_wf_reify
theorem full_bva_match_large_wf : Func.Wf full_bva_match_large_body := by t_wf_reify
theorem full_bva_scan_cands_wf : Func.Wf full_bva_scan_cands_body := by t_wf_reify
theorem full_bva_pick_cand_wf : Func.Wf full_bva_pick_cand_body := by t_wf_reify
theorem full_bva_filter_row_wf : Func.Wf full_bva_filter_row_body := by t_wf_reify
theorem full_bva_commit_wf : Func.Wf full_bva_commit_body := by t_wf_reify
theorem full_bva_try_lit_wf : Func.Wf full_bva_try_lit_body := by t_wf_reify
theorem full_fheap_up_wf : Func.Wf full_fheap_up_body := by t_wf_reify
theorem full_fheap_down_wf : Func.Wf full_fheap_down_body := by t_wf_reify
theorem full_factor_wf : Func.Wf full_factor_body := by t_wf_reify

theorem bvaHeap_fns_wf : ∀ f ∈ bvaHeap_fns, f.Wf := by
  simp only [bvaHeap_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_init_fresh_var_wf, full_bva_hop1_wf, full_bva_hop2_wf, full_bva_hop3_wf,
    full_bva_match_large_wf, full_bva_scan_cands_wf, full_bva_pick_cand_wf,
    full_bva_filter_row_wf, full_bva_commit_wf, full_bva_try_lit_wf,
    full_fheap_up_wf, full_fheap_down_wf, full_factor_wf⟩

theorem bvaHeap_acyclic : bvaHeapModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullBvaHeap
