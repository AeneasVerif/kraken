module

public import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M4d BVA / Factoring & Elim Scheduling Upgrades (`FullM4Bva`)

Standalone C0 BVA/factoring and elimination-scheduling upgrades for `D-Full M4`,
preserving the `144`-word `FullHdr` and `FullCfg` arena layout with shared-cache
3-hop tie-breaking, wider clause bounds, and balanced elim/factor orchestration:

1. **Exact Shared-Cache 3-Hop Tie-Breaking (`full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`,
   `full_bva_pick_cand`)**:
   - Guards `s1`/`s2` memo stores on `h->ant_sz > 0ULL` so budget-truncated walks never pollute the
     cache.
   - Shares the `s1`/`s2` memo table across all tied candidates for the same `f0v` in
     `full_bva_pick_cand` with `65536` step budget and `tt < 128` tie cap (up from `256` / `8`),
     clearing `s1`/`s2` once after tie-breaking.
2. **Wider-Clause, Higher-Capacity, Decoupled BVA (`full_bva_filter_row`, `full_bva_commit`,
   `full_bva_try_lit`)**:
   - Lifts the `sz <= 5` clause-size cap to `sz <= 256` (`sz >= 3`) with exact dynamic `need_ar` /
     `need_w` accounting in `full_bva_commit`.
   - Raises matrix capacity from `64 × 16` (`2304` scratch words) to `256 × 32` (`16448` scratch
     words: `[0..31]` factors, `[32..63]` row lengths, `[64..8256)` rows, `[8256..16448)` parents).
   - Decouples factor acceptance (`red > 0` / `red > best_red`) from `h->elim_bound`.
3. **Original-Variable Heap Discipline & Re-Sift (`full_factor` / `full_bva_m4`)**:
   - Keeps `init_cv` as the candidate/heap ceiling within a factoring round so newly created
     auxiliary variables stay in quotient rows without displacing original variables in the
     max-degree factor heap, and re-sifts heap entries after each successful commit.
4. **Balanced Elim/Factor Orchestration (`full_eliminate`, `full_preprocess`)**:
   - Caps `elim_limit` growth with `min(scale_delta, 4000 * isqrt(eliminations) * loge)` (and
     initial `min(scale_delta(120), 6000)`), widens factor budget (`512..1024`), and runs
     `full_factor` both before and after `full_elim_bve` so BVE does not fracture aligned cliques
     before S-BVA re-encoding.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bva

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m4Bva "
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
#define FL_FACT_P  32u
#define FL_FACT_N  64u

extern u64 full_isqrt(u64 x);
extern u64 full_ilog10(u64 x);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern bool full_bva_match_large(FullHdr *h, u32 cur_cr, u32 next_lit, u32 d_ref);
extern u32 full_bva_scan_cands(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits);
extern void full_fheap_up(u32 *hp, u32 *ps, u32 *wvec, u32 p);
extern void full_fheap_down(u32 *hp, u32 *ps, u32 *wvec, u32 p, u32 n);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_elim_bve(FullHdr *h, u64 bve_lim);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_probe(FullHdr *h, bool initial);

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
  if (h->ant_sz > 0ULL) {
    if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
    s1[sidx] = res + 1ULL;
    if (h->tmp_cnt < cv) { st1[h->tmp_cnt] = sidx; h->tmp_cnt = h->tmp_cnt + 1ULL; }
  }
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
  if (h->ant_sz > 0ULL) {
    if (res > 0x3FFFFFFFFFFFFFFFULL) { res = 0x3FFFFFFFFFFFFFFFULL; }
    s2[sidx] = res + 1ULL;
    if (h->tmp_len < cv) { st2[h->tmp_len] = sidx; h->tmp_len = h->tmp_len + 1ULL; }
  }
  return res;
}

u64 full_bva_hop3(FullHdr *h, u32 src_lit, u32 dst_idx) {
  u32 sidx = src_lit >> 1; u64 res = (sidx == dst_idx) ? 1ULL : 0ULL;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
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
  return res;
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
    h->ant_sz = 65536ULL; h->tmp_cnt = 0ULL; h->tmp_len = 0ULL;
    while (ci < ncntd && tt < 128u) {
      u32 clit = cntd[ci];
      if (cnt[clit] == best_c) {
        tt = tt + 1u;
        u64 sc = full_bva_hop3(h, clit, f0v);
        u32 deg = wvec[((u64)clit << 1) + 1ULL];
        if (tt == 1u || sc > best_sc || (sc == best_sc && deg > best_deg)) {
          best_sc = sc; best_deg = deg; best_lit = clit;
        }
      }
      ci = ci + 1u;
    }
    u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig;
    u32 *st1 = (u32 *)h->min_clr; u32 *st2 = (u32 *)h->shrink_stk;
    u64 i = 0ULL; while (i < h->tmp_cnt) { s1[st1[i]] = 0ULL; i = i + 1ULL; }
    i = 0ULL; while (i < h->tmp_len) { s2[st2[i]] = 0ULL; i = i + 1ULL; }
    h->tmp_cnt = 0ULL; h->tmp_len = 0ULL;
  }
  ci = 0u; while (ci < ncntd) { cnt[cntd[ci]] = 0u; ci = ci + 1u; }
  return (best_c < 2u) ? 0xFFFFFFFFu : best_lit;
}

u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
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
  u32 dm = best_k + 1u; u32 mn = scr[32u + best_k];
  u64 need_ar = 16ULL; u64 need_w = ((u64)dm + 8ULL) * 4ULL;
  u32 m = 0u;
  while (m < mn) {
    u32 c_top = scr[64u + best_k * 256u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      need_w = need_w + 8ULL;
    } else {
      u64 csz = (u64)ar[(u64)c_top + 2ULL];
      need_ar = need_ar + 3ULL + csz;
      need_w = need_w + csz * 4ULL;
    }
    m = m + 1u;
  }
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
  m = 0u;
  while (m < mn) {
    u32 idx = m; u32 c_top = scr[64u + best_k * 256u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      full_add_bin(h, fresh ^ 1u, q);
      fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
    } else {
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
      u32 cs = scr[64u + s * 256u + idx]; u32 fs = scr[s];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      if (s == 0u) { break; }
      idx = scr[8256u + s * 256u + idx]; s = s - 1u;
    }
    m = m + 1u;
  }
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si]; full_add_bin(h, fresh, fs);
    fl[fs >> 1] = fl[fs >> 1] | (((fs & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
    si = si + 1u;
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < 16448ULL) { return false; }
  i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  if (init_cv > h->cur_vars) { init_cv = h->cur_vars; }
  u32 qn = 0u; u64 off = (u64)wvec[(u64)f0 << 1]; u64 end = off + (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 p = off;
  while (p < end && qn < 256u) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { scr[64u + qn] = w0; qn = qn + 1u; }
    } else if (p < end) {
      u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
      if ((ar[cr] & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 256u) {
        u32 hk = 0u; bool has_f0 = false; bool sat = false;
        while (hk < sz) {
          u32 hl = ar[(u64)cr + 3ULL + (u64)hk];
          if (vals[hl] > (i8)0) { sat = true; break; }
          if (hl == f0) { has_f0 = true; }
          hk = hk + 1u;
        }
        if (has_f0 && !sat) { scr[64u + qn] = cr; qn = qn + 1u; }
      }
    }
  }
  if (qn < 2u) { return false; }
  u64 init_lits = init_cv << 1;
  scr[0] = f0; scr[32] = qn; lm[f0] = (u8)1;
  u32 step = 1u; u32 cur_qn = qn; u32 best_k = 0u; u64 best_red = 0ULL;
  while (step < 32u && cur_qn >= 2u) {
    u32 ncntd = full_bva_scan_cands(h, 64u + (step - 1u) * 256u, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu) { break; }
    u32 new_qn = full_bva_filter_row(h, 64u + (step - 1u) * 256u, 64u + step * 256u,
      8256u + step * 256u, cur_qn, best_lit);
    if (new_qn < 2u) { break; }
    scr[step] = best_lit; scr[32u + step] = new_qn; lm[best_lit] = (u8)1;
    u64 dm = (u64)(step + 1u); u64 mn = (u64)new_qn;
    if (dm * mn > dm + mn) {
      u64 red = dm * mn - (dm + mn);
      if (red > best_red) { best_red = red; best_k = step; }
    }
    cur_qn = new_qn; step = step + 1u;
  }
  u32 si = 0u;
  while (si < step) { lm[scr[si]] = lm[scr[si]] & (u8)0xFE; si = si + 1u; }
  if (best_k == 0u) { return false; }
  u32 *touched = (u32 *)h->work_stk2; u32 *tcnt = (u32 *)h->wsort;
  u64 tcap = h->cur_vars << 1; u64 nt = 0ULL; u32 dm = best_k + 1u; u32 ti = 0u;
  while (ti < dm) {
    u32 flit = scr[ti];
    if (tcnt[flit] == 0u && nt < tcap) { tcnt[flit] = 1u; touched[nt] = flit; nt = nt + 1ULL; }
    u32 nflit = flit ^ 1u;
    if (tcnt[nflit] == 0u && nt < tcap) { tcnt[nflit] = 1u; touched[nt] = nflit; nt = nt + 1ULL; }
    ti = ti + 1u;
  }
  u32 mn = scr[32u + best_k]; u32 bk_lit = scr[best_k]; u32 tm = 0u;
  while (tm < mn) {
    u32 c_top = scr[64u + best_k * 256u + tm];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 ql = c_top & PW_LIT_MASK;
      if (tcnt[ql] == 0u && nt < tcap) { tcnt[ql] = 1u; touched[nt] = ql; nt = nt + 1ULL; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 tj = 0u;
      while (tj < csz) {
        u32 ql = ar[(u64)c_top + 3ULL + (u64)tj];
        if (ql != bk_lit && tcnt[ql] == 0u && nt < tcap) {
          tcnt[ql] = 1u; touched[nt] = ql; nt = nt + 1ULL;
        }
        tj = tj + 1u;
      }
    }
    tm = tm + 1u;
  }
  u64 tz = 0ULL;
  while (tz < nt) { tcnt[touched[tz]] = 0u; tz = tz + 1ULL; }
  h->res_sz = nt;
  return full_bva_commit(h, best_k);
}

u64 full_factor(FullHdr *h, u64 budget) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < 16448ULL || budget == 0ULL) { return 1ULL; }
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
    if (full_bva_try_lit(h, f0, init_cv)) {
      u64 check_l = init_cv << 1;
      u32 *touched = (u32 *)h->work_stk2;
      u64 nt = h->res_sz;
      if (nt > check_l) { nt = check_l; }
      u64 ti = 0ULL;
      while (ti < nt) {
        u32 tl = touched[ti];
        if ((u64)tl < check_l) {
          u32 pos_tl = ps[tl];
          if (pos_tl < hlen) {
            full_fheap_up(hp, ps, wvec, pos_tl);
            u32 pos2 = ps[tl];
            if (pos2 < hlen) { full_fheap_down(hp, ps, wvec, pos2, hlen); }
          } else if ((u64)hlen < mx_lits) {
            u32 tv = tl >> 1; u32 tbit = ((tl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
            if ((fl[tv] & FL_ACTIVE) != 0u && (fl[tv] & tbit) != 0u &&
                wvec[((u64)tl << 1) + 1ULL] > 1u && vals[tl] == (i8)0 &&
                pos_tl == 0xFFFFFFFFu) {
              hp[hlen] = tl; ps[tl] = hlen; full_fheap_up(hp, ps, wvec, hlen);
              hlen = hlen + 1u;
            }
          }
        }
        ti = ti + 1ULL;
      }
    }
  }
  i = 0ULL; while (i < (h->cur_vars << 1)) { hp[i] = 0u; ps[i] = 0u; i = i + 1ULL; }
  if (h->cur_vars > init_cv) {
    u64 fcv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
    u64 qst = 0ULL; u64 qidx = h->q_first;
    while (qidx < fcv && qst < fcv) {
      qst = qst + 1ULL; qs[qidx] = (u32)qst;
      qidx = (u64)qn[qidx];
    }
    h->q_cur_stamp = qst;
    if (h->q_last < fcv) {
      h->q_search_idx = h->q_last;
      h->q_search_stamp = (u64)qs[h->q_last];
    }
  }
  return 1ULL;
}

u64 full_eliminate(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    u64 d_scale = full_scale_delta(h, 250ULL * h->eliminations * loge);
    u64 d_cap = 4000ULL * full_isqrt(h->eliminations) * loge;
    h->elim_limit = h->conflicts + full_min_u64(d_scale, d_cap);
    if (h->eliminations >= 2ULL && h->elim_bound < 8ULL) {
      h->elim_bound = h->elim_bound + 2ULL;
    }
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u64 fact_bud = full_min_u64(initial ? 512ULL : (64ULL + (dticks >> 9)), 1024ULL);
  if (h->num_binary > 0ULL || h->num_irred <= 4096ULL) {
    full_factor(h, fact_bud);
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 4096ULL)) {
    full_factor(h, fact_bud);
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_preprocess(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_min_u64(full_scale_delta(h, 120ULL), 6000ULL);
  if (full_probe(h, true) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_min_u64(full_scale_delta(h, 120ULL), 6000ULL);
  return 1ULL;
}
"

/-- External callee signatures referenced by `m4Bva_fns`. -/
def m4BvaExterns : List Extern :=
  [ ⟨"full_isqrt", [i64], [i64]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_init_fresh_var", [i64, i32], []⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32]⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], []⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], []⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_forward_sub", [i64, i64], [i64]⟩
  , ⟨"full_elim_bve", [i64, i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"full_probe", [i64, .bool], [i64]⟩ ]

/-- Standalone M4d BVA/elim module (`10` upgraded functions, all external callees explicit). -/
def m4BvaModule : LeanQbe.T.Module :=
  { fns := m4Bva_fns, externs := m4BvaExterns, exits := [] }

theorem full_bva_hop1_wf : Func.Wf full_bva_hop1_body := by t_wf_reify
theorem full_bva_hop2_wf : Func.Wf full_bva_hop2_body := by t_wf_reify
theorem full_bva_hop3_wf : Func.Wf full_bva_hop3_body := by t_wf_reify
theorem full_bva_pick_cand_wf : Func.Wf full_bva_pick_cand_body := by t_wf_reify
theorem full_bva_filter_row_wf : Func.Wf full_bva_filter_row_body := by t_wf_reify
theorem full_bva_commit_wf : Func.Wf full_bva_commit_body := by t_wf_reify
theorem full_bva_try_lit_wf : Func.Wf full_bva_try_lit_body := by t_wf_reify
theorem full_factor_wf : Func.Wf full_factor_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify

theorem m4Bva_fns_wf : ∀ f ∈ m4Bva_fns, f.Wf := by
  simp only [m4Bva_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_bva_hop1_wf, full_bva_hop2_wf, full_bva_hop3_wf, full_bva_pick_cand_wf,
    full_bva_filter_row_wf, full_bva_commit_wf, full_bva_try_lit_wf, full_factor_wf,
    full_eliminate_wf, full_preprocess_wf⟩

theorem m4Bva_acyclic : m4BvaModule.checkAcyclic = true := by
  t_kernel_rfl

/-! ## Named `Fn` Handles & Splicing onto Unified `FullM3.m3Fns` (`204` → `204` Functions) -/

def m4Hop1Fn : Fn := ⟨"full_bva_hop1", [i64, i32, i32], [i64], full_bva_hop1_body⟩
def m4Hop2Fn : Fn := ⟨"full_bva_hop2", [i64, i32, i32], [i64], full_bva_hop2_body⟩
def m4Hop3Fn : Fn := ⟨"full_bva_hop3", [i64, i32, i32], [i64], full_bva_hop3_body⟩
def m4PickCandFn : Fn := ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], full_bva_pick_cand_body⟩
def m4FilterRowFn : Fn :=
  ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], full_bva_filter_row_body⟩
def m4CommitFn : Fn := ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩
def m4TryLitFn : Fn := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], full_bva_try_lit_body⟩
def m4FactorFn : Fn := ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩
def m4EliminateFn : Fn := ⟨"full_eliminate", [i64, .bool], [i64], full_eliminate_body⟩
def m4PreprocessFn : Fn := ⟨"full_preprocess", [i64], [i64], full_preprocess_body⟩

/-- Canonical alias for the upgraded M4d BVA factoring driver. -/
abbrev full_bva_m4 : Fn := m4FactorFn

/-- Name-directed 1-to-1 splice replacing the `10` upgraded BVA/elim functions in `FullM3.m3Fns`. -/
def m4BvaSplice (f : Fn) : Fn :=
  if f.name = "full_bva_hop1" then m4Hop1Fn
  else if f.name = "full_bva_hop2" then m4Hop2Fn
  else if f.name = "full_bva_hop3" then m4Hop3Fn
  else if f.name = "full_bva_pick_cand" then m4PickCandFn
  else if f.name = "full_bva_filter_row" then m4FilterRowFn
  else if f.name = "full_bva_commit" then m4CommitFn
  else if f.name = "full_bva_try_lit" then m4TryLitFn
  else if f.name = "full_factor" then m4FactorFn
  else if f.name = "full_eliminate" then m4EliminateFn
  else if f.name = "full_preprocess" then m4PreprocessFn
  else f

/-- Complete closed `204`-function M4d Kissat function list in strict topological call order. -/
def m4BvaFullFns : List Fn := FullM3.m3Fns.map m4BvaSplice

/-- Complete closed `204`-function M4d Kissat module (`externs := []`, `exits := []`). -/
def m4BvaFullModule : LeanQbe.T.Module :=
  { fns := m4BvaFullFns, externs := [], exits := [] }

theorem m4BvaSplice_wf (f : Fn) (hf : f.Wf) : (m4BvaSplice f).Wf := by
  unfold m4BvaSplice
  split; · exact full_bva_hop1_wf
  split; · exact full_bva_hop2_wf
  split; · exact full_bva_hop3_wf
  split; · exact full_bva_pick_cand_wf
  split; · exact full_bva_filter_row_wf
  split; · exact full_bva_commit_wf
  split; · exact full_bva_try_lit_wf
  split; · exact full_factor_wf
  split; · exact full_eliminate_wf
  split; · exact full_preprocess_wf
  exact hf

theorem m4BvaFullFns_wf : ∀ f ∈ m4BvaFullFns, f.Wf := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  exact m4BvaSplice_wf f (FullM3.m3Fns_wf f hf)

theorem m4BvaFullFns_length : m4BvaFullFns.length = 204 := by
  rw [m4BvaFullFns, List.length_map, FullM3.m3Fns_length]

theorem m4BvaFull_acyclic : m4BvaFullModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4Bva
