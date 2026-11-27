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
# Kissat Fidelity Step 13 Shard S5-C — BVA & Factor (`FullFidelityStep13S5BVAFactor`)

Data-pure Step-13 C0 bodies for Shard S5-C (`6` MOD functions, verbatim from
`step13_v2_frozen_direct.c`):
- `full_add_clause` (`L2330-2369`)
- `full_add_bin_m6` (`L9640-9661`)
- `full_delete_binary` (`L9697-9704`)
- `full_bva_scan_cands` (`L22713-22818`)
- `full_bva_commit` (`L22975-23196`)
- `full_factor` (`L23439-23572`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S5BVAFactor "
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

#define PH_GARB               0x00080000u
#define PH_RED                0x00400000u
#define PH_BVA_Q              0x02000000u

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_ACTIVE             1u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_watch_pop_c0(FullHdr *h, u32 lit, u32 cnt);
extern u64  full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 other);
extern u64  full_bva_clines_fid(u64 n);
extern u32  full_bva_steps_cap_fid(u64 cap);
extern void full_wstack_defrag(FullHdr *h);
extern void full_fill_u64_m7(u64 *dst, u64 n, u64 val);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern u64  full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_bva_connect_clauses_fid(FullHdr *h);
extern void full_fheap_up_fid(u32 *hp, u32 *ps, u32 *deg, u32 p);
extern void full_fheap_down_fid(u32 *hp, u32 *ps, u32 *deg, u32 p, u32 n);
extern bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv);
extern u32  full_bva_upd_lit_fid(FullHdr *h, u32 *fheap, u32 *fpos,
                                 u32 *deg, u64 cur_nl, u64 hsz_tl);

u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red) {
  u32 *tmp = (u32 *)h->tmp_lits;
  if (len == 2u) {
    u32 b0 = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (tmp[0] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, tmp[0], b0, 0u, 1u)) { return 0xFFFFFFFFULL; }
    if (!full_watch_push(h, tmp[1], b1, 0u, 1u)) {
      full_watch_pop_c0(h, tmp[0], 1u);
      return 0xFFFFFFFFULL;
    }
    u32 *fl_b = (u32 *)h->flags;
    u32 v0 = tmp[0] >> 1; u32 v1 = tmp[1] >> 1;
    fl_b[v0] = fl_b[v0] | 8u | 16u | (((tmp[0] & 1u) != 0u) ? 64u : 32u);
    fl_b[v1] = fl_b[v1] | 8u | 16u | (((tmp[1] & 1u) != 0u) ? 64u : 32u);
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFEULL;
  }
  if (len < 3u) { return 0xFFFFFFFFULL; }
  u64 cref = full_alloc_cl(h, len, glue, red);
  if (cref == 0xFFFFFFFFULL) { return 0xFFFFFFFFULL; }
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < len) { ar[cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
  if (!full_watch_push(h, tmp[0], tmp[1] & PW_LIT_MASK, (u32)cref, 2u)) {
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (!full_watch_push(h, tmp[1], tmp[0] & PW_LIT_MASK, (u32)cref, 2u)) {
    full_watch_pop_c0(h, tmp[0], 2u);
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (red) {
    h->num_redundant = h->num_redundant + 1ULL;
    if (h->first_reducible == 0xFFFFFFFFULL) { h->first_reducible = cref; }
  } else {
    h->num_irred = h->num_irred + 1ULL;
  }
  return cref;
}

u64 full_add_bin_m6(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == (b ^ 1u)) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[a] > (i8)0 || vals[b] > (i8)0) { return 0ULL; }
  if (vals[a] < (i8)0 && vals[b] < (i8)0) { h->inconsistent = 1ULL; return 20ULL; }
  if (vals[a] < (i8)0 || a == b) { full_assign_lvl(h, b, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (vals[b] < (i8)0) { full_assign_lvl(h, a, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (full_has_bin(h, a, b)) { return 0ULL; }
  u32 b0 = (b & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (a & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, a, b0, 0u, 1u) || !full_watch_push(h, b, b1, 0u, 1u)) {
    h->oom = 1ULL; return 2ULL;
  }
  u32 *fl = (u32 *)h->flags;
  u32 va = a >> 1; u32 vb = b >> 1;
  u32 addf = FL_TRANS | FL_BONE0 | FL_BONE1 | FL_SUBSUME | FL_ELIM_C;
  fl[va] = fl[va] | addf | (((a & 1u) != 0u) ? 64u : 32u);
  fl[vb] = fl[vb] | addf | (((b & 1u) != 0u) ? 64u : 32u);
  h->num_binary = h->num_binary + 1ULL;
  return 1ULL;
}

void full_delete_binary(FullHdr *h, u32 a, u32 b) {
  full_delete_bin_side(h, a, b);
  full_delete_bin_side(h, b, a);
  u32 *fl_d = (u32 *)h->flags;
  fl_d[a >> 1] = fl_d[a >> 1] | FL_ELIM_C | (((a & 1u) != 0u) ? 64u : 32u);
  fl_d[b >> 1] = fl_d[b >> 1] | FL_ELIM_C | (((b & 1u) != 0u) ? 64u : 32u);
  if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
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
          if ((u64)cand <= init_lits && (lm[cand] & (u8)1) == (u8)0 &&
              (fl[cand >> 1] & FL_ACTIVE) != 0u && vals[cand] == (i8)0) {
            if (cnt[cand] == 0u) {
              if ((u64)ncntd < (h->max_vars << 1)) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
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
          if (ok && cand != 0xFFFFFFFFu && (u64)cand <= init_lits &&
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
              if ((u64)ncntd < (h->max_vars << 1)) { cntd[ncntd] = cand; ncntd = ncntd + 1u; }
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
  bool defrag_dirty = false;
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); defrag_dirty = true; }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
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
  u64 garb_add = 0ULL;
  u64 irred_add = 0ULL;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[(dm - 1u) - si];
    if (!defrag_dirty) {
      u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
      u64 sza = (u64)wvec[((u64)fresh << 1) + 1ULL];
      u64 szb = (u64)wvec[((u64)fs << 1) + 1ULL];
      u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
      u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
      if (wl_c == 0ULL || fresh == fs || wc_c < wl_c || wl_c + na + nb > wc_c ||
          ((wl_c + na > 262144ULL || (wl_c + na) * 4ULL >= wc_c * 3ULL) &&
           (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
        defrag_dirty = true;
      }
    }
    u64 pw_b1 = h->wlen;
    u64 br = full_add_bin(h, fresh, fs);
    if (h->wlen < pw_b1) { defrag_dirty = true; }
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    u32 fbit_fs = ((fs & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    fl[fs >> 1] = fl[fs >> 1] | FL_SUBSUME | FL_ELIM_C | fbit_fs;
    fl[fresh >> 1] = fl[fresh >> 1] | FL_SUBSUME | FL_ELIM_C | FL_FACT_P;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[brow_off + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sza = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 szb = (u64)wvec[((u64)q << 1) + 1ULL];
        u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
        u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
        if (wl_c == 0ULL || nf == q || wc_c < wl_c || wl_c + na + nb > wc_c ||
            ((wl_c + na > 262144ULL || (wl_c + na) * 4ULL >= wc_c * 3ULL) &&
             (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      u64 pw_b2 = h->wlen;
      u64 br = full_add_bin(h, fresh ^ 1u, q);
      if (h->wlen < pw_b2) { defrag_dirty = true; }
      u32 fbit_q = ((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
      fl[fresh >> 1] = fl[fresh >> 1] | FL_SUBSUME | FL_ELIM_C | FL_FACT_N;
      fl[q >> 1] = fl[q >> 1] | FL_SUBSUME | FL_ELIM_C | fbit_q;
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      if (!defrag_dirty) {
        u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
        u32 nf = fresh ^ 1u;
        u64 sz0 = (u64)wvec[((u64)nf << 1) + 1ULL];
        u64 sum_nw = (sz0 == 0ULL) ? 2ULL : ((sz0 == 1ULL) ? 3ULL : (sz0 << 1));
        u32 dj = 0u;
        while (dj < csz) {
          u32 dl = ar[(u64)c_top + 3ULL + (u64)dj];
          if (dl != flit) {
            u64 szl = (u64)wvec[((u64)dl << 1) + 1ULL];
            sum_nw = sum_nw + ((szl == 0ULL) ? 2ULL : ((szl == 1ULL) ? 3ULL : (szl << 1)));
          }
          dj = dj + 1u;
        }
        if (wl_c == 0ULL || wc_c < wl_c || wl_c + sum_nw > wc_c ||
            ((wl_c + sum_nw > 262144ULL || (wl_c + sum_nw) * 4ULL >= wc_c * 3ULL) &&
             (wu_c + sum_nw) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      u32 *dst_cl = ar + (ncr + 3ULL);
      if ((ncr & 1ULL) != 0ULL) {
        j = 0u;
        while (j + 2u <= tk) {
          u64 *dp = (u64 *)(dst_cl + (u64)j);
          u64 *sp = (u64 *)(tmp + (u64)j);
          dp[0] = sp[0];
          j = j + 2u;
        }
        if (j < tk) { dst_cl[j] = tmp[j]; }
      } else {
        j = 0u;
        while (j < tk) { dst_cl[j] = tmp[j]; j = j + 1u; }
      }
      j = 0u;
      while (j < tk) {
        u64 pw_l = h->wlen;
        bool wp_l = full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u);
        if (h->wlen < pw_l) { defrag_dirty = true; }
        if (!wp_l) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          garb_add = garb_add + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        u32 fbit_t = ((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
        fl[tv] = fl[tv] | FL_SUBSUME | FL_ELIM_C | fbit_t;
        j = j + 1u;
      }
      if (ok) { irred_add = irred_add + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
    if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
    if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
    return false;
  }
  u32 fs_i = best_k;
  while (fs_i > 0u) {
    u32 ro_prev = scr[sc + (fs_i - 1u)];
    u32 po_s = scr[3u * sc + fs_i];
    u32 po_prev = (fs_i > 1u) ? scr[3u * sc + (fs_i - 1u)] : 0u;
    u32 fi = 0u;
    while (fi < mn) {
      u32 fj = scr[po_s + fi];
      if (fs_i > 1u) { scr[po_prev + fi] = scr[po_prev + fj]; }
      scr[ro_prev + fi] = scr[ro_prev + fj];
      fi = fi + 1u;
    }
    scr[2u * sc + (fs_i - 1u)] = mn;
    fs_i = fs_i - 1u;
  }
  u32 qs = best_k + 1u;
  while (qs > 0u) {
    qs = qs - 1u;
    u32 ro = scr[sc + qs];
    u32 fs = scr[qs];
    m = 0u;
    while (m < mn) {
      u32 cs = scr[ro + m];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          fl[dl >> 1] = fl[dl >> 1] | FL_ELIM_C;
          full_unwatch_large(h, dl, cs);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB;
        garb_add = garb_add + 3ULL + (u64)csz;
      }
      m = m + 1u;
    }
  }
  if (garb_add > 0ULL) { h->arena_garbage = h->arena_garbage + garb_add; }
  if (irred_add > 0ULL) { h->num_irred = h->num_irred + irred_add; }
  if (defrag_dirty) { full_fill_u64_m7((u64 *)cnt, h->cur_vars, 0ULL); }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
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
      u32 *scr_b = (u32 *)h->scratch_buf;
      u32 *ar_b = (u32 *)h->arena;
      u32 sc_b = full_bva_steps_cap_fid(h->scratch_cap);
      u32 bk = (u32)h->res_sz;
      u64 cur_nl = h->cur_vars << 1;
      u8 *tmk = (u8 *)h->lit_mark;
      u32 *tlits = (u32 *)h->work_stk2;
      u64 nt = 0ULL;
      u32 qs_idx = bk + 1u;
      while (qs_idx > 0u) {
        qs_idx = qs_idx - 1u;
        u32 factor = scr_b[qs_idx];
        u32 fneg = factor ^ 1u;
        if ((u64)factor < cur_nl && tmk[factor] == (u8)0 && nt < cur_nl) {
          tmk[factor] = (u8)1; tlits[nt] = factor; nt = nt + 1ULL;
        }
        if ((u64)fneg < cur_nl && tmk[fneg] == (u8)0 && nt < cur_nl) {
          tmk[fneg] = (u8)1; tlits[nt] = fneg; nt = nt + 1ULL;
        }
        u32 ro = scr_b[sc_b + qs_idx];
        u32 qn = scr_b[2u * sc_b + qs_idx];
        u32 qi = 0u;
        while (qi < qn) {
          u32 cw = scr_b[ro + qi];
          if ((cw & PW_BIN_FLAG) != 0u) {
            u32 ol = cw & PW_LIT_MASK;
            if ((u64)ol < cur_nl && tmk[ol] == (u8)0 && nt < cur_nl) {
              tmk[ol] = (u8)1; tlits[nt] = ol; nt = nt + 1ULL;
            }
          } else {
            u32 csz = ar_b[(u64)cw + 2ULL];
            u32 lj = 0u;
            while (lj < csz) {
              u32 l = ar_b[(u64)cw + 3ULL + (u64)lj];
              if (l != factor && (u64)l < cur_nl && tmk[l] == (u8)0 && nt < cur_nl) {
                tmk[l] = (u8)1; tlits[nt] = l; nt = nt + 1ULL;
              }
              lj = lj + 1u;
            }
          }
          qi = qi + 1u;
        }
      }
      u64 ui = 0ULL;
      while (ui < nt) {
        tmk[tlits[ui]] = (u8)0;
        ui = ui + 1ULL;
      }
      ui = 0ULL;
      while (ui < nt) {
        hsz = full_bva_upd_lit_fid(h, fheap, fpos, deg, cur_nl,
          ((u64)hsz << 32) | (u64)tlits[ui]);
        ui = ui + 1ULL;
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
    h->q_search_idx = h->q_last;
    h->q_search_stamp = s;
  }
  return 1ULL;
}
"

/-! ## 1. Canonical `Fn` Handles -/

def fidStep13S5AddClauseFn : Fn :=
  ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], full_add_clause_body⟩

def fidStep13S5AddBinM6Fn : Fn :=
  ⟨"full_add_bin_m6", [i64, i32, i32], [i64], full_add_bin_m6_body⟩

def fidStep13S5DeleteBinaryFn : Fn :=
  ⟨"full_delete_binary", [i64, i32, i32], [], full_delete_binary_body⟩

def fidStep13S5BvaScanCandsFn : Fn :=
  ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], full_bva_scan_cands_body⟩

def fidStep13S5BvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩

def fidStep13S5FactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_body⟩

def fidStep13S5CRepls : List Fn :=
  [ fidStep13S5AddClauseFn
  , fidStep13S5AddBinM6Fn
  , fidStep13S5DeleteBinaryFn
  , fidStep13S5BvaScanCandsFn
  , fidStep13S5BvaCommitFn
  , fidStep13S5FactorFn ]

def fidStep13S5CBefores : List (Sym × List Fn) := []

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_add_clause_s5_wf : Func.Wf fidStep13S5AddClauseFn.body := by t_wf_reify
theorem full_add_bin_m6_s5_wf : Func.Wf fidStep13S5AddBinM6Fn.body := by t_wf_reify
theorem full_delete_binary_s5_wf : Func.Wf fidStep13S5DeleteBinaryFn.body := by t_wf_reify
theorem full_bva_scan_cands_s5_wf : Func.Wf fidStep13S5BvaScanCandsFn.body := by t_wf_reify
theorem full_bva_commit_s5_wf : Func.Wf fidStep13S5BvaCommitFn.body := by t_wf_reify
theorem full_factor_s5_wf : Func.Wf fidStep13S5FactorFn.body := by t_wf_reify

theorem fidStep13S5CRepls_wf : ∀ f ∈ fidStep13S5CRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S5CRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_add_clause_s5_wf
  · exact full_add_bin_m6_s5_wf
  · exact full_delete_binary_s5_wf
  · exact full_bva_scan_cands_s5_wf
  · exact full_bva_commit_s5_wf
  · exact full_factor_s5_wf

theorem fidStep13S5CBefores_wf :
    ∀ h ∈ fidStep13S5CBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp [fidStep13S5CBefores] at hh

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor
