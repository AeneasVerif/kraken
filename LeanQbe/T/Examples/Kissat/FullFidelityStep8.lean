/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 8 Upstream Parity & Hotspot Closure (`FullFidelityStep8`)

Additive pure-C0 replacements (`5` functions, `0` externs, `0` exits) atop Step 7
`fidStep7Module` (`501` fns):
1. `full_walk_effort_m7` (`kimits.h:135-170`, `walk.c:413`): use `h->fwd_str_cnt`
   (`last_elim_ticks`) instead of `mode_saved_ticks`, and `500000ULL` minimum effort floor.
2. `full_watch_push_slow_m6` & `full_watch_push_m6` (`collect.h:22` `defraglim=75`): upgrade
   proactive defrag threshold from `25%` (`wlen`) to `75%` (`wlen * 3ULL`) while preserving
   on-demand defrag when `ncap > wcap - wlen`.
3. `full_delete_bin_side`: read-only scan for `(w0 & PW_BIN_FLAG) && (w0 & PW_LIT_MASK) == other`,
   then tight left-shift, `0xFFFFFFFFu` sentinel store, `sz - 1`, and `wusable += 1`.
4. `full_bva_commit`: track `defrag_dirty` conservatively across initial defrag and watch pushes,
   skipping the `cnt[0..2*cur_vars] = 0` wipe when `full_wstack_defrag*` could not execute.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
open LeanQbe.T.Examples.Kissat.PatchModule

kissat_c0! fidStep8 "
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

#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define PH_GARB               0x00080000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern void full_wstack_defrag_m6(FullHdr *h);
extern u32 full_bva_steps_cap_fid(u64 cap);
extern void full_wstack_defrag(FullHdr *h);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);

u64 full_walk_effort_m7(FullHdr *h, u64 max_flips) {
  u64 st = h->search_ticks;
  u64 mt = h->fwd_str_cnt;
  u64 dt = (st > mt) ? (st - mt) : 0ULL;
  u64 eff = 40000000ULL;
  if (dt <= 800000000ULL) { eff = dt / 20ULL; }
  if (eff < 500000ULL) { eff = 500000ULL; }
  if (eff > 40000000ULL) { eff = 40000000ULL; }
  return eff;
}

bool full_watch_push_slow_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  bool retry_fast = false;
  if (h->wlen == 0ULL) {
    if (h->wcap < 1ULL) { return false; }
    u32 *wstk0 = (u32 *)h->watch_stk;
    wstk0[0] = 0u;
    h->wlen = 1ULL;
    retry_fast = true;
  }
  if (h->wlen * 4ULL >= h->wcap * 3ULL && h->wusable * 4ULL >= h->wlen * 3ULL) {
    full_wstack_defrag_m6(h);
    retry_fast = true;
  }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen && h->wusable > 0ULL) { full_wstack_defrag_m6(h); }
    if (c > wcap - h->wlen) { return false; }
    u64 pos = h->wlen;
    wstk[pos] = w0;
    if (cnt == 2u) { wstk[pos + 1ULL] = w1; }
    wvec[(u64)lit << 1] = (u32)pos;
    wvec[((u64)lit << 1) + 1ULL] = cnt;
    h->wlen = pos + c;
    return true;
  }
  if (retry_fast) {
    u64 end = off + sz;
    if (end == h->wlen && c <= wcap - h->wlen) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      h->wlen = end + c;
      return true;
    }
    if (end + c <= h->wlen && wstk[end] == 0xFFFFFFFFu &&
        (cnt == 1u || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      if (h->wusable >= c) { h->wusable = h->wusable - c; }
      return true;
    }
  }
  u64 ncap = (sz == 0ULL) ? 2ULL : (sz << 1);
  if (ncap < sz + c) { ncap = sz + c; }
  if (ncap > wcap - h->wlen) {
    if (h->wusable > 0ULL) {
      full_wstack_defrag_m6(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k];
    wstk[off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wstk[dst + sz] = w0;
  if (cnt == 2u) { wstk[dst + sz + 1ULL] = w1; }
  k = sz + c;
  while (k < ncap) { wstk[dst + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[(u64)lit << 1] = (u32)dst;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
  h->wusable = h->wusable + sz + (ncap - (sz + c));
  h->wlen = dst + ncap;
  return true;
}

bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  u64 c = (u64)cnt;
  u64 wlen = h->wlen;
  if (wlen != 0ULL && (wlen * 4ULL < h->wcap * 3ULL || h->wusable * 4ULL < wlen * 3ULL)) {
    u64 l2 = (u64)lit << 1;
    u32 *wvec0 = (u32 *)h->watch_vec;
    u64 off = (u64)wvec0[l2];
    u64 sz = (u64)wvec0[l2 + 1ULL];
    u64 end = off + sz;
    if (end > 0ULL) {
      u32 *wstk = (u32 *)h->watch_stk;
      if (end + c <= wlen && wstk[end] == 0xFFFFFFFFu &&
          (c == 1ULL || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        if (h->wusable >= c) { h->wusable = h->wusable - c; }
        return true;
      }
      if (end == wlen && c <= h->wcap - wlen) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        h->wlen = end + c;
        return true;
      }
    } else if (c <= h->wcap - wlen) {
      u32 *wstk = (u32 *)h->watch_stk;
      wstk[wlen] = w0;
      if (c == 2ULL) { wstk[wlen + 1ULL] = w1; }
      u32 *wvec = (u32 *)h->watch_vec;
      wvec[l2] = (u32)wlen;
      wvec[l2 + 1ULL] = (u32)c;
      h->wlen = wlen + c;
      return true;
    }
  }
  return full_watch_push_slow_m6(h, lit, w0, w1, (u32)c);
}

void full_delete_bin_side(FullHdr *h, u32 lit, u32 other) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz == 0ULL) { return; }
  u64 p = off;
  u64 end = off + sz;
  bool removed = false;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == other) { removed = true; break; }
    } else if (p < end) {
      p = p + 1ULL;
    }
  }
  if (!removed) { return; }
  while (p < end) {
    wstk[p - 1ULL] = wstk[p];
    p = p + 1ULL;
  }
  wstk[end - 1ULL] = 0xFFFFFFFFu;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - 1ULL);
  h->wusable = h->wusable + 1ULL;
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
      if (defrag_dirty) {
        u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
        while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
      }
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
    if (!defrag_dirty) {
      u64 wl_c = h->wlen; u64 wu_c = h->wusable; u64 wc_c = h->wcap;
      u64 sza = (u64)wvec[((u64)fresh << 1) + 1ULL];
      u64 szb = (u64)wvec[((u64)fs << 1) + 1ULL];
      u64 na = (sza == 0ULL) ? 2ULL : (sza << 1);
      u64 nb = (szb == 0ULL) ? 2ULL : (szb << 1);
      if (wl_c == 0ULL || fresh == fs || wc_c < wl_c || wl_c + na + nb > wc_c ||
          ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
        defrag_dirty = true;
      }
    }
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | (((fs & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
    fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_P;
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
            ((wl_c + na) * 4ULL >= wc_c * 3ULL && (wu_c + na) * 4ULL >= wl_c * 3ULL)) {
          defrag_dirty = true;
        }
      }
      u64 br = full_add_bin(h, fresh ^ 1u, q);
      fl[fresh >> 1] = fl[fresh >> 1] | FL_FACT_N;
      fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
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
            ((wl_c + sum_nw) * 4ULL >= wc_c * 3ULL &&
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
    if (defrag_dirty) {
      u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
    }
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
          full_unwatch_large(h, dl, cs);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      m = m + 1u;
    }
  }
  if (defrag_dirty) {
    u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
    while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  }
  deg[fresh] = dm; deg[fresh ^ 1u] = mn;
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}
"

/-! ## 1. Canonical `Fn` Handles, Replacement List & Module (`501` fns) -/

/-- Step-8 `"full_walk_effort_m7"` using `last_elim_ticks` (`fwd_str_cnt`) and `500k` floor. -/
def fidStep8WalkEffortM7Fn : Fn :=
  ⟨"full_walk_effort_m7", [i64, i64], [i64], full_walk_effort_m7_body⟩

/-- Step-8 `"full_watch_push_slow_m6"` using upstream `75%` defrag threshold (`3/4 * wlen`). -/
def fidStep8WatchPushSlowM6Fn : Fn :=
  ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool], full_watch_push_slow_m6_body⟩

/-- Step-8 `"full_watch_push_m6"` using upstream `75%` defrag threshold (`3/4 * wlen`). -/
def fidStep8WatchPushM6Fn : Fn :=
  ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], full_watch_push_m6_body⟩

/-- Step-8 `"full_delete_bin_side"` with read-only scan then tight left-shift. -/
def fidStep8DeleteBinSideFn : Fn :=
  ⟨"full_delete_bin_side", [i64, i32, i32], [], full_delete_bin_side_body⟩

/-- Step-8 `"full_bva_commit"` skipping redundant `cnt` wipe when defrag could not run. -/
def fidStep8BvaCommitFn : Fn :=
  ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_body⟩

/-- Exact `5`-function Step-8 replacement list over `fidStep7Fns`. -/
def fidStep8Repls : List Fn :=
  [ fidStep8WalkEffortM7Fn
  , fidStep8WatchPushSlowM6Fn
  , fidStep8WatchPushM6Fn
  , fidStep8DeleteBinSideFn
  , fidStep8BvaCommitFn ]

/-- Empty helper insertion list (`fidStep8Module` remains `501` functions). -/
def fidStep8Befores : List (Sym × List Fn) := []

/-- Ordered `501`-fn Step-8 `KissatFidelity` function list (`patchFns` over `fidStep7Fns`). -/
def fidStep8ModuleFns : List Fn :=
  patchFns fidStep8Repls [] fidStep7Fns

/-- Closed `501`-function Gate-1 Step-8 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep8Module : LeanQbe.T.Module :=
  { fidStep7Module with fns := fidStep8ModuleFns }

theorem fidStep8ModuleFns_eq : fidStep8Module.fns = fidStep8ModuleFns :=
  rfl

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Exit-Freedom -/

theorem full_walk_effort_m7_step8_wf : Func.Wf fidStep8WalkEffortM7Fn.body := by t_wf_reify
theorem full_watch_push_slow_m6_step8_wf :
    Func.Wf fidStep8WatchPushSlowM6Fn.body := by
  t_wf_reify
theorem full_watch_push_m6_step8_wf : Func.Wf fidStep8WatchPushM6Fn.body := by t_wf_reify
theorem full_delete_bin_side_step8_wf : Func.Wf fidStep8DeleteBinSideFn.body := by t_wf_reify
theorem full_bva_commit_step8_wf : Func.Wf fidStep8BvaCommitFn.body := by t_wf_reify

theorem fidStep8Repls_wf : ∀ f ∈ fidStep8Repls, f.Wf := by
  intro f hf
  simp only [fidStep8Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_walk_effort_m7_step8_wf
  · exact full_watch_push_slow_m6_step8_wf
  · exact full_watch_push_m6_step8_wf
  · exact full_delete_bin_side_step8_wf
  · exact full_bva_commit_step8_wf

theorem fidStep8Module_wf : ∀ f ∈ fidStep8Module.fns, f.Wf :=
  patchFns_wf fidStep7Module_wf fidStep8Repls_wf (fun _ h => by simp at h)

theorem fidStep8_noExit : fidStep8Module.exits = [] :=
  fidStep7_noExit

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
