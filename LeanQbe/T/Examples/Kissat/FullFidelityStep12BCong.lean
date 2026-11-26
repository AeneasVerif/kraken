/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 12B — Congruence Scaling & Wide-AND Parity (`FullFidelityStep12BCong`)

Data-pure additive C0 layer (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, `0` new `FullWitnessInv`
conjuncts, every function `<= 6` args) implementing `P0-4` pure Kissat 4.0.4 congruence fixes
(`src/options.h:26`, `src/congruence.c:2338-2370,2532`):
1. **Single-pass `O(D)` marked `WATCHES(not_lhs)` scan + inner tick metering**
   (`full_cong_extract_and_clause_fid`, `full_cong_extract_from_fid`, `full_cong_extract`):
   marks candidate clause literals in `lit_mark`, scans `WATCHES(not_lhs)` once per surviving LHS
   candidate (shortest watch list first, bit-2 candidate pruning) with per-watch tick metering via
   `h->res_sz`, eliminating un-metered `O(usz^2 * D)` `full_has_bin` loops.
2. **Lift `AND <= 64` arity cap up to `congruenceandarity` (`1,000,000`):**
   - Narrow AND (`arity <= 64`), XOR, and ITE keep `tag ∈ {0, 1, 2}` and 8-bit `meta & 0xFFu`;
     wide AND (`65 <= arity <= 1,000,000`) uses `tag = 3` and 28-bit `meta & 0x0FFFFFFFu`.
   - `full_cong_and_match` replaces the 64-bit bitmask with an `O(ea + ua)` `lit_mark` + `u32`
     match counter supporting arbitrary wide AND gates (`arity <= 1,000,000`).
   - `full_cong_eval_gate` & `full_cong_worklist` lift arity `64 -> 1,000,000` and switch
     occurrence nodes to 3 words `(gn, raw_lit, nxt)` to eliminate 8-bit `slot_i` overflow.
3. **Dynamic `occ_bkt` sizing (`full_congruence_dense`, `full_cong_enq_var`,
   `full_cong_worklist`):**
   scales `occ_bkt` dynamically as a power of 2 up to `1,048,576` (bounded by `< 2 * cur_vars` and
   `<= rem_occ / 16`) to avoid hash-bucket collisions at `517k` variables.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep12BCong "
#define PH_GARB               0x00080000u
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define CONG_ARITY_MASK       0x0FFFFFFFu
#define CONG_AND_ARITY_MAX    1000000u
#define CONG_AND_USZ_MAX      1000001u

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

extern u32 full_arena_next(FullHdr *h, u32 p);
extern void full_sort_u32(u32 *a, u32 n);
extern u32 full_cong_find(u32 *repr, u32 l);
extern u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep);
extern u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep);
extern void full_cong_count_bins(FullHdr *h);
extern u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim);
extern u64 full_cong_find_units_equivs(FullHdr *h);
extern u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap);
extern u64 full_cong_extract_xor_k(FullHdr *h, u32 k, u32 neg_p, u64 g_len, u64 g_cap);
extern u32 full_cong_xor_match(FullHdr *h, u32 ent, u32 ua);
extern u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim);
extern u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim);

u64 full_cong_extract_and_clause_fid(FullHdr *h, u32 usz, u64 g_len, u64 g_cap, u64 tick_lim) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (usz < 3u || usz > CONG_AND_USZ_MAX || (u64)usz > cv) { return g_len; }
  u32 arity = usz - 1u;
  if (g_len > g_cap || g_cap - g_len < 2ULL + (u64)arity) { return g_len; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *nbc = (u32 *)h->work_stk1;
  u32 *base = (u32 *)h->work_stk2;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u8 *lm = (u8 *)h->lit_mark;
  u32 first_i = usz;
  u32 min_d = 0xFFFFFFFFu;
  u32 m = 0u;
  while (m < usz) {
    u32 bm = base[m];
    u32 nbm = bm ^ 1u;
    if (nbc[bm] >= arity) {
      lm[nbm] = (u8)5;
      u32 d = wvec[((u64)nbm << 1) + 1ULL];
      if (first_i == usz || d < min_d) { min_d = d; first_i = m; }
    } else {
      lm[nbm] = (u8)1;
    }
    m = m + 1u;
  }
  u64 ticks = h->res_sz;
  if (first_i < usz) {
    u32 step = 0u;
    while (step < usz && g_len + 2ULL + (u64)arity <= g_cap && ticks < tick_lim) {
      u32 i = (step == 0u) ? first_i : ((step <= first_i) ? (step - 1u) : step);
      u32 lhs = base[i];
      u32 not_lhs = lhs ^ 1u;
      if ((lm[not_lhs] & (u8)4) != (u8)0) {
        u64 off = (u64)wvec[(u64)not_lhs << 1];
        u64 end = off + (u64)wvec[((u64)not_lhs << 1) + 1ULL];
        u64 wp = off;
        u32 matched = 0u;
        while (wp < end && ticks < tick_lim) {
          u32 w0 = wstk[wp]; wp = wp + 1ULL;
          ticks = ticks + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits && ot != not_lhs && (lm[ot] & (u8)3) == (u8)1) {
              lm[ot] = lm[ot] | (u8)2;
              matched = matched + 1u;
            }
          } else {
            if (wp >= end) { break; }
            wp = wp + 1ULL;
          }
        }
        if (matched == arity) {
          scr[g_len] = lhs;
          scr[g_len + 1ULL] = (arity <= 64u) ? arity : ((3u << 28) | arity);
          u32 rk = 0u; u32 j = 0u;
          while (j < usz) {
            if (j != i) { scr[g_len + 2ULL + (u64)rk] = base[j] ^ 1u; rk = rk + 1u; }
            j = j + 1u;
          }
          g_len = g_len + 2ULL + (u64)arity;
        }
        m = 0u;
        while (m < usz) {
          u32 nbm = base[m] ^ 1u;
          u8 mv = lm[nbm];
          if ((mv & (u8)2) != (u8)0) { lm[nbm] = mv & (u8)5; }
          else { lm[nbm] = (u8)1; }
          m = m + 1u;
        }
      }
      step = step + 1u;
    }
  }
  m = 0u;
  while (m < usz) { lm[base[m] ^ 1u] = (u8)0; m = m + 1u; }
  h->res_sz = ticks;
  return g_len;
}

u64 full_cong_extract_from_fid(FullHdr *h, u64 g_start, u64 g_cap, u64 tick_lim) {
  if (g_start > g_cap) { return g_start; }
  full_cong_count_bins(h);
  u32 *ar = (u32 *)h->arena;
  u32 *nbc = (u32 *)h->work_stk1;
  u32 *base = (u32 *)h->work_stk2;
  u32 *rr = (u32 *)h->red_refs;
  i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars;
  u64 rcap = h->red_cap;
  u64 p = 0ULL;
  u64 g_len = g_start;
  u64 ticks = 0ULL;
  u64 wn = 0ULL;
  while (p < h->arena_len && g_len + 4ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 min_nbc = 0xFFFFFFFFu;
      u32 neg_p = 0u; bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if (usz >= CONG_AND_USZ_MAX || (u64)usz >= cv) { sat = true; break; }
          base[usz] = l; usz = usz + 1u;
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if (c_n < min_nbc) { min_nbc = c_n; }
          if ((l & 1u) != 0u) { neg_p = neg_p ^ 1u; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 3u && usz <= 65u && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity) {
          h->res_sz = ticks;
          g_len = full_cong_extract_and_clause_fid(h, usz, g_len, g_cap, tick_lim);
          ticks = h->res_sz;
        }
        if (usz == 3u && g_len + 12ULL <= g_cap) {
          g_len = full_cong_try_xor_ite(h, base[0], base[1], base[2], g_len, g_cap);
          ticks = ticks + 4ULL;
        } else if (usz >= 4u && usz <= 5u && g_len + (u64)usz * (u64)(usz + 1u) <= g_cap) {
          g_len = full_cong_extract_xor_k(h, usz, neg_p, g_len, g_cap);
          ticks = ticks + 8ULL;
        }
      } else if (!sat && usz >= 66u && usz <= CONG_AND_USZ_MAX && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity && wn < rcap) {
          rr[wn] = (u32)p; wn = wn + 1ULL;
        }
      }
    }
    p = np;
  }
  u64 wi = 0ULL;
  while (wi < wn && g_len + 4ULL <= g_cap && ticks < tick_lim) {
    u64 wp = (u64)rr[wi];
    u32 hdr = ar[wp]; u32 sz = ar[wp + 2ULL];
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 66u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 min_nbc = 0xFFFFFFFFu;
      bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[wp + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if (usz >= CONG_AND_USZ_MAX || (u64)usz >= cv) { sat = true; break; }
          base[usz] = l; usz = usz + 1u;
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if (c_n < min_nbc) { min_nbc = c_n; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 66u && usz <= CONG_AND_USZ_MAX && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity) {
          h->res_sz = ticks;
          g_len = full_cong_extract_and_clause_fid(h, usz, g_len, g_cap, tick_lim);
          ticks = h->res_sz;
        }
      }
    }
    wi = wi + 1ULL;
  }
  return g_len;
}

u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim) {
  return full_cong_extract_from_fid(h, 0ULL, g_cap, tick_lim);
}

bool full_cong_and_match(FullHdr *h, u32 ent, u32 ua) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  if (ua < 2u || ua > CONG_AND_ARITY_MAX || (u64)ua > cv) { return false; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u8 *lm = (u8 *)h->lit_mark;
  u32 em = scr[(u64)ent + 1ULL];
  u32 ea = ((em >> 28) == 3u) ? (em & CONG_ARITY_MASK) : (em & 0xFFu);
  if (ea < 2u || ea > CONG_AND_ARITY_MAX || (u64)ea > cv) { return false; }
  u32 distinct_ua = 0u; u32 k = 0u;
  while (k < ua) {
    u32 tl = tmp[k];
    if ((u64)tl >= nlits) {
      u32 c = 0u;
      while (c < k) { lm[tmp[c]] = (u8)0; c = c + 1u; }
      return false;
    }
    if (lm[tl] == (u8)0) { lm[tl] = (u8)1; distinct_ua = distinct_ua + 1u; }
    k = k + 1u;
  }
  bool ok = true; u32 matched = 0u; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { ok = false; break; }
    if (ev == (i8)0) {
      u8 mv = lm[er];
      if (mv == (u8)0) { ok = false; break; }
      if (mv == (u8)1) { lm[er] = (u8)2; matched = matched + 1u; }
    }
    j = j + 1u;
  }
  k = 0u;
  while (k < ua) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  return ok && (matched == distinct_ua);
}

void full_cong_enq_var(FullHdr *h, u64 ctrl_off, u32 v) {
  if (ctrl_off >= h->scratch_cap || (u64)v >= h->cur_vars) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 occ_bkt = scr[ctrl_off];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL];
  u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u32 b = v & (occ_bkt - 1u);
  if (scr[inq_off + (u64)b] == 0u) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    if (q_len < occ_bkt) {
      u32 tail = (q_head + q_len) & (occ_bkt - 1u);
      scr[inq_off + (u64)b] = 1u;
      scr[q_off + (u64)tail] = b;
      scr[ctrl_off + 5ULL] = q_len + 1u;
    }
  }
}

u64 full_cong_eval_gate(FullHdr *h, u64 g, u64 ht_off, u64 ht_sz, u32 next_ep, u64 ctrl_off) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *trl = (u32 *)h->trail;
  u32 raw_lhs = scr[g]; u32 meta = scr[g + 1ULL];
  u32 tag = meta >> 28;
  u32 arity = (tag == 3u) ? (meta & CONG_ARITY_MASK) : (meta & 0xFFu);
  u32 gtype = (tag == 3u) ? 0u : tag;
  if (arity < 2u || arity > CONG_AND_ARITY_MAX || (u64)arity > h->cur_vars) { return 0ULL; }
  u32 lhs = full_cong_find(repr, raw_lhs);
  u32 i = 0u;
  while (i < arity) { tmp[i] = full_cong_find(repr, scr[g + 2ULL + (u64)i]); i = i + 1u; }
  u64 ht_lim = (ht_sz * 3ULL) >> 2;
  u64 te0 = h->trail_end;
  u32 htag = gtype; u32 harity = arity; bool need_hash = true; bool changed = false;
  if (gtype == 0u) {
    bool has_false = false; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv < (i8)0) { has_false = true; break; }
      if (rv == (i8)0) { tmp[na] = r; na = na + 1u; }
      i = i + 1u;
    }
    if (has_false) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (na == 0u) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else {
      if (na > 1u) { full_sort_u32(tmp, na); }
      bool clash = false; u32 ua = 0u; u32 si = 0u;
      while (si < na) {
        u32 cur = tmp[si]; si = si + 1u;
        if (cur == (lhs ^ 1u)) { clash = true; break; }
        if (ua == 0u) { tmp[0] = cur; ua = 1u; }
        else {
          u32 prev = tmp[ua - 1u];
          if (cur == prev) { continue; }
          if (cur == (prev ^ 1u)) { clash = true; break; }
          tmp[ua] = cur; ua = ua + 1u;
        }
      }
      if (clash) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 1u) {
        u32 r0 = tmp[0];
        u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
        }
        need_hash = false;
      } else if (vals[lhs] > (i8)0) {
        u32 k = 0u;
        while (k < ua) {
          u64 uf = full_cong_unit_fold(h, tmp[k], next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          k = k + 1u;
        }
        need_hash = false;
      } else {
        harity = ua;
      }
    }
  } else if (gtype == 1u && arity >= 2u && arity <= 4u) {
    u32 flip = 0u; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv != (i8)0) {
        if (rv > (i8)0) { flip = flip ^ 1u; }
      } else {
        flip = flip ^ (r & 1u);
        tmp[na] = r & (~1u); na = na + 1u;
      }
      i = i + 1u;
    }
    lhs = lhs ^ flip;
    if (na > 1u) { full_sort_u32(tmp, na); }
    u32 ua = 0u; i = 0u;
    while (i < na) {
      if (i + 1u < na && tmp[i] == tmp[i + 1u]) { i = i + 2u; }
      else { tmp[ua] = tmp[i]; ua = ua + 1u; i = i + 1u; }
    }
    if (ua > 0u) {
      u32 lhs_v = lhs & (~1u); u32 self_i = ua; i = 0u;
      while (i < ua) {
        if (tmp[i] == lhs_v) { self_i = i; break; }
        i = i + 1u;
      }
      if (self_i < ua) {
        u32 j = self_i;
        while (j + 1u < ua) { tmp[j] = tmp[j + 1u]; j = j + 1u; }
        ua = ua - 1u;
        u32 lsign = lhs & 1u;
        if (ua == 0u) {
          if (lsign != 0u) { h->inconsistent = 1ULL; return 2ULL; }
          need_hash = false;
        } else if (ua == 1u) {
          u32 ul = tmp[0] ^ (1u ^ lsign);
          u64 uf = full_cong_unit_fold(h, ul, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 2u) {
          u32 a0 = tmp[0] ^ lsign; u32 a1 = tmp[1];
          u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
          }
          need_hash = false;
        } else {
          need_hash = false;
        }
      }
    }
    if (need_hash) {
      if (ua == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 1u) {
        u32 r0 = tmp[0];
        u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
        }
        need_hash = false;
      } else if (ua == 2u && vals[lhs] != (i8)0) {
        u32 a0 = (vals[lhs] > (i8)0) ? (tmp[0] ^ 1u) : tmp[0]; u32 a1 = tmp[1];
        u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
        }
        need_hash = false;
      } else {
        harity = ua;
      }
    }
  } else if (gtype == 2u && arity == 3u) {
    u32 c = tmp[0]; u32 t = tmp[1]; u32 e = tmp[2];
    i8 vc = vals[c]; i8 vt = vals[t]; i8 ve = vals[e];
    if (vc != (i8)0) {
      u32 br = (vc > (i8)0) ? t : e;
      u64 ef = full_cong_equiv_fold(h, lhs, br, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, br >> 1);
      }
      need_hash = false;
    } else if (t == e) {
      u64 ef = full_cong_equiv_fold(h, lhs, t, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, t >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve < (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt < (i8)0 && ve > (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c ^ 1u, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve > (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (vt < (i8)0 && ve < (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (vt == (i8)0 && ve == (i8)0 && t == (e ^ 1u)) {
      lhs = lhs ^ ((1u ^ c ^ t) & 1u);
      u32 r0 = c & (~1u); u32 r1 = t & (~1u);
      if (r0 == r1) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vals[lhs] != (i8)0) {
        u32 a0 = (vals[lhs] > (i8)0) ? (r0 ^ 1u) : r0;
        u64 ef = full_cong_equiv_fold(h, a0, r1, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, r1 >> 1);
        }
        need_hash = false;
      } else {
        tmp[0] = (r0 < r1) ? r0 : r1; tmp[1] = (r0 < r1) ? r1 : r0;
        htag = 1u; harity = 2u;
      }
    } else {
      bool ite_and = false; u32 a0 = 0u; u32 a1 = 0u;
      if (vt > (i8)0) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (vt < (i8)0) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (ve > (i8)0) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (ve < (i8)0) {
        a0 = c; a1 = t; ite_and = true;
      } else if (c == t) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (c == (t ^ 1u)) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (c == (e ^ 1u)) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (c == e) {
        a0 = c; a1 = t; ite_and = true;
      }
      if (ite_and) {
        if (a0 == a1) {
          u64 ef = full_cong_equiv_fold(h, lhs, a0, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, a0 >> 1);
          }
          need_hash = false;
        } else if (a0 == (a1 ^ 1u) || a0 == (lhs ^ 1u) || a1 == (lhs ^ 1u)) {
          u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (vals[lhs] > (i8)0) {
          u64 u0 = full_cong_unit_fold(h, a0, next_ep);
          if (u0 == 2ULL) { return 2ULL; }
          if (u0 == 1ULL) { changed = true; }
          u64 u1 = full_cong_unit_fold(h, a1, next_ep);
          if (u1 == 2ULL) { return 2ULL; }
          if (u1 == 1ULL) { changed = true; }
          need_hash = false;
        } else {
          tmp[0] = (a0 < a1) ? a0 : a1; tmp[1] = (a0 < a1) ? a1 : a0;
          htag = 0u; harity = 2u;
        }
      } else {
        if ((c & 1u) != 0u) { c = c ^ 1u; u32 sw = t; t = e; e = sw; }
        if ((t & 1u) != 0u) { lhs = lhs ^ 1u; t = t ^ 1u; e = e ^ 1u; }
        tmp[0] = c; tmp[1] = t; tmp[2] = e;
      }
    }
  } else {
    need_hash = false;
  }
  bool keep = false;
  if (need_hash && h->inconsistent == 0ULL) {
    keep = true;
    u64 hv = (u64)htag * 0x9E3779B1ULL + (u64)harity;
    i = 0u;
    while (i < harity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL); u64 probes = 0ULL; bool seen_self = false;
    while (probes < 128ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (!seen_self && htag == gtype && h->res_sz < ht_lim) {
          scr[ht_off + slot] = (u32)g; h->res_sz = h->res_sz + 1ULL;
        }
        break;
      }
      if (ent == (u32)g) {
        seen_self = true; slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
        continue;
      }
      u32 em = scr[(u64)ent + 1ULL]; u32 etag = em >> 28;
      u32 egtype = (etag == 3u) ? 0u : etag;
      if (egtype == htag) {
        bool matched = false; u32 match_lhs = scr[ent];
        if (htag == 0u) {
          matched = full_cong_and_match(h, ent, harity);
        } else if (htag == 1u) {
          u32 ml = full_cong_xor_match(h, ent, harity);
          if (ml != 0xFFFFFFFFu) { matched = true; match_lhs = ml; }
        } else if (htag == 2u && (em & 0xFFu) == 3u) {
          u32 ec = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 et = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 ee = full_cong_find(repr, scr[(u64)ent + 4ULL]);
          if ((ec & 1u) != 0u) { ec = ec ^ 1u; u32 sw = et; et = ee; ee = sw; }
          if ((et & 1u) != 0u) { match_lhs = match_lhs ^ 1u; et = et ^ 1u; ee = ee ^ 1u; }
          matched = (ec == tmp[0] && et == tmp[1] && ee == tmp[2]);
        }
        if (matched) {
          keep = false;
          u64 ef = full_cong_equiv_fold(h, lhs, match_lhs, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1);
            full_cong_enq_var(h, ctrl_off, match_lhs >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, lhs) >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, match_lhs) >> 1);
          }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
    }
  }
  while (te0 < h->trail_end) {
    u32 tl = trl[te0];
    full_cong_enq_var(h, ctrl_off, tl >> 1);
    full_cong_enq_var(h, ctrl_off, full_cong_find(repr, tl) >> 1);
    te0 = te0 + 1ULL;
  }
  if (h->inconsistent != 0ULL) { return 2ULL; }
  return (changed ? 1ULL : 0ULL) | (keep ? 4ULL : 0ULL);
}

u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim) {
  if (tick_lim > 0x7FFFFFFFFFFFFFFFULL) { tick_lim = 0x7FFFFFFFFFFFFFFFULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 occ_bkt = scr[ctrl_off]; u64 bkt_off = (u64)scr[ctrl_off + 1ULL];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL]; u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u64 ht_off = (u64)scr[ctrl_off + 6ULL]; u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  u64 i = 0ULL;
  while (i < (u64)occ_bkt) {
    scr[bkt_off + i] = 0xFFFFFFFFu; scr[inq_off + i] = 0u; i = i + 1ULL;
  }
  scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
  u64 occ_end = g_len; u64 ticks = 0ULL; u64 rehashes = 0ULL;
  u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 gm = scr[g + 1ULL];
    u32 arity = ((gm >> 28) == 3u) ? (gm & CONG_ARITY_MASK) : (gm & 0xFFu);
    u64 next_g = g + 2ULL + (u64)arity;
    ticks = ticks + 2ULL;
    u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, 2u, ctrl_off);
    if ((er & 2ULL) != 0ULL) { return 20ULL; }
    if ((er & 4ULL) != 0ULL && occ_end + (1ULL + (u64)arity) * 3ULL <= ctrl_off) {
      u32 raw_l = scr[g];
      u32 rl = full_cong_find(repr, raw_l); u32 b0 = (rl >> 1) & (occ_bkt - 1u);
      scr[occ_end] = (u32)g;
      scr[occ_end + 1ULL] = raw_l;
      scr[occ_end + 2ULL] = scr[bkt_off + (u64)b0];
      scr[bkt_off + (u64)b0] = (u32)occ_end;
      occ_end = occ_end + 3ULL;
      u32 s = 0u;
      while (s < arity) {
        u32 raw_r = scr[g + 2ULL + (u64)s];
        u32 rr = full_cong_find(repr, raw_r);
        u32 bs = (rr >> 1) & (occ_bkt - 1u);
        scr[occ_end] = (u32)g;
        scr[occ_end + 1ULL] = raw_r;
        scr[occ_end + 2ULL] = scr[bkt_off + (u64)bs];
        scr[bkt_off + (u64)bs] = (u32)occ_end;
        occ_end = occ_end + 3ULL;
        s = s + 1u;
      }
    }
    g = next_g;
  }
  u32 ep = 3u;
  while ((scr[ctrl_off + 5ULL] > 0u) && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    u32 b = scr[q_off + (u64)q_head];
    scr[ctrl_off + 4ULL] = (q_head + 1u) & (occ_bkt - 1u);
    scr[ctrl_off + 5ULL] = q_len - 1u;
    scr[inq_off + (u64)b] = 0u;
    u32 nd = scr[bkt_off + (u64)b]; scr[bkt_off + (u64)b] = 0xFFFFFFFFu;
    while (nd != 0xFFFFFFFFu && h->inconsistent == 0ULL && ticks < tick_lim) {
      u64 gn = (u64)scr[nd];
      u32 raw_lit = scr[(u64)nd + 1ULL];
      u32 nxt = scr[(u64)nd + 2ULL];
      ticks = ticks + 2ULL;
      u64 er = full_cong_eval_gate(h, gn, ht_off, ht_sz, ep, ctrl_off);
      if ((er & 2ULL) != 0ULL) { return 20ULL; }
      if ((er & 4ULL) != 0ULL) {
        u32 dst = full_cong_find(repr, raw_lit);
        u32 b_dst = (dst >> 1) & (occ_bkt - 1u);
        scr[(u64)nd + 2ULL] = scr[bkt_off + (u64)b_dst];
        scr[bkt_off + (u64)b_dst] = nd;
      }
      nd = nxt;
    }
    bool do_grow = (h->res_sz * 2ULL >= ht_sz) && (ht_sz < 1048576ULL) &&
      (ht_off + (ht_sz << 1) <= h->scratch_cap);
    bool do_flush = (!do_grow) && (h->res_sz * 4ULL >= ht_sz * 3ULL) && (rehashes < 4ULL);
    if ((do_grow || do_flush) && ticks < tick_lim) {
      if (do_grow) {
        ht_sz = ht_sz << 1;
        scr[ctrl_off + 7ULL] = (u32)ht_sz;
      } else {
        rehashes = rehashes + 1ULL;
      }
      i = 0ULL; while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL;
      g = 0ULL;
      while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
        u32 gm = scr[g + 1ULL];
    u32 arity = ((gm >> 28) == 3u) ? (gm & CONG_ARITY_MASK) : (gm & 0xFFu);
        ticks = ticks + 1ULL;
        u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, ep, ctrl_off);
        if ((er & 2ULL) != 0ULL) { return 20ULL; }
        g = g + 2ULL + (u64)arity;
      }
    }
    ep = ep + 1u;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 g_cap = h->scratch_cap >> 1;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = (u64)full_cong_extract_ite_all_m7(h, 0u, (u32)(g_cap >> 1), tick_lim);
  if (g_len <= g_cap) {
    g_len = full_cong_extract_from_fid(h, g_len, g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= g_cap) {
    u64 free_scr = h->scratch_cap - g_len;
    u64 ht_max = 64ULL;
    while (ht_max * 4ULL <= free_scr && ht_max < 1048576ULL) { ht_max = ht_max << 1; }
    u64 ht_off = h->scratch_cap - ht_max;
    u64 rem_occ = ht_off - g_len;
    u64 occ_bkt = 16ULL;
    while ((occ_bkt << 1) <= 1048576ULL && (occ_bkt << 1) < nlits &&
           (occ_bkt << 1) * 16ULL <= rem_occ) {
      occ_bkt = occ_bkt << 1;
    }
    u64 bkt_off = ht_off - occ_bkt;
    u64 inq_off = bkt_off - occ_bkt;
    u64 q_off = inq_off - occ_bkt;
    u64 ctrl_off = q_off - 8ULL;
    u64 ht_sz = 64ULL;
    while (ht_sz < g_len && (ht_sz << 1) <= ht_max) { ht_sz = ht_sz << 1; }
    i = 0ULL;
    while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    h->res_sz = 0ULL;
    scr[ctrl_off] = (u32)occ_bkt; scr[ctrl_off + 1ULL] = (u32)bkt_off;
    scr[ctrl_off + 2ULL] = (u32)inq_off; scr[ctrl_off + 3ULL] = (u32)q_off;
    scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
    scr[ctrl_off + 6ULL] = (u32)ht_off; scr[ctrl_off + 7ULL] = (u32)ht_sz;
    if (full_cong_worklist(h, g_len, ctrl_off, tick_lim) == 20ULL) {
      i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
      h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
    }
  }
  if (full_cong_fwd_subsume(h, tick_lim) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL; h->ant_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

/-! ## 1. Canonical `Fn` Handles & Patch Lists -/

def fidStep12BCongExtractAndClauseFn : Fn :=
  ⟨"full_cong_extract_and_clause_fid", [i64, i32, i64, i64, i64], [i64],
    full_cong_extract_and_clause_fid_body⟩

def fidStep12BCongExtractFromFn : Fn :=
  ⟨"full_cong_extract_from_fid", [i64, i64, i64, i64], [i64], full_cong_extract_from_fid_body⟩

def fidStep12BCongExtractFn : Fn :=
  ⟨"full_cong_extract", [i64, i64, i64], [i64], full_cong_extract_body⟩

def fidStep12BCongAndMatchFn : Fn :=
  ⟨"full_cong_and_match", [i64, i32, i32], [.bool], full_cong_and_match_body⟩

def fidStep12BCongEnqVarFn : Fn :=
  ⟨"full_cong_enq_var", [i64, i64, i32], [], full_cong_enq_var_body⟩

def fidStep12BCongEvalGateFn : Fn :=
  ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], full_cong_eval_gate_body⟩

def fidStep12BCongWorklistFn : Fn :=
  ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], full_cong_worklist_body⟩

def fidStep12BCongruenceDenseFn : Fn :=
  ⟨"full_congruence_dense", [i64, i64], [i64], full_congruence_dense_body⟩

/-- The `6` Step-12B congruence replacement functions. -/
def fidStep12BCongRepls : List Fn :=
  [ fidStep12BCongExtractFn
  , fidStep12BCongAndMatchFn
  , fidStep12BCongEnqVarFn
  , fidStep12BCongEvalGateFn
  , fidStep12BCongWorklistFn
  , fidStep12BCongruenceDenseFn ]

/-- The `2` Step-12B congruence helper functions inserted before `full_cong_extract`. -/
def fidStep12BCongBefores : List (Sym × List Fn) :=
  [ ("full_cong_extract", [fidStep12BCongExtractAndClauseFn, fidStep12BCongExtractFromFn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_cong_extract_and_clause_fid_s12b_wf :
    Func.Wf fidStep12BCongExtractAndClauseFn.body := by t_wf_reify

theorem full_cong_extract_from_fid_s12b_wf :
    Func.Wf fidStep12BCongExtractFromFn.body := by t_wf_reify

theorem full_cong_extract_s12b_wf :
    Func.Wf fidStep12BCongExtractFn.body := by t_wf_reify

theorem full_cong_and_match_s12b_wf :
    Func.Wf fidStep12BCongAndMatchFn.body := by t_wf_reify

theorem full_cong_enq_var_s12b_wf :
    Func.Wf fidStep12BCongEnqVarFn.body := by t_wf_reify

theorem full_cong_eval_gate_s12b_wf :
    Func.Wf fidStep12BCongEvalGateFn.body := by t_wf_reify

theorem full_cong_worklist_s12b_wf :
    Func.Wf fidStep12BCongWorklistFn.body := by t_wf_reify

theorem full_congruence_dense_s12b_wf :
    Func.Wf fidStep12BCongruenceDenseFn.body := by t_wf_reify

theorem fidStep12BCongRepls_wf : ∀ f ∈ fidStep12BCongRepls, f.Wf := by
  intro f hf
  simp only [fidStep12BCongRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_cong_extract_s12b_wf
  · exact full_cong_and_match_s12b_wf
  · exact full_cong_enq_var_s12b_wf
  · exact full_cong_eval_gate_s12b_wf
  · exact full_cong_worklist_s12b_wf
  · exact full_congruence_dense_s12b_wf

theorem fidStep12BCongBefores_wf : ∀ f ∈ fidStep12BCongBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidStep12BCongBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact full_cong_extract_and_clause_fid_s12b_wf
  · exact full_cong_extract_from_fid_s12b_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
