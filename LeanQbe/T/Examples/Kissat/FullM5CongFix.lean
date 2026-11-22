module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M5 Congruence Closure Fixes (`FullM5CongFix`, `RC-17`)

Drop-in replacements for `full_cong_{merge,extract_ite,emit_xor,try_xor_ite,extract,and_match,
work_step}` (`congruence.c:419-549,845-848,1300-1368,1438-1441,1576-1580,1770-2145,2532-2949`,
`0` `FullHdr` edits):
1. `full_cong_merge`: checks `full_add_bin` `2ULL` (OOM) return and resets `h->oom = 0ULL` cleanly.
2. `full_cong_extract_ite`: skips XOR-like `e == (t ^ 1u)` and normalizes both `c` and `t` positive.
3. `full_cong_emit_xor`: polarity-normalized `tag = 1, arity = 2` XOR emitter.
4. `full_cong_try_xor_ite`: canonical XOR base-clause filter (eliminating `4x` duplicate bloat) and
   non-blocking ITE selector fallback across `a`, `b`, `c`.
5. `full_cong_extract`: widens AND extraction to `sz <= 32` and removes early `break` so all valid
   LHSs of a shared base clause are extracted.
6. `full_cong_and_match`: widens `u32` bitmask matching to `2 <= ua <= 31`.
7. `full_cong_work_step`: checks `cur == (lhs ^ 1u)` in AND dedup, sets `need_hash = false` when
   `vals[lhs] > 0`, strips XOR RHS sign bits onto `lhs` + folds `vals[lhs] != 0`, normalizes ITE
   `then_lit` sign onto `lhs`, and skips self-match `ent == (u32)g` without duplicate insertion.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5CongFix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5CongFix "
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
#define PW_BIN_FLAG 0x80000000u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c);
extern void full_sort_u32(u32 *arr, u32 n);
extern u32 full_cong_find(u32 *repr, u32 l);
extern u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep);
extern u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep);

bool full_cong_merge(FullHdr *h, u32 a, u32 b) {
  u32 *repr = (u32 *)h->repr;
  u32 ra = full_cong_find(repr, a); u32 rb = full_cong_find(repr, b);
  if (ra == rb) { return false; }
  if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return true; }
  if (ra > rb) { u32 t = ra; ra = rb; rb = t; }
  repr[rb] = ra; repr[rb ^ 1u] = ra ^ 1u;
  u64 st1 = full_add_bin(h, ra ^ 1u, rb);
  if (st1 == 20ULL) { h->inconsistent = 1ULL; return true; }
  if (st1 == 2ULL) {
    h->oom = 0ULL;
  } else {
    u64 st2 = full_add_bin(h, ra, rb ^ 1u);
    if (st2 == 20ULL) { h->inconsistent = 1ULL; return true; }
    if (st2 == 2ULL) { h->oom = 0ULL; }
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  return true;
}

u64 full_cong_extract_ite(FullHdr *h, u32 c, u32 y, u32 t, u64 g_len) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)c << 1]; u64 end = off + (u64)wvec[((u64)c << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || ar[(u64)cr + 2ULL] != 3u) { continue; }
    u32 l0 = ar[(u64)cr + 3ULL]; u32 l1 = ar[(u64)cr + 4ULL]; u32 l2 = ar[(u64)cr + 5ULL];
    u32 e = 0xFFFFFFFFu;
    if (l0 == c && l1 == (y ^ 1u)) { e = l2; }
    else if (l0 == c && l2 == (y ^ 1u)) { e = l1; }
    else if (l1 == c && l0 == (y ^ 1u)) { e = l2; }
    else if (l1 == c && l2 == (y ^ 1u)) { e = l0; }
    else if (l2 == c && l0 == (y ^ 1u)) { e = l1; }
    else if (l2 == c && l1 == (y ^ 1u)) { e = l0; }
    if (e != 0xFFFFFFFFu && e != (t ^ 1u) && full_has_ternary(h, c, e ^ 1u, y)) {
      if ((c & 1u) != 0u) { u32 tmp = t; t = e; e = tmp; c = c ^ 1u; }
      if ((t & 1u) != 0u) { y = y ^ 1u; t = t ^ 1u; e = e ^ 1u; }
      scr[g_len] = y; scr[g_len + 1ULL] = (2u << 28) | 3u;
      scr[g_len + 2ULL] = c; scr[g_len + 3ULL] = t; scr[g_len + 4ULL] = e;
      return g_len + 5ULL;
    }
  }
  return g_len;
}

u64 full_cong_emit_xor(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2) {
  u32 lhs = ((x0 ^ 1u) & (~1u)) | (((x0 ^ 1u) ^ x1 ^ x2) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u);
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 2u;
  scr[g_len + 2ULL] = (r0 < r1) ? r0 : r1; scr[g_len + 3ULL] = (r0 < r1) ? r1 : r0;
  return g_len + 4ULL;
}

u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = (a > b) ? a : b;
  if (c > mx) { mx = c; }
  if (((a & 1u) == 0u || a == mx) && ((b & 1u) == 0u || b == mx) &&
      ((c & 1u) == 0u || c == mx) &&
      full_has_ternary(h, a, b ^ 1u, c ^ 1u) && full_has_ternary(h, a ^ 1u, b, c ^ 1u) &&
      full_has_ternary(h, a ^ 1u, b ^ 1u, c)) {
    if (g_len + 12ULL <= g_cap) {
      g_len = full_cong_emit_xor(scr, g_len, a, b, c);
      g_len = full_cong_emit_xor(scr, g_len, b, a, c);
      g_len = full_cong_emit_xor(scr, g_len, c, a, b);
    }
    return g_len;
  }
  if (full_has_ternary(h, a, b ^ 1u, c ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, a ^ 1u, b ^ 1u, c, g_len);
    if (ng > g_len) { return ng; }
    ng = full_cong_extract_ite(h, a ^ 1u, c ^ 1u, b, g_len);
    if (ng > g_len) { return ng; }
  }
  if (full_has_ternary(h, b, a ^ 1u, c ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, b ^ 1u, a ^ 1u, c, g_len);
    if (ng > g_len) { return ng; }
    ng = full_cong_extract_ite(h, b ^ 1u, c ^ 1u, a, g_len);
    if (ng > g_len) { return ng; }
  }
  if (full_has_ternary(h, c, a ^ 1u, b ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, c ^ 1u, a ^ 1u, b, g_len);
    if (ng > g_len) { return ng; }
    ng = full_cong_extract_ite(h, c ^ 1u, b ^ 1u, a, g_len);
    if (ng > g_len) { return ng; }
  }
  return g_len;
}

u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u64 p = 0ULL; u64 g_len = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && g_len + 34ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 32u) {
      u32 i = 0u;
      while (i < sz && g_len + 2ULL + (u64)(sz - 1u) <= g_cap) {
        u32 lhs = ar[p + 3ULL + (u64)i]; bool ok = true; u32 j = 0u;
        while (j < sz) {
          if (j != i && !full_has_bin(h, lhs ^ 1u, ar[p + 3ULL + (u64)j] ^ 1u)) {
            ok = false; break;
          }
          j = j + 1u;
        }
        if (ok) {
          scr[g_len] = lhs; scr[g_len + 1ULL] = sz - 1u; u32 rk = 0u; j = 0u;
          while (j < sz) {
            if (j != i) {
              scr[g_len + 2ULL + (u64)rk] = ar[p + 3ULL + (u64)j] ^ 1u; rk = rk + 1u;
            }
            j = j + 1u;
          }
          g_len = g_len + 2ULL + (u64)(sz - 1u);
        }
        i = i + 1u;
      }
      if (sz == 3u && g_len + 14ULL <= g_cap) {
        g_len = full_cong_try_xor_ite(h, ar[p + 3ULL], ar[p + 4ULL], ar[p + 5ULL],
          g_len, g_cap);
        ticks = ticks + 4ULL;
      }
    }
    p = np;
  }
  return g_len;
}

bool full_cong_and_match(FullHdr *h, u32 ent, u32 ua) {
  if (ua < 2u || ua > 31u) { return false; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  u32 mask = 0u;
  u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { return false; }
    if (ev == (i8)0) {
      bool found = false;
      u32 k = 0u;
      while (k < ua) {
        if (tmp[k] == er) { mask = mask | (1u << k); found = true; break; }
        k = k + 1u;
      }
      if (!found) { return false; }
    }
    j = j + 1u;
  }
  u32 full_mask = (1u << ua) - 1u;
  return mask == full_mask;
}

u64 full_cong_work_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz, u32 cur_ep) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *tmk = (u32 *)h->tarjan_mark;
  i8 *vals = (i8 *)h->values;
  u32 next_ep = cur_ep + 1u;
  u64 ht_lim = (ht_sz * 3ULL) >> 2;
  bool changed = false;
  u64 work = 0ULL;
  u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL) {
    u32 raw_lhs = scr[g];
    u32 meta = scr[g + 1ULL];
    u32 tag = meta >> 28;
    u32 arity = meta & 0xFFu;
    u64 next_g = g + 2ULL + (u64)arity;
    u32 lhs = full_cong_find(repr, raw_lhs);
    bool dirty = (tmk[raw_lhs >> 1] >= cur_ep) || (tmk[lhs >> 1] >= cur_ep);
    u32 i = 0u;
    while (i < arity) {
      u32 raw_a = scr[g + 2ULL + (u64)i];
      u32 ra = full_cong_find(repr, raw_a);
      if (tmk[raw_a >> 1] >= cur_ep || tmk[ra >> 1] >= cur_ep) { dirty = true; }
      tmp[i] = ra;
      i = i + 1u;
    }
    if (!dirty) { work = work + 1ULL; g = next_g; continue; }
    work = work + 4ULL;
    u32 htag = tag;
    u32 harity = arity;
    bool need_hash = true;
    if (tag == 0u) {
      bool has_false = false;
      u32 na = 0u;
      i = 0u;
      while (i < arity) {
        u32 r = tmp[i];
        i8 rv = vals[r];
        if (rv < (i8)0) { has_false = true; }
        else if (rv == (i8)0) { tmp[na] = r; na = na + 1u; }
        i = i + 1u;
      }
      if (has_false) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (na == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else {
        if (na > 1u) { full_sort_u32(tmp, na); }
        bool clash = false;
        u32 ua = 0u;
        u32 si = 0u;
        while (si < na) {
          u32 cur = tmp[si];
          si = si + 1u;
          if (cur == (lhs ^ 1u)) { clash = true; break; }
          if (ua == 0u) { tmp[0] = cur; ua = 1u; }
          else {
            u32 prev = tmp[ua - 1u];
            if (cur == prev) { continue; }
            if (cur == (prev ^ 1u)) { clash = true; break; }
            tmp[ua] = cur;
            ua = ua + 1u;
          }
        }
        if (clash) {
          u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
          if (uf == 2ULL) { return (work << 2) | 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 0u) {
          u64 uf = full_cong_unit_fold(h, lhs, next_ep);
          if (uf == 2ULL) { return (work << 2) | 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 1u) {
          u64 ef = full_cong_equiv_fold(h, lhs, tmp[0], next_ep);
          if (ef == 2ULL) { return (work << 2) | 2ULL; }
          if (ef == 1ULL) { changed = true; }
          need_hash = false;
        } else {
          if (vals[lhs] > (i8)0) {
            u32 k = 0u;
            while (k < ua) {
              u64 uf = full_cong_unit_fold(h, tmp[k], next_ep);
              if (uf == 2ULL) { return (work << 2) | 2ULL; }
              if (uf == 1ULL) { changed = true; }
              k = k + 1u;
            }
            need_hash = false;
          } else {
            harity = ua;
          }
        }
      }
    } else if (tag == 1u && arity == 2u) {
      u32 t0 = tmp[0]; u32 t1 = tmp[1];
      i8 v0 = vals[t0]; i8 v1 = vals[t1];
      if (v0 != (i8)0) {
        u32 eq = (v0 > (i8)0) ? (t1 ^ 1u) : t1;
        u64 ef = full_cong_equiv_fold(h, lhs, eq, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (v1 != (i8)0) {
        u32 eq = (v1 > (i8)0) ? (t0 ^ 1u) : t0;
        u64 ef = full_cong_equiv_fold(h, lhs, eq, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if ((t0 >> 1) == (t1 >> 1)) {
        u32 ul = (t0 == t1) ? (lhs ^ 1u) : lhs;
        u64 uf = full_cong_unit_fold(h, ul, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vals[lhs] != (i8)0) {
        u32 eq0 = (vals[lhs] > (i8)0) ? (t0 ^ 1u) : t0;
        u64 ef = full_cong_equiv_fold(h, eq0, t1, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else {
        lhs = lhs ^ ((t0 ^ t1) & 1u);
        t0 = t0 & (~1u); t1 = t1 & (~1u);
        if (t0 > t1) { u32 sw = t0; t0 = t1; t1 = sw; }
        tmp[0] = t0; tmp[1] = t1;
      }
    } else if (tag == 2u && arity == 3u) {
      u32 c = tmp[0]; u32 t = tmp[1]; u32 e = tmp[2];
      i8 vc = vals[c]; i8 vt = vals[t]; i8 ve = vals[e];
      if (vc != (i8)0) {
        u32 br = (vc > (i8)0) ? t : e;
        u64 ef = full_cong_equiv_fold(h, lhs, br, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (t == e) {
        u64 ef = full_cong_equiv_fold(h, lhs, t, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt > (i8)0 && ve < (i8)0) {
        u64 ef = full_cong_equiv_fold(h, lhs, c, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt < (i8)0 && ve > (i8)0) {
        u64 ef = full_cong_equiv_fold(h, lhs, c ^ 1u, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt > (i8)0 && ve > (i8)0) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt < (i8)0 && ve < (i8)0) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else {
        if ((c & 1u) != 0u) { c = c ^ 1u; u32 sw = t; t = e; e = sw; }
        if ((t & 1u) != 0u) { lhs = lhs ^ 1u; t = t ^ 1u; e = e ^ 1u; }
        tmp[0] = c; tmp[1] = t; tmp[2] = e;
      }
    }
    if (!need_hash) { g = next_g; continue; }
    u64 hv = (u64)htag * 0x9E3779B1ULL + (u64)harity;
    i = 0u;
    while (i < harity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL);
    u64 probes = 0ULL;
    bool seen_self = false;
    while (probes < 64ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (!seen_self && h->res_sz < ht_lim) {
          scr[ht_off + slot] = (u32)g;
          h->res_sz = h->res_sz + 1ULL;
        }
        break;
      }
      if (ent == (u32)g) {
        seen_self = true;
        slot = (slot + 1ULL) & (ht_sz - 1ULL);
        probes = probes + 1ULL;
        continue;
      }
      u32 em = scr[(u64)ent + 1ULL];
      u32 etag = em >> 28;
      if (etag == htag) {
        bool matched = false;
        u32 match_lhs = scr[ent];
        if (htag == 0u) {
          matched = full_cong_and_match(h, ent, harity);
        } else if (htag == 1u && (em & 0xFFu) == 2u) {
          u32 e0 = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 e1 = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 eflip = (e0 ^ e1) & 1u;
          e0 = e0 & (~1u); e1 = e1 & (~1u);
          matched = (e0 == tmp[0] && e1 == tmp[1]) || (e0 == tmp[1] && e1 == tmp[0]);
          match_lhs = match_lhs ^ eflip;
        } else if (htag == 2u && (em & 0xFFu) == 3u) {
          u32 ec = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 et = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 ee = full_cong_find(repr, scr[(u64)ent + 4ULL]);
          if ((ec & 1u) != 0u) { ec = ec ^ 1u; u32 sw = et; et = ee; ee = sw; }
          if ((et & 1u) != 0u) { match_lhs = match_lhs ^ 1u; et = et ^ 1u; ee = ee ^ 1u; }
          matched = (ec == tmp[0] && et == tmp[1] && ee == tmp[2]);
        }
        if (matched) {
          u64 ef = full_cong_equiv_fold(h, lhs, match_lhs, next_ep);
          if (ef == 2ULL) { return (work << 2) | 2ULL; }
          if (ef == 1ULL) { changed = true; }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL);
      probes = probes + 1ULL;
    }
    g = next_g;
  }
  u64 st = (h->inconsistent != 0ULL) ? 2ULL : (changed ? 1ULL : 0ULL);
  return (work << 2) | st;
}
"

def m5CongFixExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_sort_u32", [i64, i32], []⟩
  , ⟨"full_cong_find", [i64, i32], [i32]⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64]⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64]⟩ ]

def m5CongFixModule : LeanQbe.T.Module :=
  { fns := m5CongFix_fns, externs := m5CongFixExterns, exits := [] }

theorem full_cong_merge_wf : Func.Wf full_cong_merge_body := by t_wf_reify
theorem full_cong_extract_ite_wf : Func.Wf full_cong_extract_ite_body := by t_wf_reify
theorem full_cong_emit_xor_wf : Func.Wf full_cong_emit_xor_body := by t_wf_reify
theorem full_cong_try_xor_ite_wf : Func.Wf full_cong_try_xor_ite_body := by t_wf_reify
theorem full_cong_extract_wf : Func.Wf full_cong_extract_body := by t_wf_reify
theorem full_cong_and_match_wf : Func.Wf full_cong_and_match_body := by t_wf_reify
theorem full_cong_work_step_wf : Func.Wf full_cong_work_step_body := by t_wf_reify

theorem m5CongFix_fns_wf : ∀ f ∈ m5CongFix_fns, f.Wf := by
  simp only [m5CongFix_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_cong_merge_wf, full_cong_extract_ite_wf, full_cong_emit_xor_wf,
    full_cong_try_xor_ite_wf, full_cong_extract_wf, full_cong_and_match_wf,
    full_cong_work_step_wf⟩

theorem m5CongFix_acyclic : m5CongFixModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5CongFix
