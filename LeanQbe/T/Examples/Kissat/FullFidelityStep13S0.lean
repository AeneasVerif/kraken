/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Module
import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step-13 Shard `S0`: Soft-Float `f64u_*` Helpers, `m6_wm4_*`, & Header Updates

Strictly additive data-pure C0 source module (`0` `*Proof*`/`*Lemmas*`/`*Audit*`/`*Spec*` imports)
defining the `17` `S0` functions (`14` ADD + `3` MOD) from `step13_v2_frozen_direct.c`:
- **ADD (`14`):** `f64u_msb64`, `f64u_round_pack`, `f64u_add`, `f64u_sub`, `f64u_mul`,
  `f64u_div`, `f64u_inv_u64`, `f64u_from_u64`, `f64u_to_u64`, `u64_mul128`,
  `f64u_log10_u64`, `f64u_nlogpown`, `m6_wm4_get`, `m6_wm4_set`.
- **MOD (`3`):** `full_init_hdr`, `m6_hdr_init`, `m6_hdr_recompute_tiers_mode`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

@[expose] public section

kissat_c0! fidStep13S0 "
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

typedef C0_RET2(u64, u64) s0_u64_pair;

extern void m6_ext_ensure_init(FullHdr *h);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);

u64 f64u_msb64(u64 x) {
  u64 r = 0ULL;
  if (x >= (1ULL << 32)) { x = x >> 32; r = r + 32ULL; }
  if (x >= (1ULL << 16)) { x = x >> 16; r = r + 16ULL; }
  if (x >= (1ULL << 8))  { x = x >> 8;  r = r + 8ULL; }
  if (x >= (1ULL << 4))  { x = x >> 4;  r = r + 4ULL; }
  if (x >= (1ULL << 2))  { x = x >> 2;  r = r + 2ULL; }
  if (x >= 2ULL)         { r = r + 1ULL; }
  return r;
}

u64 f64u_round_pack(u64 exp, u64 sig55) {
  if (sig55 == 0ULL) { return 0ULL; }
  if (sig55 >= (1ULL << 56)) {
    u64 msb = f64u_msb64(sig55);
    u64 sh = msb - 55ULL;
    u64 lost = sig55 & ((1ULL << sh) - 1ULL);
    sig55 = (sig55 >> sh) | (lost != 0ULL ? 1ULL : 0ULL);
    exp = exp + sh;
  } else if (sig55 < (1ULL << 55) && exp > 1ULL) {
    u64 msb = f64u_msb64(sig55);
    u64 need = 55ULL - msb;
    u64 sh = (need < (exp - 1ULL)) ? need : (exp - 1ULL);
    sig55 = sig55 << sh;
    exp = exp - sh;
  }
  if (exp == 1ULL && sig55 < (1ULL << 55)) {
    u64 rem = sig55 & 7ULL;
    u64 m = sig55 >> 3;
    if (rem > 4ULL || (rem == 4ULL && (m & 1ULL) != 0ULL)) {
      m = m + 1ULL;
      if (m == (1ULL << 52)) { return 1ULL << 52; }
    }
    return m;
  }
  if (exp >= 2047ULL) { return 0x7FF0000000000000ULL; }
  u64 rem = sig55 & 7ULL;
  u64 m = sig55 >> 3;
  if (rem > 4ULL || (rem == 4ULL && (m & 1ULL) != 0ULL)) {
    m = m + 1ULL;
    if (m >= (1ULL << 53)) {
      m = m >> 1;
      exp = exp + 1ULL;
      if (exp >= 2047ULL) { return 0x7FF0000000000000ULL; }
    }
  }
  return (exp << 52) | (m & ((1ULL << 52) - 1ULL));
}

u64 f64u_add(u64 a, u64 b) {
  if (a == 0ULL) { return b; }
  if (b == 0ULL) { return a; }
  if (a < b) { u64 t = a; a = b; b = t; }
  u64 ea = a >> 52;
  u64 eb = b >> 52;
  if (ea >= 2047ULL) { return a; }
  if (ea > 0ULL && eb > 0ULL) {
    u64 shift = ea - eb;
    if (shift > 56ULL) { return a; }
    u64 mask52 = (1ULL << 52) - 1ULL;
    u64 ma = ((1ULL << 52) | (a & mask52)) << 3;
    u64 mb = ((1ULL << 52) | (b & mask52)) << 3;
    u64 sb = mb;
    if (shift > 0ULL) {
      u64 lost = sb & ((1ULL << shift) - 1ULL);
      sb = (sb >> shift) | (lost != 0ULL ? 1ULL : 0ULL);
    }
    u64 sum = ma + sb;
    u64 exp = ea;
    if (sum >= (1ULL << 56)) {
      sum = (sum >> 1) | (sum & 1ULL);
      exp = exp + 1ULL;
    }
    if (exp >= 2047ULL) { return 0x7FF0000000000000ULL; }
    u64 rem = sum & 7ULL;
    u64 m = sum >> 3;
    if (rem > 4ULL || (rem == 4ULL && (m & 1ULL) != 0ULL)) {
      m = m + 1ULL;
      if (m >= (1ULL << 53)) {
        m = m >> 1;
        exp = exp + 1ULL;
        if (exp >= 2047ULL) { return 0x7FF0000000000000ULL; }
      }
    }
    return (exp << 52) | (m & mask52);
  }
  u64 ma = (ea == 0ULL) ? ((a & ((1ULL << 52) - 1ULL)) << 3)
                        : (((1ULL << 52) | (a & ((1ULL << 52) - 1ULL))) << 3);
  u64 mb = (b & ((1ULL << 52) - 1ULL)) << 3;
  u64 dea = (ea == 0ULL) ? 1ULL : ea;
  u64 shift = dea - 1ULL;
  if (shift > 56ULL) { return a; }
  u64 sb = mb;
  if (shift > 0ULL) {
    u64 lost = sb & ((1ULL << shift) - 1ULL);
    sb = (sb >> shift) | (lost != 0ULL ? 1ULL : 0ULL);
  }
  u64 sum = ma + sb;
  if (ea == 0ULL) {
    if (sum >= (1ULL << 55)) { return f64u_round_pack(1ULL, sum); }
    return sum >> 3;
  }
  return f64u_round_pack(dea, sum);
}

u64 f64u_sub(u64 a, u64 b) {
  if (a <= b) { return 0ULL; }
  if (b == 0ULL) { return a; }
  u64 ea = a >> 52;
  u64 eb = b >> 52;
  if (ea >= 2047ULL) { return a; }
  u64 ma = (ea == 0ULL) ? ((a & ((1ULL << 52) - 1ULL)) << 3)
                        : (((1ULL << 52) | (a & ((1ULL << 52) - 1ULL))) << 3);
  u64 mb = (eb == 0ULL) ? ((b & ((1ULL << 52) - 1ULL)) << 3)
                        : (((1ULL << 52) | (b & ((1ULL << 52) - 1ULL))) << 3);
  u64 dea = (ea == 0ULL) ? 1ULL : ea;
  u64 deb = (eb == 0ULL) ? 1ULL : eb;
  u64 shift = dea - deb;
  if (shift > 57ULL) { return a; }
  u64 sb = mb;
  if (shift > 0ULL) {
    u64 lost = sb & ((1ULL << shift) - 1ULL);
    sb = (sb >> shift) | (lost != 0ULL ? 1ULL : 0ULL);
  }
  u64 diff = ma - sb;
  if (ea == 0ULL) { return diff >> 3; }
  return f64u_round_pack(dea, diff);
}

u64 f64u_mul(u64 a, u64 b) {
  if (a == 0ULL || b == 0ULL) { return 0ULL; }
  u64 ea = a >> 52;
  u64 eb = b >> 52;
  if (ea >= 2047ULL || eb >= 2047ULL) { return 0x7FF0000000000000ULL; }
  u64 ma = (ea == 0ULL) ? (a & ((1ULL << 52) - 1ULL))
                        : ((1ULL << 52) | (a & ((1ULL << 52) - 1ULL)));
  u64 mb = (eb == 0ULL) ? (b & ((1ULL << 52) - 1ULL))
                        : ((1ULL << 52) | (b & ((1ULL << 52) - 1ULL)));
  u64 exp_bias = (ea == 0ULL ? 1ULL : ea) + (eb == 0ULL ? 1ULL : eb);
  if (ea == 0ULL) {
    u64 sh = 52ULL - f64u_msb64(ma);
    ma = ma << sh;
    exp_bias = exp_bias - sh;
  }
  if (eb == 0ULL) {
    u64 sh = 52ULL - f64u_msb64(mb);
    mb = mb << sh;
    exp_bias = exp_bias - sh;
  }
  u64 a_hi = ma >> 26; u64 a_lo = ma & ((1ULL << 26) - 1ULL);
  u64 b_hi = mb >> 26; u64 b_lo = mb & ((1ULL << 26) - 1ULL);
  u64 p00 = a_lo * b_lo;
  u64 p01 = a_lo * b_hi;
  u64 p10 = a_hi * b_lo;
  u64 p11 = a_hi * b_hi;
  u64 mid = p01 + p10 + (p00 >> 26);
  u64 lo_sticky = ((p00 & ((1ULL << 26) - 1ULL)) != 0ULL) ? 1ULL : 0ULL;
  u64 top = (p11 << 3) + (mid >> 23);
  if ((mid & ((1ULL << 23) - 1ULL)) != 0ULL) { lo_sticky = 1ULL; }
  u64 sig55 = top | lo_sticky;
  if (sig55 >= (1ULL << 56)) {
    sig55 = (sig55 >> 1) | (sig55 & 1ULL);
    exp_bias = exp_bias + 1ULL;
  }
  if (exp_bias <= 1023ULL) {
    u64 sh = 1024ULL - exp_bias;
    if (sh > 56ULL) { return 0ULL; }
    u64 lost = sig55 & ((1ULL << sh) - 1ULL);
    sig55 = (sig55 >> sh) | (lost != 0ULL ? 1ULL : 0ULL);
    return f64u_round_pack(1ULL, sig55);
  }
  return f64u_round_pack(exp_bias - 1023ULL, sig55);
}

u64 f64u_div(u64 a, u64 b) {
  if (a == 0ULL) { return 0ULL; }
  if (b == 0ULL) { return 0x7FF0000000000000ULL; }
  u64 ea = a >> 52;
  u64 eb = b >> 52;
  u64 ma = (ea == 0ULL) ? (a & ((1ULL << 52) - 1ULL))
                        : ((1ULL << 52) | (a & ((1ULL << 52) - 1ULL)));
  u64 mb = (eb == 0ULL) ? (b & ((1ULL << 52) - 1ULL))
                        : ((1ULL << 52) | (b & ((1ULL << 52) - 1ULL)));
  u64 ean = (ea == 0ULL) ? 1ULL : ea;
  u64 ebn = (eb == 0ULL) ? 1ULL : eb;
  u64 neg_exp = 0ULL;
  u64 exp_val = 0ULL;
  if (ea == 0ULL) {
    u64 sh = 52ULL - f64u_msb64(ma);
    ma = ma << sh;
    if (ean >= sh) { ean = ean - sh; } else { neg_exp = sh - ean; ean = 0ULL; }
  }
  if (eb == 0ULL) {
    u64 sh = 52ULL - f64u_msb64(mb);
    mb = mb << sh;
    ebn = ebn + sh;
  }
  if (ma < mb) {
    ma = ma << 1;
    if (ean > 0ULL) { ean = ean - 1ULL; } else { neg_exp = neg_exp + 1ULL; }
  }
  u64 pos = 1023ULL + ean;
  u64 neg = ebn + neg_exp;
  u64 q = 0ULL;
  u64 r = ma;
  u64 i = 0ULL;
  while (i < 56ULL) {
    q = q << 1;
    if (r >= mb) { r = r - mb; q = q | 1ULL; }
    r = r << 1;
    i = i + 1ULL;
  }
  if (r != 0ULL) { q = q | 1ULL; }
  if (pos <= neg) {
    u64 sh = (neg - pos) + 1ULL;
    if (sh > 56ULL) { return 0ULL; }
    u64 lost = q & ((1ULL << sh) - 1ULL);
    q = (q >> sh) | (lost != 0ULL ? 1ULL : 0ULL);
    return f64u_round_pack(1ULL, q);
  }
  exp_val = pos - neg;
  return f64u_round_pack(exp_val, q);
}

u64 f64u_inv_u64(u64 k) {
  if (k == 0ULL) { return 0x7FF0000000000000ULL; }
  if (k == 1ULL) { return 0x3FF0000000000000ULL; }
  u64 msb = f64u_msb64(k);
  if ((k & (k - 1ULL)) == 0ULL) {
    if (msb >= 1023ULL) { return 0ULL; }
    return (1023ULL - msb) << 52;
  }
  u64 d = k;
  u64 d_msb = msb;
  if (msb > 52ULL) {
    u64 sh = msb - 52ULL;
    u64 m = k >> sh;
    u64 rem = k & ((1ULL << sh) - 1ULL);
    u64 half = 1ULL << (sh - 1ULL);
    if (rem > half || (rem == half && (m & 1ULL) != 0ULL)) {
      m = m + 1ULL;
      if (m >= (1ULL << 53)) { m = m >> 1; msb = msb + 1ULL; }
    }
    d = m;
    d_msb = 52ULL;
  }
  u64 exp = 1023ULL - msb;
  if (d_msb <= 8ULL) {
    u64 num = 1ULL << (55ULL + d_msb);
    u64 q = num / d;
    u64 r = num - q * d;
    if (r != 0ULL) { q = q | 1ULL; }
    return f64u_round_pack(exp, q);
  }
  u64 s2 = d_msb - 8ULL;
  u64 q1 = (1ULL << 63) / d;
  u64 r1 = (1ULL << 63) - q1 * d;
  if (d_msb <= 32ULL) {
    u64 q2 = (r1 << s2) / d;
    u64 r2 = (r1 << s2) - q2 * d;
    u64 q = (q1 << s2) + q2;
    if (r2 != 0ULL) { q = q | 1ULL; }
    return f64u_round_pack(exp, q);
  }
  u64 q = q1;
  u64 rem = r1;
  while (s2 > 0ULL) {
    u64 st = (s2 > 11ULL) ? 11ULL : s2;
    u64 num = rem << st;
    u64 qi = num / d;
    rem = num - qi * d;
    q = (q << st) + qi;
    s2 = s2 - st;
  }
  if (rem != 0ULL) { q = q | 1ULL; }
  return f64u_round_pack(exp, q);
}

u64 f64u_from_u64(u64 x) {
  if (x == 0ULL) { return 0ULL; }
  u64 msb = f64u_msb64(x);
  u64 exp = 1023ULL + msb;
  if (msb <= 52ULL) {
    u64 m = x << (52ULL - msb);
    return (exp << 52) | (m & ((1ULL << 52) - 1ULL));
  }
  u64 sh = msb - 52ULL;
  u64 m = x >> sh;
  u64 rem = x & ((1ULL << sh) - 1ULL);
  u64 half = 1ULL << (sh - 1ULL);
  if (rem > half || (rem == half && (m & 1ULL) != 0ULL)) {
    m = m + 1ULL;
    if (m >= (1ULL << 53)) { m = m >> 1; exp = exp + 1ULL; }
  }
  return (exp << 52) | (m & ((1ULL << 52) - 1ULL));
}

u64 f64u_to_u64(u64 a) {
  u64 e = a >> 52;
  if (e < 1023ULL) { return 0ULL; }
  u64 sh = e - 1023ULL;
  if (sh >= 64ULL) { return 0xFFFFFFFFFFFFFFFFULL; }
  u64 m = (1ULL << 52) | (a & ((1ULL << 52) - 1ULL));
  if (sh >= 52ULL) { return m << (sh - 52ULL); }
  return m >> (52ULL - sh);
}

s0_u64_pair u64_mul128(u64 a, u64 b) {
  u64 a0 = a & 0xFFFFFFFFULL;
  u64 a1 = a >> 32;
  u64 b0 = b & 0xFFFFFFFFULL;
  u64 b1 = b >> 32;
  u64 p00 = a0 * b0;
  u64 p01 = a0 * b1;
  u64 p10 = a1 * b0;
  u64 p11 = a1 * b1;
  u64 mid = (p00 >> 32) + (p01 & 0xFFFFFFFFULL) + (p10 & 0xFFFFFFFFULL);
  u64 lo = (p00 & 0xFFFFFFFFULL) | (mid << 32);
  u64 hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
  return C0_TUP2(s0_u64_pair, lo, hi);
}

u64 f64u_log10_u64(u64 x) {
  if (x <= 1ULL) { return 0ULL; }
  u64 k = f64u_msb64(x);
  u64 m = (k <= 61ULL) ? (x << (61ULL - k)) : (x >> (k - 61ULL));
  u64 frac = 0ULL;
  u64 i = 0ULL;
  while (i < 64ULL) {
    u64 hi = 0ULL;
    u64 lo = 0ULL;
    C0_TIE2(lo, hi, u64_mul128(m, m));
    u64 sq = (hi << 3) | (lo >> 61);
    frac = frac << 1;
    if (sq >= (1ULL << 62)) { frac = frac | 1ULL; m = sq >> 1; }
    else { m = sq; }
    i = i + 1ULL;
  }
  u64 lg2_hi = 0x4D104D427DE7FBCCULL;
  u64 a = (k << 58) | (frac >> 6);
  u64 p_hi = 0ULL;
  u64 p_lo = 0ULL;
  C0_TIE2(p_lo, p_hi, u64_mul128(a, lg2_hi));
  u64 exp = 1028ULL;
  if (p_hi == 0ULL) {
    if (p_lo == 0ULL) { return 0ULL; }
    u64 sh = 63ULL - f64u_msb64(p_lo);
    p_hi = p_lo >> (64ULL - sh);
    if (sh == 64ULL) { p_hi = p_lo; }
    p_lo = 0ULL;
    exp = exp - sh;
  } else if (p_hi < (1ULL << 63)) {
    u64 sh = 63ULL - f64u_msb64(p_hi);
    p_hi = (p_hi << sh) | (p_lo >> (64ULL - sh));
    p_lo = p_lo << sh;
    exp = exp - sh;
  }
  u64 low8 = (p_hi & 255ULL) | ((p_lo != 0ULL) ? 1ULL : 0ULL);
  return f64u_round_pack(exp, (p_hi >> 8) | ((low8 != 0ULL) ? 1ULL : 0ULL));
}

u64 f64u_nlogpown(u64 count, u64 exponent) {
  u64 arg = (count > (~0ULL) - 9ULL) ? (~0ULL) : (count + 9ULL);
  u64 tmp = f64u_log10_u64(arg);
  u64 factor = 0x3FF0000000000000ULL;
  u64 i = 0ULL;
  while (i < exponent) {
    factor = f64u_mul(factor, tmp);
    i = i + 1ULL;
  }
  return f64u_mul(f64u_from_u64(count), factor);
}

u64 m6_wm4_get(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - 2304ULL);
  if (e[0] != 0x4D36484452455831ULL) { return 0ULL; }
  return e[28ULL];
}

void m6_wm4_set(FullHdr *h, u64 v) {
  u64 *e = (u64 *)((u64)h - 2304ULL);
  if (e[0] != 0x4D36484452455831ULL) { return; }
  e[28ULL] = v;
}

void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = 0ULL;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = 0ULL; h->scinc = 0x3FF0000000000000ULL;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL; h->rel_limit = 1048576ULL; h->rel_wait = 1024ULL;
  h->rel_u = 1ULL; h->rel_v = 1ULL; h->rel_trigger = 0ULL;
  h->conflicts = 0ULL; h->learned_lits = 0ULL; h->min_removed = 0ULL;
  h->stable = 0ULL; h->switched = 0ULL; h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL; h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL; h->search_ticks = 0ULL;
  h->q_first = 0xFFFFFFFFULL;
  h->q_last = 0xFFFFFFFFULL;
  h->q_search_idx = 0xFFFFFFFFULL;
  h->q_search_stamp = 0ULL; h->q_cur_stamp = 0ULL;
  h->target_assigned = 0ULL; h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL; h->rephased = 0ULL;
  h->reduce_limit = 1000ULL; h->reductions = 0ULL;
  h->tier1 = 2ULL; h->tier2 = 6ULL;
  h->restarts = 0ULL; h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 0x3FF0000000000000ULL;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 0x3FF0000000000000ULL;
  h->oom = 0ULL; h->extend_len = 0ULL;
  h->rng_state = 0x9E3779B97F4A7C15ULL ^ (mv + 1ULL);
  h->chrono_levels = 100ULL; h->otfs_cnt = 0ULL; h->eager_sub_cnt = 0ULL;
  h->probe_limit = 2000ULL; h->probings = 0ULL;
  h->elim_limit = 5000ULL; h->eliminations = 0ULL; h->elim_bound = 0ULL;
  h->dense_mode = 0ULL; h->inconsistent = 0ULL; h->iterating = 0ULL;
  h->hbr_cnt = 0ULL; h->trans_cnt = 0ULL; h->viv_cnt = 0ULL; h->subst_cnt = 0ULL;
  h->cong_cnt = 0ULL; h->sweep_cnt = 0ULL; h->bve_cnt = 0ULL; h->bce_cnt = 0ULL;
  h->bva_cnt = 0ULL; h->walk_cnt_stat = 0ULL; h->fwd_sub_cnt = 0ULL; h->fwd_str_cnt = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
}

#define M6_EXT_WORDS 288ULL
#define M6_EXT_BYTES 2304ULL
#define M6_HDR_MAGIC 0x4D36484452455831ULL
#define M6W_MAGIC 0ULL
#define M6W_DR_STATE 1ULL
#define M6W_DR_SE 6ULL
#define M6W_TIER1 8ULL
#define M6W_TIER2 10ULL
#define M6W_GLUE_INTV 13ULL
#define M6W_TOTAL_USED 14ULL
#define M6W_WM_BASE 24ULL
#define M6W_USED0 32ULL
#define M6W_USED1 160ULL
#define M6_GLUE_BINS 128ULL

void m6_hdr_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 i = 0ULL;
  while (i < M6_EXT_WORDS) {
    e[i] = 0ULL;
    i = i + 1ULL;
  }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_SE] = 0x3FF0000000000000ULL;
  e[M6W_DR_SE + 1ULL] = 0x3FF0000000000000ULL;
  e[M6W_TIER1] = 2ULL;
  e[M6W_TIER1 + 1ULL] = 2ULL;
  e[M6W_TIER2] = 6ULL;
  e[M6W_TIER2 + 1ULL] = 6ULL;
  e[M6W_GLUE_INTV] = 2ULL;
  e[M6W_WM_BASE] = h->fwd_sub_cnt;
  e[M6W_WM_BASE + 1ULL] = 0ULL;
  e[M6W_MAGIC] = M6_HDR_MAGIC;
}

void m6_hdr_recompute_tiers_mode(FullHdr *h, u64 st) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 mode = (st != 0ULL) ? 1ULL : 0ULL;
  u64 base = (mode == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < M6_GLUE_BINS) {
    u64 u = e[base + g];
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  e[M6W_TOTAL_USED + mode] = total;
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = total >> 1;
    u64 lim2 = f64u_to_u64(f64u_mul(f64u_from_u64(total), 0x3FECCCCCCCCCCCCDULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < M6_GLUE_BINS) {
      u64 u = e[base + g];
      if (acc <= 0xFFFFFFFFFFFFFFFFULL - u) { acc = acc + u; }
      else { acc = 0xFFFFFFFFFFFFFFFFULL; }
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  e[M6W_TIER1 + mode] = t1;
  e[M6W_TIER2 + mode] = t2;
  m6_hdr_sync_legacy_tiers(h);
}

#undef M6_EXT_WORDS
#undef M6_EXT_BYTES
#undef M6_HDR_MAGIC
#undef M6W_MAGIC
#undef M6W_DR_STATE
#undef M6W_DR_SE
#undef M6W_TIER1
#undef M6W_TIER2
#undef M6W_GLUE_INTV
#undef M6W_TOTAL_USED
#undef M6W_WM_BASE
#undef M6W_USED0
#undef M6W_USED1
#undef M6_GLUE_BINS
"

/-- The `14` new `S0` helper functions (callees-first order). -/
def fidStep13S0AddFns : List Fn :=
  [ f64u_msb64, f64u_round_pack, f64u_add, f64u_sub, f64u_mul, f64u_div
  , f64u_inv_u64, f64u_from_u64, f64u_to_u64, u64_mul128, f64u_log10_u64
  , f64u_nlogpown, m6_wm4_get, m6_wm4_set ]

/-- The `3` modified `S0` replacement functions (`full_init_hdr` & `m6_hdr_*`). -/
def fidStep13S0Repls : List Fn :=
  [ full_init_hdr, m6_hdr_init, m6_hdr_recompute_tiers_mode ]

/-- All `17` Step-13 `S0` functions in module order. -/
def fidStep13S0AllFns : List Fn :=
  fidStep13S0AddFns ++ fidStep13S0Repls

end

public section

theorem f64u_msb64_wf : Func.Wf f64u_msb64_body := by t_wf_reify
theorem f64u_round_pack_wf : Func.Wf f64u_round_pack_body := by t_wf_reify
theorem f64u_add_wf : Func.Wf f64u_add_body := by t_wf_reify
theorem f64u_sub_wf : Func.Wf f64u_sub_body := by t_wf_reify
theorem f64u_mul_wf : Func.Wf f64u_mul_body := by t_wf_reify
theorem f64u_div_wf : Func.Wf f64u_div_body := by t_wf_reify
theorem f64u_inv_u64_wf : Func.Wf f64u_inv_u64_body := by t_wf_reify
theorem f64u_from_u64_wf : Func.Wf f64u_from_u64_body := by t_wf_reify
theorem f64u_to_u64_wf : Func.Wf f64u_to_u64_body := by t_wf_reify
theorem u64_mul128_wf : Func.Wf u64_mul128_body := by t_wf_reify
theorem f64u_log10_u64_wf : Func.Wf f64u_log10_u64_body := by t_wf_reify
theorem f64u_nlogpown_wf : Func.Wf f64u_nlogpown_body := by t_wf_reify
theorem m6_wm4_get_wf : Func.Wf m6_wm4_get_body := by t_wf_reify
theorem m6_wm4_set_wf : Func.Wf m6_wm4_set_body := by t_wf_reify
theorem full_init_hdr_wf : Func.Wf full_init_hdr_body := by t_wf_reify
theorem m6_hdr_init_wf : Func.Wf m6_hdr_init_body := by t_wf_reify
theorem m6_hdr_recompute_tiers_mode_wf :
    Func.Wf m6_hdr_recompute_tiers_mode_body := by t_wf_reify

theorem fidStep13S0AllFns_eq : fidStep13S0AllFns = fidStep13S0_fns := rfl

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
