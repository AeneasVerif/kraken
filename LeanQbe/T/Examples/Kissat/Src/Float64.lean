/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Soft IEEE-754 Float64 & Watermark4 Helpers (`Src/Float64.lean`)

Pure-integer IEEE-754 binary64 arithmetic (`log10`, `nlogpown`, rounding/mul/div) and 4-word
watermark counters matching Step-13 S0 (`14` live functions, DAG level `L0`):
- `f64u_msb64`
- `f64u_round_pack`
- `f64u_add`
- `f64u_sub`
- `f64u_mul`
- `f64u_div`
- `f64u_inv_u64`
- `f64u_from_u64`
- `f64u_to_u64`
- `u64_mul128`
- `f64u_log10_u64`
- `f64u_nlogpown`
- `m6_wm4_get`
- `m6_wm4_set`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Float64

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! float64 "
#include \"kissat_internal.h\"

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

typedef C0_RET2(u64, u64) s0_u64_pair;

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
"

end

end LeanQbe.T.Examples.Kissat.Src.Float64
