/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Limits, Smooth EMAs, Reluctant, RNG & Utilities (`Src/Limits.lean`)

Mirrors upstream `kissat/src/kimits.c, smooth.c, reluctant.c, random.h, sort.c`
(`17` live functions, DAG level `L0`):
- `full_isqrt` (R4: `kissat_isqrt`)
- `full_ilog10` (R4: `kissat_ilog10`)
- `full_rng_next` (R4: `kissat_rng_next`)
- `full_tick_rel` (R4: `kissat_tick_reluctant`)
- `full_log10_q16_m7` (R4: `kissat_log10_q16`)
- `full_scale_delta_m5` (R4: `kissat_scale_delta_probe`)
- `full_ema_update` (R4: `kissat_update_smooth`)
- `full_scale_delta` (R4: `kissat_scale_delta`)
- `full_fill_u64_m7` (R4: `kissat_fill_u64`)
- `full_sort_u32` (R4: `kissat_sort_u32`)
- `full_max_u64` (R4: `kissat_max_u64`)
- `full_elim_dticks` (R4: `kissat_elim_delta_ticks`)
- `full_lcg_next_m7` (R4: `kissat_lcg_next`)
- `full_m7_get64` (R4: `kissat_ext_get64`)
- `full_m7_set64` (R4: `kissat_ext_set64`)
- `full_m7_state_init` (R4: `kissat_mode_state_init`)
- `full_ema_swap_m7` (R4: `kissat_swap_averages`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Limits

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! limits "
#include \"kissat_internal.h\"

u64 full_isqrt(u64 x) {
  if (x <= 1ULL) { return x; }
  u64 r = 0ULL;
  u64 bit = 1ULL << 62;
  while (bit > x) { bit = bit >> 2; }
  while (bit != 0ULL) {
    if (x >= r + bit) {
      x = x - (r + bit);
      r = (r >> 1) + bit;
    } else {
      r = r >> 1;
    }
    bit = bit >> 2;
  }
  return (r == 0ULL) ? 1ULL : r;
}

u64 full_ilog10(u64 x) {
  u64 r = 1ULL;
  u64 p = 10ULL;
  while (x / 10ULL >= p && r < 19ULL) {
    r = r + 1ULL;
    p = p * 10ULL;
  }
  return r;
}

u64 full_rng_next(FullHdr *h) {
  u64 x = h->rng_state * 6364136223846793005ULL + 1442695040888963407ULL;
  h->rng_state = x;
  return x >> 32;
}

void full_tick_rel(FullHdr *h) {
  if (h->stable == 0ULL || h->rel_period == 0ULL || h->rel_trigger != 0ULL) { return; }
  if (h->rel_wait > 0ULL) { h->rel_wait = h->rel_wait - 1ULL; }
  if (h->rel_wait > 0ULL) { return; }
  u64 u = h->rel_u;
  u64 v = h->rel_v;
  if (u == 0ULL || v == 0ULL) { u = 1ULL; v = 1ULL; }
  if ((u & (0ULL - u)) == v) { u = u + 1ULL; v = 1ULL; } else { v = v << 1ULL; }
  if (v == 0ULL || v > (1ULL << 30) || h->rel_period > (1ULL << 30)) { u = 1ULL; v = 1ULL; }
  u64 wait = v * h->rel_period;
  if (h->rel_limit > 0ULL && wait > h->rel_limit) { u = 1ULL; v = 1ULL; wait = h->rel_period; }
  h->rel_trigger = 1ULL; h->rel_wait = wait; h->rel_u = u; h->rel_v = v;
}

u64 full_log10_q16_m7(u64 x) {
  if (x <= 1ULL) { return 0ULL; }
  u64 d = 0ULL;
  u64 pow10 = 1ULL;
  while (x / 10ULL >= pow10 && d < 19ULL) {
    d = d + 1ULL;
    pow10 = pow10 * 10ULL;
  }
  u64 xm = x;
  u64 pm = pow10;
  if (pm > 100000000ULL) {
    u64 sc = pm / 100000000ULL;
    xm = xm / sc;
    pm = 100000000ULL;
  }
  u64 m = (xm << 32) / pm;
  u64 lim10 = 10ULL << 32;
  u64 frac = 0ULL;
  u64 i = 0ULL;
  while (i < 16ULL) {
    u64 m_hi = m >> 16;
    u64 m_lo = m & 0xFFFFULL;
    u64 q = (m_lo * m_lo) >> 16;
    u64 mid = (2ULL * m_hi * m_lo) + q;
    m = (m_hi * m_hi) + (mid >> 16);
    frac = frac << 1;
    if (m >= lim10) {
      m = m / 10ULL;
      frac = frac + 1ULL;
    }
    i = i + 1ULL;
  }
  return (d << 16) + frac;
}

u64 full_scale_delta_m5(FullHdr *h, u64 delta) {
  if (delta == 0ULL) { return 0ULL; }
  u64 ir = h->num_irred;
  u64 bn = h->num_binary;
  u64 clauses = (ir > 0xFFFFFFFFFFFFFFFFULL - bn) ? 0xFFFFFFFFFFFFFFFFULL : (ir + bn);
  u64 arg = (clauses > 0xFFFFFFFFFFFFFFF5ULL) ? 0xFFFFFFFFFFFFFFFFULL : (clauses + 10ULL);
  u64 l = full_log10_q16_m7(arg);
  if (l < 65536ULL) { l = 65536ULL; }
  if (l > 1310720ULL) { l = 1310720ULL; }
  u64 target = 327680ULL;
  u64 f_abs = (l >= target) ? (l - target) : (target - l);
  u64 fff_q16 = ((9ULL * f_abs * f_abs) >> 17) + 1638400ULL;
  u64 lim = 0xFFFFFFFFFFFFFFFFULL / fff_q16;
  if (delta <= lim) {
    return (fff_q16 * delta) >> 16;
  }
  u64 hi = delta >> 16;
  if (hi <= lim) {
    u64 lo = delta & 0xFFFFULL;
    u64 q1 = hi * fff_q16;
    u64 q2 = (lo * fff_q16) >> 16;
    if (q1 > 0xFFFFFFFFFFFFFFFFULL - q2) { return 0xFFFFFFFFFFFFFFFFULL; }
    return q1 + q2;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

void full_ema_update(FullHdr *h, u64 glue) {
  if (h->stable != 0ULL) { return; }
  u64 g = (glue > 16383ULL) ? 16383ULL : glue;
  u64 ys = g << 32;
  u64 fb = h->ema_fast_biased;
  u64 fe = h->ema_fast_exp;
  u64 sb = h->ema_slow_biased;
  u64 se = h->ema_slow_exp;
  if (fe == (1ULL << 24) && se == (1ULL << 24) && fb == 0ULL && sb == 0ULL) {
    fe = 1ULL << 32;
    se = 1ULL << 32;
  }
  if (ys >= fb) { fb = fb + ((ys - fb) / 33ULL); }
  else { fb = fb - ((fb - ys) / 33ULL); }
  h->ema_fast_biased = fb;
  if (fe > 0ULL) {
    u64 df = fe / 33ULL;
    h->ema_fast_exp = (df == 0ULL) ? 0ULL : (fe - df);
  }
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  h->ema_slow_biased = sb;
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    h->ema_slow_exp = (ds == 0ULL) ? 0ULL : (se - ds);
  }
}

u64 full_scale_delta(FullHdr *h, u64 delta) {
  if (delta == 0ULL) { return 0ULL; }
  u64 ir = h->num_irred;
  u64 bn = h->num_binary;
  u64 clauses = (ir > 0xFFFFFFFFFFFFFFFFULL - bn) ? 0xFFFFFFFFFFFFFFFFULL : (ir + bn);
  u64 arg = (clauses > 0xFFFFFFFFFFFFFFF5ULL) ? 0xFFFFFFFFFFFFFFFFULL : (clauses + 10ULL);
  u64 l = full_log10_q16_m7(arg);
  if (l < 65536ULL) { l = 65536ULL; }
  if (l > 1310720ULL) { l = 1310720ULL; }
  u64 target = 327680ULL;
  u64 f_abs = (l >= target) ? (l - target) : (target - l);
  u64 fff_q16 = ((9ULL * f_abs * f_abs) >> 17) + 1638400ULL;
  u64 lim = 0xFFFFFFFFFFFFFFFFULL / fff_q16;
  if (delta <= lim) {
    return (fff_q16 * delta) >> 16;
  }
  u64 hi = delta >> 16;
  if (hi <= lim) {
    u64 lo = delta & 0xFFFFULL;
    u64 q1 = hi * fff_q16;
    u64 q2 = (lo * fff_q16) >> 16;
    if (q1 > 0xFFFFFFFFFFFFFFFFULL - q2) { return 0xFFFFFFFFFFFFFFFFULL; }
    return q1 + q2;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

void full_fill_u64_m7(u64 *dst, u64 n, u64 val) {
  u64 i = 0ULL;
  while (i + 4ULL <= n) {
    dst[i] = val;
    dst[i + 1ULL] = val;
    dst[i + 2ULL] = val;
    dst[i + 3ULL] = val;
    i = i + 4ULL;
  }
  while (i < n) {
    dst[i] = val;
    i = i + 1ULL;
  }
}

void full_sort_u32(u32 *arr, u32 n) {
  u64 len = (u64)n;
  if (len <= 1ULL) {
    return;
  }
  if (len == 2ULL) {
    u32 a = arr[0];
    u32 b = arr[1];
    if (a > b) {
      arr[0] = b;
      arr[1] = a;
    }
    return;
  }
  u64 gap = 1ULL;
  if (len > 16ULL) {
    u64 lim = len / 3ULL;
    while (gap < lim) {
      gap = gap * 3ULL + 1ULL;
    }
  }
  while (gap >= 1ULL) {
    u64 i = gap;
    while (i < len) {
      u32 x = arr[i];
      u64 j = i;
      bool go = true;
      while (go) {
        if (j < gap) {
          go = false;
        } else {
          u32 prev = arr[j - gap];
          if (prev <= x) {
            go = false;
          } else {
            arr[j] = prev;
            j = j - gap;
          }
        }
      }
      arr[j] = x;
      i = i + 1ULL;
    }
    gap = gap / 3ULL;
  }
}

u64 full_max_u64(u64 a, u64 b) { return (a > b) ? a : b; }

u64 full_elim_dticks(FullHdr *h, bool initial) {
  u64 raw = (h->search_ticks > h->fwd_str_cnt) ? (h->search_ticks - h->fwd_str_cnt) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + h->num_irred + h->num_binary) * 12ULL) : raw;
  return full_max_u64(dticks, 10000000ULL);
}

u64 full_lcg_next_m7(FullHdr *h) {
  u64 x = h->rng_state;
  x = x * 6364136223846793005ULL + 1442695040888963407ULL;
  h->rng_state = x;
  return x >> 32;
}

u64 full_m7_get64(FullHdr *h, u64 idx) {
  if (idx >= 63ULL) { return 0ULL; }
  u32 *gu = (u32 *)h->glue_used;
  return ((u64)gu[idx]) | (((u64)gu[idx + 1ULL]) << 32);
}

void full_m7_set64(FullHdr *h, u64 idx, u64 val) {
  if (idx >= 63ULL) { return; }
  u32 *gu = (u32 *)h->glue_used;
  gu[idx] = (u32)val;
  gu[idx + 1ULL] = (u32)(val >> 32);
}

void full_m7_state_init(FullHdr *h) {
  if (full_m7_get64(h, M7_GU_MAGIC) == M7_SEARCH_MAGIC) { return; }
  full_m7_set64(h, M7_GU_MAGIC, M7_SEARCH_MAGIC);
  u64 cm = (h->stable != 0ULL) ? 1ULL : 0ULL;
  full_m7_set64(h, M7_GU_EMA_MASK, 1ULL << cm);
  u64 init_exp = 1ULL << 32;
  if (cm == 0ULL) {
    full_m7_set64(h, M7_GU_EMA0_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA0_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA0_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA1_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_SE, init_exp);
  } else {
    full_m7_set64(h, M7_GU_EMA1_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA1_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA1_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA0_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_SE, init_exp);
  }
  full_m7_set64(h, M7_GU_RANDEC_REM, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + 500ULL);
  full_m7_set64(h, M7_GU_RANDEC_SEQ, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
}

void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m) {
  u64 om = (old_m != 0ULL) ? 1ULL : 0ULL;
  u64 nm = (new_m != 0ULL) ? 1ULL : 0ULL;
  h->stable = om;
  full_m7_state_init(h);
  h->stable = nm;
  u64 old_base = (om == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  full_m7_set64(h, old_base, h->ema_fast_biased);
  full_m7_set64(h, old_base + 2ULL, h->ema_fast_exp);
  full_m7_set64(h, old_base + 4ULL, h->ema_slow_biased);
  full_m7_set64(h, old_base + 6ULL, h->ema_slow_exp);
  u64 mask = full_m7_get64(h, M7_GU_EMA_MASK) | (1ULL << om);
  u64 new_base = (nm == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  u64 bit = 1ULL << nm;
  if ((mask & bit) != 0ULL) {
    h->ema_fast_biased = full_m7_get64(h, new_base);
    h->ema_fast_exp = full_m7_get64(h, new_base + 2ULL);
    h->ema_slow_biased = full_m7_get64(h, new_base + 4ULL);
    h->ema_slow_exp = full_m7_get64(h, new_base + 6ULL);
  } else {
    u64 init_exp = 1ULL << 32;
    h->ema_fast_biased = 0ULL;
    h->ema_fast_exp = init_exp;
    h->ema_slow_biased = 0ULL;
    h->ema_slow_exp = init_exp;
    full_m7_set64(h, new_base, 0ULL);
    full_m7_set64(h, new_base + 2ULL, init_exp);
    full_m7_set64(h, new_base + 4ULL, 0ULL);
    full_m7_set64(h, new_base + 6ULL, init_exp);
    mask = mask | bit;
  }
  full_m7_set64(h, M7_GU_EMA_MASK, mask);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Limits
