/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Restarts, Trail Reuse & Focused/Stable Mode Switching (`Src/Restart.lean`)

Mirrors upstream `kissat/src/restart.c, mode.c` (`3` live functions, DAG level `L3`):
- `full_restart_due` (R4: `kissat_restarting`)
- `full_restart` (R4: `kissat_restart`)
- `full_switch_mode_m7` (R4: `kissat_switch_search_mode`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Restart

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! restart "
#include \"kissat_internal.h\"

extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_sub(u64 a, u64 b);
extern u64 f64u_log10_u64(u64 x);
extern u64 f64u_to_u64(u64 a);
extern u64 full_randec_var_lvl_fid(FullHdr *h, u64 max_lvl);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_heap_push(FullHdr *h, u32 v);
extern u64 f64u_nlogpown(u64 count, u64 exponent);
extern void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m);
extern void m6_hdr_dr_init(FullHdr *h);
extern u64 full_ilog10(u64 x);
extern u64 full_m7_get64(FullHdr *h, u64 idx);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);

u64 full_restart_due(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) { h->rel_trigger = 0ULL; return 1ULL; }
    return 0ULL;
  }
  u64 fe = h->ema_fast_exp;
  u64 se = h->ema_slow_exp;
  u64 fb = h->ema_fast_biased;
  u64 sb = h->ema_slow_biased;
  u64 margin = 0x3FF199999999999AULL;
  bool fire = false;
  if (fe == 0ULL && se == 0ULL) {
    fire = (f64u_mul(margin, sb) <= fb);
  } else {
    u64 one = 0x3FF0000000000000ULL;
    u64 fdiv = (fe == 0ULL) ? one : f64u_sub(one, fe);
    u64 sdiv = (se == 0ULL) ? one : f64u_sub(one, se);
    if (fdiv == 0ULL || sdiv == 0ULL) { return 0ULL; }
    u64 lhs = f64u_mul(f64u_mul(margin, sb), fdiv);
    u64 rhs = f64u_mul(fb, sdiv);
    fire = (lhs <= rhs);
  }
  if (fire) {
    u64 rst = (h->restarts < 1000000000000ULL) ? (h->restarts + 1ULL) : 1000000000000ULL;
    u64 lg = f64u_log10_u64(rst + 9ULL);
    u64 delta = f64u_to_u64(lg);
    if (delta < 1ULL) { delta = 1ULL; }
    h->restart_limit = h->conflicts + delta;
    return 1ULL;
  }
  return 0ULL;
}

void full_restart(FullHdr *h) {
  h->restarts = h->restarts + 1ULL;
  u64 nv = full_randec_var_lvl_fid(h, 1ULL);
  if (nv == 0xFFFFFFFFFFFFFFFFULL) { nv = full_next_dec_var(h); }
  u64 reuse = 0ULL;
  if (nv < h->cur_vars && h->cur_level > 0ULL) {
    u32 *fdec = (u32 *)h->frame_dec;
    if (h->stable != 0ULL) {
      u64 *sc = (u64 *)h->score; u64 lim = sc[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || sc[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    } else {
      u32 *qs = (u32 *)h->q_stamp; u32 lim = qs[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || qs[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    }
  }
  full_backtrack(h, reuse);
}

void full_switch_mode_m7(FullHdr *h) {
  u64 old_m = 0ULL;
  u64 new_m = 1ULL;
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    old_m = 0ULL;
    new_m = 1ULL;
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 v = 0ULL;
    u64 wm4__ = m6_wm4_get(h);
    if ((wm4__ & 1ULL) == 0ULL) {
      while (v < cv) { ps[v] = 0xFFFFFFFFu; v = v + 1ULL; }
      h->heap_len = 0ULL;
      m6_wm4_set(h, wm4__ | 1ULL);
    } else {
      v = 0ULL;
      while (v < cv) {
        if ((fl[v] & FL_ACTIVE) == 0u) {
          u64 n__ = h->heap_len; u32 p__ = ps[v];
          if (n__ > 0ULL && n__ <= cv && (u64)p__ < n__ && hp[p__] == (u32)v) {
            u32 last__ = hp[n__ - 1ULL];
            h->heap_len = n__ - 1ULL;
            if ((u64)last__ < cv) { ps[last__] = 0xFFFFFFFFu; }
            if (last__ != (u32)v) {
              ps[v] = 0xFFFFFFFFu;
              if ((u64)last__ < cv) {
                hp[p__] = last__; ps[last__] = p__;
                full_heap_up(h, last__); full_heap_down(h, last__);
              }
            }
          } else { ps[v] = 0xFFFFFFFFu; }
        }
        v = v + 1ULL;
      }
    }
    v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u) { full_heap_push(h, (u32)v); }
      v = v + 1ULL;
    }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 scaled = 1000ULL * f64u_to_u64(f64u_nlogpown(cnt, 4ULL));
    h->mode_confl_lim = h->conflicts + scaled;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  full_ema_swap_m7(h, old_m, new_m);
  {
    m6_hdr_dr_init(h);
    u64 *e__ = (u64 *)((u64)h - 2304ULL);
    u64 mask56__ = (1ULL << 56) - 1ULL;
    u64 decs__ = e__[1] & mask56__;
    e__[1] = (1ULL << 63) | ((h->switched & 127ULL) << 56) | decs__;
    e__[2ULL + ((h->stable != 0ULL) ? 1ULL : 0ULL)] = decs__;
  }
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 0ULL) ? d10 : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
    u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
    u64 lc = full_m7_get64(h, M7_GU_RANDEC_CFL);
    if (h->conflicts > lc) {
      u64 dc = h->conflicts - lc;
      rem = (rem > dc) ? (rem - dc) : 0ULL;
      full_m7_set64(h, M7_GU_RANDEC_REM, rem);
    }
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
    if (rem == 0ULL) {
      u64 rseq = full_m7_get64(h, M7_GU_RANDEC_SEQ) + 1ULL;
      full_m7_set64(h, M7_GU_RANDEC_SEQ, rseq);
      u64 qarg = (rseq > (~0ULL) - 9ULL) ? (~0ULL) : (rseq + 9ULL);
      u64 lg = f64u_log10_u64(qarg);
      u64 rlen = f64u_to_u64(f64u_mul(0x4024000000000000ULL, lg));
      if (rlen < 10ULL) { rlen = 10ULL; }
      u64 rdelta = f64u_to_u64(f64u_mul(0x407F400000000000ULL, lg));
      full_m7_set64(h, M7_GU_RANDEC_REM, rlen);
      full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + rdelta);
    }
  }
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Restart
