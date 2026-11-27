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
- `full_switch_mode_m7` (R4: `kissat_switch_search_mode`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Restart

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! restart "
#include \"kissat_internal.h\"

extern u64 full_ilog10(u64 x);
extern u64 full_log10_q16_m7(u64 x);
extern u64 full_m7_get64(FullHdr *h, u64 idx);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_next_dec_var(FullHdr *h);

u64 full_restart_due(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) { h->rel_trigger = 0ULL; return 1ULL; }
    return 0ULL;
  }
  u64 scale = 1ULL << 32;
  u64 fe = h->ema_fast_exp;
  u64 se = h->ema_slow_exp;
  if (fe >= scale || se >= scale) { return 0ULL; }
  u64 fd = scale - fe;
  u64 sd = scale - se;
  if (fd == 0ULL || sd == 0ULL) { return 0ULL; }
  u64 fb = h->ema_fast_biased;
  u64 sb = h->ema_slow_biased;
  u64 fbc = (fb > (16384ULL << 32)) ? (16384ULL << 32) : fb;
  u64 sbc = (sb > (16384ULL << 32)) ? (16384ULL << 32) : sb;
  u64 fval = (fbc << 16) / fd;
  u64 sval = (sbc << 16) / sd;
  if (fval > (1ULL << 32)) { fval = 1ULL << 32; }
  if (sval > (1ULL << 32)) { sval = 1ULL << 32; }
  if (fval * 100ULL >= sval * 110ULL) {
    u64 rst = (h->restarts < 1000000000000ULL) ? (h->restarts + 1ULL) : 1000000000000ULL;
    u64 d10 = full_ilog10(rst + 9ULL);
    u64 delta = (d10 > 0ULL) ? d10 : 1ULL;
    h->restart_limit = h->conflicts + delta;
    return 1ULL;
  }
  return 0ULL;
}

void full_restart(FullHdr *h) {
  h->restarts = h->restarts + 1ULL;
  u64 nv = full_next_dec_var(h);
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
    u64 n = 0ULL;
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u) {
        hp[n] = (u32)v;
        ps[v] = (u32)n;
        n = n + 1ULL;
      } else {
        ps[v] = 0xFFFFFFFFu;
      }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16_m7(cc + 9ULL);
    u64 l2 = (q * q) >> 16;
    u64 l4 = (l2 * l2) >> 16;
    u64 scaled = 0ULL;
    if (cnt <= 1000000ULL) {
      scaled = (1000ULL * cnt * l4) >> 16;
    } else {
      u64 clim = (cnt > 100000000ULL) ? 100000000ULL : cnt;
      scaled = ((1000ULL * clim) >> 16) * l4;
    }
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
      u64 qarg = (rseq < 1000000000000ULL) ? (rseq + 9ULL) : 1000000000009ULL;
      u64 lg = full_log10_q16_m7(qarg);
      u64 rlen = (10ULL * lg) >> 16;
      if (rlen < 10ULL) { rlen = 10ULL; }
      u64 rdelta = (500ULL * lg) >> 16;
      full_m7_set64(h, M7_GU_RANDEC_REM, rlen);
      full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + rdelta);
    }
  }
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Restart
