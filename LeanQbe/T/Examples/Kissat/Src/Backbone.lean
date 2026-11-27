/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Binary Backbone Probing (`Src/Backbone.lean`)

Mirrors upstream `kissat/src/backbone.c` (`7` live functions, DAG level `L3`):
- `full_backbone_sched_m6` (R4: `kissat_schedule_backbone_candidates`)
- `full_backbone_keep_m6` (R4: `kissat_keep_backbone_candidates`)
- `full_backbone_unwind_m6` (R4: `kissat_backbone_backtrack`)
- `full_backbone_prop_m6` (R4: `kissat_backbone_propagate`)
- `full_backbone_analyze_m6` (R4: `kissat_backbone_analyze`)
- `full_backbone_round_m6` (R4: `kissat_backbone_round`)
- `full_backbone_m6` (R4: `kissat_binary_clauses_backbone`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Backbone

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! backbone "
#include \"kissat_internal.h\"

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern bool full_prioritize_binaries_m6(FullHdr *h);
extern u64 m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);
extern bool full_add_unit(FullHdr *h, u32 lit);

u64 full_backbone_sched_m6(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *cands = (u32 *)h->work_stk1;
  u64 cand_n = 0ULL;
  u64 not_resched = 0ULL;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if ((fl[v] & FL_BONE0) != 0u) {
        cands[cand_n] = (u32)(v << 1); cand_n = cand_n + 1ULL;
      } else {
        not_resched = not_resched + 1ULL;
      }
      if ((fl[v] & FL_BONE1) != 0u) {
        cands[cand_n] = (u32)((v << 1) | 1ULL); cand_n = cand_n + 1ULL;
      } else {
        not_resched = not_resched + 1ULL;
      }
    }
    v = v + 1ULL;
  }
  if (not_resched > 0ULL) {
    v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        if ((fl[v] & FL_BONE0) == 0u) {
          cands[cand_n] = (u32)(v << 1); cand_n = cand_n + 1ULL;
        }
        if ((fl[v] & FL_BONE1) == 0u) {
          cands[cand_n] = (u32)((v << 1) | 1ULL); cand_n = cand_n + 1ULL;
        }
      }
      v = v + 1ULL;
    }
  }
  return cand_n;
}

void full_backbone_keep_m6(FullHdr *h, u64 cand_n) {
  u32 *fl = (u32 *)h->flags;
  u32 *cands = (u32 *)h->work_stk1;
  u64 prioritized = 0ULL;
  u64 remain = 0ULL;
  u64 i = 0ULL;
  while (i < cand_n) {
    u32 lit = cands[i];
    u32 lv = lit >> 1;
    if ((fl[lv] & FL_ACTIVE) != 0u) {
      remain = remain + 1ULL;
      u32 bit = ((lit & 1u) != 0u) ? FL_BONE1 : FL_BONE0;
      if ((fl[lv] & bit) != 0u) { prioritized = prioritized + 1ULL; }
    }
    i = i + 1ULL;
  }
  if (remain == 0ULL || prioritized == remain || prioritized > 0ULL) { return; }
  i = 0ULL;
  while (i < cand_n) {
    u32 lit = cands[i];
    u32 lv = lit >> 1;
    if ((fl[lv] & FL_ACTIVE) != 0u) {
      if ((lit & 1u) == 0u) { fl[lv] = fl[lv] | FL_BONE0; }
      else { fl[lv] = fl[lv] | FL_BONE1; }
    }
    i = i + 1ULL;
  }
}

void full_backbone_unwind_m6(FullHdr *h, u64 saved, u64 target_lvl) {
  u32 *trl = (u32 *)h->trail;
  i8 *vals = (i8 *)h->values;
  while (h->trail_end > saved) {
    h->trail_end = h->trail_end - 1ULL;
    u32 ul = trl[h->trail_end];
    vals[ul] = (i8)0;
    vals[ul ^ 1u] = (i8)0;
  }
  h->cur_level = target_lvl;
}

bool full_backbone_prop_m6(FullHdr *h, u64 prop_start, bool stop_early) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u64 ticks = h->ant_sz;
  u32 clvl = (u32)h->cur_level;
  u64 prop = prop_start;
  while (prop < h->trail_end) {
    u32 lit = trl[prop]; prop = prop + 1ULL;
    u32 not_lit = lit ^ 1u;
    u64 off = (u64)wvec[(u64)not_lit << 1];
    u64 end = off + (u64)wvec[((u64)not_lit << 1) + 1ULL];
    u64 q = off;
    bool confl = false;
    while (q < end) {
      u32 qw = wstk[q];
      if ((qw & PW_BIN_FLAG) == 0u) {
        if (stop_early) { break; }
        q = q + 2ULL;
        continue;
      }
      q = q + 1ULL;
      u32 ot = qw & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        i8 ov = vals[ot];
        if (ov < (i8)0) {
          h->confl_lit0 = (u64)not_lit;
          h->confl_lit1 = (u64)ot;
          confl = true;
          break;
        }
        if (ov == (i8)0 && h->trail_end < h->max_vars) {
          vals[ot] = (i8)1; vals[ot ^ 1u] = (i8)(-1);
          lvl[ot >> 1] = clvl;
          rsns[ot >> 1] = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
          trl[h->trail_end] = ot;
          h->trail_end = h->trail_end + 1ULL;
        }
      }
    }
    u64 dt = 1ULL + (((q - off) + 31ULL) >> 5);
    ticks = (ticks > dt) ? (ticks - dt) : 0ULL;
    if (confl) {
      h->ant_sz = ticks;
      return false;
    }
  }
  h->ant_sz = ticks;
  return true;
}

u32 full_backbone_analyze_m6(FullHdr *h, u32 c0, u32 c1, u64 saved) {
  (void)saved;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u8 *mrk = (u8 *)h->mark;
  u64 saved0 = h->res_sz;
  u32 lv1 = lvl[c1 >> 1];
  if (lv1 == 0u) { return c0 ^ 1u; }
  if (lvl[c0 >> 1] == 0u) { return c1 ^ 1u; }
  if (c0 == c1) { return c0 ^ 1u; }
  mrk[c0 >> 1] = (u8)1; mrk[c1 >> 1] = (u8)1;
  u64 t = h->trail_end;
  u32 res = 0xFFFFFFFFu;
  while (t > saved0) {
    t = t - 1ULL;
    u32 z = trl[t]; u32 zv = z >> 1;
    if (mrk[zv] == (u8)0) { continue; }
    mrk[zv] = (u8)0;
    u32 rsn = rsns[zv];
    if (rsn == 0xFFFFFFFFu || (rsn & PW_BIN_FLAG) == 0u) { break; }
    u32 p = (rsn & PW_LIT_MASK) ^ 1u;
    u32 pv = p >> 1;
    if (mrk[pv] != (u8)0) {
      res = p;
      break;
    }
    mrk[pv] = (u8)1;
  }
  mrk[c0 >> 1] = (u8)0; mrk[c1 >> 1] = (u8)0;
  u64 k = saved0;
  while (k < h->trail_end) { mrk[trl[k] >> 1] = (u8)0; k = k + 1ULL; }
  return res;
}

u64 full_backbone_round_m6(FullHdr *h, u64 cand_n, bool stop_early) {
  u64 saved0 = h->trail_end; u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *fl = (u32 *)h->flags;
  u32 *cands = (u32 *)h->work_stk1; u32 *units = (u32 *)h->work_stk2;
  u64 ucnt = 0ULL; u64 keep = 0ULL; u64 ci = 0ULL; bool incons = false;
  while (ci < cand_n && h->ant_sz > 0ULL && h->trail_end < h->max_vars) {
    u32 probe = cands[ci]; ci = ci + 1ULL;
    i8 pv = vals[probe];
    if (pv > (i8)0) {
      u32 plv = probe >> 1;
      fl[plv] = fl[plv] & (~(((probe & 1u) != 0u) ? FL_BONE1 : FL_BONE0));
      continue;
    }
    if (pv < (i8)0) {
      if (lvl[probe >> 1] > 0u) { cands[keep] = probe; keep = keep + 1ULL; }
      continue;
    }
    u64 saved = h->trail_end; u64 old_lvl = h->cur_level;
    u64 nlvl = old_lvl + 1ULL;
    if (nlvl > h->max_vars) { cands[keep] = probe; keep = keep + 1ULL; break; }
    h->cur_level = nlvl;
    vals[probe] = (i8)1; vals[probe ^ 1u] = (i8)(-1);
    lvl[probe >> 1] = (u32)nlvl; rsns[probe >> 1] = 0xFFFFFFFFu;
    trl[saved] = probe; h->trail_end = saved + 1ULL;
    if (full_backbone_prop_m6(h, saved, stop_early)) {
      continue;
    }
    u32 c0 = (u32)h->confl_lit0; u32 c1 = (u32)h->confl_lit1;
    h->res_sz = saved0;
    u32 uip = full_backbone_analyze_m6(h, c0, c1, saved);
    full_backbone_unwind_m6(h, saved, old_lvl);
    if (uip == 0xFFFFFFFFu) {
      cands[keep] = probe; keep = keep + 1ULL; continue;
    }
    u32 not_uip = uip ^ 1u;
    if (ucnt < nlits) { units[ucnt] = not_uip; ucnt = ucnt + 1ULL; }
    i8 nv = vals[not_uip];
    if (nv < (i8)0) { incons = true; break; }
    if (nv == (i8)0 && h->trail_end < h->max_vars) {
      u64 ustart = h->trail_end;
      vals[not_uip] = (i8)1; vals[uip] = (i8)(-1);
      lvl[not_uip >> 1] = (u32)old_lvl; rsns[not_uip >> 1] = 0xFFFFFFFFu;
      trl[ustart] = not_uip; h->trail_end = ustart + 1ULL;
      bool pok = full_backbone_prop_m6(h, ustart, stop_early);
      if (!pok) { incons = true; break; }
    }
  }
  while (ci < cand_n) {
    cands[keep] = cands[ci]; keep = keep + 1ULL; ci = ci + 1ULL;
  }
  full_backbone_unwind_m6(h, saved0, 0ULL);
  if (!incons) {
    u64 fk = 0ULL; u64 fo = 0ULL;
    while (fk < keep) {
      u32 rem = cands[fk]; fk = fk + 1ULL;
      if (vals[rem] > (i8)0) {
        u32 rlv = rem >> 1;
        fl[rlv] = fl[rlv] & (~(((rem & 1u) != 0u) ? FL_BONE1 : FL_BONE0));
      } else {
        cands[fo] = rem; fo = fo + 1ULL;
      }
    }
    keep = fo;
  }
  h->res_sz = ucnt | (incons ? 0x8000000000000000ULL : 0ULL);
  return keep;
}

u64 full_backbone_m6(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  u64 saved_prob = h->probing;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    return 1ULL;
  }
  h->probing = 1ULL;
  u64 pr0 = full_propagate(h);
  if (pr0 == 1ULL) { h->probing = saved_prob; return 20ULL; }
  if (pr0 == 2ULL) { h->probing = saved_prob; return 1ULL; }
  bool stop_early = full_prioritize_binaries_m6(h);
  u64 cand_n = full_backbone_sched_m6(h);
  h->ant_sz = tick_lim;
  u32 *units = (u32 *)h->work_stk2;
  u64 wm4 = m6_wm4_get(h);
  u64 comp = ((wm4 >> 2) & 0xFFFFULL) + 1ULL;
  m6_wm4_set(h, (wm4 & (~(0xFFFFULL << 2))) | ((comp & 0xFFFFULL) << 2));
  u64 max_rounds = (comp >= 10ULL) ? 1000ULL : (100ULL * comp);
  u64 res = 1ULL;
  u64 round = 0ULL;
  while (round < max_rounds && cand_n > 0ULL && h->ant_sz > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL) {
    cand_n = full_backbone_round_m6(h, cand_n, stop_early);
    bool r_inc = (h->res_sz & 0x8000000000000000ULL) != 0ULL;
    u64 ucnt = h->res_sz & 0x7FFFFFFFFFFFFFFFULL;
    if (ucnt > 0ULL) {
      u64 ui = 0ULL;
      while (ui < ucnt) {
        if (!full_add_unit(h, units[ui])) { res = 20ULL; break; }
        h->delayed_len = h->delayed_len + 1ULL;
        ui = ui + 1ULL;
      }
      if (res == 20ULL) { break; }
      u64 pr = full_propagate(h);
      if (pr == 1ULL) { res = 20ULL; break; }
      if (pr == 2ULL) { break; }
    }
    if (r_inc) { break; }
    round = round + 1ULL;
  }
  full_backbone_keep_m6(h, cand_n);
  h->probing = saved_prob;
  return res;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Backbone
