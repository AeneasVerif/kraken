/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M7` Shared Vivification & Focused-Tier Parity Module (`FullM7ParityVivTiers`)

Purely additive C0 replacement module shared by both Target A (`FullM7Fidelity`) and Target B
(`FullM7Plus`), fixing the `3` compounding vivification and focused-tier bugs with `0` new externs
and `0` `m7SpecTable` contract changes (`patchFns` / `spliceFns`-ready):

1. **`m6_hdr_sync_legacy_tiers`**: reads focused `e[M6W_TIER2]` instead of stable
   `e[M6W_TIER2 + 1ULL]`, matching `e[M6W_TIER1]` (`FullM6Hdr.m6HdrW2aSpec [] []`).
2. **`full_propagate_ignore_hot`** (also canonical handle `"full_propagate_ignore"`): deletes
   ONLY the `3` `if (rec_ph)` guards around `h->search_ticks += ticks` so probing BCP records real
   ticks while preserving phase-saving `if (rec_ph)` guards (`fullPropagateIgnoreSpec`).
3. **`full_vivify_tier_m6_hdr`**: drops the synthetic `spent` heuristic and gates directly on
   `h->search_ticks < tick_lim`, staying 100% over `FullMem` (`m6aVivifyTierSpec`).
4. **`full_vivify_m6_hdr`**: saves/restores `start = h->search_ticks`, merges `tier1 >= tier2`
   weights, and carries unused tick budgets saturatingly across tiers `1, 2, 3, 0`
   (`FullM6OrchAdapters.m6aVivifySpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7ParityVivTiers "
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

#define PH_GARB           0x00080000u
#define PW_BIN_FLAG       0x80000000u
#define PW_LIT_MASK       0x7FFFFFFFu
#define FL_ACTIVE         1u
#define M6_EXT_BYTES      2304ULL
#define M6W_TIER1         8ULL
#define M6W_TIER2         10ULL
#define M6_WM_PROBE_TICKS 0ULL

extern void m6_ext_ensure_init(FullHdr *h);
extern bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 w0, u32 cref);
extern bool full_prop_chrono_hot(FullHdr *h, u64 t0);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_viv_collect_m6(FullHdr *h, u64 tier_mode);
extern void full_viv_count_m6(FullHdr *h, u64 bn);
extern void full_viv_keys_m6(FullHdr *h, u64 bn);
extern void full_viv_sort_sched_m6(FullHdr *h, u64 bn);
extern u64 full_viv_clause_m6(FullHdr *h, u32 cref);
extern u64 full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);

void m6_hdr_sync_legacy_tiers(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 t1 = e[M6W_TIER1];
  u64 t2 = e[M6W_TIER2];
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1;
  h->tier2 = t2;
}

u64 full_propagate_ignore_hot(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    u64 fl_rem = h->fuel;
    if (fl_rem == 0ULL) {
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return 2ULL;
    }
    h->fuel = fl_rem - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u32 *wvec0 = (u32 *)h->watch_vec;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec0[nl64];
    u64 sz = (u64)wvec0[nl64 + 1ULL];
    if (sz == 0ULL) {
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u64 t0 = 0xFFFFFFFFFFFFFFFFULL;
    if (clvl != 0ULL && (u64)lit < nlits && (u64)lvl[lit >> 1] < clvl) {
      t0 = tend;
    }
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 brk = 0ULL;
    bool ovf = true;
    while (ovf) {
      ovf = false;
      u32 ovf_rw = 0u;
      u32 ovf_other = 0u;
      u32 ovf_cref = 0u;
      u64 ovf_ri = 0ULL;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          p = p + 1ULL;
          u32 blk = w0 & PW_LIT_MASK;
          i8 bv = vals[blk];
          wstk[q] = w0;
          q = q + 1ULL;
          if (bv > (i8)0) { continue; }
          if (bv < (i8)0) {
            brk = 1ULL;
            h->confl_type = 1ULL;
            h->confl_lit0 = (u64)not_lit;
            h->confl_lit1 = (u64)blk;
            break;
          }
          ticks = ticks + 1ULL;
          u32 alvl = lvl[not_lit >> 1];
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = alvl;
          if (alvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            rsns[bv64] = PW_BIN_FLAG | not_lit;
          }
          tpos[bv64] = (u32)tend;
          trl[tend] = blk;
          tend = tend + 1ULL;
          continue;
        }
        if ((u64)w0 < nlits && vals[w0] > (i8)0) {
          u32 cref0 = wstk[p + 1ULL];
          p = p + 2ULL;
          wstk[q] = w0;
          wstk[q + 1ULL] = cref0;
          q = q + 2ULL;
          continue;
        }
        u32 cref = wstk[p + 1ULL];
        p = p + 2ULL;
        ticks = ticks + 1ULL;
        u32 chdr = ar[cref];
        if ((chdr & PH_GARB) != 0u) { continue; }
        u64 cbase = (u64)cref + 3ULL;
        u32 l0 = ar[cbase];
        u32 l1 = ar[cbase + 1ULL];
        if (l0 != not_lit && l1 != not_lit) { continue; }
        u32 other = l0 ^ l1 ^ not_lit;
        if (l0 == not_lit) {
          ar[cbase] = other;
          ar[cbase + 1ULL] = not_lit;
        }
        i8 ov = vals[other];
        if (ov > (i8)0) {
          wstk[q] = other;
          wstk[q + 1ULL] = cref;
          q = q + 2ULL;
          continue;
        }
        u64 csz = (u64)ar[(u64)cref + 2ULL];
        u64 srch = (u64)ar[(u64)cref + 1ULL];
        if (srch < 2ULL || srch >= csz) { srch = 2ULL; }
        u64 ri = srch;
        u32 repl = 0u;
        bool found = false;
        while (ri < csz) {
          u32 cand = ar[cbase + ri];
          if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
          ri = ri + 1ULL;
        }
        if (!found) {
          ri = 2ULL;
          while (ri < srch) {
            u32 cand = ar[cbase + ri];
            if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
            ri = ri + 1ULL;
          }
        }
        if (found) {
          ticks = ticks + 1ULL;
          ar[(u64)cref + 1ULL] = (u32)ri;
          u32 rw = repl;
          if (rw == not_lit) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[q] = other;
            wstk[q + 1ULL] = cref;
            q = q + 2ULL;
          } else {
            u32 *wvec = (u32 *)h->watch_vec;
            u64 wcap = h->wcap;
            u64 wlen = h->wlen;
            u64 rw64 = (u64)rw << 1;
            u64 roff = (u64)wvec[rw64];
            u64 rsz = (u64)wvec[rw64 + 1ULL];
            if (rsz == 0ULL && wlen + 2ULL <= wcap) {
              ar[cbase] = other;
              ar[cbase + 1ULL] = repl;
              ar[cbase + ri] = not_lit;
              wvec[rw64] = (u32)wlen;
              wvec[rw64 + 1ULL] = 2u;
              wstk[wlen] = other;
              wstk[wlen + 1ULL] = cref;
              h->wlen = wlen + 2ULL;
            } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
              ar[cbase] = other;
              ar[cbase + 1ULL] = repl;
              ar[cbase + ri] = not_lit;
              wstk[wlen] = other;
              wstk[wlen + 1ULL] = cref;
              h->wlen = wlen + 2ULL;
              wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
            } else if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
                       wstk[roff + rsz] == 0xFFFFFFFFu &&
                       wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
              ar[cbase] = other;
              ar[cbase + 1ULL] = repl;
              ar[cbase + ri] = not_lit;
              wstk[roff + rsz] = other;
              wstk[roff + rsz + 1ULL] = cref;
              wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
              u64 wu = h->wusable;
              if (wu >= 2ULL) { h->wusable = wu - 2ULL; }
            } else {
              ovf_rw = rw;
              ovf_other = other;
              ovf_cref = cref;
              ovf_ri = ri;
              ovf = true;
              break;
            }
          }
          continue;
        }
        wstk[q] = other;
        wstk[q + 1ULL] = cref;
        q = q + 2ULL;
        if ((u64)cref == ignore_ref) { continue; }
        if (ov < (i8)0) {
          brk = 1ULL;
          h->confl_type = 2ULL;
          h->confl_ref = (u64)cref;
          break;
        }
        ticks = ticks + 1ULL;
        u32 nl_lvl = lvl[not_lit >> 1];
        u32 alvl = nl_lvl;
        if (nl_lvl < clvl32) {
          u32 mx = 0u;
          u64 bi = 0ULL;
          while (bi < csz) {
            u32 clit = ar[cbase + bi];
            if (clit != other) {
              u32 lv = lvl[clit >> 1];
              if (lv > mx) { mx = lv; }
            }
            bi = bi + 1ULL;
          }
          alvl = mx;
        }
        u64 ov64 = (u64)(other >> 1);
        vals[other] = (i8)1;
        vals[other ^ 1u] = (i8)(-1);
        if ((fl[ov64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
        if (rec_ph) {
          if ((other & 1u) != 0u) { ph[ov64] = (i8)(-1); }
          else { ph[ov64] = (i8)1; }
        }
        lvl[ov64] = alvl;
        if (alvl == 0u) {
          rsns[ov64] = 0xFFFFFFFFu;
          fl[ov64] = fl[ov64] & (~FL_ACTIVE);
          unfl = unfl + 1ULL;
        } else {
          rsns[ov64] = cref;
        }
        tpos[ov64] = (u32)tend;
        trl[tend] = other;
        tend = tend + 1ULL;
      }
      if (ovf) {
        bool pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        u32 *wvec2 = (u32 *)h->watch_vec;
        u64 noff = (u64)wvec2[(u64)not_lit << 1];
        if (noff != off) {
          q = noff + (q - off);
          p = noff + (p - off);
          end = noff + (end - off);
          off = noff;
        }
        if (!pushed) {
          wstk[q] = ovf_other;
          wstk[q + 1ULL] = ovf_cref;
          q = q + 2ULL;
          brk = 2ULL;
          break;
        }
        u64 obase = (u64)ovf_cref + 3ULL;
        ar[obase] = ovf_other;
        ar[obase + 1ULL] = ovf_rw;
        ar[obase + ovf_ri] = not_lit;
      }
    }
    while (p < end) {
      wstk[q] = wstk[p];
      q = q + 1ULL;
      p = p + 1ULL;
    }
    u32 *wvec1 = (u32 *)h->watch_vec;
    wvec1[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (brk != 2ULL && t0 < tend) {
      h->trail_end = tend;
      if (!full_prop_chrono_hot(h, t0)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  h->search_ticks = h->search_ticks + ticks;
  return 0ULL;
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL;
  u64 bn = full_viv_collect_m6(h, tier_mode);
  full_viv_count_m6(h, bn);
  full_viv_keys_m6(h, bn);
  full_viv_sort_sched_m6(h, bn);
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         h->search_ticks < tick_lim) {
    u32 cr = rr[bi * 3ULL];
    budget = budget - 1ULL;
    u64 vc = full_viv_clause_m6(h, cr);
    if (vc == 20ULL) { res = 20ULL; break; }
    if (vc == 2ULL) { break; }
    if (h->cur_level == 0ULL && full_propagate(h) == 1ULL) { res = 20ULL; break; }
    bi = bi + 1ULL;
  }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (res == 1ULL && bi >= bn && bn < bmax) {
    full_viv_clear_tier_m6(h, tier_mode);
  }
  h->probing = 0ULL;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  m6_hdr_sync_legacy_tiers(h);
  u64 start = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start > last_p) ? (start - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  u64 res = 1ULL;
  if (h->num_redundant == 0ULL) {
    u64 lim0 = (start > (~0ULL) - total) ? (~0ULL) : (start + total);
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim0);
    h->search_ticks = start;
    return res;
  }
  u64 w1 = 3ULL; u64 w2 = 3ULL; u64 w3 = 1ULL; u64 w0 = 3ULL;
  if (h->tier1 >= h->tier2) { w1 = w1 + w2; w2 = 0ULL; }
  u64 lim = start;
  u64 a1 = (total * w1) / 10ULL;
  lim = (lim > (~0ULL) - a1) ? (~0ULL) : (lim + a1);
  res = full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, lim);
  if (res != 20ULL && w2 > 0ULL) {
    u64 a2 = (total * w2) / 10ULL;
    lim = (lim > (~0ULL) - a2) ? (~0ULL) : (lim + a2);
    res = full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL) {
    u64 a3 = (total * w3) / 10ULL;
    lim = (lim > (~0ULL) - a3) ? (~0ULL) : (lim + a3);
    res = full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL) {
    u64 a0 = (total * w0) / 10ULL;
    lim = (lim > (~0ULL) - a0) ? (~0ULL) : (lim + a0);
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim);
  }
  h->search_ticks = start;
  return res;
}
"

/-- Function list of `FullM7ParityVivTiers` (`4` functions). -/
def m7ParityVivTiersFns : List Fn := m7ParityVivTiers_fns

/-- External callee signatures referenced by `m7ParityVivTiersFns` (`12` externs). -/
def m7ParityVivTiersExterns : List Extern :=
  [ ⟨"m6_ext_ensure_init", [i64], []⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64]⟩
  , ⟨"full_viv_count_m6", [i64, i64], []⟩
  , ⟨"full_viv_keys_m6", [i64, i64], []⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], []⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], []⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩ ]

/-- Standalone `FullM7ParityVivTiers` module (`4` fns, `12` externs, `0` exits). -/
def m7ParityVivTiersModule : LeanQbe.T.Module :=
  { fns := m7ParityVivTiersFns, externs := m7ParityVivTiersExterns, exits := [] }

/-- Canonical drop-in `Fn` handles matching `FullM7.m7Fns` slot names (`5` handles for
`patchFns` / `spliceFns`). -/
def m7pSyncLegacyTiersFn : Fn :=
  ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6_hdr_sync_legacy_tiers_body⟩
def m7pPropIgnoreHotFn : Fn :=
  ⟨"full_propagate_ignore_hot", [i64, i64], [i64], full_propagate_ignore_hot_body⟩
def m7pPropIgnoreFn : Fn :=
  ⟨"full_propagate_ignore", [i64, i64], [i64], full_propagate_ignore_hot_body⟩
def m7pVivifyTierFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩
def m7pVivifyFn : Fn :=
  ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_body⟩

/-- Canonical replacement list for `FullM7Splice.patchFns` / `spliceFns` on `FullM7.m7Fns`. -/
def m7ParityVivTiersPatchFns : List Fn :=
  [ m7pSyncLegacyTiersFn
  , m7pPropIgnoreHotFn
  , m7pPropIgnoreFn
  , m7pVivifyTierFn
  , m7pVivifyFn ]

theorem m6_hdr_sync_legacy_tiers_wf : Func.Wf m6_hdr_sync_legacy_tiers_body := by
  t_wf_reify

theorem full_propagate_ignore_hot_wf : Func.Wf full_propagate_ignore_hot_body := by
  t_wf_reify

theorem full_vivify_tier_m6_hdr_wf : Func.Wf full_vivify_tier_m6_hdr_body := by
  t_wf_reify

theorem full_vivify_m6_hdr_wf : Func.Wf full_vivify_m6_hdr_body := by
  t_wf_reify

theorem m7ParityVivTiers_fns_wf : ∀ f ∈ m7ParityVivTiersFns, f.Wf := by
  simp only [m7ParityVivTiersFns, m7ParityVivTiers_fns, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  exact ⟨m6_hdr_sync_legacy_tiers_wf, full_propagate_ignore_hot_wf,
    full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf⟩

theorem m7ParityVivTiersPatchFns_wf : ∀ r ∈ m7ParityVivTiersPatchFns, r.Wf := by
  simp only [m7ParityVivTiersPatchFns, m7pSyncLegacyTiersFn, m7pPropIgnoreHotFn,
    m7pPropIgnoreFn, m7pVivifyTierFn, m7pVivifyFn, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  exact ⟨m6_hdr_sync_legacy_tiers_wf, full_propagate_ignore_hot_wf,
    full_propagate_ignore_hot_wf, full_vivify_tier_m6_hdr_wf, full_vivify_m6_hdr_wf⟩

theorem m7ParityVivTiers_acyclic : m7ParityVivTiersModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
