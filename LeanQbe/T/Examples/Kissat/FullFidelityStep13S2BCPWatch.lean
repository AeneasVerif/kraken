/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 13 Shard S2-A — BCP & Watch C0 (`FullFidelityStep13S2BCPWatch`)

Pure C0 layer (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, `<= 100` cols) for Shard `S2-A`
(`4` sig-preserving replacement functions from `step13_v2_frozen_direct.c`):
1. `full_watch_push_slow_m6` (`L1526-1604`): proactive `wlen > 262144` defrag trigger.
2. `full_watch_push_m6` (`L1606-1646`): `L6a` hoist (`wcap`, `wvec`, `wstk`, `(u32)sz + (u32)c`).
3. `full_propagate_ignore_hot` (`L3742-4029`): `bigbig` `jumpreasons`, `m6_wm4_get`,
   `m6_hdr_add_ticks` / `search_ticks`, delayed watch flushing without eager `l0/l1` swap.
4. `full_propagate_ignore` (`L4043-4330`): cold twin with identical C0 body.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S2BCPWatch "
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

#define FL_ACTIVE             1u
#define PH_GARB               0x00080000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern void full_wstack_defrag_m6(FullHdr *h);
extern u64  m6_wm4_get(FullHdr *h);
extern void m6_hdr_add_ticks(FullHdr *h, u64 ticks);
extern bool full_prop_flush_del_fid(FullHdr *h, u64 di);
extern bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 other, u32 cref);

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
  if ((h->wlen > 262144ULL || h->wlen * 4ULL >= h->wcap * 3ULL) &&
      h->wusable * 4ULL >= h->wlen * 3ULL) {
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
  u64 wcap = h->wcap;
  if (wlen != 0ULL &&
      ((wlen <= 262144ULL && wlen * 4ULL < wcap * 3ULL) ||
       h->wusable * 4ULL < wlen * 3ULL)) {
    u64 l2 = (u64)lit << 1;
    u32 *wvec = (u32 *)h->watch_vec;
    u32 *wstk = (u32 *)h->watch_stk;
    u64 off = (u64)wvec[l2];
    u64 sz = (u64)wvec[l2 + 1ULL];
    u64 end = off + sz;
    if (end > 0ULL) {
      if (end + c <= wlen && wstk[end] == 0xFFFFFFFFu &&
          (c == 1ULL || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        wvec[l2 + 1ULL] = (u32)sz + (u32)c;
        if (h->wusable >= c) { h->wusable = h->wusable - c; }
        return true;
      }
      if (end == wlen && c <= wcap - wlen) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        wvec[l2 + 1ULL] = (u32)sz + (u32)c;
        h->wlen = end + c;
        return true;
      }
    } else if (c <= wcap - wlen) {
      wstk[wlen] = w0;
      if (c == 2ULL) { wstk[wlen + 1ULL] = w1; }
      wvec[l2] = (u32)wlen;
      wvec[l2 + 1ULL] = (u32)c;
      h->wlen = wlen + c;
      return true;
    }
  }
  return full_watch_push_slow_m6(h, lit, w0, w1, (u32)c);
}

u64 full_propagate_ignore_hot(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u32 *del = (u32 *)h->delayed;
  u64 dlim = h->delayed_cap * 3ULL;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  bool bigbig = ((m6_wm4_get(h) & 2ULL) != 0ULL);
  u64 fuel = h->fuel;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    if (fuel == 0ULL) {
      h->fuel = 0ULL;
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
      else { h->search_ticks = h->search_ticks + ticks; }
      return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec[nl64];
    u64 sz = (u64)wvec[nl64 + 1ULL];
    if (sz == 0ULL) {
      ticks = ticks + 1ULL;
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u32 nl_lvl = lvl[not_lit >> 1];
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 di = 0ULL;
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
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = nl_lvl;
          if (nl_lvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            u32 jr__ = PW_BIN_FLAG | not_lit;
            if (bigbig) {
              u32 nr__ = rsns[not_lit >> 1];
              if (nr__ != 0xFFFFFFFFu && (nr__ & PW_BIN_FLAG) != 0u) { jr__ = nr__; }
            }
            rsns[bv64] = jr__;
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
          if (repl == not_lit) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[q] = other;
            wstk[q + 1ULL] = cref;
            q = q + 2ULL;
          } else if (di < dlim) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            del[di] = repl;
            del[di + 1ULL] = other;
            del[di + 2ULL] = cref;
            di = di + 3ULL;
          } else {
            ovf_rw = repl;
            ovf_other = other;
            ovf_cref = cref;
            ovf_ri = ri;
            ovf = true;
            break;
          }
          continue;
        }
        wstk[q] = w0;
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
        bool fok = true;
        if (di > 0ULL) {
          fok = full_prop_flush_del_fid(h, di);
          di = 0ULL;
        }
        bool pushed = false;
        if (fok) {
          pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        }
        u64 noff = (u64)wvec[nl64];
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
    wvec[nl64 + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (di > 0ULL) {
      if (!full_prop_flush_del_fid(h, di)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->fuel = fuel;
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
      else { h->search_ticks = h->search_ticks + ticks; }
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->fuel = fuel;
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
  else { h->search_ticks = h->search_ticks + ticks; }
  return 0ULL;
}

u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u32 *del = (u32 *)h->delayed;
  u64 dlim = h->delayed_cap * 3ULL;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  bool bigbig = ((m6_wm4_get(h) & 2ULL) != 0ULL);
  u64 fuel = h->fuel;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    if (fuel == 0ULL) {
      h->fuel = 0ULL;
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
      else { h->search_ticks = h->search_ticks + ticks; }
      return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec[nl64];
    u64 sz = (u64)wvec[nl64 + 1ULL];
    if (sz == 0ULL) {
      ticks = ticks + 1ULL;
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u32 nl_lvl = lvl[not_lit >> 1];
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 di = 0ULL;
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
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = nl_lvl;
          if (nl_lvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            u32 jr__ = PW_BIN_FLAG | not_lit;
            if (bigbig) {
              u32 nr__ = rsns[not_lit >> 1];
              if (nr__ != 0xFFFFFFFFu && (nr__ & PW_BIN_FLAG) != 0u) { jr__ = nr__; }
            }
            rsns[bv64] = jr__;
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
          if (repl == not_lit) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[q] = other;
            wstk[q + 1ULL] = cref;
            q = q + 2ULL;
          } else if (di < dlim) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            del[di] = repl;
            del[di + 1ULL] = other;
            del[di + 2ULL] = cref;
            di = di + 3ULL;
          } else {
            ovf_rw = repl;
            ovf_other = other;
            ovf_cref = cref;
            ovf_ri = ri;
            ovf = true;
            break;
          }
          continue;
        }
        wstk[q] = w0;
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
        bool fok = true;
        if (di > 0ULL) {
          fok = full_prop_flush_del_fid(h, di);
          di = 0ULL;
        }
        bool pushed = false;
        if (fok) {
          pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        }
        u64 noff = (u64)wvec[nl64];
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
    wvec[nl64 + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (di > 0ULL) {
      if (!full_prop_flush_del_fid(h, di)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->fuel = fuel;
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
      else { h->search_ticks = h->search_ticks + ticks; }
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->fuel = fuel;
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
  else { h->search_ticks = h->search_ticks + ticks; }
  return 0ULL;
}
"

/-! ## 1. `Fn` Handles, Replacements & Empty Insertion List -/

/-- Step-13 `full_watch_push_slow_m6` replacement (`wlen > 262144` defrag trigger). -/
def fidStep13S2WatchPushSlowM6Fn : Fn :=
  ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
    full_watch_push_slow_m6_body⟩

/-- Step-13 `full_watch_push_m6` replacement (`L6a` hoist). -/
def fidStep13S2WatchPushM6Fn : Fn :=
  ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
    full_watch_push_m6_body⟩

/-- Step-13 `full_propagate_ignore_hot` replacement (`jumpreasons`/`bigbig` + ticks). -/
def fidStep13S2PropIgnoreHotFn : Fn :=
  ⟨"full_propagate_ignore_hot", [i64, i64], [i64], full_propagate_ignore_hot_body⟩

/-- Step-13 `full_propagate_ignore` replacement (`jumpreasons`/`bigbig` + ticks). -/
def fidStep13S2PropIgnoreFn : Fn :=
  ⟨"full_propagate_ignore", [i64, i64], [i64], full_propagate_ignore_body⟩

/-- Ordered `4`-function Shard `S2-A` replacement list (`0` ABI changes). -/
def fidStep13S2BCPWatchRepls : List Fn :=
  [ fidStep13S2WatchPushSlowM6Fn
  , fidStep13S2WatchPushM6Fn
  , fidStep13S2PropIgnoreHotFn
  , fidStep13S2PropIgnoreFn ]

/-- Empty helper-insertion list for Shard `S2-A`. -/
def fidStep13S2BCPWatchBefores : List (Sym × List Fn) := []

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Twin Body Equality -/

public section

theorem full_propagate_ignore_body_eq_hot :
    full_propagate_ignore_body = full_propagate_ignore_hot_body :=
  rfl

theorem full_watch_push_slow_m6_s13_wf :
    Func.Wf fidStep13S2WatchPushSlowM6Fn.body := by t_wf_reify

theorem full_watch_push_m6_s13_wf :
    Func.Wf fidStep13S2WatchPushM6Fn.body := by t_wf_reify

theorem full_propagate_ignore_hot_s13_wf :
    Func.Wf fidStep13S2PropIgnoreHotFn.body := by t_wf_reify

theorem full_propagate_ignore_s13_wf :
    Func.Wf fidStep13S2PropIgnoreFn.body := by t_wf_reify

theorem fidStep13S2BCPWatchRepls_wf :
    ∀ f ∈ fidStep13S2BCPWatchRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S2BCPWatchRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_watch_push_slow_m6_s13_wf
  · exact full_watch_push_m6_s13_wf
  · exact full_propagate_ignore_hot_s13_wf
  · exact full_propagate_ignore_s13_wf

theorem fidStep13S2BCPWatchBefores_wf :
    ∀ h ∈ fidStep13S2BCPWatchBefores.flatMap Prod.snd, h.Wf := by
  intro _ hh
  simp [fidStep13S2BCPWatchBefores] at hh

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
