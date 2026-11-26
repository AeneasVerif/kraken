/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Delayed-Watch BCP & Hot-Loop Base-Pointer Caching (`FullFidelityBcp`)

Purely additive C0 overrides (`0` edits to existing `FullM6*`/`FullM7*`/`FullM8*` modules)
closing upstream Kissat 4.0.4 `proplit.h:17-40` delayed-watch BCP and Layer-C2 C0 hot-loop
base-pointer caching gaps (zero beyond-upstream heuristics):

1. **Upstream `proplit.h:17-40` Delayed-Watch BCP (`full_prop_flush_del_fid`,
   `full_propagate_ignore_fid`)**:
   - Buffers 2WL large-clause replacement watches `(repl, other, cref)` into `h->delayed`
     (`3 * h->delayed_cap` `u32` words, 0 aliasing with `h->wsort`/`h->work_stk1`) during the
     watch scan and flushes them in a linear pass after compaction via `full_prop_flush_del_fid`
     (with cold mid-scan flush + slice rebase if `di >= dlim`, including `delayed_cap == 0`).
   - Hoists `wvec`, `del`, `dlim`, `fuel`, `nl_lvl`, `trail_end`, `unassigned`, `unflushed`
     out of inner/outer propagation loops while preserving unconditional `h->search_ticks += ticks`
     (`FullM7ParityVivTiers` parity).
2. **Bit-Identical Hot-Loop Base-Pointer Caching**:
   - `full_heap_down_fid` (`"full_heap_down"`), `full_heap_pop_fid` (`"full_heap_pop"`), and
     `full_next_dec_var_fid` (`"full_next_dec_var"`): hoist `nvars = h->cur_vars` and `sc[sv]`,
     cache `hlen = h->heap_len`, and split stable/focused array pointer loads to eliminate
     per-iteration `FullHdr` reloads and register spills.
   - `full_deduce_1uip_fid` (`"full_deduce_1uip_m6"`) and `full_deduce_1uip_hdr_fid`
     (`"full_deduce_1uip_m6_hdr"`): hoist `cv = h->cur_vars` and scalarize `tcnt = h->tmp_cnt`
     across unmarked trail steps, syncing `h->tmp_cnt` only on marked current-level literals.
   - `m6_hdr_decide_fid_fast` (`"m6_hdr_decide_fid"`): fast inline steady-state check on
     `e[M6W_MAGIC] == M6_HDR_MAGIC && (st >> 63) != 0ULL`, calling `m6_hdr_dr_init` only on the
     cold uninitialized path.
3. **Composition Descriptors**:
   Exports `extract_c0_direct.py`- and `PatchModule`-compatible `fidBcpRepls`/`fidBcpBefores`,
   `fidBcpHotPushRepls`/`fidBcpHotPushBefores` (with `FullM7HotWatchPush`), and
   `fidBcpHotPushMemRepls`/`fidBcpHotPushMemBefores` (with `FullM7HotWatchPush` +
   `FullM7MemShrinkV5`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fidBcp "
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

#define PH_GARB        0x00080000u
#define PW_BIN_FLAG    0x80000000u
#define PW_LIT_MASK    0x7FFFFFFFu
#define FL_ACTIVE      1u

#define M6_EXT_BYTES   2304ULL
#define M6_HDR_MAGIC   0x4D36484452455831ULL
#define M6W_MAGIC      0ULL
#define M6W_DR_STATE   1ULL

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64 full_heap_pop(FullHdr *h);
extern bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 w0, u32 cref);
extern bool full_prop_chrono_hot(FullHdr *h, u64 t0);
extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern bool full_analyze_rsn_m6_hdr(FullHdr *h, u32 rsn, u32 skip_var);
extern void full_clear_ana(FullHdr *h);
extern bool full_otfs_large(FullHdr *h, u32 cref, u32 uip);
extern bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip);
extern void full_otfs_subsume(
  FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin);
extern u64 full_decide_m7(FullHdr *h);
extern void m6_hdr_dr_init(FullHdr *h);

void full_heap_down_fid(FullHdr *h, u32 v) {
  u64 nvars = h->cur_vars;
  if ((u64)v >= nvars) { return; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 *sc = (u64 *)h->score;
  u32 p = ps[v];
  u64 hlen = h->heap_len;
  if ((u64)p >= hlen || hlen > nvars || hp[p] != v) { return; }
  u64 vsc = sc[v];
  while (true) {
    u64 cp = ((u64)p << 1) + 1ULL;
    if (cp >= hlen) { break; }
    u32 cv = hp[cp];
    if ((u64)cv >= nvars) { break; }
    u64 csc = sc[cv];
    u64 sp = cp + 1ULL;
    if (sp < hlen) {
      u32 sv = hp[sp];
      if ((u64)sv < nvars) {
        u64 ssc = sc[sv];
        if (ssc > csc) { cp = sp; cv = sv; csc = ssc; }
      }
    }
    if (csc <= vsc) { break; }
    hp[p] = cv;
    ps[cv] = p;
    p = (u32)cp;
  }
  hp[p] = v;
  ps[v] = p;
}

u64 full_heap_pop_fid(FullHdr *h) {
  u64 nvars = h->cur_vars;
  u64 hlen = h->heap_len;
  if (hlen == 0ULL || hlen > nvars) { return 0xFFFFFFFFULL; }
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 top = hp[0];
  u64 nlen = hlen - 1ULL;
  h->heap_len = nlen;
  u32 last = hp[nlen];
  if ((u64)top < nvars) { ps[top] = 0xFFFFFFFFu; }
  if (nlen > 0ULL && (u64)last < nvars) {
    hp[0] = last;
    ps[last] = 0u;
    full_heap_down(h, last);
  }
  if ((u64)top >= nvars) { return 0xFFFFFFFFULL; }
  return (u64)top;
}

bool full_prop_flush_del_fid(FullHdr *h, u64 di) {
  u32 *del = (u32 *)h->delayed;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 wlen = h->wlen;
  u64 wu = h->wusable;
  u64 j = 0ULL;
  while (j < di) {
    u32 rw = del[j];
    u32 ow = del[j + 1ULL];
    u32 cr = del[j + 2ULL];
    j = j + 3ULL;
    u64 rw64 = (u64)rw << 1;
    u64 roff = (u64)wvec[rw64];
    u64 rsz = (u64)wvec[rw64 + 1ULL];
    if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
        wstk[roff + rsz] == 0xFFFFFFFFu &&
        wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
      wstk[roff + rsz] = ow;
      wstk[roff + rsz + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      if (wu >= 2ULL) { wu = wu - 2ULL; }
    } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      wlen = wlen + 2ULL;
    } else if (rsz == 0ULL && wlen > 0ULL && wlen + 2ULL <= wcap) {
      wvec[rw64] = (u32)wlen;
      wvec[rw64 + 1ULL] = 2u;
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wlen = wlen + 2ULL;
    } else {
      h->wlen = wlen;
      h->wusable = wu;
      if (!full_watch_push(h, rw, ow, cr, 2u)) { return false; }
      wlen = h->wlen;
      wu = h->wusable;
    }
  }
  h->wlen = wlen;
  h->wusable = wu;
  return true;
}

u64 full_propagate_ignore_fid(FullHdr *h, u64 ignore_ref) {
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
      h->search_ticks = h->search_ticks + ticks;
      return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec[nl64];
    u64 sz = (u64)wvec[nl64 + 1ULL];
    if (sz == 0ULL) {
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
      h->search_ticks = h->search_ticks + ticks;
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->fuel = fuel;
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  h->search_ticks = h->search_ticks + ticks;
  return 0ULL;
}

u64 full_deduce_1uip_fid(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  u64 tcnt = h->tmp_cnt;
  if (!seed_ok || tcnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (tcnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= cv) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      tcnt = tcnt - 1ULL;
      h->tmp_cnt = tcnt;
      if (tcnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      tcnt = h->tmp_cnt;
      u64 rsz = h->res_sz;
      if (rsz > 0ULL) { rsz = rsz - 1ULL; h->res_sz = rsz; }
      u64 asz = h->ant_sz;
      if (asz >= 3ULL && rsz < asz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (asz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_deduce_1uip_hdr_fid(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn_m6_hdr(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  u64 tcnt = h->tmp_cnt;
  if (!seed_ok || tcnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (tcnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= cv) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      tcnt = tcnt - 1ULL;
      h->tmp_cnt = tcnt;
      if (tcnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn_m6_hdr(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      tcnt = h->tmp_cnt;
      u64 rsz = h->res_sz;
      if (rsz > 0ULL) { rsz = rsz - 1ULL; h->res_sz = rsz; }
      u64 asz = h->ant_sz;
      if (asz >= 3ULL && rsz < asz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (asz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}

u64 full_next_dec_var_fid(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars;
  if (h->stable != 0ULL) {
    u32 *hp = (u32 *)h->heap;
    u64 hlen = h->heap_len;
    while (hlen > 0ULL && hlen <= cv) {
      u32 top = hp[0];
      if ((u64)top >= cv) { break; }
      if ((fl[top] & FL_ACTIVE) != 0u && vals[(u64)top << 1] == (i8)0) { return (u64)top; }
      full_heap_pop(h);
      hlen = h->heap_len;
    }
  } else {
    u32 *qp = (u32 *)h->q_prev;
    u64 cur = h->q_search_idx;
    u64 steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        u32 *qs = (u32 *)h->q_stamp;
        h->q_search_idx = cur;
        h->q_search_stamp = (u64)qs[cur];
        return cur;
      }
      cur = (u64)qp[cur];
      steps = steps + 1ULL;
    }
    cur = h->q_last;
    steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        u32 *qs = (u32 *)h->q_stamp;
        h->q_search_idx = cur;
        h->q_search_stamp = (u64)qs[cur];
        return cur;
      }
      cur = (u64)qp[cur];
      steps = steps + 1ULL;
    }
  }
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) { return v; }
    v = v + 1ULL;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

u64 m6_hdr_decide_fid_fast(FullHdr *h) {
  if (full_decide_m7(h) == 0ULL) { return 0ULL; }
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  if (e[M6W_MAGIC] != M6_HDR_MAGIC || (st >> 63) == 0ULL) {
    m6_hdr_dr_init(h);
    st = e[M6W_DR_STATE];
  }
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 hi = st & (~mask56);
  u64 decs = st & mask56;
  if (decs < mask56) { e[M6W_DR_STATE] = hi | (decs + 1ULL); }
  return 1ULL;
}
"

/-! ## 1. Standalone Module, Canonical `Fn` Handles, & Composition Descriptors -/

/-- External callee signatures referenced by `fidBcp_fns` (`14` externs). -/
def fidBcpExterns : List Extern :=
  [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_heap_pop", [i64], [i64]⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool]⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool]⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], []⟩
  , ⟨"full_decide_m7", [i64], [i64]⟩
  , ⟨"m6_hdr_dr_init", [i64], []⟩ ]

/-- Standalone `8`-function module containing all `FullFidelityBcp` functions. -/
def fidBcpModule : LeanQbe.T.Module :=
  { fns := fidBcp_fns, externs := fidBcpExterns, exits := [] }

/-- Canonical `"full_heap_down"` override with cached `nvars = h->cur_vars` and `sc[sv]`. -/
def fidHeapDownFn : Fn :=
  ⟨"full_heap_down", [i64, i32], [], full_heap_down_fid_body⟩

/-- Canonical `"full_heap_pop"` override with cached `nvars = h->cur_vars` and `hlen`. -/
def fidHeapPopFn : Fn :=
  ⟨"full_heap_pop", [i64], [i64], full_heap_pop_fid_body⟩

/-- Linear delayed-watch flush helper inserted immediately before `"full_propagate_ignore_hot"`. -/
def fidPropFlushDelFn : Fn :=
  ⟨"full_prop_flush_del_fid", [i64, i64], [.bool], full_prop_flush_del_fid_body⟩

/-- Canonical `"full_propagate_ignore_hot"` override (delayed-watch BCP + hoisted scalars). -/
def fidPropagateIgnoreHotFn : Fn :=
  ⟨"full_propagate_ignore_hot", [i64, i64], [i64], full_propagate_ignore_fid_body⟩

/-- Canonical `"full_propagate_ignore"` override sharing `full_propagate_ignore_fid_body`. -/
def fidPropagateIgnoreFn : Fn :=
  ⟨"full_propagate_ignore", [i64, i64], [i64], full_propagate_ignore_fid_body⟩

/-- Canonical `"full_deduce_1uip_m6"` override with hoisted `cv` and scalarized `tcnt`. -/
def fidDeduce1uipM6Fn : Fn :=
  ⟨"full_deduce_1uip_m6", [i64], [i64], full_deduce_1uip_fid_body⟩

/-- Canonical `"full_deduce_1uip_m6_hdr"` override with hoisted `cv` and scalarized `tcnt`. -/
def fidDeduce1uipM6HdrFn : Fn :=
  ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], full_deduce_1uip_hdr_fid_body⟩

/-- Canonical `"full_next_dec_var"` override with split stable/focused pointer loads. -/
def fidNextDecVarFn : Fn :=
  ⟨"full_next_dec_var", [i64], [i64], full_next_dec_var_fid_body⟩

/-- Canonical `"m6_hdr_decide_fid"` override with fast inline steady-state magic check. -/
def fidHdrDecideFn : Fn :=
  ⟨"m6_hdr_decide_fid", [i64], [i64], m6_hdr_decide_fid_fast_body⟩

/-- `8` canonical replacements defined by `FullFidelityBcp`. -/
def fidBcpRepls : List Fn :=
  [ fidHeapDownFn
  , fidHeapPopFn
  , fidPropagateIgnoreHotFn
  , fidPropagateIgnoreFn
  , fidDeduce1uipM6Fn
  , fidDeduce1uipM6HdrFn
  , fidNextDecVarFn
  , fidHdrDecideFn ]

/-- Helper insertion placing `fidPropFlushDelFn` ahead of `"full_propagate_ignore_hot"`. -/
def fidBcpBefores : List (Sym × List Fn) :=
  [("full_propagate_ignore_hot", [fidPropFlushDelFn])]

/-- Composed `9` replacements combining `FullFidelityBcp` with `FullM7HotWatchPush`. -/
def fidBcpHotPushRepls : List Fn :=
  FullM7HotWatchPush.m7HotWatchPushRepl ++ fidBcpRepls

/-- Composed `2` helper anchors combining `FullM7HotWatchPush` and `FullFidelityBcp`. -/
def fidBcpHotPushBefores : List (Sym × List Fn) :=
  FullM7HotWatchPush.m7HotWatchPushBefore ++ fidBcpBefores

/-- Composed `21` disjoint canonical replacements combining `FullFidelityBcp`,
`FullM7HotWatchPush`, and `FullM7MemShrinkV5`. -/
def fidBcpHotPushMemRepls : List Fn :=
  FullM7MemShrinkV5.m7msRepls ++ fidBcpHotPushRepls

/-- Composed `4` helper anchors (`+4` helpers) combining `FullM7MemShrinkV5`,
`FullM7HotWatchPush`, and `FullFidelityBcp`. -/
def fidBcpHotPushMemBefores : List (Sym × List Fn) :=
  FullM7MemShrinkV5.m7msBefores ++ fidBcpHotPushBefores

/-! ## 2. Structural Well-Formedness, Acyclicity, & 4-ISA Codegen Guards -/

theorem full_heap_down_fid_wf : Func.Wf full_heap_down_fid_body := by t_wf_reify
theorem full_heap_pop_fid_wf : Func.Wf full_heap_pop_fid_body := by t_wf_reify
theorem full_prop_flush_del_fid_wf : Func.Wf full_prop_flush_del_fid_body := by t_wf_reify
theorem full_propagate_ignore_fid_wf : Func.Wf full_propagate_ignore_fid_body := by t_wf_reify
theorem full_deduce_1uip_fid_wf : Func.Wf full_deduce_1uip_fid_body := by t_wf_reify
theorem full_deduce_1uip_hdr_fid_wf : Func.Wf full_deduce_1uip_hdr_fid_body := by t_wf_reify
theorem full_next_dec_var_fid_wf : Func.Wf full_next_dec_var_fid_body := by t_wf_reify
theorem m6_hdr_decide_fid_fast_wf : Func.Wf m6_hdr_decide_fid_fast_body := by t_wf_reify

theorem fidBcp_fns_wf : ∀ f ∈ fidBcp_fns, f.Wf := by
  simp only [fidBcp_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_heap_down_fid_wf, full_heap_pop_fid_wf, full_prop_flush_del_fid_wf,
    full_propagate_ignore_fid_wf, full_deduce_1uip_fid_wf, full_deduce_1uip_hdr_fid_wf,
    full_next_dec_var_fid_wf, m6_hdr_decide_fid_fast_wf⟩

theorem fidBcpRepls_wf : ∀ f ∈ fidBcpRepls, f.Wf := by
  simp only [fidBcpRepls, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_heap_down_fid_wf, full_heap_pop_fid_wf, full_propagate_ignore_fid_wf,
    full_propagate_ignore_fid_wf, full_deduce_1uip_fid_wf, full_deduce_1uip_hdr_fid_wf,
    full_next_dec_var_fid_wf, m6_hdr_decide_fid_fast_wf⟩

theorem fidBcpBefores_wf : ∀ f ∈ fidBcpBefores.flatMap Prod.snd, f.Wf := by
  simp only [fidBcpBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact full_prop_flush_del_fid_wf

theorem fidBcpHotPushRepls_wf : ∀ f ∈ fidBcpHotPushRepls, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · simp only [FullM7HotWatchPush.m7HotWatchPushRepl, List.mem_singleton] at h1
    subst h1; exact FullM7HotWatchPush.m7WatchPushFastFn_wf
  · exact fidBcpRepls_wf f h2

theorem fidBcpHotPushBefores_wf : ∀ f ∈ fidBcpHotPushBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidBcpHotPushBefores, FullM7HotWatchPush.m7HotWatchPushBefore, fidBcpBefores,
    List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact FullM7HotWatchPush.m7WatchPushSlowFn_wf
  · exact full_prop_flush_del_fid_wf

theorem fidBcpHotPushMemRepls_wf : ∀ f ∈ fidBcpHotPushMemRepls, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact FullM7MemShrinkV5.m7msRepls_wf f h1
  · exact fidBcpHotPushRepls_wf f h2

theorem fidBcpHotPushMemBefores_wf : ∀ f ∈ fidBcpHotPushMemBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  rw [fidBcpHotPushMemBefores, List.flatMap_append] at hf
  rcases List.mem_append.mp hf with h1 | h2
  · rcases List.mem_flatMap.mp h1 with ⟨p, hp, hfp⟩
    exact FullM7MemShrinkV5.m7msBefores_wf p hp f hfp
  · exact fidBcpHotPushBefores_wf f h2

theorem fidBcp_acyclic : fidBcpModule.checkAcyclic = true := by t_kernel_rfl

#guard fidBcp_fns.length == 8
#guard fidBcpRepls.length == 8
#guard fidBcpHotPushRepls.length == 9
#guard fidBcpHotPushMemRepls.length == 21
#guard fidBcpModule.checkAcyclic == true

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
