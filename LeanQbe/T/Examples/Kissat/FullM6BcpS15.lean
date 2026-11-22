module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 `S1.5`: Single-Function In-Place Delayed-Watch BCP (`FullM6BcpS15`)

Single-function call-free hot-loop BCP preserving frozen `FullHdr` (`144` words) and landed
`RC-11` improvements (`vals[blk] > 0` checked before `PW_BIN_FLAG`, cache-line + propagation
ticks gated strictly on `h->probing == 0ULL`, dead-tail `0xFFFFFFFFu` sentinel fill):
1. Inline watch replacement in `full_prop_lit_raw_s15`: first attempts in-place sentinel-reuse
   (`wstk[rwend] == 0xFFFFFFFFu && wstk[rwend + 1] == 0xFFFFFFFFu`) or end-of-stack append
   (`rwend == wlen && 2 <= wcap - wlen`), and buffers only relocation misses in `h->delayed`
   (`di < 3 * h->delayed_cap`) using plain scalar locals (zero `nonblk` call, zero `u64` `qd`
   bitpacking, zero edits to `h->delayed_len`).
2. Post-loop compaction, dead-tail `0xFFFFFFFFu` tombstoning, and `h->delayed` flush via
   `full_watch_push` (preserving all watches on conflict and OOM exits).
3. Cold 6-argument overflow handler `full_prop_lit_ovf_s15` flushing `h->delayed` and finishing
   remaining watches `[pr..er)` when `di >= dlim` (including `delayed_cap == 0`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6BcpS15

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6BcpS15 "
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

#define PH_GARB 0x00080000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE 1u

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);

bool full_prop_lit_ovf_s15(
    FullHdr *h, u32 not_lit, u64 ignore_ref, u64 pr, u64 qr, u64 di) {
  u32 *del = (u32 *)h->delayed;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 er = (u64)wvec[((u64)not_lit << 1) + 1ULL];
  u64 j = 0ULL;
  while (j < di) {
    u32 rlit = del[j];
    u32 rw0 = del[j + 1ULL];
    u32 rcr = del[j + 2ULL];
    j = j + 3ULL;
    if (!full_watch_push(h, rlit, rw0, rcr, 2u)) {
      u64 off_f = (u64)wvec[(u64)not_lit << 1];
      u64 pf = off_f + pr; u64 qf = off_f + qr; u64 ef = off_f + er;
      while (pf < ef) { wstk[qf] = wstk[pf]; qf = qf + 1ULL; pf = pf + 1ULL; }
      u64 kf = qf;
      while (kf < ef) { wstk[kf] = 0xFFFFFFFFu; kf = kf + 1ULL; }
      wvec[((u64)not_lit << 1) + 1ULL] = (u32)(qf - off_f);
      h->wusable = h->wusable + (ef - qf);
      h->oom = 1ULL;
      return false;
    }
  }
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u64 off = (u64)wvec[(u64)not_lit << 1];
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u64 max_v = h->max_vars;
  u64 alen = h->arena_len;
  u64 tend = h->trail_end;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u32 cur_lvl = (u32)h->cur_level;
  u32 nl_lvl = lvl[not_lit >> 1];
  bool rec_ph = (h->probing == 0ULL);
  u64 ticks = 0ULL;
  u64 p = off + pr;
  u64 q = off + qr;
  u64 end = off + er;
  bool confl = false;
  u32 bin_rsn = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      if ((w0 & PW_BIN_FLAG) != 0u) {
        wstk[q] = w0; q = q + 1ULL; continue;
      }
      if (p < end) {
        u32 cref = wstk[p]; p = p + 1ULL;
        wstk[q] = w0; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
      }
      break;
    }
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
      if ((u64)blk >= nlits) { continue; }
      i8 ov = vals[blk];
      if (ov < (i8)0) {
        h->confl_type = 1ULL; h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)blk; h->confl_ref = 0xFFFFFFFFULL;
        confl = true; break;
      }
      ticks = ticks + 1ULL;
      if (tend < max_v) {
        u32 ov_v = blk >> 1;
        vals[blk] = (i8)1; vals[blk ^ 1u] = (i8)(-1);
        if ((fl[ov_v] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
        if (rec_ph) { ph[ov_v] = ((blk & 1u) != 0u) ? (i8)(-1) : (i8)1; }
        lvl[ov_v] = nl_lvl;
        if (nl_lvl == 0u) {
          rsns[ov_v] = 0xFFFFFFFFu; fl[ov_v] = fl[ov_v] & (~FL_ACTIVE);
          unfl = unfl + 1ULL;
        } else { rsns[ov_v] = bin_rsn; }
        tpos[ov_v] = (u32)tend; trl[tend] = blk; tend = tend + 1ULL;
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cref = wstk[p]; p = p + 1ULL;
    if ((u64)cref + 3ULL > alen) { continue; }
    ticks = ticks + 1ULL;
    u32 hdr = ar[cref]; u32 csz = ar[(u64)cref + 2ULL];
    u64 cbase = (u64)cref + 3ULL;
    if ((hdr & PH_GARB) != 0u || csz < 3u || cbase + (u64)csz > alen) { continue; }
    u32 l0 = ar[cbase]; u32 l1 = ar[cbase + 1ULL];
    if (l0 == not_lit) { ar[cbase] = l1; ar[cbase + 1ULL] = not_lit; l0 = l1; }
    else if (l1 != not_lit) { continue; }
    u32 other = l0;
    if ((u64)other >= nlits) { continue; }
    i8 ov = vals[other];
    if (ov > (i8)0) {
      wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
    }
    u32 srch = ar[(u64)cref + 1ULL];
    if (srch < 2u || srch >= csz) { srch = 2u; }
    u32 ri = 0xFFFFFFFFu; u32 repl = 0u; u32 r = srch;
    while (r < csz) {
      u32 cand = ar[cbase + (u64)r];
      if ((u64)cand < nlits && vals[cand] >= (i8)0) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) {
      r = 2u;
      while (r < srch) {
        u32 cand = ar[cbase + (u64)r];
        if ((u64)cand < nlits && vals[cand] >= (i8)0) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
    }
    if (ri != 0xFFFFFFFFu) {
      ticks = ticks + 1ULL;
      ar[(u64)cref + 1ULL] = ri;
      ar[cbase + 1ULL] = repl; ar[cbase + (u64)ri] = not_lit;
      u64 pr2 = p - off; u64 qr2 = q - off; u64 er2 = end - off;
      bool pok = full_watch_push(h, repl, other & PW_LIT_MASK, cref, 2u);
      off = (u64)wvec[(u64)not_lit << 1]; p = off + pr2; q = off + qr2; end = off + er2;
      if (!pok) {
        ar[cbase + 1ULL] = not_lit; ar[cbase + (u64)ri] = repl;
        wstk[q] = w0; wstk[q + 1ULL] = cref; q = q + 2ULL;
        h->oom = 1ULL; confl = true; break;
      }
      continue;
    }
    wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL;
    if ((u64)cref == ignore_ref) { continue; }
    if (ov < (i8)0) {
      h->confl_type = 2ULL; h->confl_ref = (u64)cref; confl = true; break;
    }
    ticks = ticks + 1ULL;
    u32 alvl = nl_lvl;
    if (nl_lvl < cur_lvl) {
      alvl = 0u; u32 li = 0u;
      while (li < csz) {
        u32 clit = ar[cbase + (u64)li];
        if (clit != other) {
          u32 clv = lvl[clit >> 1];
          if (clv > alvl) { alvl = clv; }
        }
        li = li + 1u;
      }
    }
    if (tend < max_v) {
      u32 ov_v = other >> 1;
      vals[other] = (i8)1; vals[other ^ 1u] = (i8)(-1);
      if ((fl[ov_v] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
      if (rec_ph) { ph[ov_v] = ((other & 1u) != 0u) ? (i8)(-1) : (i8)1; }
      lvl[ov_v] = alvl;
      if (alvl == 0u) {
        rsns[ov_v] = 0xFFFFFFFFu; fl[ov_v] = fl[ov_v] & (~FL_ACTIVE);
        unfl = unfl + 1ULL;
      } else { rsns[ov_v] = cref; }
      tpos[ov_v] = (u32)tend; trl[tend] = other; tend = tend + 1ULL;
    }
  }
  while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  h->trail_end = tend; h->unassigned = unass; h->unflushed = unfl;
  if (h->probing == 0ULL) { h->search_ticks = h->search_ticks + ticks; }
  return !confl;
}

bool full_prop_lit_raw_s15(FullHdr *h, u32 lit, u64 ignore_ref) {
  u32 not_lit = lit ^ 1u;
  u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)not_lit << 1];
  u64 sz = (u64)wvec[((u64)not_lit << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u32 *ar = (u32 *)h->arena;
  u32 *del = (u32 *)h->delayed;
  u64 dlim = h->delayed_cap * 3ULL;
  u64 wcap = h->wcap;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u64 max_v = h->max_vars;
  u64 alen = h->arena_len;
  u64 tend = h->trail_end;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u32 cur_lvl = (u32)h->cur_level;
  u32 nl_lvl = lvl[not_lit >> 1];
  bool rec_ph = (h->probing == 0ULL);
  u64 ticks = 1ULL + ((sz + 31ULL) >> 5);
  u64 p = off;
  u64 q = off;
  u64 end = off + sz;
  u64 di = 0ULL;
  bool confl = false;
  bool ovf = false;
  u32 bin_rsn = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      if ((w0 & PW_BIN_FLAG) != 0u) {
        wstk[q] = w0; q = q + 1ULL; continue;
      }
      if (p < end) {
        u32 cref = wstk[p]; p = p + 1ULL;
        wstk[q] = w0; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
      }
      break;
    }
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
      if ((u64)blk >= nlits) { continue; }
      i8 ov = vals[blk];
      if (ov < (i8)0) {
        h->confl_type = 1ULL; h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)blk; h->confl_ref = 0xFFFFFFFFULL;
        confl = true; break;
      }
      ticks = ticks + 1ULL;
      if (tend < max_v) {
        u32 ov_v = blk >> 1;
        vals[blk] = (i8)1; vals[blk ^ 1u] = (i8)(-1);
        if ((fl[ov_v] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
        if (rec_ph) { ph[ov_v] = ((blk & 1u) != 0u) ? (i8)(-1) : (i8)1; }
        lvl[ov_v] = nl_lvl;
        if (nl_lvl == 0u) {
          rsns[ov_v] = 0xFFFFFFFFu; fl[ov_v] = fl[ov_v] & (~FL_ACTIVE);
          unfl = unfl + 1ULL;
        } else { rsns[ov_v] = bin_rsn; }
        tpos[ov_v] = (u32)tend; trl[tend] = blk; tend = tend + 1ULL;
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cref = wstk[p]; p = p + 1ULL;
    if ((u64)cref + 3ULL > alen) { continue; }
    ticks = ticks + 1ULL;
    u32 hdr = ar[cref]; u32 csz = ar[(u64)cref + 2ULL];
    u64 cbase = (u64)cref + 3ULL;
    if ((hdr & PH_GARB) != 0u || csz < 3u || cbase + (u64)csz > alen) { continue; }
    u32 l0 = ar[cbase]; u32 l1 = ar[cbase + 1ULL];
    if (l0 == not_lit) { ar[cbase] = l1; ar[cbase + 1ULL] = not_lit; l0 = l1; }
    else if (l1 != not_lit) { continue; }
    u32 other = l0;
    if ((u64)other >= nlits) { continue; }
    i8 ov = vals[other];
    if (ov > (i8)0) {
      wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL; continue;
    }
    u32 srch = ar[(u64)cref + 1ULL];
    if (srch < 2u || srch >= csz) { srch = 2u; }
    u32 ri = 0xFFFFFFFFu; u32 repl = 0u; u32 r = srch;
    while (r < csz) {
      u32 cand = ar[cbase + (u64)r];
      if ((u64)cand < nlits && vals[cand] >= (i8)0) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) {
      r = 2u;
      while (r < srch) {
        u32 cand = ar[cbase + (u64)r];
        if ((u64)cand < nlits && vals[cand] >= (i8)0) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
    }
    if (ri != 0xFFFFFFFFu) {
      u64 roff = (u64)wvec[(u64)repl << 1];
      u64 rsz = (u64)wvec[((u64)repl << 1) + 1ULL];
      u64 rwend = roff + rsz;
      u64 wlen = h->wlen;
      if (roff > 0ULL && rwend + 2ULL <= wlen &&
          wstk[rwend] == 0xFFFFFFFFu && wstk[rwend + 1ULL] == 0xFFFFFFFFu) {
        ticks = ticks + 1ULL;
        ar[(u64)cref + 1ULL] = ri;
        ar[cbase + 1ULL] = repl; ar[cbase + (u64)ri] = not_lit;
        wstk[rwend] = other & PW_LIT_MASK; wstk[rwend + 1ULL] = cref;
        wvec[((u64)repl << 1) + 1ULL] = (u32)(rsz + 2ULL);
        if (h->wusable >= 2ULL) { h->wusable = h->wusable - 2ULL; }
        continue;
      }
      if (roff > 0ULL && rwend == wlen && 2ULL <= wcap - wlen) {
        ticks = ticks + 1ULL;
        ar[(u64)cref + 1ULL] = ri;
        ar[cbase + 1ULL] = repl; ar[cbase + (u64)ri] = not_lit;
        wstk[rwend] = other & PW_LIT_MASK; wstk[rwend + 1ULL] = cref;
        wvec[((u64)repl << 1) + 1ULL] = (u32)(rsz + 2ULL);
        h->wlen = rwend + 2ULL;
        continue;
      }
      if (di < dlim) {
        ticks = ticks + 1ULL;
        ar[(u64)cref + 1ULL] = ri;
        ar[cbase + 1ULL] = repl; ar[cbase + (u64)ri] = not_lit;
        del[di] = repl; del[di + 1ULL] = other & PW_LIT_MASK; del[di + 2ULL] = cref;
        di = di + 3ULL;
        continue;
      }
      p = p - 2ULL;
      ticks = ticks - 1ULL;
      ovf = true;
      break;
    }
    wstk[q] = other & PW_LIT_MASK; wstk[q + 1ULL] = cref; q = q + 2ULL;
    if ((u64)cref == ignore_ref) { continue; }
    if (ov < (i8)0) {
      h->confl_type = 2ULL; h->confl_ref = (u64)cref; confl = true; break;
    }
    ticks = ticks + 1ULL;
    u32 alvl = nl_lvl;
    if (nl_lvl < cur_lvl) {
      alvl = 0u; u32 li = 0u;
      while (li < csz) {
        u32 clit = ar[cbase + (u64)li];
        if (clit != other) {
          u32 clv = lvl[clit >> 1];
          if (clv > alvl) { alvl = clv; }
        }
        li = li + 1u;
      }
    }
    if (tend < max_v) {
      u32 ov_v = other >> 1;
      vals[other] = (i8)1; vals[other ^ 1u] = (i8)(-1);
      if ((fl[ov_v] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
      if (rec_ph) { ph[ov_v] = ((other & 1u) != 0u) ? (i8)(-1) : (i8)1; }
      lvl[ov_v] = alvl;
      if (alvl == 0u) {
        rsns[ov_v] = 0xFFFFFFFFu; fl[ov_v] = fl[ov_v] & (~FL_ACTIVE);
        unfl = unfl + 1ULL;
      } else { rsns[ov_v] = cref; }
      tpos[ov_v] = (u32)tend; trl[tend] = other; tend = tend + 1ULL;
    }
  }
  h->trail_end = tend; h->unassigned = unass; h->unflushed = unfl;
  if (h->probing == 0ULL) { h->search_ticks = h->search_ticks + ticks; }
  if (ovf) {
    return full_prop_lit_ovf_s15(h, not_lit, ignore_ref, p - off, q - off, di);
  }
  while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  if (di > 0ULL) {
    u64 j = 0ULL;
    while (j < di) {
      u32 rlit = del[j];
      u32 rw0 = del[j + 1ULL];
      u32 rcr = del[j + 2ULL];
      j = j + 3ULL;
      if (!full_watch_push(h, rlit, rw0, rcr, 2u)) {
        h->oom = 1ULL; confl = true; break;
      }
    }
  }
  return !confl;
}

u64 full_propagate_ignore_s15(FullHdr *h, u64 ignore_ref) {
  u32 *trl = (u32 *)h->trail;
  u64 prop = h->propagated;
  u64 fuel = h->fuel;
  while (prop < h->trail_end) {
    if (h->oom != 0ULL || fuel == 0ULL) {
      h->propagated = prop; h->fuel = fuel; return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    prop = prop + 1ULL;
    h->propagated = prop;
    if (!full_prop_lit_raw_s15(h, lit, ignore_ref)) {
      h->fuel = fuel;
      return (h->oom != 0ULL) ? 2ULL : 1ULL;
    }
  }
  h->propagated = prop; h->fuel = fuel;
  return 0ULL;
}

u64 full_bcp_s15(FullHdr *h) {
  return full_propagate_ignore_s15(h, 0xFFFFFFFFULL);
}
"

/-- External callee signatures referenced by `m6BcpS15_fns`. -/
def m6BcpS15Externs : List Extern :=
  [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩ ]

def m6BcpS15Module : LeanQbe.T.Module :=
  { fns := m6BcpS15_fns, externs := m6BcpS15Externs, exits := [] }

theorem full_prop_lit_ovf_s15_wf : Func.Wf full_prop_lit_ovf_s15_body := by t_wf_reify
theorem full_prop_lit_raw_s15_wf : Func.Wf full_prop_lit_raw_s15_body := by t_wf_reify
theorem full_propagate_ignore_s15_wf : Func.Wf full_propagate_ignore_s15_body := by t_wf_reify
theorem full_bcp_s15_wf : Func.Wf full_bcp_s15_body := by t_wf_reify

theorem m6BcpS15_fns_wf : ∀ f ∈ m6BcpS15_fns, f.Wf := by
  simp only [m6BcpS15_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_prop_lit_ovf_s15_wf, full_prop_lit_raw_s15_wf,
    full_propagate_ignore_s15_wf, full_bcp_s15_wf⟩

theorem m6BcpS15_acyclic : m6BcpS15Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6BcpS15
