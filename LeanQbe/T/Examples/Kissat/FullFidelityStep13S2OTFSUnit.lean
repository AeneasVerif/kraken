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
# Kissat Fidelity Step 13 Shard S2-B — OTFS, Unit Learn & Warmup BCP
(`FullFidelityStep13S2OTFSUnit`)

Pure C0 layer (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, `<= 100` cols) for Shard `S2-B`
(`2` ADD + `4` MOD functions verbatim from `step13_v2_frozen_direct.c`):
1. **ADD `full_update_classify_fid` (`L439-449`, non-static):** updates `watermarks[4]` bit 1
   (`bigbig` binary-heavy threshold) via `m6_wm4_get` / `m6_wm4_set`.
2. **MOD `full_otfs_large` (`L6208-6297`):** tightens redundant glue on OTFS shrink and marks
   irred literals `flags |= 24u`.
3. **MOD `full_one_lit_confl` (`L7415-7493`):** binary `jumpreasons` on `confl_type == 1`.
4. **MOD `full_eager_subsume` (`L7499-7562`):** decrements `h->num_redundant` on subsumed clauses.
5. **MOD `full_learn_clause_m6` (`L7954-8025`):** unit `full_det_new_level`/`iterating`/`eager`,
   dropped `tlen > 2` reverse block, binary `jumpreasons`.
6. **ADD `full_propagate_beyond_m7` (`L8855-9132`):** warmup propagation without conflict break.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S2OTFSUnit "
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
#define PH_RED                0x00400000u
#define PH_SHRK               0x00800000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern u64  m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);
extern void m6_hdr_add_ticks(FullHdr *h, u64 ticks);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_backtrack_ac_fid(FullHdr *h, u64 target_lvl);
extern u64  full_det_new_level(FullHdr *h, u64 jump);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64  full_reduce_m6(FullHdr *h, bool force);
extern u64  full_reduce_purge_c0(FullHdr *h);
extern u64  full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern bool full_prop_flush_del_fid(FullHdr *h, u64 di);
extern bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 other, u32 cref);

void full_update_classify_fid(FullHdr *h) {
  u64 clauses = h->num_binary + h->num_irred;
  bool bigbig = false;
  if (clauses > 100000ULL && (h->num_binary * 100000ULL >= clauses * 990ULL)) {
    bigbig = true;
  }
  u64 wm4 = m6_wm4_get(h);
  if (bigbig) { wm4 = wm4 | 2ULL; }
  else { wm4 = wm4 & (~2ULL); }
  m6_wm4_set(h, wm4);
}

bool full_otfs_large(FullHdr *h, u32 cref, u32 uip) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u64 cb = (u64)cref + 3ULL;
  u32 l0 = ar[cb]; u32 l1 = ar[cb + 1ULL];
  if (l0 == uip) { l0 = l1; }
  else if (l1 != uip) { return false; }
  u32 old_sz = ar[(u64)cref + 2ULL];
  u32 cnt = 1u; u32 i = 2u;
  while (i < old_sz) {
    if (lvl[ar[cb + (u64)i] >> 1] > 0u) {
      cnt = cnt + 1u;
      if (cnt >= 3u) { break; }
    }
    i = i + 1u;
  }
  if (cnt < 3u) { return false; }
  u32 hl_pre = 0u; u32 nl1_pre = uip;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > hl_pre) { hl_pre = cl; nl1_pre = ot; }
    i = i + 1u;
  }
  if (h->wcap - h->wlen < 2ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
  }
  if (!full_watch_push(h, nl1_pre, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL; return false;
  }
  ar[cb] = l0; ar[cb + 1ULL] = uip;
  full_unwatch_large(h, uip, cref);
  u32 new_sz = 1u; u32 hp = 1u; u32 hl = 0u;
  i = 2u;
  while (i < old_sz) {
    u32 ot = ar[cb + (u64)i];
    u32 cl = lvl[ot >> 1];
    if (cl > 0u) {
      ar[cb + (u64)new_sz] = ot;
      if (cl > hl) { hl = cl; hp = new_sz; }
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  u32 hdr = ar[cref];
  ar[(u64)cref + 2ULL] = new_sz; ar[(u64)cref + 1ULL] = 2u;
  if ((hdr & 0x00400000u) != 0u) {
    if ((hdr & 0x7FFFFu) >= new_sz) {
      hdr = (hdr & (~0x7FFFFu)) | (new_sz - 1u);
      ar[cref] = hdr;
    }
  } else {
    u32 *fl_ot = (u32 *)h->flags;
    fl_ot[uip >> 1] = fl_ot[uip >> 1] | 24u;
    u32 oi_ot = 0u;
    while (oi_ot < new_sz) {
      u32 ol_ot = ar[cb + (u64)oi_ot];
      fl_ot[ol_ot >> 1] = fl_ot[ol_ot >> 1] | 24u;
      oi_ot = oi_ot + 1u;
    }
  }
  if ((hdr & PH_SHRK) == 0u) {
    ar[cref] = hdr | PH_SHRK;
    ar[cb + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
  }
  if (hp != 1u) {
    u32 t = ar[cb + 1ULL]; ar[cb + 1ULL] = ar[cb + (u64)hp];
    ar[cb + (u64)hp] = t;
  }
  u32 nl1 = ar[cb + 1ULL];
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  if ((cref & PW_BIN_FLAG) == 0u) {
    u64 off = (u64)wvec[(u64)l0 << 1];
    u64 sz = (u64)wvec[((u64)l0 << 1) + 1ULL];
    if (sz >= 2ULL) {
      u64 p = off + sz;
      u64 off2 = off + 2ULL;
      while (p >= off2) {
        u32 w = wstk[p - 1ULL];
        if (w == cref) { wstk[p - 2ULL] = nl1 & PW_LIT_MASK; break; }
        p = p - 2ULL + (u64)(w >> 31);
      }
    }
  }
  h->otfs_cnt = h->otfs_cnt + 1ULL;
  return true;
}

u64 full_one_lit_confl(FullHdr *h) {
  u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena;
  if (h->confl_type == 1ULL) {
    u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
    u32 la = lvl[a >> 1]; u32 lb = lvl[b >> 1];
    u64 clvl = (la >= lb) ? (u64)la : (u64)lb;
    if (clvl == 0ULL) { return 20ULL; }
    if (clvl < h->cur_level) { full_backtrack_ac_fid(h, clvl); }
    if (la == lb) { return 0ULL; }
    u32 forced = (la > lb) ? a : b;
    u32 other = (la > lb) ? b : a;
    u64 jlvl = (la > lb) ? (u64)lb : (u64)la;
    u64 nlvl = full_det_new_level(h, jlvl);
    full_backtrack_ac_fid(h, nlvl);
    u32 jr_ol = (other & PW_LIT_MASK) | PW_BIN_FLAG;
    if (jlvl > 0ULL) {
      u32 *rsns_ol = (u32 *)h->reason;
      u32 nr_ol = rsns_ol[other >> 1];
      if (nr_ol != 0xFFFFFFFFu && (nr_ol & PW_BIN_FLAG) != 0u) { jr_ol = nr_ol; }
    }
    full_assign_lvl(h, forced, jr_ol, (u32)jlvl);
    return 1ULL;
  }
  u32 cref = (u32)h->confl_ref;
  if ((u64)cref + 3ULL > h->arena_len) { return 2ULL; }
  u32 csz = ar[(u64)cref + 2ULL];
  u64 clvl = 0ULL; u64 jlvl = 0ULL; u64 cnt = 0ULL; u32 forced = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < csz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u64 ll = (u64)lvl[l >> 1];
    if (cnt == 0ULL || ll > clvl) {
      jlvl = (cnt == 0ULL) ? 0ULL : clvl; clvl = ll; cnt = 1ULL; forced = l;
    } else if (ll == clvl) {
      if (clvl > jlvl) { jlvl = ll; } cnt = cnt + 1ULL;
    } else if (ll > jlvl) { jlvl = ll; }
    i = i + 1u;
  }
  if (clvl == 0ULL) { return 20ULL; }
  if (clvl < h->cur_level) { full_backtrack_ac_fid(h, clvl); }
  u32 pos = 0u;
  while (pos < 2u) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)pos];
    u32 hl = lvl[lit >> 1];
    u32 hp = pos;
    u32 j = pos + 1u;
    while (j < csz) {
      u32 cand = ar[(u64)cref + 3ULL + (u64)j];
      u32 cl = lvl[cand >> 1];
      if (cl > hl) { hl = cl; hp = j; }
      j = j + 1u;
    }
    if (hp != pos) {
      u32 high_lit = ar[(u64)cref + 3ULL + (u64)hp];
      if (hp > 1u) {
        u32 other = ar[(u64)cref + 3ULL + (u64)(pos ^ 1u)];
        if (h->wcap - h->wlen < 2ULL) {
          if (h->wusable > 0ULL) { full_wstack_defrag(h); }
          if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return 2ULL; }
        }
        if (!full_watch_push(h, high_lit, other & PW_LIT_MASK, cref, 2u)) {
          h->oom = 1ULL; return 2ULL;
        }
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
        full_unwatch_large(h, lit, cref);
      } else {
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
      }
    }
    pos = pos + 1u;
  }
  if (cnt > 1ULL) { return 0ULL; }
  u64 nlvl = full_det_new_level(h, jlvl);
  full_backtrack_ac_fid(h, nlvl);
  full_assign_lvl(h, forced, cref, (u32)jlvl);
  return 1ULL;
}

void full_eager_subsume(FullHdr *h, u64 new_ref) {
  u8 *lm = (u8 *)h->lit_mark;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *ll = (u32 *)h->last_learned;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u64 tlen = h->tmp_len;
  u64 i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)1; i = i + 1ULL; }
  bool subsumed = false;
  i = 0ULL;
  while (i < 4ULL) {
    u32 cr = ll[i];
    if (cr != 0xFFFFFFFFu && (u64)cr + 3ULL <= h->arena_len) {
      u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
      if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) != 0u && (u64)csz > tlen &&
          (u64)cr + 3ULL + (u64)csz <= h->arena_len) {
        u64 need = tlen; u64 rem = (u64)csz; u32 j = 0u;
        while (j < csz) {
          if (lm[ar[(u64)cr + 3ULL + (u64)j]] != (u8)0) {
            need = need - 1ULL; if (need == 0ULL) { break; }
          } else { rem = rem - 1ULL; if (rem < need) { break; } }
          j = j + 1u;
        }
        if (need == 0ULL) {
          bool act = false; u32 rj = 0u;
          while (rj < csz) {
            u32 rl = ar[(u64)cr + 3ULL + (u64)rj];
            if ((u64)rl < (h->cur_vars << 1) && vals[rl] > (i8)0 &&
                lvl[rl >> 1] > 0u && rsns[rl >> 1] == cr) { act = true; break; }
            rj = rj + 1u;
          }
          if (!act) {
            ar[cr] = hdr | PH_GARB;
            h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
            if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
            ll[i] = 0xFFFFFFFFu;
            h->eager_sub_cnt = h->eager_sub_cnt + 1ULL;
            subsumed = true;
          }
        }
      }
    }
    i = i + 1ULL;
  }
  i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)0; i = i + 1ULL; }
  if (subsumed) {
    u64 q = 0ULL; u64 p = 0ULL;
    while (p < 4ULL) {
      u32 cr = ll[p];
      if (cr != 0xFFFFFFFFu) { ll[q] = cr; q = q + 1ULL; }
      p = p + 1ULL;
    }
    while (q < 4ULL) { ll[q] = 0xFFFFFFFFu; q = q + 1ULL; }
  }
  if (new_ref < 0x80000000ULL) {
    u64 k = 3ULL;
    while (k > 0ULL) { ll[k] = ll[k - 1ULL]; k = k - 1ULL; }
    ll[0] = (u32)new_ref;
  }
}

u64 full_learn_clause_m6(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    u64 nlvl_u = full_det_new_level(h, 0ULL);
    full_backtrack_ac_fid(h, nlvl_u);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    if (h->probing == 0ULL) { h->iterating = 1ULL; }
    full_eager_subsume(h, 0xFFFFFFFFULL);
    return 1ULL;
  }
  u64 tlen = h->tmp_len;
  u64 i = 2ULL;
  while (i < tlen) {
    u32 x = tmp[i];
    u32 lx = lvl[((u64)x) >> 1];
    u64 j = i;
    while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] < lx) {
      tmp[j] = tmp[j - 1ULL];
      j = j - 1ULL;
    }
    tmp[j] = x;
    i = i + 1ULL;
  }
  u64 max_lvl = (u64)lvl[((u64)tmp[1]) >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack_ac_fid(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce_m6(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  u64 step = 0ULL;
  while (new_ref == 0xFFFFFFFFULL && step < 3ULL) {
    if (step == 0ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    } else {
      u64 gr = (step == 1ULL) ? full_reduce_m6(h, true) : full_reduce_purge_c0(h);
      if (gr == 20ULL) { return 20ULL; }
      if (gr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
    new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
    step = step + 1ULL;
  }
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (u32)new_ref;
  if (new_ref == 0xFFFFFFFEULL) {
    rsn = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (max_lvl > 0ULL) {
      u32 *rsns_lc = (u32 *)h->reason;
      u32 nr_lc = rsns_lc[tmp[1] >> 1];
      if (nr_lc != 0xFFFFFFFFu && (nr_lc & PW_BIN_FLAG) != 0u) { rsn = nr_lc; }
    }
  }
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

u64 full_propagate_beyond_m7(FullHdr *h) {
  u64 ignore_ref = 0xFFFFFFFFULL;
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
          if (bv < (i8)0) { continue; }
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
        if (ov < (i8)0) { continue; }
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

/-! ## 1. `Fn` Handles, Replacements & Inserted `Befores` -/

/-- Step-13 inserted helper `full_update_classify_fid` (`watermarks[4]` bit 1). -/
def fidStep13S2UpdateClassifyFn : Fn :=
  ⟨"full_update_classify_fid", [i64], [], full_update_classify_fid_body⟩

/-- Step-13 `full_otfs_large` replacement. -/
def fidStep13S2OtfsLargeFn : Fn :=
  ⟨"full_otfs_large", [i64, i32, i32], [.bool], full_otfs_large_body⟩

/-- Step-13 `full_one_lit_confl` replacement (`jumpreasons`). -/
def fidStep13S2OneLitConflFn : Fn :=
  ⟨"full_one_lit_confl", [i64], [i64], full_one_lit_confl_body⟩

/-- Step-13 `full_eager_subsume` replacement (`num_redundant` decrement). -/
def fidStep13S2EagerSubsumeFn : Fn :=
  ⟨"full_eager_subsume", [i64, i64], [], full_eager_subsume_body⟩

/-- Step-13 `full_learn_clause_m6` replacement (`iterating`, `jumpreasons`, no reverse). -/
def fidStep13S2LearnClauseM6Fn : Fn :=
  ⟨"full_learn_clause_m6", [i64, i64], [i64], full_learn_clause_m6_body⟩

/-- Step-13 inserted helper `full_propagate_beyond_m7` (warmup BCP). -/
def fidStep13S2PropBeyondM7Fn : Fn :=
  ⟨"full_propagate_beyond_m7", [i64], [i64], full_propagate_beyond_m7_body⟩

/-- Ordered `4`-function Shard `S2-B` replacement list (`0` ABI changes). -/
def fidStep13S2OTFSUnitRepls : List Fn :=
  [ fidStep13S2OtfsLargeFn
  , fidStep13S2OneLitConflFn
  , fidStep13S2EagerSubsumeFn
  , fidStep13S2LearnClauseM6Fn ]

/-- Ordered `2`-function Shard `S2-B` insertion list (`full_update_classify_fid` before
`full_reduce_m6`, `full_propagate_beyond_m7` before `full_warmup_m7`). -/
def fidStep13S2OTFSUnitBefores : List (Sym × List Fn) :=
  [ ("full_reduce_m6", [fidStep13S2UpdateClassifyFn])
  , ("full_warmup_m7", [fidStep13S2PropBeyondM7Fn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_update_classify_fid_s13_wf :
    Func.Wf fidStep13S2UpdateClassifyFn.body := by t_wf_reify

theorem full_otfs_large_s13_wf :
    Func.Wf fidStep13S2OtfsLargeFn.body := by t_wf_reify

theorem full_one_lit_confl_s13_wf :
    Func.Wf fidStep13S2OneLitConflFn.body := by t_wf_reify

theorem full_eager_subsume_s13_wf :
    Func.Wf fidStep13S2EagerSubsumeFn.body := by t_wf_reify

theorem full_learn_clause_m6_s13_wf :
    Func.Wf fidStep13S2LearnClauseM6Fn.body := by t_wf_reify

theorem full_propagate_beyond_m7_s13_wf :
    Func.Wf fidStep13S2PropBeyondM7Fn.body := by t_wf_reify

theorem fidStep13S2OTFSUnitRepls_wf :
    ∀ f ∈ fidStep13S2OTFSUnitRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S2OTFSUnitRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_otfs_large_s13_wf
  · exact full_one_lit_confl_s13_wf
  · exact full_eager_subsume_s13_wf
  · exact full_learn_clause_m6_s13_wf

theorem fidStep13S2OTFSUnitBefores_wf :
    ∀ h ∈ fidStep13S2OTFSUnitBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep13S2OTFSUnitBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact full_update_classify_fid_s13_wf
  · exact full_propagate_beyond_m7_s13_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
