/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Fidelity Step 12B — BVE, Backbone & Forward Subsumption (`FullFidelityStep12BBveFwd`)

Data-pure additive C0 layer (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, `0` new `FullWitnessInv`
conjuncts, every function `<= 6` args) implementing four pure Kissat 4.0.4 scaling/fidelity fixes:
1. **`P1-2` (`full_bve_weaken_unit_fid`, `full_bve_var_m7`; `src/eliminate.c:295-325`,
   `src/weaken.c:13-60`):** Non-incremental single-polarity weakening pushing only the smaller
   polarity's clauses onto `extend_stk` plus a single opposite unit `EXT_BLK_FLAG | opp_lit`
   (and single unit only for pure literals), cutting `extend_stk` consumption by `>= 2x`.
2. **`P1-7` (`full_bve_commit_res`; `src/eliminate.c:207-245`, `src/inline.h:52-67`):** Marks
   `FL_SUBSUME | FL_ELIM_C | FL_FACT_P/N` on newly committed binary/large resolvent literals and
   `PH_SUBSUME` on newly allocated irredundant large resolvent clause headers.
3. **`P1-5a/c` (`full_backbone_sched_m6`, `full_backbone_m6`; `src/backbone.c:16-68,345-350`):**
   Two-pass candidate scheduling appending all remaining non-prioritized active unassigned literals
   after prioritized `FL_BONE0/1` literals, plus scaled round limit `min(1000, 100 * comp)`.
4. **`P1-6b/c` (`full_dense_prop_unit_m7`, `full_forward_sub_m7`; `src/eliminate.c:444-447`,
   `src/propdense.c:4-78`):** `unass > 1u` early break in dense large-clause propagation, and
   `full_fwd_reconnect_irred_m7(h)` (+ trail `propagated` rewind) BEFORE
   `full_dense_flush_units_m7(h)` in `full_forward_sub_m7`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep12BBveFwd "
#define PH_GARB               0x00080000u
#define PH_SUBSUME            0x01000000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu
#define EXT_BLK_FLAG          0x80000000u

#define FL_ACTIVE             1u
#define FL_ELIM               2u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u

#define M8_OCC_LIM            2001u
#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define M8_RES_OFF            4192u
#define FID_K6_MIN_SCR        16384ULL

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

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_alloc_cl(FullHdr *h, u32 len, u32 glue, bool red);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_prioritize_binaries_m6(FullHdr *h);
extern u64 full_backbone_round_m6(FullHdr *h, u64 cand_n, bool stop_early);
extern void full_backbone_keep_m6(FullHdr *h, u64 cand_n);
extern bool full_fwd_dedup_bins(FullHdr *h);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64 full_fwd_collect_sort_m7(FullHdr *h);
extern void full_fwd_flush_large_m7(FullHdr *h);
extern bool full_fwd_check_cl_m7(FullHdr *h, u32 cref);
extern void full_fwd_connect_subsumer_m7(FullHdr *h, u32 cref);
extern void full_fwd_reconnect_irred_m7(FullHdr *h);
extern u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern void full_bve_gates_fid(FullHdr *h, u32 v, u32 np, u32 nn);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);

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

u64 full_backbone_m6(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    h->probing = 0ULL; return 1ULL;
  }
  h->probing = 1ULL;
  u64 pr0 = full_propagate(h);
  if (pr0 == 1ULL) { h->probing = 0ULL; return 20ULL; }
  if (pr0 == 2ULL) { h->probing = 0ULL; return 1ULL; }
  bool stop_early = full_prioritize_binaries_m6(h);
  u64 cand_n = full_backbone_sched_m6(h);
  h->ant_sz = tick_lim;
  u32 *units = (u32 *)h->work_stk2;
  u64 comp = (h->probings > 0ULL) ? h->probings : 1ULL;
  u64 max_rounds = (comp >= 10ULL) ? 1000ULL : (100ULL * comp);
  u64 res = 1ULL;
  u64 round = 0ULL;
  while (round < max_rounds && cand_n > 0ULL && h->ant_sz > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL) {
    cand_n = full_backbone_round_m6(h, cand_n, stop_early);
    u64 ucnt = h->res_sz;
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
    round = round + 1ULL;
  }
  full_backbone_keep_m6(h, cand_n);
  h->probing = 0ULL;
  return res;
}

bool full_dense_prop_unit_m7(FullHdr *h, u32 lit) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  if ((u64)lit >= nlits || vals[lit] <= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 nl = lit ^ 1u;
  u64 off = (u64)wvec[(u64)nl << 1];
  u64 end = off + (u64)wvec[((u64)nl << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      i8 vo = vals[ot];
      if (vo < (i8)0) { h->inconsistent = 1ULL; return false; }
      if (vo == (i8)0 && !full_add_unit(h, ot)) { return false; }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 unass = 0u;
    u32 ulit = 0u;
    u32 k = 0u;
    while (k < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)k];
      i8 vl = vals[cl];
      if (vl > (i8)0) { sat = true; break; }
      if (vl == (i8)0) {
        unass = unass + 1u;
        if (unass > 1u) { break; }
        ulit = cl;
      }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    } else if (unass == 0u) {
      h->inconsistent = 1ULL;
      return false;
    } else if (unass == 1u) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, ulit)) { return false; }
    }
  }
  off = (u64)wvec[(u64)lit << 1];
  end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    u32 hdr = ar[cr];
    if ((hdr & PH_GARB) != 0u) { continue; }
    u32 sz = ar[(u64)cr + 2ULL];
    bool sat = false;
    u32 k = 0u;
    while (k < sz) {
      if (vals[ar[(u64)cr + 3ULL + (u64)k]] > (i8)0) { sat = true; break; }
      k = k + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    }
  }
  return true;
}

u64 full_forward_sub_m7(FullHdr *h, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  u64 saved_prop = h->propagated;
  u64 ncand = full_fwd_collect_sort_m7(h);
  if (ncand == 0ULL) { return (h->inconsistent != 0ULL) ? 20ULL : 1ULL; }
  full_fwd_flush_large_m7(h);
  u32 *rr = (u32 *)h->red_refs;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  u64 rem = budget;
  while (i < ncand && rem > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 cr = rr[i];
    rem = rem - 1ULL;
    if (!full_fwd_check_cl_m7(h, cr)) { return 20ULL; }
    if (h->oom == 0ULL && h->inconsistent == 0ULL && (ar[cr] & PH_GARB) == 0u) {
      full_fwd_connect_subsumer_m7(h, cr);
    }
    i = i + 1ULL;
  }
  if (i == ncand && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 *fl = (u32 *)h->flags;
    u64 cv = h->cur_vars;
    u64 v = 0ULL;
    while (v < cv) { fl[v] = fl[v] & (~FL_SUBSUME); v = v + 1ULL; }
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_SUBSUME) != 0u) {
        ar[p] = hdr & (~PH_SUBSUME);
        if ((hdr & PH_GARB) == 0u) {
          u32 k = 0u;
          while (k < sz) {
            u32 lv = ar[p + 3ULL + (u64)k] >> 1;
            if ((u64)lv < cv) { fl[lv] = fl[lv] | FL_SUBSUME | FL_ELIM_C; }
            k = k + 1u;
          }
        } else if (sz >= 2u) {
          u32 v0 = ar[p + 3ULL] >> 1;
          u32 v1 = ar[p + 4ULL] >> 1;
          if ((u64)v0 < cv) { fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C; }
          if ((u64)v1 < cv) { fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C; }
        }
      }
      p = np;
    }
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  full_fwd_reconnect_irred_m7(h);
  if (saved_prop < h->propagated && saved_prop <= h->trail_end) {
    h->propagated = saved_prop;
  }
  if (!full_dense_flush_units_m7(h)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars;
  u64 p = r_off;
  while (p < r_end) {
    u32 sz = scr[p]; p = p + 1ULL;
    if (sz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (sz == 1u) { if (!full_add_unit(h, scr[p])) { return 20ULL; } }
    else if (sz == 2u) {
      u32 l0 = scr[p]; u32 l1 = scr[p + 1ULL];
      u64 br = full_add_bin(h, l0, l1);
      if (br == 20ULL) { return 20ULL; }
      if (br == 2ULL) { return 2ULL; }
      u32 v0 = l0 >> 1; u32 v1 = l1 >> 1;
      if ((u64)v0 < cv) {
        fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C | (((l0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      }
      if ((u64)v1 < cv) {
        fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C | (((l1 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      }
    } else {
      u64 cr = full_alloc_cl(h, sz, 0u, false);
      if (cr == 0xFFFFFFFFULL) { h->oom = 1ULL; return 2ULL; }
      u32 *ar = (u32 *)h->arena;
      ar[cr] = ar[cr] | PH_SUBSUME;
      u32 k = 0u;
      while (k < sz) {
        u32 lk = scr[p + (u64)k];
        ar[cr + 3ULL + (u64)k] = lk;
        u32 vk = lk >> 1;
        if ((u64)vk < cv) {
          fl[vk] = fl[vk] | FL_SUBSUME | FL_ELIM_C | (((lk & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        }
        k = k + 1u;
      }
      k = 0u;
      while (k < sz) {
        if (!full_watch_push(h, ar[cr + 3ULL + (u64)k], sz & PW_LIT_MASK, (u32)cr, 2u)) {
          ar[cr] = ar[cr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
          h->oom = 1ULL; return 2ULL;
        }
        k = k + 1u;
      }
      h->num_irred = h->num_irred + 1ULL;
    }
    p = p + (u64)sz;
  }
  return 1ULL;
}

bool full_bve_weaken_unit_fid(FullHdr *h, u32 blk_lit, u32 off, u32 cnt) {
  if (cnt == 0u) { return true; }
  if (h->extend_len >= h->extend_cap) { return false; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      full_delete_binary(h, blk_lit, ot);
    } else {
      ar[w] = ar[w] | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
    }
    i = i + 1u;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = (blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG;
  h->extend_len = p + 1ULL;
  return true;
}

u64 full_bve_var_m7(FullHdr *h, u32 v) {
  u64 scap = h->scratch_cap;
  if (scap < 2048ULL) { return 1ULL; }
  bool use_m8 = (scap >= FID_K6_MIN_SCR);
  u32 occ_lim = use_m8 ? M8_OCC_LIM : 512u;
  u32 neg_off = use_m8 ? M8_NEG_OFF : 512u;
  u32 pos_mask = use_m8 ? M8_POS_MASK : 1024u;
  u32 neg_mask = use_m8 ? M8_NEG_MASK : 1040u;
  u32 gf_idx = use_m8 ? M8_GF_IDX : 1056u;
  u32 rg_idx = use_m8 ? M8_RG_IDX : 1057u;
  u64 r_off = use_m8 ? (u64)M8_RES_OFF : 1088ULL;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 cv2 = h->cur_vars << 1;
  u64 acap = h->arena_cap;
  u64 wcap = h->wcap;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, occ_lim);
  u32 nn = full_bve_collect_m7(h, nl, scr + neg_off, occ_lim);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  if (np > 0u && nn > 0u && (u64)np + (u64)nn > 2000ULL) { return 1ULL; }
  u64 ext_p = (np > 0u) ? full_bve_ext_need(h, 0u, np) : 0ULL;
  u64 ext_n = (nn > 0u) ? full_bve_ext_need(h, neg_off, nn) : 0ULL;
  bool push_pos = (ext_p <= ext_n);
  u64 ext_need = 0ULL;
  if (np == 0u || nn == 0u) {
    ext_need = (np > 0u || nn > 0u) ? 1ULL : 0ULL;
  } else {
    ext_need = (push_pos ? ext_p : ext_n) + 1ULL;
  }
  bool ext_ok = (h->extend_len <= h->extend_cap && ext_need <= h->extend_cap - h->extend_len);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken_unit_fid(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken_unit_fid(h, nl, neg_off, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    if (use_m8) { full_bve_gates_fid(h, v, np, nn); }
    else { full_bve_gates_m7(h, v, np, nn); }
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (vals[pl] != (i8)0) { return 1ULL; }
    bool gf = (scr[gf_idx] != 0u);
    bool rg = (scr[rg_idx] != 0u);
    u64 res_sz = h->res_sz;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[pos_mask + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[neg_mask + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair) {
          res_sz = res_sz + 1ULL;
          if (full_bve_resolve_pair(h, v, scr[i], scr[neg_off + j])) {
            u64 rlen = h->tmp_len;
            if (rlen == 0ULL) {
              h->res_sz = res_sz;
              h->inconsistent = 1ULL;
              return 20ULL;
            }
            if (rlen == 1ULL) {
              u32 ul = tmp[0];
              if ((u64)ul < cv2) {
                i8 uv = vals[ul];
                if (uv < (i8)0) {
                  h->res_sz = res_sz;
                  h->inconsistent = 1ULL;
                  return 20ULL;
                }
                if (uv == (i8)0) { full_assign_lvl(h, ul, 0xFFFFFFFFu, 0u); }
              }
              j = j + 1u;
              continue;
            }
            r_cnt = r_cnt + 1ULL;
            if (rlen > 100ULL || r_cnt > lim_cls || rp + 1ULL + rlen > scap) {
              fit = false;
              break;
            }
            scr[rp] = (u32)rlen;
            u32 k = 0u;
            while ((u64)k < rlen) {
              u32 lk = tmp[k];
              scr[rp + 1ULL + (u64)k] = lk;
              if (rlen >= 2ULL && (u64)lk < cv2) {
                w_est = w_est + (((u64)wvec[((u64)lk << 1) + 1ULL]) << 1) + 4ULL;
              }
              k = k + 1u;
            }
            rp = rp + 1ULL + rlen;
          }
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
    h->res_sz = res_sz;
  }
  if (fit) {
    u64 ar_need = (rp - r_off) + (r_cnt * 2ULL) + 16ULL;
    u64 w_need = w_est + (r_cnt * 4ULL) + 16ULL;
    if (ar_need > acap - h->arena_len) {
      fit = false;
    } else if (w_need > wcap - h->wlen) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (w_need > wcap - h->wlen) { fit = false; }
    }
  }
  if (fit) {
    bool wok = false;
    if (push_pos) {
      wok = full_bve_weaken(h, pl, 0u, np) &&
            full_bve_weaken_unit_fid(h, nl, neg_off, nn);
    } else {
      wok = full_bve_weaken(h, nl, neg_off, nn) &&
            full_bve_weaken_unit_fid(h, pl, 0u, np);
    }
    if (!wok) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    u64 cr = full_bve_commit_res(h, r_off, rp);
    if (cr == 20ULL) { return 20ULL; }
    if (cr == 1ULL && !full_dense_flush_units_m7(h)) { return 20ULL; }
    return cr;
  }
  return 1ULL;
}
"

/-! ## 1. Canonical `Fn` Handles & Patch Lists -/

def fidStep12BBackboneSchedM6Fn : Fn :=
  ⟨"full_backbone_sched_m6", [i64], [i64], full_backbone_sched_m6_body⟩

def fidStep12BBackboneM6Fn : Fn :=
  ⟨"full_backbone_m6", [i64, i64], [i64], full_backbone_m6_body⟩

def fidStep12BDensePropUnitM7Fn : Fn :=
  ⟨"full_dense_prop_unit_m7", [i64, i32], [.bool], full_dense_prop_unit_m7_body⟩

def fidStep12BForwardSubM7Fn : Fn :=
  ⟨"full_forward_sub_m7", [i64, i64], [i64], full_forward_sub_m7_body⟩

def fidStep12BBveCommitResFn : Fn :=
  ⟨"full_bve_commit_res", [i64, i64, i64], [i64], full_bve_commit_res_body⟩

def fidStep12BBveWeakenUnitFn : Fn :=
  ⟨"full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool], full_bve_weaken_unit_fid_body⟩

def fidStep12BBveVarM7Fn : Fn :=
  ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩

/-- The `6` Step-12B BVE/Backbone/Forward-Subsumption replacement functions. -/
def fidStep12BBveFwdRepls : List Fn :=
  [ fidStep12BBackboneSchedM6Fn
  , fidStep12BBackboneM6Fn
  , fidStep12BDensePropUnitM7Fn
  , fidStep12BForwardSubM7Fn
  , fidStep12BBveCommitResFn
  , fidStep12BBveVarM7Fn ]

/-- The `1` Step-12B BVE helper inserted before `full_bve_var_m7`. -/
def fidStep12BBveFwdBefores : List (Sym × List Fn) :=
  [ ("full_bve_var_m7", [fidStep12BBveWeakenUnitFn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_backbone_sched_m6_s12b_wf :
    Func.Wf fidStep12BBackboneSchedM6Fn.body := by t_wf_reify

theorem full_backbone_m6_s12b_wf :
    Func.Wf fidStep12BBackboneM6Fn.body := by t_wf_reify

theorem full_dense_prop_unit_m7_s12b_wf :
    Func.Wf fidStep12BDensePropUnitM7Fn.body := by t_wf_reify

theorem full_forward_sub_m7_s12b_wf :
    Func.Wf fidStep12BForwardSubM7Fn.body := by t_wf_reify

theorem full_bve_commit_res_s12b_wf :
    Func.Wf fidStep12BBveCommitResFn.body := by t_wf_reify

theorem full_bve_weaken_unit_fid_s12b_wf :
    Func.Wf fidStep12BBveWeakenUnitFn.body := by t_wf_reify

theorem full_bve_var_m7_s12b_wf :
    Func.Wf fidStep12BBveVarM7Fn.body := by t_wf_reify

theorem fidStep12BBveFwdRepls_wf : ∀ f ∈ fidStep12BBveFwdRepls, f.Wf := by
  intro f hf
  simp only [fidStep12BBveFwdRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_backbone_sched_m6_s12b_wf
  · exact full_backbone_m6_s12b_wf
  · exact full_dense_prop_unit_m7_s12b_wf
  · exact full_forward_sub_m7_s12b_wf
  · exact full_bve_commit_res_s12b_wf
  · exact full_bve_var_m7_s12b_wf

theorem fidStep12BBveFwdBefores_wf :
    ∀ f ∈ fidStep12BBveFwdBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidStep12BBveFwdBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_singleton] at hf
  subst hf
  exact full_bve_weaken_unit_fid_s12b_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
