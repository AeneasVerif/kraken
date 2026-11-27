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
# Kissat Fidelity Step 13 Shard S5-B (`FullFidelityStep13S5VivifyBackbone`)

Data-pure Step-13 C0 bodies for Shard S5-B (`1` ADD + `13` MOD = `14` functions, verbatim from
`step13_v2_frozen_direct.c`, with `static` dropped on `full_viv_recompute_promote_fid`):
- ADD: `full_viv_recompute_promote_fid` (inserted before `full_viv_deduce_m6`)
- MOD: `full_viv_commit_m6`, `full_viv_mark_garb_m6`, `full_viv_deduce_m6`, `full_viv_finish_m6`,
  `full_vivify_tier_m6_hdr`, `full_vivify_m6_hdr`, `full_backbone_keep_m6`,
  `full_backbone_prop_m6`, `full_backbone_analyze_m6`, `full_backbone_round_m6`,
  `full_backbone_m6`, `full_trans_lit_m6`, `full_transitive_m6`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S5VivifyBackbone "
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

#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u
#define PH_SHRK               0x00800000u

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_ACTIVE             1u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u

#define M6_DELAY_VIVIFYIRR    3ULL
#define M6_WM_PROBE_TICKS     0ULL

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64  full_add_bin_m6(FullHdr *h, u32 a, u32 b);
extern void full_viv_unreason_m6(FullHdr *h, u32 cref);
extern void full_viv_best_watch_m6(FullHdr *h, u32 olen);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern bool full_viv_subsumes_bin_m6(FullHdr *h, u32 a, u32 b);
extern bool full_viv_subsumes_cl_m6(FullHdr *h, u32 rcr, u32 sz);
extern void full_viv_reestablish_m6(FullHdr *h, u32 cref);
extern u64  full_viv_inst_m6(FullHdr *h, u32 cref, u32 sz);
extern u64  full_viv_collect_fid(FullHdr *h, u64 tier_mode);
extern u32  full_arena_next(FullHdr *h, u32 cref);
extern void full_viv_sort_fid(FullHdr *h, u64 bn);
extern u64  m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern u64  full_viv_clause_m6(FullHdr *h, u32 cref);
extern u64  full_propagate(FullHdr *h);
extern void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode);
extern u64  m6_hdr_get_tier1(FullHdr *h, bool vivify_mode);
extern u64  m6_hdr_get_tier2(FullHdr *h, bool vivify_mode);
extern bool m6_hdr_delaying(FullHdr *h, u64 id);
extern void m6_hdr_bump_delay(FullHdr *h, u64 id);
extern void m6_hdr_reduce_delay(FullHdr *h, u64 id);
extern void m6_hdr_sync_legacy_tiers(FullHdr *h);
extern void full_backbone_unwind_m6(FullHdr *h, u64 saved, u64 target_lvl);
extern bool full_prioritize_binaries_m6(FullHdr *h);
extern u64  full_backbone_sched_m6(FullHdr *h);
extern u64  m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 other);
extern void full_trans_sort_m6(FullHdr *h, u64 n);
extern void full_wstack_defrag(FullHdr *h);

void full_viv_recompute_promote_fid(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((u64)cref + 3ULL > h->arena_len) { return; }
  u32 hdr = ar[cref];
  if ((hdr & 0x00400000u) == 0u) { return; }
  u64 glue = (u64)(hdr & 0x7FFFFu);
  if (glue <= 1ULL) { return; }
  u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)cref + 3ULL + (u64)sz > h->arena_len) { return; }
  u32 *lv = (u32 *)h->level;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *mclr = (u32 *)h->min_clr;
  u64 cv = h->cur_vars;
  u64 ng = 0ULL;
  u32 k = 0u;
  while (k < sz) {
    u64 kv = (u64)(ar[(u64)cref + 3ULL + (u64)k] >> 1);
    if (kv < cv) {
      u64 kl = (u64)lv[kv];
      if (kl <= h->cur_level && (ftrl[kl] & 0x80000000u) == 0u) {
        ftrl[kl] = ftrl[kl] | 0x80000000u;
        mclr[ng] = (u32)kl;
        ng = ng + 1ULL;
        if (ng >= glue) { break; }
      }
    }
    k = k + 1u;
  }
  u64 ui = 0ULL;
  while (ui < ng) {
    u32 ml = mclr[ui];
    ftrl[ml] = ftrl[ml] & 0x7FFFFFFFu;
    ui = ui + 1ULL;
  }
  if (ng > 0ULL && ng < glue) {
    ar[cref] = (hdr & (~0x7FFFFu)) | (u32)ng;
  }
}

u64 full_viv_commit_m6(FullHdr *h, u32 cref, u32 olen, u32 implied) {
  u32 *ar = (u32 *)h->arena; u32 *out = (u32 *)h->work_stk2;
  u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  if (olen >= old_sz) { return 1ULL; }
  h->viv_cnt = h->viv_cnt + 1ULL;
  if (olen == 0u) {
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (olen <= 2u) {
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
    full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    if (olen == 1u) { return full_add_unit(h, out[0]) ? 1ULL : 20ULL; }
    u64 br = full_add_bin_m6(h, out[0], out[1]);
    if (br == 20ULL) { return 20ULL; }
    if (br == 2ULL) { return 2ULL; }
    return 1ULL;
  }
  if (implied == 0xFFFFFFFFu) {
    u64 target = (u64)(olen - 2u);
    if (h->cur_level > target) { full_backtrack(h, target); }
  }
  full_viv_unreason_m6(h, cref);
  full_viv_best_watch_m6(h, olen);
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u32 i = 0u;
  while (i < olen) { ar[(u64)cref + 3ULL + (u64)i] = out[i]; i = i + 1u; }
  ar[(u64)cref + 2ULL] = olen; ar[(u64)cref + 1ULL] = 2u;
  u32 nhdr = hdr;
  if ((nhdr & PH_RED) != 0u) {
    u32 glue = nhdr & PH_GLUE_MASK;
    if (glue >= olen) {
      nhdr = (nhdr & (~PH_GLUE_MASK)) | ((olen - 1u) & PH_GLUE_MASK);
    }
  }
  if ((nhdr & PH_SHRK) == 0u) {
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
    nhdr = nhdr | PH_SHRK;
  }
  ar[cref] = nhdr;
  if ((nhdr & PH_RED) == 0u) {
    u32 *fl_v = (u32 *)h->flags;
    u32 k_v = 0u;
    while (k_v < olen) {
      u32 lv = out[k_v];
      u32 fbit_v = ((lv & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
      fl_v[lv >> 1] = fl_v[lv >> 1] | FL_SUBSUME | FL_ELIM_C | fbit_v;
      k_v = k_v + 1u;
    }
  }
  u32 l0 = out[0]; u32 l1 = out[1];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL;
    if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
    return 2ULL;
  }
  return 1ULL;
}

void full_viv_mark_garb_m6(FullHdr *h, u32 cref) {
  full_viv_unreason_m6(h, cref);
  u32 *ar = (u32 *)h->arena;
  u32 hdr = ar[cref];
  if ((hdr & PH_GARB) != 0u) { return; }
  u32 sz = ar[(u64)cref + 2ULL];
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  ar[cref] = hdr | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
  if ((hdr & PH_RED) != 0u) {
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
  } else {
    if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    u32 *fl_g = (u32 *)h->flags;
    u32 k_g = 0u;
    while (k_g < sz) {
      u32 lg = ar[(u64)cref + 3ULL + (u64)k_g];
      u32 fbit_g = ((lg & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
      fl_g[lg >> 1] = fl_g[lg >> 1] | FL_ELIM_C | fbit_g;
      k_g = k_g + 1u;
    }
  }
  h->viv_cnt = h->viv_cnt + 1ULL;
}

u32 full_viv_deduce_m6(FullHdr *h, u32 cref, u32 sz, u32 implied) {
  u32 *ar = (u32 *)h->arena; u8 *mrk = (u8 *)h->mark; u8 *lm = (u8 *)h->lit_mark;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *qstk = (u32 *)h->work_stk1; u32 *out = (u32 *)h->work_stk2; u64 cv = h->cur_vars;
  u32 mk = 0u;
  while (mk < sz) { lm[tmp[mk]] = (u8)1; mk = mk + 1u; }
  u64 qlen = 0ULL; u64 qi = 0ULL; u32 olen = 0u; bool taut = false;
  h->ant_sz = 0xFFFFFFFFFFFFFFFFULL; h->res_sz = 0ULL;
  if (implied != 0xFFFFFFFFu) {
    u32 iv = implied >> 1;
    if ((u64)iv < cv && lvl[iv] > 0u) { mrk[iv] = (u8)1; qstk[qlen] = iv; qlen = qlen + 1ULL; }
    out[olen] = implied; olen = olen + 1u;
  } else {
    u32 src_cr = (h->confl_type == 2ULL) ? (u32)h->confl_ref : cref;
    if (h->confl_type == 1ULL) {
      u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
      if (full_viv_subsumes_bin_m6(h, a, b)) {
        h->ant_sz = 0xFFFFFFFFFFFFFFFEULL;
      } else {
        if (lvl[a >> 1] > 0u && mrk[a >> 1] == (u8)0 && qlen < cv) {
          mrk[a >> 1] = (u8)1; qstk[qlen] = a >> 1; qlen = qlen + 1ULL;
        }
        if (lvl[b >> 1] > 0u && mrk[b >> 1] == (u8)0 && qlen < cv) {
          mrk[b >> 1] = (u8)1; qstk[qlen] = b >> 1; qlen = qlen + 1ULL;
        }
      }
    } else if ((u64)src_cr + 3ULL <= h->arena_len) {
      if (src_cr != cref) {
        if ((ar[src_cr] & PH_RED) != 0u) {
          h->res_sz = 1ULL;
          full_viv_recompute_promote_fid(h, src_cr);
        }
        if (full_viv_subsumes_cl_m6(h, src_cr, sz)) { h->ant_sz = (u64)src_cr; }
      }
      if (h->ant_sz == 0xFFFFFFFFFFFFFFFFULL) {
        u32 csz = ar[(u64)src_cr + 2ULL]; u32 i = 0u;
        while (i < csz) {
          u32 lv = ar[(u64)src_cr + 3ULL + (u64)i] >> 1;
          if ((u64)lv < cv && lvl[lv] > 0u && mrk[lv] == (u8)0 && qlen < cv) {
            mrk[lv] = (u8)1; qstk[qlen] = lv; qlen = qlen + 1ULL;
          }
          i = i + 1u;
        }
      }
    }
  }
  u32 *trl = (u32 *)h->trail; u32 *tpos = (u32 *)h->trail_pos;
  while (qi < qlen && h->ant_sz == 0xFFFFFFFFFFFFFFFFULL) {
    u32 v = qstk[qi]; qi = qi + 1ULL;
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) {
      u32 tl = trl[tpos[v]];
      if (tl == implied) { taut = true; }
      else if ((u64)olen < cv) { out[olen] = tl ^ 1u; olen = olen + 1u; }
    } else if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      u32 tl = trl[tpos[v]];
      if (full_viv_subsumes_bin_m6(h, tl, ot)) {
        h->ant_sz = 0xFFFFFFFFFFFFFFFEULL;
        break;
      }
      u32 ov = ot >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
        mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
      }
    } else if ((u64)rsn + 3ULL <= h->arena_len) {
      if ((ar[rsn] & PH_RED) != 0u) {
        h->res_sz = 1ULL;
        full_viv_recompute_promote_fid(h, rsn);
      }
      if (rsn != cref && full_viv_subsumes_cl_m6(h, rsn, sz)) {
        h->ant_sz = (u64)rsn;
        break;
      }
      u32 rsz = ar[(u64)rsn + 2ULL]; u32 j = 0u;
      while (j < rsz && (u64)rsn + 3ULL + (u64)rsz <= h->arena_len) {
        u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
        if (ov != v && (u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
          mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
        }
        j = j + 1u;
      }
    }
  }
  qi = 0ULL; while (qi < qlen) { mrk[qstk[qi]] = (u8)0; qi = qi + 1ULL; }
  mk = 0u; while (mk < sz) { lm[tmp[mk]] = (u8)0; mk = mk + 1u; }
  if (taut) { h->ant_sz = 0xFFFFFFFFFFFFFFFFULL; return 0xFFFFFFFFu; }
  return olen;
}

u64 full_viv_finish_m6(FullHdr *h, u32 cref, u32 sz,
                       bool confl, u32 implied, bool all_done) {
  u32 *ar = (u32 *)h->arena;
  u32 olen = sz;
  bool has_ded = false;
  h->ant_sz = 0xFFFFFFFFFFFFFFFFULL;
  h->res_sz = 0ULL;
  if (confl || implied != 0xFFFFFFFFu || all_done) {
    olen = full_viv_deduce_m6(h, cref, sz, confl ? 0xFFFFFFFFu : implied);
    has_ded = (olen != 0xFFFFFFFFu);
  }
  bool used_red = (h->res_sz != 0ULL);
  u64 sub_ref = h->ant_sz;
  u32 hdr = ar[cref];
  bool is_red = ((hdr & PH_RED) != 0u);
  if (sub_ref != 0xFFFFFFFFFFFFFFFFULL) {
    if (sub_ref < h->arena_len) {
      u32 shdr = ar[sub_ref];
      if (!is_red && (shdr & PH_RED) != 0u) {
        ar[sub_ref] = shdr & (~PH_RED);
        if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
        h->num_irred = h->num_irred + 1ULL;
        u32 *fl_p = (u32 *)h->flags;
        u32 ssz_p = ar[sub_ref + 2ULL];
        u32 k_p = 0u;
        while (k_p < ssz_p) {
          u32 lp = ar[sub_ref + 3ULL + (u64)k_p];
          u32 fbit_p = ((lp & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
          fl_p[lp >> 1] = fl_p[lp >> 1] | FL_SUBSUME | FL_ELIM_C | fbit_p;
          k_p = k_p + 1u;
        }
      } else if (is_red && (shdr & PH_RED) != 0u) {
        u32 cgl = hdr & PH_GLUE_MASK;
        u32 sgl = shdr & PH_GLUE_MASK;
        if (cgl < sgl) { ar[sub_ref] = (shdr & (~PH_GLUE_MASK)) | cgl; }
      }
    }
    full_viv_mark_garb_m6(h, cref);
    if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
    return 1ULL;
  }
  if (has_ded && olen < sz) {
    u64 cr = full_viv_commit_m6(h, cref, olen, confl ? 0xFFFFFFFFu : implied);
    if (cr == 1ULL) { full_viv_reestablish_m6(h, cref); }
    return cr;
  }
  if (has_ded && (confl || implied != 0xFFFFFFFFu) && (is_red || !used_red)) {
    full_viv_mark_garb_m6(h, cref);
    if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
    return 1ULL;
  }
  if (!confl && implied == 0xFFFFFFFFu && all_done) {
    u64 ir = full_viv_inst_m6(h, cref, sz);
    if (ir != 0ULL) {
      if (ir == 1ULL) { full_viv_reestablish_m6(h, cref); }
      return ir;
    }
  }
  if (confl && h->cur_level > 0ULL) { full_backtrack(h, h->cur_level - 1ULL); }
  full_viv_reestablish_m6(h, cref);
  return 1ULL;
}

u64 full_vivify_tier_m6_hdr(FullHdr *h, u64 tier_mode, u64 budget, u64 tick_lim) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap;
  u64 bn = full_viv_collect_fid(h, tier_mode);
  {
    u64 nlits_vc = h->cur_vars << 1;
    u32 *cnt_vc = (u32 *)h->tarjan_reach;
    u32 *ar_vc = (u32 *)h->arena;
    u64 l_vc = 0ULL;
    while (l_vc < nlits_vc) { cnt_vc[l_vc] = 0u; l_vc = l_vc + 1ULL; }
    u64 p_vc = 0ULL;
    while (p_vc < h->arena_len) {
      u32 hdr_vc = ar_vc[p_vc];
      u32 sz_vc = ar_vc[p_vc + 2ULL];
      u64 np_vc = (u64)full_arena_next(h, (u32)p_vc);
      if ((hdr_vc & PH_GARB) == 0u && sz_vc >= 3u) {
        u32 k_vc = 0u;
        while (k_vc < sz_vc) {
          u32 lit_vc = ar_vc[p_vc + 3ULL + (u64)k_vc];
          if ((u64)lit_vc < nlits_vc && cnt_vc[lit_vc] < 0xFFFFFFFFu) {
            cnt_vc[lit_vc] = cnt_vc[lit_vc] + 1u;
          }
          k_vc = k_vc + 1u;
        }
      }
      p_vc = np_vc;
    }
  }
  bool do_sort = (tier_mode != 0ULL || h->num_irred / 10ULL <= h->num_redundant);
  if (do_sort) {
    full_viv_sort_fid(h, bn);
  }
  u64 res = 1ULL;
  u64 bi = 0ULL;
  while (bi < bn && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL &&
         m6_hdr_get_watermark(h, 5ULL) <= tick_lim) {
    u32 cr = rr[bn - 1ULL - bi];
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
  h->res_sz = bi;
  h->probing = saved_prob;
  return res;
}

u64 full_vivify_m6_hdr(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->tier1 = m6_hdr_get_tier1(h, true);
  h->tier2 = m6_hdr_get_tier2(h, true);
  u64 w0 = m6_hdr_delaying(h, M6_DELAY_VIVIFYIRR) ? 0ULL : 3ULL;
  u64 w1 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w2 = (h->num_redundant == 0ULL) ? 0ULL : 3ULL;
  u64 w3 = (h->num_redundant == 0ULL) ? 0ULL : 1ULL;
  u64 sum = w0 + w1 + w2 + w3;
  if (sum == 0ULL) { return 1ULL; }
  u64 start_s = h->search_ticks;
  u64 last_p = m6_hdr_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 delta = (start_s > last_p) ? (start_s - last_p) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 total = eff_ref / 10ULL;
  if (w1 > 0ULL && w2 > 0ULL && h->tier1 >= h->tier2) { w1 = w1 + w2; w2 = 0ULL; }
  u64 res = 1ULL;
  u64 lim = m6_hdr_get_watermark(h, 5ULL);
  if (w1 > 0ULL) {
    u64 a1 = (total * w1) / sum;
    lim = (lim > (~0ULL) - a1) ? (~0ULL) : (lim + a1);
    res = full_vivify_tier_m6_hdr(h, 1ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w2 > 0ULL) {
    u64 a2 = (total * w2) / sum;
    lim = (lim > (~0ULL) - a2) ? (~0ULL) : (lim + a2);
    res = full_vivify_tier_m6_hdr(h, 2ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w3 > 0ULL) {
    u64 a3 = (total * w3) / sum;
    lim = (lim > (~0ULL) - a3) ? (~0ULL) : (lim + a3);
    res = full_vivify_tier_m6_hdr(h, 3ULL, 0xFFFFFFFFULL, lim);
  }
  if (res != 20ULL && w0 > 0ULL) {
    u64 a0 = (total * w0) / sum;
    lim = (lim > (~0ULL) - a0) ? (~0ULL) : (lim + a0);
    u64 vb = h->viv_cnt;
    u64 ub = h->unassigned;
    res = full_vivify_tier_m6_hdr(h, 0ULL, 0xFFFFFFFFULL, lim);
    u64 tried = h->res_sz;
    if (res != 20ULL) {
      u64 du = (ub > h->unassigned) ? (ub - h->unassigned) : 0ULL;
      u64 y = (h->viv_cnt - vb) + du;
      if (tried == 0ULL || y * 100ULL < tried) {
        m6_hdr_bump_delay(h, M6_DELAY_VIVIFYIRR);
      } else {
        m6_hdr_reduce_delay(h, M6_DELAY_VIVIFYIRR);
      }
    }
  }
  m6_hdr_sync_legacy_tiers(h);
  return res;
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

bool full_trans_lit_m6(FullHdr *h, u32 src, bool stop_early) {
  i8 *vals = (i8 *)h->values;
  if (vals[src] != (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *trl = (u32 *)h->trail; u64 nlits = h->cur_vars << 1;
  u64 off = (u64)wvec[(u64)src << 1]; u64 sz = (u64)wvec[((u64)src << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u32 not_src = src ^ 1u; bool failed = false; u64 reduced = 0ULL;
  u64 p = off; u64 end = off + sz;
  while (p < end && !failed && h->ant_sz > 0ULL) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) == 0u) {
      if (stop_early) { break; }
      p = p + 2ULL; continue;
    }
    u32 dst = w0 & PW_LIT_MASK;
    if ((u64)dst >= nlits || dst <= src || vals[dst] != (i8)0) { p = p + 1ULL; continue; }
    u64 ticks = h->ant_sz - 1ULL;
    u64 saved = h->trail_end; u64 prop = saved; bool trans = false;
    vals[not_src] = (i8)1; vals[src] = (i8)(-1); trl[saved] = not_src;
    h->trail_end = saved + 1ULL;
    while (!trans && !failed && prop < h->trail_end && ticks > 0ULL) {
      u32 lit = trl[prop]; prop = prop + 1ULL; u32 nl = lit ^ 1u;
      u64 loff = (u64)wvec[(u64)nl << 1];
      u64 lend = loff + (u64)wvec[((u64)nl << 1) + 1ULL];
      ticks = ticks - 1ULL;
      u64 q = loff;
      while (q < lend) {
        u32 qw = wstk[q];
        if (qw == 0xFFFFFFFFu) { q = q + 1ULL; continue; }
        if ((qw & PW_BIN_FLAG) == 0u) {
          if (stop_early) { break; }
          q = q + 2ULL;
          if (((q - loff) & 31ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
          continue;
        }
        if (nl == src && q == p) { q = q + 1ULL; continue; }
        q = q + 1ULL;
        if (((q - loff) & 31ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
        u32 ot = qw & PW_LIT_MASK;
        if (ot == dst) { trans = true; break; }
        if ((u64)ot < nlits) {
          if (vals[ot] < (i8)0) { failed = true; break; }
          if (vals[ot] == (i8)0 && h->trail_end < h->max_vars) {
            vals[ot] = (i8)1; vals[ot ^ 1u] = (i8)(-1);
            trl[h->trail_end] = ot; h->trail_end = h->trail_end + 1ULL;
          }
        }
      }
    }
    h->ant_sz = ticks;
    while (h->trail_end > saved) {
      h->trail_end = h->trail_end - 1ULL; u32 ul = trl[h->trail_end];
      vals[ul] = (i8)0; vals[ul ^ 1u] = (i8)0;
    }
    if (trans) {
      full_delete_bin_side(h, dst, src);
      wstk[p] = 0xFFFFFFFFu; reduced = reduced + 1ULL;
      h->trans_cnt = h->trans_cnt + 1ULL;
    }
    p = p + 1ULL;
  }
  if (reduced > 0ULL) {
    u64 q = off; p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if (w0 == 0xFFFFFFFFu) { p = p + 1ULL; }
      else if ((w0 & PW_BIN_FLAG) != 0u) { wstk[q] = w0; q = q + 1ULL; p = p + 1ULL; }
      else if (p + 1ULL < end) {
        wstk[q] = w0; wstk[q + 1ULL] = wstk[p + 1ULL]; q = q + 2ULL; p = p + 2ULL;
      } else { p = p + 1ULL; }
    }
    while (q < end) { wstk[q] = 0xFFFFFFFFu; q = q + 1ULL; }
    wvec[((u64)src << 1) + 1ULL] = (u32)((end - off) - reduced);
    h->wusable = h->wusable + reduced;
    if (h->num_binary >= reduced) { h->num_binary = h->num_binary - reduced; }
  }
  if (failed) { h->trans_cnt = h->trans_cnt + 1ULL; return full_add_unit(h, src); }
  return true;
}

u64 full_transitive_m6(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  u64 saved_prob = h->probing;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    return 1ULL;
  }
  h->probing = 1ULL;
  bool stop_early = full_prioritize_binaries_m6(h);
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *probes = (u32 *)h->work_stk1;
  u64 pn = 0ULL; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_TRANS)) == (FL_ACTIVE | FL_TRANS) &&
        vals[v << 1] == (i8)0) {
      probes[pn] = (u32)v; pn = pn + 1ULL;
    }
    v = v + 1ULL;
  }
  if (pn > 1ULL) { full_trans_sort_m6(h, pn); }
  h->ant_sz = tick_lim;
  u64 res = 1ULL; u64 pi = 0ULL;
  while (pi < pn && h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u32 pv = probes[pi];
    if ((fl[pv] & FL_ACTIVE) != 0u && vals[(u64)pv << 1] == (i8)0) {
      if (!full_trans_lit_m6(h, pv << 1, stop_early)) { res = 20ULL; break; }
      u64 p0 = full_propagate(h);
      if (p0 == 1ULL) { res = 20ULL; break; }
      if (p0 == 2ULL) { break; }
      if (h->ant_sz == 0ULL || h->oom != 0ULL || h->fuel == 0ULL) { break; }
      if (!full_trans_lit_m6(h, (pv << 1) | 1u, stop_early)) { res = 20ULL; break; }
      u64 p1 = full_propagate(h);
      if (p1 == 1ULL) { res = 20ULL; break; }
      if (p1 == 2ULL) { break; }
      if (h->ant_sz > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
        fl[pv] = fl[pv] & (~FL_TRANS);
      }
    } else {
      fl[pv] = fl[pv] & (~FL_TRANS);
    }
    pi = pi + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
  h->probing = saved_prob;
  return res;
}
"

/-! ## 1. Canonical `Fn` Handles -/

def fidStep13S5VivRecomputePromoteFn : Fn :=
  ⟨"full_viv_recompute_promote_fid", [i64, i32], [], full_viv_recompute_promote_fid_body⟩

def fidStep13S5VivCommitFn : Fn :=
  ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64], full_viv_commit_m6_body⟩

def fidStep13S5VivMarkGarbFn : Fn :=
  ⟨"full_viv_mark_garb_m6", [i64, i32], [], full_viv_mark_garb_m6_body⟩

def fidStep13S5VivDeduceFn : Fn :=
  ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32], full_viv_deduce_m6_body⟩

def fidStep13S5VivFinishFn : Fn :=
  ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64], full_viv_finish_m6_body⟩

def fidStep13S5VivifyTierFn : Fn :=
  ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], full_vivify_tier_m6_hdr_body⟩

def fidStep13S5VivifyFn : Fn :=
  ⟨"full_vivify_m6_hdr", [i64], [i64], full_vivify_m6_hdr_body⟩

def fidStep13S5BackboneKeepFn : Fn :=
  ⟨"full_backbone_keep_m6", [i64, i64], [], full_backbone_keep_m6_body⟩

def fidStep13S5BackbonePropFn : Fn :=
  ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool], full_backbone_prop_m6_body⟩

def fidStep13S5BackboneAnalyzeFn : Fn :=
  ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32], full_backbone_analyze_m6_body⟩

def fidStep13S5BackboneRoundFn : Fn :=
  ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64], full_backbone_round_m6_body⟩

def fidStep13S5BackboneFn : Fn :=
  ⟨"full_backbone_m6", [i64, i64], [i64], full_backbone_m6_body⟩

def fidStep13S5TransLitFn : Fn :=
  ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], full_trans_lit_m6_body⟩

def fidStep13S5TransitiveFn : Fn :=
  ⟨"full_transitive_m6", [i64, i64], [i64], full_transitive_m6_body⟩

def fidStep13S5BRepls : List Fn :=
  [ fidStep13S5VivCommitFn
  , fidStep13S5VivMarkGarbFn
  , fidStep13S5VivDeduceFn
  , fidStep13S5VivFinishFn
  , fidStep13S5VivifyTierFn
  , fidStep13S5VivifyFn
  , fidStep13S5BackboneKeepFn
  , fidStep13S5BackbonePropFn
  , fidStep13S5BackboneAnalyzeFn
  , fidStep13S5BackboneRoundFn
  , fidStep13S5BackboneFn
  , fidStep13S5TransLitFn
  , fidStep13S5TransitiveFn ]

def fidStep13S5BBefores : List (Sym × List Fn) :=
  [ ("full_viv_deduce_m6", [fidStep13S5VivRecomputePromoteFn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem full_viv_recompute_promote_fid_s5_wf :
    Func.Wf fidStep13S5VivRecomputePromoteFn.body := by t_wf_reify
theorem full_viv_commit_m6_s5_wf : Func.Wf fidStep13S5VivCommitFn.body := by t_wf_reify
theorem full_viv_mark_garb_m6_s5_wf : Func.Wf fidStep13S5VivMarkGarbFn.body := by t_wf_reify
theorem full_viv_deduce_m6_s5_wf : Func.Wf fidStep13S5VivDeduceFn.body := by t_wf_reify
theorem full_viv_finish_m6_s5_wf : Func.Wf fidStep13S5VivFinishFn.body := by t_wf_reify
theorem full_vivify_tier_m6_hdr_s5_wf : Func.Wf fidStep13S5VivifyTierFn.body := by t_wf_reify
theorem full_vivify_m6_hdr_s5_wf : Func.Wf fidStep13S5VivifyFn.body := by t_wf_reify
theorem full_backbone_keep_m6_s5_wf : Func.Wf fidStep13S5BackboneKeepFn.body := by t_wf_reify
theorem full_backbone_prop_m6_s5_wf : Func.Wf fidStep13S5BackbonePropFn.body := by t_wf_reify
theorem full_backbone_analyze_m6_s5_wf :
    Func.Wf fidStep13S5BackboneAnalyzeFn.body := by t_wf_reify
theorem full_backbone_round_m6_s5_wf : Func.Wf fidStep13S5BackboneRoundFn.body := by t_wf_reify
theorem full_backbone_m6_s5_wf : Func.Wf fidStep13S5BackboneFn.body := by t_wf_reify
theorem full_trans_lit_m6_s5_wf : Func.Wf fidStep13S5TransLitFn.body := by t_wf_reify
theorem full_transitive_m6_s5_wf : Func.Wf fidStep13S5TransitiveFn.body := by t_wf_reify

theorem fidStep13S5BRepls_wf : ∀ f ∈ fidStep13S5BRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S5BRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_viv_commit_m6_s5_wf
  · exact full_viv_mark_garb_m6_s5_wf
  · exact full_viv_deduce_m6_s5_wf
  · exact full_viv_finish_m6_s5_wf
  · exact full_vivify_tier_m6_hdr_s5_wf
  · exact full_vivify_m6_hdr_s5_wf
  · exact full_backbone_keep_m6_s5_wf
  · exact full_backbone_prop_m6_s5_wf
  · exact full_backbone_analyze_m6_s5_wf
  · exact full_backbone_round_m6_s5_wf
  · exact full_backbone_m6_s5_wf
  · exact full_trans_lit_m6_s5_wf
  · exact full_transitive_m6_s5_wf

theorem fidStep13S5BBefores_wf :
    ∀ h ∈ fidStep13S5BBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep13S5BBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl
  exact full_viv_recompute_promote_fid_s5_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone
