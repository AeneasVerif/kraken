module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M6 Vivification Subsumption/Instantiation &
Multi-Level Backbone / Sorted Transitive Parity (`FullM6VivBackbone`)

Standalone C0 drop-in override module preserving the unchanged `144`-word `FullHdr`
layout for vivification, multi-level backbone, and transitive reduction:

1. **Flag maintenance & OOM guards**:
   - `full_add_bin_m6`: sets `FL_TRANS | FL_BONE0 | FL_BONE1` on both endpoints when adding a
     binary clause (`Full.fullAddBinSpec`).
   - `full_init_fresh_var_m6`: initializes fresh BVA variables with `FL_TRANS | FL_BONE0 |
     FL_BONE1` alongside existing active/elim/sweep/factor flags (`Full.fullInitFreshVarSpec`,
     `FullBvaHeap.fullInitFreshVarHeapSpec`).
   - `full_probe_assume_pair_m6`: fixes OOM swallow in `Full3.full_probe_assume_pair`
     (`Full.fullProbeAssumePairSpec`).
2. **Vivification parity**:
   - Preserves `full_viv_reestablish_m6` 2WL invariant backtrack repair.
   - `full_viv_deduce_m6` with binary/large subsumption check (`full_viv_subsumes_bin_m6`,
     `full_viv_subsumes_cl_m6`), redundant subsumer promotion & glue lowering in
     `full_viv_finish_m6`.
   - Same-size `vivified_implied` & `vivified_asym` deletion via `full_viv_mark_garb_m6`.
   - `full_viv_best_implied_m6` min-`tpos` literal selection (`better_implied`).
   - `full_viv_inst_m6` + `full_viv_inst_check_m6`: instantiation strengthening with 1-step
     resolution verification.
   - Prefix-preserving commit (`full_viv_commit_m6`, `olen - 2` on conflict, keep level on
     implied), `full_viv_watch_rank_m6` + `full_viv_best_watch_m6` (`swap_first_literal_with_
     best_watch`), glue promotion (`glue >= olen -> olen - 1`), NO backwards red->irred
     promotion, and `full_viv_unreason_m6` trail guard.
   - True literal occurrence counting (`full_viv_count_m6` into `tarjan_reach`), prefix sort
     (`full_viv_sort_counts_m6`), `[!PH_VIV, PH_VIV]` schedule collection & sorting, OOM
     propagation in `full_viv_simplify_m6` & `full_viv_l0_simp_m6`, `PH_VIV` set only on
     non-aborting completion, and canonical `full_vivify_m6` (`fullVivifyFastSpec`).
3. **Backbone & transitive parity**:
   - `full_prioritize_binaries_m6`: partitions binary watches ahead of large watches in place.
   - Multi-level 1UIP backbone (`full_backbone_sched_m6`, `full_backbone_keep_m6`,
     `full_backbone_unwind_m6`, `full_backbone_prop_m6`, `full_backbone_analyze_m6`,
     `full_backbone_round_m6`, `full_backbone_m6` -> `FullM3Backbone.fullBackboneSpec`) with
     cache-line tick accounting, `stop_early`, up to `100` rounds, and persistent `FL_BONE*`.
   - Sorted transitive reduction (`full_trans_lit_m6`, `full_trans_sort_m6`,
     `full_transitive_m6` -> `FullFastBveBudgets.fullTransitiveFastSpec`) with `dst > src`,
     inner-BFS cache-line ticks, `stop_early`, and post-pair `FL_TRANS` clearing.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6VivBackbone "
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

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_VIV  0x00100000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_FACT_P  32u
#define FL_FACT_N  64u
#define FL_BONE0   128u
#define FL_BONE1   256u
#define FL_TRANS   512u
#define FL_SWEEP   1024u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_delete_bin_side(FullHdr *h, u32 lit, u32 other);
extern void full_wstack_defrag(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref);
extern u64 full_propagate(FullHdr *h);
extern u64 full_probe_prop(FullHdr *h);
extern u64 full_probe_flush_hbr(FullHdr *h, u64 hbr_n);
extern u64 full_analyze(FullHdr *h);

u64 full_add_bin_m6(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == (b ^ 1u)) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[a] > (i8)0 || vals[b] > (i8)0) { return 0ULL; }
  if (vals[a] < (i8)0 && vals[b] < (i8)0) { h->inconsistent = 1ULL; return 20ULL; }
  if (vals[a] < (i8)0 || a == b) { full_assign_lvl(h, b, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (vals[b] < (i8)0) { full_assign_lvl(h, a, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (full_has_bin(h, a, b)) { return 0ULL; }
  u32 b0 = (b & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (a & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, a, b0, 0u, 1u) || !full_watch_push(h, b, b1, 0u, 1u)) {
    h->oom = 1ULL; return 2ULL;
  }
  u32 *fl = (u32 *)h->flags;
  u32 va = a >> 1; u32 vb = b >> 1;
  u32 addf = FL_TRANS | FL_BONE0 | FL_BONE1;
  fl[va] = fl[va] | addf;
  fl[vb] = fl[vb] | addf;
  h->num_binary = h->num_binary + 1ULL;
  return 1ULL;
}

void full_init_fresh_var_m6(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases; u32 *wvec = (u32 *)h->watch_vec; u64 *sc = (u64 *)h->score;
  u64 wb = (u64)fv << 2;
  wvec[wb] = 0u; wvec[wb + 1ULL] = 0u; wvec[wb + 2ULL] = 0u; wvec[wb + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)1; lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu;
  ps[fv] = 0xFFFFFFFFu; sc[fv] = 0ULL;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP |
           FL_FACT_P | FL_FACT_N | FL_TRANS | FL_BONE0 | FL_BONE1;
  u32 ol = (u32)h->q_last; qp[fv] = ol; qn[fv] = 0xFFFFFFFFu;
  if ((u64)ol < h->cur_vars) { qn[ol] = fv; } else { h->q_first = (u64)fv; }
  h->q_last = (u64)fv; h->q_cur_stamp = h->q_cur_stamp + 1ULL; qs[fv] = (u32)h->q_cur_stamp;
  h->unassigned = h->unassigned + 1ULL;
}

u64 full_probe_assume_pair_m6(FullHdr *h, u32 lit) {
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u32 *trl = (u32 *)h->trail; u8 *lm = (u8 *)h->lit_mark;
  u32 *sav = (u32 *)h->work_stk1; u64 cv = h->cur_vars;
  h->tmp_cnt = 0ULL; u64 t0 = h->trail_end;
  ftrl[1] = (u32)t0; fdec[1] = lit; h->cur_level = 1ULL;
  full_assign(h, lit, 0xFFFFFFFFu);
  u64 pr = full_probe_prop(h);
  u64 hbr0 = h->tmp_cnt;
  if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
  if (pr == 1ULL) {
    u64 ast = full_analyze(h);
    if (ast == 20ULL) { return 20ULL; }
    if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
    u64 pp = full_propagate(h);
    if (pp == 1ULL) { return 20ULL; }
    if (pp == 2ULL) { return 2ULL; }
    return full_probe_flush_hbr(h, hbr0);
  }
  u64 sn = 0ULL; u64 k = t0;
  while (k < h->trail_end && sn < cv) {
    u32 tl = trl[k]; lm[tl] = (u8)1; sav[sn] = tl; sn = sn + 1ULL; k = k + 1ULL;
  }
  full_backtrack(h, 0ULL);
  u64 fh = full_probe_flush_hbr(h, hbr0);
  if (fh != 1ULL) {
    k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
    return fh;
  }
  i8 *vals = (i8 *)h->values; u32 *bones = (u32 *)h->tmp_lits; u64 bn = 0ULL;
  h->tmp_cnt = 0ULL;
  if (vals[lit ^ 1u] == (i8)0) {
    u64 t1 = h->trail_end;
    ftrl[1] = (u32)t1; fdec[1] = lit ^ 1u; h->cur_level = 1ULL;
    full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
    u64 pr2 = full_probe_prop(h);
    u64 hbr1 = h->tmp_cnt;
    if (pr2 == 2ULL) {
      k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
      full_backtrack(h, 0ULL); return 2ULL;
    }
    if (pr2 == 1ULL) {
      k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
      u64 ast = full_analyze(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      u64 pp = full_propagate(h);
      if (pp == 1ULL) { return 20ULL; }
      if (pp == 2ULL) { return 2ULL; }
      return full_probe_flush_hbr(h, hbr1);
    }
    if (pr2 == 0ULL) {
      k = t1;
      while (k < h->trail_end && bn < cv) {
        u32 tl = trl[k];
        if (lm[tl] != (u8)0) { bones[bn] = tl; bn = bn + 1ULL; }
        k = k + 1ULL;
      }
    }
    full_backtrack(h, 0ULL);
    h->tmp_cnt = hbr1;
  }
  u64 hbr1 = h->tmp_cnt;
  k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
  k = 0ULL;
  while (k < bn) {
    if (!full_add_unit(h, bones[k])) { return 20ULL; }
    k = k + 1ULL;
  }
  return full_probe_flush_hbr(h, hbr1);
}

void full_viv_unreason_m6(FullHdr *h, u32 cref) {
  if (h->cur_level == 0ULL) { return; }
  u32 *trl = (u32 *)h->trail;
  u32 *rsns = (u32 *)h->reason;
  u64 te = h->trail_end;
  u64 i = 0ULL;
  while (i < te) {
    u32 rsn = rsns[trl[i] >> 1];
    if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) == 0u && rsn == cref) {
      full_backtrack(h, 0ULL);
      return;
    }
    i = i + 1ULL;
  }
}

u64 full_viv_watch_rank_m6(FullHdr *h, u32 lit) {
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  i8 v = vals[lit];
  if (v > (i8)0) { return 0x200000000ULL + (0xFFFFFFFFULL - (u64)lvl[lit >> 1]); }
  if (v == (i8)0) { return 0x100000000ULL; }
  return (u64)lvl[lit >> 1];
}

void full_viv_best_watch_m6(FullHdr *h, u32 olen) {
  u32 *out = (u32 *)h->work_stk2;
  u32 pos = 0u;
  while (pos < 2u && pos < olen) {
    u32 best = pos;
    u64 brank = full_viv_watch_rank_m6(h, out[pos]);
    u32 k = pos + 1u;
    while (k < olen) {
      u64 r = full_viv_watch_rank_m6(h, out[k]);
      if (r > brank) { best = k; brank = r; }
      k = k + 1u;
    }
    if (best != pos) {
      u32 tmp = out[pos];
      out[pos] = out[best];
      out[best] = tmp;
    }
    pos = pos + 1u;
  }
}

u64 full_viv_simplify_m6(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  u32 k = 0u; u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] > (i8)0) {
      full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
      full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
      if ((hdr & PH_RED) != 0u) {
        if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
      } else {
        if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
      }
      return 1ULL;
    }
    if (vals[lit] == (i8)0) { k = k + 1u; }
    i = i + 1u;
  }
  if (k == old_sz) { return 0ULL; }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u32 nsz = 0u; i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] == (i8)0) { ar[(u64)cref + 3ULL + (u64)nsz] = lit; nsz = nsz + 1u; }
    i = i + 1u;
  }
  if (nsz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
  if (nsz == 1u) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    return full_add_unit(h, ar[(u64)cref + 3ULL]) ? 1ULL : 20ULL;
  }
  if (nsz == 2u) {
    u64 br = full_add_bin_m6(h, ar[(u64)cref + 3ULL], ar[(u64)cref + 4ULL]);
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    if ((hdr & PH_RED) != 0u) {
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    } else {
      if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    }
    if (br == 20ULL) { return 20ULL; }
    if (br == 2ULL) { return 2ULL; }
    return 1ULL;
  }
  ar[(u64)cref + 2ULL] = nsz; ar[(u64)cref + 1ULL] = 2u;
  u32 nhdr = hdr;
  if ((nhdr & PH_RED) != 0u) {
    u32 glue = nhdr & PH_GLUE_MASK;
    if (glue >= nsz) {
      nhdr = (nhdr & (~PH_GLUE_MASK)) | ((nsz - 1u) & PH_GLUE_MASK);
    }
  }
  if ((nhdr & PH_SHRK) == 0u) {
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
    nhdr = nhdr | PH_SHRK;
  }
  ar[cref] = nhdr;
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) {
    h->oom = 1ULL; return 2ULL;
  }
  return 0ULL;
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
  }
  h->viv_cnt = h->viv_cnt + 1ULL;
}

bool full_viv_subsumes_bin_m6(FullHdr *h, u32 a, u32 b) {
  u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  bool oka = (lm[a] != (u8)0) || (vals[a] < (i8)0 && lvl[a >> 1] == 0u);
  bool okb = (lm[b] != (u8)0) || (vals[b] < (i8)0 && lvl[b >> 1] == 0u);
  return oka && okb;
}

bool full_viv_subsumes_cl_m6(FullHdr *h, u32 rcr, u32 sz) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 rsz = ar[(u64)rcr + 2ULL];
  if (rsz > sz) { return false; }
  u32 j = 0u;
  while (j < rsz) {
    u32 sl = ar[(u64)rcr + 3ULL + (u64)j];
    if (lm[sl] == (u8)0 && !(vals[sl] < (i8)0 && lvl[sl >> 1] == 0u)) { return false; }
    j = j + 1u;
  }
  return true;
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
      if (full_viv_subsumes_bin_m6(h, a, b)) { h->ant_sz = 0xFFFFFFFFFFFFFFFEULL; }
      if (lvl[a >> 1] > 0u && mrk[a >> 1] == (u8)0 && qlen < cv) {
        mrk[a >> 1] = (u8)1; qstk[qlen] = a >> 1; qlen = qlen + 1ULL;
      }
      if (lvl[b >> 1] > 0u && mrk[b >> 1] == (u8)0 && qlen < cv) {
        mrk[b >> 1] = (u8)1; qstk[qlen] = b >> 1; qlen = qlen + 1ULL;
      }
    } else if ((u64)src_cr + 3ULL <= h->arena_len) {
      if (src_cr != cref) {
        if ((ar[src_cr] & PH_RED) != 0u) { h->res_sz = 1ULL; }
        if (full_viv_subsumes_cl_m6(h, src_cr, sz)) { h->ant_sz = (u64)src_cr; }
      }
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
  u32 *trl = (u32 *)h->trail; u32 *tpos = (u32 *)h->trail_pos;
  while (qi < qlen) {
    u32 v = qstk[qi]; qi = qi + 1ULL;
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) {
      u32 tl = trl[tpos[v]];
      if (tl == implied) { taut = true; }
      else if ((u64)olen < cv) { out[olen] = tl ^ 1u; olen = olen + 1u; }
    } else if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ot = rsn & PW_LIT_MASK;
      if (h->ant_sz == 0xFFFFFFFFFFFFFFFFULL) {
        u32 tl = trl[tpos[v]];
        if (full_viv_subsumes_bin_m6(h, tl, ot)) { h->ant_sz = 0xFFFFFFFFFFFFFFFEULL; }
      }
      u32 ov = ot >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
        mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
      }
    } else if ((u64)rsn + 3ULL <= h->arena_len) {
      if ((ar[rsn] & PH_RED) != 0u) { h->res_sz = 1ULL; }
      if (h->ant_sz == 0xFFFFFFFFFFFFFFFFULL && rsn != cref &&
          full_viv_subsumes_cl_m6(h, rsn, sz)) {
        h->ant_sz = (u64)rsn;
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

u32 full_viv_best_implied_m6(FullHdr *h, u32 sz) {
  u32 *tmp = (u32 *)h->tmp_lits;
  i8 *vals = (i8 *)h->values;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 best = 0xFFFFFFFFu;
  u32 best_pos = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < sz) {
    u32 l = tmp[i];
    if (vals[l] > (i8)0) {
      u32 tp = tpos[l >> 1];
      if (best == 0xFFFFFFFFu || tp < best_pos) {
        best = l; best_pos = tp;
      }
    }
    i = i + 1u;
  }
  return best;
}

void full_viv_reestablish_m6(FullHdr *h, u32 cref) {
  if (h->cur_level == 0ULL) { return; }
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return; }
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  i8 v0 = vals[l0]; i8 v1 = vals[l1];
  u64 lvl0 = (v0 != (i8)0) ? (u64)lvl[l0 >> 1] : 0ULL;
  u64 lvl1 = (v1 != (i8)0) ? (u64)lvl[l1 >> 1] : 0ULL;
  u64 new_lvl = 0ULL;
  if (v0 < (i8)0) {
    if (v1 < (i8)0) { new_lvl = (lvl0 < lvl1) ? lvl0 : lvl1; }
    else if (v1 == (i8)0) { new_lvl = lvl0; }
    else if (lvl0 < lvl1) { new_lvl = lvl0; }
  } else if (v1 < (i8)0) {
    if (v0 == (i8)0) { new_lvl = lvl1; }
    else if (lvl1 < lvl0) { new_lvl = lvl1; }
  }
  if (new_lvl > 0ULL && new_lvl - 1ULL < h->cur_level) {
    full_backtrack(h, new_lvl - 1ULL);
  }
}

bool full_viv_inst_check_m6(FullHdr *h, u32 sz, u32 iolen, u32 not_lit) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *out = (u32 *)h->work_stk2;
  u8 *lm = (u8 *)h->lit_mark;
  u32 k = 0u;
  while (k + 1u < sz) { lm[tmp[k]] = (u8)1; k = k + 1u; }
  bool ok = true;
  u32 i = 0u;
  while (i < iolen) {
    u32 x = out[i];
    if (x != not_lit && lm[x] == (u8)0) { ok = false; break; }
    i = i + 1u;
  }
  k = 0u;
  while (k + 1u < sz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  return ok;
}

u64 full_viv_inst_m6(FullHdr *h, u32 cref, u32 sz) {
  if (h->cur_level == 0ULL || sz < 3u) { return 0ULL; }
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 lit = tmp[sz - 1u];
  if (!(vals[lit] < (i8)0 && (u64)lvl[lit >> 1] == h->cur_level &&
        rsns[lit >> 1] == 0xFFFFFFFFu)) {
    return 0ULL;
  }
  full_backtrack(h, h->cur_level - 1ULL);
  if (vals[lit] != (i8)0) { return 0ULL; }
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  u64 pr = full_propagate_ignore(h, (u64)cref);
  if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
  if (pr != 1ULL) {
    full_backtrack(h, h->cur_level - 1ULL);
    return 0ULL;
  }
  u32 iolen = full_viv_deduce_m6(h, cref, sz, 0xFFFFFFFFu);
  if (iolen == 0xFFFFFFFFu || !full_viv_inst_check_m6(h, sz, iolen, lit ^ 1u)) {
    full_backtrack(h, h->cur_level - 1ULL);
    return 0ULL;
  }
  u32 *out = (u32 *)h->work_stk2;
  u32 nsz = sz - 1u;
  u32 k = 0u;
  while (k < nsz) { out[k] = tmp[k]; k = k + 1u; }
  return full_viv_commit_m6(h, cref, nsz, 0xFFFFFFFFu);
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

void full_viv_sort_counts_m6(FullHdr *h, u32 sz) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u32 i = 1u;
  while (i < sz) {
    u32 x = tmp[i];
    u32 dx = cnt[x];
    u32 j = i;
    while (j > 0u) {
      u32 prev = tmp[j - 1u];
      u32 dp = cnt[prev];
      if (dp > dx || (dp == dx && prev < x)) { break; }
      tmp[j] = prev;
      j = j - 1u;
    }
    tmp[j] = x;
    i = i + 1u;
  }
}

bool full_viv_has_l0_m6(FullHdr *h, u32 cref, u32 sz) {
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[l] != (i8)0 && lvl[l >> 1] == 0u) { return true; }
    i = i + 1u;
  }
  return false;
}

u64 full_viv_l0_simp_m6(FullHdr *h, u32 cref, u32 sz) {
  if (!full_viv_has_l0_m6(h, cref, sz)) { return 0ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  return full_viv_simplify_m6(h, cref);
}

void full_viv_reuse_prefix_m6(FullHdr *h, u32 cref, u32 sz) {
  if (h->cur_level == 0ULL) { return; }
  u32 *tmp = (u32 *)h->tmp_lits; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u64 clvl = h->cur_level; u64 keep_lvl = 0ULL; u32 i = 0u;
  while (i < sz && keep_lvl < clvl) {
    u32 l = tmp[i];
    if (l == (fdec[keep_lvl + 1ULL] ^ 1u)) { keep_lvl = keep_lvl + 1ULL; }
    else if (!(vals[l] < (i8)0 && (u64)lvl[l >> 1] <= keep_lvl)) { break; }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < sz && keep_lvl > 0ULL) {
    u32 l = tmp[j];
    if (vals[l] > (i8)0 && rsns[l >> 1] == cref) {
      u64 rl = (u64)lvl[l >> 1];
      if (rl == 0ULL) { keep_lvl = 0ULL; }
      else if (rl - 1ULL < keep_lvl) { keep_lvl = rl - 1ULL; }
    }
    j = j + 1u;
  }
  if (keep_lvl < clvl) { full_backtrack(h, keep_lvl); }
}

u64 full_viv_clause_m6(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((ar[cref] & PH_GARB) != 0u) { return 1ULL; }
  u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u64 l0r = full_viv_l0_simp_m6(h, cref, sz);
  if (l0r != 0ULL) { return l0r; }
  sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u;
  while (i < sz) { tmp[i] = ar[(u64)cref + 3ULL + (u64)i]; i = i + 1u; }
  full_viv_sort_counts_m6(h, sz);
  full_viv_reuse_prefix_m6(h, cref, sz);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  bool confl = false; u32 implied = 0xFFFFFFFFu;
  i = 0u;
  while (i < sz) {
    u32 lit = tmp[i]; i8 lv = vals[lit];
    if (lv > (i8)0) { implied = full_viv_best_implied_m6(h, sz); break; }
    if (lv == (i8)0) {
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { break; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
      full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
      u64 pr = full_propagate_ignore(h, (u64)cref);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) { confl = true; break; }
      u32 bi = full_viv_best_implied_m6(h, sz);
      if (bi != 0xFFFFFFFFu) { implied = bi; break; }
    }
    i = i + 1u;
  }
  u64 fr = full_viv_finish_m6(h, cref, sz, confl, implied, i == sz);
  if (fr != 2ULL && (ar[cref] & PH_GARB) == 0u) { ar[cref] = ar[cref] | PH_VIV; }
  return fr;
}

bool full_viv_tier_match_m6(FullHdr *h, u32 hdr, u64 tier_mode) {
  bool is_red = ((hdr & PH_RED) != 0u);
  u64 glue = (u64)(hdr & PH_GLUE_MASK);
  if (tier_mode == 0ULL) { return !is_red; }
  if (tier_mode == 1ULL) { return is_red && glue <= h->tier1; }
  if (tier_mode == 2ULL) { return is_red && glue > h->tier1 && glue <= h->tier2; }
  return is_red && glue > h->tier2;
}

u64 full_viv_collect_m6(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena; u32 *rr = (u32 *)h->red_refs;
  u64 bmax = h->red_cap / 3ULL; u64 bn = 0ULL;
  u64 pass = 0ULL;
  while (pass < 2ULL && bn < bmax) {
    u64 p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      u64 np = (u64)full_arena_next(h, (u32)p);
      if ((hdr & PH_GARB) == 0u) {
        bool want = (pass == 0ULL) ? ((hdr & PH_VIV) == 0u) : ((hdr & PH_VIV) != 0u);
        if (want && full_viv_tier_match_m6(h, hdr, tier_mode) && bn < bmax) {
          rr[bn * 3ULL] = (u32)p;
          bn = bn + 1ULL;
        }
      }
      p = np;
    }
    pass = pass + 1ULL;
  }
  return bn;
}

void full_viv_count_m6(FullHdr *h, u64 bn) {
  u64 nlits = h->cur_vars << 1;
  u32 *cnt = (u32 *)h->tarjan_reach;
  u64 l = 0ULL;
  while (l < nlits) { cnt[l] = 0u; l = l + 1ULL; }
  u32 *ar = (u32 *)h->arena; u32 *rr = (u32 *)h->red_refs;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi * 3ULL];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k = 0u;
    while (k < sz) {
      u32 lit = ar[(u64)cr + 3ULL + (u64)k];
      if ((u64)lit < nlits && cnt[lit] < 0xFFFFFFFFu) { cnt[lit] = cnt[lit] + 1u; }
      k = k + 1u;
    }
    bi = bi + 1ULL;
  }
}

void full_viv_keys_m6(FullHdr *h, u64 bn) {
  u32 *ar = (u32 *)h->arena; u32 *cnt = (u32 *)h->tarjan_reach;
  u32 *rr = (u32 *)h->red_refs; u64 nlits = h->cur_vars << 1;
  u64 bi = 0ULL;
  while (bi < bn) {
    u32 cr = rr[bi * 3ULL];
    u32 sz = ar[(u64)cr + 2ULL];
    u32 k0 = 0xFFFFFFFFu; u32 d0 = 0u;
    u32 k1 = 0xFFFFFFFFu; u32 d1 = 0u;
    u32 j = 0u;
    while (j < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)j];
      u32 dl = ((u64)l < nlits) ? cnt[l] : 0u;
      if (k0 == 0xFFFFFFFFu || dl > d0 || (dl == d0 && l < k0)) {
        k1 = k0; d1 = d0; k0 = l; d0 = dl;
      } else if (k1 == 0xFFFFFFFFu || dl > d1 || (dl == d1 && l < k1)) {
        k1 = l; d1 = dl;
      }
      j = j + 1u;
    }
    rr[bi * 3ULL + 1ULL] = k0;
    rr[bi * 3ULL + 2ULL] = k1;
    bi = bi + 1ULL;
  }
}

void full_viv_sort_sched_m6(FullHdr *h, u64 bn) {
  u32 *rr = (u32 *)h->red_refs; u32 *ar = (u32 *)h->arena;
  u32 *cnt = (u32 *)h->tarjan_reach; u64 nlits = h->cur_vars << 1;
  u64 gap = bn >> 1;
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < bn) {
      u64 sb = si * 3ULL;
      u32 cr = rr[sb]; u32 k0 = rr[sb + 1ULL]; u32 k1 = rr[sb + 2ULL];
      bool v0 = ((ar[cr] & PH_VIV) != 0u);
      u32 dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u;
      u32 dk1 = ((u64)k1 < nlits) ? cnt[k1] : 0u;
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap; u64 pb = pj * 3ULL;
        u32 pcr = rr[pb]; u32 pk0 = rr[pb + 1ULL]; u32 pk1 = rr[pb + 2ULL];
        bool pv0 = ((ar[pcr] & PH_VIV) != 0u);
        u32 dpk0 = ((u64)pk0 < nlits) ? cnt[pk0] : 0u;
        u32 dpk1 = ((u64)pk1 < nlits) ? cnt[pk1] : 0u;
        if (!pv0 && v0) { break; }
        if (pv0 == v0) {
          if (dpk0 > dk0) { break; }
          if (dpk0 == dk0) {
            if (pk0 < k0) { break; }
            if (pk0 == k0) {
              if (dpk1 > dk1) { break; }
              if (dpk1 == dk1) {
                if (pk1 < k1 || (pk1 == k1 && pcr <= cr)) { break; }
              }
            }
          }
        }
        u64 jb = sj * 3ULL;
        rr[jb] = pcr; rr[jb + 1ULL] = pk0; rr[jb + 2ULL] = pk1;
        sj = pj;
      }
      u64 fb = sj * 3ULL;
      rr[fb] = cr; rr[fb + 1ULL] = k0; rr[fb + 2ULL] = k1;
      si = si + 1ULL;
    }
    gap = gap >> 1;
  }
}

void full_viv_clear_tier_m6(FullHdr *h, u64 tier_mode) {
  u32 *ar = (u32 *)h->arena;
  u64 q = 0ULL;
  while (q < h->arena_len) {
    u32 hdr = ar[q];
    if ((hdr & (PH_GARB | PH_VIV)) == PH_VIV) {
      if (full_viv_tier_match_m6(h, hdr, tier_mode)) { ar[q] = hdr & (~PH_VIV); }
    }
    q = (u64)full_arena_next(h, (u32)q);
  }
}

u64 full_vivify_m6(FullHdr *h, u64 tier_mode, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 start_ticks = h->search_ticks;
  u64 delta = (start_ticks > h->fwd_sub_cnt) ? (start_ticks - h->fwd_sub_cnt) : 0ULL;
  u64 eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta;
  u64 base_eff = eff_ref / 100ULL;
  u64 tick_cap = (tier_mode == 3ULL) ? base_eff : (base_eff * 3ULL);
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
         (h->search_ticks - start_ticks) < tick_cap) {
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

bool full_prioritize_binaries_m6(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 scap = h->scratch_cap;
  bool all_prio = true;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz > 1ULL) {
      if (sz > scap) {
        all_prio = false;
      } else {
        u64 end = off + sz;
        u64 p = off;
        u64 q = off;
        u64 ln = 0ULL;
        while (p < end) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) {
            wstk[q] = w0; q = q + 1ULL;
          } else if (p < end) {
            u32 cr = wstk[p]; p = p + 1ULL;
            scr[ln] = w0; scr[ln + 1ULL] = cr; ln = ln + 2ULL;
          }
        }
        u64 k = 0ULL;
        while (k < ln) { wstk[q + k] = scr[k]; k = k + 1ULL; }
      }
    }
    l = l + 1ULL;
  }
  return all_prio;
}

u64 full_backbone_sched_m6(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *cands = (u32 *)h->work_stk1;
  u64 cand_n = 0ULL;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if ((fl[v] & FL_BONE0) != 0u) { cands[cand_n] = (u32)(v << 1); cand_n = cand_n + 1ULL; }
      if ((fl[v] & FL_BONE1) != 0u) {
        cands[cand_n] = (u32)((v << 1) | 1ULL); cand_n = cand_n + 1ULL;
      }
    }
    v = v + 1ULL;
  }
  if (cand_n == 0ULL) {
    v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        fl[v] = fl[v] | FL_BONE0 | FL_BONE1;
        cands[cand_n] = (u32)(v << 1); cand_n = cand_n + 1ULL;
        cands[cand_n] = (u32)((v << 1) | 1ULL); cand_n = cand_n + 1ULL;
      }
      v = v + 1ULL;
    }
  }
  return cand_n;
}

void full_backbone_keep_m6(FullHdr *h, u64 cand_n) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *cands = (u32 *)h->work_stk1;
  u32 mask = ~(FL_BONE0 | FL_BONE1);
  u64 v = 0ULL;
  while (v < cv) { fl[v] = fl[v] & mask; v = v + 1ULL; }
  u64 i = 0ULL;
  while (i < cand_n) {
    u32 lit = cands[i];
    if (vals[lit] == (i8)0) {
      u32 lv = lit >> 1;
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
  while (prop < h->trail_end && ticks > 0ULL) {
    u32 lit = trl[prop]; prop = prop + 1ULL;
    u32 not_lit = lit ^ 1u;
    u64 off = (u64)wvec[(u64)not_lit << 1];
    u64 end = off + (u64)wvec[((u64)not_lit << 1) + 1ULL];
    ticks = ticks - 1ULL;
    u64 q = off;
    while (q < end) {
      u32 qw = wstk[q];
      if ((qw & PW_BIN_FLAG) == 0u) {
        if (stop_early) { break; }
        q = q + 2ULL;
        if (((q - off) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
        continue;
      }
      q = q + 1ULL;
      if (((q - off) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
      u32 ot = qw & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        i8 ov = vals[ot];
        if (ov < (i8)0) {
          h->confl_lit0 = (u64)not_lit;
          h->confl_lit1 = (u64)ot;
          h->ant_sz = ticks;
          return false;
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
  }
  h->ant_sz = ticks;
  return true;
}

u32 full_backbone_analyze_m6(FullHdr *h, u32 c0, u32 c1, u64 saved) {
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u8 *mrk = (u8 *)h->mark;
  u32 lv1 = lvl[c1 >> 1];
  if (lv1 == 0u) { return c0 ^ 1u; }
  if ((u64)lv1 != h->cur_level) { return 0xFFFFFFFFu; }
  if (c0 == c1) { return c0 ^ 1u; }
  mrk[c0 >> 1] = (u8)1; mrk[c1 >> 1] = (u8)1;
  u64 t = h->trail_end;
  while (t > saved) {
    t = t - 1ULL;
    u32 z = trl[t]; u32 zv = z >> 1;
    if (mrk[zv] == (u8)0) { continue; }
    mrk[zv] = (u8)0;
    u32 rsn = rsns[zv];
    if ((rsn & PW_BIN_FLAG) == 0u) { break; }
    u32 p = (rsn & PW_LIT_MASK) ^ 1u;
    u32 pv = p >> 1;
    if (mrk[pv] != (u8)0) {
      mrk[pv] = (u8)0;
      return p;
    }
    mrk[pv] = (u8)1;
  }
  u64 k = saved;
  while (k < h->trail_end) { mrk[trl[k] >> 1] = (u8)0; k = k + 1ULL; }
  return 0xFFFFFFFFu;
}

u64 full_backbone_round_m6(FullHdr *h, u64 cand_n, bool stop_early) {
  u64 saved0 = h->trail_end; u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *cands = (u32 *)h->work_stk1; u32 *units = (u32 *)h->work_stk2;
  u64 ucnt = 0ULL; u64 keep = 0ULL; u64 ci = 0ULL; bool broken = false;
  while (ci < cand_n && h->ant_sz > 0ULL && h->trail_end < h->max_vars) {
    u32 probe = cands[ci]; ci = ci + 1ULL;
    i8 pv = vals[probe];
    if (pv > (i8)0) { continue; }
    if (pv < (i8)0) { cands[keep] = probe; keep = keep + 1ULL; continue; }
    u64 saved = h->trail_end; u64 old_lvl = h->cur_level;
    u64 nlvl = old_lvl + 1ULL;
    if (nlvl > h->max_vars) { cands[keep] = probe; keep = keep + 1ULL; broken = true; break; }
    h->cur_level = nlvl;
    vals[probe] = (i8)1; vals[probe ^ 1u] = (i8)(-1);
    lvl[probe >> 1] = (u32)nlvl; rsns[probe >> 1] = 0xFFFFFFFFu;
    trl[saved] = probe; h->trail_end = saved + 1ULL;
    if (full_backbone_prop_m6(h, saved, stop_early)) {
      if (h->ant_sz == 0ULL) {
        full_backbone_unwind_m6(h, saved, old_lvl);
        cands[keep] = probe; keep = keep + 1ULL;
        broken = true; break;
      }
      continue;
    }
    u32 c0 = (u32)h->confl_lit0; u32 c1 = (u32)h->confl_lit1;
    u32 uip = full_backbone_analyze_m6(h, c0, c1, saved);
    full_backbone_unwind_m6(h, saved, old_lvl);
    if (uip == 0xFFFFFFFFu) {
      cands[keep] = probe; keep = keep + 1ULL; continue;
    }
    u32 not_uip = uip ^ 1u;
    if (ucnt < nlits) { units[ucnt] = not_uip; ucnt = ucnt + 1ULL; }
    if (uip != probe) { cands[keep] = probe; keep = keep + 1ULL; }
    i8 nv = vals[not_uip];
    if (nv < (i8)0) { broken = true; break; }
    if (nv == (i8)0 && h->trail_end < h->max_vars) {
      u64 ustart = h->trail_end;
      h->cur_level = 0ULL;
      vals[not_uip] = (i8)1; vals[uip] = (i8)(-1);
      lvl[not_uip >> 1] = 0u; rsns[not_uip >> 1] = 0xFFFFFFFFu;
      trl[ustart] = not_uip; h->trail_end = ustart + 1ULL;
      bool pok = full_backbone_prop_m6(h, ustart, stop_early);
      h->cur_level = old_lvl;
      if (!pok || h->ant_sz == 0ULL) { broken = true; break; }
    }
  }
  while (ci < cand_n) {
    u32 rem = cands[ci];
    if (broken || vals[rem] <= (i8)0) { cands[keep] = rem; keep = keep + 1ULL; }
    ci = ci + 1ULL;
  }
  full_backbone_unwind_m6(h, saved0, 0ULL);
  h->res_sz = ucnt;
  return keep;
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
  u64 res = 1ULL;
  u64 round = 0ULL;
  while (round < 100ULL && cand_n > 0ULL && h->ant_sz > 0ULL &&
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
          if (((q - loff) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
          continue;
        }
        if (nl == src && q == p) { q = q + 1ULL; continue; }
        q = q + 1ULL;
        if (((q - loff) & 15ULL) == 0ULL && ticks > 0ULL) { ticks = ticks - 1ULL; }
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

void full_trans_sort_m6(FullHdr *h, u64 n) {
  u32 *probes = (u32 *)h->work_stk1;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  bool stab = (h->stable != 0ULL);
  u64 gap = n >> 1;
  while (gap > 0ULL) {
    u64 si = gap;
    while (si < n) {
      u32 v = probes[si];
      u64 kv = stab ? sc[v] : (u64)qs[v];
      u64 sj = si;
      while (sj >= gap) {
        u64 pj = sj - gap;
        u32 pv = probes[pj];
        u64 kpv = stab ? sc[pv] : (u64)qs[pv];
        if (kpv > kv || (kpv == kv && pv <= v)) { break; }
        probes[sj] = pv;
        sj = pj;
      }
      probes[sj] = v;
      si = si + 1ULL;
    }
    gap = gap >> 1;
  }
}

u64 full_transitive_m6(FullHdr *h, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 cv = h->cur_vars;
  if (h->num_binary == 0ULL || tick_lim == 0ULL || cv == 0ULL) {
    h->probing = 0ULL; return 1ULL;
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
  h->probing = 0ULL;
  return res;
}
"

/-- Canonical external callee signatures referenced by `m6VivBackbone_fns` (`15` externs). -/
def m6VivBackboneExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_delete_bin_side", [i64, i32, i32], []⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_probe_prop", [i64], [i64]⟩
  , ⟨"full_probe_flush_hbr", [i64, i64], [i64]⟩
  , ⟨"full_analyze", [i64], [i64]⟩ ]

/-- Standalone M6 vivification/backbone module (`40` functions + `15` externs, `0` exits). -/
def m6VivBackboneModule : LeanQbe.T.Module :=
  { fns := m6VivBackbone_fns, externs := m6VivBackboneExterns, exits := [] }

theorem full_add_bin_m6_wf : Func.Wf full_add_bin_m6_body := by t_wf_reify
theorem full_init_fresh_var_m6_wf : Func.Wf full_init_fresh_var_m6_body := by t_wf_reify
theorem full_probe_assume_pair_m6_wf : Func.Wf full_probe_assume_pair_m6_body := by t_wf_reify
theorem full_viv_unreason_m6_wf : Func.Wf full_viv_unreason_m6_body := by t_wf_reify
theorem full_viv_watch_rank_m6_wf : Func.Wf full_viv_watch_rank_m6_body := by t_wf_reify
theorem full_viv_best_watch_m6_wf : Func.Wf full_viv_best_watch_m6_body := by t_wf_reify
theorem full_viv_simplify_m6_wf : Func.Wf full_viv_simplify_m6_body := by t_wf_reify
theorem full_viv_commit_m6_wf : Func.Wf full_viv_commit_m6_body := by t_wf_reify
theorem full_viv_mark_garb_m6_wf : Func.Wf full_viv_mark_garb_m6_body := by t_wf_reify
theorem full_viv_subsumes_bin_m6_wf : Func.Wf full_viv_subsumes_bin_m6_body := by t_wf_reify
theorem full_viv_subsumes_cl_m6_wf : Func.Wf full_viv_subsumes_cl_m6_body := by t_wf_reify
theorem full_viv_deduce_m6_wf : Func.Wf full_viv_deduce_m6_body := by t_wf_reify
theorem full_viv_best_implied_m6_wf : Func.Wf full_viv_best_implied_m6_body := by t_wf_reify
theorem full_viv_reestablish_m6_wf : Func.Wf full_viv_reestablish_m6_body := by t_wf_reify
theorem full_viv_inst_check_m6_wf : Func.Wf full_viv_inst_check_m6_body := by t_wf_reify
theorem full_viv_inst_m6_wf : Func.Wf full_viv_inst_m6_body := by t_wf_reify
theorem full_viv_finish_m6_wf : Func.Wf full_viv_finish_m6_body := by t_wf_reify
theorem full_viv_sort_counts_m6_wf : Func.Wf full_viv_sort_counts_m6_body := by t_wf_reify
theorem full_viv_has_l0_m6_wf : Func.Wf full_viv_has_l0_m6_body := by t_wf_reify
theorem full_viv_l0_simp_m6_wf : Func.Wf full_viv_l0_simp_m6_body := by t_wf_reify
theorem full_viv_reuse_prefix_m6_wf : Func.Wf full_viv_reuse_prefix_m6_body := by t_wf_reify
theorem full_viv_clause_m6_wf : Func.Wf full_viv_clause_m6_body := by t_wf_reify
theorem full_viv_tier_match_m6_wf : Func.Wf full_viv_tier_match_m6_body := by t_wf_reify
theorem full_viv_collect_m6_wf : Func.Wf full_viv_collect_m6_body := by t_wf_reify
theorem full_viv_count_m6_wf : Func.Wf full_viv_count_m6_body := by t_wf_reify
theorem full_viv_keys_m6_wf : Func.Wf full_viv_keys_m6_body := by t_wf_reify
theorem full_viv_sort_sched_m6_wf : Func.Wf full_viv_sort_sched_m6_body := by t_wf_reify
theorem full_viv_clear_tier_m6_wf : Func.Wf full_viv_clear_tier_m6_body := by t_wf_reify
theorem full_vivify_m6_wf : Func.Wf full_vivify_m6_body := by t_wf_reify
theorem full_prioritize_binaries_m6_wf : Func.Wf full_prioritize_binaries_m6_body := by t_wf_reify
theorem full_backbone_sched_m6_wf : Func.Wf full_backbone_sched_m6_body := by t_wf_reify
theorem full_backbone_keep_m6_wf : Func.Wf full_backbone_keep_m6_body := by t_wf_reify
theorem full_backbone_unwind_m6_wf : Func.Wf full_backbone_unwind_m6_body := by t_wf_reify
theorem full_backbone_prop_m6_wf : Func.Wf full_backbone_prop_m6_body := by t_wf_reify
theorem full_backbone_analyze_m6_wf : Func.Wf full_backbone_analyze_m6_body := by t_wf_reify
theorem full_backbone_round_m6_wf : Func.Wf full_backbone_round_m6_body := by t_wf_reify
theorem full_backbone_m6_wf : Func.Wf full_backbone_m6_body := by t_wf_reify
theorem full_trans_lit_m6_wf : Func.Wf full_trans_lit_m6_body := by t_wf_reify
theorem full_trans_sort_m6_wf : Func.Wf full_trans_sort_m6_body := by t_wf_reify
theorem full_transitive_m6_wf : Func.Wf full_transitive_m6_body := by t_wf_reify

theorem m6VivBackbone_fns_wf : ∀ f ∈ m6VivBackbone_fns, f.Wf := by
  simp only [m6VivBackbone_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_add_bin_m6_wf, full_init_fresh_var_m6_wf, full_probe_assume_pair_m6_wf,
    full_viv_unreason_m6_wf, full_viv_watch_rank_m6_wf, full_viv_best_watch_m6_wf,
    full_viv_simplify_m6_wf, full_viv_commit_m6_wf, full_viv_mark_garb_m6_wf,
    full_viv_subsumes_bin_m6_wf, full_viv_subsumes_cl_m6_wf, full_viv_deduce_m6_wf,
    full_viv_best_implied_m6_wf, full_viv_reestablish_m6_wf, full_viv_inst_check_m6_wf,
    full_viv_inst_m6_wf, full_viv_finish_m6_wf, full_viv_sort_counts_m6_wf,
    full_viv_has_l0_m6_wf, full_viv_l0_simp_m6_wf, full_viv_reuse_prefix_m6_wf,
    full_viv_clause_m6_wf, full_viv_tier_match_m6_wf, full_viv_collect_m6_wf,
    full_viv_count_m6_wf, full_viv_keys_m6_wf, full_viv_sort_sched_m6_wf,
    full_viv_clear_tier_m6_wf, full_vivify_m6_wf, full_prioritize_binaries_m6_wf,
    full_backbone_sched_m6_wf, full_backbone_keep_m6_wf, full_backbone_unwind_m6_wf,
    full_backbone_prop_m6_wf, full_backbone_analyze_m6_wf, full_backbone_round_m6_wf,
    full_backbone_m6_wf, full_trans_lit_m6_wf, full_trans_sort_m6_wf, full_transitive_m6_wf⟩

theorem m6VivBackbone_acyclic : m6VivBackboneModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
