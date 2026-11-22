module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M5 Wave 1 (`PR-W1A`): Core Heuristics, Probing Isolation & Phases (`FullM5HeurCore`)

Standalone drop-in C0 overrides off `main @ 39bf9969` (`0` edits to `Full1..3`, `FullM4*`, or
`FullHdr`), covering `RC-09`, `RC-10`, and `RC-12`:
1. **Tier-1/2 `used = 31` (`RC-09`):**
   - `full_analyze_rsn_m5`: unconditionally sets `used = 31u` on all redundant reasons
     (`deduce.c:14-27`) and allows `glue > 1` promotion.
   - `full_otfs_subsume_m5`: clamps surviving redundant `glue <= min(c->glue, old_cr->glue)` and
     decrements `num_irred`/`num_redundant` on `PH_GARB` (`strengthen.c:156-187`).
   - `full_eager_subsume_m5`: caps window at `4` with `flush_last_learned` compaction
     (`learn.c:133-195`).
   - `full_learn_clause_m5`: initializes `used = 31u` (`ar[new_ref] |= 31u << 27`) on every newly
     learned large clause (`learn.c:109-110`).
2. **Probing isolation & OTFS bump (`RC-10`):**
   - `full_bump_analyzed_m5`: guards bumping + `full_bump_decay` on `h->probing == 0ULL`, checks
     `FL_ACTIVE`, and skips `full_queue_mtf` when `stable != 0`.
   - `full_restore_bump_ana_m5` + `full_analyze_m5`: guards `full_bump_analyzed`, `full_tick_rel`,
     and `full_ema_update` with `h->probing == 0ULL`; writes OTFS asserting literal to `tmp[0]`
     before bumping; runs regular `full_bump_analyzed` *after* `full_min_shrink`.
3. **Target/best phases & warmup (`RC-12`):**
   - `full_save_target_best_m5`: guards `ptgt[k]` / `pbst[k]` writes with `tv != (i8)0`
     (`phases.c:48-68`).
   - `full_backtrack_raw_m5` + `full_backtrack_m5`: unwinds 1 level before saving target/best
     phases in stable non-probing mode (`backtrack.c:150-161`).
   - `full_warmup_m5`: preserves `ph[v]` saving (does NOT set `probing = 1ULL`), propagates beyond
     conflicts (`warmup.c:16-28`), unwinds via `full_backtrack_raw_m5`, and restores `search_ticks`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5HeurCore

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5HeurCore "
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
#define PH_GARB      0x00080000u
#define PH_RED       0x00400000u
#define PW_BIN_FLAG  0x80000000u
#define PW_LIT_MASK  0x7FFFFFFFu
#define FL_ACTIVE    1u

extern void full_heap_push(FullHdr *h, u32 v);
extern void full_save_target_best(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_analyze_lit(FullHdr *h, u32 lit, u32 skip_var);
extern void full_bump_var(FullHdr *h, u32 v);
extern void full_queue_mtf(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_bump_analyzed(FullHdr *h);
extern void full_clear_ana(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_reduce(FullHdr *h, bool force);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern void full_eager_subsume(FullHdr *h, u64 new_ref);
extern u64 full_one_lit_confl(FullHdr *h);
extern u64 full_deduce_1uip(FullHdr *h);
extern void full_min_shrink(FullHdr *h);
extern void full_tick_rel(FullHdr *h);
extern void full_ema_update(FullHdr *h, u64 glue);
extern u64 full_learn_clause(FullHdr *h, u64 glue);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern u64 full_propagate(FullHdr *h);

void full_save_target_best_m5(FullHdr *h) {
  if (h->probing != 0ULL || h->stable == 0ULL) { return; }
  i8 *vals = (i8 *)h->values;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 assigned = h->trail_end;
  if (assigned > h->target_assigned) {
    h->target_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { ptgt[k] = tv; }
      k = k + 1ULL;
    }
  }
  if (assigned > h->best_assigned) {
    h->best_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { pbst[k] = tv; }
      k = k + 1ULL;
    }
  }
}

void full_backtrack_raw_m5(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  full_save_target_best(h);
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail;
  u64 cv = h->cur_vars;
  u64 q = (u64)ftrl[target_lvl + 1ULL];
  if (q > h->trail_end) { q = h->trail_end; }
  u64 q_start = q;
  u64 p = q;
  while (p < h->trail_end) {
    u32 lit = trl[p];
    u32 v = lit >> 1;
    if ((u64)v < cv && (u64)lvl[v] <= target_lvl) {
      trl[q] = lit; tpos[v] = (u32)q; q = q + 1ULL;
    } else if ((u64)v < cv) {
      vals[lit] = (i8)0; vals[lit ^ 1u] = (i8)0;
      lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
      if ((fl[v] & FL_ACTIVE) != 0u) { h->unassigned = h->unassigned + 1ULL; }
      if (h->stable != 0ULL) { full_heap_push(h, v); }
      else if ((u64)qs[v] > h->q_search_stamp) {
        h->q_search_idx = (u64)v; h->q_search_stamp = (u64)qs[v];
      }
    }
    p = p + 1ULL;
  }
  h->trail_end = q;
  if (h->propagated > q_start) { h->propagated = q_start; }
  if (h->propagated > q) { h->propagated = q; }
  h->cur_level = target_lvl;
}

void full_backtrack_m5(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  if (h->probing == 0ULL && h->stable != 0ULL) {
    u64 back = h->cur_level - 1ULL;
    if (back < h->max_vars) {
      h->probing = 1ULL;
      full_backtrack_raw_m5(h, back);
      h->probing = 0ULL;
      full_save_target_best(h);
      if (target_lvl < back) {
        h->probing = 1ULL;
        full_backtrack_raw_m5(h, target_lvl);
        h->probing = 0ULL;
      }
      return;
    }
    full_save_target_best(h);
  }
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  full_backtrack_raw_m5(h, target_lvl);
  h->probing = saved_prob;
}

bool full_analyze_rsn_m5(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > 1ULL) {
      u64 lim = glue - 1ULL;
      if (lim > h->tier2) { lim = h->tier2; }
      if (lim > 32ULL) { lim = 32ULL; }
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    u32 *gu = (u32 *)h->glue_used;
    u64 gi = (glue > 63ULL) ? 63ULL : glue;
    if (gu[gi] < 0xFFFFFFFFu) { gu[gi] = gu[gi] + 1u; }
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

void full_otfs_subsume_m5(FullHdr *h, u32 new_confl, u64 old_ctype, u64 old_cref, bool to_bin) {
  if (old_ctype != 2ULL || old_cref == 0xFFFFFFFFULL) { return; }
  u32 *ar = (u32 *)h->arena;
  u32 dhdr = ar[old_cref];
  if ((dhdr & PH_GARB) != 0u) { return; }
  ar[old_cref] = dhdr | PH_GARB;
  h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[old_cref + 2ULL];
  if ((dhdr & PH_RED) != 0u) {
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    if (!to_bin) {
      u32 chdr = ar[new_confl];
      if ((chdr & PH_RED) != 0u) {
        u32 cg = chdr & PH_GLUE_MASK;
        u32 dg = dhdr & PH_GLUE_MASK;
        if (cg > dg) { ar[new_confl] = (chdr & (~PH_GLUE_MASK)) | dg; }
      }
    }
  } else {
    if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
    if (!to_bin && (ar[new_confl] & PH_RED) != 0u) {
      ar[new_confl] = ar[new_confl] & (~PH_RED);
      if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
      h->num_irred = h->num_irred + 1ULL;
    }
  }
}

void full_bump_analyzed_m5(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  u8 *mrk = (u8 *)h->mark;
  u64 cv = h->cur_vars;
  u64 saved = h->min_clr_len;
  u64 lim = saved * 10ULL;
  u64 i = 0ULL;
  while (i < h->tmp_len && h->min_clr_len <= lim) {
    u32 uv = tmp[i] >> 1;
    u32 rsn = ((u64)uv < cv) ? rsns[uv] : 0xFFFFFFFFu;
    if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) != 0u) {
      u32 ov = (rsn & PW_LIT_MASK) >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
        mrk[ov] = (u8)1; ana[h->min_clr_len] = ov; h->min_clr_len = h->min_clr_len + 1ULL;
      }
    } else if (rsn != 0xFFFFFFFFu && (u64)rsn + 3ULL <= h->arena_len) {
      u32 sz = ar[(u64)rsn + 2ULL];
      if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len) {
        u32 j = 0u;
        while (j < sz && h->min_clr_len <= lim) {
          u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
          if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && h->min_clr_len < cv) {
            mrk[ov] = (u8)1; ana[h->min_clr_len] = ov;
            h->min_clr_len = h->min_clr_len + 1ULL;
          }
          j = j + 1u;
        }
      }
    }
    i = i + 1ULL;
  }
  if (h->min_clr_len > lim) {
    while (h->min_clr_len > saved) {
      h->min_clr_len = h->min_clr_len - 1ULL;
      u32 rv = ana[h->min_clr_len];
      if ((u64)rv < cv) { mrk[rv] = (u8)0; }
    }
  }
  i = 0ULL;
  while (i < h->min_clr_len) {
    u32 bv = ana[i];
    if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
      full_bump_var(h, bv);
      if (h->stable == 0ULL) { full_queue_mtf(h, bv); }
    }
    i = i + 1ULL;
  }
  full_bump_decay(h);
}

void full_restore_bump_ana_m5(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  u64 cv = h->cur_vars;
  u64 ana_n = h->res_sz;
  if (ana_n > cv) { ana_n = cv; }
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u64 w = 0ULL;
  u64 k = 0ULL;
  while (k < ana_n) {
    u32 av = ana[k];
    if ((u64)av < cv && mrk[av] == (u8)0) {
      mrk[av] = (u8)1;
      ana[w] = av;
      w = w + 1ULL;
    }
    k = k + 1ULL;
  }
  h->min_clr_len = w;
  if (w > 0ULL) {
    full_bump_analyzed(h);
    full_clear_ana(h);
  }
}

void full_eager_subsume_m5(FullHdr *h, u64 new_ref) {
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

u64 full_learn_clause_m5(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    full_backtrack(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    return 1ULL;
  }
  u64 max_idx = h->tmp_len - 1ULL;
  u64 max_lvl = (u64)lvl[tmp[max_idx] >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u32 w1 = tmp[1]; tmp[1] = tmp[max_idx]; tmp[max_idx] = w1;
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

u64 full_analyze_m5(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  u32 *lvl = (u32 *)h->level;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u64 iter = 0ULL;
  u64 iter_lim = h->cur_vars + 64ULL;
  while (iter < iter_lim) {
    iter = iter + 1ULL;
    u64 ol = full_one_lit_confl(h);
    if (ol == 20ULL) { return 20ULL; }
    if (ol == 1ULL) { return 1ULL; }
    if (ol == 2ULL) { return 0ULL; }
    u64 dst = full_deduce_1uip(h);
    if (dst == 20ULL) { return 20ULL; }
    if (dst == 0ULL) { return 0ULL; }
    if (dst == 2ULL) {
      h->conflicts = h->conflicts + 1ULL;
      if (h->probing == 0ULL) {
        if (h->cur_vars > 0ULL) {
          if (h->confl_type == 1ULL) {
            tmp[0] = (u32)h->confl_lit0;
            h->tmp_len = 1ULL;
          } else if (h->confl_type == 2ULL && h->confl_ref < h->arena_len &&
                     3ULL < h->arena_len - h->confl_ref) {
            tmp[0] = ar[h->confl_ref + 3ULL];
            h->tmp_len = 1ULL;
          }
        }
        full_restore_bump_ana_m5(h);
      }
      continue;
    }
    full_min_shrink(h);
    if (h->probing == 0ULL) {
      full_restore_bump_ana_m5(h);
      full_tick_rel(h);
    }
    u64 glue = 1ULL; u32 last_lvl = 0u; u64 gi = 1ULL;
    while (gi < h->tmp_len) {
      u32 gl = lvl[tmp[gi] >> 1];
      if (gl != last_lvl) { glue = glue + 1ULL; last_lvl = gl; }
      gi = gi + 1ULL;
    }
    if (h->probing == 0ULL) { full_ema_update(h, glue); }
    return full_learn_clause(h, glue);
  }
  return 0ULL;
}

void full_warmup_m5(FullHdr *h) {
  if (h->cur_level != 0ULL || h->unassigned == 0ULL) { return; }
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u64 saved_ticks = h->search_ticks;
  u64 steps = 0ULL;
  while (h->unassigned > 0ULL && steps < h->cur_vars && h->fuel > 0ULL && h->oom == 0ULL) {
    steps = steps + 1ULL;
    u64 v = full_next_dec_var(h);
    if (v == 0xFFFFFFFFFFFFFFFFULL) { break; }
    i8 dph = ph[v];
    if (h->stable != 0ULL && ptgt[v] != (i8)0) { dph = ptgt[v]; }
    u32 lit = (dph < (i8)0) ? ((u32)(v << 1) | 1u) : (u32)(v << 1);
    u64 nlvl = h->cur_level + 1ULL;
    if (nlvl > h->max_vars) { break; }
    ftrl[nlvl] = (u32)h->trail_end;
    fdec[nlvl] = lit;
    h->cur_level = nlvl;
    full_assign(h, lit, 0xFFFFFFFFu);
    while (h->propagated < h->trail_end && h->oom == 0ULL && h->fuel > 0ULL) {
      u64 pr = full_propagate(h);
      if (pr == 0ULL || pr == 2ULL) { break; }
    }
  }
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  full_backtrack_raw_m5(h, 0ULL);
  h->probing = saved_prob;
  h->search_ticks = saved_ticks;
}
"

/-- External canonical callees referenced by `m5HeurCore_fns`. -/
def m5HeurCoreExterns : List Extern :=
  [ ⟨"full_heap_push", [i64, i32], []⟩
  , ⟨"full_save_target_best", [i64], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"full_bump_var", [i64, i32], []⟩
  , ⟨"full_queue_mtf", [i64, i32], []⟩
  , ⟨"full_bump_decay", [i64], []⟩
  , ⟨"full_bump_analyzed", [i64], []⟩
  , ⟨"full_clear_ana", [i64], []⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_det_new_level", [i64, i64], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_reduce", [i64, .bool], [i64]⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_eager_subsume", [i64, i64], []⟩
  , ⟨"full_one_lit_confl", [i64], [i64]⟩
  , ⟨"full_deduce_1uip", [i64], [i64]⟩
  , ⟨"full_min_shrink", [i64], []⟩
  , ⟨"full_tick_rel", [i64], []⟩
  , ⟨"full_ema_update", [i64, i64], []⟩
  , ⟨"full_learn_clause", [i64, i64], [i64]⟩
  , ⟨"full_next_dec_var", [i64], [i64]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩ ]

/-- Standalone M5 Wave-1 `PR-W1A` module (`11` functions + `24` externs, `0` exits). -/
def m5HeurCoreModule : LeanQbe.T.Module :=
  { fns := m5HeurCore_fns, externs := m5HeurCoreExterns, exits := [] }

/-! ## Drop-In Replacement `Fn` Handles for `FullM5` Unification -/

def m5SaveTargetBestFn : Fn :=
  ⟨"full_save_target_best", [i64], [], full_save_target_best_m5_body⟩
def m5BacktrackRawFn : Fn :=
  ⟨"full_backtrack_raw_m5", [i64, i64], [], full_backtrack_raw_m5_body⟩
def m5BacktrackFn : Fn :=
  ⟨"full_backtrack", [i64, i64], [], full_backtrack_m5_body⟩
def m5AnalyzeRsnFn : Fn :=
  ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], full_analyze_rsn_m5_body⟩
def m5OtfsSubsumeFn : Fn :=
  ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], full_otfs_subsume_m5_body⟩
def m5BumpAnalyzedFn : Fn :=
  ⟨"full_bump_analyzed", [i64], [], full_bump_analyzed_m5_body⟩
def m5RestoreBumpAnaFn : Fn :=
  ⟨"full_restore_bump_ana_m5", [i64], [], full_restore_bump_ana_m5_body⟩
def m5EagerSubsumeFn : Fn :=
  ⟨"full_eager_subsume", [i64, i64], [], full_eager_subsume_m5_body⟩
def m5LearnClauseFn : Fn :=
  ⟨"full_learn_clause", [i64, i64], [i64], full_learn_clause_m5_body⟩
def m5AnalyzeFn : Fn :=
  ⟨"full_analyze", [i64], [i64], full_analyze_m5_body⟩
def m5WarmupFn : Fn :=
  ⟨"full_warmup", [i64], [], full_warmup_m5_body⟩

theorem full_save_target_best_m5_wf : Func.Wf full_save_target_best_m5_body := by t_wf_reify
theorem full_backtrack_raw_m5_wf : Func.Wf full_backtrack_raw_m5_body := by t_wf_reify
theorem full_backtrack_m5_wf : Func.Wf full_backtrack_m5_body := by t_wf_reify
theorem full_analyze_rsn_m5_wf : Func.Wf full_analyze_rsn_m5_body := by t_wf_reify
theorem full_otfs_subsume_m5_wf : Func.Wf full_otfs_subsume_m5_body := by t_wf_reify
theorem full_bump_analyzed_m5_wf : Func.Wf full_bump_analyzed_m5_body := by t_wf_reify
theorem full_restore_bump_ana_m5_wf : Func.Wf full_restore_bump_ana_m5_body := by t_wf_reify
theorem full_eager_subsume_m5_wf : Func.Wf full_eager_subsume_m5_body := by t_wf_reify
theorem full_learn_clause_m5_wf : Func.Wf full_learn_clause_m5_body := by t_wf_reify
theorem full_analyze_m5_wf : Func.Wf full_analyze_m5_body := by t_wf_reify
theorem full_warmup_m5_wf : Func.Wf full_warmup_m5_body := by t_wf_reify

theorem m5HeurCore_fns_wf : ∀ f ∈ m5HeurCore_fns, f.Wf := by
  simp only [m5HeurCore_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_save_target_best_m5_wf, full_backtrack_raw_m5_wf, full_backtrack_m5_wf,
    full_analyze_rsn_m5_wf, full_otfs_subsume_m5_wf, full_bump_analyzed_m5_wf,
    full_restore_bump_ana_m5_wf, full_eager_subsume_m5_wf, full_learn_clause_m5_wf,
    full_analyze_m5_wf, full_warmup_m5_wf⟩

theorem m5HeurCore_acyclic : m5HeurCoreModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5HeurCore
