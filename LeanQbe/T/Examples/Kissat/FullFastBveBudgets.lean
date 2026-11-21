module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M2 Tier-A BVE / Tarjan / Budgeted Inprocessing & Init-Hdr Upgrades

Ports the `6` Tier-A mandatory changed functions plus `full_init_hdr` from
`prototype/kissat-fast-c0` (`076fcb00`) onto the byte-identical `144`-word (`FullHdr`) layout
(`4` `KissatDimacs` words + `140` tail words; `0` layout churn):
1. `full_init_hdr`: tunes `probe_limit: 500 -> 2000`, `elim_limit: 1500 -> 5000`.
2. `full_probe_run`: early guard `if (budget == 0ULL || h->num_binary == 0ULL) return 1ULL;`.
3. `full_transitive(h, tick_lim)`: `u64` tick limit parameter + early guard
   `if (h->num_binary == 0ULL || tick_lim == 0ULL) return 1ULL;`.
4. `full_vivify(h, tier_mode, budget)`: `u64` budget parameter + early guard
   `if (budget == 0ULL) return 1ULL;`.
5. `full_tarjan_scc`: zeroes `tmk[i] = 0u; trc[i] = 0u;` in the exit loop so `TmkZero` holds
   on entry to `full_find_definition` and `full_sweep_cone`.
6. `full_forward_sub(h, budget)`: `u64` budget parameter + early guard
   `if (budget == 0ULL) return 1ULL;`.
7. `full_bve_var`: raises occ-collect cap `32u -> 64u` and switches gate-skip polarity to
   `need_pair = !gate_found || (((pmask >> i) | (nmask >> j)) & 1) != 0` (skipping `P_ng × N_ng`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFastBveBudgets

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fastBveBudgets "
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
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_ELIM    2u
#define FL_TRANS   512u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 a, u32 b);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cr);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern u64 full_probe_assume_pair(FullHdr *h, u32 lit);
extern bool full_trans_lit(FullHdr *h, u32 lit);
extern u64 full_viv_clause(FullHdr *h, u32 cref);
extern bool full_tarjan_pop_scc(FullHdr *h, u32 root, u32 lit, u32 mroot);
extern bool full_fwd_dedup_bins(FullHdr *h);
extern bool full_fwd_check_cl(FullHdr *h, u32 cr);
extern u32 full_bve_collect(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern void full_bve_gates(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);

void full_init_hdr(FullHdr *h, u64 mv, u64 max_v, u64 fuel) {
  h->max_vars = max_v; h->cur_vars = mv; h->bva_cap = max_v - mv;
  h->unassigned = mv;
  h->delayed_len = 0ULL; h->arena_len = 0ULL; h->wlen = 1ULL; h->wusable = 0ULL;
  h->arena_garbage = 0ULL; h->first_reducible = 0xFFFFFFFFULL;
  h->num_irred = 0ULL; h->num_redundant = 0ULL; h->num_binary = 0ULL;
  h->unflushed = 0ULL; h->probing = 0ULL; h->trail_end = 0ULL; h->propagated = 0ULL;
  h->cur_level = 0ULL; h->fuel = fuel; h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL; h->confl_lit0 = 0ULL; h->confl_lit1 = 0ULL;
  h->tmp_cnt = 0ULL; h->tmp_len = 0ULL; h->heap_len = mv; h->scinc = 1ULL << 28;
  h->min_clr_len = 0ULL; h->min_clr_full = 0ULL;
  h->rel_period = 1024ULL; h->rel_limit = 1048576ULL; h->rel_wait = 1024ULL;
  h->rel_u = 1ULL; h->rel_v = 1ULL; h->rel_trigger = 0ULL;
  h->conflicts = 0ULL; h->learned_lits = 0ULL; h->min_removed = 0ULL;
  h->stable = 0ULL; h->switched = 0ULL; h->mode_count = 0ULL;
  h->mode_confl_lim = 1000ULL; h->mode_tick_lim = 0ULL;
  h->mode_saved_ticks = 0ULL; h->search_ticks = 0ULL;
  h->q_first = (mv == 0ULL) ? 0xFFFFFFFFULL : 0ULL;
  h->q_last = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_idx = (mv == 0ULL) ? 0xFFFFFFFFULL : (mv - 1ULL);
  h->q_search_stamp = mv; h->q_cur_stamp = mv;
  h->target_assigned = 0ULL; h->best_assigned = 0ULL;
  h->rephase_limit = 1000ULL; h->rephased = 0ULL;
  h->reduce_limit = 1000ULL; h->reductions = 0ULL;
  h->tier1 = 2ULL; h->tier2 = 6ULL;
  h->restarts = 0ULL; h->restart_limit = 1ULL;
  h->ema_fast_biased = 0ULL; h->ema_fast_exp = 1ULL << 24;
  h->ema_slow_biased = 0ULL; h->ema_slow_exp = 1ULL << 24;
  h->oom = 0ULL; h->extend_len = 0ULL;
  h->rng_state = 0x9E3779B97F4A7C15ULL ^ (mv + 1ULL);
  h->chrono_levels = 100ULL; h->otfs_cnt = 0ULL; h->eager_sub_cnt = 0ULL;
  h->probe_limit = 2000ULL; h->probings = 0ULL;
  h->elim_limit = 5000ULL; h->eliminations = 0ULL; h->elim_bound = 0ULL;
  h->dense_mode = 0ULL; h->inconsistent = 0ULL; h->iterating = 0ULL;
  h->hbr_cnt = 0ULL; h->trans_cnt = 0ULL; h->viv_cnt = 0ULL; h->subst_cnt = 0ULL;
  h->cong_cnt = 0ULL; h->sweep_cnt = 0ULL; h->bve_cnt = 0ULL; h->bce_cnt = 0ULL;
  h->bva_cnt = 0ULL; h->walk_cnt_stat = 0ULL; h->fwd_sub_cnt = 0ULL; h->fwd_str_cnt = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
}

u64 full_probe_run(FullHdr *h, u64 budget) {
  if (budget == 0ULL || h->num_binary == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL; u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars; u64 done = 0ULL; u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && done < budget && h->fuel > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u64 st = full_probe_assume_pair(h, (u32)(v << 1));
      done = done + 1ULL;
      if (st == 20ULL) { res = 20ULL; break; }
      if (st == 2ULL) { break; }
    }
    v = v + 1ULL;
  }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 0ULL; return res;
}

u64 full_transitive(FullHdr *h, u64 tick_lim) {
  if (h->num_binary == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL; u32 *fl = (u32 *)h->flags; u64 cv = h->cur_vars;
  h->ant_sz = tick_lim; u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && h->ant_sz > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_TRANS)) == (FL_ACTIVE | FL_TRANS)) {
      fl[v] = fl[v] & (~FL_TRANS);
      if (!full_trans_lit(h, (u32)(v << 1))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      if (!full_trans_lit(h, (u32)((v << 1) | 1ULL))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
    }
    v = v + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
  h->probing = 0ULL; return res;
}

u64 full_vivify(FullHdr *h, u64 tier_mode, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL; u32 *ar = (u32 *)h->arena;
  u64 p = 0ULL; u64 res = 1ULL;
  while (p < h->arena_len && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u32 hdr = ar[p]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_VIV)) == 0u) {
      bool is_red = ((hdr & PH_RED) != 0u);
      u64 glue = (u64)(hdr & PH_GLUE_MASK);
      bool take = false;
      if (tier_mode == 0ULL) { take = !is_red; }
      else if (tier_mode == 1ULL) { take = is_red && glue <= h->tier1; }
      else if (tier_mode == 2ULL) { take = is_red && glue > h->tier1 && glue <= h->tier2; }
      else { take = is_red && glue > h->tier2; }
      if (take) {
        budget = budget - 1ULL;
        u64 vc = full_viv_clause(h, (u32)p);
        if (vc == 20ULL) { res = 20ULL; break; }
        if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      }
    }
    p = np;
  }
  if (res == 1ULL) {
    p = 0ULL;
    while (p < h->arena_len) {
      ar[p] = ar[p] & (~PH_VIV);
      p = (u64)full_arena_next(h, (u32)p);
    }
  }
  h->probing = 0ULL; return res;
}

u64 full_tarjan_scc(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *scc = (u32 *)h->work_stk1;
  u32 *dv = (u32 *)h->work_stk2; u32 *dpos = (u32 *)h->wsort;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *fl = (u32 *)h->flags;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = 0xFFFFFFFFu; tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL; }
  u32 reached = 0u; h->tmp_cnt = 0ULL; h->res_sz = 0ULL; u64 root = 0ULL;
  while (root < nlits && h->inconsistent == 0ULL) {
    if (tmk[root] == 0u && (fl[root >> 1] & FL_ACTIVE) != 0u) {
      bool failed = false; u32 mroot = reached + 1u;
      u64 dsp = 1ULL; dv[0] = (u32)root; dpos[0] = 0u;
      reached = reached + 1u; tmk[root] = reached; trc[root] = reached;
      scc[h->tmp_cnt] = (u32)root; h->tmp_cnt = h->tmp_cnt + 1ULL;
      while (dsp > 0ULL && h->inconsistent == 0ULL) {
        u32 lit = dv[dsp - 1ULL]; u32 nl = lit ^ 1u; u32 pos = dpos[dsp - 1ULL];
        u64 off = (u64)wvec[(u64)nl << 1]; u32 sz = wvec[((u64)nl << 1) + 1ULL];
        if (pos < sz) {
          u32 w0 = wstk[off + (u64)pos];
          if ((w0 & PW_BIN_FLAG) == 0u) { dpos[dsp - 1ULL] = pos + 2u; continue; }
          dpos[dsp - 1ULL] = pos + 1u; u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u && tmk[ot] == 0u) {
            reached = reached + 1u; tmk[ot] = reached; trc[ot] = reached;
            scc[h->tmp_cnt] = ot; h->tmp_cnt = h->tmp_cnt + 1ULL;
            dv[dsp] = ot; dpos[dsp] = 0u; dsp = dsp + 1ULL;
          }
          continue;
        }
        u32 p = 0u; u32 rlit = trc[lit];
        while (p < sz) {
          u32 w0 = wstk[off + (u64)p];
          if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2u; continue; }
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u && trc[ot] < rlit) {
            rlit = trc[ot];
          }
          p = p + 1u;
        }
        dsp = dsp - 1ULL;
        if (rlit != tmk[lit]) { trc[lit] = rlit; }
        else {
          u32 mr = failed ? 0xFFFFFFFFu : mroot;
          if (full_tarjan_pop_scc(h, (u32)root, lit, mr)) { failed = true; }
        }
      }
    }
    root = root + 1ULL;
  }
  i = 0ULL;
  while (i < nlits) {
    if (repr[i] == 0xFFFFFFFFu) { repr[i] = (u32)i; }
    tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL;
  }
  return h->res_sz;
}

u64 full_forward_sub(FullHdr *h, u64 budget) {
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  if (budget == 0ULL) { return 1ULL; }
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len && budget > 0ULL && h->inconsistent == 0ULL) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 32u) {
      budget = budget - 1ULL;
      if (!full_fwd_check_cl(h, (u32)p)) { return 20ULL; }
    }
    p = np;
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_bve_var(FullHdr *h, u32 v) {
  if (h->scratch_cap < 512ULL) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 pl = v << 1; u32 nl = pl | 1u;
  u32 np = full_bve_collect(h, pl, scr, 64u);
  u32 nn = full_bve_collect(h, nl, scr + 64, 64u);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, 64u, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, 64u, nn))) { h->oom = 1ULL; return 2ULL; }
    full_set_inactive(h, v, FL_ELIM); h->bve_cnt = h->bve_cnt + 1ULL; return 1ULL;
  }
  u64 r_cnt = 0ULL; u64 rp = 160ULL; u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    full_bve_gates(h, v, np, nn);
    u64 pmask = (u64)scr[128] | ((u64)scr[129] << 32);
    u64 nmask = (u64)scr[130] | ((u64)scr[131] << 32);
    bool gate_found = (pmask != 0ULL || nmask != 0ULL);
    u32 i = 0u;
    while (i < np && fit) {
      u32 j = 0u;
      while (j < nn && fit) {
        bool need_pair = !gate_found ||
          ((((pmask >> (u64)i) | (nmask >> (u64)j)) & 1ULL) != 0ULL);
        if (need_pair && full_bve_resolve_pair(h, v, scr[i], scr[64u + j])) {
          r_cnt = r_cnt + 1ULL;
          if (r_cnt > lim_cls || rp + 1ULL + h->tmp_len > h->scratch_cap) { fit = false; break; }
          scr[rp] = (u32)h->tmp_len; u32 *tmp = (u32 *)h->tmp_lits; u32 k = 0u;
          while ((u64)k < h->tmp_len) { scr[rp + 1ULL + (u64)k] = tmp[k]; k = k + 1u; }
          rp = rp + 1ULL + h->tmp_len;
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
  }
  if (fit && h->arena_len + (rp - 160ULL) + (r_cnt * 2ULL) + 16ULL <= h->arena_cap) {
    if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, 64u, nn)) {
      h->oom = 1ULL; return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM); h->bve_cnt = h->bve_cnt + 1ULL;
    return full_bve_commit_res(h, 160ULL, rp);
  }
  u32 i = 0u;
  while (i < np) {
    if (full_bve_try_bce(h, pl, scr[i], 64u, nn)) {
      if ((scr[i] & PW_BIN_FLAG) != 0u) {
        if (full_extend_push2(h, pl, scr[i] & PW_LIT_MASK)) {
          full_delete_binary(h, pl, scr[i] & PW_LIT_MASK); h->bce_cnt = h->bce_cnt + 1ULL;
        }
      } else if (full_extend_push_cl(h, pl, scr[i])) {
        u32 *ar = (u32 *)h->arena; u32 ccr = scr[i]; ar[ccr] = ar[ccr] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)ccr + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    i = i + 1u;
  }
  return 1ULL;
}
"

def fastBveBudgetsExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_set_inactive", [i64, i32, i32], []⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64]⟩
  , ⟨"full_trans_lit", [i64, i32], [.bool]⟩
  , ⟨"full_viv_clause", [i64, i32], [i64]⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool]⟩
  , ⟨"full_fwd_check_cl", [i64, i32], [.bool]⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32]⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], []⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64]⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64]⟩ ]

def fastBveBudgetsModule : LeanQbe.T.Module :=
  { fns := fastBveBudgets_fns, externs := fastBveBudgetsExterns, exits := [] }

theorem full_init_hdr_wf : Func.Wf full_init_hdr_body := by t_wf_reify
theorem full_probe_run_wf : Func.Wf full_probe_run_body := by t_wf_reify
theorem full_transitive_wf : Func.Wf full_transitive_body := by t_wf_reify
theorem full_vivify_wf : Func.Wf full_vivify_body := by t_wf_reify
theorem full_tarjan_scc_wf : Func.Wf full_tarjan_scc_body := by t_wf_reify
theorem full_forward_sub_wf : Func.Wf full_forward_sub_body := by t_wf_reify
theorem full_bve_var_wf : Func.Wf full_bve_var_body := by t_wf_reify

theorem fastBveBudgets_fns_wf : ∀ f ∈ fastBveBudgets_fns, f.Wf := by
  simp only [fastBveBudgets_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_init_hdr_wf, full_probe_run_wf, full_transitive_wf, full_vivify_wf,
    full_tarjan_scc_wf, full_forward_sub_wf, full_bve_var_wf⟩

theorem fastBveBudgets_acyclic : fastBveBudgetsModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullFastBveBudgets
