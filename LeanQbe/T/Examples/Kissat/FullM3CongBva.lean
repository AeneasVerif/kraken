module

public import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M3b Congruence, Pure-3-CNF Bypass & BVA/BVE Upgrades (`FullM3CongBva`)

Standalone C0 upgrades spliced onto `FullFast.fastFns` (`0` edits to `Full*` / `FullFast*`,
`0` `FullHdr` / `FullCfg` / `FullState` / `FullMem` / `FullInv` layout churn):
1. **Worklist Gate Congruence Closure (`full_congruence_dense` + `full_cong_work_step`)**:
   - Removes the `6`-pass depth cap (`pass < min((cv << 1) + 4, 0x7FFFFFFF)`, early fixpoint).
   - Raises `ht_sz` cap from `4096` to `65536` (`ht_sz * 8 <= scratch_cap`), keeps persistent hash
     table across passes (refreshing at `75%` load via `res_sz`), uses `tarjan_mark[0..cv)` epoch
     worklist filtering (`tmk[v] >= cur_epoch`), and zeroes `tarjan_mark` before exit.
   - Adds AND (`tag == 0`) constant/duplicate/clash folding + `full_cong_and_match` + XOR/ITE
     constant folding + condition-polarity canonicalization `ITE(c^1, e, t) == ITE(c, t, e)`.
2. **Pure-3-CNF Bypass Removal (`full_probe`, `full_preprocess`)**:
   - Removes `num_binary == 0 && cur_vars >= 48` skip in `full_preprocess` and `num_binary >= 4`
     dense guard in `full_probe`.
3. **BVE Neighbor Re-Arming & Zero-Churn BVA `factorbound` Decoupling (`full_elim_bve`,
   `full_eliminate`)**:
   - Collects active unassigned neighbors into `work_stk2` (deduped via `min_clr` cleared before
     `full_bve_var`), re-arms `FL_ELIM_C` on elimination/BCE over up to `16` passes, widens
     initial `bve_lim = cv * 4 + 256`, and saves/restores `elim_bound = 0` around `full_factor`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m3CongBva "
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
#define FL_ELIM_C 16u

extern u32 full_cong_find(u32 *repr, u32 l);
extern bool full_cong_merge(FullHdr *h, u32 a, u32 b);
extern void full_sort_u32(u32 *arr, u32 n);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim);
extern u64 full_bve_var(FullHdr *h, u32 v);
extern u64 full_probe_dticks(FullHdr *h, bool initial);
extern u64 full_ilog10(u64 x);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim);
extern u64 full_probe_tail(FullHdr *h, u64 dticks);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_forward_sub(FullHdr *h, u64 budget);
extern u64 full_factor(FullHdr *h, u64 budget);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);

void full_cong_mark_trail(FullHdr *h, u64 prev_te, u32 ep) {
  u32 *trl = (u32 *)h->trail;
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 te = h->trail_end;
  u64 i = prev_te;
  while (i < te) {
    u32 lit = trl[i];
    u32 lv = lit >> 1;
    if ((u64)lv < cv) {
      tmk[lv] = ep;
      u32 r = full_cong_find(repr, lit);
      u32 rv = r >> 1;
      if ((u64)rv < cv) { tmk[rv] = ep; }
    }
    i = i + 1ULL;
  }
}

u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep) {
  i8 *vals = (i8 *)h->values;
  if (vals[lit] > (i8)0) { return 0ULL; }
  u64 prev_te = h->trail_end;
  if (!full_add_unit(h, lit)) {
    full_cong_mark_trail(h, prev_te, next_ep);
    return 2ULL;
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  full_cong_mark_trail(h, prev_te, next_ep);
  return (h->inconsistent != 0ULL) ? 2ULL : 1ULL;
}

u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep) {
  u64 prev_te = h->trail_end;
  u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 ra = full_cong_find(repr, a);
  u32 rb = full_cong_find(repr, b);
  bool ch = false;
  i8 va = vals[ra];
  i8 vb = vals[rb];
  if (va != (i8)0) {
    u32 target = (va > (i8)0) ? rb : (rb ^ 1u);
    if (vals[target] <= (i8)0) {
      if (!full_add_unit(h, target)) {
        full_cong_mark_trail(h, prev_te, next_ep);
        return 2ULL;
      }
      h->cong_cnt = h->cong_cnt + 1ULL;
      ch = true;
    }
  } else if (vb != (i8)0) {
    u32 target = (vb > (i8)0) ? ra : (ra ^ 1u);
    if (vals[target] <= (i8)0) {
      if (!full_add_unit(h, target)) {
        full_cong_mark_trail(h, prev_te, next_ep);
        return 2ULL;
      }
      h->cong_cnt = h->cong_cnt + 1ULL;
      ch = true;
    }
  }
  if (full_cong_merge(h, ra, rb)) {
    ch = true;
    u64 cv = h->cur_vars;
    u32 av = a >> 1; u32 bv = b >> 1; u32 rav = ra >> 1; u32 rbv = rb >> 1;
    if ((u64)av < cv) { tmk[av] = next_ep; }
    if ((u64)bv < cv) { tmk[bv] = next_ep; }
    if ((u64)rav < cv) { tmk[rav] = next_ep; }
    if ((u64)rbv < cv) { tmk[rbv] = next_ep; }
  }
  if (h->trail_end > prev_te) { full_cong_mark_trail(h, prev_te, next_ep); }
  return (h->inconsistent != 0ULL) ? 2ULL : (ch ? 1ULL : 0ULL);
}

bool full_cong_and_match(FullHdr *h, u32 ent, u32 ua) {
  if (ua < 2u || ua > 8u) { return false; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  u32 mask = 0u;
  u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { return false; }
    if (ev == (i8)0) {
      bool found = false;
      u32 k = 0u;
      while (k < ua) {
        if (tmp[k] == er) { mask = mask | (1u << k); found = true; break; }
        k = k + 1u;
      }
      if (!found) { return false; }
    }
    j = j + 1u;
  }
  u32 full_mask = (1u << ua) - 1u;
  return mask == full_mask;
}

u64 full_cong_work_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz, u32 cur_ep) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *tmk = (u32 *)h->tarjan_mark;
  i8 *vals = (i8 *)h->values;
  u32 next_ep = cur_ep + 1u;
  u64 ht_lim = (ht_sz * 3ULL) >> 2;
  bool changed = false;
  u64 work = 0ULL;
  u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL) {
    u32 raw_lhs = scr[g];
    u32 meta = scr[g + 1ULL];
    u32 tag = meta >> 28;
    u32 arity = meta & 0xFFu;
    u64 next_g = g + 2ULL + (u64)arity;
    u32 lhs = full_cong_find(repr, raw_lhs);
    bool dirty = (tmk[raw_lhs >> 1] >= cur_ep) || (tmk[lhs >> 1] >= cur_ep);
    u32 i = 0u;
    while (i < arity) {
      u32 raw_a = scr[g + 2ULL + (u64)i];
      u32 ra = full_cong_find(repr, raw_a);
      if (tmk[raw_a >> 1] >= cur_ep || tmk[ra >> 1] >= cur_ep) { dirty = true; }
      tmp[i] = ra;
      i = i + 1u;
    }
    if (!dirty) { work = work + 1ULL; g = next_g; continue; }
    work = work + 4ULL;
    u32 htag = tag;
    u32 harity = arity;
    bool need_hash = true;
    if (tag == 0u) {
      bool has_false = false;
      u32 na = 0u;
      i = 0u;
      while (i < arity) {
        u32 r = tmp[i];
        i8 rv = vals[r];
        if (rv < (i8)0) { has_false = true; }
        else if (rv == (i8)0) { tmp[na] = r; na = na + 1u; }
        i = i + 1u;
      }
      if (has_false) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (na == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else {
        if (na > 1u) { full_sort_u32(tmp, na); }
        bool clash = false;
        u32 ua = 0u;
        u32 si = 0u;
        while (si < na) {
          u32 cur = tmp[si];
          si = si + 1u;
          if (ua == 0u) { tmp[0] = cur; ua = 1u; }
          else {
            u32 prev = tmp[ua - 1u];
            if (cur == prev) { continue; }
            if (cur == (prev ^ 1u)) { clash = true; break; }
            tmp[ua] = cur;
            ua = ua + 1u;
          }
        }
        if (clash) {
          u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
          if (uf == 2ULL) { return (work << 2) | 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 0u) {
          u64 uf = full_cong_unit_fold(h, lhs, next_ep);
          if (uf == 2ULL) { return (work << 2) | 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 1u) {
          u64 ef = full_cong_equiv_fold(h, lhs, tmp[0], next_ep);
          if (ef == 2ULL) { return (work << 2) | 2ULL; }
          if (ef == 1ULL) { changed = true; }
          need_hash = false;
        } else {
          if (vals[lhs] > (i8)0) {
            u32 k = 0u;
            while (k < ua) {
              u64 uf = full_cong_unit_fold(h, tmp[k], next_ep);
              if (uf == 2ULL) { return (work << 2) | 2ULL; }
              if (uf == 1ULL) { changed = true; }
              k = k + 1u;
            }
          }
          harity = ua;
        }
      }
    } else if (tag == 1u && arity == 2u) {
      u32 t0 = tmp[0]; u32 t1 = tmp[1];
      i8 v0 = vals[t0]; i8 v1 = vals[t1];
      if (v0 != (i8)0) {
        u32 eq = (v0 > (i8)0) ? (t1 ^ 1u) : t1;
        u64 ef = full_cong_equiv_fold(h, lhs, eq, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (v1 != (i8)0) {
        u32 eq = (v1 > (i8)0) ? (t0 ^ 1u) : t0;
        u64 ef = full_cong_equiv_fold(h, lhs, eq, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if ((t0 >> 1) == (t1 >> 1)) {
        u32 ul = (t0 == t1) ? (lhs ^ 1u) : lhs;
        u64 uf = full_cong_unit_fold(h, ul, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (t0 > t1) {
        tmp[0] = t1; tmp[1] = t0;
      }
    } else if (tag == 2u && arity == 3u) {
      u32 c = tmp[0]; u32 t = tmp[1]; u32 e = tmp[2];
      i8 vc = vals[c]; i8 vt = vals[t]; i8 ve = vals[e];
      if (vc != (i8)0) {
        u32 br = (vc > (i8)0) ? t : e;
        u64 ef = full_cong_equiv_fold(h, lhs, br, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (t == e) {
        u64 ef = full_cong_equiv_fold(h, lhs, t, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt > (i8)0 && ve < (i8)0) {
        u64 ef = full_cong_equiv_fold(h, lhs, c, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt < (i8)0 && ve > (i8)0) {
        u64 ef = full_cong_equiv_fold(h, lhs, c ^ 1u, next_ep);
        if (ef == 2ULL) { return (work << 2) | 2ULL; }
        if (ef == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt > (i8)0 && ve > (i8)0) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vt < (i8)0 && ve < (i8)0) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return (work << 2) | 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if ((c & 1u) != 0u) {
        tmp[0] = c ^ 1u; tmp[1] = e; tmp[2] = t;
      }
    }
    if (!need_hash) { g = next_g; continue; }
    u64 hv = (u64)htag * 0x9E3779B1ULL + (u64)harity;
    i = 0u;
    while (i < harity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL);
    u64 probes = 0ULL;
    while (probes < 64ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (h->res_sz < ht_lim) {
          scr[ht_off + slot] = (u32)g;
          h->res_sz = h->res_sz + 1ULL;
        }
        break;
      }
      u32 em = scr[(u64)ent + 1ULL];
      u32 etag = em >> 28;
      if (etag == htag) {
        bool matched = false;
        if (htag == 0u) {
          matched = full_cong_and_match(h, ent, harity);
        } else if (htag == 1u && (em & 0xFFu) == 2u) {
          u32 e0 = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 e1 = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          matched = (e0 == tmp[0] && e1 == tmp[1]) || (e0 == tmp[1] && e1 == tmp[0]);
        } else if (htag == 2u && (em & 0xFFu) == 3u) {
          u32 ec = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 et = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 ee = full_cong_find(repr, scr[(u64)ent + 4ULL]);
          if ((ec & 1u) != 0u) { ec = ec ^ 1u; u32 sw = et; et = ee; ee = sw; }
          matched = (ec == tmp[0] && et == tmp[1] && ee == tmp[2]);
        }
        if (matched) {
          u64 ef = full_cong_equiv_fold(h, lhs, scr[ent], next_ep);
          if (ef == 2ULL) { return (work << 2) | 2ULL; }
          if (ef == 1ULL) { changed = true; }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL);
      probes = probes + 1ULL;
    }
    g = next_g;
  }
  u64 st = (h->inconsistent != 0ULL) ? 2ULL : (changed ? 1ULL : 0ULL);
  return (work << 2) | st;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  u64 ht_sz = 64ULL;
  while (ht_sz * 8ULL <= h->scratch_cap && ht_sz < 65536ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 g_len = full_cong_extract(h, ht_off, tick_lim);
  if (g_len == 0ULL) { return 1ULL; }
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  i = 0ULL;
  while (i < cv) { tmk[i] = 1u; i = i + 1ULL; }
  i = 0ULL;
  while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
  h->res_sz = 0ULL;
  u64 max_passes = (cv << 1) + 4ULL;
  if (max_passes > 0x7FFFFFFFULL) { max_passes = 0x7FFFFFFFULL; }
  u64 pass = 0ULL;
  u64 ticks = 0ULL;
  u64 rehashes = 0ULL;
  while (pass < max_passes && h->inconsistent == 0ULL && ticks < tick_lim) {
    u64 ret = full_cong_work_step(h, g_len, ht_off, ht_sz, (u32)(pass + 1ULL));
    ticks = ticks + (ret >> 2);
    u64 st = ret & 3ULL;
    if (st == 2ULL) { break; }
    if (h->res_sz * 4ULL >= ht_sz * 3ULL && rehashes < 4ULL) {
      i = 0ULL;
      while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL;
      u32 n_ep = (u32)(pass + 2ULL);
      i = 0ULL;
      while (i < cv) { tmk[i] = n_ep; i = i + 1ULL; }
      rehashes = rehashes + 1ULL;
    } else if (st == 0ULL) {
      break;
    }
    pass = pass + 1ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_elim_collect_nbrs(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *seen = (u32 *)h->min_clr;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 nn = 0ULL;
  u32 pol = 0u;
  while (pol < 2u) {
    u32 lit = (v << 1) | pol;
    u64 off = (u64)wvec[(u64)lit << 1];
    u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
    u64 p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 u = (w0 & PW_LIT_MASK) >> 1;
        if ((u64)u < cv && u != v && seen[u] == 0u &&
            (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
          seen[u] = 1u;
          if (nn < cv) { nbrs[nn] = u; nn = nn + 1ULL; }
        }
        continue;
      }
      if (p >= end) { break; }
      u32 cr = wstk[p];
      p = p + 1ULL;
      if ((u64)cr + 3ULL > h->arena_len) { continue; }
      u32 hdr = ar[cr];
      u32 sz = ar[(u64)cr + 2ULL];
      if ((hdr & PH_GARB) != 0u || (u64)cr + 3ULL + (u64)sz > h->arena_len) { continue; }
      u32 i = 0u;
      while (i < sz) {
        u32 u = ar[(u64)cr + 3ULL + (u64)i] >> 1;
        if ((u64)u < cv && u != v && seen[u] == 0u &&
            (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
          seen[u] = 1u;
          if (nn < cv) { nbrs[nn] = u; nn = nn + 1ULL; }
        }
        i = i + 1u;
      }
    }
    pol = pol + 1u;
  }
  u64 k = 0ULL;
  while (k < nn) { seen[nbrs[k]] = 0u; k = k + 1ULL; }
  return nn;
}

u64 full_elim_bve(FullHdr *h, u64 bve_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *seen = (u32 *)h->min_clr;
  u64 cv = h->cur_vars;
  u64 ci = 0ULL;
  while (ci < cv) { seen[ci] = 0u; ci = ci + 1ULL; }
  u64 pass = 0ULL;
  u64 tried = 0ULL;
  u64 res = 1ULL;
  while (pass < 16ULL && tried < bve_lim && h->oom == 0ULL && h->fuel > 0ULL && res == 1ULL) {
    bool rearmed = false;
    u64 v = 0ULL;
    while (v < cv && tried < bve_lim && h->oom == 0ULL && h->fuel > 0ULL) {
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) && vals[v << 1] == (i8)0) {
        fl[v] = fl[v] & (~FL_ELIM_C);
        tried = tried + 1ULL;
        u64 nn = full_elim_collect_nbrs(h, (u32)v);
        u64 prev_bce = h->bce_cnt;
        u64 br = full_bve_var(h, (u32)v);
        if (br == 20ULL) { res = 20ULL; break; }
        if ((fl[v] & FL_ACTIVE) == 0u || h->bce_cnt > prev_bce) {
          u32 *nbrs = (u32 *)h->work_stk2;
          u64 cur_cv = h->cur_vars;
          u64 k = 0ULL;
          while (k < nn) {
            u32 u = nbrs[k];
            if ((u64)u < cur_cv && (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
              if ((fl[u] & FL_ELIM_C) == 0u) { rearmed = true; }
              fl[u] = fl[u] | FL_ELIM_C;
            }
            k = k + 1ULL;
          }
        }
        if (br == 2ULL) { res = 2ULL; break; }
      }
      v = v + 1ULL;
    }
    if (!rearmed || res != 1ULL) { break; }
    pass = pass + 1ULL;
  }
  return (res == 20ULL) ? 20ULL : 1ULL;
}

u64 full_probe(FullHdr *h, bool initial) {
  u64 dticks = full_probe_dticks(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta(h, 120ULL * h->probings * logp);
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
  bool do_dense = (initial || h->num_binary * 3ULL >= h->num_irred);
  if (do_dense) {
    if (full_enter_dense(h)) {
      u64 sweep_bud = full_min_u64(8ULL + (dticks >> 11), 32ULL);
      if (full_congruence_dense(h, dticks * 2ULL + 16384ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_sweep_dense(h, sweep_bud, dticks + 4096ULL) == 20ULL) {
        full_rebuild_watches(h); return 20ULL;
      }
      if (full_rebuild_watches(h) == 20ULL) { return 20ULL; }
    } else if (h->inconsistent != 0ULL) { return 20ULL; }
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) { return 20ULL; }
  if (!initial && full_probe_tail(h, dticks) == 20ULL) { return 20ULL; }
  h->fwd_sub_cnt = h->search_ticks;
  return 1ULL;
}

u64 full_eliminate(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    h->elim_limit = h->conflicts + full_scale_delta(h, 250ULL * h->eliminations * loge);
    if (h->eliminations >= 2ULL && h->elim_bound < 8ULL) {
      h->elim_bound = h->elim_bound + 2ULL;
    }
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 bve_lim = initial ? (cv * 4ULL + 256ULL) : full_min_u64(64ULL + (dticks >> 7), cv * 2ULL);
  u64 res = full_elim_bve(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    u64 fact_bud = full_min_u64(initial ? 128ULL : (16ULL + (dticks >> 10)), 256ULL);
    u64 saved_eb = h->elim_bound;
    h->elim_bound = 0ULL;
    full_factor(h, fact_bud);
    h->elim_bound = saved_eb;
  }
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_preprocess(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unflushed > 0ULL) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    h->unflushed = 0ULL;
  }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_scale_delta(h, 120ULL);
  if (full_probe(h, true) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h, true) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  h->probe_limit = full_scale_delta(h, 50ULL);
  h->elim_limit = full_scale_delta(h, 120ULL);
  return 1ULL;
}
"

/-- External callee signatures referenced by `m3CongBva_fns`. -/
def m3Externs : List Extern :=
  [ ⟨"full_cong_find", [i64, i32], [i32]⟩
  , ⟨"full_cong_merge", [i64, i32, i32], [.bool]⟩
  , ⟨"full_sort_u32", [i64, i32], []⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64]⟩
  , ⟨"full_bve_var", [i64, i32], [i64]⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_scale_delta", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64]⟩
  , ⟨"full_probe_tail", [i64, i64], [i64]⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64]⟩
  , ⟨"full_forward_sub", [i64, i64], [i64]⟩
  , ⟨"full_factor", [i64, i64], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩ ]

/-- Standalone M3b module (`11` fns, all external callees explicit). -/
def m3Module : LeanQbe.T.Module :=
  { fns := m3CongBva_fns, externs := m3Externs, exits := [] }

theorem full_cong_mark_trail_wf : Func.Wf full_cong_mark_trail_body := by t_wf_reify
theorem full_cong_unit_fold_wf : Func.Wf full_cong_unit_fold_body := by t_wf_reify
theorem full_cong_equiv_fold_wf : Func.Wf full_cong_equiv_fold_body := by t_wf_reify
theorem full_cong_and_match_wf : Func.Wf full_cong_and_match_body := by t_wf_reify
theorem full_cong_work_step_wf : Func.Wf full_cong_work_step_body := by t_wf_reify
theorem full_congruence_dense_wf : Func.Wf full_congruence_dense_body := by t_wf_reify
theorem full_elim_collect_nbrs_wf : Func.Wf full_elim_collect_nbrs_body := by t_wf_reify
theorem full_elim_bve_wf : Func.Wf full_elim_bve_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify

theorem m3_fns_wf : ∀ f ∈ m3CongBva_fns, f.Wf := by
  simp only [m3CongBva_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_cong_mark_trail_wf, full_cong_unit_fold_wf, full_cong_equiv_fold_wf,
    full_cong_and_match_wf, full_cong_work_step_wf, full_congruence_dense_wf,
    full_elim_collect_nbrs_wf, full_elim_bve_wf, full_probe_wf, full_eliminate_wf,
    full_preprocess_wf⟩

theorem m3_acyclic : m3Module.checkAcyclic = true := by
  t_kernel_rfl

/-! ## Splicing onto the M2 `FullFast.fastFns` (`196` → `201` functions) -/

def m3MarkTrailFn : Fn := ⟨"full_cong_mark_trail", _, _, full_cong_mark_trail_body⟩
def m3UnitFoldFn : Fn := ⟨"full_cong_unit_fold", _, _, full_cong_unit_fold_body⟩
def m3EquivFoldFn : Fn := ⟨"full_cong_equiv_fold", _, _, full_cong_equiv_fold_body⟩
def m3AndMatchFn : Fn := ⟨"full_cong_and_match", _, _, full_cong_and_match_body⟩
def m3CongWorkStepFn : Fn := ⟨"full_cong_work_step", _, _, full_cong_work_step_body⟩
def m3CongruenceDenseFn : Fn := ⟨"full_congruence_dense", _, _, full_congruence_dense_body⟩
def m3ElimCollectNbrsFn : Fn := ⟨"full_elim_collect_nbrs", _, _, full_elim_collect_nbrs_body⟩
def m3ElimBveFn : Fn := ⟨"full_elim_bve", _, _, full_elim_bve_body⟩
def m3ProbeFn : Fn := ⟨"full_probe", _, _, full_probe_body⟩
def m3EliminateFn : Fn := ⟨"full_eliminate", _, _, full_eliminate_body⟩
def m3PreprocessFn : Fn := ⟨"full_preprocess", _, _, full_preprocess_body⟩

/-- Name-directed splice replacing `full_cong_hash_step`, `full_congruence_dense`, `full_elim_bve`,
`full_probe`, `full_eliminate`, and `full_preprocess` with M3b upgrades and helpers. -/
def m3Splice (f : Fn) : List Fn :=
  if f.name = "full_cong_hash_step" then
    [m3MarkTrailFn, m3UnitFoldFn, m3EquivFoldFn, m3AndMatchFn, m3CongWorkStepFn]
  else if f.name = "full_congruence_dense" then [m3CongruenceDenseFn]
  else if f.name = "full_elim_bve" then [m3ElimCollectNbrsFn, m3ElimBveFn]
  else if f.name = "full_probe" then [m3ProbeFn]
  else if f.name = "full_eliminate" then [m3EliminateFn]
  else if f.name = "full_preprocess" then [m3PreprocessFn]
  else [f]

/-- Unified M3b function list (`201` functions in topological call order). -/
def m3Fns : List Fn := FullFast.fastFns.flatMap m3Splice

/-- Closed M3b compilation module (`externs := []`, `exits := []`). -/
def m3FullModule : LeanQbe.T.Module :=
  { fns := m3Fns, externs := [], exits := [] }

theorem m3Splice_wf (f : Fn) (hf : f.Wf) : ∀ g ∈ m3Splice f, g.Wf := by
  intro g hg
  unfold m3Splice at hg
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact full_cong_mark_trail_wf
    · exact full_cong_unit_fold_wf
    · exact full_cong_equiv_fold_wf
    · exact full_cong_and_match_wf
    · exact full_cong_work_step_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_congruence_dense_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact full_elim_collect_nbrs_wf
    · exact full_elim_bve_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_probe_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_eliminate_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_preprocess_wf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; exact hf

theorem m3Fns_wf : ∀ f ∈ m3Fns, f.Wf := by
  intro g hg
  obtain ⟨f, hf, hg⟩ := List.mem_flatMap.mp hg
  exact m3Splice_wf f (FullFast.fastFns_wf f hf) g hg

theorem m3Fns_length : m3Fns.length = 201 := by t_kernel_rfl

theorem m3Full_acyclic : m3FullModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM3CongBva
