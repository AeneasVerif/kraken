module

public import LeanQbe.T.Examples.Kissat.Full1

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Full` C0 Solver — Embedded Scratch `kitten` Sub-Solver (`Stage 4`)

Ports all `15` scratch-resident `kitten` mini-CDCL sub-solver and DAG UNSAT-core shrinking
functions from `prototype/kissat-fast-c0` into `Kissat.Full` without modifying `FullHdr` (`144`
`u64` words, omitting the dead write-only `kitten_calls` counter):
1. Initialization, 2-watched-literal attachment, and clause loading (`full_kitten_init`,
   `full_kitten_watch`, `full_kitten_add_clause`).
2. Trail assignment, VMTF bump-to-front, backtracking, and level-0 unit antecedent recording
   (`full_kitten_assign`, `full_kitten_mtf`, `full_kitten_backtrack`, `full_kitten_learn_unit0`).
3. 2WL BCP, 1UIP conflict analysis, assumption-conflict core marking, and CDCL solve loop
   (`full_kitten_propagate`, `full_kitten_ana_clause`, `full_kitten_analyze`,
   `full_kitten_build_failing`, `full_kitten_solve`).
4. DAG-closed core extraction, shrinking, and O(1) literal flip for sweeping
   (`full_kitten_core`, `full_kitten_shrink`, `full_kitten_flip`).
-/

namespace LeanQbe.T.Examples.Kissat.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! fullKitten "
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

#define K_BASE 256u
#define K_MAX_V 128u
#define K_MAX_L 256u
#define K_MAX_ORIG 512u
#define K_MAX_CL 896u

#define KH_NV 0u
#define KH_NC 1u
#define KH_ORIG_NC 2u
#define KH_LVL 3u
#define KH_PROP 4u
#define KH_TRL_END 5u
#define KH_UNASS 6u
#define KH_INCONS 7u
#define KH_FAILING 8u
#define KH_ANTE 9u
#define KH_QFIRST 10u
#define KH_QLAST 11u
#define KH_QSEARCH 12u
#define KH_QSTAMP 13u
#define KH_TICKS 14u
#define KH_TICK_LIM 15u
#define KH_ALEN 16u
#define KH_ACAP 17u
#define KH_NASSUMP 18u
#define KH_NUNITS 19u
#define KH_NRES 20u
#define KH_NKL 21u
#define KH_NANA 22u
#define KH_STATUS 23u
#define KH_PHASE 24u

#define KO_LVL 32u
#define KO_RSN 160u
#define KO_QPREV 288u
#define KO_QNEXT 416u
#define KO_QSTAMP 544u
#define KO_TRL 672u
#define KO_FLAGS 800u
#define KO_VALS 928u
#define KO_ASSUMP 1184u
#define KO_ANA 1312u
#define KO_KL 1440u
#define KO_UNITS 1568u
#define KO_RES 1824u
#define KO_WHEAD 2080u
#define KO_WNEXT 2336u
#define KO_WBLIT 4128u
#define KO_CL_OFF 5920u
#define KO_CL_META 6816u
#define KO_CL_AUX 7712u
#define KO_ARENA 8608u

#define KM_CORE 0x10000u
#define KM_LRN  0x20000u

void full_kitten_init(FullHdr *h, u32 nv, u32 track_ante) {
  if (h->scratch_cap < 10240ULL || nv > K_MAX_V) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  u32 i = 0u;
  while (i < 32u) { k[i] = 0u; i = i + 1u; }
  k[KH_NV] = nv; k[KH_UNASS] = nv; k[KH_ANTE] = track_ante;
  k[KH_INCONS] = 0xFFFFFFFFu; k[KH_FAILING] = 0xFFFFFFFFu;
  k[KH_TICK_LIM] = 8192u;
  k[KH_ACAP] = (u32)(h->scratch_cap - (u64)K_BASE - (u64)KO_ARENA);
  if (nv == 0u) {
    k[KH_QFIRST] = 0xFFFFFFFFu; k[KH_QLAST] = 0xFFFFFFFFu; k[KH_QSEARCH] = 0xFFFFFFFFu;
  } else {
    k[KH_QFIRST] = 0u; k[KH_QLAST] = nv - 1u; k[KH_QSEARCH] = nv - 1u; k[KH_QSTAMP] = nv;
  }
  i = 0u;
  while (i < nv) {
    k[KO_LVL + i] = 0u; k[KO_RSN + i] = 0xFFFFFFFFu; k[KO_FLAGS + i] = 0u;
    k[KO_QSTAMP + i] = i + 1u;
    k[KO_QPREV + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    k[KO_QNEXT + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  u32 nl = nv << 1; i = 0u;
  while (i < nl) { k[KO_VALS + i] = 0u; k[KO_WHEAD + i] = 0xFFFFFFFFu; i = i + 1u; }
}

void full_kitten_watch(u32 *k, u32 cid, u32 l0, u32 l1) {
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  k[KO_WBLIT + w0] = l1; k[KO_WNEXT + w0] = k[KO_WHEAD + l0]; k[KO_WHEAD + l0] = w0;
  k[KO_WBLIT + w1] = l0; k[KO_WNEXT + w1] = k[KO_WHEAD + l1]; k[KO_WHEAD + l1] = w1;
}

bool full_kitten_add_clause(FullHdr *h, u32 id, u32 *lits, u32 sz) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  u32 nc = k[KH_NC]; u32 off = k[KH_ALEN];
  if (nc >= K_MAX_ORIG || off + sz > k[KH_ACAP]) { return false; }
  if (sz == 0u) {
    k[KO_CL_OFF + nc] = off; k[KO_CL_META + nc] = 0u; k[KO_CL_AUX + nc] = id;
    if (k[KH_INCONS] == 0xFFFFFFFFu) { k[KH_INCONS] = nc; }
    k[KH_NC] = nc + 1u; k[KH_ORIG_NC] = nc + 1u; return true;
  }
  u32 i = 0u;
  while (i < sz) { k[KO_ARENA + off + i] = lits[i]; i = i + 1u; }
  k[KH_ALEN] = off + sz;
  k[KO_CL_OFF + nc] = off; k[KO_CL_META + nc] = sz; k[KO_CL_AUX + nc] = id;
  k[KH_NC] = nc + 1u; k[KH_ORIG_NC] = nc + 1u;
  if (sz == 1u) {
    u32 nu = k[KH_NUNITS];
    if (nu < 256u) { k[KO_UNITS + nu] = nc; k[KH_NUNITS] = nu + 1u; }
    return true;
  }
  full_kitten_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_kitten_assign(u32 *k, u32 lit, u32 rsn) {
  u32 v = lit >> 1; u32 te = k[KH_TRL_END];
  k[KO_VALS + lit] = 1u; k[KO_VALS + (lit ^ 1u)] = 2u;
  k[KO_LVL + v] = k[KH_LVL]; k[KO_RSN + v] = rsn;
  k[KO_TRL + te] = lit; k[KH_TRL_END] = te + 1u;
  if (k[KH_UNASS] > 0u) { k[KH_UNASS] = k[KH_UNASS] - 1u; }
  u32 fl = k[KO_FLAGS + v];
  k[KO_FLAGS + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_kitten_mtf(u32 *k, u32 v) {
  u32 nv = k[KH_NV];
  if (v >= nv || v == k[KH_QLAST]) { return; }
  u32 pv = k[KO_QPREV + v]; u32 nxt = k[KO_QNEXT + v];
  if (k[KO_VALS + (v << 1)] != 0u && v == k[KH_QSEARCH]) {
    if (pv < nv) { k[KH_QSEARCH] = pv; } else if (nxt < nv) { k[KH_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[KH_QFIRST] = nxt; } else { k[KO_QNEXT + pv] = nxt; }
  if (nxt >= nv) { k[KH_QLAST] = pv; } else { k[KO_QPREV + nxt] = pv; }
  u32 ol = k[KH_QLAST];
  k[KO_QPREV + v] = ol; k[KO_QNEXT + v] = 0xFFFFFFFFu; k[KH_QLAST] = v;
  if (ol >= nv) { k[KH_QFIRST] = v; } else { k[KO_QNEXT + ol] = v; }
  if (k[KH_QSTAMP] < 0xFFFFFFF0u) {
    k[KH_QSTAMP] = k[KH_QSTAMP] + 1u; k[KO_QSTAMP + v] = k[KH_QSTAMP];
  }
  if (k[KO_VALS + (v << 1)] == 0u) { k[KH_QSEARCH] = v; }
}

void full_kitten_backtrack(u32 *k, u32 target_lvl) {
  u32 te = k[KH_TRL_END]; u32 best_st = 0u;
  if (k[KH_QSEARCH] < k[KH_NV]) { best_st = k[KO_QSTAMP + k[KH_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = k[KO_TRL + te - 1u]; u32 v = lit >> 1;
    if (k[KO_LVL + v] <= target_lvl) { break; }
    te = te - 1u;
    k[KO_VALS + lit] = 0u; k[KO_VALS + (lit ^ 1u)] = 0u;
    k[KO_LVL + v] = 0u; k[KO_RSN + v] = 0xFFFFFFFFu;
    k[KH_UNASS] = k[KH_UNASS] + 1u;
    if (k[KO_QSTAMP + v] > best_st) { best_st = k[KO_QSTAMP + v]; k[KH_QSEARCH] = v; }
  }
  k[KH_TRL_END] = te;
  if (k[KH_PROP] > te) { k[KH_PROP] = te; }
  k[KH_LVL] = target_lvl;
}

u32 full_kitten_learn_unit0(u32 *k, u32 lit, u32 src_cid, bool from_res) {
  u32 nc = k[KH_NC]; u32 off = k[KH_ALEN]; u32 cap = k[KH_ACAP];
  u32 ante = k[KH_ANTE]; u32 need = 1u;
  if (ante != 0u) {
    if (from_res) {
      u32 nr = k[KH_NRES];
      if (nr > 256u) { return 0xFFFFFFFFu; }
      need = 1u + nr;
    } else {
      need = 2u;
      u32 soff = k[KO_CL_OFF + src_cid]; u32 ssz = k[KO_CL_META + src_cid] & 0xFFFFu;
      u32 i = 0u;
      while (i < ssz) {
        u32 ot = k[KO_ARENA + soff + i];
        if (ot != lit && k[KO_RSN + (ot >> 1)] != 0xFFFFFFFFu) { need = need + 1u; }
        i = i + 1u;
      }
    }
  }
  if (nc >= K_MAX_CL || off + need > cap) { return 0xFFFFFFFFu; }
  k[KO_ARENA + off] = lit; u32 ap = off + 1u; u32 na = 0u;
  if (ante != 0u) {
    if (from_res) {
      u32 nr = k[KH_NRES]; u32 i = 0u;
      while (i < nr) {
        k[KO_ARENA + ap] = k[KO_RES + i]; ap = ap + 1u; na = na + 1u; i = i + 1u;
      }
    } else {
      k[KO_ARENA + ap] = src_cid; ap = ap + 1u; na = 1u;
      u32 soff = k[KO_CL_OFF + src_cid]; u32 ssz = k[KO_CL_META + src_cid] & 0xFFFFu;
      u32 i = 0u;
      while (i < ssz) {
        u32 ot = k[KO_ARENA + soff + i];
        if (ot != lit) {
          u32 rc = k[KO_RSN + (ot >> 1)];
          if (rc != 0xFFFFFFFFu) { k[KO_ARENA + ap] = rc; ap = ap + 1u; na = na + 1u; }
        }
        i = i + 1u;
      }
    }
  }
  k[KH_ALEN] = ap; k[KO_CL_OFF + nc] = off;
  k[KO_CL_META + nc] = 1u | KM_LRN; k[KO_CL_AUX + nc] = na;
  k[KH_NC] = nc + 1u;
  u32 nu = k[KH_NUNITS];
  if (nu < 256u) { k[KO_UNITS + nu] = nc; k[KH_NUNITS] = nu + 1u; }
  return nc;
}

u32 full_kitten_propagate(u32 *k) {
  while (k[KH_PROP] < k[KH_TRL_END]) {
    u32 lit = k[KO_TRL + k[KH_PROP]]; k[KH_PROP] = k[KH_PROP] + 1u;
    u32 nl = lit ^ 1u; k[KH_TICKS] = k[KH_TICKS] + 1u;
    u32 prev = 0xFFFFFFFFu; u32 w = k[KO_WHEAD + nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = k[KO_WNEXT + w];
      if (k[KO_VALS + k[KO_WBLIT + w]] == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1; u32 slot = w & 1u;
      u32 off = k[KO_CL_OFF + cid]; u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
      u32 other = k[KO_ARENA + off + (slot ^ 1u)];
      if (k[KO_VALS + other] == 1u) { k[KO_WBLIT + w] = other; prev = w; w = nxt; continue; }
      k[KH_TICKS] = k[KH_TICKS] + 1u;
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = k[KO_ARENA + off + r];
        if (k[KO_VALS + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        k[KO_ARENA + off + slot] = repl; k[KO_ARENA + off + ri] = nl;
        if (prev == 0xFFFFFFFFu) { k[KO_WHEAD + nl] = nxt; } else { k[KO_WNEXT + prev] = nxt; }
        k[KO_WBLIT + w] = other; k[KO_WNEXT + w] = k[KO_WHEAD + repl]; k[KO_WHEAD + repl] = w;
        w = nxt; continue;
      }
      k[KO_WBLIT + w] = other; prev = w; w = nxt;
      u32 ov = k[KO_VALS + other];
      if (ov == 2u) { return cid; }
      if (ov == 0u) {
        u32 rsn = cid;
        if (k[KH_LVL] == 0u && k[KH_ANTE] != 0u) {
          rsn = full_kitten_learn_unit0(k, other, cid, false);
          if (rsn == 0xFFFFFFFFu) { return 0xFFFFFFFEu; }
        }
        full_kitten_assign(k, other, rsn);
      }
    }
  }
  return 0xFFFFFFFFu;
}

void full_kitten_ana_clause(u32 *k, u32 cid, u32 skip_v) {
  u32 clvl = k[KH_LVL]; u32 off = k[KO_CL_OFF + cid];
  u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
  if (k[KH_ANTE] != 0u) {
    u32 nr = k[KH_NRES];
    if (nr < 256u) { k[KO_RES + nr] = cid; k[KH_NRES] = nr + 1u; }
    else if (nr == 256u) { k[KH_NRES] = 257u; }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = k[KO_ARENA + off + i]; u32 v = l >> 1;
    if (v != skip_v) {
      u32 vlvl = k[KO_LVL + v];
      if (vlvl == 0u) {
        u32 r0 = k[KO_RSN + v];
        if (k[KH_ANTE] != 0u && r0 != 0xFFFFFFFFu) {
          u32 nr = k[KH_NRES];
          if (nr < 256u) { k[KO_RES + nr] = r0; k[KH_NRES] = nr + 1u; }
          else if (nr == 256u) { k[KH_NRES] = 257u; }
        }
      } else if ((k[KO_FLAGS + v] & 2u) == 0u) {
        k[KO_FLAGS + v] = k[KO_FLAGS + v] | 2u;
        if (k[KH_NANA] < 128u) { k[KO_ANA + k[KH_NANA]] = v; k[KH_NANA] = k[KH_NANA] + 1u; }
        if (vlvl == clvl) { k[KH_STATUS] = k[KH_STATUS] + 1u; }
        else if (k[KH_NKL] < 128u) { k[KO_KL + k[KH_NKL]] = l; k[KH_NKL] = k[KH_NKL] + 1u; }
      }
    }
    i = i + 1u;
  }
}

bool full_kitten_analyze(u32 *k, u32 confl_cid) {
  k[KH_NRES] = 0u; k[KH_NKL] = 1u; k[KH_NANA] = 0u; k[KH_STATUS] = 0u;
  full_kitten_ana_clause(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[KH_LVL]; u32 idx = k[KH_TRL_END]; u32 uip = 0xFFFFFFFFu;
  while (k[KH_STATUS] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = k[KO_TRL + idx]; u32 pv = p >> 1;
    if ((k[KO_FLAGS + pv] & 2u) != 0u && k[KO_LVL + pv] == clvl) {
      k[KH_STATUS] = k[KH_STATUS] - 1u;
      if (k[KH_STATUS] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = k[KO_RSN + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_kitten_ana_clause(k, rsn, pv);
    }
  }
  u32 ai = 0u;
  while (ai < k[KH_NANA]) {
    u32 av = k[KO_ANA + ai]; k[KO_FLAGS + av] = k[KO_FLAGS + av] & (~2u); ai = ai + 1u;
  }
  if (uip == 0xFFFFFFFFu || (k[KH_ANTE] != 0u && k[KH_NRES] > 256u)) { return false; }
  k[KO_KL] = uip;
  u32 nkl = k[KH_NKL]; u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 il = k[KO_LVL + (k[KO_KL + i] >> 1)];
    if (il > jlvl) { jlvl = il; wi = i; }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = k[KO_KL + 1u]; k[KO_KL + 1u] = k[KO_KL + wi]; k[KO_KL + wi] = t;
  }
  full_kitten_backtrack(k, jlvl);
  ai = 0u; while (ai < k[KH_NANA]) { full_kitten_mtf(k, k[KO_ANA + ai]); ai = ai + 1u; }
  if (nkl == 1u) {
    u32 ucid = full_kitten_learn_unit0(k, uip, 0xFFFFFFFFu, true);
    if (ucid == 0xFFFFFFFFu) { return false; }
    full_kitten_assign(k, uip, ucid); return true;
  }
  u32 nc = k[KH_NC]; u32 off = k[KH_ALEN]; u32 cap = k[KH_ACAP];
  u32 nr = (k[KH_ANTE] != 0u) ? k[KH_NRES] : 0u;
  if (nc >= K_MAX_CL || off + nkl + nr > cap) { return false; }
  i = 0u; while (i < nkl) { k[KO_ARENA + off + i] = k[KO_KL + i]; i = i + 1u; }
  i = 0u; while (i < nr) { k[KO_ARENA + off + nkl + i] = k[KO_RES + i]; i = i + 1u; }
  k[KH_ALEN] = off + nkl + nr;
  k[KO_CL_OFF + nc] = off; k[KO_CL_META + nc] = nkl | KM_LRN; k[KO_CL_AUX + nc] = nr;
  k[KH_NC] = nc + 1u;
  full_kitten_watch(k, nc, k[KO_KL], k[KO_KL + 1u]);
  full_kitten_assign(k, uip, nc);
  return true;
}

void full_kitten_build_failing(u32 *k, u32 alit) {
  u32 nv = k[KH_NV]; u32 i = 0u;
  while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  k[KO_FLAGS + (alit >> 1)] = k[KO_FLAGS + (alit >> 1)] | 2u;
  i = k[KH_TRL_END];
  while (i > 0u) {
    i = i - 1u;
    u32 lit = k[KO_TRL + i]; u32 v = lit >> 1;
    if ((k[KO_FLAGS + v] & 2u) == 0u) { continue; }
    k[KO_FLAGS + v] = k[KO_FLAGS + v] & (~2u);
    u32 rsn = k[KO_RSN + v];
    if (rsn == 0xFFFFFFFFu) { continue; }
    k[KO_CL_META + rsn] = k[KO_CL_META + rsn] | KM_CORE;
    u32 off = k[KO_CL_OFF + rsn]; u32 sz = k[KO_CL_META + rsn] & 0xFFFFu; u32 j = 0u;
    while (j < sz) {
      u32 lv = k[KO_ARENA + off + j] >> 1;
      if (lv != v) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
      j = j + 1u;
    }
  }
  i = 0u; while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  k[KH_FAILING] = 1u;
}

u64 full_kitten_solve(FullHdr *h, u64 tick_lim) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  full_kitten_backtrack(k, 0u);
  if (k[KH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  k[KH_TICK_LIM] = k[KH_TICKS] + (u32)tick_lim;
  k[KH_FAILING] = 0xFFFFFFFFu;
  u32 ui = 0u;
  while (ui < k[KH_NUNITS]) {
    u32 ucid = k[KO_UNITS + ui]; u32 ul = k[KO_ARENA + k[KO_CL_OFF + ucid]];
    u32 uv = k[KO_VALS + ul];
    if (uv == 2u) { k[KH_INCONS] = ucid; return 20ULL; }
    if (uv == 0u) { full_kitten_assign(k, ul, ucid); }
    ui = ui + 1u;
  }
  u32 confl = full_kitten_propagate(k);
  if (confl == 0xFFFFFFFEu) { return 0ULL; }
  if (confl != 0xFFFFFFFFu) { k[KH_INCONS] = confl; return 20ULL; }
  while (k[KH_TICKS] <= k[KH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[KH_LVL] == 0u) { k[KH_INCONS] = confl; return 20ULL; }
      if (!full_kitten_analyze(k, confl)) { return 0ULL; }
      confl = full_kitten_propagate(k);
      if (confl == 0xFFFFFFFEu) { return 0ULL; }
      continue;
    }
    u32 ad = 0u; u32 na = k[KH_NASSUMP]; bool did_assump = false;
    while (ad < na) {
      u32 a = k[KO_ASSUMP + ad]; u32 av = k[KO_VALS + a];
      if (av == 2u) { full_kitten_build_failing(k, a); return 20ULL; }
      if (av == 0u) {
        k[KH_LVL] = k[KH_LVL] + 1u; full_kitten_assign(k, a, 0xFFFFFFFFu);
        confl = full_kitten_propagate(k); did_assump = true; break;
      }
      ad = ad + 1u;
    }
    if (confl == 0xFFFFFFFEu) { return 0ULL; }
    if (did_assump) { continue; }
    if (k[KH_UNASS] == 0u) { return 10ULL; }
    u32 cur = k[KH_QSEARCH]; u32 nv = k[KH_NV]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = k[KO_QPREV + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[KH_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = k[KO_QPREV + cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    k[KH_QSEARCH] = pick;
    u32 ph = (k[KO_FLAGS + pick] ^ k[KH_PHASE]) & 1u;
    k[KH_LVL] = k[KH_LVL] + 1u;
    full_kitten_assign(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_kitten_propagate(k);
    if (confl == 0xFFFFFFFEu) { return 0ULL; }
  }
  return 0ULL;
}

u32 full_kitten_core(FullHdr *h) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE; u32 nc = k[KH_NC];
  if (k[KH_FAILING] == 0xFFFFFFFFu) {
    u32 i = 0u;
    while (i < nc) { k[KO_CL_META + i] = k[KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
    u32 inc = k[KH_INCONS];
    if (inc != 0xFFFFFFFFu) {
      k[KO_CL_META + inc] = k[KO_CL_META + inc] | KM_CORE;
      u32 off = k[KO_CL_OFF + inc]; u32 sz = k[KO_CL_META + inc] & 0xFFFFu;
      u32 j = 0u;
      while (j < sz) {
        u32 r0 = k[KO_RSN + (k[KO_ARENA + off + j] >> 1)];
        if (r0 != 0xFFFFFFFFu) { k[KO_CL_META + r0] = k[KO_CL_META + r0] | KM_CORE; }
        j = j + 1u;
      }
    }
  }
  u32 cid = nc;
  while (cid > 0u) {
    cid = cid - 1u; u32 meta = k[KO_CL_META + cid];
    if ((meta & KM_CORE) != 0u && (meta & KM_LRN) != 0u) {
      u32 off = k[KO_CL_OFF + cid]; u32 sz = meta & 0xFFFFu; u32 na = k[KO_CL_AUX + cid];
      u32 j = 0u;
      while (j < na) {
        u32 ant = k[KO_ARENA + off + sz + j];
        if (ant < nc) { k[KO_CL_META + ant] = k[KO_CL_META + ant] | KM_CORE; }
        j = j + 1u;
      }
    }
  }
  u32 csz = 0u; u32 i = 0u;
  while (i < k[KH_ORIG_NC]) {
    if ((k[KO_CL_META + i] & KM_CORE) != 0u) { csz = csz + 1u; }
    i = i + 1u;
  }
  return csz;
}

void full_kitten_shrink(FullHdr *h) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE; u32 onc = k[KH_ORIG_NC];
  u32 dst = 0u; u32 ap = 0u; u32 i = 0u;
  while (i < onc) {
    u32 meta = k[KO_CL_META + i];
    if ((meta & KM_CORE) != 0u) {
      u32 off = k[KO_CL_OFF + i]; u32 sz = meta & 0xFFFFu;
      if (ap != off) {
        u32 j = 0u; while (j < sz) { k[KO_ARENA + ap + j] = k[KO_ARENA + off + j]; j = j + 1u; }
      }
      k[KO_CL_OFF + dst] = ap; k[KO_CL_META + dst] = sz; k[KO_CL_AUX + dst] = k[KO_CL_AUX + i];
      ap = ap + sz; dst = dst + 1u;
    }
    i = i + 1u;
  }
  k[KH_NC] = dst; k[KH_ORIG_NC] = dst; k[KH_ALEN] = ap;
  k[KH_LVL] = 0u; k[KH_PROP] = 0u; k[KH_TRL_END] = 0u; k[KH_UNASS] = k[KH_NV];
  k[KH_INCONS] = 0xFFFFFFFFu; k[KH_FAILING] = 0xFFFFFFFFu; k[KH_NUNITS] = 0u;
  k[KH_PHASE] = k[KH_PHASE] ^ 1u; k[KH_QSEARCH] = k[KH_QLAST];
  u32 nl = k[KH_NV] << 1; i = 0u;
  while (i < nl) { k[KO_VALS + i] = 0u; k[KO_WHEAD + i] = 0xFFFFFFFFu; i = i + 1u; }
  i = 0u; while (i < k[KH_NV]) { k[KO_LVL + i] = 0u; k[KO_RSN + i] = 0xFFFFFFFFu; i = i + 1u; }
  i = 0u;
  while (i < dst) {
    u32 off = k[KO_CL_OFF + i]; u32 sz = k[KO_CL_META + i] & 0xFFFFu;
    if (sz == 0u) { if (k[KH_INCONS] == 0xFFFFFFFFu) { k[KH_INCONS] = i; } }
    else if (sz == 1u) {
      u32 nu = k[KH_NUNITS]; if (nu < 256u) { k[KO_UNITS + nu] = i; k[KH_NUNITS] = nu + 1u; }
    }
    else { full_kitten_watch(k, i, k[KO_ARENA + off], k[KO_ARENA + off + 1u]); }
    i = i + 1u;
  }
}

bool full_kitten_flip(FullHdr *h, u32 lit) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE; u32 v = lit >> 1;
  if (v >= k[KH_NV] || k[KO_VALS + lit] != 1u || k[KO_LVL + v] == 0u) { return false; }
  u32 w = k[KO_WHEAD + lit]; u32 prev = 0xFFFFFFFFu;
  while (w != 0xFFFFFFFFu) {
    u32 nxt = k[KO_WNEXT + w];
    u32 cid = w >> 1; u32 slot = w & 1u; u32 off = k[KO_CL_OFF + cid];
    u32 sz = k[KO_CL_META + cid] & 0xFFFFu; u32 other = k[KO_ARENA + off + (slot ^ 1u)];
    if (k[KO_VALS + other] == 1u) { k[KO_WBLIT + w] = other; prev = w; w = nxt; continue; }
    u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
    while (r < sz) {
      u32 cand = k[KO_ARENA + off + r];
      if (cand != lit && k[KO_VALS + cand] == 1u) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) { return false; }
    k[KO_ARENA + off + slot] = repl; k[KO_ARENA + off + ri] = lit;
    if (prev == 0xFFFFFFFFu) { k[KO_WHEAD + lit] = nxt; } else { k[KO_WNEXT + prev] = nxt; }
    k[KO_WBLIT + w] = other; k[KO_WNEXT + w] = k[KO_WHEAD + repl]; k[KO_WHEAD + repl] = w;
    w = nxt;
  }
  k[KO_VALS + lit] = 2u; k[KO_VALS + (lit ^ 1u)] = 1u;
  return true;
}
"

def fullKittenModule : LeanQbe.T.Module :=
  { fns := fullKitten_fns, externs := [], exits := [] }

theorem full_kitten_init_wf : Func.Wf full_kitten_init_body := by t_wf_reify
theorem full_kitten_watch_wf : Func.Wf full_kitten_watch_body := by t_wf_reify
theorem full_kitten_add_clause_wf : Func.Wf full_kitten_add_clause_body := by t_wf_reify
theorem full_kitten_assign_wf : Func.Wf full_kitten_assign_body := by t_wf_reify
theorem full_kitten_mtf_wf : Func.Wf full_kitten_mtf_body := by t_wf_reify
theorem full_kitten_backtrack_wf : Func.Wf full_kitten_backtrack_body := by t_wf_reify
theorem full_kitten_learn_unit0_wf : Func.Wf full_kitten_learn_unit0_body := by t_wf_reify
theorem full_kitten_propagate_wf : Func.Wf full_kitten_propagate_body := by t_wf_reify
theorem full_kitten_ana_clause_wf : Func.Wf full_kitten_ana_clause_body := by t_wf_reify
theorem full_kitten_analyze_wf : Func.Wf full_kitten_analyze_body := by t_wf_reify
theorem full_kitten_build_failing_wf : Func.Wf full_kitten_build_failing_body := by t_wf_reify
theorem full_kitten_solve_wf : Func.Wf full_kitten_solve_body := by t_wf_reify
theorem full_kitten_core_wf : Func.Wf full_kitten_core_body := by t_wf_reify
theorem full_kitten_shrink_wf : Func.Wf full_kitten_shrink_body := by t_wf_reify
theorem full_kitten_flip_wf : Func.Wf full_kitten_flip_body := by t_wf_reify

theorem fullKitten_fns_wf : ∀ f ∈ fullKitten_fns, f.Wf := by
  simp only [fullKitten_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_kitten_init_wf, full_kitten_watch_wf, full_kitten_add_clause_wf,
    full_kitten_assign_wf, full_kitten_mtf_wf, full_kitten_backtrack_wf,
    full_kitten_learn_unit0_wf, full_kitten_propagate_wf, full_kitten_ana_clause_wf,
    full_kitten_analyze_wf, full_kitten_build_failing_wf, full_kitten_solve_wf,
    full_kitten_core_wf, full_kitten_shrink_wf, full_kitten_flip_wf⟩

theorem fullKitten_acyclic : fullKittenModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full
