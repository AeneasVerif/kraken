module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M4b — 512-Var `kitten` + Partition-Class Sweeping & `FL_SWEEP` Re-Arming

Standalone, zero-conflict M4b upgrade addressing Canary #3 (`sweep.c` + `kitten.c`) on the
byte-identical `144`-word (`FullHdr`) arena layout (`Full1.lean`):
1. **512-var scratch-resident `kitten` sub-solver (`12` fns, `K512_MAX_V = 512`,
   `K512_MAX_ORIG = 1536`, `K512_MAX_CL = 2048`, `K512_MIN_SCR = 24576`, fitting cleanly inside
   existing `32768`-word `scratch_buf`):**
   - `full_k512_init`, `full_k512_watch`, `full_k512_assign`, `full_k512_add_clause`,
     `full_k512_mtf`, `full_k512_backtrack`, `full_k512_propagate`, `full_k512_ana_clause`,
     `full_k512_analyze`, `full_k512_solve`, `full_k512_flip`, `full_k512_add_live`.
2. **512-var cone extraction, 64-bit random simulation + multi-round flip refinement,
   1024-bucket partition-class hash table, live equivalence/unit merging, and `FL_SWEEP`
   re-arming (`12` fns):**
   - `full_m4_sweep_cone`, `full_m4_sweep_refine_sig`, `full_m4_sweep_rand_phases`,
     `full_m4_sweep_flip_round`, `full_m4_sweep_sim`, `full_m4_sweep_rearm`,
     `full_m4_sweep_build_pht`, `full_m4_sweep_units`, `full_m4_sweep_classes`,
     `full_m4_sweep_var`, `full_m4_sweep_dense`, `full_m4_sweep_sat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! fullM4Sweep "
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
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE 1u
#define FL_SWEEP  1024u

#define PHT_HEAD   256u
#define PHT_SZ     1024u
#define PHT_MASK   1023u
#define PHT_NEXT   1280u
#define PHT_MERGED 1792u

#define K512_BASE     2304u
#define K512_MAX_V    512u
#define K512_MAX_L    1024u
#define K512_MAX_ORIG 1536u
#define K512_MAX_CL   2048u
#define K512_MIN_SCR  24576ULL

#define K5H_NV       0u
#define K5H_NC       1u
#define K5H_LVL      2u
#define K5H_PROP     3u
#define K5H_TRL_END  4u
#define K5H_UNASS    5u
#define K5H_INCONS   6u
#define K5H_QFIRST   7u
#define K5H_QLAST    8u
#define K5H_QSEARCH  9u
#define K5H_QSTAMP   10u
#define K5H_TICKS    11u
#define K5H_TICK_LIM 12u
#define K5H_ALEN     13u
#define K5H_ACAP     14u
#define K5H_NASSUMP  15u
#define K5H_NKL      16u
#define K5H_NANA     17u
#define K5H_STATUS   18u
#define K5H_PHASE    19u

#define K5O_LVL    32u
#define K5O_RSN    544u
#define K5O_QPREV  1056u
#define K5O_QNEXT  1568u
#define K5O_QSTAMP 2080u
#define K5O_TRL    2592u
#define K5O_FLAGS  3104u
#define K5O_ANA    3616u
#define K5O_KL     4128u
#define K5O_ASSUMP 4640u
#define K5O_VALS   5152u
#define K5O_WHEAD  6176u
#define K5O_WNEXT  7200u
#define K5O_WBLIT  11296u
#define K5O_CL_OFF 15392u
#define K5O_CL_SZ  17440u
#define K5O_ARENA  19488u

extern u64 full_rng_next(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);

void full_k512_init(FullHdr *h, u32 nv) {
  if (h->scratch_cap < K512_MIN_SCR || nv > K512_MAX_V) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u32 i = 0u;
  while (i < 32u) { k[i] = 0u; i = i + 1u; }
  k[K5H_NV] = nv; k[K5H_UNASS] = nv;
  k[K5H_TICK_LIM] = 16384u;
  k[K5H_ACAP] = (u32)(h->scratch_cap - (u64)K512_BASE - (u64)K5O_ARENA);
  if (nv == 0u) {
    k[K5H_QFIRST] = 0xFFFFFFFFu; k[K5H_QLAST] = 0xFFFFFFFFu; k[K5H_QSEARCH] = 0xFFFFFFFFu;
  } else {
    k[K5H_QFIRST] = 0u; k[K5H_QLAST] = nv - 1u; k[K5H_QSEARCH] = nv - 1u; k[K5H_QSTAMP] = nv;
  }
  i = 0u;
  while (i < nv) {
    k[K5O_LVL + i] = 0u; k[K5O_RSN + i] = 0xFFFFFFFFu; k[K5O_FLAGS + i] = 0u;
    k[K5O_QSTAMP + i] = i + 1u;
    k[K5O_QPREV + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    k[K5O_QNEXT + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  u32 nl = nv << 1; i = 0u;
  while (i < nl) { k[K5O_VALS + i] = 0u; k[K5O_WHEAD + i] = 0xFFFFFFFFu; i = i + 1u; }
}

void full_k512_watch(u32 *k, u32 cid, u32 l0, u32 l1) {
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  k[K5O_WBLIT + w0] = l1; k[K5O_WNEXT + w0] = k[K5O_WHEAD + l0]; k[K5O_WHEAD + l0] = w0;
  k[K5O_WBLIT + w1] = l0; k[K5O_WNEXT + w1] = k[K5O_WHEAD + l1]; k[K5O_WHEAD + l1] = w1;
}

void full_k512_assign(u32 *k, u32 lit, u32 rsn) {
  u32 v = lit >> 1; u32 te = k[K5H_TRL_END];
  k[K5O_VALS + lit] = 1u; k[K5O_VALS + (lit ^ 1u)] = 2u;
  k[K5O_LVL + v] = k[K5H_LVL]; k[K5O_RSN + v] = rsn;
  k[K5O_TRL + te] = lit; k[K5H_TRL_END] = te + 1u;
  if (k[K5H_UNASS] > 0u) { k[K5H_UNASS] = k[K5H_UNASS] - 1u; }
  u32 fl = k[K5O_FLAGS + v];
  k[K5O_FLAGS + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

bool full_k512_add_clause(FullHdr *h, u32 *lits, u32 sz) {
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  if (sz == 0u) { k[K5H_INCONS] = 1u; return true; }
  if (sz == 1u) {
    u32 ul = lits[0]; u32 uv = k[K5O_VALS + ul];
    if (uv == 2u) { k[K5H_INCONS] = 1u; }
    else if (uv == 0u) { full_k512_assign(k, ul, 0xFFFFFFFFu); }
    return true;
  }
  u32 nc = k[K5H_NC]; u32 off = k[K5H_ALEN];
  if (nc >= K512_MAX_CL || off + sz > k[K5H_ACAP]) { return false; }
  u32 i = 0u;
  while (i < sz) { k[K5O_ARENA + off + i] = lits[i]; i = i + 1u; }
  k[K5H_ALEN] = off + sz;
  k[K5O_CL_OFF + nc] = off; k[K5O_CL_SZ + nc] = sz;
  k[K5H_NC] = nc + 1u;
  full_k512_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_k512_mtf(u32 *k, u32 v) {
  u32 nv = k[K5H_NV];
  if (v >= nv || v == k[K5H_QLAST]) { return; }
  u32 pv = k[K5O_QPREV + v]; u32 nxt = k[K5O_QNEXT + v];
  if (k[K5O_VALS + (v << 1)] != 0u && v == k[K5H_QSEARCH]) {
    if (pv < nv) { k[K5H_QSEARCH] = pv; } else if (nxt < nv) { k[K5H_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[K5H_QFIRST] = nxt; } else { k[K5O_QNEXT + pv] = nxt; }
  if (nxt >= nv) { k[K5H_QLAST] = pv; } else { k[K5O_QPREV + nxt] = pv; }
  u32 ol = k[K5H_QLAST];
  k[K5O_QPREV + v] = ol; k[K5O_QNEXT + v] = 0xFFFFFFFFu; k[K5H_QLAST] = v;
  if (ol >= nv) { k[K5H_QFIRST] = v; } else { k[K5O_QNEXT + ol] = v; }
  if (k[K5H_QSTAMP] < 0xFFFFFFF0u) {
    k[K5H_QSTAMP] = k[K5H_QSTAMP] + 1u; k[K5O_QSTAMP + v] = k[K5H_QSTAMP];
  }
  if (k[K5O_VALS + (v << 1)] == 0u) { k[K5H_QSEARCH] = v; }
}

void full_k512_backtrack(u32 *k, u32 target_lvl) {
  u32 te = k[K5H_TRL_END]; u32 best_st = 0u;
  if (k[K5H_QSEARCH] < k[K5H_NV]) { best_st = k[K5O_QSTAMP + k[K5H_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = k[K5O_TRL + te - 1u]; u32 v = lit >> 1;
    if (k[K5O_LVL + v] <= target_lvl) { break; }
    te = te - 1u;
    k[K5O_VALS + lit] = 0u; k[K5O_VALS + (lit ^ 1u)] = 0u;
    k[K5O_LVL + v] = 0u; k[K5O_RSN + v] = 0xFFFFFFFFu;
    k[K5H_UNASS] = k[K5H_UNASS] + 1u;
    if (k[K5O_QSTAMP + v] > best_st) { best_st = k[K5O_QSTAMP + v]; k[K5H_QSEARCH] = v; }
  }
  k[K5H_TRL_END] = te;
  if (k[K5H_PROP] > te) { k[K5H_PROP] = te; }
  k[K5H_LVL] = target_lvl;
}

u32 full_k512_propagate(u32 *k) {
  while (k[K5H_PROP] < k[K5H_TRL_END]) {
    u32 lit = k[K5O_TRL + k[K5H_PROP]]; k[K5H_PROP] = k[K5H_PROP] + 1u;
    u32 nl = lit ^ 1u; k[K5H_TICKS] = k[K5H_TICKS] + 1u;
    u32 prev = 0xFFFFFFFFu; u32 w = k[K5O_WHEAD + nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = k[K5O_WNEXT + w];
      if (k[K5O_VALS + k[K5O_WBLIT + w]] == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1; u32 slot = w & 1u;
      u32 off = k[K5O_CL_OFF + cid]; u32 sz = k[K5O_CL_SZ + cid];
      u32 other = k[K5O_ARENA + off + (slot ^ 1u)];
      if (k[K5O_VALS + other] == 1u) { k[K5O_WBLIT + w] = other; prev = w; w = nxt; continue; }
      k[K5H_TICKS] = k[K5H_TICKS] + 1u;
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = k[K5O_ARENA + off + r];
        if (k[K5O_VALS + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        k[K5O_ARENA + off + slot] = repl; k[K5O_ARENA + off + ri] = nl;
        if (prev == 0xFFFFFFFFu) { k[K5O_WHEAD + nl] = nxt; } else { k[K5O_WNEXT + prev] = nxt; }
        k[K5O_WBLIT + w] = other; k[K5O_WNEXT + w] = k[K5O_WHEAD + repl]; k[K5O_WHEAD + repl] = w;
        w = nxt; continue;
      }
      k[K5O_WBLIT + w] = other; prev = w; w = nxt;
      u32 ov = k[K5O_VALS + other];
      if (ov == 2u) { return cid; }
      if (ov == 0u) { full_k512_assign(k, other, cid); }
    }
  }
  return 0xFFFFFFFFu;
}

void full_k512_ana_clause(u32 *k, u32 cid, u32 skip_v) {
  u32 clvl = k[K5H_LVL]; u32 off = k[K5O_CL_OFF + cid]; u32 sz = k[K5O_CL_SZ + cid];
  u32 i = 0u;
  while (i < sz) {
    u32 l = k[K5O_ARENA + off + i]; u32 v = l >> 1;
    if (v != skip_v) {
      u32 vlvl = k[K5O_LVL + v];
      if (vlvl > 0u && (k[K5O_FLAGS + v] & 2u) == 0u) {
        k[K5O_FLAGS + v] = k[K5O_FLAGS + v] | 2u;
        if (k[K5H_NANA] < K512_MAX_V) {
          k[K5O_ANA + k[K5H_NANA]] = v; k[K5H_NANA] = k[K5H_NANA] + 1u;
        }
        if (vlvl == clvl) { k[K5H_STATUS] = k[K5H_STATUS] + 1u; }
        else if (k[K5H_NKL] < K512_MAX_V) {
          k[K5O_KL + k[K5H_NKL]] = l; k[K5H_NKL] = k[K5H_NKL] + 1u;
        }
      }
    }
    i = i + 1u;
  }
}

bool full_k512_analyze(u32 *k, u32 confl_cid) {
  k[K5H_NKL] = 1u; k[K5H_NANA] = 0u; k[K5H_STATUS] = 0u;
  full_k512_ana_clause(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[K5H_LVL]; u32 idx = k[K5H_TRL_END]; u32 uip = 0xFFFFFFFFu;
  while (k[K5H_STATUS] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = k[K5O_TRL + idx]; u32 pv = p >> 1;
    if ((k[K5O_FLAGS + pv] & 2u) != 0u && k[K5O_LVL + pv] == clvl) {
      k[K5H_STATUS] = k[K5H_STATUS] - 1u;
      if (k[K5H_STATUS] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = k[K5O_RSN + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k512_ana_clause(k, rsn, pv);
    }
  }
  u32 ai = 0u;
  while (ai < k[K5H_NANA]) {
    u32 av = k[K5O_ANA + ai]; k[K5O_FLAGS + av] = k[K5O_FLAGS + av] & (~2u); ai = ai + 1u;
  }
  if (uip == 0xFFFFFFFFu) { return false; }
  k[K5O_KL] = uip;
  u32 nkl = k[K5H_NKL]; u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 il = k[K5O_LVL + (k[K5O_KL + i] >> 1)];
    if (il > jlvl) { jlvl = il; wi = i; }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = k[K5O_KL + 1u]; k[K5O_KL + 1u] = k[K5O_KL + wi]; k[K5O_KL + wi] = t;
  }
  full_k512_backtrack(k, jlvl);
  ai = 0u; while (ai < k[K5H_NANA]) { full_k512_mtf(k, k[K5O_ANA + ai]); ai = ai + 1u; }
  if (nkl == 1u) { full_k512_assign(k, uip, 0xFFFFFFFFu); return true; }
  u32 nc = k[K5H_NC]; u32 off = k[K5H_ALEN]; u32 cap = k[K5H_ACAP];
  if (nc >= K512_MAX_CL || off + nkl > cap) { return false; }
  i = 0u; while (i < nkl) { k[K5O_ARENA + off + i] = k[K5O_KL + i]; i = i + 1u; }
  k[K5H_ALEN] = off + nkl;
  k[K5O_CL_OFF + nc] = off; k[K5O_CL_SZ + nc] = nkl; k[K5H_NC] = nc + 1u;
  full_k512_watch(k, nc, k[K5O_KL], k[K5O_KL + 1u]);
  full_k512_assign(k, uip, nc);
  return true;
}

u64 full_k512_solve(FullHdr *h, u64 tick_lim) {
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  full_k512_backtrack(k, 0u);
  if (k[K5H_INCONS] != 0u) { return 20ULL; }
  u64 cur_t = (u64)k[K5H_TICKS];
  u64 rem_t = 0xFFFFFFFFULL - cur_t;
  k[K5H_TICK_LIM] = (tick_lim >= rem_t) ? 0xFFFFFFFFu : (u32)(cur_t + tick_lim);
  u32 confl = full_k512_propagate(k);
  if (confl != 0xFFFFFFFFu) { k[K5H_INCONS] = 1u; return 20ULL; }
  while (k[K5H_TICKS] < k[K5H_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[K5H_LVL] == 0u) { k[K5H_INCONS] = 1u; return 20ULL; }
      if (!full_k512_analyze(k, confl)) { return 0ULL; }
      confl = full_k512_propagate(k);
      continue;
    }
    u32 ad = 0u; u32 na = k[K5H_NASSUMP]; bool did_assump = false;
    while (ad < na) {
      u32 a = k[K5O_ASSUMP + ad]; u32 av = k[K5O_VALS + a];
      if (av == 2u) { return 20ULL; }
      if (av == 0u) {
        k[K5H_LVL] = k[K5H_LVL] + 1u; full_k512_assign(k, a, 0xFFFFFFFFu);
        confl = full_k512_propagate(k); did_assump = true; break;
      }
      ad = ad + 1u;
    }
    if (did_assump) { continue; }
    if (k[K5H_UNASS] == 0u) { return 10ULL; }
    u32 cur = k[K5H_QSEARCH]; u32 nv = k[K5H_NV]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (k[K5O_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = k[K5O_QPREV + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[K5H_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (k[K5O_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = k[K5O_QPREV + cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (k[K5O_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    k[K5H_QSEARCH] = pick;
    u32 ph = (k[K5O_FLAGS + pick] ^ k[K5H_PHASE]) & 1u;
    k[K5H_LVL] = k[K5H_LVL] + 1u;
    full_k512_assign(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k512_propagate(k);
  }
  return 0ULL;
}

bool full_k512_flip(FullHdr *h, u32 lit) {
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE; u32 v = lit >> 1;
  if (v >= k[K5H_NV] || k[K5O_VALS + lit] != 1u || k[K5O_LVL + v] == 0u) { return false; }
  u32 w = k[K5O_WHEAD + lit]; u32 prev = 0xFFFFFFFFu;
  while (w != 0xFFFFFFFFu) {
    u32 nxt = k[K5O_WNEXT + w];
    u32 cid = w >> 1; u32 slot = w & 1u; u32 off = k[K5O_CL_OFF + cid];
    u32 sz = k[K5O_CL_SZ + cid]; u32 other = k[K5O_ARENA + off + (slot ^ 1u)];
    if (k[K5O_VALS + other] == 1u) { k[K5O_WBLIT + w] = other; prev = w; w = nxt; continue; }
    u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
    while (r < sz) {
      u32 cand = k[K5O_ARENA + off + r];
      if (cand != lit && k[K5O_VALS + cand] == 1u) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) { return false; }
    k[K5O_ARENA + off + slot] = repl; k[K5O_ARENA + off + ri] = lit;
    if (prev == 0xFFFFFFFFu) { k[K5O_WHEAD + lit] = nxt; } else { k[K5O_WNEXT + prev] = nxt; }
    k[K5O_WBLIT + w] = other; k[K5O_WNEXT + w] = k[K5O_WHEAD + repl]; k[K5O_WHEAD + repl] = w;
    w = nxt;
  }
  k[K5O_VALS + lit] = 2u; k[K5O_VALS + (lit ^ 1u)] = 1u;
  return true;
}

void full_k512_add_live(FullHdr *h, u32 a, u32 b) {
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  full_k512_backtrack(k, 0u);
  if (k[K5H_INCONS] != 0u) { return; }
  if (b == 0xFFFFFFFFu) {
    u32 va = k[K5O_VALS + a];
    if (va == 2u) { k[K5H_INCONS] = 1u; }
    else if (va == 0u) { full_k512_assign(k, a, 0xFFFFFFFFu); }
    return;
  }
  u32 nc = k[K5H_NC]; u32 off = k[K5H_ALEN];
  if (nc >= K512_MAX_CL || off + 2u > k[K5H_ACAP]) { return; }
  k[K5O_ARENA + off] = a; k[K5O_ARENA + off + 1u] = b;
  k[K5H_ALEN] = off + 2u; k[K5O_CL_OFF + nc] = off; k[K5O_CL_SZ + nc] = 2u;
  k[K5H_NC] = nc + 1u;
  full_k512_watch(k, nc, a, b);
  u32 va = k[K5O_VALS + a]; u32 vb = k[K5O_VALS + b];
  if (va == 2u) {
    if (vb == 2u) { k[K5H_INCONS] = 1u; }
    else if (vb == 0u) { full_k512_assign(k, b, nc); }
  } else if (vb == 2u && va == 0u) {
    full_k512_assign(k, a, nc);
  }
}

u64 full_m4_sweep_cone(FullHdr *h, u32 root_v) {
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  full_k512_init(h, K512_MAX_V);
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u; u32 qi = 0u;
  while (qi < nv && nc < K512_MAX_ORIG) {
    u32 cv = cone_v[qi]; u32 cur_tmk = tmk[cv]; u32 map_c = cur_tmk - 1u;
    qi = qi + 1u; u32 pol = 0u;
    while (pol < 2u && nc < K512_MAX_ORIG) {
      u32 lit = (cv << 1) | pol;
      u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      u64 p = off;
      while (p < end && nc < K512_MAX_ORIG) {
        u32 w0 = wstk[p]; p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK; u32 ov = ot >> 1;
          if (ov != cv && vals[ot] == (i8)0 && (tmk[ov] != 0u || nv < K512_MAX_V)) {
            if (tmk[ov] == 0u) { nv = nv + 1u; tmk[ov] = nv; cone_v[nv - 1u] = ov; }
            if (lit < ot) {
              tmp[0] = (map_c << 1) | pol; tmp[1] = ((tmk[ov] - 1u) << 1) | (ot & 1u);
              if (full_k512_add_clause(h, tmp, 2u)) { nc = nc + 1u; }
            }
          }
          continue;
        }
        if (p >= end) { break; }
        u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
        if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz < 3u || sz > 8u) { continue; }
        bool sat = false; u32 cnt = 0u; u32 idx = 0u;
        while (idx < sz) {
          u32 l = ar[(u64)cr + 3ULL + (u64)idx];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (vals[l] == (i8)0) {
            u32 lv = l >> 1; u32 ltm = tmk[lv];
            if ((ltm != 0u && ltm < cur_tmk) || (lv == cv && (l & 1u) < pol)) {
              sat = true; break;
            }
            if (ltm == 0u && nv < K512_MAX_V) {
              nv = nv + 1u; tmk[lv] = nv; cone_v[nv - 1u] = lv;
            }
            if (tmk[lv] == 0u) { sat = true; break; }
            tmp[cnt] = ((tmk[lv] - 1u) << 1) | (l & 1u); cnt = cnt + 1u;
          }
          idx = idx + 1u;
        }
        if (!sat && cnt >= 2u && full_k512_add_clause(h, tmp, cnt)) { nc = nc + 1u; }
      }
      pol = pol + 1u;
    }
  }
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  k[K5H_NV] = nv; k[K5H_UNASS] = nv;
  if (nv > 0u) {
    k[K5H_QLAST] = nv - 1u; k[K5H_QSEARCH] = nv - 1u;
    k[K5H_QSTAMP] = nv; k[K5O_QNEXT + nv - 1u] = 0xFFFFFFFFu;
  }
  return (u64)nv | ((u64)nc << 16);
}

void full_m4_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit_idx) {
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u64 mask = 1ULL << (u64)(bit_idx & 63u); u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (k[K5O_VALS + (i << 1)] == 1u) { sig[gv] = sig[gv] | mask; }
    else { sig[gv] = sig[gv] & (~mask); }
    i = i + 1u;
  }
}

void full_m4_sweep_rand_phases(FullHdr *h, u32 nv) {
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u64 rbits = full_rng_next(h);
  u32 i = 0u;
  while (i < nv) {
    if ((i & 63u) == 0u && i > 0u) { rbits = full_rng_next(h); }
    u32 fl = k[K5O_FLAGS + i];
    k[K5O_FLAGS + i] = (fl & (~1u)) | ((u32)rbits & 1u);
    rbits = rbits >> 1; i = i + 1u;
  }
  k[K5H_PHASE] = k[K5H_PHASE] ^ 1u;
}

u32 full_m4_sweep_flip_round(FullHdr *h, u32 nv) {
  if (nv == 0u) { return 0u; }
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u32 start = (u32)(full_rng_next(h) % (u64)nv);
  u64 rbits = full_rng_next(h);
  u32 flipped = 0u; u32 step = 0u;
  while (step < nv) {
    if ((step & 63u) == 0u && step > 0u) { rbits = full_rng_next(h); }
    if ((rbits & 1ULL) != 0ULL) {
      u32 v = start + step;
      if (v >= nv) { v = v - nv; }
      u32 lit = (k[K5O_VALS + (v << 1)] == 1u) ? (v << 1) : ((v << 1) | 1u);
      if (full_k512_flip(h, lit)) { flipped = flipped + 1u; }
    }
    rbits = rbits >> 1; step = step + 1u;
  }
  return flipped;
}

u32 full_m4_sweep_sim(FullHdr *h, u32 nv, u64 tick_lim) {
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u32 i = 0u; while (i < nv) { sig[cone_v[i]] = 0ULL; i = i + 1u; }
  k[K5H_NASSUMP] = 0u;
  u64 st0 = full_k512_solve(h, tick_lim);
  if (st0 == 20ULL) { return 0xFFFFFFFFu; }
  if (st0 != 10ULL) { return 0u; }
  u32 rbit = 0u; full_m4_sweep_refine_sig(h, nv, rbit); rbit = 1u;
  u64 sim_lim = (tick_lim < 1024ULL) ? tick_lim : 1024ULL;
  u32 round = 0u;
  while (round < 4u && rbit < 64u && h->fuel > 0ULL) {
    u32 fr = 0u;
    while (fr < 3u && rbit < 64u) {
      if (full_m4_sweep_flip_round(h, nv) > 0u) {
        full_m4_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
      } else { break; }
      fr = fr + 1u;
    }
    round = round + 1u;
    u64 cur_t = (u64)k[K5H_TICKS];
    if (round < 4u && rbit < 64u && cur_t < sim_lim && h->fuel > 0ULL) {
      full_m4_sweep_rand_phases(h, nv);
      k[K5H_NASSUMP] = 0u;
      u64 st = full_k512_solve(h, sim_lim - cur_t);
      if (st == 20ULL) { return 0xFFFFFFFFu; }
      if (st != 10ULL) { break; }
      full_m4_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
    }
  }
  return rbit;
}

void full_m4_sweep_rearm(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  if ((u64)v >= cv) { return; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u32 *fl = (u32 *)h->flags;
  u32 pol = 0u;
  while (pol < 2u) {
    u32 lit = (v << 1) | pol;
    u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
    u64 p = off; u64 lim = 0ULL;
    while (p < end && lim < 128ULL) {
      u32 w0 = wstk[p]; p = p + 1ULL; lim = lim + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ov = (w0 & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && ov != v && (fl[ov] & FL_ACTIVE) != 0u) {
          fl[ov] = fl[ov] | FL_SWEEP;
        }
        continue;
      }
      if (p >= end) { break; }
      u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
      if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz > 16u) { continue; }
      u32 i = 0u;
      while (i < sz) {
        u32 lv = ar[(u64)cr + 3ULL + (u64)i] >> 1;
        if ((u64)lv < cv && lv != v && (fl[lv] & FL_ACTIVE) != 0u) {
          fl[lv] = fl[lv] | FL_SWEEP;
        }
        i = i + 1u;
      }
    }
    pol = pol + 1u;
  }
}

void full_m4_sweep_build_pht(FullHdr *h, u32 nv, u64 smask) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 b = 0u;
  while (b < PHT_SZ) { scr[PHT_HEAD + b] = 0xFFFFFFFFu; b = b + 1u; }
  u32 i = 0u;
  while (i < nv) {
    if (scr[PHT_MERGED + i] == 0u) {
      u32 gv = cone_v[i];
      u64 raw = sig[gv] & smask;
      u64 key = ((raw & 1ULL) != 0ULL) ? (raw ^ smask) : raw;
      u32 hidx = (u32)((key ^ (key >> 17) ^ (key >> 34) ^ (key >> 51)) & (u64)PHT_MASK);
      scr[PHT_NEXT + i] = scr[PHT_HEAD + hidx];
      scr[PHT_HEAD + hidx] = i;
    } else {
      scr[PHT_NEXT + i] = 0xFFFFFFFFu;
    }
    i = i + 1u;
  }
}

u64 full_m4_sweep_units(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *k = scr + K512_BASE;
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u; while (i < nv) { scr[PHT_MERGED + i] = 0u; i = i + 1u; }
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? (~0ULL) : ((1ULL << rbit) - 1ULL);
  i = 0u;
  while (i < nv && h->inconsistent == 0ULL && h->fuel > 0ULL && (u64)k[K5H_TICKS] < tick_lim) {
    u32 gv = cone_v[i];
    if (vals[gv << 1] != (i8)0) { scr[PHT_MERGED + i] = 1u; i = i + 1u; continue; }
    u64 s0 = sig[gv] & smask;
    if (s0 == 0ULL || s0 == smask) {
      u32 wf = (s0 == 0ULL) ? 0u : 1u;
      u32 test_lit = (i << 1) | wf;
      if (full_k512_flip(h, test_lit ^ 1u)) {
        if (rbit < 64u) {
          full_m4_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      } else {
        u64 rem = tick_lim - (u64)k[K5H_TICKS];
        k[K5H_NASSUMP] = 1u; k[K5O_ASSUMP] = test_lit;
        u64 d = full_k512_solve(h, rem);
        if (d == 20ULL) {
          u32 gl = (gv << 1) | (1u - wf);
          if (!full_add_unit(h, gl)) { return 0xFFFFFFFFFFFFFFFFULL; }
          scr[PHT_MERGED + i] = 1u;
          full_k512_add_live(h, test_lit ^ 1u, 0xFFFFFFFFu);
          full_m4_sweep_rearm(h, gv);
          h->sweep_cnt = h->sweep_cnt + 1ULL;
        } else if (d == 10ULL && rbit < 64u) {
          full_m4_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      }
    }
    i = i + 1u;
  }
  return (h->inconsistent != 0ULL) ? 0xFFFFFFFFFFFFFFFFULL : (u64)rbit;
}

u64 full_m4_sweep_classes(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *k = scr + K512_BASE;
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *fl = (u32 *)h->flags;
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? (~0ULL) : ((1ULL << rbit) - 1ULL);
  full_m4_sweep_build_pht(h, nv, smask);
  u32 b = 0u;
  while (b < PHT_SZ && h->inconsistent == 0ULL && h->fuel > 0ULL && (u64)k[K5H_TICKS] < tick_lim) {
    u32 a = scr[PHT_HEAD + b];
    while (a < nv && h->inconsistent == 0ULL && h->fuel > 0ULL && (u64)k[K5H_TICKS] < tick_lim) {
      if (scr[PHT_MERGED + a] == 0u) {
        u32 gv_a = cone_v[a];
        u32 c = scr[PHT_NEXT + a];
        while (c < nv && h->inconsistent == 0ULL && h->fuel > 0ULL &&
               (u64)k[K5H_TICKS] < tick_lim) {
          if (scr[PHT_MERGED + c] == 0u) {
            u32 gv_c = cone_v[c];
            u64 xr = (sig[gv_c] ^ sig[gv_a]) & smask;
            if (xr == 0ULL || xr == smask) {
              u32 pol = (xr == 0ULL) ? 0u : 1u;
              u32 fa = (k[K5O_VALS + (a << 1)] == 1u) ? (a << 1) : ((a << 1) | 1u);
              u32 fc = (k[K5O_VALS + (c << 1)] == 1u) ? (c << 1) : ((c << 1) | 1u);
              if (full_k512_flip(h, fa) || full_k512_flip(h, fc)) {
                if (rbit < 64u) {
                  full_m4_sweep_refine_sig(h, nv, rbit);
                  smask = smask | (1ULL << rbit); rbit = rbit + 1u;
                }
              } else {
                u64 rem1 = tick_lim - (u64)k[K5H_TICKS];
                k[K5H_NASSUMP] = 2u;
                k[K5O_ASSUMP] = a << 1; k[K5O_ASSUMP + 1u] = (c << 1) | (1u ^ pol);
                u64 d1 = full_k512_solve(h, rem1);
                if (d1 == 10ULL && rbit < 64u) {
                  full_m4_sweep_refine_sig(h, nv, rbit);
                  smask = smask | (1ULL << rbit); rbit = rbit + 1u;
                } else if (d1 == 20ULL && (u64)k[K5H_TICKS] < tick_lim) {
                  u64 rem2 = tick_lim - (u64)k[K5H_TICKS];
                  k[K5H_NASSUMP] = 2u;
                  k[K5O_ASSUMP] = (a << 1) | 1u; k[K5O_ASSUMP + 1u] = (c << 1) | pol;
                  u64 d2 = full_k512_solve(h, rem2);
                  if (d2 == 10ULL && rbit < 64u) {
                    full_m4_sweep_refine_sig(h, nv, rbit);
                    smask = smask | (1ULL << rbit); rbit = rbit + 1u;
                  } else if (d2 == 20ULL) {
                    u32 la = gv_a << 1; u32 lc = (gv_c << 1) | pol;
                    if (full_add_bin(h, la ^ 1u, lc) == 20ULL ||
                        full_add_bin(h, la, lc ^ 1u) == 20ULL) { return 20ULL; }
                    scr[PHT_MERGED + c] = 1u;
                    fl[gv_c] = fl[gv_c] & (~FL_SWEEP);
                    full_k512_add_live(h, (a << 1) ^ 1u, (c << 1) | pol);
                    full_k512_add_live(h, a << 1, ((c << 1) | pol) ^ 1u);
                    full_m4_sweep_rearm(h, gv_a);
                    full_m4_sweep_rearm(h, gv_c);
                    h->sweep_cnt = h->sweep_cnt + 1ULL;
                  }
                }
              }
            }
          }
          c = scr[PHT_NEXT + c];
        }
      }
      a = scr[PHT_NEXT + a];
    }
    b = b + 1u;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_m4_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim) {
  u64 pk = full_m4_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 1ULL;
  }
  u32 rbit = full_m4_sweep_sim(h, nv, tick_lim);
  if (rbit == 0xFFFFFFFFu) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (rbit == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 1ULL;
  }
  u64 ur = full_m4_sweep_units(h, nv, rbit, tick_lim);
  if (ur == 0xFFFFFFFFFFFFFFFFULL) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 20ULL;
  }
  u64 cr = full_m4_sweep_classes(h, nv, (u32)ur, tick_lim);
  u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
  return (cr == 20ULL || h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_m4_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim) {
  if (h->scratch_cap < K512_MIN_SCR || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + K512_BASE;
  u64 cv = h->cur_vars; u64 i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  u64 rem_ticks = (tick_lim > 16384ULL) ? 16384ULL : tick_lim;
  u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && budget > 0ULL && rem_ticks > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); budget = budget - 1ULL;
      u64 vlim = (rem_ticks > 8192ULL) ? 8192ULL : rem_ticks;
      if (full_m4_sweep_var(h, (u32)v, vlim) == 20ULL) { res = 20ULL; break; }
      u64 spent = (u64)k[K5H_TICKS] + 64ULL;
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
    v = v + 1ULL;
  }
  return (res == 20ULL || h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_m4_sweep_sat(FullHdr *h, u64 budget, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->scratch_cap < K512_MIN_SCR || budget == 0ULL) { return 1ULL; }
  if (!full_enter_dense(h)) { return (h->inconsistent != 0ULL) ? 20ULL : 1ULL; }
  u64 res = full_m4_sweep_dense(h, budget, tick_lim);
  u64 rr = full_rebuild_watches(h);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  return 1ULL;
}
"

def fullM4SweepExterns : List Extern :=
  [ ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩ ]

def fullM4SweepModule : LeanQbe.T.Module :=
  { fns := fullM4Sweep_fns, externs := fullM4SweepExterns, exits := [] }

theorem full_k512_init_wf : Func.Wf full_k512_init_body := by t_wf_reify
theorem full_k512_watch_wf : Func.Wf full_k512_watch_body := by t_wf_reify
theorem full_k512_assign_wf : Func.Wf full_k512_assign_body := by t_wf_reify
theorem full_k512_add_clause_wf : Func.Wf full_k512_add_clause_body := by t_wf_reify
theorem full_k512_mtf_wf : Func.Wf full_k512_mtf_body := by t_wf_reify
theorem full_k512_backtrack_wf : Func.Wf full_k512_backtrack_body := by t_wf_reify
theorem full_k512_propagate_wf : Func.Wf full_k512_propagate_body := by t_wf_reify
theorem full_k512_ana_clause_wf : Func.Wf full_k512_ana_clause_body := by t_wf_reify
theorem full_k512_analyze_wf : Func.Wf full_k512_analyze_body := by t_wf_reify
theorem full_k512_solve_wf : Func.Wf full_k512_solve_body := by t_wf_reify
theorem full_k512_flip_wf : Func.Wf full_k512_flip_body := by t_wf_reify
theorem full_k512_add_live_wf : Func.Wf full_k512_add_live_body := by t_wf_reify
theorem full_m4_sweep_cone_wf : Func.Wf full_m4_sweep_cone_body := by t_wf_reify
theorem full_m4_sweep_refine_sig_wf : Func.Wf full_m4_sweep_refine_sig_body := by t_wf_reify
theorem full_m4_sweep_rand_phases_wf : Func.Wf full_m4_sweep_rand_phases_body := by t_wf_reify
theorem full_m4_sweep_flip_round_wf : Func.Wf full_m4_sweep_flip_round_body := by t_wf_reify
theorem full_m4_sweep_sim_wf : Func.Wf full_m4_sweep_sim_body := by t_wf_reify
theorem full_m4_sweep_rearm_wf : Func.Wf full_m4_sweep_rearm_body := by t_wf_reify
theorem full_m4_sweep_build_pht_wf : Func.Wf full_m4_sweep_build_pht_body := by t_wf_reify
theorem full_m4_sweep_units_wf : Func.Wf full_m4_sweep_units_body := by t_wf_reify
theorem full_m4_sweep_classes_wf : Func.Wf full_m4_sweep_classes_body := by t_wf_reify
theorem full_m4_sweep_var_wf : Func.Wf full_m4_sweep_var_body := by t_wf_reify
theorem full_m4_sweep_dense_wf : Func.Wf full_m4_sweep_dense_body := by t_wf_reify
theorem full_m4_sweep_sat_wf : Func.Wf full_m4_sweep_sat_body := by t_wf_reify

theorem fullM4Sweep_fns_wf : ∀ f ∈ fullM4Sweep_fns, f.Wf := by
  simp only [fullM4Sweep_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_k512_init_wf, full_k512_watch_wf, full_k512_assign_wf, full_k512_add_clause_wf,
    full_k512_mtf_wf, full_k512_backtrack_wf, full_k512_propagate_wf, full_k512_ana_clause_wf,
    full_k512_analyze_wf, full_k512_solve_wf, full_k512_flip_wf, full_k512_add_live_wf,
    full_m4_sweep_cone_wf, full_m4_sweep_refine_sig_wf, full_m4_sweep_rand_phases_wf,
    full_m4_sweep_flip_round_wf, full_m4_sweep_sim_wf, full_m4_sweep_rearm_wf,
    full_m4_sweep_build_pht_wf, full_m4_sweep_units_wf, full_m4_sweep_classes_wf,
    full_m4_sweep_var_wf, full_m4_sweep_dense_wf, full_m4_sweep_sat_wf⟩

theorem fullM4Sweep_acyclic : fullM4SweepModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4Sweep
