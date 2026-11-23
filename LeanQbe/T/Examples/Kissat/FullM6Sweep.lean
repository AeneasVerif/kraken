module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M6 Wave-2 (`PR-W2F-sweep` / `RC-24`): BFS Cone, Scaled Kitten, & Dense ELS

Standalone drop-in override on the frozen `144`-word `FullHdr` arena layout (`Full1.lean`):
1. **Scaled `K6` sub-solver (`14` fns, `512 <= MAX_V <= 8192`, `0` `FullHdr` edits):**
   - `full_m6_max_v(cap)` scales `MAX_V`, `MAX_ORIG = 3 * MAX_V`, `MAX_CL = 4 * MAX_V`, and
     `PHT_NEXT`/`PHT_MERGED`/`K6_BASE` dynamically inside existing `scratch_buf`, preserving exact
     `24576`-word backwards compatibility at `cap = 24576`.
   - Inline binary `katch` (`K6_BIN_FLAG = 0x80000000u` on `wblit`), separate `K6H_OPEN` for
     `1UIP` analysis, strict `K6H_STATUS ∈ {0, 10, 20}`, saturating `u32` `K6H_TICKS` +
     `K6H_TICK_LIM`, VMTF `QLAST = QSEARCH = nv - 1`, and `full_k512_add_live_m6` with
     `STATUS == 10` handling + immediate level-`0` BCP.
2. **Inter-var dense propagation, clean BFS cone, per-solve phases, dynamic partition split,
   & direct dense ELS (`24` fns):**
   - `full_m6_dense_prop_lit`, `full_m6_dense_prop` (read-only occurrence BCP + `PH_GARB`).
   - `full_m6_sweep_cone` (drops `sz > 8`, binary-first BFS, `cnt <= 1`, `sweep_depth = 3`,
     buffered rollback on cone overflow, VMTF tail repair).
   - `full_m6_sweep_solve` (per-solve `randomize_phases`), `full_m6_refine_partition`
     (unlimited dynamic partition-class splitting), `full_m6_dense_els` (union-find +
     connected watch/arena substitution + `extend_push2`), `full_m6_sweep_vars`,
     `full_m6_sweep_dense`, `full_m6_sweep_sat`, and canonical `full_sweep_sat_m6`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6Sweep "
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
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE 1u
#define FL_SUBST  4u
#define FL_SWEEP  1024u

#define PHT_HEAD  256u
#define PHT_SZ    1024u
#define PHT_MASK  1023u
#define PHT_NEXT  1280u

#define K6_MIN_SCR  24576ULL
#define K6_MAX_V    8192ULL
#define K6_BIN_FLAG 0x80000000u
#define K6_LIT_MASK 0x7FFFFFFFu

#define K6H_NV       0u
#define K6H_NC       1u
#define K6H_LVL      2u
#define K6H_PROP     3u
#define K6H_TRL_END  4u
#define K6H_UNASS    5u
#define K6H_INCONS   6u
#define K6H_QFIRST   7u
#define K6H_QLAST    8u
#define K6H_QSEARCH  9u
#define K6H_QSTAMP   10u
#define K6H_TICKS    11u
#define K6H_TICK_LIM 12u
#define K6H_ALEN     13u
#define K6H_ACAP     14u
#define K6H_NASSUMP  15u
#define K6H_NKL      16u
#define K6H_NANA     17u
#define K6H_STATUS   18u
#define K6H_PHASE    19u
#define K6H_OPEN     20u
#define K6H_MAX_V    21u
#define K6H_MAX_ORIG 22u
#define K6H_MAX_CL   23u
#define K6H_NEQ      24u

extern u64 full_rng_next(FullHdr *h);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_substitute(FullHdr *h);

u64 full_m6_max_v(u64 cap) {
  if (cap < K6_MIN_SCR) { return 0ULL; }
  if (cap >= 524288ULL) { return K6_MAX_V; }
  u64 raw = ((cap - 1312ULL) / 45ULL) & 0xFFFFFFFFFFFFFFC0ULL;
  if (raw < 512ULL) { return 512ULL; }
  if (raw > K6_MAX_V) { return K6_MAX_V; }
  return raw;
}

void full_k6_add_ticks(u32 *k, u64 delta) {
  u64 cur = (u64)k[K6H_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur;
  k[K6H_TICKS] = (delta >= rem) ? 0xFFFFFFFFu : (u32)(cur + delta);
}

void full_k6_init(FullHdr *h, u32 nv) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 base = 1280u + (mv << 1);
  u32 *k = ((u32 *)h->scratch_buf) + base;
  u32 i = 0u;
  while (i < 32u) { k[i] = 0u; i = i + 1u; }
  k[K6H_NV] = nv; k[K6H_UNASS] = nv;
  k[K6H_TICK_LIM] = 16384u;
  k[K6H_MAX_V] = mv; k[K6H_MAX_ORIG] = mv * 3u; k[K6H_MAX_CL] = mv * 4u;
  k[K6H_ACAP] = (u32)(h->scratch_cap - (u64)(base + 32u + 38u * mv));
  if (nv == 0u) {
    k[K6H_QFIRST] = 0xFFFFFFFFu; k[K6H_QLAST] = 0xFFFFFFFFu; k[K6H_QSEARCH] = 0xFFFFFFFFu;
  } else {
    k[K6H_QFIRST] = 0u; k[K6H_QLAST] = nv - 1u; k[K6H_QSEARCH] = nv - 1u; k[K6H_QSTAMP] = nv;
  }
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv);
  u32 *qprev = k + (32u + 2u * mv); u32 *qnext = k + (32u + 3u * mv);
  u32 *qst = k + (32u + 4u * mv); u32 *flags = k + (32u + 6u * mv);
  i = 0u;
  while (i < nv) {
    lvl[i] = 0u; rsn[i] = 0xFFFFFFFFu; flags[i] = 0u; qst[i] = i + 1u;
    qprev[i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    qnext[i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  u32 *vals = k + (32u + 10u * mv); u32 *whead = k + (32u + 12u * mv);
  u32 nl = nv << 1; i = 0u;
  while (i < nl) { vals[i] = 0u; whead[i] = 0xFFFFFFFFu; i = i + 1u; }
}

void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1) {
  u32 mv = k[K6H_MAX_V];
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 bf = (cl_sz[cid] == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  wblit[w0] = l1 | bf; wnext[w0] = whead[l0]; whead[l0] = w0;
  wblit[w1] = l0 | bf; wnext[w1] = whead[l1]; whead[l1] = w1;
}

void full_k6_assign(u32 *k, u32 lit, u32 rsn_cid) {
  u32 mv = k[K6H_MAX_V]; u32 v = lit >> 1; u32 te = k[K6H_TRL_END];
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv); u32 *trl = k + (32u + 5u * mv);
  u32 *flags = k + (32u + 6u * mv); u32 *vals = k + (32u + 10u * mv);
  vals[lit] = 1u; vals[lit ^ 1u] = 2u;
  lvl[v] = k[K6H_LVL]; rsn[v] = rsn_cid;
  trl[te] = lit; k[K6H_TRL_END] = te + 1u;
  if (k[K6H_UNASS] > 0u) { k[K6H_UNASS] = k[K6H_UNASS] - 1u; }
  u32 fl = flags[v];
  flags[v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (sz == 0u) { k[K6H_INCONS] = 1u; return true; }
  if (sz == 1u) {
    u32 *vals = k + (32u + 10u * mv);
    u32 ul = lits[0]; u32 uv = vals[ul];
    if (uv == 2u) { k[K6H_INCONS] = 1u; }
    else if (uv == 0u) { full_k6_assign(k, ul, 0xFFFFFFFFu); }
    return true;
  }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN];
  if (nc >= k[K6H_MAX_CL] || off + sz > k[K6H_ACAP]) { return false; }
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  u32 i = 0u;
  while (i < sz) { arena[off + i] = lits[i]; i = i + 1u; }
  k[K6H_ALEN] = off + sz;
  cl_off[nc] = off; cl_sz[nc] = sz;
  k[K6H_NC] = nc + 1u;
  full_k6_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_k6_mtf(u32 *k, u32 v) {
  u32 nv = k[K6H_NV];
  if (v >= nv || v == k[K6H_QLAST]) { return; }
  u32 mv = k[K6H_MAX_V];
  u32 *qprev = k + (32u + 2u * mv); u32 *qnext = k + (32u + 3u * mv);
  u32 *qst = k + (32u + 4u * mv); u32 *vals = k + (32u + 10u * mv);
  u32 pv = qprev[v]; u32 nxt = qnext[v];
  if (vals[v << 1] != 0u && v == k[K6H_QSEARCH]) {
    if (pv < nv) { k[K6H_QSEARCH] = pv; } else if (nxt < nv) { k[K6H_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[K6H_QFIRST] = nxt; } else { qnext[pv] = nxt; }
  if (nxt >= nv) { k[K6H_QLAST] = pv; } else { qprev[nxt] = pv; }
  u32 ol = k[K6H_QLAST];
  qprev[v] = ol; qnext[v] = 0xFFFFFFFFu; k[K6H_QLAST] = v;
  if (ol >= nv) { k[K6H_QFIRST] = v; } else { qnext[ol] = v; }
  if (k[K6H_QSTAMP] < 0xFFFFFFF0u) {
    k[K6H_QSTAMP] = k[K6H_QSTAMP] + 1u; qst[v] = k[K6H_QSTAMP];
  }
  if (vals[v << 1] == 0u) { k[K6H_QSEARCH] = v; }
}

void full_k6_backtrack(u32 *k, u32 target_lvl) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv);
  u32 *qst = k + (32u + 4u * mv); u32 *trl = k + (32u + 5u * mv);
  u32 *vals = k + (32u + 10u * mv);
  u32 te = k[K6H_TRL_END]; u32 best_st = 0u;
  if (k[K6H_QSEARCH] < k[K6H_NV]) { best_st = qst[k[K6H_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = trl[te - 1u]; u32 v = lit >> 1;
    if (lvl[v] <= target_lvl) { break; }
    te = te - 1u;
    vals[lit] = 0u; vals[lit ^ 1u] = 0u;
    lvl[v] = 0u; rsn[v] = 0xFFFFFFFFu;
    k[K6H_UNASS] = k[K6H_UNASS] + 1u;
    if (qst[v] > best_st) { best_st = qst[v]; k[K6H_QSEARCH] = v; }
  }
  k[K6H_TRL_END] = te;
  if (k[K6H_PROP] > te) { k[K6H_PROP] = te; }
  k[K6H_LVL] = target_lvl;
}

u32 full_k6_propagate(u32 *k) {
  u32 mv = k[K6H_MAX_V];
  u32 *trl = k + (32u + 5u * mv); u32 *vals = k + (32u + 10u * mv);
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  u64 ticks = 0ULL;
  while (k[K6H_PROP] < k[K6H_TRL_END]) {
    u32 lit = trl[k[K6H_PROP]]; k[K6H_PROP] = k[K6H_PROP] + 1u;
    u32 nl = lit ^ 1u; u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu; u32 w = whead[nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = wnext[w]; visits = visits + 1ULL;
      u32 wb = wblit[w]; u32 bv = wb & K6_LIT_MASK;
      u32 bvv = vals[bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          full_k6_add_ticks(k, ticks + (visits >> 7) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign(k, bv, cid); }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
      u32 other = arena[off + (slot ^ 1u)];
      if (vals[other] == 1u) { wblit[w] = other; prev = w; w = nxt; continue; }
      ticks = ticks + 1ULL;
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = arena[off + r];
        if (vals[cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        arena[off + slot] = repl; arena[off + ri] = nl;
        if (prev == 0xFFFFFFFFu) { whead[nl] = nxt; } else { wnext[prev] = nxt; }
        wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
        w = nxt; continue;
      }
      wblit[w] = other; prev = w; w = nxt;
      u32 ov = vals[other];
      if (ov == 2u) {
        full_k6_add_ticks(k, ticks + (visits >> 7) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign(k, other, cid); }
    }
    ticks = ticks + (visits >> 7) + 1ULL;
  }
  full_k6_add_ticks(k, ticks);
  return 0xFFFFFFFFu;
}

void full_k6_ana_clause(u32 *k, u32 cid, u32 skip_v) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *flags = k + (32u + 6u * mv);
  u32 *ana = k + (32u + 7u * mv); u32 *kl = k + (32u + 8u * mv);
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  u32 clvl = k[K6H_LVL]; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
  u32 i = 0u;
  while (i < sz) {
    u32 l = arena[off + i]; u32 v = l >> 1;
    if (v != skip_v) {
      u32 vlvl = lvl[v];
      if (vlvl > 0u && (flags[v] & 2u) == 0u) {
        flags[v] = flags[v] | 2u;
        if (k[K6H_NANA] < mv) { ana[k[K6H_NANA]] = v; k[K6H_NANA] = k[K6H_NANA] + 1u; }
        if (vlvl == clvl) { k[K6H_OPEN] = k[K6H_OPEN] + 1u; }
        else if (k[K6H_NKL] < mv) { kl[k[K6H_NKL]] = l; k[K6H_NKL] = k[K6H_NKL] + 1u; }
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze(u32 *k, u32 confl_cid) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *rsn_arr = k + (32u + mv); u32 *trl = k + (32u + 5u * mv);
  u32 *flags = k + (32u + 6u * mv); u32 *ana = k + (32u + 7u * mv);
  u32 *kl = k + (32u + 8u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  k[K6H_NKL] = 1u; k[K6H_NANA] = 0u; k[K6H_OPEN] = 0u;
  full_k6_ana_clause(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[K6H_LVL]; u32 idx = k[K6H_TRL_END]; u32 uip = 0xFFFFFFFFu;
  while (k[K6H_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((flags[pv] & 2u) != 0u && lvl[pv] == clvl) {
      k[K6H_OPEN] = k[K6H_OPEN] - 1u;
      if (k[K6H_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = rsn_arr[pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_clause(k, rsn, pv);
    }
  }
  u32 ai = 0u;
  while (ai < k[K6H_NANA]) {
    u32 av = ana[ai]; flags[av] = flags[av] & (~2u); ai = ai + 1u;
  }
  if (uip == 0xFFFFFFFFu) { return false; }
  kl[0] = uip;
  u32 nkl = k[K6H_NKL]; u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 il = lvl[kl[i] >> 1];
    if (il > jlvl) { jlvl = il; wi = i; }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) { u32 t = kl[1]; kl[1] = kl[wi]; kl[wi] = t; }
  full_k6_backtrack(k, jlvl);
  ai = 0u; while (ai < k[K6H_NANA]) { full_k6_mtf(k, ana[ai]); ai = ai + 1u; }
  if (nkl == 1u) { full_k6_assign(k, uip, 0xFFFFFFFFu); return true; }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN]; u32 cap = k[K6H_ACAP];
  if (nc >= k[K6H_MAX_CL] || off + nkl > cap) { return false; }
  i = 0u; while (i < nkl) { arena[off + i] = kl[i]; i = i + 1u; }
  k[K6H_ALEN] = off + nkl;
  cl_off[nc] = off; cl_sz[nc] = nkl; k[K6H_NC] = nc + 1u;
  full_k6_watch(k, nc, kl[0], kl[1]);
  full_k6_assign(k, uip, nc);
  return true;
}

u64 full_k6_solve(FullHdr *h, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0ULL; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  full_k6_backtrack(k, 0u);
  if (k[K6H_INCONS] != 0u) { k[K6H_STATUS] = 20u; return 20ULL; }
  u64 cur_t = (u64)k[K6H_TICKS];
  u64 rem_t = 0xFFFFFFFFULL - cur_t;
  k[K6H_TICK_LIM] = (tick_lim >= rem_t) ? 0xFFFFFFFFu : (u32)(cur_t + tick_lim);
  k[K6H_STATUS] = 0u;
  u32 confl = full_k6_propagate(k);
  if (confl != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return 20ULL; }
  u32 *qprev = k + (32u + 2u * mv); u32 *flags = k + (32u + 6u * mv);
  u32 *assump = k + (32u + 9u * mv); u32 *vals = k + (32u + 10u * mv);
  while (k[K6H_TICKS] < k[K6H_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[K6H_LVL] == 0u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return 20ULL; }
      if (!full_k6_analyze(k, confl)) { k[K6H_STATUS] = 0u; return 0ULL; }
      confl = full_k6_propagate(k);
      continue;
    }
    u32 ad = 0u; u32 na = k[K6H_NASSUMP]; bool did_assump = false;
    while (ad < na) {
      u32 a = assump[ad]; u32 av = vals[a];
      if (av == 2u) { k[K6H_STATUS] = 20u; return 20ULL; }
      if (av == 0u) {
        k[K6H_LVL] = k[K6H_LVL] + 1u; full_k6_assign(k, a, 0xFFFFFFFFu);
        confl = full_k6_propagate(k); did_assump = true; break;
      }
      ad = ad + 1u;
    }
    if (did_assump) { continue; }
    if (k[K6H_UNASS] == 0u) { k[K6H_STATUS] = 10u; return 10ULL; }
    u32 cur = k[K6H_QSEARCH]; u32 nv = k[K6H_NV]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (vals[cur << 1] == 0u) { pick = cur; break; }
      cur = qprev[cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[K6H_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (vals[cur << 1] == 0u) { pick = cur; break; }
        cur = qprev[cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) { if (vals[cur << 1] == 0u) { pick = cur; break; } cur = cur + 1u; }
    }
    if (pick == 0xFFFFFFFFu) { k[K6H_STATUS] = 10u; return 10ULL; }
    k[K6H_QSEARCH] = pick;
    u32 ph = (flags[pick] ^ k[K6H_PHASE]) & 1u;
    k[K6H_LVL] = k[K6H_LVL] + 1u;
    full_k6_assign(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_propagate(k);
  }
  k[K6H_STATUS] = 0u;
  return 0ULL;
}

bool full_k6_flip(FullHdr *h, u32 lit) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 v = lit >> 1;
  u32 *lvl = k + 32u; u32 *vals = k + (32u + 10u * mv);
  if (k[K6H_STATUS] != 10u || v >= k[K6H_NV] || vals[lit] != 1u || lvl[v] == 0u) {
    return false;
  }
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  u32 w = whead[lit]; u32 prev = 0xFFFFFFFFu;
  u64 visits = 0ULL; u64 ticks = 1ULL; bool ok = true;
  while (w != 0xFFFFFFFFu) {
    u32 nxt = wnext[w]; visits = visits + 1ULL;
    u32 wb = wblit[w]; u32 bv = wb & K6_LIT_MASK;
    if ((wb & K6_BIN_FLAG) != 0u) {
      if (bv == lit || vals[bv] != 1u) { ok = false; break; }
      prev = w; w = nxt; continue;
    }
    if (bv != lit && vals[bv] == 1u) { prev = w; w = nxt; continue; }
    ticks = ticks + 1ULL;
    u32 cid = w >> 1; u32 slot = w & 1u; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
    u32 other = arena[off + (slot ^ 1u)];
    if (other != lit && vals[other] == 1u) {
      wblit[w] = other; prev = w; w = nxt; continue;
    }
    u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
    while (r < sz) {
      u32 cand = arena[off + r];
      if (cand != lit && vals[cand] == 1u) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) { ok = false; break; }
    arena[off + slot] = repl; arena[off + ri] = lit;
    if (prev == 0xFFFFFFFFu) { whead[lit] = nxt; } else { wnext[prev] = nxt; }
    wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
    w = nxt;
  }
  full_k6_add_ticks(k, ticks + (visits >> 7));
  if (!ok) { return false; }
  vals[lit] = 2u; vals[lit ^ 1u] = 1u;
  return true;
}

void full_k512_add_live_m6(FullHdr *h, u32 a, u32 b) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (k[K6H_STATUS] == 10u || k[K6H_LVL] != 0u) {
    full_k6_backtrack(k, 0u);
    k[K6H_STATUS] = 0u;
  }
  if (k[K6H_INCONS] != 0u) { k[K6H_STATUS] = 20u; return; }
  u32 *vals = k + (32u + 10u * mv);
  if (b == 0xFFFFFFFFu) {
    u32 va = vals[a];
    if (va == 2u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return; }
    if (va == 0u) { full_k6_assign(k, a, 0xFFFFFFFFu); }
    if (full_k6_propagate(k) != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; }
    return;
  }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN];
  if (nc >= k[K6H_MAX_CL] || off + 2u > k[K6H_ACAP]) { return; }
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  arena[off] = a; arena[off + 1u] = b;
  k[K6H_ALEN] = off + 2u; cl_off[nc] = off; cl_sz[nc] = 2u;
  k[K6H_NC] = nc + 1u;
  full_k6_watch(k, nc, a, b);
  u32 va = vals[a]; u32 vb = vals[b];
  if (va == 2u) {
    if (vb == 2u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return; }
    if (vb == 0u) { full_k6_assign(k, b, nc); }
  } else if (vb == 2u && va == 0u) {
    full_k6_assign(k, a, nc);
  }
  if (full_k6_propagate(k) != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; }
}

bool full_m6_dense_prop_lit(FullHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u; u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)not_lit << 1];
  u64 end = off + (u64)wvec[((u64)not_lit << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot >= nlits || vals[ot] > (i8)0) { continue; }
      if (vals[ot] < (i8)0) {
        h->inconsistent = 1ULL; h->confl_type = 1ULL;
        h->confl_lit0 = (u64)not_lit; h->confl_lit1 = (u64)ot; return false;
      }
      full_assign_lvl(h, ot, 0xFFFFFFFFu, 0u);
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((u64)cr + 3ULL > h->arena_len) { continue; }
    u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u || (u64)cr + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    bool sat = false; u32 non_false = 0u; u32 unit = 0xFFFFFFFFu; u32 i = 0u;
    while (i < csz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)i];
      if ((u64)cl < nlits) {
        i8 v = vals[cl];
        if (v > (i8)0) { sat = true; break; }
        if (v == (i8)0) {
          non_false = non_false + 1u; unit = cl;
          if (non_false > 1u) { break; }
        }
      }
      i = i + 1u;
    }
    if (sat) {
      ar[cr] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      continue;
    }
    if (non_false == 0u) {
      h->inconsistent = 1ULL; h->confl_type = 2ULL; h->confl_ref = (u64)cr; return false;
    }
    if (non_false == 1u && vals[unit] == (i8)0) {
      full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u);
    }
  }
  return true;
}

bool full_m6_dense_prop(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end && h->inconsistent == 0ULL) {
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    if (!full_m6_dense_prop_lit(h, lit)) { return false; }
  }
  return h->inconsistent == 0ULL;
}

u64 full_m6_sweep_cone(FullHdr *h, u32 root_v) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0ULL; }
  u32 max_orig = mv * 3u;
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  full_k6_init(h, mv);
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u;
  u32 qi = 0u; u32 depth = 0u; bool limit_reached = false;
  while (qi < nv && depth < 3u && !limit_reached && nc < max_orig) {
    u32 layer_end = nv; depth = depth + 1u;
    while (qi < layer_end && !limit_reached && nc < max_orig) {
      u32 cv = cone_v[qi]; u32 cur_tmk = tmk[cv]; u32 map_c = cur_tmk - 1u;
      qi = qi + 1u;
      u32 pol = 0u;
      while (pol < 2u && !limit_reached && nc < max_orig) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < max_orig) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 1ULL; continue; }
          u32 ot = w0 & PW_LIT_MASK; u32 ov = ot >> 1;
          i8 ovv = vals[ot];
          if (ovv > (i8)0) { continue; }
          if (ov == cv) {
            if (ot == lit && pol == 0u) {
              tmp[0] = map_c << 1;
              if (full_k6_add_clause(h, tmp, 1u)) {
                nc = nc + 1u;
                if (k[K6H_INCONS] != 0u) { limit_reached = true; }
              } else { limit_reached = true; }
            }
            continue;
          }
          if (ovv < (i8)0) {
            tmp[0] = (map_c << 1) | pol;
            if (full_k6_add_clause(h, tmp, 1u)) {
              nc = nc + 1u;
              if (k[K6H_INCONS] != 0u) { limit_reached = true; }
            } else { limit_reached = true; }
            continue;
          }
          if (tmk[ov] != 0u && tmk[ov] < cur_tmk) { continue; }
          u32 saved_nv = nv;
          if (tmk[ov] == 0u) {
            if (nv >= mv) { limit_reached = true; break; }
            cone_v[nv] = ov; nv = nv + 1u; tmk[ov] = nv;
          }
          tmp[0] = (map_c << 1) | pol;
          tmp[1] = ((tmk[ov] - 1u) << 1) | (ot & 1u);
          if (full_k6_add_clause(h, tmp, 2u)) {
            nc = nc + 1u;
          } else {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            limit_reached = true;
          }
        }
        pol = pol + 1u;
      }
      pol = 0u;
      while (pol < 2u && !limit_reached && nc < max_orig) {
        u32 lit = (cv << 1) | pol;
        u64 off = (u64)wvec[(u64)lit << 1];
        u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
        u64 p = off;
        while (p < end && !limit_reached && nc < max_orig) {
          u32 w0 = wstk[p]; p = p + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
          if (p >= end) { break; }
          u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
          if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz < 3u) { continue; }
          u32 saved_nv = nv; bool drop = false; u32 cnt = 0u; u32 idx = 0u;
          while (idx < sz) {
            u32 l = ar[(u64)cr + 3ULL + (u64)idx];
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { drop = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1; u32 ltm = tmk[lv];
              if ((ltm != 0u && ltm < cur_tmk) || (lv == cv && (l & 1u) < pol)) {
                drop = true; break;
              }
              if (ltm == 0u) {
                if (nv >= mv) { limit_reached = true; drop = true; break; }
                cone_v[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              tmp[cnt] = ((tmk[lv] - 1u) << 1) | (l & 1u); cnt = cnt + 1u;
            }
            idx = idx + 1u;
          }
          if (drop) {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            continue;
          }
          if (full_k6_add_clause(h, tmp, cnt)) {
            nc = nc + 1u;
            if (k[K6H_INCONS] != 0u) { limit_reached = true; }
          } else {
            while (nv > saved_nv) { nv = nv - 1u; tmk[cone_v[nv]] = 0u; }
            limit_reached = true;
          }
        }
        pol = pol + 1u;
      }
    }
  }
  u32 te = k[K6H_TRL_END];
  k[K6H_NV] = nv;
  k[K6H_UNASS] = (te <= nv) ? (nv - te) : 0u;
  if (nv > 0u) {
    u32 *qnext = k + (32u + 3u * mv);
    k[K6H_QLAST] = nv - 1u; k[K6H_QSEARCH] = nv - 1u;
    k[K6H_QSTAMP] = nv; qnext[nv - 1u] = 0xFFFFFFFFu;
  }
  return (u64)nv | ((u64)nc << 16);
}

void full_m6_sweep_refine_sig(FullHdr *h, u32 nv, u32 bit_idx) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *vals = k + (32u + 10u * mv);
  u64 mask = 1ULL << (u64)(bit_idx & 63u); u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (vals[i << 1] == 1u) { sig[gv] = sig[gv] | mask; }
    else { sig[gv] = sig[gv] & (~mask); }
    i = i + 1u;
  }
}

void full_m6_sweep_rand_phases(FullHdr *h, u32 nv) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *flags = k + (32u + 6u * mv);
  u64 rbits = full_rng_next(h);
  u32 i = 0u;
  while (i < nv) {
    if ((i & 63u) == 0u && i > 0u) { rbits = full_rng_next(h); }
    u32 fl = flags[i];
    flags[i] = (fl & (~1u)) | ((u32)rbits & 1u);
    rbits = rbits >> 1; i = i + 1u;
  }
  k[K6H_PHASE] = k[K6H_PHASE] ^ 1u;
}

u64 full_m6_sweep_solve(FullHdr *h, u32 nv, u64 tick_lim) {
  full_m6_sweep_rand_phases(h, nv);
  return full_k6_solve(h, tick_lim);
}

u32 full_m6_sweep_flip_round(FullHdr *h, u32 nv) {
  if (nv == 0u) { return 0u; }
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 *vals = k + (32u + 10u * mv);
  u32 start = (u32)(full_rng_next(h) % (u64)nv);
  u64 rbits = full_rng_next(h);
  u32 flipped = 0u; u32 step = 0u;
  while (step < nv) {
    if ((step & 63u) == 0u && step > 0u) { rbits = full_rng_next(h); }
    if ((rbits & 1ULL) != 0ULL) {
      u32 v = start + step;
      if (v >= nv) { v = v - nv; }
      u32 lit = (vals[v << 1] == 1u) ? (v << 1) : ((v << 1) | 1u);
      if (full_k6_flip(h, lit)) { flipped = flipped + 1u; }
    }
    rbits = rbits >> 1; step = step + 1u;
  }
  return flipped;
}

u32 full_m6_sweep_sim(FullHdr *h, u32 nv, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 i = 0u; while (i < nv) { sig[cone_v[i]] = 0ULL; i = i + 1u; }
  k[K6H_NASSUMP] = 0u;
  u64 st0 = full_m6_sweep_solve(h, nv, tick_lim);
  if (st0 == 20ULL) { return 0xFFFFFFFFu; }
  if (st0 != 10ULL) { return 0u; }
  u32 rbit = 0u; full_m6_sweep_refine_sig(h, nv, rbit); rbit = 1u;
  u64 sim_lim = (tick_lim < 2048ULL) ? tick_lim : 2048ULL;
  u32 round = 0u;
  while (round < 4u && rbit < 64u && h->fuel > 0ULL) {
    u32 fr = 0u;
    while (fr < 3u && rbit < 64u) {
      if (full_m6_sweep_flip_round(h, nv) > 0u) {
        full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
      } else { break; }
      fr = fr + 1u;
    }
    round = round + 1u;
    u64 cur_t = (u64)k[K6H_TICKS];
    if (round < 4u && rbit < 64u && cur_t < sim_lim && h->fuel > 0ULL) {
      k[K6H_NASSUMP] = 0u;
      u64 st = full_m6_sweep_solve(h, nv, sim_lim - cur_t);
      if (st == 20ULL) { return 0xFFFFFFFFu; }
      if (st != 10ULL) { break; }
      full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u;
    }
  }
  return rbit;
}

void full_m6_sweep_rearm(FullHdr *h, u32 v) {
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

void full_m6_sweep_build_pht(FullHdr *h, u32 nv, u64 smask) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *pht_next = scr + PHT_NEXT; u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  i8 *vals_m = (i8 *)h->values;
  u32 b = 0u;
  while (b < PHT_SZ) { scr[PHT_HEAD + b] = 0xFFFFFFFFu; b = b + 1u; }
  u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (pht_merged[i] == 0u && vals_m[gv << 1] == (i8)0) {
      u64 raw = sig[gv] & smask;
      u64 key = ((raw & 1ULL) != 0ULL) ? (raw ^ smask) : raw;
      u32 hidx = (u32)((key ^ (key >> 17) ^ (key >> 34) ^ (key >> 51)) & (u64)PHT_MASK);
      pht_next[i] = scr[PHT_HEAD + hidx];
      scr[PHT_HEAD + hidx] = i;
    } else {
      pht_next[i] = 0xFFFFFFFFu;
    }
    i = i + 1u;
  }
}

u32 full_m6_extract_pht(FullHdr *h, u32 nv, u64 smask) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  u32 ncls = 0u; u32 b = 0u;
  while (b < PHT_SZ) {
    u32 guard = nv;
    while (scr[PHT_HEAD + b] < nv && guard > 0u) {
      guard = guard - 1u;
      u32 h0 = scr[PHT_HEAD + b]; scr[PHT_HEAD + b] = 0xFFFFFFFFu;
      u32 keep_tail = 0xFFFFFFFFu; u32 cls_tail = h0; u32 csz = 1u;
      pols[h0] = 0u; u64 s0 = sig[cone_v[h0]] & smask;
      u32 y = pht_next[h0]; u32 inner_g = nv;
      while (y < nv && inner_g > 0u) {
        inner_g = inner_g - 1u;
        u32 ny = pht_next[y];
        u64 xr = (sig[cone_v[y]] ^ s0) & smask;
        if (xr == 0ULL || xr == smask) {
          pols[y] = (xr == 0ULL) ? 0u : 1u;
          pht_next[cls_tail] = y; cls_tail = y; csz = csz + 1u;
        } else {
          if (keep_tail == 0xFFFFFFFFu) { scr[PHT_HEAD + b] = y; }
          else { pht_next[keep_tail] = y; }
          keep_tail = y;
        }
        y = ny;
      }
      pht_next[cls_tail] = 0xFFFFFFFFu;
      if (keep_tail < nv) { pht_next[keep_tail] = 0xFFFFFFFFu; }
      if (csz >= 2u && (u64)ncls < h->max_vars) { heads[ncls] = h0; ncls = ncls + 1u; }
    }
    b = b + 1u;
  }
  return ncls;
}

u32 full_m6_refine_partition(FullHdr *h, u32 nv, u32 ncls) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 0u; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1)); u32 *kvals = k + (32u + 10u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; i8 *vals_m = (i8 *)h->values;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  u32 *nheads = (u32 *)h->wsort; u32 new_n = 0u; u32 ci = 0u;
  while (ci < ncls) {
    u32 x = heads[ci];
    u32 ph = 0xFFFFFFFFu; u32 pt = 0xFFFFFFFFu; u32 pc = 0u;
    u32 nh = 0xFFFFFFFFu; u32 nt = 0xFFFFFFFFu; u32 nc = 0u;
    u32 g = nv;
    while (x < nv && g > 0u) {
      g = g - 1u;
      u32 nx = pht_next[x];
      if (pht_merged[x] == 0u && vals_m[cone_v[x] << 1] == (i8)0) {
        u32 kv = kvals[(x << 1) | (pols[x] & 1u)];
        if (kv == 1u) {
          if (pt == 0xFFFFFFFFu) { ph = x; } else { pht_next[pt] = x; }
          pt = x; pc = pc + 1u;
        } else if (kv == 2u) {
          if (nt == 0xFFFFFFFFu) { nh = x; } else { pht_next[nt] = x; }
          nt = x; nc = nc + 1u;
        }
      }
      x = nx;
    }
    if (pt < nv) { pht_next[pt] = 0xFFFFFFFFu; }
    if (nt < nv) { pht_next[nt] = 0xFFFFFFFFu; }
    if (pc >= 2u && (u64)new_n < h->max_vars) { nheads[new_n] = ph; new_n = new_n + 1u; }
    if (nc >= 2u && (u64)new_n < h->max_vars) { nheads[new_n] = nh; new_n = new_n + 1u; }
    ci = ci + 1u;
  }
  ci = 0u; while (ci < new_n) { heads[ci] = nheads[ci]; ci = ci + 1u; }
  return new_n;
}

u64 full_m6_sweep_units(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return (u64)rbit_in; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1)); u32 *assump = k + (32u + 9u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u; while (i < nv) { pht_merged[i] = 0u; i = i + 1u; }
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << rbit) - 1ULL);
  i = 0u;
  while (i < nv && h->inconsistent == 0ULL && h->fuel > 0ULL && (u64)k[K6H_TICKS] < tick_lim) {
    u32 gv = cone_v[i];
    if (vals[gv << 1] != (i8)0) { pht_merged[i] = 1u; i = i + 1u; continue; }
    u64 s0 = sig[gv] & smask;
    if (s0 == 0ULL || s0 == smask) {
      u32 wf = (s0 == 0ULL) ? 0u : 1u;
      u32 test_lit = (i << 1) | wf;
      if (full_k6_flip(h, test_lit ^ 1u)) {
        if (rbit < 64u) {
          full_m6_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      } else {
        u64 rem = tick_lim - (u64)k[K6H_TICKS];
        k[K6H_NASSUMP] = 1u; assump[0] = test_lit;
        u64 d = full_m6_sweep_solve(h, nv, rem);
        if (d == 20ULL) {
          u32 gl = (gv << 1) | (1u - wf);
          if (!full_add_unit(h, gl)) { return 0xFFFFFFFFFFFFFFFFULL; }
          pht_merged[i] = 1u;
          full_k512_add_live_m6(h, test_lit ^ 1u, 0xFFFFFFFFu);
          if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 0xFFFFFFFFFFFFFFFFULL; }
          full_m6_sweep_rearm(h, gv);
          h->sweep_cnt = h->sweep_cnt + 1ULL;
        } else if (d == 10ULL && rbit < 64u) {
          full_m6_sweep_refine_sig(h, nv, rbit);
          smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        }
      }
    }
    i = i + 1u;
  }
  return (h->inconsistent != 0ULL) ? 0xFFFFFFFFFFFFFFFFULL : (u64)rbit;
}

u64 full_m6_sweep_classes(FullHdr *h, u32 nv, u32 rbit_in, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *pht_next = scr + PHT_NEXT;
  u32 *pht_merged = scr + (PHT_NEXT + mv);
  u32 *k = scr + (1280u + (mv << 1));
  u32 *assump = k + (32u + 9u * mv); u32 *kvals = k + (32u + 10u * mv);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *eqb = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags;
  u32 *heads = (u32 *)h->shrink_stk; u32 *pols = (u32 *)h->min_clr;
  k[K6H_NEQ] = 0u;
  u32 rbit = rbit_in;
  u64 smask = (rbit >= 64u) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << rbit) - 1ULL);
  full_m6_sweep_build_pht(h, nv, smask);
  u32 ncls = full_m6_extract_pht(h, nv, smask);
  u32 neq = 0u; u32 steps = (nv << 2) + 64u;
  while (ncls > 0u && steps > 0u && h->inconsistent == 0ULL && h->oom == 0ULL &&
         h->fuel > 0ULL && (u64)k[K6H_TICKS] < tick_lim) {
    steps = steps - 1u;
    u32 a = heads[ncls - 1u]; u32 c = pht_next[a];
    if (c >= nv) { ncls = ncls - 1u; continue; }
    if (pht_merged[a] != 0u || pht_merged[c] != 0u) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    u32 gv_a = cone_v[a]; u32 gv_c = cone_v[c];
    u32 pa = pols[a] & 1u; u32 pc = pols[c] & 1u; u32 pol = pa ^ pc;
    u32 fa = (kvals[a << 1] == 1u) ? (a << 1) : ((a << 1) | 1u);
    u32 fc = (kvals[c << 1] == 1u) ? (c << 1) : ((c << 1) | 1u);
    if (full_k6_flip(h, fa) || full_k6_flip(h, fc)) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    u64 rem1 = tick_lim - (u64)k[K6H_TICKS];
    k[K6H_NASSUMP] = 2u; assump[0] = a << 1; assump[1] = (c << 1) | (1u ^ pol);
    u64 d1 = full_m6_sweep_solve(h, nv, rem1);
    if (d1 == 10ULL) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    if (d1 != 20ULL || (u64)k[K6H_TICKS] >= tick_lim) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    u64 rem2 = tick_lim - (u64)k[K6H_TICKS];
    k[K6H_NASSUMP] = 2u; assump[0] = (a << 1) | 1u; assump[1] = (c << 1) | pol;
    u64 d2 = full_m6_sweep_solve(h, nv, rem2);
    if (d2 == 10ULL) {
      if (rbit < 64u) { full_m6_sweep_refine_sig(h, nv, rbit); rbit = rbit + 1u; }
      ncls = full_m6_refine_partition(h, nv, ncls);
      continue;
    }
    if (d2 != 20ULL) {
      pht_next[a] = pht_next[c];
      if (pht_next[a] >= nv) { ncls = ncls - 1u; }
      continue;
    }
    pht_merged[c] = 1u;
    pht_next[a] = pht_next[c];
    if (pht_next[a] >= nv) { ncls = ncls - 1u; }
    fl[gv_c] = fl[gv_c] & (~FL_SWEEP);
    full_k512_add_live_m6(h, (a << 1) ^ 1u, (c << 1) | pol);
    if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 20ULL; }
    full_k512_add_live_m6(h, a << 1, ((c << 1) | pol) ^ 1u);
    if (k[K6H_INCONS] != 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if ((u64)neq < h->cur_vars) {
      eqb[neq << 1] = gv_a << 1; eqb[(neq << 1) + 1u] = (gv_c << 1) | pol;
      neq = neq + 1u; k[K6H_NEQ] = neq;
    }
    full_m6_sweep_rearm(h, gv_a);
    full_m6_sweep_rearm(h, gv_c);
    h->sweep_cnt = h->sweep_cnt + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

bool full_m6_els_ar(FullHdr *h, u32 cr, u32 rl) {
  if ((u64)cr + 3ULL > h->arena_len) { return true; }
  u32 *ar = (u32 *)h->arena; u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
  if ((hdr & PH_GARB) != 0u || sz < 3u || (u64)cr + 3ULL + (u64)sz > h->arena_len) {
    return true;
  }
  u32 *repr = (u32 *)h->repr; u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u64 nlits = h->cur_vars << 1;
  bool chg = false; u32 k = 0u;
  while (k < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)k];
    if ((u64)l < nlits && repr[l] != l) { chg = true; break; }
    k = k + 1u;
  }
  if (!chg) {
    if (!full_watch_push(h, rl, sz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
    return true;
  }
  bool taut = false; u32 nsz = 0u; k = 0u;
  while (k < sz) {
    u32 x = ar[(u64)cr + 3ULL + (u64)k];
    u32 rx = ((u64)x < nlits) ? repr[x] : x;
    if ((u64)rx < nlits) {
      if (lm[rx ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rx] == (u8)0 && (u64)nsz < h->max_vars) {
        lm[rx] = (u8)1; tmp[nsz] = rx; nsz = nsz + 1u;
      }
    }
    k = k + 1u;
  }
  k = 0u; while (k < nsz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  if (taut || nsz <= 2u) {
    ar[cr] = hdr | PH_GARB;
    h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
    if (!taut && nsz == 1u && !full_add_unit(h, tmp[0])) { return false; }
    if (!taut && nsz == 2u) {
      u64 ab = full_add_bin(h, tmp[0], tmp[1]);
      if (ab == 20ULL) { return false; }
    }
    return true;
  }
  k = 0u; while (k < nsz) { ar[(u64)cr + 3ULL + (u64)k] = tmp[k]; k = k + 1u; }
  if (nsz < sz) {
    ar[(u64)cr + 2ULL] = nsz; ar[(u64)cr + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[cr] = hdr | PH_SHRK; ar[(u64)cr + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
    }
  }
  if (!full_watch_push(h, rl, nsz & PW_LIT_MASK, cr, 2u)) { h->oom = 1ULL; }
  return true;
}

bool full_m6_els_lit(FullHdr *h, u32 l, u32 rl) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *repr = (u32 *)h->repr; u64 nlits = h->cur_vars << 1;
  u64 guard = (u64)wvec[((u64)l << 1) + 1ULL];
  while (guard > 0ULL && wvec[((u64)l << 1) + 1ULL] > 0u &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    guard = guard - 1ULL;
    u64 off = (u64)wvec[(u64)l << 1];
    u64 sz = (u64)wvec[((u64)l << 1) + 1ULL];
    u32 w0 = wstk[off];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wvec[(u64)l << 1] = (u32)(off + 1ULL);
      wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 1ULL);
      h->wusable = h->wusable + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      u32 rot = ((u64)ot < nlits) ? repr[ot] : ot;
      if ((u64)rot >= nlits || rl == (rot ^ 1u)) { continue; }
      if (rl == rot) { if (!full_add_unit(h, rl)) { return false; } continue; }
      u64 ab = full_add_bin(h, rl, rot);
      if (ab == 20ULL) { return false; }
      if (ab == 2ULL) { return true; }
      continue;
    }
    if (sz < 2ULL) { wvec[((u64)l << 1) + 1ULL] = 0u; break; }
    u32 cr = wstk[off + 1ULL];
    wvec[(u64)l << 1] = (u32)(off + 2ULL);
    wvec[((u64)l << 1) + 1ULL] = (u32)(sz - 2ULL);
    h->wusable = h->wusable + 2ULL;
    if (!full_m6_els_ar(h, cr, rl)) { return false; }
  }
  return h->inconsistent == 0ULL;
}

bool full_m6_els_fold(FullHdr *h, u32 neq) {
  u32 *repr = (u32 *)h->repr; u32 *eqb = (u32 *)h->work_stk2;
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u64 i = 0u; while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  u64 ei = 0ULL;
  while (ei < (u64)neq) {
    u32 a = eqb[ei << 1]; u32 b = eqb[(ei << 1) + 1u];
    u32 ra = a; u64 ga = cv;
    while (ga > 0ULL && repr[ra] != ra) { ra = repr[ra]; ga = ga - 1ULL; }
    u32 rb = b; u64 gb = cv;
    while (gb > 0ULL && repr[rb] != rb) { rb = repr[rb]; gb = gb - 1ULL; }
    if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return false; }
    if (ra != rb) {
      if ((rb >> 1) < (ra >> 1)) { u32 tmp = ra; ra = rb; rb = tmp; }
      repr[rb] = ra; repr[rb ^ 1u] = ra ^ 1u;
    }
    ei = ei + 1ULL;
  }
  u64 v = 0ULL;
  while (v < cv) {
    u32 pl = (u32)(v << 1); u32 r = repr[pl];
    if (r != pl) { r = repr[r]; repr[pl] = r; repr[pl | 1u] = r ^ 1u; }
    v = v + 1ULL;
  }
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  v = 0ULL;
  while (v < cv) {
    u32 lit = (u32)(v << 1); u32 rep = repr[lit];
    if (rep != lit) {
      i8 vl = vals[lit]; i8 vr = vals[rep];
      if (vl != (i8)0 && vr == (i8)0) {
        u32 u = (vl > (i8)0) ? rep : (rep ^ 1u);
        if (!full_add_unit(h, u)) { return false; }
      } else if (vr != (i8)0 && vl == (i8)0) {
        u32 u = (vr > (i8)0) ? lit : (lit ^ 1u);
        if (!full_add_unit(h, u)) { return false; }
      } else if (vl != (i8)0 && vl != vr) {
        h->inconsistent = 1ULL; return false;
      }
    }
    v = v + 1ULL;
  }
  v = 0ULL;
  while (v < cv) {
    u32 lit = (u32)(v << 1); u32 rep = repr[lit];
    if (rep != lit) {
      if ((fl[v] & FL_ACTIVE) == 0u || (fl[rep >> 1] & FL_ACTIVE) == 0u ||
          vals[lit] != (i8)0 || vals[rep] != (i8)0) {
        repr[lit] = lit; repr[lit | 1u] = lit | 1u;
      } else if (h->extend_len + 4ULL <= h->extend_cap) {
        full_extend_push2(h, lit | 1u, rep);
        full_extend_push2(h, lit, rep ^ 1u);
        full_set_inactive(h, (u32)v, FL_SUBST);
        fl[rep >> 1] = fl[rep >> 1] | FL_SWEEP;
        h->subst_cnt = h->subst_cnt + 1ULL;
      } else {
        repr[lit] = lit; repr[lit | 1u] = lit | 1u;
      }
    }
    v = v + 1ULL;
  }
  return true;
}

bool full_m6_dense_els(FullHdr *h, u32 neq) {
  if (neq == 0u || h->inconsistent != 0ULL) { return h->inconsistent == 0ULL; }
  if (!full_m6_els_fold(h, neq)) { return false; }
  u32 *repr = (u32 *)h->repr; u64 cv = h->cur_vars; u64 v = 0ULL;
  while (v < cv && h->oom == 0ULL && h->inconsistent == 0ULL) {
    u32 lit = (u32)(v << 1); u32 rl = repr[lit];
    if (rl != lit) {
      if (!full_m6_els_lit(h, lit, rl)) { return false; }
      if (!full_m6_els_lit(h, lit | 1u, rl ^ 1u)) { return false; }
    }
    v = v + 1ULL;
  }
  if (h->inconsistent != 0ULL) { return false; }
  return full_m6_dense_prop(h);
}

u64 full_m6_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 1ULL; }
  u64 pk = full_m6_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (k[K6H_INCONS] != 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u32 rbit = full_m6_sweep_sim(h, nv, tick_lim);
  if (rbit == 0xFFFFFFFFu) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (rbit == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 1ULL;
  }
  u64 ur = full_m6_sweep_units(h, nv, rbit, tick_lim);
  if (ur == 0xFFFFFFFFFFFFFFFFULL) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    return 20ULL;
  }
  u64 cr = full_m6_sweep_classes(h, nv, (u32)ur, tick_lim);
  u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
  if (cr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  u32 neq = k[K6H_NEQ];
  if (neq > 0u && !full_m6_dense_els(h, neq)) { return 20ULL; }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

void full_m6_cand_sift(u32 *cands, u32 *deg, u32 start, u32 n) {
  u32 r = start;
  while (true) {
    u32 c = (r << 1) + 1u;
    if (c >= n) { break; }
    if (c + 1u < n && deg[cands[c + 1u]] > deg[cands[c]]) { c = c + 1u; }
    if (deg[cands[r]] >= deg[cands[c]]) { break; }
    u32 tmp = cands[r]; cands[r] = cands[c]; cands[c] = tmp;
    r = c;
  }
}

u32 full_m6_collect_cands(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv == 0ULL) { return 0u; }
  u32 *cands = (u32 *)h->tarjan_reach; u32 *deg = (u32 *)h->work_stk2;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u32 *wvec = (u32 *)h->watch_vec;
  u32 nc = 0u; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      u64 d = (u64)wvec[((v << 1) << 1) + 1ULL] + (u64)wvec[(((v << 1) | 1ULL) << 1) + 1ULL];
      deg[v] = (d > 0xFFFFFFFFULL) ? 0xFFFFFFFFu : (u32)d;
      cands[nc] = (u32)v; nc = nc + 1u;
    }
    v = v + 1ULL;
  }
  if (nc < 2u) { return nc; }
  u32 s = nc >> 1;
  while (s > 0u) { s = s - 1u; full_m6_cand_sift(cands, deg, s, nc); }
  u32 end = nc;
  while (end > 1u) {
    end = end - 1u;
    u32 t = cands[0]; cands[0] = cands[end]; cands[end] = t;
    full_m6_cand_sift(cands, deg, 0u, end);
  }
  return nc;
}

u64 full_m6_sweep_vars(FullHdr *h, u64 budget, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || budget == 0ULL || tick_lim == 0ULL) { return 1ULL; }
  if (!full_m6_dense_prop(h)) { return 20ULL; }
  u32 nc = full_m6_collect_cands(h);
  if (nc == 0u) { return 1ULL; }
  u32 *cands = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u64 rem_ticks = (tick_lim > 0xFFFFFFFFULL) ? 0xFFFFFFFFULL : tick_lim;
  u64 per_v = (mv >= 2048u) ? 65536ULL : 16384ULL;
  u32 ci = 0u; u64 rem_b = budget;
  while (ci < nc && rem_b > 0ULL && rem_ticks > 0ULL &&
         h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u32 v = cands[ci]; ci = ci + 1u;
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); rem_b = rem_b - 1ULL;
      u64 vlim = (rem_ticks > per_v) ? per_v : rem_ticks;
      if (full_m6_sweep_var(h, v, vlim) == 20ULL) { return 20ULL; }
      if (h->propagated < h->trail_end && !full_m6_dense_prop(h)) { return 20ULL; }
      u64 spent = (u64)k[K6H_TICKS] + 64ULL;
      rem_ticks = (spent >= rem_ticks) ? 0ULL : (rem_ticks - spent);
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_m6_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim) {
  if (full_m6_max_v(h->scratch_cap) == 0ULL || budget == 0ULL || tick_lim == 0ULL) {
    return 1ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark; u64 cv = h->cur_vars;
  u64 i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  u64 round = 0ULL;
  while (round < 2ULL && h->oom == 0ULL && h->fuel > 0ULL && h->inconsistent == 0ULL) {
    u64 before = h->sweep_cnt;
    if (full_m6_sweep_vars(h, budget, tick_lim) == 20ULL) { return 20ULL; }
    if (h->sweep_cnt == before) { break; }
    round = round + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_m6_sweep_sat(FullHdr *h, u64 budget, u64 tick_lim) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (full_m6_max_v(h->scratch_cap) == 0ULL || budget == 0ULL) { return 1ULL; }
  u64 before_sw = h->sweep_cnt;
  if (!full_enter_dense(h)) { return (h->inconsistent != 0ULL) ? 20ULL : 1ULL; }
  u64 res = full_m6_sweep_dense(h, budget, tick_lim);
  u64 rr = full_rebuild_watches(h);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom == 0ULL && h->sweep_cnt > before_sw && full_substitute(h) == 20ULL) {
    return 20ULL;
  }
  return 1ULL;
}

u64 full_sweep_sat_m6(FullHdr *h) {
  return full_m6_sweep_sat(h, 256ULL, 65536ULL);
}
"

def m6SweepExterns : List Extern :=
  [ ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_set_inactive", [i64, i32, i32], []⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩ ]

def m6SweepModule : LeanQbe.T.Module :=
  { fns := m6Sweep_fns, externs := m6SweepExterns, exits := [] }

theorem full_m6_max_v_wf : Func.Wf full_m6_max_v_body := by t_wf_reify
theorem full_k6_add_ticks_wf : Func.Wf full_k6_add_ticks_body := by t_wf_reify
theorem full_k6_init_wf : Func.Wf full_k6_init_body := by t_wf_reify
theorem full_k6_watch_wf : Func.Wf full_k6_watch_body := by t_wf_reify
theorem full_k6_assign_wf : Func.Wf full_k6_assign_body := by t_wf_reify
theorem full_k6_add_clause_wf : Func.Wf full_k6_add_clause_body := by t_wf_reify
theorem full_k6_mtf_wf : Func.Wf full_k6_mtf_body := by t_wf_reify
theorem full_k6_backtrack_wf : Func.Wf full_k6_backtrack_body := by t_wf_reify
theorem full_k6_propagate_wf : Func.Wf full_k6_propagate_body := by t_wf_reify
theorem full_k6_ana_clause_wf : Func.Wf full_k6_ana_clause_body := by t_wf_reify
theorem full_k6_analyze_wf : Func.Wf full_k6_analyze_body := by t_wf_reify
theorem full_k6_solve_wf : Func.Wf full_k6_solve_body := by t_wf_reify
theorem full_k6_flip_wf : Func.Wf full_k6_flip_body := by t_wf_reify
theorem full_k512_add_live_m6_wf : Func.Wf full_k512_add_live_m6_body := by t_wf_reify
theorem full_m6_dense_prop_lit_wf : Func.Wf full_m6_dense_prop_lit_body := by t_wf_reify
theorem full_m6_dense_prop_wf : Func.Wf full_m6_dense_prop_body := by t_wf_reify
theorem full_m6_sweep_cone_wf : Func.Wf full_m6_sweep_cone_body := by t_wf_reify
theorem full_m6_sweep_refine_sig_wf : Func.Wf full_m6_sweep_refine_sig_body := by t_wf_reify
theorem full_m6_sweep_rand_phases_wf : Func.Wf full_m6_sweep_rand_phases_body := by t_wf_reify
theorem full_m6_sweep_solve_wf : Func.Wf full_m6_sweep_solve_body := by t_wf_reify
theorem full_m6_sweep_flip_round_wf : Func.Wf full_m6_sweep_flip_round_body := by t_wf_reify
theorem full_m6_sweep_sim_wf : Func.Wf full_m6_sweep_sim_body := by t_wf_reify
theorem full_m6_sweep_rearm_wf : Func.Wf full_m6_sweep_rearm_body := by t_wf_reify
theorem full_m6_sweep_build_pht_wf : Func.Wf full_m6_sweep_build_pht_body := by t_wf_reify
theorem full_m6_extract_pht_wf : Func.Wf full_m6_extract_pht_body := by t_wf_reify
theorem full_m6_refine_partition_wf : Func.Wf full_m6_refine_partition_body := by t_wf_reify
theorem full_m6_sweep_units_wf : Func.Wf full_m6_sweep_units_body := by t_wf_reify
theorem full_m6_sweep_classes_wf : Func.Wf full_m6_sweep_classes_body := by t_wf_reify
theorem full_m6_els_ar_wf : Func.Wf full_m6_els_ar_body := by t_wf_reify
theorem full_m6_els_lit_wf : Func.Wf full_m6_els_lit_body := by t_wf_reify
theorem full_m6_els_fold_wf : Func.Wf full_m6_els_fold_body := by t_wf_reify
theorem full_m6_dense_els_wf : Func.Wf full_m6_dense_els_body := by t_wf_reify
theorem full_m6_sweep_var_wf : Func.Wf full_m6_sweep_var_body := by t_wf_reify
theorem full_m6_cand_sift_wf : Func.Wf full_m6_cand_sift_body := by t_wf_reify
theorem full_m6_collect_cands_wf : Func.Wf full_m6_collect_cands_body := by t_wf_reify
theorem full_m6_sweep_vars_wf : Func.Wf full_m6_sweep_vars_body := by t_wf_reify
theorem full_m6_sweep_dense_wf : Func.Wf full_m6_sweep_dense_body := by t_wf_reify
theorem full_m6_sweep_sat_wf : Func.Wf full_m6_sweep_sat_body := by t_wf_reify
theorem full_sweep_sat_m6_wf : Func.Wf full_sweep_sat_m6_body := by t_wf_reify

theorem m6Sweep_fns_wf : ∀ f ∈ m6Sweep_fns, f.Wf := by
  simp only [m6Sweep_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_m6_max_v_wf, full_k6_add_ticks_wf, full_k6_init_wf, full_k6_watch_wf,
    full_k6_assign_wf, full_k6_add_clause_wf, full_k6_mtf_wf, full_k6_backtrack_wf,
    full_k6_propagate_wf, full_k6_ana_clause_wf, full_k6_analyze_wf, full_k6_solve_wf,
    full_k6_flip_wf, full_k512_add_live_m6_wf, full_m6_dense_prop_lit_wf, full_m6_dense_prop_wf,
    full_m6_sweep_cone_wf, full_m6_sweep_refine_sig_wf, full_m6_sweep_rand_phases_wf,
    full_m6_sweep_solve_wf, full_m6_sweep_flip_round_wf, full_m6_sweep_sim_wf,
    full_m6_sweep_rearm_wf, full_m6_sweep_build_pht_wf, full_m6_extract_pht_wf,
    full_m6_refine_partition_wf, full_m6_sweep_units_wf, full_m6_sweep_classes_wf,
    full_m6_els_ar_wf, full_m6_els_lit_wf, full_m6_els_fold_wf, full_m6_dense_els_wf,
    full_m6_sweep_var_wf, full_m6_cand_sift_wf, full_m6_collect_cands_wf,
    full_m6_sweep_vars_wf, full_m6_sweep_dense_wf, full_m6_sweep_sat_wf, full_sweep_sat_m6_wf⟩

theorem m6Sweep_acyclic : m6SweepModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6Sweep
