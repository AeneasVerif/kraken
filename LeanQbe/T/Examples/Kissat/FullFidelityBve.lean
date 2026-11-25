/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.FullM8SweepV2
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParity
meta import LeanQbe.T.Examples.Kissat.FullM7HotTernary
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Legal
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Kissat Fidelity BVE Upstream Parity (`FullFidelityBve`, `GAP-BVE-01..03`)

Purely additive C0 BVE parity layer (`0` `FullHdr` word growth, `0` edits to `FullM6*`/`FullM7*`/
`FullM8*` files, `0` beyond-upstream heuristics) closing all 3 upstream Kissat 4.0.4
`eliminate.c` / `definition.c` / `resolve.c` / `gates.c` parity gaps over
`FullM8SweepV2.m8FidV123t2Module`:

1. **`GAP-BVE-01` (Dynamic scratch-scaled `K6` definition subsolver & tick envelope):**
   - `full_bve_k6_mv_fid(cap)` scales `mv ∈ [256, 8192]` (`mc = 4*mv`, `max_orig = 2*mv`,
     `acap = cap - (4224 + 45*mv)`) inside existing `scratch_buf[4192..)`, raising Pass 1 / Pass 2
     ticks to upstream `1_000_000u` / `10_000_000u` (`options.h:35-37`, `definition.c:132-150`)
     with saturating `u32` ticks, `max_csz = min(max_vars, 65535)`, removal of `np + nn < 3u`,
     and `GF/RG` clearing on Pass 2 abort (`definition.c:149`).
2. **`GAP-BVE-02` (Resolution-effort termination & strict upstream gate/BVE purity):**
   - `full_eliminate_m6` sets `res_lim = max(dticks, 10_000_000ULL) / 10ULL` (`SET_EFFORT_LIMIT`,
     `eliminate.c:428`, `kimits.h:135-170`, `eliminateeffort = 100` per mille).
   - `full_elim_bve_m7` resets `h->res_sz = 0ULL` (reusing existing `FullHdr.res_sz`, `0` header
     growth), terminates on `h->res_sz > res_lim` (`eliminate.c:478, 523`), calls
     `full_dense_flush_units_m7` after each variable (`eliminate.c:494`), and drops `h->bce_cnt`.
   - `full_bve_gates_fid` strictly OMITS `D-11` (`full_bve_find_xor_m8`, `gates.c:44-55`), and
     `full_bve_var_m7` strictly OMITS `D-22` (`full_bve_bce_side_m8`, `eliminate.c:385-414`),
     while rejecting `np > 0 && nn > 0 && np + nn > 2000` (`resolve.c:285`) and counting
     `h->res_sz++` per attempted resolvent pair (`resolve.c:157`).
3. **`GAP-BVE-03` (Immediate trail enqueueing of one-sided gate core & resolvent units):**
   - `full_bve_certify_unit_fid` certifies one-sided cores (`pos_core == 0` -> `unit = nl`,
     `neg_core == 0` -> `unit = pl`, `definition.c:188-219`) either directly (`direct_entail`) or
     via the already-verified `full_k6_init`/`full_k6_add_clause`/`full_k6_solve` solver,
     immediately enqueuing `unit` via `full_assign_lvl` (or setting `h->inconsistent = 1ULL`).
   - `full_bve_var_m7` checks `vals[pl] != 0` after `full_bve_gates_fid` (`resolve.c:316-321`)
     and immediately handles `rlen == 0` (UNSAT) and `rlen == 1` (`full_assign_lvl` / UNSAT,
     `resolve.c:216-237`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM7HotTernary

kissat_c0! fidBve "
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

#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_ACTIVE             1u
#define FL_ELIM               2u
#define FL_ELIM_C             16u

#define M8_OCC_LIM            2001u
#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define M8_RES_OFF            4192u

#define FID_K6_MIN_SCR        16384ULL
#define FID_K6_MAX_V          8192ULL
#define FID_K6_TICK_P1        1000000u
#define FID_K6_TICK_P2        10000000u
#define K6_BIN_FLAG           0x80000000u
#define K6_LIT_MASK           0x7FFFFFFFu
#define KM_LRN                0x40000000u
#define KM_CORE               0x80000000u

#define FKH_NV                4192u
#define FKH_NC                4193u
#define FKH_ORIG_NC           4194u
#define FKH_LVL               4195u
#define FKH_PROP              4196u
#define FKH_TRL_END           4197u
#define FKH_UNASS             4198u
#define FKH_INCONS            4199u
#define FKH_QFIRST            4200u
#define FKH_QLAST             4201u
#define FKH_QSEARCH           4202u
#define FKH_QSTAMP            4203u
#define FKH_TICKS             4204u
#define FKH_TICK_LIM          4205u
#define FKH_ALEN              4206u
#define FKH_ACAP              4207u
#define FKH_NANA              4208u
#define FKH_NKL               4209u
#define FKH_NRES              4210u
#define FKH_NUNITS            4211u
#define FKH_OPEN              4212u
#define FKH_PHASE             4213u
#define FKH_MAX_V             4214u
#define FKH_MAX_CL            4215u
#define FKH_MAX_ORIG          4216u

extern void full_wstack_defrag(FullHdr *h);
extern u64 full_log10_q16_m7(u64 x);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);
extern u64 full_m6_max_v(u64 cap);
extern void full_k6_init(FullHdr *h, u32 nv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);
extern u64 full_k6_solve(FullHdr *h, u64 tick_lim);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc);
extern bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt);
extern u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end);
extern u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt);
extern bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn);
extern bool full_bve_find_and_m8(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n);
extern bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn);
extern u64 full_bve_heap_push_m7(FullHdr *h, u64 hlen, u32 v);
extern u32 full_bve_heap_pop_m7(FullHdr *h, u64 hlen);
extern u64 full_bve_collect_nbrs_m7(FullHdr *h, u32 v);
extern u64 full_min_u64(u64 a, u64 b);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern u64 full_forward_sub(FullHdr *h, u64 budget);

/* === GAP-BVE-01: Dynamic scratch-scaled K6 definition subsolver === */

u64 full_bve_k6_mv_fid(u64 cap) {
  if (cap < FID_K6_MIN_SCR) { return 0ULL; }
  if (cap >= 524288ULL) { return FID_K6_MAX_V; }
  u64 raw = ((cap - 4224ULL) / 64ULL) & 0xFFFFFFFFFFFFFFC0ULL;
  if (raw < 256ULL) { return 256ULL; }
  if (raw > FID_K6_MAX_V) { return FID_K6_MAX_V; }
  return raw;
}

void full_fid_k6_add_ticks(FullHdr *h, u64 delta) {
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cur = (u64)scr[FKH_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur;
  scr[FKH_TICKS] = (delta >= rem) ? 0xFFFFFFFFu : (u32)(cur + delta);
}

void full_k6_watch_fid(FullHdr *h, u32 cid, u32 l0, u32 l1, u32 sz) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 mc = mv << 2;
  if (mv < 256u || mv > 8192u || cid >= mc || l0 >= (mv << 1) || l1 >= (mv << 1)) { return; }
  u32 o_whead = 4224u + 11u * mv;
  u32 o_wnext = 4224u + 13u * mv;
  u32 o_wblit = 4224u + 21u * mv;
  u32 bf = (sz == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  scr[o_wblit + w0] = l1 | bf;
  scr[o_wnext + w0] = scr[o_whead + l0]; scr[o_whead + l0] = w0;
  scr[o_wblit + w1] = l0 | bf;
  scr[o_wnext + w1] = scr[o_whead + l1]; scr[o_whead + l1] = w1;
}

void full_k6_assign_fid(FullHdr *h, u32 lit, u32 rsn_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 te = scr[FKH_TRL_END];
  if (mv < 256u || mv > 8192u || lit >= (mv << 1) || te >= mv) { return; }
  u32 v = lit >> 1;
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  scr[o_vals + lit] = 1u; scr[o_vals + (lit ^ 1u)] = 2u;
  scr[4224u + v] = scr[FKH_LVL]; scr[o_rsn + v] = rsn_cid;
  scr[o_trl + te] = lit; scr[FKH_TRL_END] = te + 1u;
  if (scr[FKH_UNASS] > 0u) { scr[FKH_UNASS] = scr[FKH_UNASS] - 1u; }
  u32 fl = scr[o_flags + v];
  scr[o_flags + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_k6_mtf_fid(FullHdr *h, u32 v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || v >= nv || nv > mv) { return; }
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_qnext = 4224u + 3u * mv;
  u32 o_qst = 4224u + 4u * mv;
  u32 ql = scr[FKH_QLAST];
  if (v != ql) {
    u32 pv = scr[o_qprev + v]; u32 nx = scr[o_qnext + v];
    if (pv < nv) { scr[o_qnext + pv] = nx; } else { scr[FKH_QFIRST] = nx; }
    if (nx < nv) { scr[o_qprev + nx] = pv; } else { scr[FKH_QLAST] = pv; }
    u32 old_last = scr[FKH_QLAST];
    scr[o_qprev + v] = old_last; scr[o_qnext + v] = 0xFFFFFFFFu;
    if (old_last < nv) { scr[o_qnext + old_last] = v; } else { scr[FKH_QFIRST] = v; }
    scr[FKH_QLAST] = v;
  }
  u32 st = scr[FKH_QSTAMP] + 1u;
  scr[FKH_QSTAMP] = st; scr[o_qst + v] = st; scr[FKH_QSEARCH] = v;
}

void full_k6_backtrack_fid(FullHdr *h, u32 target_lvl) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || nv > mv) { return; }
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 te = scr[FKH_TRL_END];
  if (te > mv) { te = mv; }
  while (te > 0u) {
    u32 lit = scr[o_trl + te - 1u]; u32 v = lit >> 1;
    if (v >= nv || scr[4224u + v] <= target_lvl) { break; }
    te = te - 1u;
    scr[o_vals + lit] = 0u; scr[o_vals + (lit ^ 1u)] = 0u;
    scr[4224u + v] = 0u; scr[o_rsn + v] = 0xFFFFFFFFu;
    scr[FKH_UNASS] = scr[FKH_UNASS] + 1u;
  }
  scr[FKH_TRL_END] = te; scr[FKH_LVL] = target_lvl;
  if (scr[FKH_PROP] > te) { scr[FKH_PROP] = te; }
}

u32 full_k6_prop_fid(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV]; u32 nc = scr[FKH_NC]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || nv > mv || nc > (mv << 2)) { return 0xFFFFFFFFu; }
  u32 mc = mv << 2;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_whead = 4224u + 11u * mv;
  u32 o_wnext = 4224u + 13u * mv;
  u32 o_wblit = 4224u + 21u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u64 ticks = 0ULL;
  while (scr[FKH_PROP] < scr[FKH_TRL_END] && scr[FKH_PROP] < mv) {
    u32 lit = scr[o_trl + scr[FKH_PROP]]; scr[FKH_PROP] = scr[FKH_PROP] + 1u;
    if (lit >= (nv << 1)) { continue; }
    u32 nl = lit ^ 1u; u64 visits = 0ULL; u32 prev = 0xFFFFFFFFu;
    u32 w = scr[o_whead + nl]; u32 wsteps = 0u;
    while (w < (nc << 1) && wsteps < (mc << 1)) {
      wsteps = wsteps + 1u;
      u32 nxt = scr[o_wnext + w]; visits = visits + 1ULL;
      u32 wb = scr[o_wblit + w]; u32 bv = wb & K6_LIT_MASK;
      if (bv >= (nv << 1)) { prev = w; w = nxt; continue; }
      u32 bvv = scr[o_vals + bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          full_fid_k6_add_ticks(h, ticks + (visits >> 4) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign_fid(h, bv, cid); }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u; u32 off = scr[o_cl_off + cid];
      u32 sz = scr[o_cl_meta + cid] & 0xFFFFu;
      if (sz < 2u || off + sz > acap) { prev = w; w = nxt; continue; }
      u32 other = scr[o_arena + off + (slot ^ 1u)];
      if (other >= (nv << 1)) { prev = w; w = nxt; continue; }
      ticks = ticks + 1ULL;
      if (scr[o_vals + other] == 1u) {
        scr[o_wblit + w] = other; prev = w; w = nxt; continue;
      }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = scr[o_arena + off + r];
        if (cand < (nv << 1) && scr[o_vals + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        scr[o_arena + off + slot] = repl; scr[o_arena + off + ri] = nl;
        if (prev >= (nc << 1)) { scr[o_whead + nl] = nxt; }
        else { scr[o_wnext + prev] = nxt; }
        scr[o_wblit + w] = other;
        scr[o_wnext + w] = scr[o_whead + repl];
        scr[o_whead + repl] = w;
        w = nxt; continue;
      }
      scr[o_wblit + w] = other; prev = w; w = nxt;
      u32 ov = scr[o_vals + other];
      if (ov == 2u) {
        full_fid_k6_add_ticks(h, ticks + (visits >> 4) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign_fid(h, other, cid); }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  full_fid_k6_add_ticks(h, ticks);
  return 0xFFFFFFFFu;
}

void full_k6_ana_cl_fid(FullHdr *h, u32 cid, u32 skip_v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nc = scr[FKH_NC]; u32 nv = scr[FKH_NV]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || cid >= nc || nc > (mv << 2) || nv > mv) { return; }
  u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_ana = 4224u + 7u * mv;
  u32 o_kl = 4224u + 8u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_res = 4224u + 43u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 clvl = scr[FKH_LVL]; u32 off = scr[o_cl_off + cid];
  u32 sz = scr[o_cl_meta + cid] & 0xFFFFu;
  if (off + sz > acap) { return; }
  if (scr[FKH_NRES] < max_orig) {
    scr[o_res + scr[FKH_NRES]] = cid; scr[FKH_NRES] = scr[FKH_NRES] + 1u;
  } else { scr[FKH_NRES] = max_orig + 1u; }
  u32 i = 0u;
  while (i < sz) {
    u32 l = scr[o_arena + off + i]; u32 v = l >> 1;
    if (v < nv && v != skip_v && (scr[o_flags + v] & 2u) == 0u) {
      scr[o_flags + v] = scr[o_flags + v] | 2u;
      if (scr[FKH_NANA] < mv) {
        scr[o_ana + scr[FKH_NANA]] = v; scr[FKH_NANA] = scr[FKH_NANA] + 1u;
      }
      u32 vlvl = scr[4224u + v];
      if (vlvl == 0u) {
        u32 r0 = scr[o_rsn + v];
        if (r0 != 0xFFFFFFFFu) {
          if (scr[FKH_NRES] < max_orig) {
            scr[o_res + scr[FKH_NRES]] = r0; scr[FKH_NRES] = scr[FKH_NRES] + 1u;
          } else { scr[FKH_NRES] = max_orig + 1u; }
        }
      } else if (vlvl == clvl) {
        scr[FKH_OPEN] = scr[FKH_OPEN] + 1u;
      } else if (scr[FKH_NKL] < mv) {
        scr[o_kl + scr[FKH_NKL]] = l; scr[FKH_NKL] = scr[FKH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze_fid(FullHdr *h, u32 confl_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || nv > mv) { return false; }
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_ana = 4224u + 7u * mv;
  u32 o_kl = 4224u + 8u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_res = 4224u + 43u * mv;
  u32 o_arena = 4224u + 45u * mv;
  scr[FKH_NKL] = 1u; scr[FKH_NANA] = 0u; scr[FKH_NRES] = 0u; scr[FKH_OPEN] = 0u;
  full_k6_ana_cl_fid(h, confl_cid, 0xFFFFFFFFu);
  u32 clvl = scr[FKH_LVL]; u32 idx = scr[FKH_TRL_END];
  if (idx > mv) { idx = mv; }
  u32 uip = 0xFFFFFFFFu;
  while (scr[FKH_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = scr[o_trl + idx]; u32 pv = p >> 1;
    if (pv < nv && (scr[o_flags + pv] & 2u) != 0u && scr[4224u + pv] == clvl) {
      scr[FKH_OPEN] = scr[FKH_OPEN] - 1u;
      if (scr[FKH_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = scr[o_rsn + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_cl_fid(h, rsn, pv);
    }
  }
  u32 nana = scr[FKH_NANA]; if (nana > mv) { nana = mv; }
  u32 ai = 0u;
  while (ai < nana) {
    u32 av = scr[o_ana + ai];
    if (av < nv) { scr[o_flags + av] = scr[o_flags + av] & (~2u); }
    ai = ai + 1u;
  }
  u32 nres = scr[FKH_NRES]; u32 nkl = scr[FKH_NKL];
  if (uip == 0xFFFFFFFFu || uip >= (nv << 1) ||
      nres > max_orig || nkl == 0u || nkl > mv) {
    return false;
  }
  scr[o_kl] = uip;
  u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 kv = scr[o_kl + i] >> 1;
    if (kv < nv) { u32 il = scr[4224u + kv]; if (il > jlvl) { jlvl = il; wi = i; } }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = scr[o_kl + 1u]; scr[o_kl + 1u] = scr[o_kl + wi]; scr[o_kl + wi] = t;
  }
  full_k6_backtrack_fid(h, jlvl);
  ai = 0u; while (ai < nana) { full_k6_mtf_fid(h, scr[o_ana + ai]); ai = ai + 1u; }
  u32 nc = scr[FKH_NC]; u32 off = scr[FKH_ALEN];
  if (nc >= mc || off + nkl + nres > scr[FKH_ACAP]) { return false; }
  i = 0u; while (i < nkl) { scr[o_arena + off + i] = scr[o_kl + i]; i = i + 1u; }
  i = 0u; while (i < nres) { scr[o_arena + off + nkl + i] = scr[o_res + i]; i = i + 1u; }
  scr[FKH_ALEN] = off + nkl + nres;
  scr[o_cl_off + nc] = off;
  scr[o_cl_meta + nc] = nkl | KM_LRN; scr[o_cl_aux + nc] = nres;
  scr[FKH_NC] = nc + 1u;
  if (nkl == 1u) { full_k6_assign_fid(h, uip, nc); return true; }
  full_k6_watch_fid(h, nc, scr[o_kl], scr[o_kl + 1u], nkl);
  full_k6_assign_fid(h, uip, nc);
  return true;
}

u64 full_k6_solve_fid(FullHdr *h, u32 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  if (mv < 256u || mv > 8192u) { return 0ULL; }
  full_k6_backtrack_fid(h, 0u);
  if (scr[FKH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  scr[FKH_TICK_LIM] = tick_lim; scr[FKH_TICKS] = 0u;
  u32 nv = scr[FKH_NV]; u32 nc = scr[FKH_NC];
  u32 acap = scr[FKH_ACAP]; u32 nunits = scr[FKH_NUNITS];
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  if (nv > mv || nc > mc || nunits > max_orig) { return 0ULL; }
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_units = 4224u + 41u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 ui = 0u;
  while (ui < nunits) {
    u32 ucid = scr[o_units + ui];
    if (ucid < nc) {
      u32 off = scr[o_cl_off + ucid];
      if (off < acap) {
        u32 ul = scr[o_arena + off];
        if (ul < (nv << 1)) {
          u32 uv = scr[o_vals + ul];
          if (uv == 2u) { scr[FKH_INCONS] = ucid; return 20ULL; }
          if (uv == 0u) { full_k6_assign_fid(h, ul, ucid); }
        }
      }
    }
    ui = ui + 1u;
  }
  u32 confl = full_k6_prop_fid(h);
  if (confl != 0xFFFFFFFFu) { scr[FKH_INCONS] = confl; return 20ULL; }
  while (scr[FKH_TICKS] < scr[FKH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (scr[FKH_LVL] == 0u) { scr[FKH_INCONS] = confl; return 20ULL; }
      if (!full_k6_analyze_fid(h, confl)) { return 0ULL; }
      confl = full_k6_prop_fid(h);
      continue;
    }
    if (scr[FKH_UNASS] == 0u) { return 10ULL; }
    u32 cur = scr[FKH_QSEARCH]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
      cur = scr[o_qprev + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = scr[FKH_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
        cur = scr[o_qprev + cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    scr[FKH_QSEARCH] = pick;
    u32 ph = (scr[o_flags + pick] ^ scr[FKH_PHASE]) & 1u;
    scr[FKH_LVL] = scr[FKH_LVL] + 1u;
    full_k6_assign_fid(h, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_prop_fid(h);
  }
  return 0ULL;
}

void full_k6_core_fid(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nc = scr[FKH_NC]; u32 nv = scr[FKH_NV]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || nc > (mv << 2) || nv > mv) { return; }
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 i = 0u;
  while (i < nc) { scr[o_cl_meta + i] = scr[o_cl_meta + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = scr[FKH_INCONS];
  if (inc < nc) {
    i = 0u; while (i < nv) { scr[o_flags + i] = scr[o_flags + i] & (~2u); i = i + 1u; }
    scr[o_cl_meta + inc] = scr[o_cl_meta + inc] | KM_CORE;
    u32 off = scr[o_cl_off + inc]; u32 sz = scr[o_cl_meta + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = scr[o_arena + off + j] >> 1;
        if (lv < nv) { scr[o_flags + lv] = scr[o_flags + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = scr[FKH_TRL_END]; if (ti > mv) { ti = mv; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = scr[o_trl + ti] >> 1;
      if (v >= nv || (scr[o_flags + v] & 2u) == 0u) { continue; }
      scr[o_flags + v] = scr[o_flags + v] & (~2u);
      u32 rsn = scr[o_rsn + v];
      if (rsn >= nc) { continue; }
      scr[o_cl_meta + rsn] = scr[o_cl_meta + rsn] | KM_CORE;
      u32 roff = scr[o_cl_off + rsn]; u32 rsz = scr[o_cl_meta + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = scr[o_arena + roff + j] >> 1;
          if (lv < nv && lv != v) { scr[o_flags + lv] = scr[o_flags + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u; while (i < nv) { scr[o_flags + i] = scr[o_flags + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u; bool changed = true;
  while (changed && pass < nc) {
    changed = false; pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = scr[o_cl_meta + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = scr[o_cl_off + cid]; u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = scr[o_cl_aux + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = scr[o_arena + off + sz + j];
              if (ant < nc && (scr[o_cl_meta + ant] & KM_CORE) == 0u) {
                scr[o_cl_meta + ant] = scr[o_cl_meta + ant] | KM_CORE; changed = true;
              }
              j = j + 1u;
            }
          }
        } else if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = scr[o_arena + off + j] >> 1;
            if (lv < nv && scr[4224u + lv] == 0u) {
              u32 r0 = scr[o_rsn + lv];
              if (r0 < nc && (scr[o_cl_meta + r0] & KM_CORE) == 0u) {
                scr[o_cl_meta + r0] = scr[o_cl_meta + r0] | KM_CORE; changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

bool full_k6_extract_and_solve_fid(
    FullHdr *h, u32 v, u32 np, u32 nn, bool second_pass, u32 tick_lim) {
  u32 mv = (u32)full_bve_k6_mv_fid(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_qnext = 4224u + 3u * mv;
  u32 o_qst = 4224u + 4u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_whead = 4224u + 11u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_units = 4224u + 41u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 acap = (u32)(h->scratch_cap - (u64)o_arena);
  u32 max_csz = (h->max_vars < 65535ULL) ? (u32)h->max_vars : 65535u;
  u32 nv = 0u; u32 nc = 0u; u32 alen = 0u; u32 nunits = 0u;
  u32 trivial_eid = 0xFFFFFFFFu; bool abort_def = false;
  u32 pl = v << 1; u32 nl = pl | 1u;
  u32 s_step = 0u;
  while (s_step < 2u && !abort_def && trivial_eid == 0xFFFFFFFFu) {
    u32 side = second_pass ? (1u - s_step) : s_step;
    u32 cnt = (side == 0u) ? np : nn;
    u32 off_s = (side == 0u) ? 0u : M8_NEG_OFF;
    u32 mb = (side == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 except = (side == 0u) ? pl : nl;
    u32 step = 0u;
    while (step < cnt && !abort_def) {
      u32 idx = second_pass ? (cnt - 1u - step) : step;
      step = step + 1u;
      if (second_pass && ((scr[mb + (idx >> 5)] >> (idx & 31u)) & 1u) == 0u) { continue; }
      u32 w = scr[off_s + idx];
      u32 eid = (side << 11) | idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { trivial_eid = eid; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= mv || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
          if (nc >= max_orig || alen + 1u > acap) { abort_def = true; break; }
          scr[o_arena + alen] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          scr[o_cl_off + nc] = alen; scr[o_cl_meta + nc] = 1u; scr[o_cl_aux + nc] = eid;
          scr[o_units + nunits] = nc; nunits = nunits + 1u; nc = nc + 1u; alen = alen + 1u;
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= mv || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              if (csz >= max_csz) { abort_def = true; break; }
              tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_eid = eid; break; }
          if (nc >= max_orig || alen + csz > acap) { abort_def = true; break; }
          m = 0u; while (m < csz) { scr[o_arena + alen + m] = tmp[m]; m = m + 1u; }
          scr[o_cl_off + nc] = alen; scr[o_cl_meta + nc] = csz;
          scr[o_cl_aux + nc] = eid;
          if (csz == 1u) { scr[o_units + nunits] = nc; nunits = nunits + 1u; }
          nc = nc + 1u; alen = alen + csz;
        }
      }
    }
    s_step = s_step + 1u;
  }
  u32 ci = 0u;
  while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_eid != 0xFFFFFFFFu) {
    u32 idx = trivial_eid & 0x7FFu;
    u32 mbase = ((trivial_eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
    scr[mbase + (idx >> 5)] = 1u << (idx & 31u);
    scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u;
    return true;
  }
  if (abort_def || nv == 0u || nc < 2u) { return false; }
  scr[FKH_NV] = nv; scr[FKH_NC] = nc; scr[FKH_ORIG_NC] = nc;
  scr[FKH_LVL] = 0u; scr[FKH_PROP] = 0u; scr[FKH_TRL_END] = 0u; scr[FKH_UNASS] = nv;
  scr[FKH_INCONS] = 0xFFFFFFFFu;
  scr[FKH_QFIRST] = 0u; scr[FKH_QLAST] = nv - 1u;
  scr[FKH_QSEARCH] = nv - 1u; scr[FKH_QSTAMP] = nv;
  scr[FKH_TICKS] = 0u; scr[FKH_TICK_LIM] = tick_lim;
  scr[FKH_ALEN] = alen; scr[FKH_ACAP] = acap;
  scr[FKH_NANA] = 0u; scr[FKH_NKL] = 0u; scr[FKH_NRES] = 0u; scr[FKH_NUNITS] = nunits;
  scr[FKH_OPEN] = 0u; scr[FKH_PHASE] = 0u;
  scr[FKH_MAX_V] = mv; scr[FKH_MAX_CL] = mc; scr[FKH_MAX_ORIG] = max_orig;
  u32 i = 0u;
  while (i < nv) {
    scr[4224u + i] = 0u; scr[o_rsn + i] = 0xFFFFFFFFu; scr[o_flags + i] = 0u;
    scr[o_qst + i] = i + 1u;
    scr[o_qprev + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    scr[o_qnext + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  i = 0u;
  while (i < (nv << 1)) {
    scr[o_vals + i] = 0u; scr[o_whead + i] = 0xFFFFFFFFu; i = i + 1u;
  }
  i = 0u;
  while (i < nc) {
    u32 sz = scr[o_cl_meta + i] & 0xFFFFu;
    if (sz >= 2u) {
      u32 off = scr[o_cl_off + i];
      full_k6_watch_fid(h, i, scr[o_arena + off], scr[o_arena + off + 1u], sz);
    }
    i = i + 1u;
  }
  if (full_k6_solve_fid(h, tick_lim) != 20ULL) { return false; }
  full_k6_core_fid(h);
  u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
  bool any = false; u32 onc = scr[FKH_ORIG_NC]; i = 0u;
  while (i < onc) {
    if ((scr[o_cl_meta + i] & KM_CORE) != 0u) {
      u32 eid = scr[o_cl_aux + i];
      u32 idx = eid & 0x7FFu;
      u32 mbase = ((eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
      u32 widx = mbase + (idx >> 5);
      scr[widx] = scr[widx] | (1u << (idx & 31u));
      any = true;
    }
    i = i + 1u;
  }
  if (any) { scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u; }
  return any;
}

/* === GAP-BVE-03: Certified one-sided core unit enqueueing === */

bool full_bve_certify_unit_fid(
    FullHdr *h, u32 v, u32 unit, u32 side_off, u32 side_cnt, u32 side_mask) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 mv_sw = (u32)full_m6_max_v(h->scratch_cap);
  u32 max_csz = (h->max_vars < 65535ULL) ? (u32)h->max_vars : 65535u;
  u32 nv = 0u;
  bool direct_entail = false;
  bool abort_c = false;
  u32 idx = 0u;
  while (idx < side_cnt && !direct_entail && !abort_c) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { direct_entail = true; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_c) { break; }
        if (!sat) {
          if (csz == 0u) { direct_entail = true; break; }
          if (csz > max_csz) { abort_c = true; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  if (direct_entail) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    i8 uv = vals[unit];
    if (uv < (i8)0) { h->inconsistent = 1ULL; }
    else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
    return true;
  }
  if (abort_c || nv == 0u || mv_sw == 0u || 1280u + (mv_sw << 1) < 4192u) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    return false;
  }
  full_k6_init(h, nv);
  bool ok = true;
  idx = 0u;
  while (idx < side_cnt && ok) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        if (vals[l] == (i8)0) {
          u32 loc = tmk[l >> 1];
          if (loc == 0u || loc > nv) { ok = false; break; }
          tmp[0] = ((loc - 1u) << 1) | (l & 1u);
          if (!full_k6_add_clause(h, tmp, 1u)) { ok = false; break; }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 loc = tmk[l >> 1];
              if (loc == 0u || loc > nv || csz >= max_csz) { ok = false; break; }
              tmp[csz] = ((loc - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (!ok) { break; }
        if (!sat) {
          if (!full_k6_add_clause(h, tmp, csz)) { ok = false; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (!ok) { return false; }
  if (full_k6_solve(h, (u64)FID_K6_TICK_P1) != 20ULL) { return false; }
  i8 uv = vals[unit];
  if (uv < (i8)0) { h->inconsistent = 1ULL; }
  else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
  return true;
}

void full_bve_def_k6_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 mv = (u32)full_bve_k6_mv_fid(h->scratch_cap);
  if (mv == 0u || np == 0u || nn == 0u || np + nn > (mv << 1)) { return; }
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, false, FID_K6_TICK_P1)) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, true, FID_K6_TICK_P2)) {
    scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    return;
  }
  bool has_pos = false; bool has_neg = false; u32 mi = 0u;
  while (mi < 64u) {
    if (scr[M8_POS_MASK + mi] != 0u) { has_pos = true; }
    if (scr[M8_NEG_MASK + mi] != 0u) { has_neg = true; }
    mi = mi + 1u;
  }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (!has_pos && has_neg) {
    full_bve_certify_unit_fid(h, v, nl, M8_NEG_OFF, nn, M8_NEG_MASK);
  } else if (has_pos && !has_neg) {
    full_bve_certify_unit_fid(h, v, pl, 0u, np, M8_POS_MASK);
  }
}

/* === GAP-BVE-02: Pure upstream gate dispatcher (no D-11 XOR) & BVE driver (no D-22 BCE) === */

void full_bve_gates_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 130u) { scr[M8_POS_MASK + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m8(h, np, nn)) { return; }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (full_bve_find_and_m8(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m8(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m8(h, v, np, nn)) { return; }
  full_bve_def_k6_fid(h, v, np, nn);
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
  u64 ext_need = full_bve_ext_need(h, 0u, np) + full_bve_ext_need(h, neg_off, nn);
  bool ext_ok = (h->extend_len + ext_need <= h->extend_cap);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken(h, nl, neg_off, nn))) {
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
    if (!full_bve_weaken(h, pl, 0u, np) || !full_bve_weaken(h, nl, neg_off, nn)) {
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

u64 full_bve_var(FullHdr *h, u32 v) {
  return full_bve_var_m7(h, v);
}

u64 full_elim_bve_m7(FullHdr *h, u64 res_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *hp = (u32 *)h->work_stk1;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 mv = h->max_vars;
  u32 *mclr = (u32 *)h->min_clr;
  u64 cv0 = h->cur_vars;
  u64 ci = 0ULL;
  while (ci < cv0) { mclr[ci] = 0u; ci = ci + 1ULL; }
  h->res_sz = 0ULL;
  bool hit_lim = false;
  u64 hlen = 0ULL;
  bool last_round_elim = false;
  u64 round = 0ULL;
  while (round < 2ULL && !hit_lim && h->res_sz <= res_lim && h->fuel > 0ULL &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    if (!full_dense_flush_units_m7(h)) { return 20ULL; }
    u64 cv = h->cur_vars;
    u64 i = 0ULL;
    while (i < cv) { hp[mv + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    hlen = 0ULL;
    i = 0ULL;
    while (i < cv) {
      if ((fl[i] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) &&
          vals[i << 1] == (i8)0) {
        hlen = full_bve_heap_push_m7(h, hlen, (u32)i);
      }
      i = i + 1ULL;
    }
    if (hlen == 0ULL) { last_round_elim = false; break; }
    bool round_elim = false;
    while (hlen > 0ULL && h->fuel > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
      if (h->res_sz > res_lim) { hit_lim = true; break; }
      u32 v = full_bve_heap_pop_m7(h, hlen);
      hlen = hlen - 1ULL;
      u64 cv1 = h->cur_vars;
      if (v == 0xFFFFFFFFu || (u64)v >= cv1) { continue; }
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) != (FL_ACTIVE | FL_ELIM_C) ||
          vals[(u64)v << 1] != (i8)0) { continue; }
      fl[v] = fl[v] & (~FL_ELIM_C);
      h->fuel = h->fuel - 1ULL;
      u64 nn = full_bve_collect_nbrs_m7(h, v);
      u64 b0 = h->bve_cnt;
      u64 st = full_bve_var_m7(h, v);
      if (st == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
      if (st == 2ULL) { break; }
      if (!full_dense_flush_units_m7(h)) { return 20ULL; }
      if (h->bve_cnt > b0) {
        round_elim = true;
        u64 cv2 = h->cur_vars;
        u64 k = 0ULL;
        while (k < nn) {
          u32 u = nbrs[k];
          if ((u64)u < cv2 && (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
            fl[u] = fl[u] | FL_ELIM_C;
            hlen = full_bve_heap_push_m7(h, hlen, u);
          }
          k = k + 1ULL;
        }
      }
    }
    last_round_elim = round_elim;
    if (!round_elim) { break; }
    round = round + 1ULL;
  }
  if (h->inconsistent == 0ULL) {
    u64 cvf = h->cur_vars;
    bool complete = (!hit_lim && h->res_sz <= res_lim && hlen == 0ULL &&
        !last_round_elim && h->oom == 0ULL && h->fuel > 0ULL);
    if (complete) {
      u64 cur_b = h->elim_bound;
      if (cur_b < 16ULL) {
        u64 next_b = (cur_b == 0ULL) ? 1ULL : (cur_b << 1);
        if (next_b > 16ULL) { next_b = 16ULL; }
        h->elim_bound = next_b;
        u64 k = 0ULL;
        while (k < cvf) { fl[k] = fl[k] | FL_ELIM_C; k = k + 1ULL; }
      }
    } else {
      u64 k = 0ULL;
      while (k < cvf) { fl[k] = fl[k] & (~FL_ELIM_C); k = k + 1ULL; }
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 arg = (h->eliminations > (~0ULL) - 9ULL) ? (~0ULL) : (h->eliminations + 9ULL);
    u64 qlog = full_log10_q16_m7(arg);
    u64 ec = (h->eliminations > 100000000ULL) ? 100000000ULL : h->eliminations;
    u64 nloge = ((((500ULL * ec) * qlog) >> 16) * qlog) >> 16;
    u64 delta = full_scale_delta(h, nloge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!full_enter_dense(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbud = full_min_u64(initial ? 2048ULL : (128ULL + (dticks >> 6)), 4096ULL);
  u64 fs = full_forward_sub(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 base_t = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 res_lim = base_t / 10ULL;
  u64 res = full_elim_bve_m7(h, res_lim);
  u64 rr = full_rebuild_watches(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}
"

/-! ## 1. `Fn` Handles, Pure BVE Helper/Replacement Lists, & Spliced Modules -/

def fidBveK6MvFn : Fn :=
  ⟨"full_bve_k6_mv_fid", [i64], [i64], full_bve_k6_mv_fid_body⟩
def fidK6AddTicksFn : Fn :=
  ⟨"full_fid_k6_add_ticks", [i64, i64], [], full_fid_k6_add_ticks_body⟩
def fidK6WatchFn : Fn :=
  ⟨"full_k6_watch_fid", [i64, i32, i32, i32, i32], [], full_k6_watch_fid_body⟩
def fidK6AssignFn : Fn :=
  ⟨"full_k6_assign_fid", [i64, i32, i32], [], full_k6_assign_fid_body⟩
def fidK6MtfFn : Fn :=
  ⟨"full_k6_mtf_fid", [i64, i32], [], full_k6_mtf_fid_body⟩
def fidK6BacktrackFn : Fn :=
  ⟨"full_k6_backtrack_fid", [i64, i32], [], full_k6_backtrack_fid_body⟩
def fidK6PropFn : Fn :=
  ⟨"full_k6_prop_fid", [i64], [i32], full_k6_prop_fid_body⟩
def fidK6AnaClFn : Fn :=
  ⟨"full_k6_ana_cl_fid", [i64, i32, i32], [], full_k6_ana_cl_fid_body⟩
def fidK6AnalyzeFn : Fn :=
  ⟨"full_k6_analyze_fid", [i64, i32], [.bool], full_k6_analyze_fid_body⟩
def fidK6SolveFn : Fn :=
  ⟨"full_k6_solve_fid", [i64, i32], [i64], full_k6_solve_fid_body⟩
def fidK6CoreFn : Fn :=
  ⟨"full_k6_core_fid", [i64], [], full_k6_core_fid_body⟩
def fidK6ExtractSolveFn : Fn :=
  ⟨"full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool],
    full_k6_extract_and_solve_fid_body⟩
def fidBveCertifyUnitFn : Fn :=
  ⟨"full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool],
    full_bve_certify_unit_fid_body⟩
def fidBveDefK6Fn : Fn :=
  ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [], full_bve_def_k6_fid_body⟩
def fidBveGatesFn : Fn :=
  ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], full_bve_gates_fid_body⟩

def fidBveVarM7Fn : Fn :=
  ⟨"full_bve_var_m7", [i64, i32], [i64], full_bve_var_m7_body⟩
def fidBveVarFn : Fn :=
  ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_body⟩
def fidElimBveM7Fn : Fn :=
  ⟨"full_elim_bve_m7", [i64, i64], [i64], full_elim_bve_m7_body⟩
def fidEliminateM6Fn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], full_eliminate_m6_body⟩

/-- Pure upstream BVE helper list (`20` fns = `5` reused M8 equiv/and/ite helpers + `15` dynamic
K6 / unit-certification / gate helpers; strictly OMITS `D-11` XOR and `D-22` BCE). -/
def fidBveHelpers : List Fn :=
  [ m8BveFindEquivFn, m8BveFindAndFn, m8BveMatchTernFn, m8BveFindIteSideFn, m8BveFindIteFn
  , fidBveK6MvFn, fidK6AddTicksFn, fidK6WatchFn, fidK6AssignFn, fidK6MtfFn
  , fidK6BacktrackFn, fidK6PropFn, fidK6AnaClFn, fidK6AnalyzeFn, fidK6SolveFn
  , fidK6CoreFn, fidK6ExtractSolveFn, fidBveCertifyUnitFn, fidBveDefK6Fn, fidBveGatesFn ]

/-- Insertion plan placing all `20` pure BVE helpers immediately before `full_bve_var_m7`. -/
def fidBveBefores : List (Sym × List Fn) :=
  [ ("full_bve_var_m7", fidBveHelpers) ]

/-- `5`-function BVE parity replacement table over `FullM8SweepV2.m8FidV123t2Module`
(compatible with `MainLinkReuse`, `FullM8SweepV2`, and `FullM8CoreParity`). -/
def fidBveRepls : List Fn :=
  [ fidBveVarM7Fn, fidBveVarFn, m8BveVarKeyM7Fn, fidElimBveM7Fn, fidEliminateM6Fn ]

/-- Purified combined replacement list uniting `FullM8CoreParity` Ranks `#4/#5` +
`FullM7HotTernary` + `FullFidelityBve` (`0` `D-11` XOR, `0` `D-22` BCE). -/
def fidBveCoreParityRepls : List Fn :=
  [ m8MinShrinkM6Fn, fidBveVarM7Fn, fidBveVarFn, m8BveVarKeyM7Fn, fidElimBveM7Fn
  , fidEliminateM6Fn, m8ProbeDticksM6HdrFn, m8ProbeM6Fn, m8SearchM6Fn, m7HasTernaryFn ]

/-- Purified combined insertion list uniting `FullM8CoreParity` Rank `#5` helpers +
`FullFidelityBve` pure BVE helpers (`0` `D-11` XOR, `0` `D-22` BCE). -/
def fidBveCoreParityBefores : List (Sym × List Fn) :=
  [ ("full_min_shrink_m6", m8MinHelpers)
  , ("full_bve_var_m7", fidBveHelpers) ]

/-! ## 2. Well-Formedness & Spliced Modules (`fidBveModule`, `fidBveCoreParityModule`) -/

theorem full_bve_k6_mv_fid_wf : Func.Wf full_bve_k6_mv_fid_body := by t_wf_reify
theorem full_fid_k6_add_ticks_wf : Func.Wf full_fid_k6_add_ticks_body := by t_wf_reify
theorem full_k6_watch_fid_wf : Func.Wf full_k6_watch_fid_body := by t_wf_reify
theorem full_k6_assign_fid_wf : Func.Wf full_k6_assign_fid_body := by t_wf_reify
theorem full_k6_mtf_fid_wf : Func.Wf full_k6_mtf_fid_body := by t_wf_reify
theorem full_k6_backtrack_fid_wf : Func.Wf full_k6_backtrack_fid_body := by t_wf_reify
theorem full_k6_prop_fid_wf : Func.Wf full_k6_prop_fid_body := by t_wf_reify
theorem full_k6_ana_cl_fid_wf : Func.Wf full_k6_ana_cl_fid_body := by t_wf_reify
theorem full_k6_analyze_fid_wf : Func.Wf full_k6_analyze_fid_body := by t_wf_reify
theorem full_k6_solve_fid_wf : Func.Wf full_k6_solve_fid_body := by t_wf_reify
theorem full_k6_core_fid_wf : Func.Wf full_k6_core_fid_body := by t_wf_reify
theorem full_k6_extract_and_solve_fid_wf :
    Func.Wf full_k6_extract_and_solve_fid_body := by t_wf_reify
theorem full_bve_certify_unit_fid_wf : Func.Wf full_bve_certify_unit_fid_body := by t_wf_reify
theorem full_bve_def_k6_fid_wf : Func.Wf full_bve_def_k6_fid_body := by t_wf_reify
theorem full_bve_gates_fid_wf : Func.Wf full_bve_gates_fid_body := by t_wf_reify
theorem full_bve_var_m7_fid_wf : Func.Wf full_bve_var_m7_body := by t_wf_reify
theorem full_bve_var_fid_wf : Func.Wf full_bve_var_body := by t_wf_reify
theorem full_elim_bve_m7_fid_wf : Func.Wf full_elim_bve_m7_body := by t_wf_reify
theorem full_eliminate_m6_fid_wf : Func.Wf full_eliminate_m6_body := by t_wf_reify

theorem fidBveHelpers_wf : ∀ h ∈ fidBveHelpers, h.Wf := by
  intro h hh
  simp only [fidBveHelpers, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_bve_find_equiv_m8_wf
  · exact full_bve_find_and_m8_wf
  · exact full_bve_match_tern_m8_wf
  · exact full_bve_find_ite_side_m8_wf
  · exact full_bve_find_ite_m8_wf
  · exact full_bve_k6_mv_fid_wf
  · exact full_fid_k6_add_ticks_wf
  · exact full_k6_watch_fid_wf
  · exact full_k6_assign_fid_wf
  · exact full_k6_mtf_fid_wf
  · exact full_k6_backtrack_fid_wf
  · exact full_k6_prop_fid_wf
  · exact full_k6_ana_cl_fid_wf
  · exact full_k6_analyze_fid_wf
  · exact full_k6_solve_fid_wf
  · exact full_k6_core_fid_wf
  · exact full_k6_extract_and_solve_fid_wf
  · exact full_bve_certify_unit_fid_wf
  · exact full_bve_def_k6_fid_wf
  · exact full_bve_gates_fid_wf

theorem fidBveRepls_wf : ∀ r ∈ fidBveRepls, r.Wf := by
  intro r hr
  simp only [fidBveRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact full_bve_var_m7_fid_wf
  · exact full_bve_var_fid_wf
  · exact full_bve_var_key_m7_m8_wf
  · exact full_elim_bve_m7_fid_wf
  · exact full_eliminate_m6_fid_wf

theorem fidBveBefores_flat_wf : ∀ h ∈ fidBveBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidBveBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hh
  exact fidBveHelpers_wf h hh

theorem fidBveNew_wf : ∀ fn, (fn ∈ fidBveRepls ∨ fn ∈ fidBveBefores.flatMap Prod.snd) → fn.Wf := by
  intro fn h
  rcases h with h1 | h2
  · exact fidBveRepls_wf fn h1
  · exact fidBveBefores_flat_wf fn h2

theorem fidBveCoreParityRepls_wf : ∀ r ∈ fidBveCoreParityRepls, r.Wf := by
  intro r hr
  simp only [fidBveCoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_min_shrink_m6_m8_wf
  · exact full_bve_var_m7_fid_wf
  · exact full_bve_var_fid_wf
  · exact full_bve_var_key_m7_m8_wf
  · exact full_elim_bve_m7_fid_wf
  · exact full_eliminate_m6_fid_wf
  · exact full_probe_dticks_m6_hdr_m8_wf
  · exact full_probe_m6_m8_wf
  · exact full_search_m6_m8_wf
  · exact m7HasTernaryFn_wf

theorem fidBveCoreParityBefores_flat_wf :
    ∀ h ∈ fidBveCoreParityBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidBveCoreParityBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at hh
  rcases hh with hmin | hbve
  · exact m8CoreParityBefores_wf ("full_min_shrink_m6", m8MinHelpers)
      (by simp [m8CoreParityBefores]) h hmin
  · exact fidBveHelpers_wf h hbve

/-- `469`-function pure BVE parity module function list over `FullM8SweepV2.m8FidV123t2Module`
(`449 + 20`, `0` `D-11` XOR, `0` `D-22` BCE). -/
def fidBveFns : List Fn :=
  PatchModule.patchFns fidBveRepls fidBveBefores FullM8SweepV2.m8FidV123t2Fns

/-- Closed `469`-function pure BVE parity module over `FullM8SweepV2.m8FidV123t2Module`
(`0` externs, `0` exits). -/
def fidBveModule : LeanQbe.T.Module :=
  PatchModule.patchModule FullM8SweepV2.m8FidV123t2Module fidBveRepls fidBveBefores

/-- `472`-function purified combined module function list uniting `FullM8CoreParity` Ranks `#4/#5`
+ `FullM7HotTernary` + `FullFidelityBve` (`449 + 23`, `0` `D-11` XOR, `0` `D-22` BCE). -/
def fidBveCoreParityFns : List Fn :=
  PatchModule.patchFns fidBveCoreParityRepls fidBveCoreParityBefores FullM8SweepV2.m8FidV123t2Fns

/-- Closed `472`-function purified combined module (`0` externs, `0` exits). -/
def fidBveCoreParityModule : LeanQbe.T.Module :=
  PatchModule.patchModule FullM8SweepV2.m8FidV123t2Module
    fidBveCoreParityRepls fidBveCoreParityBefores

theorem fidBveModule_noExit : fidBveModule.exits = [] :=
  FullM8SweepV2.m8FidV123t2_noExit
theorem fidBveCoreParityModule_noExit : fidBveCoreParityModule.exits = [] :=
  FullM8SweepV2.m8FidV123t2_noExit

end LeanQbe.T.Examples.Kissat.FullFidelityBve

end
