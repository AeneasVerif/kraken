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
# Kissat Fidelity Step 13 Shard S1-C — Core K6 (`FullFidelityStep13S1Core`)

Data-pure C0 module (`0` `*Proof*` imports, `0` edits to Step-12 files) containing the `4`
Step-13 S1-C replacement functions copied verbatim from frozen `step13_v2_frozen_direct.c`:
1. `full_k6_init` (`L15821-15867`, `R1` `glue_used[33]` HWM + `L6a` split initialization loops)
2. `full_k6_add_clause` (`L15907-15942`, `R1` `glue_used[33]` HWM tracking + `full_k6_add_ticks`)
3. `full_k6_core_m7` (`L19596-19685`, `F-P0-1` non-exclusive `if (off + sz <= acap)` level-0 trace)
4. `full_k6_core_fid` (`L21514-21600`, `F-P0-1` non-exclusive `if (off + sz <= acap)` level-0 trace)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

@[expose] public section

kissat_c0! fidStep13S1Core "
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

#define K6H_NV       0u
#define K6H_NC       1u
#define K6H_UNASS    5u
#define K6H_INCONS   6u
#define K6H_QFIRST   7u
#define K6H_QLAST    8u
#define K6H_QSEARCH  9u
#define K6H_QSTAMP   10u
#define K6H_TICK_LIM 12u
#define K6H_ALEN     13u
#define K6H_ACAP     14u
#define K6H_MAX_V    21u
#define K6H_MAX_ORIG 22u
#define K6H_MAX_CL   23u

#define K6_MV        64u
#define K6_MC        256u
#define KH_NV        0u
#define KH_NC        1u
#define KH_TRL_END   5u
#define KH_INCONS    7u
#define KH_ACAP      15u
#define KO_LVL       32u
#define KO_RSN       96u
#define KO_TRL       352u
#define KO_FLAGS     416u
#define KO_CL_OFF    1888u
#define KO_CL_META   2144u
#define KO_CL_AUX    2400u
#define KO_ARENA     2912u

#define KM_LRN       0x40000000u
#define KM_CORE      0x80000000u

#define FKH_NV       4192u
#define FKH_NC       4193u
#define FKH_TRL_END  4197u
#define FKH_INCONS   4199u
#define FKH_ACAP     4207u
#define FKH_MAX_V    4214u

extern u64 full_m6_max_v(u64 cap);
extern void full_k6_assign(u32 *k, u32 lit, u32 rsn_cid);
extern void full_k6_add_ticks(u32 *k, u64 delta);
extern void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1);

void full_k6_init(FullHdr *h, u32 nv) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 *gu_hw = (u32 *)h->glue_used;
  u32 hw = gu_hw[33];
  u32 lim = nv;
  if (nv == mv && hw < mv) { lim = hw; }
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
  if (lim > 0u) {
    i = 0u;
    while (i < lim) { lvl[i] = 0u; i = i + 1u; }
    i = 0u;
    while (i < lim) { rsn[i] = 0xFFFFFFFFu; i = i + 1u; }
    i = 0u;
    while (i < lim) { flags[i] = 0u; i = i + 1u; }
    i = 0u;
    while (i < lim) { qst[i] = i + 1u; i = i + 1u; }
    qprev[0] = 0xFFFFFFFFu;
    i = 1u;
    while (i < lim) { qprev[i] = i - 1u; i = i + 1u; }
    i = 0u;
    while (i < lim) { qnext[i] = i + 1u; i = i + 1u; }
    if (nv > 0u && nv - 1u < lim) { qnext[nv - 1u] = 0xFFFFFFFFu; }
  }
  u32 *vals = k + (32u + 10u * mv); u32 *whead = k + (32u + 12u * mv);
  u32 nl = lim << 1;
  i = 0u;
  while (i < nl) { vals[i] = 0u; i = i + 1u; }
  i = 0u;
  while (i < nl) { whead[i] = 0xFFFFFFFFu; i = i + 1u; }
  if (nv == mv) { gu_hw[33] = 0u; } else if (hw < nv) { gu_hw[33] = nv; }
}

bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz) {
  u32 *gu_hw = (u32 *)h->glue_used;
  u32 hw = gu_hw[33];
  if (hw != 0xFFFFFFFFu) {
    u32 xi = 0u;
    while (xi < sz) {
      u32 xv = (lits[xi] >> 1) + 1u;
      if (xv > hw) { hw = xv; }
      xi = xi + 1u;
    }
    gu_hw[33] = hw;
  }
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
  full_k6_add_ticks(k, 1ULL);
  full_k6_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_k6_core_m7(u32 *k) {
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (nc > K6_MC || nv > K6_MV) { return; }
  u32 i = 0u;
  while (i < nc) { k[KO_CL_META + i] = k[KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = k[KH_INCONS];
  if (inc < nc) {
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
    k[KO_CL_META + inc] = k[KO_CL_META + inc] | KM_CORE;
    u32 off = k[KO_CL_OFF + inc];
    u32 sz = k[KO_CL_META + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = k[KO_ARENA + off + j] >> 1;
        if (lv < nv) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = k[KH_TRL_END];
    if (ti > K6_MV) { ti = K6_MV; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = k[KO_TRL + ti] >> 1;
      if (v >= nv || (k[KO_FLAGS + v] & 2u) == 0u) { continue; }
      k[KO_FLAGS + v] = k[KO_FLAGS + v] & (~2u);
      u32 rsn = k[KO_RSN + v];
      if (rsn >= nc) { continue; }
      k[KO_CL_META + rsn] = k[KO_CL_META + rsn] | KM_CORE;
      u32 roff = k[KO_CL_OFF + rsn];
      u32 rsz = k[KO_CL_META + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = k[KO_ARENA + roff + j] >> 1;
          if (lv < nv && lv != v) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u;
  bool changed = true;
  while (changed && pass < nc) {
    changed = false;
    pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = k[KO_CL_META + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = k[KO_CL_OFF + cid];
        u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = k[KO_CL_AUX + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = k[KO_ARENA + off + sz + j];
              if (ant < nc && (k[KO_CL_META + ant] & KM_CORE) == 0u) {
                k[KO_CL_META + ant] = k[KO_CL_META + ant] | KM_CORE;
                changed = true;
              }
              j = j + 1u;
            }
          }
        }
        if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = k[KO_ARENA + off + j] >> 1;
            if (lv < nv && k[KO_LVL + lv] == 0u) {
              u32 r0 = k[KO_RSN + lv];
              if (r0 < nc && (k[KO_CL_META + r0] & KM_CORE) == 0u) {
                k[KO_CL_META + r0] = k[KO_CL_META + r0] | KM_CORE;
                changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
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
        }
        if (off + sz <= acap) {
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
"

/-- Step-13 `full_k6_init` (`R1` HWM + `L6a` split loops). -/
def fidStep13S1K6InitFn : Fn :=
  ⟨"full_k6_init", [i64, i32], [], full_k6_init_body⟩

/-- Step-13 `full_k6_add_clause` (`R1` HWM + `full_k6_add_ticks`). -/
def fidStep13S1K6AddClauseFn : Fn :=
  ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], full_k6_add_clause_body⟩

/-- Step-13 `full_k6_core_m7` (`F-P0-1` non-exclusive level-0 trace). -/
def fidStep13S1K6CoreM7Fn : Fn :=
  ⟨"full_k6_core_m7", [i64], [], full_k6_core_m7_body⟩

/-- Step-13 `full_k6_core_fid` (`F-P0-1` non-exclusive level-0 trace). -/
def fidStep13S1K6CoreFidFn : Fn :=
  ⟨"full_k6_core_fid", [i64], [], full_k6_core_fid_body⟩

/-- Ordered `4`-function Step-13 S1-C replacement list. -/
def fidStep13S1CoreRepls : List Fn :=
  [ fidStep13S1K6InitFn
  , fidStep13S1K6AddClauseFn
  , fidStep13S1K6CoreM7Fn
  , fidStep13S1K6CoreFidFn ]

end

public section

theorem fidStep13S1K6Init_wf : Func.Wf fidStep13S1K6InitFn.body := by t_wf_reify
theorem fidStep13S1K6AddClause_wf : Func.Wf fidStep13S1K6AddClauseFn.body := by t_wf_reify
theorem fidStep13S1K6CoreM7_wf : Func.Wf fidStep13S1K6CoreM7Fn.body := by t_wf_reify
theorem fidStep13S1K6CoreFid_wf : Func.Wf fidStep13S1K6CoreFidFn.body := by t_wf_reify

theorem fidStep13S1CoreRepls_wf : ∀ f ∈ fidStep13S1CoreRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S1CoreRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact fidStep13S1K6Init_wf
  · exact fidStep13S1K6AddClause_wf
  · exact fidStep13S1K6CoreM7_wf
  · exact fidStep13S1K6CoreFid_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
