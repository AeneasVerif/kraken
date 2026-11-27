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
# Kissat Fidelity Step 13 Shard S3-B: Search, Restart, EMAs & `--seed`
(`FullFidelityStep13S3SearchRestart`)

Data-pure C0 layer (`20` sig-preserving replacement functions + `2` added functions:
`full_randec_var_lvl_fid` and `kissat_solve_bytes_seeded`; `0` `*Proof*` imports, every function
`<= 6` SysV args) copied verbatim from frozen `step13_v2_frozen_direct.c`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fidStep13S3SearchRestart "
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

#define PH_GARB             0x00080000u
#define PH_RED              0x00400000u
#define PW_BIN_FLAG         0x80000000u
#define PW_LIT_MASK         0x7FFFFFFFu

#define FL_ACTIVE           1u
#define FL_SUBSUME          8u
#define FL_ELIM_C           16u
#define FL_FACT_P           32u
#define FL_FACT_N           64u
#define FL_BONE0            128u
#define FL_BONE1            256u
#define FL_TRANS            512u
#define FL_SWEEP            1024u

#define M6_EXT_BYTES        2304ULL
#define M6_HDR_TOTAL_BYTES  3456ULL
#define M6_WM_PROBE_TICKS   0ULL
#define M6W_DR_STATE        1ULL
#define M6W_DR_PREV         2ULL
#define M6W_DR_SB           4ULL
#define M6W_DR_SE           6ULL

#define M7_SEARCH_MAGIC     0x4D37534541524348ULL
#define M7_GU_MAGIC         36ULL
#define M7_GU_EMA_MASK      38ULL
#define M7_GU_EMA0_FB       40ULL
#define M7_GU_EMA0_FE       42ULL
#define M7_GU_EMA0_SB       44ULL
#define M7_GU_EMA0_SE       46ULL
#define M7_GU_EMA1_FB       48ULL
#define M7_GU_EMA1_FE       50ULL
#define M7_GU_EMA1_SB       52ULL
#define M7_GU_EMA1_SE       54ULL
#define M7_GU_RANDEC_REM    56ULL
#define M7_GU_RANDEC_LIM    58ULL
#define M7_GU_RANDEC_SEQ    60ULL
#define M7_GU_RANDEC_CFL    62ULL

extern u64 f64u_add(u64 a, u64 b);
extern u64 f64u_sub(u64 a, u64 b);
extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_div(u64 a, u64 b);
extern u64 f64u_from_u64(u64 x);
extern u64 f64u_to_u64(u64 a);
extern u64 f64u_log10_u64(u64 x);
extern u64 f64u_nlogpown(u64 count, u64 exponent);
extern u64 m6_wm4_get(FullHdr *h);
extern void m6_wm4_set(FullHdr *h, u64 v);
extern void full_update_classify_fid(FullHdr *h);
extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max);
extern u64 full_ilog10(u64 x);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_heap_up(FullHdr *h, u32 v);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_heap_push(FullHdr *h, u32 v);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void m6_ext_ensure_init(FullHdr *h);
extern u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end, u64 work_base, u64 avail, u64 fuel);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);
extern u64 full_propagate(FullHdr *h);
extern u64 full_parse_body(FullHdr *h, u64 cnf_end);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern u64 full_analyze_m6_hdr(FullHdr *h);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_walk(FullHdr *h);
extern void full_extend(FullHdr *h);
extern u64 full_reorder_m6(FullHdr *h, u64 budget);
extern u64 full_lcg_next_m7(FullHdr *h);
extern u64 full_m7_get64(FullHdr *h, u64 idx);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern u64 full_lucky_late_m7(FullHdr *h);
extern u64 full_preprocess_m6(FullHdr *h);
extern u64 full_simplify_m6(FullHdr *h, bool do_probe, bool do_elim);
extern u64 m6_hdr_decide_fid(FullHdr *h);

u64 full_scale_delta_m5(FullHdr *h, u64 delta) {
  if (delta == 0ULL) { return 0ULL; }
  u64 ir = h->num_irred;
  u64 bn = h->num_binary;
  u64 clauses = (ir > 0xFFFFFFFFFFFFFFFFULL - bn) ? 0xFFFFFFFFFFFFFFFFULL : (ir + bn);
  u64 arg = (clauses > 0xFFFFFFFFFFFFFFF5ULL) ? 0xFFFFFFFFFFFFFFFFULL : (clauses + 10ULL);
  u64 l = f64u_log10_u64(arg);
  if (l < 0x3FF0000000000000ULL) { l = 0x3FF0000000000000ULL; }
  u64 five = 0x4014000000000000ULL;
  u64 f_abs = (l >= five) ? f64u_sub(l, five) : f64u_sub(five, l);
  u64 ff = f64u_mul(f_abs, f_abs);
  u64 fff = f64u_add(f64u_mul(0x4012000000000000ULL, ff), 0x4039000000000000ULL);
  return f64u_to_u64(f64u_mul(fff, f64u_from_u64(delta)));
}

void full_ema_update(FullHdr *h, u64 glue) {
  if (h->stable != 0ULL) { return; }
  u64 y = f64u_from_u64(glue);
  u64 fb = h->ema_fast_biased;
  u64 fe = h->ema_fast_exp;
  u64 sb = h->ema_slow_biased;
  u64 se = h->ema_slow_exp;
  u64 af = 0x3F9F07C1F07C1F08ULL;
  u64 bf = 0x3FEF07C1F07C1F08ULL;
  if (y >= fb) { fb = f64u_add(fb, f64u_mul(af, f64u_sub(y, fb))); }
  else { fb = f64u_sub(fb, f64u_mul(af, f64u_sub(fb, y))); }
  h->ema_fast_biased = fb;
  if (fe != 0ULL) {
    u64 nfe = f64u_mul(fe, bf);
    h->ema_fast_exp = (nfe == fe) ? 0ULL : nfe;
  }
  u64 as = 0x3EE4F8B588E368F1ULL;
  u64 bs = 0x3FEFFFEB074A771DULL;
  if (y >= sb) { sb = f64u_add(sb, f64u_mul(as, f64u_sub(y, sb))); }
  else { sb = f64u_sub(sb, f64u_mul(as, f64u_sub(sb, y))); }
  h->ema_slow_biased = sb;
  if (se != 0ULL) {
    u64 nse = f64u_mul(se, bs);
    h->ema_slow_exp = (nse == se) ? 0ULL : nse;
  }
}

u64 full_scale_delta(FullHdr *h, u64 delta) {
  if (delta == 0ULL) { return 0ULL; }
  u64 ir = h->num_irred;
  u64 bn = h->num_binary;
  u64 clauses = (ir > 0xFFFFFFFFFFFFFFFFULL - bn) ? 0xFFFFFFFFFFFFFFFFULL : (ir + bn);
  u64 arg = (clauses > 0xFFFFFFFFFFFFFFF5ULL) ? 0xFFFFFFFFFFFFFFFFULL : (clauses + 10ULL);
  u64 l = f64u_log10_u64(arg);
  if (l < 0x3FF0000000000000ULL) { l = 0x3FF0000000000000ULL; }
  u64 five = 0x4014000000000000ULL;
  u64 f_abs = (l >= five) ? f64u_sub(l, five) : f64u_sub(five, l);
  u64 ff = f64u_mul(f_abs, f_abs);
  u64 fff = f64u_add(f64u_mul(0x4012000000000000ULL, ff), 0x4039000000000000ULL);
  return f64u_to_u64(f64u_mul(fff, f64u_from_u64(delta)));
}

void full_zero_tables2(FullHdr *h) {
  u64 mx = h->max_vars;
  u8 *mrk = (u8 *)h->mark;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  u64 *sc = (u64 *)h->score;
  u64 *sig = (u64 *)h->sim_sig;
  u64 v = 0ULL;
  while (v < mx) {
    mrk[v] = (u8)0; ph[v] = (i8)0; ptgt[v] = (i8)0; pbst[v] = (i8)0; wbst[v] = (i8)1;
    lvl[v] = 0u; rsns[v] = 0xFFFFFFFFu;
    ftrl[v] = 0u; fdec[v] = 0xFFFFFFFFu; sc[v] = 0ULL; sig[v] = 0ULL;
    fl[v] = 0u; hp[v] = 0u; ps[v] = 0xFFFFFFFFu;
    qp[v] = 0xFFFFFFFFu; qn[v] = 0xFFFFFFFFu; qs[v] = 0u;
    v = v + 1ULL;
  }
  ftrl[mx] = 0u; fdec[mx] = 0xFFFFFFFFu;
}

void m6_hdr_dr_init(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) != 0ULL) { return; }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_PREV] = 0ULL;
  e[M6W_DR_PREV + 1ULL] = 0ULL;
  e[M6W_DR_SB] = 0ULL;
  e[M6W_DR_SB + 1ULL] = 0ULL;
  e[M6W_DR_SE] = 0x3FF0000000000000ULL;
  e[M6W_DR_SE + 1ULL] = 0x3FF0000000000000ULL;
}

void m6_hdr_dr_update(FullHdr *h) {
  m6_hdr_dr_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 cur = st & mask56;
  u64 last_sw = (st >> 56) & 127ULL;
  u64 cur_sw = h->switched & 127ULL;
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  if (cur_sw != last_sw) {
    e[M6W_DR_STATE] = (1ULL << 63) | (cur_sw << 56) | cur;
    e[M6W_DR_PREV + mode] = cur;
    e[M6W_DR_SB + mode] = 0ULL;
    e[M6W_DR_SE + mode] = 0x3FF0000000000000ULL;
    return;
  }
  u64 prev = e[M6W_DR_PREV + mode];
  e[M6W_DR_PREV + mode] = cur;
  u64 d = (cur >= prev) ? (cur - prev) : 0ULL;
  u64 y = f64u_from_u64(d);
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  u64 alpha = 0x3EE4F8B588E368F1ULL;
  u64 beta  = 0x3FEFFFEB074A771DULL;
  if (y >= sb) {
    sb = f64u_add(sb, f64u_mul(alpha, f64u_sub(y, sb)));
  } else {
    sb = f64u_sub(sb, f64u_mul(alpha, f64u_sub(sb, y)));
  }
  if (se != 0ULL) {
    u64 nse = f64u_mul(se, beta);
    se = (nse == se) ? 0ULL : nse;
  }
  e[M6W_DR_SB + mode] = sb;
  e[M6W_DR_SE + mode] = se;
}

bool m6_hdr_dr_allow(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) == 0ULL) { return true; }
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  u64 val = sb;
  if (se != 0ULL) {
    u64 div = f64u_sub(0x3FF0000000000000ULL, se);
    if (div == 0ULL) { return true; }
    val = f64u_div(sb, div);
  }
  return val < 0x4024000000000000ULL;
}

void full_m7_state_init(FullHdr *h) {
  if (full_m7_get64(h, M7_GU_MAGIC) == M7_SEARCH_MAGIC) { return; }
  full_m7_set64(h, M7_GU_MAGIC, M7_SEARCH_MAGIC);
  u64 cm = (h->stable != 0ULL) ? 1ULL : 0ULL;
  full_m7_set64(h, M7_GU_EMA_MASK, 1ULL << cm);
  u64 init_exp = 0x3FF0000000000000ULL;
  if (cm == 0ULL) {
    full_m7_set64(h, M7_GU_EMA0_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA0_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA0_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA1_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_SE, init_exp);
  } else {
    full_m7_set64(h, M7_GU_EMA1_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA1_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA1_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA0_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_SE, init_exp);
  }
  full_m7_set64(h, M7_GU_RANDEC_REM, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + 500ULL);
  full_m7_set64(h, M7_GU_RANDEC_SEQ, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
}

u64 full_randec_var_lvl_fid(FullHdr *h, u64 max_lvl) {
  u64 cv = h->cur_vars;
  if (cv == 0ULL || h->stable != 0ULL || h->probing != 0ULL) {
    return 0xFFFFFFFFFFFFFFFFULL;
  }
  full_m7_state_init(h);
  u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
  u64 lc = full_m7_get64(h, M7_GU_RANDEC_CFL);
  if (h->conflicts > lc) {
    u64 dc = h->conflicts - lc;
    rem = (rem > dc) ? (rem - dc) : 0ULL;
    full_m7_set64(h, M7_GU_RANDEC_REM, rem);
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
  }
  if (rem == 0ULL) {
    if (h->cur_level > max_lvl) { return 0xFFFFFFFFFFFFFFFFULL; }
    u64 lim = full_m7_get64(h, M7_GU_RANDEC_LIM);
    if (h->conflicts < lim) { return 0xFFFFFFFFFFFFFFFFULL; }
    u64 cnt = full_m7_get64(h, M7_GU_RANDEC_SEQ) + 1ULL;
    full_m7_set64(h, M7_GU_RANDEC_SEQ, cnt);
    u64 qarg = (cnt > (~0ULL) - 9ULL) ? (~0ULL) : (cnt + 9ULL);
    u64 lg = f64u_log10_u64(qarg);
    u64 len = f64u_to_u64(f64u_mul(0x4024000000000000ULL, lg));
    if (len < 10ULL) { len = 10ULL; }
    u64 delta = f64u_to_u64(f64u_mul(0x407F400000000000ULL, lg));
    full_m7_set64(h, M7_GU_RANDEC_REM, len);
    full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + delta);
    rem = len;
  }
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u64 max_tries = (cv < 4096ULL) ? (cv * 4ULL + 16ULL) : 16384ULL;
  u64 tries = 0ULL;
  while (tries < max_tries) {
    u64 idx = full_lcg_next_m7(h) % cv;
    if ((fl[idx] & FL_ACTIVE) != 0u && vals[idx << 1] == (i8)0) {
      return idx;
    }
    tries = tries + 1ULL;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

u64 full_randec_var_m7(FullHdr *h) {
  return full_randec_var_lvl_fid(h, 0ULL);
}

void full_rephase(FullHdr *h) {
  if (h->stable == 0ULL) {
    h->rephase_limit = h->mode_confl_lim;
    return;
  }
  if (h->cur_level > 0ULL) {
    full_backtrack(h, 0ULL);
  }
  h->rephased = h->rephased + 1ULL;
  u64 step = (h->rephased - 1ULL) % 6ULL;
  i8 *ph = (i8 *)h->phases;
  i8 *pb = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  if (step == 0ULL || step == 3ULL) {
    u64 v = 0ULL;
    while (v < cv) {
      if (pb[v] != (i8)0) {
        ph[v] = pb[v];
      }
      v = v + 1ULL;
    }
    h->best_assigned = 0ULL;
  } else if (step == 1ULL || step == 4ULL) {
    full_walk(h);
  } else if (step == 2ULL) {
    u64 v = 0ULL;
    while (v < cv) {
      ph[v] = (i8)255;
      v = v + 1ULL;
    }
  } else {
    u64 v = 0ULL;
    while (v < cv) {
      ph[v] = (i8)1;
      v = v + 1ULL;
    }
  }
  i8 *pt = (i8 *)h->phases_target;
  u64 k = 0ULL;
  while (k < cv) {
    pt[k] = ph[k];
    k = k + 1ULL;
  }
  h->target_assigned = 0ULL;
  u64 cnt = h->rephased;
  u64 scaled = 1000ULL * f64u_to_u64(f64u_nlogpown(cnt, 3ULL));
  h->rephase_limit = h->conflicts + scaled;
}

u64 full_restart_due(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  if (h->conflicts < h->restart_limit) { return 0ULL; }
  if (h->stable != 0ULL) {
    if (h->rel_trigger != 0ULL) { h->rel_trigger = 0ULL; return 1ULL; }
    return 0ULL;
  }
  u64 fe = h->ema_fast_exp;
  u64 se = h->ema_slow_exp;
  u64 fb = h->ema_fast_biased;
  u64 sb = h->ema_slow_biased;
  u64 margin = 0x3FF199999999999AULL;
  bool fire = false;
  if (fe == 0ULL && se == 0ULL) {
    fire = (f64u_mul(margin, sb) <= fb);
  } else {
    u64 one = 0x3FF0000000000000ULL;
    u64 fdiv = (fe == 0ULL) ? one : f64u_sub(one, fe);
    u64 sdiv = (se == 0ULL) ? one : f64u_sub(one, se);
    if (fdiv == 0ULL || sdiv == 0ULL) { return 0ULL; }
    u64 lhs = f64u_mul(f64u_mul(margin, sb), fdiv);
    u64 rhs = f64u_mul(fb, sdiv);
    fire = (lhs <= rhs);
  }
  if (fire) {
    u64 rst = (h->restarts < 1000000000000ULL) ? (h->restarts + 1ULL) : 1000000000000ULL;
    u64 lg = f64u_log10_u64(rst + 9ULL);
    u64 delta = f64u_to_u64(lg);
    if (delta < 1ULL) { delta = 1ULL; }
    h->restart_limit = h->conflicts + delta;
    return 1ULL;
  }
  return 0ULL;
}

void full_restart(FullHdr *h) {
  h->restarts = h->restarts + 1ULL;
  u64 nv = full_randec_var_lvl_fid(h, 1ULL);
  if (nv == 0xFFFFFFFFFFFFFFFFULL) { nv = full_next_dec_var(h); }
  u64 reuse = 0ULL;
  if (nv < h->cur_vars && h->cur_level > 0ULL) {
    u32 *fdec = (u32 *)h->frame_dec;
    if (h->stable != 0ULL) {
      u64 *sc = (u64 *)h->score; u64 lim = sc[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || sc[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    } else {
      u32 *qs = (u32 *)h->q_stamp; u32 lim = qs[nv];
      while (reuse < h->cur_level) {
        u32 dv = fdec[reuse + 1ULL] >> 1;
        if ((u64)dv >= h->cur_vars || qs[dv] <= lim) { break; }
        reuse = reuse + 1ULL;
      }
    }
  }
  full_backtrack(h, reuse);
}

void full_init_fresh_var(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u32 *wvec = (u32 *)h->watch_vec; u64 *sc = (u64 *)h->score;
  wvec[(u64)fv << 2] = 0u; wvec[((u64)fv << 2) + 1ULL] = 0u;
  wvec[((u64)fv << 2) + 2ULL] = 0u; wvec[((u64)fv << 2) + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)0;
  ptgt[fv] = (i8)0; pbst[fv] = (i8)0; wbst[fv] = (i8)1;
  lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu; ps[fv] = 0xFFFFFFFFu; sc[fv] = 0ULL;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP |
           FL_FACT_P | FL_FACT_N | FL_BONE0 | FL_BONE1 | FL_TRANS;
  u32 old_first = (u32)h->q_first;
  qp[fv] = 0xFFFFFFFFu;
  if ((u64)old_first < h->cur_vars) { qn[fv] = old_first; qp[old_first] = fv; }
  else { qn[fv] = 0xFFFFFFFFu; h->q_last = (u64)fv; }
  h->q_first = (u64)fv; qs[fv] = 0u;
  if (h->stable != 0ULL) { full_heap_push(h, fv); }
  h->unassigned = h->unassigned + 1ULL;
}

void full_compact_mark_live(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *map = (u32 *)h->work_stk1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 v = 0ULL;
  while (v < cv) {
    map[v] = ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) ? 1u : 0u;
    v = v + 1ULL;
  }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    u32 lneg = ((u32)l) ^ 1u;
    u64 p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && ot != lneg &&
            vals[l] == (i8)0 && vals[ot] == (i8)0 &&
            (fl[l >> 1] & FL_ACTIVE) != 0u &&
            (fl[ot >> 1] & FL_ACTIVE) != 0u) {
          map[l >> 1] = 1u;
          map[ot >> 1] = 1u;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    l = l + 1ULL;
  }
  u64 alen = h->arena_len;
  u64 pos = 0ULL;
  while (pos < alen) {
    if (pos + 3ULL > alen) { break; }
    u32 hdr = ar[pos];
    u32 csz = ar[pos + 2ULL];
    u64 npos = (u64)full_arena_next(h, (u32)pos);
    if ((hdr & PH_GARB) == 0u && csz >= 3u && pos + 3ULL + (u64)csz <= alen) {
      bool sat = false;
      bool has_dead = false;
      u32 ucnt = 0u;
      u32 i = 0u;
      while (i < csz) {
        u32 lit = ar[pos + 3ULL + (u64)i];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) {
            if ((fl[lit >> 1] & FL_ACTIVE) == 0u) {
              has_dead = true;
            } else {
              ucnt = ucnt + 1u;
            }
          }
        }
        i = i + 1u;
      }
      if (!sat && !((hdr & PH_RED) != 0u && has_dead) && ucnt >= 1u) {
        i = 0u;
        while (i < csz) {
          u32 lit = ar[pos + 3ULL + (u64)i];
          if ((u64)lit < nlits && vals[lit] == (i8)0 &&
              (fl[lit >> 1] & FL_ACTIVE) != 0u) {
            map[lit >> 1] = 1u;
          }
          i = i + 1u;
        }
      }
    }
    pos = npos;
  }
}

void full_compact_vars(FullHdr *h, u64 old_cv, u64 ncv) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *ps = (u32 *)h->pos;
  u32 *inv = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  u64 nlits = old_cv << 1;
  while (l < nlits) { vals[l] = (i8)0; l = l + 1ULL; }
  u64 tgt_asg = 0ULL;
  u64 bst_asg = 0ULL;
  u64 nv = 0ULL;
  while (nv < ncv) {
    u32 ov = inv[nv];
    fl[nv] = fl[ov];
    ph[nv] = ph[ov];
    i8 tv = ptgt[ov];
    i8 bv = pbst[ov];
    ptgt[nv] = tv;
    pbst[nv] = bv;
    if (tv != (i8)0) { tgt_asg = tgt_asg + 1ULL; }
    if (bv != (i8)0) { bst_asg = bst_asg + 1ULL; }
    wbst[nv] = wbst[ov];
    sc[nv] = sc[ov];
    qs[nv] = qs[ov];
    lvl[nv] = 0u;
    rsns[nv] = 0xFFFFFFFFu;
    nv = nv + 1ULL;
  }
  u64 v = ncv;
  while (v < old_cv) {
    fl[v] = 0u;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    sc[v] = 0ULL;
    ph[v] = (i8)0;
    ptgt[v] = (i8)0;
    pbst[v] = (i8)0;
    wbst[v] = (i8)1;
    qs[v] = 0u;
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    ps[v] = 0xFFFFFFFFu;
    v = v + 1ULL;
  }
  ftrl[0] = 0u;
  fdec[0] = 0xFFFFFFFFu;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  h->target_assigned = tgt_asg;
  h->best_assigned = bst_asg;
  h->cur_vars = ncv;
  h->unassigned = ncv;
  if (ncv < h->d.mv) { h->d.mv = ncv; h->bva_cap = h->max_vars - ncv; }
}

void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m) {
  u64 om = (old_m != 0ULL) ? 1ULL : 0ULL;
  u64 nm = (new_m != 0ULL) ? 1ULL : 0ULL;
  h->stable = om;
  full_m7_state_init(h);
  h->stable = nm;
  u64 old_base = (om == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  full_m7_set64(h, old_base, h->ema_fast_biased);
  full_m7_set64(h, old_base + 2ULL, h->ema_fast_exp);
  full_m7_set64(h, old_base + 4ULL, h->ema_slow_biased);
  full_m7_set64(h, old_base + 6ULL, h->ema_slow_exp);
  u64 mask = full_m7_get64(h, M7_GU_EMA_MASK) | (1ULL << om);
  u64 new_base = (nm == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  u64 bit = 1ULL << nm;
  if ((mask & bit) != 0ULL) {
    h->ema_fast_biased = full_m7_get64(h, new_base);
    h->ema_fast_exp = full_m7_get64(h, new_base + 2ULL);
    h->ema_slow_biased = full_m7_get64(h, new_base + 4ULL);
    h->ema_slow_exp = full_m7_get64(h, new_base + 6ULL);
  } else {
    u64 init_exp = 0x3FF0000000000000ULL;
    h->ema_fast_biased = 0ULL;
    h->ema_fast_exp = init_exp;
    h->ema_slow_biased = 0ULL;
    h->ema_slow_exp = init_exp;
    full_m7_set64(h, new_base, 0ULL);
    full_m7_set64(h, new_base + 2ULL, init_exp);
    full_m7_set64(h, new_base + 4ULL, 0ULL);
    full_m7_set64(h, new_base + 6ULL, init_exp);
    mask = mask | bit;
  }
  full_m7_set64(h, M7_GU_EMA_MASK, mask);
}

void full_switch_mode_m7(FullHdr *h) {
  u64 old_m = 0ULL;
  u64 new_m = 1ULL;
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    old_m = 0ULL;
    new_m = 1ULL;
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 v = 0ULL;
    u64 wm4__ = m6_wm4_get(h);
    if ((wm4__ & 1ULL) == 0ULL) {
      while (v < cv) { ps[v] = 0xFFFFFFFFu; v = v + 1ULL; }
      h->heap_len = 0ULL;
      m6_wm4_set(h, wm4__ | 1ULL);
    } else {
      v = 0ULL;
      while (v < cv) {
        if ((fl[v] & FL_ACTIVE) == 0u) {
          u64 n__ = h->heap_len; u32 p__ = ps[v];
          if (n__ > 0ULL && n__ <= cv && (u64)p__ < n__ && hp[p__] == (u32)v) {
            u32 last__ = hp[n__ - 1ULL];
            h->heap_len = n__ - 1ULL;
            if ((u64)last__ < cv) { ps[last__] = 0xFFFFFFFFu; }
            if (last__ != (u32)v) {
              ps[v] = 0xFFFFFFFFu;
              if ((u64)last__ < cv) {
                hp[p__] = last__; ps[last__] = p__;
                full_heap_up(h, last__); full_heap_down(h, last__);
              }
            }
          } else { ps[v] = 0xFFFFFFFFu; }
        }
        v = v + 1ULL;
      }
    }
    v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u) { full_heap_push(h, (u32)v); }
      v = v + 1ULL;
    }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 scaled = 1000ULL * f64u_to_u64(f64u_nlogpown(cnt, 4ULL));
    h->mode_confl_lim = h->conflicts + scaled;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  full_ema_swap_m7(h, old_m, new_m);
  {
    m6_hdr_dr_init(h);
    u64 *e__ = (u64 *)((u64)h - 2304ULL);
    u64 mask56__ = (1ULL << 56) - 1ULL;
    u64 decs__ = e__[1] & mask56__;
    e__[1] = (1ULL << 63) | ((h->switched & 127ULL) << 56) | decs__;
    e__[2ULL + ((h->stable != 0ULL) ? 1ULL : 0ULL)] = decs__;
  }
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 0ULL) ? d10 : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
    u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
    u64 lc = full_m7_get64(h, M7_GU_RANDEC_CFL);
    if (h->conflicts > lc) {
      u64 dc = h->conflicts - lc;
      rem = (rem > dc) ? (rem - dc) : 0ULL;
      full_m7_set64(h, M7_GU_RANDEC_REM, rem);
    }
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
    if (rem == 0ULL) {
      u64 rseq = full_m7_get64(h, M7_GU_RANDEC_SEQ) + 1ULL;
      full_m7_set64(h, M7_GU_RANDEC_SEQ, rseq);
      u64 qarg = (rseq > (~0ULL) - 9ULL) ? (~0ULL) : (rseq + 9ULL);
      u64 lg = f64u_log10_u64(qarg);
      u64 rlen = f64u_to_u64(f64u_mul(0x4024000000000000ULL, lg));
      if (rlen < 10ULL) { rlen = 10ULL; }
      u64 rdelta = f64u_to_u64(f64u_mul(0x407F400000000000ULL, lg));
      full_m7_set64(h, M7_GU_RANDEC_REM, rlen);
      full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + rdelta);
    }
  }
}

u64 full_search_m6(FullHdr *h) {
  u64 reorder_limit = 10000ULL;
  u64 reordered = 0ULL;
  u64 last_reduce_cfl = 0xFFFFFFFFFFFFFFFFULL;
  u64 lkr = full_lucky_late_m7(h);
  if (lkr == 10ULL || lkr == 20ULL) { return lkr; }
  h->search_ticks = 0ULL; h->mode_saved_ticks = 0ULL;
  full_update_classify_fid(h);
  m6_hdr_set_watermark(h, M6_WM_PROBE_TICKS, 0ULL); h->fwd_str_cnt = 0ULL;
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze_m6_hdr(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
    } else if (h->unassigned == 0ULL) {
      return 10ULL;
    } else if (h->fuel == 0ULL) {
      return 0ULL;
    } else if (h->num_redundant > 0ULL && h->conflicts >= h->reduce_limit) {
      last_reduce_cfl = h->conflicts;
      h->fuel = h->fuel - 1ULL;
      u64 rr = full_reduce_m6(h, false);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
    } else if ((h->stable == 0ULL) ? (h->conflicts >= h->mode_confl_lim)
                                   : (h->search_ticks >= h->mode_tick_lim)) {
      h->fuel = h->fuel - 1ULL;
      full_switch_mode_m7(h);
    } else if (full_restart_due(h) != 0ULL) {
      h->fuel = h->fuel - 1ULL;
      full_restart(h);
    } else if (h->cur_level == 0ULL && h->conflicts >= reorder_limit) {
      reordered = reordered + 1ULL;
      reorder_limit = h->conflicts + 10000ULL * reordered;
      h->fuel = h->fuel - 1ULL;
      full_reorder_m6(h, 256ULL);
    } else if (h->stable != 0ULL && h->conflicts > h->rephase_limit) {
      h->fuel = h->fuel - 1ULL;
      full_rephase(h);
    } else if (h->conflicts != last_reduce_cfl && h->conflicts > h->probe_limit) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, true, false);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else if (h->conflicts != last_reduce_cfl && h->conflicts >= h->elim_limit &&
               (h->num_irred + h->num_binary) > 0ULL) {
      h->fuel = h->fuel - 1ULL;
      u64 sr = full_simplify_m6(h, false, true);
      if (sr == 20ULL) { return 20ULL; }
      if (sr != 1ULL) { return 0ULL; }
    } else {
      if (m6_hdr_decide_fid(h) == 0ULL) {
        return (h->unassigned == 0ULL) ? 10ULL : 0ULL;
      }
    }
  }
}

u64 kissat_solve_bytes_seeded(u64 cnf_ptr, u64 cnf_len, u64 work_ptr,
                              u64 work_cap, u64 fuel, u64 seed) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + M6_HDR_TOTAL_BYTES) { return 0ULL; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  u64 hdr_addr = full_m6_mem_init(cnf_ptr, cnf_end, work_base, avail, fuel);
  if (hdr_addr == 0ULL) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 orig_mv = h->d.mv;
  u64 pp = full_preprocess_m6(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = 0ULL;
  if (pp == 10ULL) {
    r = 10ULL;
  } else if (pp != 0ULL) {
    h->rng_state = seed & 0xFFFFFFFFULL;
    r = full_search_m6(h);
  }
  if (r == 10ULL) {
    full_extend(h);
    h->d.mv = orig_mv;
    h->bva_cap = h->max_vars - orig_mv;
    u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, orig_mv);
    return (ok == 1ULL) ? 10ULL : 0ULL;
  }
  return r;
}

u64 kissat_solve_bytes_m6(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  return kissat_solve_bytes_seeded(cnf_ptr, cnf_len, work_ptr, work_cap, fuel, 0ULL);
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  return kissat_solve_bytes_seeded(cnf_ptr, cnf_len, work_ptr, work_cap, fuel, 0ULL);
}
"

/-! ## 1. Drop-In `Fn` Handles, Replacement List (`20` fns) & Insertion List (`2` fns) -/

def fidStep13S3ScaleDeltaM5Fn : Fn :=
  ⟨"full_scale_delta_m5", [i64, i64], [i64], full_scale_delta_m5_body⟩

def fidStep13S3EmaUpdateFn : Fn :=
  ⟨"full_ema_update", [i64, i64], [], full_ema_update_body⟩

def fidStep13S3ScaleDeltaFn : Fn :=
  ⟨"full_scale_delta", [i64, i64], [i64], full_scale_delta_body⟩

def fidStep13S3ZeroTables2Fn : Fn :=
  ⟨"full_zero_tables2", [i64], [], full_zero_tables2_body⟩

def fidStep13S3DrInitFn : Fn :=
  ⟨"m6_hdr_dr_init", [i64], [], m6_hdr_dr_init_body⟩

def fidStep13S3DrUpdateFn : Fn :=
  ⟨"m6_hdr_dr_update", [i64], [], m6_hdr_dr_update_body⟩

def fidStep13S3DrAllowFn : Fn :=
  ⟨"m6_hdr_dr_allow", [i64], [.bool], m6_hdr_dr_allow_body⟩

def fidStep13S3RephaseFn : Fn :=
  ⟨"full_rephase", [i64], [], full_rephase_body⟩

def fidStep13S3RestartDueFn : Fn :=
  ⟨"full_restart_due", [i64], [i64], full_restart_due_body⟩

def fidStep13S3RestartFn : Fn :=
  ⟨"full_restart", [i64], [], full_restart_body⟩

def fidStep13S3InitFreshVarFn : Fn :=
  ⟨"full_init_fresh_var", [i64, i32], [], full_init_fresh_var_body⟩

def fidStep13S3CompactMarkLiveFn : Fn :=
  ⟨"full_compact_mark_live", [i64], [], full_compact_mark_live_body⟩

def fidStep13S3CompactVarsFn : Fn :=
  ⟨"full_compact_vars", [i64, i64, i64], [], full_compact_vars_body⟩

def fidStep13S3M7StateInitFn : Fn :=
  ⟨"full_m7_state_init", [i64], [], full_m7_state_init_body⟩

def fidStep13S3RandecVarLvlFn : Fn :=
  ⟨"full_randec_var_lvl_fid", [i64, i64], [i64], full_randec_var_lvl_fid_body⟩

def fidStep13S3RandecVarM7Fn : Fn :=
  ⟨"full_randec_var_m7", [i64], [i64], full_randec_var_m7_body⟩

def fidStep13S3EmaSwapM7Fn : Fn :=
  ⟨"full_ema_swap_m7", [i64, i64, i64], [], full_ema_swap_m7_body⟩

def fidStep13S3SwitchModeM7Fn : Fn :=
  ⟨"full_switch_mode_m7", [i64], [], full_switch_mode_m7_body⟩

def fidStep13S3SearchM6Fn : Fn :=
  ⟨"full_search_m6", [i64], [i64], full_search_m6_body⟩

def fidStep13S3SolveBytesSeededFn : Fn :=
  ⟨"kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64],
    kissat_solve_bytes_seeded_body⟩

def fidStep13S3SolveBytesM6Fn : Fn :=
  ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_m6_body⟩

def fidStep13S3SolveBytesFn : Fn :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissat_solve_bytes_body⟩

/-- Ordered list of all `20` Step-13 S3-B sig-preserving replacement functions. -/
def fidStep13S3SearchRepls : List Fn :=
  [ fidStep13S3ScaleDeltaM5Fn
  , fidStep13S3EmaUpdateFn
  , fidStep13S3ScaleDeltaFn
  , fidStep13S3ZeroTables2Fn
  , fidStep13S3DrInitFn
  , fidStep13S3DrUpdateFn
  , fidStep13S3DrAllowFn
  , fidStep13S3RephaseFn
  , fidStep13S3RestartDueFn
  , fidStep13S3RestartFn
  , fidStep13S3InitFreshVarFn
  , fidStep13S3CompactMarkLiveFn
  , fidStep13S3CompactVarsFn
  , fidStep13S3M7StateInitFn
  , fidStep13S3RandecVarM7Fn
  , fidStep13S3EmaSwapM7Fn
  , fidStep13S3SwitchModeM7Fn
  , fidStep13S3SearchM6Fn
  , fidStep13S3SolveBytesM6Fn
  , fidStep13S3SolveBytesFn ]

/-- Ordered helper insertions (`+2` added functions: `full_randec_var_lvl_fid` anchored before
`full_randec_var_m7` and `kissat_solve_bytes_seeded` anchored before `kissat_solve_bytes_m6`). -/
def fidStep13S3SearchBefores : List (Sym × List Fn) :=
  [ ("full_randec_var_m7", [fidStep13S3RandecVarLvlFn])
  , ("kissat_solve_bytes_m6", [fidStep13S3SolveBytesSeededFn]) ]

end

/-! ## 2. Function Well-Formedness (`Func.Wf`) -/

public section

theorem fidStep13S3ScaleDeltaM5_wf : Func.Wf fidStep13S3ScaleDeltaM5Fn.body := by t_wf_reify
theorem fidStep13S3EmaUpdate_wf : Func.Wf fidStep13S3EmaUpdateFn.body := by t_wf_reify
theorem fidStep13S3ScaleDelta_wf : Func.Wf fidStep13S3ScaleDeltaFn.body := by t_wf_reify
theorem fidStep13S3ZeroTables2_wf : Func.Wf fidStep13S3ZeroTables2Fn.body := by t_wf_reify
theorem fidStep13S3DrInit_wf : Func.Wf fidStep13S3DrInitFn.body := by t_wf_reify
theorem fidStep13S3DrUpdate_wf : Func.Wf fidStep13S3DrUpdateFn.body := by t_wf_reify
theorem fidStep13S3DrAllow_wf : Func.Wf fidStep13S3DrAllowFn.body := by t_wf_reify
theorem fidStep13S3Rephase_wf : Func.Wf fidStep13S3RephaseFn.body := by t_wf_reify
theorem fidStep13S3RestartDue_wf : Func.Wf fidStep13S3RestartDueFn.body := by t_wf_reify
theorem fidStep13S3Restart_wf : Func.Wf fidStep13S3RestartFn.body := by t_wf_reify
theorem fidStep13S3InitFreshVar_wf : Func.Wf fidStep13S3InitFreshVarFn.body := by t_wf_reify
theorem fidStep13S3CompactMarkLive_wf : Func.Wf fidStep13S3CompactMarkLiveFn.body := by t_wf_reify
theorem fidStep13S3CompactVars_wf : Func.Wf fidStep13S3CompactVarsFn.body := by t_wf_reify
theorem fidStep13S3M7StateInit_wf : Func.Wf fidStep13S3M7StateInitFn.body := by t_wf_reify
theorem fidStep13S3RandecVarLvl_wf : Func.Wf fidStep13S3RandecVarLvlFn.body := by t_wf_reify
theorem fidStep13S3RandecVarM7_wf : Func.Wf fidStep13S3RandecVarM7Fn.body := by t_wf_reify
theorem fidStep13S3EmaSwapM7_wf : Func.Wf fidStep13S3EmaSwapM7Fn.body := by t_wf_reify
theorem fidStep13S3SwitchModeM7_wf : Func.Wf fidStep13S3SwitchModeM7Fn.body := by t_wf_reify
theorem fidStep13S3SearchM6_wf : Func.Wf fidStep13S3SearchM6Fn.body := by t_wf_reify
theorem fidStep13S3SolveBytesSeeded_wf : Func.Wf fidStep13S3SolveBytesSeededFn.body := by t_wf_reify
theorem fidStep13S3SolveBytesM6_wf : Func.Wf fidStep13S3SolveBytesM6Fn.body := by t_wf_reify
theorem fidStep13S3SolveBytes_wf : Func.Wf fidStep13S3SolveBytesFn.body := by t_wf_reify

theorem fidStep13S3SearchRepls_wf : ∀ f ∈ fidStep13S3SearchRepls, f.Wf := by
  intro f hf
  simp only [fidStep13S3SearchRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fidStep13S3ScaleDeltaM5_wf
  · exact fidStep13S3EmaUpdate_wf
  · exact fidStep13S3ScaleDelta_wf
  · exact fidStep13S3ZeroTables2_wf
  · exact fidStep13S3DrInit_wf
  · exact fidStep13S3DrUpdate_wf
  · exact fidStep13S3DrAllow_wf
  · exact fidStep13S3Rephase_wf
  · exact fidStep13S3RestartDue_wf
  · exact fidStep13S3Restart_wf
  · exact fidStep13S3InitFreshVar_wf
  · exact fidStep13S3CompactMarkLive_wf
  · exact fidStep13S3CompactVars_wf
  · exact fidStep13S3M7StateInit_wf
  · exact fidStep13S3RandecVarM7_wf
  · exact fidStep13S3EmaSwapM7_wf
  · exact fidStep13S3SwitchModeM7_wf
  · exact fidStep13S3SearchM6_wf
  · exact fidStep13S3SolveBytesM6_wf
  · exact fidStep13S3SolveBytes_wf

theorem fidStep13S3SearchBefores_wf :
    ∀ h ∈ fidStep13S3SearchBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep13S3SearchBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact fidStep13S3RandecVarLvl_wf
  · exact fidStep13S3SolveBytesSeeded_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
