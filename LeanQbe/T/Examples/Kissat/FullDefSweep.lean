module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` Semantic Gate Mining + `kitten`-Backed Cone Sweeping & Dense Congruence

Ports from `prototype/kissat-fast-c0` (`Fast.lean` + `Fast4.lean`) onto the byte-identical
`144`-word (`FullHdr`) arena layout (`Full1.lean`, omitting dead `h->def_cnt` updates):
1. Semantic gate mining (`definition.c`):
   - `full_bve_mark_and` (duplicate-literal guard via `lm[ot] == 2` + `nmask` bitmask)
   - `full_find_definition` (`kitten`-backed semantic gate core extraction + unit/trivial side)
   - `full_bve_gates` (`P_ng × N_ng` bitmask check via `scr[128..131]` + `full_find_definition`)
2. Ticks-bounded dense gate congruence (`congruence.c`):
   - `full_cong_extract`
   - `full_congruence_dense`
3. `kitten`-backed dense cone SAT sweeping (`sweep.c`):
   - `full_sweep_cone` (`K_MAX_V = 128`, `K_MAX_ORIG = 512`, zero-based `tarjan_mark`)
   - `full_sweep_refine_kitten`
   - `full_sweep_var`
   - `full_sweep_dense`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! full_def_sweep "
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

#define FL_ACTIVE  1u
#define FL_SWEEP   1024u

#define K_BASE 256u
#define K_MAX_V 128u
#define K_MAX_ORIG 512u

#define KH_NV 0u
#define KH_UNASS 6u
#define KH_NASSUMP 18u

#define KO_VALS 928u
#define KO_ASSUMP 1184u
#define KO_CL_META 6816u
#define KO_CL_AUX 7712u
#define KM_CORE 0x10000u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap);
extern bool full_cong_hash_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_kitten_init(FullHdr *h, u32 nv, u32 track_ante);
extern bool full_kitten_add_clause(FullHdr *h, u32 id, u32 *lits, u32 sz);
extern u64 full_kitten_solve(FullHdr *h, u64 tick_lim);
extern u32 full_kitten_core(FullHdr *h);
extern void full_kitten_shrink(FullHdr *h);
extern bool full_kitten_flip(FullHdr *h, u32 lit);

bool full_bve_mark_and(FullHdr *h, u32 v_lit, u32 cr, u32 n_off, u32 nn) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark; u32 sz = ar[(u64)cr + 2ULL]; u32 need = 0u; u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) { lm[l ^ 1u] = (u8)1; need = need + 1u; }
    i = i + 1u;
  }
  u32 matched = 0u; u64 nmask = 0ULL; u32 j = 0u;
  while (j < nn) {
    u32 w = scr[n_off + j];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (lm[ot] == (u8)1) {
        lm[ot] = (u8)2; nmask = nmask | (1ULL << (u64)j); matched = matched + 1u;
      } else if (lm[ot] == (u8)2) { nmask = nmask | (1ULL << (u64)j); }
    }
    j = j + 1u;
  }
  i = 0u; while (i < sz) { lm[ar[(u64)cr + 3ULL + (u64)i] ^ 1u] = (u8)0; i = i + 1u; }
  if (matched >= need) { scr[130] = (u32)nmask; scr[131] = (u32)(nmask >> 32); return true; }
  return false;
}

void full_find_definition(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 10240ULL || np == 0u || nn == 0u || np + nn < 3u) { return; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *exp = (u32 *)h->wsort; u32 *tmp = (u32 *)h->tmp_lits;
  full_kitten_init(h, 128u, 1u);
  u32 nv = 0u; u32 pl = v << 1; u32 nl = pl | 1u; bool abort_def = false;
  u32 trivial_side = 0xFFFFFFFFu; u32 side = 0u;
  while (side < 2u && !abort_def && trivial_side == 0xFFFFFFFFu) {
    u32 cnt = (side == 0u) ? np : nn; u32 off_s = (side == 0u) ? 0u : 64u;
    u32 except = (side == 0u) ? pl : nl; u32 idx = 0u;
    while (idx < cnt && !abort_def) {
      u32 w = scr[off_s + idx]; u32 eid = off_s + idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK; u32 lv = l >> 1;
        if (vals[l] == (i8)0) {
          if (tmk[lv] == 0u) {
            if (nv >= 128u) { abort_def = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
          tmp[0] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          if (!full_kitten_add_clause(h, eid, tmp, 1u)) { abort_def = true; break; }
        } else if (vals[l] < (i8)0) { trivial_side = eid; break; }
      } else {
        u32 sz = ar[(u64)w + 2ULL]; bool sat = false; u32 csz = 0u; u32 k = 0u;
        while (k < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)k];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= 128u) { abort_def = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              if ((u64)csz < h->cur_vars) {
                tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u); csz = csz + 1u;
              } else { abort_def = true; break; }
            }
          }
          k = k + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_side = eid; break; }
          if (!full_kitten_add_clause(h, eid, tmp, csz)) { abort_def = true; break; }
        }
      }
      idx = idx + 1u;
    }
    side = side + 1u;
  }
  u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_side != 0xFFFFFFFFu) {
    u64 pm = (trivial_side < 64u) ? (1ULL << (u64)trivial_side) : 0ULL;
    u64 nm = (trivial_side >= 64u) ? (1ULL << (u64)(trivial_side - 64u)) : 0ULL;
    scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32);
    scr[130] = (u32)nm; scr[131] = (u32)(nm >> 32);
    return;
  }
  if (abort_def || nv == 0u) { return; }
  u32 *k = scr + 256; k[0] = nv; k[6] = nv; k[18] = 0u;
  u64 st = full_kitten_solve(h, 8192ULL);
  if (st != 20ULL) { return; }
  u32 red = full_kitten_core(h);
  if (red == 0u) { return; }
  full_kitten_shrink(h);
  if (full_kitten_solve(h, 16384ULL) == 20ULL) { red = full_kitten_core(h); }
  u64 pmask = 0ULL; u64 nmask = 0ULL; u32 onc = k[2]; ci = 0u;
  while (ci < onc) {
    if ((k[KO_CL_META + ci] & KM_CORE) != 0u) {
      u32 eid = k[KO_CL_AUX + ci];
      if (eid < 64u) { pmask = pmask | (1ULL << (u64)eid); }
      else if (eid < 128u) { nmask = nmask | (1ULL << (u64)(eid - 64u)); }
    }
    ci = ci + 1u;
  }
  if (pmask != 0ULL || nmask != 0ULL) {
    scr[128] = (u32)pmask; scr[129] = (u32)(pmask >> 32);
    scr[130] = (u32)nmask; scr[131] = (u32)(nmask >> 32);
  }
}

void full_bve_gates(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  scr[128] = 0u; scr[129] = 0u; scr[130] = 0u; scr[131] = 0u;
  u32 pl = v << 1; u32 i = 0u;
  while (i < np) {
    u32 wp = scr[i];
    if ((wp & PW_BIN_FLAG) != 0u) {
      u32 ot = wp & PW_LIT_MASK; u32 j = 0u;
      while (j < nn) {
        u32 wn = scr[64u + j];
        if ((wn & PW_BIN_FLAG) != 0u && (wn & PW_LIT_MASK) == (ot ^ 1u)) {
          u64 pm = 1ULL << (u64)i; u64 nm = 1ULL << (u64)j;
          scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32);
          scr[130] = (u32)nm; scr[131] = (u32)(nm >> 32); return;
        }
        j = j + 1u;
      }
    } else if (full_bve_mark_and(h, pl, wp, 64u, nn)) {
      u64 pm = 1ULL << (u64)i; scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32); return;
    }
    i = i + 1u;
  }
  u32 j = 0u;
  while (j < nn) {
    u32 wn = scr[64u + j];
    if ((wn & PW_BIN_FLAG) == 0u && full_bve_mark_and(h, pl ^ 1u, wn, 0u, np)) {
      u64 pm = (u64)scr[130] | ((u64)scr[131] << 32);
      u64 nm = 1ULL << (u64)j;
      scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32);
      scr[130] = (u32)nm; scr[131] = (u32)(nm >> 32); return;
    }
    j = j + 1u;
  }
  full_find_definition(h, v, np, nn);
}

u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u64 p = 0ULL; u64 g_len = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && g_len + 16ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 8u) {
      u32 i = 0u;
      while (i < sz) {
        u32 lhs = ar[p + 3ULL + (u64)i]; bool ok = true; u32 j = 0u;
        while (j < sz) {
          if (j != i && !full_has_bin(h, lhs ^ 1u, ar[p + 3ULL + (u64)j] ^ 1u)) {
            ok = false; break;
          }
          j = j + 1u;
        }
        if (ok) {
          scr[g_len] = lhs; scr[g_len + 1ULL] = sz - 1u; u32 rk = 0u; j = 0u;
          while (j < sz) {
            if (j != i) {
              scr[g_len + 2ULL + (u64)rk] = ar[p + 3ULL + (u64)j] ^ 1u; rk = rk + 1u;
            }
            j = j + 1u;
          }
          g_len = g_len + 2ULL + (u64)(sz - 1u); break;
        }
        i = i + 1u;
      }
      if (sz == 3u && g_len + 14ULL <= g_cap) {
        g_len = full_cong_try_xor_ite(h, ar[p + 3ULL], ar[p + 4ULL], ar[p + 5ULL],
          g_len, g_cap);
        ticks = ticks + 4ULL;
      }
    }
    p = np;
  }
  return g_len;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  u64 ht_sz = 64ULL;
  while (ht_sz * 4ULL < h->scratch_cap && ht_sz < 4096ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 g_len = full_cong_extract(h, ht_off, tick_lim);
  if (g_len == 0ULL) { return 1ULL; }
  u32 *repr = (u32 *)h->repr; u64 nlits = h->cur_vars << 1;
  u64 i = 0ULL; while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  u64 pass = 0ULL;
  while (pass < 6ULL && h->inconsistent == 0ULL) {
    if (!full_cong_hash_step(h, g_len, ht_off, ht_sz)) { break; }
    pass = pass + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_sweep_cone(FullHdr *h, u32 root_v) {
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  full_kitten_init(h, K_MAX_V, 0u);
  u32 nv = 1u; u32 nc = 0u;
  cone_v[0] = root_v; tmk[root_v] = 1u; u32 qi = 0u;
  while (qi < nv && nv < K_MAX_V && nc < K_MAX_ORIG) {
    u32 cv = cone_v[qi]; u32 map_c = tmk[cv] - 1u; qi = qi + 1u; u32 pol = 0u;
    while (pol < 2u && nc < K_MAX_ORIG) {
      u32 lit = (cv << 1) | pol;
      u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      u64 p = off;
      while (p < end && nc < K_MAX_ORIG) {
        u32 w0 = wstk[p]; p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK; u32 ov = ot >> 1;
          if (vals[ot] == (i8)0 && (tmk[ov] != 0u || nv < K_MAX_V)) {
            if (tmk[ov] == 0u) { nv = nv + 1u; tmk[ov] = nv; cone_v[nv - 1u] = ov; }
            if (lit < ot) {
              tmp[0] = (map_c << 1) | pol; tmp[1] = ((tmk[ov] - 1u) << 1) | (ot & 1u);
              if (full_kitten_add_clause(h, nc, tmp, 2u)) { nc = nc + 1u; }
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
            u32 lv = l >> 1;
            if (tmk[lv] == 0u && nv < K_MAX_V) { nv = nv + 1u; tmk[lv] = nv; cone_v[nv - 1u] = lv; }
            if (tmk[lv] == 0u) { sat = true; break; }
            tmp[cnt] = ((tmk[lv] - 1u) << 1) | (l & 1u); cnt = cnt + 1u;
          }
          idx = idx + 1u;
        }
        if (!sat && cnt >= 2u && full_kitten_add_clause(h, nc, tmp, cnt)) { nc = nc + 1u; }
      }
      pol = pol + 1u;
    }
  }
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE; k[KH_NV] = nv; k[KH_UNASS] = nv;
  return (u64)nv | ((u64)nc << 16);
}

void full_sweep_refine_kitten(FullHdr *h, u32 nv, u32 bit_idx) {
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  u64 mask = 1ULL << (u64)(bit_idx & 63u); u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (k[KO_VALS + (i << 1)] == 1u) { sig[gv] = sig[gv] | mask; }
    else { sig[gv] = sig[gv] & (~mask); }
    i = i + 1u;
  }
}

u64 full_sweep_var(FullHdr *h, u32 root_v, u64 tick_lim) {
  u64 pk = full_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u64 *sig = (u64 *)h->sim_sig; u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 1ULL;
  }
  u32 i = 0u; while (i < nv) { sig[cone_v[i]] = 0ULL; i = i + 1u; }
  k[KH_NASSUMP] = 0u;
  u64 st0 = full_kitten_solve(h, tick_lim);
  if (st0 == 20ULL) {
    i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  if (st0 != 10ULL) { i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 1ULL; }
  u32 rbit = 0u; full_sweep_refine_kitten(h, nv, rbit); rbit = 1u;
  u32 s = 1u;
  while (s < nv && rbit < 4u) {
    if (full_kitten_flip(h, s << 1) || full_kitten_flip(h, (s << 1) | 1u)) {
      full_sweep_refine_kitten(h, nv, rbit); rbit = rbit + 1u;
    }
    s = s + 1u;
  }
  u64 smask = (rbit >= 64u) ? (~0ULL) : ((1ULL << rbit) - 1ULL);
  u64 s0 = sig[root_v] & smask;
  if (s0 == 0ULL || s0 == smask) {
    u32 test = (s0 == 0ULL) ? 0u : 1u;
    if (!full_kitten_flip(h, test ^ 1u)) {
      k[KH_NASSUMP] = 1u; k[KO_ASSUMP] = test;
      u64 d = full_kitten_solve(h, tick_lim);
      if (d == 20ULL) {
        if (!full_add_unit(h, (root_v << 1) | (1u - test))) {
          i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 20ULL;
        }
        h->sweep_cnt = h->sweep_cnt + 1ULL;
      } else if (d == 10ULL && rbit < 64u) {
        full_sweep_refine_kitten(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
      }
    } else if (rbit < 64u) {
      full_sweep_refine_kitten(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
    }
  }
  u32 j = 1u;
  while (j < nv && h->inconsistent == 0ULL && h->fuel > 0ULL) {
    u32 ov = cone_v[j]; u64 xr = (sig[ov] ^ sig[root_v]) & smask;
    if (xr == 0ULL || xr == smask) {
      u32 pol = (xr == 0ULL) ? 0u : 1u;
      k[KH_NASSUMP] = 2u; k[KO_ASSUMP] = 0u; k[KO_ASSUMP + 1u] = (j << 1) | (1u ^ pol);
      u64 d1 = full_kitten_solve(h, tick_lim);
      if (d1 == 10ULL && rbit < 64u) {
        full_sweep_refine_kitten(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
      } else if (d1 == 20ULL) {
        k[KO_ASSUMP] = 1u; k[KO_ASSUMP + 1u] = (j << 1) | pol;
        u64 d2 = full_kitten_solve(h, tick_lim);
        if (d2 == 10ULL && rbit < 64u) {
          full_sweep_refine_kitten(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        } else if (d2 == 20ULL) {
          u32 rl = root_v << 1; u32 ol = (ov << 1) | pol;
          if (full_add_bin(h, rl ^ 1u, ol) == 20ULL || full_add_bin(h, rl, ol ^ 1u) == 20ULL) {
            i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; } return 20ULL;
          }
          h->sweep_cnt = h->sweep_cnt + 1ULL;
        }
      }
    }
    j = j + 1u;
  }
  i = 0u; while (i < nv) { tmk[cone_v[i]] = 0u; i = i + 1u; }
  return 1ULL;
}

u64 full_sweep_dense(FullHdr *h, u64 budget, u64 tick_lim) {
  if (h->scratch_cap < 10240ULL || budget == 0ULL) { return 1ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars; u64 i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); budget = budget - 1ULL;
      if (full_sweep_var(h, (u32)v, tick_lim) == 20ULL) { res = 20ULL; break; }
    }
    v = v + 1ULL;
  }
  return res;
}
"

def fullDefSweepExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]⟩
  , ⟨"full_cong_hash_step", [i64, i64, i64, i64], [.bool]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_kitten_init", [i64, i32, i32], []⟩
  , ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool]⟩
  , ⟨"full_kitten_solve", [i64, i64], [i64]⟩
  , ⟨"full_kitten_core", [i64], [i32]⟩
  , ⟨"full_kitten_shrink", [i64], []⟩
  , ⟨"full_kitten_flip", [i64, i32], [.bool]⟩ ]

def fullDefSweepModule : LeanQbe.T.Module :=
  { fns := full_def_sweep_fns, externs := fullDefSweepExterns, exits := [] }

theorem full_bve_mark_and_wf : Func.Wf full_bve_mark_and_body := by t_wf_reify
theorem full_find_definition_wf : Func.Wf full_find_definition_body := by t_wf_reify
theorem full_bve_gates_wf : Func.Wf full_bve_gates_body := by t_wf_reify
theorem full_cong_extract_wf : Func.Wf full_cong_extract_body := by t_wf_reify
theorem full_congruence_dense_wf : Func.Wf full_congruence_dense_body := by t_wf_reify
theorem full_sweep_cone_wf : Func.Wf full_sweep_cone_body := by t_wf_reify
theorem full_sweep_refine_kitten_wf : Func.Wf full_sweep_refine_kitten_body := by t_wf_reify
theorem full_sweep_var_wf : Func.Wf full_sweep_var_body := by t_wf_reify
theorem full_sweep_dense_wf : Func.Wf full_sweep_dense_body := by t_wf_reify

theorem full_def_sweep_fns_wf : ∀ f ∈ full_def_sweep_fns, f.Wf := by
  simp only [full_def_sweep_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_bve_mark_and_wf, full_find_definition_wf, full_bve_gates_wf,
    full_cong_extract_wf, full_congruence_dense_wf, full_sweep_cone_wf,
    full_sweep_refine_kitten_wf, full_sweep_var_wf, full_sweep_dense_wf⟩

theorem fullDefSweep_acyclic : fullDefSweepModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullDefSweep
