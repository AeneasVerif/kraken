module

public import LeanQbe.T.Examples.Kissat.Full3

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Full` C0 Solver — Part 4 (`Congruence`, `Sweep`, `Forward/SSR`, `BVE/Gates/BCE`, `BVA`)

Implements:
1. **Gate Congruence Closure (`congruence.c`)**: AND/XOR/ITE extraction, canonical hash merging,
   equivalence/unit discovery (`full_congruence`).
2. **Bounded Cone SAT Sweeping (`sweep.c`)**: local cone BFS (`<= 24` vars), 64-bit bit-parallel
   simulation, iterative DPLL assumption refutation for units/equivalences (`full_sweep_sat`).
3. **Forward Subsumption & SSR (`forward.c`, `strengthen.c`)**: hyper-unary binary dedup,
   subsumption, and self-subsuming resolution (`full_forward_sub`).
4. **BVE + Gate-Restricted BVE (`Equiv`/`AND`/`ITE`/`XOR`) + Pure/BCE (`eliminate.c`, `gates.c`)**.
5. **Bounded Variable Addition / Factoring (`BVA`, `factor.c`)** into `d.mv .. max_vars - 1`.
6. **Top-Level CDCL + Preprocessing/Inprocessing + Model Reconstruction (`kissat_solve_bytes`)**.
-/

namespace LeanQbe.T.Examples.Kissat.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! full4 "
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

extern u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d,
                              i8 *vals, u64 mv_max);

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_ELIM    2u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_FACT_P  32u
#define FL_FACT_N  64u
#define FL_SWEEP   1024u

extern u64 full_isqrt(u64 x);
extern u64 full_rng_next(FullHdr *h);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_heap_push(FullHdr *h, u32 v);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);
extern u64 full_parse_body(FullHdr *h, u64 cnf_end);
extern u64 full_propagate(FullHdr *h);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_reduce(FullHdr *h, bool force);
extern u64 full_analyze(FullHdr *h);
extern u64 full_decide(FullHdr *h);
extern void full_warmup(FullHdr *h);
extern void full_rephase(FullHdr *h);
extern void full_switch_mode(FullHdr *h);
extern u64 full_restart_due(FullHdr *h);
extern void full_restart(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern void full_extend(FullHdr *h);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_lucky(FullHdr *h);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_transitive(FullHdr *h);
extern u64 full_vivify(FullHdr *h, u64 tier_mode);
extern u64 full_substitute(FullHdr *h);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);

u32 full_cong_find(u32 *repr, u32 l) {
  u32 r = l;
  while (repr[r] != r) { r = repr[r]; }
  u32 c = l;
  while (repr[c] != r) { u32 n = repr[c]; repr[c] = r; c = n; }
  return r;
}

bool full_cong_merge(FullHdr *h, u32 a, u32 b) {
  u32 *repr = (u32 *)h->repr;
  u32 ra = full_cong_find(repr, a); u32 rb = full_cong_find(repr, b);
  if (ra == rb) { return false; }
  if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return true; }
  if (ra > rb) { u32 t = ra; ra = rb; rb = t; }
  repr[rb] = ra; repr[rb ^ 1u] = ra ^ 1u;
  if (full_add_bin(h, ra ^ 1u, rb) == 20ULL || full_add_bin(h, ra, rb ^ 1u) == 20ULL) {
    h->inconsistent = 1ULL; return true;
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  return true;
}

bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 off = (u64)wvec[(u64)a << 1]; u64 end = off + (u64)wvec[((u64)a << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { continue; }
    u32 nf = 0u; bool ha = false; bool hb = false; bool hc = false; bool sat = false; u32 i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)i];
      if (vals[l] > (i8)0) { sat = true; break; }
      if (vals[l] == (i8)0) {
        nf = nf + 1u;
        if (l == a) { ha = true; } if (l == b) { hb = true; } if (l == c) { hc = true; }
      }
      i = i + 1u;
    }
    if (!sat && nf == 3u && ha && hb && hc) { return true; }
  }
  return false;
}

void full_sort_u32(u32 *arr, u32 n) {
  u32 i = 1u;
  while (i < n) {
    u32 x = arr[i]; u32 j = i;
    while (j > 0u && arr[j - 1u] > x) { arr[j] = arr[j - 1u]; j = j - 1u; }
    arr[j] = x; i = i + 1u;
  }
}

u64 full_cong_extract_ite(FullHdr *h, u32 c, u32 y, u32 t, u64 g_len) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)c << 1]; u64 end = off + (u64)wvec[((u64)c << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || ar[(u64)cr + 2ULL] != 3u) { continue; }
    u32 l0 = ar[(u64)cr + 3ULL]; u32 l1 = ar[(u64)cr + 4ULL]; u32 l2 = ar[(u64)cr + 5ULL];
    u32 e = 0xFFFFFFFFu;
    if (l0 == c && l1 == (y ^ 1u)) { e = l2; }
    else if (l0 == c && l2 == (y ^ 1u)) { e = l1; }
    else if (l1 == c && l0 == (y ^ 1u)) { e = l2; }
    else if (l1 == c && l2 == (y ^ 1u)) { e = l0; }
    else if (l2 == c && l0 == (y ^ 1u)) { e = l1; }
    else if (l2 == c && l1 == (y ^ 1u)) { e = l0; }
    if (e != 0xFFFFFFFFu && full_has_ternary(h, c, e ^ 1u, y)) {
      if ((c & 1u) != 0u) { u32 tmp = t; t = e; e = tmp; c = c ^ 1u; }
      if ((y & 1u) != 0u) { y = y ^ 1u; t = t ^ 1u; e = e ^ 1u; }
      scr[g_len] = y; scr[g_len + 1ULL] = (2u << 28) | 3u;
      scr[g_len + 2ULL] = c; scr[g_len + 3ULL] = t; scr[g_len + 4ULL] = e;
      return g_len + 5ULL;
    }
  }
  return g_len;
}

u64 full_cong_emit_xor(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2) {
  u32 lhs = ((x0 ^ 1u) & (~1u)) | (((x0 ^ 1u) ^ x1 ^ x2) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u);
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 2u;
  scr[g_len + 2ULL] = (r0 < r1) ? r0 : r1; scr[g_len + 3ULL] = (r0 < r1) ? r1 : r0;
  return g_len + 4ULL;
}

u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap) {
  u32 *scr = (u32 *)h->scratch_buf;
  if (full_has_ternary(h, a, b ^ 1u, c ^ 1u) && full_has_ternary(h, a ^ 1u, b, c ^ 1u) &&
      full_has_ternary(h, a ^ 1u, b ^ 1u, c)) {
    if (g_len + 12ULL <= g_cap) {
      g_len = full_cong_emit_xor(scr, g_len, a, b, c);
      g_len = full_cong_emit_xor(scr, g_len, b, a, c);
      g_len = full_cong_emit_xor(scr, g_len, c, a, b);
    }
    return g_len;
  }
  if (full_has_ternary(h, a, b ^ 1u, c ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, a ^ 1u, b ^ 1u, c, g_len);
    if (ng > g_len) { return ng; }
    return full_cong_extract_ite(h, a ^ 1u, c ^ 1u, b, g_len);
  }
  if (full_has_ternary(h, b, a ^ 1u, c ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, b ^ 1u, a ^ 1u, c, g_len);
    if (ng > g_len) { return ng; }
    return full_cong_extract_ite(h, b ^ 1u, c ^ 1u, a, g_len);
  }
  if (full_has_ternary(h, c, a ^ 1u, b ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, c ^ 1u, a ^ 1u, b, g_len);
    if (ng > g_len) { return ng; }
    return full_cong_extract_ite(h, c ^ 1u, b ^ 1u, a, g_len);
  }
  return g_len;
}

u64 full_cong_extract(FullHdr *h, u64 g_cap) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u64 p = 0ULL; u64 g_len = 0ULL;
  while (p < h->arena_len && g_len + 16ULL <= g_cap) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
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
            if (j != i) { scr[g_len + 2ULL + (u64)rk] = ar[p + 3ULL + (u64)j] ^ 1u; rk = rk + 1u; }
            j = j + 1u;
          }
          g_len = g_len + 2ULL + (u64)(sz - 1u); break;
        }
        i = i + 1u;
      }
      if (sz == 3u && g_len + 14ULL <= g_cap) {
        g_len = full_cong_try_xor_ite(h, ar[p + 3ULL], ar[p + 4ULL], ar[p + 5ULL], g_len, g_cap);
      }
    }
    p = np;
  }
  return g_len;
}

bool full_cong_hash_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr; u32 *tmp = (u32 *)h->tmp_lits;
  u64 k = 0ULL; while (k < ht_sz) { scr[ht_off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  bool changed = false; u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL) {
    u32 lhs = full_cong_find(repr, scr[g]);
    u32 meta = scr[g + 1ULL]; u32 tag = meta >> 28; u32 arity = meta & 0xFFu;
    u32 i = 0u;
    while (i < arity) { tmp[i] = full_cong_find(repr, scr[g + 2ULL + (u64)i]); i = i + 1u; }
    if (tag != 2u) { full_sort_u32(tmp, arity); }
    if (tag == 2u && tmp[1] == tmp[2]) {
      if (full_cong_merge(h, lhs, tmp[1])) { changed = true; }
      g = g + 2ULL + (u64)arity; continue;
    }
    if (tag == 1u && arity == 2u && (tmp[0] >> 1) == (tmp[1] >> 1)) {
      u32 ul = (tmp[0] == tmp[1]) ? (lhs ^ 1u) : lhs;
      if (!full_add_unit(h, ul)) { return true; }
      h->cong_cnt = h->cong_cnt + 1ULL; g = g + 4ULL; continue;
    }
    u64 hv = (u64)tag * 0x9E3779B1ULL + (u64)arity;
    i = 0u; while (i < arity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL); u64 probes = 0ULL;
    while (probes < 16ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) { scr[ht_off + slot] = (u32)g; break; }
      u32 em = scr[(u64)ent + 1ULL];
      if ((em >> 28) == tag && (em & 0xFFu) == arity) {
        u32 rhs_eq = 1u;
        i = 0u;
        while (i < arity) {
          if (full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)i]) != tmp[i]) { rhs_eq = 0u; break; }
          i = i + 1u;
        }
        if (rhs_eq != 0u) {
          if (full_cong_merge(h, lhs, scr[ent])) { changed = true; }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
    }
    g = g + 2ULL + (u64)arity;
  }
  return changed;
}

u64 full_congruence(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->scratch_cap < 256ULL || !full_enter_dense(h)) { return 1ULL; }
  u64 ht_sz = 64ULL;
  while (ht_sz * 4ULL < h->scratch_cap && ht_sz < 4096ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 g_len = full_cong_extract(h, ht_off);
  u32 *repr = (u32 *)h->repr; u64 nlits = h->cur_vars << 1;
  u64 i = 0ULL; while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  u64 pass = 0ULL;
  while (pass < 6ULL && h->inconsistent == 0ULL) {
    if (!full_cong_hash_step(h, g_len, ht_off, ht_sz)) { break; }
    pass = pass + 1ULL;
  }
  u64 rr = full_rebuild_watches(h);
  if (rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_sweep_add_cl(FullHdr *h, u32 *lits, u32 sz, u32 nc) {
  u64 lp = h->res_sz;
  if (nc >= 64u || lp + (u64)sz > 1024ULL) { return (u64)nc; }
  u32 *scr = (u32 *)h->scratch_buf;
  scr[nc] = (u32)lp; scr[64ULL + (u64)nc] = sz;
  u32 k = 0u; while (k < sz) { scr[lp + (u64)k] = lits[k]; k = k + 1u; }
  h->res_sz = lp + (u64)sz;
  return (u64)(nc + 1u);
}

u64 full_sweep_cone(FullHdr *h, u32 root_v) {
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 nv = 1u; u32 nc = 0u; h->res_sz = 128ULL;
  cone_v[0] = root_v; tmk[root_v] = 0u; u32 qi = 0u;
  while (qi < nv && nv < 24u && nc < 64u) {
    u32 cv = cone_v[qi]; qi = qi + 1u; u32 pol = 0u;
    while (pol < 2u && nc < 64u) {
      u32 lit = (cv << 1) | pol;
      u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      u64 p = off;
      while (p < end && nc < 64u) {
        u32 w0 = wstk[p]; p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK; u32 ov = ot >> 1;
          if (vals[ot] == (i8)0 && (tmk[ov] != 0xFFFFFFFFu || nv < 24u)) {
            if (tmk[ov] == 0xFFFFFFFFu) { tmk[ov] = nv; cone_v[nv] = ov; nv = nv + 1u; }
            if (lit < ot) {
              tmp[0] = (tmk[cv] << 1) | pol; tmp[1] = (tmk[ov] << 1) | (ot & 1u);
              nc = (u32)full_sweep_add_cl(h, tmp, 2u, nc);
            }
          }
          continue;
        }
        if (p >= end) { break; }
        u32 cr = wstk[p]; p = p + 1ULL; u32 sz = ar[(u64)cr + 2ULL];
        if ((ar[cr] & (PH_GARB | PH_RED)) != 0u || sz < 3u || sz > 6u) { continue; }
        bool sat = false; u32 cnt = 0u; u32 k = 0u;
        while (k < sz) {
          u32 l = ar[(u64)cr + 3ULL + (u64)k];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (vals[l] == (i8)0) {
            u32 lv = l >> 1;
            if (tmk[lv] == 0xFFFFFFFFu && nv < 24u) { tmk[lv] = nv; cone_v[nv] = lv; nv = nv + 1u; }
            if (tmk[lv] == 0xFFFFFFFFu) { sat = true; break; }
            tmp[cnt] = (tmk[lv] << 1) | (l & 1u); cnt = cnt + 1u;
          }
          k = k + 1u;
        }
        if (!sat && cnt >= 2u) { nc = (u32)full_sweep_add_cl(h, tmp, cnt, nc); }
      }
      pol = pol + 1u;
    }
  }
  return (u64)nv | ((u64)nc << 16);
}

u64 full_sweep_dpll(FullHdr *h, u32 nv, u32 nc, u32 a0, u32 a1) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *val = scr + 1024; u32 *dv = scr + 1048;
  u32 *dph = scr + 1072; u32 *trl = scr + 1096; u32 *dt = scr + 1120;
  u32 i = 0u; while (i < nv) { val[i] = 0u; i = i + 1u; }
  u32 tn = 0u; u32 sp = 0u;
  if (a0 < (nv << 1)) { val[a0 >> 1] = (a0 & 1u) + 1u; trl[tn] = a0 >> 1; tn = tn + 1u; }
  if (a1 < (nv << 1)) {
    u32 v1 = a1 >> 1; u32 w1 = (a1 & 1u) + 1u;
    if (val[v1] != 0u && val[v1] != w1) { return 20ULL; }
    if (val[v1] == 0u) { val[v1] = w1; trl[tn] = v1; tn = tn + 1u; }
  }
  u64 budget = 256ULL;
  while (budget > 0ULL) {
    if (h->fuel == 0ULL) { return 0ULL; }
    h->fuel = h->fuel - 1ULL;
    budget = budget - 1ULL; bool confl = false; bool chg = true;
    while (chg && !confl) {
      chg = false; u32 c = 0u;
      while (c < nc) {
        u32 off = scr[c]; u32 sz = scr[64u + c];
        bool sat = false; u32 un = 0u; u32 ul = 0u; u32 k = 0u;
        while (k < sz) {
          u32 l = scr[(u64)off + (u64)k]; u32 vw = val[l >> 1]; u32 want = (l & 1u) + 1u;
          if (vw == want) { sat = true; break; }
          if (vw == 0u) { un = un + 1u; ul = l; }
          k = k + 1u;
        }
        if (!sat && un == 0u) { confl = true; break; }
        if (!sat && un == 1u) {
          val[ul >> 1] = (ul & 1u) + 1u; trl[tn] = ul >> 1; tn = tn + 1u; chg = true;
        }
        c = c + 1u;
      }
    }
    if (confl) {
      while (sp > 0u && dph[sp - 1u] != 0u) { sp = sp - 1u; }
      if (sp == 0u) { return 20ULL; }
      sp = sp - 1u; u32 v = dv[sp]; u32 nv_w = 3u - val[v];
      while (tn > dt[sp]) { tn = tn - 1u; val[trl[tn]] = 0u; }
      dph[sp] = 1u; dt[sp] = tn; val[v] = nv_w; trl[tn] = v; tn = tn + 1u; sp = sp + 1u;
      continue;
    }
    u32 pick = 0u; while (pick < nv && val[pick] != 0u) { pick = pick + 1u; }
    if (pick == nv) { return 10ULL; }
    dv[sp] = pick; dph[sp] = 0u; dt[sp] = tn;
    val[pick] = (u32)(full_rng_next(h) & 1ULL) + 1u; trl[tn] = pick;
    tn = tn + 1u; sp = sp + 1u;
  }
  return 0ULL;
}

void full_sweep_refine(FullHdr *h, u32 nv, u32 bit_idx) {
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 *val = ((u32 *)h->scratch_buf) + 1024;
  u64 mask = 1ULL << (u64)(bit_idx & 63u); u32 i = 0u;
  while (i < nv) {
    u32 gv = cone_v[i];
    if (val[i] == 1u) { sig[gv] = sig[gv] | mask; } else { sig[gv] = sig[gv] & (~mask); }
    i = i + 1u;
  }
}

u32 full_sweep_seed_sim(FullHdr *h, u32 nv, u32 nc) {
  u32 *cone_v = (u32 *)h->work_stk1; u64 *sig = (u64 *)h->sim_sig;
  u32 i = 0u; while (i < nv) { sig[cone_v[i]] = 0ULL; i = i + 1u; }
  u32 rbit = 0u; u32 s = 0u;
  while (s < 8u && rbit < 64u && h->fuel > 0ULL) {
    u32 a0 = (s < 2u) ? 0xFFFFFFFFu : ((s % nv) << 1) | (s & 1u);
    u64 d = full_sweep_dpll(h, nv, nc, a0, 0xFFFFFFFFu);
    if (d == 20ULL && a0 == 0xFFFFFFFFu) { return 0xFFFFFFFFu; }
    if (d == 10ULL) { full_sweep_refine(h, nv, rbit); rbit = rbit + 1u; }
    s = s + 1u;
  }
  return rbit;
}

u64 full_sweep_var(FullHdr *h, u32 root_v) {
  u64 pk = full_sweep_cone(h, root_v);
  u32 nv = (u32)(pk & 0xFFFFULL); u32 nc = (u32)(pk >> 16);
  u32 *cone_v = (u32 *)h->work_stk1; u32 *tmk = (u32 *)h->tarjan_mark; u64 *sig = (u64 *)h->sim_sig;
  if (nv < 2u || nc == 0u) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0xFFFFFFFFu; i = i + 1u; } return 1ULL;
  }
  u32 rbit = full_sweep_seed_sim(h, nv, nc);
  if (rbit == 0xFFFFFFFFu) {
    u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0xFFFFFFFFu; i = i + 1u; }
    h->inconsistent = 1ULL; return 20ULL;
  }
  u64 smask = (rbit == 0u) ? 0ULL : ((rbit >= 64u) ? (~0ULL) : ((1ULL << rbit) - 1ULL));
  u64 s0 = sig[root_v] & smask;
  if (rbit > 0u && (s0 == 0ULL || s0 == smask)) {
    u32 test = (s0 == 0ULL) ? 0u : 1u;
    u64 d = full_sweep_dpll(h, nv, nc, test, 0xFFFFFFFFu);
    if (d == 20ULL) {
      if (!full_add_unit(h, (root_v << 1) | (1u - test))) {
        u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0xFFFFFFFFu; i = i + 1u; } return 20ULL;
      }
      h->sweep_cnt = h->sweep_cnt + 1ULL;
    } else if (d == 10ULL && rbit < 64u) {
      full_sweep_refine(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
    }
  }
  u32 j = 1u;
  while (j < nv && h->inconsistent == 0ULL) {
    u32 ov = cone_v[j]; u64 xr = (sig[ov] ^ sig[root_v]) & smask;
    if (rbit > 0u && (xr == 0ULL || xr == smask)) {
      u32 pol = (xr == 0ULL) ? 0u : 1u;
      u64 d1 = full_sweep_dpll(h, nv, nc, 0u, (j << 1) | (1u ^ pol));
      if (d1 == 10ULL && rbit < 64u) {
        full_sweep_refine(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
      } else if (d1 == 20ULL) {
        u64 d2 = full_sweep_dpll(h, nv, nc, 1u, (j << 1) | pol);
        if (d2 == 10ULL && rbit < 64u) {
          full_sweep_refine(h, nv, rbit); smask = smask | (1ULL << rbit); rbit = rbit + 1u;
        } else if (d2 == 20ULL) {
          u32 rl = root_v << 1; u32 ol = (ov << 1) | pol;
          if (full_add_bin(h, rl ^ 1u, ol) == 20ULL || full_add_bin(h, rl, ol ^ 1u) == 20ULL) {
            u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0xFFFFFFFFu; i = i + 1u; } return 20ULL;
          }
          h->sweep_cnt = h->sweep_cnt + 1ULL;
        }
      }
    }
    j = j + 1u;
  }
  u32 i = 0u; while (i < nv) { tmk[cone_v[i]] = 0xFFFFFFFFu; i = i + 1u; }
  return 1ULL;
}

u64 full_sweep_sat(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->scratch_cap < 1152ULL || !full_enter_dense(h)) { return 1ULL; }
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars; u64 i = 0ULL; while (i < cv) { tmk[i] = 0xFFFFFFFFu; i = i + 1ULL; }
  u64 v = 0ULL; u64 budget = 32ULL; u64 res = 1ULL;
  while (v < cv && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_SWEEP)) == (FL_ACTIVE | FL_SWEEP) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_SWEEP); budget = budget - 1ULL;
      if (full_sweep_var(h, (u32)v) == 20ULL) { res = 20ULL; break; }
    }
    v = v + 1ULL;
  }
  u64 rr = full_rebuild_watches(h);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  return 1ULL;
}

bool full_fwd_dedup_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark; u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u64 p = off; u64 q = off; u64 end = off + sz; bool unit_l = false;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits && lm[ot] != (u8)0) {
        if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if ((u64)ot < nlits && lm[ot ^ 1u] != (u8)0) { unit_l = true; }
        if ((u64)ot < nlits) { lm[ot] = (u8)1; }
        wstk[q] = w0; q = q + 1ULL;
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    if (unit_l && !full_add_unit(h, (u32)l)) { return false; }
    l = l + 1ULL;
  }
  return true;
}

bool full_fwd_check_cl(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 hdr = ar[cref]; u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { return true; }
  u32 i = 0u; while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)1; i = i + 1u; }
  bool subsumed = false; u32 drop = 0xFFFFFFFFu; u32 min_l = ar[(u64)cref + 3ULL];
  u32 min_deg = wvec[((u64)min_l << 1) + 1ULL];
  i = 1u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u32 d = wvec[((u64)l << 1) + 1ULL];
    if (d < min_deg) { min_deg = d; min_l = l; }
    i = i + 1u;
  }
  i = 0u;
  while (i < sz && !subsumed && drop == 0xFFFFFFFFu) {
    u32 l = (i == 0u) ? min_l : ar[(u64)cref + 3ULL + (u64)i];
    if (i > 0u && l == min_l) { l = ar[(u64)cref + 3ULL]; }
    u64 off = (u64)wvec[(u64)l << 1]; u64 end = off + (u64)wvec[((u64)l << 1) + 1ULL];
    u64 p = off;
    while (p < end && p - off < 128ULL) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if (lm[ot] != (u8)0) { subsumed = true; break; }
        if ((ot ^ 1u) != l && lm[ot ^ 1u] != (u8)0) { drop = ot ^ 1u; break; }
        continue;
      }
      if (p >= end) { break; }
      u32 cr = wstk[p]; p = p + 1ULL;
      if (cr == cref || (ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
      u32 dsz = ar[(u64)cr + 2ULL];
      if (dsz > sz) { continue; }
      u32 miss = 0u; u32 cand = 0xFFFFFFFFu; u32 j = 0u;
      while (j < dsz) {
        u32 dl = ar[(u64)cr + 3ULL + (u64)j];
        if (lm[dl] == (u8)0 && vals[dl] >= (i8)0) {
          if (lm[dl ^ 1u] != (u8)0 && cand == 0xFFFFFFFFu) { cand = dl ^ 1u; }
          else { miss = 2u; break; }
        }
        j = j + 1u;
      }
      if (miss == 0u && cand == 0xFFFFFFFFu) { subsumed = true; break; }
      if (miss == 0u && cand != 0xFFFFFFFFu) { drop = cand; break; }
    }
    i = i + 1u;
  }
  i = 0u; while (i < sz) { lm[ar[(u64)cref + 3ULL + (u64)i]] = (u8)0; i = i + 1u; }
  if (subsumed) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    h->fwd_sub_cnt = h->fwd_sub_cnt + 1ULL; return true;
  }
  if (drop != 0xFFFFFFFFu) {
    h->fwd_str_cnt = h->fwd_str_cnt + 1ULL; full_unwatch_large(h, drop, cref);
    u32 nsz = 0u; i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)i];
      if (l != drop) { ar[(u64)cref + 3ULL + (u64)nsz] = l; nsz = nsz + 1u; }
      i = i + 1u;
    }
    if (nsz <= 2u) {
      ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (nsz == 1u) { return full_add_unit(h, ar[(u64)cref + 3ULL]); }
      return full_add_bin(h, ar[(u64)cref + 3ULL], ar[(u64)cref + 4ULL]) != 20ULL;
    }
    ar[(u64)cref + 2ULL] = nsz; ar[(u64)cref + 1ULL] = 2u;
    if ((hdr & PH_SHRK) == 0u) {
      ar[cref] = hdr | PH_SHRK; ar[(u64)cref + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
    }
  }
  return true;
}

u64 full_forward_sub(FullHdr *h) {
  if (!full_fwd_dedup_bins(h)) { return 20ULL; }
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL; u64 budget = 2048ULL;
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

u32 full_bve_collect(FullHdr *h, u32 lit, u32 *out, u32 cap) {
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 p = off; u32 cnt = 0u;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] > (i8)0) { continue; }
      if (cnt >= cap) { return 0xFFFFFFFFu; }
      out[cnt] = w0; cnt = cnt + 1u;
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    if (cnt >= cap) { return 0xFFFFFFFFu; }
    out[cnt] = cr; cnt = cnt + 1u;
  }
  return cnt;
}

bool full_bve_mark_and(FullHdr *h, u32 v_lit, u32 cr, u32 n_off, u32 nn) {
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u8 *lm = (u8 *)h->lit_mark; u32 sz = ar[(u64)cr + 2ULL]; u32 need = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cr + 3ULL + (u64)i];
    if (l != v_lit) { lm[l ^ 1u] = (u8)1; need = need + 1u; }
    i = i + 1u;
  }
  u32 matched = 0u; u64 nmask = 0ULL; u32 j = 0u;
  while (j < nn) {
    u32 w = scr[n_off + j];
    if ((w & PW_BIN_FLAG) != 0u && lm[w & PW_LIT_MASK] != (u8)0) {
      nmask = nmask | (1ULL << (u64)j); matched = matched + 1u;
    }
    j = j + 1u;
  }
  i = 0u; while (i < sz) { lm[ar[(u64)cr + 3ULL + (u64)i] ^ 1u] = (u8)0; i = i + 1u; }
  if (matched >= need) { scr[130] = (u32)nmask; scr[131] = (u32)(nmask >> 32); return true; }
  return false;
}

void full_bve_gates(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf; scr[128] = 0u; scr[129] = 0u; scr[130] = 0u; scr[131] = 0u;
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
      scr[130] = scr[130]; u64 pm = (u64)scr[130] | ((u64)scr[131] << 32);
      u64 nm = 1ULL << (u64)j;
      scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32);
      scr[130] = (u32)nm; scr[131] = (u32)(nm >> 32); return;
    }
    j = j + 1u;
  }
}

bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  i8 *vals = (i8 *)h->values; u32 pl = v << 1; u32 nl = pl | 1u;
  u32 rlen = 0u; bool taut = false;
  if ((pc & PW_BIN_FLAG) != 0u) {
    u32 l = pc & PW_LIT_MASK; if (vals[l] > (i8)0) { taut = true; }
    else if (vals[l] == (i8)0) { lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u; }
  } else {
    u32 psz = ar[(u64)pc + 2ULL]; u32 i = 0u;
    while (i < psz) {
      u32 l = ar[(u64)pc + 3ULL + (u64)i];
      if (l != pl) {
        if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; break; }
        if (vals[l] == (i8)0 && lm[l] == (u8)0) { lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u; }
      }
      i = i + 1u;
    }
  }
  if (!taut) {
    if ((nc & PW_BIN_FLAG) != 0u) {
      u32 l = nc & PW_LIT_MASK;
      if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; }
      else if (vals[l] == (i8)0 && lm[l] == (u8)0) {
        lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u;
      }
    } else {
      u32 nsz = ar[(u64)nc + 2ULL]; u32 i = 0u;
      while (i < nsz) {
        u32 l = ar[(u64)nc + 3ULL + (u64)i];
        if (l != nl) {
          if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; break; }
          if (vals[l] == (i8)0 && lm[l] == (u8)0) {
            lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u;
          }
        }
        i = i + 1u;
      }
    }
  }
  u32 k = 0u; while (k < rlen) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  h->tmp_len = (u64)rlen; return !taut;
}

bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena; u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (!full_extend_push2(h, blk_lit, ot)) { return false; }
      full_delete_binary(h, blk_lit, ot);
    } else {
      if (!full_extend_push_cl(h, blk_lit, w)) { return false; }
      ar[w] = ar[w] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
    }
    i = i + 1u;
  }
  return true;
}

bool full_bve_try_bce(FullHdr *h, u32 blk_lit, u32 cr, u32 opp_off, u32 opp_n) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena;
  u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits; u32 mcnt = 0u;
  if ((cr & PW_BIN_FLAG) != 0u) {
    u32 ot = cr & PW_LIT_MASK; lm[ot ^ 1u] = (u8)1; tmp[mcnt] = ot ^ 1u; mcnt = 1u;
  } else {
    u32 sz = ar[(u64)cr + 2ULL]; u32 i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)i];
      if (l != blk_lit) { lm[l ^ 1u] = (u8)1; tmp[mcnt] = l ^ 1u; mcnt = mcnt + 1u; }
      i = i + 1u;
    }
  }
  bool blocked = true; u32 j = 0u;
  while (j < opp_n && blocked) {
    u32 ow = scr[opp_off + j]; bool hit = false;
    if ((ow & PW_BIN_FLAG) != 0u) { if (lm[ow & PW_LIT_MASK] != (u8)0) { hit = true; } }
    else {
      u32 osz = ar[(u64)ow + 2ULL]; u32 k = 0u;
      while (k < osz) {
        if (lm[ar[(u64)ow + 3ULL + (u64)k]] != (u8)0) { hit = true; break; }
        k = k + 1u;
      }
    }
    if (!hit) { blocked = false; }
    j = j + 1u;
  }
  u32 i = 0u; while (i < mcnt) { lm[tmp[i]] = (u8)0; i = i + 1u; }
  return blocked;
}

u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end) {
  u32 *scr = (u32 *)h->scratch_buf; u64 p = r_off;
  while (p < r_end) {
    u32 sz = scr[p]; p = p + 1ULL;
    if (sz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (sz == 1u) { if (!full_add_unit(h, scr[p])) { return 20ULL; } }
    else if (sz == 2u) {
      u64 br = full_add_bin(h, scr[p], scr[p + 1ULL]);
      if (br == 20ULL) { return 20ULL; }
      if (br == 2ULL) { return 2ULL; }
    } else {
      u64 cr = full_alloc_cl(h, sz, 0u, false);
      if (cr == 0xFFFFFFFFULL) { h->oom = 1ULL; return 2ULL; }
      u32 *ar = (u32 *)h->arena; u32 k = 0u;
      while (k < sz) { ar[cr + 3ULL + (u64)k] = scr[p + (u64)k]; k = k + 1u; }
      k = 0u;
      while (k < sz) {
        if (!full_watch_push(h, ar[cr + 3ULL + (u64)k], sz & PW_LIT_MASK, (u32)cr, 2u)) {
          ar[cr] = ar[cr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
          h->oom = 1ULL; return 2ULL;
        }
        k = k + 1u;
      }
      h->num_irred = h->num_irred + 1ULL;
    }
    p = p + (u64)sz;
  }
  return 1ULL;
}

u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena;
  u64 need = 0ULL; u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) { need = need + 2ULL; }
    else { need = need + (u64)ar[(u64)w + 2ULL] + 1ULL; }
    i = i + 1u;
  }
  return need;
}

u64 full_bve_var(FullHdr *h, u32 v) {
  if (h->scratch_cap < 512ULL) { return 1ULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 pl = v << 1; u32 nl = pl | 1u;
  u32 np = full_bve_collect(h, pl, scr, 32u);
  u32 nn = full_bve_collect(h, nl, scr + 64, 32u);
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
    u32 i = 0u;
    while (i < np && fit) {
      u32 j = 0u;
      while (j < nn && fit) {
        if ((((pmask >> (u64)i) & (nmask >> (u64)j)) & 1ULL) == 0ULL &&
            full_bve_resolve_pair(h, v, scr[i], scr[64u + j])) {
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
        u32 *ar = (u32 *)h->arena; u32 ccr = scr[i];
        ar[ccr] = ar[ccr] | PH_GARB;
        h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)ccr + 2ULL];
        h->bce_cnt = h->bce_cnt + 1ULL;
      }
    }
    i = i + 1u;
  }
  return 1ULL;
}

void full_init_fresh_var(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases; u32 *wvec = (u32 *)h->watch_vec;
  u64 wb = (u64)fv << 2;
  wvec[wb] = 0u; wvec[wb + 1ULL] = 0u; wvec[wb + 2ULL] = 0u; wvec[wb + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)1; lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu; ps[fv] = 0xFFFFFFFFu;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP;
  u32 ol = (u32)h->q_last; qp[fv] = ol; qn[fv] = 0xFFFFFFFFu;
  if ((u64)ol < h->cur_vars) { qn[ol] = fv; } else { h->q_first = (u64)fv; }
  h->q_last = (u64)fv; h->q_cur_stamp = h->q_cur_stamp + 1ULL; qs[fv] = (u32)h->q_cur_stamp;
  h->unassigned = h->unassigned + 1ULL;
  if (h->stable != 0ULL) { full_heap_push(h, fv); }
}

bool full_bva_try_lit(FullHdr *h, u32 f0) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < 512ULL) { return false; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *scr = (u32 *)h->scratch_buf; i8 *vals = (i8 *)h->values;
  if (vals[f0] != (i8)0) { return false; }
  u64 off = (u64)wvec[(u64)f0 << 1]; u64 end = off + (u64)wvec[((u64)f0 << 1) + 1ULL];
  u32 qn = 0u; u64 p = off;
  while (p < end && qn < 32u) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] == (i8)0) { scr[qn] = ot; qn = qn + 1u; }
    } else if (p < end) { p = p + 1ULL; }
  }
  if (qn < 2u) { return false; }
  u32 q0 = scr[0]; u64 qoff = (u64)wvec[(u64)q0 << 1];
  u64 qend = qoff + (u64)wvec[((u64)q0 << 1) + 1ULL];
  u32 dn = 1u; scr[64] = f0; p = qoff;
  while (p < qend && dn < 16u) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 cand = w0 & PW_LIT_MASK;
      if (cand != f0 && cand != (f0 ^ 1u) && vals[cand] == (i8)0) {
        scr[64u + dn] = cand; dn = dn + 1u;
      }
    } else if (p < qend) { p = p + 1ULL; }
  }
  u32 bi = 1u;
  while (bi < dn) {
    u32 f1 = scr[64u + bi]; u32 mn = 0u; u32 qi = 0u;
    while (qi < qn) {
      if (full_has_bin(h, f1, scr[qi])) { scr[128u + mn] = scr[qi]; mn = mn + 1u; }
      qi = qi + 1u;
    }
    if (mn >= 2u) {
      u32 dm = 2u; scr[192] = f0; scr[193] = f1; u32 dj = bi + 1u;
      while (dj < dn && dm < 8u) {
        u32 fj = scr[64u + dj]; bool all_m = true; u32 k = 0u;
        while (k < mn) {
          if (!full_has_bin(h, fj, scr[128u + k])) { all_m = false; break; }
          k = k + 1u;
        }
        if (all_m) { scr[192u + dm] = fj; dm = dm + 1u; }
        dj = dj + 1u;
      }
      if ((u64)dm * (u64)mn > (u64)dm + (u64)mn &&
          (h->wcap - h->wlen >= ((u64)dm + (u64)mn + 4ULL) * 8ULL)) {
        u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
        full_init_fresh_var(h, fv); u32 fresh = fv << 1; u32 j = 0u;
        while (j < dm) { full_add_bin(h, fresh, scr[192u + j]); j = j + 1u; }
        u32 k = 0u;
        while (k < mn) {
          u32 q = scr[128u + k]; j = 0u;
          while (j < dm) { full_delete_binary(h, scr[192u + j], q); j = j + 1u; }
          full_add_bin(h, fresh ^ 1u, q); k = k + 1u;
        }
        h->bva_cnt = h->bva_cnt + 1ULL; return true;
      }
    }
    bi = bi + 1u;
  }
  return false;
}

u64 full_factor(FullHdr *h) {
  if (h->cur_vars >= h->max_vars) { return 1ULL; }
  u32 *fl = (u32 *)h->flags; u64 cv = h->cur_vars; u64 budget = 64ULL; u64 v = 0ULL;
  while (v < cv && h->cur_vars < h->max_vars && budget > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & FL_ACTIVE) != 0u) {
      if ((fl[v] & FL_FACT_P) != 0u) {
        fl[v] = fl[v] & (~FL_FACT_P); budget = budget - 1ULL; full_bva_try_lit(h, (u32)(v << 1));
      }
      if ((fl[v] & FL_FACT_N) != 0u && h->cur_vars < h->max_vars) {
        fl[v] = fl[v] & (~FL_FACT_N); budget = budget - 1ULL;
        full_bva_try_lit(h, (u32)((v << 1) | 1u));
      }
    }
    v = v + 1ULL;
  }
  return 1ULL;
}

u64 full_probe(FullHdr *h) {
  h->probings = h->probings + 1ULL;
  h->probe_limit = h->conflicts + 500ULL * full_isqrt(h->probings);
  if (full_substitute(h) == 20ULL) { return 20ULL; }
  if (full_congruence(h) == 20ULL) { return 20ULL; }
  if (full_substitute(h) == 20ULL) { return 20ULL; }
  if (full_sweep_sat(h) == 20ULL) { return 20ULL; }
  if (full_transitive(h) == 20ULL) { return 20ULL; }
  if (full_probe_run(h, 64ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 1ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 0ULL) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_eliminate(FullHdr *h) {
  h->eliminations = h->eliminations + 1ULL;
  h->elim_limit = h->conflicts + 1500ULL * full_isqrt(h->eliminations);
  if (!full_enter_dense(h)) { return 1ULL; }
  if (full_forward_sub(h) == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values; u64 cv = h->cur_vars;
  u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~FL_ELIM_C);
      u64 br = full_bve_var(h, (u32)v);
      if (br == 20ULL) { res = 20ULL; break; }
      if (br == 2ULL) { break; }
    }
    v = v + 1ULL;
  }
  if (res == 1ULL) { full_factor(h); }
  u64 rr = full_rebuild_watches(h);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_preprocess(FullHdr *h) {
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  if (full_probe(h) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->unassigned == 0ULL) { return 10ULL; }
  return 1ULL;
}

u64 full_simplify(FullHdr *h) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (full_reduce(h, true) == 20ULL) { return 20ULL; }
  if (full_probe(h) == 20ULL) { return 20ULL; }
  if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
  if (full_eliminate(h) == 20ULL) { return 20ULL; }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->oom != 0ULL) { return 0ULL; }
  return 1ULL;
}

u64 full_search(FullHdr *h) {
  u64 lk = full_lucky(h);
  if (lk == 20ULL || lk == 10ULL) { return lk; }
  full_warmup(h);
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 pr = full_propagate(h);
    if (pr == 2ULL) { return 0ULL; }
    if (pr == 1ULL) {
      u64 ast = full_analyze(h);
      if (ast == 20ULL) { return 20ULL; }
      if (ast != 1ULL) { return 0ULL; }
      full_switch_mode(h);
      if (h->conflicts >= h->rephase_limit) { full_rephase(h); }
      if (h->conflicts >= h->reduce_limit) {
        u64 rr = full_reduce(h, false);
        if (rr == 20ULL) { return 20ULL; }
        if (rr != 1ULL) { return 0ULL; }
      }
      if (h->conflicts >= h->probe_limit || h->conflicts >= h->elim_limit) {
        u64 sr = full_simplify(h);
        if (sr == 20ULL) { return 20ULL; }
        if (sr != 1ULL) { return 0ULL; }
      } else if (full_restart_due(h) != 0ULL) { full_restart(h); }
    } else {
      if (h->unassigned == 0ULL) { return 10ULL; }
      if (full_decide(h) == 0ULL) { return (h->unassigned == 0ULL) ? 10ULL : 0ULL; }
    }
  }
}

u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + (u64)sizeof(FullHdr)) { return 0ULL; }
  u64 hdr_addr = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  if (!full_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)) { return 0ULL; }
  FullHdr *h = (FullHdr *)hdr_addr;
  u64 pb = full_parse_body(h, cnf_end);
  if (pb != 1ULL) { return pb; }
  u64 pp = full_preprocess(h);
  if (pp == 20ULL) { return 20ULL; }
  u64 r = (pp == 10ULL) ? 10ULL : ((pp == 0ULL) ? 0ULL : full_search(h));
  if (r == 10ULL) {
    full_extend(h);
    u64 ok = kissat_check_model(cnf_ptr, cnf_end, &h->d, (i8 *)h->values, h->d.mv);
    return (ok == 1ULL) ? 10ULL : 0ULL;
  }
  return r;
}
"

def fullFns : List Fn := dimacs_fns ++ full1_fns ++ full2_fns ++ full3_fns ++ full4_fns

def fullModule : LeanQbe.T.Module :=
  { fns := fullFns, externs := [], exits := [] }

theorem full_cong_find_wf : Func.Wf full_cong_find_body := by t_wf_reify
theorem full_cong_merge_wf : Func.Wf full_cong_merge_body := by t_wf_reify
theorem full_has_ternary_wf : Func.Wf full_has_ternary_body := by t_wf_reify
theorem full_sort_u32_wf : Func.Wf full_sort_u32_body := by t_wf_reify
theorem full_cong_extract_ite_wf : Func.Wf full_cong_extract_ite_body := by t_wf_reify
theorem full_cong_emit_xor_wf : Func.Wf full_cong_emit_xor_body := by t_wf_reify
theorem full_cong_try_xor_ite_wf : Func.Wf full_cong_try_xor_ite_body := by t_wf_reify
theorem full_cong_extract_wf : Func.Wf full_cong_extract_body := by t_wf_reify
theorem full_cong_hash_step_wf : Func.Wf full_cong_hash_step_body := by t_wf_reify
theorem full_congruence_wf : Func.Wf full_congruence_body := by t_wf_reify
theorem full_sweep_add_cl_wf : Func.Wf full_sweep_add_cl_body := by t_wf_reify
theorem full_sweep_cone_wf : Func.Wf full_sweep_cone_body := by t_wf_reify
theorem full_sweep_dpll_wf : Func.Wf full_sweep_dpll_body := by t_wf_reify
theorem full_sweep_refine_wf : Func.Wf full_sweep_refine_body := by t_wf_reify
theorem full_sweep_seed_sim_wf : Func.Wf full_sweep_seed_sim_body := by t_wf_reify
theorem full_sweep_var_wf : Func.Wf full_sweep_var_body := by t_wf_reify
theorem full_sweep_sat_wf : Func.Wf full_sweep_sat_body := by t_wf_reify
theorem full_fwd_dedup_bins_wf : Func.Wf full_fwd_dedup_bins_body := by t_wf_reify
theorem full_fwd_check_cl_wf : Func.Wf full_fwd_check_cl_body := by t_wf_reify
theorem full_forward_sub_wf : Func.Wf full_forward_sub_body := by t_wf_reify
theorem full_bve_collect_wf : Func.Wf full_bve_collect_body := by t_wf_reify
theorem full_bve_mark_and_wf : Func.Wf full_bve_mark_and_body := by t_wf_reify
theorem full_bve_gates_wf : Func.Wf full_bve_gates_body := by t_wf_reify
theorem full_bve_resolve_pair_wf : Func.Wf full_bve_resolve_pair_body := by t_wf_reify
theorem full_bve_weaken_wf : Func.Wf full_bve_weaken_body := by t_wf_reify
theorem full_bve_try_bce_wf : Func.Wf full_bve_try_bce_body := by t_wf_reify
theorem full_bve_commit_res_wf : Func.Wf full_bve_commit_res_body := by t_wf_reify
theorem full_bve_ext_need_wf : Func.Wf full_bve_ext_need_body := by t_wf_reify
theorem full_bve_var_wf : Func.Wf full_bve_var_body := by t_wf_reify
theorem full_init_fresh_var_wf : Func.Wf full_init_fresh_var_body := by t_wf_reify
theorem full_bva_try_lit_wf : Func.Wf full_bva_try_lit_body := by t_wf_reify
theorem full_factor_wf : Func.Wf full_factor_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify
theorem full_preprocess_wf : Func.Wf full_preprocess_body := by t_wf_reify
theorem full_simplify_wf : Func.Wf full_simplify_body := by t_wf_reify
theorem full_search_wf : Func.Wf full_search_body := by t_wf_reify
theorem kissat_solve_bytes_full_wf : Func.Wf kissat_solve_bytes_body := by t_wf_reify

theorem full4_fns_wf : ∀ f ∈ full4_fns, f.Wf := by
  simp only [full4_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_cong_find_wf, full_cong_merge_wf, full_has_ternary_wf, full_sort_u32_wf,
    full_cong_extract_ite_wf, full_cong_emit_xor_wf, full_cong_try_xor_ite_wf,
    full_cong_extract_wf, full_cong_hash_step_wf, full_congruence_wf, full_sweep_add_cl_wf,
    full_sweep_cone_wf, full_sweep_dpll_wf, full_sweep_refine_wf, full_sweep_seed_sim_wf,
    full_sweep_var_wf, full_sweep_sat_wf, full_fwd_dedup_bins_wf,
    full_fwd_check_cl_wf, full_forward_sub_wf, full_bve_collect_wf, full_bve_mark_and_wf,
    full_bve_gates_wf, full_bve_resolve_pair_wf, full_bve_weaken_wf, full_bve_try_bce_wf,
    full_bve_commit_res_wf, full_bve_ext_need_wf, full_bve_var_wf, full_init_fresh_var_wf,
    full_bva_try_lit_wf, full_factor_wf, full_probe_wf, full_eliminate_wf, full_preprocess_wf,
    full_simplify_wf, full_search_wf, kissat_solve_bytes_full_wf⟩

theorem fullFns_wf : ∀ f ∈ fullFns, f.Wf := by
  intro f hf
  simp only [fullFns, List.mem_append] at hf
  rcases hf with (((h | h) | h) | h) | h
  · exact dimacsFns_wf f h
  · exact full1_fns_wf f h
  · exact full2_fns_wf f h
  · exact full3_fns_wf f h
  · exact full4_fns_wf f h

theorem full_acyclic : fullModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full
