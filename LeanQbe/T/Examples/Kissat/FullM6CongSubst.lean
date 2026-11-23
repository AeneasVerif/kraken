module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M6 Congruence Closure & 2-Round Substitute (`FullM6CongSubst`)

Standalone `FullHdr`-free (`144`-word layout, zero `Full1..3` / `FullM4*` / `FullM5*` edits)
implementation of dense congruence closure, 2-round substitution, and OOM/dedup
safety:
1. **Single-pass `wvec` Tarjan SCC & 2-round `substitute`**:
   - `full_tarjan_scc`: folds pass-2 lowlink scan into the single `wvec[nl]` DFS traversal while
     zeroing `tarjan_mark` and `tarjan_reach` on exit.
   - `full_subst_rewrite_bins` / `full_subst_rewrite_ar`: `lit_mark` bit-1 binary dedup + clean
     `h->oom` abort without false `20ULL` UNSAT returns.
   - `full_substitute`: 2-round fixpoint (`round < 2ULL`), rewrites if `ucnt > 0 || subst > 0`,
     runs `full_arena_sweep` before `full_propagate`.
2. **Dense Congruence Closure**:
   - `full_cong_count_bins`: populates `negbincount[0..nlits)` in `work_stk1` (`O(nlits + bins)`).
   - `full_cong_extract_binaries`: `negbincount`-filtered, ticks-bounded ternary resolution.
   - `full_cong_find_units_equivs`: dense binary `find_units` + `find_equivalences` before gating.
   - `full_cong_extract`: `negbincount` AND filter + widened `sz <= 32` non-breaking LHS loop +
     canonical `arity <= 4` XOR gate detection (`sz in 3..5`, `large_deg` filter) + normalized ITE.
   - `full_cong_worklist`: true FIFO bucketed occurrence-list worklist in `scratch_buf` (with bit-
     packed `[slot << 24 | g, next]` nodes, up to 4x HT rehash, immutable `scr[0..g_len)`), shared
     with `full_cong_eval_gate` supporting `arity <= 31` AND, `arity 2..4` XOR, and normalized ITE.
   - `full_cong_fwd_subsume`: dense forward subsumption modulo `repr` in strict `(sz, cref)` order.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6CongSubst "
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

#define PH_GARB     0x00080000u
#define PH_RED      0x00400000u
#define PH_SHRK     0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE   1u
#define FL_SUBST    4u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern bool full_tarjan_pop_scc(FullHdr *h, u32 root_lit, u32 lit, u32 mark_root);
extern bool full_subst_elim_vars(FullHdr *h, u64 ucnt);
extern u32 full_cong_find(u32 *repr, u32 l);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c);
extern void full_sort_u32(u32 *arr, u32 n);
extern u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep);
extern u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep);

u64 full_tarjan_scc(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *scc = (u32 *)h->work_stk1;
  u32 *dv = (u32 *)h->work_stk2; u32 *dpos = (u32 *)h->wsort;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *fl = (u32 *)h->flags;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = 0xFFFFFFFFu; tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL; }
  u32 reached = 0u; h->tmp_cnt = 0ULL; h->res_sz = 0ULL;
  u64 root = 0ULL;
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
          dpos[dsp - 1ULL] = pos + 1u;
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u) {
            if (tmk[ot] == 0u) {
              reached = reached + 1u; tmk[ot] = reached; trc[ot] = reached;
              scc[h->tmp_cnt] = ot; h->tmp_cnt = h->tmp_cnt + 1ULL;
              dv[dsp] = ot; dpos[dsp] = 0u; dsp = dsp + 1ULL;
            } else if (trc[ot] < trc[lit]) {
              trc[lit] = trc[ot];
            }
          }
          continue;
        }
        u32 rlit = trc[lit];
        dsp = dsp - 1ULL;
        if (rlit != tmk[lit]) {
          trc[lit] = rlit;
          if (dsp > 0ULL) {
            u32 par = dv[dsp - 1ULL];
            if (rlit < trc[par]) { trc[par] = rlit; }
          }
        } else {
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

bool full_subst_rewrite_bins(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark;
  u32 *pa = (u32 *)h->work_stk1; u32 *pb = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u32 rl = repr[l]; u64 pn = 0ULL; bool ovf = false;
    u64 p = off; u64 q = off; u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK; u32 rot = ((u64)ot < nlits) ? repr[ot] : ot;
      if (rl == (u32)l && rot == ot) {
        if ((lm[ot] & (u8)1) == (u8)0) {
          lm[ot] = lm[ot] | (u8)1; wstk[q] = w0; q = q + 1ULL;
        } else if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if (l < (u64)ot) {
          if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
          if (rl != (rot ^ 1u)) {
            if ((u64)rot < nlits) {
              if ((lm[rot] & (u8)2) == (u8)0) {
                if (pn < nlits) {
                  lm[rot] = lm[rot] | (u8)2; pa[pn] = rl; pb[pn] = rot; pn = pn + 1ULL;
                } else { ovf = true; }
              }
            } else { ovf = true; }
          }
        }
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = 0ULL;
    while (c < pn) { lm[pb[c]] = (u8)0; c = c + 1ULL; }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    if (ovf) { h->oom = 1ULL; return true; }
    c = 0ULL;
    while (c < pn) {
      if (pa[c] == pb[c]) { if (!full_add_unit(h, pa[c])) { return false; } }
      else {
        u64 br = full_add_bin(h, pa[c], pb[c]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
      c = c + 1ULL;
    }
    l = l + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_ar(FullHdr *h) {
  if (h->oom != 0ULL) { return true; }
  u32 *ar = (u32 *)h->arena; u32 *repr = (u32 *)h->repr;
  u8 *lm = (u8 *)h->lit_mark; u64 nlits = h->cur_vars << 1;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool chg = false; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k];
      if ((u64)l < nlits && repr[l] != l) { chg = true; break; }
      k = k + 1u;
    }
    if (!chg) { p = np; continue; }
    bool taut = false; u32 nsz = 0u; k = 0u;
    while (k < sz) {
      u32 rl = repr[ar[p + 3ULL + (u64)k]];
      if (lm[rl ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rl] == (u8)0) { lm[rl] = (u8)1; ar[p + 3ULL + (u64)nsz] = rl; nsz = nsz + 1u; }
      k = k + 1u;
    }
    k = 0u; while (k < nsz) { lm[ar[p + 3ULL + (u64)k]] = (u8)0; k = k + 1u; }
    if (taut || nsz <= 2u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (!taut && nsz == 1u && !full_add_unit(h, ar[p + 3ULL])) { return false; }
      if (!taut && nsz == 2u) {
        u64 br = full_add_bin(h, ar[p + 3ULL], ar[p + 4ULL]);
        if (br == 20ULL) { return false; }
        if (br == 2ULL || h->oom != 0ULL) { h->oom = 1ULL; return true; }
      }
    } else if (nsz < sz) {
      ar[p + 2ULL] = nsz; ar[p + 1ULL] = 2u;
      if ((hdr & PH_SHRK) == 0u) {
        ar[p] = hdr | PH_SHRK; ar[p + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      }
    }
    p = np;
  }
  return true;
}

u64 full_substitute(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->num_binary == 0ULL || h->oom != 0ULL) { return 1ULL; }
  u64 round = 0ULL;
  while (round < 2ULL && h->inconsistent == 0ULL && h->oom == 0ULL) {
    u64 before = h->subst_cnt;
    u64 ucnt = full_tarjan_scc(h);
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (!full_subst_elim_vars(h, ucnt)) { return 20ULL; }
    if (ucnt == 0ULL && h->subst_cnt == before) { break; }
    if (!full_subst_rewrite_bins(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    if (!full_subst_rewrite_ar(h)) { return 20ULL; }
    if (h->oom != 0ULL) { return 1ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL || h->oom != 0ULL) { return 1ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    round = round + 1ULL;
  }
  return 1ULL;
}

bool full_cong_merge(FullHdr *h, u32 a, u32 b) {
  u32 *repr = (u32 *)h->repr;
  u32 ra = full_cong_find(repr, a); u32 rb = full_cong_find(repr, b);
  if (ra == rb) { return false; }
  if (ra == (rb ^ 1u)) { h->inconsistent = 1ULL; return true; }
  if (ra > rb) { u32 t = ra; ra = rb; rb = t; }
  repr[rb] = ra; repr[rb ^ 1u] = ra ^ 1u;
  u64 st1 = full_add_bin(h, ra ^ 1u, rb);
  if (st1 == 20ULL) { h->inconsistent = 1ULL; return true; }
  if (st1 == 2ULL) {
    h->oom = 0ULL; h->ant_sz = 1ULL;
  } else {
    u64 st2 = full_add_bin(h, ra, rb ^ 1u);
    if (st2 == 20ULL) { h->inconsistent = 1ULL; return true; }
    if (st2 == 2ULL) { h->oom = 0ULL; h->ant_sz = 1ULL; }
  }
  h->cong_cnt = h->cong_cnt + 1ULL;
  return true;
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
    if (e != 0xFFFFFFFFu && e != (t ^ 1u) && full_has_ternary(h, c, e ^ 1u, y)) {
      if ((c & 1u) != 0u) { u32 tmp = t; t = e; e = tmp; c = c ^ 1u; }
      if ((t & 1u) != 0u) { y = y ^ 1u; t = t ^ 1u; e = e ^ 1u; }
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

bool full_cong_has_clause_k(FullHdr *h, u32 k) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *lm = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  if (k < 3u || k > 5u || (u64)k > h->cur_vars) { return false; }
  u32 min_l = tmp[0]; u32 min_d = wvec[((u64)min_l << 1) + 1ULL];
  u32 i = 0u;
  while (i < k) {
    u32 tl = tmp[i];
    lm[tl] = (u8)(i + 1u);
    u32 d = wvec[((u64)tl << 1) + 1ULL];
    if (d < min_d) { min_d = d; min_l = tl; }
    i = i + 1u;
  }
  bool res = false; u32 full_m = (1u << k) - 1u;
  u64 off = (u64)wvec[(u64)min_l << 1]; u64 end = off + (u64)wvec[((u64)min_l << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < k) { continue; }
    bool ok = true; u32 mask = 0u; u32 j = 0u;
    while (j < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)j];
      i8 cv = vals[cl];
      if (cv > (i8)0) { ok = false; break; }
      if (cv == (i8)0) {
        u8 mk = lm[cl];
        if (mk == (u8)0) { ok = false; break; }
        mask = mask | (1u << ((u32)mk - 1u));
      }
      j = j + 1u;
    }
    if (ok && mask == full_m) { res = true; break; }
  }
  i = 0u;
  while (i < k) { lm[tmp[i]] = (u8)0; i = i + 1u; }
  return res;
}

u64 full_cong_extract_xor_k(FullHdr *h, u32 k, u32 neg_p, u64 g_len, u64 g_cap) {
  if (k < 3u || k > 5u || (u64)k > h->cur_vars) { return g_len; }
  u64 need_words = (u64)k * (u64)(k + 1u);
  if (g_len + need_words > g_cap) { return g_len; }
  u32 *base = (u32 *)h->work_stk2; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec; u32 *nbc = (u32 *)h->work_stk1;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = 0u; u32 j = 0u;
  while (j < k) {
    u32 bj = base[j];
    if (bj > mx) { mx = bj; }
    u32 bi = 0u;
    while (bi < j) {
      if ((base[bi] >> 1) == (bj >> 1)) { return g_len; }
      bi = bi + 1u;
    }
    j = j + 1u;
  }
  j = 0u;
  while (j < k) {
    u32 bj = base[j];
    if ((bj & 1u) != 0u && bj != mx) { return g_len; }
    j = j + 1u;
  }
  u32 needed_cl = 1u << (k - 2u);
  j = 0u;
  while (j < k) {
    u32 pl = base[j] & (~1u); u32 nl = pl | 1u;
    u32 wp = wvec[((u64)pl << 1) + 1ULL]; u32 wn = wvec[((u64)nl << 1) + 1ULL];
    u32 bp = nbc[pl ^ 1u]; u32 bn = nbc[nl ^ 1u];
    u32 lp = (wp > bp) ? ((wp - bp) >> 1) : 0u;
    u32 ln = (wn > bn) ? ((wn - bn) >> 1) : 0u;
    if (lp < needed_cl || ln < needed_cl) { return g_len; }
    j = j + 1u;
  }
  u32 lim = 1u << k;
  u32 mask = 1u;
  while (mask < lim) {
    u32 pop = 0u; u32 b = 0u;
    while (b < k) { pop = pop ^ ((mask >> b) & 1u); b = b + 1u; }
    if (pop == 0u) {
      b = 0u;
      while (b < k) { tmp[b] = base[b] ^ ((mask >> b) & 1u); b = b + 1u; }
      if (!full_cong_has_clause_k(h, k)) { return g_len; }
    }
    mask = mask + 1u;
  }
  u32 arity = k - 1u; u32 sign = 1u ^ (neg_p & 1u);
  j = 0u;
  while (j < k) {
    u32 lhs = (base[j] & (~1u)) | sign;
    scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | arity;
    u32 rk = 0u; u32 i = 0u;
    while (i < k) {
      if (i != j) { tmp[rk] = base[i] & (~1u); rk = rk + 1u; }
      i = i + 1u;
    }
    full_sort_u32(tmp, arity);
    i = 0u;
    while (i < arity) { scr[g_len + 2ULL + (u64)i] = tmp[i]; i = i + 1u; }
    g_len = g_len + 2ULL + (u64)arity;
    j = j + 1u;
  }
  return g_len;
}

u64 full_cong_try_xor_ite(FullHdr *h, u32 a, u32 b, u32 c, u64 g_len, u64 g_cap) {
  if ((a >> 1) == (b >> 1) || (a >> 1) == (c >> 1) || (b >> 1) == (c >> 1)) { return g_len; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mx = (a > b) ? a : b;
  if (c > mx) { mx = c; }
  if (((a & 1u) == 0u || a == mx) && ((b & 1u) == 0u || b == mx) &&
      ((c & 1u) == 0u || c == mx) &&
      full_has_ternary(h, a, b ^ 1u, c ^ 1u) && full_has_ternary(h, a ^ 1u, b, c ^ 1u) &&
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
    ng = full_cong_extract_ite(h, a ^ 1u, c ^ 1u, b, g_len);
    if (ng > g_len) { return ng; }
  }
  if (full_has_ternary(h, b, a ^ 1u, c ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, b ^ 1u, a ^ 1u, c, g_len);
    if (ng > g_len) { return ng; }
    ng = full_cong_extract_ite(h, b ^ 1u, c ^ 1u, a, g_len);
    if (ng > g_len) { return ng; }
  }
  if (full_has_ternary(h, c, a ^ 1u, b ^ 1u)) {
    u64 ng = full_cong_extract_ite(h, c ^ 1u, a ^ 1u, b, g_len);
    if (ng > g_len) { return ng; }
    ng = full_cong_extract_ite(h, c ^ 1u, b ^ 1u, a, g_len);
    if (ng > g_len) { return ng; }
  }
  return g_len;
}

void full_cong_count_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *nbc = (u32 *)h->work_stk1;
  u64 l = 0ULL;
  while (l < nlits) { nbc[l] = 0u; l = l + 1ULL; }
  l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    u64 p = off; u32 bc = 0u;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) { bc = bc + 1u; p = p + 1ULL; }
      else { p = p + 2ULL; }
    }
    nbc[l ^ 1ULL] = bc;
    l = l + 1ULL;
  }
}

bool full_cong_eb_match(FullHdr *h, u32 x, u32 l, u32 k) {
  u32 *nbc = (u32 *)h->work_stk1;
  if (nbc[x] == 0u) { return false; }
  return full_has_bin(h, x ^ 1u, l) || full_has_bin(h, x ^ 1u, k);
}

u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  full_cong_count_bins(h);
  u64 alen = h->arena_len; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 p = 0ULL; u64 ticks = 0ULL;
  while (p < alen && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz == 3u) {
      u32 a = ar[p + 3ULL]; u32 b = ar[p + 4ULL]; u32 c = ar[p + 5ULL];
      if (vals[a] == (i8)0 && vals[b] == (i8)0 && vals[c] == (i8)0) {
        u32 l = 0u; u32 k = 0u; bool found = false;
        if (full_cong_eb_match(h, a, b, c)) { l = b; k = c; found = true; }
        else if (full_cong_eb_match(h, b, a, c)) { l = a; k = c; found = true; }
        else if (full_cong_eb_match(h, c, a, b)) { l = a; k = b; found = true; }
        if (found && !full_has_bin(h, l, k)) {
          ticks = ticks + 2ULL;
          u64 st = full_add_bin(h, l, k);
          if (st == 20ULL) { return 20ULL; }
          if (st == 2ULL) { h->oom = 0ULL; h->ant_sz = 1ULL; break; }
        }
      }
    }
    p = np;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_find_units_equivs(FullHdr *h) {
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u8 *lm = (u8 *)h->lit_mark; i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *fl = (u32 *)h->flags;
  u64 v = 0ULL;
  while (v < cv && h->inconsistent == 0ULL) {
    if ((fl[v] & FL_ACTIVE) == 0u || vals[v << 1] != (i8)0) { v = v + 1ULL; continue; }
    u64 sign = 0ULL;
    while (sign < 2ULL && vals[v << 1] == (i8)0 && h->inconsistent == 0ULL) {
      u32 lit = (u32)((v << 1) | sign);
      u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      bool found_u = false;
      u64 p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits) {
          if (ot == lit || lm[ot ^ 1u] != (u8)0) { found_u = true; break; }
          lm[ot] = (u8)1;
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits) { lm[ot] = (u8)0; }
      }
      if (found_u) {
        if (!full_add_unit(h, lit)) { return 20ULL; }
        h->cong_cnt = h->cong_cnt + 1ULL;
      }
      sign = sign + 1ULL;
    }
    v = v + 1ULL;
  }
  v = 0ULL;
  while (v < cv && h->inconsistent == 0ULL) {
    if ((fl[v] & FL_ACTIVE) == 0u || vals[v << 1] != (i8)0) { v = v + 1ULL; continue; }
    u32 lit = (u32)(v << 1);
    u64 off = (u64)wvec[(u64)lit << 1]; u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
    u64 p = off; bool any = false;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
      p = p + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits && (u64)(ot >> 1) > v) { lm[ot] = (u8)1; any = true; }
    }
    u64 mcnt = 0ULL;
    if (any) {
      u32 nlit = lit ^ 1u;
      u64 noff = (u64)wvec[(u64)nlit << 1]; u64 nend = noff + (u64)wvec[((u64)nlit << 1) + 1ULL];
      p = noff;
      while (p < nend) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && (u64)(ot >> 1) > v && lm[ot ^ 1u] == (u8)1) {
          lm[ot ^ 1u] = (u8)3;
          if (mcnt < cv) { tmp[mcnt] = ot; mcnt = mcnt + 1ULL; }
        }
      }
      p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
        p = p + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && (u64)(ot >> 1) > v) { lm[ot] = (u8)0; }
      }
      u64 k = 0ULL;
      while (k < mcnt && h->inconsistent == 0ULL) {
        if (full_cong_equiv_fold(h, lit, tmp[k], 1u) == 2ULL) { return 20ULL; }
        k = k + 1ULL;
      }
    }
    v = v + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim) {
  full_cong_count_bins(h);
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *nbc = (u32 *)h->work_stk1; u32 *base = (u32 *)h->work_stk2;
  i8 *vals = (i8 *)h->values; u64 cv = h->cur_vars;
  u64 p = 0ULL; u64 g_len = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && g_len + 34ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u && sz <= 32u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 neg_p = 0u; bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if ((u64)usz < cv) { base[usz] = l; usz = usz + 1u; }
          else { sat = true; break; }
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if ((l & 1u) != 0u) { neg_p = neg_p ^ 1u; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 3u && usz <= 32u && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (max_nbc >= arity) {
          u32 i = 0u;
          while (i < usz && g_len + 2ULL + (u64)arity <= g_cap) {
            u32 lhs = base[i];
            if (nbc[lhs] >= arity) {
              bool ok = true; u32 j = 0u;
              while (j < usz) {
                if (j != i && !full_has_bin(h, lhs ^ 1u, base[j] ^ 1u)) { ok = false; break; }
                j = j + 1u;
              }
              if (ok) {
                scr[g_len] = lhs; scr[g_len + 1ULL] = arity;
                u32 rk = 0u; j = 0u;
                while (j < usz) {
                  if (j != i) { scr[g_len + 2ULL + (u64)rk] = base[j] ^ 1u; rk = rk + 1u; }
                  j = j + 1u;
                }
                g_len = g_len + 2ULL + (u64)arity;
              }
            }
            i = i + 1u;
          }
        }
        if (usz == 3u && g_len + 14ULL <= g_cap) {
          g_len = full_cong_try_xor_ite(h, base[0], base[1], base[2], g_len, g_cap);
          ticks = ticks + 4ULL;
        } else if (usz >= 4u && usz <= 5u && g_len + 25ULL <= g_cap) {
          g_len = full_cong_extract_xor_k(h, usz, neg_p, g_len, g_cap);
          ticks = ticks + 8ULL;
        }
      }
    }
    p = np;
  }
  return g_len;
}

bool full_cong_and_match(FullHdr *h, u32 ent, u32 ua) {
  if (ua < 2u || ua > 31u) { return false; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  u32 mask = 0u; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { return false; }
    if (ev == (i8)0) {
      bool found = false; u32 k = 0u;
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

u32 full_cong_xor_match(FullHdr *h, u32 ent, u32 ua) {
  if (ua < 2u || ua > 4u || h->cur_vars < 2ULL || (u64)ua > h->cur_vars) { return 0xFFFFFFFFu; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ep = (u32 *)h->min_clr;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  if (ea < 2u || ea > 4u || (u64)ea > h->cur_vars) { return 0xFFFFFFFFu; }
  u32 eflip = 0u; u32 ena = 0u; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev != (i8)0) {
      if (ev > (i8)0) { eflip = eflip ^ 1u; }
    } else {
      eflip = eflip ^ (er & 1u);
      ep[ena] = er & (~1u);
      ena = ena + 1u;
    }
    j = j + 1u;
  }
  if (ena < ua) { return 0xFFFFFFFFu; }
  if (ena > 1u) { full_sort_u32(ep, ena); }
  u32 eua = 0u; j = 0u;
  while (j < ena) {
    if (j + 1u < ena && ep[j] == ep[j + 1u]) { j = j + 2u; }
    else { ep[eua] = ep[j]; eua = eua + 1u; j = j + 1u; }
  }
  if (eua != ua) { return 0xFFFFFFFFu; }
  j = 0u;
  while (j < ua) { if (ep[j] != tmp[j]) { return 0xFFFFFFFFu; } j = j + 1u; }
  return full_cong_find(repr, scr[ent]) ^ eflip;
}

void full_cong_enq_var(FullHdr *h, u64 ctrl_off, u32 v) {
  if (ctrl_off >= h->scratch_cap || (u64)v >= h->cur_vars) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 occ_bkt = scr[ctrl_off];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL];
  u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u32 b = v & (occ_bkt - 1u);
  if (scr[inq_off + (u64)b] == 0u) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    if (q_len < occ_bkt) {
      u32 tail = (q_head + q_len) & (occ_bkt - 1u);
      scr[inq_off + (u64)b] = 1u;
      scr[q_off + (u64)tail] = b;
      scr[ctrl_off + 5ULL] = q_len + 1u;
    }
  }
}

u64 full_cong_eval_gate(FullHdr *h, u64 g, u64 ht_off, u64 ht_sz, u32 next_ep, u64 ctrl_off) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *trl = (u32 *)h->trail;
  u32 raw_lhs = scr[g]; u32 meta = scr[g + 1ULL];
  u32 tag = meta >> 28; u32 arity = meta & 0xFFu;
  if (arity < 2u || arity > 31u || (u64)arity > h->cur_vars) { return 0ULL; }
  u32 lhs = full_cong_find(repr, raw_lhs);
  u32 i = 0u;
  while (i < arity) { tmp[i] = full_cong_find(repr, scr[g + 2ULL + (u64)i]); i = i + 1u; }
  u64 ht_lim = (ht_sz * 3ULL) >> 2;
  u64 te0 = h->trail_end;
  u32 htag = tag; u32 harity = arity; bool need_hash = true; bool changed = false;
  if (tag == 0u) {
    bool has_false = false; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv < (i8)0) { has_false = true; break; }
      if (rv == (i8)0) { tmp[na] = r; na = na + 1u; }
      i = i + 1u;
    }
    if (has_false) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (na == 0u) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else {
      if (na > 1u) { full_sort_u32(tmp, na); }
      bool clash = false; u32 ua = 0u; u32 si = 0u;
      while (si < na) {
        u32 cur = tmp[si]; si = si + 1u;
        if (cur == (lhs ^ 1u)) { clash = true; break; }
        if (ua == 0u) { tmp[0] = cur; ua = 1u; }
        else {
          u32 prev = tmp[ua - 1u];
          if (cur == prev) { continue; }
          if (cur == (prev ^ 1u)) { clash = true; break; }
          tmp[ua] = cur; ua = ua + 1u;
        }
      }
      if (clash) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 0u) {
        u64 uf = full_cong_unit_fold(h, lhs, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (ua == 1u) {
        u32 r0 = tmp[0];
        u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
        }
        need_hash = false;
      } else if (vals[lhs] > (i8)0) {
        u32 k = 0u;
        while (k < ua) {
          u64 uf = full_cong_unit_fold(h, tmp[k], next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          k = k + 1u;
        }
        need_hash = false;
      } else if (ua > 31u) {
        need_hash = false;
      } else {
        harity = ua;
      }
    }
  } else if (tag == 1u && arity >= 2u && arity <= 4u) {
    u32 flip = 0u; u32 na = 0u; i = 0u;
    while (i < arity) {
      u32 r = tmp[i]; i8 rv = vals[r];
      if (rv != (i8)0) {
        if (rv > (i8)0) { flip = flip ^ 1u; }
      } else {
        flip = flip ^ (r & 1u);
        tmp[na] = r & (~1u); na = na + 1u;
      }
      i = i + 1u;
    }
    lhs = lhs ^ flip;
    if (na > 1u) { full_sort_u32(tmp, na); }
    u32 ua = 0u; i = 0u;
    while (i < na) {
      if (i + 1u < na && tmp[i] == tmp[i + 1u]) { i = i + 2u; }
      else { tmp[ua] = tmp[i]; ua = ua + 1u; i = i + 1u; }
    }
    if (ua == 0u) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (ua == 1u) {
      u32 r0 = tmp[0];
      u64 ef = full_cong_equiv_fold(h, lhs, r0, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, r0 >> 1);
      }
      need_hash = false;
    } else if (ua == 2u && vals[lhs] != (i8)0) {
      u32 a0 = (vals[lhs] > (i8)0) ? (tmp[0] ^ 1u) : tmp[0]; u32 a1 = tmp[1];
      u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
      }
      need_hash = false;
    } else {
      harity = ua;
    }
  } else if (tag == 2u && arity == 3u) {
    u32 c = tmp[0]; u32 t = tmp[1]; u32 e = tmp[2];
    i8 vc = vals[c]; i8 vt = vals[t]; i8 ve = vals[e];
    if (vc != (i8)0) {
      u32 br = (vc > (i8)0) ? t : e;
      u64 ef = full_cong_equiv_fold(h, lhs, br, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, br >> 1);
      }
      need_hash = false;
    } else if (t == e) {
      u64 ef = full_cong_equiv_fold(h, lhs, t, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, t >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve < (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt < (i8)0 && ve > (i8)0) {
      u64 ef = full_cong_equiv_fold(h, lhs, c ^ 1u, next_ep);
      if (ef == 2ULL) { return 2ULL; }
      if (ef == 1ULL) {
        changed = true;
        full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, c >> 1);
      }
      need_hash = false;
    } else if (vt > (i8)0 && ve > (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else if (vt < (i8)0 && ve < (i8)0) {
      u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
      if (uf == 2ULL) { return 2ULL; }
      if (uf == 1ULL) { changed = true; }
      need_hash = false;
    } else {
      if ((c & 1u) != 0u) { c = c ^ 1u; u32 sw = t; t = e; e = sw; }
      if ((t & 1u) != 0u) { lhs = lhs ^ 1u; t = t ^ 1u; e = e ^ 1u; }
      tmp[0] = c; tmp[1] = t; tmp[2] = e;
    }
  } else {
    need_hash = false;
  }
  bool keep = false;
  if (need_hash && h->inconsistent == 0ULL) {
    keep = true;
    u64 hv = (u64)htag * 0x9E3779B1ULL + (u64)harity;
    i = 0u;
    while (i < harity) { hv = hv * 0x85EBCA77ULL + (u64)tmp[i] + 1ULL; i = i + 1u; }
    u64 slot = hv & (ht_sz - 1ULL); u64 probes = 0ULL; bool seen_self = false;
    while (probes < 64ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (!seen_self && h->res_sz < ht_lim) {
          scr[ht_off + slot] = (u32)g; h->res_sz = h->res_sz + 1ULL;
        }
        break;
      }
      if (ent == (u32)g) {
        seen_self = true; slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
        continue;
      }
      u32 em = scr[(u64)ent + 1ULL]; u32 etag = em >> 28;
      if (etag == htag) {
        bool matched = false; u32 match_lhs = scr[ent];
        if (htag == 0u) {
          matched = full_cong_and_match(h, ent, harity);
        } else if (htag == 1u) {
          u32 ml = full_cong_xor_match(h, ent, harity);
          if (ml != 0xFFFFFFFFu) { matched = true; match_lhs = ml; }
        } else if (htag == 2u && (em & 0xFFu) == 3u) {
          u32 ec = full_cong_find(repr, scr[(u64)ent + 2ULL]);
          u32 et = full_cong_find(repr, scr[(u64)ent + 3ULL]);
          u32 ee = full_cong_find(repr, scr[(u64)ent + 4ULL]);
          if ((ec & 1u) != 0u) { ec = ec ^ 1u; u32 sw = et; et = ee; ee = sw; }
          if ((et & 1u) != 0u) { match_lhs = match_lhs ^ 1u; et = et ^ 1u; ee = ee ^ 1u; }
          matched = (ec == tmp[0] && et == tmp[1] && ee == tmp[2]);
        }
        if (matched) {
          keep = false;
          u64 ef = full_cong_equiv_fold(h, lhs, match_lhs, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1);
            full_cong_enq_var(h, ctrl_off, match_lhs >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, lhs) >> 1);
            full_cong_enq_var(h, ctrl_off, full_cong_find(repr, match_lhs) >> 1);
          }
          break;
        }
      }
      slot = (slot + 1ULL) & (ht_sz - 1ULL); probes = probes + 1ULL;
    }
  }
  while (te0 < h->trail_end) {
    u32 tl = trl[te0];
    full_cong_enq_var(h, ctrl_off, tl >> 1);
    full_cong_enq_var(h, ctrl_off, full_cong_find(repr, tl) >> 1);
    te0 = te0 + 1ULL;
  }
  if (h->inconsistent != 0ULL) { return 2ULL; }
  return (changed ? 1ULL : 0ULL) | (keep ? 4ULL : 0ULL);
}

u64 full_cong_work_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz, u32 cur_ep) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark; u32 next_ep = cur_ep + 1u;
  bool changed = false; u64 work = 0ULL; u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL) {
    u32 raw_lhs = scr[g]; u32 meta = scr[g + 1ULL]; u32 arity = meta & 0xFFu;
    u64 next_g = g + 2ULL + (u64)arity;
    u32 lhs = full_cong_find(repr, raw_lhs);
    bool dirty = (tmk[raw_lhs >> 1] >= cur_ep) || (tmk[lhs >> 1] >= cur_ep);
    u32 i = 0u;
    while (i < arity && !dirty) {
      u32 raw_a = scr[g + 2ULL + (u64)i]; u32 ra = full_cong_find(repr, raw_a);
      if (tmk[raw_a >> 1] >= cur_ep || tmk[ra >> 1] >= cur_ep) { dirty = true; }
      i = i + 1u;
    }
    if (!dirty) { work = work + 1ULL; g = next_g; continue; }
    work = work + 4ULL;
    u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, next_ep, h->scratch_cap);
    if ((er & 2ULL) != 0ULL) { return (work << 2) | 2ULL; }
    if ((er & 1ULL) != 0ULL) { changed = true; }
    g = next_g;
  }
  u64 st = (h->inconsistent != 0ULL) ? 2ULL : (changed ? 1ULL : 0ULL);
  return (work << 2) | st;
}

u64 full_cong_worklist(FullHdr *h, u64 g_len, u64 ctrl_off, u64 tick_lim) {
  if (tick_lim > 0x7FFFFFFFFFFFFFFFULL) { tick_lim = 0x7FFFFFFFFFFFFFFFULL; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 occ_bkt = scr[ctrl_off]; u64 bkt_off = (u64)scr[ctrl_off + 1ULL];
  u64 inq_off = (u64)scr[ctrl_off + 2ULL]; u64 q_off = (u64)scr[ctrl_off + 3ULL];
  u64 ht_off = (u64)scr[ctrl_off + 6ULL]; u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  u64 i = 0ULL;
  while (i < (u64)occ_bkt) {
    scr[bkt_off + i] = 0xFFFFFFFFu; scr[inq_off + i] = 0u; i = i + 1ULL;
  }
  scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
  u64 occ_end = g_len; u64 ticks = 0ULL; u64 rehashes = 0ULL;
  u64 g = 0ULL;
  while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 arity = scr[g + 1ULL] & 0xFFu; u64 next_g = g + 2ULL + (u64)arity;
    ticks = ticks + 2ULL;
    u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, 2u, ctrl_off);
    if ((er & 2ULL) != 0ULL) { return 20ULL; }
    if ((er & 4ULL) != 0ULL && occ_end + (u64)(1u + arity) * 2ULL <= ctrl_off) {
      u32 rl = full_cong_find(repr, scr[g]); u32 b0 = (rl >> 1) & (occ_bkt - 1u);
      scr[occ_end] = (u32)g; scr[occ_end + 1ULL] = scr[bkt_off + (u64)b0];
      scr[bkt_off + (u64)b0] = (u32)occ_end; occ_end = occ_end + 2ULL;
      u32 s = 0u;
      while (s < arity) {
        u32 rr = full_cong_find(repr, scr[g + 2ULL + (u64)s]);
        u32 bs = (rr >> 1) & (occ_bkt - 1u);
        scr[occ_end] = ((s + 1u) << 24) | (u32)g;
        scr[occ_end + 1ULL] = scr[bkt_off + (u64)bs];
        scr[bkt_off + (u64)bs] = (u32)occ_end; occ_end = occ_end + 2ULL;
        s = s + 1u;
      }
    }
    g = next_g;
  }
  u32 ep = 3u;
  while ((scr[ctrl_off + 5ULL] > 0u) && h->inconsistent == 0ULL && ticks < tick_lim) {
    u32 q_head = scr[ctrl_off + 4ULL]; u32 q_len = scr[ctrl_off + 5ULL];
    u32 b = scr[q_off + (u64)q_head];
    scr[ctrl_off + 4ULL] = (q_head + 1u) & (occ_bkt - 1u);
    scr[ctrl_off + 5ULL] = q_len - 1u;
    scr[inq_off + (u64)b] = 0u;
    u32 nd = scr[bkt_off + (u64)b]; scr[bkt_off + (u64)b] = 0xFFFFFFFFu;
    while (nd != 0xFFFFFFFFu && h->inconsistent == 0ULL && ticks < tick_lim) {
      u32 entry = scr[nd]; u32 nxt = scr[(u64)nd + 1ULL];
      u64 gn = (u64)(entry & 0x00FFFFFFu); u32 slot_i = entry >> 24;
      ticks = ticks + 2ULL;
      u64 er = full_cong_eval_gate(h, gn, ht_off, ht_sz, ep, ctrl_off);
      if ((er & 2ULL) != 0ULL) { return 20ULL; }
      if ((er & 4ULL) != 0ULL) {
        u32 r_off = (slot_i == 0u) ? 0u : (1u + slot_i);
        u32 dst = full_cong_find(repr, scr[gn + (u64)r_off]);
        u32 b_dst = (dst >> 1) & (occ_bkt - 1u);
        scr[(u64)nd + 1ULL] = scr[bkt_off + (u64)b_dst];
        scr[bkt_off + (u64)b_dst] = nd;
      }
      nd = nxt;
    }
    if (h->res_sz * 4ULL >= ht_sz * 3ULL && rehashes < 4ULL && ticks < tick_lim) {
      i = 0ULL; while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL; rehashes = rehashes + 1ULL;
      g = 0ULL;
      while (g < g_len && h->inconsistent == 0ULL && ticks < tick_lim) {
        u32 arity = scr[g + 1ULL] & 0xFFu;
        ticks = ticks + 1ULL;
        u64 er = full_cong_eval_gate(h, g, ht_off, ht_sz, ep, ctrl_off);
        if ((er & 2ULL) != 0ULL) { return 20ULL; }
        g = g + 2ULL + (u64)arity;
      }
    }
    ep = ep + 1u;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim) {
  if (h->inconsistent != 0ULL || h->ant_sz != 0ULL) {
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 cv = h->cur_vars; u32 *repr = (u32 *)h->repr; u32 *fl = (u32 *)h->flags;
  u32 *mch = (u32 *)h->min_clr; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u64 i = 0ULL; while (i < cv) { mch[i] = 0u; i = i + 1ULL; }
  bool has_mch = false; i = 0ULL;
  while (i < cv) {
    if ((fl[i] & FL_ACTIVE) != 0u) {
      u32 lit = (u32)(i << 1); u32 r = full_cong_find(repr, lit);
      if (r != lit) { mch[i] = 1u; mch[r >> 1] = 1u; has_mch = true; }
    }
    i = i + 1ULL;
  }
  if (!has_mch) { return 1ULL; }
  u64 p = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && ticks < tick_lim && h->inconsistent == 0ULL) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { p = np; continue; }
    bool sat = false; bool taut = false; bool c_mch = false; bool ovf = false;
    u32 msz = 0u; u32 min_l = 0xFFFFFFFFu; u32 min_ld = 0xFFFFFFFFu; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k]; i8 lv = vals[l];
      if (lv > (i8)0) { sat = true; break; }
      if (lv < (i8)0) { k = k + 1u; continue; }
      if (mch[l >> 1] != 0u) { c_mch = true; }
      u32 wd = wvec[((u64)l << 1) + 1ULL];
      if (wd < min_ld) { min_ld = wd; min_l = l; }
      u32 r = full_cong_find(repr, l); i8 rv = vals[r];
      if (rv > (i8)0) { sat = true; break; }
      if (rv < (i8)0) { k = k + 1u; continue; }
      if (lm[r ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[r] == (u8)0) {
        if ((u64)msz < cv) { lm[r] = (u8)1; tmp[msz] = r; msz = msz + 1u; }
        else { ovf = true; break; }
      }
      k = k + 1u;
    }
    k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
    if (sat || taut) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      p = np; continue;
    }
    if (ovf) { p = np; continue; }
    if (msz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (msz == 1u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!full_add_unit(h, tmp[0])) { return 20ULL; }
      p = np; continue;
    }
    if (!c_mch) { p = np; continue; }
    u32 min_r = tmp[0]; u32 min_rd = wvec[((u64)min_r << 1) + 1ULL];
    k = 0u;
    while (k < msz) {
      u32 rk = tmp[k]; lm[rk] = (u8)1;
      u32 rd = wvec[((u64)rk << 1) + 1ULL];
      if (rd < min_rd) { min_rd = rd; min_r = rk; }
      k = k + 1u;
    }
    bool subsumed = false;
    k = 0u;
    while (k < msz && !subsumed) {
      u32 rk = tmp[k];
      u64 boff = (u64)wvec[(u64)rk << 1]; u64 bend = boff + (u64)wvec[((u64)rk << 1) + 1ULL];
      u64 bp = boff;
      while (bp < bend) {
        u32 w0 = wstk[bp];
        if ((w0 & PW_BIN_FLAG) == 0u) { bp = bp + 2ULL; continue; }
        bp = bp + 1ULL;
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < (cv << 1) && vals[ot] == (i8)0) {
          u32 ro = full_cong_find(repr, ot);
          if (vals[ro] == (i8)0 && lm[ro] != (u8)0) { subsumed = true; break; }
        }
      }
      k = k + 1u;
    }
    u32 pass = 0u;
    while (pass < 2u && !subsumed) {
      u32 wl = (pass == 0u) ? min_r : min_l;
      if (pass == 1u && min_l == min_r) { break; }
      if (wl != 0xFFFFFFFFu) {
        u64 woff = (u64)wvec[(u64)wl << 1]; u64 wend = woff + (u64)wvec[((u64)wl << 1) + 1ULL];
        u64 wp = woff;
        while (wp < wend && ticks < tick_lim) {
          u32 w0 = wstk[wp]; wp = wp + 1ULL;
          if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
          if (wp >= wend) { break; }
          u32 cr = wstk[wp]; wp = wp + 1ULL;
          ticks = ticks + 1ULL;
          if (cr == (u32)p) { continue; }
          u32 dhdr = ar[cr]; u32 dsz = ar[(u64)cr + 2ULL];
          if ((dhdr & (PH_GARB | PH_RED)) != 0u) { continue; }
          if (dsz > sz || (dsz == sz && cr >= (u32)p)) { continue; }
          bool dok = true; u32 dj = 0u;
          while (dj < dsz) {
            u32 ol = ar[(u64)cr + 3ULL + (u64)dj]; i8 ov = vals[ol];
            if (ov > (i8)0) { dok = false; break; }
            if (ov == (i8)0) {
              u32 ro = full_cong_find(repr, ol); i8 rov = vals[ro];
              if (rov > (i8)0) { dok = false; break; }
              if (rov == (i8)0 && lm[ro] == (u8)0) { dok = false; break; }
            }
            dj = dj + 1u;
          }
          if (dok) { subsumed = true; break; }
        }
      }
      pass = pass + 1u;
    }
    k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
    if (subsumed) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
    }
    p = np;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  h->ant_sz = 0ULL;
  if (full_cong_extract_binaries(h, tick_lim) == 20ULL) { h->ant_sz = 0ULL; return 20ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  if (full_cong_find_units_equivs(h) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  u64 ht_sz = 64ULL;
  while (ht_sz * 8ULL <= h->scratch_cap && ht_sz < 4096ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 occ_bkt = (ht_off >= 16384ULL) ? 512ULL : ((ht_off >= 2048ULL) ? 256ULL :
    ((ht_off >= 256ULL) ? 32ULL : 16ULL));
  u64 bkt_off = ht_off - occ_bkt;
  u64 inq_off = bkt_off - occ_bkt;
  u64 q_off = inq_off - occ_bkt;
  u64 ctrl_off = q_off - 8ULL;
  u64 g_cap = (ctrl_off * 3ULL) >> 2;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = full_cong_extract(h, g_cap, tick_lim);
  if (g_len > 0ULL && g_len <= ctrl_off) {
    i = 0ULL;
    while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    h->res_sz = 0ULL;
    scr[ctrl_off] = (u32)occ_bkt; scr[ctrl_off + 1ULL] = (u32)bkt_off;
    scr[ctrl_off + 2ULL] = (u32)inq_off; scr[ctrl_off + 3ULL] = (u32)q_off;
    scr[ctrl_off + 4ULL] = 0u; scr[ctrl_off + 5ULL] = 0u;
    scr[ctrl_off + 6ULL] = (u32)ht_off; scr[ctrl_off + 7ULL] = (u32)ht_sz;
    if (full_cong_worklist(h, g_len, ctrl_off, tick_lim) == 20ULL) {
      i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
      h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
    }
  }
  if (full_cong_fwd_subsume(h, tick_lim) == 20ULL) {
    i = 0ULL; while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
    h->res_sz = 0ULL; h->ant_sz = 0ULL; return 20ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL; h->ant_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

def m6CongSubstExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool]⟩
  , ⟨"full_set_inactive", [i64, i32, i32], []⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_subst_elim_vars", [i64, i64], [.bool]⟩
  , ⟨"full_cong_find", [i64, i32], [i32]⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_sort_u32", [i64, i32], []⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64]⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64]⟩ ]

def m6CongSubstModule : LeanQbe.T.Module :=
  { fns := m6CongSubst_fns, externs := m6CongSubstExterns, exits := [] }

theorem full_tarjan_scc_wf : Func.Wf full_tarjan_scc_body := by t_wf_reify
theorem full_subst_rewrite_bins_wf : Func.Wf full_subst_rewrite_bins_body := by t_wf_reify
theorem full_subst_rewrite_ar_wf : Func.Wf full_subst_rewrite_ar_body := by t_wf_reify
theorem full_substitute_wf : Func.Wf full_substitute_body := by t_wf_reify
theorem full_cong_merge_wf : Func.Wf full_cong_merge_body := by t_wf_reify
theorem full_cong_extract_ite_wf : Func.Wf full_cong_extract_ite_body := by t_wf_reify
theorem full_cong_emit_xor_wf : Func.Wf full_cong_emit_xor_body := by t_wf_reify
theorem full_cong_has_clause_k_wf : Func.Wf full_cong_has_clause_k_body := by t_wf_reify
theorem full_cong_extract_xor_k_wf : Func.Wf full_cong_extract_xor_k_body := by t_wf_reify
theorem full_cong_try_xor_ite_wf : Func.Wf full_cong_try_xor_ite_body := by t_wf_reify
theorem full_cong_count_bins_wf : Func.Wf full_cong_count_bins_body := by t_wf_reify
theorem full_cong_eb_match_wf : Func.Wf full_cong_eb_match_body := by t_wf_reify
theorem full_cong_extract_binaries_wf : Func.Wf full_cong_extract_binaries_body := by t_wf_reify
theorem full_cong_find_units_equivs_wf : Func.Wf full_cong_find_units_equivs_body := by t_wf_reify
theorem full_cong_extract_wf : Func.Wf full_cong_extract_body := by t_wf_reify
theorem full_cong_and_match_wf : Func.Wf full_cong_and_match_body := by t_wf_reify
theorem full_cong_xor_match_wf : Func.Wf full_cong_xor_match_body := by t_wf_reify
theorem full_cong_enq_var_wf : Func.Wf full_cong_enq_var_body := by t_wf_reify
theorem full_cong_eval_gate_wf : Func.Wf full_cong_eval_gate_body := by t_wf_reify
theorem full_cong_work_step_wf : Func.Wf full_cong_work_step_body := by t_wf_reify
theorem full_cong_worklist_wf : Func.Wf full_cong_worklist_body := by t_wf_reify
theorem full_cong_fwd_subsume_wf : Func.Wf full_cong_fwd_subsume_body := by t_wf_reify
theorem full_congruence_dense_wf : Func.Wf full_congruence_dense_body := by t_wf_reify

theorem m6CongSubst_fns_wf : ∀ f ∈ m6CongSubst_fns, f.Wf := by
  simp only [m6CongSubst_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_tarjan_scc_wf, full_subst_rewrite_bins_wf, full_subst_rewrite_ar_wf,
    full_substitute_wf, full_cong_merge_wf, full_cong_extract_ite_wf, full_cong_emit_xor_wf,
    full_cong_has_clause_k_wf, full_cong_extract_xor_k_wf, full_cong_try_xor_ite_wf,
    full_cong_count_bins_wf, full_cong_eb_match_wf, full_cong_extract_binaries_wf,
    full_cong_find_units_equivs_wf, full_cong_extract_wf, full_cong_and_match_wf,
    full_cong_xor_match_wf, full_cong_enq_var_wf, full_cong_eval_gate_wf,
    full_cong_work_step_wf, full_cong_worklist_wf, full_cong_fwd_subsume_wf,
    full_congruence_dense_wf⟩

theorem m6CongSubst_acyclic : m6CongSubstModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Splices `m6CongSubst_fns` onto a `FullM4`-compatible function list in topological order. -/
def spliceM6CongSubst (base : List Fn) : List Fn :=
  let byName (nm : String) : List Fn := m6CongSubst_fns.filter (fun f => f.name == nm)
  let preExtract :=
    [ "full_cong_has_clause_k", "full_cong_extract_xor_k",
      "full_cong_count_bins", "full_cong_eb_match", "full_cong_extract_binaries" ].flatMap byName
  let preWorkStep :=
    [ "full_cong_find_units_equivs", "full_cong_xor_match", "full_cong_enq_var",
      "full_cong_eval_gate", "full_cong_worklist", "full_cong_fwd_subsume" ].flatMap byName
  let ovNames : List String :=
    [ "full_tarjan_scc", "full_subst_rewrite_bins", "full_subst_rewrite_ar", "full_substitute",
      "full_cong_merge", "full_cong_extract_ite", "full_cong_emit_xor", "full_cong_try_xor_ite",
      "full_cong_extract", "full_cong_and_match", "full_cong_work_step", "full_congruence_dense" ]
  base.flatMap fun f =>
    let f' := if ovNames.contains f.name then (byName f.name).headD f else f
    if f.name == "full_cong_extract" then preExtract ++ [f']
    else if f.name == "full_cong_work_step" then preWorkStep ++ [f']
    else [f']

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
