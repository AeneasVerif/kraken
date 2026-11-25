/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.PatchModule
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullM8SweepV2
meta import LeanQbe.T.Examples.Kissat.FullM8CoreParity
meta import LeanQbe.T.Examples.Kissat.FullM7HotTernary
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Legal
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Kissat 4.0.4 Congruence Closure Parity (`FullFidelityCong`)

Purely additive C0 parity layer (`0` `FullHdr` word growth, `0` beyond-upstream heuristics,
`0` edits to existing `FullM6*`/`FullM7*`/`FullM8*` files) closing all four upstream Kissat 4.0.4
`congruence.c` algorithmic parity gaps (`GAP-CONG-01..04`) plus the P0 `BUG-CONG-00` quadratic
forward-subsumption bug:

1. **`GAP-CONG-01` (Wide AND gates up to arity `64`, `congruence.c:2526-2600`):**
   - `full_cong_extract`: scans clauses with `sz >= 3u` skipping root-falsified literals up to
     `usz <= 65u` (`arity <= 64u`), with upstream `min_nbc > 0u` O(1) filter.
   - `full_cong_and_match`: 64-bit `u64 mask` covering `2 <= ua <= 64` (UB-free `ua == 64`).
   - `full_cong_eval_gate` & `full_cong_ht_*_m7`: lift arity cap `31 -> 64`.
2. **`GAP-CONG-02` (4-literal XOR `k=3` inputs & normalization, `congruence.c:2744-2950`):**
   - `full_cong_emit_xor4`: dedicated 4-literal (`k=3` input) sorting-network XOR normalizer.
   - `full_cong_has_clause_k`: accepts any subsuming irredundant clause (binary or shorter large).
   - `full_cong_extract_xor_k`: uses `full_cong_emit_xor4` for `k == 4`, binary-inclusive degree
     guard, and exact `usz * (usz + 1)` capacity check in `full_cong_extract`.
   - `full_cong_eval_gate`: adds XOR LHS self-cancellation and ITE-to-AND/XOR simplification &
     rewriting (`congruence.c:1871-2080`).
3. **`GAP-CONG-03` (Dynamic scratch HT up to `1,048,576` / `1M` buckets, `congruence.c:398`):**
   - `full_congruence_dense`: extracts gates first, reserves `ht_max` up to `1,048,576` buckets
     when scratch capacity permits, and sizes initial `ht_sz` dynamically to `g_len`.
   - `full_cong_worklist`: doubles `ht_sz` in-place at `50%` load up to `min(1M, cap - ht_off)`,
     falling back to bounded stale-flush rehashing at `ht_max`.
   - `full_cong_ht_{init,grow,grow_clear,lookup,insert}_m7`: cap lifted `131,072 -> 1,048,576`.
4. **`GAP-CONG-04` + P0 `BUG-CONG-00` (Conditional equivalences & upstream forward subsumption):**
   - `full_cong_copy_condbin_m7`: handles `sz >= 3u` clauses with `3` unassigned literals.
   - `full_cong_merge_condeq_m7`: emits trivial conditional equivalences (`e == t`,
     `congruence.c:1362-1368`), immediately merged by `full_cong_eval_gate`.
   - `full_cong_fwd_subsume` + `full_cong_sift_pairs_fid` / `full_cong_sort_pairs_fid`:
     exact upstream `forward_subsume_matching_clauses` + `find_subsuming_clause`
     (`congruence.c:4347-4575`) over irredundant & redundant clauses, sorted ascending by
     `(msz, redundant)`, using initially-empty `repr`-indexed occurrence lists in idle
     `work_stk1`/`work_stk2`/`scratch_buf` with proper `ticks < tick_lim` guarding and ZERO
     unbounded sparse 2WL scanning (`BUG-CONG-00`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

kissat_c0! fidCong "
#define PH_GARB 0x00080000u
#define PH_RED 0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE 1u

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

extern u32 full_arena_next(FullHdr *h, u32 p);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 c);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern void full_sort_u32(u32 *a, u32 n);
extern u32 full_cong_find(u32 *repr, u32 l);
extern u64 full_cong_unit_fold(FullHdr *h, u32 lit, u32 next_ep);
extern u64 full_cong_equiv_fold(FullHdr *h, u32 a, u32 b, u32 next_ep);
extern void full_cong_count_bins(FullHdr *h);
extern u64 full_cong_extract_binaries(FullHdr *h, u64 tick_lim);
extern u64 full_cong_find_units_equivs(FullHdr *h);
extern u32 full_cong_xor_match(FullHdr *h, u32 ent, u32 ua);
extern void full_cong_enq_var(FullHdr *h, u64 ctrl_off, u32 v);
extern void full_cong_u64_sort_m7(u64 *a, u64 n);
extern u64 full_cong_extract_condeq_m7(u64 *cb, u64 m, u64 *ceq, u64 cap);

u64 full_cong_emit_xor(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2) {
  u32 lhs = ((x0 ^ 1u) & (~1u)) | (((x0 ^ 1u) ^ x1 ^ x2) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u);
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 2u;
  scr[g_len + 2ULL] = (r0 < r1) ? r0 : r1; scr[g_len + 3ULL] = (r0 < r1) ? r1 : r0;
  return g_len + 4ULL;
}

u64 full_cong_emit_xor4(u32 *scr, u64 g_len, u32 x0, u32 x1, u32 x2, u32 x3) {
  u32 lhs = (x0 & (~1u)) | ((1u ^ x0 ^ x1 ^ x2 ^ x3) & 1u);
  u32 r0 = x1 & (~1u); u32 r1 = x2 & (~1u); u32 r2 = x3 & (~1u);
  if (r0 > r1) { u32 t = r0; r0 = r1; r1 = t; }
  if (r1 > r2) { u32 t = r1; r1 = r2; r2 = t; }
  if (r0 > r1) { u32 t = r0; r0 = r1; r1 = t; }
  scr[g_len] = lhs; scr[g_len + 1ULL] = (1u << 28) | 3u;
  scr[g_len + 2ULL] = r0; scr[g_len + 3ULL] = r1; scr[g_len + 4ULL] = r2;
  return g_len + 5ULL;
}

bool full_cong_has_clause_k(FullHdr *h, u32 k) {
  u32 *tmp = (u32 *)h->tmp_lits; u8 *lm = (u8 *)h->lit_mark;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u64 nlits = h->cur_vars << 1;
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
  bool res = false;
  u64 off = (u64)wvec[(u64)min_l << 1]; u64 end = off + (u64)wvec[((u64)min_l << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot < nlits) {
        i8 ov = vals[ot];
        if (ov < (i8)0 || (ov == (i8)0 && lm[ot] != (u8)0)) { res = true; break; }
      }
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u) { continue; }
    bool ok = true; u32 j = 0u;
    while (j < sz) {
      u32 cl = ar[(u64)cr + 3ULL + (u64)j];
      i8 cv = vals[cl];
      if (cv > (i8)0) { ok = false; break; }
      if (cv == (i8)0 && lm[cl] == (u8)0) { ok = false; break; }
      j = j + 1u;
    }
    if (ok) { res = true; break; }
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
    if ((u64)lp + (u64)bp < (u64)needed_cl || (u64)ln + (u64)bn < (u64)needed_cl) {
      return g_len;
    }
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
  if (k == 4u) {
    u32 b0 = base[0]; u32 b1 = base[1]; u32 b2 = base[2]; u32 b3 = base[3];
    g_len = full_cong_emit_xor4(scr, g_len, b0, b1, b2, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b1, b0, b2, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b2, b0, b1, b3);
    g_len = full_cong_emit_xor4(scr, g_len, b3, b0, b1, b2);
    return g_len;
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
  return g_len;
}

u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim) {
  full_cong_count_bins(h);
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *nbc = (u32 *)h->work_stk1; u32 *base = (u32 *)h->work_stk2;
  i8 *vals = (i8 *)h->values; u64 cv = h->cur_vars;
  u64 p = 0ULL; u64 g_len = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && g_len + 4ULL <= g_cap && ticks < tick_lim) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 usz = 0u; u32 max_nbc = 0u; u32 min_nbc = 0xFFFFFFFFu;
      u32 neg_p = 0u; bool sat = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        i8 lv = vals[l];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          if (usz >= 65u || (u64)usz >= cv) { sat = true; break; }
          base[usz] = l; usz = usz + 1u;
          u32 c_n = nbc[l];
          if (c_n > max_nbc) { max_nbc = c_n; }
          if (c_n < min_nbc) { min_nbc = c_n; }
          if ((l & 1u) != 0u) { neg_p = neg_p ^ 1u; }
        }
        k = k + 1u;
      }
      if (!sat && usz >= 3u && usz <= 65u && (u64)usz <= cv) {
        u32 arity = usz - 1u;
        if (min_nbc > 0u && max_nbc >= arity) {
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
        if (usz == 3u && g_len + 12ULL <= g_cap) {
          g_len = full_cong_try_xor_ite(h, base[0], base[1], base[2], g_len, g_cap);
          ticks = ticks + 4ULL;
        } else if (usz >= 4u && usz <= 5u && g_len + (u64)usz * (u64)(usz + 1u) <= g_cap) {
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
  if (ua < 2u || ua > 64u) { return false; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  i8 *vals = (i8 *)h->values; u32 *tmp = (u32 *)h->tmp_lits;
  u32 ea = scr[(u64)ent + 1ULL] & 0xFFu;
  u64 mask = 0ULL; u32 j = 0u;
  while (j < ea) {
    u32 er = full_cong_find(repr, scr[(u64)ent + 2ULL + (u64)j]);
    i8 ev = vals[er];
    if (ev < (i8)0) { return false; }
    if (ev == (i8)0) {
      bool found = false; u32 k = 0u;
      while (k < ua) {
        if (tmp[k] == er) { mask = mask | (1ULL << (u64)k); found = true; break; }
        k = k + 1u;
      }
      if (!found) { return false; }
    }
    j = j + 1u;
  }
  u64 full_mask = (ua == 64u) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << (u64)ua) - 1ULL);
  return mask == full_mask;
}

u64 full_cong_eval_gate(FullHdr *h, u64 g, u64 ht_off, u64 ht_sz, u32 next_ep, u64 ctrl_off) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *repr = (u32 *)h->repr;
  u32 *tmp = (u32 *)h->tmp_lits; i8 *vals = (i8 *)h->values;
  u32 *trl = (u32 *)h->trail;
  u32 raw_lhs = scr[g]; u32 meta = scr[g + 1ULL];
  u32 tag = meta >> 28; u32 arity = meta & 0xFFu;
  if (arity < 2u || arity > 64u || (u64)arity > h->cur_vars) { return 0ULL; }
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
      } else if (ua > 64u) {
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
    if (ua > 0u) {
      u32 lhs_v = lhs & (~1u); u32 self_i = ua; i = 0u;
      while (i < ua) {
        if (tmp[i] == lhs_v) { self_i = i; break; }
        i = i + 1u;
      }
      if (self_i < ua) {
        u32 j = self_i;
        while (j + 1u < ua) { tmp[j] = tmp[j + 1u]; j = j + 1u; }
        ua = ua - 1u;
        u32 lsign = lhs & 1u;
        if (ua == 0u) {
          if (lsign != 0u) { h->inconsistent = 1ULL; return 2ULL; }
          need_hash = false;
        } else if (ua == 1u) {
          u32 ul = tmp[0] ^ (1u ^ lsign);
          u64 uf = full_cong_unit_fold(h, ul, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (ua == 2u) {
          u32 a0 = tmp[0] ^ lsign; u32 a1 = tmp[1];
          u64 ef = full_cong_equiv_fold(h, a0, a1, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, a1 >> 1);
          }
          need_hash = false;
        } else {
          need_hash = false;
        }
      }
    }
    if (need_hash) {
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
    } else if (vt == (i8)0 && ve == (i8)0 && t == (e ^ 1u)) {
      lhs = lhs ^ ((1u ^ c ^ t) & 1u);
      u32 r0 = c & (~1u); u32 r1 = t & (~1u);
      if (r0 == r1) {
        u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
        if (uf == 2ULL) { return 2ULL; }
        if (uf == 1ULL) { changed = true; }
        need_hash = false;
      } else if (vals[lhs] != (i8)0) {
        u32 a0 = (vals[lhs] > (i8)0) ? (r0 ^ 1u) : r0;
        u64 ef = full_cong_equiv_fold(h, a0, r1, next_ep);
        if (ef == 2ULL) { return 2ULL; }
        if (ef == 1ULL) {
          changed = true;
          full_cong_enq_var(h, ctrl_off, a0 >> 1); full_cong_enq_var(h, ctrl_off, r1 >> 1);
        }
        need_hash = false;
      } else {
        tmp[0] = (r0 < r1) ? r0 : r1; tmp[1] = (r0 < r1) ? r1 : r0;
        htag = 1u; harity = 2u;
      }
    } else {
      bool ite_and = false; u32 a0 = 0u; u32 a1 = 0u;
      if (vt > (i8)0) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (vt < (i8)0) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (ve > (i8)0) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (ve < (i8)0) {
        a0 = c; a1 = t; ite_and = true;
      } else if (c == t) {
        lhs = lhs ^ 1u; a0 = c ^ 1u; a1 = e ^ 1u; ite_and = true;
      } else if (c == (t ^ 1u)) {
        a0 = c ^ 1u; a1 = e; ite_and = true;
      } else if (c == (e ^ 1u)) {
        lhs = lhs ^ 1u; a0 = c; a1 = t ^ 1u; ite_and = true;
      } else if (c == e) {
        a0 = c; a1 = t; ite_and = true;
      }
      if (ite_and) {
        if (a0 == a1) {
          u64 ef = full_cong_equiv_fold(h, lhs, a0, next_ep);
          if (ef == 2ULL) { return 2ULL; }
          if (ef == 1ULL) {
            changed = true;
            full_cong_enq_var(h, ctrl_off, lhs >> 1); full_cong_enq_var(h, ctrl_off, a0 >> 1);
          }
          need_hash = false;
        } else if (a0 == (a1 ^ 1u) || a0 == (lhs ^ 1u) || a1 == (lhs ^ 1u)) {
          u64 uf = full_cong_unit_fold(h, lhs ^ 1u, next_ep);
          if (uf == 2ULL) { return 2ULL; }
          if (uf == 1ULL) { changed = true; }
          need_hash = false;
        } else if (vals[lhs] > (i8)0) {
          u64 u0 = full_cong_unit_fold(h, a0, next_ep);
          if (u0 == 2ULL) { return 2ULL; }
          if (u0 == 1ULL) { changed = true; }
          u64 u1 = full_cong_unit_fold(h, a1, next_ep);
          if (u1 == 2ULL) { return 2ULL; }
          if (u1 == 1ULL) { changed = true; }
          need_hash = false;
        } else {
          tmp[0] = (a0 < a1) ? a0 : a1; tmp[1] = (a0 < a1) ? a1 : a0;
          htag = 0u; harity = 2u;
        }
      } else {
        if ((c & 1u) != 0u) { c = c ^ 1u; u32 sw = t; t = e; e = sw; }
        if ((t & 1u) != 0u) { lhs = lhs ^ 1u; t = t ^ 1u; e = e ^ 1u; }
        tmp[0] = c; tmp[1] = t; tmp[2] = e;
      }
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
    while (probes < 128ULL) {
      u32 ent = scr[ht_off + slot];
      if (ent == 0xFFFFFFFFu) {
        if (!seen_self && htag == tag && h->res_sz < ht_lim) {
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
    bool do_grow = (h->res_sz * 2ULL >= ht_sz) && (ht_sz < 1048576ULL) &&
      (ht_off + (ht_sz << 1) <= h->scratch_cap);
    bool do_flush = (!do_grow) && (h->res_sz * 4ULL >= ht_sz * 3ULL) && (rehashes < 4ULL);
    if ((do_grow || do_flush) && ticks < tick_lim) {
      if (do_grow) {
        ht_sz = ht_sz << 1;
        scr[ctrl_off + 7ULL] = (u32)ht_sz;
      } else {
        rehashes = rehashes + 1ULL;
      }
      i = 0ULL; while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL;
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

void full_cong_sift_pairs_fid(u32 *a, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 sw = root;
    u32 sw_s = a[sw << 1]; u32 sw_r = a[(sw << 1) + 1ULL];
    u32 c_s = a[child << 1]; u32 c_r = a[(child << 1) + 1ULL];
    if (c_s > sw_s || (c_s == sw_s && c_r > sw_r)) {
      sw = child; sw_s = c_s; sw_r = c_r;
    }
    u64 right = child + 1ULL;
    if (right < n) {
      u32 r_s = a[right << 1]; u32 r_r = a[(right << 1) + 1ULL];
      if (r_s > sw_s || (r_s == sw_s && r_r > sw_r)) {
        sw = right; sw_s = r_s; sw_r = r_r;
      }
    }
    if (sw == root) { break; }
    u32 t_s = a[root << 1]; u32 t_r = a[(root << 1) + 1ULL];
    a[root << 1] = sw_s; a[(root << 1) + 1ULL] = sw_r;
    a[sw << 1] = t_s; a[(sw << 1) + 1ULL] = t_r;
    root = sw;
  }
}

void full_cong_sort_pairs_fid(u32 *a, u64 n) {
  if (n <= 1ULL) { return; }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_cong_sift_pairs_fid(a, start, n);
  }
  u64 end = n;
  while (end > 1ULL) {
    end = end - 1ULL;
    u32 t_s = a[0]; u32 t_r = a[1];
    a[0] = a[end << 1]; a[1] = a[(end << 1) + 1ULL];
    a[end << 1] = t_s; a[(end << 1) + 1ULL] = t_r;
    full_cong_sift_pairs_fid(a, 0ULL, end);
  }
}

u64 full_cong_fwd_subsume(FullHdr *h, u64 tick_lim) {
  if (h->inconsistent != 0ULL || h->ant_sz != 0ULL) {
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  if (tick_lim > 0x7FFFFFFFFFFFFFFFULL) { tick_lim = 0x7FFFFFFFFFFFFFFFULL; }
  if (tick_lim == 0ULL || h->scratch_cap < 4ULL) { return 1ULL; }
  u64 cv = h->cur_vars; u64 nlits = cv << 1;
  u32 *repr = (u32 *)h->repr; u32 *fl = (u32 *)h->flags;
  u32 *mch = (u32 *)h->min_clr; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *occ_head = (u32 *)h->work_stk1; u32 *occ_cnt = (u32 *)h->work_stk2;
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
  u64 max_cand = h->scratch_cap >> 2;
  u64 ncand = 0ULL; u64 p = 0ULL; u64 ticks = 0ULL;
  while (p < h->arena_len && ticks < tick_lim && h->inconsistent == 0ULL) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    ticks = ticks + 1ULL;
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool sat = false; bool taut = false; bool c_mch = false; bool ovf = false;
    u32 msz = 0u; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k]; i8 lv = vals[l];
      if (lv > (i8)0) { sat = true; break; }
      if (lv < (i8)0) { k = k + 1u; continue; }
      if (mch[l >> 1] != 0u) { c_mch = true; }
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
    if (ncand < max_cand) {
      u32 key = (msz << 1) | (((hdr & PH_RED) != 0u) ? 1u : 0u);
      scr[ncand << 1] = key; scr[(ncand << 1) + 1ULL] = (u32)p;
      ncand = ncand + 1ULL;
    }
    p = np;
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (ncand <= 1ULL || ticks >= tick_lim) { return 1ULL; }
  full_cong_sort_pairs_fid(scr, ncand);
  i = 0ULL;
  while (i < nlits) { occ_head[i] = 0xFFFFFFFFu; occ_cnt[i] = 0u; i = i + 1ULL; }
  u64 occ_pos = ncand << 1;
  u64 ci = 0ULL;
  while (ci < ncand && ticks < tick_lim && h->inconsistent == 0ULL) {
    u32 cref = scr[(ci << 1) + 1ULL];
    u32 chdr = ar[cref]; u32 csz = ar[(u64)cref + 2ULL];
    ticks = ticks + 1ULL;
    if ((chdr & PH_GARB) != 0u || csz < 3u) { ci = ci + 1ULL; continue; }
    bool c_red = (chdr & PH_RED) != 0u;
    bool sat = false; bool taut = false; bool ovf = false;
    u32 msz = 0u; u32 k = 0u;
    while (k < csz) {
      u32 l = ar[(u64)cref + 3ULL + (u64)k]; i8 lv = vals[l];
      if (lv > (i8)0) { sat = true; break; }
      if (lv < (i8)0) { k = k + 1u; continue; }
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
    if (sat || taut) {
      k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      ci = ci + 1ULL; continue;
    }
    if (ovf) {
      k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
      ci = ci + 1ULL; continue;
    }
    if (msz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (msz == 1u) {
      lm[tmp[0]] = (u8)0;
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      if (!full_add_unit(h, tmp[0])) { return 20ULL; }
      ci = ci + 1ULL; continue;
    }
    u32 least_r = tmp[0]; u32 least_cnt = occ_cnt[least_r];
    bool subsumed = false;
    k = 0u;
    while (k < msz && !subsumed && ticks < tick_lim) {
      u32 rk = tmp[k]; u32 cnt = occ_cnt[rk];
      if (cnt < least_cnt) { least_cnt = cnt; least_r = rk; }
      u32 nd = occ_head[rk];
      while (nd != 0xFFFFFFFFu && ticks < tick_lim) {
        ticks = ticks + 1ULL;
        u32 dref = scr[nd]; u32 nxt = scr[(u64)nd + 1ULL];
        u32 dhdr = ar[dref]; u32 dsz = ar[(u64)dref + 2ULL];
        bool d_red = (dhdr & PH_RED) != 0u;
        if ((dhdr & PH_GARB) == 0u && dref != cref && (c_red || !d_red)) {
          bool dok = true; u32 dj = 0u;
          while (dj < dsz) {
            u32 ol = ar[(u64)dref + 3ULL + (u64)dj]; i8 ov = vals[ol];
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
        nd = nxt;
      }
      k = k + 1u;
    }
    k = 0u; while (k < msz) { lm[tmp[k]] = (u8)0; k = k + 1u; }
    if (subsumed) {
      ar[cref] = chdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
    } else if (occ_pos + 2ULL <= h->scratch_cap) {
      scr[occ_pos] = cref;
      scr[occ_pos + 1ULL] = occ_head[least_r];
      occ_head[least_r] = (u32)occ_pos;
      occ_cnt[least_r] = occ_cnt[least_r] + 1u;
      occ_pos = occ_pos + 2ULL;
    }
    ci = ci + 1ULL;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_cong_ht_hash_ent_m7(FullHdr *h, u32 ent, u64 ht_off) {
  u64 e = (u64)ent;
  if (e + 2ULL > ht_off || ht_off > h->scratch_cap) { return 0ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 meta = scr[e + 1ULL];
  u64 htag = (u64)(meta >> 28);
  u64 harity = (u64)(meta & 0xFFu);
  if (harity > 64ULL || e + 2ULL + harity > ht_off) { return 0ULL; }
  u64 hv = htag * 0x9E3779B1ULL + harity;
  u64 i = 0ULL;
  while (i < harity) {
    hv = hv * 0x85EBCA77ULL + (u64)scr[e + 2ULL + i] + 1ULL;
    i = i + 1ULL;
  }
  return hv;
}

u64 full_cong_ht_init_m7(FullHdr *h, u64 ctrl_off, u64 ht_off, u64 max_sz) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) { return 0ULL; }
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) { return 0ULL; }
  u64 avail = cap - ht_off;
  if (avail < 16ULL) { return 0ULL; }
  u64 lim = (max_sz == 0ULL) ? 1048576ULL : max_sz;
  if (lim > 1048576ULL) { lim = 1048576ULL; }
  if (lim < 16ULL) { lim = 16ULL; }
  u64 top = (lim < avail) ? lim : avail;
  u64 sz = 16ULL;
  while (sz * 2ULL <= top) { sz = sz << 1; }
  u32 *scr = (u32 *)h->scratch_buf;
  scr[ctrl_off + 6ULL] = (u32)ht_off;
  scr[ctrl_off + 7ULL] = (u32)sz;
  u64 k = 0ULL;
  while (k < sz) { scr[ht_off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  h->res_sz = 0ULL;
  return sz;
}

u64 full_cong_ht_grow_m7(FullHdr *h, u64 ctrl_off) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) { return 0ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 old_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) { return 0ULL; }
  if (old_sz < 16ULL || old_sz > 1048576ULL || (old_sz & (old_sz - 1ULL)) != 0ULL ||
      old_sz > cap - ht_off) {
    return 0ULL;
  }
  if (old_sz == 1048576ULL) { return old_sz; }
  u64 new_sz = old_sz << 1;
  if (new_sz > cap - ht_off) { return old_sz; }
  u64 k = old_sz;
  while (k < new_sz) { scr[ht_off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  u64 i = 0ULL;
  while (i < old_sz) {
    u32 raw = scr[ht_off + i];
    if (raw != 0xFFFFFFFFu && (raw & 0x80000000u) == 0u && (u64)raw < ht_off) {
      scr[ht_off + i] = 0xFFFFFFFFu;
      u32 cur = raw; u64 hops = 0ULL;
      while (hops < new_sz) {
        u64 hv = full_cong_ht_hash_ent_m7(h, cur, ht_off);
        u64 slot = hv & (new_sz - 1ULL); u64 p = 0ULL;
        while (p < new_sz) {
          u32 dst = scr[ht_off + slot];
          if (dst == 0xFFFFFFFFu) {
            scr[ht_off + slot] = cur | 0x80000000u; cur = 0xFFFFFFFFu; break;
          }
          if ((dst & 0x80000000u) == 0u) {
            scr[ht_off + slot] = cur | 0x80000000u;
            cur = ((u64)dst < ht_off) ? dst : 0xFFFFFFFFu;
            break;
          }
          slot = (slot + 1ULL) & (new_sz - 1ULL); p = p + 1ULL;
        }
        if (cur == 0xFFFFFFFFu) { break; }
        hops = hops + 1ULL;
      }
    }
    i = i + 1ULL;
  }
  u64 j = 0ULL;
  while (j < new_sz) {
    u32 v = scr[ht_off + j];
    if (v != 0xFFFFFFFFu) { scr[ht_off + j] = v & 0x7FFFFFFFu; }
    j = j + 1ULL;
  }
  scr[ctrl_off + 7ULL] = (u32)new_sz;
  return new_sz;
}

u64 full_cong_ht_grow_clear_m7(FullHdr *h, u64 ctrl_off) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) { return 0ULL; }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 old_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) { return 0ULL; }
  if (old_sz < 16ULL || old_sz > 1048576ULL || (old_sz & (old_sz - 1ULL)) != 0ULL ||
      old_sz > cap - ht_off) {
    return 0ULL;
  }
  if (old_sz == 1048576ULL) { return old_sz; }
  u64 new_sz = old_sz << 1;
  if (new_sz > cap - ht_off) { return old_sz; }
  u64 k = 0ULL;
  while (k < new_sz) { scr[ht_off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  scr[ctrl_off + 7ULL] = (u32)new_sz;
  h->res_sz = 0ULL;
  return new_sz;
}

u32 full_cong_ht_lookup_m7(FullHdr *h, u64 ctrl_off, u32 htag, u32 harity) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) { return 0xFFFFFFFFu; }
  u64 ha = (u64)harity;
  if (ha > 64ULL || ha > h->max_vars) { return 0xFFFFFFFFu; }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) { return 0xFFFFFFFFu; }
  if (ht_sz < 16ULL || ht_sz > 1048576ULL || (ht_sz & (ht_sz - 1ULL)) != 0ULL ||
      ht_sz > cap - ht_off) {
    return 0xFFFFFFFFu;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 hv = (u64)htag * 0x9E3779B1ULL + ha;
  u64 hi = 0ULL;
  while (hi < ha) { hv = hv * 0x85EBCA77ULL + (u64)tmp[hi] + 1ULL; hi = hi + 1ULL; }
  u64 slot = hv & (ht_sz - 1ULL); u64 p = 0ULL;
  while (p < ht_sz) {
    u32 ent = scr[ht_off + slot];
    if (ent == 0xFFFFFFFFu) { return 0xFFFFFFFFu; }
    u64 e = (u64)ent;
    if (e + 2ULL + ha <= ht_off) {
      u32 meta = scr[e + 1ULL];
      if ((meta >> 28) == htag && (meta & 0xFFu) == harity) {
        u32 eq = 1u; u64 k = 0ULL;
        while (k < ha) {
          if (scr[e + 2ULL + k] != tmp[k]) { eq = 0u; break; }
          k = k + 1ULL;
        }
        if (eq != 0u) { return ent; }
      }
    }
    slot = (slot + 1ULL) & (ht_sz - 1ULL); p = p + 1ULL;
  }
  return 0xFFFFFFFFu;
}

u32 full_cong_ht_insert_m7(FullHdr *h, u64 ctrl_off, u32 ent) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) { return 0xFFFFFFFFu; }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) { return 0xFFFFFFFFu; }
  if (ht_sz < 16ULL || ht_sz > 1048576ULL || (ht_sz & (ht_sz - 1ULL)) != 0ULL ||
      ht_sz > cap - ht_off) {
    return 0xFFFFFFFFu;
  }
  u64 e = (u64)ent;
  if (e + 2ULL > ht_off) { return 0xFFFFFFFFu; }
  u32 meta = scr[e + 1ULL]; u32 etag = meta >> 28; u32 earity = meta & 0xFFu;
  u64 ea = (u64)earity;
  if (ea > 64ULL || e + 2ULL + ea > ht_off) { return 0xFFFFFFFFu; }
  if (ht_sz <= 1048576ULL && (h->res_sz >= ht_sz || h->res_sz * 4ULL >= ht_sz * 3ULL)) {
    u64 grown = full_cong_ht_grow_m7(h, ctrl_off);
    if (grown >= 16ULL && (grown & (grown - 1ULL)) == 0ULL && grown <= cap - ht_off) {
      ht_sz = grown;
    }
  }
  u64 hv = full_cong_ht_hash_ent_m7(h, ent, ht_off);
  u64 slot = hv & (ht_sz - 1ULL); u64 p = 0ULL;
  while (p < ht_sz) {
    u32 cur = scr[ht_off + slot];
    if (cur == 0xFFFFFFFFu) {
      scr[ht_off + slot] = ent; h->res_sz = h->res_sz + 1ULL; return ent;
    }
    if (cur == ent) { return ent; }
    u64 c = (u64)cur;
    if (c + 2ULL + ea <= ht_off) {
      u32 cmeta = scr[c + 1ULL];
      if ((cmeta >> 28) == etag && (cmeta & 0xFFu) == earity) {
        u32 eq = 1u; u64 k = 0ULL;
        while (k < ea) {
          if (scr[c + 2ULL + k] != scr[e + 2ULL + k]) { eq = 0u; break; }
          k = k + 1ULL;
        }
        if (eq != 0u) { return cur; }
      }
    }
    slot = (slot + 1ULL) & (ht_sz - 1ULL); p = p + 1ULL;
  }
  return 0xFFFFFFFFu;
}

u64 full_cong_copy_condbin_m7(FullHdr *h, u32 lit, u64 *dst, u64 cap) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 alen = h->arena_len;
  u64 widx = (u64)lit << 1ULL;
  u64 off = (u64)wvec[widx];
  u64 wsz = (u64)wvec[widx + 1ULL];
  u64 p = off; u64 end = off + wsz; u64 cnt = 0ULL;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      p = p + 1ULL;
    } else {
      if (p + 1ULL >= end) { break; }
      u32 cr = wstk[p + 1ULL]; p = p + 2ULL;
      if ((u64)cr + 2ULL < alen) {
        u32 hdr = arena[cr]; u32 sz = arena[(u64)cr + 2ULL];
        if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u &&
            (u64)cr + 2ULL + (u64)sz < alen) {
          u32 a = 0u; u32 b = 0u; u32 ocnt = 0u;
          bool found_lit = false; bool ok = true; u32 k = 0u;
          while (k < sz) {
            u32 l = arena[(u64)cr + 3ULL + (u64)k];
            i8 lv = vals[l];
            if (lv > (i8)0) { ok = false; break; }
            if (lv == (i8)0) {
              if (l == lit) { found_lit = true; }
              else if (ocnt == 0u) { a = l; ocnt = 1u; }
              else if (ocnt == 1u) { b = l; ocnt = 2u; }
              else { ok = false; break; }
            }
            k = k + 1u;
          }
          if (ok && found_lit && ocnt == 2u && (a >> 1) != (b >> 1) &&
              (a >> 1) != (lit >> 1) && (b >> 1) != (lit >> 1)) {
            if (cnt >= cap) { return 0ULL; }
            u32 mn = (b < a) ? b : a;
            u32 mx = (b < a) ? a : b;
            dst[cnt] = ((u64)mn << 32ULL) | (u64)mx;
            cnt = cnt + 1ULL;
          }
        }
      }
    }
  }
  if (cnt <= 1ULL) { return cnt; }
  full_cong_u64_sort_m7(dst, cnt);
  u64 u = 1ULL; u64 i = 1ULL;
  while (i < cnt) {
    if (dst[i] != dst[u - 1ULL]) { dst[u] = dst[i]; u = u + 1ULL; }
    i = i + 1ULL;
  }
  return u;
}

u32 full_cong_merge_condeq_m7(FullHdr *h, u32 cond, u64 pos_n, u64 neg_n,
                              u32 g_len, u32 g_cap) {
  if (pos_n == 0ULL || neg_n == 0ULL || g_len > g_cap ||
      (u64)g_cap > h->scratch_cap) {
    return g_len;
  }
  u64 *pos_eq = (u64 *)h->work_stk1;
  u64 *neg_eq = (u64 *)h->work_stk2;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 gl = g_len; u64 p = 0ULL; u64 q = 0ULL;
  while (p < pos_n && q < neg_n && (u64)gl + 5ULL <= (u64)g_cap) {
    u64 pv = pos_eq[p];
    u32 lhs_p = (u32)(pv >> 32ULL);
    u32 lhs_n = (u32)(neg_eq[q] >> 32ULL);
    if (lhs_p < lhs_n) {
      p = p + 1ULL;
    } else if (lhs_n < lhs_p) {
      q = q + 1ULL;
    } else {
      u64 q2 = q;
      while (q2 < neg_n && (u64)gl + 5ULL <= (u64)g_cap) {
        u64 nv = neg_eq[q2];
        if ((u32)(nv >> 32ULL) != lhs_p) { break; }
        u32 y = lhs_p; u32 t = (u32)pv; u32 e = (u32)nv;
        if (e != (t ^ 1u)) {
          u32 yy = y; u32 tt = t; u32 ee = e;
          if ((t & 1u) != 0u) { yy = y ^ 1u; tt = t ^ 1u; ee = e ^ 1u; }
          scr[gl] = yy;
          scr[(u64)gl + 1ULL] = (2u << 28u) | 3u;
          scr[(u64)gl + 2ULL] = cond;
          scr[(u64)gl + 3ULL] = tt;
          scr[(u64)gl + 4ULL] = ee;
          gl = gl + 5u;
        }
        q2 = q2 + 1ULL;
      }
      p = p + 1ULL;
    }
  }
  return gl;
}

u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap, u64 tick_lim) {
  u64 cv = h->cur_vars; u64 mv = h->max_vars;
  if (g_len > g_cap || (u64)g_cap > h->scratch_cap ||
      cv < 3ULL || cv > mv || tick_lim == 0ULL) {
    return g_len;
  }
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec; u64 *wsort = (u64 *)h->wsort;
  u64 *wk1 = (u64 *)h->work_stk1; u64 *wk2 = (u64 *)h->work_stk2;
  u64 v = 0ULL; u64 ticks = 0ULL; u32 gl = g_len;
  while (v < cv && ticks < tick_lim && (u64)gl + 5ULL <= (u64)g_cap) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1ULL] == (i8)0) {
      u32 lit0 = (u32)(v << 1ULL); u32 lit1 = lit0 | 1u;
      u32 sz0 = wvec[((u64)lit0 << 1ULL) + 1ULL];
      u32 sz1 = wvec[((u64)lit1 << 1ULL) + 1ULL];
      if (sz0 <= 1u || sz1 <= 1u) {
        ticks = ticks + 1ULL;
      } else {
        ticks = ticks + 1ULL + (u64)sz0 + (u64)sz1;
        u32 small_lit = lit0; u32 large_lit = lit1;
        u64 *dst0 = wk2; u64 *dst1 = wk1; bool flipped = false;
        if (sz1 < sz0) {
          small_lit = lit1; large_lit = lit0;
          dst0 = wk1; dst1 = wk2; flipped = true;
        }
        u64 m0 = full_cong_copy_condbin_m7(h, small_lit, wsort, mv);
        if (m0 > 1ULL) {
          u64 n0 = full_cong_extract_condeq_m7(wsort, m0, dst0, mv);
          if (n0 > 0ULL) {
            u64 m1 = full_cong_copy_condbin_m7(h, large_lit, wsort, mv);
            if (m1 > 1ULL) {
              u64 n1 = full_cong_extract_condeq_m7(wsort, m1, dst1, mv);
              if (n1 > 0ULL) {
                if (flipped) {
                  gl = full_cong_merge_condeq_m7(h, lit0, n0, n1, gl, g_cap);
                } else {
                  gl = full_cong_merge_condeq_m7(h, lit0, n1, n0, gl, g_cap);
                }
              }
            }
          }
        }
      }
    }
    v = v + 1ULL;
  }
  return gl;
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
  u64 g_cap = h->scratch_cap >> 1;
  if (g_cap > 0x00FFFFFFULL) { g_cap = 0x00FFFFFFULL; }
  u64 g_len = full_cong_extract(h, g_cap, tick_lim);
  if (g_len <= g_cap) {
    g_len = (u64)full_cong_extract_ite_all_m7(h, (u32)g_len, (u32)g_cap, tick_lim);
  }
  if (g_len > 0ULL && g_len <= g_cap) {
    u64 free_scr = h->scratch_cap - g_len;
    u64 ht_max = 64ULL;
    while (ht_max * 4ULL <= free_scr && ht_max < 1048576ULL) { ht_max = ht_max << 1; }
    u64 ht_off = h->scratch_cap - ht_max;
    u64 rem_occ = ht_off - g_len;
    u64 occ_bkt = (rem_occ >= 262144ULL) ? 8192ULL : ((rem_occ >= 65536ULL) ? 2048ULL :
      ((rem_occ >= 16384ULL) ? 512ULL : ((rem_occ >= 2048ULL) ? 256ULL :
      ((rem_occ >= 256ULL) ? 32ULL : 16ULL))));
    u64 bkt_off = ht_off - occ_bkt;
    u64 inq_off = bkt_off - occ_bkt;
    u64 q_off = inq_off - occ_bkt;
    u64 ctrl_off = q_off - 8ULL;
    u64 ht_sz = 64ULL;
    while (ht_sz < g_len && (ht_sz << 1) <= ht_max) { ht_sz = ht_sz << 1; }
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

/-! ## 1. Exported `Fn` Handles, Replacement / Helper Tables & Spliced Module -/

def fidCongEmitXorFn : Fn := full_cong_emit_xor
def fidCongEmitXor4Fn : Fn := full_cong_emit_xor4
def fidCongHasClauseKFn : Fn := full_cong_has_clause_k
def fidCongExtractXorKFn : Fn := full_cong_extract_xor_k
def fidCongTryXorIteFn : Fn := full_cong_try_xor_ite
def fidCongExtractFn : Fn := full_cong_extract
def fidCongAndMatchFn : Fn := full_cong_and_match
def fidCongEvalGateFn : Fn := full_cong_eval_gate
def fidCongWorklistFn : Fn := full_cong_worklist
def fidCongSiftPairsFn : Fn := full_cong_sift_pairs_fid
def fidCongSortPairsFn : Fn := full_cong_sort_pairs_fid
def fidCongFwdSubsumeFn : Fn := full_cong_fwd_subsume
def fidCongHtHashEntFn : Fn := full_cong_ht_hash_ent_m7
def fidCongHtInitFn : Fn := full_cong_ht_init_m7
def fidCongHtGrowFn : Fn := full_cong_ht_grow_m7
def fidCongHtGrowClearFn : Fn := full_cong_ht_grow_clear_m7
def fidCongHtLookupFn : Fn := full_cong_ht_lookup_m7
def fidCongHtInsertFn : Fn := full_cong_ht_insert_m7
def fidCongCopyCondbinFn : Fn := full_cong_copy_condbin_m7
def fidCongMergeCondeqFn : Fn := full_cong_merge_condeq_m7
def fidCongExtractIteAllFn : Fn := full_cong_extract_ite_all_m7
def fidCongruenceDenseFn : Fn := full_congruence_dense

/-- `19`-function drop-in replacement list closing `GAP-CONG-01..04` + `BUG-CONG-00`. -/
def fidCongRepls : List Fn :=
  [ fidCongEmitXorFn, fidCongHasClauseKFn, fidCongExtractXorKFn, fidCongTryXorIteFn
  , fidCongExtractFn, fidCongAndMatchFn, fidCongEvalGateFn, fidCongWorklistFn
  , fidCongFwdSubsumeFn, fidCongHtHashEntFn, fidCongHtInitFn, fidCongHtGrowFn
  , fidCongHtGrowClearFn, fidCongHtLookupFn, fidCongHtInsertFn, fidCongCopyCondbinFn
  , fidCongMergeCondeqFn, fidCongExtractIteAllFn, fidCongruenceDenseFn ]

/-- `3` new helper functions inserted before their congruence hosts (`emit_xor4` + pair sort). -/
def fidCongBefores : List (Sym × List Fn) :=
  [ ("full_cong_extract_xor_k", [fidCongEmitXor4Fn])
  , ("full_cong_fwd_subsume", [fidCongSiftPairsFn, fidCongSortPairsFn]) ]

/-- Base `471`-function combined `M8SweepV2 + M8CoreParity + HotTernary` function list
(definitionally equal to `FullM8CoreParity.m8SweepV2CoreParityFns`). -/
def fidCongBaseFns : List Fn :=
  PatchModule.patchFns
    (FullM8CoreParity.m8CoreParityRepls ++ [FullM7HotTernary.m7HasTernaryFn])
    FullM8CoreParity.m8CoreParityBefores
    FullM8SweepV2.m8FidV123t2Fns

/-- Base `471`-function module (`0` externs, `0` exits). -/
def fidCongBaseModule : LeanQbe.T.Module :=
  PatchModule.patchModule FullM8SweepV2.m8FidV123t2Module
    (FullM8CoreParity.m8CoreParityRepls ++ [FullM7HotTernary.m7HasTernaryFn])
    FullM8CoreParity.m8CoreParityBefores

/-- `474`-function module splicing `fidCongRepls` (`19`) + `fidCongBefores` (`+3`) onto
`fidCongBaseModule` (`471` fns). -/
def fidCongFns : List Fn :=
  PatchModule.patchFns fidCongRepls fidCongBefores fidCongBaseFns

/-- Closed `474`-function congruence-parity module (`0` externs, `0` exits). -/
def fidCongModule : LeanQbe.T.Module :=
  PatchModule.patchModule fidCongBaseModule fidCongRepls fidCongBefores

/-! ## 2. Function Well-Formedness (`Func.Wf`) & Acyclicity (`checkAcyclic = true`) -/

theorem full_cong_emit_xor_wf : Func.Wf full_cong_emit_xor_body := by t_wf_reify
theorem full_cong_emit_xor4_wf : Func.Wf full_cong_emit_xor4_body := by t_wf_reify
theorem full_cong_has_clause_k_wf : Func.Wf full_cong_has_clause_k_body := by t_wf_reify
theorem full_cong_extract_xor_k_wf : Func.Wf full_cong_extract_xor_k_body := by t_wf_reify
theorem full_cong_try_xor_ite_wf : Func.Wf full_cong_try_xor_ite_body := by t_wf_reify
theorem full_cong_extract_wf : Func.Wf full_cong_extract_body := by t_wf_reify
theorem full_cong_and_match_wf : Func.Wf full_cong_and_match_body := by t_wf_reify
theorem full_cong_eval_gate_wf : Func.Wf full_cong_eval_gate_body := by t_wf_reify
theorem full_cong_worklist_wf : Func.Wf full_cong_worklist_body := by t_wf_reify
theorem full_cong_sift_pairs_fid_wf : Func.Wf full_cong_sift_pairs_fid_body := by t_wf_reify
theorem full_cong_sort_pairs_fid_wf : Func.Wf full_cong_sort_pairs_fid_body := by t_wf_reify
theorem full_cong_fwd_subsume_wf : Func.Wf full_cong_fwd_subsume_body := by t_wf_reify
theorem full_cong_ht_hash_ent_m7_wf : Func.Wf full_cong_ht_hash_ent_m7_body := by t_wf_reify
theorem full_cong_ht_init_m7_wf : Func.Wf full_cong_ht_init_m7_body := by t_wf_reify
theorem full_cong_ht_grow_m7_wf : Func.Wf full_cong_ht_grow_m7_body := by t_wf_reify
theorem full_cong_ht_grow_clear_m7_wf : Func.Wf full_cong_ht_grow_clear_m7_body := by t_wf_reify
theorem full_cong_ht_lookup_m7_wf : Func.Wf full_cong_ht_lookup_m7_body := by t_wf_reify
theorem full_cong_ht_insert_m7_wf : Func.Wf full_cong_ht_insert_m7_body := by t_wf_reify
theorem full_cong_copy_condbin_m7_wf : Func.Wf full_cong_copy_condbin_m7_body := by t_wf_reify
theorem full_cong_merge_condeq_m7_wf : Func.Wf full_cong_merge_condeq_m7_body := by t_wf_reify
theorem full_cong_extract_ite_all_m7_wf : Func.Wf full_cong_extract_ite_all_m7_body := by
  t_wf_reify
theorem full_congruence_dense_wf : Func.Wf full_congruence_dense_body := by t_wf_reify

theorem fidCongRepls_wf : ∀ f ∈ fidCongRepls, f.Wf := by
  intro f hf
  simp only [fidCongRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_cong_emit_xor_wf
  · exact full_cong_has_clause_k_wf
  · exact full_cong_extract_xor_k_wf
  · exact full_cong_try_xor_ite_wf
  · exact full_cong_extract_wf
  · exact full_cong_and_match_wf
  · exact full_cong_eval_gate_wf
  · exact full_cong_worklist_wf
  · exact full_cong_fwd_subsume_wf
  · exact full_cong_ht_hash_ent_m7_wf
  · exact full_cong_ht_init_m7_wf
  · exact full_cong_ht_grow_m7_wf
  · exact full_cong_ht_grow_clear_m7_wf
  · exact full_cong_ht_lookup_m7_wf
  · exact full_cong_ht_insert_m7_wf
  · exact full_cong_copy_condbin_m7_wf
  · exact full_cong_merge_condeq_m7_wf
  · exact full_cong_extract_ite_all_m7_wf
  · exact full_congruence_dense_wf

theorem fidCongBefores_wf : ∀ f ∈ fidCongBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidCongBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact full_cong_emit_xor4_wf
  · exact full_cong_sift_pairs_fid_wf
  · exact full_cong_sort_pairs_fid_wf

/-! ## 3. Compile-Time `#guard` Verification (`PrintCpp`, `PrintQbe`, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

#guard fidCongFns.length == 474
#guard (fidCongFns.map Fn.name).eraseDups.length == 474
#guard fidCongModule.checkAcyclic
#guard fidCongModule.exits.isEmpty && fidCongModule.externs.isEmpty
#guard (ppTModule fidCongModule).isOk
#guard (PrintQbe.module fidCongModule).isOk
#guard (ppModule (fidCongFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidCongFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidCongFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (fidCongFns.map (Fn.legal .x64AVX2))).isOk
#guard fidCongFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidCongFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidCongFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard fidCongFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullFidelityCong
