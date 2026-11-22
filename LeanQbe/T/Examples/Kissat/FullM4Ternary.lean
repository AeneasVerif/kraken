module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M4c Standalone Module: `promote.c`, `reorder.c`/`tumble`, & `ternary.c`

Standalone, zero-conflict C0 implementation on the byte-identical `144`-word (`FullHdr`) arena
layout (`Full1.lean`..`Full3.lean`) covering Kissat's remaining core algorithmic features:
1. Reason-clause LBD recomputation & tier promotion/demotion (`promote.c`):
   - `full_compute_lbd` (scratch-only distinct positive decision-level count via `work_stk2`)
   - `full_promote_clause` (glue demotion + `tier1`/`tier2` usage bump + `glue_used[64]` update)
   - `full_promote_reasons` (active positive-level trail reason-clause promotion pass)
2. Variable decision-order reordering & clause-literal tumbling (`reorder.c` / `tumble`):
   - `full_score_sift` (VSIDS score max-heap sift-down on `wsort`)
   - `full_reorder_queue` (VMTF queue heapsort & relink by ascending score)
   - `full_reorder_heap` (VSIDS binary max-heap rebuild via `full_heap_push`)
   - `full_tumble_clause` (Fisher-Yates non-watched literal shuffle via `full_rng_next`)
   - `full_tumble_clauses` (budget-capped arena tumbling walk via `full_arena_next`)
   - `full_reorder` (combined VMTF + VSIDS + clause-tumble driver)
3. Hyper-ternary binary-resolvent derivation (`ternary.c`):
   - `full_ternary_match_bin` (pure complementary-pivot binary-resolvent matcher)
   - `full_ternary_collect` (live ternary clause collector into `scratch_buf`)
   - `full_ternary_resolve_bin` (3-pivot binary resolvent derivation via `full_add_bin`)
   - `full_ternary_round` (budget-capped pairwise hyper-ternary pass + level-0 BCP)
   - `full_ternary` (multi-round level-0 hyper-ternary driver)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Ternary

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! full_m4_ternary "
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

#define PH_GLUE_MASK 0x0007FFFFu
#define PH_GARB      0x00080000u
#define PH_RED       0x00400000u
#define PH_KEEP_META 0x07F80000u
#define FL_ACTIVE    1u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_rng_next(FullHdr *h);
extern void full_heap_push(FullHdr *h, u32 v);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);

u32 full_compute_lbd(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *seen = (u32 *)h->work_stk2;
  u64 cv = h->cur_vars;
  if ((u64)cref + 3ULL > h->arena_len) { return 0u; }
  u32 sz = ar[(u64)cref + 2ULL];
  if ((u64)cref + 3ULL + (u64)sz > h->arena_len) { return 0u; }
  u32 glue = 0u;
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i];
    u32 v = l >> 1;
    if ((u64)v < cv) {
      u32 lv = lvl[v];
      if (lv > 0u) {
        bool dup = false;
        u32 j = 0u;
        while (j < glue) {
          if (seen[j] == lv) { dup = true; break; }
          j = j + 1u;
        }
        if (!dup && (u64)glue < cv && glue < PH_GLUE_MASK) {
          seen[glue] = lv;
          glue = glue + 1u;
        }
      }
    }
    i = i + 1u;
  }
  return glue;
}

bool full_promote_clause(FullHdr *h, u32 cref) {
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 *ar = (u32 *)h->arena;
  u32 hdr = ar[cref];
  if ((hdr & PH_RED) == 0u || (hdr & PH_GARB) != 0u) { return false; }
  u32 new_glue = full_compute_lbd(h, cref);
  u32 *gu = (u32 *)h->glue_used;
  u32 bucket = (new_glue < 64u) ? new_glue : 63u;
  gu[bucket] = gu[bucket] + 1u;
  u32 old_glue = hdr & PH_GLUE_MASK;
  u32 used = (hdr >> 27) & 31u;
  u32 new_used = used;
  if ((u64)new_glue <= h->tier1) { new_used = 31u; }
  else if ((u64)new_glue <= h->tier2) { if (new_used < 30u) { new_used = 30u; } }
  else { if (new_used < 1u) { new_used = 1u; } }
  bool promoted = new_glue < old_glue;
  u32 final_glue = promoted ? new_glue : old_glue;
  if (promoted || new_used > used) {
    u32 nhdr = (hdr & PH_KEEP_META) | (final_glue & PH_GLUE_MASK) | (new_used << 27);
    ar[cref] = nhdr;
  }
  return promoted;
}

u64 full_promote_reasons(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u64 te = h->trail_end;
  u64 cnt = 0ULL;
  u64 i = 0ULL;
  while (i < te) {
    u32 v = trl[i] >> 1;
    if ((u64)v < h->cur_vars && lvl[v] > 0u) {
      u32 rsn = rsns[v];
      if (rsn != 0xFFFFFFFFu && (rsn & 0x80000000u) == 0u) {
        if (full_promote_clause(h, rsn)) { cnt = cnt + 1ULL; }
      }
    }
    i = i + 1ULL;
  }
  return cnt;
}

void full_score_sift(FullHdr *h, u64 start, u64 n) {
  if (n == 0ULL || start >= n || n > h->cur_vars) { return; }
  u32 *ws = (u32 *)h->wsort;
  u64 *sc = (u64 *)h->score;
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 best = root;
    u32 bv = ws[best];
    u32 cv = ws[child];
    if (sc[cv] > sc[bv]) { best = child; bv = cv; }
    u64 rch = child + 1ULL;
    if (rch < n) {
      u32 rv = ws[rch];
      if (sc[rv] > sc[bv]) { best = rch; bv = rv; }
    }
    if (best == root) { break; }
    u32 tmp = ws[root];
    ws[root] = bv;
    ws[best] = tmp;
    root = best;
  }
}

u64 full_reorder_queue(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  u32 *ws = (u32 *)h->wsort;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  i8 *vals = (i8 *)h->values;
  u64 n = 0ULL;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u) { ws[n] = (u32)v; n = n + 1ULL; }
    v = v + 1ULL;
  }
  v = 0ULL;
  while (v < cv) {
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    qs[v] = 0u;
    v = v + 1ULL;
  }
  if (n == 0ULL) {
    h->q_first = 0xFFFFFFFFULL;
    h->q_last = 0xFFFFFFFFULL;
    h->q_search_idx = 0xFFFFFFFFULL;
    h->q_cur_stamp = 0ULL;
    h->q_search_stamp = 0ULL;
    return 0ULL;
  }
  u64 s = n >> 1;
  while (s > 0ULL) {
    s = s - 1ULL;
    full_score_sift(h, s, n);
  }
  u64 e = n;
  while (e > 1ULL) {
    e = e - 1ULL;
    u32 tmp = ws[0];
    ws[0] = ws[e];
    ws[e] = tmp;
    full_score_sift(h, 0ULL, e);
  }
  u64 sidx = 0xFFFFFFFFULL;
  u64 sstamp = 0ULL;
  u64 i = 0ULL;
  while (i < n) {
    u32 cur = ws[i];
    qp[cur] = (i > 0ULL) ? ws[i - 1ULL] : 0xFFFFFFFFu;
    qn[cur] = (i + 1ULL < n) ? ws[i + 1ULL] : 0xFFFFFFFFu;
    qs[cur] = (u32)(i + 1ULL);
    if (vals[(u64)cur << 1] == (i8)0) { sidx = (u64)cur; sstamp = i + 1ULL; }
    i = i + 1ULL;
  }
  h->q_first = (u64)ws[0];
  h->q_last = (u64)ws[n - 1ULL];
  h->q_cur_stamp = n;
  if (sidx >= cv) { sidx = (u64)ws[n - 1ULL]; sstamp = n; }
  h->q_search_idx = sidx;
  h->q_search_stamp = sstamp;
  return n;
}

u64 full_reorder_heap(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *ps = (u32 *)h->pos;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  h->heap_len = 0ULL;
  u64 v = 0ULL;
  while (v < cv) { ps[v] = 0xFFFFFFFFu; v = v + 1ULL; }
  v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) { full_heap_push(h, (u32)v); }
    v = v + 1ULL;
  }
  return h->heap_len;
}

bool full_tumble_clause(FullHdr *h, u32 cref) {
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 *ar = (u32 *)h->arena;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & PH_GARB) != 0u || sz < 4u || (u64)cref + 3ULL + (u64)sz > h->arena_len) {
    return false;
  }
  ar[(u64)cref + 1ULL] = 2u;
  u32 i = sz - 1u;
  while (i > 2u) {
    u64 r = full_rng_next(h);
    u32 span = i - 1u;
    u32 j = 2u + (u32)(r % (u64)span);
    u32 li = ar[(u64)cref + 3ULL + (u64)i];
    u32 lj = ar[(u64)cref + 3ULL + (u64)j];
    ar[(u64)cref + 3ULL + (u64)i] = lj;
    ar[(u64)cref + 3ULL + (u64)j] = li;
    i = i - 1u;
  }
  return true;
}

u64 full_tumble_clauses(FullHdr *h, u64 budget) {
  u64 p = 0ULL;
  u64 done = 0ULL;
  while (p < h->arena_len && done < budget) {
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (full_tumble_clause(h, (u32)p)) { done = done + 1ULL; }
    if (np <= p) { break; }
    p = np;
  }
  return done;
}

u64 full_reorder(FullHdr *h, u64 budget) {
  full_reorder_queue(h);
  full_reorder_heap(h);
  return full_tumble_clauses(h, budget);
}

bool full_ternary_match_bin(u32 p, u32 u, u32 v, u32 b0, u32 b1, u32 b2) {
  u32 np = p ^ 1u;
  if (b0 == np) { return (b1 == u && b2 == v) || (b1 == v && b2 == u); }
  if (b1 == np) { return (b0 == u && b2 == v) || (b0 == v && b2 == u); }
  if (b2 == np) { return (b0 == u && b1 == v) || (b0 == v && b1 == u); }
  return false;
}

u64 full_ternary_collect(FullHdr *h, u64 cap) {
  u64 lim = (cap < h->scratch_cap) ? cap : h->scratch_cap;
  u32 *ar = (u32 *)h->arena;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 p = 0ULL;
  u64 n = 0ULL;
  while (p < h->arena_len && n < lim) {
    if (p + 3ULL > h->arena_len) { break; }
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) == 0u && sz == 3u) { scr[n] = (u32)p; n = n + 1ULL; }
    if (np <= p) { break; }
    p = np;
  }
  return n;
}

u64 full_ternary_resolve_bin(FullHdr *h, u32 c1, u32 c2) {
  if (c1 == c2) { return 0ULL; }
  if ((u64)c1 + 6ULL > h->arena_len || (u64)c2 + 6ULL > h->arena_len) { return 0ULL; }
  u32 *ar = (u32 *)h->arena;
  if ((ar[c1] & PH_GARB) != 0u || (ar[c2] & PH_GARB) != 0u) { return 0ULL; }
  if (ar[(u64)c1 + 2ULL] != 3u || ar[(u64)c2 + 2ULL] != 3u) { return 0ULL; }
  u32 a0 = ar[(u64)c1 + 3ULL];
  u32 a1 = ar[(u64)c1 + 4ULL];
  u32 a2 = ar[(u64)c1 + 5ULL];
  u32 b0 = ar[(u64)c2 + 3ULL];
  u32 b1 = ar[(u64)c2 + 4ULL];
  u32 b2 = ar[(u64)c2 + 5ULL];
  bool found = false;
  u32 u = 0u;
  u32 v = 0u;
  if (full_ternary_match_bin(a0, a1, a2, b0, b1, b2)) { u = a1; v = a2; found = true; }
  else if (full_ternary_match_bin(a1, a0, a2, b0, b1, b2)) { u = a0; v = a2; found = true; }
  else if (full_ternary_match_bin(a2, a0, a1, b0, b1, b2)) { u = a0; v = a1; found = true; }
  if (!found) { return 0ULL; }
  u64 st = full_add_bin(h, u, v);
  if (st == 1ULL) { h->hbr_cnt = h->hbr_cnt + 1ULL; }
  return st;
}

u64 full_ternary_round(FullHdr *h, u64 n, u64 budget) {
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ticks = 0ULL;
  u64 added = 0ULL;
  u64 i = 0ULL;
  while (i < n && ticks < budget && h->oom == 0ULL && h->fuel > 0ULL) {
    u64 j = i + 1ULL;
    while (j < n && ticks < budget && h->oom == 0ULL && h->fuel > 0ULL) {
      ticks = ticks + 1ULL;
      u64 st = full_ternary_resolve_bin(h, scr[i], scr[j]);
      if (st == 20ULL) { return 20ULL; }
      if (st == 2ULL) { return 2ULL; }
      if (st == 1ULL) {
        added = added + 1ULL;
        u64 ps = full_propagate(h);
        if (ps == 1ULL) { h->inconsistent = 1ULL; return 20ULL; }
        if (ps == 2ULL) { return 2ULL; }
      }
      j = j + 1ULL;
    }
    i = i + 1ULL;
  }
  return (added > 0ULL) ? 1ULL : 0ULL;
}

u64 full_ternary(FullHdr *h, u64 rounds, u64 budget) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  u64 p0 = full_propagate(h);
  if (p0 == 1ULL) { h->inconsistent = 1ULL; return 20ULL; }
  if (p0 == 2ULL) { return 1ULL; }
  u64 round = 0ULL;
  while (round < rounds && h->oom == 0ULL && h->fuel > 0ULL) {
    u64 n = full_ternary_collect(h, 1024ULL);
    if (n < 2ULL) { break; }
    u64 st = full_ternary_round(h, n, budget);
    if (st == 20ULL) { return 20ULL; }
    if (st != 1ULL) { break; }
    round = round + 1ULL;
  }
  return 1ULL;
}
"

def fullM4TernaryExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_rng_next", [i64], [i64]⟩
  , ⟨"full_heap_push", [i64, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩ ]

def fullM4TernaryModule : LeanQbe.T.Module :=
  { fns := full_m4_ternary_fns, externs := fullM4TernaryExterns, exits := [] }

theorem full_compute_lbd_wf : Func.Wf full_compute_lbd_body := by t_wf_reify
theorem full_promote_clause_wf : Func.Wf full_promote_clause_body := by t_wf_reify
theorem full_promote_reasons_wf : Func.Wf full_promote_reasons_body := by t_wf_reify
theorem full_score_sift_wf : Func.Wf full_score_sift_body := by t_wf_reify
theorem full_reorder_queue_wf : Func.Wf full_reorder_queue_body := by t_wf_reify
theorem full_reorder_heap_wf : Func.Wf full_reorder_heap_body := by t_wf_reify
theorem full_tumble_clause_wf : Func.Wf full_tumble_clause_body := by t_wf_reify
theorem full_tumble_clauses_wf : Func.Wf full_tumble_clauses_body := by t_wf_reify
theorem full_reorder_wf : Func.Wf full_reorder_body := by t_wf_reify
theorem full_ternary_match_bin_wf : Func.Wf full_ternary_match_bin_body := by t_wf_reify
theorem full_ternary_collect_wf : Func.Wf full_ternary_collect_body := by t_wf_reify
theorem full_ternary_resolve_bin_wf : Func.Wf full_ternary_resolve_bin_body := by t_wf_reify
theorem full_ternary_round_wf : Func.Wf full_ternary_round_body := by t_wf_reify
theorem full_ternary_wf : Func.Wf full_ternary_body := by t_wf_reify

theorem full_m4_ternary_fns_wf : ∀ f ∈ full_m4_ternary_fns, f.Wf := by
  simp only [full_m4_ternary_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_compute_lbd_wf, full_promote_clause_wf, full_promote_reasons_wf,
    full_score_sift_wf, full_reorder_queue_wf, full_reorder_heap_wf,
    full_tumble_clause_wf, full_tumble_clauses_wf, full_reorder_wf,
    full_ternary_match_bin_wf, full_ternary_collect_wf, full_ternary_resolve_bin_wf,
    full_ternary_round_wf, full_ternary_wf⟩

theorem fullM4Ternary_acyclic : fullM4TernaryModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4Ternary
