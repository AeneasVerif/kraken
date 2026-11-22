module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M5 Dense Binary Extraction (`FullM5CongBins`)

Drop-in replacement for `full_congruence_dense` (`congruence.c:2226-2300` `extract_binaries` +
`FullM3CongBva.full_congruence_dense`, `0` `FullHdr` changes):
1. `full_cong_eb_match`: checks `(x ^ 1, l) ∨ (x ^ 1, k)` in binary watches via `full_has_bin`.
2. `full_cong_extract_binaries`: scans irredundant non-garbage ternary arena clauses `(a ∨ b ∨ c)`
   with unassigned literals before `full_cong_extract`, deducing strengthened binaries via
   resolution with existing binary clauses and committing them with `full_add_bin`.
3. `full_congruence_dense`: runs `full_cong_extract_binaries(h)` before `full_cong_extract`,
   preserving the exact `FullM3CongBva.full_congruence_dense` hash-table closure loop.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5CongBins

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5CongBins "
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

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_cong_extract(FullHdr *h, u64 g_cap, u64 tick_lim);
extern u64 full_cong_work_step(FullHdr *h, u64 g_len, u64 ht_off, u64 ht_sz, u32 cur_ep);

bool full_cong_eb_match(FullHdr *h, u32 x, u32 l, u32 k) {
  return full_has_bin(h, x ^ 1u, l) || full_has_bin(h, x ^ 1u, k);
}

u64 full_cong_extract_binaries(FullHdr *h) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  u64 alen = h->arena_len;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 p = 0ULL;
  while (p < alen) {
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz == 3u) {
      u32 a = ar[p + 3ULL];
      u32 b = ar[p + 4ULL];
      u32 c = ar[p + 5ULL];
      if (vals[a] == (i8)0 && vals[b] == (i8)0 && vals[c] == (i8)0) {
        u32 l = 0u;
        u32 k = 0u;
        bool found = false;
        if (full_cong_eb_match(h, a, b, c)) {
          l = b; k = c; found = true;
        } else if (full_cong_eb_match(h, b, a, c)) {
          l = a; k = c; found = true;
        } else if (full_cong_eb_match(h, c, a, b)) {
          l = a; k = b; found = true;
        }
        if (found && !full_has_bin(h, l, k)) {
          u64 st = full_add_bin(h, l, k);
          if (st == 20ULL) { return 20ULL; }
          if (st == 2ULL) { h->oom = 0ULL; break; }
        }
      }
    }
    p = np;
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

u64 full_congruence_dense(FullHdr *h, u64 tick_lim) {
  if (h->scratch_cap < 256ULL || tick_lim == 0ULL) { return 1ULL; }
  if (full_cong_extract_binaries(h) == 20ULL) { return 20ULL; }
  u64 ht_sz = 64ULL;
  while (ht_sz * 8ULL <= h->scratch_cap && ht_sz < 65536ULL) { ht_sz = ht_sz << 1; }
  u64 ht_off = h->scratch_cap - ht_sz;
  u64 g_len = full_cong_extract(h, ht_off, tick_lim);
  if (g_len == 0ULL) { return 1ULL; }
  u32 *repr = (u32 *)h->repr;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = (u32)i; i = i + 1ULL; }
  i = 0ULL;
  while (i < cv) { tmk[i] = 1u; i = i + 1ULL; }
  i = 0ULL;
  while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
  h->res_sz = 0ULL;
  u64 max_passes = (cv << 1) + 4ULL;
  if (max_passes > 0x7FFFFFFFULL) { max_passes = 0x7FFFFFFFULL; }
  u64 pass = 0ULL;
  u64 ticks = 0ULL;
  u64 rehashes = 0ULL;
  while (pass < max_passes && h->inconsistent == 0ULL && ticks < tick_lim) {
    u64 ret = full_cong_work_step(h, g_len, ht_off, ht_sz, (u32)(pass + 1ULL));
    ticks = ticks + (ret >> 2);
    u64 st = ret & 3ULL;
    if (st == 2ULL) { break; }
    if (st == 0ULL) { break; }
    if (h->res_sz * 4ULL >= ht_sz * 3ULL && rehashes < 4ULL) {
      i = 0ULL;
      while (i < ht_sz) { scr[ht_off + i] = 0xFFFFFFFFu; i = i + 1ULL; }
      h->res_sz = 0ULL;
      u32 n_ep = (u32)(pass + 2ULL);
      i = 0ULL;
      while (i < cv) { tmk[i] = n_ep; i = i + 1ULL; }
      rehashes = rehashes + 1ULL;
    }
    pass = pass + 1ULL;
  }
  i = 0ULL;
  while (i < cv) { tmk[i] = 0u; i = i + 1ULL; }
  h->res_sz = 0ULL;
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}
"

def m5CongBinsExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64]⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64]⟩ ]

def m5CongBinsModule : LeanQbe.T.Module :=
  { fns := m5CongBins_fns, externs := m5CongBinsExterns, exits := [] }

theorem full_cong_eb_match_wf : Func.Wf full_cong_eb_match_body := by t_wf_reify
theorem full_cong_extract_binaries_wf : Func.Wf full_cong_extract_binaries_body := by
  t_wf_reify
theorem full_congruence_dense_wf : Func.Wf full_congruence_dense_body := by t_wf_reify

theorem m5CongBins_fns_wf : ∀ f ∈ m5CongBins_fns, f.Wf := by
  simp only [m5CongBins_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_cong_eb_match_wf, full_cong_extract_binaries_wf, full_congruence_dense_wf⟩

theorem m5CongBins_acyclic : m5CongBinsModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5CongBins
