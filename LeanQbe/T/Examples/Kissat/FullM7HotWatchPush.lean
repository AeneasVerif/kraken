module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Inline
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Hot/Cold Split of `full_watch_push_m6` (`FullM7HotWatchPush`)

Purely additive hot/cold split of `FullM6WatchGc.full_watch_push_m6` (exact same canonical
`Full.fullWatchPushSpec` contract and bit-identical behavior, `0` edits to existing compiler
passes, `FullM7InlPolicy`, or existing cert slices):

1. **`full_watch_push_slow_m6` (`m7WatchPushSlowFn`)**: `@[noinline]` cold fallback containing
   the `wlen == 0` empty-stack initialization, proactive 75% `full_wstack_defrag_m6` trigger,
   `retry_fast` post-defrag Cases B/C, Case A grow-with-defrag, and Case D watch relocation/copy
   (`wvec`/`wstk`/`wcap` cached once before Case A; redundant reloads elided).
2. **`full_watch_push_m6` (`m7WatchPushFastFn`)**: leaf-like fast path (`saved = 0` callee-saved
   GPRs in standalone x86-64/Arm64 lowering, `1` cold call to `full_watch_push_slow_m6`, `0`
   loops) checking Case C (sentinel-reuse overwrite) before Case B (tail append) before Case A
   (empty literal init) when `!defrag_needed`, falling back to `full_watch_push_slow_m6` on
   init/defrag/relocation.
3. **`m7HotWatchPushInlPolicy`**: extends `FullM7InlPolicy.m7InlPolicy` with budget `220` for
   `"full_watch_push_m6"` and `"full_watch_push"` (allowing `full_rewatch_range_m6`,
   `full_enter_dense`, `full_add_clause`, `full_add_bin_m6`, etc. to inline the leaf fast path),
   budget `0` and `keepOutOfLine := ["full_watch_push_slow_m6"]` for the cold helper.
4. Exports `m7HotWatchPushModule`, `m7WatchPushSlowFn`, `m7WatchPushFastFn`, `patchM7HotWatchPushFns`,
   and `Wf`/`checkAcyclic` proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7HotWatchPush

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

kissat_c0! m7HotWatchPush "
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

extern void full_wstack_defrag_m6(FullHdr *h);

bool full_watch_push_slow_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  bool retry_fast = false;
  if (h->wlen == 0ULL) {
    if (h->wcap < 1ULL) { return false; }
    u32 *wstk0 = (u32 *)h->watch_stk;
    wstk0[0] = 0u;
    h->wlen = 1ULL;
    retry_fast = true;
  }
  if (h->wlen * 4ULL >= h->wcap * 3ULL && h->wusable * 4ULL >= h->wlen) {
    full_wstack_defrag_m6(h);
    retry_fast = true;
  }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (sz == 0ULL && off == 0ULL) {
    if (c > wcap - h->wlen && h->wusable > 0ULL) { full_wstack_defrag_m6(h); }
    if (c > wcap - h->wlen) { return false; }
    u64 pos = h->wlen;
    wstk[pos] = w0;
    if (cnt == 2u) { wstk[pos + 1ULL] = w1; }
    wvec[(u64)lit << 1] = (u32)pos;
    wvec[((u64)lit << 1) + 1ULL] = cnt;
    h->wlen = pos + c;
    return true;
  }
  if (retry_fast) {
    u64 end = off + sz;
    if (end == h->wlen && c <= wcap - h->wlen) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      h->wlen = end + c;
      return true;
    }
    if (end + c <= h->wlen && wstk[end] == 0xFFFFFFFFu &&
        (cnt == 1u || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
      wstk[end] = w0;
      if (cnt == 2u) { wstk[end + 1ULL] = w1; }
      wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
      if (h->wusable >= c) { h->wusable = h->wusable - c; }
      return true;
    }
  }
  u64 ncap = (sz == 0ULL) ? 2ULL : (sz << 1);
  if (ncap < sz + c) { ncap = sz + c; }
  if (ncap > wcap - h->wlen) {
    if (h->wusable > 0ULL) {
      full_wstack_defrag_m6(h);
      off = (u64)wvec[(u64)lit << 1];
      sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    }
    if (ncap > wcap - h->wlen) { ncap = sz + c; }
    if (ncap > wcap - h->wlen) { return false; }
  }
  u64 dst = h->wlen;
  u64 k = 0ULL;
  while (k < sz) {
    wstk[dst + k] = wstk[off + k];
    wstk[off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  wstk[dst + sz] = w0;
  if (cnt == 2u) { wstk[dst + sz + 1ULL] = w1; }
  k = sz + c;
  while (k < ncap) { wstk[dst + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[(u64)lit << 1] = (u32)dst;
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz + c);
  h->wusable = h->wusable + sz + (ncap - (sz + c));
  h->wlen = dst + ncap;
  return true;
}

bool full_watch_push_m6(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1) || (cnt != 1u && cnt != 2u)) {
    return false;
  }
  u64 c = (u64)cnt;
  u64 wlen = h->wlen;
  if (wlen != 0ULL && (wlen * 4ULL < h->wcap * 3ULL || h->wusable * 4ULL < wlen)) {
    u64 l2 = (u64)lit << 1;
    u32 *wvec0 = (u32 *)h->watch_vec;
    u64 off = (u64)wvec0[l2];
    u64 sz = (u64)wvec0[l2 + 1ULL];
    u64 end = off + sz;
    if (end > 0ULL) {
      u32 *wstk = (u32 *)h->watch_stk;
      if (end + c <= wlen && wstk[end] == 0xFFFFFFFFu &&
          (c == 1ULL || wstk[end + 1ULL] == 0xFFFFFFFFu)) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        if (h->wusable >= c) { h->wusable = h->wusable - c; }
        return true;
      }
      if (end == wlen && c <= h->wcap - wlen) {
        wstk[end] = w0;
        if (c == 2ULL) { wstk[end + 1ULL] = w1; }
        u32 *wvec = (u32 *)h->watch_vec;
        wvec[l2 + 1ULL] = wvec[l2 + 1ULL] + (u32)c;
        h->wlen = end + c;
        return true;
      }
    } else if (c <= h->wcap - wlen) {
      u32 *wstk = (u32 *)h->watch_stk;
      wstk[wlen] = w0;
      if (c == 2ULL) { wstk[wlen + 1ULL] = w1; }
      u32 *wvec = (u32 *)h->watch_vec;
      wvec[l2] = (u32)wlen;
      wvec[l2 + 1ULL] = (u32)c;
      h->wlen = wlen + c;
      return true;
    }
  }
  return full_watch_push_slow_m6(h, lit, w0, w1, (u32)c);
}
"

/-- Cold slow path for `full_watch_push_m6` (empty-stack init, defrag, grow-and-relocate). -/
def m7WatchPushSlowFn : Fn :=
  ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool], full_watch_push_slow_m6_body⟩

/-- Leaf-like hot fast path for `"full_watch_push_m6"`, delegating cold cases to `m7WatchPushSlowFn`. -/
def m7WatchPushFastFn : Fn :=
  ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], full_watch_push_m6_body⟩

/-- Ordered `2`-function list (`[m7WatchPushSlowFn, m7WatchPushFastFn]`) in callee-first order. -/
def m7HotWatchPushFns : List Fn :=
  [m7WatchPushSlowFn, m7WatchPushFastFn]

/-- Standalone module (`2` fns, `1` extern `"full_wstack_defrag_m6"`, `0` exits). -/
def m7HotWatchPushModule : LeanQbe.T.Module :=
  { fns := m7HotWatchPushFns
    externs := [⟨"full_wstack_defrag_m6", [i64], []⟩]
    exits := [] }

/-- `extract_c0_direct`-compatible `before` hook placing `m7WatchPushSlowFn` ahead of `"full_watch_push_m6"`. -/
def m7HotWatchPushBefore : List (Sym × List Fn) :=
  [("full_watch_push_m6", [m7WatchPushSlowFn])]

/-- `extract_c0_direct`-compatible replacement list containing `m7WatchPushFastFn`. -/
def m7HotWatchPushRepl : List Fn :=
  [m7WatchPushFastFn]

/-- Splice `[m7WatchPushSlowFn, m7WatchPushFastFn]` in place of `"full_watch_push_m6"` in a larger fn list. -/
def patchM7HotWatchPushFns (fns : List Fn) : List Fn :=
  fns.flatMap fun f =>
    if f.name = "full_watch_push_m6" then [m7WatchPushSlowFn, m7WatchPushFastFn]
    else [f]

/-- Budget helper extending `m7PgoBudget` so `"full_watch_push_m6"` / `"full_watch_push"` inline
into multi-call callers (`full_rewatch_range_m6`, `full_enter_dense`, `full_add_clause`) while
keeping `"full_watch_push_slow_m6"` out-of-line (`budget = 0`). -/
def m7HotWatchPushBudget (s : Sym) : Nat :=
  if s == "full_watch_push_m6" || s == "full_watch_push" then 220
  else if s == "full_watch_push_slow_m6" then 0
  else m7PgoBudget s

/-- Additive `InlinePolicy` extending `FullM7InlPolicy.m7InlPolicy` for the hot/cold watch-push split. -/
def m7HotWatchPushInlPolicy : InlinePolicy :=
  { m7InlPolicy with
    budget := m7HotWatchPushBudget
    keepOutOfLine := ["full_watch_push_slow_m6"] }

theorem full_watch_push_slow_m6_wf : Func.Wf full_watch_push_slow_m6_body := by t_wf_reify
theorem full_watch_push_m6_wf : Func.Wf full_watch_push_m6_body := by t_wf_reify

theorem m7WatchPushSlowFn_wf : m7WatchPushSlowFn.Wf := full_watch_push_slow_m6_wf
theorem m7WatchPushFastFn_wf : m7WatchPushFastFn.Wf := full_watch_push_m6_wf

theorem m7HotWatchPushFns_wf : ∀ f ∈ m7HotWatchPushFns, f.Wf := by
  intro f hf
  simp only [m7HotWatchPushFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact m7WatchPushSlowFn_wf
  · exact m7WatchPushFastFn_wf

theorem m7HotWatchPush_fns_wf : ∀ f ∈ m7HotWatchPush_fns, f.Wf := by
  intro f hf
  simp only [m7HotWatchPush_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact full_watch_push_slow_m6_wf
  · exact full_watch_push_m6_wf

theorem m7HotWatchPush_acyclic : m7HotWatchPushModule.checkAcyclic = true := by
  t_kernel_rfl

theorem patchM7HotWatchPushFns_wf {fns : List Fn} (h : ∀ f ∈ fns, f.Wf) :
    ∀ f ∈ patchM7HotWatchPushFns fns, f.Wf := by
  intro g hg
  simp only [patchM7HotWatchPushFns, List.mem_flatMap] at hg
  obtain ⟨f, hf, hmem⟩ := hg
  split at hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact m7WatchPushSlowFn_wf
    · exact m7WatchPushFastFn_wf
  · simp only [List.mem_singleton] at hmem
    subst hmem
    exact h g hf

end LeanQbe.T.Examples.Kissat.FullM7HotWatchPush

end
