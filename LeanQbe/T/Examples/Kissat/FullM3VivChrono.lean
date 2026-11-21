module

public import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M3a Upgrades: Vivify Cursor + Tier-3, Chrono `lits[1]` Swap, Glue Promotion

Standalone M3a C0 upgrades spliced onto the M2 `FullFast.fastFns` (`196` fns) by name, keeping
the byte-identical `144`-word `FullHdr` layout (`0` edits to `Full*` / `FullFast*`):

1. **Persistent wrap-around `vivify` cursor (`full_vivify`)**: `PH_VIV` bits now persist across
   calls (Kissat's per-clause `vivify` cursor bit). Each call skips already-vivified clauses of the
   requested tier, so clauses past the first `budget` candidates are reached on later calls. Only
   once a scan reaches the arena end are the `PH_VIV` bits of *that tier's* clauses cleared
   (wrap-around), replacing the M2 unconditional full-arena wipe.
2. **Tier-3 vivification (`full_probe_tail`)**: schedules `tier1, tier2, tier3, irred`
   (`vivifytier3 = 1`) instead of skipping redundant clauses with `glue > tier2`.
3. **Chronological `lits[1]` max-level watch swap (`full_prop_lit`)**: wraps the M2 `FastCore`
   BCP (renamed `full_prop_lit_raw`). After propagating a literal whose level is below
   `cur_level`, every newly assigned literal with a large reason clause gets the highest-level
   false literal swapped into `lits[1]` and watched (Kissat/CaDiCaL chrono watch invariant).
4. **Reason glue promotion (`full_analyze_rsn`, `promote.c`)**: redundant reason clauses with
   `glue > tier1` recompute their glue (distinct levels, bounded by `min(glue - 1, tier2, 32)`)
   and lower the stored glue when smaller, before the `used` update.
5. **Stable-only reluctant doubling (`full_tick_rel`)**: `full_tick_rel` is a no-op unless
   `h->stable != 0`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3VivChrono

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m3VivChrono "
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

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_VIV  0x00100000u
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern bool full_analyze_lit(FullHdr *h, u32 lit, u32 skip_var);
extern bool full_prop_lit_raw(FullHdr *h, u32 lit, u64 ignore_ref);
extern u64 full_propagate(FullHdr *h);
extern u64 full_viv_clause(FullHdr *h, u32 cref);
extern u64 full_transitive(FullHdr *h, u64 tick_lim);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_min_u64(u64 a, u64 b);

void full_tick_rel(FullHdr *h) {
  if (h->stable == 0ULL || h->rel_period == 0ULL || h->rel_trigger != 0ULL) { return; }
  if (h->rel_wait > 0ULL) { h->rel_wait = h->rel_wait - 1ULL; }
  if (h->rel_wait > 0ULL) { return; }
  u64 u = h->rel_u;
  u64 v = h->rel_v;
  if (u == 0ULL || v == 0ULL) { u = 1ULL; v = 1ULL; }
  if ((u & (0ULL - u)) == v) { u = u + 1ULL; v = 1ULL; } else { v = v << 1ULL; }
  if (v == 0ULL || v > (1ULL << 30) || h->rel_period > (1ULL << 30)) { u = 1ULL; v = 1ULL; }
  u64 wait = v * h->rel_period;
  if (h->rel_limit > 0ULL && wait > h->rel_limit) { u = 1ULL; v = 1ULL; wait = h->rel_period; }
  h->rel_trigger = 1ULL; h->rel_wait = wait; h->rel_u = u; h->rel_v = v;
}

bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn == 0xFFFFFFFFu) { return false; }
  if ((rsn & PW_BIN_FLAG) != 0u) {
    return full_analyze_lit(h, rsn & PW_LIT_MASK, skip_var);
  }
  u32 *ar = (u32 *)h->arena;
  if ((u64)rsn + 3ULL > h->arena_len) { return false; }
  u32 hdr = ar[rsn];
  u32 sz = ar[(u64)rsn + 2ULL];
  if (sz < 3u || (u64)rsn + 3ULL + (u64)sz > h->arena_len) { return false; }
  if ((hdr & PH_RED) != 0u) {
    u64 glue = (u64)(hdr & PH_GLUE_MASK);
    if (glue > h->tier1 && glue > 1ULL) {
      u64 lim = glue - 1ULL;
      if (lim > h->tier2) { lim = h->tier2; }
      if (lim > 32ULL) { lim = 32ULL; }
      u32 *lv = (u32 *)h->level;
      u64 cv = h->cur_vars;
      u64 ng = 0ULL; u64 lo = 0ULL; bool more = true;
      while (more && ng <= lim) {
        u64 best = 0xFFFFFFFFFFFFFFFFULL; u32 k = 0u;
        while (k < sz) {
          u64 kv = (u64)(ar[(u64)rsn + 3ULL + (u64)k] >> 1);
          if (kv < cv) {
            u64 kl = (u64)lv[kv];
            if (kl >= lo && kl < best) { best = kl; }
          }
          k = k + 1u;
        }
        if (best == 0xFFFFFFFFFFFFFFFFULL) { more = false; }
        else { ng = ng + 1ULL; lo = best + 1ULL; }
      }
      if (!more && ng > 0ULL && ng < glue) {
        hdr = (hdr & (~PH_GLUE_MASK)) | (u32)ng;
        ar[rsn] = hdr;
        glue = ng;
      }
    }
    u32 *gu = (u32 *)h->glue_used;
    u64 gi = (glue > 63ULL) ? 63ULL : glue;
    if (gu[gi] < 0xFFFFFFFFu) { gu[gi] = gu[gi] + 1u; }
    u32 new_u = (glue <= h->tier2) ? 31u : 1u;
    u32 old_u = (hdr >> 27) & 31u;
    if (new_u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (new_u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}

bool full_prop_lit(FullHdr *h, u32 lit, u64 ignore_ref) {
  u64 t0 = h->trail_end;
  if (!full_prop_lit_raw(h, lit, ignore_ref)) { return false; }
  u64 te = h->trail_end;
  u64 nlits = h->cur_vars << 1;
  if (t0 >= te || (u64)lit >= nlits) { return true; }
  u32 *lvl = (u32 *)h->level;
  if ((u64)lvl[lit >> 1] >= h->cur_level) { return true; }
  u32 *trl = (u32 *)h->trail;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u64 alen = h->arena_len;
  u64 t = t0;
  while (t < te) {
    u32 ol = trl[t];
    t = t + 1ULL;
    if ((u64)ol >= nlits) { continue; }
    u32 r = rsns[ol >> 1];
    if (r == 0xFFFFFFFFu || (r & PW_BIN_FLAG) != 0u) { continue; }
    if ((u64)r + 3ULL > alen) { continue; }
    u32 hdr = ar[r]; u32 csz = ar[(u64)r + 2ULL];
    u64 cb = (u64)r + 3ULL;
    if ((hdr & PH_GARB) != 0u || csz < 3u || cb + (u64)csz > alen) { continue; }
    if (ar[cb] != ol) { continue; }
    u32 l1 = ar[cb + 1ULL];
    if ((u64)l1 >= nlits) { continue; }
    u32 best = lvl[l1 >> 1]; u32 bi = 1u; u32 k = 2u;
    while (k < csz) {
      u32 ck = ar[cb + (u64)k];
      if ((u64)ck < nlits) {
        u32 kl = lvl[ck >> 1];
        if (kl > best) { best = kl; bi = k; }
      }
      k = k + 1u;
    }
    if (bi != 1u) {
      u32 nw = ar[cb + (u64)bi];
      if (!full_watch_push(h, nw, ol & PW_LIT_MASK, r, 2u)) { h->oom = 1ULL; return false; }
      ar[cb + 1ULL] = nw; ar[cb + (u64)bi] = l1;
    }
  }
  return true;
}

u64 full_vivify(FullHdr *h, u64 tier_mode, u64 budget) {
  if (budget == 0ULL) { return 1ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL; u32 *ar = (u32 *)h->arena;
  u64 p = 0ULL; u64 res = 1ULL;
  while (p < h->arena_len && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u32 hdr = ar[p]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_VIV)) == 0u) {
      bool is_red = ((hdr & PH_RED) != 0u);
      u64 glue = (u64)(hdr & PH_GLUE_MASK);
      bool take = false;
      if (tier_mode == 0ULL) { take = !is_red; }
      else if (tier_mode == 1ULL) { take = is_red && glue <= h->tier1; }
      else if (tier_mode == 2ULL) { take = is_red && glue > h->tier1 && glue <= h->tier2; }
      else { take = is_red && glue > h->tier2; }
      if (take) {
        budget = budget - 1ULL;
        u64 vc = full_viv_clause(h, (u32)p);
        if (vc == 20ULL) { res = 20ULL; break; }
        if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      }
    }
    p = np;
  }
  if (res == 1ULL && p >= h->arena_len) {
    p = 0ULL;
    while (p < h->arena_len) {
      u32 hdr = ar[p];
      if ((hdr & (PH_GARB | PH_VIV)) == PH_VIV) {
        bool is_red = ((hdr & PH_RED) != 0u);
        u64 glue = (u64)(hdr & PH_GLUE_MASK);
        bool take = false;
        if (tier_mode == 0ULL) { take = !is_red; }
        else if (tier_mode == 1ULL) { take = is_red && glue <= h->tier1; }
        else if (tier_mode == 2ULL) { take = is_red && glue > h->tier1 && glue <= h->tier2; }
        else { take = is_red && glue > h->tier2; }
        if (take) { ar[p] = hdr & (~PH_VIV); }
      }
      p = (u64)full_arena_next(h, (u32)p);
    }
  }
  h->probing = 0ULL; return res;
}

u64 full_probe_tail(FullHdr *h, u64 dticks) {
  if (h->num_binary > 0ULL && full_transitive(h, dticks * 2ULL + 20000ULL) == 20ULL) {
    return 20ULL;
  }
  u64 pbud = full_min_u64(8ULL + (dticks >> 10), 64ULL);
  if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) { return 20ULL; }
  u64 v1 = full_min_u64(32ULL + (dticks >> 7), 1024ULL);
  u64 v0 = full_min_u64(16ULL + (dticks >> 8), 512ULL);
  if (full_vivify(h, 1ULL, v1) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 2ULL, v1) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 3ULL, v0) == 20ULL) { return 20ULL; }
  if (full_vivify(h, 0ULL, v0) == 20ULL) { return 20ULL; }
  return 1ULL;
}
"

/-- External callee signatures referenced by `m3VivChrono_fns`. -/
def m3Externs : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool]⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_viv_clause", [i64, i32], [i64]⟩
  , ⟨"full_transitive", [i64, i64], [i64]⟩
  , ⟨"full_probe_run", [i64, i64], [i64]⟩
  , ⟨"full_min_u64", [i64, i64], [i64]⟩ ]

/-- Standalone M3a module (`5` fns, all callees external). -/
def m3Module : LeanQbe.T.Module :=
  { fns := m3VivChrono_fns, externs := m3Externs, exits := [] }

theorem full_tick_rel_wf : Func.Wf full_tick_rel_body := by t_wf_reify
theorem full_analyze_rsn_wf : Func.Wf full_analyze_rsn_body := by t_wf_reify
theorem full_prop_lit_wf : Func.Wf full_prop_lit_body := by t_wf_reify
theorem full_vivify_wf : Func.Wf full_vivify_body := by t_wf_reify
theorem full_probe_tail_wf : Func.Wf full_probe_tail_body := by t_wf_reify

theorem m3_fns_wf : ∀ f ∈ m3VivChrono_fns, f.Wf := by
  simp only [m3VivChrono_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_tick_rel_wf, full_analyze_rsn_wf, full_prop_lit_wf, full_vivify_wf,
    full_probe_tail_wf⟩

theorem m3_acyclic : m3Module.checkAcyclic = true := by
  t_kernel_rfl

/-! ## Splicing onto the M2 `FullFast.fastFns` (`196` → `197` functions) -/

/-- The M2 `FastCore` BCP renamed so that the M3 chrono wrapper can take its name. -/
def propLitRawFn (f : Fn) : Fn := { f with name := "full_prop_lit_raw" }

def m3TickRelFn : Fn := ⟨"full_tick_rel", _, _, full_tick_rel_body⟩
def m3AnalyzeRsnFn : Fn := ⟨"full_analyze_rsn", _, _, full_analyze_rsn_body⟩
def m3PropLitFn : Fn := ⟨"full_prop_lit", _, _, full_prop_lit_body⟩
def m3VivifyFn : Fn := ⟨"full_vivify", _, _, full_vivify_body⟩
def m3ProbeTailFn : Fn := ⟨"full_probe_tail", _, _, full_probe_tail_body⟩

/-- Name-directed splice: replaces the `4` upgraded M2 functions and inserts the chrono wrapper
directly after the renamed `FastCore` BCP. -/
def m3Splice (f : Fn) : List Fn :=
  if f.name = "full_prop_lit" then [propLitRawFn f, m3PropLitFn]
  else if f.name = "full_tick_rel" then [m3TickRelFn]
  else if f.name = "full_analyze_rsn" then [m3AnalyzeRsnFn]
  else if f.name = "full_vivify" then [m3VivifyFn]
  else if f.name = "full_probe_tail" then [m3ProbeTailFn]
  else [f]

/-- Unified M3a function list (`197` functions in topological call order). -/
def m3Fns : List Fn := FullFast.fastFns.flatMap m3Splice

/-- Closed M3a compilation module (`externs := []`, `exits := []`). -/
def m3FullModule : LeanQbe.T.Module :=
  { fns := m3Fns, externs := [], exits := [] }

theorem m3Splice_wf (f : Fn) (hf : f.Wf) : ∀ g ∈ m3Splice f, g.Wf := by
  intro g hg
  unfold m3Splice at hg
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hf
    · exact full_prop_lit_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; exact full_tick_rel_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_analyze_rsn_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; exact full_vivify_wf
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
    exact full_probe_tail_wf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; exact hf

theorem m3Fns_wf : ∀ f ∈ m3Fns, f.Wf := by
  intro g hg
  obtain ⟨f, hf, hg⟩ := List.mem_flatMap.mp hg
  exact m3Splice_wf f (FullFast.fastFns_wf f hf) g hg

theorem m3Fns_length : m3Fns.length = 197 := by t_kernel_rfl

theorem m3Full_acyclic : m3FullModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM3VivChrono
