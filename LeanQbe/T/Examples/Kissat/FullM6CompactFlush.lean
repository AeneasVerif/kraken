module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M6 Compact, Root Trail Flush & Binary Dedup (`FullM6CompactFlush`)

Standalone drop-in C0 replacements covering the non-watch-gc `RC-23` Kissat M6 parity upgrades
with zero `FullHdr` layout churn (`144` words frozen) and zero edits to landed `Full*.lean` files:

1. `full_flush_trail` & `full_compact_flush_m6cf`: clean root-level trail flush matching upstream
   Kissat `src/trail.c` / `src/backtrack.c` / `src/compact.c` (backtrack to level 0, OOM guard,
   level-0 propagation with `inconsistent = 1` on conflict, `unflushed`/`confl_*` reset, and
   fixpoint arena sweep loop for compaction).
2. `full_sweep_bins_m6cf` & `full_enter_dense_m6cf`: `wsort`-stamped `O(1)` binary clause
   deduplication + tautology drop + empty-offset zeroing on binary sweeps and dense entry
   (preserving `FullFastSched` `prop_done` completeness and `RC-02` OOM safety).
3. `full_compact_needed_m6cf` & `full_compact_mark_live_m6cf`: upstream `10%` compaction trigger
   (`dead * 10ULL > cv`, `src/collect.c:633-643`) + isolated-variable elimination (`map[v] = 0u`
   initialization so unassigned variables with `0` remaining occurrences are compacted out).
4. `full_extend_push2_m6cf` & `full_extend_push_cl_m6cf`: root-false literal skipping in witness
   extension pushing (`src/weaken.c:13-27`) with overflow-safe exact capacity checks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6CompactFlush

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m6CompactFlush "
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

#define PH_GARB      0x00080000u
#define PH_RED       0x00400000u
#define PW_BIN_FLAG  0x80000000u
#define PW_LIT_MASK  0x7FFFFFFFu
#define EXT_BLK_FLAG 0x80000000u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);

u64 full_flush_trail(FullHdr *h) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->propagated < h->trail_end) {
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { h->inconsistent = 1ULL; return 20ULL; }
    if (pr != 0ULL || h->oom != 0ULL) { return 0ULL; }
  }
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  return 1ULL;
}

void full_sweep_bins_m6cf(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *seen = (u32 *)h->wsort;
  bool prop_done = (h->propagated >= h->trail_end);
  u64 si = 0ULL;
  while (si < nlits) { seen[si] = 0xFFFFFFFFu; si = si + 1ULL; }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) {
      wvec[l << 1] = 0u;
      l = l + 1ULL;
      continue;
    }
    bool lsat = (lvl[l >> 1] == 0u && vals[l] > (i8)0);
    bool lfix = lsat || (prop_done && lvl[l >> 1] == 0u && vals[l] < (i8)0);
    u32 ltag = (u32)l;
    u32 lneg = ltag ^ 1u;
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        bool osat = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] > (i8)0);
        bool ofix = osat ||
          (prop_done && (u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
        bool drop = lfix || ofix || ot == lneg ||
          ((u64)ot < nlits && seen[ot] == ltag);
        if (drop) {
          if (l < (u64)ot && h->num_binary > 0ULL) {
            h->num_binary = h->num_binary - 1ULL;
          }
        } else {
          if ((u64)ot < nlits) { seen[ot] = ltag; }
          wstk[q] = w0; q = q + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    if (q == off) {
      wvec[l << 1] = 0u;
      wvec[(l << 1) + 1ULL] = 0u;
    } else {
      wvec[(l << 1) + 1ULL] = (u32)(q - off);
    }
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  full_wstack_defrag(h);
}

bool full_enter_dense_m6cf(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return false; }
  if (h->dense_mode != 0ULL) { return true; }
  if (full_flush_trail(h) != 1ULL) { return false; }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

bool full_compact_needed_m6cf(FullHdr *h) {
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL) { return false; }
  u64 cv = h->cur_vars;
  if (cv == 0ULL || cv <= h->unassigned) { return false; }
  u64 dead = cv - h->unassigned;
  return (dead * 10ULL > cv);
}

u64 full_compact_flush_m6cf(FullHdr *h) {
  u64 fr = full_flush_trail(h);
  if (fr != 1ULL) { return fr; }
  while (true) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 0ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL || h->oom != 0ULL) { return 0ULL; }
    if (sr == 0ULL && h->propagated >= h->trail_end) { break; }
    u64 pr = full_flush_trail(h);
    if (pr != 1ULL) { return pr; }
  }
  h->unflushed = 0ULL;
  return 1ULL;
}

void full_compact_mark_live_m6cf(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *map = (u32 *)h->work_stk1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 v = 0ULL;
  while (v < cv) {
    map[v] = 0u;
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
            vals[l] == (i8)0 && vals[ot] == (i8)0) {
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
      u32 ucnt = 0u;
      u32 i = 0u;
      while (i < csz) {
        u32 lit = ar[pos + 3ULL + (u64)i];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) { ucnt = ucnt + 1u; }
        }
        i = i + 1u;
      }
      if (!sat && ucnt >= 1u) {
        i = 0u;
        while (i < csz) {
          u32 lit = ar[pos + 3ULL + (u64)i];
          if ((u64)lit < nlits && vals[lit] == (i8)0) { map[lit >> 1] = 1u; }
          i = i + 1u;
        }
      }
    }
    pos = npos;
  }
}

bool full_extend_push2_m6cf(FullHdr *h, u32 blk_lit, u32 other) {
  u64 nlits = h->cur_vars << 1;
  u32 ot = other & PW_LIT_MASK;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  bool skip_ot = ((u64)ot < nlits && lvl[ot >> 1] == 0u && vals[ot] < (i8)0);
  u64 need = skip_ot ? 1ULL : 2ULL;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = (blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG;
  if (!skip_ot) { ext[p + 1ULL] = ot; }
  h->extend_len = p + need;
  return true;
}

bool full_extend_push_cl_m6cf(FullHdr *h, u32 blk_lit, u32 cref) {
  u32 *ar = (u32 *)h->arena;
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 sz = ar[(u64)cref + 2ULL];
  if ((u64)cref + 3ULL + (u64)sz > h->arena_len) { return false; }
  u64 nlits = h->cur_vars << 1;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 bl = blk_lit & PW_LIT_MASK;
  u64 keep = 0ULL;
  u32 i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl && !((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
      keep = keep + 1ULL;
    }
    i = i + 1u;
  }
  u64 need = 1ULL + keep;
  if (h->extend_len > h->extend_cap || need > h->extend_cap - h->extend_len) {
    return false;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = bl | EXT_BLK_FLAG;
  p = p + 1ULL;
  i = 0u;
  while (i < sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i] & PW_LIT_MASK;
    if (lit != bl && !((u64)lit < nlits && lvl[lit >> 1] == 0u && vals[lit] < (i8)0)) {
      ext[p] = lit; p = p + 1ULL;
    }
    i = i + 1u;
  }
  h->extend_len = p;
  return true;
}
"

/-- External callee signatures referenced by `m6CompactFlush_fns`. -/
def m6CompactFlushExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_sweep_bins", [i64], []⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩ ]

/-- Standalone M6 Wave-2 compact/flush/dedup module (`8` functions + `7` externs, `0` exits). -/
def m6CompactFlushModule : LeanQbe.T.Module :=
  { fns := m6CompactFlush_fns, externs := m6CompactFlushExterns, exits := [] }

/-- Drop-in renamed `Fn` handles matching canonical `FullM4`/`FullM5`/`FullM6` splice slots. -/
def m6cfFlushTrailFn : Fn := ⟨"full_flush_trail", [i64], [i64], full_flush_trail_body⟩
def m6cfSweepBinsFn : Fn := ⟨"full_sweep_bins", [i64], [], full_sweep_bins_m6cf_body⟩
def m6cfEnterDenseFn : Fn := ⟨"full_enter_dense", [i64], [.bool], full_enter_dense_m6cf_body⟩
def m6cfCompactNeededFn : Fn :=
  ⟨"full_compact_needed", [i64], [.bool], full_compact_needed_m6cf_body⟩
def m6cfCompactFlushFn : Fn := ⟨"full_compact_flush", [i64], [i64], full_compact_flush_m6cf_body⟩
def m6cfCompactMarkLiveFn : Fn :=
  ⟨"full_compact_mark_live", [i64], [], full_compact_mark_live_m6cf_body⟩
def m6cfExtendPush2Fn : Fn :=
  ⟨"full_extend_push2", [i64, i32, i32], [.bool], full_extend_push2_m6cf_body⟩
def m6cfExtendPushClFn : Fn :=
  ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], full_extend_push_cl_m6cf_body⟩

theorem full_flush_trail_wf : Func.Wf full_flush_trail_body := by t_wf_reify
theorem full_sweep_bins_m6cf_wf : Func.Wf full_sweep_bins_m6cf_body := by t_wf_reify
theorem full_enter_dense_m6cf_wf : Func.Wf full_enter_dense_m6cf_body := by t_wf_reify
theorem full_compact_needed_m6cf_wf : Func.Wf full_compact_needed_m6cf_body := by t_wf_reify
theorem full_compact_flush_m6cf_wf : Func.Wf full_compact_flush_m6cf_body := by t_wf_reify
theorem full_compact_mark_live_m6cf_wf : Func.Wf full_compact_mark_live_m6cf_body := by t_wf_reify
theorem full_extend_push2_m6cf_wf : Func.Wf full_extend_push2_m6cf_body := by t_wf_reify
theorem full_extend_push_cl_m6cf_wf : Func.Wf full_extend_push_cl_m6cf_body := by t_wf_reify

theorem m6CompactFlush_fns_wf : ∀ f ∈ m6CompactFlush_fns, f.Wf := by
  simp only [m6CompactFlush_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_flush_trail_wf, full_sweep_bins_m6cf_wf, full_enter_dense_m6cf_wf,
    full_compact_needed_m6cf_wf, full_compact_flush_m6cf_wf, full_compact_mark_live_m6cf_wf,
    full_extend_push2_m6cf_wf, full_extend_push_cl_m6cf_wf⟩

theorem m6CompactFlush_acyclic : m6CompactFlushModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6CompactFlush
