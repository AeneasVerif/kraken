module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 (`FullM7AnalyzeSort`): `sort_deduced_clause`, Shell `sort_u32`, 6-Step `rephase`

Purely additive C0 extension module on top of frozen `FullHdr` (`144` `u64` words = `1152` bytes;
zero edits to `Full1..6*`, `FullM6*`, or sibling `FullM7*` modules), bringing three core routines
to upstream Kissat 4.0.4 parity:

1. **`full_sort_tmp_m7` (`src/analyze.c:sort_deduced_clause` parity, ascending `(lvl, tpos)`):**
   - Fast exits for `tmp_len <= 2` or `tmp_len > max_vars`, 1-compare specialization for
     `tmp_len == 3`, and low-overhead `(lvl, tpos)` insertion sort for `4 <= tmp_len <= 16`.
   - For `tmp_len > 16`: single pass copies `tmp[1..tmp_len)` into idle `wsort[1..tmp_len)` and
     tracks `[min_l, max_l]`. If `span == 1` or `span > max_vars` or `span > 4 * n`, dispatches
     to inlined `(lvl, tpos)` heapsort (`full_sort_tmp_heap_m7` / `full_sort_tmp_sift_m7`).
     Otherwise performs `O(n + span)` histogram + prefix-sum scatter using `wsort[mv..mv+span)`
     (leaving `work_stk2` strictly untouched) directly into `tmp[1..tmp_len)` followed by
     per-bucket `tpos` tie-breaking (`rlen == 2`, insertion `rlen <= 16`, or heap).
2. **`full_sort_u32_m7` (`src/sort.c` sub-quadratic `u32` sort):**
   - Replaces `O(n^2)` insertion sort with Knuth Shellsort (`h_{k+1} = 3*h_k + 1`), specialized
     for `n <= 1` and `n == 2` and skipping gap setup for `n <= 16`.
3. **`full_rephase_m7` (`src/rephase.c` 6-step stable-only schedule parity):**
   - Guards `if (h->stable == 0ULL) { h->rephase_limit = h->mode_confl_lim; return; }` BEFORE
     backtracking (`cur_level > 0`), restores upstream 6-step cycle
     `(best, walk, inverted, best, walk, original)` (`(rephased - 1) % 6`) with zero-guard
     `if (pb[v] != 0)` on `rephase_best`, `phases -> phases_target` copy, and
     `rephase_limit = conflicts + scale(n * log10^3(n + 9))` via local `full_log10_q16_m7`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7AnalyzeSort "
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

extern void full_backtrack(FullHdr *h, u64 lvl);
extern void full_walk(FullHdr *h);

void full_sort_tmp_sift_m7(u32 *tmp, u32 *lvl, u32 *tpos, u64 start, u64 n) {
  u64 r = start;
  while ((r << 1) + 1ULL < n) {
    u64 c1 = (r << 1) + 1ULL;
    u64 best = c1;
    u32 best_lit = tmp[1ULL + c1];
    u64 vb = ((u64)best_lit) >> 1;
    u32 bl = lvl[vb];
    u32 bt = tpos[vb];
    u64 c2 = c1 + 1ULL;
    if (c2 < n) {
      u32 lit2 = tmp[1ULL + c2];
      u64 v2 = ((u64)lit2) >> 1;
      u32 l2 = lvl[v2];
      u32 t2 = tpos[v2];
      if (bl < l2 || (bl == l2 && bt < t2)) {
        best = c2;
        best_lit = lit2;
        bl = l2;
        bt = t2;
      }
    }
    u32 r_lit = tmp[1ULL + r];
    u64 vr = ((u64)r_lit) >> 1;
    u32 rl = lvl[vr];
    u32 rt = tpos[vr];
    if (rl < bl || (rl == bl && rt < bt)) {
      tmp[1ULL + r] = best_lit;
      tmp[1ULL + best] = r_lit;
      r = best;
    } else {
      return;
    }
  }
}

void full_sort_tmp_heap_m7(u32 *tmp, u32 *lvl, u32 *tpos, u64 tlen) {
  if (tlen <= 2ULL) {
    return;
  }
  u64 n = tlen - 1ULL;
  u64 i = n >> 1;
  while (i > 0ULL) {
    i = i - 1ULL;
    full_sort_tmp_sift_m7(tmp, lvl, tpos, i, n);
  }
  u64 m = n;
  while (m > 1ULL) {
    m = m - 1ULL;
    u32 top = tmp[1];
    tmp[1] = tmp[1ULL + m];
    tmp[1ULL + m] = top;
    full_sort_tmp_sift_m7(tmp, lvl, tpos, 0ULL, m);
  }
}

void full_sort_tmp_m7(FullHdr *h) {
  u64 tlen = h->tmp_len;
  u64 mv = h->max_vars;
  if (tlen <= 2ULL || tlen > mv) {
    return;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  u32 *tpos = (u32 *)h->trail_pos;
  if (tlen == 3ULL) {
    u32 a = tmp[1];
    u32 b = tmp[2];
    u64 va = ((u64)a) >> 1;
    u64 vb = ((u64)b) >> 1;
    u32 la = lvl[va];
    u32 lb = lvl[vb];
    if (la > lb || (la == lb && tpos[va] > tpos[vb])) {
      tmp[1] = b;
      tmp[2] = a;
    }
    return;
  }
  if (tlen <= 16ULL) {
    u64 i = 2ULL;
    while (i < tlen) {
      u32 x = tmp[i];
      u64 vx = ((u64)x) >> 1;
      u32 lx = lvl[vx];
      u32 tx = tpos[vx];
      u64 j = i;
      bool go = true;
      while (go) {
        if (j <= 1ULL) {
          go = false;
        } else {
          u32 prev = tmp[j - 1ULL];
          u64 vp = ((u64)prev) >> 1;
          u32 lp = lvl[vp];
          if (lp < lx || (lp == lx && tpos[vp] <= tx)) {
            go = false;
          } else {
            tmp[j] = prev;
            j = j - 1ULL;
          }
        }
      }
      tmp[j] = x;
      i = i + 1ULL;
    }
    return;
  }
  u32 *sh = (u32 *)h->wsort;
  u32 x1 = tmp[1];
  sh[1] = x1;
  u32 l1 = lvl[((u64)x1) >> 1];
  u32 min_l = l1;
  u32 max_l = l1;
  u64 k = 2ULL;
  while (k < tlen) {
    u32 x = tmp[k];
    sh[k] = x;
    u32 lx = lvl[((u64)x) >> 1];
    if (lx < min_l) {
      min_l = lx;
    }
    if (lx > max_l) {
      max_l = lx;
    }
    k = k + 1ULL;
  }
  u64 span = (u64)max_l - (u64)min_l + 1ULL;
  u64 n = tlen - 1ULL;
  if (span == 1ULL || span > mv || span > (n << 2)) {
    full_sort_tmp_heap_m7(tmp, lvl, tpos, tlen);
    return;
  }
  u64 b = 0ULL;
  while (b < span) {
    sh[mv + b] = 0u;
    b = b + 1ULL;
  }
  k = 1ULL;
  while (k < tlen) {
    u32 x = sh[k];
    u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
    sh[mv + bi] = sh[mv + bi] + 1u;
    k = k + 1ULL;
  }
  u64 pos = 1ULL;
  b = 0ULL;
  while (b < span) {
    u32 c = sh[mv + b];
    sh[mv + b] = (u32)pos;
    pos = pos + (u64)c;
    b = b + 1ULL;
  }
  k = 1ULL;
  while (k < tlen) {
    u32 x = sh[k];
    u64 bi = (u64)lvl[((u64)x) >> 1] - (u64)min_l;
    u64 dst = (u64)sh[mv + bi];
    sh[mv + bi] = (u32)(dst + 1ULL);
    tmp[dst] = x;
    k = k + 1ULL;
  }
  u64 run_beg = 1ULL;
  while (run_beg < tlen) {
    u32 rl = lvl[((u64)tmp[run_beg]) >> 1];
    u64 run_end = run_beg + 1ULL;
    bool same = true;
    while (same) {
      if (run_end >= tlen) {
        same = false;
      } else if (lvl[((u64)tmp[run_end]) >> 1] != rl) {
        same = false;
      } else {
        run_end = run_end + 1ULL;
      }
    }
    u64 rlen = run_end - run_beg;
    if (rlen == 2ULL) {
      u32 a = tmp[run_beg];
      u32 c = tmp[run_beg + 1ULL];
      if (tpos[((u64)a) >> 1] > tpos[((u64)c) >> 1]) {
        tmp[run_beg] = c;
        tmp[run_beg + 1ULL] = a;
      }
    } else if (rlen > 2ULL) {
      if (rlen <= 16ULL) {
        u64 ri = run_beg + 1ULL;
        while (ri < run_end) {
          u32 x = tmp[ri];
          u32 tx = tpos[((u64)x) >> 1];
          u64 rj = ri;
          bool rgo = true;
          while (rgo) {
            if (rj <= run_beg) {
              rgo = false;
            } else {
              u32 prev = tmp[rj - 1ULL];
              if (tpos[((u64)prev) >> 1] <= tx) {
                rgo = false;
              } else {
                tmp[rj] = prev;
                rj = rj - 1ULL;
              }
            }
          }
          tmp[rj] = x;
          ri = ri + 1ULL;
        }
      } else {
        u32 *sub = (u32 *)((u64)tmp + ((run_beg - 1ULL) << 2));
        full_sort_tmp_heap_m7(sub, lvl, tpos, rlen + 1ULL);
      }
    }
    run_beg = run_end;
  }
}

void full_sort_u32_m7(u32 *arr, u32 n) {
  u64 len = (u64)n;
  if (len <= 1ULL) {
    return;
  }
  if (len == 2ULL) {
    u32 a = arr[0];
    u32 b = arr[1];
    if (a > b) {
      arr[0] = b;
      arr[1] = a;
    }
    return;
  }
  u64 gap = 1ULL;
  if (len > 16ULL) {
    u64 lim = len / 3ULL;
    while (gap < lim) {
      gap = gap * 3ULL + 1ULL;
    }
  }
  while (gap >= 1ULL) {
    u64 i = gap;
    while (i < len) {
      u32 x = arr[i];
      u64 j = i;
      bool go = true;
      while (go) {
        if (j < gap) {
          go = false;
        } else {
          u32 prev = arr[j - gap];
          if (prev <= x) {
            go = false;
          } else {
            arr[j] = prev;
            j = j - gap;
          }
        }
      }
      arr[j] = x;
      i = i + 1ULL;
    }
    gap = gap / 3ULL;
  }
}

u64 full_log10_q16_m7(u64 n) {
  if (n <= 1ULL) {
    return 0ULL;
  }
  u64 d = 0ULL;
  u64 p = 1ULL;
  while (d < 18ULL && p <= n / 10ULL) {
    p = p * 10ULL;
    d = d + 1ULL;
  }
  u64 span = 9ULL * p;
  u64 frac = 0ULL;
  if (span > 0ULL && n > p) {
    frac = ((n - p) << 16) / span;
  }
  return (d << 16) + frac;
}

void full_rephase_m7(FullHdr *h) {
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
  u64 nc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
  u64 q = full_log10_q16_m7(nc + 9ULL);
  u64 l2 = (q * q) >> 16;
  u64 l3 = (l2 * q) >> 16;
  u64 scaled = 0ULL;
  if (cnt <= 1000000ULL) {
    scaled = (1000ULL * cnt * l3) >> 16;
  } else {
    u64 nlim = (cnt > 100000000ULL) ? 100000000ULL : cnt;
    scaled = ((1000ULL * nlim) >> 16) * l3;
  }
  h->rephase_limit = h->conflicts + scaled;
}
"

/-- External canonical callees referenced by `m7AnalyzeSort_fns`. -/
def m7AnalyzeSortExterns : List Extern :=
  [ ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_walk", [i64], []⟩ ]

/-- Standalone M7 analyze/sort/rephase module (`6` functions + `2` externs, `0` exits). -/
def m7AnalyzeSortModule : LeanQbe.T.Module :=
  { fns := m7AnalyzeSort_fns, externs := m7AnalyzeSortExterns, exits := [] }

/-! ## Drop-In Replacement `Fn` Handles for M6 / M7 Unification -/

def m7SortTmpSiftFn : Fn :=
  ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], full_sort_tmp_sift_m7_body⟩

def m7SortTmpHeapFn : Fn :=
  ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [], full_sort_tmp_heap_m7_body⟩

def m7SortTmpFn : Fn :=
  ⟨"full_sort_tmp", [i64], [], full_sort_tmp_m7_body⟩

def m7SortU32Fn : Fn :=
  ⟨"full_sort_u32", [i64, i32], [], full_sort_u32_m7_body⟩

def m7Log10Q16Fn : Fn :=
  ⟨"full_log10_q16_m7", [i64], [i64], full_log10_q16_m7_body⟩

def m7RephaseFn : Fn :=
  ⟨"full_rephase", [i64], [], full_rephase_m7_body⟩

theorem full_sort_tmp_sift_m7_wf : Func.Wf full_sort_tmp_sift_m7_body := by t_wf_reify
theorem full_sort_tmp_heap_m7_wf : Func.Wf full_sort_tmp_heap_m7_body := by t_wf_reify
theorem full_sort_tmp_m7_wf : Func.Wf full_sort_tmp_m7_body := by t_wf_reify
theorem full_sort_u32_m7_wf : Func.Wf full_sort_u32_m7_body := by t_wf_reify
theorem full_log10_q16_m7_wf : Func.Wf full_log10_q16_m7_body := by t_wf_reify
theorem full_rephase_m7_wf : Func.Wf full_rephase_m7_body := by t_wf_reify

theorem m7AnalyzeSort_fns_wf : ∀ f ∈ m7AnalyzeSort_fns, f.Wf := by
  simp only [m7AnalyzeSort_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_sort_tmp_sift_m7_wf, full_sort_tmp_heap_m7_wf, full_sort_tmp_m7_wf,
    full_sort_u32_m7_wf, full_log10_q16_m7_wf, full_rephase_m7_wf⟩

theorem m7AnalyzeSort_acyclic : m7AnalyzeSortModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
