module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Bump, Knuth LCG RNG & Limit Scaling (`FullM7Bump`)

Additive Kissat 4.0.4 parity module matching `src/random.h`, `src/kimits.c`,
`src/analyze.c`, and `src/bump.c`:
1. `full_rng_next_m7` (`src/random.h:10-18`, `kissat_next_random32`): updates 64-bit Knuth LCG
   `state' = 6364136223846793005ULL * state + 1442695040888963407ULL` and returns `state' >> 32`
   (upper 32 bits, avoiding LCG bit-0 alternation on `& 1` callers).
2. `full_log10_q16_m7` & `full_scale_delta_m7` (`src/kimits.c:39-57`): `Q16` integer `log10`
   approximation (`0%` error at powers of `10`, `~1e-5` between powers) computing
   `fff = 4.5 * (log10(BINIRR_CLAUSES + 10) - 5)^2 + 25` with overflow-safe `u64` scaling and
   guaranteed `delta <= scaled`.
3. `full_bump_sift_m7`, `full_bump_sort_stamps_m7`, `full_bump_reasons_m7`, and
   `full_bump_analyzed_m7` (`src/bump.c` + `src/analyze.c`):
   - Early return when `h->probing != 0ULL`.
   - Faithful `bumpreasons` (`bumpreasonslimit = 10`, rollback & unmarking above `10 * saved`,
     bounds-guarded against `work_stk1` / `cur_vars` / `arena_len`).
   - Focused vs stable split:
     * `h->stable == 0ULL`: heapsort analyzed variables ascending by `q_stamp[v]` via
       `full_bump_sort_stamps_m7` and call ONLY `full_queue_mtf` (no VSIDS score/decay work).
     * `h->stable != 0ULL`: bump ONLY EVSIDS scores via `full_bump_var` + `full_bump_decay`
       (no VMTF sort or MTF work).
4. Drop-in handles: `m7RngNextFn`, `m7ScaleDeltaFn`, `m7ScaleDeltaM6Fn`, `m7BumpAnalyzedFn`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Bump

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7_bump "
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

#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE   1u

extern void full_bump_var(FullHdr *h, u32 v);
extern void full_bump_decay(FullHdr *h);
extern void full_queue_mtf(FullHdr *h, u32 v);

u64 full_rng_next_m7(FullHdr *h) {
  u64 x = h->rng_state * 6364136223846793005ULL + 1442695040888963407ULL;
  h->rng_state = x;
  return x >> 32;
}

u64 full_log10_q16_m7(u64 x) {
  if (x < 10ULL) { return 0ULL; }
  u64 d = 1ULL;
  u64 p = 10ULL;
  while (d < 19ULL && p <= x / 10ULL) {
    d = d + 1ULL;
    p = p * 10ULL;
  }
  u64 m = 1000000ULL;
  if (p < 1000000ULL) {
    m = x * (1000000ULL / p);
  } else {
    m = x / (p / 1000000ULL);
  }
  u64 frac = 0ULL;
  u64 step = 32768ULL;
  u64 k = 0ULL;
  while (k < 16ULL) {
    m = (m * m) / 1000000ULL;
    if (m >= 10000000ULL) {
      m = m / 10ULL;
      frac = frac + step;
    }
    step = step >> 1;
    k = k + 1ULL;
  }
  return d * 65536ULL + frac;
}

u64 full_scale_delta_m7(FullHdr *h, u64 delta) {
  if (delta == 0ULL) { return 0ULL; }
  u64 ir = h->num_irred;
  u64 bn = h->num_binary;
  u64 clauses = (ir > 0xFFFFFFFFFFFFFFFFULL - bn) ? 0xFFFFFFFFFFFFFFFFULL : (ir + bn);
  u64 arg = (clauses > 0xFFFFFFFFFFFFFFF5ULL) ? 0xFFFFFFFFFFFFFFFFULL : (clauses + 10ULL);
  u64 l = full_log10_q16_m7(arg);
  if (l < 65536ULL) { l = 65536ULL; }
  if (l > 1310720ULL) { l = 1310720ULL; }
  u64 target = 327680ULL;
  u64 f_abs = (l >= target) ? (l - target) : (target - l);
  u64 fff_q16 = ((9ULL * f_abs * f_abs) >> 17) + 1638400ULL;
  u64 lim = 0xFFFFFFFFFFFFFFFFULL / fff_q16;
  if (delta <= lim) {
    return (fff_q16 * delta) >> 16;
  }
  u64 hi = delta >> 16;
  if (hi <= lim) {
    u64 lo = delta & 0xFFFFULL;
    u64 q1 = hi * fff_q16;
    u64 q2 = (lo * fff_q16) >> 16;
    if (q1 > 0xFFFFFFFFFFFFFFFFULL - q2) { return 0xFFFFFFFFFFFFFFFFULL; }
    return q1 + q2;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

void full_bump_sift_m7(FullHdr *h, u64 start, u64 n) {
  u64 cv = h->cur_vars;
  if (n == 0ULL || start >= n || n > cv || cv > h->max_vars) { return; }
  u32 *ws = (u32 *)h->work_stk1;
  u32 *qs = (u32 *)h->q_stamp;
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cl = ws[ch];
    u32 cq = ((u64)cl < cv) ? qs[cl] : 0u;
    if (ch + 1ULL < n) {
      u32 sl = ws[ch + 1ULL];
      u32 sq = ((u64)sl < cv) ? qs[sl] : 0u;
      if (sq > cq || (sq == cq && sl > cl)) {
        ch = ch + 1ULL;
        cl = sl;
        cq = sq;
      }
    }
    u32 rl = ws[root];
    u32 rq = ((u64)rl < cv) ? qs[rl] : 0u;
    if (rq > cq || (rq == cq && rl >= cl)) { break; }
    ws[root] = cl;
    ws[ch] = rl;
    root = ch;
  }
}

void full_bump_sort_stamps_m7(FullHdr *h, u64 n) {
  u64 cv = h->cur_vars;
  if (n <= 1ULL || n > cv || cv > h->max_vars) { return; }
  u64 start = n >> 1;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_bump_sift_m7(h, start, n);
  }
  u64 end = n;
  u32 *ws = (u32 *)h->work_stk1;
  while (end > 1ULL) {
    end = end - 1ULL;
    u32 tmp = ws[0];
    ws[0] = ws[end];
    ws[end] = tmp;
    full_bump_sift_m7(h, 0ULL, end);
  }
}

void full_bump_reasons_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv > h->max_vars) { cv = h->max_vars; }
  u64 tl = h->tmp_len;
  if (tl > cv) { tl = cv; }
  u64 saved = h->min_clr_len;
  if (saved >= cv || tl == 0ULL) { return; }
  u64 lim = (saved > 0x1999999999999999ULL) ? 0xFFFFFFFFFFFFFFFFULL : (saved * 10ULL);
  u64 alen = h->arena_len;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *rsns = (u32 *)h->reason;
  u32 *lvl = (u32 *)h->level;
  u8 *mrk = (u8 *)h->mark;
  u32 *ana = (u32 *)h->work_stk1;
  u32 *ar = (u32 *)h->arena;
  u64 i = 0ULL;
  while (i < tl) {
    u32 lit = tmp[i];
    u32 uv = lit >> 1;
    if ((u64)uv < cv) {
      u32 rsn = rsns[uv];
      if (rsn != 0xFFFFFFFFu) {
        if ((rsn & PW_BIN_FLAG) != 0u) {
          u32 olit = rsn & PW_LIT_MASK;
          u32 ov = olit >> 1;
          if ((u64)ov < cv && ov != uv && lvl[ov] > 0u && mrk[ov] == (u8)0) {
            if (h->min_clr_len < cv) {
              mrk[ov] = (u8)1;
              ana[h->min_clr_len] = ov;
              h->min_clr_len = h->min_clr_len + 1ULL;
            }
          }
        } else if (alen >= 3ULL && (u64)rsn <= alen - 3ULL) {
          u32 sz = ar[(u64)rsn + 2ULL];
          if (sz >= 3u && (u64)sz <= alen - ((u64)rsn + 3ULL)) {
            u64 k = 0ULL;
            while (k < (u64)sz) {
              u32 olit = ar[(u64)rsn + 3ULL + k];
              u32 ov = olit >> 1;
              if ((u64)ov < cv && ov != uv && lvl[ov] > 0u && mrk[ov] == (u8)0) {
                if (h->min_clr_len < cv) {
                  mrk[ov] = (u8)1;
                  ana[h->min_clr_len] = ov;
                  h->min_clr_len = h->min_clr_len + 1ULL;
                }
              }
              k = k + 1ULL;
            }
          }
        }
      }
    }
    i = i + 1ULL;
  }
  if (h->min_clr_len > lim) {
    while (h->min_clr_len > saved) {
      h->min_clr_len = h->min_clr_len - 1ULL;
      u32 rv = ana[h->min_clr_len];
      if ((u64)rv < cv) { mrk[rv] = (u8)0; }
    }
  }
}

void full_bump_analyzed_m7(FullHdr *h) {
  if (h->probing != 0ULL) { return; }
  full_bump_reasons_m7(h);
  u64 cnt = h->min_clr_len;
  u64 cv = h->cur_vars;
  if (cv > h->max_vars) { return; }
  if (cnt > cv) { cnt = cv; }
  u32 *ana = (u32 *)h->work_stk1;
  u32 *fl = (u32 *)h->flags;
  if (h->stable == 0ULL) {
    full_bump_sort_stamps_m7(h, cnt);
    u64 iv = 0ULL;
    while (iv < cnt) {
      u32 bv = ana[iv];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_queue_mtf(h, bv);
      }
      iv = iv + 1ULL;
    }
  } else {
    u64 iv = 0ULL;
    while (iv < cnt) {
      u32 bv = ana[iv];
      if ((u64)bv < cv && (fl[bv] & FL_ACTIVE) != 0u) {
        full_bump_var(h, bv);
      }
      iv = iv + 1ULL;
    }
    full_bump_decay(h);
  }
}
"

/-- Canonical external callee list for `m7BumpModule`. -/
def m7BumpExterns : List Extern :=
  [ ⟨"full_bump_var", [i64, i32], []⟩
  , ⟨"full_bump_decay", [i64], []⟩
  , ⟨"full_queue_mtf", [i64, i32], []⟩ ]

/-- Standalone `m7Bump` function list (`7` functions). -/
def m7BumpFns : List Fn := m7_bump_fns

/-- Drop-in `Fn` handle preserving `"full_rng_next"` (`[i64] -> [i64]`). -/
def m7RngNextFn : Fn :=
  ⟨"full_rng_next", [i64], [i64], full_rng_next_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_scale_delta"` (`[i64, i64] -> [i64]`). -/
def m7ScaleDeltaFn : Fn :=
  ⟨"full_scale_delta", [i64, i64], [i64], full_scale_delta_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_scale_delta_m6"` (`[i64, i64] -> [i64]`). -/
def m7ScaleDeltaM6Fn : Fn :=
  ⟨"full_scale_delta_m6", [i64, i64], [i64], full_scale_delta_m7_body⟩

/-- Drop-in `Fn` handle preserving `"full_bump_analyzed"` (`[i64] -> []`). -/
def m7BumpAnalyzedFn : Fn :=
  ⟨"full_bump_analyzed", [i64], [], full_bump_analyzed_m7_body⟩

/-- Standalone M7 bump/RNG/scaling module (`7` functions, `3` externs, `0` exits). -/
def m7BumpModule : LeanQbe.T.Module :=
  { fns := m7BumpFns, externs := m7BumpExterns, exits := [] }

theorem full_rng_next_m7_wf : Func.Wf full_rng_next_m7_body := by t_wf_reify
theorem full_log10_q16_m7_wf : Func.Wf full_log10_q16_m7_body := by t_wf_reify
theorem full_scale_delta_m7_wf : Func.Wf full_scale_delta_m7_body := by t_wf_reify
theorem full_bump_sift_m7_wf : Func.Wf full_bump_sift_m7_body := by t_wf_reify
theorem full_bump_sort_stamps_m7_wf : Func.Wf full_bump_sort_stamps_m7_body := by t_wf_reify
theorem full_bump_reasons_m7_wf : Func.Wf full_bump_reasons_m7_body := by t_wf_reify
theorem full_bump_analyzed_m7_wf : Func.Wf full_bump_analyzed_m7_body := by t_wf_reify

theorem m7RngNextFn_wf : m7RngNextFn.Wf := full_rng_next_m7_wf
theorem m7ScaleDeltaFn_wf : m7ScaleDeltaFn.Wf := full_scale_delta_m7_wf
theorem m7ScaleDeltaM6Fn_wf : m7ScaleDeltaM6Fn.Wf := full_scale_delta_m7_wf
theorem m7BumpAnalyzedFn_wf : m7BumpAnalyzedFn.Wf := full_bump_analyzed_m7_wf

theorem m7BumpFns_wf : ∀ f ∈ m7BumpFns, f.Wf := by
  simp only [m7BumpFns, m7_bump_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_rng_next_m7_wf, full_log10_q16_m7_wf, full_scale_delta_m7_wf,
    full_bump_sift_m7_wf, full_bump_sort_stamps_m7_wf, full_bump_reasons_m7_wf,
    full_bump_analyzed_m7_wf⟩

theorem m7Bump_acyclic : m7BumpModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7Bump

end
