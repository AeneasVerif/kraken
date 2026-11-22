module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave 4 `PR-W4B`: Weighted Literal Occurrence VMTF Reorder (`FullM7Reorder`)

Purely additive `T1` direct replacement for `FullM4Ternary.full_reorder_queue` matching upstream
Kissat 4.0.4 `src/reorder.c:24-217` (`compute_weights`, `less_focused_order`, `reorder_focused`):
- `full_reorder_weight_m7(sz)`: quantized `2^-(sz - 2)` weight `(1ULL << 40) >> (sz - 2)` for
  `2 <= sz <= 42` (`0` otherwise, avoiding `u64` overflow up to `16M` clauses per literal).
- `full_reorder_sift_m7(h, start, n)`: max-heap sift-down on `wsort[0..n)` ordering variables
  ascending by `(wl[v], q_stamp[v])` (`less_focused_order` so highest weight lands at `q_last`).
- `full_reorder_queue_m7(h)`:
  1. Zeros `u64 *wl = (u64 *)h->tarjan_mark` and `u64 *wr = (u64 *)h->tarjan_reach`
     on `0..cur_vars`.
  2. Scans irredundant, non-garbage, non-satisfied arena clauses via `full_arena_next` and
     accumulates quantized weights per unassigned literal (`wl[v]` even, `wr[v]` odd, saturating
     at `1ULL << 60`).
  3. Adds `w2 = 1ULL << 40` to both sides of each active unassigned binary watch `(lit < other)`.
  4. Folds `wl[v] = max(wl[v], wr[v]) + 2 * min(wl[v], wr[v])`.
  5. Collects active variables into `wsort`, heapsorts ascending by `(wl[v], q_stamp[v])`, clears
     and relinks `q_prev`/`q_next`/`q_stamp`/`q_first`/`q_last`/`q_search_idx`/`q_search_stamp`.
- Drop-in handle `m7ReorderQueueFn` preserves `"full_reorder_queue"` (`[i64] -> [i64]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Reorder

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7_reorder "
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
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE   1u

extern u32 full_arena_next(FullHdr *h, u32 cref);

u64 full_reorder_weight_m7(u64 sz) {
  if (sz < 2ULL || sz > 42ULL) { return 0ULL; }
  return (1ULL << 40) >> (sz - 2ULL);
}

void full_reorder_sift_m7(FullHdr *h, u64 start, u64 n) {
  if (n == 0ULL || start >= n || n > h->cur_vars) { return; }
  u32 *ws = (u32 *)h->wsort;
  u64 *wl = (u64 *)h->tarjan_mark;
  u32 *qs = (u32 *)h->q_stamp;
  u64 root = start;
  while (true) {
    u64 child = (root << 1) + 1ULL;
    if (child >= n) { break; }
    u64 best = root;
    u32 bv = ws[best];
    u64 bw = wl[bv];
    u32 bs = qs[bv];
    u32 cv = ws[child];
    u64 cw = wl[cv];
    u32 cs = qs[cv];
    if (cw > bw || (cw == bw && cs > bs)) {
      best = child; bv = cv; bw = cw; bs = cs;
    }
    u64 rch = child + 1ULL;
    if (rch < n) {
      u32 rv = ws[rch];
      u64 rw = wl[rv];
      u32 rs = qs[rv];
      if (rw > bw || (rw == bw && rs > bs)) {
        best = rch; bv = rv;
      }
    }
    if (best == root) { break; }
    u32 tmp = ws[root];
    ws[root] = bv;
    ws[best] = tmp;
    root = best;
  }
}

u64 full_reorder_queue_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  u64 alen = h->arena_len;
  u64 wlen = h->wlen;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *qs = (u32 *)h->q_stamp;
  u64 *wl = (u64 *)h->tarjan_mark;
  u64 *wr = (u64 *)h->tarjan_reach;
  u64 w2 = 1ULL << 40;
  u64 wcap = 1ULL << 60;
  u64 z = 0ULL;
  while (z < cv) {
    wl[z] = 0ULL;
    wr[z] = 0ULL;
    z = z + 1ULL;
  }
  u64 p = 0ULL;
  while (p < alen) {
    if (p + 3ULL > alen) { break; }
    u32 hdr = ar[p];
    u32 csz = ar[p + 2ULL];
    u64 clen = (u64)csz;
    if ((hdr & (PH_GARB | PH_RED)) == 0u && clen <= alen - (p + 3ULL)) {
      bool sat = false;
      u64 sz = 0ULL;
      u64 ci = 0ULL;
      while (ci < clen) {
        u32 lit = ar[p + 3ULL + ci];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) { sz = sz + 1ULL; }
        }
        ci = ci + 1ULL;
      }
      if (!sat && sz >= 2ULL && sz <= 100ULL) {
        u64 w = full_reorder_weight_m7(sz);
        if (w > 0ULL) {
          ci = 0ULL;
          while (ci < clen) {
            u32 lit = ar[p + 3ULL + ci];
            if ((u64)lit < nlits) {
              if (vals[lit] == (i8)0) {
                u32 av = lit >> 1;
                if ((lit & 1u) == 0u) {
                  u64 cur = wl[av];
                  wl[av] = (cur > wcap - w) ? wcap : (cur + w);
                } else {
                  u64 cur = wr[av];
                  wr[av] = (cur > wcap - w) ? wcap : (cur + w);
                }
              }
            }
            ci = ci + 1ULL;
          }
        }
      }
    }
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (np <= p) { break; }
    p = np;
  }
  u64 lit = 0ULL;
  while (lit < nlits) {
    u64 lvar = lit >> 1;
    if ((fl[lvar] & FL_ACTIVE) != 0u && vals[lit] == (i8)0) {
      u64 off = (u64)wvec[lit << 1];
      u64 wsz = (u64)wvec[(lit << 1) + 1ULL];
      if (wsz > 0ULL && off < wlen && wsz <= wlen - off) {
        u64 wp = off;
        u64 wend = off + wsz;
        while (wp < wend) {
          u32 w0 = wstk[wp];
          if ((w0 & PW_BIN_FLAG) == 0u) {
            if (wp + 1ULL < wend) { wp = wp + 2ULL; continue; }
            break;
          }
          u32 other = w0 & PW_LIT_MASK;
          if ((u64)other > lit && (u64)other < nlits) {
            u64 ov = (u64)(other >> 1);
            if ((fl[ov] & FL_ACTIVE) != 0u && vals[other] == (i8)0) {
              if ((lit & 1ULL) == 0ULL) {
                u64 c1 = wl[lvar];
                wl[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              } else {
                u64 c1 = wr[lvar];
                wr[lvar] = (c1 > wcap - w2) ? wcap : (c1 + w2);
              }
              if ((other & 1u) == 0u) {
                u64 c2 = wl[ov];
                wl[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              } else {
                u64 c2 = wr[ov];
                wr[ov] = (c2 > wcap - w2) ? wcap : (c2 + w2);
              }
            }
          }
          wp = wp + 1ULL;
        }
      }
    }
    lit = lit + 1ULL;
  }
  u64 fv = 0ULL;
  while (fv < cv) {
    u64 a = wl[fv];
    u64 b = wr[fv];
    wl[fv] = (a >= b) ? (a + (b << 1)) : (b + (a << 1));
    fv = fv + 1ULL;
  }
  u64 n = 0ULL;
  u64 av = 0ULL;
  while (av < cv) {
    if ((fl[av] & FL_ACTIVE) != 0u) { ws[n] = (u32)av; n = n + 1ULL; }
    av = av + 1ULL;
  }
  if (n > 1ULL) {
    u64 s = n >> 1;
    while (s > 0ULL) {
      s = s - 1ULL;
      full_reorder_sift_m7(h, s, n);
    }
    u64 e = n;
    while (e > 1ULL) {
      e = e - 1ULL;
      u32 tmp = ws[0];
      ws[0] = ws[e];
      ws[e] = tmp;
      full_reorder_sift_m7(h, 0ULL, e);
    }
  }
  u64 rv = 0ULL;
  while (rv < cv) {
    qp[rv] = 0xFFFFFFFFu;
    qn[rv] = 0xFFFFFFFFu;
    qs[rv] = 0u;
    rv = rv + 1ULL;
  }
  if (n == 0ULL) {
    h->q_first = 0xFFFFFFFFULL;
    h->q_last = 0xFFFFFFFFULL;
    h->q_search_idx = 0xFFFFFFFFULL;
    h->q_cur_stamp = 0ULL;
    h->q_search_stamp = 0ULL;
    return 0ULL;
  }
  u64 sidx = 0xFFFFFFFFULL;
  u64 sstamp = 0ULL;
  u64 qi = 0ULL;
  while (qi < n) {
    u32 cur = ws[qi];
    qp[cur] = (qi > 0ULL) ? ws[qi - 1ULL] : 0xFFFFFFFFu;
    qn[cur] = (qi + 1ULL < n) ? ws[qi + 1ULL] : 0xFFFFFFFFu;
    qs[cur] = (u32)(qi + 1ULL);
    if (vals[(u64)cur << 1] == (i8)0) { sidx = (u64)cur; sstamp = qi + 1ULL; }
    qi = qi + 1ULL;
  }
  h->q_first = (u64)ws[0];
  h->q_last = (u64)ws[n - 1ULL];
  h->q_cur_stamp = n;
  if (sidx >= cv) { sidx = (u64)ws[n - 1ULL]; sstamp = n; }
  h->q_search_idx = sidx;
  h->q_search_stamp = sstamp;
  return n;
}
"

/-- Canonical external callee list for `m7ReorderModule` (`full_arena_next`). -/
def m7ReorderExterns : List Extern :=
  [⟨"full_arena_next", [i64, i32], [i32]⟩]

/-- Standalone `m7Reorder` function list (`3` functions). -/
def m7ReorderFns : List Fn := m7_reorder_fns

/-- Drop-in Wave-3/4 `Fn` handle preserving canonical `"full_reorder_queue"` (`[i64] -> [i64]`). -/
def m7ReorderQueueFn : Fn :=
  ⟨"full_reorder_queue", [i64], [i64], full_reorder_queue_m7_body⟩

/-- Standalone Wave-4 `PR-W4B` module (`3` functions, `1` extern, `0` exits). -/
def m7ReorderModule : LeanQbe.T.Module :=
  { fns := m7ReorderFns, externs := m7ReorderExterns, exits := [] }

theorem full_reorder_weight_m7_wf : Func.Wf full_reorder_weight_m7_body := by t_wf_reify
theorem full_reorder_sift_m7_wf : Func.Wf full_reorder_sift_m7_body := by t_wf_reify
theorem full_reorder_queue_m7_wf : Func.Wf full_reorder_queue_m7_body := by t_wf_reify

theorem m7ReorderQueueFn_wf : m7ReorderQueueFn.Wf :=
  full_reorder_queue_m7_wf

theorem m7ReorderFns_wf : ∀ f ∈ m7ReorderFns, f.Wf := by
  simp only [m7ReorderFns, m7_reorder_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_reorder_weight_m7_wf, full_reorder_sift_m7_wf, full_reorder_queue_m7_wf⟩

theorem m7Reorder_acyclic : m7ReorderModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7Reorder

end
