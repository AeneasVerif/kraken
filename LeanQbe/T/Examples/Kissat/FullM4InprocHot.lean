module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M4 Track A6: Same-Spec Inprocessing Hot-Spot Optimizations (`FullM4InprocHot`)

Standalone same-spec optimizations of three inprocessing hot spots (`0` edits to landed
`Full*`/`FullFast*`/`FullM3*` files, `0` `FullHdr` layout changes, trajectory-identical):
1. `full_has_ternary_m4` (replaces `full_has_ternary`): scans the **smallest** occurrence list
   among `{a, b, c}` (with bounds + unassigned guards) instead of always `a`.
2. `full_kitten_init_m4` (replaces `full_kitten_init`): `u64`-widened pointer-stepped
   initialization of `KH_*` header and `nv`/`2*nv` variable/literal tables.
3. `full_wstack_defrag_m4` (replaces `full_wstack_defrag`): `u64` paired `wvec` collection with
   already-sorted fast skip, inlined hole-sifting `O(n log n)` heap sort (zero `full_wsort_sift`
   calls, loop-invariant key caching), and compacted watch copy.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4InprocHot

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m4InprocHot "
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
#define PW_BIN_FLAG 0x80000000u

#define K_BASE 256u
#define K_MAX_V 128u
#define KH_NV 0u
#define KH_UNASS 6u
#define KH_INCONS 7u
#define KH_FAILING 8u
#define KH_ANTE 9u
#define KH_QFIRST 10u
#define KH_QLAST 11u
#define KH_QSEARCH 12u
#define KH_QSTAMP 13u
#define KH_TICK_LIM 15u
#define KH_ACAP 17u
#define KO_LVL 32u
#define KO_RSN 160u
#define KO_QPREV 288u
#define KO_QNEXT 416u
#define KO_QSTAMP 544u
#define KO_FLAGS 800u
#define KO_VALS 928u
#define KO_WHEAD 2080u
#define KO_ARENA 8608u

bool full_has_ternary_m4(FullHdr *h, u32 a, u32 b, u32 c) {
  i8 *vals = (i8 *)h->values;
  if (vals[a] != (i8)0) { return false; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 scan = a;
  u32 min_sz = wvec[((u64)a << 1) + 1ULL];
  if ((u64)b < nlits) {
    if (vals[b] != (i8)0) { return false; }
    u32 b_sz = wvec[((u64)b << 1) + 1ULL];
    if (b_sz < min_sz) { scan = b; min_sz = b_sz; }
  }
  if ((u64)c < nlits) {
    if (vals[c] != (i8)0) { return false; }
    u32 c_sz = wvec[((u64)c << 1) + 1ULL];
    if (c_sz < min_sz) { scan = c; min_sz = c_sz; }
  }
  if (min_sz == 0u) { return false; }
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 off = (u64)wvec[(u64)scan << 1];
  u64 end = off + (u64)min_sz;
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) { continue; }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    u32 hdr = ar[cr]; u32 sz = ar[(u64)cr + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) != 0u || sz < 3u) { continue; }
    u32 nf = 0u; bool ha = false; bool hb = false; bool hc = false; bool sat = false; u32 i = 0u;
    while (i < sz) {
      u32 l = ar[(u64)cr + 3ULL + (u64)i];
      if (vals[l] > (i8)0) { sat = true; break; }
      if (vals[l] == (i8)0) {
        nf = nf + 1u;
        if (l == a) { ha = true; } if (l == b) { hb = true; } if (l == c) { hc = true; }
      }
      i = i + 1u;
    }
    if (!sat && nf == 3u && ha && hb && hc) { return true; }
  }
  return false;
}

void full_kitten_init_m4(FullHdr *h, u32 nv, u32 track_ante) {
  if (h->scratch_cap < 10240ULL || nv > K_MAX_V) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  u64 *k64 = (u64 *)k;
  u64 ih = 0ULL;
  while (ih < 16ULL) { k64[ih] = 0ULL; ih = ih + 1ULL; }
  k[KH_NV] = nv; k[KH_UNASS] = nv; k[KH_ANTE] = track_ante;
  k[KH_INCONS] = 0xFFFFFFFFu; k[KH_FAILING] = 0xFFFFFFFFu;
  k[KH_TICK_LIM] = 8192u;
  k[KH_ACAP] = (u32)(h->scratch_cap - (u64)K_BASE - (u64)KO_ARENA);
  if (nv == 0u) {
    k[KH_QFIRST] = 0xFFFFFFFFu; k[KH_QLAST] = 0xFFFFFFFFu; k[KH_QSEARCH] = 0xFFFFFFFFu;
    return;
  }
  k[KH_QFIRST] = 0u; k[KH_QLAST] = nv - 1u; k[KH_QSEARCH] = nv - 1u; k[KH_QSTAMP] = nv;
  u64 ones = 0xFFFFFFFFFFFFFFFFULL;
  u64 qnext_w = 0x0000000200000001ULL;
  u64 step2 = 0x0000000200000002ULL;
  u64 *p = k64 + 16ULL;
  u64 *pv = k64 + 464ULL;
  u64 *pw = k64 + 1040ULL;
  u32 i = 0u;
  while (i + 1u < nv) {
    p[0] = 0ULL;
    p[64] = ones;
    p[128] = qnext_w - step2;
    p[192] = qnext_w;
    p[256] = qnext_w;
    p[384] = 0ULL;
    pv[0] = 0ULL; pv[1] = 0ULL;
    pw[0] = ones; pw[1] = ones;
    p = p + 1ULL;
    pv = pv + 2ULL;
    pw = pw + 2ULL;
    qnext_w = qnext_w + step2;
    i = i + 2u;
  }
  if (i < nv) {
    k[KO_LVL + i] = 0u; k[KO_RSN + i] = 0xFFFFFFFFu; k[KO_FLAGS + i] = 0u;
    k[KO_QSTAMP + i] = i + 1u;
    k[KO_QPREV + i] = i - 1u;
    k[KO_QNEXT + i] = 0xFFFFFFFFu;
    u32 l0 = i << 1;
    k[KO_VALS + l0] = 0u; k[KO_VALS + l0 + 1u] = 0u;
    k[KO_WHEAD + l0] = 0xFFFFFFFFu; k[KO_WHEAD + l0 + 1u] = 0xFFFFFFFFu;
  }
  k[KO_QPREV] = 0xFFFFFFFFu;
  if (nv >= 2u) { k[KO_QPREV + 1u] = 0u; }
  k[KO_QNEXT + nv - 1u] = 0xFFFFFFFFu;
}

void full_wstack_defrag_m4(FullHdr *h) {
  if (h->wlen <= 1ULL) { h->wusable = 0ULL; return; }
  u64 nlits = h->cur_vars << 1;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 *wvec64 = (u64 *)wvec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ws = (u32 *)h->wsort;
  u64 n = 0ULL;
  u64 l = 0ULL;
  u32 prev_off = 0u;
  bool sorted = true;
  while (l < nlits) {
    u64 pair = wvec64[l];
    u32 sz = (u32)(pair >> 32);
    if (sz == 0u) {
      if ((u32)pair != 0u) { wvec64[l] = 0ULL; }
    } else {
      u32 off = (u32)pair;
      ws[n] = (u32)l; n = n + 1ULL;
      if (off < prev_off) { sorted = false; }
      prev_off = off;
    }
    l = l + 1ULL;
  }
  if (n == 0ULL) { wstk[0] = 0u; h->wlen = 1ULL; h->wusable = 0ULL; return; }
  if (!sorted && n > 1ULL) {
    if (n <= nlits - n) {
      u64 blk = 0ULL;
      while (blk < n) {
        u64 hi = blk + 16ULL;
        if (hi > n) { hi = n; }
        u64 ii = blk + 1ULL;
        while (ii < hi) {
          u32 xl = ws[ii];
          u32 xo = wvec[(u64)xl << 1];
          u64 jj = ii;
          while (jj > blk) {
            u32 pl = ws[jj - 1ULL];
            if (wvec[(u64)pl << 1] <= xo) { break; }
            ws[jj] = pl;
            jj = jj - 1ULL;
          }
          ws[jj] = xl;
          ii = ii + 1ULL;
        }
        blk = blk + 16ULL;
      }
      u64 src_off = 0ULL;
      u64 dst_off = n;
      u64 width = 16ULL;
      while (width < n) {
        u64 lo = 0ULL;
        while (lo < n) {
          u64 mid = lo + width;
          if (mid > n) { mid = n; }
          u64 hi = mid + width;
          if (hi > n) { hi = n; }
          u64 li = lo;
          u64 ri = mid;
          u64 ki = lo;
          while (li < mid && ri < hi) {
            u32 ll = ws[src_off + li];
            u32 rl = ws[src_off + ri];
            if (wvec[(u64)ll << 1] <= wvec[(u64)rl << 1]) {
              ws[dst_off + ki] = ll; li = li + 1ULL;
            } else {
              ws[dst_off + ki] = rl; ri = ri + 1ULL;
            }
            ki = ki + 1ULL;
          }
          while (li < mid) {
            ws[dst_off + ki] = ws[src_off + li]; li = li + 1ULL; ki = ki + 1ULL;
          }
          while (ri < hi) {
            ws[dst_off + ki] = ws[src_off + ri]; ri = ri + 1ULL; ki = ki + 1ULL;
          }
          lo = lo + (width << 1);
        }
        u64 tmp_off = src_off; src_off = dst_off; dst_off = tmp_off;
        width = width << 1;
      }
      if (src_off != 0ULL) {
        u64 ci = 0ULL;
        while (ci < n) { ws[ci] = ws[src_off + ci]; ci = ci + 1ULL; }
      }
    } else {
      u64 start = n >> 1;
      while (start > 0ULL) {
        start = start - 1ULL;
        u64 root = start;
        u32 rl = ws[root];
        u32 ro = wvec[(u64)rl << 1];
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= n) { break; }
          u32 cl = ws[ch];
          u32 co = wvec[(u64)cl << 1];
          if (ch + 1ULL < n) {
            u32 sl = ws[ch + 1ULL];
            u32 so = wvec[(u64)sl << 1];
            if (so > co) { ch = ch + 1ULL; cl = sl; co = so; }
          }
          if (ro >= co) { break; }
          ws[root] = cl;
          root = ch;
        }
        ws[root] = rl;
      }
      u64 end = n - 1ULL;
      while (end > 0ULL) {
        u32 rl = ws[end];
        ws[end] = ws[0];
        u32 ro = wvec[(u64)rl << 1];
        u64 root = 0ULL;
        while (true) {
          u64 ch = (root << 1) + 1ULL;
          if (ch >= end) { break; }
          u32 cl = ws[ch];
          u32 co = wvec[(u64)cl << 1];
          if (ch + 1ULL < end) {
            u32 sl = ws[ch + 1ULL];
            u32 so = wvec[(u64)sl << 1];
            if (so > co) { ch = ch + 1ULL; cl = sl; co = so; }
          }
          if (ro >= co) { break; }
          ws[root] = cl;
          root = ch;
        }
        ws[root] = rl;
        end = end - 1ULL;
      }
    }
  }
  u64 p = 1ULL;
  u64 i = 0ULL;
  while (i < n) {
    u32 lit = ws[i];
    u64 off = (u64)wvec[(u64)lit << 1];
    u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
    if (off != p) {
      u64 k = 0ULL;
      while (k < sz) { wstk[p + k] = wstk[off + k]; k = k + 1ULL; }
      wvec[(u64)lit << 1] = (u32)p;
    }
    p = p + sz;
    i = i + 1ULL;
  }
  h->wlen = p;
  h->wusable = 0ULL;
}
"

def m4InprocHotModule : LeanQbe.T.Module :=
  { fns := m4InprocHot_fns, externs := [], exits := [] }

theorem full_has_ternary_m4_wf : Func.Wf full_has_ternary_m4_body := by t_wf_reify
theorem full_kitten_init_m4_wf : Func.Wf full_kitten_init_m4_body := by t_wf_reify
theorem full_wstack_defrag_m4_wf : Func.Wf full_wstack_defrag_m4_body := by t_wf_reify

theorem m4InprocHot_fns_wf : ∀ f ∈ m4InprocHot_fns, f.Wf := by
  simp only [m4InprocHot_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_has_ternary_m4_wf, full_kitten_init_m4_wf, full_wstack_defrag_m4_wf⟩

theorem m4InprocHot_acyclic : m4InprocHotModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Spliced `Fn` entries for `FullM4` / `FullM3` unification (canonical names). -/
def m4HasTernaryFn : Fn :=
  ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], full_has_ternary_m4_body⟩

def m4KittenInitFn : Fn :=
  ⟨"full_kitten_init", [i64, i32, i32], [], full_kitten_init_m4_body⟩

def m4WstackDefragFn : Fn :=
  ⟨"full_wstack_defrag", [i64], [], full_wstack_defrag_m4_body⟩

end LeanQbe.T.Examples.Kissat.FullM4InprocHot
