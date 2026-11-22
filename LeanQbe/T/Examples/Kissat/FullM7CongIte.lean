module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave 4 `PR-W4A`: `O(deg log deg)` Conditional-Equivalence ITE Extraction (`FullM7CongIte`)

Purely additive C0 extension module on top of frozen `FullHdr` (`144` `u64` words = `1152` bytes;
zero edits to `Full1..5*`, `FullM5Cong*`, or `FullM6*`), implementing upstream Kissat 4.0.4's
`MERGE_CONDITIONAL_EQUIVALENCES` (`congruence.c:3373-3705`) as `full_cong_extract_ite_all_m7`:

1. `full_cong_u64_sift_m7` / `full_cong_u64_sort_m7`: in-place `O(n log n)` heapsort on packed
   `u64` `(a << 32) | b` literal pairs.
2. `full_cong_bsearch_u64_m7`: binary search over a sorted `u64` slice `[lo..hi)`.
3. `full_cong_copy_condbin_m7`: scans non-garbage irredundant unassigned ternary watches of
   `lit`, packs `(min(a,b) << 32) | max(a,b)` into `dst[0..cap)`, sorts, and deduplicates.
4. `full_cong_extract_condeq_m7`: extracts opposite-polarity conditional-equivalence pairs
   `((u, v))` and symmetric inverse `((v_pos, u_flipped))` via binary-search merge across
   adjacent `(2*k, 2*k+1)` variable runs, sorts, and deduplicates.
5. `full_cong_merge_condeq_m7`: two-pointer merge over sorted `work_stk1` (`cond ^ 1`) and
   `work_stk2` (`cond`) conditional equivalences, normalizing `(t & 1) != 0` and emitting
   `5`-word `(y, (2u << 28u) | 3u, c, t, e)` gate records into `scratch_buf[g_len..g_cap)`.
6. `full_cong_extract_ite_all_m7(h, g_len, g_cap, tick_lim)`: bounded sweep over active
   unassigned variables `v < cv`, reusing idle `wsort`, `work_stk1`, and `work_stk2`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongIte

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7CongIte "
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
#define FL_ACTIVE   1u

void full_cong_u64_sift_m7(u64 *a, u64 start, u64 n) {
  u64 root = start;
  while (root < n) {
    u64 child = root * 2ULL + 1ULL;
    if (child >= n) {
      break;
    }
    u64 swp = root;
    if (a[swp] < a[child]) {
      swp = child;
    }
    if (child + 1ULL < n && a[swp] < a[child + 1ULL]) {
      swp = child + 1ULL;
    }
    if (swp == root) {
      break;
    }
    u64 tmp = a[root];
    a[root] = a[swp];
    a[swp] = tmp;
    root = swp;
  }
}

void full_cong_u64_sort_m7(u64 *a, u64 n) {
  if (n <= 1ULL) {
    return;
  }
  u64 start = n >> 1ULL;
  while (start > 0ULL) {
    start = start - 1ULL;
    full_cong_u64_sift_m7(a, start, n);
  }
  u64 end = n - 1ULL;
  while (end > 0ULL) {
    u64 tmp = a[end];
    a[end] = a[0];
    a[0] = tmp;
    full_cong_u64_sift_m7(a, 0ULL, end);
    end = end - 1ULL;
  }
}

bool full_cong_bsearch_u64_m7(u64 *a, u64 lo, u64 hi, u64 key) {
  u64 l = lo;
  u64 r = hi;
  while (l < r) {
    u64 mid = l + ((r - l) >> 1ULL);
    u64 v = a[mid];
    if (v == key) {
      return true;
    }
    if (v < key) {
      l = mid + 1ULL;
    } else {
      r = mid;
    }
  }
  return false;
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
  u64 p = off;
  u64 end = off + wsz;
  u64 cnt = 0ULL;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      p = p + 1ULL;
    } else {
      if (p + 1ULL >= end) {
        break;
      }
      u32 cr = wstk[p + 1ULL];
      p = p + 2ULL;
      if ((u64)cr + 5ULL < alen) {
        u32 hdr = arena[cr];
        u32 sz = arena[(u64)cr + 2ULL];
        if ((hdr & (PH_GARB | PH_RED)) == 0u && sz == 3u) {
          u32 l0 = arena[(u64)cr + 3ULL];
          u32 l1 = arena[(u64)cr + 4ULL];
          u32 l2 = arena[(u64)cr + 5ULL];
          if (vals[l0] == (i8)0 && vals[l1] == (i8)0 && vals[l2] == (i8)0) {
            u32 a = 0u;
            u32 b = 0u;
            bool ok = false;
            if (l0 == lit) {
              a = l1;
              b = l2;
              ok = true;
            } else if (l1 == lit) {
              a = l0;
              b = l2;
              ok = true;
            } else if (l2 == lit) {
              a = l0;
              b = l1;
              ok = true;
            }
            if (ok && (a >> 1) != (b >> 1) &&
                (a >> 1) != (lit >> 1) && (b >> 1) != (lit >> 1)) {
              if (cnt >= cap) {
                return 0ULL;
              }
              u32 mn = a;
              u32 mx = b;
              if (b < a) {
                mn = b;
                mx = a;
              }
              dst[cnt] = ((u64)mn << 32ULL) | (u64)mx;
              cnt = cnt + 1ULL;
            }
          }
        }
      }
    }
  }
  if (cnt <= 1ULL) {
    return cnt;
  }
  full_cong_u64_sort_m7(dst, cnt);
  u64 u = 1ULL;
  u64 i = 1ULL;
  while (i < cnt) {
    if (dst[i] != dst[u - 1ULL]) {
      dst[u] = dst[i];
      u = u + 1ULL;
    }
    i = i + 1ULL;
  }
  return u;
}

u64 full_cong_extract_condeq_m7(u64 *cb, u64 m, u64 *ceq, u64 cap) {
  u64 d = 0ULL;
  u64 i = 0ULL;
  while (i < m) {
    u32 a = (u32)(cb[i] >> 32ULL);
    if ((a & 1u) != 0u) {
      u64 j = i + 1ULL;
      while (j < m && (u32)(cb[j] >> 32ULL) == a) {
        j = j + 1ULL;
      }
      i = j;
    } else {
      u64 pos_start = i;
      u64 pos_end = i + 1ULL;
      while (pos_end < m && (u32)(cb[pos_end] >> 32ULL) == a) {
        pos_end = pos_end + 1ULL;
      }
      u32 opp_a = a | 1u;
      u64 neg_start = pos_end;
      u64 neg_end = pos_end;
      while (neg_end < m && (u32)(cb[neg_end] >> 32ULL) == opp_a) {
        neg_end = neg_end + 1ULL;
      }
      u64 npos = pos_end - pos_start;
      u64 nneg = neg_end - neg_start;
      if (nneg > 0ULL) {
        if (npos <= nneg) {
          u64 k = pos_start;
          while (k < pos_end) {
            u32 b = (u32)cb[k];
            u32 not_b = b ^ 1u;
            u64 key = ((u64)opp_a << 32ULL) | (u64)not_b;
            if (full_cong_bsearch_u64_m7(cb, neg_start, neg_end, key)) {
              if (d + 2ULL <= cap) {
                u32 inv_l = ((not_b & 1u) != 0u) ? b : not_b;
                u32 inv_r = ((not_b & 1u) != 0u) ? opp_a : a;
                ceq[d] = ((u64)a << 32ULL) | (u64)not_b;
                ceq[d + 1ULL] = ((u64)inv_l << 32ULL) | (u64)inv_r;
                d = d + 2ULL;
              }
            }
            k = k + 1ULL;
          }
        } else {
          u64 k = neg_start;
          while (k < neg_end) {
            u32 b = (u32)cb[k];
            u32 not_b = b ^ 1u;
            u64 key = ((u64)a << 32ULL) | (u64)not_b;
            if (full_cong_bsearch_u64_m7(cb, pos_start, pos_end, key)) {
              if (d + 2ULL <= cap) {
                u32 inv_l = ((b & 1u) != 0u) ? not_b : b;
                u32 inv_r = ((b & 1u) != 0u) ? opp_a : a;
                ceq[d] = ((u64)a << 32ULL) | (u64)b;
                ceq[d + 1ULL] = ((u64)inv_l << 32ULL) | (u64)inv_r;
                d = d + 2ULL;
              }
            }
            k = k + 1ULL;
          }
        }
      }
      i = neg_end;
    }
  }
  if (d <= 1ULL) {
    return d;
  }
  full_cong_u64_sort_m7(ceq, d);
  u64 u = 1ULL;
  u64 idx = 1ULL;
  while (idx < d) {
    if (ceq[idx] != ceq[u - 1ULL]) {
      ceq[u] = ceq[idx];
      u = u + 1ULL;
    }
    idx = idx + 1ULL;
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
  u32 gl = g_len;
  u64 p = 0ULL;
  u64 q = 0ULL;
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
        if ((u32)(nv >> 32ULL) != lhs_p) {
          break;
        }
        u32 y = lhs_p;
        u32 t = (u32)pv;
        u32 e = (u32)nv;
        if (e != t && e != (t ^ 1u)) {
          u32 yy = y;
          u32 tt = t;
          u32 ee = e;
          if ((t & 1u) != 0u) {
            yy = y ^ 1u;
            tt = t ^ 1u;
            ee = e ^ 1u;
          }
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

u32 full_cong_extract_ite_all_m7(FullHdr *h, u32 g_len, u32 g_cap,
                                 u64 tick_lim) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if (g_len > g_cap || (u64)g_cap > h->scratch_cap ||
      cv < 3ULL || cv > mv || tick_lim == 0ULL) {
    return g_len;
  }
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 *wsort = (u64 *)h->wsort;
  u64 *wk1 = (u64 *)h->work_stk1;
  u64 *wk2 = (u64 *)h->work_stk2;
  u64 v = 0ULL;
  u64 ticks = 0ULL;
  u32 gl = g_len;
  while (v < cv && ticks < tick_lim && (u64)gl + 5ULL <= (u64)g_cap) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1ULL] == (i8)0) {
      u32 lit0 = (u32)(v << 1ULL);
      u32 lit1 = lit0 | 1u;
      u32 sz0 = wvec[((u64)lit0 << 1ULL) + 1ULL];
      u32 sz1 = wvec[((u64)lit1 << 1ULL) + 1ULL];
      if (sz0 <= 1u || sz1 <= 1u) {
        ticks = ticks + 1ULL;
      } else {
        ticks = ticks + 1ULL + (u64)sz0 + (u64)sz1;
        u32 small_lit = lit0;
        u32 large_lit = lit1;
        u64 *dst0 = wk2;
        u64 *dst1 = wk1;
        bool flipped = false;
        if (sz1 < sz0) {
          small_lit = lit1;
          large_lit = lit0;
          dst0 = wk1;
          dst1 = wk2;
          flipped = true;
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
"

/-- Closed function list for Wave-4 `PR-W4A` (`7` functions). -/
def m7CongIteFns : List Fn := m7CongIte_fns

/-- Closed standalone module (`7` functions, `0` externs, `0` exits). -/
def m7CongIteModule : LeanQbe.T.Module :=
  { fns := m7CongIteFns, externs := [], exits := [] }

end LeanQbe.T.Examples.Kissat.FullM7CongIte

end

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongIte

open LeanQbe.T

theorem full_cong_u64_sift_m7_wf : Func.Wf full_cong_u64_sift_m7_body := by
  t_wf_reify

theorem full_cong_u64_sort_m7_wf : Func.Wf full_cong_u64_sort_m7_body := by
  t_wf_reify

theorem full_cong_bsearch_u64_m7_wf : Func.Wf full_cong_bsearch_u64_m7_body := by
  t_wf_reify

theorem full_cong_copy_condbin_m7_wf : Func.Wf full_cong_copy_condbin_m7_body := by
  t_wf_reify

theorem full_cong_extract_condeq_m7_wf : Func.Wf full_cong_extract_condeq_m7_body := by
  t_wf_reify

theorem full_cong_merge_condeq_m7_wf : Func.Wf full_cong_merge_condeq_m7_body := by
  t_wf_reify

theorem full_cong_extract_ite_all_m7_wf : Func.Wf full_cong_extract_ite_all_m7_body := by
  t_wf_reify

theorem m7CongIteFns_wf : ∀ f ∈ m7CongIteFns, f.Wf := by
  simp only [m7CongIteFns, m7CongIte_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_cong_u64_sift_m7_wf, full_cong_u64_sort_m7_wf,
    full_cong_bsearch_u64_m7_wf, full_cong_copy_condbin_m7_wf,
    full_cong_extract_condeq_m7_wf, full_cong_merge_condeq_m7_wf,
    full_cong_extract_ite_all_m7_wf⟩

theorem m7CongIte_acyclic : m7CongIteModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7CongIte

end
