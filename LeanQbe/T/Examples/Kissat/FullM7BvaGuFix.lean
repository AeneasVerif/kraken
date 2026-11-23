module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M7 Purely Additive Bug Fixes (`FullM7BvaGuFix`)

Purely additive drop-in C0 replacements over unchanged `FullHdr` fixing two confirmed `P0`
bugs for `FullM7`:

1. `full_bva_commit_m7` (`P0-3`): identical to `FullM5DenseSafe.full_bva_commit_m5` except
   `FL_FACT_P = 32u` and `FL_FACT_N = 64u` (instead of `256u`/`512u`, which collided with
   `FL_BONE1`/`FL_TRANS` in `FullM7BvaFactor`).
2. `full_analyze_rsn_m7` (`P0-4`): identical to `FullM5HeurCore.full_analyze_rsn_m5` except
   guarding `glue_used` updates with `if (glue < 36ULL)` so `h->glue_used[36..63]`
   (persistent `FullM7Search` state under `M7_GU_MAGIC = 36ULL`) is never overwritten.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7BvaGuFix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7BvaGuFix "
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
#define PH_RED  0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_FACT_P 32u
#define FL_FACT_N 64u

extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern void full_init_fresh_var(FullHdr *h, u32 fv);
extern bool full_analyze_lit(FullHdr *h, u32 lit, u32 skip_var);

bool full_bva_commit_m7(FullHdr *h, u32 best_k) {
  if (h->oom != 0ULL) { return false; }
  u32 *ar = (u32 *)h->arena; u32 *scr = (u32 *)h->scratch_buf;
  u32 *cnt = (u32 *)h->wsort; u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 dm = best_k + 1u; u32 mn = scr[32u + best_k];
  u64 need_ar = 16ULL;
  u64 need_w = (((u64)dm + (u64)mn + 8ULL) << 3);
  u32 si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 fsz = (u64)wvec[((u64)fs << 1) + 1ULL];
    need_w = need_w + (fsz << 1) + 2ULL;
    si = si + 1u;
  }
  u32 m = 0u;
  while (m < mn) {
    u32 c_top = scr[64u + best_k * 256u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u32 q = c_top & PW_LIT_MASK;
      u64 qsz = (u64)wvec[((u64)q << 1) + 1ULL];
      need_w = need_w + (qsz << 1) + 2ULL;
    } else {
      u32 csz = ar[(u64)c_top + 2ULL];
      need_ar = need_ar + 3ULL + (u64)csz;
      u32 flit = scr[best_k]; u32 j = 0u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) {
          u64 lsz = (u64)wvec[((u64)l << 1) + 1ULL];
          need_w = need_w + (lsz << 1) + 2ULL;
        }
        j = j + 1u;
      }
    }
    m = m + 1u;
  }
  if (h->cur_vars >= h->max_vars || h->arena_cap < h->arena_len ||
      h->arena_cap - h->arena_len < need_ar) { return false; }
  if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->wcap < h->wlen || h->wcap - h->wlen < need_w) {
      u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
      while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
      return false;
    }
  }
  u32 fv = (u32)h->cur_vars; h->cur_vars = h->cur_vars + 1ULL;
  full_init_fresh_var(h, fv);
  u64 *s1 = (u64 *)h->repr; u64 *s2 = (u64 *)h->sim_sig; s1[fv] = 0ULL; s2[fv] = 0ULL;
  cnt[fv << 1] = 0u; cnt[(fv << 1) | 1u] = 0u;
  u32 fresh = fv << 1; u32 *tmp = (u32 *)h->tmp_lits;
  bool ok = true;
  si = 0u;
  while (si < dm) {
    u32 fs = scr[si];
    u64 br = full_add_bin(h, fresh, fs);
    if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    fl[fs >> 1] = fl[fs >> 1] | FL_FACT_P | FL_FACT_N;
    si = si + 1u;
  }
  m = 0u;
  while (m < mn && ok) {
    u32 c_top = scr[64u + best_k * 256u + m];
    if ((c_top & PW_BIN_FLAG) != 0u) {
      u64 br = full_add_bin(h, fresh ^ 1u, c_top & PW_LIT_MASK);
      if (br == 2ULL || br == 20ULL || h->oom != 0ULL) { ok = false; break; }
    } else {
      u32 csz = ar[(u64)c_top + 2ULL]; u32 flit = scr[best_k]; u32 tk = 1u; u32 j = 0u;
      tmp[0] = fresh ^ 1u;
      while (j < csz) {
        u32 l = ar[(u64)c_top + 3ULL + (u64)j];
        if (l != flit) { tmp[tk] = l; tk = tk + 1u; }
        j = j + 1u;
      }
      u64 ncr = full_alloc_cl(h, tk, 0u, false);
      if (ncr == 0xFFFFFFFFULL) { ok = false; break; }
      j = 0u; while (j < tk) { ar[ncr + 3ULL + (u64)j] = tmp[j]; j = j + 1u; }
      j = 0u;
      while (j < tk) {
        if (!full_watch_push(h, tmp[j], tk & PW_LIT_MASK, (u32)ncr, 2u)) {
          u32 uk = 0u;
          while (uk < j) { full_unwatch_large(h, tmp[uk], (u32)ncr); uk = uk + 1u; }
          ar[ncr] = ar[ncr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)tk;
          ok = false; break;
        }
        u32 tv = tmp[j] >> 1;
        fl[tv] = fl[tv] | (((tmp[j] & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        j = j + 1u;
      }
      if (ok) { h->num_irred = h->num_irred + 1ULL; }
    }
    m = m + 1u;
  }
  if (!ok) {
    u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
    while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
    return false;
  }
  m = 0u;
  while (m < mn) {
    u32 idx = m;
    u32 s = best_k;
    while (true) {
      u32 cs = scr[64u + s * 256u + idx]; u32 fs = scr[s];
      if ((cs & PW_BIN_FLAG) != 0u) {
        u32 q = cs & PW_LIT_MASK;
        full_delete_binary(h, fs, q);
        fl[q >> 1] = fl[q >> 1] | (((q & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      } else {
        u32 csz = ar[(u64)cs + 2ULL]; u32 k = 0u;
        while (k < csz) {
          u32 dl = ar[(u64)cs + 3ULL + (u64)k];
          full_unwatch_large(h, dl, cs);
          fl[dl >> 1] = fl[dl >> 1] | (((dl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
          k = k + 1u;
        }
        ar[cs] = ar[cs] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
      }
      if (s == 0u) { break; }
      idx = scr[8256u + s * 256u + idx]; s = s - 1u;
    }
    m = m + 1u;
  }
  u64 zi = 0ULL; u64 zl = h->cur_vars << 1;
  while (zi < zl) { cnt[zi] = 0u; zi = zi + 1ULL; }
  h->bva_cnt = h->bva_cnt + 1ULL;
  return true;
}

bool full_analyze_rsn_m7(FullHdr *h, u32 rsn, u32 skip_var) {
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
    if (glue > 1ULL) {
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
    if (glue < 36ULL) {
      if (gu[glue] < 0xFFFFFFFFu) { gu[glue] = gu[glue] + 1u; }
    }
    u32 old_u = (hdr >> 27) & 31u;
    if (31u > old_u) { ar[rsn] = (hdr & 0x07FFFFFFu) | (31u << 27); }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)rsn + 3ULL + (u64)i];
    if (!full_analyze_lit(h, l, skip_var)) { return false; }
    i = i + 1u;
  }
  return true;
}
"

/-- External callee signatures referenced by `m7BvaGuFix_fns`. -/
def m7BvaGuFixExterns : List Extern :=
  [ ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_delete_binary", [i64, i32, i32], []⟩
  , ⟨"full_init_fresh_var", [i64, i32], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩ ]

/-- Standalone M7 BVA/glue-used fix module (`2` functions + `8` externs, `0` exits). -/
def m7BvaGuFixModule : LeanQbe.T.Module :=
  { fns := m7BvaGuFix_fns, externs := m7BvaGuFixExterns, exits := [] }

/-- Drop-in renamed `Fn` handles matching canonical `FullM5` / `FullM7` splice slots. -/
def m7BvaCommitFn : Fn := ⟨"full_bva_commit", [i64, i32], [.bool], full_bva_commit_m7_body⟩
def m7AnalyzeRsnFn : Fn :=
  ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], full_analyze_rsn_m7_body⟩

theorem full_bva_commit_m7_wf : Func.Wf full_bva_commit_m7_body := by t_wf_reify
theorem full_analyze_rsn_m7_wf : Func.Wf full_analyze_rsn_m7_body := by t_wf_reify

theorem m7BvaGuFix_fns_wf : ∀ f ∈ m7BvaGuFix_fns, f.Wf := by
  simp only [m7BvaGuFix_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_bva_commit_m7_wf, full_analyze_rsn_m7_wf⟩

theorem m7BvaGuFix_acyclic : m7BvaGuFixModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
