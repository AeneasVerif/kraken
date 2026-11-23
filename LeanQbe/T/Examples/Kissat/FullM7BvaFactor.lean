module

public import LeanQbe.T.Examples.Kissat.Dimacs

/-!
# Kissat M7 Upstream `factor.c` BVA Parity (`FullM7BvaFactor`)

Additive `3`-function drop-in upgrade over `FullM4Bva` / `FullBvaHeap` / `FullM6VivBackbone`,
preserving exact `FullM6Hdr` / `FullHdr` layouts and `FullBvaHeapSpec` / `FullM6BvaNoHops`
contracts (`0` changes to `Full1..6*` or other `FullM7*` modules):

1. `full_init_fresh_var_m7` (`"full_init_fresh_var"`): initializes fresh BVA variables with full
   M6 flags (`2041u` = `FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP | FL_FACT_P | FL_FACT_N |
   FL_BONE0 | FL_BONE1 | FL_TRANS`) and enqueues at **`q_first`** (VMTF head, decided last, matching
   upstream `factor.c:fresh_variable`) instead of `q_last`.
2. `full_bva_try_lit_m7` (`"full_bva_try_lit"`): matches upstream `factor.c` clause length bound
   `factorsize = 5` (`3 <= csz <= 5`), checks `red > h->elim_bound` (`dm * mn - (dm + mn)`), uses
   the `256 x 32` `FullM4Bva` scratch matrix, and collects touched literals into `work_stk2`.
3. `full_factor_m7` (`"full_factor"`): skips unused `repr`/`sim_sig` zeroing, prechecks
   `wvec[2 * f0 + 1] > 1u` before decrementing `budget` and calling `full_bva_try_lit`, sifts/
   reschedules touched literals on the `fheap`, and renumbers VMTF `q_stamp` from `q_first`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7BvaFactor

open LeanQbe.T

kissat_c0! m7BvaFactor "
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

#define FL_ACTIVE   1u
#define FL_SUBSUME  8u
#define FL_ELIM_C   16u
#define FL_FACT_P   32u
#define FL_FACT_N   64u
#define FL_BONE0    128u
#define FL_BONE1    256u
#define FL_TRANS    512u
#define FL_SWEEP    1024u
#define PH_GARB     0x00080000u
#define PH_RED      0x00400000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define M7_ROW_MAX     256u
#define M7_STEPS_MAX   32u
#define M7_ROW_BASE    64u
#define M7_PAR_BASE    8256u
#define M7_SCR_MIN     16448ULL

extern u32 full_bva_scan_cands(FullHdr *h, u32 row_off, u32 cur_qn, u64 init_lits);
extern u32 full_bva_pick_cand(FullHdr *h, u32 ncntd, u32 f0);
extern u32 full_bva_filter_row(FullHdr *h, u32 row_off, u32 nrow_off, u32 par_off,
    u32 cur_qn, u32 best_lit);
extern bool full_bva_commit(FullHdr *h, u32 best_k);
extern void full_fheap_up(u32 *heap, u32 *fpos, u32 *wvec, u32 k);
extern void full_fheap_down(u32 *heap, u32 *fpos, u32 *wvec, u32 k, u32 hsz);
extern bool full_bva_try_lit(FullHdr *h, u32 f0, u64 init_cv);

void full_init_fresh_var_m7(FullHdr *h, u32 fv) {
  i8 *vals = (i8 *)h->values; u8 *mrk = (u8 *)h->mark; u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason; u32 *ps = (u32 *)h->pos;
  u32 *qp = (u32 *)h->q_prev; u32 *qn = (u32 *)h->q_next; u32 *qs = (u32 *)h->q_stamp;
  i8 *ph = (i8 *)h->phases; u32 *wvec = (u32 *)h->watch_vec; u64 *sc = (u64 *)h->score;
  wvec[(u64)fv << 2] = 0u; wvec[((u64)fv << 2) + 1ULL] = 0u;
  wvec[((u64)fv << 2) + 2ULL] = 0u; wvec[((u64)fv << 2) + 3ULL] = 0u;
  vals[(u64)fv << 1] = (i8)0; vals[((u64)fv << 1) | 1ULL] = (i8)0;
  mrk[fv] = (u8)0; ph[fv] = (i8)1;
  lvl[fv] = 0u; rsns[fv] = 0xFFFFFFFFu; ps[fv] = 0xFFFFFFFFu; sc[fv] = 0ULL;
  fl[fv] = FL_ACTIVE | FL_SUBSUME | FL_ELIM_C | FL_SWEEP |
           FL_FACT_P | FL_FACT_N | FL_BONE0 | FL_BONE1 | FL_TRANS;
  u32 old_first = (u32)h->q_first;
  qp[fv] = 0xFFFFFFFFu;
  if ((u64)old_first < h->cur_vars) { qn[fv] = old_first; qp[old_first] = fv; }
  else { qn[fv] = 0xFFFFFFFFu; h->q_last = (u64)fv; }
  h->q_first = (u64)fv; qs[fv] = 0u;
  h->unassigned = h->unassigned + 1ULL;
}

bool full_bva_try_lit_m7(FullHdr *h, u32 f0, u64 init_cv) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < M7_SCR_MIN) { return false; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *arena = (u32 *)h->arena;
  u8 *counted = (u8 *)h->lit_mark;
  u32 *scr = (u32 *)h->scratch_buf;
  if (vals[f0] != (i8)0) { return false; }
  u64 init_lits = (init_cv <= h->cur_vars) ? (init_cv << 1) : (h->cur_vars << 1);
  u64 off0 = (u64)wvec[(u64)f0 << 1];
  u64 sz0 = (u64)wvec[((u64)f0 << 1) + 1ULL];
  u64 wi = 0ULL;
  u32 r0n = 0u;
  while (wi < sz0 && r0n < M7_ROW_MAX) {
    u32 w0 = wstk[off0 + wi]; wi = wi + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 other = w0 & PW_LIT_MASK;
      if (vals[other] == (i8)0) {
        scr[M7_ROW_BASE + r0n] = w0;
        r0n = r0n + 1u;
      }
    } else if (wi < sz0) {
      u32 cr = wstk[off0 + wi]; wi = wi + 1ULL;
      u32 csz = arena[(u64)cr + 2ULL];
      u32 cfl = arena[(u64)cr];
      if ((cfl & (PH_GARB | PH_RED)) == 0u && csz >= 3u && csz <= 5u) {
        u32 j = 0u; bool has_f0 = false; bool sat = false;
        while (j < csz) {
          u32 l = arena[(u64)cr + 3ULL + (u64)j];
          if (vals[l] > (i8)0) { sat = true; break; }
          if (l == f0) { has_f0 = true; }
          j = j + 1u;
        }
        if (!sat && has_f0) {
          scr[M7_ROW_BASE + r0n] = cr;
          r0n = r0n + 1u;
        }
      }
    }
  }
  if (r0n < 2u) { return false; }
  u64 elim_bound = h->elim_bound;
  scr[0] = f0;
  scr[32] = r0n;
  counted[f0] = (u8)1;
  u32 step = 1u;
  u32 cur_qn = r0n;
  u32 best_k = 0u;
  u64 best_red = 0ULL;
  while (step < M7_STEPS_MAX && cur_qn >= 2u) {
    u32 row_off = M7_ROW_BASE + (step - 1u) * M7_ROW_MAX;
    u32 ncntd = full_bva_scan_cands(h, row_off, cur_qn, init_lits);
    u32 best_lit = full_bva_pick_cand(h, ncntd, f0);
    if (best_lit == 0xFFFFFFFFu) { break; }
    u32 nrow_off = M7_ROW_BASE + step * M7_ROW_MAX;
    u32 par_off = M7_PAR_BASE + step * M7_ROW_MAX;
    cur_qn = full_bva_filter_row(h, row_off, nrow_off, par_off, cur_qn, best_lit);
    if (cur_qn < 2u) { break; }
    scr[step] = best_lit;
    scr[32u + step] = cur_qn;
    counted[best_lit] = (u8)1;
    step = step + 1u;
    u64 dm = (u64)step;
    u64 mn = (u64)cur_qn;
    u64 prod = dm * mn;
    u64 sum = dm + mn;
    if (prod > sum) {
      u64 red = prod - sum;
      if (red > elim_bound && red > best_red) {
        best_red = red;
        best_k = step - 1u;
      }
    }
  }
  u32 ci = 0u;
  while (ci < step) {
    counted[scr[ci]] = (u8)0;
    ci = ci + 1u;
  }
  if (best_k == 0u) { return false; }
  u32 *touched = (u32 *)h->work_stk2;
  u32 *tmark = (u32 *)h->wsort;
  u64 tlimit = h->cur_vars << 1;
  u64 nt = 0ULL;
  u32 fi = 0u;
  u32 bf_end = best_k + 1u;
  while (fi < bf_end) {
    u32 lit = scr[fi];
    if (tmark[lit] == 0u && nt < tlimit) {
      tmark[lit] = 1u; touched[nt] = lit; nt = nt + 1ULL;
    }
    u32 neg = lit ^ 1u;
    if (tmark[neg] == 0u && nt < tlimit) {
      tmark[neg] = 1u; touched[nt] = neg; nt = nt + 1ULL;
    }
    fi = fi + 1u;
  }
  u32 qn_best = scr[32u + best_k];
  u32 bkey = scr[best_k];
  u32 brow_off = M7_ROW_BASE + best_k * M7_ROW_MAX;
  u32 qi = 0u;
  while (qi < qn_best) {
    u32 entry = scr[brow_off + qi]; qi = qi + 1u;
    if ((entry & PW_BIN_FLAG) != 0u) {
      u32 other = entry & PW_LIT_MASK;
      if (tmark[other] == 0u && nt < tlimit) {
        tmark[other] = 1u; touched[nt] = other; nt = nt + 1ULL;
      }
    } else {
      u32 csz = arena[(u64)entry + 2ULL];
      u32 j = 0u;
      while (j < csz) {
        u32 l = arena[(u64)entry + 3ULL + (u64)j];
        if (l != bkey && tmark[l] == 0u && nt < tlimit) {
          tmark[l] = 1u; touched[nt] = l; nt = nt + 1ULL;
        }
        j = j + 1u;
      }
    }
  }
  u64 ti = 0ULL;
  while (ti < nt) { tmark[touched[ti]] = 0u; ti = ti + 1ULL; }
  h->res_sz = nt;
  return full_bva_commit(h, best_k);
}

u64 full_factor_m7(FullHdr *h, u64 budget) {
  if (h->cur_vars >= h->max_vars || h->scratch_cap < M7_SCR_MIN || budget == 0ULL) {
    return 1ULL;
  }
  u64 init_cv = h->cur_vars;
  u64 init_nlits = init_cv << 1;
  u32 *tmark = (u32 *)h->wsort;
  u32 *fheap = (u32 *)h->tarjan_mark;
  u32 *fpos = (u32 *)h->tarjan_reach;
  u32 *fl = (u32 *)h->flags;
  u32 *wvec = (u32 *)h->watch_vec;
  i8 *vals = (i8 *)h->values;
  u64 zi = 0ULL;
  while (zi < init_nlits) {
    tmark[zi] = 0u; fheap[zi] = 0u; fpos[zi] = 0xFFFFFFFFu;
    zi = zi + 1ULL;
  }
  u32 hsz = 0u;
  u64 v = 0ULL;
  while (v < init_cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 pl = (u32)(v << 1);
      u32 nl = pl | 1u;
      if ((fl[v] & FL_FACT_P) != 0u && wvec[((u64)pl << 1) + 1ULL] > 1u) {
        fheap[hsz] = pl; fpos[pl] = hsz;
        full_fheap_up(fheap, fpos, wvec, hsz); hsz = hsz + 1u;
      }
      if ((fl[v] & FL_FACT_N) != 0u && wvec[((u64)nl << 1) + 1ULL] > 1u) {
        fheap[hsz] = nl; fpos[nl] = hsz;
        full_fheap_up(fheap, fpos, wvec, hsz); hsz = hsz + 1u;
      }
    }
    v = v + 1ULL;
  }
  while (hsz > 0u && h->cur_vars < h->max_vars && budget > 0ULL && h->oom == 0ULL) {
    u32 f0 = fheap[0];
    hsz = hsz - 1u;
    fpos[f0] = 0xFFFFFFFFu;
    if (hsz > 0u) {
      fheap[0] = fheap[hsz];
      fpos[fheap[0]] = 0u;
      full_fheap_down(fheap, fpos, wvec, 0u, hsz);
    }
    u32 fv = f0 >> 1;
    u32 fbit = ((f0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
    if ((fl[fv] & FL_ACTIVE) == 0u) { continue; }
    if ((fl[fv] & fbit) == 0u) { continue; }
    if (vals[f0] != (i8)0) { continue; }
    fl[fv] = fl[fv] & (~fbit);
    if (wvec[((u64)f0 << 1) + 1ULL] <= 1u) { continue; }
    budget = budget - 1ULL;
    if (full_bva_try_lit(h, f0, init_cv)) {
      u32 *touched = (u32 *)h->work_stk2;
      u64 nt = h->res_sz;
      u64 n2 = (nt > init_nlits) ? init_nlits : nt;
      u64 tj = 0ULL;
      while (tj < n2) {
        u32 tl = touched[tj];
        if ((u64)tl < init_nlits) {
          u32 p = fpos[tl];
          if (p < hsz) {
            full_fheap_up(fheap, fpos, wvec, p);
            u32 p2 = fpos[tl];
            if (p2 < hsz) {
              full_fheap_down(fheap, fpos, wvec, p2, hsz);
            }
          } else if ((u64)hsz < init_nlits) {
            u32 tv = tl >> 1;
            u32 tbit = ((tl & 1u) != 0u) ? FL_FACT_N : FL_FACT_P;
            if ((fl[tv] & FL_ACTIVE) != 0u && (fl[tv] & tbit) != 0u &&
                wvec[((u64)tl << 1) + 1ULL] > 1u && vals[tl] == (i8)0 && p == 0xFFFFFFFFu) {
              fheap[hsz] = tl; fpos[tl] = hsz;
              full_fheap_up(fheap, fpos, wvec, hsz);
              hsz = hsz + 1u;
            }
          }
        }
        tj = tj + 1ULL;
      }
    }
  }
  u64 end_nlits = h->cur_vars << 1;
  u64 ci = 0ULL;
  while (ci < end_nlits) {
    fheap[ci] = 0u; fpos[ci] = 0u;
    ci = ci + 1ULL;
  }
  if (h->cur_vars > init_cv) {
    u64 cv = h->cur_vars;
    u32 *qn = (u32 *)h->q_next;
    u32 *qs = (u32 *)h->q_stamp;
    u64 p = h->q_first;
    u64 s = 0ULL;
    while (p < cv && s < cv) {
      s = s + 1ULL;
      qs[p] = (u32)s;
      p = (u64)qn[p];
    }
    h->q_cur_stamp = s;
    if (h->q_search_idx < cv) {
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  return 1ULL;
}
"

/-- Drop-in M7 `Fn` handle preserving the canonical `"full_init_fresh_var"` symbol name. -/
def m7InitFreshVarFn : Fn :=
  ⟨"full_init_fresh_var", [i64, i32], [], full_init_fresh_var_m7_body⟩

/-- Drop-in M7 `Fn` handle preserving the canonical `"full_bva_try_lit"` symbol name. -/
def m7BvaTryLitFn : Fn :=
  ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], full_bva_try_lit_m7_body⟩

/-- Drop-in M7 `Fn` handle preserving the canonical `"full_factor"` symbol name. -/
def m7FactorFn : Fn :=
  ⟨"full_factor", [i64, i64], [i64], full_factor_m7_body⟩

/-- Drop-in function list (`3` upgraded fns in topological callee-first order). -/
def m7BvaFactorFns : List Fn :=
  [m7InitFreshVarFn, m7BvaTryLitFn, m7FactorFn]

/-- External callee declarations for standalone `FullM7BvaFactor` verification. -/
def m7BvaFactorExterns : List Extern :=
  [ ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32]⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32]⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool]⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], []⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], []⟩
  ]

/-- Standalone closed module (`3` functions + `6` externs, `0` exits). -/
def m7BvaFactorModule : LeanQbe.T.Module :=
  { fns := m7BvaFactorFns, externs := m7BvaFactorExterns, exits := [] }

/-- Reconcile `FullM7BvaFactor` overrides cleanly into a larger Kissat `Fn` list. -/
def spliceM7BvaFactorFns (fns : List Fn) : List Fn :=
  fns.map fun f =>
    if f.name = "full_init_fresh_var" then m7InitFreshVarFn
    else if f.name = "full_bva_try_lit" then m7BvaTryLitFn
    else if f.name = "full_factor" then m7FactorFn
    else f

theorem full_init_fresh_var_m7_wf : Func.Wf full_init_fresh_var_m7_body := by t_wf_reify
theorem full_bva_try_lit_m7_wf : Func.Wf full_bva_try_lit_m7_body := by t_wf_reify
theorem full_factor_m7_wf : Func.Wf full_factor_m7_body := by t_wf_reify

theorem m7InitFreshVarFn_wf : m7InitFreshVarFn.Wf := full_init_fresh_var_m7_wf
theorem m7BvaTryLitFn_wf : m7BvaTryLitFn.Wf := full_bva_try_lit_m7_wf
theorem m7FactorFn_wf : m7FactorFn.Wf := full_factor_m7_wf

theorem m7BvaFactorFns_wf : ∀ f ∈ m7BvaFactorFns, f.Wf := by
  intro f hf
  simp only [m7BvaFactorFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact m7InitFreshVarFn_wf
  · exact m7BvaTryLitFn_wf
  · exact m7FactorFn_wf

theorem m7BvaFactor_fns_wf : ∀ f ∈ m7BvaFactor_fns, f.Wf := by
  intro f hf
  simp only [m7BvaFactor_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact full_init_fresh_var_m7_wf
  · exact full_bva_try_lit_m7_wf
  · exact full_factor_m7_wf

theorem m7BvaFactor_acyclic : m7BvaFactorModule.checkAcyclic = true := by decide

end LeanQbe.T.Examples.Kissat.FullM7BvaFactor
