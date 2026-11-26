/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Examples.Kissat.Dimacs

/-!
# Kissat Step-11 `S11-7` Consistent-State Backtrack & OTFS Counters (`FullFidelityBacktrackCs`)

Purely additive C0 layer (`0` edits to Step-10 modules, `<= 6` args per fn, `0` new memory):
1. **`full_save_target_best`:** Computes `assigned = cur_vars - unassigned` (guarded by
   `cur_vars > unassigned`), matching upstream `kissat_assigned (solver)`.
2. **`full_backtrack` (consistent-state default) + `full_backtrack_ac_fid` (after-conflict):**
   Rebinds default `"full_backtrack"` to the consistent-state body (`backtrack.c:150-153`),
   inserts `full_backtrack_ac_fid` (exact `FullM5HeurCore.full_backtrack_m5_body`,
   `backtrack.c:155-161`) before `"full_one_lit_confl"`, and rewires the `3` conflict callers
   present in `fidStep10Module`: `full_one_lit_confl`, `full_learn_clause`, `full_learn_clause_m6`.
3. **OTFS binary caller counters (`full_deduce_1uip_m6`, `full_deduce_1uip_m6_hdr`):**
   Decrements `h->num_redundant` or `h->num_irred` in the caller when `full_otfs_bin` returns
   `true` (`deduce.c:149-154`), leaving `fullOtfsBinSpec` unchanged.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

kissat_c0! fid11BacktrackCs "
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

#define PH_RED       0x00400000u
#define PW_BIN_FLAG  0x80000000u

extern void full_save_target_best(FullHdr *h);
extern void full_backtrack_raw_m5(FullHdr *h, u64 target_lvl);
extern bool full_analyze_lit(FullHdr *h, u32 lit, u32 skip_var);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern void full_clear_ana(FullHdr *h);
extern bool full_otfs_large(FullHdr *h, u32 cref, u32 uip);
extern bool full_otfs_bin(FullHdr *h, u32 cref, u32 uip);
extern void full_otfs_subsume(FullHdr *h, u32 cref, u64 old_ct, u64 old_cr, bool to_bin);

void fid11_save_target_best(FullHdr *h) {
  if (h->probing != 0ULL || h->stable == 0ULL) { return; }
  i8 *vals = (i8 *)h->values;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  u64 cv = h->cur_vars;
  u64 assigned = (cv > h->unassigned) ? (cv - h->unassigned) : 0ULL;
  if (assigned > h->target_assigned) {
    h->target_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { ptgt[k] = tv; }
      k = k + 1ULL;
    }
  }
  if (assigned > h->best_assigned) {
    h->best_assigned = assigned;
    u64 k = 0ULL;
    while (k < cv) {
      i8 tv = vals[k << 1];
      if (tv != (i8)0) { pbst[k] = tv; }
      k = k + 1ULL;
    }
  }
}

void fid11_backtrack_cs(FullHdr *h, u64 target_lvl) {
  if (h->cur_level <= target_lvl) { return; }
  full_save_target_best(h);
  u64 saved_prob = h->probing;
  h->probing = 1ULL;
  full_backtrack_raw_m5(h, target_lvl);
  h->probing = saved_prob;
}

u64 fid11_deduce_1uip_m6(FullHdr *h) {
  h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; h->min_clr_len = 0ULL;
  h->ant_sz = 0ULL; h->res_sz = 0ULL;
  bool seed_ok = false;
  if (h->confl_type == 1ULL) {
    seed_ok = full_analyze_lit(h, (u32)h->confl_lit0, 0xFFFFFFFFu) &&
              full_analyze_lit(h, (u32)h->confl_lit1, 0xFFFFFFFFu);
  } else if (h->confl_ref + 3ULL <= h->arena_len) {
    seed_ok = full_analyze_rsn(h, (u32)h->confl_ref, 0xFFFFFFFFu);
  }
  u64 init_res_sz = h->res_sz;
  u64 tcnt = h->tmp_cnt;
  if (!seed_ok || tcnt == 0ULL) {
    full_clear_ana(h);
    if (seed_ok && h->tmp_len == 1ULL) { return 20ULL; }
    return 0ULL;
  }
  u8 *mrk = (u8 *)h->mark; u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason; u32 *trl = (u32 *)h->trail;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u32 cur_lvl = (u32)h->cur_level; u64 idx = h->trail_end;
  u32 uip_lit = 0xFFFFFFFFu; u64 resolved = 0ULL;
  while (tcnt > 0ULL) {
    if (idx == 0ULL) { full_clear_ana(h); return 0ULL; }
    idx = idx - 1ULL;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((u64)pv >= cv) { full_clear_ana(h); return 0ULL; }
    if (mrk[pv] != (u8)0 && lvl[pv] == cur_lvl) {
      tcnt = tcnt - 1ULL;
      h->tmp_cnt = tcnt;
      if (tcnt == 0ULL) { uip_lit = p ^ 1u; break; }
      u32 rsn = rsns[pv]; h->ant_sz = 0ULL; resolved = resolved + 1ULL;
      if (!full_analyze_rsn(h, rsn, pv)) { full_clear_ana(h); return 0ULL; }
      tcnt = h->tmp_cnt;
      u64 rsz = h->res_sz;
      if (rsz > 0ULL) { rsz = rsz - 1ULL; h->res_sz = rsz; }
      u64 asz = h->ant_sz;
      if (asz >= 3ULL && rsz < asz && (rsn & PW_BIN_FLAG) == 0u) {
        u64 old_ct = h->confl_type; u64 old_cr = h->confl_ref;
        if (asz == 3ULL) {
          if (full_otfs_bin(h, rsn, p)) {
            u32 *ar = (u32 *)h->arena;
            bool rsn_red = ((ar[rsn] & PH_RED) != 0u);
            if (rsn_red) {
              if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
            } else {
              if (h->num_irred > 0ULL) { h->num_irred = h->num_irred - 1ULL; }
            }
            if (resolved == 1ULL && h->res_sz < init_res_sz) {
              full_otfs_subsume(h, 0u, old_ct, old_cr, true);
            }
            h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
          }
        } else if (full_otfs_large(h, rsn, p)) {
          h->confl_type = 2ULL; h->confl_ref = (u64)rsn;
          if (resolved == 1ULL && h->res_sz < init_res_sz) {
            full_otfs_subsume(h, rsn, old_ct, old_cr, false);
          }
          h->res_sz = h->min_clr_len; full_clear_ana(h); return 2ULL;
        }
      }
    }
  }
  if (uip_lit == 0xFFFFFFFFu) { full_clear_ana(h); return 0ULL; }
  tmp[0] = uip_lit;
  h->res_sz = h->min_clr_len;
  full_clear_ana(h);
  return 1ULL;
}
"

/-- Callee rename routing `"full_backtrack"` to after-conflict `"full_backtrack_ac_fid"`. -/
def pr3BtAcMap : Sym → Sym
  | "full_backtrack" => "full_backtrack_ac_fid"
  | s => s

/-- Callee rename routing `"full_analyze_rsn"` to `"full_analyze_rsn_m6_hdr"`. -/
def pr3ArsnHdrMap : Sym → Sym
  | "full_analyze_rsn" => "full_analyze_rsn_m6_hdr"
  | s => s

/-- Rebound `full_one_lit_confl` body calling `full_backtrack_ac_fid`. -/
def fid11OneLitConflBody : Func [i64] [i64] :=
  renameFuncCalls pr3BtAcMap FullM5Otfs.full_one_lit_confl_m5_body

/-- Rebound `full_learn_clause` body calling `full_backtrack_ac_fid`. -/
def fid11LearnClauseBody : Func [i64, i64] [i64] :=
  renameFuncCalls pr3BtAcMap FullFidelityStep7.full_learn_clause_body

/-- Rebound `full_learn_clause_m6` body calling `full_backtrack_ac_fid`. -/
def fid11LearnClauseM6Body : Func [i64, i64] [i64] :=
  renameFuncCalls pr3BtAcMap FullFidelityStep10.full_learn_clause_m6_body

/-- `full_deduce_1uip_m6_hdr` body matching `fid11_deduce_1uip_m6` with M6Hdr reasons. -/
def fid11Deduce1uipM6HdrBody : Func [i64] [i64] :=
  renameFuncCalls pr3ArsnHdrMap fid11_deduce_1uip_m6_body

/-- Replacement `Fn` for `"full_save_target_best"` (`assigned = cur_vars - unassigned`). -/
def fid11SaveTargetBestFn : Fn :=
  ⟨"full_save_target_best", [i64], [], fid11_save_target_best_body⟩

/-- Replacement `Fn` for default consistent-state `"full_backtrack"`. -/
def fid11BacktrackFn : Fn :=
  ⟨"full_backtrack", [i64, i64], [], fid11_backtrack_cs_body⟩

/-- Helper `Fn` `"full_backtrack_ac_fid"` (exact `FullM5HeurCore.full_backtrack_m5_body`). -/
def fid11BacktrackAcFn : Fn :=
  ⟨"full_backtrack_ac_fid", [i64, i64], [], FullM5HeurCore.full_backtrack_m5_body⟩

/-- Replacement `Fn` for `"full_one_lit_confl"`. -/
def fid11OneLitConflFn : Fn :=
  ⟨"full_one_lit_confl", [i64], [i64], fid11OneLitConflBody⟩

/-- Replacement `Fn` for `"full_learn_clause"`. -/
def fid11LearnClauseFn : Fn :=
  ⟨"full_learn_clause", [i64, i64], [i64], fid11LearnClauseBody⟩

/-- Replacement `Fn` for `"full_learn_clause_m6"`. -/
def fid11LearnClauseM6Fn : Fn :=
  ⟨"full_learn_clause_m6", [i64, i64], [i64], fid11LearnClauseM6Body⟩

/-- Replacement `Fn` for `"full_deduce_1uip_m6"`. -/
def fid11Deduce1uipM6Fn : Fn :=
  ⟨"full_deduce_1uip_m6", [i64], [i64], fid11_deduce_1uip_m6_body⟩

/-- Replacement `Fn` for `"full_deduce_1uip_m6_hdr"`. -/
def fid11Deduce1uipM6HdrFn : Fn :=
  ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], fid11Deduce1uipM6HdrBody⟩

/-- `S11-7` replacement functions (`7` fns). -/
def fid11BacktrackCsRepls : List Fn :=
  [ fid11SaveTargetBestFn
  , fid11BacktrackFn
  , fid11Deduce1uipM6Fn
  , fid11Deduce1uipM6HdrFn
  , fid11OneLitConflFn
  , fid11LearnClauseFn
  , fid11LearnClauseM6Fn ]

/-- `S11-7` helper insertion (`full_backtrack_ac_fid` inserted before `"full_one_lit_confl"`). -/
def fid11BacktrackCsBefores : List (Sym × List Fn) :=
  [ ("full_one_lit_confl", [fid11BacktrackAcFn]) ]

end

public section

theorem fid11_save_target_best_wf : Func.Wf fid11SaveTargetBestFn.body := by
  t_wf_reify

theorem fid11_backtrack_cs_wf : Func.Wf fid11BacktrackFn.body := by
  t_wf_reify

theorem fid11_backtrack_ac_wf : Func.Wf fid11BacktrackAcFn.body :=
  FullM5HeurCore.full_backtrack_m5_wf

theorem fid11_one_lit_confl_wf : Func.Wf fid11OneLitConflFn.body := fun _ _ _ _ xs₁ xs₂ =>
  wf_renameExprCalls (FullM5Otfs.full_one_lit_confl_m5_wf _ _ _ _ xs₁ xs₂)

theorem fid11_learn_clause_wf : Func.Wf fid11LearnClauseFn.body := fun _ _ _ _ xs₁ xs₂ =>
  wf_renameExprCalls (FullFidelityStep7.full_learn_clause_step7_wf _ _ _ _ xs₁ xs₂)

theorem fid11_learn_clause_m6_wf : Func.Wf fid11LearnClauseM6Fn.body := fun _ _ _ _ xs₁ xs₂ =>
  wf_renameExprCalls (FullFidelityStep10.full_learn_clause_m6_step10_wf _ _ _ _ xs₁ xs₂)

theorem fid11_deduce_1uip_m6_wf : Func.Wf fid11Deduce1uipM6Fn.body := by
  t_wf_reify

theorem fid11_deduce_1uip_m6_hdr_wf : Func.Wf fid11Deduce1uipM6HdrFn.body :=
  fun _ _ _ _ xs₁ xs₂ => wf_renameExprCalls (fid11_deduce_1uip_m6_wf _ _ _ _ xs₁ xs₂)

theorem fid11BacktrackCsRepls_wf : ∀ f ∈ fid11BacktrackCsRepls, f.Wf := by
  intro f hf
  simp only [fid11BacktrackCsRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fid11_save_target_best_wf
  · exact fid11_backtrack_cs_wf
  · exact fid11_deduce_1uip_m6_wf
  · exact fid11_deduce_1uip_m6_hdr_wf
  · exact fid11_one_lit_confl_wf
  · exact fid11_learn_clause_wf
  · exact fid11_learn_clause_m6_wf

theorem fid11BacktrackCsBefores_wf : ∀ h ∈ fid11BacktrackCsBefores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fid11BacktrackCsBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_singleton] at hh
  subst hh
  exact fid11_backtrack_ac_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
