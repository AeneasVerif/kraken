module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M4g (`A5a` / `VarF`): Focused-Mode `full_heap_up` Elision in `full_bump_var_m4`

Standalone M4g C0 optimization off `main @ d8468dce` (`0` edits to landed `Full*` / `FullM3*`),
keeping the byte-identical `144`-word `FullHdr` layout and exact `Full.fullBumpVarSpec` contract:

- `full_bump_var_m4(FullHdr *h, u32 v)` always updates the VSIDS score `h->score[v]` (and calls
  `full_rescale(h)` on saturation) so VSIDS scores stay warm across focused phases (`stable == 0`),
  but guards `full_heap_up(h, v)` with `if (h->stable != 0ULL)`.
- **100% trajectory-identical**: nothing reads `h->heap` or `h->pos` while `h->stable == 0`
  (`full_switch_mode` rebuilds `h->heap`/`h->pos` from `h->score` on entry to stable mode).
- Exports `m4BumpVarFn` renamed to `"full_bump_var"` for single-line splicing at M4 unify.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bump

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m4Bump "
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

extern void full_heap_up(FullHdr *h, u32 v);
extern void full_rescale(FullHdr *h);

void full_bump_var_m4(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return; }
  u64 *sc = (u64 *)h->score;
  u64 cur = sc[v];
  u64 inc = h->scinc;
  u64 nsc = (cur > (1ULL << 61) || inc > (1ULL << 61)) ? (1ULL << 60) : (cur + inc);
  sc[v] = nsc;
  if (h->stable != 0ULL) { full_heap_up(h, v); }
  if (nsc >= (1ULL << 60)) { full_rescale(h); }
}
"

/-- External callee signatures referenced by `m4Bump_fns`. -/
def m4BumpExterns : List Extern :=
  [ ⟨"full_heap_up", [i64, i32], []⟩
  , ⟨"full_rescale", [i64], []⟩ ]

/-- Standalone M4g module (`1` upgraded function + `2` externs, `0` exits). -/
def m4BumpModule : LeanQbe.T.Module :=
  { fns := m4Bump_fns, externs := m4BumpExterns, exits := [] }

/-- Drop-in replacement `Fn` renamed to `"full_bump_var"` for M4 unification. -/
def m4BumpVarFn : Fn :=
  ⟨"full_bump_var", [i64, i32], [], full_bump_var_m4_body⟩

theorem full_bump_var_m4_wf : Func.Wf full_bump_var_m4_body := by
  t_wf_reify

theorem m4Bump_fns_wf : ∀ f ∈ m4Bump_fns, f.Wf := by
  simp only [m4Bump_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact full_bump_var_m4_wf

theorem m4BumpVarFn_wf : m4BumpVarFn.Wf :=
  full_bump_var_m4_wf

theorem m4Bump_acyclic : m4BumpModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM4Bump
