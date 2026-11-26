/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
public import LeanQbe.T.Examples.Kissat.ExportCnfFmt
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Wf

/-!
# Verified C0 Simplified-CNF State Exporter (`ExportCnfState`)

Strictly additive, data-pure (`0` `*Proof*`/`*Lemmas*`/`*Spec*` imports) C0 leaf module
implementing the 2-pass acyclic, iterative simplified-CNF DIMACS exporter over Kissat's frozen
`FullHdr` state layout (`<= 5` `u64` arguments per function, `0` exits, `0` stack allocations,
legal on both SysV x86-64 and AAPCS64 Arm64):

1. `kissat_export_arena_next(h, cref)`: `PH_SHRK`-aware arena scanner matching `fullArenaNextOff`.
2. `kissat_export_trail_units(h, out, cap, pos, cnt_ptr)`: counts/emits level-0 `h->trail` units.
3. `kissat_export_bin_clauses(h, out, cap, pos, cnt_ptr)`: counts/emits binary clauses in
   `watch_stk` (`PW_BIN_FLAG`, deduplicated by `l0 < l1`), valid in both sparse and dense watch
   modes.
4. `kissat_export_arena_clauses(h, out, cap, pos, cnt_ptr)`: counts/emits live irredundant arena
   clauses (`(hdr & (PH_GARB | PH_RED)) == 0`).
5. `kissat_export_cnf_bytes(h, out, cap, out_len_ptr)`:
   - if `h->cur_level > 0`, calls `full_backtrack(h, 0ULL)` (against canonical `fullBacktrackSpec`);
   - if `h->inconsistent != 0`, emits `"p cnf 0 1\n0\n"` (`12` bytes);
   - else runs Pass 1 (dry-run `cap = 0`) to count `clause_cnt` and `need` bytes, checks
     `dimacsBound` (`< 2^28`) and `need <= cap`, and runs Pass 2 to emit header + clauses via
     `ExportCnfFmt`.

Separation-logic WP proofs and UNSAT-soundness round-trip theorems (`FullWitnessInv` -> valid
`parseDimacs` output with `cnfOut.Unsat -> F0.Unsat`) live in
`LeanQbe.T.Examples.Kissat.ExportCnfStateProof`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfState

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat.ExportCnfFmt

@[expose] public section

local elab "export_cnf_state_c0! " pfx:ident src:str : command => do
  let nm := Lean.mkIdent `exportCnfStateC0Src
  let defCmd ← `(command| def $nm : String := $src)
  Lean.Elab.Command.elabCommand defCmd
  elabC0Module (some pfx.getId) src.getString (forceExpose := true) (emitModule := false)

export_cnf_state_c0! exportCnfState "
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

#define PH_GARB             0x00080000u
#define PH_RED              0x00400000u
#define PH_SHRK             0x00800000u
#define PW_BIN_FLAG         0x80000000u
#define PW_LIT_MASK         0x7FFFFFFFu
#define EXPORT_DIMACS_BOUND 268435456ULL

extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 kissat_emit_byte(u64 out, u64 cap, u64 pos, u64 b);
extern u64 kissat_emit_dimacs_lit(u64 out, u64 cap, u64 pos, u64 lit);
extern u64 kissat_emit_dimacs_hdr(u64 out, u64 cap, u64 pos, u64 mv, u64 nc);

u64 kissat_export_arena_next(FullHdr *h, u64 cref) {
  u32 *ar = (u32 *)h->arena;
  u64 alen = h->arena_len;
  if (cref + 3ULL > alen) {
    return alen;
  }
  u32 hdr = ar[cref];
  u32 sz = ar[cref + 2ULL];
  u64 p = cref + 3ULL + (u64)sz;
  if (p > alen) {
    return alen;
  }
  if ((hdr & PH_SHRK) != 0u) {
    while (p < alen && ar[p] != 0xFFFFFFFFu) {
      p = p + 1ULL;
    }
    if (p < alen) {
      p = p + 1ULL;
    }
  }
  return p;
}

u64 kissat_export_trail_units(FullHdr *h, u64 out, u64 cap, u64 pos, u64 *cnt_ptr) {
  u32 *trl = (u32 *)h->trail;
  u64 te = h->trail_end;
  u64 i = 0ULL;
  while (i < te) {
    u64 lit = (u64)trl[i];
    pos = kissat_emit_dimacs_lit(out, cap, pos, lit);
    pos = kissat_emit_byte(out, cap, pos, 48ULL);
    pos = kissat_emit_byte(out, cap, pos, 10ULL);
    i = i + 1ULL;
  }
  *cnt_ptr = *cnt_ptr + te;
  return pos;
}

u64 kissat_export_bin_clauses(FullHdr *h, u64 out, u64 cap, u64 pos, u64 *cnt_ptr) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 nlits = h->cur_vars * 2ULL;
  u64 cnt = *cnt_ptr;
  u64 l0 = 0ULL;
  while (l0 < nlits) {
    u64 off = (u64)wvec[l0 * 2ULL];
    u64 sz = (u64)wvec[l0 * 2ULL + 1ULL];
    u64 end = off + sz;
    u64 p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u64 l1 = (u64)(w0 & PW_LIT_MASK);
        if (l0 < l1) {
          pos = kissat_emit_dimacs_lit(out, cap, pos, l0);
          pos = kissat_emit_dimacs_lit(out, cap, pos, l1);
          pos = kissat_emit_byte(out, cap, pos, 48ULL);
          pos = kissat_emit_byte(out, cap, pos, 10ULL);
          cnt = cnt + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    l0 = l0 + 1ULL;
  }
  *cnt_ptr = cnt;
  return pos;
}

u64 kissat_export_arena_clauses(FullHdr *h, u64 out, u64 cap, u64 pos, u64 *cnt_ptr) {
  u32 *ar = (u32 *)h->arena;
  u64 alen = h->arena_len;
  u64 cnt = *cnt_ptr;
  u64 cref = 0ULL;
  while (cref + 3ULL <= alen) {
    u32 hdr = ar[cref];
    u32 sz = ar[cref + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u) {
      u64 i = 0ULL;
      u64 n = (u64)sz;
      while (i < n) {
        u64 lit = (u64)ar[cref + 3ULL + i];
        pos = kissat_emit_dimacs_lit(out, cap, pos, lit);
        i = i + 1ULL;
      }
      pos = kissat_emit_byte(out, cap, pos, 48ULL);
      pos = kissat_emit_byte(out, cap, pos, 10ULL);
      cnt = cnt + 1ULL;
    }
    cref = kissat_export_arena_next(h, cref);
  }
  *cnt_ptr = cnt;
  return pos;
}

u64 kissat_export_cnf_bytes(FullHdr *h, u64 out, u64 cap, u64 *out_len_ptr) {
  if (h->cur_level > 0ULL) {
    full_backtrack(h, 0ULL);
  }
  if (h->inconsistent != 0ULL) {
    *out_len_ptr = 12ULL;
    if (cap < 12ULL) {
      return 0ULL;
    }
    u64 pos = kissat_emit_dimacs_hdr(out, cap, 0ULL, 0ULL, 1ULL);
    pos = kissat_emit_byte(out, cap, pos, 48ULL);
    pos = kissat_emit_byte(out, cap, pos, 10ULL);
    *out_len_ptr = pos;
    return 1ULL;
  }
  u64 mv = h->cur_vars;
  if (mv >= EXPORT_DIMACS_BOUND) {
    *out_len_ptr = 0ULL;
    return 0ULL;
  }
  *out_len_ptr = 0ULL;
  u64 body_len = kissat_export_trail_units(h, out, 0ULL, 0ULL, out_len_ptr);
  body_len = kissat_export_bin_clauses(h, out, 0ULL, body_len, out_len_ptr);
  body_len = kissat_export_arena_clauses(h, out, 0ULL, body_len, out_len_ptr);
  u64 clause_cnt = *out_len_ptr;
  if (clause_cnt >= EXPORT_DIMACS_BOUND) {
    *out_len_ptr = 0ULL;
    return 0ULL;
  }
  u64 hdr_len = kissat_emit_dimacs_hdr(out, 0ULL, 0ULL, mv, clause_cnt);
  u64 need = hdr_len + body_len;
  *out_len_ptr = need;
  if (need > cap) {
    return 0ULL;
  }
  *out_len_ptr = 0ULL;
  u64 pos = kissat_emit_dimacs_hdr(out, cap, 0ULL, mv, clause_cnt);
  pos = kissat_export_trail_units(h, out, cap, pos, out_len_ptr);
  pos = kissat_export_bin_clauses(h, out, cap, pos, out_len_ptr);
  pos = kissat_export_arena_clauses(h, out, cap, pos, out_len_ptr);
  *out_len_ptr = pos;
  return 1ULL;
}
"

/-- Combined callees-first function list (`4` formatter helpers + `5` state exporter helpers). -/
def exportCnfStateAllFns : List Fn :=
  exportCnfFmt_fns ++ exportCnfState_fns

/-- Acyclic `Module` packaging `ExportCnfFmt` + `ExportCnfState` with sole Kissat extern
`full_backtrack(FullHdr*, u64)` and zero exits. -/
def exportCnfStateMod : LeanQbe.T.Module :=
  { fns := exportCnfStateAllFns
    externs := [⟨"full_backtrack", [i64, i64], []⟩]
    exits := [] }

end

/-! ## Well-Formedness and Structural Certificates (`Func.Wf`, Acyclicity, Arity) -/

public section

theorem kissat_export_arena_next_wf : Func.Wf kissat_export_arena_next_body := by
  t_wf_tac

theorem kissat_export_trail_units_wf : Func.Wf kissat_export_trail_units_body := by
  t_wf_tac

theorem kissat_export_bin_clauses_wf : Func.Wf kissat_export_bin_clauses_body := by
  t_wf_tac

theorem kissat_export_arena_clauses_wf : Func.Wf kissat_export_arena_clauses_body := by
  t_wf_tac

theorem kissat_export_cnf_bytes_wf : Func.Wf kissat_export_cnf_bytes_body := by
  t_wf_tac

/-- All five functions in `exportCnfState_fns` satisfy `Fn.Wf`. -/
theorem exportCnfState_fns_wf : ∀ f ∈ exportCnfState_fns, f.Wf := by
  intro f hf
  simp only [exportCnfState_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact kissat_export_arena_next_wf
  · exact kissat_export_trail_units_wf
  · exact kissat_export_bin_clauses_wf
  · exact kissat_export_arena_clauses_wf
  · exact kissat_export_cnf_bytes_wf

/-- All nine functions in `exportCnfStateAllFns` satisfy `Fn.Wf`. -/
theorem exportCnfStateAllFns_wf : ∀ f ∈ exportCnfStateAllFns, f.Wf := by
  intro f hf
  rw [exportCnfStateAllFns, List.mem_append] at hf
  exact hf.elim (exportCnfFmt_fns_wf f) (exportCnfState_fns_wf f)

/-- Acyclicity certificate for `exportCnfStateMod`. -/
theorem exportCnfStateMod_checkAcyclic : exportCnfStateMod.checkAcyclic = true := by
  decide

/-- Unique function-name certificate for `exportCnfStateMod`. -/
theorem exportCnfStateMod_namesNodup : exportCnfStateMod.namesNodup := by
  simp only [Module.namesNodup, Module.names, exportCnfStateMod, exportCnfStateAllFns,
    exportCnfFmt_fns, exportCnfState_fns]
  decide

/-- Every function in `exportCnfStateAllFns` takes at most 6 scalar arguments (x64 & Arm64 ABI). -/
theorem exportCnfStateAllFns_max6args : ∀ f ∈ exportCnfStateAllFns, f.as.length ≤ 6 := by
  intro f hf
  simp only [exportCnfStateAllFns, exportCnfFmt_fns, exportCnfState_fns,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end

end LeanQbe.T.Examples.Kissat.ExportCnfState
