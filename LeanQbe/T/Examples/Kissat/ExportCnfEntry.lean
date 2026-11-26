/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
public import LeanQbe.T.Examples.Kissat.ExportCnfState
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Wf

/-!
# Verified Simplified-CNF Exporter — Shard E3 (Data-Pure C0 Entrypoint)

Strictly additive, data-pure (`0` `*Proof*`/`*Lemmas*`/`*Spec*` imports) C0 leaf module
implementing the end-to-end simplified-CNF export entrypoint:
- `KissatExportOut`: `{ out_ptr, out_cap, out_len }` (`24 B`) keeping SysV x64/Arm64 arity `<= 6`;
- `kissat_emit_trivial_cnf_bytes(out, cap, out_len_ptr, is_unsat)`: bounds-checked emitter
  writing `"p cnf 0 1\n0\n"` (`12 B`, UNSAT `20ULL`) or `"p cnf 0 0\n"` (`10 B`, SAT `10ULL`);
- `kissat_simplify_export_bytes(cnf_ptr, cnf_len, work_ptr, work_cap, fuel, out)`: composes
  `full_m6_mem_init` -> `full_parse_body_m6` -> `full_preprocess_m6` -> `kissat_export_cnf_bytes`,
  fixing upstream `krite.c` `BUG-CROSS-01` by emitting `"p cnf 0 1\n0\n"` whenever UNSAT is
  established during parse (`pb == 20`), preprocessing (`pp == 20`), or solver state export
  (`h->inconsistent != 0`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfEntry

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open LeanQbe.T.Examples.Kissat.ExportCnfState

@[expose] public section

local elab "export_cnf_entry_c0! " pfx:ident src:str : command => do
  let nm := Lean.mkIdent (pfx.getId ++ `C0Src)
  let defCmd ← `(command| def $nm : String := $src)
  Lean.Elab.Command.elabCommand defCmd
  elabC0Module (some pfx.getId) src.getString (forceExpose := true) (emitModule := false)

export_cnf_entry_c0! exportCnfEntry "
typedef struct {
  u64 out_ptr;
  u64 out_cap;
  u64 out_len;
} KissatExportOut;

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

#define M6_HDR_TOTAL_BYTES 3456ULL

extern u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end,
                            u64 work_base, u64 avail, u64 fuel);
extern u64 full_parse_body_m6(FullHdr *h, u64 cnf_end);
extern u64 full_preprocess_m6(FullHdr *h);
extern u64 kissat_emit_byte(u64 out, u64 cap, u64 pos, u64 b);
extern u64 kissat_emit_dimacs_hdr(u64 out, u64 cap, u64 pos, u64 mv, u64 nc);
extern u64 kissat_export_cnf_bytes(FullHdr *h, u64 out, u64 cap,
                                   u64 *out_len_ptr);

u64 kissat_emit_trivial_cnf_bytes(u64 out, u64 cap, u64 *out_len_ptr,
                                  u64 is_unsat) {
  if (is_unsat != 0ULL) {
    *out_len_ptr = 12ULL;
    if (cap < 12ULL) { return 0ULL; }
    u64 pos = kissat_emit_dimacs_hdr(out, cap, 0ULL, 0ULL, 1ULL);
    pos = kissat_emit_byte(out, cap, pos, 48ULL);
    *out_len_ptr = kissat_emit_byte(out, cap, pos, 10ULL);
    return 20ULL;
  }
  *out_len_ptr = 10ULL;
  if (cap < 10ULL) { return 0ULL; }
  *out_len_ptr = kissat_emit_dimacs_hdr(out, cap, 0ULL, 0ULL, 0ULL);
  return 10ULL;
}

u64 kissat_simplify_export_loaded(FullHdr *h, u64 cnf_end,
                                  KissatExportOut *out) {
  u64 pb = full_parse_body_m6(h, cnf_end);
  if (pb == 0ULL) { return 0ULL; }
  u64 out_ptr = out->out_ptr;
  u64 out_cap = out->out_cap;
  if (pb == 20ULL) {
    return kissat_emit_trivial_cnf_bytes(out_ptr, out_cap, &out->out_len, 1ULL);
  }
  u64 pp = full_preprocess_m6(h);
  if (pp == 20ULL) {
    return kissat_emit_trivial_cnf_bytes(out_ptr, out_cap, &out->out_len, 1ULL);
  }
  if (pp == 10ULL) {
    return kissat_emit_trivial_cnf_bytes(out_ptr, out_cap, &out->out_len, 0ULL);
  }
  if (pp != 1ULL) { return 0ULL; }
  u64 ok = kissat_export_cnf_bytes(h, out_ptr, out_cap, &out->out_len);
  if (ok == 0ULL) {
    if (out->out_len <= out_cap) { out->out_len = 0ULL; }
    return 0ULL;
  }
  if (h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 kissat_simplify_export_bytes(
    u64 cnf_ptr, u64 cnf_len,
    u64 work_ptr, u64 work_cap,
    u64 fuel, KissatExportOut *out) {
  if ((u64)out == 0ULL || (((u64)out) & 7ULL) != 0ULL) { return 0ULL; }
  if ((u64)out > (~0ULL) - 24ULL) { return 0ULL; }
  out->out_len = 0ULL;
  u64 out_ptr = out->out_ptr;
  u64 out_cap = out->out_cap;
  if (out_cap > 0ULL && out_ptr == 0ULL) { return 0ULL; }
  if (out_cap > (~0ULL) - out_ptr) { return 0ULL; }
  if (fuel == 0ULL || cnf_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (cnf_len > (~0ULL) - cnf_ptr || work_cap > (~0ULL) - work_ptr) {
    return 0ULL;
  }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + M6_HDR_TOTAL_BYTES) { return 0ULL; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_cap - pad;
  u64 cnf_end = cnf_ptr + cnf_len;
  u64 hdr_addr = full_m6_mem_init(cnf_ptr, cnf_end, work_base, avail, fuel);
  if (hdr_addr == 0ULL) { return 0ULL; }
  return kissat_simplify_export_loaded((FullHdr *)hdr_addr, cnf_end, out);
}
"

/-- Combined function list containing `ExportCnfFmt` (`4`), `ExportCnfState` (`5`),
and `ExportCnfEntry` (`3`) (`12` total). -/
def exportCnfEntryAllFns : List Fn :=
  exportCnfStateAllFns ++ exportCnfEntry_fns

/-- Acyclic `Module` packaging the full exporter stack with the 4 Kissat M6 externs
and zero exits. -/
def exportCnfEntryMod : LeanQbe.T.Module :=
  { fns := exportCnfEntryAllFns
    externs :=
      [ ⟨"full_backtrack", [i64, i64], []⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]⟩
      , ⟨"full_parse_body_m6", [i64, i64], [i64]⟩
      , ⟨"full_preprocess_m6", [i64], [i64]⟩ ]
    exits := [] }

end

/-! ## Well-Formedness and Structural Certificates (`Func.Wf`, Acyclicity, Arity) -/

public section

theorem kissat_emit_trivial_cnf_bytes_wf :
    Func.Wf kissat_emit_trivial_cnf_bytes_body := by
  t_wf_tac

theorem kissat_simplify_export_loaded_wf :
    Func.Wf kissat_simplify_export_loaded_body := by
  t_wf_tac

theorem kissat_simplify_export_bytes_wf :
    Func.Wf kissat_simplify_export_bytes_body := by
  t_wf_tac

/-- All three functions in `exportCnfEntry_fns` satisfy `Fn.Wf`. -/
theorem exportCnfEntry_fns_wf : ∀ f ∈ exportCnfEntry_fns, f.Wf := by
  intro f hf
  simp only [exportCnfEntry_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact kissat_emit_trivial_cnf_bytes_wf
  · exact kissat_simplify_export_loaded_wf
  · exact kissat_simplify_export_bytes_wf

/-- All twelve functions in `exportCnfEntryAllFns` satisfy `Fn.Wf`. -/
theorem exportCnfEntryAllFns_wf : ∀ f ∈ exportCnfEntryAllFns, f.Wf := by
  intro f hf
  rw [exportCnfEntryAllFns, List.mem_append] at hf
  exact hf.elim (exportCnfStateAllFns_wf f) (exportCnfEntry_fns_wf f)

/-- Acyclicity certificate for `exportCnfEntryMod`. -/
theorem exportCnfEntryMod_checkAcyclic :
    exportCnfEntryMod.checkAcyclic = true := by
  decide

/-- Unique function-name certificate for `exportCnfEntryMod`. -/
theorem exportCnfEntryMod_namesNodup : exportCnfEntryMod.namesNodup := by
  simp only [Module.namesNodup, Module.names, exportCnfEntryMod,
    exportCnfEntryAllFns, exportCnfStateAllFns, exportCnfFmt_fns,
    exportCnfState_fns, exportCnfEntry_fns]
  decide

/-- Every function in `exportCnfEntryAllFns` takes at most 6 scalar arguments
(x64 & Arm64 SysV ABI). -/
theorem exportCnfEntryAllFns_max6args :
    ∀ f ∈ exportCnfEntryAllFns, f.as.length ≤ 6 := by
  intro f hf
  simp only [exportCnfEntryAllFns, exportCnfStateAllFns, exportCnfFmt_fns,
    exportCnfState_fns, exportCnfEntry_fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

end

end LeanQbe.T.Examples.Kissat.ExportCnfEntry
