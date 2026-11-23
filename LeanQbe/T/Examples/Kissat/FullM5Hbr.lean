module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M5 Budgeted Hyper-Binary Resolution (`FullM5Hbr`)

Drop-in M5 replacement `full_hbr_dom_m5` for `full_hbr_dom` with a local `steps < 128`
trail-walk expansion budget (`0` `FullHdr` changes, `0` borrowed fields). Only marked level-1
node expansions increment `steps` (non-marked or non-level-1 trail entries skip before
incrementing `steps`). On budget exhaustion, `dom` remains `0xFFFFFFFFu` while the `min_clr`
mark-clear loop still runs to preserve `FullMrkZero`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Hbr

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5Hbr "
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

u32 full_hbr_dom_m5(FullHdr *h, u32 cref, u32 implied) {
  u32 *ar = (u32 *)h->arena; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *clr = (u32 *)h->min_clr;
  u64 cv = h->cur_vars; u32 sz = ar[(u64)cref + 2ULL];
  u64 clen = 0ULL; u64 open = 0ULL; u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u32 v = l >> 1;
    if (l != implied && (u64)v < cv && lvl[v] == 1u && mrk[v] == (u8)0) {
      mrk[v] = (u8)1; clr[clen] = v; clen = clen + 1ULL; open = open + 1ULL;
    }
    i = i + 1u;
  }
  u32 dom = 0xFFFFFFFFu;
  if (open >= 2ULL) {
    u64 idx = h->trail_end;
    u64 steps = 0ULL;
    while (open > 0ULL && idx > 0ULL && steps < 128ULL) {
      idx = idx - 1ULL;
      u32 p = trl[idx]; u32 pv = p >> 1;
      if ((u64)pv >= cv || lvl[pv] != 1u || mrk[pv] == (u8)0) { continue; }
      steps = steps + 1ULL;
      open = open - 1ULL;
      if (open == 0ULL) { dom = p; break; }
      u32 rsn = rsns[pv];
      if (rsn == 0xFFFFFFFFu) { break; }
      if ((rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] == 1u && mrk[ov] == (u8)0 && clen < cv) {
          mrk[ov] = (u8)1; clr[clen] = ov; clen = clen + 1ULL; open = open + 1ULL;
        }
      } else if ((u64)rsn + 3ULL <= h->arena_len) {
        u32 rsz = ar[(u64)rsn + 2ULL]; u32 j = 0u;
        while (j < rsz && (u64)rsn + 3ULL + (u64)rsz <= h->arena_len) {
          u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
          if (ov != pv && (u64)ov < cv && lvl[ov] == 1u && mrk[ov] == (u8)0 && clen < cv) {
            mrk[ov] = (u8)1; clr[clen] = ov; clen = clen + 1ULL; open = open + 1ULL;
          }
          j = j + 1u;
        }
      }
    }
  }
  u64 k = 0ULL;
  while (k < clen) { mrk[clr[k]] = (u8)0; k = k + 1ULL; }
  return dom;
}
"

/-- Closed standalone `LeanQbe.T.Module` for M5 budgeted HBR (`1` fn, `0` externs, `0` exits). -/
def m5HbrModule : LeanQbe.T.Module :=
  { fns := m5Hbr_fns, externs := [], exits := [] }

theorem full_hbr_dom_m5_wf : Func.Wf full_hbr_dom_m5_body := by t_wf_reify

theorem m5Hbr_fns_wf : ∀ f ∈ m5Hbr_fns, f.Wf := by
  simp only [m5Hbr_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact full_hbr_dom_m5_wf

theorem m5Hbr_acyclic : m5HbrModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5Hbr
