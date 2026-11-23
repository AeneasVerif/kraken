module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M5 Probing Literal Propagation (`FullM5ProbeProp`)

Drop-in override for `Full3.lean` `full_probe_prop_lit`:
1. Checks `vals[w0 & PW_LIT_MASK] > 0` before branching on `(w0 & PW_BIN_FLAG) != 0u`.
2. Tracks local probing ticks (`1 + ((sz + 31) >> 5)` plus binary/large/replacement/assignment
   increments) without polluting `h->search_ticks`, preserving byte-identical `FullHdr` and exact
   canonical `Full.fullProbePropLitSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5ProbeProp

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5ProbeProp "
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
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern u64 full_find_repl(FullHdr *h, u64 cref);
extern u32 full_hbr_dom(FullHdr *h, u32 cref, u32 implied);

bool full_probe_prop_lit_m5(FullHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u; u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u32 *hstk = (u32 *)h->work_stk2;
  u64 off = (u64)wvec[(u64)not_lit << 1]; u64 sz = (u64)wvec[((u64)not_lit << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u64 ticks = 1ULL + ((sz + 31ULL) >> 5);
  u64 p = off; u64 q = off; u64 end = off + sz; bool confl = false;
  u32 bin_rsn = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      if ((w0 & PW_BIN_FLAG) != 0u) {
        wstk[q] = w0; q = q + 1ULL; continue;
      }
      if (p < end) {
        u32 cr = wstk[p]; p = p + 1ULL;
        wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL; continue;
      }
      break;
    }
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
      if ((u64)blk >= nlits) { continue; }
      if (vals[blk] < (i8)0) {
        h->confl_type = 1ULL; h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)blk; confl = true; break;
      }
      ticks = ticks + 1ULL;
      full_assign_lvl(h, blk, bin_rsn, 1u);
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL;
    if ((u64)cr + 3ULL > h->arena_len) { continue; }
    ticks = ticks + 1ULL;
    u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u || (u64)cr + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    u32 l0 = ar[(u64)cr + 3ULL]; u32 l1 = ar[(u64)cr + 4ULL];
    if (l0 == not_lit) { ar[(u64)cr + 3ULL] = l1; ar[(u64)cr + 4ULL] = not_lit; l0 = l1; }
    else if (l1 != not_lit) { continue; }
    if ((u64)l0 >= nlits) { continue; }
    i8 ov = vals[l0];
    if (ov > (i8)0) { wstk[q] = l0 & PW_LIT_MASK; wstk[q + 1ULL] = cr; q = q + 2ULL; continue; }
    u64 ri = full_find_repl(h, (u64)cr);
    if (ri != 0xFFFFFFFFULL) {
      ticks = ticks + 1ULL;
      u32 repl = ar[(u64)cr + 3ULL + ri];
      ar[(u64)cr + 4ULL] = repl; ar[(u64)cr + 3ULL + ri] = not_lit;
      u64 pr = p - off; u64 qr = q - off; u64 er = end - off;
      bool pok = full_watch_push(h, repl, l0 & PW_LIT_MASK, cr, 2u);
      off = (u64)wvec[(u64)not_lit << 1]; p = off + pr; q = off + qr; end = off + er;
      if (!pok) {
        ar[(u64)cr + 4ULL] = not_lit; ar[(u64)cr + 3ULL + ri] = repl;
        wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL; h->oom = 1ULL; confl = true; break;
      }
      continue;
    }
    wstk[q] = l0 & PW_LIT_MASK; wstk[q + 1ULL] = cr; q = q + 2ULL;
    if (ov < (i8)0) { h->confl_type = 2ULL; h->confl_ref = (u64)cr; confl = true; break; }
    ticks = ticks + 1ULL;
    u32 dom = full_hbr_dom(h, cr, l0);
    if (dom != 0xFFFFFFFFu && h->tmp_cnt < h->cur_vars) {
      u64 hn = h->tmp_cnt; hstk[hn << 1] = dom ^ 1u; hstk[(hn << 1) + 1ULL] = l0;
      h->tmp_cnt = hn + 1ULL;
    }
    full_assign_lvl(h, l0, cr, 1u);
  }
  while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  return !confl;
}
"

/-- External callee signatures referenced by `m5ProbeProp_fns`. -/
def m5ProbePropExterns : List Extern :=
  [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_find_repl", [i64, i64], [i64]⟩
  , ⟨"full_hbr_dom", [i64, i32, i32], [i32]⟩
  ]

def m5ProbePropModule : LeanQbe.T.Module :=
  { fns := m5ProbeProp_fns, externs := m5ProbePropExterns, exits := [] }

theorem full_probe_prop_lit_m5_wf : Func.Wf full_probe_prop_lit_m5_body := by t_wf_reify

theorem m5ProbeProp_fns_wf : ∀ f ∈ m5ProbeProp_fns, f.Wf := by
  simp only [m5ProbeProp_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact full_probe_prop_lit_m5_wf

theorem m5ProbeProp_acyclic : m5ProbePropModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5ProbeProp
