module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `D-Full` M7 Purely Additive Compaction Fix (`FullM7CompactFix`)

Additive drop-in C0 replacements over unchanged `FullHdr` fixing confirmed `P0-2` compaction
bugs for `FullM7` without modifying `FullM4Compact*` or `FullM6CompactFlush*`:

1. `full_compact_needed_m7fix`: upstream `1%` compaction trigger parity (`dead * 100ULL > cv`)
   with `cv >= 128ULL`, `cur_level == 0`, `dense_mode == 0` (matching
   `FullM4Compact.fullCompactNeededSpec`).
2. `full_compact_mark_live_m7fix`: prevents zombie resurrection of `!FL_ACTIVE` variables via
   retained `PH_RED` clauses or binary watches by gating binary and arena marking on
   `(fl[v] & FL_ACTIVE) != 0u` and skipping `PH_RED` clauses that reference any unassigned
   `!FL_ACTIVE` literal.
3. `full_compact_vars_m7fix`: preserves `fl[nv] = fl[ov]` instead of clearing
   `FL_ELIM | FL_SUBST` and forcing `| FL_ACTIVE`.
4. `full_sweep_copy_m7fix`: drops `PH_RED` clauses containing any `!FL_ACTIVE` variable
   during `full_arena_sweep` / `full_rebuild_watches` by returning `0xFFFFFFFFULL` (reading
   header `PH_RED` before the copy loop to avoid `dst`/`src` aliasing).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7CompactFix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7CompactFix "
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
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE   1u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 lvl);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 wcnt);

bool full_compact_needed_m7fix(FullHdr *h) {
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL) { return false; }
  u64 cv = h->cur_vars;
  if (cv < 128ULL || cv <= h->unassigned) { return false; }
  u64 dead = cv - h->unassigned;
  return (dead * 100ULL > cv);
}

void full_compact_mark_live_m7fix(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *map = (u32 *)h->work_stk1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 v = 0ULL;
  while (v < cv) {
    map[v] = 0u;
    v = v + 1ULL;
  }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    u32 lneg = ((u32)l) ^ 1u;
    u64 p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && ot != lneg &&
            vals[l] == (i8)0 && vals[ot] == (i8)0 &&
            (fl[l >> 1] & FL_ACTIVE) != 0u &&
            (fl[ot >> 1] & FL_ACTIVE) != 0u) {
          map[l >> 1] = 1u;
          map[ot >> 1] = 1u;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    l = l + 1ULL;
  }
  u64 alen = h->arena_len;
  u64 pos = 0ULL;
  while (pos < alen) {
    if (pos + 3ULL > alen) { break; }
    u32 hdr = ar[pos];
    u32 csz = ar[pos + 2ULL];
    u64 npos = (u64)full_arena_next(h, (u32)pos);
    if ((hdr & PH_GARB) == 0u && csz >= 3u && pos + 3ULL + (u64)csz <= alen) {
      bool sat = false;
      bool has_dead = false;
      u32 ucnt = 0u;
      u32 i = 0u;
      while (i < csz) {
        u32 lit = ar[pos + 3ULL + (u64)i];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) {
            if ((fl[lit >> 1] & FL_ACTIVE) == 0u) {
              has_dead = true;
            } else {
              ucnt = ucnt + 1u;
            }
          }
        }
        i = i + 1u;
      }
      if (!sat && !((hdr & PH_RED) != 0u && has_dead) && ucnt >= 1u) {
        i = 0u;
        while (i < csz) {
          u32 lit = ar[pos + 3ULL + (u64)i];
          if ((u64)lit < nlits && vals[lit] == (i8)0 &&
              (fl[lit >> 1] & FL_ACTIVE) != 0u) {
            map[lit >> 1] = 1u;
          }
          i = i + 1u;
        }
      }
    }
    pos = npos;
  }
}

void full_compact_vars_m7fix(FullHdr *h, u64 old_cv, u64 ncv) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *ps = (u32 *)h->pos;
  u32 *inv = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  u64 nlits = old_cv << 1;
  while (l < nlits) { vals[l] = (i8)0; l = l + 1ULL; }
  u64 tgt_asg = 0ULL;
  u64 bst_asg = 0ULL;
  u64 nv = 0ULL;
  while (nv < ncv) {
    u32 ov = inv[nv];
    fl[nv] = fl[ov];
    ph[nv] = ph[ov];
    i8 tv = ptgt[ov];
    i8 bv = pbst[ov];
    ptgt[nv] = tv;
    pbst[nv] = bv;
    if (tv != (i8)0) { tgt_asg = tgt_asg + 1ULL; }
    if (bv != (i8)0) { bst_asg = bst_asg + 1ULL; }
    wbst[nv] = wbst[ov];
    sc[nv] = sc[ov];
    qs[nv] = qs[ov];
    lvl[nv] = 0u;
    rsns[nv] = 0xFFFFFFFFu;
    nv = nv + 1ULL;
  }
  u64 v = ncv;
  while (v < old_cv) {
    fl[v] = 0u;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    sc[v] = 0ULL;
    qs[v] = 0u;
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    ps[v] = 0xFFFFFFFFu;
    v = v + 1ULL;
  }
  ftrl[0] = 0u;
  fdec[0] = 0xFFFFFFFFu;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  h->target_assigned = tgt_asg;
  h->best_assigned = bst_asg;
  h->cur_vars = ncv;
  h->unassigned = ncv;
  if (ncv < h->d.mv) { h->d.mv = ncv; h->bva_cap = h->max_vars - ncv; }
}

u64 full_sweep_copy_m7fix(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u64 cv = h->cur_vars;
  if (!at_root) {
    u32 i = 0u;
    while (i < old_sz) { ar[dst + 3ULL + (u64)i] = ar[src + 3ULL + (u64)i]; i = i + 1u; }
    return (u64)old_sz;
  }
  bool is_red = (ar[src] & PH_RED) != 0u;
  u32 new_sz = 0u;
  u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[src + 3ULL + (u64)i];
    u32 v = lit >> 1;
    if ((u64)v < cv && is_red && (fl[v] & FL_ACTIVE) == 0u) {
      return 0xFFFFFFFFULL;
    }
    if ((u64)v < cv && lvl[v] == 0u && vals[lit] != (i8)0) {
      if (vals[lit] > (i8)0) { return 0xFFFFFFFFULL; }
    } else {
      ar[dst + 3ULL + (u64)new_sz] = lit;
      new_sz = new_sz + 1u;
    }
    i = i + 1u;
  }
  if (new_sz == 0u) { return 0xFFFFFFFEULL; }
  if (new_sz == 1u) {
    u32 ulit = ar[dst + 3ULL];
    if (vals[ulit] < (i8)0) { return 0xFFFFFFFEULL; }
    if (vals[ulit] == (i8)0) { full_assign_lvl(h, ulit, 0xFFFFFFFFu, 0u); return 1ULL; }
    return 0xFFFFFFFFULL;
  }
  if (new_sz == 2u) {
    u32 l0 = ar[dst + 3ULL]; u32 l1 = ar[dst + 4ULL];
    u32 b0 = (l1 & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (l0 & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, l0, b0, 0u, 1u) || !full_watch_push(h, l1, b1, 0u, 1u)) {
      h->oom = 1ULL; return 0xFFFFFFFDULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFFULL;
  }
  return (u64)new_sz;
}
"

/-- External callee signatures referenced by `m7CompactFix_fns`. -/
def m7CompactFixExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩ ]

/-- Standalone M7 compaction & sweep fix module (`4` functions + `3` externs, `0` exits). -/
def m7CompactFixModule : LeanQbe.T.Module :=
  { fns := m7CompactFix_fns, externs := m7CompactFixExterns, exits := [] }

/-- Drop-in renamed `Fn` handles matching canonical `FullM4Compact` / `Full1` splice slots. -/
def m7fixCompactNeededFn : Fn :=
  ⟨"full_compact_needed", [i64], [.bool], full_compact_needed_m7fix_body⟩

def m7fixCompactMarkLiveFn : Fn :=
  ⟨"full_compact_mark_live", [i64], [], full_compact_mark_live_m7fix_body⟩

def m7fixCompactVarsFn : Fn :=
  ⟨"full_compact_vars", [i64, i64, i64], [], full_compact_vars_m7fix_body⟩

def m7fixSweepCopyFn : Fn :=
  ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], full_sweep_copy_m7fix_body⟩

theorem full_compact_needed_m7fix_wf : Func.Wf full_compact_needed_m7fix_body := by t_wf_reify
theorem full_compact_mark_live_m7fix_wf : Func.Wf full_compact_mark_live_m7fix_body := by
  t_wf_reify
theorem full_compact_vars_m7fix_wf : Func.Wf full_compact_vars_m7fix_body := by t_wf_reify
theorem full_sweep_copy_m7fix_wf : Func.Wf full_sweep_copy_m7fix_body := by t_wf_reify

theorem m7CompactFix_fns_wf : ∀ f ∈ m7CompactFix_fns, f.Wf := by
  simp only [m7CompactFix_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_compact_needed_m7fix_wf, full_compact_mark_live_m7fix_wf,
    full_compact_vars_m7fix_wf, full_sweep_copy_m7fix_wf⟩

theorem m7CompactFix_acyclic : m7CompactFixModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7CompactFix
