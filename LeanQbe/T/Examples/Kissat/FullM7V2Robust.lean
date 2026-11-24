module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat `M7` v2 Robustness Splice Candidates (`FullM7V2Robust`)

Additive C0 anti-`UNKNOWN` (`r = 0`) splice candidates for the unified `M7` v2 base. Every
replacement keeps the name and signature of the function it replaces, applies unchanged to BOTH
`FullM7Fidelity.m7FidelityFns` and `FullM7Plus.m7PlusFns` (the replaced bodies are identical in
the two bases), touches no restart / rephase / mode / probe / eliminate scheduling code, adds no
`FullHdr` / `M6HdrExt` state, and is inert unless the solver has just run out of arena or
watch-stack space. No existing file is edited and no certificate slice is generated here.

## Learn-time OOM-retry ladder

* `full_add_clause`, `full_sweep_copy` — *atomic failure*: a failed add leaves no half binary
  (`full_watch_pop_c0` rolls the first watch back), no dangling large watch, and no dead arena
  words (`arena_len` is rolled back), so the caller can garbage-collect and retry.
* `full_learn_clause` — when `full_add_clause` fails (previously an immediate `return 0`), retry
  after (1) watch-stack defrag, (2) the regular forced `full_reduce(h, true)`, (3) the emergency
  purge `full_reduce_purge_c0`, which collects ALL non-reason redundant clauses. The pre-existing
  headroom pre-check is kept verbatim.

The solver's execution is unchanged up to the first failed `full_add_clause` in
`full_learn_clause`, i.e. up to a point where the base solver returns `0`. Hence every run the
base decides is reproduced bit-for-bit (same verdict, same telemetry), and only base-`UNKNOWN`
runs can change.

`patchFns` is an exposed copy of `FullM7Splice.patchFns`, so `checkAcyclic` of a patched module
reduces in the kernel.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7V2Robust

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

/-! ## 1. Candidate Functions -/

kissat_c0! v2Robust "
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

#define PH_RSN       0x00200000u
#define PW_BIN_FLAG  0x80000000u
#define PW_LIT_MASK  0x7FFFFFFFu
#define FL_ACTIVE    1u
#define PH_RED       0x00400000u
#define PH_GARB      0x00080000u

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern void full_mark_reasons(FullHdr *h, bool set_flag);
extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_det_new_level(FullHdr *h, u64 jump);
extern void full_wstack_defrag(FullHdr *h);
extern u64 full_reduce(FullHdr *h, bool force);
extern void full_eager_subsume(FullHdr *h, u64 new_ref);

void full_watch_pop_c0(FullHdr *h, u32 lit, u32 cnt) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 c = (u64)cnt;
  if (c == 0ULL || sz < c || off + sz > h->wlen) { return; }
  u64 k = sz - c;
  while (k < sz) { wstk[off + k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)lit << 1) + 1ULL] = (u32)(sz - c);
  h->wusable = h->wusable + c;
}

u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red) {
  u32 *tmp = (u32 *)h->tmp_lits;
  if (len == 2u) {
    u32 b0 = (tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG;
    u32 b1 = (tmp[0] & PW_LIT_MASK) | PW_BIN_FLAG;
    if (!full_watch_push(h, tmp[0], b0, 0u, 1u)) { return 0xFFFFFFFFULL; }
    if (!full_watch_push(h, tmp[1], b1, 0u, 1u)) {
      full_watch_pop_c0(h, tmp[0], 1u);
      return 0xFFFFFFFFULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFEULL;
  }
  if (len < 3u) { return 0xFFFFFFFFULL; }
  u64 cref = full_alloc_cl(h, len, glue, red);
  if (cref == 0xFFFFFFFFULL) { return 0xFFFFFFFFULL; }
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < len) { ar[cref + 3ULL + (u64)i] = tmp[i]; i = i + 1u; }
  if (!full_watch_push(h, tmp[0], tmp[1] & PW_LIT_MASK, (u32)cref, 2u)) {
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (!full_watch_push(h, tmp[1], tmp[0] & PW_LIT_MASK, (u32)cref, 2u)) {
    full_watch_pop_c0(h, tmp[0], 2u);
    h->arena_len = cref;
    return 0xFFFFFFFFULL;
  }
  if (red) {
    h->num_redundant = h->num_redundant + 1ULL;
    if (h->first_reducible == 0xFFFFFFFFULL) { h->first_reducible = cref; }
  } else {
    h->num_irred = h->num_irred + 1ULL;
  }
  return cref;
}

u64 full_sweep_copy(FullHdr *h, u64 src, u64 dst, u32 old_sz, bool at_root) {
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
    if (!full_watch_push(h, l0, b0, 0u, 1u)) { h->oom = 1ULL; return 0xFFFFFFFDULL; }
    if (!full_watch_push(h, l1, b1, 0u, 1u)) {
      full_watch_pop_c0(h, l0, 1u);
      h->oom = 1ULL; return 0xFFFFFFFDULL;
    }
    h->num_binary = h->num_binary + 1ULL;
    return 0xFFFFFFFFULL;
  }
  return (u64)new_sz;
}

u64 full_reduce_purge_c0(FullHdr *h) {
  if (h->unflushed > 0ULL) {
    if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  full_mark_reasons(h, true);
  u32 *ar = (u32 *)h->arena;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 n = full_arena_next(h, (u32)p);
    if (p + 3ULL <= h->arena_len && (hdr & PH_RED) != 0u &&
        (hdr & (PH_GARB | PH_RSN)) == 0u) {
      ar[p] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[p + 2ULL];
    }
    if ((u64)n <= p) { break; }
    p = (u64)n;
  }
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (sr == 0ULL) { break; }
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { return 20ULL; }
    if (pr != 0ULL) { return 0ULL; }
    h->unflushed = 0ULL;
  }
  return 1ULL;
}

u64 full_learn_clause(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    full_backtrack(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    return 1ULL;
  }
  u64 max_idx = h->tmp_len - 1ULL;
  u64 max_lvl = (u64)lvl[tmp[max_idx] >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u32 w1 = tmp[1]; tmp[1] = tmp[max_idx]; tmp[max_idx] = w1;
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  u64 step = 0ULL;
  while (new_ref == 0xFFFFFFFFULL && step < 3ULL) {
    if (step == 0ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    } else {
      u64 gr = (step == 1ULL) ? full_reduce(h, true) : full_reduce_purge_c0(h);
      if (gr == 20ULL) { return 20ULL; }
      if (gr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
    new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
    step = step + 1ULL;
  }
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}
"

/-- External callee signatures referenced by `v2Robust_fns` (`12` externs). -/
def v2RobustExterns : List Extern :=
  [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_mark_reasons", [i64, .bool], []⟩
  , ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_arena_sweep", [i64], [i64]⟩
  , ⟨"full_det_new_level", [i64, i64], [i64]⟩
  , ⟨"full_wstack_defrag", [i64], []⟩
  , ⟨"full_reduce", [i64, .bool], [i64]⟩
  , ⟨"full_eager_subsume", [i64, i64], []⟩ ]

/-- Standalone candidate module (`5` functions, `0` exits). -/
def v2RobustModule : LeanQbe.T.Module :=
  { fns := v2Robust_fns, externs := v2RobustExterns, exits := [] }

/-! ## 2. `Fn` Handles & Well-Formedness -/

def v2rWatchPopFn : Fn :=
  ⟨"full_watch_pop_c0", [i64, i32, i32], [], full_watch_pop_c0_body⟩
def v2rAddClauseFn : Fn :=
  ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], full_add_clause_body⟩
def v2rSweepCopyFn : Fn :=
  ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], full_sweep_copy_body⟩
def v2rReducePurgeFn : Fn :=
  ⟨"full_reduce_purge_c0", [i64], [i64], full_reduce_purge_c0_body⟩
def v2rLearnClauseFn : Fn :=
  ⟨"full_learn_clause", [i64, i64], [i64], full_learn_clause_body⟩

theorem full_watch_pop_c0_wf : Func.Wf full_watch_pop_c0_body := by t_wf_reify
theorem full_add_clause_wf : Func.Wf full_add_clause_body := by t_wf_reify
theorem full_sweep_copy_wf : Func.Wf full_sweep_copy_body := by t_wf_reify
theorem full_reduce_purge_c0_wf : Func.Wf full_reduce_purge_c0_body := by t_wf_reify
theorem full_learn_clause_wf : Func.Wf full_learn_clause_body := by t_wf_reify

theorem v2Robust_fns_wf : ∀ f ∈ v2Robust_fns, f.Wf := by
  simp only [v2Robust_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_watch_pop_c0_wf,
    full_add_clause_wf,
    full_sweep_copy_wf,
    full_reduce_purge_c0_wf,
    full_learn_clause_wf⟩

theorem v2Robust_acyclic : v2RobustModule.checkAcyclic = true := by
  t_kernel_rfl

/-! ## 3. Splice Lists -/

/-- Canonical replacements (same name and signature as the replaced base function). -/
def v2RobustRepls : List Fn :=
  [ v2rAddClauseFn, v2rSweepCopyFn, v2rLearnClauseFn ]

/-- Helpers inserted immediately before their first caller. -/
def v2RobustBefores : List (Sym × List Fn) :=
  [ ("full_add_clause", [v2rWatchPopFn])
  , ("full_learn_clause", [v2rReducePurgeFn]) ]

/-- Helper functions queued immediately before `f.name` from `(anchor, hs) ∈ befores`. -/
def patchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  (befores.filterMap fun (a, hs) => if a == f.name then some hs else none).flatten

/-- Replace functions matching `repls` by name and insert the queued helpers `befores`
immediately before each anchor (exposed copy of `FullM7Splice.patchFns`). -/
def patchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

private theorem mem_patchInsAt {befores : List (Sym × List Fn)} {g fn : Fn}
    (h : fn ∈ patchInsAt befores g) : ∃ hs, (g.name, hs) ∈ befores ∧ fn ∈ hs := by
  unfold patchInsAt at h
  rcases List.mem_flatten.mp h with ⟨hs, hhs, hfn⟩
  rcases List.mem_filterMap.mp hhs with ⟨⟨a, hs0⟩, hm, hif⟩
  cases hcmp : (a == g.name)
  · simp [hcmp] at hif
  · have ha : a = g.name := beq_iff_eq.mp hcmp
    subst ha
    simp at hif
    subst hif
    exact ⟨hs0, hm, hfn⟩

theorem patchFns_wf {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf)
    (hi : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf) :
    ∀ f ∈ patchFns repls befores fs, f.Wf := by
  intro fn hfn
  rcases List.mem_flatMap.mp hfn with ⟨g, hg, hmem⟩
  rcases List.mem_append.mp hmem with h_ins | h_rep
  · rcases mem_patchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hi (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | none => exact hfs g hg
    | some r => exact hr r (List.mem_of_find?_eq_some h)

/-- Every base function whose name is not replaced is carried over unchanged, so its existing
specification row and `Func.wp` proof remain applicable verbatim. -/
theorem patchFns_mem_of_ne {repls fs : List Fn} {befores : List (Sym × List Fn)} {g : Fn}
    (hg : g ∈ fs) (hne : ∀ r ∈ repls, r.name ≠ g.name) : g ∈ patchFns repls befores fs := by
  refine List.mem_flatMap.mpr ⟨g, hg, List.mem_append_right _ ?_⟩
  have hnone : repls.find? (fun x => x.name == g.name) = none := by
    rw [List.find?_eq_none]
    intro r hr
    simpa using hne r hr
  simp [hnone]

/-- `FullM7Fidelity` + OOM-retry ladder (`415` functions). -/
def m7FidV2RobustFns : List Fn :=
  patchFns v2RobustRepls v2RobustBefores FullM7Fidelity.m7FidelityFns

/-- `FullM7Plus` + OOM-retry ladder (`412` functions). -/
def m7PlusV2RobustFns : List Fn :=
  patchFns v2RobustRepls v2RobustBefores FullM7Plus.m7PlusFns

def m7FidV2RobustModule : LeanQbe.T.Module :=
  { fns := m7FidV2RobustFns, externs := [], exits := [] }

def m7PlusV2RobustModule : LeanQbe.T.Module :=
  { fns := m7PlusV2RobustFns, externs := [], exits := [] }

theorem v2RobustRepls_wf : ∀ r ∈ v2RobustRepls, r.Wf := by
  simp only [v2RobustRepls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_add_clause_wf, full_sweep_copy_wf, full_learn_clause_wf⟩

theorem v2RobustBefores_wf : ∀ p ∈ v2RobustBefores, ∀ h ∈ p.2, h.Wf := by
  simp only [v2RobustBefores, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨full_watch_pop_c0_wf, full_reduce_purge_c0_wf⟩

theorem m7FidV2RobustFns_wf : ∀ f ∈ m7FidV2RobustFns, f.Wf :=
  patchFns_wf FullM7Fidelity.m7FidelityFns_wf v2RobustRepls_wf v2RobustBefores_wf

theorem m7PlusV2RobustFns_wf : ∀ f ∈ m7PlusV2RobustFns, f.Wf :=
  patchFns_wf FullM7Plus.m7PlusFns_wf v2RobustRepls_wf v2RobustBefores_wf

theorem m7FidV2RobustFns_length : m7FidV2RobustFns.length = 415 := by
  t_kernel_rfl

theorem m7PlusV2RobustFns_length : m7PlusV2RobustFns.length = 412 := by
  t_kernel_rfl

theorem m7FidV2Robust_acyclic : m7FidV2RobustModule.checkAcyclic = true := by
  t_kernel_rfl

theorem m7PlusV2Robust_acyclic : m7PlusV2RobustModule.checkAcyclic = true := by
  t_kernel_rfl

theorem m7FidV2Robust_noExit : m7FidV2RobustModule.exits = [] := rfl

theorem m7PlusV2Robust_noExit : m7PlusV2RobustModule.exits = [] := rfl

/-! ## 4. Compile-Time `#guard` Verification (ABI, PrintCpp, PrintQbe, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

private def fidNames : List Sym := FullM7Fidelity.m7FidelityFns.map Fn.name
private def plusNames : List Sym := FullM7Plus.m7PlusFns.map Fn.name

#guard v2RobustModule.checkAcyclic
#guard m7FidV2RobustFns.length == 415 && m7PlusV2RobustFns.length == 412
#guard (m7FidV2RobustFns.map Fn.name).eraseDups.length == 415
#guard (m7PlusV2RobustFns.map Fn.name).eraseDups.length == 412
#guard m7FidV2RobustModule.checkAcyclic && m7PlusV2RobustModule.checkAcyclic
#guard m7FidV2RobustModule.externs.isEmpty && m7PlusV2RobustModule.externs.isEmpty

-- ABI: only the helpers are new names, the base name order is preserved, and every replacement
-- keeps the exact signature of the function it replaces in BOTH bases.
#guard (m7FidV2RobustFns.map Fn.name).filter (fun n => !fidNames.contains n) ==
  ["full_watch_pop_c0", "full_reduce_purge_c0"]
#guard (m7PlusV2RobustFns.map Fn.name).filter (fun n => !plusNames.contains n) ==
  ["full_watch_pop_c0", "full_reduce_purge_c0"]
#guard (m7FidV2RobustFns.map Fn.name).filter fidNames.contains == fidNames
#guard (m7PlusV2RobustFns.map Fn.name).filter plusNames.contains == plusNames
#guard v2RobustRepls.all fun r =>
  (FullM7Fidelity.m7FidelityFns.find? (·.name == r.name)).map Fn.sig == some r.sig
#guard v2RobustRepls.all fun r =>
  (FullM7Plus.m7PlusFns.find? (·.name == r.name)).map Fn.sig == some r.sig
#guard (v2RobustRepls.map Fn.name).eraseDups.length == 3

#guard (ppTModule m7FidV2RobustModule).isOk
#guard (PrintQbe.module m7FidV2RobustModule).isOk
#guard (ppTModule m7PlusV2RobustModule).isOk
#guard (PrintQbe.module m7PlusV2RobustModule).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .x64AVX2))).isOk
#guard v2Robust_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard v2Robust_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard v2Robust_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard v2Robust_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM7V2Robust
