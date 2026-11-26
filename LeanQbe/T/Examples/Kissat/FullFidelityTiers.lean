/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM6Hdr
public import LeanQbe.T.Examples.Kissat.FullFidelityBase
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0
public meta import LeanQbe.T.Examples.Kissat.FullM6Hdr
public meta import LeanQbe.T.Examples.Kissat.FullFidelityBase
public meta import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Upstream 4.0.4 Tier & Glue-Promotion Parity (`FullFidelityTiers`)

Purely additive Gate-1 parity module fixing Defect #2 (`StreamReader_13` & `posixpath_13`
tier/glue parity vs upstream Kissat 4.0.4) with zero edits to existing `.lean` files:

1. **Fix 2a (`m6_hdr_sync_legacy_tiers`, upstream `internal.h:250-257` where `TIEDX` is `#if 0`):**
   - `FullM7ParityVivTiers` mistakenly synced `h->tier2` from `e[M6W_TIER2]` (`tier2[0]`,
     focused) instead of `e[M6W_TIER2 + 1ULL]` (`tier2[1]`, stable).
   - `fidSyncLegacyTiersFn` re-exports `FullM6Hdr.m6_hdr_sync_legacy_tiers_body`, which already
     reads `e[M6W_TIER2 + 1ULL]`, reusing `FullM6Hdr.m6_hdr_sync_legacy_tiers_wf` directly.
2. **Fix 2b (`full_analyze_rsn_m6_hdr`, upstream `deduce.c:6-27` & `promote.h:8-20`):**
   - `FullM6Orch` artificially capped `recompute_glue` via `if (lim > h->tier2) { lim = h->tier2; }`
     and `if (lim > 32ULL) { lim = 32ULL; }`, aborting glue promotions whenever `new_glue > tier2`
     and polluting `m6_hdr_record_used`.
   - `fidAnalyzeRsnFn` (`fidAnalyzeRsnBody`) removes both caps so `u64 lim = glue - 1ULL;` runs
     uncapped (`glue = hdr & PH_GLUE_MASK < 2^19`, so `lim.toNat + 1 < 2^64`).
3. **Exports:**
   - `fidTiersRepls`, `fidTiersStandModule` (`2` repls + `3` externs, `0` exits), `fidTiersFns`,
     and `fidTiersModule` (`469` fns patched over `FullFidelityBase.fidBaseModule`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTiers

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Fix 2b C0 Implementation (`full_analyze_rsn_m6_hdr_fid`) -/

kissat_c0! fidTiers "
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

#define PH_GLUE_MASK          0x7FFFFu
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

extern bool full_analyze_lit(FullHdr *h, u32 l, u32 skip_var);
extern void m6_hdr_record_used(FullHdr *h, u64 glue);

bool full_analyze_rsn_m6_hdr_fid(FullHdr *h, u32 rsn, u32 skip_var) {
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
    m6_hdr_record_used(h, glue);
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

/-! ## 2. Canonical Handles, Replacement List, and Spliced Modules -/

/-- Canonical uncapped `full_analyze_rsn_m6_hdr` C0 body (`Fix 2b`). -/
abbrev fidAnalyzeRsnBody : Func [i64, i32, i32] [.bool] :=
  full_analyze_rsn_m6_hdr_fid_body

/-- Fix 2a `Fn` handle reusing `FullM6Hdr.m6_hdr_sync_legacy_tiers_body` (`tier2[1]`, stable). -/
def fidSyncLegacyTiersFn : Fn :=
  ⟨"m6_hdr_sync_legacy_tiers", [i64], [], FullM6Hdr.m6_hdr_sync_legacy_tiers_body⟩

/-- Fix 2b `Fn` handle exporting uncapped `full_analyze_rsn_m6_hdr`. -/
def fidAnalyzeRsnFn : Fn :=
  ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], full_analyze_rsn_m6_hdr_fid_body⟩

/-- Canonical `2`-function Gate-1 tier/glue parity replacement list. -/
def fidTiersRepls : List Fn :=
  [fidSyncLegacyTiersFn, fidAnalyzeRsnFn]

/-- External callees referenced by `fidTiersRepls` (`3` externs). -/
def fidTiersStandExterns : List Extern :=
  [ ⟨"m6_ext_ensure_init", [i64], []⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool]⟩
  , ⟨"m6_hdr_record_used", [i64, i64], []⟩ ]

/-- Standalone Gate-1 tier/glue parity module (`2` functions + `3` externs, `0` exits). -/
def fidTiersStandModule : LeanQbe.T.Module :=
  { fns := fidTiersRepls, externs := fidTiersStandExterns, exits := [] }

/-- Ordered `469`-function solver list splicing `fidTiersRepls` onto `fidBaseFns`. -/
def fidTiersFns : List Fn :=
  PatchModule.patchFns fidTiersRepls [] fidBaseFns

/-- Closed `469`-function `KissatFidelity` + Tier/Glue parity module (`0` externs, `0` exits). -/
def fidTiersModule : LeanQbe.T.Module :=
  PatchModule.patchModule fidBaseModule fidTiersRepls []

theorem fidSyncLegacyTiers_wf : Func.Wf FullM6Hdr.m6_hdr_sync_legacy_tiers_body :=
  FullM6Hdr.m6_hdr_sync_legacy_tiers_wf

theorem full_analyze_rsn_m6_hdr_fid_wf : Func.Wf full_analyze_rsn_m6_hdr_fid_body := by
  t_wf_reify

theorem fidTiersRepls_wf : ∀ r ∈ fidTiersRepls, r.Wf := by
  intro r hr
  simp only [fidTiersRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fidSyncLegacyTiers_wf
  · exact full_analyze_rsn_m6_hdr_fid_wf

theorem fidTiersStand_acyclic : fidTiersStandModule.checkAcyclic = true := by
  t_kernel_rfl

theorem fidTiers_noExit : fidTiersModule.exits = [] := by
  dsimp only [fidTiersModule, PatchModule.patchModule]
  exact fidBase_noExit

/-! ## 3. Standalone Codegen & 4-ISA Legalization Guards -/

#guard fidTiersRepls.length == 2
#guard fidTiersStandModule.checkAcyclic == true
#guard fidTiersFns.length == 469
#guard (fidTiersFns.map Fn.name).eraseDups.length == 469
#guard fidTiersModule.checkAcyclic == true
#guard fidTiersModule.externs.isEmpty == true
#guard fidTiersModule.exits.isEmpty == true

end LeanQbe.T.Examples.Kissat.FullFidelityTiers
