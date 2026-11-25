/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Inline
public import LeanQbe.T.MainInline
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-!
# Profile-Guided Inline Policy for Kissat Fidelity (`FullFidelityInlPolicy`)

Extends `FullM7InlPolicy.m7PgoBudget` with budgets tuned on the purified `469`-function
`KissatFidelity` solver spine (strictly `0` `M8Opt` / `XorGauss` / `Prelearn` / `WaveACore` /
`SbvaTie` symbols):
* Fixes the underbudgeted PGO entries where post-inlining IR grew past the `m7`/`m8` threshold
  (`full_cong_find => 52`, `full_sort_u32 => 162`, `m6_hdr_bump_delay => 82`,
  `full_sort_tmp_heap_m7 => 215` covering `2 * full_sort_tmp_sift_m7`, `full_m6_max_v => 32`,
  `full_shrink_lower_m8 => 165` covering `2 * full_min_mark`).
* Covers unlisted hot leaves and Fidelity helpers (`full_bva_match_large_fid`,
  `full_reorder_sift_fid`, `full_assign_lvl`, `full_assign`, `full_min_mark`,
  `full_cong_enq_var`, `full_extend_push2`, `full_cong_unit_fold`, `full_cong_mark_trail`,
  `full_add_unit`, `full_bump_var`, `full_m6_dense_prop`, `full_elim_dticks`, `full_otfs_subsume`,
  `m6_hdr_{delaying,reduce_delay,dr_init,sync_legacy_tiers,decide_fid}`, `m6_ext_ensure_init`,
  `full_k6_*`, `full_k6_*_m8`, `full_bve_{match_tern,def_k6}_m8`, `full_k512_flip`,
  `full_k6_flip`, `full_m6_sweep_{rearm,refine_sig,rand_phases,solve}`, `full_queue_mtf`,
  `full_cong_eb_match`, `full_sweep_copy`, and `full_analyze_rsn_m6_hdr`).
* Keeps cold initialization loop `m6_hdr_init` out-of-line (`budget := 0` and `"m6_hdr_init"` in
  `keepOutOfLine`), avoiding `+16.6 KB` cold `.text` bloat in `full_probe_m6` and preserving tight
  `m6_hdr_*` helper budgets.
* Retains explicit `full_backtrack => 64` (actual post-inline IR `208` stays OOL because inlining
  it exposes `3 * full_backtrack_raw_m5` and expands call count `+128`).
* Tunes `maxCallerSize := 4000`, `leafMax := 165`, `maxCalleeLoops := some 1`,
  `maxTotalDup := 1500`, `maxCallerCalls := 24` so hot drivers (`full_cong_eval_gate`,
  `full_reorder_queue_m7`, `full_bve_def_k6_m7`, `full_bva_filter_row`, `full_deduce_1uip_m6_hdr`)
  inline hot leaves without exceeding `~3.5k` IR nodes (`maxFnSize = 2792` on purified `469`-fn
  module; `469/469` functions lower cleanly on both `x86-64` and `AArch64`).

All `Module.optInlinePolicy_*` correctness, `Func.Wf`, acyclicity, and `LegalTarget` transport
theorems apply directly with `0` compiler proof LOC.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-- Per-callee PGO inline budget for `KissatFidelity`, delegating remaining symbols to
`m7PgoBudget` (`0` `M8Opt`/`XorGauss`/`Prelearn`/`WaveACore`/`SbvaTie` symbols). -/
def fidPgoBudget : Sym → Nat
  -- Fidelity `FullM8CoreParity` (`K6` kitten-core, `BVE` gate, minimize/shrink)
  | "full_k6_watch_m8" => 63
  | "full_k6_assign_m8" => 87
  | "full_k6_mtf_m8" => 110
  | "full_k6_backtrack_m8" => 96
  | "full_shrink_lower_m8" => 165
  | "full_bve_match_tern_m8" => 115
  | "full_bve_def_k6_m8" => 30
  -- Fidelity `FullM8SweepV2` (`K6` sweeping kitten, base parity)
  | "full_k6_watch" => 70
  | "full_k6_assign" => 97
  | "full_k6_backtrack" => 137
  | "full_k6_mtf" => 177
  | "full_k6_add_ticks" => 18
  | "full_m6_max_v" => 32
  -- Underbudgeted PGO entries updated above observed post-inline IR size
  | "full_cong_find" => 52
  | "full_sort_u32" => 162
  | "m6_hdr_bump_delay" => 82
  | "full_sort_tmp_heap_m7" => 215
  -- Keep cold `m6_hdr_init` OOL (`0`); inline hot `m6_hdr` metadata/delay helpers
  | "m6_hdr_init" => 0
  | "m6_ext_ensure_init" => 75
  | "m6_hdr_delaying" => 40
  | "m6_hdr_reduce_delay" => 48
  | "m6_hdr_dr_init" => 60
  | "m6_hdr_sync_legacy_tiers" => 30
  | "m6_hdr_decide_fid" => 90
  -- Newly covered hot leaves and Fidelity helpers (`0` beyond-upstream heuristics)
  | "full_bva_match_large_fid" => 65
  | "full_reorder_sift_fid" => 105
  | "full_assign_lvl" => 165
  | "full_assign" => 150
  | "full_min_mark" => 75
  | "full_cong_enq_var" => 85
  | "full_backtrack" => 64
  | "full_extend_push2" => 97
  | "full_cong_unit_fold" => 72
  | "full_cong_mark_trail" => 76
  | "full_add_unit" => 185
  | "full_bump_var" => 175
  | "full_m6_dense_prop" => 44
  | "full_elim_dticks" => 42
  | "full_otfs_subsume" => 130
  | "full_k512_flip" => 165
  | "full_k6_flip" => 250
  | "full_m6_sweep_rearm" => 155
  | "full_m6_sweep_refine_sig" => 90
  | "full_m6_sweep_rand_phases" => 110
  | "full_m6_sweep_solve" => 115
  | "full_queue_mtf" => 240
  | "full_cong_eb_match" => 200
  | "full_sweep_copy" => 315
  | "full_analyze_rsn_m6_hdr" => 450
  -- Gate-1 Step 5 (`Bve`) & Step 6 (`Bva`) purified `_fid` leaf helpers
  | "full_bve_k6_mv_fid" => 25
  | "full_fid_k6_add_ticks" => 30
  | "full_k6_watch_fid" => 90
  | "full_k6_assign_fid" => 115
  | "full_k6_mtf_fid" => 135
  | "full_k6_backtrack_fid" => 120
  | "full_bve_def_k6_fid" => 90
  | "full_bva_steps_cap_fid" => 20
  | "full_bva_clines_fid" => 15
  | "full_fheap_up_fid" => 55
  | "full_fheap_down_fid" => 80
  | "full_bva_count_lit_deg_fid" => 55
  | "full_bva_match_large_bva_fid" => 70
  | s => m7PgoBudget s

/-- Profile-guided `InlinePolicy` for `KissatFidelity` (`maxCallerSize := 4000`, `leafMax := 165`,
`m6_hdr_init` kept out-of-line). -/
def fidInlPolicy : InlinePolicy :=
  { m7InlPolicy with
    budget := fidPgoBudget
    leafMax := 165
    maxCallerSize := 4000
    maxCalleeLoops := some 1
    maxTotalDup := 1500
    maxCallerCalls := 24
    keepOutOfLine := ["m6_hdr_init"] }

/-- Zero-scan chunkable `InlinePolicy` matching `fidInlPolicy` on `KissatFidelity`: sets
`singleSiteMax := 0`, `maxTotalDup := 0`, and `requireLoopSite := false` so `inlSiteCounts` and
`inlLoopCounts` reduce to `[]` in `O(1)` inside `inline_chunk_base!`. -/
def fidInlChunkPolicy : InlinePolicy :=
  { fidInlPolicy with
    singleSiteMax := 0
    maxTotalDup := 0
    requireLoopSite := false }

/-- Every function in `M.optInlinePolicy fidInlPolicy` remains well-formed. -/
theorem fidInlPolicy_wf {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy fidInlPolicy).fns, f.Wf :=
  Module.optInlinePolicy_wf fidInlPolicy hchk hwf

/-- Acyclicity transports from `M` to `M.optInlinePolicy fidInlPolicy`. -/
theorem fidInlPolicy_checkAcyclic {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy fidInlPolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic fidInlPolicy hchk hwf

/-- `ModuleOk` transports from `M` to `M.optInlinePolicy fidInlPolicy`. -/
theorem fidInlPolicy_ok {Γ : Env} {M : Module} :
    ModuleOk Γ M → ModuleOk Γ (M.optInlinePolicy fidInlPolicy) :=
  Module.optInlinePolicy_ok fidInlPolicy

/-- Ordered `Fn.callsOk` transports from `M` to `M.optInlinePolicy fidInlPolicy`. -/
theorem fidInlPolicy_callsOk {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy fidInlPolicy).fns = pre ++ fn :: post →
      Fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits fn :=
  Module.optInlinePolicy_callsOk fidInlPolicy hchk hwf

/-- Per-function WP specification transports from `M` to `M.optInlinePolicy fidInlPolicy`. -/
theorem fidInlPolicy_spec {Γ : Env} {M : Module}
    (hok : ModuleOk Γ M) {f : Fn} (hf : f ∈ (M.optInlinePolicy fidInlPolicy).fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hpre : Γ f.name f.as f.rs xs m Q X) : Func.wp Γ f.body xs m Q X :=
  Module.optInlinePolicy_spec fidInlPolicy hok f hf xs m Q X hpre

/-- `Func.supportsSource` transports from `M` to `M.optInlinePolicy fidInlPolicy`. -/
theorem fidInlPolicy_supportsSource (lt : LegalTarget) {M : Module}
    (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsup : ∀ f ∈ M.fns, Func.supportsSource lt f.body = true) :
    ∀ f ∈ (M.optInlinePolicy fidInlPolicy).fns, Func.supportsSource lt f.body = true :=
  Module.optInlinePolicy_supportsSource lt fidInlPolicy hwf hsup

/-- Every function in `M.optInlinePolicy fidInlChunkPolicy` remains well-formed. -/
theorem fidInlChunkPolicy_wf {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy fidInlChunkPolicy).fns, f.Wf :=
  Module.optInlinePolicy_wf fidInlChunkPolicy hchk hwf

/-- Acyclicity transports from `M` to `M.optInlinePolicy fidInlChunkPolicy`. -/
theorem fidInlChunkPolicy_checkAcyclic {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy fidInlChunkPolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic fidInlChunkPolicy hchk hwf

/-- `ModuleOk` transports from `M` to `M.optInlinePolicy fidInlChunkPolicy`. -/
theorem fidInlChunkPolicy_ok {Γ : Env} {M : Module} :
    ModuleOk Γ M → ModuleOk Γ (M.optInlinePolicy fidInlChunkPolicy) :=
  Module.optInlinePolicy_ok fidInlChunkPolicy

/-- Ordered `Fn.callsOk` transports from `M` to `M.optInlinePolicy fidInlChunkPolicy`. -/
theorem fidInlChunkPolicy_callsOk {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy fidInlChunkPolicy).fns = pre ++ fn :: post →
      Fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits fn :=
  Module.optInlinePolicy_callsOk fidInlChunkPolicy hchk hwf

/-- Per-function WP specification transports from `M` to `M.optInlinePolicy fidInlChunkPolicy`.
-/
theorem fidInlChunkPolicy_spec {Γ : Env} {M : Module}
    (hok : ModuleOk Γ M) {f : Fn} (hf : f ∈ (M.optInlinePolicy fidInlChunkPolicy).fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hpre : Γ f.name f.as f.rs xs m Q X) : Func.wp Γ f.body xs m Q X :=
  Module.optInlinePolicy_spec fidInlChunkPolicy hok f hf xs m Q X hpre

/-- `Func.supportsSource` transports from `M` to `M.optInlinePolicy fidInlChunkPolicy`. -/
theorem fidInlChunkPolicy_supportsSource (lt : LegalTarget) {M : Module}
    (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsup : ∀ f ∈ M.fns, Func.supportsSource lt f.body = true) :
    ∀ f ∈ (M.optInlinePolicy fidInlChunkPolicy).fns, Func.supportsSource lt f.body = true :=
  Module.optInlinePolicy_supportsSource lt fidInlChunkPolicy hwf hsup

end LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

end
