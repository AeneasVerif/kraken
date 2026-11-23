module

public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushLemmas
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
meta import LeanQbe.T.Examples.Kissat.FullM6CompactFlushLemmas
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Splice Parity, Backend Guards, and Axiom Audit for Kissat M6 Compact & Flush
(`FullM6CompactFlush`)

1. Executable `#guard` checks on `m6CompactFlushModule` (`8` fns + `7` externs, `0` exits),
   `checkAcyclic = true`, `m6CompactFlushSpecTable` (`15` rows), exact signature parity and
   closed `232`-fn acyclicity when inserting `m6cfFlushTrailFn` after `full_propagate` and
   splicing the `7` drop-in handles (`m6cfSweepBinsFn..m6cfExtendPushClFn`) into `FullM4.m4Fns`,
   `PrintCpp`, `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated headline theorems for `m6CompactFlush_fns_wf`, `m6CompactFlush_acyclic`,
   all `8` parametric `Func.wp` proofs (plus `TmkZero` variants), closed `15`-row
   `m6CompactFlush_moduleOk`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

namespace M6CfAudit

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks, `FullM4` Splice Parity & Backend Compilation Guards -/

private def m6cfOverrideHandles : List Fn :=
  [ m6cfSweepBinsFn, m6cfEnterDenseFn, m6cfCompactNeededFn, m6cfCompactFlushFn
  , m6cfCompactMarkLiveFn, m6cfExtendPush2Fn, m6cfExtendPushClFn ]

private def spliceOneM4 (fn : Fn) : List Fn :=
  let rep := match m6cfOverrideHandles.find? (fun h => h.name == fn.name) with
    | some h => h
    | none => fn
  if fn.name == "full_propagate" then [rep, m6cfFlushTrailFn] else [rep]

private def splicedM4Module : LeanQbe.T.Module :=
  { fns := FullM4.m4Fns.flatMap spliceOneM4, externs := [], exits := [] }

#guard m6CompactFlushModule.checkAcyclic == true
#guard m6CompactFlushModule.exits.isEmpty
#guard m6CompactFlush_fns.length == 8
#guard m6CompactFlushExterns.length == 7
#guard m6CompactFlushSpecTable.length == 15
#guard !(FullM4.m4Fns.any (fun f => f.name == m6cfFlushTrailFn.name))
#guard m6cfOverrideHandles.all (fun h =>
  FullM4.m4Fns.any (fun f => f.name == h.name && f.as == h.as && f.rs == h.rs))
#guard splicedM4Module.fns.length == 232
#guard splicedM4Module.checkAcyclic == true
#guard (ppTModule m6CompactFlushModule).isOk
#guard (PrintQbe.module m6CompactFlushModule).isOk
#guard (ppModule (m6CompactFlush_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6CompactFlush_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6CompactFlush_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m6CompactFlush_fns` (`8` M6 compact/flush/dedup functions) is well-formed. -/
public theorem m6cf_wf : ∀ f ∈ m6CompactFlush_fns, f.Wf :=
  m6CompactFlush_fns_wf

/-- Standalone M6 compact/flush module `m6CompactFlushModule` passes `checkAcyclic = true`. -/
public theorem m6cf_acyc : m6CompactFlushModule.checkAcyclic = true :=
  m6CompactFlush_acyclic

/-- `full_flush_trail` satisfies `fullFlushTrailSpec` parametrically in `Γ`. -/
public theorem m6cf_flush_trail_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullFlushTrailSpec a m Q X → Func.wp Γ full_flush_trail_body a m Q X :=
  full_flush_trail_wp Γ hBacktrack hProp

/-- `full_sweep_bins_m6cf` satisfies canonical `Full.fullSweepBinsSpec`. -/
public theorem m6cf_sweep_bins_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_m6cf_body a m Q X :=
  full_sweep_bins_m6cf_wp Γ hDefrag

/-- `full_enter_dense_m6cf` satisfies canonical `FullFastSched.schedEnterDenseSpec`. -/
public theorem m6cf_enter_dense_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, schedEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_m6cf_body a m Q X :=
  full_enter_dense_m6cf_wp Γ hBacktrack hFlush hSweepBins hWatchPush hSweep hArenaNext

/-- `full_compact_needed_m6cf` satisfies `fullCompactNeededM6Spec` (`10%` trigger). -/
public theorem m6cf_compact_needed_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Func.wp Γ full_compact_needed_m6cf_body a m Q X :=
  full_compact_needed_m6cf_wp Γ

/-- `full_compact_flush_m6cf` satisfies canonical `FullM4Compact.fullCompactFlushSpec`. -/
public theorem m6cf_compact_flush_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCompactFlushSpec a m Q X → Func.wp Γ full_compact_flush_m6cf_body a m Q X :=
  full_compact_flush_m6cf_wp Γ hFlush hSweep

/-- `full_compact_mark_live_m6cf` satisfies canonical `FullM4Compact.fullCompactMarkLiveSpec`. -/
public theorem m6cf_mark_live_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_m6cf_body a m Q X :=
  full_compact_mark_live_m6cf_wp Γ hNext

/-- `full_extend_push2_m6cf` satisfies `TmkZero`-preserving `fullExtendPush2TmkSpec`. -/
public theorem m6cf_ext_push2_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2TmkSpec a m Q X →
      Func.wp Γ full_extend_push2_m6cf_body a m Q X :=
  full_extend_push2_m6cf_tmk_wp Γ

/-- `full_extend_push2_m6cf` satisfies canonical `Full.fullExtendPush2Spec`. -/
public theorem m6cf_ext_push2_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2Spec a m Q X → Func.wp Γ full_extend_push2_m6cf_body a m Q X :=
  full_extend_push2_m6cf_wp Γ

/-- `full_extend_push_cl_m6cf` satisfies `TmkZero`-preserving `fullExtendPushClTmkSpec`. -/
public theorem m6cf_ext_push_cl_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClTmkSpec a m Q X →
      Func.wp Γ full_extend_push_cl_m6cf_body a m Q X :=
  full_extend_push_cl_m6cf_tmk_wp Γ

/-- `full_extend_push_cl_m6cf` satisfies canonical `Full.fullExtendPushClSpec`. -/
public theorem m6cf_ext_push_cl_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClSpec a m Q X → Func.wp Γ full_extend_push_cl_m6cf_body a m Q X :=
  full_extend_push_cl_m6cf_wp Γ

/-- Closed `15`-row `ModuleOk` certifying `m6CompactFlushModule` under `m6CompactFlushEnv`. -/
public theorem m6cf_mod_ok : ModuleOk m6CompactFlushEnv m6CompactFlushModule :=
  m6CompactFlush_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_flush_trail`. -/
public theorem m6cf_nv_flush :
    Func.wp m6CompactFlushEnv full_flush_trail_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvCompactF0.Unsat) ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_flush_trail

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_sweep_bins_m6cf`. -/
public theorem m6cf_nv_sweep_bins :
    Func.wp m6CompactFlushEnv full_sweep_bins_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun () m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ nvCompactF0.Unsat ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_sweep_bins

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_enter_dense_m6cf`. -/
public theorem m6cf_nv_enter_dense :
    Func.wp m6CompactFlushEnv full_enter_dense_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (ok, ()) m' => ∃ s',
        (if ok then FullDenseInv nvCompactCfg nvCompactF0 s'
         else FullSparseInv nvCompactCfg nvCompactF0 s') ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_enter_dense

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_needed_m6cf`. -/
public theorem m6cf_nv_needed :
    Func.wp m6CompactFlushEnv full_compact_needed_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (res, ()) m' =>
        (res = true → nvCompactState.core.cur_vars <
          10 * (nvCompactState.core.cur_vars - nvCompactState.core.unassigned.toNat)) ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg nvCompactState m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_compact_needed

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_flush_m6cf`. -/
public theorem m6cf_nv_cflush :
    Func.wp m6CompactFlushEnv full_compact_flush_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvCompactF0.Unsat) ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_compact_flush

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_mark_live_m6cf`. -/
public theorem m6cf_nv_mark_live :
    Func.wp m6CompactFlushEnv full_compact_mark_live_m6cf_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun () m' => ∃ s',
        FullSparseInv nvCompactCfg nvCompactF0 s' ∧ nvCompactF0.Unsat ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_compact_mark_live

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_extend_push2_m6cf`. -/
public theorem m6cf_nv_ext2 :
    Func.wp m6CompactFlushEnv full_extend_push2_m6cf_body
      (nvCompactCfg.hdr, 0#32, 1#32, ()) nvCompactMem
      (fun (_, ()) m' => ∃ s',
        s'.core = nvCompactState.core ∧ s'.LengthsOk nvCompactCfg ∧
        s'.scratch.extend_len ≤ nvCompactCfg.extend_cap ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_extend_push2

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_extend_push_cl_m6cf`. -/
public theorem m6cf_nv_ext_cl :
    Func.wp m6CompactFlushEnv full_extend_push_cl_m6cf_body
      (nvCompactCfg.hdr, 0#32, 0#32, ()) nvCompactMem
      (fun (_, ()) m' => ∃ s',
        s'.core = nvCompactState.core ∧ s'.LengthsOk nvCompactCfg ∧
        s'.scratch.extend_len ≤ nvCompactCfg.extend_cap ∧
        nvCompactF0.Unsat ∧ FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m6cf_extend_push_cl

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m6cf_wf
#print axioms m6cf_acyc
#print axioms m6cf_flush_trail_wp
#print axioms m6cf_sweep_bins_wp
#print axioms m6cf_enter_dense_wp
#print axioms m6cf_compact_needed_wp
#print axioms m6cf_compact_flush_wp
#print axioms m6cf_mark_live_wp
#print axioms m6cf_ext_push2_tmk_wp
#print axioms m6cf_ext_push2_wp
#print axioms m6cf_ext_push_cl_tmk_wp
#print axioms m6cf_ext_push_cl_wp
#print axioms m6cf_mod_ok
#print axioms m6cf_nv_flush
#print axioms m6cf_nv_sweep_bins
#print axioms m6cf_nv_enter_dense
#print axioms m6cf_nv_needed
#print axioms m6cf_nv_cflush
#print axioms m6cf_nv_mark_live
#print axioms m6cf_nv_ext2
#print axioms m6cf_nv_ext_cl

end M6CfAudit
