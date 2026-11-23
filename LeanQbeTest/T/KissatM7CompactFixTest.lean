module

public import LeanQbe.T.Examples.Kissat.FullM7CompactFix
public import LeanQbe.T.Examples.Kissat.FullM7CompactFixProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7CompactFix
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7CompactFix`

1. Executable `#guard` checks on `m7CompactFixModule` (`4` fns, `3` externs, `0` exits),
   drop-in handles (`m7fixCompactNeededFn`, `m7fixCompactMarkLiveFn`, `m7fixCompactVarsFn`,
   `m7fixSweepCopyFn`), `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal`
   across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, canonical specs
   (`fullCompactNeededSpec`, `fullCompactMarkLiveSpec`, `fullCompactVarsSpec`,
   `fullSweepCopySpec`), strengthened M7 fix guarantees (`1%` trigger parity, `NoZombieMap`,
   `fl[nv] = fl[ov]` flag preservation, `PH_RED` zombie drop), closed `ModuleOk`, and
   concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7CompactFixTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7CompactFix_fns.length == 4
#guard m7CompactFixModule.fns.length == 4
#guard m7CompactFixExterns.length == 3
#guard m7CompactFixModule.externs.length == 3
#guard m7CompactFixModule.checkAcyclic == true
#guard m7CompactFixModule.exits.isEmpty == true
#guard m7fixCompactNeededFn.name == "full_compact_needed"
#guard m7fixCompactNeededFn.as == [i64]
#guard m7fixCompactNeededFn.rs == [.bool]
#guard m7fixCompactMarkLiveFn.name == "full_compact_mark_live"
#guard m7fixCompactMarkLiveFn.as == [i64]
#guard m7fixCompactMarkLiveFn.rs == []
#guard m7fixCompactVarsFn.name == "full_compact_vars"
#guard m7fixCompactVarsFn.as == [i64, i64, i64]
#guard m7fixCompactVarsFn.rs == []
#guard m7fixSweepCopyFn.name == "full_sweep_copy"
#guard m7fixSweepCopyFn.as == [i64, i64, i64, i32, .bool]
#guard m7fixSweepCopyFn.rs == [i64]
#guard (ppTModule m7CompactFixModule).isOk
#guard (PrintQbe.module m7CompactFixModule).isOk
#guard (ppModule (m7CompactFix_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7CompactFix_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7CompactFix_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7CompactFix_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem wf_needed : Func.Wf full_compact_needed_m7fix_body :=
  full_compact_needed_m7fix_wf

theorem wf_mkLive : Func.Wf full_compact_mark_live_m7fix_body :=
  full_compact_mark_live_m7fix_wf

theorem wf_vars : Func.Wf full_compact_vars_m7fix_body :=
  full_compact_vars_m7fix_wf

theorem wf_sweep : Func.Wf full_sweep_copy_m7fix_body :=
  full_sweep_copy_m7fix_wf

theorem fns_wf : ∀ f ∈ m7CompactFix_fns, f.Wf :=
  m7CompactFix_fns_wf

theorem acyc : m7CompactFixModule.checkAcyclic = true :=
  m7CompactFix_acyclic

theorem tbl_len : m7CompactFixSpecTable.length = 7 :=
  m7CompactFixSpecTable_length

theorem noExit :
    ∀ f as bs xs m Q X X',
      m7CompactFixEnv f as bs xs m Q X → m7CompactFixEnv f as bs xs m Q X' :=
  m7CompactFixEnv_noExit

theorem mod_ok : ModuleOk m7CompactFixEnv m7CompactFixModule :=
  m7CompactFix_moduleOk

theorem needed_exact_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededM7FixSpec a m Q X →
      Func.wp Γ full_compact_needed_m7fix_body a m Q X :=
  full_compact_needed_m7fix_exact_wp Γ

theorem needed_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededSpec a m Q X →
      Func.wp Γ full_compact_needed_m7fix_body a m Q X :=
  full_compact_needed_m7fix_wp Γ

theorem mkLive_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_m7fix_body a m Q X :=
  full_compact_mark_live_m7fix_wp Γ hnext

theorem vars_wp (Γ : Env) :
    ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Func.wp Γ full_compact_vars_m7fix_body a m Q X :=
  full_compact_vars_m7fix_wp Γ

theorem sweep_wp (Γ : Env)
    (hassign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X →
      Func.wp Γ full_sweep_copy_m7fix_body a m Q X :=
  full_sweep_copy_m7fix_wp Γ hassign hpush

theorem neededFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactNeededFn
      ⟨"full_compact_needed", [i64], [.bool], fullCompactNeededSpec, true⟩ :=
  m7fixCompactNeededFn_impl

theorem mkLiveFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactMarkLiveFn
      ⟨"full_compact_mark_live", [i64], [], fullCompactMarkLiveSpec, true⟩ :=
  m7fixCompactMarkLiveFn_impl

theorem varsFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactVarsFn
      ⟨"full_compact_vars", [i64, i64, i64], [], fullCompactVarsSpec, true⟩ :=
  m7fixCompactVarsFn_impl

theorem sweepFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixSweepCopyFn
      ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩ :=
  m7fixSweepCopyFn_impl

theorem nv_needed :
    Func.wp m7CompactFixEnv full_compact_needed_m7fix_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (res, ()) m' =>
        res = false ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg nvCompactState m')
      (fun _ _ _ _ => False) :=
  nv_m7fix_compact_needed

theorem nv_mkLive :
    Func.wp m7CompactFixEnv full_compact_mark_live_m7fix_body (nvM7MkLiveCfg.hdr, ())
      nvM7MkLiveMem
      (fun () m' => ∃ ws1',
        let s' : FullState :=
          { nvM7MkLiveState with scratch := { nvM7MkLiveState.scratch with work_stk1 := ws1' } }
        FullSparseInv nvM7MkLiveCfg nvOneLitF0 s' ∧ ws1'[1]? = some 0#32 ∧
        nvOneLitF0.Unsat ∧ FullMem nvM7MkLiveCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7fix_compact_mark_live

theorem nv_vars :
    Func.wp m7CompactFixEnv full_compact_vars_m7fix_body
      (nvM7MkLiveCfg.hdr, 3#64, 1#64, ()) nvM7MkLiveMem
      (fun () m' => ∃ c' vals' fl' lvl' rsns' ft0' fd0' sc',
        let s' : FullState :=
          { core := { nvM7MkLiveState.core with
                      vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                      frame_trail := nvM7MkLiveState.core.frame_trail.set 0 ft0',
                      frame_dec := nvM7MkLiveState.core.frame_dec.set 0 fd0',
                      trail_end := 0, propagated := 0, cur_level := 0,
                      unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                      cur_vars := 1, unassigned := 1#64 }
            scratch := sc' }
        FullCfgCompat nvM7MkLiveCfg c' ∧ c'.mv = 1 ∧ s'.LengthsOk c' ∧
        fl'[0]? = some 8#32 ∧ nvOneLitF0.Unsat ∧ FullMem c' s' m')
      (fun _ _ _ _ => False) :=
  nv_m7fix_compact_vars

theorem nv_sweep :
    Func.wp m7CompactFixEnv full_sweep_copy_m7fix_body
      (nvM7MkLiveCfg.hdr, 0#64, 0#64, 3#32, true, ()) nvM7MkLiveMem
      (fun (r, ()) _ => r = 0xFFFFFFFF#64 ∧ nvOneLitF0.Unsat)
      (fun _ _ _ _ => False) :=
  nv_m7fix_sweep_copy

end LeanQbeTest.T.KissatM7CompactFixTest

/-! ## 3. Single-Line `#print axioms` Audit (Standard Axioms) -/

abbrev m7cf_wf_needed := @LeanQbeTest.T.KissatM7CompactFixTest.wf_needed
abbrev m7cf_wf_mkLive := @LeanQbeTest.T.KissatM7CompactFixTest.wf_mkLive
abbrev m7cf_wf_vars := @LeanQbeTest.T.KissatM7CompactFixTest.wf_vars
abbrev m7cf_wf_sweep := @LeanQbeTest.T.KissatM7CompactFixTest.wf_sweep
abbrev m7cf_fns_wf := @LeanQbeTest.T.KissatM7CompactFixTest.fns_wf
abbrev m7cf_acyc := @LeanQbeTest.T.KissatM7CompactFixTest.acyc
abbrev m7cf_tbl_len := @LeanQbeTest.T.KissatM7CompactFixTest.tbl_len
abbrev m7cf_noExit := @LeanQbeTest.T.KissatM7CompactFixTest.noExit
abbrev m7cf_modOk := @LeanQbeTest.T.KissatM7CompactFixTest.mod_ok
abbrev m7cf_needed_ex := @LeanQbeTest.T.KissatM7CompactFixTest.needed_exact_wp
abbrev m7cf_needed := @LeanQbeTest.T.KissatM7CompactFixTest.needed_wp
abbrev m7cf_mkLive := @LeanQbeTest.T.KissatM7CompactFixTest.mkLive_wp
abbrev m7cf_vars := @LeanQbeTest.T.KissatM7CompactFixTest.vars_wp
abbrev m7cf_sweep := @LeanQbeTest.T.KissatM7CompactFixTest.sweep_wp
abbrev m7cf_neededFn := @LeanQbeTest.T.KissatM7CompactFixTest.neededFn_impl
abbrev m7cf_mkLiveFn := @LeanQbeTest.T.KissatM7CompactFixTest.mkLiveFn_impl
abbrev m7cf_varsFn := @LeanQbeTest.T.KissatM7CompactFixTest.varsFn_impl
abbrev m7cf_sweepFn := @LeanQbeTest.T.KissatM7CompactFixTest.sweepFn_impl
abbrev m7cf_nv_needed := @LeanQbeTest.T.KissatM7CompactFixTest.nv_needed
abbrev m7cf_nv_mkLive := @LeanQbeTest.T.KissatM7CompactFixTest.nv_mkLive
abbrev m7cf_nv_vars := @LeanQbeTest.T.KissatM7CompactFixTest.nv_vars
abbrev m7cf_nv_sweep := @LeanQbeTest.T.KissatM7CompactFixTest.nv_sweep

#print axioms m7cf_wf_needed
#print axioms m7cf_wf_mkLive
#print axioms m7cf_wf_vars
#print axioms m7cf_wf_sweep
#print axioms m7cf_fns_wf
#print axioms m7cf_acyc
#print axioms m7cf_tbl_len
#print axioms m7cf_noExit
#print axioms m7cf_modOk
#print axioms m7cf_needed_ex
#print axioms m7cf_needed
#print axioms m7cf_mkLive
#print axioms m7cf_vars
#print axioms m7cf_sweep
#print axioms m7cf_neededFn
#print axioms m7cf_mkLiveFn
#print axioms m7cf_varsFn
#print axioms m7cf_sweepFn
#print axioms m7cf_nv_needed
#print axioms m7cf_nv_mkLive
#print axioms m7cf_nv_vars
#print axioms m7cf_nv_sweep

end
