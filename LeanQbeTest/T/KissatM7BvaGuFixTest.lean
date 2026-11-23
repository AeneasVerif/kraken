module

public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
meta import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
meta import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
meta import LeanQbe.T.Examples.Kissat.FullM5HeurCore
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Signature Guards, and Axiom Audit for `FullM7BvaGuFix`

1. Executable `#guard` checks on `m7BvaGuFixModule` (`2` fns + `8` externs, `0` exits),
   `checkAcyclic = true`, drop-in `Fn.sig` equality with `FullM5DenseSafe.m5BvaCommitFn` and
   `FullM5HeurCore.m5AnalyzeRsnFn`, `PrintCpp`, `PrintQbe`, and `Fn.legal` (`aarch64`,
   `scalar64`, `x64AVX2`).
2. Audit-ready restated headline theorems (`m7BvaGuFix_fns_wf`, `m7BvaGuFix_acyclic`,
   `full_bva_commit_m7_wp`, `full_analyze_rsn_m7_wp`, `full_analyze_rsn_m7_gu36_preserved`,
   `m7BvaGuFix_moduleOk`, and concrete non-bailout `nv_m7_analyze_rsn`).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BvaGuFixTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks, Signature Equality Guards, and Backend Compilation -/

#guard m7BvaGuFixModule.checkAcyclic == true
#guard m7BvaGuFixModule.exits.isEmpty
#guard m7BvaGuFix_fns.length == 2
#guard m7BvaGuFixExterns.length == 8
#guard m7BvaCommitFn.sig == FullM5DenseSafe.m5BvaCommitFn.sig
#guard m7AnalyzeRsnFn.sig == FullM5HeurCore.m5AnalyzeRsnFn.sig
#guard (ppTModule m7BvaGuFixModule).isOk
#guard (PrintQbe.module m7BvaGuFixModule).isOk
#guard (ppModule (m7BvaGuFix_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BvaGuFix_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BvaGuFix_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m7f_wf : ∀ f ∈ m7BvaGuFix_fns, f.Wf :=
  m7BvaGuFix_fns_wf

theorem m7f_acyc : m7BvaGuFixModule.checkAcyclic = true :=
  m7BvaGuFix_acyclic

theorem m7f_tbl_len : m7BvaGuFixSpecTable.length = 10 :=
  m7BvaGuFixSpecTable_length

theorem m7f_bva_sig : m7BvaCommitFn.sig = FullM5DenseSafe.m5BvaCommitFn.sig := rfl

theorem m7f_rsn_sig : m7AnalyzeRsnFn.sig = FullM5HeurCore.m5AnalyzeRsnFn.sig := rfl

theorem m7f_bva_wp (Γ : Env)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, m4BvaCommitSpec args m Q X →
      Func.wp Γ full_bva_commit_m7_body args m Q X :=
  full_bva_commit_m7_wp Γ hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch

theorem m7f_rsn_wp (Γ : Env)
    (hLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
      Func.wp Γ full_analyze_rsn_m7_body a m Q X :=
  full_analyze_rsn_m7_wp Γ hLit

theorem m7f_mod_ok : ModuleOk m7BvaGuFixEnv m7BvaGuFixModule :=
  m7BvaGuFix_moduleOk

theorem m7f_nv_rsn :
    Func.wp m7BvaGuFixEnv full_analyze_rsn_m7_body (nvM7RsnCfg.hdr, 0#32, 0#32, ()) nvM7RsnMem
      (fun (_ok, ()) m' => ∃ mrk' tmp' tc' tl' mcl' arena' sc',
        let s' : FullState :=
          { nvM7RsnState with
            core := { nvM7RsnState.core with
              mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
              min_clr_len := mcl', arena := arena' }
            scratch := sc' }
        s'.LengthsOk nvM7RsnCfg ∧
        FullWitnessCutInv nvM7RsnCfg nvOneLitF0 [[0], [1]]
          nvM7RsnState.core.trail_end s'.core ∧
        (∀ i, 36 ≤ i → i < 64 → sc'.glue_used[i]? = some 0x12345678#32) ∧
        nvOneLitF0.Unsat ∧ FullMem nvM7RsnCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_analyze_rsn

end AuditSpec

end LeanQbeTest.T.KissatM7BvaGuFixTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7f_a_wf := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_wf
abbrev m7f_a_acyc := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_acyc
abbrev m7f_a_tlen := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_tbl_len
abbrev m7f_a_bsig := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_bva_sig
abbrev m7f_a_rsig := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_rsn_sig
abbrev m7f_a_bva := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_bva_wp
abbrev m7f_a_rsn := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_rsn_wp
abbrev m7f_a_mod := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_mod_ok
abbrev m7f_a_nv := @LeanQbeTest.T.KissatM7BvaGuFixTest.m7f_nv_rsn

#print axioms m7f_a_wf
#print axioms m7f_a_acyc
#print axioms m7f_a_tlen
#print axioms m7f_a_bsig
#print axioms m7f_a_rsig
#print axioms m7f_a_bva
#print axioms m7f_a_rsn
#print axioms m7f_a_mod
#print axioms m7f_a_nv
