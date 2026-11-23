module

public import LeanQbe.T.Examples.Kissat.FullM3VivChrono
public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM3VivChrono
meta import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat M3 (`FullM3VivChrono`)

1. Executable `#guard` checks on `m3Module` (`5` fns + `10` externs), `m3FullModule` (`197`
   fns, `0` externs, `0` exits), `checkAcyclic = true`, `m3SpecTable` (`15` rows), `PrintCpp`,
   `PrintQbe`, and `Fn.legal` across `aarch64`, `scalar64`, and `x64AVX2`.
2. Audit-ready restated theorem types (every type written explicitly in full) for `m3_fns_wf`,
   `m3_acyclic`, `m3Fns_wf`, `m3Full_acyclic`, all `5` parametric `Func.wp` UNSAT-soundness theorems
   (`XPost := False`), `m3_moduleOk : ModuleOk m3Env m3Module`, and all `5` concrete `Mem 64`
   UNSAT non-vacuity theorems (`nv_m3_*`, `XPost := False`, `0` SAT model proofs).
3. Single-line `#print axioms` audit on all `15` restated theorems (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM3VivChronoTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3VivChrono
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m3Module.checkAcyclic == true
#guard m3FullModule.checkAcyclic == true
#guard m3Module.exits.isEmpty && m3FullModule.exits.isEmpty && m3FullModule.externs.isEmpty
#guard m3VivChrono_fns.length == 5
#guard m3Externs.length == 10
#guard m3Fns.length == 197
#guard m3SpecTable.length == 15
#guard (ppTModule m3Module).isOk
#guard (ppTModule m3FullModule).isOk
#guard (PrintQbe.module m3Module).isOk
#guard (PrintQbe.module m3FullModule).isOk
#guard (ppModule (m3Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m3Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m3Fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

/-- Every function in `m3VivChrono_fns` (`5` M3 upgraded functions) is well-formed. -/
theorem m3a_wf : ∀ f ∈ m3VivChrono_fns, f.Wf :=
  m3_fns_wf

/-- Standalone M3 vivification/chrono module `m3Module` passes `checkAcyclic = true`. -/
theorem m3a_acyc : m3Module.checkAcyclic = true :=
  m3_acyclic

/-- Every function in `m3Fns` (`197` functions spliced onto `FullFast.fastFns`) is well-formed. -/
theorem m3a_full_wf : ∀ f ∈ m3Fns, f.Wf :=
  m3Fns_wf

/-- Spliced M3 full module `m3FullModule` passes `checkAcyclic = true`. -/
theorem m3a_full_acyc : m3FullModule.checkAcyclic = true :=
  m3Full_acyclic

/-- Stable-only `full_tick_rel` satisfies `fullTickRelSpec` parametrically in `Γ`. -/
theorem m3a_tick_wp (Γ : Env) :
    ∀ a m Q X, fullTickRelSpec a m Q X → Func.wp Γ FullM3VivChrono.full_tick_rel_body a m Q X :=
  m3_tick_rel_wp Γ

/-- Glue-promoting `full_analyze_rsn` satisfies `fullAnalyzeRsnSpec` parametrically in `Γ`. -/
theorem m3a_rsn_wp (Γ : Env)
    (hLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
      Func.wp Γ FullM3VivChrono.full_analyze_rsn_body a m Q X :=
  m3_analyze_rsn_wp Γ hLit

/-- Chrono `lits[1]`-swapping `full_prop_lit` satisfies `fullPropLitSpec` parametrically in `Γ`.
-/
theorem m3a_prop_wp (Γ : Env)
    (hRaw : ∀ a m Q X, fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullPropLitSpec a m Q X → Func.wp Γ FullM3VivChrono.full_prop_lit_body a m Q X :=
  m3_prop_lit_wp Γ hRaw hPush

/-- Cursor + Tier-3 `full_vivify` satisfies `fullVivifyFastSpec` parametrically in `Γ`. -/
theorem m3a_viv_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hNext : ∀ args m Q X, Full.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hVivClause : ∀ args m Q X, Full.fullVivClauseSpec args m Q X →
      Γ "full_viv_clause" [i64, i32] [i64] args m Q X)
    (hProp : ∀ args m Q X, Full.fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullVivifyFastSpec args m Q X →
      Func.wp Γ FullM3VivChrono.full_vivify_body args m Q X :=
  m3_vivify_wp Γ hBacktrack hNext hVivClause hProp

/-- Tier-1/2/3/0 `full_probe_tail` satisfies `schedProbeTailSpec` parametrically in `Γ`. -/
theorem m3a_tail_wp (Γ : Env)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunFastSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X →
      Func.wp Γ FullM3VivChrono.full_probe_tail_body a m Q X :=
  m3_probe_tail_wp Γ hTrans hMin hPRun hViv

/-- Closed `15`-row `ModuleOk` certifying all `5` M3 upgraded functions under `m3Env`. -/
theorem m3a_mod_ok : ModuleOk m3Env m3Module :=
  m3_moduleOk

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_tick_rel`. -/
theorem m3a_nv_tick :
    Func.wp m3Env FullM3VivChrono.full_tick_rel_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_tick_rel

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_analyze_rsn`. -/
theorem m3a_nv_rsn :
    Func.wp m3Env FullM3VivChrono.full_analyze_rsn_body
      (nvOneLitCfg.hdr, 0x80000000#32, 0#32, ()) nvOneLitMem
      (fun (_ok, ()) m' => ∃ mrk' tmp' tc' tl' mcl' arena' sc',
        let s' : FullState :=
          { nvOneLitState with
            core := { nvOneLitState.core with
              mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
              min_clr_len := mcl', arena := arena' }
            scratch := sc' }
        s'.LengthsOk nvOneLitCfg ∧
        FullWitnessCutInv nvOneLitCfg nvOneLitF0 [[0], [1]]
          nvOneLitState.core.trail_end s'.core ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_analyze_rsn

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_prop_lit`. -/
theorem m3a_nv_prop :
    Func.wp m3Env FullM3VivChrono.full_prop_lit_body (nvOneLitCfg.hdr, 0#32, 0#64, ()) nvOneLitMem
      (fun (_ok, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧
        FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] s'.core ∧
        s'.core.dense_mode = 0#64 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_prop_lit

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for Tier-3 `full_vivify`. -/
theorem m3a_nv_viv :
    Func.wp m3Env FullM3VivChrono.full_vivify_body (nvOneLitCfg.hdr, 3#64, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_vivify

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_tail`. -/
theorem m3a_nv_tail :
    Func.wp m3Env FullM3VivChrono.full_probe_tail_body (nvOneLitCfg.hdr, 0#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_probe_tail

end AuditSpec

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m3a_wf
#print axioms m3a_acyc
#print axioms m3a_full_wf
#print axioms m3a_full_acyc
#print axioms m3a_tick_wp
#print axioms m3a_rsn_wp
#print axioms m3a_prop_wp
#print axioms m3a_viv_wp
#print axioms m3a_tail_wp
#print axioms m3a_mod_ok
#print axioms m3a_nv_tick
#print axioms m3a_nv_rsn
#print axioms m3a_nv_prop
#print axioms m3a_nv_viv
#print axioms m3a_nv_tail

end LeanQbeTest.T.KissatM3VivChronoTest
