module

public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM3Backbone
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for Kissat M3c Backbone & `probe_run` Cursor

1. Executable `#guard` checks on `m3BackboneLocalModule` (`5` fns + `15` externs),
   `m3BackboneFastModule` (`198` fns, closed), and `m3BackboneFullModule` (`168` fns, closed):
   acyclicity, `PrintCpp`, `PrintQbe`, and `Legal` across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. Audit-ready restated theorems (`m3b_*`) covering:
   - `Func.Wf` & `checkAcyclic = true` for all `6` M3c functions and all `3` modules
   - `Func.wp` UNSAT-soundness for wrap-around `full_probe_run` (cursor-bound + canonical + Fast),
     `full_backbone_lit` (explicit semantic unit-entailment `EntailsClause [cand]` + `F0.Unsat`),
     `full_backbone`, `full_probe_tail`, `full_probe`, and `FullProbeFull.full_probe`
   - `ModuleOk` for `m3BackboneLocalModule` (`5/5`) and unconditional `168/168` closed-module
     `ModuleOk` for `m3BackboneFullModule` (`externs := []`, `exits := []`)
   - End-to-end `kissat_solve_bytes` UNSAT soundness and concrete `Mem 64` UNSAT non-vacuity
     (`XPost := False`, strictly UNSAT-only — zero SAT model-finding proofs).
3. Single-line `#print axioms` (`<= 100` cols) strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3Backbone

/-! ## 1. Executable `#guard` Checks (`Acyclicity`, `PrintCpp`, `PrintQbe`, `Legal`) -/

#guard m3Backbone_fns.length == 5
#guard FullProbeFull.fullProbeM3_fns.length == 1
#guard m3BackboneLocalModule.checkAcyclic == true
#guard m3BackboneLocalModule.exits.isEmpty
#guard m3BackboneFastFns.length == 198
#guard m3BackboneFastModule.checkAcyclic == true
#guard m3BackboneFastModule.exits.isEmpty && m3BackboneFastModule.externs.isEmpty
#guard m3BackboneFullFns.length == 168
#guard m3BackboneFullModule.checkAcyclic == true
#guard m3BackboneFullModule.exits.isEmpty && m3BackboneFullModule.externs.isEmpty
#guard (ppTModule m3BackboneLocalModule).isOk
#guard (PrintQbe.module m3BackboneLocalModule).isOk
#guard (ppTModule m3BackboneFastModule).isOk
#guard (PrintQbe.module m3BackboneFastModule).isOk
#guard (ppTModule m3BackboneFullModule).isOk
#guard (PrintQbe.module m3BackboneFullModule).isOk
#guard (ppModule (m3Backbone_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m3Backbone_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m3Backbone_fns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (FullProbeFull.fullProbeM3_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (FullProbeFull.fullProbeM3_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (FullProbeFull.fullProbeM3_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Theorems (`m3b_*`) -/

theorem m3b_fns_wf : ∀ f ∈ m3Backbone_fns, f.Wf := m3Backbone_fns_wf
theorem m3b_probe_full_wf : Func.Wf FullProbeFull.full_probe_body := FullProbeFull.full_probe_wf
theorem m3b_fast_wf : ∀ f ∈ m3BackboneFastFns, f.Wf := m3BackboneFastFns_wf
theorem m3b_full_wf : ∀ f ∈ m3BackboneFullFns, f.Wf := m3BackboneFullFns_wf

theorem m3b_local_acyclic : m3BackboneLocalModule.checkAcyclic = true := m3BackboneLocal_acyclic
theorem m3b_fast_acyclic : m3BackboneFastModule.checkAcyclic = true := m3BackboneFast_acyclic
theorem m3b_full_acyclic : m3BackboneFullModule.checkAcyclic = true := m3BackboneFull_acyclic

theorem m3b_probe_run_cursor_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAp : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullProbeRunCursorSpec a m Q X →
      Func.wp Γ FullM3Backbone.full_probe_run_body a m Q X :=
  m3_probe_run_cursor_wp Γ hBt hAp

theorem m3b_probe_run_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAp : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, Full.fullProbeRunSpec a m Q X →
      Func.wp Γ FullM3Backbone.full_probe_run_body a m Q X :=
  m3_probe_run_wp Γ hBt hAp

theorem m3b_probe_run_fast_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAp : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullProbeRunFastSpec a m Q X →
      Func.wp Γ FullM3Backbone.full_probe_run_body a m Q X :=
  m3_probe_run_fast_wp Γ hBt hAp

theorem m3b_backbone_lit_entails_wp (Γ : Env)
    (hAu : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBackboneLitEntailsSpec a m Q X → Func.wp Γ full_backbone_lit_body a m Q X :=
  m3_backbone_lit_entails_wp Γ hAu

theorem m3b_backbone_lit_wp (Γ : Env)
    (hAu : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBackboneLitSpec a m Q X → Func.wp Γ full_backbone_lit_body a m Q X :=
  m3_backbone_lit_wp Γ hAu

theorem m3b_backbone_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hPr : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hBl : ∀ a m Q X, fullBackboneLitSpec a m Q X →
      Γ "full_backbone_lit" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullBackboneSpec a m Q X → Func.wp Γ full_backbone_body a m Q X :=
  m3_backbone_wp Γ hBt hPr hBl

theorem m3b_probe_tail_wp (Γ : Env)
    (hBn : ∀ a m Q X, fullBackboneSpec a m Q X → Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTr : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMn : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPr : ∀ a m Q X, fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hVv : ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X →
      Func.wp Γ FullM3Backbone.full_probe_tail_body a m Q X :=
  m3_probe_tail_wp Γ hBn hTr hMn hPr hVv

theorem m3b_probe_wp (Γ : Env)
    (hDt : ∀ a m Q X, schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks" [i64, .bool] [i64] a m Q X)
    (hIl : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hSc : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hSb : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hEn : ∀ a m Q X, schedEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMn : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hCg : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, m3SweepDenseSpec a m Q X →
      Γ "full_sweep_dense" [i64, i64, i64] [i64] a m Q X)
    (hRb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBn : ∀ a m Q X, fullBackboneSpec a m Q X → Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTr : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hPr : ∀ a m Q X, fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hTl : ∀ a m Q X, schedProbeTailSpec a m Q X →
      Γ "full_probe_tail" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeSpec a m Q X →
      Func.wp Γ FullM3Backbone.full_probe_body a m Q X :=
  m3_probe_wp Γ hDt hIl hSc hSb hEn hMn hCg hSw hRb hBn hTr hPr hTl

theorem m3b_probe_full_wp (Γ : Env)
    (hSq : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hSb : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCg : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hBn : ∀ a m Q X, fullBackboneSpec a m Q X → Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTr : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPr : ∀ a m Q X, fullProbeRunSpec a m Q X → Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hVv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullProbeSpec a m Q X → Func.wp Γ FullProbeFull.full_probe_body a m Q X :=
  m3_probe_full_wp Γ hSq hSb hCg hSw hBn hTr hPr hVv

theorem m3b_local_moduleOk : ModuleOk m3BackboneLocalEnv m3BackboneLocalModule :=
  m3BackboneLocal_moduleOk

theorem m3b_full_moduleOk : ModuleOk m3BackboneFullEnv m3BackboneFullModule :=
  m3BackboneFullEnv_moduleOk

theorem m3b_full_unsat_moduleOk : ModuleOk m3BackboneFullUnsatEnv m3BackboneFullModule :=
  m3BackboneFullUnsatEnv_moduleOk

theorem m3b_full_solve_bytes_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3BackboneFullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m3BackboneFull_solve_bytes_correct hcfit hwfit hm

theorem m3b_full_unsat_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3BackboneFullUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ fullNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
  m3BackboneFull_unsat_nonvacuous

theorem m3b_nv_probe_run :
    Func.wp m3BackboneLocalEnv FullM3Backbone.full_probe_run_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_probe_run

theorem m3b_nv_backbone_lit_entails :
    Func.wp m3BackboneLocalEnv full_backbone_lit_body
      (nvOneLitCfg.hdr, 0#32, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧ s'.core.cur_level = 0 ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 1#64 → (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0])) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_backbone_lit_entails

theorem m3b_nv_backbone :
    Func.wp m3BackboneLocalEnv full_backbone_body
      (nvOneLitCfg.hdr, 65536#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_backbone

theorem m3b_nv_probe_tail :
    Func.wp m3BackboneLocalEnv FullM3Backbone.full_probe_tail_body
      (nvOneLitCfg.hdr, 1024#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_probe_tail

theorem m3b_nv_probe :
    Func.wp m3BackboneLocalEnv FullM3Backbone.full_probe_body
      (nvOneLitCfg.hdr, true, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_probe

theorem m3b_nv_probe_full :
    Func.wp m3BackboneFullEnv FullProbeFull.full_probe_body
      (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m3_probe_full

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms m3b_fns_wf
#print axioms m3b_probe_full_wf
#print axioms m3b_fast_wf
#print axioms m3b_full_wf
#print axioms m3b_local_acyclic
#print axioms m3b_fast_acyclic
#print axioms m3b_full_acyclic
#print axioms m3b_probe_run_cursor_wp
#print axioms m3b_probe_run_wp
#print axioms m3b_probe_run_fast_wp
#print axioms m3b_backbone_lit_entails_wp
#print axioms m3b_backbone_lit_wp
#print axioms m3b_backbone_wp
#print axioms m3b_probe_tail_wp
#print axioms m3b_probe_wp
#print axioms m3b_probe_full_wp
#print axioms m3b_local_moduleOk
#print axioms m3b_full_moduleOk
#print axioms m3b_full_unsat_moduleOk
#print axioms m3b_full_solve_bytes_ok
#print axioms m3b_full_unsat_nv
#print axioms m3b_nv_probe_run
#print axioms m3b_nv_backbone_lit_entails
#print axioms m3b_nv_backbone
#print axioms m3b_nv_probe_tail
#print axioms m3b_nv_probe
#print axioms m3b_nv_probe_full
