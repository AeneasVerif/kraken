module

public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification & Axiom Audit for Kissat M5 Scheduler (`FullM5Sched`)

1. Executable `#guard` checks on `m5Sched_fns` (`6` fns), `m5SchedModule.checkAcyclic`,
   `m5SchedModule.exits`, `m5SchedSpecTable` (`10` rows, `noExit = true`), `PrintCpp.ppTModule`,
   `PrintQbe.module`, and `Fn.legal` legality across `aarch64`, `scalar64`, `x64AVX512`, and
   `x64AVX2`.
2. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `m5SchedEnv`, zero SAT/model proofs)
   across all `6` scheduler functions (`full_log10_q16`, `full_scale_delta_m5`, `full_ema_update`,
   `full_rephase`, `full_switch_mode`, `full_restart_due`).
3. Single-line `#print axioms` audit across all exported `FullM5Sched`,
   `FullM5SchedLemmas`, and NV theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatM5SchedTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_ema_update_body full_rephase_body full_switch_mode_body full_restart_due_body
open LeanQbe.T.Examples.Kissat.FullM5Sched
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` sanity checks -/

#guard m5Sched_fns.length == 6
#guard m5Sched_fns.map Fn.name ==
  [ "full_log10_q16", "full_scale_delta_m5", "full_ema_update",
    "full_rephase", "full_switch_mode", "full_restart_due" ]
#guard m5SchedModule.checkAcyclic == true
#guard m5SchedModule.exits.isEmpty == true
#guard m5SchedSpecTable.length == 10
#guard m5SchedSpecTable.all (·.noExit) == true
#guard (PrintCpp.ppTModule m5SchedModule).isOk == true
#guard (PrintQbe.module m5SchedModule).isOk == true
#guard m5Sched_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m5Sched_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m5Sched_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m5Sched_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `m5SchedEnv`) -/

private theorem nvOneLitF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvOneLitMem_sep : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
  rw [sep_emp]; exact nvOneLitMem_ok

/-- Focused-mode (`stable = 0#64`, empty trail) `FullState` on `nvOneLitCfg` for `full_rephase`. -/
def nvRephaseState : FullState :=
  { nvOneLitState with
    core :=
      { nvOneLitState.core with
        vals := [0#8, 0#8]
        trail_end := 0
        propagated := 0 } }

/-- Concrete `Mem 64` carrying `FullCoreInv nvOneLitCfg nvOneLitF0 nvRephaseState`. -/
def nvRephaseMem : Mem 64 :=
  storeMem (storeMem (storeMem (storeMem nvOneLitMem
    i8 (nvOneLitCfg.pVals + 0#64) 0#8)
    i8 (nvOneLitCfg.pVals + 1#64) 0#8)
    i64 (nvOneLitCfg.hdr + 144) 0#64)
    i64 (nvOneLitCfg.hdr + 152) 0#64

private theorem nvRephase_lengths : nvRephaseState.LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with
     vals_len := rfl
     trail_end_le := Nat.zero_le _
     propagated_le := Nat.zero_le _ },
   nvOneLit_lengths.scratch_ok⟩

private theorem nvRephase_inv : FullCoreInv nvOneLitCfg nvOneLitF0 nvRephaseState := by
  refine ⟨nvRephase_lengths, [[0], [1]], fullWitnessInv_empty
    (hext := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩)
    (hinc := rfl) (hal := rfl)
    (hwvec := fun l hl => by
      have hcv : nvRephaseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (hte := rfl) (hcl := rfl) (hft0 := rfl)
    (hvals := fun l hl => by
      have hcv : nvRephaseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl)⟩

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics in
private theorem nvRephaseMem_ok : FullMem nvOneLitCfg nvRephaseState nvRephaseMem := by
  have h1 := (FullArenaTactics.store_full_vals (i := 0) (v := 0#8) (by decide) nvOneLitMem_sep).2
  have h2 := (FullArenaTactics.store_full_vals (i := 1) (v := 0#8) (by decide) h1).2
  have h3 := (FullArenaTactics.store_full_trail_end (v := 0) (by decide) h2).2
  have h4 := (FullArenaTactics.store_full_propagated (v := 0) (by decide) h3).2
  rw [sep_emp] at h4
  simpa only [nvRephaseState, nvRephaseMem, nvOneLitState,
    show (([1#8, 0xFF#8] : List (BitVec 8)).set 0 0#8).set 1 0#8 = [0#8, 0#8] from rfl] using h4

/-- Closed pure `Mem 64` preservation & range witness for `full_log10_q16` (`X := False`). -/
theorem full_log10_q16_nv (x : BitVec 64) (m : Mem 64) :
    Func.wp m5SchedEnv full_log10_q16_body (x, ()) m
      (fun (r, ()) m' => r.toNat < 20 * 65536 ∧ (10 ≤ x.toNat → 65536 ≤ r.toNat) ∧ m' = m)
      (fun _ _ _ _ => False) :=
  full_log10_q16_wp m5SchedEnv (x, ()) m _ _ fun _ hr hge => ⟨hr, hge, rfl⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for `full_scale_delta_m5` on
`nvOneLitMem`. -/
theorem full_scale_delta_m5_nv :
    Func.wp m5SchedEnv full_scale_delta_m5_body (nvOneLitCfg.hdr, 500#64, ()) nvOneLitMem
      (fun (_r, ()) m' => m' = nvOneLitMem ∧ nvOneLitF0.Unsat)
      (fun _ _ _ _ => False) :=
  m5Sched_tableImpl.2.1.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun _ => ⟨rfl, nvOneLitF0_unsat⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for `full_ema_update` on `nvOneLitMem`. -/
theorem full_ema_update_nv :
    Func.wp m5SchedEnv full_ema_update_body (nvOneLitCfg.hdr, 4#64, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m5Sched_tableImpl.2.2.1.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun () s' m' hco hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvOneLitF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for focused-mode `full_rephase` on
`nvRephaseMem`. -/
theorem full_rephase_nv :
    Func.wp m5SchedEnv full_rephase_body (nvOneLitCfg.hdr, ()) nvRephaseMem
      (fun () m' => ∃ s',
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level ≤ nvRephaseState.core.cur_level ∧
        s'.core.fuel.toNat ≤ nvRephaseState.core.fuel.toNat ∧
        FullExtScratchPres nvRephaseState s' ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvRephaseState ⋆ emp) nvRephaseMem := by
    rw [sep_emp]; exact nvRephaseMem_ok
  exact m5Sched_tableImpl.2.2.2.1.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvRephaseState, emp, rfl, nvRephase_inv, hm,
      fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' m' hinv _ hcl hfl hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hinv, hcl, hfl, hpr, nvOneLitF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for `full_switch_mode` on
`nvOneLitMem`. -/
theorem full_switch_mode_nv :
    Func.wp m5SchedEnv full_switch_mode_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s',
        PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m5Sched_tableImpl.2.2.2.2.1.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun () s' m' hco hln hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hco, hln, hpr, nvOneLitF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for `full_restart_due` on
`nvOneLitMem`. -/
theorem full_restart_due_nv :
    Func.wp m5SchedEnv full_restart_due_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        (r = 0#64 ∨ r = 1#64) ∧ PreservesCoreSlice FullState.core nvOneLitState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullExtScratchPres nvOneLitState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m5Sched_tableImpl.2.2.2.2.2.1.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvOneLitMem_sep,
      fun (r, ()) s' m' hco hln ⟨hr, hpr⟩ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hr, hco, hln, hpr, nvOneLitF0_unsat, hm'⟩⟩

end LeanQbeTest.T.KissatM5SchedTest

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev m5s_log10_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_log10_q16_wf
abbrev m5s_sc_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_scale_delta_m5_wf
abbrev m5s_ema_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_ema_update_wf
abbrev m5s_reph_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_rephase_wf
abbrev m5s_sw_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_switch_mode_wf
abbrev m5s_rst_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_restart_due_wf
abbrev m5s_fns_wf := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5Sched_fns_wf
abbrev m5s_acyc := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5Sched_acyclic
abbrev m5s_reph_st := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5RephaseSpec_of_stable
abbrev m5s_log10_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_log10_q16_wp
abbrev m5s_sc_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_scale_delta_m5_wp
abbrev m5s_ema_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_ema_update_wp
abbrev m5s_reph_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_rephase_wp
abbrev m5s_sw_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_switch_mode_wp
abbrev m5s_rst_wp := @LeanQbe.T.Examples.Kissat.FullM5Sched.full_restart_due_wp
abbrev m5s_noExit_tbl := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5SchedSpecTable_noExit
abbrev m5s_noExit := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5Sched_noExit
abbrev m5s_tableImpl := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5Sched_tableImpl
abbrev m5s_moduleOk := @LeanQbe.T.Examples.Kissat.FullM5Sched.m5Sched_moduleOk
abbrev m5s_log10_nv := @LeanQbeTest.T.KissatM5SchedTest.full_log10_q16_nv
abbrev m5s_sc_nv := @LeanQbeTest.T.KissatM5SchedTest.full_scale_delta_m5_nv
abbrev m5s_ema_nv := @LeanQbeTest.T.KissatM5SchedTest.full_ema_update_nv
abbrev m5s_reph_nv := @LeanQbeTest.T.KissatM5SchedTest.full_rephase_nv
abbrev m5s_sw_nv := @LeanQbeTest.T.KissatM5SchedTest.full_switch_mode_nv
abbrev m5s_rst_nv := @LeanQbeTest.T.KissatM5SchedTest.full_restart_due_nv

#print axioms m5s_log10_wf
#print axioms m5s_sc_wf
#print axioms m5s_ema_wf
#print axioms m5s_reph_wf
#print axioms m5s_sw_wf
#print axioms m5s_rst_wf
#print axioms m5s_fns_wf
#print axioms m5s_acyc
#print axioms m5s_reph_st
#print axioms m5s_log10_wp
#print axioms m5s_sc_wp
#print axioms m5s_ema_wp
#print axioms m5s_reph_wp
#print axioms m5s_sw_wp
#print axioms m5s_rst_wp
#print axioms m5s_noExit_tbl
#print axioms m5s_noExit
#print axioms m5s_tableImpl
#print axioms m5s_moduleOk
#print axioms m5s_log10_nv
#print axioms m5s_sc_nv
#print axioms m5s_ema_nv
#print axioms m5s_reph_nv
#print axioms m5s_sw_nv
#print axioms m5s_rst_nv
