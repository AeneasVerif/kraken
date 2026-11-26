/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
public import LeanQbe.T.Examples.Kissat.FullM7HotTernaryProof
public import LeanQbe.T.Examples.Kissat.FullM7HotHop1Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullBvaHeap
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import LeanQbe.T.Examples.Kissat.FullM7BveGates
import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6Sweep
import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM5HeurCore
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity `PatchModule` Splice Bridges (`FullM8CoreParityProofSplice`)

Closes the three compositional `PatchModule` / `FullM7Splice` bridges over `FullM8CoreParityProof`:
1. `m8CoreParityHotModule` (`435` fns): splices `m7HasTernaryFn` (`FullM7HotTernary`) onto
   `m8CoreParityModule` with `ModuleOk`, `TableImpl`, `solve_bytes_sound`, and `unsat_nv`.
2. `m8HotHop1BridgeModule` (`13` fns): splices `m7Hop1Fn` + `m7Hop2Fn` (`FullM7HotHop1`) onto
   `FullBvaHeap.bvaHeapModule` with `checkAcyclic` and `ModuleOk`.
3. `m8SweepV2CoreParityModule` (`471` fns): patches `m8CoreParityRepls ++ [m7HasTernaryFn]` +
   `m8CoreParityBefores` onto `FullM8SweepV2.m8FidV123t2Module` with `SpecTable`, `ModuleOk`,
   `TableImpl`, `solve_bytes_sound`, and `unsat_nv`.

Zero `@[expose]` tags, `0` `*Lemmas*` in `public import`, UNSAT-only (`0` SAT model proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7HotTernary
open LeanQbe.T.Examples.Kissat.FullM7HotHop1
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM6Sweep

private abbrev spliceRowSig (e : SpecEntry) : SigEntry := (e.name, e.as, e.rs)

/-! ## 1. `FullM8CoreParity` + `FullM7HotTernary` (`m8CoreParityHotModule`, `435` fns) -/

/-- `435`-function module splicing `m7HasTernaryFn` (`FullM7HotTernary`) onto
`m8CoreParityModule`. -/
def m8CoreParityHotFns : List Fn :=
  FullM7Splice.spliceFns [m7HasTernaryFn] m8CoreParityFns

/-- `435`-function module with hot `full_has_ternary` (`0` externs, `0` exits). -/
def m8CoreParityHotModule : LeanQbe.T.Module :=
  { m8CoreParityModule with fns := m8CoreParityHotFns }

private theorem m8cp_hot_replSigs :
    ∀ r ∈ ([m7HasTernaryFn] : List Fn), ∀ f ∈ m8CoreParityFns, r.name = f.name → r.sig = f.sig := by
  have hi243 : m7FidelityFns[243]?.map Fn.sig =
      some ("full_has_ternary", [i64, i32, i32, i32], [.bool]) := by
    t_kernel_rfl
  obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map hi243
  have hgMem : g ∈ m8CoreParityFns := by
    rw [m8CoreParityFns_eq_patchFns]
    refine m8cp_patchFns_mem_of_ne (List.mem_of_getElem? hg) fun r hr => ?_
    have hn : r.name ∈ m8CoreParityRepls.map Fn.name := List.mem_map_of_mem hr
    have hgNm : g.name = "full_has_ternary" := congrArg Prod.fst hsg
    rw [hgNm]
    exact fun h => absurd (h ▸ hn) (by decide)
  intro r hr f hf hnm
  rcases List.mem_singleton.mp hr with rfl
  have hfg := m8cp_nodup_name_eq Fn.name m8CoreParityFns_names_nodup hf hgMem
    (hnm.symm.trans (congrArg Prod.fst hsg).symm)
  subst hfg; exact hsg.symm

theorem m8CoreParityHot_acyclic : m8CoreParityHotModule.checkAcyclic = true := by
  dsimp only [m8CoreParityHotModule, m8CoreParityHotFns]
  change ({ m8CoreParityModule with
      fns := FullM7Splice.spliceFns [m7HasTernaryFn] m8CoreParityModule.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  refine spliceModule_checkAcyclic (M := m8CoreParityModule) m8CoreParity_acyclic
    m8cp_hot_replSigs ?_
  intro pre f post r hsplit hr _hnm
  rcases List.mem_singleton.mp hr with rfl
  exact fn_checkCallsOk_mono (fun _ h => by simp at h)
    (by decide : m7HasTernaryFn.checkCallsOk [] [] = true)

theorem m8CoreParityHot_moduleOk : ModuleOk m8CoreParityEnv m8CoreParityHotModule := by
  dsimp only [m8CoreParityHotModule, m8CoreParityHotFns]
  change ModuleOk m8CoreParityEnv
    { m8CoreParityModule with
      fns := FullM7Splice.spliceFns [m7HasTernaryFn] m8CoreParityModule.fns }
  refine spliceModule_moduleOk_sameEnv m8CoreParity_moduleOk m8CoreParityHot_acyclic ?_ ?_
  · intro r hr; rcases List.mem_singleton.mp hr with rfl; exact m7HasTernaryFn_wf
  · intro r hr xs m Q X hsp
    rcases List.mem_singleton.mp hr with rfl
    exact m7HasTernaryFn_wp m8CoreParityEnv xs m Q X
      (m8cp_m7FidBase_elim (fun hb => hb) m8cp_hasTernary_mem
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp)

theorem m8CoreParityHot_tableImpl :
    TableImpl m8CoreParityEnv m8CoreParityHotModule.fns m8CoreParitySpecTable := by
  have hSigs :
      m8CoreParitySpecTable.map spliceRowSig = m8CoreParityHotModule.fns.map Fn.sig := by
    change m8CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      (FullM7Splice.spliceFns [m7HasTernaryFn] m8CoreParityFns).map Fn.sig
    rw [m8CoreParitySpecTable_sigs]
    exact (spliceFns_sigs m8cp_hot_replSigs).symm
  exact tableImpl_of_moduleOk m8CoreParityHot_moduleOk hSigs
    m8CoreParitySpecTable_nodup (fun _ _ _ _ _ _ ht => m8CoreParityEnv_of_specTable ht)

theorem m8CoreParityHot_solveBytes_mem : m6oSolveBytesFn ∈ m8CoreParityHotModule.fns := by
  change m6oSolveBytesFn ∈ FullM7Splice.spliceFns [m7HasTernaryFn] m8CoreParityFns
  exact spliceFns_mem_of_ne m8CoreParity_solveBytes_mem fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; decide

/-- Top-level unconditional byte-level UNSAT soundness of `m8CoreParityHotModule` (`435` fns). -/
theorem m8CoreParityHot_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of m8CoreParityHot_moduleOk m8CoreParityHot_solveBytes_mem
    (fun _ _ _ _ hs => m8CoreParityEnv_solve_bytes_iff.mpr hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `m8CoreParityHotModule`. -/
theorem m8CoreParityHot_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for
`m8CoreParityHotModule`. -/
theorem m8CoreParityHot_unsat_nv :
    Func.wp m8CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of m8CoreParityHot_moduleOk m8CoreParityHot_solveBytes_mem
    (fun _ _ _ _ hs => m8CoreParityEnv_solve_bytes_iff.mpr hs)

/-! ## 2. `FullBvaHeap` + `FullM7HotHop1` Splice Bridge (`m8HotHop1BridgeModule`, `13` fns) -/

/-- `13`-function factoring bridge splicing `m7Hop1Fn` + `m7Hop2Fn` (`FullM7HotHop1`) onto
`FullBvaHeap.bvaHeapModule`. -/
def m8HotHop1BridgeFns : List Fn :=
  FullM7Splice.spliceFns [m7Hop1Fn, m7Hop2Fn] bvaHeapModule.fns

/-- `13`-function factoring bridge module over `FullBvaHeap.bvaHeapModule`. -/
def m8HotHop1BridgeModule : LeanQbe.T.Module :=
  { bvaHeapModule with fns := m8HotHop1BridgeFns }

private theorem m8cp_hop_replSigs :
    ∀ r ∈ ([m7Hop1Fn, m7Hop2Fn] : List Fn), ∀ f ∈ bvaHeapModule.fns,
      r.name = f.name → r.sig = f.sig := by
  have hnd : (bvaHeapModule.fns.map Fn.name).Nodup := by
    have hchk := bvaHeap_acyclic
    simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hchk
    have hn := LeanQbe.T.Module.namesNodup_of_checkNamesNodup hchk.1
    change (bvaHeapModule.fns.map Fn.name ++ bvaHeapModule.externs.map Extern.name).Nodup at hn
    exact (List.nodup_append.mp hn).1
  have h1 : bvaHeapModule.fns[1]?.map Fn.sig = some ("full_bva_hop1", [i64, i32, i32], [i64]) :=
    rfl
  have h2 : bvaHeapModule.fns[2]?.map Fn.sig = some ("full_bva_hop2", [i64, i32, i32], [i64]) :=
    rfl
  obtain ⟨g1, hg1, hs1⟩ := m8cp_sig_of_map h1
  obtain ⟨g2, hg2, hs2⟩ := m8cp_sig_of_map h2
  intro r hr f hf hnm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hfg := m8cp_nodup_name_eq Fn.name hnd hf (List.mem_of_getElem? hg1)
      (hnm.symm.trans (congrArg Prod.fst hs1).symm)
    subst hfg; exact hs1.symm
  · have hfg := m8cp_nodup_name_eq Fn.name hnd hf (List.mem_of_getElem? hg2)
      (hnm.symm.trans (congrArg Prod.fst hs2).symm)
    subst hfg; exact hs2.symm

theorem m8HotHop1Bridge_acyclic : m8HotHop1BridgeModule.checkAcyclic = true := by
  dsimp only [m8HotHop1BridgeModule, m8HotHop1BridgeFns]
  refine spliceModule_checkAcyclic (M := bvaHeapModule) bvaHeap_acyclic m8cp_hop_replSigs ?_
  have hnd : (bvaHeapModule.fns.map Fn.name).Nodup := by
    have hchk := bvaHeap_acyclic
    simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hchk
    have hn := LeanQbe.T.Module.namesNodup_of_checkNamesNodup hchk.1
    change (bvaHeapModule.fns.map Fn.name ++ bvaHeapModule.externs.map Extern.name).Nodup at hn
    exact (List.nodup_append.mp hn).1
  have h1 : bvaHeapModule.fns[1]?.map Fn.sig = some ("full_bva_hop1", [i64, i32, i32], [i64]) :=
    rfl
  have h2 : bvaHeapModule.fns[2]?.map Fn.sig = some ("full_bva_hop2", [i64, i32, i32], [i64]) :=
    rfl
  obtain ⟨g1, hg1, hs1⟩ := m8cp_sig_of_map h1
  obtain ⟨g2, hg2, hs2⟩ := m8cp_sig_of_map h2
  intro pre f post r hsplit hr hnm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hc : m7Hop1Fn.checkCallsOk [] [] = true := by t_kernel_rfl
    exact fn_checkCallsOk_mono (fun _ h => False.elim (List.not_mem_nil h)) hc
  · have hc : m7Hop2Fn.checkCallsOk
        [("full_bva_hop1", [i64, i32, i32], [i64])] [] = true := by t_kernel_rfl
    refine fn_checkCallsOk_mono (fun s hs => ?_) hc
    simp only [List.mem_singleton] at hs; subst hs
    exact List.mem_append_left _ (hs1 ▸ sig_mem_pre_of_lt_idx hnd hsplit hg2
      (hnm.symm.trans (congrArg Prod.fst hs2).symm) hg1 (by decide))

theorem m8HotHop1Bridge_moduleOk : ModuleOk bvaHeapEnv m8HotHop1BridgeModule := by
  dsimp only [m8HotHop1BridgeModule, m8HotHop1BridgeFns]
  change ModuleOk bvaHeapEnv
    { bvaHeapModule with
      fns := FullM7Splice.spliceFns [m7Hop1Fn, m7Hop2Fn] bvaHeapModule.fns }
  refine spliceModule_moduleOk_sameEnv bvaHeap_moduleOk m8HotHop1Bridge_acyclic ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact m7Hop1Fn_wf
    · exact m7Hop2Fn_wf
  · intro r hr xs m Q X hsp
    have hnd : (bvaHeapSpecTable.map SpecEntry.name).Nodup := bvaHeapSpecTable_names_nodup
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hmem : (⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩ :
          SpecEntry) ∈ bvaHeapSpecTable := by simp [bvaHeapSpecTable]
      obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim hnd hmem hsp
      exact m7Hop1Fn_wp bvaHeapEnv xs m Q X hc
    · have hmem : (⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩ :
          SpecEntry) ∈ bvaHeapSpecTable := by simp [bvaHeapSpecTable]
      obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim hnd hmem hsp
      have hHop1 : ∀ a m Q X, fullBvaHop1Spec a m Q X →
          bvaHeapEnv "full_bva_hop1" [i64, i32, i32] [i64] a m Q X := fun a m Q X hs =>
        Env.ofTable_of_mem (by simp [bvaHeapSpecTable] :
          (⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩ : SpecEntry) ∈
            bvaHeapSpecTable) hnd hs
      exact m7Hop2Fn_wp bvaHeapEnv hHop1 xs m Q X hc

/-! ## 3. `FullM8SweepV2` + `FullM8CoreParity` (`m8SweepV2CoreParity`, `471` fns) -/

/-- `8`-function replacement list uniting `m8CoreParityRepls` (`7`) + `m7HasTernaryFn` (`1`). -/
def m8SweepV2CoreParityRepls : List Fn :=
  m8CoreParityRepls ++ [m7HasTernaryFn]

/-- `471`-function combined `M8` parity + revived `V3t2` sweep module body (`449 + 22`). -/
def m8SweepV2CoreParityFns : List Fn :=
  PatchModule.patchFns m8SweepV2CoreParityRepls m8CoreParityBefores m8FidV123t2Fns

/-- Closed `471`-function combined `M8` module over `FullM8SweepV2.m8FidV123t2Module`
(`0` externs, `0` exits). -/
def m8SweepV2CoreParityModule : LeanQbe.T.Module :=
  PatchModule.patchModule m8FidV123t2Module m8SweepV2CoreParityRepls m8CoreParityBefores

/-- Base `413`-row `V12` specification table over `m7FidSpecTable`. -/
def m8SwV12SpecTable : List SpecEntry :=
  m7FidSpecTable.map fun e =>
    if e.name == "full_extend_push2" then
      ⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec, true⟩
    else if e.name == "full_cong_enq_var" then
      ⟨"full_cong_enq_var", [i64, i64, i32], [], m8CongEnqVarSpec, true⟩
    else if e.name == "full_cong_eval_gate" then
      ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m8CongEvalGateSpec, true⟩
    else if e.name == "full_cong_worklist" then
      ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m8CongWorklistSpec, true⟩
    else e

/-- Pre-parity `449`-row `FullM8SweepV2` specification table. -/
def m8SwBaseSpecTable : List SpecEntry :=
  PatchModule.patchRows [] [("full_sweep_dense_m6", m8SweepEnvRows)] m8SwV12SpecTable

/-- Unconditional `471`-row specification table matching `m8SweepV2CoreParityFns`. -/
def m8SweepV2CoreParitySpecTable : List SpecEntry :=
  PatchModule.patchRows (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook)
    (m8CoreParityBeforeRows m8BveHook) m8SwBaseSpecTable

/-- Canonical closed unconditional `Env` for `m8SweepV2CoreParityModule` (`471` fns). -/
def m8SweepV2CoreParityEnv : Env :=
  M8CoreParityEnv m8BveHook m8FidV123t2Env

private theorem m8cp_sw_replSigs :
    ∀ r ∈ m8SweepV2CoreParityRepls, ∀ g ∈ m8FidV123t2Fns, r.name = g.name → r.sig = g.sig := by
  have hi135 : m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], []) := by
    t_kernel_rfl
  have hi243 : m8FidV123t2Fns[243]?.map Fn.sig =
      some ("full_has_ternary", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
  have hi374 : m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64]) := by
    t_kernel_rfl
  have hi375 : m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64]) := by
    t_kernel_rfl
  have hi415 : m8FidV123t2Fns[415]?.map Fn.sig =
      some ("full_bve_var_key_m7", [i64, i32], [i64]) := by t_kernel_rfl
  have hi438 : m8FidV123t2Fns[438]?.map Fn.sig =
      some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := by t_kernel_rfl
  have hi440 : m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64]) := by
    t_kernel_rfl
  have hi444 : m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64]) := by
    t_kernel_rfl
  obtain ⟨g135, hg135, hs135⟩ := m8cp_sig_of_map hi135
  obtain ⟨g243, hg243, hs243⟩ := m8cp_sig_of_map hi243
  obtain ⟨g374, hg374, hs374⟩ := m8cp_sig_of_map hi374
  obtain ⟨g375, hg375, hs375⟩ := m8cp_sig_of_map hi375
  obtain ⟨g415, hg415, hs415⟩ := m8cp_sig_of_map hi415
  obtain ⟨g438, hg438, hs438⟩ := m8cp_sig_of_map hi438
  obtain ⟨g440, hg440, hs440⟩ := m8cp_sig_of_map hi440
  obtain ⟨g444, hg444, hs444⟩ := m8cp_sig_of_map hi444
  intro r hr f hf hnm
  simp only [m8SweepV2CoreParityRepls, m8CoreParityRepls, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg135) (hnm.symm.trans (congrArg Prod.fst hs135).symm)) ▸ hs135.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg374) (hnm.symm.trans (congrArg Prod.fst hs374).symm)) ▸ hs374.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg375) (hnm.symm.trans (congrArg Prod.fst hs375).symm)) ▸ hs375.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg415) (hnm.symm.trans (congrArg Prod.fst hs415).symm)) ▸ hs415.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg438) (hnm.symm.trans (congrArg Prod.fst hs438).symm)) ▸ hs438.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg440) (hnm.symm.trans (congrArg Prod.fst hs440).symm)) ▸ hs440.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg444) (hnm.symm.trans (congrArg Prod.fst hs444).symm)) ▸ hs444.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg243) (hnm.symm.trans (congrArg Prod.fst hs243).symm)) ▸ hs243.symm

private theorem m8cp_sw_fast_acyclic :
    m8SweepV2CoreParityModule.namesNodup ∧
    (∀ pre fn post, m8SweepV2CoreParityModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ m8FidV123t2Module.externs.map Extern.sig)
        m8FidV123t2Module.exits) :=
  PatchModule.patchModule_checkAcyclic_fast m8FidV123t2_acyclic (by t_kernel_rfl) (by t_kernel_rfl)
    m8cp_sw_replSigs

theorem m8SweepV2CoreParityFns_names_nodup : (m8SweepV2CoreParityFns.map Fn.name).Nodup := by
  have hnd := m8cp_sw_fast_acyclic.1
  change (m8SweepV2CoreParityFns.map Fn.name ++
    m8FidV123t2Module.externs.map Extern.name).Nodup at hnd
  exact (List.nodup_append.mp hnd).1

private theorem m8cp_sw_v12Table_sigs :
    m8SwV12SpecTable.map spliceRowSig = m8FidV12Fns.map Fn.sig := by
  have hFns : m8FidV12Fns.map Fn.sig = m7FidelityFns.map Fn.sig :=
    m8FidV12Fns_sigs
  have hm7 : m7FidSpecTable.map spliceRowSig = m7FidelityFns.map Fn.sig := by
    change m7FidSpecTable.map (fun e => (e.name, e.as, e.rs)) = _
    exact m7FidSpecTable_sigs
  rw [hFns, ← hm7]
  have hf1 : (m7FidelityFns.find? (·.name == "full_extend_push2")).map Fn.sig =
      some ("full_extend_push2", [i64, i32, i32], [.bool]) := by t_kernel_rfl
  have hf2 : (m7FidelityFns.find? (·.name == "full_cong_enq_var")).map Fn.sig =
      some ("full_cong_enq_var", [i64, i64, i32], []) := by t_kernel_rfl
  have hf3 : (m7FidelityFns.find? (·.name == "full_cong_eval_gate")).map Fn.sig =
      some ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]) := by t_kernel_rfl
  have hf4 : (m7FidelityFns.find? (·.name == "full_cong_worklist")).map Fn.sig =
      some ("full_cong_worklist", [i64, i64, i64, i64], [i64]) := by t_kernel_rfl
  have hSigOf : ∀ {nm : Sym} {s : SigEntry},
      ((m7FidelityFns.find? (·.name == nm)).map Fn.sig = some s) →
      ∀ e ∈ m7FidSpecTable, e.name = nm → spliceRowSig e = s := by
    intro nm s hf e he hnm
    cases hfi : m7FidelityFns.find? (·.name == nm) with
    | none => simp [hfi] at hf
    | some g =>
      simp only [hfi, Option.map_some, Option.some.injEq] at hf
      have hre : spliceRowSig e ∈ m7FidSpecTable.map spliceRowSig := List.mem_map_of_mem he
      rw [hm7] at hre
      rcases List.mem_map.mp hre with ⟨g', hg', hgeg'⟩
      have hfs := beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == nm) hfi)
      have h1 : g'.name = e.name := congrArg Prod.fst hgeg'
      have heNm : g'.name = g.name := h1.trans (hnm.trans hfs.symm)
      have hgeq := m8cp_nodup_name_eq Fn.name m7FidelityFns_names_nodup hg'
        (List.mem_of_find?_eq_some hfi) heNm
      rw [← hgeg', hgeq, hf]
  unfold m8SwV12SpecTable
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  dsimp only [Function.comp_def]
  split
  · rename_i h1; exact (hSigOf hf1 e he (beq_iff_eq.mp h1)).symm
  · split
    · rename_i h2; exact (hSigOf hf2 e he (beq_iff_eq.mp h2)).symm
    · split
      · rename_i h3; exact (hSigOf hf3 e he (beq_iff_eq.mp h3)).symm
      · split
        · rename_i h4; exact (hSigOf hf4 e he (beq_iff_eq.mp h4)).symm
        · rfl

private theorem m8cp_swBase_sigs :
    m8SwBaseSpecTable.map spliceRowSig = m8FidV123t2Fns.map Fn.sig := by
  have hEq : m8FidV123t2Fns =
      PatchModule.patchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Fns := by
    rw [m8FidV123t2Fns_eq_patch]
    unfold mfPatchFns PatchModule.patchFns
    induction m8FidV12Fns with
    | nil => rfl
    | cons a t ih =>
      simp only [List.flatMap_cons]
      have hi : PatchModule.patchInsAt m8FidV123t2Befores a =
          mfPatchInsAt m8FidV123t2Befores a := by
        dsimp only [PatchModule.patchInsAt, mfPatchInsAt, m8FidV123t2Befores]
        by_cases h1 : ("full_sweep_dense_m6" == a.name)
        · have h1e := beq_iff_eq.mp h1
          rw [← h1e]
          simp only [beq_self_eq_true, List.find?, List.filterMap_cons, ↓reduceIte,
            List.filterMap_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
        · have h1n : "full_sweep_dense_m6" ≠ a.name := fun h => h1 (beq_iff_eq.mpr h)
          simp only [m8cp_sym_ne_beq h1n, List.find?, List.filterMap_cons, Bool.false_eq_true,
            ↓reduceIte, List.filterMap_nil, List.flatten_nil]
      rw [hi, ih]
  have hSwSigs : m8SweepEnvRows.map spliceRowSig = m8SweepV2Helpers.map Fn.sig := by t_kernel_rfl
  rw [m8SwBaseSpecTable, hEq]
  refine patchRows_sigs_eq_patchFns_self m8cp_sw_v12Table_sigs ?_ (fun _ hm => nomatch hm) ?_
  · intro e f hnm
    dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt, m8FidV123t2Befores]
    rw [hnm]
    by_cases h1 : ("full_sweep_dense_m6" == f.name)
    · have h1e := beq_iff_eq.mp h1
      rw [← h1e]
      simp only [List.find?, beq_self_eq_true]
      exact hSwSigs
    · have h1n : "full_sweep_dense_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
      simp only [List.find?, m8cp_sym_ne_beq h1n, List.map_nil]
  · intro r hr f hf hnm
    rcases List.mem_singleton.mp hr with rfl
    have hfi : (m8FidV12Fns.find? (·.name == "full_sweep_dense_m6")).map Fn.sig =
        some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := by t_kernel_rfl
    cases hfd : m8FidV12Fns.find? (·.name == "full_sweep_dense_m6") with
    | none => simp [hfd] at hfi
    | some g =>
      simp only [hfd, Option.map_some, Option.some.injEq] at hfi
      have hfs :=
        beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == "full_sweep_dense_m6") hfd)
      have hfg := m8cp_nodup_name_eq Fn.name m8FidV12Fns_names_nodup hf
        (List.mem_of_find?_eq_some hfd) (hnm.symm.trans hfs.symm)
      rw [hfg, hfi] <;> rfl

theorem m8SweepV2CoreParitySpecTable_sigs :
    m8SweepV2CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m8SweepV2CoreParityFns.map Fn.sig := by
  change (PatchModule.patchRows (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook)
    (m8CoreParityBeforeRows m8BveHook) m8SwBaseSpecTable).map spliceRowSig =
    m8SweepV2CoreParityFns.map Fn.sig
  refine patchRows_sigs_eq_patchFns_self m8cp_swBase_sigs (m8cp_befores_sigs_match m8BveHook) ?_
    m8cp_sw_replSigs
  exact m8cp_replRows_sigs_of_fns m8BveHook m8cp_swBase_sigs m8FidV123t2Fns_names_nodup
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], [])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[137]?.map Fn.sig = some ("full_min_shrink", [i64], [])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[438]?.map Fn.sig = some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64])))

theorem m8SweepV2CoreParitySpecTable_length :
    m8SweepV2CoreParitySpecTable.length = 471 := by
  rw [rowSigs_eq_fnSigs_len m8SweepV2CoreParitySpecTable_sigs]
  t_kernel_rfl

theorem m8SweepV2CoreParitySpecTable_noExit :
    m8SweepV2CoreParitySpecTable.all SpecEntry.noExit = true := by
  have hv12No : m8SwV12SpecTable.all SpecEntry.noExit = true := by
    rw [List.all_eq_true]
    intro x hx
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    have hno := List.all_eq_true.mp m7FidSpecTable_noExit e he
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · exact hno
  have hBaseNo : m8SwBaseSpecTable.all SpecEntry.noExit = true := by
    refine patchRows_noExit hv12No rfl fun p hp => ?_
    rcases List.mem_singleton.mp hp with rfl
    exact List.all_eq_true.mpr m8SweepEnvRows_noExit
  refine patchRows_noExit hBaseNo ?_ ?_
  · simp only [m8CoreParityReplRows, m8cpRewireRows, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true]
  · intro p hp
    simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> first
      | exact m8MinHelperRows_noExit | exact m8BveHook.helperRows_noExit

theorem m8SweepV2CoreParitySpecTable_nodup :
    (m8SweepV2CoreParitySpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup m8SweepV2CoreParitySpecTable_sigs m8SweepV2CoreParityFns_names_nodup

private theorem m8cp_sw_noExit_names :
    (["full_extend_push2", "full_cong_enq_var", "full_cong_eval_gate",
      "full_cong_worklist"] : List Sym).all
      (fun nm => !((mfExtraRows.map SpecEntry.name).contains nm)) = true := by
  t_kernel_rfl

private theorem m8cp_m7Fid_to_m8Sw :
    ∀ f as bs xs m Q X, m7FidelityEnv f as bs xs m Q X → m8FidV123t2Env f as bs xs m Q X := by
  intro f as bs xs m Q X h
  by_cases hf : f = "full_extend_push2"
  · subst hf
    generalize hnm : ("full_extend_push2" : Sym) = nm at h
    cases h with
    | base _ hb =>
      subst hnm
      have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
      obtain ⟨has, hrs, heff⟩ := m8cp_ofTable_sig_elim m7FidBaseTable_nodup hc2.extendPush2 hb
      dsimp only at has hrs; cases has; cases hrs
      rcases heff with ⟨c, s, R, hpre, hlen, hm, hQ⟩
      exact .extPush2 ⟨c, s, R, hpre, hlen, hm,
        fun r s' m' hcore hlen' ⟨h1, h2, h3, h4, _, _⟩ hm' =>
          hQ r s' m' hcore hlen' ⟨h1, h2, h3, h4⟩ hm'⟩
    | extra he =>
      have hchk := List.all_eq_true.mp m8cp_sw_noExit_names "full_extend_push2" (by decide)
      simp only [Bool.not_eq_true'] at hchk
      exact absurd (hnm ▸ m8CoreParity_ofTable_name_mem he) (by simpa using hchk)
  · exact .base (by simpa [m8SwExclNames] using hf) (.base h)

private theorem m8cp_sw_to_m7_of_ne {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h1 : nm ≠ "full_extend_push2") (h2 : nm ∉ m8SweepEnvRows.map SpecEntry.name)
    (h3 : nm ≠ "full_cong_enq_var") (h4 : nm ≠ "full_cong_eval_gate")
    (h5 : nm ≠ "full_cong_worklist") (h : m8FidV123t2Env nm as bs xs m Q X) :
    m7FidelityEnv nm as bs xs m Q X := by
  cases h with
  | base _ hv12 =>
    cases hv12 with
    | base hm7 => exact hm7
    | enqVar => exact absurd rfl h3
    | evalGate => exact absurd rfl h4
    | worklist => exact absurd rfl h5
  | extPush2 => exact absurd rfl h1
  | sweep hs => exact absurd (m8CoreParity_ofTable_name_mem hs) h2

private theorem m8cp_sw_base_to_env {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m8SwBaseSpecTable f as bs xs m Q X) :
    m8FidV123t2Env f as bs xs m Q X := by
  have hm7 : m7FidSpecTable.map spliceRowSig = m7FidelityFns.map Fn.sig := by
    change m7FidSpecTable.map (fun e => (e.name, e.as, e.rs)) = _
    exact m7FidSpecTable_sigs
  have hBefDisj : ∀ p ∈ ([("full_sweep_dense_m6", m8SweepEnvRows)] :
      List (Sym × List SpecEntry)),
      ∀ b ∈ p.2, b.name ∉ m8SwV12SpecTable.map SpecEntry.name := by
    have hn : m8SwV12SpecTable.map SpecEntry.name = m7FidelityFns.map Fn.name := by
      have hm := congrArg (List.map Prod.fst) m8cp_sw_v12Table_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hm
      rw [hm]
      have hm2 := congrArg (List.map Prod.fst) m8FidV12Fns_sigs
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm2
    rw [hn]
    intro p hp b hb hmem
    rcases List.mem_singleton.mp hp with rfl
    have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
        (fun s => !((m7FidelityFns.map Fn.name).contains s)) = true := by t_kernel_rfl
    have hchk := List.all_eq_true.mp hdisj b.name (List.mem_map_of_mem hb)
    simp only [Bool.not_eq_true'] at hchk
    exact absurd hmem (by simpa using hchk)
  rcases ofTable_patchRows_elim (rRows := []) (fun _ h => nomatch h) hBefDisj h with
    hr | hb | hbase
  · rcases hr with ⟨_, hm, _⟩; nomatch hm
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    rcases List.mem_singleton.mp hp with rfl
    exact .sweep (ofTable_of_cast hb_p m8SweepEnvRows_nodup rfl has hrs hcast)
  · rcases hbase with ⟨_, _, htbl⟩
    obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim htbl
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    by_cases h1 : (e0.name == "full_extend_push2") = true
    · simp only [h1, ↓reduceIte] at hnm has hrs hcast
      cases has; cases hrs; cases hnm
      exact .extPush2 (by
        simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m6ExtendPush2Spec, SafetySlice.spec]
          using hcast)
    · by_cases h2 : (e0.name == "full_cong_enq_var") = true
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hnm has hrs hcast
        cases has; cases hrs; cases hnm
        exact .base (by decide) (.enqVar xs m Q X
          (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongEnqVarSpec] using hcast))
      · by_cases h3 : (e0.name == "full_cong_eval_gate") = true
        · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at hnm has hrs hcast
          cases has; cases hrs; cases hnm
          exact .base (by decide) (.evalGate xs m Q X
            (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongEvalGateSpec] using
              hcast))
        · by_cases h4 : (e0.name == "full_cong_worklist") = true
          · simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hnm has hrs hcast
            cases has; cases hrs; cases hnm
            exact .base (by decide) (.worklist xs m Q X
              (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongWorklistSpec] using
                hcast))
          · simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hnm has hrs hcast
            exact m8cp_m7Fid_to_m8Sw _ _ _ xs m Q X (m7Fid_ofTable_to_env
              (ofTable_of_cast he0 m7FidSpecTable_nodup hnm has hrs hcast))

private theorem m8cp_min_help_not_in_sw :
    ∀ e ∈ m8MinHelperRows, e.name ∉ m8FidV123t2Fns.map Fn.name := by
  intro e he hmem
  have hdisj :
      (["full_min_lit_dfs_m8", "full_shrink_lower_m8", "full_shrink_blk_bool_m8"] : List String).all
        (fun nm => !((m8FidV123t2Fns.map Fn.name).any (· == nm))) = true := by
    t_kernel_rfl
  simp only [m8MinHelperRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · have h := List.all_eq_true.mp hdisj "full_min_lit_dfs_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm
  · have h := List.all_eq_true.mp hdisj "full_shrink_lower_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm
  · have h := List.all_eq_true.mp hdisj "full_shrink_blk_bool_m8" (by decide)
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h
    rcases List.mem_map.mp hmem with ⟨f, hf, hnm⟩
    exact h _ ⟨f, hf, rfl⟩ hnm

private theorem m8cp_bve_help_not_in_sw (H : M8BveHook) :
    ∀ e ∈ H.helperRows, e.name ∉ m8FidV123t2Fns.map Fn.name := by
  have hdisj : (m8BveHelpers.map Fn.name).all
      (fun nm => !((m8FidV123t2Fns.map Fn.name).contains nm)) = true := by
    t_kernel_rfl
  intro e he hmem
  have he_bve : e.name ∈ m8BveHelpers.map Fn.name := by
    rw [← m8cp_bveHelperRows_names_eq H]; exact List.mem_map_of_mem he
  have h1 := List.all_eq_true.mp hdisj e.name he_bve
  simp only [Bool.not_eq_true'] at h1
  exact absurd hmem (by simpa using h1)

theorem m8SweepV2CoreParityEnv_of_specTable {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m8SweepV2CoreParitySpecTable f as bs xs m Q X) :
    m8SweepV2CoreParityEnv f as bs xs m Q X := by
  refine m8CoreParityEnv_of_specTable_gen m8BveHook m8cp_swBase_sigs m8FidV123t2Fns_names_nodup
    (fun _ _ _ _ _ _ _ ht => m8cp_sw_base_to_env ht) m8cp_m7Fid_to_m8Sw
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], [])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[137]?.map Fn.sig = some ("full_min_shrink", [i64], [])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[438]?.map Fn.sig = some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64])))
    (m8cp_sig_exists_of_map (by t_kernel_rfl :
      m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64])))
    ?_ h
  have hnm_sw : m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) m8cp_swBase_sigs
    simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
  rw [hnm_sw]
  intro p hp b hb
  simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact m8cp_min_help_not_in_sw b hb
  · exact m8cp_bve_help_not_in_sw m8BveHook b hb

private theorem m8cp_sw_not_help (H : M8BveHook) :
    ∀ g ∈ m8FidV123t2Fns,
      g.name ∉ m8MinHelperRows.map SpecEntry.name ∧ g.name ∉ H.helperRows.map SpecEntry.name := by
  intro g hg
  have hgn : g.name ∈ m8FidV123t2Fns.map Fn.name := List.mem_map_of_mem hg
  refine ⟨fun hm => ?_, fun hb => ?_⟩
  · rcases List.mem_map.mp hm with ⟨e, he, hnm⟩
    exact m8cp_min_help_not_in_sw e he (hnm ▸ hgn)
  · rcases List.mem_map.mp hb with ⟨e, he, hnm⟩
    exact m8cp_bve_help_not_in_sw H e he (hnm ▸ hgn)

private theorem m8cp_helpers_disj_swRows :
    (m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name).all
      (fun nm => !((m8SweepEnvRows.map SpecEntry.name).contains nm)) = true := by
  t_kernel_rfl

private theorem m8cp_help_not_in_swEnv (H : M8BveHook) {nm : Sym}
    (hnm : nm ∈ m8MinHelperRows.map SpecEntry.name ∨ nm ∈ H.helperRows.map SpecEntry.name)
    {as bs xs m Q X} (hb : m8FidV123t2Env nm as bs xs m Q X) : False := by
  have hmem : nm ∈ m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name := by
    rcases hnm with h1 | h2
    · exact List.mem_append_left _ h1
    · rw [m8cp_bveHelperRows_names_eq H] at h2
      exact List.mem_append_right _ h2
  have hnot : nm ∉ ["full_extend_push2", "full_cong_enq_var", "full_cong_eval_gate",
      "full_cong_worklist"] := by
    intro h4
    have hchk : (["full_extend_push2", "full_cong_enq_var", "full_cong_eval_gate",
        "full_cong_worklist"] : List Sym).all
        (fun s => !(m8MinHelperRows.map SpecEntry.name ++ m8BveHelpers.map Fn.name).contains s) =
        true := by decide
    have h1 := List.all_eq_true.mp hchk nm h4
    simp only [Bool.not_eq_true'] at h1
    exact absurd hmem (by simpa using h1)
  have hnot_sw : nm ∉ m8SweepEnvRows.map SpecEntry.name := by
    have hchk := List.all_eq_true.mp m8cp_helpers_disj_swRows nm hmem
    simp only [Bool.not_eq_true'] at hchk
    simpa using hchk
  exact m8cp_help_not_in_m7FidEnv H hnm
    (m8cp_sw_to_m7_of_ne (fun h => hnot (by simp [h])) hnot_sw
      (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h])) hb)

private theorem m8cp_m8Sw_noCallBad :
    PatchModule.checkNoCallBad m8cpSkipNames m8CpExclNames m8FidV123t2Fns = true := by
  t_kernel_rfl

private theorem m8cp_sw_fn_137 : m8FidV123t2Fns[137]? = some m6oMinShrinkFn := by
  t_kernel_rfl
private theorem m8cp_sw_fn_149 : m8FidV123t2Fns[149]? = some m8AnalyzeFn := by
  t_kernel_rfl
private theorem m8cp_sw_fn_150 : m8FidV123t2Fns[150]? = some m8AnalyzeCoreM6Fn := by
  t_kernel_rfl
private theorem m8cp_sw_fn_418 :
    m8FidV123t2Fns[418]? = some
      ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM7BveGates.full_bve_heap_push_m7_body⟩ := by
  t_kernel_rfl
private theorem m8cp_sw_fn_421 :
    m8FidV123t2Fns[421]? = some FullM7FidelityCore.fidElimBveM7Fn := by
  t_kernel_rfl

private theorem m8cp_not_in_swRows (nm : Sym)
    (h : !((m8SweepEnvRows.map SpecEntry.name).contains nm) = true) :
    nm ∉ m8SweepEnvRows.map SpecEntry.name := by
  simp only [Bool.not_eq_true'] at h
  simpa using h

/-- Closed unconditional `471/471` `ModuleOk` certifying `m8SweepV2CoreParityModule` under
`m8SweepV2CoreParityEnv` (`0` sorry, UNSAT-only). -/
theorem m8SweepV2CoreParity_moduleOk :
    ModuleOk m8SweepV2CoreParityEnv m8SweepV2CoreParityModule := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hBaseSw : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m8FidV123t2Env f as bs xs m Q X →
      m8SweepV2CoreParityEnv f as bs xs m Q X := fun _ _ _ _ _ _ _ hne h => .base hne h
  have hBaseM7 : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      m8SweepV2CoreParityEnv f as bs xs m Q X := fun f as bs xs m Q X hne h =>
    .base hne (m8cp_m7Fid_to_m8Sw f as bs xs m Q X h)
  have hBaseToM7 : ∀ f as bs xs m Q X,
      f ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
        "full_probe_m6", "full_search_m6"] →
      m8FidV123t2Env f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X := by
    intro f as bs xs m Q X hmem h
    refine m8cp_sw_to_m7_of_ne ?_ ?_ ?_ ?_ ?_ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · have hchk : (["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
          "full_probe_m6", "full_search_m6"] : List Sym).all
          (fun s => !((m8SweepEnvRows.map SpecEntry.name).contains s)) = true := by t_kernel_rfl
      have h1 := List.all_eq_true.mp hchk f hmem
      simp only [Bool.not_eq_true'] at h1
      simpa using h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
  have hAnaToM7 : ∀ {xs m Q X}, m8FidV123t2Env "full_analyze_core_m6" [i64] [i64] xs m Q X →
      m7FidelityEnv "full_analyze_core_m6" [i64] [i64] xs m Q X := fun {xs m Q X} h =>
    m8cp_sw_to_m7_of_ne (by decide) (m8cp_not_in_swRows _ (by t_kernel_rfl))
      (by decide) (by decide) (by decide) h
  have hElimToM7 : ∀ {xs m Q X}, m8FidV123t2Env "full_elim_bve_m7" [i64, i64] [i64] xs m Q X →
      m7FidelityEnv "full_elim_bve_m7" [i64, i64] [i64] xs m Q X := fun {xs m Q X} h =>
    m8cp_sw_to_m7_of_ne (by decide) (m8cp_not_in_swRows _ (by t_kernel_rfl))
      (by decide) (by decide) (by decide) h
  have hReplWf : ∀ r ∈ m8SweepV2CoreParityRepls, r.Wf := by
    intro r hr
    rcases List.mem_append.mp hr with hr1 | hr2
    · exact m8CoreParityRepls_wf r hr1
    · rcases List.mem_singleton.mp hr2 with rfl; exact m7HasTernaryFn_wf
  have hCoreWp : ∀ xs m Q X, FullM6Hdr.m6HdrAnalyzeSpec xs m Q X →
      Func.wp m8SweepV2CoreParityEnv m8AnalyzeCoreM6Fn.body xs m Q X :=
    fun xs m Q X hs => m8_analyze_core_m6_m8_wp m8SweepV2CoreParityEnv
      (m8cp_base_row hBaseM7 hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBaseM7 hc2p.anaFailedLit (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
      (m8cp_base_row hBaseM7 m7FidBase_deduce1uipM6Hdr_mem (by decide) (by decide)
        (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h))
      (m8cp_base_row hBaseM7 hc2p.restoreBumpAna (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
      (fun _ _ _ _ h => .minShrinkM6 h)
      (m8cp_base_row hBaseM7 hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBaseM7 hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
      (m8cp_base_row hBaseM7 hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
      xs m Q X hs
  refine m8cp_patch_moduleOk_of_noCallBad m8FidV123t2_moduleOk
    m8cp_sw_fast_acyclic.1 m8cp_sw_fast_acyclic.2
    hReplWf m8CoreParityBefores_wf m8cp_m8Sw_noCallBad hBaseSw ?_ ?_ ?_ ?_
  · intro g hg hskip _hnone
    simp only [m8cpSkipNames, m8CoreParityRepls, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with h | h | h | h | h | h | h | h | h | h | h | h
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [m8SweepV2CoreParityRepls, m8CoreParityRepls, h]))
    · refine m8cp_common_skip_wp m8BveHook hBaseM7 hAnaToM7 hElimToM7 (Or.inl h)
        (fun hn => m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
          (List.mem_of_getElem? m8cp_sw_fn_137) (hn.trans rfl))
        m8AnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · have hgeq : g = m8AnalyzeFn :=
        m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
          (List.mem_of_getElem? m8cp_sw_fn_149) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      have hSwToM7 : ∀ {xs m Q X}, m8FidV123t2Env "full_analyze" [i64] [i64] xs m Q X →
          m7FidelityEnv "full_analyze" [i64] [i64] xs m Q X := fun h =>
        m8cp_sw_to_m7_of_ne (by decide) (m8cp_not_in_swRows _ (by t_kernel_rfl))
          (by decide) (by decide) (by decide) h
      have hs0 := m8cp_m7FidBase_elim (H := m8BveHook) (Γbase := m8FidV123t2Env) hSwToM7
        m8cp_analyzeM5_mem (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hsp
      exact m8_analyze_m8_wp m8SweepV2CoreParityEnv
        (m8cp_base_row hBaseM7 hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBaseM7 (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.deduce1uip)
          (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBaseM7 m8cp_restoreBumpAnaM5_mem (by decide) (by decide)
          (fun _ _ _ _ h => h))
        (fun _ _ _ _ hs => .minShrink hs)
        (m8cp_base_row hBaseM7 hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBaseM7 hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
        (m8cp_base_row hBaseM7 hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X hs0
    · refine m8cp_common_skip_wp m8BveHook hBaseM7 hAnaToM7 hElimToM7 (Or.inr (Or.inl h))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m8AnalyzeCoreM6Fn.body
        (fun hn => m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
          (List.mem_of_getElem? m8cp_sw_fn_150) (hn.trans rfl)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · refine m8cp_common_skip_wp m8BveHook hBaseM7 hAnaToM7 hElimToM7 (Or.inr (Or.inr (Or.inl h)))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m8AnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
          (List.mem_of_getElem? m8cp_sw_fn_418) (hn.trans rfl))
        (fun hn => absurd (h.symm.trans hn) (by decide))
    · refine m8cp_common_skip_wp m8BveHook hBaseM7 hAnaToM7 hElimToM7 (Or.inr (Or.inr (Or.inr h)))
        (fun hn => absurd (h.symm.trans hn) (by decide))
        m8AnalyzeCoreM6Fn.body (fun hn => absurd (h.symm.trans hn) (by decide)) hCoreWp
        (fun hn => absurd (h.symm.trans hn) (by decide))
        (fun hn => m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
          (List.mem_of_getElem? m8cp_sw_fn_421) (hn.trans rfl))
  · intro g hg hskip hr xs m Q X hsp
    exact m8cp_untouched_pull (m8cp_sw_not_help m8BveHook) hg hskip hr
      (by decide) (by decide) hsp
  · intro r hr xs m Q X hsp
    rcases List.mem_append.mp hr with hr1 | hr2
    · exact m8cp_common_repl_wp m8BveHook hBaseM7 hBaseToM7 r hr1 xs m Q X hsp
    · rcases List.mem_singleton.mp hr2 with rfl
      have hHtToM7 : ∀ {xs m Q X},
          m8FidV123t2Env "full_has_ternary" [i64, i32, i32, i32] [.bool] xs m Q X →
          m7FidelityEnv "full_has_ternary" [i64, i32, i32, i32] [.bool] xs m Q X := fun h =>
        m8cp_sw_to_m7_of_ne (by decide) (m8cp_not_in_swRows _ (by t_kernel_rfl))
          (by decide) (by decide) (by decide) h
      exact m7HasTernaryFn_wp m8SweepV2CoreParityEnv xs m Q X
        (m8cp_m7FidBase_elim hHtToM7 m8cp_hasTernary_mem
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp)
  · intro p hp h hh xs m Q X hs
    simp only [m8CoreParityBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8cp_minHelper_wp m8BveHook
        (fun nm hnm _ _ _ _ _ _ hb => m8cp_help_not_in_swEnv m8BveHook hnm hb)
        hBaseM7 h hh xs m Q X hs
    · exact m8cp_bveHelper_wp m8BveHook
        (fun nm hnm _ _ _ _ _ _ hb => m8cp_help_not_in_swEnv m8BveHook hnm hb)
        hBaseM7 h hh xs m Q X hs

theorem m8SweepV2CoreParity_tableImpl :
    TableImpl m8SweepV2CoreParityEnv m8SweepV2CoreParityModule.fns m8SweepV2CoreParitySpecTable :=
  tableImpl_of_moduleOk m8SweepV2CoreParity_moduleOk m8SweepV2CoreParitySpecTable_sigs
    m8SweepV2CoreParitySpecTable_nodup
    (fun _ _ _ _ _ _ ht => m8SweepV2CoreParityEnv_of_specTable ht)

theorem m8SweepV2CoreParity_solveBytes_mem :
    m6oSolveBytesFn ∈ m8SweepV2CoreParityModule.fns := by
  change m6oSolveBytesFn ∈ m8SweepV2CoreParityFns
  exact m8cp_patchFns_mem_of_ne m8FidV123t2_solveBytes_mem fun r hr => by
    simp only [m8SweepV2CoreParityRepls, m8CoreParityRepls, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level unconditional byte-level UNSAT soundness of `m8SweepV2CoreParityModule`
(`471` fns). -/
theorem m8SweepV2CoreParity_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of m8SweepV2CoreParity_moduleOk m8SweepV2CoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))
    hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `m8SweepV2CoreParityModule`. -/
theorem m8SweepV2CoreParity_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for
`m8SweepV2CoreParityModule`. -/
theorem m8SweepV2CoreParity_unsat_nv :
    Func.wp m8SweepV2CoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of m8SweepV2CoreParity_moduleOk m8SweepV2CoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))

theorem m8SweepV2CoreParityEnv_minMark {a m Q X} (h : Full.fullMinMarkSpec a m Q X) :
    m8SweepV2CoreParityEnv "full_min_mark" [i64, i32, i8] [] a m Q X :=
  .base (by decide) (m8cp_m7Fid_to_m8Sw "full_min_mark" [i64, i32, i8] [] a m Q X
    (mf_extra_at 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl
      (fun _ _ _ _ hs => hs) _ _ _ _ h))

theorem m8SweepV2CoreParityEnv_getWatermark {a m Q X}
    (h : FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X) :
    m8SweepV2CoreParityEnv "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
  let hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  .base (by decide) (m8cp_m7Fid_to_m8Sw "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X
    (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem hc1.hdrGetWm
        (fun _ _ _ _ hs => FullM6Hdr.m6HdrW2aSpec_monoX hs) _ _ _ _ h)))

theorem m8SweepV2CoreParityEnv_probeDticks_wp :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp m8SweepV2CoreParityEnv full_probe_dticks_m6_hdr_body a m Q X :=
  full_probe_dticks_m6_hdr_m8_wp m8SweepV2CoreParityEnv
    (fun _ _ _ _ hs => m8SweepV2CoreParityEnv_getWatermark hs)

theorem m8SweepV2CoreParityEnv_minShrinkM6_wp :
    ∀ a m Q X, m8MinShrinkSpec a m Q X →
      Func.wp m8SweepV2CoreParityEnv full_min_shrink_m6_body a m Q X := by
  have hBaseM7 : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      m8SweepV2CoreParityEnv f as bs xs m Q X := fun f as bs xs m Q X hne h =>
    .base hne (m8cp_m7Fid_to_m8Sw f as bs xs m Q X h)
  have hBaseToM7 : ∀ f as bs xs m Q X,
      f ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
        "full_probe_m6", "full_search_m6"] →
      m8FidV123t2Env f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X := by
    intro f as bs xs m Q X hmem h
    refine m8cp_sw_to_m7_of_ne ?_ ?_ ?_ ?_ ?_ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · have hchk : (["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
          "full_probe_m6", "full_search_m6"] : List Sym).all
          (fun s => !((m8SweepEnvRows.map SpecEntry.name).contains s)) = true := by t_kernel_rfl
      have h1 := List.all_eq_true.mp hchk f hmem
      simp only [Bool.not_eq_true'] at h1
      simpa using h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> decide
  exact fun a m Q X hs =>
    m8cp_common_repl_wp m8BveHook hBaseM7 hBaseToM7 m8MinShrinkM6Fn List.mem_cons_self a m Q X
      (.minShrinkM6 hs)

end LeanQbe.T.Examples.Kissat.FullM8CoreParity

end
