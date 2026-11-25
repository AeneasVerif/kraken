/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6a
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6b
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6c
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofCert
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar0
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullM7HotTernary
import LeanQbe.T.Examples.Kissat.FullM7BveGates
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
# Kissat Full-Fidelity BVE Parity Splice Proofs (`FullFidelityBveProof`)

Certifies both additive `PatchModule` splice targets built atop `FullM8SweepV2.m8FidV123t2Module`:
1. **`fidBveModule` (`469` fns):** `m8FidV123t2Module` patched with `fidBveRepls` (`5` fns) and
   `fidBveBefores` (`20` pure BVE/K6/unit-cert helpers; ZERO `D-11` XOR, ZERO `D-22` BCE), with
   closed `fidBveSpecTable`, `fidBveEnv`, `fidBve_moduleOk`, `fidBve_tableImpl`,
   `fidBve_solve_bytes_sound`, `fidBve_solve_bytes_host_sound`, and `fidBve_unsat_nv`.
2. **`fidBveCoreParityModule` (`472` fns):** `m8FidV123t2Module` patched with
   `fidBveCoreParityRepls` (`10` fns) and `fidBveCoreParityBefores` (`23` helpers), uniting
   `FullM8CoreParity` Ranks `#4/#5` + `FullM7HotTernary` + `FullFidelityBve`, with closed
   `fidBveCoreParitySpecTable`, `fidBveCoreParityEnv`, `fidBveCoreParity_moduleOk`,
   `fidBveCoreParity_tableImpl`, `fidBveCoreParity_solve_bytes_sound`,
   `fidBveCoreParity_solve_bytes_host_sound`, and `fidBveCoreParity_unsat_nv`.

Plain `public section`, zero expose attributes, zero `*Lemmas*` in `public import`, UNSAT-only
(`XPost := False`, `std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7HotTernary
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

private abbrev fidRowSig (e : SpecEntry) : SigEntry := (e.name, e.as, e.rs)

/-! ## 1. Spec Tables, Exclusions, and Closed Environments -/

/-- Symbols excluded from `m8FidV123t2Env` pass-through in `fidBveEnv`. -/
def fidBveExclNames : List Sym :=
  ["full_bve_var_key_m7", "full_bve_heap_push_m7"]

/-- `20`-row specification table aligned 1-to-1 with `fidBveHelpers`. -/
def fidBveHelperRows : List SpecEntry :=
  [ ⟨"full_bve_find_equiv_m8", [i64, i32, i32], [.bool], m8BveFindEquivSpec, true⟩
  , ⟨"full_bve_find_and_m8", [i64, i32, i32, i32], [.bool], m8BveFindAndSpec, true⟩
  , ⟨"full_bve_match_tern_m8", [i64, i32, i32, i32, i32, i32], [i32],
      m8BveMatchTernSpec, true⟩
  , ⟨"full_bve_find_ite_side_m8", [i64, i32, i32, i32, .bool], [.bool],
      m8BveFindIteSideSpec, true⟩
  , ⟨"full_bve_find_ite_m8", [i64, i32, i32, i32], [.bool], m8BveFindIteSpec, true⟩
  , ⟨"full_bve_k6_mv_fid", [i64], [i64], fidBveK6MvSpec, true⟩
  , ⟨"full_fid_k6_add_ticks", [i64, i64], [], fidK6AddTicksSpec, true⟩
  , ⟨"full_k6_watch_fid", [i64, i32, i32, i32, i32], [], fidK6WatchSpec, true⟩
  , ⟨"full_k6_assign_fid", [i64, i32, i32], [], fidK6AssignSpec, true⟩
  , ⟨"full_k6_mtf_fid", [i64, i32], [], fidK6MtfSpec, true⟩
  , ⟨"full_k6_backtrack_fid", [i64, i32], [], fidK6BacktrackSpec, true⟩
  , ⟨"full_k6_prop_fid", [i64], [i32], fidK6PropSpec, true⟩
  , ⟨"full_k6_ana_cl_fid", [i64, i32, i32], [], fidK6AnaClSpec, true⟩
  , ⟨"full_k6_analyze_fid", [i64, i32], [.bool], fidK6AnalyzeSpec, true⟩
  , ⟨"full_k6_solve_fid", [i64, i32], [i64], fidK6SolveSpec, true⟩
  , ⟨"full_k6_core_fid", [i64], [], fidK6CoreSpec, true⟩
  , ⟨"full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool],
      fidK6ExtractSolveSpec, true⟩
  , ⟨"full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool],
      fidBveCertifyUnitSpec, true⟩
  , ⟨"full_bve_def_k6_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩
  , ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩ ]

theorem fidBveHelperRows_sigs :
    fidBveHelperRows.map (fun e => (e.name, e.as, e.rs)) = fidBveHelpers.map Fn.sig := by
  t_kernel_rfl

theorem fidBveHelperRows_noExit : fidBveHelperRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidBveHelperRows_nodup : (fidBveHelperRows.map SpecEntry.name).Nodup := by
  decide

/-- `5`-row specification slice aligned with `fidBveRepls`. -/
def fidBveReplRows : List SpecEntry :=
  [ ⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveVarKeySpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩ ]

/-- Insertion row map matching `fidBveBefores`. -/
def fidBveBeforeRows : List (Sym × List SpecEntry) :=
  [ ("full_bve_var_m7", fidBveHelperRows) ]

/-- Untouched base-table rewire for `"full_bve_heap_push_m7"` against `m8BveVarKeySpec`. -/
def fidBveRewireRows : List SpecEntry :=
  [ ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], m8BveHeapPushSpec, true⟩ ]

/-- Full `469`-row specification table for `fidBveModule`. -/
def fidBveSpecTable : List SpecEntry :=
  PatchModule.patchRows (fidBveReplRows ++ fidBveRewireRows) fidBveBeforeRows m8SwBaseSpecTable

/-- `10`-row specification slice aligned with `fidBveCoreParityRepls`. -/
def fidBveCoreParityReplRows : List SpecEntry :=
  [ ⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveVarKeySpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64],
      FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], FullM6Orch.m6ProbeSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], FullM6.fullM6SearchSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], Full.fullHasTernarySpec, true⟩ ]

/-- Insertion row map matching `fidBveCoreParityBefores`. -/
def fidBveCoreParityBeforeRows : List (Sym × List SpecEntry) :=
  [ ("full_min_shrink_m6", m8MinHelperRows)
  , ("full_bve_var_m7", fidBveHelperRows) ]

/-- Rewired rows for `"full_min_shrink"` and `"full_bve_heap_push_m7"`. -/
def fidBveCoreParityRewireRows : List SpecEntry :=
  [ ⟨"full_min_shrink", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], m8BveHeapPushSpec, true⟩ ]

/-- Full `472`-row specification table for `fidBveCoreParityModule`. -/
def fidBveCoreParitySpecTable : List SpecEntry :=
  PatchModule.patchRows (fidBveCoreParityReplRows ++ fidBveCoreParityRewireRows)
    fidBveCoreParityBeforeRows m8SwBaseSpecTable

/-- Closed specification environment extending `m8FidV123t2Env` for `fidBveModule`. -/
inductive FidBveEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ∉ fidBveExclNames → Γ f as bs xs m Q X → FidBveEnv Γ f as bs xs m Q X
  | varKey {a m Q X} :
      m8BveVarKeySpec a m Q X → FidBveEnv Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X
  | heapPush {a m Q X} :
      m8BveHeapPushSpec a m Q X →
      FidBveEnv Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X
  | bveHelp {f as bs xs m Q X} :
      Env.ofTable fidBveHelperRows f as bs xs m Q X → FidBveEnv Γ f as bs xs m Q X

/-- Canonical closed `Env` for `fidBveModule` (`469` fns, `0` externs, `0` exits). -/
def fidBveEnv : Env := FidBveEnv m8FidV123t2Env

/-- Closed specification environment extending `m8FidV123t2Env` for `fidBveCoreParityModule`. -/
inductive FidBveCoreParityEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ∉ m8CpExclNames → Γ f as bs xs m Q X → FidBveCoreParityEnv Γ f as bs xs m Q X
  | minShrinkM6 {a m Q X} :
      m8MinShrinkSpec a m Q X → FidBveCoreParityEnv Γ "full_min_shrink_m6" [i64] [] a m Q X
  | minShrink {a m Q X} :
      m8MinShrinkSpec a m Q X → FidBveCoreParityEnv Γ "full_min_shrink" [i64] [] a m Q X
  | varKey {a m Q X} :
      m8BveVarKeySpec a m Q X →
      FidBveCoreParityEnv Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X
  | heapPush {a m Q X} :
      m8BveHeapPushSpec a m Q X →
      FidBveCoreParityEnv Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X
  | minHelp {f as bs xs m Q X} :
      Env.ofTable m8MinHelperRows f as bs xs m Q X →
      FidBveCoreParityEnv Γ f as bs xs m Q X
  | bveHelp {f as bs xs m Q X} :
      Env.ofTable fidBveHelperRows f as bs xs m Q X →
      FidBveCoreParityEnv Γ f as bs xs m Q X

/-- Canonical closed `Env` for `fidBveCoreParityModule` (`472` fns, `0` externs, `0` exits). -/
def fidBveCoreParityEnv : Env := FidBveCoreParityEnv m8FidV123t2Env

/-! ## 2. Structural Checkers, Acyclicity, and `SpecTable` Properties -/

private theorem fid_sw_replSigs_core :
    ∀ r ∈ fidBveCoreParityRepls, ∀ g ∈ m8FidV123t2Fns, r.name = g.name → r.sig = g.sig := by
  have hi135 : m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], []) := by
    t_kernel_rfl
  have hi374 : m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64]) := by
    t_kernel_rfl
  have hi375 : m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64]) := by
    t_kernel_rfl
  have hi415 : m8FidV123t2Fns[415]?.map Fn.sig =
      some ("full_bve_var_key_m7", [i64, i32], [i64]) := by t_kernel_rfl
  have hi421 : m8FidV123t2Fns[421]?.map Fn.sig =
      some ("full_elim_bve_m7", [i64, i64], [i64]) := by t_kernel_rfl
  have hi423 : m8FidV123t2Fns[423]?.map Fn.sig =
      some ("full_eliminate_m6", [i64, .bool], [i64]) := by t_kernel_rfl
  have hi438 : m8FidV123t2Fns[438]?.map Fn.sig =
      some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := by t_kernel_rfl
  have hi440 : m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64]) := by
    t_kernel_rfl
  have hi444 : m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64]) := by
    t_kernel_rfl
  have hi243 : m8FidV123t2Fns[243]?.map Fn.sig =
      some ("full_has_ternary", [i64, i32, i32, i32], [.bool]) := by t_kernel_rfl
  obtain ⟨g135, hg135, hs135⟩ := m8cp_sig_of_map hi135
  obtain ⟨g374, hg374, hs374⟩ := m8cp_sig_of_map hi374
  obtain ⟨g375, hg375, hs375⟩ := m8cp_sig_of_map hi375
  obtain ⟨g415, hg415, hs415⟩ := m8cp_sig_of_map hi415
  obtain ⟨g421, hg421, hs421⟩ := m8cp_sig_of_map hi421
  obtain ⟨g423, hg423, hs423⟩ := m8cp_sig_of_map hi423
  obtain ⟨g438, hg438, hs438⟩ := m8cp_sig_of_map hi438
  obtain ⟨g440, hg440, hs440⟩ := m8cp_sig_of_map hi440
  obtain ⟨g444, hg444, hs444⟩ := m8cp_sig_of_map hi444
  obtain ⟨g243, hg243, hs243⟩ := m8cp_sig_of_map hi243
  intro r hr f hf hnm
  simp only [fidBveCoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg135) (hnm.symm.trans (congrArg Prod.fst hs135).symm)) ▸ hs135.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg374) (hnm.symm.trans (congrArg Prod.fst hs374).symm)) ▸ hs374.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg375) (hnm.symm.trans (congrArg Prod.fst hs375).symm)) ▸ hs375.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg415) (hnm.symm.trans (congrArg Prod.fst hs415).symm)) ▸ hs415.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg421) (hnm.symm.trans (congrArg Prod.fst hs421).symm)) ▸ hs421.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg423) (hnm.symm.trans (congrArg Prod.fst hs423).symm)) ▸ hs423.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg438) (hnm.symm.trans (congrArg Prod.fst hs438).symm)) ▸ hs438.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg440) (hnm.symm.trans (congrArg Prod.fst hs440).symm)) ▸ hs440.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg444) (hnm.symm.trans (congrArg Prod.fst hs444).symm)) ▸ hs444.symm
  · exact (m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hf
      (List.mem_of_getElem? hg243) (hnm.symm.trans (congrArg Prod.fst hs243).symm)) ▸ hs243.symm

private theorem fid_sw_replSigs_bve :
    ∀ r ∈ fidBveRepls, ∀ g ∈ m8FidV123t2Fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  refine fid_sw_replSigs_core r ?_ g hg hnm
  simp only [fidBveRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [fidBveCoreParityRepls]

theorem fidBve_checkPatchCallsOk :
    PatchModule.checkPatchCallsOk m8FidV123t2Module fidBveRepls fidBveBefores = true := by
  t_kernel_rfl

theorem fidBveCoreParity_checkPatchCallsOk :
    PatchModule.checkPatchCallsOk m8FidV123t2Module fidBveCoreParityRepls
      fidBveCoreParityBefores = true := by
  t_kernel_rfl

private theorem fidBve_fast_acyclic :
    fidBveModule.namesNodup ∧
    (∀ pre fn post, fidBveModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ m8FidV123t2Module.externs.map Extern.sig)
        m8FidV123t2Module.exits) :=
  PatchModule.patchModule_checkAcyclic_fast m8FidV123t2_acyclic (by t_kernel_rfl)
    fidBve_checkPatchCallsOk fid_sw_replSigs_bve

private theorem fidBveCoreParity_fast_acyclic :
    fidBveCoreParityModule.namesNodup ∧
    (∀ pre fn post, fidBveCoreParityModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ m8FidV123t2Module.externs.map Extern.sig)
        m8FidV123t2Module.exits) :=
  PatchModule.patchModule_checkAcyclic_fast m8FidV123t2_acyclic (by t_kernel_rfl)
    fidBveCoreParity_checkPatchCallsOk fid_sw_replSigs_core

theorem fidBveFns_names_nodup : (fidBveFns.map Fn.name).Nodup := by
  have hnd := fidBve_fast_acyclic.1
  change (fidBveFns.map Fn.name ++ m8FidV123t2Module.externs.map Extern.name).Nodup at hnd
  exact (List.nodup_append.mp hnd).1

theorem fidBveCoreParityFns_names_nodup : (fidBveCoreParityFns.map Fn.name).Nodup := by
  have hnd := fidBveCoreParity_fast_acyclic.1
  change (fidBveCoreParityFns.map Fn.name ++
    m8FidV123t2Module.externs.map Extern.name).Nodup at hnd
  exact (List.nodup_append.mp hnd).1

private theorem fid_row_sig_of_sw {nm : Sym} {as rs : List Ty}
    (hex : ∃ g ∈ m8FidV123t2Fns, g.sig = (nm, as, rs)) :
    ∀ e ∈ m8SwBaseSpecTable, nm = e.name → (e.name, e.as, e.rs) = (nm, as, rs) := by
  obtain ⟨g, hg, hsg⟩ := hex
  intro e he hnm
  have hmem : (e.name, e.as, e.rs) ∈ m8SwBaseSpecTable.map fidRowSig :=
    List.mem_map_of_mem he
  have hSwBase : m8SwBaseSpecTable.map fidRowSig = m8FidV123t2Fns.map Fn.sig := m8cp_swBase_sigs
  rw [hSwBase] at hmem
  rcases List.mem_map.mp hmem with ⟨g', hg', hgeg'⟩
  have hnm' : g'.name = g.name :=
    (congrArg Prod.fst hgeg').trans (hnm.symm.trans (congrArg Prod.fst hsg).symm)
  have hgeq := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg' hg hnm'
  exact hgeg'.symm.trans (by rw [hgeq, hsg])

private theorem fid_sw_sig_exists {i : Nat} {sg : SigEntry}
    (h : m8FidV123t2Fns[i]?.map Fn.sig = some sg) :
    ∃ g ∈ m8FidV123t2Fns, g.sig = sg :=
  m8cp_sig_exists_of_map h

theorem fidBveSpecTable_sigs :
    fidBveSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidBveFns.map Fn.sig := by
  refine patchRows_sigs_eq_patchFns_self m8cp_swBase_sigs ?_ ?_ fid_sw_replSigs_bve
  · intro e f hnm
    dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt,
      fidBveBeforeRows, fidBveBefores]
    rw [hnm]
    by_cases h1 : ("full_bve_var_m7" == f.name)
    · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp; exact fidBveHelperRows_sigs
    · have h1n : "full_bve_var_m7" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
      simp [m8cp_sym_ne_beq h1n]
  · intro r hr e he hnm
    have h418 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    have h374 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    have h375 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    have h415 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    have h421 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[421]?.map Fn.sig = some ("full_elim_bve_m7", [i64, i64], [i64])))
    have h423 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[423]?.map Fn.sig = some ("full_eliminate_m6", [i64, .bool], [i64])))
    simp only [fidBveReplRows, fidBveRewireRows, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl
    · exact (h374 e he hnm).symm
    · exact (h375 e he hnm).symm
    · exact (h415 e he hnm).symm
    · exact (h421 e he hnm).symm
    · exact (h423 e he hnm).symm
    · exact (h418 e he hnm).symm

theorem fidBveCoreParitySpecTable_sigs :
    fidBveCoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidBveCoreParityFns.map Fn.sig := by
  refine patchRows_sigs_eq_patchFns_self m8cp_swBase_sigs ?_ ?_ fid_sw_replSigs_core
  · intro e f hnm
    dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt,
      fidBveCoreParityBeforeRows, fidBveCoreParityBefores]
    rw [hnm]
    by_cases h1 : ("full_min_shrink_m6" == f.name) <;>
      by_cases h2 : ("full_bve_var_m7" == f.name)
    · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
    · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp; exact m8MinHelperRows_sigs
    · have h2e := beq_iff_eq.mp h2; rw [← h2e]; simp; exact fidBveHelperRows_sigs
    · have h1n : "full_min_shrink_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
      have h2n : "full_bve_var_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
      simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n]
  · intro r hr e he hnm
    have h135 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], [])))
    have h137 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[137]?.map Fn.sig = some ("full_min_shrink", [i64], [])))
    have h374 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    have h375 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    have h415 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    have h418 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    have h421 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[421]?.map Fn.sig = some ("full_elim_bve_m7", [i64, i64], [i64])))
    have h423 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[423]?.map Fn.sig = some ("full_eliminate_m6", [i64, .bool], [i64])))
    have h438 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[438]?.map Fn.sig = some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])))
    have h440 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64])))
    have h444 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64])))
    have h243 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[243]?.map Fn.sig = some ("full_has_ternary", [i64, i32, i32, i32], [.bool])))
    simp only [fidBveCoreParityReplRows, fidBveCoreParityRewireRows, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact (h135 e he hnm).symm
    · exact (h374 e he hnm).symm
    · exact (h375 e he hnm).symm
    · exact (h415 e he hnm).symm
    · exact (h421 e he hnm).symm
    · exact (h423 e he hnm).symm
    · exact (h438 e he hnm).symm
    · exact (h440 e he hnm).symm
    · exact (h444 e he hnm).symm
    · exact (h243 e he hnm).symm
    · exact (h137 e he hnm).symm
    · exact (h418 e he hnm).symm

theorem fidBveSpecTable_length : fidBveSpecTable.length = 469 := by
  rw [rowSigs_eq_fnSigs_len fidBveSpecTable_sigs]
  t_kernel_rfl

theorem fidBveCoreParitySpecTable_length : fidBveCoreParitySpecTable.length = 472 := by
  rw [rowSigs_eq_fnSigs_len fidBveCoreParitySpecTable_sigs]
  t_kernel_rfl

private theorem fid_swBaseTable_noExit : m8SwBaseSpecTable.all SpecEntry.noExit = true := by
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
  unfold m8SwBaseSpecTable
  apply @FullM8CoreParity.patchRows_noExit m8SwV12SpecTable []
    [("full_sweep_dense_m6", m8SweepEnvRows)]
  · exact hv12No
  · rfl
  · intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact List.all_eq_true.mpr m8SweepEnvRows_noExit

theorem fidBveSpecTable_noExit : fidBveSpecTable.all SpecEntry.noExit = true := by
  unfold fidBveSpecTable
  apply @FullM8CoreParity.patchRows_noExit m8SwBaseSpecTable
    (fidBveReplRows ++ fidBveRewireRows) fidBveBeforeRows
  · exact fid_swBaseTable_noExit
  · rw [List.all_eq_true]
    intro r hr
    simp only [fidBveReplRows, fidBveRewireRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl <;> rfl
  · intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact fidBveHelperRows_noExit

theorem fidBveCoreParitySpecTable_noExit :
    fidBveCoreParitySpecTable.all SpecEntry.noExit = true := by
  unfold fidBveCoreParitySpecTable
  apply @FullM8CoreParity.patchRows_noExit m8SwBaseSpecTable
    (fidBveCoreParityReplRows ++ fidBveCoreParityRewireRows) fidBveCoreParityBeforeRows
  · exact fid_swBaseTable_noExit
  · rw [List.all_eq_true]
    intro r hr
    simp only [fidBveCoreParityReplRows, fidBveCoreParityRewireRows, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> rfl
  · intro p hp
    simp only [fidBveCoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8MinHelperRows_noExit
    · exact fidBveHelperRows_noExit

theorem fidBveSpecTable_nodup : (fidBveSpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup fidBveSpecTable_sigs fidBveFns_names_nodup

theorem fidBveCoreParitySpecTable_nodup :
    (fidBveCoreParitySpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup fidBveCoreParitySpecTable_sigs fidBveCoreParityFns_names_nodup

/-! ## 3. Shared Parametric BVE & Repl Lifting Proofs -/

private theorem fid_bveHelperRows_disj_sw :
    ∀ e ∈ fidBveHelperRows, e.name ∉ m8FidV123t2Fns.map Fn.name := by
  have hdisj : (fidBveHelpers.map Fn.name).all
      (fun nm => !((m8FidV123t2Fns.map Fn.name).contains nm)) = true := by
    t_kernel_rfl
  intro e he hmem
  have he_nm : e.name ∈ fidBveHelpers.map Fn.name := by
    have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at h1
    rw [← h1]
    exact List.mem_map_of_mem he
  have hchk := List.all_eq_true.mp hdisj e.name he_nm
  simp only [Bool.not_eq_true'] at hchk
  exact absurd hmem (by simpa using hchk)

private theorem fid_sw_helpers_not_mem (f : Fn) (hf : f ∈ m8FidV123t2Fns) :
    f.name ∉ fidBveHelperRows.map SpecEntry.name := by
  intro hm
  rcases List.mem_map.mp hm with ⟨e, he, hnm⟩
  exact fid_bveHelperRows_disj_sw e he (hnm ▸ List.mem_map_of_mem hf)

private theorem fid_bveHelp_disj_swRows :
    (fidBveHelpers.map Fn.name).all
      (fun nm => !((m8SweepEnvRows.map SpecEntry.name).contains nm)) = true := by
  t_kernel_rfl

private theorem fid_bveHelp_disj_minRows :
    (m8MinHelperRows.map SpecEntry.name).all
      (fun nm => !((fidBveHelpers.map Fn.name).contains nm)) = true := by
  decide

private theorem fid_bveHelp_not_in_m7FidEnv {nm : Sym}
    (hnm : nm ∈ fidBveHelperRows.map SpecEntry.name) {as bs xs m Q X}
    (hb : m7FidelityEnv nm as bs xs m Q X) : False := by
  have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at h1
  have hmem : nm ∈ fidBveHelpers.map Fn.name := h1 ▸ hnm
  have hdisjM7 : (fidBveHelpers.map Fn.name).all
      (fun s => !((m7Fns.map Fn.name).contains s)) = true := by t_kernel_rfl
  have hdisjEx : (fidBveHelpers.map Fn.name).all
      (fun s => !((mfExtraRows.map SpecEntry.name).contains s)) = true := by t_kernel_rfl
  cases hb with
  | base _ hb0 =>
    have htb : nm ∈ m7FidBaseTable.map SpecEntry.name := m8CoreParity_ofTable_name_mem hb0
    have hsg := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hsg
    change nm ∈ m7FidBaseTable.map SpecEntry.name at htb
    rw [hsg] at htb
    have hchk := List.all_eq_true.mp hdisjM7 nm hmem
    simp only [Bool.not_eq_true'] at hchk
    exact absurd htb (by simpa using hchk)
  | extra he =>
    have hte := m8CoreParity_ofTable_name_mem he
    have hchk := List.all_eq_true.mp hdisjEx nm hmem
    simp only [Bool.not_eq_true'] at hchk
    exact absurd hte (by simpa using hchk)

private theorem fid_bveHelp_not_in_swEnv {nm : Sym}
    (hnm : nm ∈ fidBveHelperRows.map SpecEntry.name) {as bs xs m Q X}
    (hb : m8FidV123t2Env nm as bs xs m Q X) : False := by
  have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at h1
  have hmem : nm ∈ fidBveHelpers.map Fn.name := h1 ▸ hnm
  have hnot : nm ∉ ["full_extend_push2", "full_cong_enq_var", "full_cong_eval_gate",
      "full_cong_worklist"] := by
    intro h4
    have hchk : (["full_extend_push2", "full_cong_enq_var", "full_cong_eval_gate",
        "full_cong_worklist"] : List Sym).all
        (fun s => !((fidBveHelpers.map Fn.name).contains s)) = true := by decide
    have h2 := List.all_eq_true.mp hchk nm h4
    simp only [Bool.not_eq_true'] at h2
    exact absurd hmem (by simpa using h2)
  have hnot_sw : nm ∉ m8SweepEnvRows.map SpecEntry.name := by
    have hchk := List.all_eq_true.mp fid_bveHelp_disj_swRows nm hmem
    simp only [Bool.not_eq_true'] at hchk
    simpa using hchk
  exact fid_bveHelp_not_in_m7FidEnv hnm
    (m8cp_sw_to_m7_of_ne (fun h => hnot (by simp [h])) hnot_sw
      (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h])) hb)

private theorem fid_bveHelp_row {Γ : Env}
    (hHelp : ∀ e ∈ fidBveHelperRows, ∀ xs m Q X,
      Env.ofTable fidBveHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (k : Nat) (hk : k < fidBveHelperRows.length) {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidBveHelperRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X := fun a m Q X hs =>
  hHelp ⟨nm, as, bs, sp, true⟩ (heq ▸ List.getElem_mem hk) a m Q X
    (Env.ofTable_of_mem (heq ▸ List.getElem_mem hk) fidBveHelperRows_nodup (hno a m Q X hs))

private theorem fid_sw_bveRow {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (k : Nat) (hk : k < m7FidBveRows.length) {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X :=
  m8cp_bveRow_base hBase k hk heq hnef hncp

private theorem fid_sw_row_at {Γ : Env}
    (hSw : ∀ e ∈ m8SweepEnvRows, ∀ xs m Q X,
      Env.ofTable m8SweepEnvRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (k : Nat) (hk : k < m8SweepEnvRows.length) {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m8SweepEnvRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X := fun a m Q X hs =>
  hSw ⟨nm, as, bs, sp, true⟩ (heq ▸ List.getElem_mem hk) a m Q X
    (Env.ofTable_of_mem (heq ▸ List.getElem_mem hk) m8SweepEnvRows_nodup (hno a m Q X hs))

private theorem fid_bve_helpers_impl (Γ : Env)
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hSw : ∀ e ∈ m8SweepEnvRows, ∀ xs m Q X,
      Env.ofTable m8SweepEnvRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X)
    (hHelp : ∀ e ∈ fidBveHelperRows, ∀ xs m Q X,
      Env.ofTable fidBveHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) :
    TableImpl Γ fidBveHelpers fidBveHelperRows := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hAssignLvl := m8cp_base_row hBase hc1.assignLvl (by decide) (by decide) (fun _ _ _ _ h => h)
  have hMaxV := fid_sw_row_at hSw 0 (by decide) rfl (fun _ _ _ _ h => h)
  have hK6Init := fid_sw_row_at hSw 2 (by decide) rfl (fun _ _ _ _ h => h)
  have hK6Add := fid_sw_row_at hSw 5 (by decide) rfl (fun _ _ _ _ h => h)
  have hK6Solve := fid_sw_row_at hSw 11 (by decide) rfl (fun _ _ _ _ h => h)
  have hEquiv := fid_bveHelp_row hHelp 0 (by decide) rfl m8BveFindEquivSpec_noExit
  have hAnd := fid_bveHelp_row hHelp 1 (by decide) rfl m8BveFindAndSpec_noExit
  have hMatch := fid_bveHelp_row hHelp 2 (by decide) rfl m8BveMatchTernSpec_noExit
  have hIteSide := fid_bveHelp_row hHelp 3 (by decide) rfl m8BveFindIteSideSpec_noExit
  have hIte := fid_bveHelp_row hHelp 4 (by decide) rfl m8BveFindIteSpec_noExit
  have hK6Mv := fid_bveHelp_row hHelp 5 (by decide) rfl fidBveK6MvSpec_noExit
  have hAddTicks := fid_bveHelp_row hHelp 6 (by decide) rfl fidK6AddTicksSpec_noExit
  have hWatch := fid_bveHelp_row hHelp 7 (by decide) rfl fidK6WatchSpec_noExit
  have hAssign := fid_bveHelp_row hHelp 8 (by decide) rfl fidK6AssignSpec_noExit
  have hMtf := fid_bveHelp_row hHelp 9 (by decide) rfl fidK6MtfSpec_noExit
  have hBt := fid_bveHelp_row hHelp 10 (by decide) rfl fidK6BacktrackSpec_noExit
  have hProp := fid_bveHelp_row hHelp 11 (by decide) rfl fidK6PropSpec_noExit
  have hAnaCl := fid_bveHelp_row hHelp 12 (by decide) rfl fidK6AnaClSpec_noExit
  have hAnalyze := fid_bveHelp_row hHelp 13 (by decide) rfl fidK6AnalyzeSpec_noExit
  have hSolve := fid_bveHelp_row hHelp 14 (by decide) rfl fidK6SolveSpec_noExit
  have hCore := fid_bveHelp_row hHelp 15 (by decide) rfl fidK6CoreSpec_noExit
  have hExtSolve := fid_bveHelp_row hHelp 16 (by decide) rfl fidK6ExtractSolveSpec_noExit
  have hCertUnit := fid_bveHelp_row hHelp 17 (by decide) rfl fidBveCertifyUnitSpec_noExit
  have hDefK6 := fid_bveHelp_row hHelp 18 (by decide) rfl m8BveGatesSpec_noExit
  dsimp only [fidBveHelpers, fidBveHelperRows]
  exact ⟨ SpecEntry.Impl.of (full_bve_find_equiv_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_find_and_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_match_tern_m8_wp Γ),
    SpecEntry.Impl.of (full_bve_find_ite_side_m8_wp Γ
      (fid_sw_bveRow hBase 15 (by decide) rfl (by decide) (by decide)) hMatch),
    SpecEntry.Impl.of (full_bve_find_ite_m8_wp Γ hIteSide),
    SpecEntry.Impl.of (full_bve_k6_mv_fid_wp Γ),
    SpecEntry.Impl.of (full_fid_k6_add_ticks_wp Γ),
    SpecEntry.Impl.of (full_k6_watch_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_assign_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_mtf_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_backtrack_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_prop_fid_wp Γ hAddTicks hAssign),
    SpecEntry.Impl.of (full_k6_ana_cl_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_analyze_fid_wp Γ hAnaCl hBt hMtf hAssign hWatch),
    SpecEntry.Impl.of (full_k6_solve_fid_wp Γ hBt hAssign hProp hAnalyze),
    SpecEntry.Impl.of (full_k6_core_fid_wp Γ),
    SpecEntry.Impl.of (full_k6_extract_and_solve_fid_wp Γ hK6Mv hWatch hSolve hCore),
    SpecEntry.Impl.of (full_bve_certify_unit_fid_wp Γ hMaxV hK6Init hK6Add hK6Solve hAssignLvl),
    SpecEntry.Impl.of (full_bve_def_k6_fid_wp Γ hK6Mv hExtSolve hCertUnit),
    SpecEntry.Impl.of (full_bve_gates_fid_wp Γ hEquiv hAnd hIte hDefK6),
    trivial ⟩

private theorem fid_varM7_wp {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hHelp : ∀ e ∈ fidBveHelperRows, ∀ xs m Q X,
      Env.ofTable fidBveHelperRows e.name e.as e.rs xs m Q X → Γ e.name e.as e.rs xs m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ full_bve_var_m7_body a m Q X := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  exact full_bve_var_m7_fid_wp Γ
    (fid_sw_bveRow hBase 9 (by decide) rfl (by decide) (by decide))
    (m8cp_base_row hBase (m7FidP3Bve5_mem (i := 4) (by decide))
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase (m7FidP3Bve5_mem (i := 1) (by decide))
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase hc2.setInactive (by decide) (by decide) (fun _ _ _ _ h => h))
    (fid_bveHelp_row hHelp 19 (by decide) rfl m8BveGatesSpec_noExit)
    (fid_sw_bveRow hBase 31 (by decide) rfl (by decide) (by decide))
    (m8cp_base_row hBase (m7FidP3Bve5_mem (i := 0) (by decide))
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase hc1.assignLvl (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase (m7FidP3Bve5_mem (i := 3) (by decide))
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (fid_sw_bveRow hBase 1 (by decide) rfl (by decide) (by decide))

private theorem fid_elimBveM7_wp {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hPush : ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Func.wp Γ full_elim_bve_m7_body a m Q X :=
  full_elim_bve_m7_fid_wp Γ
    (fid_sw_bveRow hBase 38 (by decide) rfl (by decide) (by decide))
    (fid_sw_bveRow hBase 39 (by decide) rfl (by decide) (by decide))
    (fid_sw_bveRow hBase 32 (by decide) rfl (by decide) (by decide))
    (fid_sw_bveRow hBase 1 (by decide) rfl (by decide) (by decide))
    hPush

private theorem fid_eliminateM6_wp {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_m6_body a m Q X := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  exact full_eliminate_m6_fid_wp Γ
    (m8cp_base_row hBase m7FidP3ElimDticks_mem (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase hc1.log10Q16M7 (by decide) (by decide)
      (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
    (m8cp_base_row hBase hc1.scaleDelta (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase hc2.enterDense (by decide) (by decide) (fun _ _ _ _ h => h))
    (m8cp_base_row hBase m7FidP3MinU64_mem (by decide) (by decide) (fun _ _ _ _ h => h))
    (fid_sw_bveRow hBase 10 (by decide) rfl (by decide) (by decide))
    (fid_sw_bveRow hBase 40 (by decide) rfl (by decide) (by decide))
    (m8cp_base_row hBase hc2.rebuildWatches (by decide) (by decide) (fun _ _ _ _ h => h))

private theorem fid_heapPush_wp {Γ : Env}
    (hBase : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      Γ f as bs xs m Q X)
    (hKey : ∀ a m Q X, m8BveVarKeySpec a m Q X →
      Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Func.wp Γ FullM7BveGates.full_bve_heap_push_m7_body a m Q X :=
  full_bve_heap_push_m7_m8_wp Γ hKey
    (fid_sw_bveRow hBase 35 (by decide) rfl (by decide) (by decide))
    (fid_sw_bveRow hBase 36 (by decide) rfl (by decide) (by decide))

private theorem fid_bve_ofTable_to_m7_elim {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hSwToM7 : ∀ {xs m Q X}, m8FidV123t2Env nm as bs xs m Q X → m7FidelityEnv nm as bs xs m Q X)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hb : m8FidV123t2Env nm as bs xs m Q X) : sp xs m Q (fun _ _ _ _ => False) := by
  have hm7 := hSwToM7 hb
  cases hm7 with
  | base _ hb0 => exact (m8cp_ofTable_sig_elim m7FidBaseTable_nodup hmem hb0).2.2
  | extra he => exact False.elim (hneEx (m8CoreParity_ofTable_name_mem he))

private theorem fid_m8SwToM7_of_not_sw {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h1 : nm ≠ "full_extend_push2")
    (h2 : nm ≠ "full_cong_enq_var") (h3 : nm ≠ "full_cong_eval_gate")
    (h4 : nm ≠ "full_cong_worklist")
    (hmem : (nm ∉ m8SweepEnvRows.map SpecEntry.name))
    (h : m8FidV123t2Env nm as bs xs m Q X) : m7FidelityEnv nm as bs xs m Q X :=
  m8cp_sw_to_m7_of_ne h1 hmem h2 h3 h4 h

/-! ## 4. `fidBveModule` (`469` fns): `ModuleOk`, `TableImpl`, Soundness, and Tier-3b NV -/

private theorem fidBve_env_of_m8SwBase {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidBveSpecTable f as bs xs m Q X) :
    fidBveEnv f as bs xs m Q X := by
  have hReplSigs : ∀ r ∈ (fidBveReplRows ++ fidBveRewireRows),
      ∀ e ∈ m8SwBaseSpecTable, r.name = e.name → fidRowSig r = fidRowSig e := by
    have h418 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    have h374 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    have h375 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    have h415 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    have h421 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[421]?.map Fn.sig = some ("full_elim_bve_m7", [i64, i64], [i64])))
    have h423 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[423]?.map Fn.sig = some ("full_eliminate_m6", [i64, .bool], [i64])))
    intro r hr e he hnm
    simp only [fidBveReplRows, fidBveRewireRows, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl
    · exact (h374 e he hnm).symm
    · exact (h375 e he hnm).symm
    · exact (h415 e he hnm).symm
    · exact (h421 e he hnm).symm
    · exact (h423 e he hnm).symm
    · exact (h418 e he hnm).symm
  have hBefDisj : ∀ p ∈ fidBveBeforeRows, ∀ b ∈ p.2,
      b.name ∉ m8SwBaseSpecTable.map SpecEntry.name := by
    have hnm_sw : m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name := by
      have hm := congrArg (List.map Prod.fst) m8cp_swBase_sigs
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    rw [hnm_sw]
    intro p hp b hb hmem
    rcases List.mem_singleton.mp hp with rfl
    exact fid_bveHelperRows_disj_sw b hb hmem
  have hSwBveVar : ∀ {a m Q X}, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      m8FidV123t2Env "full_bve_var" [i64, i32] [i64] a m Q X := fun hs =>
    m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl))
        (fun _ _ _ _ h => h) _ _ _ _ hs))
  have hSwBveVarM7 : ∀ {a m Q X}, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      m8FidV123t2Env "full_bve_var_m7" [i64, i32] [i64] a m Q X := fun hs =>
    m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem m7FidBase_bveVar_mem (fun _ _ _ _ h => h) _ _ _ _ hs))
  have hSwElimBve : ∀ {a m Q X}, FullM3CongBva.m3ElimBveSpec a m Q X →
      m8FidV123t2Env "full_elim_bve_m7" [i64, i64] [i64] a m Q X := fun hs =>
    m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem m7FidBase_elimBveM7_mem (fun _ _ _ _ h => h) _ _ _ _ hs))
  have hSwElimM6 : ∀ {a m Q X}, FullFastSched.schedEliminateSpec a m Q X →
      m8FidV123t2Env "full_eliminate_m6" [i64, .bool] [i64] a m Q X := fun hs =>
    m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 42) rfl))
        (fun _ _ _ _ h => h) _ _ _ _ hs))
  rcases ofTable_patchRows_elim hReplSigs hBefDisj h with hr | hb | hbase
  · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
    rcases List.mem_append.mp hr with hrRepl | hrRew
    · simp only [fidBveReplRows, List.mem_cons, List.not_mem_nil, or_false] at hrRepl
      rcases hrRepl with rfl | rfl | rfl | rfl | rfl
      · cases has; cases hrs; exact .base (by decide) (hSwBveVarM7 hcast)
      · cases has; cases hrs; exact .base (by decide) (hSwBveVar hcast)
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact .varKey hcast
      · cases has; cases hrs; exact .base (by decide) (hSwElimBve hcast)
      · cases has; cases hrs; exact .base (by decide) (hSwElimM6 hcast)
    · rcases List.mem_singleton.mp hrRew with rfl
      cases has; cases hrs
      dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
      exact .heapPush hcast
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    rcases List.mem_singleton.mp hp with rfl
    exact .bveHelp (ofTable_of_cast hb_p fidBveHelperRows_nodup rfl has hrs hcast)
  · rcases hbase with ⟨hnr, _, htbl⟩
    refine .base (fun hexcl => ?_) (m8cp_sw_base_to_env htbl)
    simp only [fidBveExclNames, List.mem_cons, List.not_mem_nil, or_false] at hexcl
    rcases hexcl with rfl | rfl
    · exact hnr (by simp [fidBveReplRows])
    · exact hnr (by simp [fidBveRewireRows])

theorem fidBveEnv_of_specTable {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidBveSpecTable f as bs xs m Q X) :
    fidBveEnv f as bs xs m Q X :=
  fidBve_env_of_m8SwBase h

private theorem fidBveEnv_name_cases {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (h : fidBveEnv f as bs xs m Q X) :
    (f ∉ fidBveExclNames ∧ m8FidV123t2Env f as bs xs m Q X) ∨
    f = "full_bve_var_key_m7" ∨ f = "full_bve_heap_push_m7" ∨
    Env.ofTable fidBveHelperRows f as bs xs m Q X := by
  change FidBveEnv m8FidV123t2Env f as bs xs m Q X at h
  cases h with
  | base hne hb => exact Or.inl ⟨hne, hb⟩
  | varKey _ => exact Or.inr (Or.inl rfl)
  | heapPush _ => exact Or.inr (Or.inr (Or.inl rfl))
  | bveHelp ht => exact Or.inr (Or.inr (Or.inr ht))

private theorem fidBveEnv_varKey_inv {a m Q X}
    (h : fidBveEnv "full_bve_var_key_m7" [i64, i32] [i64] a m Q X) :
    m8BveVarKeySpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_bve_var_key_m7" → HEq xs a → HEq Q' Q → m8BveVarKeySpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_bve_var_key_m7" ∈ fidBveExclNames)) hne
  | varKey hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | heapPush _ => exact absurd hf (by decide)
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_var_key_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private theorem fidBveEnv_heapPush_inv {a m Q X}
    (h : fidBveEnv "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    m8BveHeapPushSpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_bve_heap_push_m7" → HEq xs a → HEq Q' Q → m8BveHeapPushSpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_bve_heap_push_m7" ∈ fidBveExclNames)) hne
  | varKey _ => exact absurd hf (by decide)
  | heapPush hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_heap_push_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private def fidBveSkipNames : List Sym :=
  fidBveRepls.map Fn.name ++ ["full_bve_heap_push_m7"]

private theorem fidBve_noCallBad :
    PatchModule.checkNoCallBad fidBveSkipNames fidBveExclNames m8FidV123t2Fns = true := by
  t_kernel_rfl

/-- Closed unconditional `469/469` `ModuleOk` certifying `fidBveModule` under `fidBveEnv`. -/
theorem fidBve_moduleOk : ModuleOk fidBveEnv fidBveModule := by
  have hBaseM7 : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      fidBveEnv f as bs xs m Q X := fun _ _ _ _ _ _ _ hne h =>
    .base (fun hex => hne (by
      simp only [fidBveExclNames, List.mem_cons, List.not_mem_nil, or_false] at hex
      rcases hex with rfl | rfl <;> decide)) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ h)
  have hSw : ∀ e ∈ m8SweepEnvRows, ∀ xs m Q X,
      Env.ofTable m8SweepEnvRows e.name e.as e.rs xs m Q X →
      fidBveEnv e.name e.as e.rs xs m Q X := fun _ _ _ _ _ _ h => .base (by
    have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
        (fun s => !(fidBveExclNames.contains s)) = true := by decide
    have hm := List.all_eq_true.mp hdisj _ (m8Sw_ofTable_name_mem h)
    simp only [Bool.not_eq_true'] at hm
    simpa using hm) (.sweep h)
  have hVarM7 := fid_varM7_wp hBaseM7 (fun _ _ _ _ _ _ h => .bveHelp h)
  have hElimBve := fid_elimBveM7_wp hBaseM7 (fun _ _ _ _ h => .heapPush h)
  have hElimM6 := fid_eliminateM6_wp hBaseM7
  have hHeapPush := fid_heapPush_wp hBaseM7 (fun _ _ _ _ h => .varKey h)
  refine m8cp_patch_moduleOk_of_noCallBad m8FidV123t2_moduleOk
    fidBve_fast_acyclic.1 fidBve_fast_acyclic.2
    fidBveRepls_wf (fun p hp h hh => by
      rcases List.mem_singleton.mp hp with rfl; exact fidBveHelpers_wf h hh)
    fidBve_noCallBad (fun _ _ _ _ _ _ _ hne h => .base hne h) ?_ ?_ ?_ ?_
  · intro g hg hskip _hnone
    simp only [fidBveSkipNames, fidBveRepls, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with h | h | h | h | h | h
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [fidBveRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [fidBveRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [fidBveRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [fidBveRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone (by simp [fidBveRepls, h]))
    · obtain rfl := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
        (List.mem_of_getElem? m8cp_sw_fn_418) (h.trans rfl)
      intro xs m Q X hsp
      exact hHeapPush xs m Q X (fidBveEnv_heapPush_inv hsp)
  · intro g hg hskip hr xs m Q X hsp
    rcases fidBveEnv_name_cases hsp with ⟨_, hb⟩ | heq | heq | hm
    · exact hb
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hr (by rw [heq]; decide))
    · exact False.elim (hskip (heq ▸ by decide))
    · exact False.elim (fid_sw_helpers_not_mem g hg (m8CoreParity_ofTable_name_mem hm))
  · intro r hr xs m Q X hsp
    have hnm_sw : ∀ f as bs xs m Q X, m8FidV123t2Env f as bs xs m Q X →
        (f = "full_bve_var_m7" ∨ f = "full_bve_var" ∨ f = "full_elim_bve_m7" ∨
          f = "full_eliminate_m6") → m7FidelityEnv f as bs xs m Q X := fun f as bs xs m Q X hb hf =>
      fid_m8SwToM7_of_not_sw (by rcases hf with h | h | h | h <;> rw [h] <;> decide)
        (by rcases hf with h | h | h | h <;> rw [h] <;> decide)
        (by rcases hf with h | h | h | h <;> rw [h] <;> decide)
        (by rcases hf with h | h | h | h <;> rw [h] <;> decide)
        (by
          have hchk : (["full_bve_var_m7", "full_bve_var", "full_elim_bve_m7",
              "full_eliminate_m6"] : List Sym).all
              (fun s => !((m8SweepEnvRows.map SpecEntry.name).contains s)) = true := by
            t_kernel_rfl
          have h0 := List.all_eq_true.mp hchk f (by
            rcases hf with h | h | h | h <;> simp [h])
          simp only [Bool.not_eq_true'] at h0; simpa using h0)
        hb
    have hElimBase : ∀ {nm as bs} {sp : Spec as bs},
        nm ∈ ["full_bve_var_m7", "full_bve_var", "full_elim_bve_m7", "full_eliminate_m6"] →
        (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
        nm ∉ mfExtraRows.map SpecEntry.name →
        ∀ {xs m Q X}, fidBveEnv nm as bs xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      intro nm as bs sp hnf hm hnex xs m Q X hsp'
      rcases fidBveEnv_name_cases hsp' with ⟨_, hb⟩ | hc | hc | hm'
      · exact fid_bve_ofTable_to_m7_elim (fun {xs m Q X} h => hnm_sw nm as bs xs m Q X h (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnf; exact hnf))
          hm hnex hb
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6") with rfl | rfl | rfl | rfl <;> decide)
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6") with rfl | rfl | rfl | rfl <;> decide)
      · have hni : nm ∉ fidBveHelperRows.map SpecEntry.name := by
          rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6") with rfl | rfl | rfl | rfl <;> decide
        exact absurd (m8CoreParity_ofTable_name_mem hm') hni
    simp only [fidBveRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hVarM7 xs m Q X (hElimBase (by decide) m7FidBase_bveVar_mem (by decide) hsp)
    · exact full_bve_var_fid_wp fidBveEnv
        (m8cp_base_row hBaseM7 m7FidBase_bveVar_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (hElimBase (by decide)
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl)) (by decide) hsp)
    · exact full_bve_var_key_m7_m8_wp fidBveEnv xs m Q X (fidBveEnv_varKey_inv hsp)
    · exact hElimBve xs m Q X (hElimBase (by decide) m7FidBase_elimBveM7_mem (by decide) hsp)
    · exact hElimM6 xs m Q X (hElimBase (by decide)
        (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 42) rfl)) (by decide) hsp)
  · intro p hp h hh xs m Q X hs
    rcases List.mem_singleton.mp hp with rfl
    have hTbl : TableImpl fidBveEnv fidBveHelpers fidBveHelperRows :=
      fid_bve_helpers_impl fidBveEnv hBaseM7 hSw (fun _ _ _ _ _ _ hb => .bveHelp hb)
    refine m8cp_tableImpl_mem_wp hTbl ?_ h hh xs m Q X hs
    intro r hr' xs' m' Q' X' hs'
    have hr_nm : r.name ∈ fidBveHelperRows.map SpecEntry.name := List.mem_map_of_mem hr'
    rcases fidBveEnv_name_cases hs' with ⟨_, hb⟩ | heq | heq | hm
    · exact False.elim (fid_bveHelp_not_in_swEnv hr_nm hb)
    · exact False.elim (by
        have hc : ("full_bve_var_key_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name :=
          heq ▸ hr_nm
        exact absurd hc (by decide))
    · exact False.elim (by
        have hc : ("full_bve_heap_push_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name :=
          heq ▸ hr_nm
        exact absurd hc (by decide))
    · exact (m8cp_ofTable_sig_elim fidBveHelperRows_nodup hr' hm).2.2

theorem fidBve_tableImpl :
    TableImpl fidBveEnv fidBveModule.fns fidBveSpecTable :=
  tableImpl_of_moduleOk fidBve_moduleOk fidBveSpecTable_sigs fidBveSpecTable_nodup
    (fun _ _ _ _ _ _ ht => fidBveEnv_of_specTable ht)

theorem fidBve_solveBytes_mem : m6oSolveBytesFn ∈ fidBveModule.fns := by
  change m6oSolveBytesFn ∈ fidBveFns
  exact m8cp_patchFns_mem_of_ne m8FidV123t2_solveBytes_mem fun r hr => by
    simp only [fidBveRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level unconditional byte-level UNSAT soundness of `fidBveModule` (`469` fns). -/
theorem fidBve_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBveEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of fidBve_moduleOk fidBve_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))
    hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidBveModule`. -/
theorem fidBve_solve_bytes_host_sound
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

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for `fidBveModule`. -/
theorem fidBve_unsat_nv :
    Func.wp fidBveEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of fidBve_moduleOk fidBve_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))

/-! ## 5. `fidBveCoreParityModule` (`472` fns): `ModuleOk`, `TableImpl`, Soundness, and NV -/

private theorem fidCoreParity_env_of_m8SwBase {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidBveCoreParitySpecTable f as bs xs m Q X) :
    fidBveCoreParityEnv f as bs xs m Q X := by
  have hReplSigs : ∀ r ∈ (fidBveCoreParityReplRows ++ fidBveCoreParityRewireRows),
      ∀ e ∈ m8SwBaseSpecTable, r.name = e.name → fidRowSig r = fidRowSig e := by
    have h135 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[135]?.map Fn.sig = some ("full_min_shrink_m6", [i64], [])))
    have h137 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[137]?.map Fn.sig = some ("full_min_shrink", [i64], [])))
    have h374 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[374]?.map Fn.sig = some ("full_bve_var_m7", [i64, i32], [i64])))
    have h375 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[375]?.map Fn.sig = some ("full_bve_var", [i64, i32], [i64])))
    have h415 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[415]?.map Fn.sig = some ("full_bve_var_key_m7", [i64, i32], [i64])))
    have h418 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[418]?.map Fn.sig = some ("full_bve_heap_push_m7", [i64, i64, i32], [i64])))
    have h421 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[421]?.map Fn.sig = some ("full_elim_bve_m7", [i64, i64], [i64])))
    have h423 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[423]?.map Fn.sig = some ("full_eliminate_m6", [i64, .bool], [i64])))
    have h438 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[438]?.map Fn.sig = some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])))
    have h440 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[440]?.map Fn.sig = some ("full_probe_m6", [i64, .bool], [i64])))
    have h444 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[444]?.map Fn.sig = some ("full_search_m6", [i64], [i64])))
    have h243 := fid_row_sig_of_sw (fid_sw_sig_exists (by t_kernel_rfl :
      m8FidV123t2Fns[243]?.map Fn.sig = some ("full_has_ternary", [i64, i32, i32, i32], [.bool])))
    intro r hr e he hnm
    simp only [fidBveCoreParityReplRows, fidBveCoreParityRewireRows,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact (h135 e he hnm).symm
    · exact (h374 e he hnm).symm
    · exact (h375 e he hnm).symm
    · exact (h415 e he hnm).symm
    · exact (h421 e he hnm).symm
    · exact (h423 e he hnm).symm
    · exact (h438 e he hnm).symm
    · exact (h440 e he hnm).symm
    · exact (h444 e he hnm).symm
    · exact (h243 e he hnm).symm
    · exact (h137 e he hnm).symm
    · exact (h418 e he hnm).symm
  have hBefDisj : ∀ p ∈ fidBveCoreParityBeforeRows, ∀ b ∈ p.2,
      b.name ∉ m8SwBaseSpecTable.map SpecEntry.name := by
    have hnm_sw : m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name := by
      have hm := congrArg (List.map Prod.fst) m8cp_swBase_sigs
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    rw [hnm_sw]
    intro p hp b hb hmem
    simp only [fidBveCoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8cp_min_help_not_in_sw b hb hmem
    · exact fid_bveHelperRows_disj_sw b hb hmem
  have hSwM7 : ∀ {nm as bs} {sp : Spec as bs},
      (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      (∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) →
      ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv nm as bs a m Q X :=
    fun hm hnef hncp hno a m Q X hs =>
    .base hncp (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _
      (M7FidelityEnv.base hnef (m7FidBase_row_mem hm hno a m Q X hs)))
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  rcases ofTable_patchRows_elim hReplSigs hBefDisj h with hr | hb | hbase
  · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
    rcases List.mem_append.mp hr with hrRepl | hrRew
    · simp only [fidBveCoreParityReplRows, List.mem_cons, List.not_mem_nil, or_false] at hrRepl
      rcases hrRepl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · cases has; cases hrs; exact .minShrinkM6 (m8MinShrinkSpec_monoX hcast)
      · cases has; cases hrs
        exact hSwM7 m7FidBase_bveVar_mem (by decide) (by decide) (fun _ _ _ _ h => h) _ _ _ _ hcast
      · cases has; cases hrs
        exact hSwM7 (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl))
          (by decide) (by decide) (fun _ _ _ _ h => h) _ _ _ _ hcast
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact .varKey hcast
      · cases has; cases hrs
        exact hSwM7 m7FidBase_elimBveM7_mem (by decide) (by decide) (fun _ _ _ _ h => h)
          _ _ _ _ hcast
      · cases has; cases hrs
        exact hSwM7 (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 42) rfl))
          (by decide) (by decide) (fun _ _ _ _ h => h) _ _ _ _ hcast
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact hSwM7 hc3p.probeDticks (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h) _ _ _ _
          (FullM6Hdr.m6HdrW2aSpec_monoX hcast)
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact hSwM7 m7FidBase_probeM6_mem (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h) _ _ _ _
          (FullM6Orch.m6ProbeSpec_monoX hcast)
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact hSwM7 m7FidBase_searchM6_mem (by decide) (by decide)
          (fun _ _ _ _ h => fullM6SearchSpec_monoX h) _ _ _ _ (fullM6SearchSpec_monoX hcast)
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact hSwM7 m8cp_hasTernary_mem (by decide) (by decide)
          (fun _ _ _ _ h => h) _ _ _ _ hcast
    · simp only [fidBveCoreParityRewireRows, List.mem_cons, List.not_mem_nil, or_false] at hrRew
      rcases hrRew with rfl | rfl
      · cases has; cases hrs; exact .minShrink (m8MinShrinkSpec_monoX hcast)
      · cases has; cases hrs
        dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast; rw [ite_eq_left rfl] at hcast
        exact .heapPush hcast
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    simp only [fidBveCoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .minHelp (ofTable_of_cast hb_p m8MinHelperRows_nodup rfl has hrs hcast)
    · exact .bveHelp (ofTable_of_cast hb_p fidBveHelperRows_nodup rfl has hrs hcast)
  · rcases hbase with ⟨hnr, _, htbl⟩
    refine .base (fun hexcl => ?_) (m8cp_sw_base_to_env htbl)
    simp only [m8CpExclNames, List.mem_cons, List.not_mem_nil, or_false] at hexcl
    rcases hexcl with rfl | rfl | rfl | rfl
    · exact hnr (by simp [fidBveCoreParityReplRows])
    · exact hnr (by simp [fidBveCoreParityRewireRows])
    · exact hnr (by simp [fidBveCoreParityReplRows])
    · exact hnr (by simp [fidBveCoreParityRewireRows])

theorem fidBveCoreParityEnv_of_specTable {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidBveCoreParitySpecTable f as bs xs m Q X) :
    fidBveCoreParityEnv f as bs xs m Q X :=
  fidCoreParity_env_of_m8SwBase h

private theorem fidBveCoreParityEnv_name_cases {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (h : fidBveCoreParityEnv f as bs xs m Q X) :
    (f ∉ m8CpExclNames ∧ m8FidV123t2Env f as bs xs m Q X) ∨
    f = "full_min_shrink_m6" ∨ f = "full_min_shrink" ∨
    f = "full_bve_var_key_m7" ∨ f = "full_bve_heap_push_m7" ∨
    Env.ofTable m8MinHelperRows f as bs xs m Q X ∨
    Env.ofTable fidBveHelperRows f as bs xs m Q X := by
  change FidBveCoreParityEnv m8FidV123t2Env f as bs xs m Q X at h
  cases h with
  | base hne hb => exact Or.inl ⟨hne, hb⟩
  | minShrinkM6 _ => exact Or.inr (Or.inl rfl)
  | minShrink _ => exact Or.inr (Or.inr (Or.inl rfl))
  | varKey _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | heapPush _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | minHelp ht => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  | bveHelp ht => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))

private theorem fidBveCoreParityEnv_minShrinkM6_inv {a m Q X}
    (h : fidBveCoreParityEnv "full_min_shrink_m6" [i64] [] a m Q X) :
    m8MinShrinkSpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveCoreParityEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_min_shrink_m6" → HEq xs a → HEq Q' Q → m8MinShrinkSpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_min_shrink_m6" ∈ m8CpExclNames)) hne
  | minShrinkM6 hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | minShrink _ => exact absurd hf (by decide)
  | varKey _ => exact absurd hf (by decide)
  | heapPush _ => exact absurd hf (by decide)
  | minHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_min_shrink_m6" : Sym) ∈ m8MinHelperRows.map SpecEntry.name) (by decide)
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_min_shrink_m6" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private theorem fidBveCoreParityEnv_minShrink_inv {a m Q X}
    (h : fidBveCoreParityEnv "full_min_shrink" [i64] [] a m Q X) :
    m8MinShrinkSpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveCoreParityEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_min_shrink" → HEq xs a → HEq Q' Q → m8MinShrinkSpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_min_shrink" ∈ m8CpExclNames)) hne
  | minShrinkM6 _ => exact absurd hf (by decide)
  | minShrink hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | varKey _ => exact absurd hf (by decide)
  | heapPush _ => exact absurd hf (by decide)
  | minHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_min_shrink" : Sym) ∈ m8MinHelperRows.map SpecEntry.name) (by decide)
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_min_shrink" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private theorem fidBveCoreParityEnv_varKey_inv {a m Q X}
    (h : fidBveCoreParityEnv "full_bve_var_key_m7" [i64, i32] [i64] a m Q X) :
    m8BveVarKeySpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveCoreParityEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_bve_var_key_m7" → HEq xs a → HEq Q' Q → m8BveVarKeySpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_bve_var_key_m7" ∈ m8CpExclNames)) hne
  | minShrinkM6 _ => exact absurd hf (by decide)
  | minShrink _ => exact absurd hf (by decide)
  | varKey hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | heapPush _ => exact absurd hf (by decide)
  | minHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_var_key_m7" : Sym) ∈ m8MinHelperRows.map SpecEntry.name) (by decide)
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_var_key_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private theorem fidBveCoreParityEnv_heapPush_inv {a m Q X}
    (h : fidBveCoreParityEnv "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    m8BveHeapPushSpec a m Q X := by
  suffices H : ∀ {f as bs xs Q'}, FidBveCoreParityEnv m8FidV123t2Env f as bs xs m Q' X →
      f = "full_bve_heap_push_m7" → HEq xs a → HEq Q' Q → m8BveHeapPushSpec a m Q X from
    H h rfl HEq.rfl HEq.rfl
  intro f as bs xs Q' h' hf hxs hq
  cases h' with
  | base hne _ => exact absurd (hf ▸ (by decide : "full_bve_heap_push_m7" ∈ m8CpExclNames)) hne
  | minShrinkM6 _ => exact absurd hf (by decide)
  | minShrink _ => exact absurd hf (by decide)
  | varKey _ => exact absurd hf (by decide)
  | heapPush hs => rw [← eq_of_heq hxs, ← eq_of_heq hq]; exact hs
  | minHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_heap_push_m7" : Sym) ∈ m8MinHelperRows.map SpecEntry.name) (by decide)
  | bveHelp ht =>
    exact absurd (hf ▸ m8CoreParity_ofTable_name_mem ht :
      ("full_bve_heap_push_m7" : Sym) ∈ fidBveHelperRows.map SpecEntry.name) (by decide)

private def fidBveCoreParitySkipNames : List Sym :=
  fidBveCoreParityRepls.map Fn.name ++
    ["full_min_shrink", "full_analyze", "full_analyze_core_m6", "full_bve_heap_push_m7"]

private theorem fidBveCoreParity_noCallBad :
    PatchModule.checkNoCallBad fidBveCoreParitySkipNames m8CpExclNames m8FidV123t2Fns = true := by
  t_kernel_rfl

/-- Closed unconditional `472/472` `ModuleOk` certifying `fidBveCoreParityModule` under
`fidBveCoreParityEnv`. -/
theorem fidBveCoreParity_moduleOk :
    ModuleOk fidBveCoreParityEnv fidBveCoreParityModule := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have hBaseM7 : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      fidBveCoreParityEnv f as bs xs m Q X := fun _ _ _ _ _ _ _ hne h =>
    .base hne (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ h)
  have hSw : ∀ e ∈ m8SweepEnvRows, ∀ xs m Q X,
      Env.ofTable m8SweepEnvRows e.name e.as e.rs xs m Q X →
      fidBveCoreParityEnv e.name e.as e.rs xs m Q X := fun _ _ _ _ _ _ h => .base (by
    have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
        (fun s => !(m8CpExclNames.contains s)) = true := by decide
    have hm := List.all_eq_true.mp hdisj _ (m8Sw_ofTable_name_mem h)
    simp only [Bool.not_eq_true'] at hm
    simpa using hm) (.sweep h)
  have hVarM7 := fid_varM7_wp hBaseM7 (fun _ _ _ _ _ _ h => .bveHelp h)
  have hElimBve := fid_elimBveM7_wp hBaseM7 (fun _ _ _ _ h => .heapPush h)
  have hElimM6 := fid_eliminateM6_wp hBaseM7
  have hHeapPush := fid_heapPush_wp hBaseM7 (fun _ _ _ _ h => .varKey h)
  have hBR : ∀ {f as bs sp}, (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      ∀ (hnmf : f ∉ mfExclNames) (hncp : f ∉ m8CpExclNames)
        (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)),
      ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv f as bs a m Q X :=
    fun hm hnmf hncp hno a m Q X hs =>
      hBaseM7 _ _ _ a m Q X hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hm hno a m Q X hs))
  have hCoreWp : ∀ xs m Q X, FullM6Hdr.m6HdrAnalyzeSpec xs m Q X →
      Func.wp fidBveCoreParityEnv m8AnalyzeCoreM6Fn.body xs m Q X :=
    fun xs m Q X hs => m8_analyze_core_m6_m8_wp fidBveCoreParityEnv
      (hBR hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2p.anaFailedLit (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
      (hBR m7FidBase_deduce1uipM6Hdr_mem (by decide) (by decide)
        (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h))
      (hBR hc2p.restoreBumpAna (by decide) (by decide)
        (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
      (fun _ _ _ _ h => .minShrinkM6 h)
      (hBR hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
      (hBR hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
      xs m Q X hs
  have hMinImpl : TableImpl fidBveCoreParityEnv m8MinHelpers m8MinHelperRows :=
    m8cp_minHelper_impl hBaseM7 (fun _ _ _ _ _ _ h => .minHelp h)
  have hBveHelpImpl : TableImpl fidBveCoreParityEnv fidBveHelpers fidBveHelperRows :=
    fid_bve_helpers_impl fidBveCoreParityEnv hBaseM7 hSw (fun _ _ _ _ _ _ h => .bveHelp h)
  refine m8cp_patch_moduleOk_of_noCallBad m8FidV123t2_moduleOk
    fidBveCoreParity_fast_acyclic.1 fidBveCoreParity_fast_acyclic.2
    fidBveCoreParityRepls_wf (fun p hp h hh => by
      simp only [fidBveCoreParityBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact m8CoreParityBefores_wf ("full_min_shrink_m6", m8MinHelpers)
          (by simp [m8CoreParityBefores]) h hh
      · exact fidBveHelpers_wf h hh)
    fidBveCoreParity_noCallBad (fun _ _ _ _ _ _ _ hne h => .base hne h) ?_ ?_ ?_ ?_
  · intro g hg hskip _hnone
    simp only [fidBveCoreParitySkipNames, fidBveCoreParityRepls, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none _hnone
        (by simp [fidBveCoreParityRepls, h]))
    · obtain rfl := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
        (List.mem_of_getElem? m8cp_sw_fn_137) (h.trans rfl)
      intro xs m Q X hsp
      exact full_min_shrink_m8_wp fidBveCoreParityEnv (fun _ _ _ _ s => .minShrinkM6 s)
        xs m Q X (fidBveCoreParityEnv_minShrink_inv hsp)
    · obtain rfl := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
        (List.mem_of_getElem? m8cp_sw_fn_149) (h.trans rfl)
      intro xs m Q X hsp
      have hSwToM7 : ∀ {xs m Q X}, m8FidV123t2Env "full_analyze" [i64] [i64] xs m Q X →
          m7FidelityEnv "full_analyze" [i64] [i64] xs m Q X := fun hb =>
        fid_m8SwToM7_of_not_sw (by decide) (by decide) (by decide) (by decide)
          (m8cp_not_in_swRows _ (by t_kernel_rfl)) hb
      have hsp' : m8FidV123t2Env "full_analyze" [i64] [i64] xs m Q X := by
        rcases fidBveCoreParityEnv_name_cases hsp with ⟨_, hb⟩ | hc | hc | hc | hc | hm | hm
        · exact hb
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
        · have hm2 : ("full_analyze" : Sym) ∈ fidBveHelperRows.map SpecEntry.name :=
            m8CoreParity_ofTable_name_mem hm
          exact absurd hm2 (by decide)
      have hs0 := fid_bve_ofTable_to_m7_elim hSwToM7 m8cp_analyzeM5_mem (by decide) hsp'
      exact m8_analyze_m8_wp fidBveCoreParityEnv
        (hBR hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.deduce1uip)
          (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m8cp_restoreBumpAnaM5_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (fun _ _ _ _ hs => .minShrink hs)
        (hBR hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X hs0
    · obtain rfl := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
        (List.mem_of_getElem? m8cp_sw_fn_150) (h.trans rfl)
      intro xs m Q X hsp
      have hSwToM7 : ∀ {xs m Q X}, m8FidV123t2Env "full_analyze_core_m6" [i64] [i64] xs m Q X →
          m7FidelityEnv "full_analyze_core_m6" [i64] [i64] xs m Q X := fun hb =>
        fid_m8SwToM7_of_not_sw (by decide) (by decide) (by decide) (by decide)
          (m8cp_not_in_swRows _ (by t_kernel_rfl)) hb
      have hsp' : m8FidV123t2Env "full_analyze_core_m6" [i64] [i64] xs m Q X := by
        rcases fidBveCoreParityEnv_name_cases hsp with ⟨_, hb⟩ | hc | hc | hc | hc | hm | hm
        · exact hb
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)
        · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
        · exact absurd (m8CoreParity_ofTable_name_mem hm) (by decide)
      exact hCoreWp xs m Q X (FullM6Hdr.m6HdrAnalyzeSpec_monoX
        (fid_bve_ofTable_to_m7_elim hSwToM7
          (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.analyzeCoreM6) (by decide) hsp'))
    · obtain rfl := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup hg
        (List.mem_of_getElem? m8cp_sw_fn_418) (h.trans rfl)
      intro xs m Q X hsp
      exact hHeapPush xs m Q X (fidBveCoreParityEnv_heapPush_inv hsp)
  · intro g hg hskip hr xs m Q X hsp
    rcases fidBveCoreParityEnv_name_cases hsp with ⟨_, hb⟩ | heq | heq | heq | heq | hm | hm
    · exact hb
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hr (by rw [heq]; decide))
    · exact False.elim (hskip (heq ▸ by decide))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hr (by rw [heq]; decide))
    · exact False.elim (hskip (heq ▸ by decide))
    · exact False.elim (by
        rcases List.mem_map.mp (m8CoreParity_ofTable_name_mem hm) with ⟨e, he, hnm⟩
        exact m8cp_min_help_not_in_sw e he (hnm ▸ List.mem_map_of_mem hg))
    · exact False.elim (fid_sw_helpers_not_mem g hg (m8CoreParity_ofTable_name_mem hm))
  · intro r hr xs m Q X hsp
    have hElimSw : ∀ {nm as bs} {sp : Spec as bs},
        nm ∈ ["full_bve_var_m7", "full_bve_var", "full_elim_bve_m7", "full_eliminate_m6",
          "full_probe_dticks_m6_hdr", "full_probe_m6", "full_search_m6", "full_has_ternary"] →
        (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
        nm ∉ mfExtraRows.map SpecEntry.name →
        ∀ {xs m Q X}, fidBveCoreParityEnv nm as bs xs m Q X →
          sp xs m Q (fun _ _ _ _ => False) := by
      intro nm as bs sp hnf hm hnex xs m Q X hsp'
      have hSwToM7 : ∀ {xs m Q X}, m8FidV123t2Env nm as bs xs m Q X →
          m7FidelityEnv nm as bs xs m Q X := fun hb => fid_m8SwToM7_of_not_sw
          (by rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by
            have hchk : (["full_bve_var_m7", "full_bve_var", "full_elim_bve_m7",
                "full_eliminate_m6", "full_probe_dticks_m6_hdr", "full_probe_m6",
                "full_search_m6", "full_has_ternary"] : List Sym).all
                (fun s => !((m8SweepEnvRows.map SpecEntry.name).contains s)) = true := by
              t_kernel_rfl
            have h0 := List.all_eq_true.mp hchk nm hnf
            simp only [Bool.not_eq_true'] at h0; simpa using h0)
          hb
      rcases fidBveCoreParityEnv_name_cases hsp' with ⟨_, hb⟩ | hc | hc | hc | hc | hm' | hm'
      · exact fid_bve_ofTable_to_m7_elim hSwToM7 hm hnex hb
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
          nm = "full_search_m6" ∨ nm = "full_has_ternary")
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
          nm = "full_search_m6" ∨ nm = "full_has_ternary")
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
          nm = "full_search_m6" ∨ nm = "full_has_ternary")
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      · exact absurd hc (by rcases (by simpa using hnf :
          nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
          nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
          nm = "full_search_m6" ∨ nm = "full_has_ternary")
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      · have hni : nm ∉ m8MinHelperRows.map SpecEntry.name := by
          rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact absurd (m8CoreParity_ofTable_name_mem hm') hni
      · have hni : nm ∉ fidBveHelperRows.map SpecEntry.name := by
          rcases (by simpa using hnf :
            nm = "full_bve_var_m7" ∨ nm = "full_bve_var" ∨ nm = "full_elim_bve_m7" ∨
            nm = "full_eliminate_m6" ∨ nm = "full_probe_dticks_m6_hdr" ∨ nm = "full_probe_m6" ∨
            nm = "full_search_m6" ∨ nm = "full_has_ternary")
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact absurd (m8CoreParity_ofTable_name_mem hm') hni
    simp only [fidBveCoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine full_min_shrink_m6_m8_wp fidBveCoreParityEnv
        (fun a m Q X hs => hBaseM7 _ _ _ a m Q X (by decide)
          (mf_extra_at 10 "full_sort_tmp" [i64] [] FullM7AnalyzeSort.m7SortTmpSpec rfl
            (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h) a m Q X hs))
        (fun a m Q X hs => hBaseM7 _ _ _ a m Q X (by decide)
          (mf_extra_at 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl
            (fun _ _ _ _ h => h) a m Q X hs))
        (fun a m Q X hs => .minHelp
          (Env.ofTable_of_mem (e := m8MinHelperRows[0]'(by decide)) List.mem_cons_self
            m8MinHelperRows_nodup (m8MinLitDfsSpec_monoX hs)))
        (fun a m Q X hs => .minHelp
          (Env.ofTable_of_mem (e := m8MinHelperRows[2]'(by decide))
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            m8MinHelperRows_nodup (m8ShrinkBlkBoolSpec_monoX hs)))
        xs m Q X (fidBveCoreParityEnv_minShrinkM6_inv hsp)
    · exact hVarM7 xs m Q X (hElimSw (by decide) m7FidBase_bveVar_mem (by decide) hsp)
    · exact full_bve_var_fid_wp fidBveCoreParityEnv
        (m8cp_base_row hBaseM7 m7FidBase_bveVar_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (hElimSw (by decide)
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl)) (by decide) hsp)
    · exact full_bve_var_key_m7_m8_wp fidBveCoreParityEnv xs m Q X
        (fidBveCoreParityEnv_varKey_inv hsp)
    · exact hElimBve xs m Q X (hElimSw (by decide) m7FidBase_elimBveM7_mem (by decide) hsp)
    · exact hElimM6 xs m Q X (hElimSw (by decide)
        (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 42) rfl)) (by decide) hsp)
    · refine full_probe_dticks_m6_hdr_m8_wp fidBveCoreParityEnv
        (hBR hc1.hdrGetWm (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX
          (hElimSw (by decide) hc3p.probeDticks (by decide) hsp))
    · refine full_probe_m6_m8_wp fidBveCoreParityEnv
        (hBR hc3p.probeDticks (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        (hBR hc1.log10Q16M7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
        (hBR hc1.scaleDeltaM5 (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.vivifyM6Hdr (by decide) (by decide)
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h))
        (hBR hc2.enterDense (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1p.delaying (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        (hBR hc2p.congruenceDense (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2.rebuildWatches (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1.hdrSetWm (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        (hBR hc1p.reduceDelay (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        (hBR hc1p.bumpDelay (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h))
        (hBR m7FidBase_sweepDenseM6_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.substitute (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidBase_probeTailM6_mem (by decide) (by decide)
          (fun _ _ _ _ h => m6ProbeTailSpec_monoX h))
        (hBR hc2p.backboneM6 (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidP3MinU64_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidP3Factor_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (FullM6Orch.m6ProbeSpec_monoX
          (hElimSw (by decide) m7FidBase_probeM6_mem (by decide) hsp))
    · refine full_search_m6_m8_wp fidBveCoreParityEnv
        (hBR hc3.luckyLateM7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h))
        (FullM7Proof.m7_fullPropagate_to_bcpS15
          (hBR hc1.propagate (by decide) (by decide) (fun _ _ _ _ h => h)))
        (hBR hc2.analyzeM6 (by decide) (by decide)
          (fun _ _ _ _ h => FullM6Hdr.m6HdrAnalyzeSpec_monoX h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reduceM6) (by decide) (by decide)
          (fun _ _ _ _ h => m6ReduceSpec_monoX h))
        (hBR hc3.switchModeM7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h))
        (hBR hc2.restartDue (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2.restart (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6) (by decide) (by decide)
          (fun _ _ _ _ h => h))
        (hBR hc2.rephase (by decide) (by decide) (fun _ _ _ _ h => m7RephaseSpec_monoX h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6) (by decide) (by decide)
          (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
        (fun a m Q X hs => hBaseM7 _ _ _ a m Q X (by decide)
          (mf_extra_at 59 "m6_hdr_decide_fid" [i64] [i64] FullM6Hdr.m6HdrDecideSpec rfl
            (fun _ _ _ _ h => FullM6Hdr.m6HdrDecideSpec_monoX h) a m Q X hs))
        xs m Q X (fullM6SearchSpec_monoX
          (hElimSw (by decide) m7FidBase_searchM6_mem (by decide) hsp))
    · exact m7HasTernaryFn_wp fidBveCoreParityEnv xs m Q X
        (hElimSw (by decide) m8cp_hasTernary_mem (by decide) hsp)
  · intro p hp h hh xs m Q X hs
    simp only [fidBveCoreParityBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine m8cp_tableImpl_mem_wp hMinImpl ?_ h hh xs m Q X hs
      intro r hr' xs' m' Q' X' hs'
      have hr_nm : r.name ∈ m8MinHelperRows.map SpecEntry.name := List.mem_map_of_mem hr'
      have hdisj_bve : r.name ∉ fidBveHelperRows.map SpecEntry.name := by
        have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at h1
        rw [h1]
        have hchk := List.all_eq_true.mp fid_bveHelp_disj_minRows r.name hr_nm
        simp only [Bool.not_eq_true'] at hchk; simpa using hchk
      have hdisj_ex : r.name ∉ m8CpExclNames := by
        have hchk : (m8MinHelperRows.map SpecEntry.name).all
            (fun s => !(m8CpExclNames.contains s)) = true := by decide
        have := List.all_eq_true.mp hchk r.name hr_nm
        simp only [Bool.not_eq_true'] at this; simpa using this
      rcases fidBveCoreParityEnv_name_cases hs' with ⟨_, hb⟩ | hc | hc | hc | hc | hm | hm
      · have hnot_sw : r.name ∉ m8SweepEnvRows.map SpecEntry.name := by
          have hchk : (m8MinHelperRows.map SpecEntry.name).all
              (fun s => !((m8SweepEnvRows.map SpecEntry.name).contains s)) = true := by decide
          have := List.all_eq_true.mp hchk r.name hr_nm
          simp only [Bool.not_eq_true'] at this; simpa using this
        have hm7 := fid_m8SwToM7_of_not_sw
          (by
            have hchk : (m8MinHelperRows.map SpecEntry.name).all
                (fun s => s != "full_extend_push2") = true := by decide
            intro h; exact absurd h (by
              simpa using List.all_eq_true.mp hchk r.name hr_nm))
          (by
            have hchk : (m8MinHelperRows.map SpecEntry.name).all
                (fun s => s != "full_cong_enq_var") = true := by decide
            intro h; exact absurd h (by
              simpa using List.all_eq_true.mp hchk r.name hr_nm))
          (by
            have hchk : (m8MinHelperRows.map SpecEntry.name).all
                (fun s => s != "full_cong_eval_gate") = true := by decide
            intro h; exact absurd h (by
              simpa using List.all_eq_true.mp hchk r.name hr_nm))
          (by
            have hchk : (m8MinHelperRows.map SpecEntry.name).all
                (fun s => s != "full_cong_worklist") = true := by decide
            intro h; exact absurd h (by
              simpa using List.all_eq_true.mp hchk r.name hr_nm))
          hnot_sw hb
        exact False.elim (m8cp_help_not_in_m7FidEnv (H := m8BveHook) (Or.inl hr_nm) hm7)
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact (m8cp_ofTable_sig_elim m8MinHelperRows_nodup hr' hm).2.2
      · exact absurd (m8CoreParity_ofTable_name_mem hm) hdisj_bve
    · refine m8cp_tableImpl_mem_wp hBveHelpImpl ?_ h hh xs m Q X hs
      intro r hr' xs' m' Q' X' hs'
      have hr_nm : r.name ∈ fidBveHelperRows.map SpecEntry.name := List.mem_map_of_mem hr'
      have hdisj_min : r.name ∉ m8MinHelperRows.map SpecEntry.name := by
        have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at h1
        intro hm
        have hchk := List.all_eq_true.mp fid_bveHelp_disj_minRows r.name hm
        simp only [Bool.not_eq_true'] at hchk
        exact absurd (h1 ▸ hr_nm) (by simpa using hchk)
      have hdisj_ex : r.name ∉ m8CpExclNames := by
        have h1 := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at h1
        have hchk : (fidBveHelpers.map Fn.name).all
            (fun s => !(m8CpExclNames.contains s)) = true := by decide
        have := List.all_eq_true.mp hchk r.name (h1 ▸ hr_nm)
        simp only [Bool.not_eq_true'] at this; simpa using this
      rcases fidBveCoreParityEnv_name_cases hs' with ⟨_, hb⟩ | hc | hc | hc | hc | hm | hm
      · exact False.elim (fid_bveHelp_not_in_swEnv hr_nm hb)
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd hc (fun h => hdisj_ex (by simp [m8CpExclNames, h]))
      · exact absurd (m8CoreParity_ofTable_name_mem hm) hdisj_min
      · exact (m8cp_ofTable_sig_elim fidBveHelperRows_nodup hr' hm).2.2

theorem fidBveCoreParity_tableImpl :
    TableImpl fidBveCoreParityEnv fidBveCoreParityModule.fns fidBveCoreParitySpecTable :=
  tableImpl_of_moduleOk fidBveCoreParity_moduleOk fidBveCoreParitySpecTable_sigs
    fidBveCoreParitySpecTable_nodup (fun _ _ _ _ _ _ ht => fidBveCoreParityEnv_of_specTable ht)

theorem fidBveCoreParity_solveBytes_mem : m6oSolveBytesFn ∈ fidBveCoreParityModule.fns := by
  change m6oSolveBytesFn ∈ fidBveCoreParityFns
  exact m8cp_patchFns_mem_of_ne m8FidV123t2_solveBytes_mem fun r hr => by
    simp only [fidBveCoreParityRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Top-level unconditional byte-level UNSAT soundness of `fidBveCoreParityModule` (`472` fns). -/
theorem fidBveCoreParity_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBveCoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of fidBveCoreParity_moduleOk fidBveCoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))
    hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidBveCoreParityModule`. -/
theorem fidBveCoreParity_solve_bytes_host_sound
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
`fidBveCoreParityModule`. -/
theorem fidBveCoreParity_unsat_nv :
    Func.wp fidBveCoreParityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of fidBveCoreParity_moduleOk fidBveCoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))

/-! ## 6. Closed Environment Lookup Lemmas for Non-Vacuity Instantiation -/

theorem fidBveEnv_m7Base_of_mem {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveEnv nm as bs a m Q X := fun a m Q X hs =>
  .base (fun hex => hncp (by
    simp only [fidBveExclNames, List.mem_cons, List.not_mem_nil, or_false] at hex
    rcases hex with rfl | rfl <;> decide))
    (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _
      (M7FidelityEnv.base hnef (m7FidBase_row_mem hmem hno a m Q X hs)))

theorem fidBveCoreParityEnv_m7Base_of_mem {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv nm as bs a m Q X := fun a m Q X hs =>
  .base hncp (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _
    (M7FidelityEnv.base hnef (m7FidBase_row_mem hmem hno a m Q X hs)))

theorem fidBveEnv_helper_at {k : Nat} (hk : k < fidBveHelperRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidBveHelperRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveEnv nm as bs a m Q X :=
  fid_bveHelp_row (fun _ _ _ _ _ _ h => .bveHelp h) k hk heq hno

theorem fidBveCoreParityEnv_helper_at {k : Nat} (hk : k < fidBveHelperRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidBveHelperRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv nm as bs a m Q X :=
  fid_bveHelp_row (fun _ _ _ _ _ _ h => .bveHelp h) k hk heq hno

theorem fidBveEnv_sweep_at {k : Nat} (hk : k < m8SweepEnvRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m8SweepEnvRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveEnv nm as bs a m Q X :=
  fid_sw_row_at (fun e _ _ _ _ _ h => .base (by
    have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
        (fun s => !(fidBveExclNames.contains s)) = true := by decide
    have hm := List.all_eq_true.mp hdisj _ (m8Sw_ofTable_name_mem h)
    simp only [Bool.not_eq_true'] at hm; simpa using hm) (.sweep h)) k hk heq hno

theorem fidBveCoreParityEnv_sweep_at {k : Nat} (hk : k < m8SweepEnvRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m8SweepEnvRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv nm as bs a m Q X :=
  fid_sw_row_at (fun e _ _ _ _ _ h => .base (by
    have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
        (fun s => !(m8CpExclNames.contains s)) = true := by decide
    have hm := List.all_eq_true.mp hdisj _ (m8Sw_ofTable_name_mem h)
    simp only [Bool.not_eq_true'] at hm; simpa using hm) (.sweep h)) k hk heq hno

theorem fidBveEnv_heapPush {a m Q X} (h : m8BveHeapPushSpec a m Q X) :
    fidBveEnv "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X :=
  .heapPush h

theorem fidBveCoreParityEnv_heapPush {a m Q X} (h : m8BveHeapPushSpec a m Q X) :
    fidBveCoreParityEnv "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X :=
  .heapPush h

theorem fidBveEnv_assignLvl {a m Q X} (h : Full.fullAssignLvlSpec a m Q X) :
    fidBveEnv "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X :=
  fidBveEnv_m7Base_of_mem (m7FidPart1Callees_of_sub m7FidBase_part1_mem).assignLvl
    (by decide) (by decide) (fun _ _ _ _ hs => hs) _ _ _ _ h

theorem fidBveCoreParityEnv_assignLvl {a m Q X} (h : Full.fullAssignLvlSpec a m Q X) :
    fidBveCoreParityEnv "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X :=
  fidBveCoreParityEnv_m7Base_of_mem (m7FidPart1Callees_of_sub m7FidBase_part1_mem).assignLvl
    (by decide) (by decide) (fun _ _ _ _ hs => hs) _ _ _ _ h

theorem fidBveEnv_m7BveRow {k : Nat} (hk : k < m7FidBveRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames) :
    ∀ a m Q X, sp a m Q X → fidBveEnv nm as bs a m Q X :=
  fidBveEnv_m7Base_of_mem (m7FidBase_bve_mem _ (heq ▸ List.getElem_mem hk)) hnef hncp
    (fun a m Q X hs => by
      have hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBveClosedRows :=
        List.mem_append_left _ (heq ▸ List.getElem_mem hk)
      simpa only [SpecEntry.eff, ↓reduceIte] using
        mf_bve_noExit_spec ⟨nm, as, bs, sp, true⟩ hmem a m Q X hs)

theorem fidBveCoreParityEnv_m7BveRow {k : Nat} (hk : k < m7FidBveRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hnef : nm ∉ mfExclNames) (hncp : nm ∉ m8CpExclNames) :
    ∀ a m Q X, sp a m Q X → fidBveCoreParityEnv nm as bs a m Q X :=
  fidBveCoreParityEnv_m7Base_of_mem (m7FidBase_bve_mem _ (heq ▸ List.getElem_mem hk)) hnef hncp
    (fun a m Q X hs => by
      have hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBveClosedRows :=
        List.mem_append_left _ (heq ▸ List.getElem_mem hk)
      simpa only [SpecEntry.eff, ↓reduceIte] using
        mf_bve_noExit_spec ⟨nm, as, bs, sp, true⟩ hmem a m Q X hs)

end LeanQbe.T.Examples.Kissat.FullFidelityBve

end
