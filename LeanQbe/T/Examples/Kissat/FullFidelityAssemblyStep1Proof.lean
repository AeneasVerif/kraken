/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone1
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7
import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 1 (`FullFidelityAssemblyStep1Proof`)

Certifies `FullFidelityAssemblyStep1.fidStep1Module` (`469` fns, `0` externs, `0` exits) via
`PatchModule.patchBundle_moduleOk_sameSpecs` + `FullFidelityAssemblyUtil`:
1. `fidStep1Bundle : PatchBundle` layering `FullFidelitySweep.fidSweepRepls` atop `fidBaseModule`.
2. Closed `469/469` `fidStep1_moduleOk : ModuleOk fidStep1Env fidStep1Module`,
   `fidStep1Env_noExit`, `fidStep1_solve_bytes_sound`, `fidStep1_solve_bytes_host_sound`,
   `fidStep1_unsat_nv` (`XPost := False`, `std3`), and `fidStep1UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. `PatchBundle` & `ModuleOk` Over `fidBaseModule` (`469/469` Fns) -/

/-- The `4` unchanged `SpecEntry` rows for `FullFidelitySweep.fidSweepRepls`. -/
def fidStep1ReplRows : List SpecEntry :=
  [ ⟨"full_m6_sweep_cone", [i64, i32], [i64], m6SweepConeSpec, true⟩
  , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], m6SweepSimSpec, true⟩
  , ⟨"full_m6_collect_cands", [i64], [i32], m6CollectCandsSpec, true⟩
  , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩ ]

/-- Step-1 `PatchBundle` composing `FullFidelityBase` + `FullFidelitySweep`. -/
def fidStep1Bundle : PatchBundle where
  baseMod := fidBaseModule
  baseTable := fidBaseSpecTable
  baseOk := fidBase_moduleOk
  repls := fidSweepRepls
  replRows := fidStep1ReplRows

/-- Closed `Env` for `fidStep1Module` (`469` fns). -/
def fidStep1Env : Env := patchEnv fidStep1Bundle

theorem fidStep1_externs_empty : fidStep1Module.externs = [] := by
  t_kernel_rfl

theorem fidStep1Fns_length : fidStep1Fns.length = 469 := by
  rw [fidStep1Fns, patchFns_nil, PatchModule.spliceFns, List.length_map]
  exact fidBaseFns_length

private theorem fidStep1_slot {i : Nat} {s : SigEntry}
    (hi : fidBaseFns[i]?.map Fn.sig = some s) :
    ∃ g ∈ fidBaseFns, g.sig = s := by
  cases h : fidBaseFns[i]? with
  | none => simp [h] at hi
  | some g =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    exact ⟨g, List.mem_of_getElem? h, hi⟩

theorem fidStep1Module_replSigs_ok :
    ∀ r ∈ fidSweepRepls, ∀ g ∈ fidBaseModule.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  change g ∈ fidBaseFns at hg
  have hslot : ∀ {i : Nat} {s : SigEntry},
      fidBaseFns[i]?.map Fn.sig = some s → r.sig = s → r.name = g.name → r.sig = g.sig := by
    intro i s hi hrs hnm'
    obtain ⟨g0, hg0, hsg0⟩ := fidStep1_slot hi
    have hgnm : r.name = g0.name := congrArg Prod.fst (hrs.trans hsg0.symm)
    have heq := nodup_name_eq Fn.name fidBaseFns_names_nodup hg hg0 (hnm'.symm.trans hgnm)
    rw [heq, hsg0, hrs]
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hslot (i := 318) (by t_kernel_rfl :
      fidBaseFns[318]?.map Fn.sig = some ("full_m6_sweep_cone", [i64, i32], [i64])) rfl hnm
  · exact hslot (i := 323) (by t_kernel_rfl :
      fidBaseFns[323]?.map Fn.sig = some ("full_m6_sweep_sim", [i64, i32, i64], [i32])) rfl hnm
  · exact hslot (i := 336) (by t_kernel_rfl :
      fidBaseFns[336]?.map Fn.sig = some ("full_m6_collect_cands", [i64], [i32])) rfl hnm
  · exact hslot (i := 337) (by t_kernel_rfl :
      fidBaseFns[337]?.map Fn.sig = some ("full_m6_sweep_vars", [i64, i64, i64], [i64])) rfl hnm

theorem fidStep1Module_names_nodup : fidStep1Module.namesNodup := by
  change (fidStep1Module.fns.map Fn.name ++ fidStep1Module.externs.map Extern.name).Nodup
  rw [fidStep1_externs_empty, List.map_nil, List.append_nil]
  change ((patchFns fidSweepRepls [] fidBaseFns).map Fn.name).Nodup
  rw [patchFns_nil]
  have hsigs :
      (PatchModule.spliceFns fidSweepRepls fidBaseFns).map Fn.sig = fidBaseFns.map Fn.sig := by
    rw [PatchModule.spliceFns, List.map_map]
    refine List.map_congr_left fun f hf => ?_
    cases hfd : fidSweepRepls.find? (·.name == f.name) with
    | none => simp [hfd]
    | some r =>
      have hnm := beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hfd)
      simpa [hfd] using fidStep1Module_replSigs_ok r (List.mem_of_find?_eq_some hfd) f hf hnm
  have hm := congrArg (List.map Prod.fst) hsigs
  simp only [List.map_map, Function.comp_def, Fn.sig] at hm
  rw [hm]
  exact fidBaseFns_names_nodup

private theorem fidStep1Module_patchCallsOk :
    checkPatchCallsOk fidBaseModule fidSweepRepls [] = true := by
  t_kernel_rfl

private theorem fidStep1_front_nodup :
    (fidStep1Bundle.frontTable.map SpecEntry.name).Nodup := by
  change (fidStep1ReplRows.map SpecEntry.name).Nodup
  decide

private theorem fidStep1_frontRow {i : Nat} {nm : Sym} {as bs : List Ty} (sp : Spec as bs)
    (hi : fidStep1ReplRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    M6EnvSpec fidStep1Env nm sp := by
  intro a m Q X hs
  have he : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ fidStep1Bundle.frontTable :=
    List.mem_of_getElem? hi
  exact patchEnv_of_front_mem fidStep1Bundle fidStep1_front_nodup he (hno a m Q X hs)

private theorem fidStep1_baseRow_at (i : Nat) (nm : Sym) {as bs : List Ty} (sp : Spec as bs)
    (hi : fidBaseSpecTable[i]? = some ⟨nm, as, bs, sp, true⟩ := by t_kernel_rfl)
    (hf : fidStep1Bundle.frontTable.find? (·.name == nm) = none := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    M6EnvSpec fidStep1Env nm sp := by
  intro a m Q X hs
  dsimp only [fidStep1Env]
  rw [patchEnv_base_eq fidStep1Bundle hf]
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) fidBaseSpecTable_nodup (hno a m Q X hs)

private theorem fidStep1_sameSpecs :
    ∀ e ∈ fidStep1Bundle.frontTable, ∀ xs m P E,
      Env.ofTable fidBaseSpecTable e.name e.as e.rs xs m P E → e.eff xs m P E := by
  intro e he xs m P E hBase
  change e ∈ fidStep1ReplRows at he
  simp only [fidStep1ReplRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, hc⟩ := env_ofTable_sig_elim fidBaseSpecTable_nodup
      (List.mem_of_getElem? (i := 318) (by t_kernel_rfl :
        fidBaseSpecTable[318]? =
          some ⟨"full_m6_sweep_cone", [i64, i32], [i64], m6SweepConeSpec, true⟩)) hBase
    exact hc
  · obtain ⟨_, _, hc⟩ := env_ofTable_sig_elim fidBaseSpecTable_nodup
      (List.mem_of_getElem? (i := 323) (by t_kernel_rfl :
        fidBaseSpecTable[323]? =
          some ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], m6SweepSimSpec, true⟩)) hBase
    exact hc
  · obtain ⟨_, _, hc⟩ := env_ofTable_sig_elim fidBaseSpecTable_nodup
      (List.mem_of_getElem? (i := 336) (by t_kernel_rfl :
        fidBaseSpecTable[336]? =
          some ⟨"full_m6_collect_cands", [i64], [i32], m6CollectCandsSpec, true⟩)) hBase
    exact hc
  · obtain ⟨_, _, hc⟩ := env_ofTable_sig_elim fidBaseSpecTable_nodup
      (List.mem_of_getElem? (i := 337) (by t_kernel_rfl :
        fidBaseSpecTable[337]? =
          some ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩)) hBase
    exact hc

private theorem fidStep1_fn_eq_repl {fn r : Fn}
    (hfn : fn ∈ fidStep1Module.fns) (hr : r ∈ fidSweepRepls)
    (hnm : r.name = fn.name) : fn = r := by
  have hModNd : (fidStep1Module.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp fidStep1Module_names_nodup).1
  have hslot : ∀ {i : Nat} {nm : Sym},
      fidBaseFns[i]?.map Fn.name = some nm → ∃ g ∈ fidBaseFns, nm = g.name := by
    intro i nm hi
    cases h : fidBaseFns[i]? with
    | none => simp [h] at hi
    | some g =>
      simp only [h, Option.map_some, Option.some.injEq] at hi
      exact ⟨g, List.mem_of_getElem? h, hi.symm⟩
  have hmemBase : ∃ g ∈ fidBaseFns, r.name = g.name := by
    have hr' := hr
    simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hslot (i := 318) (by t_kernel_rfl :
        fidBaseFns[318]?.map Fn.name = some "full_m6_sweep_cone")
    · exact hslot (i := 323) (by t_kernel_rfl :
        fidBaseFns[323]?.map Fn.name = some "full_m6_sweep_sim")
    · exact hslot (i := 336) (by t_kernel_rfl :
        fidBaseFns[336]?.map Fn.name = some "full_m6_collect_cands")
    · exact hslot (i := 337) (by t_kernel_rfl :
        fidBaseFns[337]?.map Fn.name = some "full_m6_sweep_vars")
  obtain ⟨g, hg, hgn⟩ := hmemBase
  have hrm : r ∈ fidStep1Module.fns :=
    mem_patchFns_of_repl (by decide) hr hg hgn
  exact nodup_name_eq Fn.name hModNd hfn hrm hnm.symm

private theorem fidStep1_agree :
    ∀ s ∈ fidBaseModule.sigs,
      ∀ xs m P E, Env.ofTable fidBaseSpecTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv fidStep1Bundle s.1 s.2.1 s.2.2 xs m P E :=
  patchEnv_agree_of_sameSpecs fidStep1Bundle fidStep1_front_nodup fidStep1_sameSpecs

private theorem fidStep1_front_covered :
    ∀ fn, (fn ∈ fidSweepRepls ∨ fn ∈ ([] : List (Sym × List Fn)).flatMap Prod.snd) →
      (fidStep1Bundle.frontTable.find? (·.name == fn.name)).isSome = true := by
  intro fn hfn
  rcases hfn with hr | hb
  · simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · simp at hb

private theorem fidStep1_front_impl :
    ∀ fn e, fn ∈ fidStep1Bundle.patchedMod.fns →
      fidStep1Bundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidStep1Env fn e := by
  intro fn e hfn hf
  change fn ∈ fidStep1Module.fns at hfn
  change fidStep1ReplRows.find? (·.name == fn.name) = some e at hf
  have he : e ∈ fidStep1ReplRows := List.mem_of_find?_eq_some hf
  have hnm : e.name = fn.name :=
    beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == fn.name) hf)
  have r302 := fidStep1_baseRow_at 302 "full_m6_max_v" m6MaxVSpec
  have r304 := fidStep1_baseRow_at 304 "full_k6_init" k6InitSpec
  have r307 := fidStep1_baseRow_at 307 "full_k6_add_clause" k6AddClauseSpec
  have r317 := fidStep1_baseRow_at 317 "full_m6_dense_prop" m6DensePropSpec
  have r319 := fidStep1_baseRow_at 319 "full_m6_sweep_refine_sig" m6SweepRefineSigSpec
  have r321 := fidStep1_baseRow_at 321 "full_m6_sweep_solve" m6SweepSolveSpec
  have r322 := fidStep1_baseRow_at 322 "full_m6_sweep_flip_round" m6SweepFlipRoundSpec
  have r334 := fidStep1_baseRow_at 334 "full_m6_sweep_var" m6SweepVarSpec
  have r335 := fidStep1_baseRow_at 335 "full_m6_cand_sift" m6CandSiftSpec
  have r336 := fidStep1_frontRow (i := 2) (nm := "full_m6_collect_cands") m6CollectCandsSpec
  simp only [fidStep1ReplRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · have hfeq := fidStep1_fn_eq_repl hfn (r := fidSweepConeFn) (by simp [fidSweepRepls]) hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (fid_sweep_cone_wp fidStep1Env r302 r304 r307 xs m Q _ hs)
  · have hfeq := fidStep1_fn_eq_repl hfn (r := fidSweepSimFn) (by simp [fidSweepRepls]) hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (fid_sweep_sim_wp fidStep1Env r302 r321 r319 r322 xs m Q _ hs)
  · have hfeq := fidStep1_fn_eq_repl hfn (r := fidCollectCandsFn) (by simp [fidSweepRepls]) hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (fid_collect_cands_wp fidStep1Env r335 xs m Q _ hs)
  · have hfeq := fidStep1_fn_eq_repl hfn
      (r := FullFidelitySweep.fidSweepVarsFn) (by simp [fidSweepRepls]) hnm
    subst hfeq
    refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ m
      (fid_sweep_vars_wp fidStep1Env r302 r317 r336 r334 xs m Q _ hs)

/-- Closed `469/469` `ModuleOk` for `FullFidelityAssemblyStep1.fidStep1Module` under
`fidStep1Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep1_moduleOk : ModuleOk fidStep1Env fidStep1Module := by
  change ModuleOk (patchEnv fidStep1Bundle) fidStep1Bundle.patchedMod
  refine patchBundle_moduleOk_sameSpecs fidStep1Bundle
    fidStep1Module_names_nodup fidStep1Module_replSigs_ok ?_ fidStep1Module_patchCallsOk
    fidStep1_front_covered fidStep1_front_impl fidStep1_agree
  intro fn hfn
  rcases hfn with hr | hb
  · exact fidSweepRepls_wf fn hr
  · change fn ∈ ([] : List (Sym × List Fn)).flatMap Prod.snd at hb
    simp at hb

/-! ## 2. Exit-Freedom, UNSAT Soundness, Host Lift, `Mem 64` NV & `KissatUnsatPkg` -/

theorem fidStep1Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep1Env f as bs xs m Q X → fidStep1Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep1Bundle (by decide) fidBaseSpecTable_noExit

theorem fidStep1Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep1Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  patchEnv_solveBytes_of fidStep1Bundle (by decide)
    (fun _ _ _ _ hs => fidBaseEnv_solve_bytes_iff.mpr hs) a m Q X

theorem fidStep1_solveBytes_mem : m6oSolveBytesFn ∈ fidStep1Module.fns :=
  patchBundle_solveBytes_mem fidStep1Bundle fidBase_solveBytes_mem fun r hr => by
    change r ∈ fidSweepRepls at hr
    simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidStep1Module` (`469` fns, `XPost := False`). -/
theorem fidStep1_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep1Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep1_moduleOk fidStep1_solveBytes_mem
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep1Module`. -/
theorem fidStep1_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fid_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep1Module`. -/
theorem fidStep1_unsat_nv :
    Func.wp fidStep1Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep1_moduleOk fidStep1_solveBytes_mem
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep1_moduleOk`. -/
theorem fidStep1Module_acyclic : fidStep1Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep1_moduleOk

/-- Canonical `KissatUnsatPkg` for Step-1 (`fidStep1Module`, `fidInlPolicy`). -/
def fidStep1UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep1Module fidInlPolicy fidStep1_solveBytes_mem
    fidStep1Env fidStep1_moduleOk fidStep1Env_noExit
    (fun _ _ _ _ hs => fidStep1Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1

end
