/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone1
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6SatNv

/-!
# Kissat Full-Fidelity Sweep — Closed `ModuleOk`, Soundness & Concrete NV (`FullFidelitySweepProof`)

Certifies the `4`-function drop-in upstream Kissat 4.0.4 `sweep.c` parity replacement
(`FullFidelitySweep.fidSweepRepls`) with zero edits to existing `FullM4*`–`FullM8*` modules:
1. Closed `449/449` `ModuleOk` (`fidSweep_moduleOk`), `kissat_solve_bytes` UNSAT soundness,
   host-framed lift, and concrete `8,192 B` UNSAT non-vacuity (`fidSweep_unsat_nv`) over
   `FullM8SweepV2.m8FidV123t2Module` (`m8FidV123t2Env`).
2. Closed `471/471` `ModuleOk` (`fidSweepCoreParity_moduleOk`), `TableImpl`, `kissat_solve_bytes`
   UNSAT soundness, host-framed lift, and concrete UNSAT non-vacuity over
   `FullM8CoreParity.m8SweepV2CoreParityModule` (`m8SweepV2CoreParityEnv`).
3. Concrete non-bailout `Mem 64` UNSAT non-vacuity witnesses (`XPost := False`) exercising both
   initial (`comp = 0`, `need_mark = true`) and escalated/resumed (`comp = 1`, `gu[28] = 1`,
   `gu[29] = 1`, `need_mark = false`) sweep execution paths.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped Full.FullArenaTactics

/-! ## 1. Closed `449/449` `ModuleOk` & Soundness (`fidSweepModule`) -/

private theorem fid_sw_elim_row {i : Nat} {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : nm ∈ m8SwNamesLit)
    (hi : m8SweepEnvRows[i]? = some ⟨nm, as, bs, sp, true⟩)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hs : m8FidV123t2Env nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) := by
  have hof := m8Sw_elim_sweep_gen hmem hs
  have hr := List.mem_of_getElem? hi
  obtain ⟨_, _, heff⟩ := m8Sw_ofTable_sig_elim m8SweepEnvRows_nodup hr hof
  exact heff

/-- Closed `449/449` `ModuleOk` for `FullFidelitySweep.fidSweepModule` under `m8FidV123t2Env`
(`0` externs, `0` exits, `std3` axioms only). -/
theorem fidSweep_moduleOk : ModuleOk m8FidV123t2Env fidSweepModule := by
  dsimp only [fidSweepModule, fidSweepFns]
  change ModuleOk m8FidV123t2Env
    { m8FidV123t2Module with fns := spliceFns fidSweepRepls m8FidV123t2Module.fns }
  refine spliceModule_moduleOk_sameEnv m8FidV123t2_moduleOk fidSweep_acyclic fidSweepRepls_wf ?_
  intro r hr xs m Q X hs
  have r0 := m8Sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec
  have r2 := m8Sw_row 2 "full_k6_init" [i64, i32] [] k6InitSpec
  have r5 := m8Sw_row 5 "full_k6_add_clause" [i64, i64, i32] [.bool] k6AddClauseSpec
  have r15 := m8Sw_row 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec
  have r17 := m8Sw_row 17 "full_m6_sweep_refine_sig" [i64, i32, i32] [] m6SweepRefineSigSpec
  have r19 := m8Sw_row 19 "full_m6_sweep_solve" [i64, i32, i64] [i64] m6SweepSolveSpec
  have r20 := m8Sw_row 20 "full_m6_sweep_flip_round" [i64, i32] [i32] m6SweepFlipRoundSpec
  have r32 := m8Sw_row 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec
  have r33 := m8Sw_row 33 "full_m6_cand_sift" [i64, i64, i32, i32] [] m6CandSiftSpec
  have r34 := m8Sw_row 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fid_sweep_cone_wp m8FidV123t2Env r0 r2 r5 xs m Q X
      (fid_sw_elim_row (i := 16) (by decide) rfl hs)
  · exact fid_sweep_sim_wp m8FidV123t2Env r0 r19 r17 r20 xs m Q X
      (fid_sw_elim_row (i := 21) (by decide) rfl hs)
  · exact fid_collect_cands_wp m8FidV123t2Env r33 xs m Q X
      (fid_sw_elim_row (i := 34) (by decide) rfl hs)
  · exact fid_sweep_vars_wp m8FidV123t2Env r0 r15 r34 r32 xs m Q X
      (fid_sw_elim_row (i := 35) (by decide) rfl hs)

theorem fidSweepFns_wf : ∀ f ∈ fidSweepFns, f.Wf := by
  intro f hf
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
  exact (fidSweep_moduleOk.fnsOk pre f post hsplit).1

theorem fidSweep_solveBytes_mem : m6oSolveBytesFn ∈ fidSweepModule.fns :=
  spliceFns_mem_of_ne m8FidV123t2_solveBytes_mem fun r hr => by
    simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `FullFidelitySweep.fidSweepModule` (`449` fns). -/
theorem fidSweep_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of fidSweep_moduleOk fidSweep_solveBytes_mem
    (fun _ _ _ _ hs => m8Sw_solve_bytes_elim hs) hcfit hwfit hm

/-- Host-framed machine-memory lift for `kissat_solve_bytes` on `fidSweepModule`. -/
theorem fidSweep_solve_bytes_host_sound
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
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes` on
`8,192 B` `nvM6UnsatInitMem` (`fidSweepModule`). -/
theorem fidSweep_unsat_nv :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of fidSweep_moduleOk fidSweep_solveBytes_mem
    (fun _ _ _ _ hs => m8Sw_solve_bytes_elim hs)

/-! ## 2. Closed `471/471` `CoreParity` Splice (`fidSweepCoreParityModule`) -/

/-- Ordered `471`-function module body splicing `fidSweepRepls` onto
`FullM8CoreParity.m8SweepV2CoreParityFns`. -/
def fidSweepCoreParityFns : List Fn :=
  spliceFns fidSweepRepls m8SweepV2CoreParityFns

/-- Closed `471`-function combined `M8CoreParity` + Full-Fidelity `sweep.c` parity module
(`0` externs, `0` exits). -/
def fidSweepCoreParityModule : LeanQbe.T.Module :=
  { m8SweepV2CoreParityModule with fns := fidSweepCoreParityFns }

private theorem fid_cp_slot_302 :
    m8SweepV2CoreParityFns[302]?.map Fn.sig = some ("full_m6_max_v", [i64], [i64]) := by
  t_kernel_rfl
private theorem fid_cp_slot_304 :
    m8SweepV2CoreParityFns[304]?.map Fn.sig = some ("full_k6_init", [i64, i32], []) := by
  t_kernel_rfl
private theorem fid_cp_slot_307 :
    m8SweepV2CoreParityFns[307]?.map Fn.sig =
      some ("full_k6_add_clause", [i64, i64, i32], [.bool]) := by t_kernel_rfl
private theorem fid_cp_slot_317 :
    m8SweepV2CoreParityFns[317]?.map Fn.sig =
      some ("full_m6_dense_prop", [i64], [.bool]) := by t_kernel_rfl
private theorem fid_cp_slot_318 :
    m8SweepV2CoreParityFns[318]?.map Fn.sig =
      some ("full_m6_sweep_cone", [i64, i32], [i64]) := by t_kernel_rfl
private theorem fid_cp_slot_319 :
    m8SweepV2CoreParityFns[319]?.map Fn.sig =
      some ("full_m6_sweep_refine_sig", [i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_cp_slot_321 :
    m8SweepV2CoreParityFns[321]?.map Fn.sig =
      some ("full_m6_sweep_solve", [i64, i32, i64], [i64]) := by t_kernel_rfl
private theorem fid_cp_slot_322 :
    m8SweepV2CoreParityFns[322]?.map Fn.sig =
      some ("full_m6_sweep_flip_round", [i64, i32], [i32]) := by t_kernel_rfl
private theorem fid_cp_slot_323 :
    m8SweepV2CoreParityFns[323]?.map Fn.sig =
      some ("full_m6_sweep_sim", [i64, i32, i64], [i32]) := by t_kernel_rfl
private theorem fid_cp_slot_334 :
    m8SweepV2CoreParityFns[334]?.map Fn.sig =
      some ("full_m6_sweep_var", [i64, i32, i64], [i64]) := by t_kernel_rfl
private theorem fid_cp_slot_335 :
    m8SweepV2CoreParityFns[335]?.map Fn.sig =
      some ("full_m6_cand_sift", [i64, i64, i32, i32], []) := by t_kernel_rfl
private theorem fid_cp_slot_336 :
    m8SweepV2CoreParityFns[336]?.map Fn.sig =
      some ("full_m6_collect_cands", [i64], [i32]) := by t_kernel_rfl
private theorem fid_cp_slot_337 :
    m8SweepV2CoreParityFns[337]?.map Fn.sig =
      some ("full_m6_sweep_vars", [i64, i64, i64], [i64]) := by t_kernel_rfl

private theorem fid_cp_replSigs :
    ∀ r ∈ fidSweepRepls, ∀ f ∈ m8SweepV2CoreParityFns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨g318, hg318, hs318⟩ := m8cp_sig_of_map fid_cp_slot_318
  obtain ⟨g323, hg323, hs323⟩ := m8cp_sig_of_map fid_cp_slot_323
  obtain ⟨g336, hg336, hs336⟩ := m8cp_sig_of_map fid_cp_slot_336
  obtain ⟨g337, hg337, hs337⟩ := m8cp_sig_of_map fid_cp_slot_337
  intro r hr f hf hnm
  simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hf
      (List.mem_of_getElem? hg318) (hnm.symm.trans (congrArg Prod.fst hs318).symm)) ▸ hs318.symm
  · exact (m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hf
      (List.mem_of_getElem? hg323) (hnm.symm.trans (congrArg Prod.fst hs323).symm)) ▸ hs323.symm
  · exact (m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hf
      (List.mem_of_getElem? hg336) (hnm.symm.trans (congrArg Prod.fst hs336).symm)) ▸ hs336.symm
  · exact (m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hf
      (List.mem_of_getElem? hg337) (hnm.symm.trans (congrArg Prod.fst hs337).symm)) ▸ hs337.symm

private theorem fid_cp_mem_pre_of_lt {xs pre post : List Fn} {f g : Fn} {i j : Nat}
    (hnd : (xs.map Fn.name).Nodup) (hsplit : xs = pre ++ f :: post)
    (hi : xs[i]? = some f) (hj : xs[j]? = some g) (hlt : j < i) : g ∈ pre := by
  have hle : i < xs.length := by
    cases Nat.lt_or_ge i xs.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hi; cases hi
  have hlp : pre.length < xs.length := by rw [hsplit, List.length_append]; simp
  have hfp : xs[pre.length]? = some f := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hf1 : xs[pre.length]'hlp = f := Option.some.inj (by rwa [← List.getElem?_eq_getElem hlp])
  have hf2 : xs[i]'hle = f := Option.some.inj (by rwa [← List.getElem?_eq_getElem hle])
  have hpw := List.pairwise_iff_getElem.mp hnd
  have hpre_len : pre.length = i := by
    rcases Nat.lt_trichotomy pre.length i with hlt' | heq | hgt'
    · exact False.elim ((hpw pre.length i (by simp [hlp]) (by simp [hle]) hlt')
        (by simp [hf1, hf2]))
    · exact heq
    · exact False.elim ((hpw i pre.length (by simp [hle]) (by simp [hlp]) hgt')
        (by simp [hf1, hf2]))
  have hj_pre : pre[j]? = some g := by
    rw [hsplit, List.getElem?_append_left (by omega)] at hj; exact hj
  exact List.mem_of_getElem? hj_pre

private theorem fid_cp_splice_split {repls xs pre post : List Fn} {fn : Fn}
    (hsplit : spliceFns repls xs = pre ++ fn :: post) :
    ∃ xs_pre g xs_post, xs = xs_pre ++ g :: xs_post ∧ pre = spliceFns repls xs_pre ∧
      fn = (repls.find? (fun r => r.name == g.name)).getD g := by
  unfold spliceFns at hsplit
  obtain ⟨xs_pre, tail, hxs, hpre, htail⟩ := List.map_eq_append_iff.mp hsplit
  cases tail with
  | nil => cases htail
  | cons g xs_post =>
    simp only [List.map_cons, List.cons.injEq] at htail
    exact ⟨xs_pre, g, xs_post, hxs, hpre.symm, htail.1.symm⟩

theorem fidSweepCoreParity_callsOk :
    fidSweepCoreParityModule.namesNodup ∧
    ∀ pre fn post, fidSweepCoreParityModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ fidSweepCoreParityModule.externs.map Extern.sig)
        fidSweepCoreParityModule.exits := by
  have hnd_fns : fidSweepCoreParityFns.map Fn.name = m8SweepV2CoreParityFns.map Fn.name := by
    have h := congrArg (List.map Prod.fst) (spliceFns_sigs fid_cp_replSigs)
    simpa only [fidSweepCoreParityFns, List.map_map, Function.comp_def, Fn.sig] using h
  have hnd : fidSweepCoreParityModule.namesNodup := by
    change (fidSweepCoreParityFns.map Fn.name ++
      m8SweepV2CoreParityModule.externs.map Extern.name).Nodup
    rw [hnd_fns]
    exact m8cp_sw_fast_acyclic.1
  refine ⟨hnd, ?_⟩
  obtain ⟨g302, hg302, hs302⟩ := m8cp_sig_of_map fid_cp_slot_302
  obtain ⟨g304, hg304, hs304⟩ := m8cp_sig_of_map fid_cp_slot_304
  obtain ⟨g307, hg307, hs307⟩ := m8cp_sig_of_map fid_cp_slot_307
  obtain ⟨g317, hg317, hs317⟩ := m8cp_sig_of_map fid_cp_slot_317
  obtain ⟨g318, hg318, hs318⟩ := m8cp_sig_of_map fid_cp_slot_318
  obtain ⟨g319, hg319, hs319⟩ := m8cp_sig_of_map fid_cp_slot_319
  obtain ⟨g321, hg321, hs321⟩ := m8cp_sig_of_map fid_cp_slot_321
  obtain ⟨g322, hg322, hs322⟩ := m8cp_sig_of_map fid_cp_slot_322
  obtain ⟨g323, hg323, hs323⟩ := m8cp_sig_of_map fid_cp_slot_323
  obtain ⟨g334, hg334, hs334⟩ := m8cp_sig_of_map fid_cp_slot_334
  obtain ⟨g335, hg335, hs335⟩ := m8cp_sig_of_map fid_cp_slot_335
  obtain ⟨g336, hg336, hs336⟩ := m8cp_sig_of_map fid_cp_slot_336
  obtain ⟨g337, hg337, hs337⟩ := m8cp_sig_of_map fid_cp_slot_337
  have hchkCone : fidSweepConeFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_k6_init", [i64, i32], []),
       ("full_k6_add_clause", [i64, i64, i32], [.bool])] [] = true := by t_kernel_rfl
  have hchkSim : fidSweepSimFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_m6_sweep_refine_sig", [i64, i32, i32], []),
       ("full_m6_sweep_solve", [i64, i32, i64], [i64]),
       ("full_m6_sweep_flip_round", [i64, i32], [i32])] [] = true := by t_kernel_rfl
  have hchkCands : fidCollectCandsFn.checkCallsOk
      [("full_m6_cand_sift", [i64, i64, i32, i32], [])] [] = true := by t_kernel_rfl
  have hchkVars : fidSweepVarsFn.checkCallsOk
      [("full_m6_max_v", [i64], [i64]), ("full_m6_dense_prop", [i64], [.bool]),
       ("full_m6_sweep_var", [i64, i32, i64], [i64]),
       ("full_m6_collect_cands", [i64], [i32])] [] = true := by t_kernel_rfl
  intro pre fn post hsplit
  change spliceFns fidSweepRepls m8SweepV2CoreParityFns = pre ++ fn :: post at hsplit
  obtain ⟨xs_pre, f, xs_post, hxs, hpre_eq, hfn_eq⟩ := fid_cp_splice_split hsplit
  have hpre_sigs : pre.map Fn.sig = xs_pre.map Fn.sig := by
    rw [hpre_eq]
    exact spliceFns_sigs (fun r hr g hg hnm =>
      fid_cp_replSigs r hr g (hxs ▸ List.mem_append_left _ hg) hnm)
  rw [hpre_sigs]
  cases hfnd : fidSweepRepls.find? (fun r => r.name == f.name) with
  | none =>
    rw [hfnd, Option.getD_none] at hfn_eq; subst fn
    exact m8cp_sw_fast_acyclic.2 xs_pre f xs_post hxs
  | some r =>
    rw [hfnd, Option.getD_some] at hfn_eq; subst fn
    have hr : r ∈ fidSweepRepls := List.mem_of_find?_eq_some hfnd
    have hbeq := List.find?_some (p := fun (x : Fn) => x.name == f.name) hfnd
    have hnm : r.name = f.name := beq_iff_eq.mp hbeq
    have hfm : f ∈ m8SweepV2CoreParityFns := hxs ▸ List.mem_append_right _ List.mem_cons_self
    have hEx : fidSweepCoreParityModule.exits = [] := m8FidV123t2_noExit
    rw [hEx]
    have addPre : ∀ {i j : Nat} {g : Fn} {s : SigEntry},
        m8SweepV2CoreParityFns[i]? = some f → m8SweepV2CoreParityFns[j]? = some g → j < i →
        g.sig = s → s ∈ xs_pre.map Fn.sig ++ fidSweepCoreParityModule.externs.map Extern.sig :=
      fun hi hj hlt hs =>
        List.mem_append_left _ (hs ▸ List.mem_map_of_mem
          (fid_cp_mem_pre_of_lt m8SweepV2CoreParityFns_names_nodup hxs hi hj hlt))
    simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have hfeq : f = g318 := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfm
        (List.mem_of_getElem? hg318) (hnm.symm.trans (congrArg Prod.fst hs318).symm)
      subst hfeq
      refine Fn.callsOk_of_checkCallsOk (fn_checkCallsOk_mono (fun s hs => ?_) hchkCone)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact addPre hg318 hg302 (by decide) hs302
      · exact addPre hg318 hg304 (by decide) hs304
      · exact addPre hg318 hg307 (by decide) hs307
    · have hfeq : f = g323 := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfm
        (List.mem_of_getElem? hg323) (hnm.symm.trans (congrArg Prod.fst hs323).symm)
      subst hfeq
      refine Fn.callsOk_of_checkCallsOk (fn_checkCallsOk_mono (fun s hs => ?_) hchkSim)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact addPre hg323 hg302 (by decide) hs302
      · exact addPre hg323 hg319 (by decide) hs319
      · exact addPre hg323 hg321 (by decide) hs321
      · exact addPre hg323 hg322 (by decide) hs322
    · have hfeq : f = g336 := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfm
        (List.mem_of_getElem? hg336) (hnm.symm.trans (congrArg Prod.fst hs336).symm)
      subst hfeq
      refine Fn.callsOk_of_checkCallsOk (fn_checkCallsOk_mono (fun s hs => ?_) hchkCands)
      simp only [List.mem_singleton] at hs; subst hs
      exact addPre hg336 hg335 (by decide) hs335
    · have hfeq : f = g337 := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfm
        (List.mem_of_getElem? hg337) (hnm.symm.trans (congrArg Prod.fst hs337).symm)
      subst hfeq
      refine Fn.callsOk_of_checkCallsOk (fn_checkCallsOk_mono (fun s hs => ?_) hchkVars)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact addPre hg337 hg302 (by decide) hs302
      · exact addPre hg337 hg317 (by decide) hs317
      · exact addPre hg337 hg334 (by decide) hs334
      · exact addPre hg337 hg336 (by decide) hs336

private theorem fid_cp_sw_row (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hne : nm ∉ m8CpExclNames := by decide)
    (hi : m8SweepEnvRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    M6EnvSpec m8SweepV2CoreParityEnv nm sp := fun xs m Q X hs =>
  .base hne (m8Sw_row i nm as bs sp hi hno xs m Q X hs)

private theorem fid_cp_elim_sw_row {i : Nat} {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : nm ∈ m8SwNamesLit)
    (hnm1 : nm ≠ "full_min_shrink_m6") (hnm2 : nm ≠ "full_min_shrink")
    (hnm3 : nm ≠ "full_bve_var_key_m7") (hnm4 : nm ≠ "full_bve_heap_push_m7")
    (hnmM : nm ∉ m8MinHelperRows.map SpecEntry.name)
    (hnmB : nm ∉ m8BveHelpers.map Fn.name)
    (hi : m8SweepEnvRows[i]? = some ⟨nm, as, bs, sp, true⟩)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hs : m8SweepV2CoreParityEnv nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) := by
  cases hs with
  | base _ hsw => exact fid_sw_elim_row hmem hi hsw
  | minShrinkM6 _ => exact absurd rfl hnm1
  | minShrink _ => exact absurd rfl hnm2
  | varKey _ => exact absurd rfl hnm3
  | heapPush _ => exact absurd rfl hnm4
  | minHelp hm => exact absurd (m8CoreParity_ofTable_name_mem hm) hnmM
  | bveHelp hb =>
    have hm := m8CoreParity_ofTable_name_mem hb
    rw [m8cp_bveHelperRows_names_eq m8BveHook] at hm
    exact absurd hm hnmB

/-- Closed unconditional `471/471` `ModuleOk` for `fidSweepCoreParityModule` under
`m8SweepV2CoreParityEnv` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidSweepCoreParity_moduleOk :
    ModuleOk m8SweepV2CoreParityEnv fidSweepCoreParityModule := by
  refine ⟨fidSweepCoreParity_callsOk.1, fun pre fn post hsplit => ?_⟩
  refine ⟨?_, fidSweepCoreParity_callsOk.2 pre fn post hsplit, ?_⟩
  · change spliceFns fidSweepRepls m8SweepV2CoreParityFns = pre ++ fn :: post at hsplit
    obtain ⟨xs_pre, g, xs_post, hxs, _, hfn_eq⟩ := fid_cp_splice_split hsplit
    cases hfnd : fidSweepRepls.find? (fun r => r.name == g.name) with
    | none =>
      rw [hfnd, Option.getD_none] at hfn_eq; subst fn
      exact (m8SweepV2CoreParity_moduleOk.fnsOk xs_pre g xs_post hxs).1
    | some r =>
      rw [hfnd, Option.getD_some] at hfn_eq; subst fn
      exact fidSweepRepls_wf r (List.mem_of_find?_eq_some hfnd)
  · intro xs m Q X hs
    change spliceFns fidSweepRepls m8SweepV2CoreParityFns = pre ++ fn :: post at hsplit
    obtain ⟨xs_pre, g, xs_post, hxs, _, hfn_eq⟩ := fid_cp_splice_split hsplit
    cases hfnd : fidSweepRepls.find? (fun r => r.name == g.name) with
    | none =>
      rw [hfnd, Option.getD_none] at hfn_eq; subst fn
      exact (m8SweepV2CoreParity_moduleOk.fnsOk xs_pre g xs_post hxs).2.2 xs m Q X hs
    | some r =>
      rw [hfnd, Option.getD_some] at hfn_eq; subst fn
      have hr : r ∈ fidSweepRepls := List.mem_of_find?_eq_some hfnd
      have r0 := fid_cp_sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec
      have r2 := fid_cp_sw_row 2 "full_k6_init" [i64, i32] [] k6InitSpec
      have r5 := fid_cp_sw_row 5 "full_k6_add_clause" [i64, i64, i32] [.bool] k6AddClauseSpec
      have r15 := fid_cp_sw_row 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec
      have r17 := fid_cp_sw_row 17 "full_m6_sweep_refine_sig" [i64, i32, i32] []
        m6SweepRefineSigSpec
      have r19 := fid_cp_sw_row 19 "full_m6_sweep_solve" [i64, i32, i64] [i64] m6SweepSolveSpec
      have r20 := fid_cp_sw_row 20 "full_m6_sweep_flip_round" [i64, i32] [i32]
        m6SweepFlipRoundSpec
      have r32 := fid_cp_sw_row 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec
      have r33 := fid_cp_sw_row 33 "full_m6_cand_sift" [i64, i64, i32, i32] [] m6CandSiftSpec
      have r34 := fid_cp_sw_row 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec
      simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact fid_sweep_cone_wp m8SweepV2CoreParityEnv r0 r2 r5 xs m Q X
          (fid_cp_elim_sw_row (i := 16) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) rfl hs)
      · exact fid_sweep_sim_wp m8SweepV2CoreParityEnv r0 r19 r17 r20 xs m Q X
          (fid_cp_elim_sw_row (i := 21) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) rfl hs)
      · exact fid_collect_cands_wp m8SweepV2CoreParityEnv r33 xs m Q X
          (fid_cp_elim_sw_row (i := 34) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) rfl hs)
      · exact fid_sweep_vars_wp m8SweepV2CoreParityEnv r0 r15 r34 r32 xs m Q X
          (fid_cp_elim_sw_row (i := 35) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) rfl hs)

theorem fidSweepCoreParity_tableImpl :
    TableImpl m8SweepV2CoreParityEnv fidSweepCoreParityModule.fns m8SweepV2CoreParitySpecTable := by
  have hSigs : m8SweepV2CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidSweepCoreParityModule.fns.map Fn.sig := by
    change m8SweepV2CoreParitySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      (spliceFns fidSweepRepls m8SweepV2CoreParityFns).map Fn.sig
    rw [m8SweepV2CoreParitySpecTable_sigs]
    exact (spliceFns_sigs fid_cp_replSigs).symm
  exact tableImpl_of_moduleOk fidSweepCoreParity_moduleOk hSigs
    m8SweepV2CoreParitySpecTable_nodup
    (fun _ _ _ _ _ _ ht => m8SweepV2CoreParityEnv_of_specTable ht)

theorem fidSweepCoreParity_solveBytes_mem : m6oSolveBytesFn ∈ fidSweepCoreParityModule.fns :=
  spliceFns_mem_of_ne m8SweepV2CoreParity_solveBytes_mem fun r hr => by
    simp only [fidSweepRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Top-level byte-level UNSAT soundness of `fidSweepCoreParityModule` (`471` fns). -/
theorem fidSweepCoreParity_solve_bytes_sound
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
  m8cp_solve_bytes_sound_of fidSweepCoreParity_moduleOk fidSweepCoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))
    hcfit hwfit hm

/-- Host-framed machine-memory lift for `kissat_solve_bytes` on `fidSweepCoreParityModule`. -/
theorem fidSweepCoreParity_solve_bytes_host_sound
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
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes` on
`8,192 B` `nvM6UnsatInitMem` (`fidSweepCoreParityModule`). -/
theorem fidSweepCoreParity_unsat_nv :
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
  m8cp_unsat_nv_of fidSweepCoreParity_moduleOk fidSweepCoreParity_solveBytes_mem
    (fun _ _ _ _ hs =>
      .base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))

/-! ## 3. Concrete Non-Bailout `Mem 64` UNSAT Non-Vacuity (`comp = 0` & Escalated `comp = 1`) -/

/-- Escalated/resumed concrete `FullState`: identical to `nvM6SweepState` (`scratch_cap = 24576`,
`mv = 512`, `inconsistent = 0#64`, `dense_mode = 1#64`) with `gu[28] = 1#32` (`sweep_completed = 1`,
escalating cone to `vlim = 512`, `clim = 2048`, `depth_lim = 3`) and `gu[29] = 1#32`
(`sweep_incomplete = 1`, entering the cursor-resume branch in `full_m6_sweep_vars`). -/
def nvFidEscState : FullState :=
  { nvM6SweepState with
    scratch :=
      { nvM6SweepState.scratch with
        glue_used := (nvM6SweepState.scratch.glue_used.set 28 1#32).set 29 1#32 } }

/-- Concrete `Mem 64` heap encoding `nvFidEscState` at `nvM4SweepCfg.hdr` (`0x1000#64`). -/
def nvFidEscMem : Mem 64 :=
  storeMem
    (storeMem nvM6SweepMem i32
      (FullM4Sweep.nvM4SweepCfg.pGlueUsed + BitVec.ofNat 64 (4 * 28)) 1#32)
    i32 (FullM4Sweep.nvM4SweepCfg.pGlueUsed + BitVec.ofNat 64 (4 * 29)) 1#32

theorem nvFidEsc_invW :
    FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] nvFidEscState := by
  have hgu : ((nvM6SweepState.scratch.glue_used.set 28 1#32).set 29 1#32).length = 64 := by
    simp [nvM6SweepState_lengths.scratch_ok.glue_used_len]
  exact ⟨⟨nvM6Sweep_invW.1.core_ok, { nvM6Sweep_invW.1.scratch_ok with glue_used_len := hgu }⟩,
    nvM6Sweep_invW.2.1, nvM6Sweep_invW.2.2.1, nvM6Sweep_invW.2.2.2.1, nvM6Sweep_invW.2.2.2.2.1,
    nvM6Sweep_invW.2.2.2.2.2.1, nvM6Sweep_invW.2.2.2.2.2.2⟩

theorem nvFidEscMem_ok : FullMem FullM4Sweep.nvM4SweepCfg nvFidEscState nvFidEscMem := by
  have hm0 : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  have h28 : 28 < nvM6SweepState.scratch.glue_used.length := by
    rw [nvM6SweepState_lengths.scratch_ok.glue_used_len]; decide
  have hm1 := (Full.FullArenaTactics.store_full_glue_used 1#32 h28 hm0).2
  have h29 : 29 < (nvM6SweepState.scratch.glue_used.set 28 1#32).length := by
    rw [List.length_set, nvM6SweepState_lengths.scratch_ok.glue_used_len]; decide
  have hm2 := (Full.FullArenaTactics.store_full_glue_used 1#32 h29 hm1).2
  rwa [sep_emp] at hm2

/-- Concrete non-bailout `Mem 64` NV (`XPost := False`) for `full_m6_sweep_cone` at `comp = 0`
(`vlim = 256`, `clim = 1024`, `depth_lim = 2`, `mv = 512`) under `m8FidV123t2Env`. -/
theorem nv_fid_sweep_cone_comp0 :
    Func.wp m8FidV123t2Env FullFidelitySweep.full_m6_sweep_cone_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  exact fid_sweep_cone_wp m8FidV123t2Env
    (m8Sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
    (m8Sw_row 2 "full_k6_init" [i64, i32] [] k6InitSpec)
    (m8Sw_row 5 "full_k6_add_clause" [i64, i64, i32] [.bool] k6AddClauseSpec)
    _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvM6SweepState, emp, rfl,
     nvM6Sweep_invW, by decide,
     Nat.lt_of_lt_of_le (by decide) nvM6SweepState_lengths.core_ok.cur_vars_ge,
     nvM6Sweep_tmkZero, hm,
     fun _ _ _ _ _ m' hd _ _ _ _ hcone _ _ _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨_, hd, hcone, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete non-bailout `Mem 64` NV (`XPost := False`) for `full_m6_sweep_cone` at escalated
`comp = 1` (`gu[28] = 1`, `vlim = 512`, `clim = 2048 -> 1536`, `depth_lim = 3`) under
`m8SweepV2CoreParityEnv`. -/
theorem nv_fid_sweep_cone_comp1 :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_sweep_cone_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ()) nvFidEscMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M6SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvFidEscState ⋆ emp) nvFidEscMem := by
    rw [sep_emp]; exact nvFidEscMem_ok
  exact fid_sweep_cone_wp m8SweepV2CoreParityEnv
    (fid_cp_sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
    (fid_cp_sw_row 2 "full_k6_init" [i64, i32] [] k6InitSpec)
    (fid_cp_sw_row 5 "full_k6_add_clause" [i64, i64, i32] [.bool] k6AddClauseSpec)
    _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, [[0], [1]], nvFidEscState, emp, rfl,
     nvFidEsc_invW, by decide,
     Nat.lt_of_lt_of_le (by decide) nvFidEsc_invW.1.core_ok.cur_vars_ge,
     nvM6Sweep_tmkZero, hm,
     fun _ _ _ _ _ m' hd _ _ _ _ hcone _ _ _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨_, hd, hcone, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete non-bailout `Mem 64` NV (`XPost := False`) for `full_m6_collect_cands` on escalated
`nvFidEscMem` under `m8SweepV2CoreParityEnv`. -/
theorem nv_fid_collect_cands_esc :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_collect_cands_body
      (FullM4Sweep.nvM4SweepCfg.hdr, ()) nvFidEscMem
      (fun (nc, ()) m' => ∃ trc' ws2',
        nc.toNat ≤ nvFidEscState.core.cur_vars ∧
        Full.nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg
          { nvFidEscState with scratch :=
            { nvFidEscState.scratch with tarjan_reach := trc', work_stk2 := ws2' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvFidEscState ⋆ emp) nvFidEscMem := by
    rw [sep_emp]; exact nvFidEscMem_ok
  exact fid_collect_cands_wp m8SweepV2CoreParityEnv
    (fid_cp_sw_row 33 "full_m6_cand_sift" [i64, i64, i32, i32] [] m6CandSiftSpec)
    _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvFidEscState, emp, rfl, nvFidEsc_invW.1, hm,
     fun nc trc' ws2' m' _ hnc _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨trc', ws2', hnc, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete non-bailout `Mem 64` NV (`XPost := False`) for `full_m6_sweep_vars` on fresh round
(`gu[29] = 0`, `need_mark = true`) under `m8FidV123t2Env`. -/
theorem nv_fid_sweep_vars_fresh :
    Func.wp m8FidV123t2Env FullFidelitySweep.full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM6SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvM6SweepState ⋆ emp) nvM6SweepMem := by
    rw [sep_emp]; exact nvM6SweepMem_ok
  exact fid_sweep_vars_wp m8FidV123t2Env
    (m8Sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
    (m8Sw_row 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec)
    (m8Sw_row 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec)
    (m8Sw_row 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec)
    _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvM6SweepState, emp, rfl,
     nvM6Sweep_invW.toDense, nvM6Sweep_tmkZero, hm,
     fun r s' m' hd _ _ ht hdom _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨s', hd, ht, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete non-bailout `Mem 64` NV (`XPost := False`) for `full_m6_sweep_vars` on escalated
resume round (`gu[28] = 1`, `gu[29] = 1`, `need_mark = false`) under `m8SweepV2CoreParityEnv`. -/
theorem nv_fid_sweep_vars_resume :
    Func.wp m8SweepV2CoreParityEnv FullFidelitySweep.full_m6_sweep_vars_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvFidEscMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg Full.nvOneLitF0 s' ∧
        M6TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg nvFidEscState ⋆ emp) nvFidEscMem := by
    rw [sep_emp]; exact nvFidEscMem_ok
  exact fid_sweep_vars_wp m8SweepV2CoreParityEnv
    (fid_cp_sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
    (fid_cp_sw_row 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec)
    (fid_cp_sw_row 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec)
    (fid_cp_sw_row 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec)
    _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, Full.nvOneLitF0, nvFidEscState, emp, rfl,
     nvFidEsc_invW.toDense, nvM6Sweep_tmkZero, hm,
     fun r s' m' hd _ _ ht hdom _ hm' => by
       rw [sep_emp] at hm'
       exact ⟨s', hd, ht, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end
