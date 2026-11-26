/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofAgree
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofReplsA
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12ProofReplsB
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical Gate-1 `KissatFidelity` Assembly Proof — Step 12 (`FullFidelityAssemblyStep12Proof`)

Certifies `FullFidelityAssemblyStep12.fidStep12Module` (`517` fns, `0` externs, `0` exits,
`0` `import all`, `0` `@[expose]` on theorems/lemmas) via `PatchModule` +
`FullFidelityAssemblyUtil`:
1. Composes `fidStep12Bundle` (`505 -> 517` fns) from `Proof0`, `Agree`, `ReplsA`, and `ReplsB`.
2. Closed `517/517` `fidStep12_moduleOk : ModuleOk fidStep12Env fidStep12Module`,
   `fidStep12Env_noExit`, `fidStep12_solve_bytes_sound`, `fidStep12_solve_bytes_host_sound`,
   `fidStep12_unsat_nv` (`XPost := False`, `r = 20#64`, `std3`), `fidStep12Module_acyclic`, and
   `fidStep12UnsatPkg : KissatUnsatPkg`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

private theorem fidStep12_frontRows_noExit :
    fidStep12Bundle.frontTable.all SpecEntry.noExit = true := by
  change (FullFidelityStep12B.fidStep12BRewireRows ++ fidStep12ReplRows ++
    fidStep12BeforeRows).all SpecEntry.noExit = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by t_kernel_rfl, ?_⟩, ?_⟩
  · simp only [fidStep12ReplRows, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨by t_kernel_rfl, by t_kernel_rfl⟩, ?_⟩,
      FullFidelityStep12B.fidStep12BReplRows_noExit⟩, ?_⟩, ?_⟩
    · have hno3 : ∀ x ∈ FullFidelityStep11Pr3.fidStep11Pr3ReplRows, x.noExit = true :=
        fun x hx => FullFidelityStep11Pr3.fidStep11Pr3Rows_noExit x (List.mem_append_left _ hx)
      simp only [fid12Pr3ReplRows, List.all_append, Bool.and_eq_true]
      refine ⟨⟨⟨List.all_eq_true.mpr fun x hx => hno3 x (List.mem_of_mem_take hx), rfl⟩,
        List.all_eq_true.mpr fun x hx =>
          hno3 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))⟩,
        List.all_eq_true.mpr fun x hx => hno3 x (List.mem_of_mem_drop hx)⟩
    · exact List.all_eq_true.mpr fun x hx =>
        FullFidelityStep12C.fidStep12CRows_noExit x (List.mem_append_left _ hx)
    · rw [fid12Step12AReplRows]
      exact List.all_eq_true.mpr fun x hx =>
        List.all_eq_true.mp FullFidelityStep12A.fidStep12AReplRows_noExit x
          (List.mem_filter.mp hx).1
  · simp only [fidStep12BeforeRows, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨by t_kernel_rfl, by t_kernel_rfl⟩,
      FullFidelityStep12B.fidStep12BBeforeRows_noExit⟩, ?_⟩
    exact List.all_eq_true.mpr fun x hx =>
      FullFidelityStep12C.fidStep12CRows_noExit x (List.mem_append_right _ hx)

/-- Closed `517/517` `ModuleOk` for `FullFidelityAssemblyStep12.fidStep12Module` under
`fidStep12Env` (`0` externs, `0` exits, `std3` axioms only). -/
theorem fidStep12_moduleOk : ModuleOk fidStep12Env fidStep12Module := by
  refine ⟨fidStep12Module_names_nodup, fun pre fn post hsplit => ?_⟩
  change patchFns fidStep12Repls fidStep12Befores fidStep10Module.fns = pre ++ fn :: post at hsplit
  obtain ⟨bPre, f0, bPost, hfs, hcase⟩ := patchFns_split_12 hsplit
  have hf0_ok := fidStep10Base_moduleOk.fnsOk bPre f0 bPost hfs
  have hsub : ∀ f ∈ bPre, f ∈ fidStep10Module.fns := fun f hf => hfs ▸ List.mem_append_left _ hf
  rcases hcase with ⟨iPre, iPost, hi, hpreM⟩ | ⟨rfl, hpreM⟩
  · rcases patchInsAt_fidStep12_cases hi with
      ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ |
      ⟨hf0, rfl⟩ | ⟨hf0, ri, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩ | ⟨hf0, rfl⟩
    · exact fid12_ok_before_A hfs (Or.inl ⟨hf0, rfl⟩) hpreM
    · exact fid12_ok_before_A hfs (Or.inr (Or.inl ⟨hf0, rfl⟩)) hpreM
    · exact fid12_ok_before_A hfs (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩))) hpreM
    · exact fid12_ok_before_A hfs (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩)))) hpreM
    · exact fid12_ok_before_A hfs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩))))) hpreM
    · exact fid12_ok_before_A hfs
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf0, rfl⟩))))) hpreM
    · exact fid12_ok_before_B hfs (Or.inl ⟨hf0, rfl⟩) hpreM
    · exact fid12_ok_before_B hfs (Or.inr (Or.inl ⟨hf0, ri, rfl⟩)) hpreM
    · exact fid12_ok_before_B hfs (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩))) hpreM
    · exact fid12_ok_before_B hfs (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩)))) hpreM
    · exact fid12_ok_before_B hfs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf0, rfl⟩))))) hpreM
    · exact fid12_ok_before_B hfs
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf0, rfl⟩))))) hpreM
  · cases hrepl : fidStep12Repls.find? (·.name == f0.name) with
    | some r =>
      have hf0_nm : f0.name = r.name :=
        (beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hrepl)).symm
      have hr_mem : r ∈ fidStep12Repls := List.mem_of_find?_eq_some hrepl
      simp only [fidStep12Repls, List.append_assoc, List.mem_append] at hr_mem
      rcases hr_mem with h1 | h2 | h3 | h4 | h5 | h6
      · exact fid12_ok_pr1 h1 hfs hf0_nm hpreM
      · exact fid12_ok_tum h2 hfs hf0_nm hpreM
      · exact fid12_ok_pr3 h3 hfs hf0_nm hpreM
      · exact fid12_ok_12b h4 hfs hf0_nm hpreM
      · exact fid12_ok_12c h5 hfs hf0_nm hpreM
      · exact fid12_ok_12a h6 hfs hf0_nm hpreM
    | none =>
      dsimp only [Option.getD]
      by_cases hws : f0.name = "full_cong_work_step"
      · have hfeq := fidStep10_workStep_eq (hfs ▸ List.mem_append_right _ List.mem_cons_self) hws
        subst hfeq
        exact fid12_ok_congWorkStep hfs hws hpreM hf0_ok.1
      · have hf0_in : f0 ∈ fidStep10Module.fns :=
          hfs ▸ List.mem_append_right _ List.mem_cons_self
        have hfrontNone := fidStep12_front_none_of_repl_none hf0_in hws hrepl
        have hcalls10 : f0.callsOk (bPre.map Fn.sig) [] := by
          simpa only [fidStep10_noExit, fidStep10_externs_empty, List.map_nil,
            List.append_nil] using hf0_ok.2.1
        have hcalls12 : f0.callsOk
            (pre.map Fn.sig ++ fidStep12Module.externs.map Extern.sig) fidStep12Module.exits := by
          rw [fidStep12_noExit, fidStep12_externs_empty, List.map_nil, List.append_nil]
          refine fn_callsOk_mono (fun s hs => hpreM s (by
            rw [List.map_append, List.mem_append]
            rcases List.mem_map.mp hs with ⟨g, hg, rfl⟩
            exact Or.inl (patchFns_sig_preserved12 hsub hg))) hcalls10
        have hnskip : !(fidStep12NoCallSkip.contains f0.name) = true := by
          by_cases hmem : fidStep12NoCallSkip.contains f0.name
          · exfalso
            obtain ⟨x, hx, hxnm⟩ := List.mem_map.mp (List.contains_iff_mem.mp hmem |> fun hc =>
              by simp only [fidStep12NoCallSkip, List.mem_cons] at hc; exact
                hc.elim (fun he => absurd he hws) (fun hm => hm))
            have hnone := List.find?_eq_none.mp hrepl x hx
            simp [hxnm] at hnone
          · rw [Bool.eq_false_iff.mpr hmem]; rfl
        have hnoCall := fidStep10_noCallBad hf0_in hnskip
        refine ⟨hf0_ok.1, hcalls12, fun xs m Q X hlookup => ?_⟩
        change fidStep12Env f0.name f0.as f0.rs xs m Q X at hlookup
        rw [fidStep12Env, patchEnv_base_eq fidStep12Bundle hfrontNone] at hlookup
        dsimp only [fidStep12Bundle] at hlookup
        have hwp_base := hf0_ok.2.2 xs m Q X hlookup
        refine fn_wp_env_agree_of_noCallIn hf0_ok.1 hf0_ok.2.1 hnoCall (fun f as bs hs hnb => ?_)
          hwp_base
        apply fidStep12_agree (f, as, bs) _ hnb
        simp only [Module.sigs, List.mem_append, List.mem_map] at hs ⊢
        rcases hs with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
        · exact Or.inl ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
        · exact Or.inr ⟨ex, hex, hexsig⟩

theorem fidStep12Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep12Env f as bs xs m Q X → fidStep12Env f as bs xs m Q X' :=
  patchEnv_noExit_of fidStep12Bundle fidStep12_frontRows_noExit fidStep10BaseSpecTable_noExit

theorem fidStep12Env_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidSolveBytesSpec a m Q X →
      fidStep12Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun hs => fid12_of_step10 (by decide) (fidStep10Env_solve_bytes_of hs)

theorem fidStep12_solveBytes_mem : m6oSolveBytesFn ∈ fidStep12Module.fns := by
  change m6oSolveBytesFn ∈ patchFns fidStep12Repls fidStep12Befores fidStep10Module.fns
  have h10 : m6oSolveBytesFn ∈ fidStep10Module.fns := fidStep10_solveBytes_mem
  have hnoRepl : fidStep12Repls.find? (·.name == m6oSolveBytesFn.name) = none := by
    rw [List.find?_eq_none]
    intro r hr hbeq
    have hnm : m6oSolveBytesFn.name = "kissat_solve_bytes" := rfl
    have hmem : "kissat_solve_bytes" ∈ fidStep12Repls.map Fn.name :=
      List.mem_map.mpr ⟨r, hr, (beq_iff_eq.mp hbeq).trans hnm⟩
    have hnot : (fidStep12Repls.map Fn.name).contains "kissat_solve_bytes" = false := by
      t_kernel_rfl
    have hc := List.contains_iff_mem.mpr hmem
    rw [hnot] at hc; cases hc
  simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
  exact ⟨m6oSolveBytesFn, h10, Or.inr (by simp [hnoRepl])⟩

/-- Top-level byte-level UNSAT soundness of `fidStep12Module` (`517` fns, `XPost := False`). -/
theorem fidStep12_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidStep12Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of fidStep12_moduleOk fidStep12_solveBytes_mem
    (fun _ _ _ _ hs => fidStep12Env_solve_bytes_of hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidStep12Module`. -/
theorem fidStep12_solve_bytes_host_sound
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
  FullFidelityAssemblyUtil.fid_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic `Mem 64` UNSAT non-vacuity (`r = 20#64`) for `fidStep12Module`. -/
theorem fidStep12_unsat_nv :
    Func.wp fidStep12Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of fidStep12_moduleOk fidStep12_solveBytes_mem
    (fun _ _ _ _ hs => fidStep12Env_solve_bytes_of hs)

/-- Acyclicity certificate (`checkAcyclic = true`) lifted in `O(1)` from `fidStep12_moduleOk`. -/
theorem fidStep12Module_acyclic : fidStep12Module.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk fidStep12_moduleOk

/-- Canonical Gate-1 Step-12 `KissatUnsatPkg` (`fidStep12Module`, `fidInlPolicy`). -/
def fidStep12UnsatPkg : KissatUnsatPkg :=
  mkFidUnsatPkg fidStep12Module fidInlPolicy fidStep12_solveBytes_mem
    fidStep12Env fidStep12_moduleOk fidStep12Env_noExit
    (fun _ _ _ _ hs => fidStep12Env_solve_bytes_of hs)

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

end
