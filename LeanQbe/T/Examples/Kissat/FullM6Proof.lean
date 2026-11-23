/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Proof0c
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6SatNv

/-!
# Kissat `D-Full` Unified `M6.0` `382`-Fn `ModuleOk` + Soundness & UNSAT NV (`FullM6Proof`)

Assembles the complete `382`-row `m6SpecTable tPfx solveSpec` aligned 1-to-1 with
`FullM6.m6Module.fns`, closed with the `24`-fn `M6Orch` prefix `m6OrchPfxSpecTable`
(`m6OrchPfx_tableImpl` + `M6OrchPfxTblSpecs` + `m6_walk_lookup`):

1. `m6SpecTable`, `mkM6Env`, `m6SpecTable_sigs`, `m6SpecTable_length` (`382`),
   `m6SpecTable_nodup`, `m6SpecTable_noExit`, and `mkM6Env_solve_bytes{_m6}_iff`.
2. `mkM6Env_moduleOk` (`ModuleOk (mkM6Env tPfx solveSpec) m6Module`), plus pre-specialized
   `mkM6Env_sound_moduleOk` (`fullM6SolveBytesSpec`) and `mkM6Env_core_moduleOk`
   (`fullM6SolveBytesCoreModelSpec`).
3. Top-level UNSAT + host-framed soundness (`m6_solve_bytes_sound`,
   `m6_solve_bytes_m6_sound`, `m6_solve_bytes_host_sound`) and
   concrete Tier-3b UNSAT non-vacuity (`m6_unsat_nv`, `m6_m6_unsat_nv`).
4. Closed dual-arch `0`-hook wiring: `m6Table`, `m6Env`, `m6CoreEnv`, `m6CoreEnv_moduleOk`,
   `m6Env_moduleOk`, `m6CoreEnv_noExit`, `m6Env_noExit`, `m6_solve_bytes_unsat`,
   `m6_closed_unsat_nv`, and `m6_closed_m6_unsat_nv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Unified `382`-Row `m6SpecTable` & Environment Metadata -/

/-- Complete `382`-row specification table aligned 1-to-1 with `FullM6.m6Module.fns`. -/
def m6SpecTable (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  m6RowsPart1 tPfx ++ (m6RowsPart2 tPfx ++ (m6RowsPart3Pfx tPfx ++ m6OrchTailRows solveSpec))

/-- Closed `Env` induced by `m6SpecTable tPfx solveSpec`. -/
def mkM6Env (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) : Env :=
  Env.ofTable (m6SpecTable tPfx solveSpec)

theorem m6SpecTable_sigs (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6SpecTable tPfx solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      m6Fns.map Fn.sig := by
  have hm123 : m6Fns =
      m6FnsPart1 ++ (m6FnsPart2 ++ (m6FnsPart3.take 121 ++ m6FnsPart3.drop 121)) := by
    rw [m6Fns, List.append_assoc, List.take_append_drop]
  rw [hm123]
  unfold m6SpecTable
  simp only [List.map_append]
  rw [m6RowsPart1_sigs hPfxSigs, m6RowsPart2_sigs hPfxSigs,
    m6RowsPart3Pfx_sigs hPfxSigs, m6OrchTailRows_sigs solveSpec]

private theorem len_eq_of_sigs_eq {fs : List Fn} {rs : List SpecEntry}
    (h : rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig) :
    fs.length = rs.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1.symm

theorem m6SpecTable_length (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6SpecTable tPfx solveSpec).length = 382 :=
  (len_eq_of_sigs_eq (m6SpecTable_sigs tPfx solveSpec hPfxSigs)).symm.trans m6Fns_length

theorem m6SpecTable_nodup (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    ((m6SpecTable tPfx solveSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (m6SpecTable_sigs tPfx solveSpec hPfxSigs)
  have hm' : (m6SpecTable tPfx solveSpec).map SpecEntry.name = m6Module.fns.map Fn.name := by
    dsimp only [m6Module]
    simp only [List.map_map, Function.comp_def, Fn.sig] at hm
    exact hm
  exact tbl_nodup_of_sigs m6_acyclic hm'

theorem m6SpecTable_noExit (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true) :
    (m6SpecTable tPfx solveSpec).all SpecEntry.noExit = true := by
  simp only [m6SpecTable, List.all_append, m6RowsPart1_noExit hPfxNoExit,
    m6RowsPart2_noExit hPfxNoExit, m6RowsPart3Pfx_noExit hPfxNoExit,
    m6OrchTailRows_noExit solveSpec, Bool.and_self]

theorem mkM6Env_noExit (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true) :
    ∀ f as bs xs m Q X X',
      mkM6Env tPfx solveSpec f as bs xs m Q X → mkM6Env tPfx solveSpec f as bs xs m Q X' :=
  env_ofTable_noExit_all (m6SpecTable_noExit tPfx solveSpec hPfxNoExit)

theorem mkM6Env_solve_bytes_m6_iff (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM6Env tPfx solveSpec "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6SpecTable tPfx solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m6OrchTail_solve_mem solveSpec).1))
  have hnd := m6SpecTable_nodup tPfx solveSpec hPfxSigs
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem mkM6Env_solve_bytes_iff (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM6Env tPfx solveSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m6SpecTable tPfx solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m6OrchTail_solve_mem solveSpec).2))
  have hnd := m6SpecTable_nodup tPfx solveSpec hPfxSigs
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem m6oSolveBytesM6Fn_mem :
    (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_m6_body⟩ : Fn) ∈ m6Module.fns := by
  change m6oSolveBytesM6Fn ∈ m6Fns
  unfold m6Fns m6FnsPart3
  repeat apply List.mem_append_right
  exact List.mem_of_getElem? (i := 6) rfl

theorem m6oSolveBytesFn_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_body⟩ : Fn) ∈ m6Module.fns := by
  change m6oSolveBytesFn ∈ m6Fns
  unfold m6Fns m6FnsPart3
  repeat apply List.mem_append_right
  exact List.mem_of_getElem? (i := 9) rfl

/-! ## 2. Complete `382/382` `ModuleOk` Assembly (Parameterized Over `hPfxOk`) -/

private theorem m6SpecTable_tPfx_mem {tPfx : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    ∀ e ∈ tPfx, e ∈ m6SpecTable tPfx solveSpec := by
  have h24 : ((m6Orch_fns.take 24).map Fn.sig).length = 24 := by t_kernel_rfl
  have hlen : tPfx.length = 24 := (m6_list_len_of_map hPfxSigs).trans h24
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi24 : i < 24 := hlen ▸ hi
  rcases Nat.lt_or_ge i 10 with h10 | h10
  · exact List.mem_append_left _ (m6RowsPart1_tPfx_mem h10 hi)
  · apply List.mem_append_right
    rcases Nat.lt_or_ge i 18 with h18 | h18
    · exact List.mem_append_left _ (m6RowsPart2_tPfx_mem h10 h18 hi)
    · apply List.mem_append_right
      exact List.mem_append_left _ (m6RowsPart3Pfx_tPfx_mem h18 hi24 hi)

/-- Parameterized `382/382` `ModuleOk` theorem for `FullM6.m6Module`, waiting only on
the `24`-row prefix `TableImpl` (`hPfxOk`) + prefix metadata (`hPfxSigs`, `hPfxSpecs`, `hWalk`). -/
theorem mkM6Env_moduleOk
    (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx solveSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx solveSpec "full_walk" [i64] [] a m Q X) :
    ModuleOk (mkM6Env tPfx solveSpec) m6Module :=
  let hnd := m6SpecTable_nodup tPfx solveSpec hPfxSigs
  let hPfxLen : (m6Orch_fns.take 24).length = tPfx.length :=
    (m6_list_len_of_map hPfxSigs).symm
  let sub1 : ∀ e ∈ m6RowsPart1 tPfx, e ∈ m6SpecTable tPfx solveSpec :=
    fun _ h => List.mem_append_left _ h
  let sub2 : ∀ e ∈ m6RowsPart2 tPfx, e ∈ m6SpecTable tPfx solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
  let sub3p : ∀ e ∈ m6RowsPart3Pfx tPfx, e ∈ m6SpecTable tPfx solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  let sub3t : ∀ e ∈ m6OrchTailRows solveSpec, e ∈ m6SpecTable tPfx solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))
  let htPfx : ∀ e ∈ tPfx, e ∈ m6SpecTable tPfx solveSpec := m6SpecTable_tPfx_mem hPfxSigs
  let hc1 : M6Part1Callees (m6SpecTable tPfx solveSpec) := m6Part1Callees_of_sub sub1
  let hc1Tail := m6Part1TailCallees_of_sub sub1
  let hc2 : M6Part2Callees (m6SpecTable tPfx solveSpec) := m6Part2Callees_of_sub sub2
  let hc2Tail := m6Part2TailCallees_of_sub sub2
  let i1 : TableImpl (mkM6Env tPfx solveSpec) m6FnsPart1 (m6RowsPart1 tPfx) :=
    m6RowsPart1_tableImpl (tbl := m6SpecTable tPfx solveSpec) hnd hPfxLen hPfxOk htPfx hPfxSpecs
      sub1
  let i2 : TableImpl (mkM6Env tPfx solveSpec) m6FnsPart2 (m6RowsPart2 tPfx) :=
    m6RowsPart2_tableImpl (tbl := m6SpecTable tPfx solveSpec) hnd hPfxLen hPfxOk htPfx hPfxSpecs
      hc1 hWalk sub2
  let i3 : TableImpl (mkM6Env tPfx solveSpec)
      m6FnsPart3 (m6RowsPart3Pfx tPfx ++ m6OrchTailRows solveSpec) :=
    m6Part3_tableImpl (tPfx := tPfx) (tbl := m6SpecTable tPfx solveSpec)
      solveSpec hWeaken hSolveMonoX hnd hPfxSigs hPfxOk htPfx hPfxSpecs hc1 hc2
      hc1Tail.1 hc1Tail.2 hc2Tail.analyzeM6 hc2Tail.restartDue hc2Tail.restart
      hc2Tail.rephaseM6 hc2Tail.hdrDecide hc2Tail.extend sub3p sub3t
  let i23 : TableImpl (mkM6Env tPfx solveSpec) (m6FnsPart2 ++ m6FnsPart3)
      (m6RowsPart2 tPfx ++ (m6RowsPart3Pfx tPfx ++ m6OrchTailRows solveSpec)) :=
    tableImpl_append (len_eq_of_sigs_eq (m6RowsPart2_sigs hPfxSigs)) i2 i3
  moduleOk_of_two_segments m6_acyclic (List.append_assoc m6FnsPart1 m6FnsPart2 m6FnsPart3)
    (len_eq_of_sigs_eq (m6RowsPart1_sigs hPfxSigs))
    (FullM6ProofUtil.allFns_of_mem fun f hf =>
      m6Fns_wf f (List.mem_append_left _ (List.mem_append_left _ hf)))
    (allFns_append
      (FullM6ProofUtil.allFns_of_mem fun f hf =>
        m6Fns_wf f (List.mem_append_left _ (List.mem_append_right _ hf)))
      (FullM6ProofUtil.allFns_of_mem fun f hf => m6Fns_wf f (List.mem_append_right _ hf)))
    i1 i23

/-- Specialized `ModuleOk` for `fullM6SolveBytesSpec` (`SAT + UNSAT`). -/
theorem mkM6Env_sound_moduleOk
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesSpec "full_walk" [i64] [] a m Q X) :
    ModuleOk (mkM6Env tPfx fullM6SolveBytesSpec) m6Module :=
  mkM6Env_moduleOk tPfx fullM6SolveBytesSpec
    (fun _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_of_spec hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesSpec_monoX hs)
    hPfxSigs hPfxSpecs hPfxOk hWalk

/-- Specialized `ModuleOk` for `fullM6SolveBytesCoreModelSpec` (for deterministic UNSAT NV). -/
theorem mkM6Env_core_moduleOk
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    ModuleOk (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) m6Module :=
  mkM6Env_moduleOk tPfx fullM6SolveBytesCoreModelSpec
    (fun _ _ _ _ hs => hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_monoX hs)
    hPfxSigs hPfxSpecs hPfxOk hWalk

/-! ## 3. Top-Level Soundness & Concrete Tier-3b UNSAT Non-Vacuity -/

/-- Top-level `kissat_solve_bytes` SAT + UNSAT soundness theorem on `FullM6.m6Module`. -/
theorem m6_solve_bytes_sound
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesSpec "full_walk" [i64] [] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator (mkM6Env tPfx fullM6SolveBytesSpec) m6Module
    "kissat_solve_bytes" FullM6Orch.kissat_solve_bytes_body
    (mkM6Env_sound_moduleOk tPfx hPfxSigs hPfxSpecs hPfxOk hWalk)
    m6oSolveBytesFn_mem
    (fun _ _ _ _ hs =>
      (mkM6Env_solve_bytes_iff tPfx fullM6SolveBytesSpec hPfxSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Top-level `kissat_solve_bytes_m6` SAT + UNSAT soundness theorem on `FullM6.m6Module`. -/
theorem m6_solve_bytes_m6_sound
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesSpec "full_walk" [i64] [] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesSpec) kissat_solve_bytes_m6_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator (mkM6Env tPfx fullM6SolveBytesSpec) m6Module
    "kissat_solve_bytes_m6" kissat_solve_bytes_m6_body
    (mkM6Env_sound_moduleOk tPfx hPfxSigs hPfxSpecs hPfxOk hWalk)
    m6oSolveBytesM6Fn_mem
    (fun _ _ _ _ hs =>
      (mkM6Env_solve_bytes_m6_iff tPfx fullM6SolveBytesSpec hPfxSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Host-framed machine-memory lift for `kissat_solve_bytes` (`PR-M6C` ready). -/
theorem m6_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      cnf.Sat (readModelFromWorkM6 st_dmem work_ptr)) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  fullM6_host_sound_lift hq hdmem

/-- Concrete Tier-3b UNSAT non-vacuity for `kissat_solve_bytes` on `nvM6UnsatInitMem`. -/
theorem m6_unsat_nv
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM6Env_core_moduleOk tPfx hPfxSigs hPfxSpecs hPfxOk hWalk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m6oSolveBytesFn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM6Env tPfx fullM6SolveBytesCoreModelSpec)
    FullM6Orch.kissat_solve_bytes_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM6Env_solve_bytes_iff tPfx fullM6SolveBytesCoreModelSpec hPfxSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

/-- Concrete Tier-3b UNSAT non-vacuity for `kissat_solve_bytes_m6` on `nvM6UnsatInitMem`. -/
theorem m6_m6_unsat_nv
    (tPfx : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hPfxSpecs : M6OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM6Env_core_moduleOk tPfx hPfxSigs hPfxSpecs hPfxOk hWalk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m6oSolveBytesM6Fn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM6Env_solve_bytes_m6_iff tPfx fullM6SolveBytesCoreModelSpec hPfxSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

/-! ## 4. Closed Dual-Arch `KissatM6` Wiring (0 Hooks) -/

/-- `M6OrchPfxTblSpecs` satisfied by concrete `m6OrchPfxSpecTable`. -/
theorem m6OrchPfxSpecTable_pfxSpecs : M6OrchPfxTblSpecs m6OrchPfxSpecTable :=
  ⟨ m6OrchPfxSpecTable_row_at 0 _
  , m6OrchPfxSpecTable_row_at 1 _
  , m6OrchPfxSpecTable_row_at 2 _
  , m6OrchPfxSpecTable_row_at 3 _
  , m6OrchPfxSpecTable_row_at 4 _
  , m6OrchPfxSpecTable_row_at 5 _
  , m6OrchPfxSpecTable_row_at 6 _
  , m6OrchPfxSpecTable_row_at 7 _
  , m6OrchPfxSpecTable_row_at 8 _
  , m6OrchPfxSpecTable_row_at 9 _
  , m6OrchPfxSpecTable_row_at 11 _
  , m6OrchPfxSpecTable_row_at 12 _
  , m6OrchPfxSpecTable_row_at 14 _
  , m6OrchPfxSpecTable_row_at 17 _
  , m6OrchPfxSpecTable_row_at 19 _
  , m6OrchPfxSpecTable_row_at 22 _
  , m6OrchPfxSpecTable_row_at 23 _ ⟩

private theorem m6_env_mem {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (nm : String) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ tbl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → Env.ofTable tbl nm as bs xs m Q X :=
  fun xs m Q X hs => Env.ofTable_of_mem hmem hnd (by
    dsimp only [SpecEntry.eff]; simp only [ite_true]; exact hno xs m Q X hs)

/-- 57-field external callee resolution for `m6OrchPfx_tableImpl` in
`mkM6Env m6OrchPfxSpecTable`. -/
theorem m6_orchPfxExtCallees (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    M6OrchPfxExtCallees (mkM6Env m6OrchPfxSpecTable solveSpec) := by
  have hnd := m6SpecTable_nodup m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs
  have sub1 : ∀ e ∈ m6RowsPart1 m6OrchPfxSpecTable,
      e ∈ m6SpecTable m6OrchPfxSpecTable solveSpec :=
    fun _ h => List.mem_append_left _ h
  have sub2 : ∀ e ∈ m6RowsPart2 m6OrchPfxSpecTable,
      e ∈ m6SpecTable m6OrchPfxSpecTable solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
  have sub3p : ∀ e ∈ m6RowsPart3Pfx m6OrchPfxSpecTable,
      e ∈ m6SpecTable m6OrchPfxSpecTable solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  have hc1 := m6Part1Callees_of_sub sub1
  have hc2 := m6Part2Callees_of_sub sub2
  have ep1 := m6Part1ExtCallees_of_sub sub1
  have ep2 := m6Part2ExtCallees_of_sub sub2
  have ep3 := m6Part3ExtCallees_of_sub sub3p
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_
         , ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_
         , ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
  · exact m6_env_mem hnd _ _ _ _ ep1.wstackDefragM6
  · exact m6_env_mem hnd _ _ _ _ ep1.watchPushM6
  · exact m6_env_mem hnd _ _ _ _ ep1.rescaleM6
  · exact m6_env_mem hnd _ _ _ _ ep1.parseBodyM6
  · exact m6_env_mem hnd _ _ _ _ ep1.litRankM6
  · exact m6_env_mem hnd _ _ _ _ ep1.sweepBinsM6cf
  · exact m6_env_mem hnd _ _ _ _ ep1.rewatchArenaM6
  · exact m6_env_mem hnd _ _ _ _ ep1.arenaSweepM6
  · exact m6_env_mem hnd _ _ _ _ ep1.markReasonsM6
  · exact m6_env_mem hnd _ _ _ _ ep2.minShrinkM6
  · exact m6_env_mem hnd _ _ _ _ ep2.deduce1uipM6
  · exact m6_env_mem hnd _ _ _ _ ep2.walkM6
  · exact m6_env_mem hnd _ _ _ _ ep3.sweepDenseM5
  · exact m6_env_mem hnd _ _ _ _ hc1.isqrt
  · exact m6_env_mem hnd _ _ _ _ hc1.backtrack
  · exact m6_env_mem hnd _ _ _ _ hc1.propagate
  · exact m6_env_mem hnd _ _ _ _ ep1.recomputeTiers
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ hc1.arenaNext
  · exact m6_env_mem hnd _ _ _ _ ep1.sortReds
  · exact m6_env_mem hnd _ _ _ _ hc1.ilog10
  · exact m6_env_mem hnd _ _ _ _ ep1.setWm
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep2.analyzeLit
  · exact m6_env_mem hnd _ _ _ _ ep1.recordUsed
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep2.clearAna
  · exact m6_env_mem hnd _ _ _ _ ep2.otfsBin
  · exact m6_env_mem hnd _ _ _ _ ep2.otfsSubsume
  · exact m6_env_mem hnd _ _ _ _ ep2.otfsLarge
  · exact m6_env_mem hnd _ _ _ _ ep2.oneLitConfl
  · exact m6_env_mem hnd _ _ _ _ ep2.anaFailedLit
      (fun _ _ _ _ h => m6aAnaFailedLitSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep2.restoreBumpAna
      (fun _ _ _ _ h => m6aRestoreBumpAnaSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ hc1.tickRel
  · exact m6_env_mem hnd _ _ _ _ hc1.emaUpdate
  · exact m6_env_mem hnd _ _ _ _ ep2.learnClause
  · exact m6_env_mem hnd _ _ _ _ ep1.extReady
      (fun _ _ _ _ h => m6HdrExtReadySpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep1.getWm
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep1.heapDown
  · exact m6_env_mem hnd _ _ _ _ hc1.log10Q16
  · exact m6_env_mem hnd _ _ _ _ ep3.reorderQueueM7
  · exact m6_env_mem hnd _ _ _ _ ep2.backboneM6
  · exact m6_env_mem hnd _ _ _ _ ep2.transitiveM6
  · exact m6_env_mem hnd _ _ _ _ ep3.minU64
  · exact m6_env_mem hnd _ _ _ _ ep2.probeRun
  · exact m6_env_mem hnd _ _ _ _ ep2.vivifyM6Hdr
      (fun _ _ _ _ h => m6aVivifySpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep3.probeDticks
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ hc1.scaleDeltaM5
  · exact m6_env_mem hnd _ _ _ _ hc2.enterDense
  · exact m6_env_mem hnd _ _ _ _ ep1.delaying
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep2.congruenceDense
  · exact m6_env_mem hnd _ _ _ _ hc2.rebuildWatches
  · exact m6_env_mem hnd _ _ _ _ ep1.reduceDelay
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep1.bumpDelay
      (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  · exact m6_env_mem hnd _ _ _ _ ep2.substitute
  · exact m6_env_mem hnd _ _ _ _ ep3.factor
  · exact m6_env_mem hnd _ _ _ _ ep2.lucky
  · exact m6_env_mem hnd _ _ _ _ ep3.compactNeeded
  · exact m6_env_mem hnd _ _ _ _ ep3.compact
  · exact m6_env_mem hnd _ _ _ _ ep3.eliminateM6

/-- Instantiated `TableImpl` for `m6Orch_fns.take 24` against `m6OrchPfxSpecTable` in `mkM6Env`. -/
theorem m6_orchPfx_tableImpl (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    TableImpl (mkM6Env m6OrchPfxSpecTable solveSpec) (m6Orch_fns.take 24) m6OrchPfxSpecTable :=
  FullM6Orch.m6OrchPfx_tableImpl
    (m6SpecTable_nodup m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs)
    (m6SpecTable_tPfx_mem m6OrchPfxSpecTable_sigs)
    (m6_orchPfxExtCallees solveSpec)

/-- `full_walk` lookup in `mkM6Env m6OrchPfxSpecTable solveSpec`. -/
theorem m6_walk_lookup (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      mkM6Env m6OrchPfxSpecTable solveSpec "full_walk" [i64] [] a m Q X := by
  intro a m Q X hs
  have hmem : (⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩ : SpecEntry) ∈
      m6SpecTable m6OrchPfxSpecTable solveSpec :=
    m6SpecTable_tPfx_mem m6OrchPfxSpecTable_sigs _ (m6OrchPfxSpecTable_row_at 15 _)
  exact Env.ofTable_of_mem hmem
    (m6SpecTable_nodup m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs) hs

/-- Canonical closed specification table for `KissatM6` (`382` rows). -/
def m6Table (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  m6SpecTable m6OrchPfxSpecTable solveSpec

/-- Canonical closed environment for `KissatM6` (`SAT + UNSAT`). -/
def m6Env : Env := mkM6Env m6OrchPfxSpecTable fullM6SolveBytesSpec

/-- Canonical closed environment for `KissatM6` (`UNSAT + CoreModel`). -/
def m6CoreEnv : Env := mkM6Env m6OrchPfxSpecTable fullM6SolveBytesCoreModelSpec

/-- Abbrev for deterministic UNSAT non-vacuity environment. -/
abbrev m6UnsatEnv : Env := m6CoreEnv

theorem m6Table_sigs (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6Table solveSpec).map (fun e => (e.name, e.as, e.rs)) = m6Fns.map Fn.sig :=
  m6SpecTable_sigs m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs

theorem m6Table_length (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6Table solveSpec).length = 382 :=
  m6SpecTable_length m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs

theorem m6Table_nodup (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m6Table solveSpec).map SpecEntry.name).Nodup :=
  m6SpecTable_nodup m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_sigs

theorem m6Table_noExit (solveSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6Table solveSpec).all SpecEntry.noExit = true :=
  m6SpecTable_noExit m6OrchPfxSpecTable solveSpec m6OrchPfxSpecTable_noExit

/-- Unconditional `ModuleOk` for `m6Module` under `m6CoreEnv` (`0` hooks). -/
theorem m6CoreEnv_moduleOk : ModuleOk m6CoreEnv m6Module :=
  mkM6Env_core_moduleOk m6OrchPfxSpecTable m6OrchPfxSpecTable_sigs
    m6OrchPfxSpecTable_pfxSpecs (m6_orchPfx_tableImpl _) (m6_walk_lookup _)

/-- Unconditional `ModuleOk` for `m6Module` under `m6Env` (`0` hooks). -/
theorem m6Env_moduleOk : ModuleOk m6Env m6Module :=
  mkM6Env_sound_moduleOk m6OrchPfxSpecTable m6OrchPfxSpecTable_sigs
    m6OrchPfxSpecTable_pfxSpecs (m6_orchPfx_tableImpl _) (m6_walk_lookup _)

/-- `noExit` property for `m6CoreEnv`. -/
theorem m6CoreEnv_noExit :
    ∀ f as bs xs m Q X X', m6CoreEnv f as bs xs m Q X → m6CoreEnv f as bs xs m Q X' :=
  mkM6Env_noExit m6OrchPfxSpecTable fullM6SolveBytesCoreModelSpec m6OrchPfxSpecTable_noExit

/-- `noExit` property for `m6Env`. -/
theorem m6Env_noExit :
    ∀ f as bs xs m Q X X', m6Env f as bs xs m Q X → m6Env f as bs xs m Q X' :=
  mkM6Env_noExit m6OrchPfxSpecTable fullM6SolveBytesSpec m6OrchPfxSpecTable_noExit

/-- Specification lookup equivalence for `kissat_solve_bytes` in `m6CoreEnv`. -/
theorem m6CoreEnv_solve_bytes_iff
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m6CoreEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      fullM6SolveBytesCoreModelSpec xs m Q (fun _ _ _ _ => False) :=
  mkM6Env_solve_bytes_iff m6OrchPfxSpecTable fullM6SolveBytesCoreModelSpec m6OrchPfxSpecTable_sigs

/-- Specification lookup equivalence for `kissat_solve_bytes` in `m6Env`. -/
theorem m6Env_solve_bytes_iff
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m6Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      fullM6SolveBytesSpec xs m Q (fun _ _ _ _ => False) :=
  mkM6Env_solve_bytes_iff m6OrchPfxSpecTable fullM6SolveBytesSpec m6OrchPfxSpecTable_sigs

/-- Unconditional UNSAT soundness of `kissat_solve_bytes` on `m6Module`. -/
theorem m6_solve_bytes_unsat
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m6Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  have hs := @m6_solve_bytes_sound m6OrchPfxSpecTable m6OrchPfxSpecTable_sigs
    m6OrchPfxSpecTable_pfxSpecs (m6_orchPfx_tableImpl _) (m6_walk_lookup _)
    cnf_ptr work_ptr fuel cnfBytes wlen R m hcfit hwfit hm
  refine wp_mono (fun rs m' hq => ?_) (fun _ _ _ _ hf => hf) _ _ hs
  rcases rs with ⟨r, ⟨⟩⟩
  exact ⟨hq.1, hq.2.1, hq.2.2.2⟩

/-- Closed concrete Tier-3b UNSAT non-vacuity for `kissat_solve_bytes` on `nvM6UnsatInitMem`. -/
theorem m6_closed_unsat_nv :
    Func.wp m6CoreEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6_unsat_nv m6OrchPfxSpecTable m6OrchPfxSpecTable_sigs
    m6OrchPfxSpecTable_pfxSpecs (m6_orchPfx_tableImpl _) (m6_walk_lookup _)

/-- Closed concrete Tier-3b UNSAT non-vacuity for `kissat_solve_bytes_m6` on `nvM6UnsatInitMem`. -/
theorem m6_closed_m6_unsat_nv :
    Func.wp m6CoreEnv kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6_m6_unsat_nv m6OrchPfxSpecTable m6OrchPfxSpecTable_sigs
    m6OrchPfxSpecTable_pfxSpecs (m6_orchPfx_tableImpl _) (m6_walk_lookup _)

end LeanQbe.T.Examples.Kissat.FullM6Proof
