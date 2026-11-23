/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Proof0c
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6SatNv

/-!
# Kissat `D-Full` Unified `M6.0` `382`-Fn `ModuleOk` + Soundness & UNSAT NV (`FullM6Proof`)

Assembles the complete `382`-row `m6SpecTable tPfx solveSpec` aligned 1-to-1 with
`FullM6.m6Module.fns`, parameterized only over the `24`-fn `M6Orch` prefix `tPfx` (`hPfxOk` +
`M6OrchPfxTblSpecs` + `hWalk`) being finished in `FullM6OrchProof0..1`:

1. `m6SpecTable`, `mkM6Env`, `m6SpecTable_sigs`, `m6SpecTable_length` (`382`),
   `m6SpecTable_nodup`, `m6SpecTable_noExit`, and `mkM6Env_solve_bytes{_m6}_iff`.
2. `mkM6Env_moduleOk` (`ModuleOk (mkM6Env tPfx solveSpec) m6Module`), plus pre-specialized
   `mkM6Env_sound_moduleOk` (`fullM6SolveBytesSpec`) and `mkM6Env_core_moduleOk`
   (`fullM6SolveBytesCoreModelSpec`).
3. Top-level UNSAT + host-framed soundness (`m6_solve_bytes_sound`,
   `m6_solve_bytes_m6_sound`, `m6_solve_bytes_host_sound`) and
   concrete Tier-3b UNSAT non-vacuity (`m6_unsat_nv`, `m6_m6_unsat_nv`).
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

end LeanQbe.T.Examples.Kissat.FullM6Proof
