/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6SatNv

/-!
# Kissat Unified `M7` `410`-Fn `ModuleOk` + Soundness & Non-Vacuity (`FullM7Proof`)

Assembles the complete `410`-row `m7SpecTable tPfx tBve solveSpec` aligned 1-to-1 with
`FullM7.m7Module.fns`, parameterized only over the `2` remaining in-flight standalone hypotheses
(`0` `sorry` / `admit` / `axiom`, `FullM7BcpHot` discharged):
- `tPfx` (`21` rows matching `m7OrchPfxFns`), awaiting `FullM6OrchProof0..1`
- `tBve` (`43` rows matching `m7BveAllFns`), awaiting `FullM7BveGatesProof0..5`

Exports:
1. `m7SpecTable`, `mkM7Env`, `m7SpecTable_sigs`, `m7SpecTable_length` (`410`),
   `m7SpecTable_nodup`, `m7SpecTable_noExit`, and `mkM7Env_solve_bytes{_m6}_iff`.
2. `mkM7Env_moduleOk` (`ModuleOk (mkM7Env tPfx tBve solveSpec) m7Module`), plus specializations
   `m7_solve_bytes_unsat_wp`, `mkM7Env_sound_moduleOk`, and `mkM7Env_core_moduleOk`.
3. Top-level source & host-framed soundness (`m7_solve_bytes_sound`, `m7_solve_bytes_m6_sound`,
   `m7_solve_bytes_host_sound`) and concrete Tier-3b UNSAT non-vacuity (`m7_unsat_nv`,
   `m7_m6_unsat_nv`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Proof

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
open LeanQbe.T.Examples.Kissat.FullM7

/-! ## 1. Unified `410`-Row `m7SpecTable` & Environment Metadata -/

/-- Complete `410`-row specification table aligned 1-to-1 with `FullM7.m7Module.fns`. -/
def m7SpecTable (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  m7RowsPart1 tPfx ++ (m7RowsPart2 tPfx ++ (m7RowsPart3Pfx tPfx tBve ++ m7OrchTailRows solveSpec))

/-- Closed `Env` induced by `m7SpecTable tPfx tBve solveSpec`. -/
def mkM7Env (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) : Env :=
  Env.ofTable (m7SpecTable tPfx tBve solveSpec)

theorem m7SpecTable_sigs (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tPfx tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      m7Fns.map Fn.sig := by
  have hm123 : m7Fns =
      m7FnsPart1 ++ (m7FnsPart2 ++ (m7FnsPart3.take 129 ++ m7FnsPart3.drop 129)) := by
    rw [m7Fns, List.append_assoc, List.take_append_drop]
  rw [hm123]
  unfold m7SpecTable
  simp only [List.map_append]
  rw [m7RowsPart1_sigs hPfxSigs, m7RowsPart2_sigs hPfxSigs,
    m7RowsPart3Pfx_sigs hPfxSigs hBveSigs, m7OrchTailRows_sigs solveSpec]

private theorem len_eq_of_sigs_eq {fs : List Fn} {rs : List SpecEntry}
    (h : rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig) :
    fs.length = rs.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1.symm

private theorem m7Fns_length : m7Fns.length = 410 := by t_kernel_rfl

theorem m7SpecTable_length (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tPfx tBve solveSpec).length = 410 :=
  (len_eq_of_sigs_eq (m7SpecTable_sigs tPfx tBve solveSpec hPfxSigs hBveSigs)).symm.trans
    m7Fns_length

theorem m7SpecTable_nodup (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ((m7SpecTable tPfx tBve solveSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (m7SpecTable_sigs tPfx tBve solveSpec hPfxSigs hBveSigs)
  have hm' : (m7SpecTable tPfx tBve solveSpec).map SpecEntry.name = m7Module.fns.map Fn.name := by
    dsimp only [m7Module]
    simp only [List.map_map, Function.comp_def, Fn.sig] at hm
    exact hm
  exact tbl_nodup_of_sigs m7_acyclic hm'

theorem m7SpecTable_noExit (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    (m7SpecTable tPfx tBve solveSpec).all SpecEntry.noExit = true := by
  simp only [m7SpecTable, List.all_append, m7RowsPart1_noExit hPfxNoExit,
    m7RowsPart2_noExit hPfxNoExit, m7RowsPart3Pfx_noExit hPfxNoExit hBveNoExit,
    m7OrchTailRows_noExit solveSpec, Bool.and_self]

theorem mkM7Env_noExit (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    ∀ f as bs xs m Q X X',
      mkM7Env tPfx tBve solveSpec f as bs xs m Q X →
      mkM7Env tPfx tBve solveSpec f as bs xs m Q X' :=
  env_ofTable_noExit_all (m7SpecTable_noExit tPfx tBve solveSpec hPfxNoExit hBveNoExit)

theorem mkM7Env_elim_of_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    {e : SpecEntry} (he : e ∈ m7SpecTable tPfx tBve solveSpec)
    (hnd : ((m7SpecTable tPfx tBve solveSpec).map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : mkM7Env tPfx tBve solveSpec e.name e.as e.rs xs m Q X) :
    e.eff xs m Q X :=
  env_ofTable_elim_of_mem he hnd h

theorem mkM7Env_row_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hnd : ((m7SpecTable tPfx tBve solveSpec).map SpecEntry.name).Nodup)
    (f : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7SpecTable tPfx tBve solveSpec)
    (hm : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) :=
      by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, sp xs m Q X → mkM7Env tPfx tBve solveSpec f as bs xs m Q X :=
  envRow_mem hnd f as bs sp hmem hm

theorem mkM7Env_solve_bytes_m6_iff (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM7Env tPfx tBve solveSpec "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7SpecTable tPfx tBve solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m7OrchTail_solve_mem solveSpec).1))
  have hnd := m7SpecTable_nodup tPfx tBve solveSpec hPfxSigs hBveSigs
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem mkM7Env_solve_bytes_iff (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM7Env tPfx tBve solveSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7SpecTable tPfx tBve solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m7OrchTail_solve_mem solveSpec).2))
  have hnd := m7SpecTable_nodup tPfx tBve solveSpec hPfxSigs hBveSigs
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem m7oSolveBytesM6Fn_mem :
    (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_m6_body⟩ : Fn) ∈ m7Module.fns := by
  change m6oSolveBytesM6Fn ∈ m7Fns
  unfold m7Fns m7FnsPart3
  apply List.mem_append_right
  exact List.mem_of_getElem? (i := 130) (by t_kernel_rfl)

theorem m7oSolveBytesFn_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      FullM6Orch.kissat_solve_bytes_body⟩ : Fn) ∈ m7Module.fns := by
  change m6oSolveBytesFn ∈ m7Fns
  unfold m7Fns m7FnsPart3
  apply List.mem_append_right
  exact List.mem_of_getElem? (i := 133) (by t_kernel_rfl)

theorem m7CheckModelFn_mem :
    (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissat_check_model_body⟩ : Fn) ∈ m7Module.fns := by
  change (⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissat_check_model_body⟩ : Fn) ∈ m7Fns
  unfold m7Fns m7FnsPart1
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_of_getElem? (i := 7) (by t_kernel_rfl)

/-! ## 2. Complete `410/410` `ModuleOk` Assembly (Parameterized Over In-Flight Hypotheses) -/

theorem m7SpecTable_part1_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart1 tPfx, e ∈ m7SpecTable tPfx tBve solveSpec :=
  fun _ h => List.mem_append_left _ h

theorem m7SpecTable_part2_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart2 tPfx, e ∈ m7SpecTable tPfx tBve solveSpec :=
  fun _ h => List.mem_append_right _ (List.mem_append_left _ h)

theorem m7SpecTable_part3Pfx_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ m7SpecTable tPfx tBve solveSpec :=
  fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))

theorem m7SpecTable_tPfx_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig) :
    ∀ e ∈ tPfx, e ∈ m7SpecTable tPfx tBve solveSpec := by
  have h21 : m7OrchPfxFns.length = 21 := by rw [m7OrchPfxFns_eq]; rfl
  have hlen : tPfx.length = 21 := (len_eq_of_sigs_eq hPfxSigs).symm.trans h21
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi21 : i < 21 := hlen ▸ hi
  rcases Nat.lt_or_ge i 10 with h10 | h10
  · exact List.mem_append_left _ (m7RowsPart1_tPfx_mem h10 hi)
  · apply List.mem_append_right
    rcases Nat.lt_or_ge i 15 with h15 | h15
    · exact List.mem_append_left _ (m7RowsPart2_tPfx_mem h10 h15 hi)
    · apply List.mem_append_right
      exact List.mem_append_left _ (m7RowsPart3Pfx_tPfx_mem h15 hi21 hi)

private theorem m7SpecTable_tBve_mem {tPfx tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ∀ e ∈ tBve, e ∈ m7SpecTable tPfx tBve solveSpec := by
  have hlen : tBve.length = 43 := (len_eq_of_sigs_eq hBveSigs).symm.trans m7BveAllFns_length
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi43 : i < 43 := hlen ▸ hi
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (m7RowsPart3Pfx_tBve_mem hi43 hi)))

/-- Parameterized `410/410` `ModuleOk` theorem for `FullM7.m7Module`, waiting only on
the `21`-row `FullM6Orch` prefix (`hPfxOk`) and `43`-row `FullM7BveGates` slice (`hBveOk`). -/
theorem mkM7Env_moduleOk
    (tPfx tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve solveSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tPfx tBve solveSpec) m7Module :=
  let hnd := m7SpecTable_nodup tPfx tBve solveSpec hPfxSigs hBveSigs
  let hnoExit := m7SpecTable_noExit tPfx tBve solveSpec hPfxNoExit hBveNoExit
  let hPfxLen : m7OrchPfxFns.length = tPfx.length := len_eq_of_sigs_eq hPfxSigs
  let sub1 : ∀ e ∈ m7RowsPart1 tPfx, e ∈ m7SpecTable tPfx tBve solveSpec :=
    fun _ h => List.mem_append_left _ h
  let sub2 : ∀ e ∈ m7RowsPart2 tPfx, e ∈ m7SpecTable tPfx tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
  let sub3p : ∀ e ∈ m7RowsPart3Pfx tPfx tBve, e ∈ m7SpecTable tPfx tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  let sub3t : ∀ e ∈ m7OrchTailRows solveSpec, e ∈ m7SpecTable tPfx tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))
  let htPfx : ∀ e ∈ tPfx, e ∈ m7SpecTable tPfx tBve solveSpec :=
    m7SpecTable_tPfx_mem hPfxSigs
  let htBve : ∀ e ∈ tBve, e ∈ m7SpecTable tPfx tBve solveSpec :=
    m7SpecTable_tBve_mem hBveSigs
  let hc1 : M7Part1Callees (m7SpecTable tPfx tBve solveSpec) := m7Part1Callees_of_sub sub1
  let hc1Tail := m7Part1TailCallees_of_sub sub1
  let hc2 : M7Part2Callees (m7SpecTable tPfx tBve solveSpec) := m7Part2Callees_of_sub sub2
  let hc2c : M7Part2CongCallees (m7SpecTable tPfx tBve solveSpec) :=
    m7Part2CongCallees_of_sub sub2
  let i1 : TableImpl (mkM7Env tPfx tBve solveSpec) m7FnsPart1 (m7RowsPart1 tPfx) :=
    m7RowsPart1_tableImpl (tbl := m7SpecTable tPfx tBve solveSpec) hnd hPfxLen hPfxOk htPfx
      hPfxSpecs sub1
  let hcd : ∀ xs m Q X, FullM3CongBva.m3CongruenceDenseSpec xs m Q X →
      Func.wp (mkM7Env tPfx tBve solveSpec) FullM7.full_congruence_dense_body xs m Q X :=
    full_congruence_dense_m7_wp (mkM7Env tPfx tBve solveSpec)
      (envRow_mem hnd _ _ _ _ hc2c.extBin) (envRow_mem hnd _ _ _ _ hc2c.findUE)
      (envRow_mem hnd _ _ _ _ hc2c.extract)
      (envRow_mem hnd _ _ _ _ hc2c.iteAll
        (fun _ _ _ _ h => FullM7CongIte.m7ExtractIteAllM6Spec_monoX h))
      (envRow_mem hnd _ _ _ _ hc2c.work) (envRow_mem hnd _ _ _ _ hc2c.fwdSub)
  let i2 : TableImpl (mkM7Env tPfx tBve solveSpec) m7FnsPart2 (m7RowsPart2 tPfx) :=
    m7RowsPart2_tableImpl (tbl := m7SpecTable tPfx tBve solveSpec) hnd hPfxLen hPfxOk htPfx
      hPfxSpecs hc1 hcd sub2
  let i3 : TableImpl (mkM7Env tPfx tBve solveSpec)
      m7FnsPart3 (m7RowsPart3Pfx tPfx tBve ++ m7OrchTailRows solveSpec) :=
    m7Part3_tableImpl solveSpec hWeaken hSolveMonoX hnd hnoExit hPfxSigs hPfxOk
      hBveSigs hBveOk hBveSpecs htBve hPfxSpecs htPfx hc1 hc2 hc1Tail sub3p sub3t
  let i23 : TableImpl (mkM7Env tPfx tBve solveSpec) (m7FnsPart2 ++ m7FnsPart3)
      (m7RowsPart2 tPfx ++ (m7RowsPart3Pfx tPfx tBve ++ m7OrchTailRows solveSpec)) :=
    tableImpl_append (len_eq_of_sigs_eq (m7RowsPart2_sigs hPfxSigs)) i2 i3
  moduleOk_of_two_segments m7_acyclic (List.append_assoc m7FnsPart1 m7FnsPart2 m7FnsPart3)
    (len_eq_of_sigs_eq (m7RowsPart1_sigs hPfxSigs))
    m7FnsPart1_wf (allFns_append m7FnsPart2_wf m7FnsPart3_wf) i1 i23

/-- Original-strength UNSAT specification dispatch on `m7SoundEnv` for `kissat_solve_bytes` and
`kissat_solve_bytes_m6` via `fullM6_unsatSpec_of_solveBytesSpec_wp`. -/
theorem m7_solve_bytes_unsat_wp
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolveBytesUnsatSpec a m Q X) :
    Func.wp (mkM7Env tPfx tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      a m Q X := by
  have hm := mkM7Env_moduleOk tPfx tBve fullM6SolveBytesSpec
    (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
    (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
    hPfxSigs hPfxNoExit hPfxSpecs hPfxOk hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesFn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsatSpec_of_solveBytesSpec_wp (mkM7Env tPfx tBve fullM6SolveBytesSpec)
    FullM6Orch.kissat_solve_bytes_body (fun a0 m0 Q0 X0 h0 => ?_) a m Q X hs
  exact hfn a0 m0 Q0 X0
    ((mkM7Env_solve_bytes_iff tPfx tBve fullM6SolveBytesSpec hPfxSigs hBveSigs).mpr
      (fullM6SolveBytesSpec_monoX h0))

/-- Specialized `ModuleOk` for `fullM6SolveBytesSpec` (`UNSAT + constructive SAT`, `m7SoundEnv`).
-/
theorem mkM7Env_sound_moduleOk
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7Module :=
  mkM7Env_moduleOk tPfx tBve fullM6SolveBytesSpec
    (fun _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_of_spec hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesSpec_monoX hs)
    hPfxSigs hPfxNoExit hPfxSpecs hPfxOk hBveSigs hBveNoExit hBveSpecs hBveOk

/-- Specialized `ModuleOk` for `fullM6SolveBytesCoreModelSpec` (for deterministic UNSAT NV). -/
theorem mkM7Env_core_moduleOk
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7Module :=
  mkM7Env_moduleOk tPfx tBve fullM6SolveBytesCoreModelSpec
    (fun _ _ _ _ hs => hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_monoX hs)
    hPfxSigs hPfxNoExit hPfxSpecs hPfxOk hBveSigs hBveNoExit hBveSpecs hBveOk

/-! ## 3. Top-Level SAT + UNSAT Soundness & Concrete Non-Vacuity -/

/-- Top-level `kissat_solve_bytes` SAT + UNSAT soundness theorem on `FullM7.m7Module`. -/
theorem m7_solve_bytes_sound
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tPfx tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
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
  fullM6_solve_bytes_moduleOk_combinator (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7Module
    "kissat_solve_bytes" FullM6Orch.kissat_solve_bytes_body
    (mkM7Env_sound_moduleOk tPfx tBve hPfxSigs hPfxNoExit hPfxSpecs hPfxOk
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7oSolveBytesFn_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tPfx tBve fullM6SolveBytesSpec hPfxSigs hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Top-level `kissat_solve_bytes_m6` SAT + UNSAT soundness theorem on `FullM7.m7Module`. -/
theorem m7_solve_bytes_m6_sound
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tPfx tBve fullM6SolveBytesSpec) kissat_solve_bytes_m6_body
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
  fullM6_solve_bytes_moduleOk_combinator (mkM7Env tPfx tBve fullM6SolveBytesSpec) m7Module
    "kissat_solve_bytes_m6" kissat_solve_bytes_m6_body
    (mkM7Env_sound_moduleOk tPfx tBve hPfxSigs hPfxNoExit hPfxSpecs hPfxOk
      hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7oSolveBytesM6Fn_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_m6_iff tPfx tBve fullM6SolveBytesSpec hPfxSigs hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Host-framed machine-memory lift for `kissat_solve_bytes`. -/
theorem m7_solve_bytes_host_sound
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

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes` on
`nvM6UnsatInitMem`. -/
theorem m7_unsat_nv
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM7Env_core_moduleOk tPfx tBve hPfxSigs hPfxNoExit hPfxSpecs hPfxOk
    hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesFn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec)
    FullM6Orch.kissat_solve_bytes_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM7Env_solve_bytes_iff tPfx tBve fullM6SolveBytesCoreModelSpec hPfxSigs hBveSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes_m6` on
`nvM6UnsatInitMem`. -/
theorem m7_m6_unsat_nv
    (tPfx tBve : List SpecEntry)
    (hPfxSigs : tPfx.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxSpecs : M7OrchPfxTblSpecs tPfx)
    (hPfxOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7OrchPfxFns tPfx)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM7Env_core_moduleOk tPfx tBve hPfxSigs hPfxNoExit hPfxSpecs hPfxOk
    hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesM6Fn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM7Env tPfx tBve fullM6SolveBytesCoreModelSpec)
    kissat_solve_bytes_m6_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM7Env_solve_bytes_m6_iff tPfx tBve fullM6SolveBytesCoreModelSpec hPfxSigs hBveSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

end LeanQbe.T.Examples.Kissat.FullM7Proof
