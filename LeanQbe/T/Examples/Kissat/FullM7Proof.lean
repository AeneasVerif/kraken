/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6SatNv

/-!
# Kissat Unified `M7` `410`-Fn `ModuleOk` + Soundness & Non-Vacuity (`FullM7Proof`)

Assembles the complete `410`-row `m7SpecTable tBve solveSpec` aligned 1-to-1 with
`FullM7.m7Module.fns`, discharging the `21`-fn `FullM6Orch` prefix (`m7OrchPfxRows`) directly via
`FullM6OrchProof0..1` and `FullM7AnalyzeHdrProof`, leaving ONLY `1` in-flight standalone hypothesis
(`0` `sorry` / `admit` / `axiom`):
- `tBve` (`43` rows matching `m7BveAllFns`), awaiting `FullM7BveGatesProof0..5`

Exports:
1. `m7OrchPfxRows`, `m7OrchPfx_tableImpl`, `m7SpecTable`, `mkM7Env`, `m7SpecTable_sigs`,
   `m7SpecTable_length` (`410`), `m7SpecTable_nodup`, `m7SpecTable_noExit`, and
   `mkM7Env_solve_bytes{_m6}_iff`.
2. `mkM7Env_moduleOk` (`ModuleOk (mkM7Env tBve solveSpec) m7Module`), plus specializations
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

/-! ## 1. Wired `21`-Row `m7OrchPfxRows` & Unified `410`-Row `m7SpecTable` -/

/-- Discharged `21`-row specification prefix aligned 1-to-1 with `m7OrchPfxFns` (all `noExit`),
matching `[0..14] ++ [18..23]` of `FullM6OrchProof` with `M7` `m7MinShrinkSpec` at `[11]`. -/
def m7OrchPfxRows : List SpecEntry :=
  [ ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_lit_rank", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], m7AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], m7Deduce1uipHdrSpec, true⟩
  , ⟨"full_analyze_core_m6", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ ]

theorem m7OrchPfxRows_sigs :
    m7OrchPfxRows.map (fun e => (e.name, e.as, e.rs)) = m7OrchPfxFns.map Fn.sig := by
  rw [m7OrchPfxFns_eq]
  t_kernel_rfl

theorem m7OrchPfxRows_noExit : m7OrchPfxRows.all SpecEntry.noExit = true := by rfl

theorem m7OrchPfxRows_specs : M7OrchPfxTblSpecs m7OrchPfxRows :=
  ⟨ List.mem_of_getElem? (i := 0) rfl
  , List.mem_of_getElem? (i := 1) rfl
  , List.mem_of_getElem? (i := 2) rfl
  , List.mem_of_getElem? (i := 3) rfl
  , List.mem_of_getElem? (i := 4) rfl
  , List.mem_of_getElem? (i := 5) rfl
  , List.mem_of_getElem? (i := 6) rfl
  , List.mem_of_getElem? (i := 7) rfl
  , List.mem_of_getElem? (i := 8) rfl
  , List.mem_of_getElem? (i := 9) rfl
  , List.mem_of_getElem? (i := 11) rfl
  , List.mem_of_getElem? (i := 12) rfl
  , List.mem_of_getElem? (i := 14) rfl
  , List.mem_of_getElem? (i := 16) rfl
  , List.mem_of_getElem? (i := 19) rfl
  , List.mem_of_getElem? (i := 20) rfl ⟩

/-- Complete `410`-row specification table aligned 1-to-1 with `FullM7.m7Module.fns`. -/
def m7SpecTable (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  m7RowsPart1 m7OrchPfxRows ++
    (m7RowsPart2 m7OrchPfxRows ++
      (m7RowsPart3Pfx m7OrchPfxRows tBve ++ m7OrchTailRows solveSpec))

/-- Closed `Env` induced by `m7SpecTable tBve solveSpec`. -/
def mkM7Env (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) : Env :=
  Env.ofTable (m7SpecTable tBve solveSpec)

theorem m7SpecTable_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      m7Fns.map Fn.sig := by
  have hm123 : m7Fns =
      m7FnsPart1 ++ (m7FnsPart2 ++ (m7FnsPart3.take 129 ++ m7FnsPart3.drop 129)) := by
    rw [m7Fns, List.append_assoc, List.take_append_drop]
  rw [hm123]
  unfold m7SpecTable
  simp only [List.map_append]
  rw [m7RowsPart1_sigs m7OrchPfxRows_sigs, m7RowsPart2_sigs m7OrchPfxRows_sigs,
    m7RowsPart3Pfx_sigs m7OrchPfxRows_sigs hBveSigs, m7OrchTailRows_sigs solveSpec]

private theorem len_eq_of_sigs_eq {fs : List Fn} {rs : List SpecEntry}
    (h : rs.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig) :
    fs.length = rs.length := by
  have h1 := congrArg List.length h
  simpa only [List.length_map] using h1.symm

theorem m7Fns_length : m7Fns.length = 410 := by t_kernel_rfl

theorem m7SpecTable_length (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tBve solveSpec).length = 410 :=
  (len_eq_of_sigs_eq (m7SpecTable_sigs tBve solveSpec hBveSigs)).symm.trans m7Fns_length

theorem m7SpecTable_nodup (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ((m7SpecTable tBve solveSpec).map SpecEntry.name).Nodup := by
  have hm := congrArg (List.map Prod.fst) (m7SpecTable_sigs tBve solveSpec hBveSigs)
  have hm' : (m7SpecTable tBve solveSpec).map SpecEntry.name = m7Module.fns.map Fn.name := by
    dsimp only [m7Module]
    simp only [List.map_map, Function.comp_def, Fn.sig] at hm
    exact hm
  exact tbl_nodup_of_sigs m7_acyclic hm'

theorem m7SpecTable_noExit (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    (m7SpecTable tBve solveSpec).all SpecEntry.noExit = true := by
  simp only [m7SpecTable, List.all_append, m7RowsPart1_noExit m7OrchPfxRows_noExit,
    m7RowsPart2_noExit m7OrchPfxRows_noExit,
    m7RowsPart3Pfx_noExit m7OrchPfxRows_noExit hBveNoExit,
    m7OrchTailRows_noExit solveSpec, Bool.and_self]

theorem mkM7Env_noExit (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    ∀ f as bs xs m Q X X',
      mkM7Env tBve solveSpec f as bs xs m Q X →
      mkM7Env tBve solveSpec f as bs xs m Q X' :=
  env_ofTable_noExit_all (m7SpecTable_noExit tBve solveSpec hBveNoExit)

theorem mkM7Env_elim_of_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    {e : SpecEntry} (he : e ∈ m7SpecTable tBve solveSpec)
    (hnd : ((m7SpecTable tBve solveSpec).map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : mkM7Env tBve solveSpec e.name e.as e.rs xs m Q X) :
    e.eff xs m Q X :=
  env_ofTable_elim_of_mem he hnd h

theorem mkM7Env_row_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hnd : ((m7SpecTable tBve solveSpec).map SpecEntry.name).Nodup)
    (f : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hm : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → mkM7Env tBve solveSpec f as bs xs m Q X :=
  envRow_mem hnd f as bs sp hmem hm

theorem mkM7Env_solve_bytes_m6_iff (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM7Env tBve solveSpec "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m7OrchTail_solve_mem solveSpec).1))
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  exact ⟨fun h => env_ofTable_elim_of_mem hmem hnd h, fun h => Env.ofTable_of_mem hmem hnd h⟩

theorem mkM7Env_solve_bytes_iff (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    mkM7Env tBve solveSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      solveSpec xs m Q (fun _ _ _ _ => False) := by
  have hmem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
      solveSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (m7OrchTail_solve_mem solveSpec).2))
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
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

/-! ## 2. Complete `410/410` `ModuleOk` Assembly (Only `tBve` Remaining) -/

theorem m7SpecTable_part1_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart1 m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec :=
  fun _ h => List.mem_append_left _ h

theorem m7SpecTable_part2_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart2 m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec :=
  fun _ h => List.mem_append_right _ (List.mem_append_left _ h)

theorem m7SpecTable_part3Pfx_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7RowsPart3Pfx m7OrchPfxRows tBve, e ∈ m7SpecTable tBve solveSpec :=
  fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))

theorem m7SpecTable_pfx_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec := by
  have hlen : m7OrchPfxRows.length = 21 := by rfl
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

theorem m7SpecTable_tBve_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ∀ e ∈ tBve, e ∈ m7SpecTable tBve solveSpec := by
  have hlen : tBve.length = 43 := (len_eq_of_sigs_eq hBveSigs).symm.trans m7BveAllFns_length
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hi43 : i < 43 := hlen ▸ hi
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (m7RowsPart3Pfx_tBve_mem hi43 hi)))

theorem m7SpecTable_tail_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} :
    ∀ e ∈ m7OrchTailRows solveSpec, e ∈ m7SpecTable tBve solveSpec :=
  fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))

/-- Discharges all `21` functions of `m7OrchPfxFns` against `m7OrchPfxRows` inside `mkM7Env`,
using `FullM6OrchProof0..1`, `FullM7AnalyzeHdrProof`, and caller rows from Part 1/2/3 + `tBve`. -/
theorem m7OrchPfx_tableImpl
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveSpecs : M7BveAllTblSpecs tBve) :
    TableImpl (mkM7Env tBve solveSpec) m7OrchPfxFns m7OrchPfxRows := by
  have hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  have hc1 := m7Part1Callees_of_sub (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc1p := m7Part1PfxCallees_of_sub
    (m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2 := m7Part2Callees_of_sub (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc2p := m7Part2PfxCallees_of_sub
    (m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec))
  have hc3p := m7Part3PfxCallees_of_sub
    (m7SpecTable_part3Pfx_mem (tBve := tBve) (solveSpec := solveSpec))
  let htPfx : ∀ e ∈ m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec := m7SpecTable_pfx_mem
  let htBve : ∀ e ∈ tBve, e ∈ m7SpecTable tBve solveSpec := m7SpecTable_tBve_mem hBveSigs
  have rArSwp := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 7) rfl))
  have rMrkRsn := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 8) rfl))
  have rAnaRsn := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 10) rfl))
    (fun _ _ _ _ h => m7AnalyzeRsnHdrSpec_monoX h)
  have rDed1uip := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 13) rfl))
    (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h)
  have rSwpDense := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 15) rfl))
  have rProbeTail := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 17) rfl))
    (fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  have rProbeM6 := envRow_mem hnd _ _ _ _ (htPfx _ (List.mem_of_getElem? (i := 18) rfl))
    (fun _ _ _ _ h => m6ProbeSpec_monoX h)
  have rMsM6 := envRow_mem hnd _ _ _ _ hc2p.minShrinkM6
    (fun _ _ _ _ h => FullM7SpecBridges.m7MinShrinkSpec_monoX h)
  have hProp := m7_fullPropagate_to_bcpS15 (envRow_mem hnd _ _ _ _ hc1.propagate)
  rw [m7OrchPfxFns_eq]; unfold m7OrchPfxRows
  exact
    ⟨ SpecEntry.Impl.of (full_wstack_defrag_wp _ (envRow_mem hnd _ _ _ _ hc1p.wstackDefragM6))
    , SpecEntry.Impl.of (full_watch_push_wp _ (envRow_mem hnd _ _ _ _ hc1p.watchPushM6))
    , SpecEntry.Impl.of (full_rescale_wp _ (envRow_mem hnd _ _ _ _ hc1p.rescaleM6))
    , SpecEntry.Impl.of (full_parse_body_wp _ (envRow_mem hnd _ _ _ _ hc1p.parseBodyM6))
    , SpecEntry.Impl.of (full_lit_rank_wp _ (envRow_mem hnd _ _ _ _ hc1p.litRankM6))
    , SpecEntry.Impl.of (full_sweep_bins_wp _ (envRow_mem hnd _ _ _ _ hc1p.sweepBinsM6cf))
    , SpecEntry.Impl.of (full_rewatch_arena_wp _ (envRow_mem hnd _ _ _ _ hc1p.rewatchArenaM6))
    , SpecEntry.Impl.of (full_arena_sweep_wp _ (envRow_mem hnd _ _ _ _ hc1p.arenaSweepM6))
    , SpecEntry.Impl.of (full_mark_reasons_wp _ (envRow_mem hnd _ _ _ _ hc1p.markReasonsM6))
    , SpecEntry.Impl.of (full_reduce_m6_wp _ (envRow_mem hnd _ _ _ _ hc1.isqrt)
        (envRow_mem hnd _ _ _ _ hc1.ilog10) (envRow_mem hnd _ _ _ _ hc1.arenaNext)
        (envRow_mem hnd _ _ _ _ hc1p.recomputeTiers (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1.hdrSetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        rMrkRsn (envRow_mem hnd _ _ _ _ hc1p.sortReds) (envRow_mem hnd _ _ _ _ hc1.backtrack)
        hProp rArSwp)
    , SpecEntry.Impl.of (full_analyze_rsn_m6_hdr_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.analyzeLit)
        (envRow_mem hnd _ _ _ _ hc1p.recordUsed (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))
    , SpecEntry.Impl.of (full_min_shrink_any_wp _ rMsM6)
    , SpecEntry.Impl.of (full_deduce_1uip_wp _ (envRow_mem hnd _ _ _ _ hc2p.deduce1uipM6))
    , SpecEntry.Impl.of (full_deduce_1uip_m6_hdr_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.analyzeLit)
        rAnaRsn (envRow_mem hnd _ _ _ _ hc2p.clearAna) (envRow_mem hnd _ _ _ _ hc2p.otfsLarge)
        (envRow_mem hnd _ _ _ _ hc2p.otfsBin) (envRow_mem hnd _ _ _ _ hc2p.otfsSubsume))
    , SpecEntry.Impl.of (full_analyze_core_m6_m7_wp _ (envRow_mem hnd _ _ _ _ hc2p.oneLitConfl)
        (envRow_mem hnd _ _ _ _ hc2p.anaFailedLit
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aAnaFailedLitSpec_monoX h))
        rDed1uip
        (envRow_mem hnd _ _ _ _ hc2p.restoreBumpAna
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aRestoreBumpAnaSpec_monoX h))
        rMsM6 (envRow_mem hnd _ _ _ _ hc1.tickRel) (envRow_mem hnd _ _ _ _ hc1.emaUpdate)
        (envRow_mem hnd _ _ _ _ hc2p.learnClause))
    , SpecEntry.Impl.of (full_sweep_dense_m6_wp _ (envRow_mem hnd _ _ _ _ hc3p.sweepDenseM5))
    , SpecEntry.Impl.of (full_reorder_m6_wp _ (envRow_mem hnd _ _ _ _ hc3p.reorderQueueM7))
    , SpecEntry.Impl.of (full_probe_tail_m6_wp _ (envRow_mem hnd _ _ _ _ hc2p.backboneM6)
        (envRow_mem hnd _ _ _ _ hc2p.transitiveM6) (envRow_mem hnd _ _ _ _ hc3p.minU64)
        (envRow_mem hnd _ _ _ _ hc2p.probeRun)
        (envRow_mem hnd _ _ _ _ hc2p.vivifyM6Hdr
          (fun _ _ _ _ h => FullM6OrchAdapters.m6aVivifySpec_monoX h)))
    , SpecEntry.Impl.of (full_probe_m6_wp _
        (envRow_mem hnd _ _ _ _ hc3p.probeDticks (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1.ilog10) (envRow_mem hnd _ _ _ _ hc1.scaleDeltaM5)
        (envRow_mem hnd _ _ _ _ hc2.enterDense)
        (envRow_mem hnd _ _ _ _ hc1p.delaying (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc2p.congruenceDense) (envRow_mem hnd _ _ _ _ hc2.rebuildWatches)
        (envRow_mem hnd _ _ _ _ hc1.hdrSetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1p.reduceDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (envRow_mem hnd _ _ _ _ hc1p.bumpDelay (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        rSwpDense (envRow_mem hnd _ _ _ _ hc2p.substitute) rProbeTail
        (envRow_mem hnd _ _ _ _ hc2p.backboneM6) (envRow_mem hnd _ _ _ _ hc3p.minU64)
        (envRow_mem hnd _ _ _ _ hc3p.factor))
    , SpecEntry.Impl.of (full_preprocess_m6_wp _ hProp rArSwp (envRow_mem hnd _ _ _ _ hc2p.lucky)
        (envRow_mem hnd _ _ _ _ hc3p.compactNeeded) (envRow_mem hnd _ _ _ _ hc3p.compact)
        (envRow_mem hnd _ _ _ _ hc1.scaleDeltaM5) rProbeM6)
    , SpecEntry.Impl.of (full_simplify_m6_wp _ (envRow_mem hnd _ _ _ _ hc1.backtrack) rProbeM6
        (envRow_mem hnd _ _ _ _ (htBve _ hBveSpecs.eliminateM6))
        (envRow_mem hnd _ _ _ _ hc3p.compactNeeded) (envRow_mem hnd _ _ _ _ hc3p.compact))
    , trivial ⟩

/-- Parameterized `410/410` `ModuleOk` theorem for `FullM7.m7Module`, awaiting only the `43`-row
`FullM7BveGates` slice (`hBveOk`). -/
theorem mkM7Env_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve solveSpec) m7Module :=
  let hnd := m7SpecTable_nodup tBve solveSpec hBveSigs
  let hnoExit := m7SpecTable_noExit tBve solveSpec hBveNoExit
  let hPfxLen : m7OrchPfxFns.length = m7OrchPfxRows.length := len_eq_of_sigs_eq m7OrchPfxRows_sigs
  let hPfxOk := m7OrchPfx_tableImpl tBve solveSpec hBveSigs hBveSpecs
  let sub1 : ∀ e ∈ m7RowsPart1 m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec :=
    fun _ h => List.mem_append_left _ h
  let sub2 : ∀ e ∈ m7RowsPart2 m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
  let sub3p : ∀ e ∈ m7RowsPart3Pfx m7OrchPfxRows tBve, e ∈ m7SpecTable tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  let sub3t : ∀ e ∈ m7OrchTailRows solveSpec, e ∈ m7SpecTable tBve solveSpec :=
    fun _ h => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))
  let htPfx : ∀ e ∈ m7OrchPfxRows, e ∈ m7SpecTable tBve solveSpec := m7SpecTable_pfx_mem
  let htBve : ∀ e ∈ tBve, e ∈ m7SpecTable tBve solveSpec := m7SpecTable_tBve_mem hBveSigs
  let hc1 : M7Part1Callees (m7SpecTable tBve solveSpec) := m7Part1Callees_of_sub sub1
  let hc1Tail := m7Part1TailCallees_of_sub sub1
  let hc2 : M7Part2Callees (m7SpecTable tBve solveSpec) := m7Part2Callees_of_sub sub2
  let hc2c : M7Part2CongCallees (m7SpecTable tBve solveSpec) := m7Part2CongCallees_of_sub sub2
  let i1 : TableImpl (mkM7Env tBve solveSpec) m7FnsPart1 (m7RowsPart1 m7OrchPfxRows) :=
    m7RowsPart1_tableImpl (tbl := m7SpecTable tBve solveSpec) hnd hPfxLen hPfxOk htPfx
      m7OrchPfxRows_specs sub1
  let hcd : ∀ xs m Q X, FullM3CongBva.m3CongruenceDenseSpec xs m Q X →
      Func.wp (mkM7Env tBve solveSpec) FullM7.full_congruence_dense_body xs m Q X :=
    full_congruence_dense_m7_wp (mkM7Env tBve solveSpec)
      (envRow_mem hnd _ _ _ _ hc2c.extBin) (envRow_mem hnd _ _ _ _ hc2c.findUE)
      (envRow_mem hnd _ _ _ _ hc2c.extract)
      (envRow_mem hnd _ _ _ _ hc2c.iteAll
        (fun _ _ _ _ h => FullM7CongIte.m7ExtractIteAllM6Spec_monoX h))
      (envRow_mem hnd _ _ _ _ hc2c.work) (envRow_mem hnd _ _ _ _ hc2c.fwdSub)
  let i2 : TableImpl (mkM7Env tBve solveSpec) m7FnsPart2 (m7RowsPart2 m7OrchPfxRows) :=
    m7RowsPart2_tableImpl (tbl := m7SpecTable tBve solveSpec) hnd hPfxLen hPfxOk htPfx
      m7OrchPfxRows_specs hc1 hcd sub2
  let i3 : TableImpl (mkM7Env tBve solveSpec)
      m7FnsPart3 (m7RowsPart3Pfx m7OrchPfxRows tBve ++ m7OrchTailRows solveSpec) :=
    m7Part3_tableImpl solveSpec hWeaken hSolveMonoX hnd hnoExit m7OrchPfxRows_sigs hPfxOk
      hBveSigs hBveOk hBveSpecs htBve m7OrchPfxRows_specs htPfx hc1 hc2 hc1Tail sub3p sub3t
  let i23 : TableImpl (mkM7Env tBve solveSpec) (m7FnsPart2 ++ m7FnsPart3)
      (m7RowsPart2 m7OrchPfxRows ++
        (m7RowsPart3Pfx m7OrchPfxRows tBve ++ m7OrchTailRows solveSpec)) :=
    tableImpl_append (len_eq_of_sigs_eq (m7RowsPart2_sigs m7OrchPfxRows_sigs)) i2 i3
  moduleOk_of_two_segments m7_acyclic (List.append_assoc m7FnsPart1 m7FnsPart2 m7FnsPart3)
    (len_eq_of_sigs_eq (m7RowsPart1_sigs m7OrchPfxRows_sigs))
    m7FnsPart1_wf (allFns_append m7FnsPart2_wf m7FnsPart3_wf) i1 i23

/-- Original-strength UNSAT specification dispatch on `m7SoundEnv` for `kissat_solve_bytes` and
`kissat_solve_bytes_m6` via `fullM6_unsatSpec_of_solveBytesSpec_wp`. -/
theorem m7_solve_bytes_unsat_wp
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolveBytesUnsatSpec a m Q X) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      a m Q X := by
  have hm := mkM7Env_moduleOk tBve fullM6SolveBytesSpec
    (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
    (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
    hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesFn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsatSpec_of_solveBytesSpec_wp (mkM7Env tBve fullM6SolveBytesSpec)
    FullM6Orch.kissat_solve_bytes_body (fun a0 m0 Q0 X0 h0 => ?_) a m Q X hs
  exact hfn a0 m0 Q0 X0
    ((mkM7Env_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
      (fullM6SolveBytesSpec_monoX h0))

/-- Specialized `ModuleOk` for `fullM6SolveBytesSpec` (`UNSAT + constructive SAT`, `m7SoundEnv`).
-/
theorem mkM7Env_sound_moduleOk
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve fullM6SolveBytesSpec) m7Module :=
  mkM7Env_moduleOk tBve fullM6SolveBytesSpec
    (fun _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_of_spec hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesSpec_monoX hs)
    hBveSigs hBveNoExit hBveSpecs hBveOk

/-- Specialized `ModuleOk` for `fullM6SolveBytesCoreModelSpec` (for deterministic UNSAT NV). -/
theorem mkM7Env_core_moduleOk
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7Module :=
  mkM7Env_moduleOk tBve fullM6SolveBytesCoreModelSpec
    (fun _ _ _ _ hs => hs)
    (fun _ _ _ _ _ hs => fullM6SolveBytesCoreModelSpec_monoX hs)
    hBveSigs hBveNoExit hBveSpecs hBveOk

/-! ## 3. Top-Level Soundness & Concrete UNSAT Non-Vacuity -/

/-- Top-level `kissat_solve_bytes` soundness theorem on `FullM7.m7Module`. -/
theorem m7_solve_bytes_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
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
  fullM6_solve_bytes_moduleOk_combinator (mkM7Env tBve fullM6SolveBytesSpec) m7Module
    "kissat_solve_bytes" FullM6Orch.kissat_solve_bytes_body
    (mkM7Env_sound_moduleOk tBve hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7oSolveBytesFn_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs))
    hcfit hwfit hm

/-- Top-level `kissat_solve_bytes_m6` soundness theorem on `FullM7.m7Module`. -/
theorem m7_solve_bytes_m6_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) kissat_solve_bytes_m6_body
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
  fullM6_solve_bytes_moduleOk_combinator (mkM7Env tBve fullM6SolveBytesSpec) m7Module
    "kissat_solve_bytes_m6" kissat_solve_bytes_m6_body
    (mkM7Env_sound_moduleOk tBve hBveSigs hBveNoExit hBveSpecs hBveOk)
    m7oSolveBytesM6Fn_mem
    (fun _ _ _ _ hs =>
      (mkM7Env_solve_bytes_m6_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
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
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM7Env_core_moduleOk tBve hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesFn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM7Env tBve fullM6SolveBytesCoreModelSpec)
    FullM6Orch.kissat_solve_bytes_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM7Env_solve_bytes_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes_m6` on
`nvM6UnsatInitMem`. -/
theorem m7_m6_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm := mkM7Env_core_moduleOk tBve hBveSigs hBveNoExit hBveSpecs hBveOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7oSolveBytesM6Fn_mem
  have hfn := (hm.fnsOk pre _ post hsplit).2.2
  refine fullM6_unsat_nv (mkM7Env tBve fullM6SolveBytesCoreModelSpec)
    kissat_solve_bytes_m6_body ?_
  intro a m0 Q X hs
  exact hfn a m0 Q X
    ((mkM7Env_solve_bytes_m6_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
      (fullM6SolveBytesCoreModelSpec_monoX hs))

end LeanQbe.T.Examples.Kissat.FullM7Proof
