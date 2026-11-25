/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainInline
public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
public import LeanQbe.T.Examples.Kissat.FullFidelityInlBase
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlBase
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Symbolic PGO-Inlined Module for `KissatFidelity` (`FullFidelityInl`, `499` fns)

Constructs `fidInlMod := fidModule.optInlinePolicy fidInlPolicy` and its zero-scan
chunk-materializable counterpart `fidInlChunkMod := fidModule.optInlinePolicy
fidInlChunkPolicy` (`499` fns, `0` externs, `0` exits, `std3` axioms only).

## Zero-Scan `inline_chunk_base!` Equivalence (`< 1s`)

Setting `singleSiteMax := 0`, `maxTotalDup := 0`, and `requireLoopSite := false` in
`fidInlChunkPolicy` reduces `inlSiteCounts`/`inlLoopCounts` to `[]` in `O(1)` inside
`FullFidelityInlBase` (`fidInlBase.rest0_eq`), while preserving bit-identical QBE and C0
printed IR (`#guard`s below).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInl

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

private theorem solveBytes_exists_of_sigs (M : Module)
    (hSigs : M.fns.map Fn.sig = fidModule.fns.map Fn.sig) :
    ∃ body : Func [i64, i64, i64, i64, i64] [i64],
      (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns := by
  have hsig : m6oSolveBytesFn.sig ∈ M.fns.map Fn.sig := by
    rw [hSigs]
    exact List.mem_map.mpr ⟨m6oSolveBytesFn, fid_solveBytes_mem, rfl⟩
  obtain ⟨f, hf, hfsig⟩ := List.mem_map.mp hsig
  rcases f with ⟨nm, as, rs, body⟩
  dsimp only [Fn.sig, m6oSolveBytesFn, FullM6Orch.m6oSolveBytesFn] at hfsig
  have hnm : nm = "kissat_solve_bytes" := congrArg Prod.fst hfsig
  have hsig2 : (as, rs) = ([i64, i64, i64, i64, i64], [i64]) := congrArg Prod.snd hfsig
  have has : as = [i64, i64, i64, i64, i64] := congrArg Prod.fst hsig2
  have hrs : rs = [i64] := congrArg Prod.snd hsig2
  subst hnm; subst has; subst hrs
  exact ⟨body, hf⟩

/-- PGO-inlined and renormalized Gate-1 `KissatFidelity` module (`499` functions). -/
abbrev fidInlMod : Module :=
  fidModule.optInlinePolicy fidInlPolicy

/-- Definitional unfolding of `fidInlMod`. -/
theorem fidInlMod_eq : fidInlMod = fidModule.optInlinePolicy fidInlPolicy :=
  rfl

/-- `fidInlMod` preserves `externs = []`. -/
theorem fidInlMod_externs : fidInlMod.externs = [] := by
  simp only [fidInlMod_eq, Module.optInlinePolicy_externs]
  exact fid_externs_empty

/-- `fidInlMod` preserves `exits = []`. -/
theorem fidInlMod_exits : fidInlMod.exits = [] :=
  fid_noExit

/-- `fidInlMod.fns` preserves the exact function-signature list of `fidModule.fns`. -/
theorem fidInlFns_sigs :
    fidInlMod.fns.map Fn.sig = fidModule.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs fidModule fidInlPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

/-- `fidInlMod` preserves the exact function count (`499`). -/
theorem fidInlFns_length : fidInlMod.fns.length = 499 := by
  have hlen := congrArg List.length fidInlFns_sigs
  simp only [List.length_map] at hlen
  exact hlen.trans fidFns_length

/-- Every function in `fidInlMod` satisfies `Fn.Wf`. -/
theorem fidInlMod_wf : ∀ f ∈ fidInlMod.fns, f.Wf :=
  fidInlPolicy_wf fidModule_acyclic fidModule_wf

/-- `fidInlMod` preserves `checkAcyclic = true`. -/
theorem fidInlMod_acyclic : fidInlMod.checkAcyclic = true :=
  fidInlPolicy_checkAcyclic fidModule_acyclic fidModule_wf

/-- Closed `0`-hook `ModuleOk` lifted across `fidInlPolicy` + `Fn.renorm` to `fidInlMod`. -/
theorem fidInlMod_ok : ModuleOk fidEnv fidInlMod :=
  fidInlPolicy_ok fid_moduleOk

/-- Existence of the `"kissat_solve_bytes"` entry point inside `fidInlMod.fns`. -/
theorem fidInl_solveBytes_exists :
    ∃ body : Func [i64, i64, i64, i64, i64] [i64],
      (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ fidInlMod.fns :=
  solveBytes_exists_of_sigs fidInlMod fidInlFns_sigs

/-- The PGO-inlined + renormalized body of `"kissat_solve_bytes"` in `fidInlMod`. -/
noncomputable def fidInlSolveBytesBody : Func [i64, i64, i64, i64, i64] [i64] :=
  Classical.choose fidInl_solveBytes_exists

/-- `fidInlSolveBytesBody` belongs to `fidInlMod.fns` under `"kissat_solve_bytes"` signature. -/
theorem fidInl_solveBytes_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fidInlSolveBytesBody⟩ : Fn) ∈
      fidInlMod.fns :=
  Classical.choose_spec fidInl_solveBytes_exists

/-- Zero-scan chunk-materializable Gate-1 PGO-inlined module (`fidInlChunkPolicy`). -/
abbrev fidInlChunkMod : Module :=
  fidModule.optInlinePolicy fidInlChunkPolicy

/-- Definitional unfolding of `fidInlChunkMod`. -/
theorem fidInlChunkMod_eq : fidInlChunkMod = fidModule.optInlinePolicy fidInlChunkPolicy :=
  rfl

/-- `fidInlChunkMod` preserves `externs = []`. -/
theorem fidInlChunkMod_externs : fidInlChunkMod.externs = [] := by
  simp only [fidInlChunkMod_eq, Module.optInlinePolicy_externs]
  exact fid_externs_empty

/-- `fidInlChunkMod` preserves `exits = []`. -/
theorem fidInlChunkMod_exits : fidInlChunkMod.exits = [] :=
  fid_noExit

/-- `fidInlChunkMod.fns` preserves the exact function-signature list of `fidModule.fns`. -/
theorem fidInlChunkFns_sigs :
    fidInlChunkMod.fns.map Fn.sig = fidModule.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs fidModule fidInlChunkPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

/-- `fidInlChunkMod` preserves the exact function count (`499`). -/
theorem fidInlChunkFns_length : fidInlChunkMod.fns.length = 499 := by
  have hlen := congrArg List.length fidInlChunkFns_sigs
  simp only [List.length_map] at hlen
  exact hlen.trans fidFns_length

/-- Every function in `fidInlChunkMod` satisfies `Fn.Wf`. -/
theorem fidInlChunkMod_wf : ∀ f ∈ fidInlChunkMod.fns, f.Wf :=
  fidInlChunkPolicy_wf fidModule_acyclic fidModule_wf

/-- `fidInlChunkMod` preserves `checkAcyclic = true`. -/
theorem fidInlChunkMod_acyclic : fidInlChunkMod.checkAcyclic = true :=
  fidInlChunkPolicy_checkAcyclic fidModule_acyclic fidModule_wf

/-- Closed `0`-hook `ModuleOk` lifted across `fidInlChunkPolicy` to `fidInlChunkMod`. -/
theorem fidInlChunkMod_ok : ModuleOk fidEnv fidInlChunkMod :=
  fidInlChunkPolicy_ok fid_moduleOk

/-- Existence of the `"kissat_solve_bytes"` entry point inside `fidInlChunkMod.fns`. -/
theorem fidInlChunk_solveBytes_exists :
    ∃ body : Func [i64, i64, i64, i64, i64] [i64],
      (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈
        fidInlChunkMod.fns :=
  solveBytes_exists_of_sigs fidInlChunkMod fidInlChunkFns_sigs

/-- The `"kissat_solve_bytes"` body inside `fidInlChunkMod`. -/
noncomputable def fidInlChunkSolveBytesBody : Func [i64, i64, i64, i64, i64] [i64] :=
  Classical.choose fidInlChunk_solveBytes_exists

/-- `fidInlChunkSolveBytesBody` belongs to `fidInlChunkMod.fns`. -/
theorem fidInlChunk_solveBytes_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fidInlChunkSolveBytesBody⟩ : Fn) ∈
      fidInlChunkMod.fns :=
  Classical.choose_spec fidInlChunk_solveBytes_exists

private def fidInlExceptEq (a b : Except String String) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | _, _ => false

#guard fidInlBase.siteCounts.isEmpty && fidInlBase.loopCounts.isEmpty
#guard fidInlExceptEq (PrintQbe.module fidInlMod) (PrintQbe.module fidInlChunkMod)
#guard fidInlExceptEq (PrintCpp.ppTModule fidInlMod) (PrintCpp.ppTModule fidInlChunkMod)

end LeanQbe.T.Examples.Kissat.FullFidelityInl

end
