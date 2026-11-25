/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainInline
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# Symbolic PGO-Inlined Module for `KissatFidelity` (`FullFidelityInl`, Step 2: `471` fns)

Constructs `fidInlMod := fidStep2Module.optInlinePolicy fidInlPolicy` symbolically and transports
`fidInlFns_length` (`471`), `0` externs, `0` exits, `fidInlMod_wf`, `fidInlMod_acyclic`,
`fidInlMod_ok`, and `fidInl_solveBytes_mem` directly via `Module.optInlinePolicy_*` (`std3`
axioms only, zero kernel reduction over AST call sites).

## Planned Materialized Chunk Schedule (`471 -> 503` fns)

When target (`Amd64`/`Arm64`) linked-certificate materialization is wired atop the final
Gate-1 assembly (`Base -> Sweep -> BcpHotPush -> Bve -> Cong -> VivK6 -> Bva`):
- Planned `inline_chunk_base!` + `inline_chunk!` split: `3 x 64` + `14 x 22` + tail chunks
  covering all functions cleanly, matching `FullM7FidelityInl` prefix chunking.
- Note: `MainCertInlineChunk.inline_chunk_base!` emits a kernel `Eq.refl` check on
  `InlineChunk.inlSiteCounts` (`fnsCallSites` via `incCallSite`) whenever `maxTotalDup > 0`
  (`fidInlPolicy.maxTotalDup := 1500`); keeping `FullFidelityInl` symbolic at Step 2 keeps
  `M5Hub` fast and clean.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInl

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-- PGO-inlined and renormalized Gate-1 Step-2 module (`471` functions). -/
abbrev fidInlMod : Module :=
  fidStep2Module.optInlinePolicy fidInlPolicy

/-- Definitional unfolding of `fidInlMod`. -/
theorem fidInlMod_eq : fidInlMod = fidStep2Module.optInlinePolicy fidInlPolicy :=
  rfl

/-- `fidInlMod` preserves `externs = []`. -/
theorem fidInlMod_externs : fidInlMod.externs = [] := by
  simp only [fidInlMod_eq, Module.optInlinePolicy_externs]
  exact fidStep2_externs_empty

/-- `fidInlMod` preserves `exits = []`. -/
theorem fidInlMod_exits : fidInlMod.exits = [] :=
  fidStep2_noExit

/-- `fidInlMod.fns` preserves the exact function-signature list of `fidStep2Module.fns`. -/
theorem fidInlFns_sigs :
    fidInlMod.fns.map Fn.sig = fidStep2Module.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs fidStep2Module fidInlPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

/-- `fidInlMod` preserves the exact function count (`471`). -/
theorem fidInlFns_length : fidInlMod.fns.length = 471 := by
  have hlen := congrArg List.length fidInlFns_sigs
  simp only [List.length_map] at hlen
  exact hlen.trans fidStep2Fns_length

/-- Every function in `fidInlMod` satisfies `Fn.Wf`. -/
theorem fidInlMod_wf : ∀ f ∈ fidInlMod.fns, f.Wf :=
  fidInlPolicy_wf fidStep2Module_acyclic fidStep2Module_wf

/-- `fidInlMod` preserves `checkAcyclic = true`. -/
theorem fidInlMod_acyclic : fidInlMod.checkAcyclic = true :=
  fidInlPolicy_checkAcyclic fidStep2Module_acyclic fidStep2Module_wf

/-- Closed `0`-hook `ModuleOk` lifted across `fidInlPolicy` + `Fn.renorm` to `fidInlMod`. -/
theorem fidInlMod_ok : ModuleOk fidStep2Env fidInlMod :=
  fidInlPolicy_ok fidStep2_moduleOk

/-- Existence of the `"kissat_solve_bytes"` entry point inside `fidInlMod.fns`. -/
theorem fidInl_solveBytes_exists :
    ∃ body : Func [i64, i64, i64, i64, i64] [i64],
      (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ fidInlMod.fns := by
  have hsig :
      m6oSolveBytesFn.sig ∈ fidInlMod.fns.map Fn.sig := by
    rw [fidInlFns_sigs]
    exact List.mem_map.mpr ⟨m6oSolveBytesFn, fidStep2_solveBytes_mem, rfl⟩
  obtain ⟨f, hf, hfsig⟩ := List.mem_map.mp hsig
  rcases f with ⟨nm, as, rs, body⟩
  dsimp only [Fn.sig, m6oSolveBytesFn, FullM6Orch.m6oSolveBytesFn] at hfsig
  have hnm : nm = "kissat_solve_bytes" := congrArg Prod.fst hfsig
  have hsig2 : (as, rs) = ([i64, i64, i64, i64, i64], [i64]) := congrArg Prod.snd hfsig
  have has : as = [i64, i64, i64, i64, i64] := congrArg Prod.fst hsig2
  have hrs : rs = [i64] := congrArg Prod.snd hsig2
  subst hnm; subst has; subst hrs
  exact ⟨body, hf⟩

/-- The PGO-inlined + renormalized body of `"kissat_solve_bytes"` in `fidInlMod`. -/
noncomputable def fidInlSolveBytesBody : Func [i64, i64, i64, i64, i64] [i64] :=
  Classical.choose fidInl_solveBytes_exists

/-- `fidInlSolveBytesBody` belongs to `fidInlMod.fns` under `"kissat_solve_bytes"` signature. -/
theorem fidInl_solveBytes_mem :
    (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fidInlSolveBytesBody⟩ : Fn) ∈
      fidInlMod.fns :=
  Classical.choose_spec fidInl_solveBytes_exists

end LeanQbe.T.Examples.Kissat.FullFidelityInl

end
