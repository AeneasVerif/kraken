/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
public import LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Step-11 PR 3 Pure C0 Row Lists (`FullFidelityStep11Pr3Rows`)

Pure AST/data assembly barrel (`0` proof/spec/meta imports, `--data-proof` firewall clean)
exporting the `12` disjoint Step-11 PR 3 replacement functions (`S11-6a` `1` fn + `S11-7` `7` fns +
`S11-8` `4` fns) and `1` inserted helper (`full_backtrack_ac_fid` before `"full_one_lit_confl"`)
plus `Func.Wf` proofs for 2-line plug-in to `FullFidelityAssemblyStep11.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Combined Step-11 PR 3 replacement list (`12` functions: `S11-6a` + `S11-7` + `S11-8`). -/
def fidStep11Pr3Repls : List Fn :=
  fid11SweepEnvRepls ++ fid11BacktrackCsRepls ++ fid11VivFlagRepls

/-- Combined Step-11 PR 3 `befores` insertion list (`1` fn: `full_backtrack_ac_fid` before
`"full_one_lit_confl"`). -/
def fidStep11Pr3Befores : List (Sym × List Fn) :=
  fid11BacktrackCsBefores

end

public section

theorem fidStep11Pr3Repls_wf : ∀ f ∈ fidStep11Pr3Repls, f.Wf := by
  intro f hf
  simp only [fidStep11Pr3Repls, List.mem_append] at hf
  rcases hf with (h | h) | h
  · exact fid11SweepEnvRepls_wf f h
  · exact fid11BacktrackCsRepls_wf f h
  · exact fid11VivFlagRepls_wf f h

theorem fidStep11Pr3Befores_wf : ∀ h ∈ fidStep11Pr3Befores.flatMap Prod.snd, h.Wf :=
  fid11BacktrackCsBefores_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
