/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 11 (`FullFidelityAssemblyStep11`, `505` fns)

Pure C0/IR assembly (`0` `*Proof*` imports, `0` `import all`, `0` `meta import` of
`PrintCpp`/`PrintQbe`/`Legal`) splicing the `8` Step-11 PR 1 replacements
(`FullFidelityStep11.fidStep11Pr1Repls`) together with plug-in slots for PR 2 (`S11-3`/`S11-5`) and
PR 3 (`S11-6a`/`S11-7`/`S11-8`) onto `fidStep10Module`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- PR 2 (`S11-3` + `S11-5` tumble) plug-in replacement slot (empty in PR 1). -/
def fidStep11TumRepls : List Fn :=
  []

/-- PR 2 (`S11-3` + `S11-5` tumble) plug-in `befores` slot (empty in PR 1). -/
def fidStep11TumBefores : List (Sym × List Fn) :=
  []

/-- PR 3 (`S11-6a` + `S11-7` + `S11-8`) plug-in replacement slot (empty in PR 1). -/
def fidStep11Pr3Repls : List Fn :=
  []

/-- PR 3 (`S11-6a` + `S11-7` + `S11-8`) plug-in `befores` slot (empty in PR 1). -/
def fidStep11Pr3Befores : List (Sym × List Fn) :=
  []

/-- Combined Step-11 replacement list (`PR1 ++ PR2 ++ PR3`). -/
def fidStep11AllRepls : List Fn :=
  FullFidelityStep11.fidStep11Pr1Repls ++ fidStep11TumRepls ++ fidStep11Pr3Repls

/-- Combined Step-11 `befores` list (`PR1 ++ PR2 ++ PR3`). -/
def fidStep11AllBefores : List (Sym × List Fn) :=
  FullFidelityStep11.fidStep11Befores ++ fidStep11TumBefores ++ fidStep11Pr3Befores

/-- Ordered Step-11 `KissatFidelity` function list (`fidStep10Fns` patched with
`fidStep11AllRepls` and `fidStep11AllBefores`). -/
def fidStep11Fns : List Fn :=
  patchFns fidStep11AllRepls fidStep11AllBefores fidStep10Fns

/-- Closed Gate-1 Step-11 `KissatFidelity` module (`0` externs, `0` exits). -/
def fidStep11Module : LeanQbe.T.Module :=
  { fidStep10Module with fns := fidStep11Fns }

end

public section

theorem fidStep11Fns_eq : fidStep11Module.fns = fidStep11Fns :=
  rfl

theorem fidStep11TumRepls_wf : ∀ f ∈ fidStep11TumRepls, f.Wf := by
  intro f hf; cases hf

theorem fidStep11Pr3Repls_wf : ∀ f ∈ fidStep11Pr3Repls, f.Wf := by
  intro f hf; cases hf

theorem fidStep11TumBefores_wf : ∀ f ∈ fidStep11TumBefores.flatMap Prod.snd, f.Wf := by
  intro f hf; cases hf

theorem fidStep11Pr3Befores_wf : ∀ f ∈ fidStep11Pr3Befores.flatMap Prod.snd, f.Wf := by
  intro f hf; cases hf

theorem fidStep11AllRepls_wf : ∀ f ∈ fidStep11AllRepls, f.Wf := by
  intro f hf
  simp only [fidStep11AllRepls, List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact FullFidelityStep11.fidStep11Pr1Repls_wf f h1
  · exact fidStep11TumRepls_wf f h2
  · exact fidStep11Pr3Repls_wf f h3

theorem fidStep11AllBefores_wf : ∀ f ∈ fidStep11AllBefores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidStep11AllBefores, List.flatMap_append, List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact FullFidelityStep11.fidStep11Befores_wf f h1
  · exact fidStep11TumBefores_wf f h2
  · exact fidStep11Pr3Befores_wf f h3

theorem fidStep11Module_wf : ∀ f ∈ fidStep11Module.fns, f.Wf :=
  patchFns_wf fidStep10Module_wf fidStep11AllRepls_wf fidStep11AllBefores_wf

theorem fidStep11_noExit : fidStep11Module.exits = [] :=
  fidStep10_noExit

end

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11
