/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleRows
public import LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
public import LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12ARows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRows
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 12 (`FullFidelityAssemblyStep12`, `517` fns)

Pure C0/IR assembly (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, `0` `import all`, `0` `meta import`
of `PrintCpp`/`PrintQbe`/`Legal`, `0` `@[expose]` on theorems/lemmas, `<= 6` SysV args/fn)
unifying ALL landed Step-11 + Step-12 bundles onto `fidStep10Module` (`505` fns -> `517` fns):
- **Step-11 PR 1 (`8` repls, `0` befores):** rebinding `full_ana_failed_lit_m6_hdr`'s conflict-state
  `full_backtrack(h, 0)` call via `renameFuncCalls pr3BtAcMap` to `"full_backtrack_ac_fid"`.
- **Step-11 PR 2 (`6` repls, `5` befores):** `FullFidelityTumbleRows` (`fidStep11TumRepls`,
  `fidStep11TumBefores`).
- **Step-11 PR 3 + P0-3b (`11` repls kept, `1` before):** `fidStep11Pr3Repls` with superseded
  `full_learn_clause_m6` dropped in favor of Step-12C's 3-step OOM recovery, and
  `full_backtrack_ac_fid` anchored before `"full_ana_failed_lit_m6_hdr"` (slot `124`) so it
  strictly precedes all four conflict-state callers (`124`, `148`, `150`, `157`).
- **Step-12B (`12` repls, `3` befores):** `FullFidelityStep12BRows` (`P0-4`, `P1-2`, `P1-5`,
  `P1-6`, `P1-7`).
- **Step-12C (`4` repls, `3` befores):** `FullFidelityStep12CRows` with `full_learn_clause_m6`
  rebound via `renameFuncCalls pr3BtAcMap` to `"full_backtrack_ac_fid"`.
- **Step-12A (`6` repls, `0` befores):** `FullFidelityStep12ARows` (`P0-1`, `P0-2`, `P0-3a`, `P1-1`)
  together with `P1-11` (`full_lucky -> full_lucky_late_m7`) applied onto PR 1's
  `full_preprocess_m6` via `renameFuncCalls fid12PreprocessLuckyMap`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityStep11
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open LeanQbe.T.Examples.Kissat.FullFidelitySweepEnv
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
open LeanQbe.T.Examples.Kissat.FullFidelityStep11Pr3
open LeanQbe.T.Examples.Kissat.FullFidelityStep12A
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- PR 1 `full_ana_failed_lit_m6_hdr` body rebound in conflict state (`cur_level == 1`) from
`"full_backtrack"` to `"full_backtrack_ac_fid"`. -/
def fid12AnaFailedLitM6Hdr_body : Func [i64] [i64] :=
  renameFuncCalls pr3BtAcMap FullFidelityStep11.full_ana_failed_lit_m6_hdr_body

/-- PR 1 `full_ana_failed_lit_m6_hdr` rebound in conflict state (`cur_level == 1`) from
`"full_backtrack"` to `"full_backtrack_ac_fid"`. -/
def fid12AnaFailedLitM6HdrFn : Fn :=
  ⟨"full_ana_failed_lit_m6_hdr", [i64], [i64], fid12AnaFailedLitM6Hdr_body⟩

/-- Rebinding map composing `Step-12A`'s `P1-11` (`full_lucky_late_m7`) onto PR 1's
`full_preprocess_m6` (`search_ticks` save/restore). -/
def fid12PreprocessLuckyMap : Sym → Sym
  | "full_lucky" => "full_lucky_late_m7"
  | s => s

/-- Composed PR 1 + Step-12A `full_preprocess_m6` body (`search_ticks` save/restore AND
`full_lucky_late_m7`). -/
def fid12PreprocessM6_body : Func [i64] [i64] :=
  renameFuncCalls fid12PreprocessLuckyMap FullFidelityStep11.full_preprocess_m6_body

/-- Composed PR 1 + Step-12A `full_preprocess_m6` fn. -/
def fid12PreprocessM6Fn : Fn :=
  ⟨"full_preprocess_m6", [i64], [i64], fid12PreprocessM6_body⟩

/-- PR 1 replacement list (`8` fns) with `fid12AnaFailedLitM6HdrFn` and
`fid12PreprocessM6Fn`. -/
def fid12Pr1Repls : List Fn :=
  [ fidStep11AnalyzeRsnM6HdrFn
  , fid12AnaFailedLitM6HdrFn
  , fidStep11MinShrinkM6Fn
  , fidStep11AnalyzeFn
  , fidStep11AnalyzeCoreM6Fn
  , fidStep11VivifyTierM6HdrFn
  , fidStep11SwitchModeM7Fn
  , fid12PreprocessM6Fn ]

/-- PR 3 replacement list (`11` fns): `fidStep11Pr3Repls` without `full_learn_clause_m6`
(superseded by Step-12C's 3-step OOM recovery ladder). -/
def fid12Pr3Repls : List Fn :=
  [ fid11SweepConeFn
  , fid11SaveTargetBestFn
  , fid11BacktrackFn
  , fid11Deduce1uipM6Fn
  , fid11Deduce1uipM6HdrFn
  , fid11OneLitConflFn
  , fid11LearnClauseFn
  , fid11VivCollectFidFn
  , fid11VivSort2FidFn
  , fid11VivSortFidFn
  , fid11VivClauseM6Fn ]

/-- Step-12C `full_learn_clause_m6` body rebound from `"full_backtrack"` to
`"full_backtrack_ac_fid"` while preserving its 3-step OOM recovery ladder. -/
def fid12LearnClauseM6_body : Func [i64, i64] [i64] :=
  renameFuncCalls pr3BtAcMap FullFidelityStep12C.full_learn_clause_m6_body

/-- Step-12C `full_learn_clause_m6` rebound from `"full_backtrack"` to `"full_backtrack_ac_fid"`
while preserving its 3-step OOM recovery ladder. -/
def fid12LearnClauseM6Fn : Fn :=
  ⟨"full_learn_clause_m6", [i64, i64], [i64], fid12LearnClauseM6_body⟩

/-- Step-12C replacement list (`4` fns) with `fid12LearnClauseM6Fn`. -/
def fid12Step12CRepls : List Fn :=
  [ fidStep12CAddClauseFn
  , fidStep12CSweepCopyFn
  , fid12LearnClauseM6Fn
  , fidStep12CVivSortCountsM6Fn ]

/-- Step-12A replacement list (`5` direct fns; `full_preprocess_m6` is composed in
`fid12PreprocessM6Fn` inside `fid12Pr1Repls`). -/
def fidStep12ARepls : List Fn :=
  [ fidStep12ATransSortFn
  , fidStep12ASweepSimFn
  , fidStep12ASweepVarsFn
  , fidStep12AFactorFn
  , fidStep12AProbeFn ]

/-- Combined unified Step-12 replacement list (`8 + 6 + 11 + 12 + 4 + 5 = 46` fns). -/
def fidStep12Repls : List Fn :=
  fid12Pr1Repls ++ fidStep11TumRepls ++ fid12Pr3Repls ++
  fidStep12BRepls ++ fid12Step12CRepls ++ fidStep12ARepls

/-- Combined unified Step-12 `befores` insertion plan (`5 + 1 + 3 + 3 = 12` helpers, `505 -> 517`
fns), placing `full_backtrack_ac_fid` before `"full_ana_failed_lit_m6_hdr"` (slot `124`) so it
precedes all four conflict-state callers (`124`, `148`, `150`, `157`). -/
def fidStep12Befores : List (Sym × List Fn) :=
  fidStep11TumBefores ++
  [("full_ana_failed_lit_m6_hdr", [fid11BacktrackAcFn])] ++
  fidStep12BBefores ++
  fidStep12CBefores

/-- Ordered `517`-function Step-12 `KissatFidelity` function list over `fidStep10Fns`. -/
def fidStep12Fns : List Fn :=
  patchFns fidStep12Repls fidStep12Befores fidStep10Fns

/-- Closed Gate-1 Step-12 `KissatFidelity` module (`517` fns, `0` externs, `0` exits). -/
def fidStep12Module : LeanQbe.T.Module :=
  { fidStep10Module with fns := fidStep12Fns }

end

public section

theorem fidStep12Module_fns : fidStep12Module.fns = fidStep12Fns :=
  rfl

theorem fidStep12_noExit : fidStep12Module.exits = [] :=
  fidStep10_noExit

theorem fid12Pr3Repls_eq :
    fid12Pr3Repls = fidStep11Pr3Repls.filter (·.name != "full_learn_clause_m6") :=
  rfl

theorem fid12AnaFailedLitM6HdrFn_wf : fid12AnaFailedLitM6HdrFn.Wf :=
  fun _ _ _ _ xs₁ xs₂ => wf_renameExprCalls (full_ana_failed_lit_m6_hdr_step11_wf _ _ _ _ xs₁ xs₂)

theorem fid12PreprocessM6Fn_wf : fid12PreprocessM6Fn.Wf :=
  fun _ _ _ _ xs₁ xs₂ => wf_renameExprCalls (full_preprocess_m6_step11_wf _ _ _ _ xs₁ xs₂)

theorem fid12Pr1Repls_wf : ∀ f ∈ fid12Pr1Repls, f.Wf := by
  intro f hf
  simp only [fid12Pr1Repls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_analyze_rsn_m6_hdr_step11_wf
  · exact fid12AnaFailedLitM6HdrFn_wf
  · exact full_min_shrink_m6_step11_wf
  · exact full_analyze_step11_wf
  · exact full_analyze_core_m6_step11_wf
  · exact full_vivify_tier_m6_hdr_step11_wf
  · exact full_switch_mode_m7_step11_wf
  · exact fid12PreprocessM6Fn_wf

theorem fid12Pr3Repls_wf : ∀ f ∈ fid12Pr3Repls, f.Wf := fun f hf =>
  fidStep11Pr3Repls_wf f (List.mem_filter.mp (fid12Pr3Repls_eq ▸ hf)).1

theorem fid12LearnClauseM6Fn_wf : fid12LearnClauseM6Fn.Wf :=
  fun _ _ _ _ xs₁ xs₂ => wf_renameExprCalls (full_learn_clause_m6_step12c_wf _ _ _ _ xs₁ xs₂)

theorem fid12Step12CRepls_wf : ∀ f ∈ fid12Step12CRepls, f.Wf := by
  intro f hf
  simp only [fid12Step12CRepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_add_clause_step12c_wf
  · exact full_sweep_copy_step12c_wf
  · exact fid12LearnClauseM6Fn_wf
  · exact full_viv_sort_counts_m6_step12c_wf

theorem fidStep12ARepls_wf : ∀ f ∈ fidStep12ARepls, f.Wf := by
  intro f hf
  simp only [fidStep12ARepls, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact fidStep12ATransSort_wf
  · exact fidStep12ASweepSim_wf
  · exact fidStep12ASweepVars_wf
  · exact fidStep12AFactor_wf
  · exact fidStep12AProbe_wf

theorem fidStep12Repls_wf : ∀ f ∈ fidStep12Repls, f.Wf := by
  intro f hf
  simp only [fidStep12Repls, List.mem_append] at hf
  rcases hf with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exact fid12Pr1Repls_wf f h1
  · exact fidStep11TumRepls_wf f h2
  · exact fid12Pr3Repls_wf f h3
  · exact fidStep12BRepls_wf f h4
  · exact fid12Step12CRepls_wf f h5
  · exact fidStep12ARepls_wf f h6

theorem fidStep12Befores_wf : ∀ f ∈ fidStep12Befores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidStep12Befores, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, List.mem_singleton] at hf
  rcases hf with ((h1 | h2) | h3) | h4
  · exact fidStep11TumBefores_wf f h1
  · subst h2; exact fid11_backtrack_ac_wf
  · exact fidStep12BBefores_wf f h3
  · exact fidStep12CBefores_wf f h4

theorem fidStep12Module_wf : ∀ f ∈ fidStep12Module.fns, f.Wf :=
  patchFns_wf fidStep10Module_wf fidStep12Repls_wf fidStep12Befores_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
