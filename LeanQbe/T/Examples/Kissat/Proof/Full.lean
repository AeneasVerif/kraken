/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.Src.InlPolicy
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Solver
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Search.Spec
import LeanQbe.T.Examples.Kissat.Proof.Float64.Cert
import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Cert
import LeanQbe.T.Examples.Kissat.Proof.Limits.Cert
import LeanQbe.T.Examples.Kissat.Proof.Arena.Cert
import LeanQbe.T.Examples.Kissat.Proof.Watch.Cert
import LeanQbe.T.Examples.Kissat.Proof.Heap.Cert
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Cert
import LeanQbe.T.Examples.Kissat.Proof.Clause.Cert
import LeanQbe.T.Examples.Kissat.Proof.Tiers.Cert
import LeanQbe.T.Examples.Kissat.Proof.Bump.Cert
import LeanQbe.T.Examples.Kissat.Proof.Internal.Cert
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Cert
import LeanQbe.T.Examples.Kissat.Proof.Parse.Cert
import LeanQbe.T.Examples.Kissat.Proof.Collect.Cert
import LeanQbe.T.Examples.Kissat.Proof.Compact.Cert
import LeanQbe.T.Examples.Kissat.Proof.Reduce.Cert
import LeanQbe.T.Examples.Kissat.Proof.Deduce.Cert
import LeanQbe.T.Examples.Kissat.Proof.Minimize.Cert
import LeanQbe.T.Examples.Kissat.Proof.Learn.Cert
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Cert
import LeanQbe.T.Examples.Kissat.Proof.Decide.Cert
import LeanQbe.T.Examples.Kissat.Proof.Restart.Cert
import LeanQbe.T.Examples.Kissat.Proof.Extend.Cert
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Cert
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Cert
import LeanQbe.T.Examples.Kissat.Proof.Backbone.Cert
import LeanQbe.T.Examples.Kissat.Proof.Transitive.Cert
import LeanQbe.T.Examples.Kissat.Proof.Substitute.Cert
import LeanQbe.T.Examples.Kissat.Proof.Dense.Cert
import LeanQbe.T.Examples.Kissat.Proof.Congruence.Cert
import LeanQbe.T.Examples.Kissat.Proof.Kitten.Cert
import LeanQbe.T.Examples.Kissat.Proof.Sweep.Cert
import LeanQbe.T.Examples.Kissat.Proof.Forward.Cert
import LeanQbe.T.Examples.Kissat.Proof.Gates.Cert
import LeanQbe.T.Examples.Kissat.Proof.Definition.Cert
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Cert
import LeanQbe.T.Examples.Kissat.Proof.Factor.Cert
import LeanQbe.T.Examples.Kissat.Proof.Reorder.Cert
import LeanQbe.T.Examples.Kissat.Proof.Probe.Cert
import LeanQbe.T.Examples.Kissat.Proof.Walk.Cert
import LeanQbe.T.Examples.Kissat.Proof.Search.Cert

/-!
# Canonical `41`-Subsystem Proof Assembly for `Src.Full.kissatModule` (`Proof.Full`)

Assembles all `41` `Src.*` modules (`418` functions) on flat `CanonicalEnv` via
`Proof.Lib.SubsystemCert.fold` with `0` legacy `Full*` imports, `0` `PatchModule` layers,
and `O(N)` `checkAcyclicTrie` verification:
1. `fullSpecs`, `fullEnv`, `fullSpecs_sigs`, `fullSpecs_nodup`, `fullSpecs_noExit`.
2. `kissatModule_checkAcyclicTrie` (`O(N)` kernel check) and `kissatModule_allWf`.
3. `fullTableImpl`, `full_moduleOk`, `kissatModule_checkAcyclic`, `kissatUnsatPkg`, and
   `full_solve_bytes_sound` (backed by canonical `Proof.Spec.Solver.solveBytesSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Full
open scoped LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.InlPolicy
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec

public section

/-! ## 1. Concatenated `41`-Module Canonical Spec Table & `Env` -/

/-- Exact `41`-module concatenation of canonical `SpecEntry` tables matching
`Src.Full.kissatFns` (`418` functions) 1:1 in topological order. -/
@[expose] def fullSpecs : List SpecEntry :=
  Float64.Spec.specs
  ++ Dimacs.Spec.specs
  ++ Limits.Spec.specs
  ++ Arena.Spec.specs
  ++ Watch.Spec.specs
  ++ Heap.Spec.specs
  ++ Backtrack.Spec.specs
  ++ Clause.Spec.specs
  ++ Tiers.Spec.specs
  ++ Bump.Spec.specs
  ++ Internal.Spec.specs
  ++ PropSearch.Spec.specs
  ++ Parse.Spec.specs
  ++ Collect.Spec.specs
  ++ Compact.Spec.specs
  ++ Reduce.Spec.specs
  ++ Deduce.Spec.specs
  ++ Minimize.Spec.specs
  ++ Learn.Spec.specs
  ++ Analyze.Spec.specs
  ++ Decide.Spec.specs
  ++ Restart.Spec.specs
  ++ Extend.Spec.specs
  ++ Lucky.Spec.specs
  ++ Vivify.Spec.specs
  ++ Backbone.Spec.specs
  ++ Transitive.Spec.specs
  ++ Substitute.Spec.specs
  ++ Dense.Spec.specs
  ++ Congruence.Spec.specs
  ++ Kitten.Spec.specs
  ++ Sweep.Spec.specs
  ++ Forward.Spec.specs
  ++ Gates.specs
  ++ Definition.Spec.specs
  ++ Eliminate.Spec.specs
  ++ Factor.Spec.specs
  ++ Reorder.Spec.specs
  ++ Probe.Spec.specs
  ++ Walk.Spec.specs
  ++ Search.Spec.specs

/-- Canonical flat solver environment (`Env.ofTable fullSpecs`). -/
@[expose] def fullEnv : Env :=
  Env.ofTable fullSpecs

private def fullCerts : List SubsystemCert :=
  [ ⟨Src.Float64.fns, Float64.Spec.specs, [], Float64.Spec.specs_sigs, rfl, Float64.cert⟩
  , ⟨Src.Dimacs.fns, Dimacs.Spec.specs, [], Dimacs.Spec.specs_sigs,
      Dimacs.Spec.specs_noExit, Dimacs.cert⟩
  , ⟨Src.Limits.fns, Limits.Spec.specs, Float64.Spec.specs, Limits.Spec.specs_sigs,
      rfl, Limits.cert⟩
  , ⟨Src.Arena.fns, Arena.Spec.specs, [], Arena.Spec.specs_sigs,
      Arena.Spec.specs_noExit, Arena.cert⟩
  , ⟨Src.Watch.fns, Watch.Spec.specs, [], Watch.Spec.specs_sigs, rfl, Watch.cert⟩
  , ⟨Src.Heap.fns, Heap.Spec.specs, [], Heap.Spec.specs_sigs,
      Heap.Spec.specs_noExit, Heap.cert⟩
  , ⟨Src.Backtrack.fns, Backtrack.Spec.specs, Backtrack.Spec.deps,
      Backtrack.Spec.specs_sigs, Backtrack.Spec.specs_noExit, Backtrack.cert⟩
  , ⟨Src.Clause.fns, Clause.Spec.specs, Clause.Spec.deps, Clause.Spec.specs_sigs,
      Clause.Spec.specs_noExit, Clause.cert⟩
  , ⟨Src.Tiers.fns, Tiers.Spec.specs, Float64.Spec.specs, Tiers.Spec.specs_sigs,
      rfl, Tiers.cert⟩
  , ⟨Src.Bump.fns, Bump.Spec.specs, Bump.Spec.deps, Bump.Spec.specs_sigs,
      List.all_eq_true.mpr Bump.Spec.specs_noExit, Bump.cert⟩
  , ⟨Src.Internal.fns, Internal.Spec.specs, Internal.Spec.deps, Internal.Spec.specs_sigs,
      Internal.Spec.specs_noExit, Internal.cert⟩
  , ⟨Src.PropSearch.fns, PropSearch.Spec.specs, PropSearch.Spec.deps,
      PropSearch.Spec.specs_sigs, PropSearch.Spec.specs_noExit, PropSearch.cert⟩
  , ⟨Src.Parse.fns, Parse.Spec.specs, Parse.Spec.deps, Parse.Spec.specs_sigs,
      List.all_eq_true.mpr Parse.Spec.specs_noExit, Parse.cert⟩
  , ⟨Src.Collect.fns, Collect.Spec.specs, Collect.Spec.deps, Collect.Spec.specs_sigs,
      Collect.Spec.specs_noExit, Collect.cert⟩
  , ⟨Src.Compact.fns, Compact.Spec.specs, Compact.Spec.deps, Compact.Spec.specs_sigs,
      Compact.Spec.specs_noExit, Compact.cert⟩
  , ⟨Src.Reduce.fns, Reduce.Spec.specs, Reduce.Spec.deps, Reduce.Spec.specs_sigs,
      List.all_eq_true.mpr Reduce.Spec.specs_noExit, Reduce.cert⟩
  , ⟨Deduce.fns, Deduce.Spec.specs, Deduce.Spec.deps, Deduce.Spec.specs_sigs,
      Deduce.Spec.specs_noExit, Deduce.cert⟩
  , ⟨Src.Minimize.fns, Minimize.Spec.specs, [], Minimize.Spec.specs_sigs, rfl, Minimize.cert⟩
  , ⟨Src.Learn.fns, Learn.Spec.specs, Learn.Spec.deps, Learn.Spec.specs_sigs,
      Learn.Spec.specs_noExit, Learn.cert⟩
  , ⟨Src.Analyze.fns, Analyze.Spec.specs, Analyze.Spec.deps, Analyze.Spec.specs_sigs,
      Analyze.Spec.specs_noExit, Analyze.cert⟩
  , ⟨Src.Decide.fns, Decide.Spec.specs, Decide.Spec.deps, Decide.Spec.specs_sigs,
      Decide.Spec.specs_noExit, Decide.cert⟩
  , ⟨Src.Restart.fns, Restart.Spec.specs, Restart.deps, Restart.specs_sigs,
      Restart.specs_noExit, Restart.cert⟩
  , ⟨Src.Extend.fns, Extend.Spec.specs, [], Extend.Spec.specs_sigs, rfl, Extend.cert⟩
  , ⟨Src.Lucky.fns, Lucky.Spec.specs, Lucky.deps, Lucky.specs_sigs,
      Lucky.specs_noExit, Lucky.cert⟩
  , ⟨Src.Vivify.fns, Vivify.Spec.specs, Vivify.Spec.deps, Vivify.Spec.specs_sigs,
      Vivify.Spec.specs_noExit, Vivify.cert⟩
  , ⟨Src.Backbone.fns, Backbone.Spec.specs, Backbone.Spec.deps, Backbone.Spec.specs_sigs,
      List.all_eq_true.mpr Backbone.Spec.specs_noExit, Backbone.cert⟩
  , ⟨Src.Transitive.fns, Transitive.Spec.specs, Transitive.Spec.deps,
      Transitive.Spec.specs_sigs, List.all_eq_true.mpr Transitive.Spec.specs_noExit,
      Transitive.cert⟩
  , ⟨Src.Substitute.fns, Substitute.Spec.specs, Substitute.Spec.deps,
      Substitute.Spec.specs_sigs, Substitute.Spec.specs_noExit, Substitute.cert⟩
  , ⟨Src.Dense.fns, Dense.Spec.specs, Dense.Spec.deps, Dense.Spec.specs_sigs,
      Dense.Spec.specs_noExit, Dense.cert⟩
  , ⟨Src.Congruence.fns, Congruence.Spec.specs, Congruence.Spec.deps,
      Congruence.Spec.specs_sigs, List.all_eq_true.mpr Congruence.Spec.specs_noExit,
      Congruence.cert⟩
  , ⟨Src.Kitten.fns, Kitten.Spec.specs, Kitten.Spec.deps, Kitten.Spec.specs_sigs,
      Kitten.Spec.specs_noExit, Kitten.cert⟩
  , ⟨Src.Sweep.fns, Sweep.Spec.specs, Sweep.Spec.deps, Sweep.Spec.specs_sigs,
      Sweep.Spec.specs_noExit, Sweep.cert⟩
  , ⟨Src.Forward.fns, Forward.Spec.specs, Forward.Spec.deps, Forward.Spec.specs_sigs,
      Forward.Spec.specs_noExit, Forward.cert⟩
  , ⟨Gates.fns, Gates.specs, [], Gates.specs_sigs, rfl, Gates.cert⟩
  , ⟨Src.Definition.fns, Definition.Spec.specs, Definition.Spec.deps,
      Definition.Spec.specs_sigs, Definition.Spec.specs_noExit, Definition.cert⟩
  , ⟨Src.Eliminate.fns, Eliminate.Spec.specs, Eliminate.Spec.deps,
      Eliminate.Spec.specs_sigs, Eliminate.Spec.specs_noExit, Eliminate.cert⟩
  , ⟨Src.Factor.fns, Factor.Spec.specs, Factor.Spec.deps, Factor.Spec.specs_sigs,
      Factor.Spec.specs_noExit, Factor.cert⟩
  , ⟨Src.Reorder.fns, Reorder.Spec.specs, Reorder.deps, Reorder.specs_sigs,
      Reorder.specs_noExit, Reorder.cert⟩
  , ⟨Src.Probe.fns, Probe.Spec.specs, Probe.Spec.deps, Probe.Spec.specs_sigs,
      Probe.Spec.specs_noExit, Probe.cert⟩
  , ⟨Src.Walk.fns, Walk.Spec.specs, Walk.deps, Walk.specs_sigs,
      Walk.specs_noExit, Walk.cert⟩
  , ⟨Src.Search.fns, Search.Spec.specs, Search.deps, Search.specs_sigs,
      Search.specs_noExit, Search.cert⟩ ]

private theorem sApp {a b t : List SpecEntry}
    (ha : ∀ e ∈ a, e ∈ t) (hb : ∀ e ∈ b, e ∈ t) : ∀ e ∈ a ++ b, e ∈ t :=
  fun _ h => (List.mem_append.mp h).elim (ha _) (hb _)

local infixl:65 " ⊕ₘ " => sApp

private theorem fullCerts_deps :
    ∀ c ∈ fullCerts, ∀ e ∈ c.deps, e ∈ SubsystemCert.allSpecs fullCerts := by
  let T := SubsystemCert.allSpecs fullCerts
  have memOf : ∀ {c : SubsystemCert}, c ∈ fullCerts → ∀ {e}, e ∈ c.specs → e ∈ T :=
    fun hc _ he => List.mem_flatMap.mpr ⟨_, hc, he⟩
  have h1  : ∀ e ∈ Float64.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 0) (by decide)) he
  have h2  : ∀ e ∈ Dimacs.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 1) (by decide)) he
  have h3  : ∀ e ∈ Limits.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 2) (by decide)) he
  have h4  : ∀ e ∈ Arena.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 3) (by decide)) he
  have h5  : ∀ e ∈ Watch.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 4) (by decide)) he
  have h6  : ∀ e ∈ Heap.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 5) (by decide)) he
  have h7  : ∀ e ∈ Backtrack.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 6) (by decide)) he
  have h8  : ∀ e ∈ Clause.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 7) (by decide)) he
  have h9  : ∀ e ∈ Tiers.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 8) (by decide)) he
  have h10 : ∀ e ∈ Bump.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 9) (by decide)) he
  have h11 : ∀ e ∈ Internal.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 10) (by decide)) he
  have h12 : ∀ e ∈ PropSearch.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 11) (by decide)) he
  have h13 : ∀ e ∈ Parse.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 12) (by decide)) he
  have h14 : ∀ e ∈ Collect.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 13) (by decide)) he
  have h15 : ∀ e ∈ Compact.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 14) (by decide)) he
  have h16 : ∀ e ∈ Reduce.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 15) (by decide)) he
  have h17 : ∀ e ∈ Deduce.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 16) (by decide)) he
  have h18 : ∀ e ∈ Minimize.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 17) (by decide)) he
  have h19 : ∀ e ∈ Learn.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 18) (by decide)) he
  have h20 : ∀ e ∈ Analyze.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 19) (by decide)) he
  have h21 : ∀ e ∈ Decide.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 20) (by decide)) he
  have h22 : ∀ e ∈ Restart.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 21) (by decide)) he
  have h23 : ∀ e ∈ Extend.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 22) (by decide)) he
  have h24 : ∀ e ∈ Lucky.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 23) (by decide)) he
  have h25 : ∀ e ∈ Vivify.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 24) (by decide)) he
  have h26 : ∀ e ∈ Backbone.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 25) (by decide)) he
  have h27 : ∀ e ∈ Transitive.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 26) (by decide)) he
  have h28 : ∀ e ∈ Substitute.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 27) (by decide)) he
  have h29 : ∀ e ∈ Dense.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 28) (by decide)) he
  have h30 : ∀ e ∈ Congruence.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 29) (by decide)) he
  have h31 : ∀ e ∈ Kitten.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 30) (by decide)) he
  have h32 : ∀ e ∈ Sweep.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 31) (by decide)) he
  have h33 : ∀ e ∈ Forward.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 32) (by decide)) he
  have h34 : ∀ e ∈ Gates.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 33) (by decide)) he
  have h35 : ∀ e ∈ Definition.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 34) (by decide)) he
  have h36 : ∀ e ∈ Eliminate.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 35) (by decide)) he
  have h37 : ∀ e ∈ Factor.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 36) (by decide)) he
  have h38 : ∀ e ∈ Reorder.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 37) (by decide)) he
  have h39 : ∀ e ∈ Probe.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 38) (by decide)) he
  have h40 : ∀ e ∈ Walk.Spec.specs, e ∈ T := by
    intro e he; exact memOf (List.getElem_mem (l := fullCerts) (n := 39) (by decide)) he
  have d12 : ∀ e ∈ PropSearch.Spec.deps, e ∈ T := by
    intro e he
    simp only [PropSearch.Spec.deps, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact h5 _ Watch.Spec.mem_full_watch_push
    · exact h1 _ (List.getElem_mem (l := Float64.Spec.specs) (n := 12) (by decide))
    · exact h9 _ (List.getElem_mem (l := Tiers.Spec.specs) (n := 2) (by decide))
    · exact h7 _ (List.getElem_mem (l := Backtrack.Spec.specs) (n := 4) (by decide))
  intro c hc
  simp only [fullCerts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ h => nomatch h
  · exact fun _ h => nomatch h
  · exact h1
  · exact fun _ h => nomatch h
  · exact fun _ h => nomatch h
  · exact fun _ h => nomatch h
  · exact h6
  · exact h4 ⊕ₘ h7 ⊕ₘ h5
  · exact h1
  · exact h1 ⊕ₘ h6 ⊕ₘ h9
  · exact h2 ⊕ₘ h1 ⊕ₘ h6 ⊕ₘ h9
  · exact d12
  · exact h7 ⊕ₘ h8 ⊕ₘ h2 ⊕ₘ h1 ⊕ₘ h6 ⊕ₘ h12 ⊕ₘ h5
  · exact h4 ⊕ₘ h7 ⊕ₘ h5
  · exact h4 ⊕ₘ h14 ⊕ₘ h12 ⊕ₘ h5
  · exact h4 ⊕ₘ h7 ⊕ₘ h1 ⊕ₘ h11 ⊕ₘ h3 ⊕ₘ h9 ⊕ₘ h14 ⊕ₘ h15 ⊕ₘ h12
  · exact h4 ⊕ₘ h9 ⊕ₘ h5
  · exact fun _ h => nomatch h
  · exact h7 ⊕ₘ h8 ⊕ₘ h16 ⊕ₘ h5
  · exact h7 ⊕ₘ h10 ⊕ₘ h17 ⊕ₘ h19 ⊕ₘ h3 ⊕ₘ h18 ⊕ₘ h9
  · exact h7 ⊕ₘ h1 ⊕ₘ h6 ⊕ₘ h3 ⊕ₘ h9
  · exact h7 ⊕ₘ h21 ⊕ₘ h1 ⊕ₘ h6 ⊕ₘ h3 ⊕ₘ h9
  · exact fun _ h => nomatch h
  · exact h4 ⊕ₘ h7 ⊕ₘ h12 ⊕ₘ h20
  · exact h4 ⊕ₘ h7 ⊕ₘ h8 ⊕ₘ h12 ⊕ₘ h9 ⊕ₘ h5
  · exact h7 ⊕ₘ h8 ⊕ₘ h1 ⊕ₘ h12 ⊕ₘ h5
  · exact h7 ⊕ₘ h8 ⊕ₘ h12 ⊕ₘ h5
  · exact h4 ⊕ₘ h7 ⊕ₘ h8 ⊕ₘ h14 ⊕ₘ h23 ⊕ₘ h11 ⊕ₘ h12
  · exact h4 ⊕ₘ h7 ⊕ₘ h8 ⊕ₘ h14 ⊕ₘ h12 ⊕ₘ h5
  · exact h4 ⊕ₘ h8 ⊕ₘ h3 ⊕ₘ h5
  · exact fun _ h => nomatch h
  · exact h31 ⊕ₘ h8 ⊕ₘ h30 ⊕ₘ h5 ⊕ₘ h29
  · exact h4 ⊕ₘ h5 ⊕ₘ h8 ⊕ₘ h14 ⊕ₘ h29
  · exact fun _ h => nomatch h
  · exact h7 ⊕ₘ h34 ⊕ₘ h31
  · exact h4 ⊕ₘ h7 ⊕ₘ h8 ⊕ₘ h35 ⊕ₘ h29 ⊕ₘ h23 ⊕ₘ h1 ⊕ₘ h33 ⊕ₘ h11 ⊕ₘ h3 ⊕ₘ h5
  · exact h4 ⊕ₘ h8 ⊕ₘ h33 ⊕ₘ h11 ⊕ₘ h3 ⊕ₘ h5
  · exact h1 ⊕ₘ h4 ⊕ₘ h10 ⊕ₘ h6
  · exact h9 ⊕ₘ h11 ⊕ₘ h29 ⊕ₘ h30 ⊕ₘ h33 ⊕ₘ h28 ⊕ₘ h26 ⊕ₘ h32 ⊕ₘ h37 ⊕ₘ h25 ⊕ₘ
      h27 ⊕ₘ h1 ⊕ₘ h3
  · exact h4 ⊕ₘ h7 ⊕ₘ h21 ⊕ₘ h29 ⊕ₘ h1 ⊕ₘ h33 ⊕ₘ h12
  · simp only [Search.deps, Search.searchDeps]
    exact h11 ⊕ₘ h3 ⊕ₘ h23 ⊕ₘ h14 ⊕ₘ h9 ⊕ₘ h21 ⊕ₘ h22 ⊕ₘ h38 ⊕ₘ h40 ⊕ₘ h15 ⊕ₘ
      h7 ⊕ₘ h16 ⊕ₘ h20 ⊕ₘ h13 ⊕ₘ h2 ⊕ₘ h39 ⊕ₘ h24 ⊕ₘ h36 ⊕ₘ h12

private def fullFold : SubsystemCert :=
  SubsystemCert.fold fullCerts fullCerts_deps

private theorem allSpecs_eq : SubsystemCert.allSpecs fullCerts = fullSpecs := by
  simp only [fullCerts, fullSpecs, SubsystemCert.allSpecs,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

private theorem allFns_eq : SubsystemCert.allFns fullCerts = kissatModule.fns := by
  rw [kissatModule_fns]
  simp only [fullCerts, kissatFns, SubsystemCert.allFns,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Signature list of `fullSpecs` matches `Src.Full.kissatModule.fns` (`418` fns) 1:1. -/
theorem fullSpecs_sigs : fullSpecs.map SpecEntry.sig = kissatModule.fns.map Fn.sig := by
  rw [← allSpecs_eq, ← allFns_eq]
  exact fullFold.specs_sigs

/-- Name list of `fullSpecs` matches `Src.Full.kissatModule.fns` 1:1. -/
theorem fullSpecs_names : fullSpecs.map SpecEntry.name = kissatModule.fns.map Fn.name :=
  names_eq_of_sigs_eq fullSpecs_sigs

/-- `O(N)` byte-trie acyclicity and `namesNodup` verification of `Src.Full.kissatModule`. -/
theorem kissatModule_checkAcyclicTrie : kissatModule.checkAcyclicTrie = true := by
  kissat_kernel_rfl

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (by simp), allFns_of_forall (fun _ hf => h _ (by simp [hf]))⟩

/-- All `418` functions in `Src.Full.kissatModule` are PHOAS well-formed (`AllFns Fn.Wf`). -/
theorem kissatModule_allWf : AllFns Fn.Wf kissatModule.fns :=
  allFns_of_forall kissatModule_wf

/-- All `418` specification names in `fullSpecs` are distinct. -/
theorem fullSpecs_nodup : (fullSpecs.map SpecEntry.name).Nodup :=
  nodup_of_checkAcyclicTrie kissatModule_checkAcyclicTrie fullSpecs_names

/-- Every row in `fullSpecs` has `noExit = true`. -/
theorem fullSpecs_noExit : ∀ e ∈ fullSpecs, e.noExit = true := by
  rw [← allSpecs_eq]
  exact fullFold.noExit_mem

/-- `fullEnv` ignores exit continuations across all `418` functions. -/
theorem fullEnv_noExit :
    ∀ f ∈ kissatModule.fns, ∀ args m Q X X',
      fullEnv f.name f.as f.rs args m Q X → fullEnv f.name f.as f.rs args m Q X' :=
  fun f _ args m Q X X' h =>
    Env.ofTable_noExit fullSpecs_noExit f.name f.as f.rs args m Q X X' h

/-! ## 2. Full `41`-Segment `SubsystemCert` Fold & `ModuleOk` -/

/-- Combined `TableImpl` across all `41` `Src.*` modules (`418` functions). -/
theorem fullTableImpl (Γ : Env) (hSat : Γ.Sat fullSpecs) :
    TableImpl Γ kissatModule.fns fullSpecs := by
  rw [← allSpecs_eq] at hSat ⊢
  rw [← allFns_eq]
  exact fullFold.cert Γ (Env.Sat.nil Γ) hSat

/-- Full `ModuleOk fullEnv Src.Full.kissatModule` (`418` functions). -/
theorem full_moduleOk : ModuleOk fullEnv kissatModule :=
  ModuleOk.ofCanonicalTrie kissatModule_checkAcyclicTrie kissatModule_allWf fullSpecs_names
    fullTableImpl

/-- `O(1)` reconstruction of `kissatModule.checkAcyclic = true` from `ModuleOk`. -/
theorem kissatModule_checkAcyclic : kissatModule.checkAcyclic = true :=
  moduleCheckAcyclic_of_moduleOk full_moduleOk

/-! ## 3. Top-Level `KissatUnsatPkg` & Arch-Free Soundness Export -/

/-- Canonical `Fn` entry for `"kissat_solve_bytes"` in `Src.Search.fns`. -/
@[expose] def fullSolveBytesFn : Fn :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], Src.Search.kissat_solve_bytes_body⟩

/-- Membership of `fullSolveBytesFn` in `Src.Full.kissatModule.fns`. -/
theorem fullSolveBytesFn_mem : fullSolveBytesFn ∈ kissatModule.fns := by
  have hSearch : fullSolveBytesFn ∈ Src.Search.fns :=
    List.mem_of_getElem? (rfl : Src.Search.fns[4]? = some fullSolveBytesFn)
  rw [kissatModule_fns]
  unfold kissatFns
  exact List.mem_append_right _ hSearch

/-- `fullEnv` satisfies `Solver.solveBytesSpec` at `"kissat_solve_bytes"`. -/
theorem fullEnv_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : Solver.solveBytesSpec a m Q X) :
    fullEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  have hSat : fullEnv.Sat Search.Spec.specs := by
    refine Env.Sat.ofTable fullSpecs_nodup (fun e he => ?_)
    unfold fullSpecs
    exact List.mem_append_right _ he
  have hX : Solver.solveBytesSpec.XFree := by
    unfold Solver.solveBytesSpec
    exact FnContract.toSpec_xfree _
  exact SpecTable.has_at hSat 4 rfl hX a m Q X h

/-- Canonical `KissatUnsatPkg` for the entire `418`-function `Src.Full.kissatModule`. -/
@[expose] def kissatUnsatPkg : KissatUnsatPkg where
  mod := kissatModule
  inlPolicy := kissatInlPolicy
  entryFn := "kissat_solve_bytes"
  entryFn_fn := fullSolveBytesFn
  entryFn_sig := ⟨rfl, rfl, rfl⟩
  entry_mem := fullSolveBytesFn_mem
  env := fullEnv
  moduleOk := full_moduleOk
  noExit := fullEnv_noExit
  solve_intro := fun hcfit hwfit hm hreq => by
    refine fullEnv_solve_bytes_of ?_
    unfold Solver.solveBytesSpec
    refine FnContract.intro (_, _) _ ⟨rfl, rfl, hcfit, hwfit⟩ hm ?_
    rintro ⟨r, ⟨⟩⟩ ⟨⟩ m' ⟨hdom, h20, htr⟩ hm'
    exact hreq r m' hdom h20
      (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => htr ⟨mv, nc, i0, h1, h2, h3, h4, h5, h6, h7⟩) hm'

/-- Arch-free WP byte-level UNSAT soundness for `kissat_solve_bytes` in `Src.Full.kissatModule`. -/
theorem full_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fullEnv Src.Search.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of_fn full_moduleOk fullSolveBytesFn_mem
    (fun _ _ _ _ h => fullEnv_solve_bytes_of h) hcfit hwfit hm

end

end LeanQbe.T.Examples.Kissat.Proof.Full
