/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.Src.InlPolicy
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
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

Assembles all `41` `Src.*` modules (`418` functions) on flat `CanonicalEnv` with `0` legacy `Full*`
imports, `0` `PatchModule` layers, and `O(N)` `checkAcyclicTrie` verification:
1. `fullSpecs`, `fullEnv`, `fullSpecs_sigs`, `fullSpecs_nodup`, `fullSpecs_noExit`.
2. `kissatModule_checkAcyclicTrie` (`O(N)` kernel check) and `kissatModule_allWf`.
3. `fullTableImpl`, `full_moduleOk`, `kissatModule_checkAcyclic`, `kissatUnsatPkg`, and
   `full_solve_bytes_sound`.
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

private theorem sigs_append {r₁ r₂ : List SpecEntry} {f₁ f₂ : List Fn}
    (h₁ : r₁.map SpecEntry.sig = f₁.map Fn.sig)
    (h₂ : r₂.map SpecEntry.sig = f₂.map Fn.sig) :
    (r₁ ++ r₂).map SpecEntry.sig = (f₁ ++ f₂).map Fn.sig := by
  simp only [List.map_append, h₁, h₂]

/-- Signature list of `fullSpecs` matches `Src.Full.kissatModule.fns` (`418` fns) 1:1. -/
theorem fullSpecs_sigs : fullSpecs.map SpecEntry.sig = kissatModule.fns.map Fn.sig := by
  unfold fullSpecs
  rw [kissatModule_fns]
  unfold kissatFns
  have h := Float64.Spec.specs_sigs
  have h := sigs_append h Dimacs.Spec.specs_sigs
  have h := sigs_append h Limits.Spec.specs_sigs
  have h := sigs_append h Arena.Spec.specs_sigs
  have h := sigs_append h Watch.Spec.specs_sigs
  have h := sigs_append h Heap.Spec.specs_sigs
  have h := sigs_append h Backtrack.Spec.specs_sigs
  have h := sigs_append h Clause.Spec.specs_sigs
  have h := sigs_append h Tiers.Spec.specs_sigs
  have h := sigs_append h Bump.Spec.specs_sigs
  have h := sigs_append h Internal.Spec.specs_sigs
  have h := sigs_append h PropSearch.Spec.specs_sigs
  have h := sigs_append h Parse.Spec.specs_sigs
  have h := sigs_append h Collect.Spec.specs_sigs
  have h := sigs_append h Compact.Spec.specs_sigs
  have h := sigs_append h Reduce.Spec.specs_sigs
  have h := sigs_append h Deduce.Spec.specs_sigs
  have h := sigs_append h Minimize.Spec.specs_sigs
  have h := sigs_append h Learn.Spec.specs_sigs
  have h := sigs_append h Analyze.Spec.specs_sigs
  have h := sigs_append h Decide.Spec.specs_sigs
  have h := sigs_append h Restart.Spec.specs_sigs
  have h := sigs_append h Extend.Spec.specs_sigs
  have h := sigs_append h Lucky.Spec.specs_sigs
  have h := sigs_append h Vivify.Spec.specs_sigs
  have h := sigs_append h Backbone.Spec.specs_sigs
  have h := sigs_append h Transitive.Spec.specs_sigs
  have h := sigs_append h Substitute.Spec.specs_sigs
  have h := sigs_append h Dense.Spec.specs_sigs
  have h := sigs_append h Congruence.Spec.specs_sigs
  have h := sigs_append h Kitten.Spec.specs_sigs
  have h := sigs_append h Sweep.Spec.specs_sigs
  have h := sigs_append h Forward.Spec.specs_sigs
  have h := sigs_append h Gates.specs_sigs
  have h := sigs_append h Definition.Spec.specs_sigs
  have h := sigs_append h Eliminate.Spec.specs_sigs
  have h := sigs_append h Factor.Spec.specs_sigs
  have h := sigs_append h Reorder.Spec.specs_sigs
  have h := sigs_append h Probe.Spec.specs_sigs
  have h := sigs_append h Walk.Spec.specs_sigs
  exact sigs_append h Search.Spec.specs_sigs

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

private theorem noExit_append {r₁ r₂ : List SpecEntry}
    (h₁ : ∀ e ∈ r₁, e.noExit = true) (h₂ : ∀ e ∈ r₂, e.noExit = true) :
    ∀ e ∈ r₁ ++ r₂, e.noExit = true := fun e he =>
  (List.mem_append.mp he).elim (h₁ e) (h₂ e)

private theorem noExit_of_all {tbl : List SpecEntry} (h : tbl.all SpecEntry.noExit = true) :
    ∀ e ∈ tbl, e.noExit = true :=
  fun e he => List.all_eq_true.mp h e he

/-- Every row in `fullSpecs` has `noExit = true`. -/
theorem fullSpecs_noExit : ∀ e ∈ fullSpecs, e.noExit = true := by
  unfold fullSpecs
  have h := noExit_of_all (rfl : Float64.Spec.specs.all SpecEntry.noExit = true)
  have h := noExit_append h (noExit_of_all Dimacs.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Limits.Spec.specs.all SpecEntry.noExit = true))
  have h := noExit_append h (noExit_of_all Arena.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Watch.Spec.specs.all SpecEntry.noExit = true))
  have h := noExit_append h (noExit_of_all Heap.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Backtrack.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Clause.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Tiers.Spec.specs.all SpecEntry.noExit = true))
  have h := noExit_append h Bump.Spec.specs_noExit
  have h := noExit_append h (noExit_of_all Internal.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all PropSearch.Spec.specs_noExit)
  have h := noExit_append h Parse.Spec.specs_noExit
  have h := noExit_append h (noExit_of_all Collect.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Compact.Spec.specs_noExit)
  have h := noExit_append h Reduce.Spec.specs_noExit
  have h := noExit_append h (noExit_of_all Deduce.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Minimize.Spec.specs.all SpecEntry.noExit = true))
  have h := noExit_append h (noExit_of_all Learn.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Analyze.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Decide.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Restart.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Extend.Spec.specs.all SpecEntry.noExit = true))
  have h := noExit_append h (noExit_of_all Lucky.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Vivify.Spec.specs_noExit)
  have h := noExit_append h Backbone.Spec.specs_noExit
  have h := noExit_append h Transitive.Spec.specs_noExit
  have h := noExit_append h (noExit_of_all Substitute.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Dense.Spec.specs_noExit)
  have h := noExit_append h Congruence.Spec.specs_noExit
  have h := noExit_append h (noExit_of_all Kitten.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Sweep.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Forward.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all (rfl : Gates.specs.all SpecEntry.noExit = true))
  have h := noExit_append h (noExit_of_all Definition.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Eliminate.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Factor.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Reorder.Spec.specs_noExit)
  have h := noExit_append h (noExit_of_all Probe.Spec.specs_noExit)
  have h := noExit_append h Walk.Spec.specs_noExit
  exact noExit_append h (noExit_of_all Search.Spec.specs_noExit)

/-- `fullEnv` ignores exit continuations across all `418` functions. -/
theorem fullEnv_noExit :
    ∀ f ∈ kissatModule.fns, ∀ args m Q X X',
      fullEnv f.name f.as f.rs args m Q X → fullEnv f.name f.as f.rs args m Q X' :=
  fun f _ args m Q X X' h =>
    Env.ofTable_noExit fullSpecs_noExit f.name f.as f.rs args m Q X X' h

/-! ## 2. Full `41`-Segment `SegCert` Chain & `ModuleOk` -/

/-- Combined `TableImpl` across all `41` `Src.*` modules (`418` functions). -/
theorem fullTableImpl (Γ : Env) (hSat : Γ.Sat fullSpecs) :
    TableImpl Γ kissatModule.fns fullSpecs := by
  unfold fullSpecs at hSat ⊢
  rw [kissatModule_fns]
  unfold kissatFns
  have r40 := hSat.left; have s41 := hSat.right
  have r39 := r40.left;  have s40 := r40.right
  have r38 := r39.left;  have s39 := r39.right
  have r37 := r38.left;  have s38 := r38.right
  have r36 := r37.left;  have s37 := r37.right
  have r35 := r36.left;  have s36 := r36.right
  have r34 := r35.left;  have s35 := r35.right
  have r33 := r34.left;  have s34 := r34.right
  have r32 := r33.left;  have s33 := r33.right
  have r31 := r32.left;  have s32 := r32.right
  have r30 := r31.left;  have s31 := r31.right
  have r29 := r30.left;  have s30 := r30.right
  have r28 := r29.left;  have s29 := r29.right
  have r27 := r28.left;  have s28 := r28.right
  have r26 := r27.left;  have s27 := r27.right
  have r25 := r26.left;  have s26 := r26.right
  have r24 := r25.left;  have s25 := r25.right
  have r23 := r24.left;  have s24 := r24.right
  have r22 := r23.left;  have s23 := r23.right
  have r21 := r22.left;  have s22 := r22.right
  have r20 := r21.left;  have s21 := r21.right
  have r19 := r20.left;  have s20 := r20.right
  have r18 := r19.left;  have s19 := r19.right
  have r17 := r18.left;  have s18 := r18.right
  have r16 := r17.left;  have s17 := r17.right
  have r15 := r16.left;  have s16 := r16.right
  have r14 := r15.left;  have s15 := r15.right
  have r13 := r14.left;  have s14 := r14.right
  have r12 := r13.left;  have s13 := r13.right
  have r11 := r12.left;  have s12 := r12.right
  have r10 := r11.left;  have s11 := r11.right
  have r9  := r10.left;  have s10 := r10.right
  have r8  := r9.left;   have s9  := r9.right
  have r7  := r8.left;   have s8  := r8.right
  have r6  := r7.left;   have s7  := r7.right
  have r5  := r6.left;   have s6  := r6.right
  have r4  := r5.left;   have s5  := r5.right
  have r3  := r4.left;   have s4  := r4.right
  have r2  := r3.left;   have s3  := r3.right
  have s1  := r2.left;   have s2  := r2.right
  have d12 : Γ.Sat PropSearch.Spec.deps := by
    intro e he
    simp only [PropSearch.Spec.deps, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact s5 _ Watch.Spec.mem_full_watch_push
    · exact s1 _ (List.getElem_mem (l := Float64.Spec.specs) (n := 12) (by decide))
    · exact s9 _ (List.getElem_mem (l := Tiers.Spec.specs) (n := 2) (by decide))
    · exact s7 _ (List.getElem_mem (l := Backtrack.Spec.specs) (n := 4) (by decide))
  have t1  := Float64.cert Γ (Env.Sat.nil Γ) s1
  have t2  := Dimacs.cert Γ (Env.Sat.nil Γ) s2
  have t3  := Limits.cert Γ s1 s3
  have t4  := Arena.cert Γ (Env.Sat.nil Γ) s4
  have t5  := Watch.cert Γ (Env.Sat.nil Γ) s5
  have t6  := Heap.cert Γ (Env.Sat.nil Γ) s6
  have t7  := Backtrack.cert Γ s6 s7
  have t8  := Clause.cert Γ (s4.append (s7.append s5)) s8
  have t9  := Tiers.cert Γ s1 s9
  have t10 := Bump.cert Γ (s1.append (s6.append s9)) s10
  have t11 := Internal.cert Γ (s2.append (s1.append (s6.append s9))) s11
  have t12 := PropSearch.cert Γ d12 s12
  have t13 := Parse.cert Γ
    (s7.append (s8.append (s2.append (s1.append (s6.append (s12.append s5)))))) s13
  have t14 := Collect.cert Γ (s4.append (s7.append s5)) s14
  have t15 := Compact.cert Γ (s4.append (s14.append (s12.append s5))) s15
  have t16 := Reduce.cert Γ
    (s4.append (s7.append (s1.append (s11.append (s3.append (s9.append
      (s14.append (s15.append s12)))))))) s16
  have t17 := Deduce.cert Γ (s4.append (s9.append s5)) s17
  have t18 := Minimize.cert Γ (Env.Sat.nil Γ) s18
  have t19 := Learn.cert Γ (s7.append (s8.append (s16.append s5))) s19
  have t20 := Analyze.cert Γ
    (s7.append (s10.append (s17.append (s19.append (s3.append (s18.append s9)))))) s20
  have t21 := Decide.cert Γ (s7.append (s1.append (s6.append (s3.append s9)))) s21
  have t22 := Restart.cert Γ (s7.append (s21.append (s1.append (s6.append (s3.append s9))))) s22
  have t23 := Extend.cert Γ (Env.Sat.nil Γ) s23
  have t24 := Lucky.cert Γ (s4.append (s7.append (s12.append s20))) s24
  have t25 := Vivify.cert Γ (s4.append (s7.append (s8.append (s12.append (s9.append s5))))) s25
  have t26 := Backbone.cert Γ (s7.append (s8.append (s1.append (s12.append s5)))) s26
  have t27 := Transitive.cert Γ (s7.append (s8.append (s12.append s5))) s27
  have t28 := Substitute.cert Γ
    (s4.append (s7.append (s8.append (s14.append (s23.append (s11.append s12)))))) s28
  have t29 := Dense.cert Γ
    (s4.append (s7.append (s8.append (s14.append (s12.append s5))))) s29
  have t30 := Congruence.cert Γ (s4.append (s8.append (s3.append s5))) s30
  have t31 := Kitten.cert Γ (Env.Sat.nil Γ) s31
  have t32 := Sweep.cert Γ (s31.append (s8.append (s30.append (s5.append s29)))) s32
  have t33 := Forward.cert Γ (s4.append (s5.append (s8.append (s14.append s29)))) s33
  have t34 := Gates.cert Γ (Env.Sat.nil Γ) s34
  have t35 := Definition.cert Γ (s7.append (s34.append s31)) s35
  have t36 := Eliminate.cert Γ
    (s4.append (s7.append (s8.append (s35.append (s29.append (s23.append
      (s1.append (s33.append (s11.append (s3.append s5)))))))))) s36
  have t37 := Factor.cert Γ
    (s4.append (s8.append (s33.append (s11.append (s3.append s5))))) s37
  have t38 := Reorder.cert Γ (s1.append (s4.append (s10.append s6))) s38
  have t39 := Probe.cert Γ
    (s9.append (s11.append (s29.append (s30.append (s33.append (s28.append
      (s26.append (s32.append (s37.append (s25.append (s27.append (s1.append s3)))))))))))) s39
  have t40 := Walk.cert Γ
    (s4.append (s7.append (s21.append (s29.append (s1.append (s33.append s12)))))) s40
  have t41 := Search.cert Γ
    (s11.append (s3.append (s23.append (s14.append (s9.append (s21.append (s22.append
      (s38.append (s40.append (s15.append (s7.append (s16.append (s20.append (s13.append
        (s2.append (s39.append (s24.append (s36.append s12)))))))))))))))))) s41
  have hs  := Float64.Spec.specs_sigs
  have acc := t1.append_sigs hs t2
  have hs  := sigs_append hs Dimacs.Spec.specs_sigs
  have acc := acc.append_sigs hs t3
  have hs  := sigs_append hs Limits.Spec.specs_sigs
  have acc := acc.append_sigs hs t4
  have hs  := sigs_append hs Arena.Spec.specs_sigs
  have acc := acc.append_sigs hs t5
  have hs  := sigs_append hs Watch.Spec.specs_sigs
  have acc := acc.append_sigs hs t6
  have hs  := sigs_append hs Heap.Spec.specs_sigs
  have acc := acc.append_sigs hs t7
  have hs  := sigs_append hs Backtrack.Spec.specs_sigs
  have acc := acc.append_sigs hs t8
  have hs  := sigs_append hs Clause.Spec.specs_sigs
  have acc := acc.append_sigs hs t9
  have hs  := sigs_append hs Tiers.Spec.specs_sigs
  have acc := acc.append_sigs hs t10
  have hs  := sigs_append hs Bump.Spec.specs_sigs
  have acc := acc.append_sigs hs t11
  have hs  := sigs_append hs Internal.Spec.specs_sigs
  have acc := acc.append_sigs hs t12
  have hs  := sigs_append hs PropSearch.Spec.specs_sigs
  have acc := acc.append_sigs hs t13
  have hs  := sigs_append hs Parse.Spec.specs_sigs
  have acc := acc.append_sigs hs t14
  have hs  := sigs_append hs Collect.Spec.specs_sigs
  have acc := acc.append_sigs hs t15
  have hs  := sigs_append hs Compact.Spec.specs_sigs
  have acc := acc.append_sigs hs t16
  have hs  := sigs_append hs Reduce.Spec.specs_sigs
  have acc := acc.append_sigs hs t17
  have hs  := sigs_append hs Deduce.Spec.specs_sigs
  have acc := acc.append_sigs hs t18
  have hs  := sigs_append hs Minimize.Spec.specs_sigs
  have acc := acc.append_sigs hs t19
  have hs  := sigs_append hs Learn.Spec.specs_sigs
  have acc := acc.append_sigs hs t20
  have hs  := sigs_append hs Analyze.Spec.specs_sigs
  have acc := acc.append_sigs hs t21
  have hs  := sigs_append hs Decide.Spec.specs_sigs
  have acc := acc.append_sigs hs t22
  have hs  := sigs_append hs Restart.Spec.specs_sigs
  have acc := acc.append_sigs hs t23
  have hs  := sigs_append hs Extend.Spec.specs_sigs
  have acc := acc.append_sigs hs t24
  have hs  := sigs_append hs Lucky.Spec.specs_sigs
  have acc := acc.append_sigs hs t25
  have hs  := sigs_append hs Vivify.Spec.specs_sigs
  have acc := acc.append_sigs hs t26
  have hs  := sigs_append hs Backbone.Spec.specs_sigs
  have acc := acc.append_sigs hs t27
  have hs  := sigs_append hs Transitive.Spec.specs_sigs
  have acc := acc.append_sigs hs t28
  have hs  := sigs_append hs Substitute.Spec.specs_sigs
  have acc := acc.append_sigs hs t29
  have hs  := sigs_append hs Dense.Spec.specs_sigs
  have acc := acc.append_sigs hs t30
  have hs  := sigs_append hs Congruence.Spec.specs_sigs
  have acc := acc.append_sigs hs t31
  have hs  := sigs_append hs Kitten.Spec.specs_sigs
  have acc := acc.append_sigs hs t32
  have hs  := sigs_append hs Sweep.Spec.specs_sigs
  have acc := acc.append_sigs hs t33
  have hs  := sigs_append hs Forward.Spec.specs_sigs
  have acc := acc.append_sigs hs t34
  have hs  := sigs_append hs Gates.specs_sigs
  have acc := acc.append_sigs hs t35
  have hs  := sigs_append hs Definition.Spec.specs_sigs
  have acc := acc.append_sigs hs t36
  have hs  := sigs_append hs Eliminate.Spec.specs_sigs
  have acc := acc.append_sigs hs t37
  have hs  := sigs_append hs Factor.Spec.specs_sigs
  have acc := acc.append_sigs hs t38
  have hs  := sigs_append hs Reorder.Spec.specs_sigs
  have acc := acc.append_sigs hs t39
  have hs  := sigs_append hs Probe.Spec.specs_sigs
  have acc := acc.append_sigs hs t40
  have hs  := sigs_append hs Walk.Spec.specs_sigs
  exact acc.append_sigs hs t41

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

/-- `fullEnv` satisfies `m7FidSolveBytesSpec` at `"kissat_solve_bytes"`. -/
theorem fullEnv_solve_bytes_of {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : m7FidSolveBytesSpec a m Q X) :
    fullEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  have hSat : fullEnv.Sat Search.Spec.specs := by
    refine Env.Sat.ofTable fullSpecs_nodup (fun e he => ?_)
    unfold fullSpecs
    exact List.mem_append_right _ he
  exact Search.Spec.has_kissat_solve_bytes hSat a m Q X (m7FidSolveBytesSpec_to_coreModel h)

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
  solve_intro := fun hcfit hwfit hm hreq =>
    fullEnv_solve_bytes_of (m7FidSolveBytesSpec_intro hcfit hwfit hm hreq)

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
