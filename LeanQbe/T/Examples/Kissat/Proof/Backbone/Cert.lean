/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.WpSimple
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.WpPropAnalyze
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.WpRound
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.WpTop
public import LeanQbe.T.Examples.Kissat.Src.Backbone
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Segment Certificate for `Kissat.Src.Backbone` (`Proof.Backbone.Cert`)

Establishes `SegCert Spec.deps Src.Backbone.fns Spec.specs` using `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Backbone

/-- Canonical segment certificate for `Kissat.Src.Backbone` (`7` functions, `deps = Spec.deps`). -/
theorem cert : SegCert Spec.deps Src.Backbone.fns Spec.specs := fun Γ hDeps hSat => by
  have hBtSat := hDeps.left.left.left.left
  have hClSat := hDeps.left.left.left.right
  have hF64Sat := hDeps.left.left.right
  have hPsSat := hDeps.left.right
  have hWtSat := hDeps.right
  have hBacktrack := Backtrack.Spec.has_full_backtrack hBtSat
  have hAddUnit := Clause.Spec.has_full_add_unit hClSat
  have hWm4Get := Float64.Spec.has_m6Wm4Get_to_w2a
    (Env.Sat.has hF64Sat (List.getElem_mem (l := Float64.Spec.specs) (n := 12) (by decide))
      Float64.Spec.m6Wm4GetSpec_xfree)
  have hWm4Set := Env.Sat.has hF64Sat
    (List.getElem_mem (l := Float64.Spec.specs) (n := 13) (by decide))
    Float64.Spec.m6Wm4SetSpec_xfree
  have hPropagate := PropSearch.Spec.has_full_propagate hPsSat
  have hPrio := Watch.Spec.has_full_prioritize_binaries_m6 hWtSat
  have hSched := Spec.has_full_backbone_sched_m6 hSat
  have hKeep := Spec.has_full_backbone_keep_m6 hSat
  have hUnwind := Spec.has_full_backbone_unwind_m6 hSat
  have hProp := Spec.has_full_backbone_prop_m6 hSat
  have hAnalyze := Spec.has_full_backbone_analyze_m6 hSat
  have hRound := Spec.has_full_backbone_round_m6 hSat
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_backbone_sched_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_keep_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_unwind_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_prop_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_analyze_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_round_m6_wp Γ hProp hAnalyze hUnwind⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_backbone_m6_wp Γ hBacktrack hPropagate hAddUnit hPrio hSched hRound
      hKeep hWm4Get hWm4Set⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Backbone
