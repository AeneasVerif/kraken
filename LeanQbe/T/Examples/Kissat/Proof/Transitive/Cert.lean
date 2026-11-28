/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpSort
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpLit
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpTop
public import LeanQbe.T.Examples.Kissat.Src.Transitive

/-!
# Transitive Reduction Certificate (`Proof.Transitive.Cert`)

Bundles the flat `SegCert` for `Src.Transitive.fns` against `Proof.Transitive.Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open LeanQbe.T

theorem cert : SegCert Spec.deps Src.Transitive.fns Spec.specs := by
  intro Γ hdeps hrows
  have hBtS : Γ.Sat Backtrack.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hClS : Γ.Sat Clause.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hPrS : Γ.Sat PropSearch.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hWaS : Γ.Sat Watch.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hDel := Watch.Spec.has_full_delete_bin_side hWaS
  have hAu := Clause.Spec.has_full_add_unit hClS
  have hBt := Backtrack.Spec.has_full_backtrack hBtS
  have hPri := Watch.Spec.has_full_prioritize_binaries_m6 hWaS
  have hProp := PropSearch.Spec.has_full_propagate hPrS
  have hDefrag := Watch.Spec.has_full_wstack_defrag hWaS
  have hLit := Spec.has_full_trans_lit_m6 hrows
  have hSort := Spec.has_full_trans_sort_m6 hrows
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_trans_lit_m6_wp Γ hDel hAu⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_trans_sort_m6_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_transitive_m6_wp Γ hBt hPri hSort hLit hProp hDefrag⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Transitive
