/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpAct
public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpBody
public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpFinish
public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpIngest
public import LeanQbe.T.Examples.Kissat.Src.Parse

/-!
# DIMACS Parsing & Tumble Ingestion Certificate (`Proof.Parse.Cert`)

Bundles the flat `SegCert` for `Src.Parse.fns` against `Proof.Parse.Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open LeanQbe.T

theorem cert : SegCert Spec.deps Src.Parse.fns Spec.specs := by
  intro Γ hdeps hrows
  have hBtS : Γ.Sat Backtrack.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hClS : Γ.Sat Clause.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hDmS : Γ.Sat Dimacs.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hF64S : Γ.Sat Float64.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hHpS : Γ.Sat Heap.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hPrS : Γ.Sat PropSearch.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hWaS : Γ.Sat Watch.Spec.specs := fun e he => hdeps e (by simp [Spec.deps, he])
  have hInv : Γ.Has "f64u_inv_u64" Float64.Spec.f64uPure1Spec :=
    hF64S.has (e := ⟨"f64u_inv_u64", [i64], [i64], Float64.Spec.f64uPure1Spec, true⟩)
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure1Spec_xfree
  have hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec :=
    hF64S.has (e := ⟨"f64u_sub", [i64, i64], [i64], Float64.Spec.f64uPure2Spec, true⟩)
      (by simp [Float64.Spec.specs]) Float64.Spec.f64uPure2Spec_xfree
  have hPush := Heap.Spec.has_full_heap_push hHpS
  have hNextLit := Dimacs.Spec.has_kissat_next_lit hDmS
  have hAssign := Backtrack.Spec.has_full_assign_lvl hBtS
  have hAddCl := Clause.Spec.has_full_add_clause hClS
  have hSkip := Dimacs.Spec.has_full_skip_cl hDmS
  have hSwc := Dimacs.Spec.has_kissat_skip_ws_comments hDmS
  have hProp := PropSearch.Spec.has_full_propagate hPrS
  have hDefrag := Watch.Spec.has_full_wstack_defrag hWaS
  have hAct := Spec.has_full_activate_lit_fid hrows
  have hIngest := Spec.has_full_ingest_cl hrows
  have hFinish := Spec.has_full_tumble_finish_fid hrows
  have hBodyM6 := Spec.has_full_parse_body_m6 hrows
  refine ⟨⟨⟨rfl, rfl, rfl⟩, full_activate_lit_fid_wp Γ hInv hSub hPush⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_ingest_cl_wp Γ hNextLit hAct hAssign hAddCl⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_tumble_finish_fid_wp Γ⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_parse_body_m6_wp Γ hSkip hIngest hProp hSwc hFinish hDefrag⟩,
    ⟨⟨rfl, rfl, rfl⟩, full_parse_body_wp Γ hBodyM6⟩, trivial⟩

end LeanQbe.T.Examples.Kissat.Proof.Parse
