/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Dimacs
public import LeanQbe.T.Examples.Kissat.Ref.Base
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Base

/-!
# Soundness Proofs for `Dimacs`

Extracted pure-Lean proofs for `Dimacs` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 2. Semantic entailment bridges on top of `Ref.Base` -/

theorem entails_of_mem_or_false {F0 : CNF Nat} {c1 c2 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (hsub : ∀ l ∈ c1, l ∈ c2 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c2) := by
  rw [CNF.entails_clause_def] at h1 ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c1).mp (h1 α hα)
  rcases hsub l hl with hin | hfalse
  · exact (clause_sat_cnfClause_iff α c2).mpr ⟨l, hin, hsat⟩
  · have hneg := CNF.entails_clause_def.mp hfalse α hα
    exact absurd ((sat_cnfClause_singleton α l).mpr hsat) ((sat_cnfClause_litNeg_iff α l).mp hneg)

theorem entails_resolve_to {F0 : CNF Nat} {p : Nat} {c1 c2 c3 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (h2 : F0.EntailsClause (cnfClause c2))
    (hs1 : ∀ l ∈ c1, l = p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l]))
    (hs2 : ∀ l ∈ c2, l = litNeg p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c3) := by
  refine entails_of_mem_or_false (entails_resolve (p := p) h1 h2) fun l hl => ?_
  unfold resolveOn at hl
  rcases List.mem_append.mp hl with hl1 | hl2
  · rw [List.mem_filter, bne_iff_ne] at hl1
    rcases hs1 l hl1.1 with rfl | hin | hf
    · exact absurd rfl hl1.2
    · exact Or.inl hin
    · exact Or.inr hf
  · rw [List.mem_filter, bne_iff_ne] at hl2
    rcases hs2 l hl2.1 with rfl | hin | hf
    · exact absurd rfl hl2.2
    · exact Or.inl hin
    · exact Or.inr hf

end LeanQbe.T.Examples.Kissat.Ref
