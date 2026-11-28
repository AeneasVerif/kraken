/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Subsume
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Reduce

/-!
# Soundness Proofs for `Subsume`

Extracted pure-Lean proofs for `Subsume` (zero `Kraken.*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Clause subsets, literal removal, and list slot deletion/replacement -/

theorem clauseSubset_iff (d c : List Nat) :
    clauseSubset d c = true ↔ ∀ l ∈ d, l ∈ c := by
  simp [clauseSubset, List.all_eq_true]

/-- A subset clause entails its superset clause for every assignment. -/
theorem sat_clause_of_subset {α : Nat → Bool} {d c : List Nat} (hsub : ∀ l ∈ d, l ∈ c) :
    (cnfClause d).Sat α → (cnfClause c).Sat α := by
  intro hd
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α d).mp hd
  exact (clause_sat_cnfClause_iff α c).mpr ⟨l, hsub l hl, hsat⟩

@[simp] theorem mem_removeLit_iff {x : Nat} {c : List Nat} {l : Nat} :
    x ∈ removeLit c l ↔ x ∈ c ∧ x ≠ l := by
  simp [removeLit, bne_iff_ne]

theorem removeLit_subset (c : List Nat) (l : Nat) :
    ∀ x ∈ removeLit c l, x ∈ c := by
  intro x hx; exact (mem_removeLit_iff.mp hx).1

theorem sat_removeLit_iff (α : Nat → Bool) (c : List Nat) (l : Nat) :
    (cnfClause (removeLit c l)).Sat α ↔
      ∃ x ∈ c, x ≠ l ∧ α (litVar x) = !(litSign x) := by
  rw [clause_sat_cnfClause_iff]
  constructor
  · rintro ⟨x, hx, hs⟩; exact ⟨x, (mem_removeLit_iff.mp hx).1, (mem_removeLit_iff.mp hx).2, hs⟩
  · rintro ⟨x, hx, hne, hs⟩; exact ⟨x, mem_removeLit_iff.mpr ⟨hx, hne⟩, hs⟩

@[simp] theorem deleteIdx_length_lt {α : Type} :
    ∀ (xs : List α) {i : Nat}, i < xs.length → (deleteIdx xs i).length + 1 = xs.length
  | [], _, hi => by cases hi
  | _ :: _, 0, _ => by simp [deleteIdx]
  | _ :: xs, i + 1, hi => by
    simp only [deleteIdx, List.length_cons]
    have ih := deleteIdx_length_lt xs (Nat.lt_of_succ_lt_succ hi)
    omega

@[simp] theorem replaceIdx_length {α : Type} :
    ∀ (xs : List α) (i : Nat) (y : α), (replaceIdx xs i y).length = xs.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, y => by simp [replaceIdx, replaceIdx_length xs i y]

theorem mem_deleteIdx_of_ne {α : Type} :
    ∀ {xs : List α} {i j : Nat} (hj : j < xs.length), j ≠ i → xs[j] ∈ deleteIdx xs i
  | _ :: _, 0, 0, _, hne => absurd rfl hne
  | _ :: _, 0, k + 1, _, _ => by simp [deleteIdx]
  | x :: xs, i + 1, 0, _, _ => by simp [deleteIdx]
  | _ :: xs, i + 1, k + 1, hj, hne =>
    List.mem_cons_of_mem _
      (mem_deleteIdx_of_ne (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h)))

theorem forall_mem_deleteIdx_iff {α : Type} :
    ∀ (xs : List α) (i : Nat) (P : α → Prop),
      (∀ x ∈ deleteIdx xs i, P x) ↔
        ∀ (j : Nat) (hj : j < xs.length), j ≠ i → P xs[j]
  | [], i, P => by simp [deleteIdx]
  | x :: xs, 0, P => by
    simp only [deleteIdx]
    constructor
    · intro h j hj hne
      cases j with
      | zero => exact absurd rfl hne
      | succ k => exact h (xs[k]'(Nat.lt_of_succ_lt_succ hj)) (List.getElem_mem _)
    · intro h y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
      exact h (k + 1) (Nat.succ_lt_succ hk) (Nat.succ_ne_zero k)
  | x :: xs, i + 1, P => by
    have ih := forall_mem_deleteIdx_iff xs i P
    simp only [deleteIdx, List.mem_cons, forall_eq_or_imp, ih]
    constructor
    · rintro ⟨hx, hrest⟩ j hj hne
      cases j with
      | zero => exact hx
      | succ k =>
        exact hrest k (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))
    · intro h
      refine ⟨h 0 (Nat.zero_lt_succ _) (Nat.zero_ne_add_one i), fun k hk hne => ?_⟩
      exact h (k + 1) (Nat.succ_lt_succ hk) (fun h' => hne (Nat.succ.inj h'))

theorem forall_mem_replaceIdx_iff {α : Type} :
    ∀ (xs : List α) {i : Nat}, i < xs.length → ∀ (y : α) (P : α → Prop),
      (∀ x ∈ replaceIdx xs i y, P x) ↔
        P y ∧ ∀ (j : Nat) (hj : j < xs.length), j ≠ i → P xs[j]
  | [], _, hi, _, _ => by cases hi
  | _ :: xs, 0, _, y, P => by
    simp only [replaceIdx, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hy, hrest⟩
      refine ⟨hy, fun j hj hne => ?_⟩
      cases j with
      | zero => exact absurd rfl hne
      | succ k => exact hrest (xs[k]'(Nat.lt_of_succ_lt_succ hj)) (List.getElem_mem _)
    · rintro ⟨hy, hrest⟩
      refine ⟨hy, fun z hz => ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
      exact hrest (k + 1) (Nat.succ_lt_succ hk) (Nat.succ_ne_zero k)
  | x :: xs, i + 1, hi, y, P => by
    have ih := forall_mem_replaceIdx_iff xs (Nat.lt_of_succ_lt_succ hi) y P
    simp only [replaceIdx, List.mem_cons, forall_eq_or_imp, ih]
    constructor
    · rintro ⟨hx, hy, hrest⟩
      refine ⟨hy, fun j hj hne => ?_⟩
      cases j with
      | zero => exact hx
      | succ k =>
        exact hrest k (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))
    · rintro ⟨hy, hrest⟩
      refine ⟨hrest 0 (Nat.zero_lt_succ _) (Nat.zero_ne_add_one i), hy, fun k hk hne => ?_⟩
      exact hrest (k + 1) (Nat.succ_lt_succ hk) (fun h => hne (Nat.succ.inj h))

theorem sat_cnfOfClauses_iff_getElem (α : Nat → Bool) (cs : List (List Nat)) :
    (cnfOfClauses cs).Sat α ↔ ∀ (j : Nat) (hj : j < cs.length), (cnfClause cs[j]).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff]
  exact ⟨fun h j hj => h cs[j] (List.getElem_mem hj),
    fun h c hc => let ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hc; heq ▸ h j hj⟩

theorem sat_cnfOfClauses_deleteIdx_iff (α : Nat → Bool) (cs : List (List Nat)) (i : Nat) :
    (cnfOfClauses (deleteIdx cs i)).Sat α ↔
      ∀ (j : Nat) (hj : j < cs.length), j ≠ i → (cnfClause cs[j]).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff, forall_mem_deleteIdx_iff]

theorem sat_cnfOfClauses_replaceIdx_iff (α : Nat → Bool) (cs : List (List Nat)) {i : Nat}
    (hi : i < cs.length) (c' : List Nat) :
    (cnfOfClauses (replaceIdx cs i c')).Sat α ↔
      (cnfClause c').Sat α ∧
        ∀ (j : Nat) (hj : j < cs.length), j ≠ i → (cnfClause cs[j]).Sat α := by
  rw [cnf_sat_cnfOfClauses_iff, forall_mem_replaceIdx_iff cs hi]

theorem sat_cnfOfClauses_replaceIdx_equiv {cs : List (List Nat)} {i : Nat}
    (hi : i < cs.length) {c' : List Nat}
    (hbwd : ∀ α, (cnfOfClauses (deleteIdx cs i)).Sat α →
      (cnfClause c').Sat α → (cnfClause cs[i]).Sat α)
    (hfwd : ∀ α, (cnfOfClauses cs).Sat α → (cnfClause c').Sat α) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i c')).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (replaceIdx cs i c')).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i c')).Sat α ↔ (cnfOfClauses cs).Sat α := by
    intro α
    rw [sat_cnfOfClauses_replaceIdx_iff _ _ hi, sat_cnfOfClauses_iff_getElem]
    have hdel : (cnfOfClauses (deleteIdx cs i)).Sat α ↔
        ∀ (j : Nat) (hj : j < cs.length), j ≠ i → (cnfClause cs[j]).Sat α :=
      sat_cnfOfClauses_deleteIdx_iff α cs i
    constructor
    · rintro ⟨hc', hrest⟩ k hk
      by_cases hki : k = i
      · subst hki; exact hbwd α (hdel.mpr hrest) hc'
      · exact hrest k hk hki
    · intro hall
      exact ⟨hfwd α ((sat_cnfOfClauses_iff_getElem α cs).mpr hall), fun j hj _ => hall j hj⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-! ## 2. Subsumption deletion soundness -/

/-- **Subsumption deletion soundness (`CNF Nat`)**: if remaining formula `f` entails clause `d`
and `d ⊆ c`, deleting `c` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem subsume_cnf_equiv {f : CNF Nat} {d c : List Nat}
    (hd : f.EntailsClause (cnfClause d)) (hsub : ∀ l ∈ d, l ∈ c) :
    (∀ α : Nat → Bool, (f.add (cnfClause c)).Sat α ↔ f.Sat α) ∧
      ((f.add (cnfClause c)).Unsat ↔ f.Unsat) :=
  entailed_del_equiv (CNF.entails_clause_def.mpr fun α hf =>
    sat_clause_of_subset hsub (CNF.entails_clause_def.mp hd α hf))

theorem subsume_mem_equiv {cs : List (List Nat)} {i : Nat} {d : List Nat}
    (hi : i < cs.length) (hd : d ∈ deleteIdx cs i) (hsub : ∀ l ∈ d, l ∈ cs[i]) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (deleteIdx cs i)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (deleteIdx cs i)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (deleteIdx cs i)).Sat α ↔ (cnfOfClauses cs).Sat α := by
    intro α
    rw [sat_cnfOfClauses_deleteIdx_iff, sat_cnfOfClauses_iff_getElem]
    constructor
    · intro hrem k hk
      by_cases hki : k = i
      · subst hki
        have hsat_d : (cnfClause d).Sat α :=
          (cnf_sat_cnfOfClauses_iff α (deleteIdx cs k)).mp
            ((sat_cnfOfClauses_deleteIdx_iff α cs k).mpr hrem) d hd
        exact sat_clause_of_subset hsub hsat_d
      · exact hrem k hk hki
    · intro hall k hk _; exact hall k hk
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Subsumption deletion soundness (clause list)**: deleting clause at index `i` when a
distinct remaining slot `j ≠ i` satisfies `cs[j] ⊆ cs[i]` preserves both `Sat α` (`↔`) and
`Unsat` (`↔`). -/
theorem subsume_clauses_equiv {cs : List (List Nat)} {i j : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (hne : j ≠ i)
    (hsub : ∀ l ∈ cs[j], l ∈ cs[i]) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (deleteIdx cs i)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (deleteIdx cs i)).Unsat ↔ (cnfOfClauses cs).Unsat) :=
  subsume_mem_equiv hi (mem_deleteIdx_of_ne hj hne) hsub

/-! ## 3. Self-subsuming resolution (`SSR`) and on-the-fly subsumption (`OTFS`) -/

/-- Any clause `d` witnessing self-subsuming resolution on `l ∈ c` (`¬l ∈ d`,
`d \ {¬l} ⊆ c \ {l}`) is automatically distinct from `c`. -/
theorem ssr_clauses_distinct {l : Nat} {c d : List Nat} (hlc : l ∈ c)
    (hsub : ∀ x ∈ removeLit d (litNeg l), x ∈ removeLit c l) : d ≠ c := by
  intro hdc
  subst hdc
  have hmem : l ∈ removeLit d (litNeg l) := mem_removeLit_iff.mpr ⟨hlc, (litNeg_ne_self l).symm⟩
  exact (mem_removeLit_iff.mp (hsub l hmem)).2 rfl

/-- Core semantic equivalence of self-subsuming resolution on a pair of clauses `(c, d)`. -/
theorem sat_ssr_and_iff (α : Nat → Bool) {l : Nat} {c d : List Nat}
    (_hlc : l ∈ c) (_hnd : litNeg l ∈ d)
    (hsub : ∀ x ∈ removeLit d (litNeg l), x ∈ removeLit c l) :
    ((cnfClause d).Sat α ∧ (cnfClause c).Sat α) ↔
      ((cnfClause d).Sat α ∧ (cnfClause (removeLit c l)).Sat α) := by
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨hd, ?_⟩
    by_cases hl : (cnfClause [l]).Sat α
    · obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α d).mp hd
      have hne : x ≠ litNeg l := by
        rintro rfl
        exact (sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α _).mpr hsat) hl
      exact sat_clause_of_subset hsub ((clause_sat_cnfClause_iff α _).mpr
        ⟨x, mem_removeLit_iff.mpr ⟨hx, hne⟩, hsat⟩)
    · obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α c).mp hc
      have hne : x ≠ l := by rintro rfl; exact hl ((sat_cnfClause_singleton α x).mpr hsat)
      exact (clause_sat_cnfClause_iff α _).mpr ⟨x, mem_removeLit_iff.mpr ⟨hx, hne⟩, hsat⟩
  · rintro ⟨hd, hc'⟩
    exact ⟨hd, sat_clause_of_subset (removeLit_subset c l) hc'⟩

/-- **Self-subsuming resolution soundness (`CNF Nat`)**: if remaining formula `f` entails `d`,
`l ∈ c`, `¬l ∈ d`, and `d \ {¬l} ⊆ c \ {l}`, strengthening `c` to `c \ {l}` preserves both
`Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem ssr_cnf_equiv {f : CNF Nat} {l : Nat} {c d : List Nat}
    (hd : f.EntailsClause (cnfClause d)) (hlc : l ∈ c) (hnd : litNeg l ∈ d)
    (hsub : ∀ x ∈ removeLit d (litNeg l), x ∈ removeLit c l) :
    (∀ α : Nat → Bool,
      (f.add (cnfClause (removeLit c l))).Sat α ↔ (f.add (cnfClause c)).Sat α) ∧
      ((f.add (cnfClause (removeLit c l))).Unsat ↔ (f.add (cnfClause c)).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (f.add (cnfClause (removeLit c l))).Sat α ↔ (f.add (cnfClause c)).Sat α := by
    intro α
    simp only [CNF.sat_add]
    constructor
    · rintro ⟨hc', hf⟩
      exact ⟨((sat_ssr_and_iff α hlc hnd hsub).mpr
        ⟨CNF.entails_clause_def.mp hd α hf, hc'⟩).2, hf⟩
    · rintro ⟨hc, hf⟩
      exact ⟨((sat_ssr_and_iff α hlc hnd hsub).mp
        ⟨CNF.entails_clause_def.mp hd α hf, hc⟩).2, hf⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Distinctness of indices `j ≠ i` is guaranteed automatically by `l ∈ cs[i]` and
`cs[j] \ {¬l} ⊆ cs[i] \ {l}`. -/
theorem ssr_distinct_idx {cs : List (List Nat)} {i j l : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (hl : l ∈ cs[i])
    (hsub : ∀ x ∈ removeLit cs[j] (litNeg l), x ∈ removeLit cs[i] l) : j ≠ i := by
  intro hji; subst hji; exact ssr_clauses_distinct hl hsub rfl

/-- **Self-subsuming resolution soundness (clause list)**: replacing `cs[i]` with
`cs[i] \ {l}` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem ssr_clauses_equiv {cs : List (List Nat)} {i j l : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (hl : l ∈ cs[i]) (hnd : litNeg l ∈ cs[j])
    (hsub : ∀ x ∈ removeLit cs[j] (litNeg l), x ∈ removeLit cs[i] l) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (removeLit cs[i] l))).Sat α ↔
        (cnfOfClauses cs).Sat α) ∧
        ((cnfOfClauses (replaceIdx cs i (removeLit cs[i] l))).Unsat ↔
        (cnfOfClauses cs).Unsat) :=
  sat_cnfOfClauses_replaceIdx_equiv hi
    (fun _ _ hc' => sat_clause_of_subset (removeLit_subset _ l) hc')
    (fun α hall =>
      have hget := (sat_cnfOfClauses_iff_getElem α cs).mp hall
      ((sat_ssr_and_iff α hl hnd hsub).mp ⟨hget j hj, hget i hi⟩).2)

/-- **On-the-fly subsumption (`OTFS`) soundness**: when resolving `cs[i]` and distinct
`cs[j]` (`j ≠ i`) on `l` yields `R = resolveOn l cs[i] cs[j]` with `R ⊆ cs[i]`, replacing
`cs[i]` with `R` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem otfs_clauses_equiv {cs : List (List Nat)} {i j l : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (_hne : j ≠ i)
    (hsub : ∀ x ∈ resolveOn l cs[i] cs[j], x ∈ cs[i]) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (resolveOn l cs[i] cs[j]))).Sat α ↔
        (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (replaceIdx cs i (resolveOn l cs[i] cs[j]))).Unsat ↔
        (cnfOfClauses cs).Unsat) :=
  sat_cnfOfClauses_replaceIdx_equiv hi
    (fun _ _ hres => sat_clause_of_subset hsub hres)
    (fun α hall =>
      let hent (k : Nat) (hk : k < cs.length) :
          (cnfOfClauses cs).EntailsClause (cnfClause cs[k]) :=
        CNF.entails_clause_def.mpr fun β hβ =>
          (sat_cnfOfClauses_iff_getElem β cs).mp hβ k hk
      CNF.entails_clause_def.mp (entails_resolve (p := l) (hent i hi) (hent j hj)) α hall)

/-- Bridge from `Sat.strengthenWithBinary` to full logical equivalence (`Sat α ↔` / `Unsat ↔`). -/
theorem strengthenBinary_equiv {f : CNF Nat} {c : List Nat} {pivot binOther : Nat}
    (hbin : f.EntailsClause (cnfClause [pivot, binOther])) :
    (∀ α : Nat → Bool,
      (f.add (cnfClause (strengthenWithBinary c pivot binOther))).Sat α ↔
        (f.add (cnfClause c)).Sat α) ∧
      ((f.add (cnfClause (strengthenWithBinary c pivot binOther))).Unsat ↔
        (f.add (cnfClause c)).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (f.add (cnfClause (strengthenWithBinary c pivot binOther))).Sat α ↔
        (f.add (cnfClause c)).Sat α := by
    intro α
    simp only [CNF.sat_add]
    constructor
    · rintro ⟨hstr, hf⟩
      refine ⟨?_, hf⟩
      unfold strengthenWithBinary at hstr
      split at hstr
      · exact sat_clause_of_subset (fun x hx => (List.mem_filter.mp hx).1) hstr
      · exact hstr
    · rintro ⟨hc, hf⟩
      have hent : (f.add (cnfClause c)).EntailsClause (cnfClause c) :=
        CNF.entails_clause_def.mpr fun β hβ => (CNF.sat_add.mp hβ).1
      have hbin' : (f.add (cnfClause c)).EntailsClause (cnfClause [pivot, binOther]) :=
        CNF.entails_clause_def.mpr fun β hβ =>
          CNF.entails_clause_def.mp hbin β (CNF.sat_add.mp hβ).2
      exact ⟨CNF.entails_clause_def.mp (strengthenWithBinary_sound hent hbin') α
        (CNF.sat_add.mpr ⟨hc, hf⟩), hf⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-! ## 4. Executable subsumption & SSR passes with equivalence theorems -/

theorem isSubsumedByAny_iff (c : List Nat) (others : List (List Nat)) :
    isSubsumedByAny c others = true ↔ ∃ d ∈ others, ∀ l ∈ d, l ∈ c := by
  simp [isSubsumedByAny, List.any_eq_true, clauseSubset_iff]

theorem trySSR_sound {c d c' : List Nat} (h : trySSR c d = some c') :
    ∃ l ∈ c, litNeg l ∈ d ∧ (∀ x ∈ removeLit d (litNeg l), x ∈ removeLit c l) ∧
      c' = removeLit c l := by
  unfold trySSR at h
  split at h
  · rename_i l hf
    simp only [Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, bne_iff_ne] at hpred
    refine ⟨l, hmem, hpred.1, fun x hx => ?_, h.symm⟩
    exact mem_removeLit_iff.mpr ⟨(hpred.2 x hx).2, (hpred.2 x hx).1⟩
  · simp at h

theorem strengthenWithList_equiv (α : Nat → Bool) (c : List Nat) (others : List (List Nat))
    (hothers : ∀ d ∈ others, (cnfClause d).Sat α) :
    (cnfClause (strengthenWithList c others)).Sat α ↔ (cnfClause c).Sat α := by
  unfold strengthenWithList
  induction others generalizing c with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons]
    have hd : (cnfClause d).Sat α := hothers d (List.mem_cons_self)
    have hds : ∀ e ∈ ds, (cnfClause e).Sat α := fun e he => hothers e (List.mem_cons_of_mem d he)
    cases htr : trySSR c d with
    | none => exact ih c hds
    | some c' =>
      obtain ⟨l, hl, hnd, hsub, rfl⟩ := trySSR_sound htr
      rw [ih (removeLit c l) hds]
      have hand := sat_ssr_and_iff α hl hnd hsub
      exact ⟨fun hc' => (hand.mpr ⟨hd, hc'⟩).2, fun hc => (hand.mp ⟨hd, hc⟩).2⟩

private theorem subsumePassAux_sat_iff (α : Nat → Bool) :
    ∀ (todo kept : List (List Nat)),
      (cnfOfClauses (subsumePassAux kept todo)).Sat α ↔
        (cnfOfClauses (kept.reverse ++ todo)).Sat α
  | [], kept => by simp [subsumePassAux]
  | c :: rest, kept => by
    have ih_keep := subsumePassAux_sat_iff α rest (c :: kept)
    have ih_drop := subsumePassAux_sat_iff α rest kept
    unfold subsumePassAux
    by_cases hsub : (isSubsumedByAny c kept || isSubsumedByAny c rest) = true
    · simp only [hsub, ↓reduceIte, ih_drop, cnf_sat_cnfOfClauses_iff, List.mem_append,
        List.mem_cons, List.mem_reverse]
      constructor
      · intro hrem d hd
        rcases hd with hk | rfl | hr
        · exact hrem d (Or.inl hk)
        · simp only [Bool.or_eq_true, isSubsumedByAny_iff] at hsub
          rcases hsub with ⟨e, he, hsube⟩ | ⟨e, he, hsube⟩
          · exact sat_clause_of_subset hsube (hrem e (Or.inl he))
          · exact sat_clause_of_subset hsube (hrem e (Or.inr he))
        · exact hrem d (Or.inr hr)
      · intro hall d hd
        rcases hd with hk | hr
        · exact hall d (Or.inl hk)
        · exact hall d (Or.inr (Or.inr hr))
    · have hsubf : (isSubsumedByAny c kept || isSubsumedByAny c rest) = false :=
        Bool.eq_false_iff.mpr hsub
      simp only [hsubf, Bool.false_eq_true, ↓reduceIte, ih_keep, cnf_sat_cnfOfClauses_iff,
        List.mem_append, List.mem_cons, List.mem_reverse]
      constructor <;> intro h d hd <;> apply h
      · rcases hd with hk | rfl | hr
        · exact Or.inl (Or.inr hk)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hr
      · rcases hd with (rfl | hk) | hr
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hk
        · exact Or.inr (Or.inr hr)

/-- **Executable subsumption pass soundness**: `subsumePass` preserves both `Sat α` (`↔`)
and `Unsat` (`↔`). -/
theorem subsume_pass_equiv (cs : List (List Nat)) :
    (∀ α : Nat → Bool, (cnfOfClauses (subsumePass cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (subsumePass cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (subsumePass cs)).Sat α ↔ (cnfOfClauses cs).Sat α := fun α => by
    simpa [subsumePass] using subsumePassAux_sat_iff α cs []
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Executable SSR pass soundness**: `ssrPass` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem ssr_pass_equiv (cs : List (List Nat)) :
    (∀ α : Nat → Bool, (cnfOfClauses (ssrPass cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (ssrPass cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (ssrPass cs)).Sat α ↔ (cnfOfClauses cs).Sat α := fun α => by
    have hstep : ∀ β c others, (cnfOfClauses others).Sat β →
        ((cnfClause (strengthenWithList c others)).Sat β ↔ (cnfClause c).Sat β) :=
      fun β c others ho =>
        strengthenWithList_equiv β c others ((cnf_sat_cnfOfClauses_iff β others).mp ho)
    simpa [ssrPass, ssrPassAux] using
      clauseTransformPassAux_sat_iff (fun others c => strengthenWithList c others) hstep α cs []
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Combined subsumption + SSR pass soundness**: preserves both `Sat α` (`↔`) and
`Unsat` (`↔`). -/
theorem subsume_ssr_equiv (fuel : Nat) (cs : List (List Nat)) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (subsumeAndSSR fuel cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (subsumeAndSSR fuel cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (subsumeAndSSR fuel cs)).Sat α ↔ (cnfOfClauses cs).Sat α := by
    induction fuel generalizing cs with
    | zero => intro α; simp [subsumeAndSSR]
    | succ k ih =>
      intro α
      rw [subsumeAndSSR, ih, (subsume_pass_equiv _).1 α, (ssr_pass_equiv cs).1 α]
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-! ## 5. Clause-DB (`Array (Option Clause)`) & `LazyTrailInv` bridge -/

/-- **Clause-DB subsumption deletion soundness**: deleting slot `cid` from `clauses` when a
distinct surviving slot `did ≠ cid` contains `d ⊆ c` preserves `survivingCnf` equivalence. -/
theorem subsume_db_equiv {clauses : Array (Option Clause)} {cid did : Nat} {c d : Clause}
    (hne : did ≠ cid) (hc : clauses[cid]? = some (some c)) (hd : clauses[did]? = some (some d))
    (hng : d.garbage = false) (hsub : ∀ l ∈ d.lits, l ∈ c.lits) :
    (∀ α : Nat → Bool,
      (survivingCnf (clauses.setIfInBounds cid none)).Sat α ↔
        (survivingCnf clauses).Sat α) ∧
      ((survivingCnf (clauses.setIfInBounds cid none)).Unsat ↔
        (survivingCnf clauses).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (survivingCnf (clauses.setIfInBounds cid none)).Sat α ↔
        (survivingCnf clauses).Sat α := by
    intro α
    simp only [sat_survivingCnf_iff, getElem?_setIfInBounds]
    constructor
    · intro hrem k c0 hget hng0
      by_cases hkc : k = cid
      · rw [hkc, hc] at hget
        simp only [Option.some.injEq] at hget
        subst hget
        have hrem_d : (cnfClause d.lits).Sat α :=
          hrem did d (by simp [hne, hd]) (by simp [hng])
        exact sat_clause_of_subset hsub hrem_d
      · exact hrem k c0 (by simp [hkc, hget]) hng0
    · intro hall k c0 hget hng0
      split at hget
      · cases hget
      · exact hall k c0 hget hng0
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Clause-DB SSR strengthening soundness**: replacing `clauses[cid]`'s literals via
`trySSR c.lits d.lits = some lits'` against a distinct surviving `d` preserves `survivingCnf`
equivalence (`Sat α ↔` and `Unsat ↔`). -/
theorem ssr_db_equiv {clauses : Array (Option Clause)} {cid did : Nat} {c d : Clause}
    {lits' : List Nat} (hc : clauses[cid]? = some (some c)) (hd : clauses[did]? = some (some d))
    (hng_c : c.garbage = false) (hng_d : d.garbage = false)
    (htry : trySSR c.lits d.lits = some lits') :
    let clauses' := clauses.setIfInBounds cid (some { c with lits := lits' })
    (∀ α : Nat → Bool, (survivingCnf clauses').Sat α ↔ (survivingCnf clauses).Sat α) ∧
      ((survivingCnf clauses').Unsat ↔ (survivingCnf clauses).Unsat) := by
  obtain ⟨l, hl, hnd, hsub, rfl⟩ := trySSR_sound htry
  have hne : did ≠ cid := by
    intro h
    rw [h, hc] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    exact ssr_clauses_distinct hl hsub rfl
  have hcid_lt : cid < clauses.size := by
    by_cases h : cid < clauses.size
    · exact h
    · simp [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hc
  have hsat : ∀ α : Nat → Bool,
      (survivingCnf (clauses.setIfInBounds cid (some { c with lits := removeLit c.lits l }))).Sat
        α ↔ (survivingCnf clauses).Sat α := by
    intro α
    simp only [sat_survivingCnf_iff, getElem?_setIfInBounds]
    constructor
    · intro hrem k c0 hget hng0
      by_cases hkc : k = cid
      · rw [hkc, hc] at hget
        simp only [Option.some.injEq] at hget
        subst hget
        have hrem_c' : (cnfClause (removeLit c.lits l)).Sat α :=
          hrem cid { c with lits := removeLit c.lits l } (by simp [hcid_lt]) (by simp [hng_c])
        exact sat_clause_of_subset (removeLit_subset c.lits l) hrem_c'
      · exact hrem k c0 (by simp [hkc, hget]) hng0
    · intro hall k c0 hget hng0
      by_cases hkc : k = cid
      · simp only [hcid_lt, hkc, and_self, ↓reduceIte, Option.some.injEq] at hget
        subst hget
        have hsat_c := hall cid c hc (by simp [hng_c])
        have hsat_d := hall did d hd (by simp [hng_d])
        exact ((sat_ssr_and_iff α hl hnd hsub).mp ⟨hsat_d, hsat_c⟩).2
      · simp only [hkc, and_false, ↓reduceIte] at hget
        exact hall k c0 hget hng0
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Deleting unreferenced subsumed clauses from `s : CdclState` (those not cited as an active
trail reason) preserves `LazyTrailInv` (`deleteUnreferencedClauses_sound`) AND preserves
`survivingCnf` equivalence when each deleted clause has a distinct non-deleted subsuming twin
(captured cleanly via single-step unreferenced deletion). -/
theorem subsume_preserves_inv {s : CdclState} (hinv : LazyTrailInv s)
    {cid did : Nat} {c d : Clause}
    (hne : did ≠ cid) (hnonact : isActiveLargeReason s cid = false)
    (hc : s.clauses[cid]? = some (some c)) (hd : s.clauses[did]? = some (some d))
    (hng : d.garbage = false) (hsub : ∀ l ∈ d.lits, l ∈ c.lits) :
    let s' := { s with clauses := s.clauses.setIfInBounds cid none }
    LazyTrailInv s' ∧
    s'.f0 = s.f0 ∧
    s'.trail = s.trail ∧
    (∀ α : Nat → Bool, (survivingCnf s'.clauses).Sat α ↔ (survivingCnf s.clauses).Sat α) ∧
    ((survivingCnf s'.clauses).Unsat ↔ (survivingCnf s.clauses).Unsat) := by
  let s' := { s with clauses := s.clauses.setIfInBounds cid none }
  have hdb_eqv := subsume_db_equiv hne hc hd hng hsub
  have hdb : ∀ (k : Nat) (c0 : Clause), s'.clauses[k]? = some (some c0) →
      s.f0.EntailsClause (cnfClause c0.lits) := by
    intro k c0 hget
    rw [getElem?_setIfInBounds] at hget
    split at hget
    · cases hget
    · exact hinv.db_sound k c0 hget
  have hinv' : LazyTrailInv s' :=
    lazyTrailInv_withClauses hinv s'.clauses hdb fun i hi k ck hrsn hgetk _ => by
      have hne_k : k ≠ cid := fun heq => by
        subst heq
        have hact := isActiveLargeReason_iff.mpr ⟨i, hi, hrsn⟩
        rw [hact] at hnonact; cases hnonact
      change (s.clauses.setIfInBounds cid none)[k]? = some (some ck)
      rw [getElem?_setIfInBounds, ite_eq_right (by simp [hne_k])]
      exact hgetk
  exact ⟨hinv', rfl, rfl, hdb_eqv.1, hdb_eqv.2⟩

end LeanQbe.T.Examples.Kissat.Ref
