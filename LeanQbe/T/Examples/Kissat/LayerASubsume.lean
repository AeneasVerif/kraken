module

public import LeanQbe.T.Examples.Kissat.LayerACollect1

/-!
# Pure Lean Layer-A Inprocessing Theory: Subsumption & Self-Subsuming Resolution

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of forward/backward
subsumption deletion, self-subsuming resolution (`SSR`), and on-the-fly subsumption (`OTFS`)
preserving full logical equivalence (`∀ α, F'.Sat α ↔ F.Sat α` and `F'.Unsat ↔ F.Unsat`):

1. **Clause-list & CNF replacement/deletion primitives** (`clauseSubset`, `removeLit`,
   `deleteIdx`, `replaceIdx`).
2. **Subsumption deletion soundness** (`subsume_cnf_equiv`, `subsume_clauses_equiv`,
   `entailed_del_equiv`): deleting `C` when another distinct clause `D ⊆ C` remains in `F`
   preserves both `Sat α` (`↔`) and `Unsat` (`↔`).
3. **Self-subsuming resolution & OTFS** (`ssr_cnf_equiv`, `ssr_clauses_equiv`,
   `otfs_clauses_equiv`): if `l ∈ C`, `¬l ∈ D`, and `(D \ {¬l}) ⊆ (C \ {l})`, then
   `D ≠ C` automatically and replacing `C` with `C \ {l}` preserves `Sat α` (`↔`) and
   `Unsat` (`↔`); similarly replacing `C` with `resolveOn l C D` when `resolveOn l C D ⊆ C`.
4. **Executable passes & DB/CDCL bridge** (`subsumePass`, `ssrPass`, `subsumeAndSSR`,
   `subsume_pass_equiv`, `ssr_pass_equiv`, `subsume_ssr_equiv`, `subsume_db_equiv`,
   `ssr_db_equiv`, `subsume_preserves_inv`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std.Sat

/-! ## 1. Clause subsets, literal removal, and list slot deletion/replacement -/

/-- Decidable clause subsumption check `d ⊆ c`. -/
def clauseSubset (d c : List Nat) : Bool :=
  d.all fun l => c.contains l

theorem clauseSubset_iff (d c : List Nat) :
    clauseSubset d c = true ↔ ∀ l ∈ d, l ∈ c := by
  simp [clauseSubset, List.all_eq_true]

/-- A subset clause entails its superset clause for every assignment. -/
theorem sat_clause_of_subset {α : Nat → Bool} {d c : List Nat} (hsub : ∀ l ∈ d, l ∈ c) :
    (cnfClause d).Sat α → (cnfClause c).Sat α := by
  intro hd
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α d).mp hd
  exact (clause_sat_cnfClause_iff α c).mpr ⟨l, hsub l hl, hsat⟩

/-- Remove every occurrence of literal `l` from clause `c`. -/
def removeLit (c : List Nat) (l : Nat) : List Nat :=
  c.filter (· != l)

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

/-- Delete element at index `i` from a list (leaving `xs` unchanged if `i ≥ xs.length`). -/
def deleteIdx {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i + 1 => x :: deleteIdx xs i

/-- Replace element at index `i` with `y` (leaving `xs` unchanged if `i ≥ xs.length`). -/
def replaceIdx {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, y => y :: xs
  | x :: xs, i + 1, y => x :: replaceIdx xs i y

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

theorem cnf_unsat_iff_of_sat_iff {f g : CNF Nat} (h : ∀ α, f.Sat α ↔ g.Sat α) :
    f.Unsat ↔ g.Unsat := by
  simp only [CNF.unsat_iff_not_sat]
  exact ⟨fun hf α hα => hf α ((h α).mpr hα), fun hg α hα => hg α ((h α).mp hα)⟩

/-! ## 2. Subsumption deletion soundness -/

/-- General semantic clause deletion soundness: if remaining formula `f` already entails
clause `c`, deleting `c` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem entailed_del_equiv {f : CNF Nat} {c : CNF.Clause Nat}
    (hent : f.EntailsClause c) :
    (∀ α : Nat → Bool, (f.add c).Sat α ↔ f.Sat α) ∧ ((f.add c).Unsat ↔ f.Unsat) := by
  have hsat : ∀ α : Nat → Bool, (f.add c).Sat α ↔ f.Sat α := fun α => by
    rw [CNF.sat_add]
    exact ⟨fun h => h.2, fun hf => ⟨CNF.entails_clause_def.mp hent α hf, hf⟩⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **Subsumption deletion soundness (`CNF Nat`)**: if remaining formula `f` entails clause `d`
and `d ⊆ c`, deleting `c` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem subsume_cnf_equiv {f : CNF Nat} {d c : List Nat}
    (hd : f.EntailsClause (cnfClause d)) (hsub : ∀ l ∈ d, l ∈ c) :
    (∀ α : Nat → Bool, (f.add (cnfClause c)).Sat α ↔ f.Sat α) ∧
      ((f.add (cnfClause c)).Unsat ↔ f.Unsat) :=
  entailed_del_equiv (CNF.entails_clause_def.mpr fun α hf =>
    sat_clause_of_subset hsub (CNF.entails_clause_def.mp hd α hf))

/-- **Subsumption deletion soundness (clause list)**: deleting clause at index `i` when a
distinct remaining slot `j ≠ i` satisfies `cs[j] ⊆ cs[i]` preserves both `Sat α` (`↔`) and
`Unsat` (`↔`). -/
theorem subsume_clauses_equiv {cs : List (List Nat)} {i j : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (hne : j ≠ i)
    (hsub : ∀ l ∈ cs[j], l ∈ cs[i]) :
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
      · subst hki; exact sat_clause_of_subset hsub (hrem j hj hne)
      · exact hrem k hk hki
    · intro hall k hk _; exact hall k hk
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Subsumption deletion when witnessing subsumer `d ∈ deleteIdx cs i` directly. -/
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
        (cnfOfClauses cs).Unsat) := by
  have hne : j ≠ i := ssr_distinct_idx hi hj hl hsub
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (removeLit cs[i] l))).Sat α ↔
        (cnfOfClauses cs).Sat α := by
    intro α
    rw [sat_cnfOfClauses_replaceIdx_iff _ _ hi, sat_cnfOfClauses_iff_getElem]
    constructor
    · rintro ⟨hc', hrest⟩ k hk
      by_cases hki : k = i
      · subst hki; exact sat_clause_of_subset (removeLit_subset _ l) hc'
      · exact hrest k hk hki
    · intro hall
      refine ⟨((sat_ssr_and_iff α hl hnd hsub).mp ⟨hall j hj, hall i hi⟩).2,
        fun k hk _ => hall k hk⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- **On-the-fly subsumption (`OTFS`) soundness**: when resolving `cs[i]` and distinct
`cs[j]` (`j ≠ i`) on `l` yields `R = resolveOn l cs[i] cs[j]` with `R ⊆ cs[i]`, replacing
`cs[i]` with `R` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem otfs_clauses_equiv {cs : List (List Nat)} {i j l : Nat}
    (hi : i < cs.length) (hj : j < cs.length) (hne : j ≠ i)
    (hsub : ∀ x ∈ resolveOn l cs[i] cs[j], x ∈ cs[i]) :
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (resolveOn l cs[i] cs[j]))).Sat α ↔
        (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (replaceIdx cs i (resolveOn l cs[i] cs[j]))).Unsat ↔
        (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx cs i (resolveOn l cs[i] cs[j]))).Sat α ↔
        (cnfOfClauses cs).Sat α := by
    intro α
    rw [sat_cnfOfClauses_replaceIdx_iff _ _ hi, sat_cnfOfClauses_iff_getElem]
    constructor
    · rintro ⟨hres, hrest⟩ k hk
      by_cases hki : k = i
      · subst hki; exact sat_clause_of_subset hsub hres
      · exact hrest k hk hki
    · intro hall
      have hi_ent : (cnfOfClauses cs).EntailsClause (cnfClause cs[i]) :=
        CNF.entails_clause_def.mpr fun β hβ =>
          (sat_cnfOfClauses_iff_getElem β cs).mp hβ i hi
      have hj_ent : (cnfOfClauses cs).EntailsClause (cnfClause cs[j]) :=
        CNF.entails_clause_def.mpr fun β hβ =>
          (sat_cnfOfClauses_iff_getElem β cs).mp hβ j hj
      have hres_ent := entails_resolve (p := l) hi_ent hj_ent
      have hsat_cs : (cnfOfClauses cs).Sat α :=
        (sat_cnfOfClauses_iff_getElem α cs).mpr hall
      exact ⟨CNF.entails_clause_def.mp hres_ent α hsat_cs, fun k hk _ => hall k hk⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Bridge from `Core.strengthenWithBinary` to full logical equivalence (`Sat α ↔` / `Unsat ↔`). -/
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

/-- Check whether `c` is subsumed by any clause in `others`. -/
def isSubsumedByAny (c : List Nat) (others : List (List Nat)) : Bool :=
  others.any fun d => clauseSubset d c

theorem isSubsumedByAny_iff (c : List Nat) (others : List (List Nat)) :
    isSubsumedByAny c others = true ↔ ∃ d ∈ others, ∀ l ∈ d, l ∈ c := by
  simp [isSubsumedByAny, List.any_eq_true, clauseSubset_iff]

/-- Try strengthening `c` by a single self-subsuming resolution step against `d`. -/
def trySSR (c d : List Nat) : Option (List Nat) :=
  match c.find? fun l =>
      d.contains (litNeg l) &&
        (removeLit d (litNeg l)).all fun x => x != l && c.contains x with
  | some l => some (removeLit c l)
  | none => none

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

/-- Iteratively self-subsume `c` against every clause in `others`. -/
def strengthenWithList (c : List Nat) (others : List (List Nat)) : List Nat :=
  others.foldl (fun cur d => match trySSR cur d with | some cur' => cur' | none => cur) c

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

/-- Single forward/backward subsumption elimination pass over a clause list, checking each
clause strictly against the remaining kept + unvisited clauses (`kept ++ rest`). -/
def subsumePassAux : List (List Nat) → List (List Nat) → List (List Nat)
  | kept, [] => kept.reverse
  | kept, c :: rest =>
    if isSubsumedByAny c kept || isSubsumedByAny c rest then
      subsumePassAux kept rest
    else
      subsumePassAux (c :: kept) rest

/-- Subsumption pass deleting subsumed clauses from `cs`. -/
def subsumePass (cs : List (List Nat)) : List (List Nat) :=
  subsumePassAux [] cs

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

/-- Single SSR strengthening pass: strengthens every clause `c` against all other kept and
remaining clauses (`kept ++ rest`). -/
def ssrPassAux : List (List Nat) → List (List Nat) → List (List Nat)
  | kept, [] => kept.reverse
  | kept, c :: rest =>
    let c' := strengthenWithList c (kept ++ rest)
    ssrPassAux (c' :: kept) rest

/-- Self-subsuming resolution pass over `cs`. -/
def ssrPass (cs : List (List Nat)) : List (List Nat) :=
  ssrPassAux [] cs

private theorem ssrPassAux_sat_iff (α : Nat → Bool) :
    ∀ (todo kept : List (List Nat)),
      (cnfOfClauses (ssrPassAux kept todo)).Sat α ↔
        (cnfOfClauses (kept.reverse ++ todo)).Sat α
  | [], kept => by simp [ssrPassAux]
  | c :: rest, kept => by
    have ih := ssrPassAux_sat_iff α rest (strengthenWithList c (kept ++ rest) :: kept)
    rw [ssrPassAux, ih]
    simp only [cnf_sat_cnfOfClauses_iff, List.mem_append, List.mem_cons, List.mem_reverse]
    have heq : (∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α) →
        ((cnfClause (strengthenWithList c (kept ++ rest))).Sat α ↔ (cnfClause c).Sat α) :=
      fun h => strengthenWithList_equiv α c (kept ++ rest) fun d hd =>
        h d (List.mem_append.mp hd)
    constructor
    · intro h
      have hkr : ∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α := fun d hd =>
        h d (hd.elim (fun hk => Or.inl (Or.inr hk)) (fun hr => Or.inr hr))
      intro d hd
      rcases hd with hk | rfl | hr
      · exact hkr d (Or.inl hk)
      · exact (heq hkr).mp (h _ (Or.inl (Or.inl rfl)))
      · exact hkr d (Or.inr hr)
    · intro h
      have hkr : ∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α := fun d hd =>
        h d (hd.elim (fun hk => Or.inl hk) (fun hr => Or.inr (Or.inr hr)))
      intro d hd
      rcases hd with (rfl | hk) | hr
      · exact (heq hkr).mpr (h _ (Or.inr (Or.inl rfl)))
      · exact hkr d (Or.inl hk)
      · exact hkr d (Or.inr hr)

/-- **Executable SSR pass soundness**: `ssrPass` preserves both `Sat α` (`↔`) and `Unsat` (`↔`). -/
theorem ssr_pass_equiv (cs : List (List Nat)) :
    (∀ α : Nat → Bool, (cnfOfClauses (ssrPass cs)).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
      ((cnfOfClauses (ssrPass cs)).Unsat ↔ (cnfOfClauses cs).Unsat) := by
  have hsat : ∀ α : Nat → Bool,
      (cnfOfClauses (ssrPass cs)).Sat α ↔ (cnfOfClauses cs).Sat α := fun α => by
    simpa [ssrPass] using ssrPassAux_sat_iff α cs []
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

/-- Iterated subsumption + self-subsuming resolution simplifier (`fuel` rounds). -/
def subsumeAndSSR : Nat → List (List Nat) → List (List Nat)
  | 0, cs => cs
  | fuel + 1, cs => subsumeAndSSR fuel (subsumePass (ssrPass cs))

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

private theorem getElem?_setIfInBounds {α : Type} (xs : Array α) (i j : Nat) (v : α) :
    (xs.setIfInBounds i v)[j]? = if i < xs.size ∧ j = i then some v else xs[j]? := by
  by_cases hi : i < xs.size
  · by_cases hij : j = i
    · subst hij
      simp [hi]
    · simp only [hi, hij, and_false, ↓reduceIte, Array.getElem?_setIfInBounds, Ne.symm hij]
  · simp [hi, Array.setIfInBounds]

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
  have hs_tr : s'.trail = s.trail := rfl
  have hs_f0 : s'.f0 = s.f0 := rfl
  have hs_lvl : ∀ x, stateLevel s' x = stateLevel s x := fun _ => rfl
  have hs_rsn : ∀ x, stateReason s' x = stateReason s x := fun _ => rfl
  have hdb : ∀ (k : Nat) (c0 : Clause), s'.clauses[k]? = some (some c0) →
      s.f0.EntailsClause (cnfClause c0.lits) := by
    intro k c0 hget
    rw [getElem?_setIfInBounds] at hget
    split at hget
    · cases hget
    · exact hinv.db_sound k c0 hget
  have hinv' : LazyTrailInv s' := by
    refine ⟨hinv.vars_nodup, hinv.levels_le, hinv.dec_earliest, hdb, hinv.units_sound, ?_,
      hinv.inconsistent_sound⟩
    intro i hi
    have hi_s : i < s.trail.size := hi
    have hrd := hinv.reason_dag i hi_s
    dsimp only at hrd
    change match stateReason s' s'.trail[i] with | _ => _
    simp only [hs_tr, hs_f0, hs_lvl, hs_rsn]
    generalize hrsn : stateReason s s.trail[i] = rsn
    rw [hrsn] at hrd
    cases rsn with
    | decision | unit | binary _ => exact hrd
    | large k =>
      obtain ⟨ck, hgetk, hngk, hmk, hallk⟩ := hrd
      have hne_k : k ≠ cid := by
        intro heq; subst heq
        have hact := isActiveLargeReason_iff.mpr ⟨i, hi_s, hrsn⟩
        rw [hact] at hnonact; cases hnonact
      refine ⟨ck, ?_, hngk, hmk, hallk⟩
      rw [getElem?_setIfInBounds, ite_eq_right (by simp [hne_k])]
      exact hgetk
  exact ⟨hinv', rfl, rfl, hdb_eqv.1, hdb_eqv.2⟩

end LeanQbe.T.Examples.Kissat
