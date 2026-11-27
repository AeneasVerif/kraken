/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Sat.CNF

/-!
# Shared Pure-Math Foundation for Kissat Layer-A Reference Specifications

Collects pure Lean definitions and lemmas shared across `LeanQbe.T.Examples.Kissat.Ref.*`
(zero `CdclState`, zero `Kraken.Mem`, `public import Std.Sat.CNF` only):

1. Kissat literal encoding (`litVar`, `litSign`, `litPol`, `litNeg`, `mkLit`, `Std.Sat.Literal`,
   `litOfBitVec`, and `kissatLitToDimacsLiteral`) with bijection lemmas.
2. `CNF Nat` / `List (List Nat)` bridges (`cnfClause`, `clauseOfCnf`, `cnfOfClauses`,
   `clausesOfCnf`, `shiftDownCnf`), resolution/stripping/tautology/freshness lemmas, and
   `sat_foldl_cnfClause_iff`.
3. Total assignment ↔ `Array Bool` evaluation (`evalVar`, `evalLit`, `evalClause`, `evalCnf`,
   `checkModel`, `evalLitVal`, `clauseEvalVal`, `cnfEvalVal`, `substUpdate`, `arraySetPad`).
4. Shared `List` / `Nodup` / pigeonhole / filter / clause-pass combinators.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Kissat-compatible literal encoding -/

/-- Variable index of an encoded Kissat literal (`lit >>> 1 = lit / 2`). -/
@[expose, inline] def litVar (l : Nat) : Nat := l / 2

/-- Sign bit of an encoded literal (`false` = positive `2 * v`, `true` = negative `2 * v + 1`). -/
@[expose, inline] def litSign (l : Nat) : Bool := l % 2 == 1

/-- Semantic polarity of an encoded literal (`true` = positive `2 * v`, `false` = negative). -/
@[expose, inline] def litPol (l : Nat) : Bool := l % 2 == 0

/-- Bitwise negation `l ^^^ 1` (`2 * v ↔ 2 * v + 1`). -/
@[expose, inline] def litNeg (l : Nat) : Nat := l ^^^ 1

/-- Construct an encoded literal from variable `v` and polarity `pol`. -/
@[expose, inline] def mkLit (v : Nat) (pol : Bool) : Nat :=
  if pol then 2 * v else 2 * v + 1

/-- Convert a Kissat literal to `Std.Sat.Literal Nat`. -/
@[expose, inline] def litToLiteral (l : Nat) : Literal Nat :=
  (litVar l, !(litSign l))

/-- Convert `Std.Sat.Literal Nat` to a Kissat literal. -/
@[expose, inline] def litOfLiteral (lit : Literal Nat) : Nat :=
  mkLit lit.1 lit.2

/-- Convert a fixed-width `BitVec w` literal word into `Nat`. -/
@[expose, inline] def litOfBitVec {w : Nat} (bv : BitVec w) : Nat := bv.toNat

/-- Convert a 0-based Kissat literal into 1-based `Std.Sat.Literal Nat` (`v + 1`). -/
@[expose, inline] def kissatLitToDimacsLiteral (l : Nat) : Literal Nat :=
  (litVar l + 1, !(litSign l))

@[simp] theorem litVar_mkLit (v : Nat) (pol : Bool) : litVar (mkLit v pol) = v := by
  cases pol <;> simp [litVar, mkLit] <;> omega

@[simp] theorem litSign_mkLit (v : Nat) (pol : Bool) : litSign (mkLit v pol) = !pol := by
  cases pol <;> simp [litSign, mkLit] <;> omega

@[simp] theorem litPol_mkLit (v : Nat) (pol : Bool) : litPol (mkLit v pol) = pol := by
  cases pol <;> simp [litPol, mkLit] <;> omega

theorem litNeg_eq (l : Nat) : litNeg l = if l % 2 = 0 then l + 1 else l - 1 := by
  unfold litNeg
  have hd : (l ^^^ 1) / 2 = l / 2 := by
    simpa using Nat.xor_div_two_pow (a := l) (b := 1) (n := 1)
  have hm : (l ^^^ 1) % 2 = l % 2 ^^^ 1 := by
    simpa using Nat.xor_mod_two_pow (a := l) (b := 1) (n := 1)
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [h] at hm; change (l ^^^ 1) % 2 = 1 at hm; simp [h]; omega
  · rw [h] at hm; change (l ^^^ 1) % 2 = 0 at hm; simp [h]; omega

@[simp] theorem litVar_litNeg (l : Nat) : litVar (litNeg l) = litVar l := by
  simp [litVar, litNeg_eq]; split <;> omega

@[simp] theorem litSign_litNeg (l : Nat) : litSign (litNeg l) = !litSign l := by
  simp [litSign, litNeg_eq]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h] <;> omega

@[simp] theorem litPol_litNeg (l : Nat) : litPol (litNeg l) = !litPol l := by
  simp [litPol, litNeg_eq]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h] <;> omega

@[simp] theorem litNeg_litNeg (l : Nat) : litNeg (litNeg l) = l := by
  rw [litNeg_eq (litNeg l), litNeg_eq l]
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [ite_eq_left h, ite_eq_right (by omega : (l + 1) % 2 ≠ 0)]; omega
  · rw [ite_eq_right (by omega : l % 2 ≠ 0), ite_eq_left (by omega : (l - 1) % 2 = 0)]; omega

theorem litNeg_ne_self (l : Nat) : litNeg l ≠ l := by
  simp [litNeg_eq]; split <;> omega

theorem litVar_eq_iff (x y : Nat) : litVar x = litVar y ↔ x = y ∨ x = litNeg y := by
  simp only [litVar, litNeg_eq]
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hy] <;> omega

@[simp] theorem litNeg_mkLit (v : Nat) (pol : Bool) :
    litNeg (mkLit v pol) = mkLit v (!pol) := by
  cases pol <;> simp [mkLit, litNeg_eq] <;> omega

theorem mkLit_litVar_litPol (l : Nat) : mkLit (litVar l) (litPol l) = l := by
  simp only [mkLit, litVar, litPol]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h] <;> omega

theorem mkLit_ne_neg (v : Nat) (pol : Bool) : mkLit v pol ≠ mkLit v (!pol) := by
  cases pol <;> simp [mkLit] <;> omega

theorem litVar_eq_iff_mkLit (l v : Nat) :
    litVar l = v ↔ l = mkLit v true ∨ l = mkLit v false := by
  have h1 := litVar_eq_iff l (mkLit v true)
  simp only [litVar_mkLit, litNeg_mkLit, Bool.not_true] at h1
  exact h1

@[simp] theorem litToLiteral_litOfLiteral (lit : Literal Nat) :
    litToLiteral (litOfLiteral lit) = lit := by
  rcases lit with ⟨v, pol⟩; simp [litToLiteral, litOfLiteral]

@[simp] theorem litOfLiteral_litToLiteral (l : Nat) :
    litOfLiteral (litToLiteral l) = l := by
  simp [litOfLiteral, litToLiteral, mkLit, litVar, litSign]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h] <;> omega

@[simp] theorem litToLiteral_litNeg (l : Nat) :
    litToLiteral (litNeg l) = (litToLiteral l).negate := by
  simp [litToLiteral, Literal.negate]

/-! ## 2. Clause & CNF conversions, resolution, `shiftDownCnf`, and `unitsCnf` -/

/-- Convert a list of Kissat literals into a `Std.Sat.CNF.Clause Nat`. -/
@[expose] def cnfClause (lits : List Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (lits.map litToLiteral)

/-- Extract Kissat literals from a `Std.Sat.CNF.Clause Nat`. -/
@[expose] def clauseOfCnf (c : CNF.Clause Nat) : List Nat :=
  c.literals.map litOfLiteral

/-- Convert a list of Kissat clauses into a `Std.Sat.CNF Nat`. -/
@[expose] def cnfOfClauses (cs : List (List Nat)) : CNF Nat :=
  ⟨(cs.map cnfClause).toArray⟩

/-- Convert a `Std.Sat.CNF Nat` into a list of Kissat clauses. -/
@[expose] def clausesOfCnf (cnf : CNF Nat) : List (List Nat) :=
  cnf.clauses.toList.map clauseOfCnf

/-- Strict upper bound (`max var + 1`) on variables appearing in a clause. -/
@[expose] def maxVarClause (c : CNF.Clause Nat) : Nat :=
  c.literals.foldl (fun m l => Nat.max m (l.1 + 1)) 0

/-- Strict upper bound (`max var + 1`) on variables appearing in a `CNF Nat`. -/
@[expose] def maxVarCnf (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m c => Nat.max m (maxVarClause c)) 0

/-- Remove duplicate literals while preserving first-seen order. -/
@[expose] def dedupLits : List Nat → List Nat
  | [] => []
  | l :: ls =>
    let rest := dedupLits ls
    if rest.contains l then rest else l :: rest

/-- Propositional resolution of `c1` and `c2` on pivot `p` (removing `p` and `¬p`). -/
@[expose] def resolveOn (p : Nat) (c1 c2 : List Nat) : List Nat :=
  c1.filter (· != p) ++ c2.filter (· != litNeg p)

/-- Strip literals certified false by predicate `isRootFalse`. -/
@[expose] def stripFalsified (isRootFalse : Nat → Bool) (c : List Nat) : List Nat :=
  c.filter (fun l => !isRootFalse l)

/-- Tautology detector: `true` iff `c` contains a complementary pair `x` and `litNeg x`. -/
@[expose] def clauseIsTaut (c : List Nat) : Bool :=
  c.any (fun x => c.contains (litNeg x))

/-- Variable `v` does not occur in any clause of `cs`. -/
@[expose] def VarFreshIn (cs : List (List Nat)) (v : Nat) : Prop :=
  ∀ c ∈ cs, ∀ x ∈ c, litVar x ≠ v

/-- Executable Boolean checker for `VarFreshIn`. -/
@[expose] def varFreshInBool (cs : List (List Nat)) (v : Nat) : Bool :=
  cs.all fun c => c.all fun x => litVar x != v

/-- Variable `v` does not occur in any clause of `f : CNF Nat`. -/
@[expose] def VarFreshCnf (f : CNF Nat) (v : Nat) : Prop :=
  VarFreshIn (clausesOfCnf f) v

/-- Convert a list of unit literals into a `Std.Sat.CNF Nat`. -/
@[expose] def unitsCnf (lits : List Nat) : CNF Nat :=
  lits.foldl (fun acc l => acc.add (cnfClause [l])) CNF.empty

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
@[expose] def shiftDownClause (cl : CNF.Clause Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.literals.map fun (v, p) => (v - 1, p))

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
@[expose] def shiftDownCnf (cnf : CNF Nat) : CNF Nat :=
  ⟨cnf.clauses.map shiftDownClause⟩

/-- Every variable occurring in `cnf` is positive (`1`-based DIMACS convention). -/
@[expose] def CnfVarsPos (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1

@[simp] theorem literals_cnfClause (lits : List Nat) :
    (cnfClause lits).literals = lits.map litToLiteral := by simp [cnfClause]

@[simp] theorem mem_cnfClause_iff {lits : List Nat} {lit : Literal Nat} :
    lit ∈ cnfClause lits ↔ litOfLiteral lit ∈ lits := by
  rw [← CNF.Clause.mem_literals_iff, literals_cnfClause, List.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => h ▸ by simpa using hx,
    fun h => ⟨litOfLiteral lit, h, litToLiteral_litOfLiteral lit⟩⟩

theorem clause_sat_cnfClause_iff (α : Nat → Bool) (lits : List Nat) :
    (cnfClause lits).Sat α ↔ ∃ l ∈ lits, α (litVar l) = !(litSign l) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨lit, hmem, heq⟩
    exact ⟨litOfLiteral lit, mem_cnfClause_iff.mp hmem,
      by simpa [litToLiteral, litOfLiteral] using heq⟩
  · rintro ⟨l, hl, heq⟩
    refine ⟨litToLiteral l, ?_, heq⟩
    rw [← CNF.Clause.mem_literals_iff, literals_cnfClause]
    exact List.mem_map_of_mem hl

@[simp] theorem sat_cnfClause_singleton (α : Nat → Bool) (l : Nat) :
    (cnfClause [l]).Sat α ↔ α (litVar l) = !(litSign l) := by
  simp [clause_sat_cnfClause_iff]

@[simp] theorem cnfClause_nil : cnfClause [] = (CNF.Clause.empty : CNF.Clause Nat) :=
  CNF.Clause.ext (by simp)

@[simp] theorem clauseOfCnf_cnfClause (lits : List Nat) :
    clauseOfCnf (cnfClause lits) = lits := by simp [clauseOfCnf, Function.comp_def]

@[simp] theorem cnfClause_clauseOfCnf (c : CNF.Clause Nat) :
    cnfClause (clauseOfCnf c) = c :=
  CNF.Clause.ext (by simp [clauseOfCnf, Function.comp_def])

theorem cnf_sat_cnfOfClauses_iff (α : Nat → Bool) (cs : List (List Nat)) :
    (cnfOfClauses cs).Sat α ↔ ∀ c ∈ cs, (cnfClause c).Sat α := by
  rw [CNF.sat_iff_all_mem_sat]
  simp only [CNF.Internal.mem_iff, cnfOfClauses, List.mem_toArray, List.mem_map]
  constructor
  · intro h c hc; exact h (cnfClause c) ⟨c, hc, rfl⟩
  · rintro h _ ⟨c, hc, rfl⟩; exact h c hc

@[simp] theorem cnfOfClauses_clausesOfCnf (f : CNF Nat) :
    cnfOfClauses (clausesOfCnf f) = f := by
  cases f; simp [cnfOfClauses, clausesOfCnf, Function.comp_def]

@[simp] theorem clausesOfCnf_cnfOfClauses (cs : List (List Nat)) :
    clausesOfCnf (cnfOfClauses cs) = cs := by
  simp [clausesOfCnf, cnfOfClauses, Function.comp_def]

theorem sat_iff_clausesOfCnf (α : Nat → Bool) (f : CNF Nat) :
    f.Sat α ↔ ∀ c ∈ clausesOfCnf f, (cnfClause c).Sat α := by
  have h := cnf_sat_cnfOfClauses_iff α (clausesOfCnf f)
  rwa [cnfOfClauses_clausesOfCnf] at h

theorem entails_mem_clausesOfCnf {f : CNF Nat} {c : List Nat} (hc : c ∈ clausesOfCnf f) :
    f.EntailsClause (cnfClause c) := by
  rw [CNF.entails_clause_def]
  exact fun α hα => (sat_iff_clausesOfCnf α f).mp hα c hc

theorem entails_mem_cnfOfClauses {cs : List (List Nat)} {c : List Nat} (hc : c ∈ cs) :
    (cnfOfClauses cs).EntailsClause (cnfClause c) :=
  entails_mem_clausesOfCnf (by simpa using hc)

theorem sat_cnfClause_litNeg_iff (α : Nat → Bool) (l : Nat) :
    (cnfClause [litNeg l]).Sat α ↔ ¬ (cnfClause [l]).Sat α := by
  simp only [sat_cnfClause_singleton, litVar_litNeg, litSign_litNeg]
  cases α (litVar l) <;> cases litSign l <;> decide

theorem entails_addClause {f : CNF Nat} {c : CNF.Clause Nat}
    (hc : f.EntailsClause c) : f.Entails (f.add c) :=
  CNF.entails_add_of_entails_clause f c hc

theorem entails_addClause_mono {f g : CNF Nat} {c : CNF.Clause Nat}
    (hfg : f.Entails g) (hc : f.EntailsClause c) : f.Entails (g.add c) :=
  CNF.entails_add_iff.mpr ⟨hfg, hc⟩

theorem unsat_of_entails_nil {f : CNF Nat} (h : f.EntailsClause (cnfClause [])) : f.Unsat := by
  rw [cnfClause_nil] at h; exact CNF.unsat_iff_entails_clause_empty.mpr h

theorem mem_dedupLits_iff {y : Nat} {c : List Nat} : y ∈ dedupLits c ↔ y ∈ c := by
  suffices ∀ c z, z ∈ dedupLits c ↔ z ∈ c from this c y
  intro c; induction c with
  | nil => simp [dedupLits]
  | cons x xs ih =>
    intro z; simp only [dedupLits, List.contains_iff_mem]
    by_cases hc : x ∈ dedupLits xs
    · simp only [hc, ↓reduceIte, List.mem_cons]
      exact ⟨fun hz => Or.inr ((ih z).mp hz),
        fun h => (ih z).mpr (h.elim (fun hzx => hzx ▸ (ih x).mp hc) id)⟩
    · simp [hc, ih]

theorem nodup_dedupLits (c : List Nat) : (dedupLits c).Nodup := by
  induction c with
  | nil => simp [dedupLits]
  | cons x xs ih =>
    simp only [dedupLits, List.contains_iff_mem]
    by_cases hc : x ∈ dedupLits xs <;> simp [hc, ih]

theorem entails_dedupLits {f : CNF Nat} {c : List Nat}
    (hc : f.EntailsClause (cnfClause c)) : f.EntailsClause (cnfClause (dedupLits c)) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  obtain ⟨y, hy, hsat⟩ := (clause_sat_cnfClause_iff α c).mp (hc α hα)
  exact (clause_sat_cnfClause_iff α _).mpr ⟨y, mem_dedupLits_iff.mpr hy, hsat⟩

theorem clause_sat_dedup_iff (α : Nat → Bool) (c : List Nat) :
    (cnfClause (dedupLits c)).Sat α ↔ (cnfClause c).Sat α := by
  simp only [clause_sat_cnfClause_iff]
  exact ⟨fun ⟨l, hl, hs⟩ => ⟨l, mem_dedupLits_iff.mp hl, hs⟩,
    fun ⟨l, hl, hs⟩ => ⟨l, mem_dedupLits_iff.mpr hl, hs⟩⟩

theorem entails_swap2 {f : CNF Nat} {a b : Nat}
    (h : f.EntailsClause (cnfClause [a, b])) : f.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨x, hx, hs⟩ := (clause_sat_cnfClause_iff α [a, b]).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  exact (clause_sat_cnfClause_iff α [b, a]).mpr ⟨x, by rcases hx with rfl | rfl <;> simp, hs⟩

theorem entails_resolve {f : CNF Nat} {p : Nat} {c1 c2 : List Nat}
    (h1 : f.EntailsClause (cnfClause c1)) (h2 : f.EntailsClause (cnfClause c2)) :
    f.EntailsClause (cnfClause (resolveOn p c1 c2)) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα; rw [clause_sat_cnfClause_iff]
  by_cases hp : (cnfClause [p]).Sat α
  · obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c2).mp (h2 α hα)
    have hne : l ≠ litNeg p := fun h => by
      subst h; exact (sat_cnfClause_litNeg_iff α p).mp ((sat_cnfClause_singleton α _).mpr hsat) hp
    exact ⟨l, List.mem_append_right _ (List.mem_filter.mpr ⟨hl, by simp [hne]⟩), hsat⟩
  · obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c1).mp (h1 α hα)
    have hne : l ≠ p := fun h => by subst h; exact hp ((sat_cnfClause_singleton α l).mpr hsat)
    exact ⟨l, List.mem_append_left _ (List.mem_filter.mpr ⟨hl, by simp [hne]⟩), hsat⟩

theorem resolveOn_comm_mem (p : Nat) (c1 c2 : List Nat) (x : Nat) :
    x ∈ resolveOn (litNeg p) c2 c1 ↔ x ∈ resolveOn p c1 c2 := by
  simp only [resolveOn, litNeg_litNeg, List.mem_append, List.mem_filter, bne_iff_ne]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

theorem entails_stripFalsified {f : CNF Nat} {isRootFalse : Nat → Bool} {c : List Nat}
    (hc : f.EntailsClause (cnfClause c))
    (hroot : ∀ l ∈ c, isRootFalse l = true → f.EntailsClause (cnfClause [litNeg l])) :
    f.EntailsClause (cnfClause (stripFalsified isRootFalse c)) := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c).mp (hc α hα)
  by_cases hrf : isRootFalse l = true
  · have hneg := CNF.entails_clause_def.mp (hroot l hl hrf) α hα
    exact absurd ((sat_cnfClause_singleton α l).mpr hsat) ((sat_cnfClause_litNeg_iff α l).mp hneg)
  · exact (clause_sat_cnfClause_iff α _).mpr
      ⟨l, by simp [stripFalsified, hl, Bool.eq_false_iff.mpr hrf], hsat⟩

theorem varFreshInBool_iff (cs : List (List Nat)) (v : Nat) :
    varFreshInBool cs v = true ↔ VarFreshIn cs v := by
  simp [varFreshInBool, VarFreshIn, List.all_eq_true, bne_iff_ne]

theorem clauseIsTaut_iff (c : List Nat) :
    clauseIsTaut c = true ↔ ∃ x ∈ c, litNeg x ∈ c := by
  simp [clauseIsTaut, List.any_eq_true]

theorem clauseIsTaut_congr {r1 r2 : List Nat} (h : ∀ x, x ∈ r1 ↔ x ∈ r2) :
    clauseIsTaut r1 = clauseIsTaut r2 := by
  apply Bool.eq_iff_iff.mpr
  simp only [clauseIsTaut_iff]
  constructor <;> rintro ⟨l, hl, hn⟩
  · exact ⟨l, (h l).mp hl, (h (litNeg l)).mp hn⟩
  · exact ⟨l, (h l).mpr hl, (h (litNeg l)).mpr hn⟩

theorem sat_cnfClause_congr {α : Nat → Bool} {c1 c2 : List Nat} (h : ∀ x, x ∈ c1 ↔ x ∈ c2) :
    (cnfClause c1).Sat α ↔ (cnfClause c2).Sat α := by
  simp only [clause_sat_cnfClause_iff]
  constructor <;> rintro ⟨x, hx, hs⟩
  · exact ⟨x, (h x).mp hx, hs⟩
  · exact ⟨x, (h x).mpr hx, hs⟩

theorem cnf_unsat_iff_of_sat_iff {f g : CNF Nat} (h : ∀ α, f.Sat α ↔ g.Sat α) :
    f.Unsat ↔ g.Unsat := by
  simp only [CNF.unsat_iff_not_sat]
  exact ⟨fun hf α hα => hf α ((h α).mpr hα), fun hg α hα => hg α ((h α).mp hα)⟩

theorem entailed_del_equiv {f : CNF Nat} {c : CNF.Clause Nat}
    (hent : f.EntailsClause c) :
    (∀ α : Nat → Bool, (f.add c).Sat α ↔ f.Sat α) ∧ ((f.add c).Unsat ↔ f.Unsat) := by
  have hsat : ∀ α : Nat → Bool, (f.add c).Sat α ↔ f.Sat α := fun α => by
    rw [CNF.sat_add]
    exact ⟨fun h => h.2, fun hf => ⟨CNF.entails_clause_def.mp hent α hf, hf⟩⟩
  exact ⟨hsat, cnf_unsat_iff_of_sat_iff hsat⟩

theorem sat_foldl_cnfClause_iff {α : Type} (f : α → List Nat) (β : Nat → Bool)
    (xs : List α) :
    (xs.foldl (fun acc x => acc.add (cnfClause (f x))) CNF.empty).Sat β ↔
      ∀ x ∈ xs, (cnfClause (f x)).Sat β := by
  suffices ∀ init : CNF Nat,
      (xs.foldl (fun acc x => acc.add (cnfClause (f x))) init).Sat β ↔
        init.Sat β ∧ ∀ x ∈ xs, (cnfClause (f x)).Sat β by
    simpa using this CNF.empty
  induction xs with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons, ih, CNF.sat_add, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨hx, hi⟩, hxs⟩ => ⟨hi, hx, hxs⟩, fun ⟨hi, hx, hxs⟩ => ⟨⟨hx, hi⟩, hxs⟩⟩

theorem sat_unitsCnf_iff (α : Nat → Bool) (lits : List Nat) :
    (unitsCnf lits).Sat α ↔ ∀ l ∈ lits, (cnfClause [l]).Sat α :=
  sat_foldl_cnfClause_iff (fun l => [l]) α lits

theorem cnfVarsPos_empty : CnfVarsPos (CNF.empty : CNF Nat) := by
  intro cl hcl; simp [CNF.empty, CNF.Internal.mem_iff] at hcl

theorem cnfVarsPos_add {cnf : CNF Nat} {cl : CNF.Clause Nat}
    (h1 : CnfVarsPos cnf) (h2 : ∀ lit ∈ cl.literals, 1 ≤ lit.1) :
    CnfVarsPos (cnf.add cl) := by
  intro c hc
  rcases CNF.mem_add.mp hc with rfl | hc'
  · exact h2
  · exact h1 c hc'

theorem shiftDownClause_sat_of_sat {cl : CNF.Clause Nat} {α : Nat → Bool}
    (hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hsat : cl.Sat α) :
    (shiftDownClause cl).Sat (fun v => α (v + 1)) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat ⊢
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := hsat
  have hmem' : (v, p) ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hmem
  have hv1 : 1 ≤ v := hpos (v, p) hmem'
  refine ⟨(v - 1, p), ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, shiftDownClause, CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨(v, p), hmem', rfl⟩
  · simpa [Nat.sub_add_cancel hv1] using heq

theorem shiftDownCnf_unsat {cnf : CNF Nat} (hpos : CnfVarsPos cnf)
    (hu : (shiftDownCnf cnf).Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  apply hu (fun v => α (v + 1))
  rw [CNF.sat_iff_all_mem_sat] at hα ⊢
  intro cl' hcl'
  rw [CNF.Internal.mem_iff, shiftDownCnf, Array.mem_map] at hcl'
  obtain ⟨cl, hcl, rfl⟩ := hcl'
  have hmem : cl ∈ cnf := CNF.Internal.mem_iff.mpr hcl
  exact shiftDownClause_sat_of_sat (hpos cl hmem) (hα cl hmem)

theorem shiftDownCnf_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    shiftDownCnf (cnf.add cl) = (shiftDownCnf cnf).add (shiftDownClause cl) := by
  simp [shiftDownCnf, CNF.add]

theorem shiftDownCnf_entails_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).Entails (shiftDownCnf cnf) := by
  rw [shiftDownCnf_add, CNF.entails_def]
  intro α hα; exact (CNF.sat_add.mp hα).2

theorem shiftDownCnf_entails_added (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).EntailsClause (shiftDownClause cl) := by
  rw [shiftDownCnf_add, CNF.entails_clause_def]
  intro α hα; exact (CNF.sat_add.mp hα).1

theorem shiftDownClause_kissatLits (lits : List Nat) :
    shiftDownClause (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral)) =
      cnfClause lits := by
  apply CNF.Clause.ext
  simp [shiftDownClause, cnfClause, kissatLitToDimacsLiteral, litToLiteral, Function.comp_def]

/-! ## 3. `Array Bool ↔ (Nat → Bool)` evaluation and padding bridges -/

/-- Set `arr[idx] := val`, padding with `pad` if `idx ≥ arr.size`. -/
@[expose] def arraySetPad {α : Type} (arr : Array α) (idx : Nat) (val pad : α) : Array α :=
  if h : idx < arr.size then
    arr.set idx val h
  else
    let padded := arr ++ Array.replicate (idx + 1 - arr.size) pad
    padded.set! idx val

/-- Lookup variable value in a `Bool` model array (defaulting out-of-range to `false`). -/
@[expose, inline] def evalVar (σ : Array Bool) (v : Nat) : Bool :=
  σ[v]?.getD false

/-- Evaluate a Kissat literal under model `σ`. -/
@[expose, inline] def evalLit (σ : Array Bool) (l : Nat) : Bool :=
  evalVar σ (litVar l) != litSign l

/-- Evaluate a Kissat clause (disjunction of literals) under model `σ`. -/
@[expose] def evalClause (σ : Array Bool) (c : List Nat) : Bool :=
  c.any (evalLit σ)

/-- Evaluate a list of Kissat clauses (conjunction of clauses) under model `σ`. -/
@[expose] def evalCnf (σ : Array Bool) (cs : List (List Nat)) : Bool :=
  cs.all (evalClause σ)

/-- Executable total model checker on `Std.Sat.CNF Nat`. -/
@[expose] def checkModel (cnf : CNF Nat) (σ : Array Bool) : Bool :=
  cnf.eval (evalVar σ)

/-- Evaluate a Kissat literal under a total Boolean assignment `α : Nat → Bool`. -/
@[expose, inline] def evalLitVal (α : Nat → Bool) (l : Nat) : Bool :=
  α (litVar l) != litSign l

/-- Evaluate a clause (disjunction of Kissat literals) under `α : Nat → Bool`. -/
@[expose] def clauseEvalVal (α : Nat → Bool) (c : List Nat) : Bool :=
  c.any (evalLitVal α)

/-- Evaluate a clause list (conjunction of clauses) under `α : Nat → Bool`. -/
@[expose] def cnfEvalVal (α : Nat → Bool) (cs : List (List Nat)) : Bool :=
  cs.all (clauseEvalVal α)

/-- Point update `α[v ↦ val]` on a total Boolean assignment `α : Nat → Bool`. -/
@[expose, inline] def substUpdate (α : Nat → Bool) (v : Nat) (val : Bool) : Nat → Bool :=
  fun x => if x == v then val else α x

theorem getElem?_setIfInBounds {α : Type} (xs : Array α) (i j : Nat) (v : α) :
    (xs.setIfInBounds i v)[j]? = if i < xs.size ∧ j = i then some v else xs[j]? := by
  by_cases hi : i < xs.size
  · by_cases hij : j = i
    · subst hij; simp [hi]
    · simp only [hi, hij, and_false, ↓reduceIte, Array.getElem?_setIfInBounds, Ne.symm hij]
  · simp [hi, Array.setIfInBounds]

theorem arraySetPad_getD {α : Type} (arr : Array α) (idx : Nat) (val pad : α) (j : Nat) :
    (arraySetPad arr idx val pad).getD j pad = if j = idx then val else arr.getD j pad := by
  unfold arraySetPad
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  split
  · rename_i hlt
    by_cases hj : j = idx
    · subst hj; simp [hlt]
    · simp only [hj, ↓reduceIte, Array.getElem?_set]
      split
      · exact absurd (Eq.symm ‹_›) hj
      · rfl
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have hps : (arr ++ Array.replicate (idx + 1 - arr.size) pad).size = idx + 1 := by
      simp [Array.size_append, Array.size_replicate]; omega
    by_cases hj : j = idx
    · subst hj; simp [hps]
    · have hij : idx ≠ j := Ne.symm hj
      simp only [hj, hij, ↓reduceIte]
      by_cases hja : j < arr.size
      · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hja]
        simp [hja, Array.getElem_append_left]
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hja)]
        by_cases hjp : j < (arr ++ Array.replicate (idx + 1 - arr.size) pad).size
        · rw [Array.getElem?_eq_getElem hjp]
          simp [Array.getElem_append_right (Nat.le_of_not_lt hja), Array.getElem_replicate]
        · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hjp)]

theorem evalVar_arraySetPad (σ : Array Bool) (v : Nat) (val : Bool) :
    evalVar (arraySetPad σ v val false) = substUpdate (evalVar σ) v val := by
  funext w
  simp only [evalVar, substUpdate, beq_iff_eq, ← Array.getD_eq_getD_getElem?]
  exact arraySetPad_getD σ v val false w

theorem evalLitVal_iff (α : Nat → Bool) (l : Nat) :
    evalLitVal α l = true ↔ (cnfClause [l]).Sat α := by
  simp only [evalLitVal, sat_cnfClause_singleton]
  cases α (litVar l) <;> cases litSign l <;> decide

@[simp] theorem evalLitVal_litNeg (α : Nat → Bool) (l : Nat) :
    evalLitVal α (litNeg l) = !(evalLitVal α l) := by
  simp only [evalLitVal, litVar_litNeg, litSign_litNeg]
  cases α (litVar l) <;> cases litSign l <;> decide

@[simp] theorem evalLitVal_mkLit (α : Nat → Bool) (v : Nat) (pol : Bool) :
    evalLitVal α (mkLit v pol) = (α v == pol) := by
  simp only [evalLitVal, litVar_mkLit, litSign_mkLit]
  cases α v <;> cases pol <;> decide

theorem evalLitVal_evalVar (σ : Array Bool) (l : Nat) :
    evalLitVal (evalVar σ) l = evalLit σ l := rfl

theorem evalLit_iff (σ : Array Bool) (l : Nat) :
    evalLit σ l = true ↔ (cnfClause [l]).Sat (evalVar σ) :=
  evalLitVal_iff (evalVar σ) l

theorem clauseEvalVal_iff (α : Nat → Bool) (c : List Nat) :
    clauseEvalVal α c = true ↔ (cnfClause c).Sat α := by
  rw [clauseEvalVal, List.any_eq_true, clause_sat_cnfClause_iff]
  simp only [evalLitVal_iff, sat_cnfClause_singleton]

theorem cnfEvalVal_iff (α : Nat → Bool) (cs : List (List Nat)) :
    cnfEvalVal α cs = true ↔ (cnfOfClauses cs).Sat α := by
  simp only [cnfEvalVal, List.all_eq_true, clauseEvalVal_iff, cnf_sat_cnfOfClauses_iff]

theorem evalClause_iff (σ : Array Bool) (c : List Nat) :
    evalClause σ c = true ↔ (cnfClause c).Sat (evalVar σ) :=
  clauseEvalVal_iff (evalVar σ) c

theorem evalCnf_iff (σ : Array Bool) (cs : List (List Nat)) :
    evalCnf σ cs = true ↔ (cnfOfClauses cs).Sat (evalVar σ) :=
  cnfEvalVal_iff (evalVar σ) cs

theorem checkModel_iff_sat (cnf : CNF Nat) (σ : Array Bool) :
    checkModel cnf σ = true ↔ cnf.Sat (evalVar σ) :=
  (CNF.sat_def (evalVar σ) cnf).symm

theorem checkModel_iff_evalCnf (cnf : CNF Nat) (σ : Array Bool) :
    evalCnf σ (clausesOfCnf cnf) = checkModel cnf σ := by
  rw [Bool.eq_iff_iff, evalCnf_iff, checkModel_iff_sat, CNF.sat_iff_all_mem_sat,
    CNF.sat_iff_all_mem_sat]
  simp only [CNF.Internal.mem_iff, cnfOfClauses, clausesOfCnf, List.mem_toArray,
    List.mem_map, Array.mem_toList_iff]
  refine ⟨fun h c hc => ?_, fun h _ ⟨lits, ⟨c, hc, h1⟩, h2⟩ => ?_⟩
  · simpa [cnfClause_clauseOfCnf] using h c ⟨clauseOfCnf c, ⟨c, hc, rfl⟩, cnfClause_clauseOfCnf c⟩
  · rw [← h2, ← h1, cnfClause_clauseOfCnf]; exact h c hc

theorem checkModel_cnfOfClauses_eq_evalCnf (cs : List (List Nat)) (σ : Array Bool) :
    checkModel (cnfOfClauses cs) σ = evalCnf σ cs := by
  rw [← checkModel_iff_evalCnf, clausesOfCnf_cnfOfClauses]

theorem checkModel_sat {cnf : CNF Nat} {σ : Array Bool}
    (h : checkModel cnf σ = true) : ∃ α, cnf.Sat α :=
  ⟨evalVar σ, (checkModel_iff_sat cnf σ).mp h⟩

theorem checkModel_sound {cnf : CNF Nat} {σ : Array Bool}
    (h : checkModel cnf σ = true) : ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
  obtain ⟨α, hα⟩ := checkModel_sat h
  exact ⟨fun hu => CNF.unsat_iff_not_sat.mp hu α hα, α, hα⟩

theorem checkModel_sound_of_parse {parse : List UInt8 → Option (CNF Nat)}
    {bs : List UInt8} {cnf : CNF Nat} {σ : Array Bool}
    (_hp : parse bs = some cnf) (h : checkModel cnf σ = true) :
    ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α :=
  checkModel_sound h

@[simp] theorem substUpdate_self (α : Nat → Bool) (v : Nat) (val : Bool) :
    substUpdate α v val v = val := by
  simp [substUpdate]

@[simp] theorem substUpdate_ne (α : Nat → Bool) {v w : Nat} (val : Bool) (hne : w ≠ v) :
    substUpdate α v val w = α w := by
  simp [substUpdate, hne]

theorem evalLitVal_substUpdate_ne (α : Nat → Bool) {v l : Nat} (val : Bool)
    (hne : litVar l ≠ v) :
    evalLitVal (substUpdate α v val) l = evalLitVal α l := by
  simp [evalLitVal, substUpdate_ne α val hne]

theorem clause_sat_of_agree {α β : Nat → Bool} {c : List Nat}
    (h : ∀ x ∈ c, evalLitVal α x = evalLitVal β x) :
    (cnfClause c).Sat α ↔ (cnfClause c).Sat β := by
  simp only [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hs⟩ => ⟨x, hx, h x hx ▸ hs⟩, fun ⟨x, hx, hs⟩ => ⟨x, hx, (h x hx).symm ▸ hs⟩⟩

theorem clause_sat_substUpdate_fresh {α : Nat → Bool} {c : List Nat} {v : Nat} (val : Bool)
    (hf : ∀ x ∈ c, litVar x ≠ v) :
    (cnfClause c).Sat (substUpdate α v val) ↔ (cnfClause c).Sat α :=
  clause_sat_of_agree fun x hx => evalLitVal_substUpdate_ne α val (hf x hx)

theorem clauseIsTaut_sat {c : List Nat} (ht : clauseIsTaut c = true) (α : Nat → Bool) :
    (cnfClause c).Sat α := by
  obtain ⟨x, hx, hnx⟩ := (clauseIsTaut_iff c).mp ht
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  cases h : evalLitVal α x
  · exact ⟨litNeg x, hnx, by simp [evalLitVal_litNeg, h]⟩
  · exact ⟨x, hx, h⟩

/-! ## 4. Shared `List` / `Nodup` / pigeonhole / pass combinators -/

theorem dedupLits_ne_nil {c : List Nat} (hc : c ≠ []) : dedupLits c ≠ [] := by
  cases c with
  | nil => exact absurd rfl hc
  | cons _ _ =>
    simp only [dedupLits]
    split
    · rename_i hmem; exact fun heq => by simp [heq] at hmem
    · simp

theorem filter_nodup_singleton_le_one {P : Nat → Bool} {np : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, P x = true → x = np) → (xs.filter P).length ≤ 1
  | [], _, _ => by simp
  | x :: xs, hnd, hall => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    by_cases hpx : P x = true
    · simp only [hpx, ↓reduceIte, List.length_cons]
      have hxeq : x = np := hall x (by simp) hpx
      have hnil : xs.filter P = [] := List.eq_nil_iff_forall_not_mem.mpr fun y hy => by
        rw [List.mem_filter] at hy
        exact hnd.1 ((hall y (by simp [hy.1]) hy.2).trans hxeq.symm ▸ hy.1)
      simp [hnil]
    · simp only [Bool.eq_false_iff.mpr hpx, Bool.false_eq_true, ↓reduceIte]
      exact filter_nodup_singleton_le_one hnd.2 fun y hy => hall y (List.mem_cons_of_mem _ hy)

theorem exists_ne_of_filter_gt_one {P : Nat → Bool} {np : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hgt : 1 < (xs.filter P).length) : ∃ q ∈ xs, P q = true ∧ q ≠ np :=
  Classical.byContradiction fun hno =>
    absurd (filter_nodup_singleton_le_one hnd fun q hq hpq =>
      Classical.byContradiction fun hne => hno ⟨q, hq, hpq, hne⟩) (by omega)

theorem mem_two_filter_length_gt_one {P : Nat → Bool} {u y : Nat}
    (huy : u ≠ y) (hpu : P u = true) (hpy : P y = true) :
    ∀ {xs : List Nat}, xs.Nodup → u ∈ xs → y ∈ xs → 1 < (xs.filter P).length
  | [], _, hu, _ => by cases hu
  | x :: xs, hnd, hu, hy => by
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at hu hy
    simp only [List.filter_cons]
    by_cases hpx : P x = true
    · simp only [hpx, ↓reduceIte, List.length_cons]
      rcases hu with rfl | hu' <;> rcases hy with rfl | hy'
      · exact absurd rfl huy
      · exact Nat.succ_lt_succ (List.length_pos_of_mem (List.mem_filter.mpr ⟨hy', hpy⟩))
      · exact Nat.succ_lt_succ (List.length_pos_of_mem (List.mem_filter.mpr ⟨hu', hpu⟩))
      · have := mem_two_filter_length_gt_one huy hpu hpy hnd.2 hu' hy'; omega
    · simp only [Bool.eq_false_iff.mpr hpx, Bool.false_eq_true, ↓reduceIte]
      exact mem_two_filter_length_gt_one huy hpu hpy hnd.2
        (hu.elim (fun h => by subst h; simp [hpu] at hpx) id)
        (hy.elim (fun h => by subst h; simp [hpy] at hpx) id)

theorem filter_nodup_drop_one {S : List Nat} (hnodup : S.Nodup) {u : Nat} (hu : u ∈ S)
    {p p' : Nat → Bool} (hpu : p u = true) (hp'u : p' u = false)
    (heq : ∀ v ∈ S, v ≠ u → p v = p' v) :
    (S.filter p).length = (S.filter p').length + 1 := by
  induction S with
  | nil => cases hu
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp hu with rfl | hxs
    · have hfx : xs.filter p = xs.filter p' :=
        List.filter_congr fun v hv => heq v (List.mem_cons_of_mem _ hv) (fun h => hnd.1 (h ▸ hv))
      simp [hpu, hp'u, hfx]
    · have heqx : p x = p' x := heq x (by simp) (fun h => hnd.1 (h ▸ hxs))
      have ih_res := ih hnd.2 hxs (fun v hv => heq v (List.mem_cons_of_mem _ hv))
      cases hpx : p' x
      · have hpx1 : p x = false := by rw [heqx, hpx]
        simp [hpx, hpx1, ih_res]
      · have hpx1 : p x = true := by rw [heqx, hpx]
        simp [hpx, hpx1, ih_res]

theorem nodup_filter_length_one {S : List Nat} (hnodup : S.Nodup) {u : Nat} (hu : u ∈ S)
    {p : Nat → Bool} (hpu : p u = true) (hlen : (S.filter p).length ≤ 1) :
    ∀ v ∈ S, p v = true → v = u :=
  fun v hv hpv => Classical.byContradiction fun hne =>
    have hgt : 1 < (S.filter p).length :=
      mem_two_filter_length_gt_one (Ne.symm hne) hpu hpv hnodup hu hv
    by omega

theorem list_map_nodup_of_getElem {l : List Nat}
    (h : ∀ i j (hi : i < l.length) (hj : j < l.length), litVar l[i] = litVar l[j] → i = j) :
    (l.map litVar).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨b, hb, hvar⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
      have hk1 : k + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hk
      have heq := h 0 (k + 1) (by simp) hk1 (by simpa using hvar.symm)
      omega
    · refine ih fun i j hi hj hvar => ?_
      have hi1 : i + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hi
      have hj1 : j + 1 < (a :: as).length := by simpa using Nat.succ_lt_succ hj
      have heq := h (i + 1) (j + 1) hi1 hj1 (by simpa using hvar)
      omega

theorem takeWhile_props {α : Type} (p : α → Bool) (xs : List α) :
    (xs.takeWhile p).length ≤ xs.length ∧
    ∀ (i : Nat) (hi : i < (xs.takeWhile p).length),
      ∃ (_hxi : i < xs.length), (xs.takeWhile p)[i] = xs[i] ∧ p xs[i] = true := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.takeWhile_cons]
    by_cases hp : p y = true
    · simp only [hp, ↓reduceIte, List.length_cons]
      refine ⟨Nat.succ_le_succ ih.1, fun i hi => ?_⟩
      cases i with
      | zero => exact ⟨Nat.zero_lt_succ _, rfl, hp⟩
      | succ k =>
        obtain ⟨hk, heq, hpk⟩ := ih.2 k (Nat.lt_of_succ_lt_succ hi)
        exact ⟨Nat.succ_lt_succ hk, heq, hpk⟩
    · simp [Bool.eq_false_iff.mpr hp]

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_of_inj hnd.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    have hxy := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self heq
    exact hnd.1 (hxy ▸ hy)

theorem nodup_length_le_of_lt :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, xs, _, hlt => by
    cases xs with
    | nil => simp
    | cons x _ => have := hlt x (by simp); omega
  | n + 1, xs, hnd, hlt => by
    have hnd' : (xs.erase n).Nodup := hnd.erase n
    have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
      have hne : y ≠ n := fun heq => by subst heq; exact (List.Nodup.not_mem_erase hnd) hy
      have := hlt y (List.mem_of_mem_erase hy); omega
    have hle := nodup_length_le_of_lt n (xs.erase n) hnd' hlt'
    have hlen : xs.length ≤ (xs.erase n).length + 1 := by
      by_cases hmem : n ∈ xs
      · rw [List.length_erase_of_mem hmem]; have := List.length_pos_of_mem hmem; omega
      · rw [List.erase_of_not_mem hmem]; omega
    omega

theorem nodup_lt_of_missing {n v : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) (hv : v < n) (hnot : v ∉ xs) :
    xs.length < n := by
  have h := nodup_length_le_of_lt n (v :: xs) (List.nodup_cons.mpr ⟨hnot, hnd⟩)
    (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hv) (hlt x))
  simp only [List.length_cons] at h
  omega

theorem inj_lt_of_missing {k n v : Nat} (f : Nat → Nat)
    (hinj : ∀ i j, i < k → j < k → f i = f j → i = j)
    (hlt : ∀ i < k, f i < n) (hv : v < n) (hmiss : ∀ i < k, f i ≠ v) : k < n := by
  let xs := (List.range k).map f
  have hlen : xs.length = k := by simp [xs]
  have hnd : xs.Nodup :=
    nodup_map_of_inj List.nodup_range fun i hi j hj heq =>
      hinj i j (List.mem_range.mp hi) (List.mem_range.mp hj) heq
  have hmem : ∀ x ∈ xs, x < n := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hlt i (List.mem_range.mp hi)
  have hnot : v ∉ xs := fun hx => by
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hx; exact hmiss i (List.mem_range.mp hi) heq
  rw [← hlen]; exact nodup_lt_of_missing hnd hmem hv hnot

theorem le_of_surj_range1 {L k : Nat} (g : Nat → Nat)
    (hsurj : ∀ x, 1 ≤ x → x ≤ L → ∃ i < k, g i = x) : L ≤ k := by
  let ys := (List.range L).map (fun x => x + 1)
  have hsub : ∀ y ∈ ys, ∃ i < k, g i = y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxlt := List.mem_range.mp hx
    exact hsurj (x + 1) (by omega) (by omega)
  have hnd : ys.Nodup := nodup_map_of_inj List.nodup_range fun a _ b _ h => by omega
  have hlen := nodup_length_le_of_lt k
    (ys.map fun y => (List.range k).findIdx (fun i => g i == y))
    (nodup_map_of_inj hnd fun a ha b hb heq => by
      obtain ⟨ia, hia, hga⟩ := hsub a ha
      obtain ⟨ib, hib, hgb⟩ := hsub b hb
      have hfa : (List.range k).findIdx (fun i => g i == a) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ia, List.mem_range.mpr hia, by simp [hga]⟩
      have hfb : (List.range k).findIdx (fun i => g i == b) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ib, List.mem_range.mpr hib, by simp [hgb]⟩
      have hpa := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == a) (w := hfa)
      have hpb := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == b) (w := hfb)
      simp only [List.getElem_range, beq_iff_eq] at hpa hpb
      rw [heq] at hpa; exact hpa.symm.trans hpb)
    (fun idx hidx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hidx
      obtain ⟨i, hi, hgi⟩ := hsub y hy
      have hlt : (List.range k).findIdx (fun j => g j == y) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨i, List.mem_range.mpr hi, by simp [hgi]⟩
      rwa [List.length_range] at hlt)
  simpa [ys] using hlen

theorem mem_or_eq_of_mem {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {x y : α}
    (hy : y ∈ xs) : y = x ∨ y ∈ xs.erase x := by
  by_cases h : y == x
  · exact Or.inl (beq_iff_eq.mp h)
  · exact Or.inr ((List.mem_erase_of_ne (fun he => h (beq_iff_eq.mpr he))).mpr hy)

/-- Generic single-pass clause transformation preserving `kept.reverse ++ todo` equivalence. -/
@[expose] def clauseTransformPassAux (step : List (List Nat) → List Nat → List Nat) :
    List (List Nat) → List (List Nat) → List (List Nat)
  | kept, [] => kept.reverse
  | kept, c :: rest =>
    clauseTransformPassAux step (step (kept ++ rest) c :: kept) rest

theorem clauseTransformPassAux_sat_iff (step : List (List Nat) → List Nat → List Nat)
    (hstep : ∀ α c others, (cnfOfClauses others).Sat α →
      ((cnfClause (step others c)).Sat α ↔ (cnfClause c).Sat α))
    (α : Nat → Bool) :
    ∀ (todo kept : List (List Nat)),
      (cnfOfClauses (clauseTransformPassAux step kept todo)).Sat α ↔
        (cnfOfClauses (kept.reverse ++ todo)).Sat α
  | [], kept => by simp [clauseTransformPassAux]
  | c :: rest, kept => by
    have ih := clauseTransformPassAux_sat_iff step hstep α rest (step (kept ++ rest) c :: kept)
    rw [clauseTransformPassAux, ih]
    simp only [cnf_sat_cnfOfClauses_iff, List.mem_append, List.mem_cons, List.mem_reverse]
    have hkr_iff : (cnfOfClauses (kept ++ rest)).Sat α ↔
        (∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α) := by
      rw [cnf_sat_cnfOfClauses_iff]; simp [List.mem_append]
    constructor
    · intro h
      have hkr : ∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α := fun d hd =>
        h d (hd.elim (fun hk => Or.inl (Or.inr hk)) Or.inr)
      intro d hd
      rcases hd with hk | hdc | hr
      · exact hkr d (Or.inl hk)
      · rw [hdc]
        exact (hstep α c (kept ++ rest) (hkr_iff.mpr hkr)).mp (h _ (Or.inl (Or.inl rfl)))
      · exact hkr d (Or.inr hr)
    · intro h
      have hkr : ∀ d, d ∈ kept ∨ d ∈ rest → (cnfClause d).Sat α := fun d hd =>
        h d (hd.elim Or.inl (fun hr => Or.inr (Or.inr hr)))
      intro d hd
      rcases hd with (hdc | hk) | hr
      · rw [hdc]
        exact (hstep α c (kept ++ rest) (hkr_iff.mpr hkr)).mpr (h _ (Or.inr (Or.inl rfl)))
      · exact hkr d (Or.inl hk)
      · exact hkr d (Or.inr hr)

end LeanQbe.T.Examples.Kissat.Ref
