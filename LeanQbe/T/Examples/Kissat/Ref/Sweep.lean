/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Vivify
public import LeanQbe.T.Examples.Kissat.Ref.Eliminate
public import LeanQbe.T.Examples.Kissat.Ref.Factor
public import LeanQbe.T.Examples.Kissat.Ref.Collect
public import LeanQbe.T.Examples.Kissat.Ref.Cdcl

/-!
# Pure Lean Layer-A UNSAT Soundness Theory for Feature-Complete Kissat (Part 1)

Pure Lean (`Std.Sat.CNF Nat`, zero `Kraken.Mem` or `Kraken.Separation` imports) UNSAT-only
compositional soundness framework for Stage 4 (`D-Full`) feature-complete Kissat:

1. **`VarsBounded`, `ExtUnsatSound`, & DIMACS Initialization**:
   `ExtUnsatSound F0 mv_cur F_cur` (`VarsBounded mv_cur F_cur ∧ ((cnfOfClauses F_cur).Unsat →
   F0.Unsat)`), initialized from 0-based or 1-based DIMACS formulas (including parametric
   `parseDimacs` bridges), plus empty-clause & CDCL refutation.
2. **Arbitrary Clause Deletion / Filtering (`List.Sublist` / `deleteIdx` / `erase` / `filter`)**:
   one-line UNSAT soundness with zero SAT model-reconstruction side conditions covering
   `reduce`, satisfied-clause GC, forward subsumption deletion, BIG transitive reduction
   (`transitive.c`), BCE deletion, pure-literal deletion, and BVE/Gate-BVE pivot deletion.
3. **Entailed Clause Addition & Inprocessing Rules**:
   unified `EntailsClause` addition & replacement covering 1UIP, OTFS, eager subsumption, SSR,
   vivification, failed-literal probing, **Hyper-Binary Resolution (`HBR`)**, **Gate Congruence
   Closure (`congruence.c`: Equiv / AND / ITE / XOR)**, **Bounded SAT Sweeping (`sweep.c`)**,
   and **BVE / Gate-BVE** resolvents.
4. **BIG SCC Substitution (`substitute.c`) & Fresh-Variable BVA (`factor.c`)**:
   `substMapClauses` simultaneous SCC substitution, `BinReach` SCC contradiction refutation, and
   `mv_cur ↦ mv_cur + 1` fresh-variable BVA factoring.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Variable bounds, `ExtUnsatSound`, and DIMACS initialization -/

/-- Every literal occurring in any clause of `F` has variable index `< mv`. -/
@[expose] def VarsBounded (mv : Nat) (F : List (List Nat)) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, litVar l < mv

/-- Executable Boolean checker for `VarsBounded`. -/
@[expose] def varsBoundedBool (mv : Nat) (F : List (List Nat)) : Bool :=
  F.all fun c => c.all fun l => decide (litVar l < mv)

theorem varsBoundedBool_iff (mv : Nat) (F : List (List Nat)) :
    varsBoundedBool mv F = true ↔ VarsBounded mv F := by
  simp [varsBoundedBool, VarsBounded, List.all_eq_true]

theorem VarsBounded.mono {mv1 mv2 : Nat} {F : List (List Nat)} (hle : mv1 ≤ mv2)
    (hb : VarsBounded mv1 F) : VarsBounded mv2 F :=
  fun c hc l hl => Nat.lt_of_lt_of_le (hb c hc l hl) hle

theorem VarsBounded.to_varFreshIn {mv z : Nat} {F : List (List Nat)} (hle : mv ≤ z)
    (hb : VarsBounded mv F) : VarFreshIn F z := by
  intro c hc x hx hv
  have hlt := hb c hc x hx
  omega

theorem varsBounded_subset {mv : Nat} {F1 F2 : List (List Nat)}
    (hsub : ∀ c ∈ F1, c ∈ F2) (hb : VarsBounded mv F2) : VarsBounded mv F1 :=
  fun c hc l hl => hb c (hsub c hc) l hl

theorem varsBounded_dedupLits {mv : Nat} {c : List Nat}
    (hb : ∀ l ∈ c, litVar l < mv) : ∀ l ∈ dedupLits c, litVar l < mv :=
  fun l hl => hb l (mem_dedupLits_iff.mp hl)

theorem varsBounded_resolveOn {mv : Nat} {p : Nat} {c d : List Nat}
    (hc : ∀ l ∈ c, litVar l < mv) (hd : ∀ l ∈ d, litVar l < mv) :
    ∀ l ∈ resolveOn p c d, litVar l < mv := by
  intro l hl
  unfold resolveOn at hl
  rcases List.mem_append.mp hl with h1 | h2
  · exact hc l (List.mem_filter.mp h1).1
  · exact hd l (List.mem_filter.mp h2).1

/-- 0-based `CNF Nat` variable bound: every variable occurring in `cnf` is `< mv`. -/
@[expose] def DimacsVarsBounded0 (mv : Nat) (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, lit.1 < mv

/-- 1-based DIMACS `CNF Nat` variable bound (`1 ≤ v ≤ mv`). -/
@[expose] def DimacsVarsBounded (mv : Nat) (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
@[expose] def shiftDimacsClause (cl : CNF.Clause Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.literals.map fun (v, p) => (v - 1, p))

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
@[expose] def shiftDimacsCnf (cnf : CNF Nat) : CNF Nat :=
  ⟨cnf.clauses.map shiftDimacsClause⟩

theorem shiftDimacsClause_sat_of_sat {cl : CNF.Clause Nat} {α : Nat → Bool}
    (hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hsat : cl.Sat α) :
    (shiftDimacsClause cl).Sat (fun v => α (v + 1)) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat ⊢
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := hsat
  have hmem' : (v, p) ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hmem
  have hv1 : 1 ≤ v := hpos (v, p) hmem'
  refine ⟨(v - 1, p), ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, shiftDimacsClause, CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨(v, p), hmem', rfl⟩
  · simpa [Nat.sub_add_cancel hv1] using heq

theorem shiftDimacsCnf_unsat {cnf : CNF Nat}
    (hpos : ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1)
    (hu : (shiftDimacsCnf cnf).Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  apply hu (fun v => α (v + 1))
  rw [CNF.sat_iff_all_mem_sat] at hα ⊢
  intro cl' hcl'
  rw [CNF.Internal.mem_iff, shiftDimacsCnf, Array.mem_map] at hcl'
  obtain ⟨cl, hcl, rfl⟩ := hcl'
  have hmem : cl ∈ cnf := CNF.Internal.mem_iff.mpr hcl
  exact shiftDimacsClause_sat_of_sat (hpos cl hmem) (hα cl hmem)

theorem varsBounded_clausesOfCnf_of0 {mv : Nat} {cnf : CNF Nat}
    (hb : DimacsVarsBounded0 mv cnf) : VarsBounded mv (clausesOfCnf cnf) := by
  intro c hc l hl
  rw [clausesOfCnf, List.mem_map] at hc
  obtain ⟨cl, hcl, rfl⟩ := hc
  have hcl_mem : cl ∈ cnf := CNF.Internal.mem_iff.mpr (Array.mem_toList_iff.mp hcl)
  have hl' : litToLiteral l ∈ cnfClause (clauseOfCnf cl) :=
    mem_cnfClause_iff.mpr (by simpa using hl)
  rw [cnfClause_clauseOfCnf] at hl'
  have hm := CNF.Clause.mem_literals_iff.mpr hl'
  have hlt := hb cl hcl_mem (litToLiteral l) hm
  simpa [litToLiteral] using hlt

theorem varsBounded_shiftDimacsCnf {mv : Nat} {cnf : CNF Nat}
    (hb : DimacsVarsBounded mv cnf) :
    VarsBounded mv (clausesOfCnf (shiftDimacsCnf cnf)) := by
  apply varsBounded_clausesOfCnf_of0
  intro cl' hcl' lit hlit
  rw [CNF.Internal.mem_iff, shiftDimacsCnf, Array.mem_map] at hcl'
  obtain ⟨cl, hcl, rfl⟩ := hcl'
  have hcl_mem : cl ∈ cnf := CNF.Internal.mem_iff.mpr hcl
  rw [shiftDimacsClause, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
  obtain ⟨⟨v, p⟩, hvp, heq⟩ := hlit
  have hvp_b := hb cl hcl_mem (v, p) hvp
  cases heq
  dsimp only
  omega

/-- Pure Layer-A UNSAT soundness & variable-bound invariant for Stage 4 feature-complete
inprocessing: all literals in `F_cur` have variable `< mv_cur`, and unsatisfiability of `F_cur`
implies unsatisfiability of the original parsed formula `F0`. -/
@[expose] def ExtUnsatSound (F0 : CNF Nat) (mv_cur : Nat) (F_cur : List (List Nat)) : Prop :=
  VarsBounded mv_cur F_cur ∧ ((cnfOfClauses F_cur).Unsat → F0.Unsat)

theorem extUnsatSound_init {F0 : CNF Nat} {mv : Nat} (hb : DimacsVarsBounded0 mv F0) :
    ExtUnsatSound F0 mv (clausesOfCnf F0) :=
  ⟨varsBounded_clausesOfCnf_of0 hb, fun hu => by simpa [cnfOfClauses_clausesOfCnf] using hu⟩

theorem extUnsatSound_init_shift {F0 : CNF Nat} {mv : Nat} (hb : DimacsVarsBounded mv F0) :
    ExtUnsatSound F0 mv (clausesOfCnf (shiftDimacsCnf F0)) :=
  ⟨varsBounded_shiftDimacsCnf hb, fun hu => by
    rw [cnfOfClauses_clausesOfCnf] at hu
    exact shiftDimacsCnf_unsat (fun cl hcl lit hlit => (hb cl hcl lit hlit).1) hu⟩

/-- Parametric parser bridge initializing `ExtUnsatSound` from any 0-based `parseDimacs`. -/
theorem extUnsatSound_init_of_parse {parse : List UInt8 → Option (CNF Nat)}
    {bs : List UInt8} {F0 : CNF Nat} {mv : Nat}
    (_hp : parse bs = some F0) (hb : DimacsVarsBounded0 mv F0) :
    ExtUnsatSound F0 mv (clausesOfCnf F0) :=
  extUnsatSound_init hb

/-- Parametric parser bridge initializing `ExtUnsatSound` from any 1-based DIMACS parser. -/
theorem extUnsatSound_shift_of_parse {parse : List UInt8 → Option (CNF Nat)}
    {bs : List UInt8} {F0 : CNF Nat} {mv : Nat}
    (_hp : parse bs = some F0) (hb : DimacsVarsBounded mv F0) :
    ExtUnsatSound F0 mv (clausesOfCnf (shiftDimacsCnf F0)) :=
  extUnsatSound_init_shift hb

/-- Empty-clause refutation lifts directly to `F0.Unsat`. -/
theorem extUnsatSound_unsat_of_nil {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (hnil : [] ∈ F_cur) : F0.Unsat := by
  apply hs.2
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h := (cnf_sat_cnfOfClauses_iff α F_cur).mp hα [] hnil
  obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff α []).mp h
  cases hm

/-- Closing via `Core.cdclSolve = .unsat` lifts directly to `F0.Unsat`. -/
theorem extUnsatSound_unsat_of_cdcl {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {fuel : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hres : cdclSolve fuel (cnfOfClauses F_cur) = .unsat) : F0.Unsat :=
  hs.2 (cdclSolve_unsat_sound hres)

theorem extUnsatSound_widen_vars {F0 : CNF Nat} {mv1 mv2 : Nat} {F_cur : List (List Nat)}
    (hle : mv1 ≤ mv2) (hs : ExtUnsatSound F0 mv1 F_cur) : ExtUnsatSound F0 mv2 F_cur :=
  ⟨hs.1.mono hle, hs.2⟩

/-! ## 2. Arbitrary clause deletion & filtering (one-line UNSAT soundness) -/

/-- **Arbitrary clause deletion soundness**: keeping any subset `F_next ⊆ F_cur` preserves
`ExtUnsatSound` with zero SAT model-reconstruction side conditions. -/
theorem extUnsatSound_of_subset {F0 : CNF Nat} {mv : Nat} {F_cur F_next : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (hsub : ∀ c ∈ F_next, c ∈ F_cur) :
    ExtUnsatSound F0 mv F_next := by
  refine ⟨varsBounded_subset hsub hs.1, fun hu => hs.2 ?_⟩
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα
  exact hu α ((cnf_sat_cnfOfClauses_iff α F_next).mpr fun c hc => hα c (hsub c hc))

/-- Sublist deletion preserves `ExtUnsatSound`. -/
theorem extUnsatSound_of_sublist {F0 : CNF Nat} {mv : Nat} {F_cur F_next : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (hsub : F_next.Sublist F_cur) :
    ExtUnsatSound F0 mv F_next :=
  extUnsatSound_of_subset hs fun _ hc => hsub.mem hc

/-- Filtering clauses (`reduce`, satisfied-clause GC, forward subsumption, BIG transitive
reduction, pure-literal deletion, BVE pivot deletion) preserves `ExtUnsatSound` in one line. -/
theorem extUnsatSound_filter {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (p : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter p) :=
  extUnsatSound_of_sublist hs List.filter_sublist

/-- Index deletion (`deleteIdx`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_deleteIdx {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (i : Nat) :
    ExtUnsatSound F0 mv (deleteIdx F_cur i) :=
  extUnsatSound_of_subset hs ((forall_mem_deleteIdx_iff F_cur i (· ∈ F_cur)).mpr
    fun _ hj _ => List.getElem_mem hj)

/-- Single-clause deletion (`List.erase`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_erase {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (c : List Nat) :
    ExtUnsatSound F0 mv (F_cur.erase c) :=
  extUnsatSound_of_subset hs fun _ hd => List.mem_of_mem_erase hd

/-- Index deletion (`List.eraseIdx`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_eraseIdx {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (i : Nat) :
    ExtUnsatSound F0 mv (F_cur.eraseIdx i) :=
  extUnsatSound_of_subset hs fun _ hd => List.mem_of_mem_eraseIdx hd

/-- One-line UNSAT soundness for clause-DB `reduce` (filtering out garbage / low-tier clauses). -/
theorem extUnsatSound_reduceDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (keep : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter keep) :=
  extUnsatSound_filter hs keep

/-- One-line UNSAT soundness for satisfied-clause garbage collection. -/
theorem extUnsatSound_satisfiedGc {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (unsatByTrail : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter unsatByTrail) :=
  extUnsatSound_filter hs unsatByTrail

/-- One-line UNSAT soundness for forward subsumption deletion. -/
theorem extUnsatSound_forwardSubsumeDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (i : Nat) :
    ExtUnsatSound F0 mv (deleteIdx F_cur i) :=
  extUnsatSound_deleteIdx hs i

/-- One-line UNSAT soundness for BIG transitive reduction (`transitive.c`). -/
theorem extUnsatSound_transitiveDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (keep : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter keep) :=
  extUnsatSound_filter hs keep

/-- One-line UNSAT soundness for BCE blocked-clause deletion (`erase`). -/
theorem extUnsatSound_bceDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (c : List Nat) :
    ExtUnsatSound F0 mv (F_cur.erase c) :=
  extUnsatSound_erase hs c

/-- One-line UNSAT soundness for pure-literal clause deletion. -/
theorem extUnsatSound_pureLitDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (hasPure : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter hasPure) :=
  extUnsatSound_filter hs hasPure

/-- One-line UNSAT soundness for BVE / Gate-BVE pivot-clause deletion. -/
theorem extUnsatSound_bvePivotDel {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (pivotFree : List Nat → Bool) :
    ExtUnsatSound F0 mv (F_cur.filter pivotFree) :=
  extUnsatSound_filter hs pivotFree

/-! ## 3. Entailed clause addition, HBR, Gate Congruence Closure, & Bounded SAT Sweeping -/

/-- Adding an entailed, variable-bounded clause preserves `ExtUnsatSound`. -/
theorem extUnsatSound_addClause {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)} {C : List Nat}
    (hs : ExtUnsatSound F0 mv F_cur)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hb : ∀ l ∈ C, litVar l < mv) :
    ExtUnsatSound F0 mv (C :: F_cur) := by
  refine ⟨fun c hc l hl => (List.mem_cons.mp hc).elim (fun he => hb l (he ▸ hl))
    (fun hm => hs.1 c hm l hl), fun hu => ?_⟩
  apply hs.2
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α ((cnf_sat_cnfOfClauses_iff α (C :: F_cur)).mpr fun c hc =>
    (List.mem_cons.mp hc).elim (fun he => he ▸ CNF.entails_clause_def.mp hent α hα)
      ((cnf_sat_cnfOfClauses_iff α F_cur).mp hα c))

/-- Adding any list of entailed, variable-bounded clauses preserves `ExtUnsatSound`. -/
theorem extUnsatSound_addClauses {F0 : CNF Nat} {mv : Nat} {F_cur newCs : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur)
    (hent : ∀ C ∈ newCs, (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hb : VarsBounded mv newCs) :
    ExtUnsatSound F0 mv (newCs ++ F_cur) := by
  refine ⟨fun c hc l hl => (List.mem_append.mp hc).elim (hb c · l hl) (hs.1 c · l hl), fun hu => ?_⟩
  apply hs.2
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  exact hu α ((cnf_sat_cnfOfClauses_iff α _).mpr fun c hc =>
    (List.mem_append.mp hc).elim (fun hn => CNF.entails_clause_def.mp (hent c hn) α hα)
      ((cnf_sat_cnfOfClauses_iff α F_cur).mp hα c))

/-- General entailed clause replacement/simplification: any `F_next` whose clauses are all
entailed by `F_cur` and variable-bounded preserves `ExtUnsatSound`. -/
theorem extUnsatSound_replace_entailed {F0 : CNF Nat} {mv : Nat}
    {F_cur F_next : List (List Nat)} (hs : ExtUnsatSound F0 mv F_cur)
    (hent : ∀ C ∈ F_next, (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hb : VarsBounded mv F_next) :
    ExtUnsatSound F0 mv F_next :=
  extUnsatSound_of_subset (extUnsatSound_addClauses hs hent hb) fun _ hC =>
    List.mem_append_left F_cur hC

/-- Replacing clause `F_cur[i]` with an entailed, var-bounded clause preserves `ExtUnsatSound`. -/
theorem extUnsatSound_replaceIdx_entailed {F0 : CNF Nat} {mv : Nat}
    {F_cur : List (List Nat)} {i : Nat} {C : List Nat}
    (hs : ExtUnsatSound F0 mv F_cur) (hi : i < F_cur.length)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hb : ∀ l ∈ C, litVar l < mv) :
    ExtUnsatSound F0 mv (replaceIdx F_cur i C) := by
  refine extUnsatSound_replace_entailed hs ?_ ?_
  · intro D hD
    exact ((forall_mem_replaceIdx_iff F_cur hi C
      (fun x => (cnfOfClauses F_cur).EntailsClause (cnfClause x))).mpr
      ⟨hent, fun _ hj _ => entails_mem_cnfOfClauses (List.getElem_mem hj)⟩) D hD
  · intro D hD l hl
    exact ((forall_mem_replaceIdx_iff F_cur hi C (fun x => ∀ y ∈ x, litVar y < mv)).mpr
      ⟨hb, fun _ hj _ => hs.1 _ (List.getElem_mem hj)⟩) D hD l hl

/-- On-the-fly subsumption (`OTFS`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_otfs {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {i j l : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hi : i < F_cur.length) (hj : j < F_cur.length) (hne : j ≠ i)
    (hsub : ∀ x ∈ resolveOn l F_cur[i] F_cur[j], x ∈ F_cur[i]) :
    ExtUnsatSound F0 mv (replaceIdx F_cur i (resolveOn l F_cur[i] F_cur[j])) :=
  ⟨fun c hc x hx => ((forall_mem_replaceIdx_iff F_cur hi _
    (fun d => ∀ y ∈ d, litVar y < mv)).mpr
    ⟨fun y hy => hs.1 _ (List.getElem_mem hi) y (hsub y hy),
     fun _ hk _ => hs.1 _ (List.getElem_mem hk)⟩) c hc x hx,
   fun hu => hs.2 ((otfs_clauses_equiv hi hj hne hsub).2.mp hu)⟩

/-- Self-subsuming resolution (`SSR`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_ssr {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {i j l : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hi : i < F_cur.length) (hj : j < F_cur.length) (hl : l ∈ F_cur[i])
    (hnd : litNeg l ∈ F_cur[j])
    (hsub : ∀ x ∈ removeLit F_cur[j] (litNeg l), x ∈ removeLit F_cur[i] l) :
    ExtUnsatSound F0 mv (replaceIdx F_cur i (removeLit F_cur[i] l)) :=
  ⟨fun c hc x hx => ((forall_mem_replaceIdx_iff F_cur hi _
    (fun d => ∀ y ∈ d, litVar y < mv)).mpr
    ⟨fun y hy => hs.1 _ (List.getElem_mem hi) y (removeLit_subset F_cur[i] l y hy),
     fun _ hk _ => hs.1 _ (List.getElem_mem hk)⟩) c hc x hx,
   fun hu => hs.2 ((ssr_clauses_equiv hi hj hl hnd hsub).2.mp hu)⟩

/-- Eager subsumption: learn entailed clause `C`, then filter out clauses subsumed by `C`. -/
theorem extUnsatSound_eagerSubsume {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {C : List Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hb : ∀ l ∈ C, litVar l < mv) :
    ExtUnsatSound F0 mv (C :: F_cur.filter fun d => !clauseSubset C d) :=
  extUnsatSound_of_subset (extUnsatSound_addClause hs hent hb) fun _ hd =>
    (List.mem_cons.mp hd).elim (fun h => h ▸ List.mem_cons_self)
      (fun h => List.mem_cons_of_mem C (List.mem_filter.mp h).1)

/-- Vivification of slot `F_cur[i]` preserves `ExtUnsatSound`. -/
theorem extUnsatSound_vivifyClause {F0 : CNF Nat} {mv fuel : Nat} {F_cur : List (List Nat)}
    {i : Nat} (hs : ExtUnsatSound F0 mv F_cur) (hi : i < F_cur.length) :
    ExtUnsatSound F0 mv (replaceIdx F_cur i (vivifyClause fuel (deleteIdx F_cur i) F_cur[i])) := by
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 ((vivify_clause_equiv fuel F_cur hi).2.mp hu)⟩
  exact ((forall_mem_replaceIdx_iff F_cur hi _ (fun d => ∀ y ∈ d, litVar y < mv)).mpr
    ⟨fun y hy => hs.1 _ (List.getElem_mem hi) y
      ((vivifyClause_sound fuel (deleteIdx F_cur i) F_cur[i]).2 y hy),
     fun _ hk _ => hs.1 _ (List.getElem_mem hk)⟩) c hc l hl

private theorem varsBounded_vivifyPassAux {mv fuel : Nat} :
    ∀ (todo kept : List (List Nat)), VarsBounded mv kept → VarsBounded mv todo →
      VarsBounded mv (vivifyPassAux fuel kept todo)
  | [], kept, hk, _ => fun c hc l hl => hk c (List.mem_reverse.mp hc) l hl
  | c :: rest, kept, hk, ht => by
    have hkc : VarsBounded mv (vivifyClause fuel (kept ++ rest) c :: kept) := fun d hd l hl => by
      rcases List.mem_cons.mp hd with rfl | hmem
      · exact ht c List.mem_cons_self l ((vivifyClause_sound fuel (kept ++ rest) c).2 l hl)
      · exact hk d hmem l hl
    exact varsBounded_vivifyPassAux rest (vivifyClause fuel (kept ++ rest) c :: kept) hkc
      fun d hd => ht d (List.mem_cons_of_mem c hd)

/-- Single-pass vivification (`vivifyPass`) preserves `ExtUnsatSound`. -/
theorem extUnsatSound_vivifyPass {F0 : CNF Nat} {mv fuel : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) :
    ExtUnsatSound F0 mv (vivifyPass fuel F_cur) :=
  ⟨varsBounded_vivifyPassAux F_cur [] (fun _ h => by cases h) hs.1,
   fun hu => hs.2 ((vivify_pass_equiv fuel F_cur).2.mp hu)⟩

/-- Failed-literal / backbone unit addition: if `F_cur ∧ d ⊢ ⊥`, add `[¬d]`. -/
theorem extUnsatSound_failedLit {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)} {d : Nat}
    (hs : ExtUnsatSound F0 mv F_cur)
    (hfail : ((cnfOfClauses F_cur).add (cnfClause [d])).Unsat) (hbd : litVar d < mv) :
    ExtUnsatSound F0 mv ([litNeg d] :: F_cur) := by
  have hfail' : ((cnfOfClauses F_cur).add (cnfClause [litNeg (litNeg d)])).Unsat := by
    simpa [litNeg_litNeg] using hfail
  have hent := (unsat_add_litNeg_iff (cnfOfClauses F_cur) (litNeg d)).mp hfail'
  exact extUnsatSound_addClause hs hent
    (fun l hl => by simp only [List.mem_singleton] at hl; simpa [hl] using hbd)

/-- Executable failed-literal probing bridge into `ExtUnsatSound`. -/
theorem extUnsatSound_failedLit_probe {F0 : CNF Nat} {mv fuel : Nat}
    {F_cur : List (List Nat)} {d : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hp : probeFailedLit fuel F_cur (litNeg d) = true) (hbd : litVar d < mv) :
    ExtUnsatSound F0 mv ([litNeg d] :: F_cur) :=
  extUnsatSound_addClause hs (probeFailedLit_sound hp)
    (fun l hl => by simp only [List.mem_singleton] at hl; simpa [hl] using hbd)

/-! ### 3.1 Hyper-Binary Resolution (`HBR`) -/

/-- **Semantic Hyper-Binary Resolution (`HBR`)**: if `f ⊨ C`, `u ∈ C`, and every other literal
`x ∈ C \ {u}` is falsified under `f ∧ d` (`(f ++ unitsCnf [d]) ⊨ [¬x]`), then `f ⊨ [¬d, u]`. -/
theorem hbr_entails {f : CNF Nat} {C : List Nat} {d u : Nat}
    (hC : f.EntailsClause (cnfClause C)) (hu : u ∈ C)
    (himp : ∀ x ∈ C, x ≠ u → (f ++ unitsCnf [d]).EntailsClause (cnfClause [litNeg x])) :
    f.EntailsClause (cnfClause [litNeg d, u]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  by_cases hd : (cnfClause [d]).Sat α
  · have hfd : (f ++ unitsCnf [d]).Sat α :=
      CNF.sat_append.mpr ⟨hα, (sat_unitsCnf_iff α [d]).mpr fun _ hm => by
        simp only [List.mem_singleton] at hm; exact hm ▸ hd⟩
    obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α C).mp (CNF.entails_clause_def.mp hC α hα)
    by_cases hxu : x = u
    · subst hxu
      exact (clause_sat_cnfClause_iff α _).mpr ⟨x, List.mem_cons_of_mem _ List.mem_cons_self, hxs⟩
    · have hnx := CNF.entails_clause_def.mp (himp x hx hxu) α hfd
      exact absurd ((sat_cnfClause_singleton α x).mpr hxs) ((sat_cnfClause_litNeg_iff α x).mp hnx)
  · have hnd : (cnfClause [litNeg d]).Sat α := (sat_cnfClause_litNeg_iff α d).mpr hd
    exact (clause_sat_cnfClause_iff α _).mpr
      ⟨litNeg d, List.mem_cons_self, (sat_cnfClause_singleton α _).mp hnd⟩

/-- Trail-backed Hyper-Binary Resolution (`HBR`): on a level-1 `LazyTrailInv` state whose only
decision at level 1 is `d`, any clause `C` entailed by `s.f0` with `u ∈ C` and all `x ∈ C \ {u}`
falsified on `s.trail` entails the hyper-binary resolvent `[¬d, u]`. -/
theorem hbr_trail_entails {s : CdclState} (hinv : LazyTrailInv s) (hlvl : s.level = 1)
    {C : List Nat} {d u : Nat}
    (hdec : ∀ q ∈ decisionsAtMost s 1, q = d)
    (hC : s.f0.EntailsClause (cnfClause C)) (hu : u ∈ C)
    (hfals : ∀ x ∈ C, x ≠ u → litNeg x ∈ s.trail.toList) :
    s.f0.EntailsClause (cnfClause [litNeg d, u]) := by
  refine hbr_entails hC hu fun x hx hne => ?_
  obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp (hfals x hx hne)
  have hle1 : stateLevel s s.trail[j] ≤ 1 := hlvl ▸ hinv.levels_le j hj
  have htrl := CNF.entails_clause_trans (unitsCnf_decisionsAtMost_mono hle1)
    (lazyTrailEntailment hinv j hj)
  rw [CNF.entails_clause_def]
  intro α hα
  rw [CNF.sat_append, sat_unitsCnf_iff] at hα
  have hdam_sat : (s.f0 ++ unitsCnf (decisionsAtMost s 1)).Sat α :=
    CNF.sat_append.mpr ⟨hα.1, (sat_unitsCnf_iff α _).mpr fun q hq =>
      (hdec q hq) ▸ hα.2 d List.mem_cons_self⟩
  simpa [hjeq] using CNF.entails_clause_def.mp htrl α hdam_sat

/-- Adding an HBR resolvent `[¬d, u]` preserves `ExtUnsatSound`. -/
theorem extUnsatSound_hbr {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {C : List Nat} {d u : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hbd : litVar d < mv) (hbu : litVar u < mv)
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C)) (hu : u ∈ C)
    (himp : ∀ x ∈ C, x ≠ u →
      ((cnfOfClauses F_cur) ++ unitsCnf [d]).EntailsClause (cnfClause [litNeg x])) :
    ExtUnsatSound F0 mv ([litNeg d, u] :: F_cur) :=
  extUnsatSound_addClause hs (hbr_entails hC hu himp) fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simpa using ‹_›

/-- Adding an HBR resolvent from a concrete member clause `C ∈ F_cur`. -/
theorem extUnsatSound_hbr_mem {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {C : List Nat} {d u : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hbd : litVar d < mv) (hCm : C ∈ F_cur) (hu : u ∈ C)
    (himp : ∀ x ∈ C, x ≠ u →
      ((cnfOfClauses F_cur) ++ unitsCnf [d]).EntailsClause (cnfClause [litNeg x])) :
    ExtUnsatSound F0 mv ([litNeg d, u] :: F_cur) :=
  extUnsatSound_hbr hs hbd (hs.1 C hCm u hu) (entails_mem_cnfOfClauses hCm) hu himp

/-- Executable HBR checker: propagates decision `d` at level `1` over `F_cur` and verifies
that `u ∈ C` and every other literal `x ∈ C \ {u}` is falsified on the resulting trail. -/
@[expose]
def hbrCheck (fuel : Nat) (F_cur : List (List Nat)) (d : Nat) (C : List Nat) (u : Nat) : Bool :=
  match propagateAll fuel (initState (cnfOfClauses F_cur)) with
  | .ok s0 =>
    match litStatus s0.trail d with
    | none =>
      match propagateAll fuel (decideLit s0 d) with
      | .ok s1 => C.contains u && C.all (fun x => x == u || trailHasLit s1.trail (litNeg x))
      | .conflict _ _ => true
      | .outOfFuel _ => false
    | some false => true
    | some true => false
  | .conflict _ _ => true
  | .outOfFuel _ => false

theorem hbrCheck_sound {fuel : Nat} {F_cur : List (List Nat)} {C : List Nat} {d u : Nat}
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hchk : hbrCheck fuel F_cur d C u = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg d, u]) := by
  have h0 := initState_inv (cnfOfClauses F_cur)
  have hpi := propagateAll_inv (fuel := fuel) h0.1
  unfold hbrCheck at hchk
  cases hp0 : propagateAll fuel (initState (cnfOfClauses F_cur)) with
  | outOfFuel _ => simp [hp0] at hchk
  | conflict confl s0 =>
    rw [hp0] at hpi
    obtain ⟨hinv0, hf0, hl0, hconfl, hfals, _⟩ := hpi
    have hunsat : (cnfOfClauses F_cur).Unsat := by
      have := unsat_of_conflict hinv0 (by simp [hl0, initState]) hconfl hfals
      rwa [hf0, h0.2] at this
    exact CNF.entails_clause_def.mpr fun α hα => absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)
  | ok s0 =>
    rw [hp0] at hpi hchk; dsimp only at hchk
    obtain ⟨hinv0, hf0, hl0, _⟩ := hpi
    have hf0' : s0.f0 = cnfOfClauses F_cur := hf0.trans h0.2
    have hls0 : s0.level = 0 := by simpa [initState] using hl0
    cases hst : litStatus s0.trail d with
    | some b =>
      rw [hst] at hchk
      cases b
      · obtain ⟨i, hi, hieq⟩ :=
          trail_mem_iff_exists.mp ((litStatus_eq_some_false hinv0.vars_nodup).mp hst)
        have hli : stateLevel s0 s0.trail[i] = 0 := by have := hinv0.levels_le i hi; omega
        have hent := trailEntailment_level0 hinv0 hi hli
        rw [hieq, hf0'] at hent
        exact CNF.entails_clause_def.mpr fun α hα =>
          sat_clause_of_subset (fun x hx => by
            simp only [List.mem_singleton] at hx; simp [hx])
            (CNF.entails_clause_def.mp hent α hα)
      · simp at hchk
    | none =>
      rw [hst] at hchk; dsimp only at hchk
      have hdec := decideLit_inv hinv0 hst
      have hpi1 := propagateAll_inv (fuel := fuel) hdec.1
      cases hp1 : propagateAll fuel (decideLit s0 d) with
      | outOfFuel _ => simp [hp1] at hchk
      | conflict _ _ =>
        rw [hp1] at hpi1
        have hfl := failedLit_sound hinv0 hls0 hst hp1
        rw [hf0'] at hfl
        exact CNF.entails_clause_def.mpr fun α hα =>
          sat_clause_of_subset (fun x hx => by
            simp only [List.mem_singleton] at hx; simp [hx])
            (CNF.entails_clause_def.mp hfl α hα)
      | ok s1 =>
        rw [hp1] at hchk hpi1; dsimp only at hchk
        obtain ⟨hinv1, hf1, hl1, hdam1⟩ := hpi1
        have hls1 : s1.level = 1 := by simpa [decideLit, hls0] using hl1
        have hf1' : s1.f0 = cnfOfClauses F_cur := hf1.trans (hdec.2.trans hf0')
        simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
          Bool.or_eq_true, beq_iff_eq, trailHasLit_iff] at hchk
        have hdec_only : ∀ q ∈ decisionsAtMost s1 1, q = d := by
          intro q hq
          have hdam1' := hdam1 1
          rw [hdam1', mem_decisionsAtMost_iff] at hq
          obtain ⟨j, hj, hjeq⟩ := trail_mem_iff_exists.mp hq.1
          simp only [decideLit, trail_assignLit, Array.size_push] at hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exfalso
            have hnv := litStatus_none_no_var hst _
              (Array.mem_toList_iff.mpr (Array.getElem_mem hj'))
            simp only [decideLit, trail_assignLit, Array.getElem_push_lt hj'] at hjeq
            have hrsn : stateReason (decideLit s0 d) s0.trail[j] = .decision := hjeq ▸ hq.2.1
            simp only [decideLit, stateReason_assignLit] at hrsn
            have hsr : stateReason s0 s0.trail[j] = .decision := by
              simpa [hnv, stateReason] using hrsn
            have hrd := hinv0.reason_dag j hj'; dsimp only at hrd; rw [hsr] at hrd
            have hle := hinv0.levels_le j hj'; omega
          · simp only [decideLit, trail_assignLit, Array.getElem_push_eq] at hjeq
            exact hjeq.symm
        have hbr := hbr_trail_entails hinv1.toLazy hls1 hdec_only (hf1' ▸ hC) hchk.1
          fun x hx hne => (hchk.2 x hx).elim (fun h => absurd h hne) id
        rwa [hf1'] at hbr

/-! ### 3.2 Gate Congruence Closure (`congruence.c`: Equiv / AND / ITE / XOR) -/

/-- Literal equivalence entailed by `f`: `f ⊨ [¬a, b]` and `f ⊨ [a, ¬b]`. -/
@[expose] def LitEquiv (f : CNF Nat) (a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [litNeg a, b]) ∧ f.EntailsClause (cnfClause [a, litNeg b])

theorem LitEquiv.refl (f : CNF Nat) (a : Nat) : LitEquiv f a a := by
  refine ⟨CNF.entails_clause_def.mpr fun α _ => ?_, CNF.entails_clause_def.mpr fun α _ => ?_⟩
  · exact clauseIsTaut_sat (by simp [clauseIsTaut, litNeg_litNeg]) α
  · exact clauseIsTaut_sat (by simp [clauseIsTaut, litNeg_litNeg]) α

theorem LitEquiv.symm {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) : LitEquiv f b a :=
  ⟨entails_swap2 h.2, entails_swap2 h.1⟩

theorem litEquiv_eval {f : CNF Nat} {a b : Nat} {α : Nat → Bool}
    (hα : f.Sat α) (h : LitEquiv f a b) : evalLitVal α a = evalLitVal α b := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h.1 α hα)
  have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h.2 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg] at h1 h2
  cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all

theorem litEquiv_of_eval_eq {f : CNF Nat} {a b : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → evalLitVal α a = evalLitVal α b) :
    LitEquiv f a b := by
  refine ⟨CNF.entails_clause_def.mpr fun α hα => ?_, CNF.entails_clause_def.mpr fun α hα => ?_⟩
  · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, List.any_cons, List.any_nil,
      Bool.or_false, evalLitVal_litNeg, h α hα]
    cases evalLitVal α b <;> decide
  · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons, List.any_cons, List.any_nil,
      Bool.or_false, evalLitVal_litNeg, h α hα]
    cases evalLitVal α b <;> decide

theorem LitEquiv.trans {f : CNF Nat} {a b c : Nat}
    (h1 : LitEquiv f a b) (h2 : LitEquiv f b c) : LitEquiv f a c :=
  litEquiv_of_eval_eq fun _ hα => (litEquiv_eval hα h1).trans (litEquiv_eval hα h2)

theorem LitEquiv.neg {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    LitEquiv f (litNeg a) (litNeg b) :=
  litEquiv_of_eval_eq fun α hα => by simp [litEquiv_eval hα h]

theorem equivEntailed_iff_litEquiv (f : CNF Nat) (v l : Nat) :
    EquivEntailed f v l ↔ LitEquiv f (mkLit v true) l := by
  simp [EquivEntailed, LitEquiv, litNeg_mkLit]

/-- Equivalence gate definition `g ↔ x` entailed by `f`. -/
@[expose] def EquivGateDef (f : CNF Nat) (g x : Nat) : Prop :=
  LitEquiv f g x

/-- Multi-input AND gate definition `g ↔ (x₁ ∧ ... ∧ xₖ)` entailed by `f`. -/
@[expose] def AndGateDef (f : CNF Nat) (g : Nat) (xs : List Nat) : Prop :=
  f.EntailsClause (cnfClause (g :: xs.map litNeg)) ∧
  ∀ x ∈ xs, f.EntailsClause (cnfClause [litNeg g, x])

/-- ITE gate definition `g ↔ (if c then t else e)` entailed by `f`. -/
@[expose] def IteGateDef (f : CNF Nat) (g c t e : Nat) : Prop :=
  f.EntailsClause (cnfClause [g, litNeg c, litNeg t]) ∧
  f.EntailsClause (cnfClause [g, c, litNeg e]) ∧
  f.EntailsClause (cnfClause [litNeg g, litNeg c, t]) ∧
  f.EntailsClause (cnfClause [litNeg g, c, e])

/-- Binary XOR gate definition `g ↔ (a ⊕ b)` entailed by `f`. -/
@[expose] def XorGateDef (f : CNF Nat) (g a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [g, litNeg a, b]) ∧
  f.EntailsClause (cnfClause [g, a, litNeg b]) ∧
  f.EntailsClause (cnfClause [litNeg g, a, b]) ∧
  f.EntailsClause (cnfClause [litNeg g, litNeg a, litNeg b])

theorem equivGateDef_of_mem {cs : List (List Nat)} {g x : Nat}
    (h1 : [litNeg g, x] ∈ cs) (h2 : [g, litNeg x] ∈ cs) :
    EquivGateDef (cnfOfClauses cs) g x :=
  ⟨entails_mem_cnfOfClauses h1, entails_mem_cnfOfClauses h2⟩

theorem andGateDef_of_mem {cs : List (List Nat)} {g : Nat} {xs : List Nat}
    (h1 : (g :: xs.map litNeg) ∈ cs) (h2 : ∀ x ∈ xs, [litNeg g, x] ∈ cs) :
    AndGateDef (cnfOfClauses cs) g xs :=
  ⟨entails_mem_cnfOfClauses h1, fun x hx => entails_mem_cnfOfClauses (h2 x hx)⟩

theorem iteGateDef_of_mem {cs : List (List Nat)} {g c t e : Nat}
    (h1 : [g, litNeg c, litNeg t] ∈ cs) (h2 : [g, c, litNeg e] ∈ cs)
    (h3 : [litNeg g, litNeg c, t] ∈ cs) (h4 : [litNeg g, c, e] ∈ cs) :
    IteGateDef (cnfOfClauses cs) g c t e :=
  ⟨entails_mem_cnfOfClauses h1, entails_mem_cnfOfClauses h2,
   entails_mem_cnfOfClauses h3, entails_mem_cnfOfClauses h4⟩

theorem xorGateDef_of_mem {cs : List (List Nat)} {g a b : Nat}
    (h1 : [g, litNeg a, b] ∈ cs) (h2 : [g, a, litNeg b] ∈ cs)
    (h3 : [litNeg g, a, b] ∈ cs) (h4 : [litNeg g, litNeg a, litNeg b] ∈ cs) :
    XorGateDef (cnfOfClauses cs) g a b :=
  ⟨entails_mem_cnfOfClauses h1, entails_mem_cnfOfClauses h2,
   entails_mem_cnfOfClauses h3, entails_mem_cnfOfClauses h4⟩

theorem andGateDef_eval {f : CNF Nat} {g : Nat} {xs : List Nat} {α : Nat → Bool}
    (hα : f.Sat α) (hg : AndGateDef f g xs) :
    evalLitVal α g = xs.all (evalLitVal α) := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.1 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_map] at h1
  cases hgv : evalLitVal α g
  · simp only [hgv, Bool.false_or, List.any_eq_true, Function.comp_def, evalLitVal_litNeg,
      Bool.not_eq_true'] at h1
    obtain ⟨x, hx, hxf⟩ := h1
    exact (List.all_eq_false.mpr ⟨x, hx, by simp [hxf]⟩).symm
  · symm
    rw [List.all_eq_true]
    intro x hx
    have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hg.2 x hx) α hα)
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      evalLitVal_litNeg, hgv] at h2
    simpa using h2

theorem iteGateDef_eval {f : CNF Nat} {g c t e : Nat} {α : Nat → Bool}
    (hα : f.Sat α) (hg : IteGateDef f g c t e) :
    evalLitVal α g = if evalLitVal α c then evalLitVal α t else evalLitVal α e := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.1 α hα)
  have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.1 α hα)
  have h3 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.2.1 α hα)
  have h4 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.2.2 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    at h1 h2 h3 h4
  cases hg' : evalLitVal α g <;> cases hc' : evalLitVal α c <;>
    cases ht' : evalLitVal α t <;> cases he' : evalLitVal α e <;> simp_all

theorem xorGateDef_eval {f : CNF Nat} {g a b : Nat} {α : Nat → Bool}
    (hα : f.Sat α) (hg : XorGateDef f g a b) :
    evalLitVal α g = (evalLitVal α a != evalLitVal α b) := by
  have h1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.1 α hα)
  have h2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.1 α hα)
  have h3 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.2.1 α hα)
  have h4 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hg.2.2.2 α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    at h1 h2 h3 h4
  cases hg' : evalLitVal α g <;> cases ha' : evalLitVal α a <;>
    cases hb' : evalLitVal α b <;> simp_all

/-- **Congruence closure (Equiv gate)**: equivalent inputs imply equivalent gate outputs. -/
theorem congruence_equivGate {f : CNF Nat} {g1 x1 g2 x2 : Nat}
    (hg1 : EquivGateDef f g1 x1) (hg2 : EquivGateDef f g2 x2) (hx : LitEquiv f x1 x2) :
    LitEquiv f g1 g2 :=
  hg1.trans (hx.trans hg2.symm)

/-- **Congruence closure (AND gate)**: pairwise/set-equivalent inputs imply equivalent outputs. -/
theorem congruence_andGate {f : CNF Nat} {g1 g2 : Nat} {xs1 xs2 : List Nat}
    (hg1 : AndGateDef f g1 xs1) (hg2 : AndGateDef f g2 xs2)
    (h12 : ∀ x1 ∈ xs1, ∃ x2 ∈ xs2, LitEquiv f x1 x2)
    (h21 : ∀ x2 ∈ xs2, ∃ x1 ∈ xs1, LitEquiv f x1 x2) :
    LitEquiv f g1 g2 := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [andGateDef_eval hα hg1, andGateDef_eval hα hg2]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine ⟨fun hall x2 hx2 => ?_, fun hall x1 hx1 => ?_⟩
  · obtain ⟨x1, hx1, heq⟩ := h21 x2 hx2
    rw [← litEquiv_eval hα heq]
    exact hall x1 hx1
  · obtain ⟨x2, hx2, heq⟩ := h12 x1 hx1
    rw [litEquiv_eval hα heq]
    exact hall x2 hx2

/-- Index-wise equal-length AND-gate congruence closure. -/
theorem congruence_andGate_list {f : CNF Nat} {g1 g2 : Nat} {xs1 xs2 : List Nat}
    (hg1 : AndGateDef f g1 xs1) (hg2 : AndGateDef f g2 xs2)
    (hlen : xs1.length = xs2.length)
    (hpt : ∀ i (h1 : i < xs1.length) (h2 : i < xs2.length), LitEquiv f xs1[i] xs2[i]) :
    LitEquiv f g1 g2 :=
  congruence_andGate hg1 hg2
    (fun x1 hx1 => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx1
      exact ⟨xs2[i]'(by omega), List.getElem_mem (by omega), hpt i hi (by omega)⟩)
    (fun x2 hx2 => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx2
      exact ⟨xs1[i]'(by omega), List.getElem_mem (by omega), hpt i (by omega) hi⟩)

/-- **Congruence closure (ITE gate)**: equivalent `(c, t, e)` inputs imply equivalent outputs. -/
theorem congruence_iteGate {f : CNF Nat} {g1 c1 t1 e1 g2 c2 t2 e2 : Nat}
    (hg1 : IteGateDef f g1 c1 t1 e1) (hg2 : IteGateDef f g2 c2 t2 e2)
    (hc : LitEquiv f c1 c2) (ht : LitEquiv f t1 t2) (he : LitEquiv f e1 e2) :
    LitEquiv f g1 g2 := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [iteGateDef_eval hα hg1, iteGateDef_eval hα hg2,
    litEquiv_eval hα hc, litEquiv_eval hα ht, litEquiv_eval hα he]

/-- **Congruence closure (XOR gate)**: equivalent `(a, b)` inputs imply equivalent outputs. -/
theorem congruence_xorGate {f : CNF Nat} {g1 a1 b1 g2 a2 b2 : Nat}
    (hg1 : XorGateDef f g1 a1 b1) (hg2 : XorGateDef f g2 a2 b2)
    (ha : LitEquiv f a1 a2) (hb : LitEquiv f b1 b2) :
    LitEquiv f g1 g2 := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [xorGateDef_eval hα hg1, xorGateDef_eval hα hg2,
    litEquiv_eval hα ha, litEquiv_eval hα hb]

/-- Add both congruence-closure binary equivalence clauses `[¬g1, g2]` and `[g1, ¬g2]` to
`F_cur`, preserving `ExtUnsatSound`. -/
theorem extUnsatSound_congruence {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {g1 g2 : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (heq : LitEquiv (cnfOfClauses F_cur) g1 g2)
    (hb1 : litVar g1 < mv) (hb2 : litVar g2 < mv) :
    ExtUnsatSound F0 mv ([litNeg g1, g2] :: [g1, litNeg g2] :: F_cur) :=
  extUnsatSound_addClauses hs (newCs := [[litNeg g1, g2], [g1, litNeg g2]])
    (fun C hC => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl
      · exact heq.1
      · exact heq.2)
    (fun C hC l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rcases hl with rfl | rfl) <;>
        first | simpa using hb1 | simpa using hb2)

/-! ### 3.3 Bounded SAT Sweeping (`sweep.c`) -/

/-- **Bounded SAT sweeping binary implication**: if a local environment `env` entailed by `F_cur`
becomes unsatisfiable under assumptions `a ∧ ¬b`, then `F_cur ⊨ [¬a, b]`. -/
theorem sweep_imp_entails {F_cur env : List (List Nat)} {a b : Nat}
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hunsat : (cnfOfClauses ([a] :: [litNeg b] :: env)).Unsat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg a, b]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  by_cases ha : (cnfClause [a]).Sat α
  · by_cases hb : (cnfClause [b]).Sat α
    · exact sat_clause_of_subset (fun x hx => by
        simp only [List.mem_singleton] at hx; rw [hx]; simp) hb
    · exfalso
      apply CNF.unsat_iff_not_sat.mp hunsat α
      rw [cnf_sat_cnfOfClauses_iff]
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc'
      · exact ha
      · exact (sat_cnfClause_litNeg_iff α b).mpr hb
      · exact CNF.entails_clause_def.mp (henv c hc') α hα
  · exact sat_clause_of_subset (fun x hx => by
      simp only [List.mem_singleton] at hx; rw [hx]; simp)
      ((sat_cnfClause_litNeg_iff α a).mpr ha)

/-- **Bounded SAT sweeping backbone detection**: if `env ∧ a ⊢ ⊥`, then `F_cur ⊨ [¬a]`. -/
theorem sweep_backbone_entails {F_cur env : List (List Nat)} {a : Nat}
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hunsat : (cnfOfClauses ([a] :: env)).Unsat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg a]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  exact (sat_cnfClause_litNeg_iff α a).mpr fun ha =>
    CNF.unsat_iff_not_sat.mp hunsat α ((cnf_sat_cnfOfClauses_iff α _).mpr fun c hc =>
      (List.mem_cons.mp hc).elim (· ▸ ha) fun hc' =>
        CNF.entails_clause_def.mp (henv c hc') α hα)

/-- Executable bounded SAT-sweeping checker for binary implication `a → b` over local `env`. -/
@[expose] def sweepCheckImplies (fuel : Nat) (env : List (List Nat)) (a b : Nat) : Bool :=
  cdclSolve fuel (cnfOfClauses ([a] :: [litNeg b] :: env)) == .unsat

/-- Executable bounded SAT-sweeping checker for backbone refutation `a ⊢ ⊥` over `env`. -/
@[expose] def sweepCheckBackbone (fuel : Nat) (env : List (List Nat)) (a : Nat) : Bool :=
  cdclSolve fuel (cnfOfClauses ([a] :: env)) == .unsat

theorem sweepCheckImplies_sound {fuel : Nat} {F_cur env : List (List Nat)} {a b : Nat}
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hchk : sweepCheckImplies fuel env a b = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg a, b]) := by
  unfold sweepCheckImplies at hchk
  exact sweep_imp_entails henv (cdclSolve_unsat_sound (beq_iff_eq.mp hchk))

theorem sweepCheckBackbone_sound {fuel : Nat} {F_cur env : List (List Nat)} {a : Nat}
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hchk : sweepCheckBackbone fuel env a = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg a]) := by
  unfold sweepCheckBackbone at hchk
  exact sweep_backbone_entails henv (cdclSolve_unsat_sound (beq_iff_eq.mp hchk))

/-- Bounded SAT sweeping adding implication `[¬a, b]` to `F_cur`. -/
theorem extUnsatSound_sweep_imp {F0 : CNF Nat} {mv : Nat} {F_cur env : List (List Nat)}
    {a b : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hunsat : (cnfOfClauses ([a] :: [litNeg b] :: env)).Unsat)
    (hba : litVar a < mv) (hbb : litVar b < mv) :
    ExtUnsatSound F0 mv ([litNeg a, b] :: F_cur) :=
  extUnsatSound_addClause hs (sweep_imp_entails henv hunsat) fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simpa using ‹_›

/-- Bounded SAT sweeping adding equivalence `[¬a, b]` and `[a, ¬b]` via refuting both cones. -/
theorem extUnsatSound_sweep_equiv {F0 : CNF Nat} {mv : Nat} {F_cur env : List (List Nat)}
    {a b : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hu1 : (cnfOfClauses ([a] :: [litNeg b] :: env)).Unsat)
    (hu2 : (cnfOfClauses ([litNeg a] :: [b] :: env)).Unsat)
    (hba : litVar a < mv) (hbb : litVar b < mv) :
    ExtUnsatSound F0 mv ([litNeg a, b] :: [a, litNeg b] :: F_cur) := by
  have heq : LitEquiv (cnfOfClauses F_cur) a b := by
    refine ⟨sweep_imp_entails henv hu1, ?_⟩
    have h2 := sweep_imp_entails henv (a := litNeg a) (b := litNeg b) (by simpa using hu2)
    simpa [litNeg_litNeg] using h2
  exact extUnsatSound_congruence hs heq hba hbb

/-- Bounded SAT sweeping adding backbone unit `[¬a]`. -/
theorem extUnsatSound_sweep_backbone {F0 : CNF Nat} {mv : Nat} {F_cur env : List (List Nat)}
    {a : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (henv : ∀ c ∈ env, (cnfOfClauses F_cur).EntailsClause (cnfClause c))
    (hunsat : (cnfOfClauses ([a] :: env)).Unsat) (hba : litVar a < mv) :
    ExtUnsatSound F0 mv ([litNeg a] :: F_cur) :=
  extUnsatSound_addClause hs (sweep_backbone_entails henv hunsat) fun l hl => by
    simp only [List.mem_singleton] at hl; simpa [hl] using hba

/-! ### 3.4 BVE & Gate-Restricted BVE (`Eliminate`, `Gates`/`Factor`) -/

/-- Adding a BVE/Gate-BVE resolvent `dedupLits (resolveOn p c d)` from `c, d ∈ F_cur`
preserves `ExtUnsatSound`. -/
theorem extUnsatSound_bve_resolvent {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {p : Nat} {c d : List Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hc : c ∈ F_cur) (hd : d ∈ F_cur) :
    ExtUnsatSound F0 mv (dedupLits (resolveOn p c d) :: F_cur) :=
  extUnsatSound_addClause hs
    (entails_dedupLits (entails_resolve (p := p)
      (entails_mem_cnfOfClauses hc) (entails_mem_cnfOfClauses hd)))
    (varsBounded_dedupLits (varsBounded_resolveOn (hs.1 c hc) (hs.1 d hd)))

/-- Full BVE variable elimination `bveClauses F_cur v` preserves `ExtUnsatSound`. -/
theorem extUnsatSound_bve {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)} {v : Nat}
    (hs : ExtUnsatSound F0 mv F_cur) :
    ExtUnsatSound F0 mv (bveClauses F_cur v) := by
  have hp := bvePartition_props F_cur v
  dsimp only at hp
  obtain ⟨hpp, hpn, hpr, _⟩ := hp
  refine ⟨fun cl hcl l hl => ?_, fun hu => hs.2 (bveClauses_unsat hu)⟩
  unfold bveClauses at hcl
  rcases List.mem_append.mp hcl with hr | hrem
  · obtain ⟨⟨c, hc, d, hd, rfl⟩, _⟩ := (mem_bveResolvents_iff _ _ _ _).mp hr
    exact varsBounded_resolveOn (hs.1 c (hpp c hc).1) (hs.1 d (hpn d hd).1) l hl
  · exact hs.1 cl (hpr cl hrem).1 l hl

/-- Gate-restricted BVE `gateBveClauses v gp` preserves `ExtUnsatSound`. -/
theorem extUnsatSound_gateBve {F0 : CNF Nat} {mv v : Nat} {F_cur : List (List Nat)}
    {gp : GatePartition} (hs : ExtUnsatSound F0 mv F_cur)
    (hall : ∀ c ∈ gp.allClauses, (cnfOfClauses F_cur).EntailsClause (cnfClause c) ∧
      ∀ l ∈ c, litVar l < mv) :
    ExtUnsatSound F0 mv (gateBveClauses v gp) := by
  have hmem_all : ∀ c, c ∈ gp.rest ∨ c ∈ gp.posGate ∨ c ∈ gp.posNonGate ∨
      c ∈ gp.negGate ∨ c ∈ gp.negNonGate →
      (cnfOfClauses F_cur).EntailsClause (cnfClause c) ∧ ∀ l ∈ c, litVar l < mv := by
    intro c hc
    apply hall c
    unfold GatePartition.allClauses
    simp only [List.mem_append]
    rcases hc with h | h | h | h | h <;> simp [h]
  refine ⟨fun cl hcl l hl => ?_, fun hu => ?_⟩
  · unfold gateBveClauses at hcl
    simp only [List.mem_append] at hcl
    rcases hcl with (hr1 | hr2) | hr3
    · exact (hmem_all cl (Or.inl hr1)).2 l hl
    · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr2
      have hd_b : ∀ y ∈ d, litVar y < mv := (List.mem_append.mp hd).elim
        (fun h => (hmem_all d (Or.inr (Or.inr (Or.inr (Or.inl h))))).2)
        (fun h => (hmem_all d (Or.inr (Or.inr (Or.inr (Or.inr h))))).2)
      exact varsBounded_dedupLits (varsBounded_resolveOn
        (hmem_all c (Or.inr (Or.inl hc))).2 hd_b) l hl
    · obtain ⟨c, hc, d, hd, _, rfl⟩ := mem_nonTautResolvents_iff.mp hr3
      exact varsBounded_dedupLits (varsBounded_resolveOn
        (hmem_all c (Or.inr (Or.inr (Or.inl hc)))).2
        (hmem_all d (Or.inr (Or.inr (Or.inr (Or.inl hd))))).2) l hl
  · have hug := gateBve_unsat_sound hu
    apply hs.2
    rw [CNF.unsat_iff_not_sat] at hug ⊢
    intro α hα
    exact hug α ((cnf_sat_cnfOfClauses_iff α _).mpr fun c hc =>
      CNF.entails_clause_def.mp (hall c hc).1 α hα)

/-- Gate-restricted BVE directly on `partitionOnVar v isGate F_cur` preserves `ExtUnsatSound`. -/
theorem extUnsatSound_gateBve_part {F0 : CNF Nat} {mv v : Nat} {F_cur : List (List Nat)}
    (hs : ExtUnsatSound F0 mv F_cur) (isGate : List Nat → Bool) :
    ExtUnsatSound F0 mv (gateBveClauses v (partitionOnVar v isGate F_cur)) := by
  refine extUnsatSound_gateBve hs fun c hc => ?_
  have hmem : c ∈ F_cur := by
    unfold GatePartition.allClauses partitionOnVar at hc
    simp only [List.mem_append, List.mem_filter] at hc
    rcases hc with ((((⟨⟨h, _⟩, _⟩ | ⟨⟨h, _⟩, _⟩) | ⟨⟨h, _⟩, _⟩) | ⟨⟨h, _⟩, _⟩) | ⟨h, _⟩) <;>
      exact h
  exact ⟨entails_mem_cnfOfClauses hmem, hs.1 c hmem⟩

/-! ## 4. BIG SCC substitution (`substitute.c`) & fresh-variable BVA (`factor.c`) -/

/-- BIG SCC contradiction refutation (`x →* ¬x` and `¬x →* x`) yields `F0.Unsat`. -/
theorem extUnsatSound_binReach_contra {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {x : Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (h1 : BinReach (cnfOfClauses F_cur) x (litNeg x))
    (h2 : BinReach (cnfOfClauses F_cur) (litNeg x) x) : F0.Unsat :=
  hs.2 (binReach_contra_unsat h1 h2)

/-- BIG SCC mutual reachability yields `LitEquiv`. -/
theorem extUnsatSound_binReach_equiv {F_cur : List (List Nat)} {v l : Nat}
    (h1 : BinReach (cnfOfClauses F_cur) (mkLit v true) l)
    (h2 : BinReach (cnfOfClauses F_cur) l (mkLit v true)) :
    LitEquiv (cnfOfClauses F_cur) (mkLit v true) l :=
  (equivEntailed_iff_litEquiv _ v l).mp (binReach_scc_equiv h1 h2)

/-- Simultaneous BIG SCC literal substitution `substMapClauses m F_cur` under `F_cur`-entailed
equivalences preserves `ExtUnsatSound`. -/
theorem extUnsatSound_substMap {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {m : Nat → Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hm : ∀ v, EquivEntailed (cnfOfClauses F_cur) v (m v))
    (hb : ∀ v < mv, litVar (m v) < mv) :
    ExtUnsatSound F0 mv (substMapClauses m F_cur) := by
  refine ⟨fun c' hc' l hl => ?_, fun hu => hs.2 ?_⟩
  · rw [substMapClauses, List.mem_filterMap] at hc'
    obtain ⟨c, hc, hsub⟩ := hc'
    unfold substMapClause at hsub
    dsimp only at hsub
    split at hsub
    · cases hsub
    · injection hsub with hce
      rw [← hce] at hl
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (mem_dedupLits_iff.mp hl)
      have hv := hb (litVar y) (hs.1 c hc y hy)
      unfold substMapLit
      cases litSign y <;> simpa
  · apply substMap_unsat_sound hm
    simpa [substMapCnf, clausesOfCnf_cnfOfClauses] using hu

/-- Simultaneous BIG SCC literal substitution directly under `LitEquiv`. -/
theorem extUnsatSound_substMap_of_litEquiv {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    {m : Nat → Nat} (hs : ExtUnsatSound F0 mv F_cur)
    (hm : ∀ v, LitEquiv (cnfOfClauses F_cur) (mkLit v true) (m v))
    (hb : ∀ v < mv, litVar (m v) < mv) :
    ExtUnsatSound F0 mv (substMapClauses m F_cur) :=
  extUnsatSound_substMap hs (fun v => (equivEntailed_iff_litEquiv _ v (m v)).mpr (hm v)) hb

/-- **Fresh-variable BVA / factorization (`factor.c`)**: introducing fresh variable `z = mv_cur`
transitions `ExtUnsatSound F0 mv_cur F_cur` cleanly to `ExtUnsatSound F0 (mv_cur + 1)
(bvaFactorClauses mv_cur L Q F_cur)`. -/
theorem extUnsatSound_bvaFactor {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L : List Nat} {Q : List (List Nat)} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL_vb : ∀ f ∈ L, litVar f < mv_cur)
    (hQ_vb : ∀ q ∈ Q, ∀ x ∈ q, litVar x < mv_cur)
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: q))) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaFactorClauses mv_cur L Q F_cur) := by
  have hval : BvaValid mv_cur L Q F_cur :=
    ⟨hs.1.to_varFreshIn (Nat.le_refl _),
     fun f hf => Nat.ne_of_lt (hL_vb f hf),
     fun q hq x hx => Nat.ne_of_lt (hQ_vb q hq x hx),
     hprod⟩
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 (bvaFactor_unsat_sound hval hu)⟩
  unfold bvaFactorClauses at hc
  simp only [List.mem_append, List.mem_filter] at hc
  rcases hc with (hdiv | hquot) | ⟨hmem, _⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hdiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp
    · exact Nat.lt_succ_of_lt (hL_vb l hf)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hquot
    rcases List.mem_cons.mp hl with rfl | hxq
    · simp
    · exact Nat.lt_succ_of_lt (hQ_vb q hq l hxq)
  · exact Nat.lt_succ_of_lt (hs.1 c hmem l hl)

/-- Fresh-variable BVA when every product clause `f :: q` occurs directly in `F_cur`. -/
theorem extUnsatSound_bvaFactor_mem {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L : List Nat} {Q : List (List Nat)} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : L ≠ []) (hQ : Q ≠ [])
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (f :: q) ∈ F_cur) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaFactorClauses mv_cur L Q F_cur) := by
  obtain ⟨f0, hf0⟩ := List.exists_mem_of_ne_nil L hL
  obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil Q hQ
  exact extUnsatSound_bvaFactor hs
    (fun f hf => hs.1 (f :: q0) (hprod f hf q0 hq0) f List.mem_cons_self)
    (fun q hq x hx => hs.1 (f0 :: q) (hprod f0 hf0 q hq) x (List.mem_cons_of_mem f0 hx))
    (fun f hf q hq => entails_mem_cnfOfClauses (hprod f hf q hq))

end LeanQbe.T.Examples.Kissat.Ref
