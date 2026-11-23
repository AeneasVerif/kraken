module

public import LeanQbe.T.Examples.Kissat.LayerASubsume
public import LeanQbe.T.Examples.Kissat.LayerAVivify
public import LeanQbe.T.Examples.Kissat.LayerABve
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.Kissat.LayerASubsume
meta import LeanQbe.T.Examples.Kissat.LayerAVivify
meta import LeanQbe.T.Examples.Kissat.LayerABve1
meta import LeanQbe.T.Examples.Kissat.LayerABve

/-!
# Verification and Axiom Audit for Kissat Pure-Lean Layer-A Inprocessing

Executable `#guard` / `#eval` tests, closed non-vacuity theorems, and single-line
`#print axioms` reports (standard axioms only) covering:
1. Subsumption & Self-Subsuming Resolution / OTFS (`LayerASubsume`).
2. Failed-literal probing & Vivification strengthening (`LayerAVivify`).
3. Bounded Variable Elimination (`BVE`), LIFO witness reconstruction (`extendBve` /
   `extendBveArray`), and `cdclSolveAfterBve_sound` (`LayerABve1` & `LayerABve`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatLayerAInprocTest

open Std.Sat
open LeanQbe.T.Examples.Kissat

/-! ## 1. Subsumption & Self-Subsuming Resolution (`LayerASubsume`) -/

@[expose] public def subsumeSample : List (List Nat) :=
  [[0, 2, 4], [0, 2], [0, 2], [1, 2, 6], [2, 6, 8]]

#guard
  -- Duplicate `[0, 2]` keeps one survivor (`!=` deleting both mutual twins),
  -- while `[0, 2, 4]` is subsumed and deleted cleanly.
  subsumePass subsumeSample == [[0, 2], [1, 2, 6], [2, 6, 8]]

#guard
  -- `trySSR [0, 2, 4] [1, 2] = some [2, 4]` (`([1, 2] \ {1}) ⊆ ([0, 2, 4] \ {0})`).
  trySSR [0, 2, 4] [1, 2] == some [2, 4] &&
  -- Self-strengthening on tautology `[0, 1]` never fires (`x != l` rejects `0 ∈ [0]`).
  trySSR [0, 1] [0, 1] == none &&
  -- `subsumeAndSSR 2`: `[0, 2]` strengthens `[1, 2, 6]` -> `[2, 6]`, subsuming `[2, 6, 8]`.
  subsumeAndSSR 2 subsumeSample == [[0, 2], [2, 6]]

#eval subsumeAndSSR 2 subsumeSample

/-! ## 2. Failed-Literal Probing & Vivification (`LayerAVivify`) -/

@[expose] public def probeSample : List (List Nat) :=
  [[0, 2], [1, 2], [3, 4]]

#guard
  -- `F ∧ ¬x1` (`3`) propagates `x0` (`0`) then conflicts on `[1, 2]`, so `2` (`x1`) is failed.
  probeFailedLit 16 probeSample 2 &&
  !(probeFailedLit 16 probeSample 0)

@[expose] public def vivifyConflRest : List (List Nat) := [[0, 2], [0, 3]]
@[expose] public def vivifyImpRest : List (List Nat) := [[0, 2], [3, 4]]
@[expose] public def vivifyDropRest : List (List Nat) := [[0, 3]]

#guard
  -- Conflict vivification: assuming `¬0 = 1` triggers conflict in `[[0, 2], [0, 3]]` -> `[0]`.
  vivifyClause 16 vivifyConflRest [0, 4, 6] == [0] &&
  -- Implied-literal vivification: `¬0 = 1` propagates `2` then `4` -> `[0, 4]`.
  vivifyClause 16 vivifyImpRest [0, 4, 6] == [0, 4] &&
  -- Falsified-literal drop: `¬0 = 1` propagates `3 = ¬2` -> drops `2` -> `[0, 4]`.
  vivifyClause 16 vivifyDropRest [0, 2, 4] == [0, 4]

@[expose] public def vivifyPassSample : List (List Nat) :=
  [[0, 2], [0, 3], [0, 4, 6], [1, 4, 5]]

#guard vivifyPass 16 vivifyPassSample == [[0], [0], [0], [4, 5]]
#eval vivifyPass 16 vivifyPassSample

/-! ## 3. Bounded Variable Elimination & Model Reconstruction (`LayerABve1`, `LayerABve`) -/

@[expose] public def bveSatSample : List (List Nat) :=
  [[0, 2, 4], [1, 3, 4], [0, 5], [1, 2, 6], [2, 3, 7], [0, 1, 8]]

#guard
  -- Pivot `0` (`x0`) produces tautology `[2, 4, 3, 4]` from `[0, 2, 4]` × `[1, 3, 4]`,
  -- drops `[0, 1, 8]` as pivot-tautological, and eliminates variable `0` completely.
  let (cs1, _) := bveStep bveSatSample 0
  !(cs1.any fun c => c.any fun l => litVar l == 0)

#guard
  -- Iterated BVE on `[0, 1]` + `cdclSolve` + `extendBveArray` yields a verified model.
  let (red, stack) := bveElim bveSatSample [0, 1]
  match cdclSolve 64 (cnfOfClauses red) with
  | .sat σ =>
    let σFull := extendBveArray stack σ
    evalCnf σ red && evalCnf σFull bveSatSample && checkModel (cnfOfClauses bveSatSample) σFull
  | _ => false

@[expose] public def bveUnsatSample : List (List Nat) :=
  [[0, 2], [0, 3], [1, 2], [1, 3]]

#guard
  let (red, _) := bveElim bveUnsatSample [0, 1]
  red == [[]] && cdclSolve 32 (cnfOfClauses red) == .unsat

#guard
  -- Cost-bounded BVE: bound 0 skips var `0` (6 > 5 clauses) and accepts within bound (1 ≤ 2).
  let (red0, st0) := bveBoundedElim 0 [[0, 2], [0, 4], [0, 10], [1, 6], [1, 8]] [0]
  let (red1, st1) := bveBoundedElim 0 [[0, 2], [1, 4]] [0]
  st0.isEmpty && red0.length == 5 && st1.length == 1 && red1 == [[2, 4]]

#eval
  let (red, stack) := bveElim bveSatSample [0, 1]
  match cdclSolve 64 (cnfOfClauses red) with
  | .sat σ => some (extendBveArray stack σ)
  | _ => none

/-! ## 4. Closed non-vacuity theorems -/

/-- Closed non-vacuity corollary for `LayerASubsume`: exercises `subsume_clauses_equiv`,
`ssr_clauses_equiv`, and `subsume_ssr_equiv` on `subsumeSample`. -/
public theorem nv_subsume_ssr_sample :
    (∀ α : Nat → Bool,
      (cnfOfClauses (subsumeAndSSR 2 subsumeSample)).Sat α ↔
        (cnfOfClauses subsumeSample).Sat α) ∧
    ((cnfOfClauses (subsumeAndSSR 2 subsumeSample)).Unsat ↔
      (cnfOfClauses subsumeSample).Unsat) ∧
    (∀ α : Nat → Bool,
      (cnfOfClauses (deleteIdx subsumeSample 0)).Sat α ↔
        (cnfOfClauses subsumeSample).Sat α) ∧
    (∀ α : Nat → Bool,
      (cnfOfClauses (replaceIdx subsumeSample 3 (removeLit [1, 2, 6] 1))).Sat α ↔
        (cnfOfClauses subsumeSample).Sat α) := by
  have h1 := subsume_ssr_equiv 2 subsumeSample
  have h2 := subsume_clauses_equiv (cs := subsumeSample) (i := 0) (j := 1)
    (by decide) (by decide) (by decide) (by decide)
  have h3 := ssr_clauses_equiv (cs := subsumeSample) (i := 3) (j := 1) (l := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨h1.1, h1.2, h2.1, h3.1⟩

/-- Closed non-vacuity corollary for `LayerAVivify`: exercises `vivify_conflict_equiv`,
`vivify_implied_equiv`, `vivify_pass_equiv`, and `failedLit_add_equiv`. -/
public theorem nv_vivify_sample :
    (∀ α : Nat → Bool,
      ((cnfOfClauses vivifyConflRest).add (cnfClause [0])).Sat α ↔
        ((cnfOfClauses vivifyConflRest).add (cnfClause [0, 4, 6])).Sat α) ∧
    (∀ α : Nat → Bool,
      ((cnfOfClauses vivifyImpRest).add (cnfClause [0, 4])).Sat α ↔
        ((cnfOfClauses vivifyImpRest).add (cnfClause [0, 4, 6])).Sat α) ∧
    (∀ α : Nat → Bool,
      (cnfOfClauses (vivifyPass 16 vivifyPassSample)).Sat α ↔
        (cnfOfClauses vivifyPassSample).Sat α) ∧
    (∀ α : Nat → Bool,
      ((cnfOfClauses probeSample).add (cnfClause [2])).Sat α ↔
        (cnfOfClauses probeSample).Sat α) := by
  have hconfl : ((cnfOfClauses vivifyConflRest) ++ unitsCnf ([0].map litNeg)).Unsat := by
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    rw [CNF.sat_append, cnf_sat_cnfOfClauses_iff, sat_unitsCnf_iff] at hα
    have hc1 := hα.1 [0, 2] (by decide)
    have hc2 := hα.1 [0, 3] (by decide)
    have h0 := hα.2 1 (by decide)
    rw [clause_sat_cnfClause_iff] at hc1 hc2
    rw [sat_cnfClause_singleton] at h0
    simp only [litVar, litSign] at h0
    rcases hc1 with ⟨l1, hl1, hs1⟩
    rcases hc2 with ⟨l2, hl2, hs2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;>
      simp only [litVar, litSign] at hs1 hs2 <;> revert hs1 hs2 h0 <;> cases α 0 <;>
      cases α 1 <;> decide
  have himp : ((cnfOfClauses vivifyImpRest) ++ unitsCnf ([0].map litNeg)).EntailsClause
      (cnfClause [4]) := by
    rw [CNF.entails_clause_def]
    intro α hα
    rw [CNF.sat_append, cnf_sat_cnfOfClauses_iff, sat_unitsCnf_iff] at hα
    have hc1 := hα.1 [0, 2] (by decide)
    have hc2 := hα.1 [3, 4] (by decide)
    have h0 := hα.2 1 (by decide)
    rw [clause_sat_cnfClause_iff] at hc1 hc2
    rw [sat_cnfClause_singleton] at h0 ⊢
    rcases hc1 with ⟨l1, hl1, hs1⟩
    rcases hc2 with ⟨l2, hl2, hs2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;>
      simp only [litVar, litSign] at hs1 hs2 h0 ⊢ <;> revert hs1 hs2 h0 <;>
      cases α 0 <;> cases α 1 <;> cases α 2 <;> decide
  have hprobe : ((cnfOfClauses probeSample).add (cnfClause [litNeg 2])).Unsat := by
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    rw [CNF.sat_add, cnf_sat_cnfOfClauses_iff] at hα
    have hc1 := hα.2 [0, 2] (by decide)
    have hc2 := hα.2 [1, 2] (by decide)
    have hn2 := hα.1
    rw [clause_sat_cnfClause_iff] at hc1 hc2
    rw [sat_cnfClause_singleton] at hn2
    simp only [litNeg, litVar, litSign] at hn2
    rcases hc1 with ⟨l1, hl1, hs1⟩
    rcases hc2 with ⟨l2, hl2, hs2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;>
      simp only [litVar, litSign] at hs1 hs2 <;> revert hs1 hs2 hn2 <;>
      cases α 0 <;> cases α 1 <;> decide
  have hv1 := vivify_conflict_equiv (f := cnfOfClauses vivifyConflRest) (pref := [0])
    (c := [0, 4, 6]) (by decide) hconfl
  have hv2 := vivify_implied_equiv (f := cnfOfClauses vivifyImpRest) (pref := [0])
    (c := [0, 4, 6]) (lm := 4) (by decide) (by decide) himp
  have hv3 := vivify_pass_equiv 16 vivifyPassSample
  have hv4 := failedLit_add_equiv hprobe
  exact ⟨hv1.1, hv2.1, hv3.1, hv4.1⟩

/-- Closed SAT witness reconstruction theorem on `bveSatSample`: constructs an explicit
reconstructed `Array Bool` model of `bveSatSample` after eliminating pivots `[0, 1]`. -/
public theorem nv_bve_sat_sample :
    ∃ σFull : Array Bool,
      evalCnf σFull bveSatSample = true ∧
      checkModel (cnfOfClauses bveSatSample) σFull = true ∧
      (cnfOfClauses bveSatSample).Sat (evalVar σFull) := by
  let red := bveElim bveSatSample [0, 1]
  have hev : evalCnf #[false, false, true, false, true] red.1 = true := by decide
  have hrec := extendBveArray_sound hev
  have hsat := (evalCnf_iff _ bveSatSample).mp hrec
  have hchk := (checkModel_iff_sat (cnfOfClauses bveSatSample) _).mpr hsat
  exact ⟨extendBveArray red.2 #[false, false, true, false, true], hrec, hchk, hsat⟩

/-- Closed UNSAT soundness theorem on `bveUnsatSample`: eliminates pivots `[0, 1]` down to
`[[]]` and certifies `(cnfOfClauses bveUnsatSample).Unsat`. -/
public theorem nv_bve_unsat_sample : (cnfOfClauses bveUnsatSample).Unsat := by
  apply bveElim_unsat_sound (pivots := [0, 1])
  have hred : (bveElim bveUnsatSample [0, 1]).1 = [[]] := by decide
  rw [hred, CNF.unsat_iff_not_sat]
  intro α hα
  have hnil := (cnf_sat_cnfOfClauses_iff α [[]]).mp hα [] (by simp)
  exact absurd hnil (by simp)

/-- Closed `cdclSolveAfterBve_sound` instantiation on `bveSatSample` and `bveUnsatSample`
(paired with the executable `#guard` outcomes in Section 3). -/
public theorem nv_cdcl_bve_sound :
    (match cdclSolve 64 (bveElimCnf (cnfOfClauses bveSatSample) [0, 1]).1 with
     | .unsat => (cnfOfClauses bveSatSample).Unsat
     | .sat σ =>
       let σFull := extendBveArray (bveElimCnf (cnfOfClauses bveSatSample) [0, 1]).2 σ
       checkModel (cnfOfClauses bveSatSample) σFull = true ∧
       ¬ (cnfOfClauses bveSatSample).Unsat ∧
       (cnfOfClauses bveSatSample).Sat (evalVar σFull)
     | .unknown => True) ∧
    (match cdclSolve 32 (bveElimCnf (cnfOfClauses bveUnsatSample) [0, 1]).1 with
     | .unsat => (cnfOfClauses bveUnsatSample).Unsat
     | .sat σ =>
       let σFull := extendBveArray (bveElimCnf (cnfOfClauses bveUnsatSample) [0, 1]).2 σ
       checkModel (cnfOfClauses bveUnsatSample) σFull = true ∧
       ¬ (cnfOfClauses bveUnsatSample).Unsat ∧
       (cnfOfClauses bveUnsatSample).Sat (evalVar σFull)
     | .unknown => True) :=
  ⟨cdclSolveAfterBve_sound 64 (cnfOfClauses bveSatSample) [0, 1],
   cdclSolveAfterBve_sound 32 (cnfOfClauses bveUnsatSample) [0, 1]⟩

/-! ## 5. Single-line `#print axioms` checks -/

#print axioms LeanQbe.T.Examples.Kissat.subsume_cnf_equiv
#print axioms LeanQbe.T.Examples.Kissat.subsume_clauses_equiv
#print axioms LeanQbe.T.Examples.Kissat.ssr_cnf_equiv
#print axioms LeanQbe.T.Examples.Kissat.ssr_clauses_equiv
#print axioms LeanQbe.T.Examples.Kissat.otfs_clauses_equiv
#print axioms LeanQbe.T.Examples.Kissat.subsume_pass_equiv
#print axioms LeanQbe.T.Examples.Kissat.ssr_pass_equiv
#print axioms LeanQbe.T.Examples.Kissat.subsume_ssr_equiv
#print axioms LeanQbe.T.Examples.Kissat.subsume_db_equiv
#print axioms LeanQbe.T.Examples.Kissat.ssr_db_equiv
#print axioms LeanQbe.T.Examples.Kissat.subsume_preserves_inv
#print axioms LeanQbe.T.Examples.Kissat.failedLit_add_equiv
#print axioms LeanQbe.T.Examples.Kissat.failedLit_drop_equiv
#print axioms LeanQbe.T.Examples.Kissat.probeFailedLit_sound
#print axioms LeanQbe.T.Examples.Kissat.failedLit_probe_equiv
#print axioms LeanQbe.T.Examples.Kissat.failedLitStep_equiv
#print axioms LeanQbe.T.Examples.Kissat.failedAnalyze_equiv
#print axioms LeanQbe.T.Examples.Kissat.vivify_conflict_equiv
#print axioms LeanQbe.T.Examples.Kissat.vivify_implied_equiv
#print axioms LeanQbe.T.Examples.Kissat.vivify_confl_clauses
#print axioms LeanQbe.T.Examples.Kissat.vivify_imp_clauses
#print axioms LeanQbe.T.Examples.Kissat.vivify_clause_equiv
#print axioms LeanQbe.T.Examples.Kissat.vivify_pass_equiv
#print axioms LeanQbe.T.Examples.Kissat.bve_var_absent
#print axioms LeanQbe.T.Examples.Kissat.bveClauses_unsat
#print axioms LeanQbe.T.Examples.Kissat.bve_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBveStep_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBveStep_sat
#print axioms LeanQbe.T.Examples.Kissat.extendBveStepArr_sound
#print axioms LeanQbe.T.Examples.Kissat.bveElim_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.bveElimCnf_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBve_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBve_cnf_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBveArray_sound
#print axioms LeanQbe.T.Examples.Kissat.extendBveArray_cnf
#print axioms LeanQbe.T.Examples.Kissat.bveElim_equisat
#print axioms LeanQbe.T.Examples.Kissat.bveBounded_sound
#print axioms LeanQbe.T.Examples.Kissat.cdclSolveAfterBve_sound
#print axioms nv_subsume_ssr_sample
#print axioms nv_vivify_sample
#print axioms nv_bve_sat_sample
#print axioms nv_bve_unsat_sample
#print axioms nv_cdcl_bve_sound

end LeanQbeTest.T.KissatLayerAInprocTest
