module

public import LeanQbe.T.Examples.Kissat.LayerAFull1
public import LeanQbe.T.Examples.Kissat.LayerAFull
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.Kissat.LayerAFull1
meta import LeanQbe.T.Examples.Kissat.LayerAFull
meta import LeanQbe.T.Examples.LratBytes

/-!
# Verification, Closed Sample Theorems, and Axiom Audit for Kissat `D-Full` Layer-A Theory

Executable `#guard` checks, closed end-to-end non-vacuity theorems, and single-line
`#print axioms` reports covering every `LayerAFull1` and `LayerAFull` transition rule:
1. DIMACS initialization (`parseDimacs` -> `ExtUnsatSound`), arbitrary deletion (`filter`,
   `eraseIdx`, `deleteIdx`, `reduceDel`, `satisfiedGc`, `forwardSubsumeDel`, `transitiveDel`,
   `bceDel`, `pureLitDel`, `bvePivotDel`), and BVE/Gate-BVE deletion & resolvents.
2. Hyper-Binary Resolution (`HBR`: `hbrCheck`, `extUnsatSound_hbr_mem`) + OTFS/SSR/vivify/probe.
3. Gate Congruence Closure (`congruence.c`: `Equiv`, `AND`, `ITE`, `XOR`).
4. Bounded SAT Sweeping (`sweep.c`: `sweepCheckImplies`, `sweepCheckBackbone`, equiv & backbone).
5. BIG SCC contradiction (`BinReach`) + simultaneous `substMapClauses` + fresh-var BVA (`mv+1`).
6. `ChronoTrailInv`: out-of-order `chronoBacktrack` + `chronoAssignUip`, `restartReuseTrail`,
   1UIP + OTFS resolution, `chronoTrailEntailment`, and minimization/shrinking.
-/

set_option autoImplicit false

section

namespace KissatLayerAFullTest

open Std.Sat
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.LratBytes

/-! ## Pure helper lemmas (avoiding kernel reduction on unexposed `CNF.Clause.ofLiterals`) -/

private theorem dimacs0_of_cnfOfClauses {mv : Nat} {cs : List (List Nat)}
    (h : VarsBounded mv cs) : DimacsVarsBounded0 mv (cnfOfClauses cs) := by
  intro cl hcl lit hlit
  rw [CNF.Internal.mem_iff] at hcl
  simp only [cnfOfClauses, List.mem_toArray, List.mem_map] at hcl
  obtain ⟨c, hc, rfl⟩ := hcl
  rw [literals_cnfClause, List.mem_map] at hlit
  obtain ⟨l, hl, rfl⟩ := hlit
  exact h c hc l hl

private theorem extUnsatSound_of_clauses {mv : Nat} {cs : List (List Nat)}
    (hb : varsBoundedBool mv cs = true) :
    ExtUnsatSound (cnfOfClauses cs) mv cs := by
  have h := extUnsatSound_init (dimacs0_of_cnfOfClauses ((varsBoundedBool_iff mv cs).mp hb))
  rwa [clausesOfCnf_cnfOfClauses] at h

/-! ## 1. DIMACS init, arbitrary deletion, inprocessing, & BVE (`LayerAFull1`) -/

def unsatDimacsBytes : List UInt8 :=
  "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n".toUTF8.toList

def dimacsUnsatCnf : CNF Nat :=
  cnfOfClauses [[2, 4], [2, 5], [3, 4], [3, 5]]

def dimacsUnsatBytes : List UInt8 :=
  encodeDimacs dimacsUnsatCnf

def delBveSample : List (List Nat) :=
  [[0, 2], [0, 3], [1, 2], [1, 3], [0, 4]]

#guard dimacsUnsatBytes == unsatDimacsBytes
#guard varsBoundedBool 3 delBveSample
#guard (delBveSample.eraseIdx 4).filter (fun c => !c.isEmpty) == [[0, 2], [0, 3], [1, 2], [1, 3]]
#guard (bveClauses [[0, 2], [0, 3], [1, 2], [1, 3]] 0).contains [] == false

theorem nv_dimacs_del_bve :
    ∃ F0 : CNF Nat, parseDimacs dimacsUnsatBytes = some F0 ∧
      ExtUnsatSound F0 2 (clausesOfCnf (shiftDimacsCnf F0)) ∧ F0.Unsat := by
  have hval : ValidDimacsCnf dimacsUnsatCnf := by
    refine ⟨?_, ?_, ?_⟩
    · unfold cnfMaxVar dimacsUnsatCnf cnfOfClauses
      rw [← Array.foldl_toList]
      simp [cnfClause, CNF.Clause.literals_ofLiterals, litToLiteral, litVar, dimacsBound]
    · simp [dimacsUnsatCnf, cnfOfClauses, dimacsBound]
    · intro cl hcl l hl
      rw [Array.mem_toList_iff] at hcl
      simp only [dimacsUnsatCnf, cnfOfClauses, List.mem_toArray, List.mem_map,
        List.mem_cons, List.not_mem_nil, or_false] at hcl
      obtain ⟨c, hc, rfl⟩ := hcl
      rcases hc with rfl | rfl | rfl | rfl <;>
        · simp only [cnfClause, CNF.Clause.literals_ofLiterals, List.mem_map, List.mem_cons,
            List.not_mem_nil, or_false] at hl
          obtain ⟨x, hx, rfl⟩ := hl
          rcases hx with rfl | rfl <;> decide
  have hp : parseDimacs dimacsUnsatBytes = some dimacsUnsatCnf :=
    parseDimacs_encodeDimacs hval
  have hb : DimacsVarsBounded 2 dimacsUnsatCnf := by
    intro cl hcl l hl
    rw [CNF.Internal.mem_iff] at hcl
    simp only [dimacsUnsatCnf, cnfOfClauses, List.mem_toArray, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at hcl
    obtain ⟨c, hc, rfl⟩ := hcl
    rcases hc with rfl | rfl | rfl | rfl <;>
      · simp only [cnfClause, CNF.Clause.literals_ofLiterals, List.mem_map, List.mem_cons,
          List.not_mem_nil, or_false] at hl
        obtain ⟨x, hx, rfl⟩ := hl
        rcases hx with rfl | rfl <;> decide
  have hs0 := extUnsatSound_shift_of_parse hp hb
  have hshift : clausesOfCnf (shiftDimacsCnf dimacsUnsatCnf) =
      [[0, 2], [0, 3], [1, 2], [1, 3]] := by
    simp [dimacsUnsatCnf, clausesOfCnf, shiftDimacsCnf, shiftDimacsClause, cnfOfClauses,
      cnfClause, clauseOfCnf, CNF.Clause.literals_ofLiterals, litToLiteral, litOfLiteral,
      litVar, litSign, mkLit]
  refine ⟨dimacsUnsatCnf, hp, hs0, ?_⟩
  have hs1 : ExtUnsatSound dimacsUnsatCnf 2 [[0, 2], [0, 3], [1, 2], [1, 3]] := by
    rwa [hshift] at hs0
  have hs2 := extUnsatSound_bve (v := 0) hs1
  have hs3 := extUnsatSound_bve (v := 1) hs2
  exact extUnsatSound_unsat_of_nil hs3 (by decide)

theorem nv_bve_del_unsat : (cnfOfClauses delBveSample).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses delBveSample) 3 delBveSample :=
    extUnsatSound_of_clauses (by decide)
  -- Exercise one-line deletion wrappers (`eraseIdx`, `reduceDel`, `satisfiedGc`, `forwardSubsume`,
  -- `transitiveDel`, `bceDel`, `pureLitDel`, `bvePivotDel`) and BVE variable elimination.
  have h_red := extUnsatSound_reduceDel hs0 (fun c => !c.contains 4)
  have h_sat := extUnsatSound_satisfiedGc h_red (fun _ => true)
  have h_fwd := extUnsatSound_forwardSubsumeDel hs0 4
  have h_tr := extUnsatSound_transitiveDel h_fwd (fun _ => true)
  have h_bce := extUnsatSound_bceDel h_tr [0, 4]
  have h_pure := extUnsatSound_pureLitDel h_bce (fun _ => true)
  have h_piv := extUnsatSound_bvePivotDel h_pure (fun _ => true)
  have hs1 := extUnsatSound_bve (v := 0) h_sat
  have hs2 := extUnsatSound_bve (v := 1) hs1
  have _ := extUnsatSound_bve (v := 0) h_piv
  exact extUnsatSound_unsat_of_nil hs2 (by decide)

def inprocSample : List (List Nat) :=
  [[0, 2], [0, 3], [1, 2], [3]]

#guard (vivifyPass 16 inprocSample).contains []

theorem nv_inproc_rules : (cnfOfClauses inprocSample).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses inprocSample) 2 inprocSample :=
    extUnsatSound_of_clauses (by decide)
  -- Exercise OTFS, SSR, Gate-BVE, eager subsumption, vivification, and failed-lit probing.
  have hs_otfs := extUnsatSound_otfs hs0 (i := 1) (j := 0) (l := 3)
    (by decide) (by decide) (by decide) (by decide)
  have hs_ssr := extUnsatSound_ssr hs_otfs (i := 0) (j := 2) (l := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs_gate := extUnsatSound_gateBve_part (v := 0) hs_ssr (fun _ => false)
  have hs_eager := extUnsatSound_eagerSubsume hs_gate (C := [2])
    (entails_mem_cnfOfClauses (by decide)) (by decide)
  have _ := extUnsatSound_vivifyPass (fuel := 16) hs0
  have hfl : ((cnfOfClauses ([2] :: (gateBveClauses 0
      (partitionOnVar 0 (fun _ => false) (replaceIdx (replaceIdx inprocSample 1
        (resolveOn 3 inprocSample[1] inprocSample[0])) 0
        (removeLit (replaceIdx inprocSample 1
          (resolveOn 3 inprocSample[1] inprocSample[0]))[0] 0)))).filter
      fun d => !clauseSubset [2] d)).add (cnfClause [3])).Unsat := by
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    rw [CNF.sat_add, cnf_sat_cnfOfClauses_iff] at hα
    have h2 := (evalLitVal_iff α 2).mpr (hα.2 [2] (by decide))
    have h3 := (evalLitVal_iff α 3).mpr hα.1
    rw [show (3 : Nat) = litNeg 2 by decide, evalLitVal_litNeg, h2] at h3
    cases h3
  have hs_fl := extUnsatSound_failedLit hs_eager hfl (by decide)
  have hs_res := extUnsatSound_bve_resolvent (p := 2) hs_fl (c := [2]) (d := [3])
    (by decide) (by decide)
  exact extUnsatSound_unsat_of_nil hs_res (by decide)

/-! ## 2. Hyper-Binary Resolution (`HBR`) -/

-- Level-1 decision `0` (`x0`) implies `2` (`x1`) via `[1, 2]` and `4` (`x2`) via `[1, 4]`,
-- falsifying `3` and `5` in `[3, 5, 6]`, so HBR derives `[1, 6]` (`[¬x0, x3]`).
def hbrSample : List (List Nat) :=
  [[1, 2], [1, 4], [3, 5, 6], [0], [7]]

#guard hbrCheck 16 hbrSample 0 [3, 5, 6] 6

theorem nv_hbr_unsat : (cnfOfClauses hbrSample).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses hbrSample) 4 hbrSample :=
    extUnsatSound_of_clauses (by decide)
  have himp : ∀ x ∈ [3, 5, 6], x ≠ 6 →
      ((cnfOfClauses hbrSample) ++ unitsCnf [0]).EntailsClause (cnfClause [litNeg x]) := by
    intro x hx hne
    rw [CNF.entails_clause_def]
    intro α hα
    rw [CNF.sat_append, cnf_sat_cnfOfClauses_iff, sat_unitsCnf_iff] at hα
    have h0 := (evalLitVal_iff α 0).mpr (hα.2 0 List.mem_cons_self)
    have h12 := (clauseEvalVal_iff α [1, 2]).mpr (hα.1 [1, 2] (by decide))
    have h14 := (clauseEvalVal_iff α [1, 4]).mpr (hα.1 [1, 4] (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [show litNeg 3 = 2 by decide, ← evalLitVal_iff]
      simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
        show (1 : Nat) = litNeg 0 by decide, evalLitVal_litNeg, h0] at h12
      simpa using h12
    · rw [show litNeg 5 = 4 by decide, ← evalLitVal_iff]
      simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
        show (1 : Nat) = litNeg 0 by decide, evalLitVal_litNeg, h0] at h14
      simpa using h14
    · exact absurd rfl hne
  have hs1 := extUnsatSound_hbr_mem hs0 (C := [3, 5, 6]) (d := 0) (u := 6)
    (by decide) (by decide) (by decide) himp
  have hs2 := extUnsatSound_bve_resolvent (p := 0) hs1 (c := [0]) (d := [1, 6])
    (by decide) (by decide)
  have hs3 := extUnsatSound_bve_resolvent (p := 6) hs2 (c := [6]) (d := [7])
    (by decide) (by decide)
  exact extUnsatSound_unsat_of_nil hs3 (by decide)

/-! ## 3. Gate Congruence Closure (`Equiv`, `AND`, `ITE`, `XOR`) -/

def congAndSample : List (List Nat) :=
  [[3, 4], [2, 5],
   [6, 1, 3], [7, 0], [7, 2],
   [8, 1, 5], [9, 0], [9, 4],
   [6], [9]]

theorem nv_congruence_gates :
    (cnfOfClauses congAndSample).Unsat ∧
    (∀ (f : CNF Nat) (g1 x1 g2 x2 : Nat),
      EquivGateDef f g1 x1 → EquivGateDef f g2 x2 → LitEquiv f x1 x2 → LitEquiv f g1 g2) ∧
    (∀ (f : CNF Nat) (g1 c1 t1 e1 g2 c2 t2 e2 : Nat),
      IteGateDef f g1 c1 t1 e1 → IteGateDef f g2 c2 t2 e2 →
      LitEquiv f c1 c2 → LitEquiv f t1 t2 → LitEquiv f e1 e2 → LitEquiv f g1 g2) ∧
    (∀ (f : CNF Nat) (g1 a1 b1 g2 a2 b2 : Nat),
      XorGateDef f g1 a1 b1 → XorGateDef f g2 a2 b2 →
      LitEquiv f a1 a2 → LitEquiv f b1 b2 → LitEquiv f g1 g2) := by
  refine ⟨?_, @congruence_equivGate, @congruence_iteGate, @congruence_xorGate⟩
  have f_eq : LitEquiv (cnfOfClauses congAndSample) 2 4 :=
    equivGateDef_of_mem (cs := congAndSample) (by decide) (by decide)
  have hg1 : AndGateDef (cnfOfClauses congAndSample) 6 [0, 2] :=
    andGateDef_of_mem (cs := congAndSample) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hg2 : AndGateDef (cnfOfClauses congAndSample) 8 [0, 4] :=
    andGateDef_of_mem (cs := congAndSample) (by decide) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hcong : LitEquiv (cnfOfClauses congAndSample) 6 8 :=
    congruence_andGate_list hg1 hg2 (by decide) (fun i h1 h2 => by
      match i with
      | 0 => exact LitEquiv.refl _ 0
      | 1 => exact f_eq)
  have hs0 : ExtUnsatSound (cnfOfClauses congAndSample) 5 congAndSample :=
    extUnsatSound_of_clauses (by decide)
  have hs1 := extUnsatSound_congruence hs0 hcong (by decide) (by decide)
  have hs2 := extUnsatSound_bve_resolvent (p := 6) hs1 (c := [6]) (d := [7, 8])
    (by decide) (by decide)
  have hs3 := extUnsatSound_bve_resolvent (p := 8) hs2 (c := [8]) (d := [9])
    (by decide) (by decide)
  exact extUnsatSound_unsat_of_nil hs3 (by decide)

/-! ## 4. Bounded SAT Sweeping (`sweep.c`) -/

def sweepCone : List (List Nat) :=
  [[1, 2], [3, 4], [5, 1]]

def sweepFormula : List (List Nat) :=
  sweepCone ++ [[0]]

#guard sweepCheckImplies 16 sweepCone 0 4
#guard sweepCheckBackbone 16 (sweepCone ++ [[5]]) 0

theorem nv_sweep_unsat : (cnfOfClauses sweepFormula).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses sweepFormula) 3 sweepFormula :=
    extUnsatSound_of_clauses (by decide)
  have himp_u : (cnfOfClauses ([0] :: [5] :: sweepCone)).Unsat := by
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    rw [cnf_sat_cnfOfClauses_iff] at hα
    have h0 := (clauseEvalVal_iff α [0]).mpr (hα [0] (by decide))
    have h5 := (clauseEvalVal_iff α [5]).mpr (hα [5] (by decide))
    have h12 := (clauseEvalVal_iff α [1, 2]).mpr (hα [1, 2] (by decide))
    have h34 := (clauseEvalVal_iff α [3, 4]).mpr (hα [3, 4] (by decide))
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal,
      litVar, litSign] at h0 h5 h12 h34
    cases h0v : α 0 <;> cases h1v : α 1 <;> cases h2v : α 2 <;> simp_all
  have hs1 := extUnsatSound_sweep_imp hs0 (env := sweepCone) (a := 0) (b := 4)
    (fun c hc => entails_mem_cnfOfClauses (List.mem_append_left [[0]] hc))
    (by simpa [litNeg] using himp_u) (by decide) (by decide)
  have hbb_u : (cnfOfClauses ([0] :: [1, 4] :: sweepCone)).Unsat := by
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    rw [cnf_sat_cnfOfClauses_iff] at hα
    have h0 := (clauseEvalVal_iff α [0]).mpr (hα [0] (by decide))
    have h14 := (clauseEvalVal_iff α [1, 4]).mpr (hα [1, 4] (by decide))
    have h51 := (clauseEvalVal_iff α [5, 1]).mpr (hα [5, 1] (by decide))
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal,
      litVar, litSign] at h0 h14 h51
    cases h0v : α 0 <;> cases h2v : α 2 <;> simp_all
  have hs2 := extUnsatSound_sweep_backbone hs1 (env := [1, 4] :: sweepCone) (a := 0)
    (fun c hc => entails_mem_cnfOfClauses (by
      rcases List.mem_cons.mp hc with rfl | hcone
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left [[0]] hcone)))
    hbb_u (by decide)
  have hs3 := extUnsatSound_bve_resolvent (p := 0) hs2 (c := [0]) (d := [1])
    (by decide) (by decide)
  exact extUnsatSound_unsat_of_nil hs3 (by decide)

/-! ## 5. BIG SCC contradiction, `substMapClauses`, & fresh-variable BVA (`mv ↦ mv + 1`) -/

def bvaSccInit : List (List Nat) :=
  [[0, 2], [0, 4], [6, 2], [6, 4], [1, 2], [3, 1], [3, 0]]

def bvaFactored : List (List Nat) :=
  bvaFactorClauses 4 [0, 6] [[2], [4]] bvaSccInit

#guard varsBoundedBool 5 bvaFactored
#guard checkBinPath bvaFactored 0 [2, 1] 1 && checkBinPath bvaFactored 1 [8, 2, 0] 0

theorem nv_bva_scc_unsat : (cnfOfClauses bvaSccInit).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses bvaSccInit) 4 bvaSccInit :=
    extUnsatSound_of_clauses (by decide)
  -- Step 1: Fresh-variable BVA adds fresh variable `z = 4`, lifting `mv_cur : 4 ↦ 5`.
  have hs1 : ExtUnsatSound (cnfOfClauses bvaSccInit) 5 bvaFactored :=
    extUnsatSound_bvaFactor_mem hs0 (by decide) (by decide) (fun f hf q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hq
      rcases hf with rfl | rfl <;> rcases hq with rfl | rfl <;> decide)
  -- Step 2: BIG SCC contradiction `0 → 2 → 1` and `1 → 8 → 2 → 0` (via fresh BVA var `z=4`).
  have h01 : BinReach (cnfOfClauses bvaFactored) 0 (litNeg 0) :=
    checkBinPath_sound (cs := bvaFactored) (a := 0) (path := [2, 1]) (b := 1) (by decide)
  have h10 : BinReach (cnfOfClauses bvaFactored) (litNeg 0) 0 :=
    checkBinPath_sound (cs := bvaFactored) (a := 1) (path := [8, 2, 0]) (b := 0) (by decide)
  exact extUnsatSound_binReach_contra hs1 h01 h10

def sccSubstSample : List (List Nat) :=
  [[1, 2], [0, 3], [0], [3]]

def sccSubstMap (v : Nat) : Nat :=
  if v == 0 then 2 else mkLit v true

#guard substMapClauses sccSubstMap sccSubstSample == [[2], [3]]

theorem nv_substMap_unsat : (cnfOfClauses sccSubstSample).Unsat := by
  have hs0 : ExtUnsatSound (cnfOfClauses sccSubstSample) 2 sccSubstSample :=
    extUnsatSound_of_clauses (by decide)
  have hs1 := extUnsatSound_substMap_of_litEquiv hs0 (m := sccSubstMap) (fun v => by
    cases v with
    | zero => exact equivGateDef_of_mem (cs := sccSubstSample) (by decide) (by decide)
    | succ k => simpa [sccSubstMap] using LitEquiv.refl (cnfOfClauses sccSubstSample) _)
    (fun v hv => by cases v with | zero => decide | succ k => simp [sccSubstMap]; omega)
  have hs2 := extUnsatSound_bve_resolvent (p := 2) hs1 (c := [2]) (d := [3])
    (by decide) (by decide)
  exact extUnsatSound_unsat_of_nil hs2 (by decide)

/-! ## 6. `ChronoTrailInv`: out-of-order `chronoBacktrack` + `chronoAssignUip` + OTFS + Reuse -/

-- UNSAT-entailing core clauses on x0(0), x1(2), x2(4), x3(6), x4(8):
-- c0 = [4, 1, 3] (prop x2 at lvl 2)
-- c1 = [8, 1, 7] (prop x4 at lvl 3; OTFS strengthens this to [1, 7]).
-- c2 = [1, 7, 9] (conflict clause at lvl 3: ¬x0, ¬x3, ¬x4).
def chronoClauses : List (List Nat) :=
  [[4, 1, 3], [8, 1, 7], [1, 7, 9]]

def buildChronoState : ChronoState :=
  let s0 := chronoInit (cnfOfClauses chronoClauses)
  let s1 := chronoDecide s0 0
  let s2 := chronoDecide s1 2
  let s3 := chronoAssignProp s2 4 (.large 0)
  let s4 := chronoDecide s3 6
  chronoAssignProp s4 8 (.large 1)

def chronoOut : ChronoAnalyzeOut :=
  chronoAnalyze1UIP buildChronoState [1, 7, 9]

def afterChronoStep : ChronoState :=
  let uipLvl := backtrackLevel buildChronoState.cdcl chronoOut.learned
  chronoConflictStep buildChronoState 2 chronoOut.otfs chronoOut.learned 0 7 uipLvl

-- Notice `afterChronoStep.cdcl.trail = #[0, 2, 4, 7]`:
-- `0` is level 1 (dec), `2` is level 2 (dec, frame[1]=1), `4` is level 2 (prop),
-- and `7` (`uip`, ¬x3) sits at index `3 >= frame[1]` with level `1 < 2 = s.cdcl.level`.
#guard buildChronoState.cdcl.trail == #[0, 2, 4, 6, 8]
#guard chronoOut.learned == [1, 7]
#guard chronoOut.otfs == [{ cid := 1, pivot := 8, newLits := [1, 7] }]
#guard afterChronoStep.cdcl.trail == #[0, 2, 4, 7]
#guard afterChronoStep.cdcl.level == 2
#guard stateLevel afterChronoStep.cdcl 7 == 1
#guard afterChronoStep.isDecision 0 && !(afterChronoStep.isDecision 7)
#guard (restartReuseTrail afterChronoStep 1).cdcl.trail == #[0, 7]
#guard restartReuseDecisionLevel afterChronoStep [0, 5] 0 == 1
#guard chronoMinimize buildChronoState 8 [1, 7, 9] == [1, 7, 9]
#guard chronoShrink buildChronoState true true 8 [1, 7, 9] == [1, 7, 9]

@[simp] private theorem level_chronoInit (f : CNF Nat) :
    (chronoInit f).cdcl.level = 0 := rfl

@[simp] private theorem level_chronoDecide (s : ChronoState) (l : Nat) :
    (chronoDecide s l).cdcl.level = s.cdcl.level + 1 := rfl

@[simp] private theorem level_chronoAssignProp (s : ChronoState) (l : Nat) (r : Reason) :
    (chronoAssignProp s l r).cdcl.level = s.cdcl.level := rfl

@[simp] private theorem stateLevel_chronoInit (f : CNF Nat) (x : Nat) :
    stateLevel (chronoInit f).cdcl x = 0 := by
  simp only [chronoInit, ChronoState.ofCdcl, stateLevel, initState, Array.getD_eq_getD_getElem?,
    Array.getElem?_replicate]
  split <;> rfl

@[simp] private theorem stateReason_chronoInit (f : CNF Nat) (x : Nat) :
    stateReason (chronoInit f).cdcl x = .unit := by
  simp only [chronoInit, ChronoState.ofCdcl, stateReason, initState, Array.getD_eq_getD_getElem?,
    Array.getElem?_replicate]
  split <;> rfl

private theorem litStatus_of_trail_eq {s : ChronoState} {ts : List Nat} {l : Nat}
    (ht : s.cdcl.trail = ts.toArray) (hn1 : l ∉ ts) (hn2 : litNeg l ∉ ts) :
    litStatus s.cdcl.trail l = none := by
  rw [ht, litStatus_eq_none, Array.mem_toList_iff, Array.mem_toList_iff]
  simp [List.mem_toArray, hn1, hn2]

@[simp] private theorem stateLevel_chronoDecide (s : ChronoState) (l x : Nat) :
    stateLevel (chronoDecide s l).cdcl x =
      if litVar x = litVar l then s.cdcl.level + 1 else stateLevel s.cdcl x := by
  simp only [chronoDecide, decideLit, stateLevel_assignLit]
  rfl

@[simp] private theorem stateReason_chronoDecide (s : ChronoState) (l x : Nat) :
    stateReason (chronoDecide s l).cdcl x =
      if litVar x = litVar l then .decision else stateReason s.cdcl x := by
  simp only [chronoDecide, decideLit, stateReason_assignLit]
  rfl

@[simp] private theorem stateLevel_chronoAssignProp (s : ChronoState) (l : Nat) (r : Reason)
    (x : Nat) :
    stateLevel (chronoAssignProp s l r).cdcl x =
      if litVar x = litVar l then s.cdcl.level else stateLevel s.cdcl x := by
  simp [chronoAssignProp]

@[simp] private theorem stateReason_chronoAssignProp (s : ChronoState) (l : Nat) (r : Reason)
    (x : Nat) :
    stateReason (chronoAssignProp s l r).cdcl x =
      if litVar x = litVar l then r else stateReason s.cdcl x := by
  simp [chronoAssignProp]

@[simp] private theorem clauses_chronoDecide (s : ChronoState) (l : Nat) :
    (chronoDecide s l).cdcl.clauses = s.cdcl.clauses := rfl

@[simp] private theorem clauses_chronoAssignProp (s : ChronoState) (l : Nat) (r : Reason) :
    (chronoAssignProp s l r).cdcl.clauses = s.cdcl.clauses := rfl

@[simp] private theorem isDecision_chronoInit (f : CNF Nat) (x : Nat) :
    (chronoInit f).isDecision x = false := by
  simp only [chronoInit, ChronoState.ofCdcl, ChronoState.isDecision, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, initState, Array.getElem?_replicate]
  split <;> rfl

@[simp] private theorem isDecision_chronoDecide (s : ChronoState) (l x : Nat) :
    (chronoDecide s l).isDecision x =
      if litVar x = litVar l then true else s.isDecision x := by
  rw [chronoDecide, ChronoState.isDecision, arraySetPad_getD]; rfl

@[simp] private theorem isDecision_chronoAssignProp (s : ChronoState) (l : Nat) (r : Reason)
    (x : Nat) :
    (chronoAssignProp s l r).isDecision x =
      if litVar x = litVar l then false else s.isDecision x := by
  rw [chronoAssignProp, ChronoState.isDecision, arraySetPad_getD]; rfl

private theorem chronoInit_clauses_getElem? (cs : List (List Nat)) (i : Nat) :
    (chronoInit (cnfOfClauses cs)).cdcl.clauses[i]? =
      (cs[i]?).map (fun lits => some { lits := lits }) := by
  simp only [chronoInit, ChronoState.ofCdcl, initState, cnfOfClauses, Array.getElem?_map,
    List.getElem?_toArray, List.getElem?_map]
  cases h : cs[i]? <;> simp [clauseOfCnf_cnfClause]

private theorem buildChronoState_inv :
    ChronoTrailInv buildChronoState ∧ buildChronoState.cdcl.f0 = cnfOfClauses chronoClauses := by
  let s0 := chronoInit (cnfOfClauses chronoClauses)
  let s1 := chronoDecide s0 0
  let s2 := chronoDecide s1 2
  let s3 := chronoAssignProp s2 4 (.large 0)
  let s4 := chronoDecide s3 6
  have hi0 := chronoInit_inv (cnfOfClauses chronoClauses)
  have hi1 := chronoDecide_inv hi0.1 (l := 0) (litStatus_of_trail_eq (ts := []) rfl
    (by decide) (by decide))
  have hi2 := chronoDecide_inv hi1.1 (l := 2) (litStatus_of_trail_eq (ts := [0]) rfl
    (by decide) (by decide))
  have hok0 : ReasonOk s2.cdcl 4 2 (.large 0) := by
    refine ⟨{ lits := [4, 1, 3] }, ?_, rfl, by decide, fun x hx hne => ?_⟩
    · simp [s2, s1, s0, chronoInit_clauses_getElem?, chronoClauses]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact absurd rfl hne
      · refine ⟨0, by decide, rfl, ?_, Or.inl ?_⟩ <;> simp [s2, s1, s0, litVar]
      · refine ⟨1, by decide, rfl, ?_, Or.inr ⟨?_, by decide⟩⟩ <;> simp [s2, s1, s0, litVar]
  have hi3 := chronoAssignProp_inv hi2.1 (l := 4) (rsn := .large 0)
    (litStatus_of_trail_eq (ts := [0, 2]) rfl (by decide) (by decide)) (by simp) hok0
  have hi4 := chronoDecide_inv hi3.1 (l := 6) (litStatus_of_trail_eq (ts := [0, 2, 4]) rfl
    (by decide) (by decide))
  have hok1 : ReasonOk s4.cdcl 8 3 (.large 1) := by
    refine ⟨{ lits := [8, 1, 7] }, ?_, rfl, by decide, fun x hx hne => ?_⟩
    · simp [s4, s3, s2, s1, s0, chronoInit_clauses_getElem?, chronoClauses]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact absurd rfl hne
      · refine ⟨0, by decide, rfl, ?_, Or.inl ?_⟩ <;> simp [s4, s3, s2, s1, s0, litVar]
      · refine ⟨3, by decide, rfl, ?_, Or.inr ⟨?_, by decide⟩⟩ <;> simp [s4, s3, s2, s1, s0, litVar]
  exact chronoAssignProp_inv hi4.1 (l := 8) (rsn := .large 1)
    (litStatus_of_trail_eq (ts := [0, 2, 4, 6]) rfl (by decide) (by decide)) (by simp) hok1

private theorem buildChronoState_level : buildChronoState.cdcl.level = 3 := by
  simp [buildChronoState]

private theorem buildChronoState_stateLevel (x : Nat) :
    stateLevel buildChronoState.cdcl x =
      if litVar x = 4 then 3 else if litVar x = 3 then 3
      else if litVar x = 2 then 2 else if litVar x = 1 then 2
      else if litVar x = 0 then 1 else 0 := by
  simp [buildChronoState, litVar]

private theorem buildChronoState_stateReason (x : Nat) :
    stateReason buildChronoState.cdcl x =
      if litVar x = 4 then .large 1 else if litVar x = 3 then .decision
      else if litVar x = 2 then .large 0 else if litVar x = 1 then .decision
      else if litVar x = 0 then .decision else .unit := by
  simp [buildChronoState, litVar]

private theorem buildChronoState_clauses_get (i : Nat) :
    buildChronoState.cdcl.clauses[i]? =
      (chronoClauses[i]?).map (fun lits => some { lits := lits }) := by
  simpa [buildChronoState] using chronoInit_clauses_getElem? chronoClauses i

private theorem buildChronoState_isDec8 : buildChronoState.isDecision 8 = false := by
  simp [buildChronoState, litVar]

private theorem chronoOut_eq :
    chronoOut = { learned := [1, 7], otfs := [{ cid := 1, pivot := 8, newLits := [1, 7] }] } := by
  unfold chronoOut chronoAnalyze1UIP
  have htrail : buildChronoState.cdcl.trail = #[0, 2, 4, 6, 8] := rfl
  have hsz : buildChronoState.cdcl.trail.size = 5 := rfl
  have hdd0 : dedupLits [1, 7, 9] = [1, 7, 9] := by decide
  rw [buildChronoState_level, hsz, hdd0]
  have hlvlf : ((3 == 0) = true) ↔ False := by decide
  simp only [hlvlf, ite_false]
  rw [chronoAnalyze1UIPAux.eq_def]
  have hcnt3 : countAtLevel buildChronoState.cdcl [1, 7, 9] 3 = 2 := by
    simp only [countAtLevel, buildChronoState_stateLevel, litVar]; decide
  have h4lt : 4 < buildChronoState.cdcl.trail.size := by rw [htrail]; decide
  have hpiv8 : ∀ h, buildChronoState.cdcl.trail[4]'h = 8 := fun _ => rfl
  have hcontains9 : ([1, 7, 9] : List Nat).contains (litNeg 8) = true := by decide
  have hl8 : stateLevel buildChronoState.cdcl 8 = 3 := by
    simp [buildChronoState_stateLevel, litVar]
  have hr8 : stateReason buildChronoState.cdcl 8 = .large 1 := by
    simp [buildChronoState_stateReason, litVar]
  have hc1 : buildChronoState.cdcl.clauses[1]? = some (some { lits := [8, 1, 7] }) := by
    simp only [buildChronoState_clauses_get, chronoClauses]; rfl
  simp only [buildChronoState_level, hdd0, hcnt3, show ¬ (2 ≤ 1) by decide, ↓reduceIte,
    h4lt, ↓reduceDIte, hpiv8, hcontains9, hl8, beq_self_eq_true, buildChronoState_isDec8,
    Bool.not_false, Bool.and_self, hr8, hc1]
  have hr4 : dedupLits (resolveOn (litNeg 8) [1, 7, 9] [8, 1, 7]) = [1, 7] := by decide
  have hsub4 : clauseSubset [1, 7] [8, 1, 7] = true := by decide
  rw [hr4]
  rw [chronoAnalyze1UIPAux.eq_def]
  have hcnt1 : countAtLevel buildChronoState.cdcl [1, 7] 3 = 1 := by
    simp only [countAtLevel, buildChronoState_stateLevel, litVar]; decide
  simp only [buildChronoState_level, hsub4, hcnt1, show dedupLits [1, 7] = [1, 7] by decide,
    show (1 ≤ 1) by decide, ↓reduceIte]

private theorem afterChronoStep_trail_eq :
    afterChronoStep.cdcl.trail = #[0, 2, 4, 7] := by
  have hbt : backtrackLevel buildChronoState.cdcl chronoOut.learned = 1 := by
    simp [chronoOut_eq, backtrackLevel, buildChronoState_level, buildChronoState_stateLevel, litVar]
  have htr : buildChronoState.cdcl.trail = #[0, 2, 4, 6, 8] := rfl
  simp only [afterChronoStep, hbt, chronoConflictStep, chronoBacktrack, backtrackFilter,
    chronoAddLearnedClause, chronoAssignUip, assignLit, addLearnedClause, htr,
    buildChronoState_stateLevel, litVar]
  decide

private theorem afterChronoStep_stateLevel (x : Nat) :
    stateLevel afterChronoStep.cdcl x =
      if litVar x = 3 then 1 else if litVar x = 4 then 3
      else if litVar x = 2 then 2 else if litVar x = 1 then 2
      else if litVar x = 0 then 1 else 0 := by
  have hbt : backtrackLevel buildChronoState.cdcl chronoOut.learned = 1 := by
    simp [chronoOut_eq, backtrackLevel, buildChronoState_level, buildChronoState_stateLevel, litVar]
  simp only [afterChronoStep, hbt, chronoConflictStep, chronoAssignUip, chronoAddLearnedClause,
    chronoBacktrack, backtrackFilter, stateLevel_assignLit, stateLevel_addLearnedClause]
  change (if litVar x = litVar 7 then 1 else stateLevel buildChronoState.cdcl x) = _
  rw [buildChronoState_stateLevel]
  simp only [litVar]
  by_cases h3 : x / 2 = 3 <;> simp [h3]

theorem nv_chrono_otfs_reuse :
    ChronoTrailInv afterChronoStep ∧
    ReasonDagInv afterChronoStep.cdcl ∧
    ChronoTrailInv (restartReuseTrail afterChronoStep 1) ∧
    (restartReuseTrail afterChronoStep 1).cdcl.trail == #[0, 7] := by
  have hi5 := buildChronoState_inv
  have hconfl : buildChronoState.cdcl.f0.EntailsClause (cnfClause [1, 7, 9]) := by
    rw [hi5.2]; exact entails_mem_cnfOfClauses (cs := chronoClauses) (by decide)
  have hfals : ∀ l ∈ [1, 7, 9], litNeg l ∈ buildChronoState.cdcl.trail.toList := by
    intro l hl
    have htr : buildChronoState.cdcl.trail = #[0, 2, 4, 6, 8] := rfl
    rw [htr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> decide
  have ha := chronoAnalyze1UIP_sound hi5.1 hconfl hfals
  have hbt : backtrackLevel buildChronoState.cdcl chronoOut.learned = 1 := by
    simp [chronoOut_eq, backtrackLevel, buildChronoState_level, buildChronoState_stateLevel, litVar]
  have hstep := chronoAnalyzeAndStep_preserves_inv (s := buildChronoState) hi5.1
    (by rw [buildChronoState_level]; decide)
    (confl := [1, 7, 9]) (learned := chronoOut.learned) hconfl hfals (fun _ h => h) ha.1
    (uip := 7) (targetLevel := 2) (glue := 0)
    (by simp [chronoOut_eq])
    (by rw [buildChronoState_level, buildChronoState_stateLevel]; decide)
    (by rw [hbt]; decide)
    (by rw [buildChronoState_level]; decide)
  have hstep' : ChronoTrailInv afterChronoStep := by
    simpa [afterChronoStep, chronoOut] using hstep.1
  have hreuse := restartReuseTrail_preserves_inv hstep' 1
  have hreuse_trl : ((restartReuseTrail afterChronoStep 1).cdcl.trail == #[0, 7]) = true := by
    simp [restartReuseTrail, chronoBacktrack, backtrackFilter, afterChronoStep_trail_eq,
      afterChronoStep_stateLevel, litVar]
  exact ⟨hstep', hstep'.reason_dag, hreuse.1, hreuse_trl⟩

theorem nv_chrono_entail_min_shrink :
    (afterChronoStep.cdcl.f0 ++ unitsCnf (chronoDecisionsAtMost afterChronoStep 1)).EntailsClause
      (cnfClause [7]) ∧
    buildChronoState.cdcl.f0.EntailsClause
      (cnfClause (chronoMinimize buildChronoState 8 [1, 7, 9])) ∧
    buildChronoState.cdcl.f0.EntailsClause
      (cnfClause (chronoShrink buildChronoState true true 8 [1, 7, 9])) := by
  have hi5 := buildChronoState_inv
  have hconfl : buildChronoState.cdcl.f0.EntailsClause (cnfClause [1, 7, 9]) := by
    rw [hi5.2]; exact entails_mem_cnfOfClauses (cs := chronoClauses) (by decide)
  have hfals : ∀ l ∈ [1, 7, 9], litNeg l ∈ buildChronoState.cdcl.trail.toList := by
    intro l hl
    have htr : buildChronoState.cdcl.trail = #[0, 2, 4, 6, 8] := rfl
    rw [htr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> decide
  have hm := chronoMinimize_sound hi5.1 hconfl hfals 8
  have hsh := chronoShrink_sound hi5.1 hconfl hfals true true 8
  have hstep := nv_chrono_otfs_reuse.1
  have hent7 := chronoTrailEntailment hstep (i := 3) (by rw [afterChronoStep_trail_eq]; decide)
  have h7 : afterChronoStep.cdcl.trail[3]'(by rw [afterChronoStep_trail_eq]; decide) = 7 := by
    simp [afterChronoStep_trail_eq]
  have hl7 : stateLevel afterChronoStep.cdcl 7 = 1 := by
    simp [afterChronoStep_stateLevel, litVar]
  rw [h7, hl7] at hent7
  exact ⟨hent7, hm.1, hsh.1⟩

/-! ## 7. Single-line `#print axioms` checks -/

#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_init_shift
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_init_of_parse
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_of_subset
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_of_sublist
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_filter
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_eraseIdx
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_addClause
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_otfs
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_ssr
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_eagerSubsume
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_vivifyPass
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_failedLit
#print axioms LeanQbe.T.Examples.Kissat.hbr_entails
#print axioms LeanQbe.T.Examples.Kissat.hbr_trail_entails
#print axioms LeanQbe.T.Examples.Kissat.hbrCheck_sound
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_hbr
#print axioms LeanQbe.T.Examples.Kissat.congruence_equivGate
#print axioms LeanQbe.T.Examples.Kissat.congruence_andGate
#print axioms LeanQbe.T.Examples.Kissat.congruence_iteGate
#print axioms LeanQbe.T.Examples.Kissat.congruence_xorGate
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_congruence
#print axioms LeanQbe.T.Examples.Kissat.sweep_imp_entails
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_sweep_equiv
#print axioms LeanQbe.T.Examples.Kissat.sweep_backbone_entails
#print axioms LeanQbe.T.Examples.Kissat.sweepCheckImplies_sound
#print axioms LeanQbe.T.Examples.Kissat.sweepCheckBackbone_sound
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_bve
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_gateBve
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_binReach_contra
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_substMap
#print axioms LeanQbe.T.Examples.Kissat.extUnsatSound_bvaFactor
#print axioms LeanQbe.T.Examples.Kissat.chronoTrailEntailment
#print axioms LeanQbe.T.Examples.Kissat.chronoAssignUip_inv
#print axioms LeanQbe.T.Examples.Kissat.chronoBacktrack_preserves_inv
#print axioms LeanQbe.T.Examples.Kissat.restartReuseTrail_preserves_inv
#print axioms LeanQbe.T.Examples.Kissat.restartReusePrefix_preserves_inv
#print axioms LeanQbe.T.Examples.Kissat.chronoAnalyze1UIP_sound
#print axioms LeanQbe.T.Examples.Kissat.chronoMinimize_sound
#print axioms LeanQbe.T.Examples.Kissat.chronoShrink_sound
#print axioms LeanQbe.T.Examples.Kissat.chronoConflictStep_preserves_inv
#print axioms nv_dimacs_del_bve
#print axioms nv_bve_del_unsat
#print axioms nv_inproc_rules
#print axioms nv_hbr_unsat
#print axioms nv_congruence_gates
#print axioms nv_sweep_unsat
#print axioms nv_bva_scc_unsat
#print axioms nv_substMap_unsat
#print axioms nv_chrono_otfs_reuse
#print axioms nv_chrono_entail_min_shrink

end KissatLayerAFullTest
