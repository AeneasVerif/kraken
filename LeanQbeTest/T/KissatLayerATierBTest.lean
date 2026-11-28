module

import LeanQbe.T.Examples.Kissat.Ref.Substitute
import LeanQbe.T.Examples.Kissat.Ref.Gates
import LeanQbe.T.Examples.Kissat.Ref.Factor
import LeanQbe.T.Examples.Kissat.Proof.Ref.Factor
meta import LeanQbe.T.Examples.Kissat.Ref.Sat
meta import LeanQbe.T.Examples.Kissat.Ref.Substitute
meta import LeanQbe.T.Examples.Kissat.Ref.Gates
meta import LeanQbe.T.Examples.Kissat.Ref.Factor

/-!
# Verification, Closed Sample Theorems, and Axiom Audit for Kissat `D-Full` Elimination Theories

Executable `#guard` / `#eval` checks, closed end-to-end theorems, and single-line
`#print axioms` audits covering:
1. `LayerASubstitute`: single-step & multi-step `SubstTrace` substitution, SCC reachability
   (`BinReach`), simultaneous representative maps (`substMapCnf`), and `Array Bool` witness
   reconstruction (`substTraceExtendArr`, `substTableExtendArr`).
2. `LayerAGates`: Blocked Clause Elimination (`extendBce`, `BceReconStack`), Gate-Restricted
   BVE (`gates.c`: `Equiv`/`AND`/`ITE`/`XOR`/`definition.c`, `extendGateBve`, blocked
   non-gate resolvents), Blocked Clause Addition (`BCA`), Bounded Variable Addition /
   Factorization (`factor.c`), and unified `TierBTrace` composition.
-/

set_option autoImplicit false

section

namespace KissatTierBTest

open Std.Sat
open LeanQbe.T.Examples.Kissat.Ref

/-! ## 1. Equivalence / SCC Literal Substitution (`LayerASubstitute`) -/

-- Literal encoding:
-- x0 = 0, ¬x0 = 1; x1 = 2, ¬x1 = 3; x2 = 4, ¬x2 = 5; x3 = 6, ¬x3 = 7.

-- Formula with x0 ↔ x1 ([1, 2], [0, 3]) and x1 ↔ ¬x2 ([3, 5], [2, 4]) plus [0, 6] and [4, 7].
def substSampleClauses : List (List Nat) :=
  [[1, 2], [0, 3], [3, 5], [2, 4], [0, 6], [4, 7]]

def substSampleCnf : CNF Nat := cnfOfClauses substSampleClauses

def substSampleTrace : SubstTrace :=
  [{ var := 0, repr := 2 }, { var := 1, repr := 5 }]

-- Reduced model sets x2 = true, x3 = true (x0, x1 left false initially).
def substReducedModel : Array Bool := #[false, false, true, true]

#guard checkModel (substTraceApply substSampleTrace substSampleCnf) substReducedModel
#guard
  let full := substTraceExtendArr substSampleTrace substReducedModel
  full == #[false, false, true, true] && checkModel substSampleCnf full

-- Flip x2 = false, x3 = false so x1 must reconstruct to true and x0 must reconstruct to true.
def substReducedModelFlip : Array Bool := #[false, false, false, false]

#guard checkModel (substTraceApply substSampleTrace substSampleCnf) substReducedModelFlip
#guard
  let full := substTraceExtendArr substSampleTrace substReducedModelFlip
  !checkModel substSampleCnf substReducedModelFlip &&
    full == #[true, true, false, false] &&
    checkModel substSampleCnf full

-- Simultaneous SCC table: x0 ↦ ¬x2 (5), x1 ↦ ¬x2 (5), x2 ↦ x2 (4), x3 ↦ x3 (6).
def sccReprTable : Array Nat := #[5, 5, 4, 6]

#guard checkModel (substMapCnf (reprOfTable sccReprTable) substSampleCnf) substReducedModelFlip
#guard
  let full := substTableExtendArr sccReprTable substReducedModelFlip
  full == #[true, true, false, false] && checkModel substSampleCnf full

-- Closed SAT reconstruction theorem for multi-step substitution trace.
theorem sample_subst_sat :
    let σ := substTraceExtendArr substSampleTrace substReducedModelFlip
    substSampleCnf.Sat (evalVar σ) ∧ ¬ substSampleCnf.Unsat := by
  have hred : checkModel (substTraceApply substSampleTrace substSampleCnf)
      substReducedModelFlip = true := by
    rw [substSampleCnf, substTraceApply_cnfOfClauses, checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hfull := substTraceExtendArr_sound hred
  exact ⟨(checkModel_iff_sat _ _).mp hfull, (checkModel_sound hfull).1⟩

-- SCC contradiction formula: x0 → x1 ([1, 2]), x1 → ¬x0 ([3, 1]), ¬x0 → ¬x1 ([0, 3]),
-- ¬x1 → x0 ([2, 0]). Thus x0 and ¬x0 lie in the same SCC -> immediate UNSAT.
def sccContraClauses : List (List Nat) :=
  [[1, 2], [3, 1], [0, 3], [2, 0]]

#guard checkBinPath sccContraClauses 0 [2, 1] 1
#guard checkBinPath sccContraClauses 1 [3, 0] 0

theorem sample_scc_unsat : (cnfOfClauses sccContraClauses).Unsat := by
  have h1 : BinReach (cnfOfClauses sccContraClauses) 0 (litNeg 0) :=
    checkBinPath_sound (cs := sccContraClauses) (a := 0) (path := [2, 1]) (b := 1) (by decide)
  have h2 : BinReach (cnfOfClauses sccContraClauses) (litNeg 0) 0 :=
    checkBinPath_sound (cs := sccContraClauses) (a := 1) (path := [3, 0]) (b := 0) (by decide)
  exact binReach_contra_unsat h1 h2

-- Closed UNSAT theorem via single-step substitution:
-- x0 ↔ x1 ([1, 2], [0, 3]), [0], [3] -> substituting x0 ↦ x1 turns [0] into [2],
-- contradicting [3] -> UNSAT.
def substUnsatClauses : List (List Nat) :=
  [[1, 2], [0, 3], [0], [3]]

theorem sample_subst_unsat : (cnfOfClauses substUnsatClauses).Unsat := by
  have heq : EquivEntailed (cnfOfClauses substUnsatClauses) 0 2 :=
    ⟨entails_mem_cnfOfClauses (by decide), entails_mem_cnfOfClauses (by decide)⟩
  apply subst_unsat_sound heq
  rw [substCnf, clausesOfCnf_cnfOfClauses, CNF.unsat_iff_not_sat]
  intro α hα
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  have h2 : (cnfClause [2]).Sat α := hα' [2] (by decide)
  have h3 : (cnfClause [3]).Sat α := hα' [3] (by decide)
  exact (sat_cnfClause_litNeg_iff α 2).mp h3 h2

/-! ## 2. Blocked Clause Elimination (`BCE`) and `BceReconStack` (`LayerAGates`) -/

-- Clauses over x0 (0/1), x1 (2/3), x2 (4/5):
-- c1 = [0, 2] blocked on x0 (0): only clause with ¬x0 (1) is c2 = [1, 3, 4],
-- resolvent [2, 3, 4] is tautological (2, 3).
-- After eliminating c1, c2 = [1, 3, 4] is blocked on ¬x0 (1): no remaining clause has x0 (0).
-- Remaining clause: [4, 2].
def bceSampleClauses : List (List Nat) :=
  [[0, 2], [1, 3, 4], [4, 2]]

def bceSampleStack : BceReconStack :=
  [{ lit := 0, clause := [0, 2] }, { lit := 1, clause := [1, 3, 4] }]

-- Reduced model satisfies [4, 2] with x0 = true, x1 = true, x2 = false:
-- falsifies c2 = [1, 3, 4]; stack must flip x0 := false to satisfy c2, then c1 = [0, 2] is
-- already satisfied by x1 = true.
def bceReducedModel : Array Bool := #[true, true, false]

#guard isBlockedOnBool (bceSampleClauses.erase [0, 2]) [0, 2] 0
#guard isBlockedOnBool ((bceSampleClauses.erase [0, 2]).erase [1, 3, 4]) [1, 3, 4] 1
#guard checkModel (cnfOfClauses (bceApplyStack bceSampleStack bceSampleClauses)) bceReducedModel
#guard
  let full := extendBceStackArr bceSampleStack bceReducedModel
  !checkModel (cnfOfClauses bceSampleClauses) bceReducedModel &&
    full == #[false, true, false] &&
    checkModel (cnfOfClauses bceSampleClauses) full

theorem sample_bce_sat :
    let σ := extendBceStackArr bceSampleStack bceReducedModel
    (cnfOfClauses bceSampleClauses).Sat (evalVar σ) ∧
      ¬ (cnfOfClauses bceSampleClauses).Unsat := by
  have hval : BceStackValid bceSampleClauses bceSampleStack := by
    refine ⟨by decide, (isBlockedOnBool_iff _ _ _).mp (by decide),
      by decide, (isBlockedOnBool_iff _ _ _).mp (by decide), trivial⟩
  have hred : checkModel (cnfOfClauses (bceApplyStack bceSampleStack bceSampleClauses))
      bceReducedModel = true := by
    rw [checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hfull := extendBceStackArr_sound hval hred
  exact ⟨(checkModel_iff_sat _ _).mp hfull, (checkModel_sound hfull).1⟩

/-! ## 3. Gate-Restricted BVE (`gates.c`: AND / ITE / XOR) (`LayerAGates`) -/

-- AND gate x0 ↔ (x1 ∧ x2):
--   P_g = [[0, 3, 5]], N_g = [[1, 2], [1, 4]]
-- Non-gate clauses on x0:
--   P_ng = [[0, 6]], N_ng = [[1, 8]], rest = [[7, 9]].
-- Non-tautological P_ng × N_ng resolvent [6, 8] is skipped by gateBveClauses.
def andGatePart : GatePartition :=
  { posGate := [[0, 3, 5]]
    posNonGate := [[0, 6]]
    negGate := [[1, 2], [1, 4]]
    negNonGate := [[1, 8]]
    rest := [[7, 9]] }

#guard gateBveClauses 0 andGatePart == [[7, 9], [3, 5, 8], [6, 2], [6, 4]]
#guard fullBveClauses 0 andGatePart == [[7, 9], [3, 5, 8], [6, 2], [6, 4], [6, 8]]

-- Model of gateBveClauses: x0=false, x1=true, x2=true, x3=false, x4=true.
-- Under x0=false, [0, 3, 5] and [0, 6] are falsified, so extendGateBve flips x0 := true.
def andGateReducedModel : Array Bool := #[false, true, true, false, true]

#guard checkModel (cnfOfClauses (gateBveClauses 0 andGatePart)) andGateReducedModel
#guard
  let full := extendGateBveArr 0 andGatePart.posClauses andGateReducedModel
  !checkModel (cnfOfClauses andGatePart.allClauses) andGateReducedModel &&
    full == #[true, true, true, false, true] &&
    checkModel (cnfOfClauses andGatePart.allClauses) full

theorem sample_andGate_sat :
    let σ := extendGateBveArr 0 andGatePart.posClauses andGateReducedModel
    (cnfOfClauses andGatePart.allClauses).Sat (evalVar σ) ∧
      ¬ (cnfOfClauses andGatePart.allClauses).Unsat := by
  have hpart : GatePartValid 0 andGatePart := by
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hfunc : GateFunctional 0 andGatePart.posGate andGatePart.negGate :=
    andGate_functional (v := 0) (xs := [2, 4]) (by decide)
  have hred : (cnfOfClauses (gateBveClauses 0 andGatePart)).Sat (evalVar andGateReducedModel) := by
    rw [← checkModel_iff_sat, checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hsat : (cnfOfClauses andGatePart.allClauses).Sat
      (evalVar (extendGateBveArr 0 andGatePart.posClauses andGateReducedModel)) := by
    rw [evalVar_extendGateBveArr]
    exact gateFunc_bve_sat hpart hfunc hred
  have hchk : checkModel (cnfOfClauses andGatePart.allClauses)
      (extendGateBveArr 0 andGatePart.posClauses andGateReducedModel) = true :=
    (checkModel_iff_sat _ _).mpr hsat
  exact ⟨hsat, (checkModel_sound hchk).1⟩

-- XOR gate UNSAT example: x0 ↔ (x1 ⊕ x2), plus x1=true ([2]), x2=true ([4]), x0=true ([0]).
def xorUnsatPart : GatePartition :=
  { posGate := [[0, 3, 4], [0, 2, 5]]
    posNonGate := [[0]]
    negGate := [[1, 2, 4], [1, 3, 5]]
    negNonGate := []
    rest := [[2], [4]] }

theorem sample_xorGate_unsat : (cnfOfClauses xorUnsatPart.allClauses).Unsat := by
  apply gateBve_unsat_sound (v := 0)
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  have h2v := (evalLitVal_iff α 2).mpr (hα' [2] (by decide))
  have h4v := (evalLitVal_iff α 4).mpr (hα' [4] (by decide))
  have h35v := (clauseEvalVal_iff α [3, 5]).mpr (hα' [3, 5] (by decide))
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h35v
  have h3 : evalLitVal α 3 = false := by
    rw [show (3 : Nat) = litNeg 2 by decide, evalLitVal_litNeg, h2v]; rfl
  have h5 : evalLitVal α 5 = false := by
    rw [show (5 : Nat) = litNeg 4 by decide, evalLitVal_litNeg, h4v]; rfl
  rw [h3, h5] at h35v; cases h35v

-- Blocked non-gate resolvent example (`gateBlocked_bve_sat`):
-- P_ng = [[0, 2]], N_ng = [[1, 4]], rest = [[3, 6]]; skipped resolvent [2, 4] is blocked on 4.
def blockedGatePart : GatePartition :=
  { posGate := []
    posNonGate := [[0, 2]]
    negGate := []
    negNonGate := [[1, 4]]
    rest := [[3, 6]] }

def blockedGateStack : BceReconStack := [{ lit := 4, clause := [2, 4] }]
def blockedGateReduced : Array Bool := #[false, false, false, false]

#guard gateBveClauses 0 blockedGatePart == [[3, 6]]
#guard fullBveClauses 0 blockedGatePart == [[3, 6], [2, 4]]
#guard
  let full := extendGateBveArr 0 blockedGatePart.posClauses
    (extendBceStackArr blockedGateStack blockedGateReduced)
  full == #[true, false, true, false] &&
    checkModel (cnfOfClauses blockedGatePart.allClauses) full

theorem sample_blocked_gate :
    let σ := extendGateBveArr 0 blockedGatePart.posClauses
      (extendBceStackArr blockedGateStack blockedGateReduced)
    (cnfOfClauses blockedGatePart.allClauses).Sat (evalVar σ) ∧
      ¬ (cnfOfClauses blockedGatePart.allClauses).Unsat := by
  have hpart : GatePartValid 0 blockedGatePart := by
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hval : BceStackValid (fullBveClauses 0 blockedGatePart) blockedGateStack :=
    ⟨by decide, (isBlockedOnBool_iff _ _ _).mp (by decide), trivial⟩
  have hsub : ∀ c ∈ bceApplyStack blockedGateStack (fullBveClauses 0 blockedGatePart),
      c ∈ gateBveClauses 0 blockedGatePart := by decide
  have hred : (cnfOfClauses (gateBveClauses 0 blockedGatePart)).Sat
      (evalVar blockedGateReduced) := by
    rw [← checkModel_iff_sat, checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hsat : (cnfOfClauses blockedGatePart.allClauses).Sat
      (evalVar (extendGateBveArr 0 blockedGatePart.posClauses
        (extendBceStackArr blockedGateStack blockedGateReduced))) := by
    rw [evalVar_extendGateBveArr, evalVar_extendBceStackArr]
    exact gateBlocked_bve_sat hpart hval hsub hred
  have hchk : checkModel (cnfOfClauses blockedGatePart.allClauses)
      (extendGateBveArr 0 blockedGatePart.posClauses
        (extendBceStackArr blockedGateStack blockedGateReduced)) = true :=
    (checkModel_iff_sat _ _).mpr hsat
  exact ⟨hsat, (checkModel_sound hchk).1⟩

/-! ## 4. Bounded Variable Addition / Factorization (`factor.c`) (`LayerAGates`) -/

-- 2 x 3 biclique over variables 0..4:
-- Dividers L = [0, 2] (x0, x1); Quotients Q = [[4], [6], [8]] (x2, x3, x4).
-- Fresh variable z = 5 (lits 10 / 11) factors the 6 product clauses into 2 + 3 = 5 clauses.
def bvaSampleClauses : List (List Nat) :=
  [[0, 4], [0, 6], [0, 8], [2, 4], [2, 6], [2, 8], [1, 3]]

def bvaDivs : List Nat := [0, 2]
def bvaQuots : List (List Nat) := [[4], [6], [8]]

#guard (bvaFactorClauses 5 bvaDivs bvaQuots bvaSampleClauses).length == 6
#guard bvaFactorClauses 5 bvaDivs bvaQuots bvaSampleClauses ==
  [[10, 0], [10, 2], [11, 4], [11, 6], [11, 8], [1, 3]]

-- Model of factored formula: x0=false, x1=true, x2=true, x3=true, x4=true, z(x5)=true.
def bvaFactoredModel : Array Bool := #[false, true, true, true, true, true]

#guard checkModel (cnfOfClauses (bvaFactorClauses 5 bvaDivs bvaQuots bvaSampleClauses))
  bvaFactoredModel
#guard checkModel (cnfOfClauses bvaSampleClauses) bvaFactoredModel

theorem sample_bva_sat :
    (cnfOfClauses bvaSampleClauses).Sat (evalVar bvaFactoredModel) ∧
      ¬ (cnfOfClauses bvaSampleClauses).Unsat := by
  have hfac : (cnfOfClauses (bvaFactorClauses 5 bvaDivs bvaQuots bvaSampleClauses)).Sat
      (evalVar bvaFactoredModel) := by
    rw [← checkModel_iff_sat, checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hsat := bvaFactor_sat_recon hfac
  have hchk : checkModel (cnfOfClauses bvaSampleClauses) bvaFactoredModel = true :=
    (checkModel_iff_sat _ _).mpr hsat
  exact ⟨hsat, (checkModel_sound hchk).1⟩

-- Closed UNSAT proof via BVA/factorization:
-- biclique [0,4], [0,6], [2,4], [2,6] + units [1], [3], [5], [7].
def bvaUnsatClauses : List (List Nat) :=
  [[0, 4], [0, 6], [2, 4], [2, 6], [1], [3], [5], [7]]

theorem sample_bva_unsat : (cnfOfClauses bvaUnsatClauses).Unsat := by
  have hval : BvaValid 5 [0, 2] [[4], [6]] bvaUnsatClauses :=
    bvaValid_of_mem ((varFreshInBool_iff _ _).mp (by decide)) (by decide) (by decide) (by decide)
  apply bvaFactor_unsat_sound hval
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hα' := (cnf_sat_cnfOfClauses_iff α _).mp hα
  have hdiv := (clauseEvalVal_iff α [10, 0]).mpr (hα' [10, 0] (by decide))
  have hquot := (clauseEvalVal_iff α [11, 4]).mpr (hα' [11, 4] (by decide))
  have h1v := (evalLitVal_iff α 1).mpr (hα' [1] (by decide))
  have h5v := (evalLitVal_iff α 5).mpr (hα' [5] (by decide))
  have h0f : evalLitVal α 0 = false := by
    rw [show (0 : Nat) = litNeg 1 by decide, evalLitVal_litNeg, h1v]; rfl
  have h4f : evalLitVal α 4 = false := by
    rw [show (4 : Nat) = litNeg 5 by decide, evalLitVal_litNeg, h5v]; rfl
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, h0f, h4f] at hdiv hquot
  have h10 : evalLitVal α 10 = true := by simpa using hdiv
  have h11 : evalLitVal α 11 = true := by simpa using hquot
  have h11f : evalLitVal α 11 = false := by
    rw [show (11 : Nat) = litNeg 10 by decide, evalLitVal_litNeg, h10]; rfl
  rw [h11] at h11f; cases h11f

/-! ## 5. Unified Elimination Pipeline (`Subst` + `BCE` + `Gate-BVE` + `BVA/Factor`) -/

-- Starting formula on variables x0..x6 (lits 0..13):
--   Equivalence x0 ↔ x1: [1, 2], [0, 3]
--   Blocked clause on x5 (10): [10, 8]
--   AND gate on x1 ↔ (x2 ∧ x3): [2, 5, 7], [3, 4], [3, 6]
--   Non-gate clauses using x0: [0, 8], [1, 9]
--   Rest clauses forming a 2 x 2 biclique with [8, 4], [8, 6]: [12, 4], [12, 6]
-- Step 1: Subst x0 ↦ x1 (2)  (drops [1, 2], [0, 3] as tautologies)
-- Step 2: BCE [10, 8] blocked on 10 (no clause has 11)
-- Step 3: Gate-BVE on x1 (var 1) using AND gate [[2, 5, 7]] / [[3, 4], [3, 6]]
-- Step 4: BVA/Factor on fresh z = 7 (lits 14/15) factoring {8, 12} × {[4], [6]}
def pipeInitClauses : List (List Nat) :=
  [[1, 2], [0, 3], [10, 8], [2, 5, 7], [3, 4], [3, 6], [0, 8], [1, 9], [12, 4], [12, 6]]

def pipeAfterSubst : List (List Nat) :=
  substClauses 0 2 pipeInitClauses

def pipeAfterBce : List (List Nat) :=
  pipeAfterSubst.erase [10, 8]

def pipeGatePart : GatePartition :=
  { posGate := [[2, 5, 7]]
    posNonGate := [[2, 8]]
    negGate := [[3, 4], [3, 6]]
    negNonGate := [[3, 9]]
    rest := [[12, 4], [12, 6]] }

def pipeAfterGate : List (List Nat) :=
  gateBveClauses 1 pipeGatePart

def pipeTrace : TierBTrace :=
  [.subst 0 2, .bce 10 [10, 8], .gateBve 1 pipeGatePart, .bvaFactor 7 [8, 12] [[4], [6]]]

-- Reduced model sets x2=true, x3=true, x7(fresh)=true (all other vars false).
def pipeReducedModel : Array Bool := #[false, false, true, true, false, false, false, true]

#guard tierBTraceApply pipeTrace pipeInitClauses ==
  [[14, 8], [14, 12], [15, 4], [15, 6], [5, 7, 9]]
#guard checkModel (cnfOfClauses (tierBTraceApply pipeTrace pipeInitClauses)) pipeReducedModel
#guard
  let full := tierBTraceExtendArr pipeTrace pipeReducedModel
  !checkModel (cnfOfClauses pipeInitClauses) pipeReducedModel &&
    full == #[true, true, true, true, false, true, false, true] &&
    checkModel (cnfOfClauses pipeInitClauses) full

theorem sample_pipe_sat :
    let σ := tierBTraceExtendArr pipeTrace pipeReducedModel
    (cnfOfClauses pipeInitClauses).Sat (evalVar σ) ∧
      ¬ (cnfOfClauses pipeInitClauses).Unsat := by
  have hstep1 : TierBStepValid pipeInitClauses (.subst 0 2) :=
    ⟨by decide, entails_mem_cnfOfClauses (by decide), entails_mem_cnfOfClauses (by decide)⟩
  have hstep2 : TierBStepValid pipeAfterSubst (.bce 10 [10, 8]) :=
    ⟨by decide, (isBlockedOnBool_iff _ _ _).mp (by decide)⟩
  have hsub1 : ∀ c ∈ pipeAfterBce, c ∈ pipeGatePart.allClauses := by decide
  have hsub2 : ∀ c ∈ pipeGatePart.allClauses, c ∈ pipeAfterBce := by decide
  have hstep3 : TierBStepValid pipeAfterBce (.gateBve 1 pipeGatePart) := by
    refine ⟨?_, ?_, ?_⟩
    · intro α
      simp only [cnf_sat_cnfOfClauses_iff]
      exact ⟨fun h c hc => h c (hsub1 c hc), fun h c hc => h c (hsub2 c hc)⟩
    · refine ⟨?_, ?_, ?_⟩ <;> decide
    · exact gateFunctional_entails (andGate_functional (v := 1) (xs := [4, 6]) (by decide))
  have hstep4 : TierBStepValid pipeAfterGate (.bvaFactor 7 [8, 12] [[4], [6]]) :=
    bvaValid_of_mem ((varFreshInBool_iff _ _).mp (by decide)) (by decide) (by decide) (by decide)
  have hval : TierBTraceValid pipeInitClauses pipeTrace :=
    ⟨hstep1, hstep2, hstep3, hstep4, trivial⟩
  have hred : checkModel (cnfOfClauses (tierBTraceApply pipeTrace pipeInitClauses))
      pipeReducedModel = true := by
    rw [checkModel_cnfOfClauses_eq_evalCnf]
    decide
  have hfull := tierBTraceExtendArr_sound hval hred
  exact ⟨(checkModel_iff_sat _ _).mp hfull, (checkModel_sound hfull).1⟩

#eval substTraceExtendArr substSampleTrace substReducedModelFlip
#eval extendBceStackArr bceSampleStack bceReducedModel
#eval extendGateBveArr 0 andGatePart.posClauses andGateReducedModel
#eval tierBTraceExtendArr pipeTrace pipeReducedModel

/-! ## 6. Single-line `#print axioms` checks -/

#print axioms LeanQbe.T.Examples.Kissat.Ref.subst_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.subst_sat_reconstruct
#print axioms LeanQbe.T.Examples.Kissat.Ref.subst_equisat
#print axioms LeanQbe.T.Examples.Kissat.Ref.subst_var_elim
#print axioms LeanQbe.T.Examples.Kissat.Ref.substTrace_unsat
#print axioms LeanQbe.T.Examples.Kissat.Ref.substTrace_sat
#print axioms LeanQbe.T.Examples.Kissat.Ref.substTrace_equisat
#print axioms LeanQbe.T.Examples.Kissat.Ref.binReach_scc_equiv
#print axioms LeanQbe.T.Examples.Kissat.Ref.binReach_contra_unsat
#print axioms LeanQbe.T.Examples.Kissat.Ref.substMap_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.substMap_sat_recon
#print axioms LeanQbe.T.Examples.Kissat.Ref.bce_extend_sat
#print axioms LeanQbe.T.Examples.Kissat.Ref.bce_erase_unsat
#print axioms LeanQbe.T.Examples.Kissat.Ref.bce_erase_sat
#print axioms LeanQbe.T.Examples.Kissat.Ref.bce_erase_equisat
#print axioms LeanQbe.T.Examples.Kissat.Ref.bceStack_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.bceStack_sat_recon
#print axioms LeanQbe.T.Examples.Kissat.Ref.gateBve_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.gateBve_sat_recon
#print axioms LeanQbe.T.Examples.Kissat.Ref.gateFunc_bve_sat
#print axioms LeanQbe.T.Examples.Kissat.Ref.gateFunc_bve_equisat
#print axioms LeanQbe.T.Examples.Kissat.Ref.gateBlocked_bve_sat
#print axioms LeanQbe.T.Examples.Kissat.Ref.equivGate_functional
#print axioms LeanQbe.T.Examples.Kissat.Ref.andGate_functional
#print axioms LeanQbe.T.Examples.Kissat.Ref.iteGate_functional
#print axioms LeanQbe.T.Examples.Kissat.Ref.xorGate_functional
#print axioms LeanQbe.T.Examples.Kissat.Ref.defGate_functional
#print axioms LeanQbe.T.Examples.Kissat.Ref.bca_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.bvaFactor_unsat_sound
#print axioms LeanQbe.T.Examples.Kissat.Ref.bvaFactor_sat_recon
#print axioms LeanQbe.T.Examples.Kissat.Ref.bvaFactor_equisat
#print axioms LeanQbe.T.Examples.Kissat.Ref.tierBTrace_unsat
#print axioms LeanQbe.T.Examples.Kissat.Ref.tierBTrace_sat_recon
#print axioms sample_subst_sat
#print axioms sample_scc_unsat
#print axioms sample_subst_unsat
#print axioms sample_bce_sat
#print axioms sample_andGate_sat
#print axioms sample_xorGate_unsat
#print axioms sample_blocked_gate
#print axioms sample_bva_sat
#print axioms sample_bva_unsat
#print axioms sample_pipe_sat

end KissatTierBTest
