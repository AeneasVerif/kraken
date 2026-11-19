module

public import LeanQbe.T.Examples.Kissat.LayerAMinimize
public import LeanQbe.T.Examples.Kissat.LayerACollect
meta import LeanQbe.T.Examples.Kissat.Core
meta import LeanQbe.T.Examples.Kissat.LayerAMinimize1
meta import LeanQbe.T.Examples.Kissat.LayerAMinimize2
meta import LeanQbe.T.Examples.Kissat.LayerAMinimize3
meta import LeanQbe.T.Examples.Kissat.LayerAMinimize
meta import LeanQbe.T.Examples.Kissat.LayerACollect1
meta import LeanQbe.T.Examples.Kissat.LayerACollect

/-!
# Verification and Axiom Audit for Kissat Pure-Lean Layer-A Theories

Executable `#guard` and `#eval` tests exercising:
1. Lazy `(level, trailPos)` ordering, `seedRemovable`, early failures (`poisoned`, `maxDepth`),
   binary-chain caching, and multi-depth iterative DFS worklist minimization.
2. `shrinkBlockExec` and multi-block `shrinkClauseExec` (`alwaysMin` / `resolveLarge` fallback).
3. `analyzeFailedLiteralExec` intermediate unit emission and `G4` empty-trail guard.
4. `markGarbageIf`, `deleteUnreferencedClauses`, `sweepClauses` + `applyRefTargets` (binary
   promotion + root-literal stripping), `partitionIrredFirst`, and `reduceAndCollect`.
5. Single-line `#print axioms` checks (`<= 120` cols, standard axioms only).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatLayerATest

open Std.Sat
open LeanQbe.T.Examples.Kissat

/-! ## 1. Iterative `minimize` (`LayerAMinimize1` & `LayerAMinimize2`) -/

@[expose] public def lazyMinCdcl : CdclState :=
  -- Variables 0..6:
  -- x0 (0): unit @ level 0, trail[0]
  -- x1 (2): decision @ level 1, trail[1]
  -- x2 (4): decision @ level 2, trail[2]
  -- x3 (6): large 0 [3, 5, 6] @ level 2, trail[3]
  -- x4 (8): binary 3 [3, 8] @ lazy level 1, trail[4] (later than level-2 x2, x3!)
  -- x5 (10): large 1 [1, 9, 10] @ level 2, trail[5] (depends on root0 ¬x0 + lazy ¬x4)
  -- x6 (12): large 2 [11, 7, 12] @ level 2, trail[6] (multi-depth DAG via x5 and x3)
  { f0 := cnfOfClauses [[0], [3, 8], [3, 5, 6], [1, 9, 10], [11, 7, 12]]
    numVars := 7
    clauses := #[some { lits := [3, 5, 6] }, some { lits := [1, 9, 10] },
      some { lits := [11, 7, 12] }]
    units := [0]
    trail := #[0, 2, 4, 6, 8, 10, 12]
    levels := #[0, 1, 2, 2, 1, 2, 2]
    reasons := #[.unit, .decision, .decision, .large 0, .binary 3, .large 1, .large 2]
    level := 2
    inconsistent := false }

@[expose] public def lazyMinInit : MinState :=
  MinState.ofCdcl lazyMinCdcl #[0, 2, 4]

#guard lazyMinInit.varTrailPos 4 == 4 && lazyMinInit.varTrailPos 2 == 2
#guard lazyMinInit.litLevel 9 == 1 && lazyMinInit.litLevel 6 == 2

#guard
  let seeded := seedRemovable lazyMinInit [3, 5, 13]
  seeded.isRemovable 1 && seeded.isRemovable 2 && seeded.isRemovable 6 &&
    !seeded.isRemovable 4 && !seeded.isRemovable 5

#guard
  -- Multi-depth minimization eliminates ¬x6 (13) through x5->x4->x1 and x3->{x1,x2},
  -- while caching intermediate binary/large variables (4, 5, 3) as removable.
  let (kept, st') := minimizeClauseWorklist lazyMinInit 10 [3, 5, 13]
  kept == [3, 5] && st'.isRemovable 4 && st'.isRemovable 5 && st'.isRemovable 3

#guard
  -- Depth limit maxDepth = 1 rejects depth-2 recursion through ¬x6 (13) cleanly.
  let seeded := seedRemovable lazyMinInit [3, 5, 13]
  !(minimizeLiteralWorklist seeded true 1 13 0).1

#guard
  -- Poisoned antecedent cleanly blocks minimization early.
  let poisoned := (seedRemovable lazyMinInit [3, 5, 11]).setPoisoned 4 true
  !(minimizeLiteralWorklist poisoned true 10 11 0).1

#guard
  -- frameUsed <= 1 prevents descending at level 1 when only 1 literal from level 1 is seen.
  let singleFrame := MinState.ofCdcl lazyMinCdcl #[0, 1, 4]
  let (kept, _) := minimizeClauseWorklist singleFrame 10 [3, 5, 11]
  kept == [3, 5, 11]

/-! ## 2. Block `shrink` and failed-literal probing (`LayerAMinimize3` & `LayerAMinimize`) -/

private def shrinkTestCdcl : CdclState :=
  -- Variables 0..5:
  -- x0 (0): unit @ level 0, trail[0]
  -- x1 (2): decision @ level 1, trail[1]
  -- x2 (4): decision @ level 2, trail[2]
  -- x3 (6): binary 3 @ lazy level 1, trail[3]
  -- x4 (8): binary 5 @ level 2, trail[4]
  -- x5 (10): large 0 [1, 5, 9, 10] @ level 2, trail[5]
  { f0 := cnfOfClauses [[0], [3, 6], [5, 8], [1, 5, 9, 10]]
    numVars := 6
    clauses := #[some { lits := [1, 5, 9, 10] }]
    units := [0]
    trail := #[0, 2, 4, 6, 8, 10]
    levels := #[0, 1, 2, 1, 2, 2]
    reasons := #[.unit, .decision, .decision, .binary 3, .binary 5, .large 0]
    level := 2
    inconsistent := false }

private def shrinkTestInit : MinState :=
  MinState.ofCdcl shrinkTestCdcl #[0, 2, 3]

#guard splitLevelBlocksRev shrinkTestInit [3, 7, 9, 11] ==
  [(2, [9, 11]), (1, [3, 7])]

#guard
  -- Shrinking level-2 block [9, 11] reaches UIP x2 (4) -> [5] and marks {2,4,5} removable.
  let (ok, outB, st') := shrinkBlockExec shrinkTestInit false true 10 2 [9, 11]
  ok && outB == [5] && st'.isRemovable 2 && st'.isRemovable 4 && st'.isRemovable 5

#guard
  -- Full clause shrinking collapses both level-2 [9, 11] -> [5] and lazy level-1 [3, 7] -> [3].
  let (c', st') := shrinkClauseExec shrinkTestInit false true 10 [3, 7, 9, 11]
  c' == [3, 5] && st'.isRemovable 1 && st'.isRemovable 2 && st'.isRemovable 3

#guard
  -- With resolveLarge = false, level-2 block [9, 11] falls back cleanly to minimization;
  -- level-1 block [3, 7] (binary reasons only) still shrinks to [3].
  let (c', _) := shrinkClauseExec shrinkTestInit false false 10 [3, 7, 9, 11]
  c' == [3, 9, 11]

#guard
  -- With alwaysMin = true, resolving ¬x5 along [1, 5, 7, 9, 10] minimizes lower-level ¬x3 (7)
  -- using cached isRemovable 1; with alwaysMin = false (without isRemovable 3), shrink stops.
  let cl7 : Clause := { lits := [1, 5, 7, 9, 10] }
  let cdcl7 := { shrinkTestCdcl with
    f0 := cnfOfClauses [[0], [3, 6], [5, 8], [1, 5, 7, 9, 10]]
    clauses := #[some cl7] }
  let seeded := (MinState.ofCdcl cdcl7 #[0, 2, 3]).setRemovable 1 true
  let (okT, outT, _) := shrinkBlockExec seeded true true 10 2 [9, 11]
  let (okF, _, _) := shrinkBlockExec seeded false true 10 2 [9, 11]
  okT && outT == [5] && !okF

private def failedLitExecCdcl : CdclState :=
  -- failed = x0 (0) @ level 1; x1 (2) via binary [1, 2]; x2 (4) via binary [3, 4];
  -- x3 (6) via large [3, 5, 6]; conflict [5, 7].
  -- Resolving x3 -> [3, 5] -> [3, ¬x1], resolving x2 -> [¬x1] emits unit 3 (¬x1),
  -- then hits other == notFailed (1) and returns [3, 1].
  { f0 := cnfOfClauses [[1, 2], [3, 4], [3, 5, 6], [5, 7]]
    numVars := 4
    clauses := #[some { lits := [3, 5, 6] }]
    units := []
    trail := #[0, 2, 4, 6]
    levels := #[1, 1, 1, 1]
    reasons := #[.decision, .binary 1, .binary 3, .large 0]
    level := 1
    inconsistent := false }

#guard analyzeFailedLiteralExec failedLitExecCdcl 0 [5, 7] == [3, 1]
#guard analyzeFailedLiteralExec { failedLitExecCdcl with trail := #[] } 0 [5, 7] == [1]

/-! ## 3. Clause sweep, binary promotion, partition, and `reduceAndCollect` (`LayerACollect`) -/

@[expose] public def collectRichState : CdclState :=
  -- x0 (0): unit @ level 0 (so lit 0 is root-true, lit 1 is root-false)
  -- x1 (2): decision @ level 1
  -- x2 (4): large 0 [1, 3, 4] @ level 1 -> root-false lit 1 stripped -> [3, 4] -> binary!
  -- x3 (6): large 5 [3, 5, 6] @ level 1 -> 3-literal irredundant clause moved to front!
  { f0 := cnfOfClauses [[0], [1, 3, 4], [0, 5], [3, 5, 7], [2, 5, 7], [3, 5, 6]]
    numVars := 4
    clauses := #[
      some { lits := [1, 3, 4], redundant := true, garbage := false },
      none,
      some { lits := [0, 5], redundant := false, garbage := false },
      some { lits := [3, 5, 7], redundant := true, garbage := false },
      some { lits := [2, 5, 7], redundant := true, garbage := false },
      some { lits := [3, 5, 6], redundant := false, garbage := false }
    ]
    units := [0]
    trail := #[0, 2, 4, 6]
    levels := #[0, 1, 1, 1]
    reasons := #[.unit, .decision, .large 0, .large 5]
    level := 1
    inconsistent := false }

#guard
  -- markGarbageIf marks cid 3 garbage, but never marks active reason cid 0 or 5.
  let s1 := markGarbageIf collectRichState fun cid _c => cid == 0 || cid == 3
  match s1.clauses[0]?, s1.clauses[3]? with
  | some (some c0), some (some c3) => !c0.garbage && c3.garbage
  | _, _ => false

#guard
  -- deleteUnreferencedClauses drops cid 3 when deleted by predicate, keeps active cid 0 and cid 5.
  let s1 := deleteUnreferencedClauses collectRichState fun cid _c => cid == 0 || cid == 3
  s1.clauses[0]?.isSome && (s1.clauses[0]?.join.isSome) &&
    s1.clauses[3]? == some none && (s1.clauses[5]?.join.isSome)

#guard
  -- sweepClauses promotes cid 0 ([1, 3, 4] -> [3, 4]) to .toBinary 3 4, drops cid 1, cid 2, cid 3.
  let (swCls, bins, tgts) := sweepClauses (markGarbageIf collectRichState fun cid _ => cid == 3)
  let s2 := applyRefTargets collectRichState swCls tgts
  bins == [(3, 4)] && swCls.size == 2 &&
    stateReason s2 4 == .binary 3 && stateReason s2 6 == .large 1

#guard
  -- reduceAndCollect marks cid 3 garbage, sweeps, promotes cid 0 to binary (3, 4),
  -- and partitions irredundant [3, 5, 6] (idx 0) before redundant [2, 5, 7] (idx 1).
  let (s3, bins) := reduceAndCollect collectRichState fun cid _ => cid == 3
  bins == [(3, 4)] && s3.clauses.size == 2 &&
    match s3.clauses[0]?, s3.clauses[1]? with
    | some (some c0), some (some c1) =>
      !c0.redundant && c0.lits == [3, 5, 6] &&
      c1.redundant && c1.lits == [2, 5, 7] &&
      stateReason s3 4 == .binary 3 && stateReason s3 6 == .large 0
    | _, _ => false

#eval (minimizeClauseWorklist lazyMinInit 10 [3, 5, 13]).1
#eval (reduceAndCollect collectRichState fun cid _ => cid == 3).2

/-! ## 4. `flushRootReasons` executable checks & closed non-vacuity corollaries -/

@[expose] public def coreFlushF0 : CNF Nat :=
  cnfOfClauses [[0], [1, 2], [1, 3, 4], [1, 7, 8]]

private def coreFlushRun : CdclState :=
  match propagateAll 16 (initState coreFlushF0) with
  | .ok s0 =>
    match propagateAll 16 (decideLit s0 6) with
    | .ok s1 => s1
    | _ => s0
  | _ => initState coreFlushF0

@[expose] public def coreFlushManual : CdclState :=
  let s0 := initState coreFlushF0
  let s1 := assignLit s0 0 s0.level (.large 0)
  let s2 := assignLit s1 2 s1.level (.binary 1)
  let s3 := assignLit s2 4 s2.level (.large 2)
  let s4 := decideLit s3 6
  assignLit s4 8 s4.level (.large 3)

#guard
  let sf := flushRootReasons coreFlushRun
  coreFlushRun.trail == coreFlushManual.trail &&
  coreFlushRun.levels == coreFlushManual.levels &&
  coreFlushRun.reasons == coreFlushManual.reasons &&
  coreFlushRun.trail == #[0, 2, 4, 6, 8] &&
  stateReason coreFlushRun 0 == .large 0 &&
  stateReason sf 0 == .unit && stateReason sf 2 == .unit && stateReason sf 4 == .unit &&
  stateReason sf 6 == .decision && stateReason sf 8 == .large 3 &&
  (reduceAndCollect sf fun _ _ => false).2 == [(7, 8)]

private theorem lazyMin_f0 :
    lazyMinCdcl.f0 = cnfOfClauses [[0], [3, 8], [3, 5, 6], [1, 9, 10], [11, 7, 12]] := rfl

private theorem collectRich_f0 :
    collectRichState.f0 = cnfOfClauses [[0], [1, 3, 4], [0, 5], [3, 5, 7], [2, 5, 7], [3, 5, 6]] :=
  rfl

private theorem entails_of_mem_clauses {cs : List (List Nat)} {c : List Nat} (hc : c ∈ cs) :
    (cnfOfClauses cs).EntailsClause (cnfClause c) :=
  CNF.entails_clause_def.mpr fun α hα => (cnf_sat_cnfOfClauses_iff α cs).mp hα c hc

private theorem stateLevel_initState (cnf : CNF Nat) (x : Nat) :
    stateLevel (initState cnf) x = 0 := by
  simp only [stateLevel, initState, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

private theorem lazyMin_sz : lazyMinCdcl.trail.size = 7 := by decide
private theorem lazyMin_tr (k : Fin 7) :
    lazyMinCdcl.trail[k.1]'(Nat.lt_of_lt_of_eq k.2 lazyMin_sz.symm) =
      [0, 2, 4, 6, 8, 10, 12][k.1] := by decide +revert
private theorem lazyMin_rs (k : Fin 7) :
    stateReason lazyMinCdcl
      (lazyMinCdcl.trail[k.1]'(Nat.lt_of_lt_of_eq k.2 lazyMin_sz.symm)) =
      [.unit, .decision, .decision, .large 0, .binary 3, .large 1, .large 2][k.1] := by
  decide +revert

private theorem lazyMin_trl {i : Nat} (hi : i < lazyMinCdcl.trail.size) :
    lazyMinCdcl.trail[i]'hi = [0, 2, 4, 6, 8, 10, 12][i]'(Nat.lt_of_lt_of_eq hi lazyMin_sz) :=
  lazyMin_tr ⟨i, Nat.lt_of_lt_of_eq hi lazyMin_sz⟩

private theorem lazyMin_rsl {i : Nat} (hi : i < lazyMinCdcl.trail.size) :
    stateReason lazyMinCdcl (lazyMinCdcl.trail[i]'hi) =
      [.unit, .decision, .decision, .large 0, .binary 3, .large 1, .large 2][i]'(
        Nat.lt_of_lt_of_eq hi lazyMin_sz) :=
  lazyMin_rs ⟨i, Nat.lt_of_lt_of_eq hi lazyMin_sz⟩

private theorem collectRich_sz : collectRichState.trail.size = 4 := by decide
private theorem collectRich_tr (k : Fin 4) :
    collectRichState.trail[k.1]'(Nat.lt_of_lt_of_eq k.2 collectRich_sz.symm) =
      [0, 2, 4, 6][k.1] := by decide +revert
private theorem collectRich_rs (k : Fin 4) :
    stateReason collectRichState
      (collectRichState.trail[k.1]'(Nat.lt_of_lt_of_eq k.2 collectRich_sz.symm)) =
      [.unit, .decision, .large 0, .large 5][k.1] := by decide +revert

private theorem collectRich_trl {i : Nat} (hi : i < collectRichState.trail.size) :
    collectRichState.trail[i]'hi = [0, 2, 4, 6][i]'(Nat.lt_of_lt_of_eq hi collectRich_sz) :=
  collectRich_tr ⟨i, Nat.lt_of_lt_of_eq hi collectRich_sz⟩

private theorem collectRich_rsl {i : Nat} (hi : i < collectRichState.trail.size) :
    stateReason collectRichState (collectRichState.trail[i]'hi) =
      [.unit, .decision, .large 0, .large 5][i]'(Nat.lt_of_lt_of_eq hi collectRich_sz) :=
  collectRich_rs ⟨i, Nat.lt_of_lt_of_eq hi collectRich_sz⟩

/-- Closed proof that `lazyMinCdcl` satisfies `LazyTrailInv` (even without `levels_mono`). -/
public theorem nv_lazyMin_inv : LazyTrailInv lazyMinCdcl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => by simp [lazyMinCdcl] at h⟩
  · have hfin : ∀ i j : Fin 7,
        litVar lazyMinCdcl.trail[i.1] = litVar lazyMinCdcl.trail[j.1] → i = j := by decide
    intro i j hi hj h; exact congrArg Fin.val (hfin ⟨i, hi⟩ ⟨j, hj⟩ h)
  · have hfin : ∀ i : Fin 7,
        stateLevel lazyMinCdcl lazyMinCdcl.trail[i.1] ≤ lazyMinCdcl.level := by decide
    intro i hi; exact hfin ⟨i, hi⟩
  · have hfin : ∀ i j : Fin 7,
        stateLevel lazyMinCdcl lazyMinCdcl.trail[i.1] =
          stateLevel lazyMinCdcl lazyMinCdcl.trail[j.1] →
        stateReason lazyMinCdcl lazyMinCdcl.trail[j.1] = .decision → j.1 ≤ i.1 := by decide
    intro i j hi hj hleq hrd; exact hfin ⟨i, hi⟩ ⟨j, hj⟩ hleq hrd
  · intro cid c hget
    match cid with
    | 0 => simp [lazyMinCdcl] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 1 => simp [lazyMinCdcl] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 2 => simp [lazyMinCdcl] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | _ + 3 => simp [lazyMinCdcl] at hget
  · intro u hu; simp [lazyMinCdcl] at hu; subst hu; exact entails_of_mem_clauses (by decide)
  · intro i hi
    dsimp only
    have htri := lazyMin_trl hi
    have hsri := lazyMin_rsl hi
    match i with
    | 0 =>
      simp only [List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨by decide, ?_⟩
      rw [lazyMin_f0]
      exact entails_of_mem_clauses (by decide)
    | 1 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      exact by decide
    | 2 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      exact by decide
    | 3 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨{ lits := [3, 5, 6] }, by simp [lazyMinCdcl], rfl, by decide, fun x hx hxne => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have hx1 : stateLevel lazyMinCdcl 3 = 1 := by decide
        have hl3 : stateLevel lazyMinCdcl 6 = 2 := by decide
        exact ⟨1, by omega, by omega, by simp [lazyMin_tr ⟨1, by omega⟩, litNeg],
          by rw [hx1, hl3]; omega, Or.inl (by rw [hx1, hl3]; omega)⟩
      · have hx2 : stateLevel lazyMinCdcl 5 = 2 := by decide
        have hl3 : stateLevel lazyMinCdcl 6 = 2 := by decide
        exact ⟨2, by omega, by omega, by simp [lazyMin_tr ⟨2, by omega⟩, litNeg],
          by rw [hx2, hl3]; omega, Or.inr ⟨by rw [hx2, hl3], by omega⟩⟩
      · exact absurd rfl hxne
    | 4 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      have hx3 : stateLevel lazyMinCdcl 3 = 1 := by decide
      have hl4 : stateLevel lazyMinCdcl 8 = 1 := by decide
      refine ⟨?_, 1, by omega, by omega, by simp [lazyMin_tr ⟨1, by omega⟩, litNeg],
        by rw [hx3, hl4]; omega, Or.inr ⟨by rw [hx3, hl4], by omega⟩⟩
      rw [lazyMin_f0]
      exact entails_swap2 (entails_of_mem_clauses (by decide))
    | 5 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨{ lits := [1, 9, 10] }, by simp [lazyMinCdcl], rfl, by decide, fun x hx hxne => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have hx1 : stateLevel lazyMinCdcl 1 = 0 := by decide
        have hl5 : stateLevel lazyMinCdcl 10 = 2 := by decide
        exact ⟨0, by omega, by omega, by simp [lazyMin_tr ⟨0, by omega⟩, litNeg],
          by rw [hx1, hl5]; omega, Or.inl (by rw [hx1, hl5]; omega)⟩
      · have hx9 : stateLevel lazyMinCdcl 9 = 1 := by decide
        have hl5 : stateLevel lazyMinCdcl 10 = 2 := by decide
        exact ⟨4, by omega, by omega, by simp [lazyMin_tr ⟨4, by omega⟩, litNeg],
          by rw [hx9, hl5]; omega, Or.inl (by rw [hx9, hl5]; omega)⟩
      · exact absurd rfl hxne
    | 6 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨{ lits := [11, 7, 12] }, by simp [lazyMinCdcl], rfl, by decide, fun x hx hxne => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have hx11 : stateLevel lazyMinCdcl 11 = 2 := by decide
        have hl6 : stateLevel lazyMinCdcl 12 = 2 := by decide
        exact ⟨5, by omega, by omega, by simp [lazyMin_tr ⟨5, by omega⟩, litNeg],
          by rw [hx11, hl6]; omega, Or.inr ⟨by rw [hx11, hl6], by omega⟩⟩
      · have hx7 : stateLevel lazyMinCdcl 7 = 2 := by decide
        have hl6 : stateLevel lazyMinCdcl 12 = 2 := by decide
        exact ⟨3, by omega, by omega, by simp [lazyMin_tr ⟨3, by omega⟩, litNeg],
          by rw [hx7, hl6]; omega, Or.inr ⟨by rw [hx7, hl6], by omega⟩⟩
      · exact absurd rfl hxne
    | _ + 7 => exact absurd (Nat.lt_of_lt_of_eq hi lazyMin_sz) (by omega)

@[expose] public def lazyMinStateC : MinState :=
  MinState.ofCdcl { lazyMinCdcl with f0 := lazyMinCdcl.f0.add (cnfClause [3, 5, 13]) } #[0, 2, 4]

/-- Closed corollary instantiating `minimize_worklist_sound` on `lazyMinStateC` and `[3, 5, 13]`. -/
public theorem nv_minimize_sound :
    let res := minimizeClauseWorklist lazyMinStateC 10 [3, 5, 13]
    MinBaseInv res.2 ∧
    lazyMinStateC.cdcl.f0.EntailsClause (cnfClause res.1) ∧
    (∀ l ∈ res.1, l ∈ [3, 5, 13]) := by
  let cdclC : CdclState := { lazyMinCdcl with f0 := lazyMinCdcl.f0.add (cnfClause [3, 5, 13]) }
  have hrs_eq : ∀ x, stateReason cdclC x = stateReason lazyMinCdcl x := fun _ => rfl
  have hlv_eq : ∀ x, stateLevel cdclC x = stateLevel lazyMinCdcl x := fun _ => rfl
  have htr_eq : cdclC.trail = lazyMinCdcl.trail := rfl
  have hcl_eq : cdclC.clauses = lazyMinCdcl.clauses := rfl
  have hinv_add : LazyTrailInv cdclC := by
    have h0 := nv_lazyMin_inv
    refine ⟨h0.vars_nodup, h0.levels_le, h0.dec_earliest, ?_, ?_, ?_, ?_⟩
    · intro cid c hget
      exact CNF.entails_clause_def.mpr fun α hα =>
        CNF.entails_clause_def.mp (h0.db_sound cid c hget) α (CNF.sat_add.mp hα).2
    · intro u hu
      exact CNF.entails_clause_def.mpr fun α hα =>
        CNF.entails_clause_def.mp (h0.units_sound u hu) α (CNF.sat_add.mp hα).2
    · intro i hi
      have hrd := h0.reason_dag i hi
      dsimp only at hrd ⊢
      simp only [hrs_eq, hlv_eq, htr_eq, hcl_eq]
      cases hrsn : stateReason lazyMinCdcl lazyMinCdcl.trail[i] with
      | decision | large _ => simpa [hrsn] using hrd
      | unit =>
        rw [hrsn] at hrd
        simpa [hrsn] using ⟨hrd.1, CNF.entails_clause_def.mpr fun α hα =>
          CNF.entails_clause_def.mp hrd.2 α (CNF.sat_add.mp hα).2⟩
      | binary other =>
        rw [hrsn] at hrd
        simpa [hrsn] using ⟨CNF.entails_clause_def.mpr fun α hα =>
          CNF.entails_clause_def.mp hrd.1 α (CNF.sat_add.mp hα).2,
          let ⟨j, hj1, hj2, heq, hle, hlex⟩ := hrd.2
          ⟨j, hj2, ⟨hj1, heq⟩, hle, hlex⟩⟩
    · intro hinc; exact absurd hinc (by simp [cdclC, lazyMinCdcl])
  have hbase : MinBaseInv lazyMinStateC := MinBaseInv.ofCdcl hinv_add #[0, 2, 4]
  have hrem := removableInv_of_ofCdcl cdclC #[0, 2, 4] [3, 5, 13]
  have hc : lazyMinStateC.cdcl.f0.EntailsClause (cnfClause [3, 5, 13]) :=
    CNF.entails_clause_def.mpr fun α hα => (CNF.sat_add.mp hα).1
  have hfals : ∀ l ∈ [3, 5, 13], litNeg l ∈ lazyMinStateC.cdcl.trail.toList := by decide
  have hm := minimize_worklist_sound hbase hc hrem hfals 10
  have hent := hm.2.2.2.1
  rw [hm.2.1] at hent
  exact ⟨hm.1, hent, hm.2.2.2.2.2.2.1⟩

/-- Closed proof that `collectRichState` satisfies `LazyTrailInv`, `ReasonLevelsPos`, and
`ReasonHasNonRootAntecedent`. -/
public theorem nv_collectRich_inv :
    LazyTrailInv collectRichState ∧
    ReasonLevelsPos collectRichState ∧
    ReasonHasNonRootAntecedent collectRichState := by
  have hc0 : collectRichState.clauses[0]? =
      some (some { lits := [1, 3, 4], redundant := true, garbage := false }) := by decide
  have hc5 : collectRichState.clauses[5]? =
      some (some { lits := [3, 5, 6], redundant := false, garbage := false }) := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => by simp [collectRichState] at h⟩, ?_, ?_⟩
  · have hfin : ∀ i j : Fin 4,
        litVar collectRichState.trail[i.1] = litVar collectRichState.trail[j.1] → i = j := by
      decide
    intro i j hi hj h; exact congrArg Fin.val (hfin ⟨i, hi⟩ ⟨j, hj⟩ h)
  · have hfin : ∀ i : Fin 4,
        stateLevel collectRichState collectRichState.trail[i.1] ≤ collectRichState.level := by
      decide
    intro i hi; exact hfin ⟨i, hi⟩
  · have hfin : ∀ i j : Fin 4,
        stateLevel collectRichState collectRichState.trail[i.1] =
          stateLevel collectRichState collectRichState.trail[j.1] →
        stateReason collectRichState collectRichState.trail[j.1] = .decision →
        j.1 ≤ i.1 := by decide
    intro i j hi hj hleq hrd; exact hfin ⟨i, hi⟩ ⟨j, hj⟩ hleq hrd
  · intro cid c hget
    match cid with
    | 0 => simp [collectRichState] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 1 => simp [collectRichState] at hget
    | 2 => simp [collectRichState] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 3 => simp [collectRichState] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 4 => simp [collectRichState] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | 5 => simp [collectRichState] at hget; subst hget; exact entails_of_mem_clauses (by decide)
    | _ + 6 => simp [collectRichState] at hget
  · intro u hu; simp [collectRichState] at hu; subst hu; exact entails_of_mem_clauses (by decide)
  · intro i hi
    dsimp only
    have htri := collectRich_trl hi
    have hsri := collectRich_rsl hi
    match i with
    | 0 =>
      simp only [List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨by decide, ?_⟩
      rw [collectRich_f0]
      exact entails_of_mem_clauses (by decide)
    | 1 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      exact by decide
    | 2 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨{ lits := [1, 3, 4], redundant := true, garbage := false },
        hc0, rfl, by decide, fun x hx hxne => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have hx1 : stateLevel collectRichState 1 = 0 := by decide
        have hl2 : stateLevel collectRichState 4 = 1 := by decide
        exact ⟨0, by omega, by omega, by simp [collectRich_tr ⟨0, by omega⟩, litNeg],
          by rw [hx1, hl2]; omega, Or.inl (by rw [hx1, hl2]; omega)⟩
      · have hx3 : stateLevel collectRichState 3 = 1 := by decide
        have hl2 : stateLevel collectRichState 4 = 1 := by decide
        exact ⟨1, by omega, by omega, by simp [collectRich_tr ⟨1, by omega⟩, litNeg],
          by rw [hx3, hl2]; omega, Or.inr ⟨by rw [hx3, hl2], by omega⟩⟩
      · exact absurd rfl hxne
    | 3 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri, htri]
      refine ⟨{ lits := [3, 5, 6], redundant := false, garbage := false },
        hc5, rfl, by decide, fun x hx hxne => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have hx3 : stateLevel collectRichState 3 = 1 := by decide
        have hl3 : stateLevel collectRichState 6 = 1 := by decide
        exact ⟨1, by omega, by omega, by simp [collectRich_tr ⟨1, by omega⟩, litNeg],
          by rw [hx3, hl3]; omega, Or.inr ⟨by rw [hx3, hl3], by omega⟩⟩
      · have hx5 : stateLevel collectRichState 5 = 1 := by decide
        have hl3 : stateLevel collectRichState 6 = 1 := by decide
        exact ⟨2, by omega, by omega, by simp [collectRich_tr ⟨2, by omega⟩, litNeg],
          by rw [hx5, hl3]; omega, Or.inr ⟨by rw [hx5, hl3], by omega⟩⟩
      · exact absurd rfl hxne
    | _ + 4 => exact absurd (Nat.lt_of_lt_of_eq hi collectRich_sz) (by omega)
  · intro i hi cid hrsn
    have htri := collectRich_trl hi
    have hsri := collectRich_rsl hi
    match i with
    | 0 | 1 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri
      rw [hsri] at hrsn; cases hrsn
    | 2 | 3 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at htri
      rw [htri]; exact by decide
    | _ + 4 => exact absurd (Nat.lt_of_lt_of_eq hi collectRich_sz) (by omega)
  · intro i hi cid c hrsn hget
    have htri := collectRich_trl hi
    have hsri := collectRich_rsl hi
    match i with
    | 0 | 1 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri
      rw [hsri] at hrsn; cases hrsn
    | 2 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri] at hrsn; injection hrsn with hcid; subst hcid
      rw [hc0] at hget; injection hget with h1; injection h1 with hce; subst hce
      rw [htri]
      have hx3 : 0 < stateLevel collectRichState 3 := by decide
      exact ⟨3, by simp, by decide, hx3⟩
    | 3 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hsri htri
      rw [hsri] at hrsn; injection hrsn with hcid; subst hcid
      rw [hc5] at hget; injection hget with h1; injection h1 with hce; subst hce
      rw [htri]
      have hx3 : 0 < stateLevel collectRichState 3 := by decide
      exact ⟨3, by simp, by decide, hx3⟩
    | _ + 4 => exact absurd (Nat.lt_of_lt_of_eq hi collectRich_sz) (by omega)

/-- Closed corollary instantiating `sweepClauses_sound` (`RefTargetSound`) and
`reduceAndCollect_sound` on `collectRichState`. -/
public theorem nv_collectRich_sound :
    let sw := sweepClauses (markGarbageIf collectRichState fun cid _ => cid == 3)
    let res := reduceAndCollect collectRichState fun cid _ => cid == 3
    RefTargetSound (markGarbageIf collectRichState fun cid _ => cid == 3) sw.1 sw.2.1 sw.2.2 ∧
    LazyTrailInv res.1 ∧
    ∀ α : Nat → Bool, collectRichState.f0.Sat α →
      (survivingCnf res.1.clauses ++ binariesCnf res.2).Sat α := by
  have ⟨hinv, hpos, hnr⟩ := nv_collectRich_inv
  have hm := markGarbageIf_sound hinv fun cid _ => cid == 3
  have hsw := sweepClauses_sound hm.1 (hm.2.2.2.1 hpos) (hm.2.2.2.2.1 hnr)
  have hrd := reduceAndCollect_sound hinv hpos hnr fun cid _ => cid == 3
  exact ⟨hsw, hrd.1, hrd.2.2.2.2.2.2.2.1⟩

/-- Closed end-to-end corollary connecting `Core` transitions (`initState` + `assignLit` +
`decideLit`) through `flushRoot_of_trailInv` to `reduceAndCollect_sound`. -/
public theorem nv_core_flush_reduce :
    let sf := flushRootReasons coreFlushManual
    let res := reduceAndCollect sf fun _ _ => false
    LazyTrailInv sf ∧ ReasonLevelsPos sf ∧ ReasonHasNonRootAntecedent sf ∧
    LazyTrailInv res.1 ∧
    ∀ α : Nat → Bool, coreFlushF0.Sat α →
      (survivingCnf res.1.clauses ++ binariesCnf res.2).Sat α := by
  have h0 := initState_inv coreFlushF0
  have hcl : ∀ (k : Nat) (cs : List (List Nat)), (hk : k < cs.length) →
      (initState (cnfOfClauses cs)).clauses[k]? = some (some { lits := cs[k] }) := by
    intro k cs hk
    simp [initState, cnfOfClauses, hk]
  have h1 := assignProp_inv h0.1 (l := 0) (rsn := .large 0)
    (by simp [initState, litStatus]) (by simp)
    ⟨{ lits := [0] }, hcl 0 [[0], [1, 2], [1, 3, 4], [1, 7, 8]] (by decide), rfl, by simp,
      fun x hx hxne => by simp only [List.mem_singleton] at hx; exact absurd hx hxne⟩
  have h2 := assignProp_inv h1.1 (l := 2) (rsn := .binary 1)
    (by simp [initState, litStatus, litNeg]) (by simp)
    ⟨by rw [h1.2]; exact entails_swap2 (entails_of_mem_clauses (cs := [[0], [1, 2], [1, 3, 4],
        [1, 7, 8]]) (by simp)),
      0, by simp [initState], by simp [initState, litNeg],
      by simp [litVar], Or.inr ⟨by simp [litVar], by simp [initState]⟩⟩
  have h3 := assignProp_inv h2.1 (l := 4) (rsn := .large 2)
    (by simp [initState, litStatus, litNeg]) (by simp)
    ⟨{ lits := [1, 3, 4] },
      by simpa [coreFlushF0] using hcl 2 [[0], [1, 2], [1, 3, 4], [1, 7, 8]] (by decide),
      rfl, by simp, fun x hx hxne => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, by simp [initState], by simp [initState, litNeg],
            by simp [litVar], Or.inr ⟨by simp [litVar], by simp [initState]⟩⟩
        · exact ⟨1, by simp [initState], by simp [initState, litNeg],
            by simp [litVar], Or.inr ⟨by simp [litVar], by simp [initState]⟩⟩
        · exact absurd rfl hxne⟩
  have h4 := decideLit_inv h3.1 (l := 6) (by simp [initState, litStatus, litNeg])
  have hlv_dec : ∀ s l x, stateLevel (decideLit s l) x =
      if litVar x = litVar l then s.level + 1 else stateLevel s x := by
    intro s l x; simp [decideLit]; rfl
  have hl_dec : ∀ s l, (decideLit s l).level = s.level + 1 := fun _ _ => rfl
  have hl_init : (initState coreFlushF0).level = 0 := rfl
  have h5 := assignProp_inv h4.1 (l := 8) (rsn := .large 3)
    (by simp [decideLit, initState, litStatus, litNeg]) (by simp)
    ⟨{ lits := [1, 7, 8] },
      by simpa [decideLit, coreFlushF0] using
        hcl 3 [[0], [1, 2], [1, 3, 4], [1, 7, 8]] (by decide),
      rfl, by simp, fun x hx hxne => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, by simp [decideLit, initState],
            by simp [decideLit, initState, litNeg],
            by simp [hlv_dec, hl_dec, hl_init, litVar],
            Or.inl (by simp [hlv_dec, hl_dec, hl_init, litVar])⟩
        · exact ⟨3, by simp [decideLit, initState],
            by simp [decideLit, initState, litNeg],
            by simp [hlv_dec, hl_dec, hl_init, litVar],
            Or.inr ⟨by simp [hlv_dec, hl_dec, hl_init, litVar],
              by simp [decideLit, initState]⟩⟩
        · exact absurd rfl hxne⟩
  have hfl := flushRoot_of_trailInv h5.1
  have hrd := reduceAndCollect_sound hfl.1 hfl.2.1 hfl.2.2.1 fun _ _ => false
  exact ⟨hfl.1, hfl.2.1, hfl.2.2.1, hrd.1, fun α hα =>
    hrd.2.2.2.2.2.2.2.1 α (by rw [hfl.2.2.2.1, h5.2, h4.2, h3.2, h2.2, h1.2, h0.2]; exact hα)⟩

/-! ## 5. Single-line `#print axioms` checks (`<= 120` cols) -/

#print axioms LeanQbe.T.Examples.Kissat.seedRemovable_preserves
#print axioms LeanQbe.T.Examples.Kissat.cut_delete_sound
#print axioms LeanQbe.T.Examples.Kissat.minimizeLiteralWorklist_sound
#print axioms LeanQbe.T.Examples.Kissat.minimize_worklist_sound
#print axioms LeanQbe.T.Examples.Kissat.shrink_block_cut_sound
#print axioms LeanQbe.T.Examples.Kissat.shrink_block_sound
#print axioms LeanQbe.T.Examples.Kissat.shrink_clause_sound
#print axioms LeanQbe.T.Examples.Kissat.failedLit_other_ne_unit
#print axioms LeanQbe.T.Examples.Kissat.analyzeFailedLiteralExec_sound
#print axioms LeanQbe.T.Examples.Kissat.collect_remap_sound
#print axioms LeanQbe.T.Examples.Kissat.core_collect_lazy_sound
#print axioms LeanQbe.T.Examples.Kissat.markGarbageIf_sound
#print axioms LeanQbe.T.Examples.Kissat.sweepClauses_sound
#print axioms LeanQbe.T.Examples.Kissat.sweep_collect_sound
#print axioms LeanQbe.T.Examples.Kissat.partitionIrredFirst_sound
#print axioms LeanQbe.T.Examples.Kissat.reduceAndCollect_sound
#print axioms LeanQbe.T.Examples.Kissat.activeReason_not_rootSatisfied
#print axioms LeanQbe.T.Examples.Kissat.flushRootReasons_sound
#print axioms LeanQbe.T.Examples.Kissat.flushRoot_of_trailInv
#print axioms nv_lazyMin_inv
#print axioms nv_minimize_sound
#print axioms nv_collectRich_inv
#print axioms nv_collectRich_sound
#print axioms nv_core_flush_reduce

end LeanQbeTest.T.KissatLayerATest
