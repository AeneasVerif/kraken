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

private def lazyMinCdcl : CdclState :=
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

private def lazyMinInit : MinState :=
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

private def collectRichState : CdclState :=
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

/-! ## 4. Single-line `#print axioms` checks (`<= 120` cols) -/

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

end LeanQbeTest.T.KissatLayerATest
