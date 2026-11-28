module

public import LeanQbe.T.MainCertSeg
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.Build.Inl.Full
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Float64
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Dimacs
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Limits
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Arena
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Watch
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Heap
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Backtrack
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Clause
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Tiers
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Bump
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Internal
public import LeanQbe.T.Examples.Kissat.Build.Amd64.PropSearch
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Parse
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Collect
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Compact
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Reduce
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce.FullDeduce1uipM6Hdr
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Minimize
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Learn
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Analyze
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Decide
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Restart
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Extend
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Lucky
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Vivify
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Backbone
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Transitive
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Substitute
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Dense
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongEvalGate
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongFwdSubsume
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Kitten
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepUnits
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepClasses
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Forward
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Gates
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Definition
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Eliminate
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Factor
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaConnectClausesFid
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaCommit
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.FullReorderQueueM7
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Probe
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Walk
public import LeanQbe.T.Examples.Kissat.Build.Amd64.Search

/-!
# Whole-Module Subsystem-Aligned Certificate on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Amd64.Full

open LeanQbe.T LeanQbe.T.Amd64

/-- Plan-inlined whole module certified by `fullCert`. -/
@[expose] def inlMod : Module :=
  LeanQbe.T.Examples.Kissat.Src.Full.kissatModule.inlinePlan
    LeanQbe.T.Examples.Kissat.Build.Inl.Full.fullPlan

/-- Ordered list of subsystem and isolated heavy-function `SegChunks`. -/
@[expose] noncomputable def allSegChunks :
    List (SegChunks x64Target x64LegalTarget [] 0 2048) := [
  LeanQbe.T.Examples.Kissat.Build.Amd64.Float64.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Dimacs.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Limits.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Arena.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Watch.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Heap.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Backtrack.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Clause.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Tiers.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Bump.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Internal.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.PropSearch.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Parse.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Collect.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Compact.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Reduce.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce.cert.part0,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Deduce.FullDeduce1uipM6Hdr.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Minimize.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Learn.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Analyze.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Decide.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Restart.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Extend.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Lucky.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Vivify.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Backbone.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Transitive.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Substitute.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Dense.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.cert.part0,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongEvalGate.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.cert.part1,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.FullCongFwdSubsume.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Congruence.cert.part2,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Kitten.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.cert.part0,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepUnits.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.FullM6SweepClasses.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Sweep.cert.part1,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Forward.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Gates.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Definition.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Eliminate.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.cert.part0,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaConnectClausesFid.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.cert.part1,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.FullBvaCommit.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Factor.cert.part2,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.cert.part0,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.FullReorderQueueM7.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Reorder.cert.part1,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Probe.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Walk.cert,
  LeanQbe.T.Examples.Kissat.Build.Amd64.Search.cert
]

/-- Function-list alignment between `inlMod` and `allSegChunks`. -/
theorem allSegs_fns_eq :
    inlMod.fns = SegChunks.allFns allSegChunks := by
  unfold inlMod
  rw [LeanQbe.T.Examples.Kissat.Build.Inl.Full.inlFns_eq]
  rfl

/-- Whole-module cross-segment link check across `allSegChunks`. -/
theorem allSegs_link :
    checkLinkList x64Layout [] (SegChunks.allChunks allSegChunks) = true := by
  t_kernel_rfl

/-- Whole-module verified `LinkedCert` assembled via `LinkedCert.ofSegs`. -/
@[expose] noncomputable def fullCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      inlMod [] [] 0 2048 :=
  LinkedCert.ofSegs allSegChunks allSegs_fns_eq allSegs_link

end LeanQbe.T.Examples.Kissat.Build.Amd64.Full
