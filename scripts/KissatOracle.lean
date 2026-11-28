/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanQbeTest.T.SegCertOracleCommon
import LeanQbe.T.Examples.Kissat.Src.Full
import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# Arch-Neutral Kissat Build Oracle CLI (`scripts/KissatOracle.lean`)

Runnable directly via `lake env lean --run scripts/KissatOracle.lean <out-dir>`:
runs `policyToInlPlan` over all 41 subsystems of `Src.Full` using `fidInlPolicy`
(exact `selectCandsForCaller` parity) and writes:
  - `<out-dir>/manifest.json` (for `scripts/gen_build_segs.py --manifest`)
  - `<out-dir>/Oracle/<S>.lean` (`plan : InlPlan`)
  - `<out-dir>/Inl/<S>/Exports.lean` (narrow `TFlatFn` export leaves)
-/

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src
open LeanQbeTest.T.SegCertOracle

private def kissatSegs : List SegInput :=
  let mk (nm : String) (fns : List Fn) : SegInput :=
    { name := nm, srcMod := s!"LeanQbe.T.Examples.Kissat.Src.{nm}", fns := fns }
  [ mk "Float64" Float64.fns, mk "Dimacs" Dimacs.fns, mk "Limits" Limits.fns
  , mk "Arena" Arena.fns, mk "Watch" Watch.fns, mk "Heap" Heap.fns
  , mk "Backtrack" Backtrack.fns, mk "Clause" Clause.fns, mk "Tiers" Tiers.fns
  , mk "Bump" Bump.fns, mk "Internal" Internal.fns, mk "PropSearch" PropSearch.fns
  , mk "Parse" Parse.fns, mk "Collect" Collect.fns, mk "Compact" Compact.fns
  , mk "Reduce" Reduce.fns, mk "Deduce" Deduce.fns, mk "Minimize" Minimize.fns
  , mk "Learn" Learn.fns, mk "Analyze" Analyze.fns, mk "Decide" Decide.fns
  , mk "Restart" Restart.fns, mk "Extend" Extend.fns, mk "Lucky" Lucky.fns
  , mk "Vivify" Vivify.fns, mk "Backbone" Backbone.fns, mk "Transitive" Transitive.fns
  , mk "Substitute" Substitute.fns, mk "Dense" Dense.fns, mk "Congruence" Congruence.fns
  , mk "Kitten" Kitten.fns, mk "Sweep" Sweep.fns, mk "Forward" Forward.fns
  , mk "Gates" Gates.fns, mk "Definition" Definition.fns, mk "Eliminate" Eliminate.fns
  , mk "Factor" Factor.fns, mk "Reorder" Reorder.fns, mk "Probe" Probe.fns
  , mk "Walk" Walk.fns, mk "Search" Search.fns ]

def main (args : List String) : IO Unit := do
  let outDir : System.FilePath := args.headD ".lake/kissat-oracle"
  let baseNs := "LeanQbe.T.Examples.Kissat.Build"
  let (_, infos) := computeSegPlans
    LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy kissatSegs
  IO.FS.createDirAll (outDir / "Oracle")
  for info in infos do
    let planSrc := renderPlanOracleLean s!"{baseNs}.Oracle.{info.seg.name}" info.plan
    IO.FS.writeFile (outDir / "Oracle" / s!"{info.seg.name}.lean") planSrc
    if !info.exportNames.isEmpty then
      let expFlats := info.inlinedFlats.filter fun tf => info.exportNames.contains tf.name
      let expDir := outDir / "Inl" / info.seg.name
      IO.FS.createDirAll expDir
      let expSrc := renderExportsLean s!"{baseNs}.Inl.{info.seg.name}.Exports" expFlats
      IO.FS.writeFile (expDir / "Exports.lean") expSrc
  let mfJson := formatManifestJson baseNs "LeanQbe.T.Examples.Kissat.Src.Full" "kissatModule" infos
  IO.FS.writeFile (outDir / "manifest.json") mfJson
  let totalExp := infos.foldl (fun a i => a + i.exportNames.length) 0
  IO.println s!"KissatOracle: wrote {infos.length} plans, {totalExp} exports -> {outDir}"
