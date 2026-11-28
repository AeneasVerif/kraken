/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanQbeTest.T.SegCertOracleCommon
import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Examples.Kissat.Src.Full
import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# SysV x64 Kissat Build Oracle CLI (`scripts/KissatOracleX64.lean`)

Runnable via `lake env lean --run scripts/KissatOracleX64.lean <out-dir>`:
writes `Oracle/Amd64/<S>.lean` (`hints`, pruned `ext`, per-fn `hint_<fn>`/`ext_<fn>`)
and `profile_x64.json` for all 41 subsystems of `Src.Full`.
-/

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Examples.Kissat.Src
open LeanQbeTest.T.SegCertOracle

private def fmtX64Reg (r : x64Isa.Reg) : String := s!"{repr r}"
private def fmtX64VReg (v : x64Isa.VReg) : String := s!"{repr v}"
private def fmtX64Cond (cc : x64Isa.Cond) : String := s!"{repr cc}"

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
  let archDir := outDir / "Oracle" / "Amd64"
  IO.FS.createDirAll archDir
  let mut extAcc : List (SigEntry × Nat) := []
  let mut allMetrics : List (Sym × Nat × Nat) := []
  for info in infos do
    let modNs := s!"{baseNs}.Oracle.Amd64.{info.seg.name}"
    let (src, nextAcc, rows) ← renderArchOracleLean x64Isa
      fmtX64Reg fmtX64VReg fmtX64Cond x64LegalTarget
      "LeanQbe.T.Amd64.Isa" "LeanQbe.T.Amd64" "x64Isa" modNs
      extAcc [] 0 2048 info.inlinedFlats
    IO.FS.writeFile (archDir / s!"{info.seg.name}.lean") src
    extAcc := nextAcc
    allMetrics := allMetrics ++ rows
  IO.FS.writeFile (outDir / "profile_x64.json") (formatProfileJson allMetrics)
  IO.println s!"KissatOracleX64: wrote {infos.length} oracle files ({allMetrics.length} fns)"
