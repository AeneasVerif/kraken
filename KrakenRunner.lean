/-
KrakenRunner - Run assembly instructions through Kraken Semantics and obtain results as json.

At this point this expects a file only containing a list of assembly instructions, no data block or similar.

Usage: krakenrunner <assembly.S>

Arguments:
- assembly.S: Assembly source file

Output:
- Json formatted Machine state of Kraken after running the assembly.
  See StateSummary for format.
-/

import Kraken.Semantics
import Kraken.Parser
import Lean.Data.Json

open Lean

-- TODO Add memory, for now we only track registers and flags.
structure StateSummary where
  regs : Reg64s
  flags : StatusFlags
deriving Lean.ToJson

def summarize (s : MachineData) : StateSummary :=
  { regs := s.regs, flags := s.status }

abbrev MachineState := MachineData × Int64

def _start: String := "_start"
def _end: String := "_end"

def finishCriterion (p: Program) (s: MachineState): Bool :=
  s.2 = p.fakeLayout.labels.label _end

def runKraken (asmCode : String)
    : Except String MachineState := do
  let prog ← Kraken.Parser.parse (_start ++ ":" ++ asmCode ++ "\n" ++ _end ++ ":")
  let initState: MachineState := ({}, prog.fakeLayout.labels.label _start)
  prog.fakeLayout.eval initState (finishCriterion prog)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then return 1

  let asmCode ← IO.FS.readFile args[0]!

  match runKraken asmCode with
  | .ok (state, _) =>
      IO.println (toJson (summarize state)).compress
      return 0
  | .error e =>
      IO.eprintln s!"Kraken Semantic Error: {e}"
      return 1
