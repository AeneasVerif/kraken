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

-- TODO Add memory, for now we only track and compare registers and flags.
structure StateSummary where
  regs : List (String × UInt64)
  flags : List (String × Bool)

-- Custom json serialization for the state summary.
instance : ToJson StateSummary where
  toJson s :=
    let regs := s.regs.map (fun (k, v) => (k, Json.num v.toNat))
    let flags := s.flags.map (fun (k, v) => (k, toJson v))
    Json.mkObj [
      ("regs", Json.mkObj regs),
      ("flags", Json.mkObj flags)
    ]

def summarize (s : MachineData) : StateSummary :=
  let r := s.regs
  let f := s.status
  { regs := [("rax", r.rax), ("rbx", r.rbx), ("rcx", r.rcx), ("rdx", r.rdx),
             ("rsi", r.rsi), ("rdi", r.rdi), ("rbp", r.rbp), ("r8", r.r8),
             ("r9", r.r9), ("r10", r.r10), ("r11", r.r11), ("r12", r.r12),
             ("r13", r.r13), ("r14", r.r14), ("r15", r.r15)],
    flags := [("cf", f.cf), ("pf", f.pf), ("af", f.af),
              ("zf", f.zf), ("sf", f.sf), ("of", f.of)] }

abbrev MachineState := MachineData × Int64

def _start: String := "_start"
def _end: String := "_end"

-- Give the program a stack of 100B initially.
def stackSize := 100
def initStack : List (UInt64 × UInt64) :=
  (List.range stackSize).map (λ i => (0xfffffffffffffff8 - (i.toUInt64 * 8), 0))

def finishCriterion (p: Program) (s: MachineState): Bool :=
  s.2 = p.fakeLayout.labels.label _end

def runKraken (asmCode : String)
    : Except String MachineState := do
  let prog ← Kraken.Parser.parse (_start ++ ":" ++ asmCode ++ "\n" ++ _end ++ ":")
  let initState: MachineState := ({dmem := .ofList initStack}, prog.fakeLayout.labels.label _start)
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
