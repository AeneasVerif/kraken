/-
KrakenRunnerAArch64 - Run AArch64 assembly instructions through Kraken Semantics and obtain results as json.

Usage: krakenrunner_aarch64 <assembly.S> [init_regs.json]

Arguments:
- assembly.S: Assembly source file
- init_regs.json: Optional JSON file providing initial register values

Output:
- Json formatted Machine state of Kraken after running the assembly.
-/

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Mem
import Lean.Data.Json

open Lean

structure StateSummary where
  regs : List (String × UInt64)
  flags : List (String × Bool)

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
  { regs := [("x0", r.X0), ("x1", r.X1), ("x2", r.X2), ("x3", r.X3),
             ("x4", r.X4), ("x5", r.X5), ("x6", r.X6), ("x7", r.X7),
             ("x8", r.X8), ("x9", r.X9), ("x10", r.X10), ("x11", r.X11),
             ("x12", r.X12), ("x13", r.X13), ("x14", r.X14), ("x15", r.X15),
             ("x16", r.X16), ("x17", r.X17), ("x18", r.X18), ("x19", r.X19),
             ("x20", r.X20), ("x21", r.X21), ("x22", r.X22), ("x23", r.X23),
             ("x24", r.X24), ("x25", r.X25), ("x26", r.X26), ("x27", r.X27),
             ("x28", r.X28), ("x29", r.X29), ("x30", r.X30), ("sp", r.SP)],
    flags := [("n", f.n), ("z", f.z), ("c", f.c), ("v", f.v)] }

def parseInitRegs (jsonStr : String) : Except String Reg64s := do
  let json ← Json.parse jsonStr
  let getVal (k : String) : UInt64 :=
    match json.getObjValAs? Nat k with
    | .ok v => v.toUInt64
    | .error _ => 0

  return {
    X0 := getVal "x0",   X1 := getVal "x1",   X2 := getVal "x2",   X3 := getVal "x3",
    X4 := getVal "x4",   X5 := getVal "x5",   X6 := getVal "x6",   X7 := getVal "x7",
    X8 := getVal "x8",   X9 := getVal "x9",   X10 := getVal "x10", X11 := getVal "x11",
    X12 := getVal "x12", X13 := getVal "x13", X14 := getVal "x14", X15 := getVal "x15",
    X16 := getVal "x16", X17 := getVal "x17", X18 := getVal "x18", X19 := getVal "x19",
    X20 := getVal "x20", X21 := getVal "x21", X22 := getVal "x22", X23 := getVal "x23",
    X24 := getVal "x24", X25 := getVal "x25", X26 := getVal "x26", X27 := getVal "x27",
    X28 := getVal "x28", X29 := getVal "x29", X30 := getVal "x30", SP := getVal "sp"
  }

def _start: String := "_start"
def _end: String := "_end"

def stackSize := 800
def initStack : DataMem := (List.replicate stackSize 0xff).At (0-stackSize)

def finishCriterion (prog: Program) (s: MachineState): Bool :=
  let layout := Program.fakeLayout prog
  s.2 = layout.labels.label _end

def runKraken (asmCode : String) (initRegs : Reg64s := {})
    : Except String MachineState := do
  let stripped := Kraken.AArch64.Parser.stripDirectives (_start ++ ":\n" ++ asmCode ++ "\n" ++ _end ++ ":\n")
  let prog ← Kraken.AArch64.Parser.parse stripped
  let layout := Program.fakeLayout prog
  let initState: MachineState := ({regs := initRegs, dmem := initStack}, layout.labels.label _start)
  layout.eval initState (finishCriterion prog)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then return (1 : UInt32)

  let asmCode ← IO.FS.readFile args[0]!
  let mut initRegs : Reg64s := {}
  if args.length > 1 then
    let jsonStr ← IO.FS.readFile args[1]!
    match parseInitRegs jsonStr with
    | .ok regs => initRegs := regs
    | .error e =>
        IO.eprintln s!"Failed to parse init json: {e}"
        return (1 : UInt32)

  match runKraken asmCode initRegs with
  | .ok (state, _) =>
      IO.println (toJson (summarize state)).compress
      return (0 : UInt32)
  | .error e =>
      IO.eprintln s!"Kraken Semantic Error: {e}"
      return (1 : UInt32)
