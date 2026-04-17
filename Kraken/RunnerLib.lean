import Kraken.Semantics
import Kraken.Parser
import Kraken.Tactics
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
  { regs := [("rax", r.rax), ("rbx", r.rbx), ("rcx", r.rcx), ("rdx", r.rdx),
             ("rsi", r.rsi), ("rdi", r.rdi), ("rbp", r.rbp), ("r8", r.r8),
             ("r9", r.r9), ("r10", r.r10), ("r11", r.r11), ("r12", r.r12),
             ("r13", r.r13), ("r14", r.r14), ("r15", r.r15)],
    flags := [("cf", f.cf), ("pf", f.pf), ("af", f.af),
              ("zf", f.zf), ("sf", f.sf), ("of", f.of)] }



def _start: String := "_start"
def _end: String := "_end"

def stackSize := 100
def initStack : List (UInt64 × UInt64) :=
  (List.range stackSize).map (λ i => (0xfffffffffffffff8 - (i.toUInt64 * 8), 0))

def finishCriterion (p: Program) (s: MachineState): Bool :=
  s.2 = p.fakeLayout.labels.label _end

def runProg (prog : Program) : Except String MachineState := do
  let initState: MachineState := ({dmem := .ofList initStack}, prog.fakeLayout.labels.label _start)
  prog.fakeLayout.eval initState (finishCriterion prog)

def runKraken (asmCode : String) : Except String MachineState := do
  let prog ← Kraken.Parser.parse (_start ++ ":" ++ asmCode ++ "\n" ++ _end ++ ":")
  runProg prog
