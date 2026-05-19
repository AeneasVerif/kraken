import Kraken.Semantics
import Kraken.Tactics

namespace Kraken.Simplified

-- A state in the simplified semantics is just the machine data and the current instruction index.
abbrev SimplifiedState := MachineData × Nat

-- Find the index of a label in a list of directives.
def findLabelIndex (prog : List Directive) (l : Label) : Nat :=
  prog.idxOf (.label l)

-- Create a Labels instance based on instruction indices.
def mkLabels (prog : List Directive) : Labels where
  label l := (findLabelIndex prog l).toInt64

-- Single step in the simplified semantics.
-- This reuses Directive.interp by using the instruction index as the address.
def step (full_prog : List Directive) (s : MachineData) (pc : Nat) : Effects :=
  match full_prog[pc]? with
  | none => .done (s, Int64.ofNat pc) -- Execution finished (out of bounds)
  | some d =>
    let labels := mkLabels full_prog
    let p : Std.Rco Int64 := .mk (Int64.ofNat pc) (Int64.ofNat (pc + 1))
    -- Bring the labels instance into scope
    let _labels := labels
    Directive.interp d s p
      (next := fun s' => .done (s', Int64.ofNat (pc + 1)))
      (jmp := fun target_addr s' =>
        -- target_addr is already an Int64 representing the index
        .done (s', target_addr))

-- Straightline execution: executes instructions until the end or a jump.
def straightline (full_prog : List Directive) (s : MachineData) (pc : Nat) : Effects :=
  let labels := mkLabels full_prog
  let _labels := labels
  let rec go (ds : List Directive) (s : MachineData) (pc : Nat) : Effects :=
    match ds with
    | [] => .done (s, Int64.ofNat pc)
    | d :: ds =>
      let p : Std.Rco Int64 := .mk (Int64.ofNat pc) (Int64.ofNat (pc + 1))
      Directive.interp d s p
        (next := fun s' => go ds s' (pc + 1))
        (jmp := fun target_addr s' => .done (s', target_addr))
  go (full_prog.drop pc) s pc

def simplified_step1 (prog: List Directive) (s: MachineState) (post: @Post MachineState) : Prop :=
  (step prog s.1 s.2.toInt.toNat).all post

def simplified_straightline_step (prog: List Directive) (s: MachineState) (post: @Post MachineState) : Prop :=
  (straightline prog s.1 s.2.toInt.toNat).all post

end Kraken.Simplified
