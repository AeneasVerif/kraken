import Kraken.Semantics

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

end Kraken.Simplified
