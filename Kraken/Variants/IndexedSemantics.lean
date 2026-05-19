import Kraken.Semantics
import Kraken.Tactics

namespace Kraken.Indexed

-- ============================================================================
-- Indexed Semantics
-- ============================================================================
/-
This is a variation of the core Kraken semantics that models programs as a list
of instructions and models the "program counter" as the index into the list.
By contrast to the core semantics, this does not model the layout of instructions
in memory. As a result, the proofs about this variation are simplified for
cases where instruction memory is not relevant (for example user-space programs
that are not self-modifying). Note that this variation shares the same
definition of Directives as the core semantics, so instruction-level semantics
are identical.
WARNING: This variant is likely not a good choice if your target software:
* Is not userspace code (e.g., OS or hypervisor code)
* Is self-modifying
* Uses computed jumps via address tables in data memory (e.g., some switch statements)
* Reads its own code as data (e.g., for integrity checks)
* Requires verification against code-injection or buffer overflow attacks targeting code
-/

-- A state in the indexed semantics is just the machine data and the current instruction index.
abbrev IndexedState := MachineData × Nat

-- Find the index of a label in a list of directives.
def findLabelIndex (prog : List Directive) (l : Label) : Nat :=
  prog.idxOf (.label l)

-- Create a Labels instance based on instruction indices.
def mkLabels (prog : List Directive) : Labels where
  label l := (findLabelIndex prog l).toInt64

-- Single step in the indexed semantics.
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

-- Helper function for `straightline`. Note: keeping it as a separate def is needed
-- to allow its use in tactics such as dsimp
def straightline_go (full_prog : List Directive) [Labels] (ds : List Directive) (s : MachineData) (pc : Nat) : Effects :=
  match ds with
  | [] => .done (s, Int64.ofNat pc)
  | d :: ds =>
    let p : Std.Rco Int64 := .mk (Int64.ofNat pc) (Int64.ofNat (pc + 1))
    Directive.interp d s p
      (next := fun s' => straightline_go full_prog ds s' (pc + 1))
      (jmp := fun target_addr s' => .done (s', target_addr))

-- Straightline execution: executes instructions until the end or a jump.
def straightline (full_prog : List Directive) (s : MachineData) (pc : Nat) : Effects :=
  let labels := mkLabels full_prog
  let _labels := labels
  straightline_go full_prog (full_prog.drop pc) s pc

def indexed_step1 (prog: List Directive) (s: MachineState) (post: @Post MachineState) : Prop :=
  (step prog s.1 s.2.toInt.toNat).all post

def indexed_straightline_step (prog: List Directive) (s: MachineState) (post: @Post MachineState) : Prop :=
  (straightline prog s.1 s.2.toInt.toNat).all post

end Kraken.Indexed
