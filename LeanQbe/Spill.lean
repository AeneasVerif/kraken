module

public import LeanQbe.Live
public import LeanQbe.Rega

/-!
# Register assignment oracle (QBE `spill.c` / `rega.c` heuristics), untrusted

First fit: every name gets one register for its whole life, chosen when it is defined, avoiding the
registers of the values live at that point. Parameters of a join point get registers distinct from
its live-in values. The result is a `Rega.Hints`; `Rega.lower` checks it, so a wrong or failed
assignment is a compile error, never a wrong program. No spilling yet (step 3): with more live values
than allocatable registers the oracle leaves a name without a register and `lower` fails.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Spill

open Live

variable {I : Isa}

abbrev Assign (I : Isa) := List (Nat × I.Reg)

def Assign.get (A : Assign I) (x : Nat) : Option I.Reg := (A.find? (·.1 == x)).map (·.2)

/-- First allocatable register not in `taken`. -/
def firstFree (taken : List I.Reg) : Option I.Reg := I.allocatable.find? (· ∉ taken)

/-- Registers for `n` parameters, avoiding `taken` and each other. -/
def freshRegs (taken : List I.Reg) : Nat → List I.Reg
  | 0 => []
  | n + 1 =>
    match firstFree taken with
    | some r => r :: freshRegs (r :: taken) n
    | none => []

structure State (I : Isa) where
  assign : Assign I
  ploc : List (Nat × List I.Reg)

/-- Walk the tree in `lower`'s order. `pl`: registers of the parameters still to be bound. -/
def alloc (L : LiveMap) : Tree → List I.Reg → State I → State I
  | .param x k, pl, st =>
    match pl with
    | r :: pl' => alloc L k pl' { st with assign := (x, r) :: st.assign }
    | [] => alloc L k [] st
  | .let_ x _ k, _, st | .load x _ k, _, st =>
    let taken := ((liveIn L k).filter (· != x)).filterMap st.assign.get
    match firstFree taken with
    | some r => alloc L k [] { st with assign := (x, r) :: st.assign }
    | none => alloc L k [] st
  | .store _ _ k, _, st => alloc L k [] st
  | .jnz _ _ t e, _, st => alloc L t [] (alloc L e [] st)
  | .label _ k, pl, st => alloc L k pl st
  | .block l b rest, pl, st =>
    let st := alloc L rest pl st
    let (ps, _) := b.params
    let taken := (L.get l).filterMap st.assign.get
    let regs := freshRegs taken ps.length
    alloc L b regs { st with ploc := (l, regs) :: st.ploc }
  | .jump _ _, _, st | .ret _, _, st | .stop, _, st => st

/-- Hints for `Rega.lower` from the oracle. -/
def hints (I : Isa) (f : Fn) : Rega.Hints I :=
  let t := Tree.ofFn f
  let L := liveLabels t
  let st := alloc (I := I) L t I.argRegs ⟨[], []⟩
  { dest := st.assign.get
    entry := fun l =>
      { live := (L.get l).filterMap fun x => (st.assign.get x).map fun r => (.var x, r)
        ploc := ((st.ploc.find? (·.1 == l)).map (·.2)).getD [] } }

end Spill
end LeanQbe
