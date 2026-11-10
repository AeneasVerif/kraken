module

public import LeanQbe.Live
public import LeanQbe.Rega

/-!
# Register assignment and spilling oracle (QBE `spill.c` / `rega.c` heuristics), untrusted

The result is a `Rega.Hints`; `Rega.lower` checks it, so a wrong or failed assignment is a compile
error, never a wrong program.

Invariant (program-independent, simple): every live name has one *home* for its whole life, a
register or a spill slot of its own.

* A name live across a call gets a slot (no callee-saved register is allocatable, so a call keeps
  only slots).
* Otherwise it gets a register, unless `allocatable.length - 2` registers are already homes of
  values live after its definition; then it gets a slot too (spill everywhere). The two registers
  kept free serve as reload registers of an instruction's spilled operands and as the temporary
  destination of a spilled definition.
* A spilled name is defined into a free register (`let_`, `load`) or arrives in its parameter
  register (function, call result, block parameter), and is stored to its slot in the pre-moves of
  the next instruction (stores first). Before each instruction that reads it as an operand, it is
  reloaded into a free allocatable register (or read from its definition register when the store is
  in that same pre-move list). Arguments of `call`, `jump`, `ret`, `exit` need no reload: the
  lowering's parallel move loads them from their slots.
* Register homes are chosen first fit, avoiding the homes of the values live at that point. Block
  parameters get registers distinct from the homes of the block's live-in values.
* The entry map of a block lists each live-in value at its home.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Spill

open Live Rega

variable {I : Isa}

/-- Look up `x` in an association list. -/
def find? {α : Type} (A : List (Nat × α)) (x : Nat) : Option α := (A.find? (·.1 == x)).map (·.2)

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
  home : List (Nat × Loc I)
  dest : List (Nat × I.Reg)
  ploc : List (Nat × List I.Reg)
  pre : List (Nat × List (Move I))
  nslots : Nat

/-- Stores still to be done in the pre-moves of the next instruction: name, slot, register. -/
abbrev Pending (I : Isa) := List (Nat × Nat × I.Reg)

/-- The registers that are homes of the names `xs`. -/
def regHomes (st : State I) (xs : List Nat) : List I.Reg :=
  xs.filterMap fun x => match find? st.home x with | some (.reg r) => some r | _ => none

/-- Reloads for the operands `xs` into registers outside `avoid`; returns the moves. An operand
whose store is pending is still in its definition register and needs none. -/
def reloads (st : State I) (ps : Pending I) : List I.Reg → List Nat → List (Move I)
  | _, [] => []
  | avoid, x :: xs =>
    match find? st.home x with
    | some (.slot s) =>
      if (ps.find? (·.1 == x)).isSome then reloads st ps avoid xs
      else
        match firstFree avoid with
        | some r => .ld r s :: reloads st ps (r :: avoid) xs
        | none => reloads st ps avoid xs
    | _ => reloads st ps avoid xs

/-- Record the pre-moves of instruction `ip`: the pending stores, then reloads of the operands
`ops`, avoiding the registers of the values `live` into the instruction. -/
def emitPre (ip : Nat) (ps : Pending I) (ops live : List Nat) (st : State I) : State I :=
  let avoid := regHomes st live ++ (ps.filter (fun p => ops.contains p.1)).map (·.2.2)
  let mvs := ps.map (fun p => Move.st p.2.1 p.2.2) ++ reloads st ps avoid (union [] ops)
  { st with pre := (ip, mvs) :: st.pre }

/-- Block live-in sets paired with their parameter counts. -/
abbrev BlockCap := List (List Nat × Nat)

/-- Name `x`, now in register `r`, with the values `liveOut` live after its definition: give it a
home. Returns the pending store if it is spilled. -/
def home (bcap : BlockCap) (cross liveOut : List Nat) (x : Nat) (r : I.Reg) (st : State I) :
    State I × Pending I :=
  if liveOut.contains x then
    let blockFull := bcap.any fun (lv, np) =>
      lv.contains x && decide ((regHomes st (lv.filter (· != x))).length + np ≥ I.allocatable.length)
    if cross.contains x || blockFull ||
        decide ((regHomes st (liveOut.filter (· != x))).length + 2 ≥ I.allocatable.length) then
      ({ st with home := (x, .slot st.nslots) :: st.home, nslots := st.nslots + 1 },
        [(x, st.nslots, r)])
    else ({ st with home := (x, .reg r) :: st.home }, [])
  else (st, [])

/-- Definition of `x` by `let_`/`load` at instruction `ip`, followed by `k`. -/
def define (L : LiveMap) (bcap : BlockCap) (cross : List Nat) (x : Nat) (k : Tree) (st : State I) :
    State I × Pending I :=
  let liveOut := liveIn L k
  match firstFree (regHomes st (liveOut.filter (· != x))) with
  | some d => home bcap cross liveOut x d { st with dest := (x, d) :: st.dest }
  | none => (st, [])

/-- Walk the tree in `lower`'s order. `pl`: registers of the parameters still to be bound; `ps`:
pending stores. -/
def alloc (L : LiveMap) (bcap : BlockCap) (cross : List Nat) : Tree → List I.Reg → Pending I → State I → State I
  | .param x k, pl, ps, st =>
    match pl with
    | r :: pl' =>
      let (st, ps') := home bcap cross (liveIn L k) x r st
      alloc L bcap cross k pl' (ps ++ ps') st
    | [] => alloc L bcap cross k [] ps st
  | .let_ ip x op k, _, ps, st =>
    let st := emitPre ip ps (opVars op) (liveIn L (.let_ ip x op k)) st
    let (st, ps) := define L bcap cross x k st
    alloc L bcap cross k [] ps st
  | .load ip x a k, _, ps, st =>
    let st := emitPre ip ps (argVars [a]) (liveIn L (.load ip x a k)) st
    let (st, ps) := define L bcap cross x k st
    alloc L bcap cross k [] ps st
  | .store ip v a k, _, ps, st =>
    alloc L bcap cross k [] [] (emitPre ip ps (argVars [v, a]) (liveIn L (.store ip v a k)) st)
  | .call ip _ _ k, _, ps, st => alloc L bcap cross k I.retRegs [] (emitPre ip ps [] [] st)
  | .jnz ip c l t e, _, ps, st =>
    let st := emitPre ip ps [c] (liveIn L (.jnz ip c l t e)) st
    alloc L bcap cross t [] [] (alloc L bcap cross e [] [] st)
  | .skip ip k, _, ps, st => alloc L bcap cross k [] [] (emitPre ip ps [] [] st)
  | .jump ip _ _, _, ps, st | .ret ip _, _, ps, st | .exit ip _ _, _, ps, st =>
    emitPre ip ps [] [] st
  | .stop, _, _, st => st
  | .label _ k, pl, ps, st => alloc L bcap cross k pl ps st
  | .block l b rest, pl, ps, st =>
    let st := alloc L bcap cross rest pl ps st
    let regs := freshRegs (regHomes st (L.get l)) b.params.1.length
    alloc L bcap cross b regs [] { st with ploc := (l, regs) :: st.ploc }

/-- Hints for `Rega.lower` from the oracle. -/
def hints (I : Isa) (f : Fn) : Rega.Hints I :=
  let t := Tree.ofFn f
  let L := liveLabels t
  let bcap := t.blocks.map fun (l, b) => (L.get l, b.params.1.length)
  let st := alloc (I := I) L bcap (acrossCalls L t) t I.argRegs [] ⟨[], [], [], [], 0⟩
  { dest := find? st.dest
    entry := fun l =>
      { live := (L.get l).filterMap fun x => (find? st.home x).map fun loc => (.var x, loc)
        ploc := (find? st.ploc l).getD [] }
    pre := fun ip => (find? st.pre ip).getD []
    nslots := st.nslots }

end Spill
end LeanQbe
