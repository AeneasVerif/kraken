module

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken

structure Sized (Directive : Type) where
  directive : Directive
  size : Nat

structure Executable (Directive : Type) where
  startAddr : Int64
  program : List (Sized Directive)

-- JP: why is `size` not `Directive → Nat`?
class Layout (Directive : Type) where
  start : Int64
  size : Nat → Nat

def Layout.apply {Directive : Type} (l : Layout Directive) (prog : List Directive) : Executable Directive :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

instance {Directive : Type} : CoeFun (Layout Directive) (fun _ => List Directive → Executable Directive) where
  coe := Layout.apply

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Directive : Type} (e : Executable Directive) : List (Addressable Directive) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Sized Directive) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Sized Directive) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd {Directive : Type} (program : List (Sized Directive)) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start {Directive : Type} (program : List (Sized Directive)) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

theorem Executable.directivesFromStart {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.addr ≠ a)).dropWhile (·.addr = a)).map (·.toSized), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

end Kraken
