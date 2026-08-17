/-
Common Kraken executable layout.
-/

namespace Kraken

abbrev Executable (Directive : Type) := Int64 × List (Directive × Nat)

-- JP: why is `size` not `Directive → Nat`?
class Layout (Directive : Type) where
  start : Int64
  size : Nat → Nat

def Layout.apply {Directive : Type} (l : Layout Directive) (prog : List Directive) : Executable Directive :=
  (l.start, prog.mapIdx (fun i d => (d, l.size i)))

instance {Directive : Type} : CoeFun (Layout Directive) (fun _ => List Directive → Executable Directive) where
  coe := Layout.apply

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Directive : Type} (e : Executable Directive) : List (Int64 × Directive × Nat) :=
  let (start_addr, ds) := e
  match ds with
  | [] => []
  | (instr, instr_sz) :: ds =>
    (start_addr, instr, instr_sz) :: Executable.withAddresses (start_addr + .ofNat instr_sz, ds)
termination_by e.2

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  (starts_at_a.takeWhile (·.1 = a)).map (·.2)

def Executable.directivesFromAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  starts_at_a.map (·.2)

theorem Executable.withAddresses_map_snd {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds ih =>
    rw [Executable.withAddresses]
    simp [ih]

theorem Executable.withAddresses_dropWhile_start {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).dropWhile (fun x => x.1 ≠ a) =
      Executable.withAddresses (a, ds) := by
  cases ds with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds =>
    rw [Executable.withAddresses]
    simp [List.dropWhile]

theorem Executable.directivesFromStart {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [Executable.directivesFromAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  rw [Executable.withAddresses_map_snd]

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a)).map (·.2), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

end Kraken
