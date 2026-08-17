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

/-- Take the leading zero-sized entries through the first positive-sized one.

Grouping zero-sized entries with their positive-sized successor is what makes
repeated stepping make progress: a zero-sized directive occupies no address
space, so fetching at its address again would yield it forever. On a listing
whose addresses are laid out consecutively this is exactly
`directivesAtAddress` at the block's start address: the entries starting at a
given address are the zero-sized run there plus the first positive-sized
directive. -/
def Directives.takeBlock {Directive : Type} : List (Directive × Nat) → List (Directive × Nat)
  | [] => []
  | entry :: rest => if entry.2 = 0 then entry :: takeBlock rest else [entry]

/-- The directives of a block are an initial segment of the directives they
were taken from. -/
theorem Directives.takeBlock_prefix {Directive : Type} (ds : List (Directive × Nat)) :
    ∃ rest, ds = Directives.takeBlock ds ++ rest := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
    by_cases h : entry.2 = 0
    · obtain ⟨tail, htail⟩ := ih
      exact ⟨tail, by simp [Directives.takeBlock, h]; exact htail⟩
    · exact ⟨rest, by simp [Directives.takeBlock, h]⟩

/-- Advance `pc` across a sequence of laid-out directives. -/
def Directives.fallthroughPC {Directive : Type} (ds : List (Directive × Nat)) (pc : Int64) : Int64 :=
  ds.foldl (fun pc d => pc + .ofNat d.2) pc

theorem Directives.fallthroughPC_append {Directive : Type}
    (ds₁ ds₂ : List (Directive × Nat)) (pc : Int64) :
    Directives.fallthroughPC (ds₁ ++ ds₂) pc =
      Directives.fallthroughPC ds₂ (Directives.fallthroughPC ds₁ pc) := by
  simp [Directives.fallthroughPC, List.foldl_append]

/-- The address assigned to directive `i` by an executable's size table.
At and beyond the end of the executable this is its fall-through address. -/
def Directives.addressAt {Directive : Type} (ds : List (Directive × Nat)) (pc : Int64) (i : Nat) : Int64 :=
  Directives.fallthroughPC (ds.take i) pc

def Executable.addressAt {Directive : Type} (e : Executable Directive) (i : Nat) : Int64 :=
  Directives.addressAt e.2 e.1 i

end Kraken
