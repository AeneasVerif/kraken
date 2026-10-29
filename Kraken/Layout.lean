module

public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken


abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

inductive Directive (Instr : Type)
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr := List (Directive Instr)

structure Executable (Instr : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr))

-- JP: why is `size` not `Directive → Nat`?
class Layout (Instr : Type) where
  start : Int64
  size : Nat → Nat

variable {Instr : Type}

def Layout.apply (l : Layout Instr) (prog : Program Instr) : Executable Instr :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

-- NOTE: We write `List (Kraken.Directive Instr)` here, and not `Kraken.Program Instr`, because architecture
-- specific `Program` types are written as `List Directive` which desugar to `List (Kraken.Directive Instr)`,
-- and so otherwise the typeclass synthesis algorithm would not find this instance.
-- Architecture specific programs are written as `List Directive` for architecture-specific `Directive`
-- instead of `Kraken.Directive Instr` so that `ls[i].foo` searches for `Directive.foo` first, instead of
-- going directly to `Kraken.Directive.foo` (which contains less information)
instance : CoeFun (Layout Instr) (fun _ => List (Directive Instr) → Executable Instr) where
  coe := Layout.apply

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Instr : Type} (e : Executable Instr) : List (Addressable (Directive Instr)) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

def Executable.directivesAtAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

theorem Executable.directivesFromStart {Instr : Type} [layout : Layout Instr] (prog : Program Instr) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

theorem directivesAtFromPrefix {Instr : Type} (e: Executable Instr) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.addr ≠ a)).dropWhile (·.addr = a)).map (·.toSized), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem Executable.mem_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore {Instr : Type} (e : Executable Instr) (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf {Instr : Type} (e : Executable Instr) (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero {Instr : Type} (e : Executable Instr) : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {Instr : Type} (e : Executable Instr) {n : Nat}
    {c : Sized (Directive Instr)} (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add {Instr : Type} (e : Executable Instr) (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {Instr : Type} (e : Executable Instr) {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {Instr : Type} (e : Executable Instr) {n : Nat} {c : Sized (Directive Instr)}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

theorem Executable.getElem?_withAddresses_mk {Instr : Type} :
    ∀ (program : List (Sized (Directive Instr))) (startAddr : Int64) (k : Nat),
      (Executable.withAddresses {startAddr, program})[k]?
        = program[k]?.map (fun c => {c with addr := Executable.addrOf {startAddr, program} k})
  | [], a, k => by rw [Executable.withAddresses]; simp
  | c :: program, a, 0 => by
    rw [Executable.withAddresses]
    simp
  | c :: program, a, k + 1 => by
    rw [Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq {Instr : Type} (e : Executable Instr) (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k


private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

theorem Executable.withAddresses_dropWhile_addrOf {Instr : Type} (e : Executable Instr) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.withAddresses.dropWhile (·.addr ≠ e.addrOf n)
      = e.withAddresses.drop j := by
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hfresh k hk
  · intro c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hj

end Kraken
