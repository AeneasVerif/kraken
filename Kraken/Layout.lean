module

public import Kraken.PNat
public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken


abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

inductive Directive (Instr Const : Type) where
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (arr : ByteArray)
  /-- A data word of `bytes` bytes whose value is a symbolic constant, e.g. a label or a
  difference of labels (a relocation). It is never executed. Jump tables (`.long .Lcase - .Ltable`)
  and pointer tables (`.quad fn`) are the typical uses. -/
  | word (bytes : Nat) (e : Const)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr Const := List (Directive Instr Const)

structure Executable (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))

variable {Instr Const : Type}

-- JP: why is `size` not `Directive → Nat`?
class Layout (p : Program Instr Const) where
  start : Int64 -- NOTE: Why is `start` a `Int64`?
  instrSize : Nat → PNat

def Layout.size {p : Program Instr Const} [l : Layout p] (i : Nat) : Nat :=
  match p[i]? with
  | some <| .instr _ => l.instrSize i
  | some <| .label _ => 0
  | some <| .byteArray arr => arr.size
  | some <| .word bytes _ => bytes
  | none => 0

def Program.size (p : Program Instr Const) [l : Layout p] := p.mapIdx (fun idx _ => l.size idx) |>.sum

class WellFormedLayout (p : Program Instr Const) extends Layout p where
  no_overflow : p.size < 2^64

def Layout.apply (prog : Program Instr Const) (l : Layout prog) : Executable Instr Const :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

abbrev Program.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

abbrev _root_.List.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

theorem Program.toExecutable_eq_of_eq (prog q : Program Instr Const) [l : Layout prog]
    (hq : prog = q := by rfl) :
    List.toExecutable prog =
      {startAddr := l.start, program := q.mapIdx (fun i directive => {directive, size := l.size i})} := by
  subst hq; rfl

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

variable (e : Executable Instr Const) (program : List (Sized (Directive Instr Const))) {c : Sized (Directive Instr Const)}

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses (e : Executable Instr Const) : List (Addressable (Directive Instr Const)) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

def Executable.directivesAtAddress (a : Int64) : List (Sized (Directive Instr Const)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress (a : Int64) : List (Sized (Directive Instr Const)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

theorem Executable.directivesFromStart {prog : Program Instr Const} [layout : Layout prog]
    (q : Program Instr Const) :
    Executable.directivesFromAddress
      {startAddr := layout.start, program := q.mapIdx (fun i directive => {directive, size := layout.size i})}
      layout.start =
      q.mapIdx (fun i directive => {directive, size := layout.size i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress]

theorem directivesAtFromPrefix (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.addr ≠ a)).dropWhile (·.addr = a)).map (·.toSized), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

variable {e} in
theorem Executable.mem_of_mem_directivesAtAddress
    {a : Int64} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

theorem Executable.getElem?_withAddresses_mk :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (k : Nat),
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

theorem Executable.getElem?_withAddresses_eq (k : Nat) :
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

theorem Executable.withAddresses_dropWhile_addrOf (j n : Nat)
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

theorem Program.map_size_toExecutable_eq (p : Program Instr Const) [l : Layout p] :
    (p.toExecutable.program.map (·.size)).sum = p.size := by
  dsimp [Program.toExecutable, Layout.apply, Program.size]
  congr 1
  generalize (l.size) = sz
  induction p generalizing sz <;> simp [List.mapIdx_cons, *]

theorem Executable.sizeBefore_le (n : Nat) :
    e.sizeBefore n ≤ (e.program.map (·.size)).sum := by
  simpa [sizeBefore, List.take_of_length_le (Nat.le_max_right n e.program.length)] using
    e.sizeBefore_mono (Nat.le_max_left n e.program.length)

theorem Program.sizeBefore_lt (prog : Program Instr Const) [WellFormedLayout prog] (n : Nat) :
    prog.toExecutable.sizeBefore n < 2^64 :=
  Nat.lt_of_le_of_lt (prog.toExecutable.sizeBefore_le n)
    (Program.map_size_toExecutable_eq prog ▸ WellFormedLayout.no_overflow)

theorem Program.sizeBefore_eq_of_addrOf_eq (prog : Program Instr Const) [WellFormedLayout prog]
    {j k : Nat} (h : prog.toExecutable.addrOf j = prog.toExecutable.addrOf k) :
    prog.toExecutable.sizeBefore j = prog.toExecutable.sizeBefore k := by
  have hj := Program.sizeBefore_lt prog j
  have hk := Program.sizeBefore_lt prog k
  grind [Executable.addrOf]

end Kraken
