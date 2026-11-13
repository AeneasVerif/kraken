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

-- JP: why is `size` not `Directive → Nat`?
class Layout {Instr Const : Type} (p : Program Instr Const) where
  start : Int64 -- NOTE: Why is `start` a `Int64`?
  instrSize : Nat → PNat

variable {Instr Const : Type}

def Layout.size {p : Program Instr Const} [l : Layout p] : Directive Instr Const → Nat → Nat
  | .instr _, idx => l.instrSize idx
  | .label _, _ => 0
  | .byteArray arr, _ => arr.size
  | .word bytes _, _ => bytes

def Program.size (p : Program Instr Const) [l : Layout p] := p.mapIdx (fun idx d => l.size d idx) |>.sum

class Layout.IsWellFormed (p : Program Instr Const) [Layout p] where
  no_overflow : p.size < 2^64

class abbrev WellFormedLayout (p : Program Instr Const) := Layout p, Layout.IsWellFormed p

def Layout.apply (prog : Program Instr Const) (l : Layout prog) : Executable Instr Const :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size directive i})}

abbrev Program.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

abbrev _root_.List.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

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

theorem Executable.withAddresses_map_snd (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

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

theorem Layout.apply_getElem? (prog : Program Instr Const) [l : Layout prog]
    (i : Nat) :
    prog.toExecutable.program[i]? = prog[i]?.map fun d => {directive := d, size := l.size d i} := by
  simp [Layout.apply, List.getElem?_mapIdx]

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp [hhead a rfl]
    | succ n =>
      simp [hprior 0 (Nat.zero_lt_succ n) a rfl,
        ih (fun k hk => hprior (k + 1) (Nat.succ_lt_succ hk)) hhead]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn
  grind

/-- If the `k`-th directive `c` of `e` has positive size (`0 < c.size`) and addresses do not wrap
around (`hinj`), then `e.directivesAtAddress (e.addrOf k)` consists of a prefix `pre` of zero-size
directives (such as labels) at `e.addrOf k` followed by `[c]`. -/
theorem Executable.directivesAtAddress_addrOf (e : Executable Instr Const)
    (hinj : ∀ j k, e.addrOf j = e.addrOf k → e.sizeBefore j = e.sizeBefore k)
    {k : Nat} {c : Sized (Directive Instr Const)} (hc : e.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre, e.directivesAtAddress (e.addrOf k) = pre ++ [c] ∧
      ∀ c' ∈ pre, c' ∈ e.program ∧ c'.size = 0 := by
  obtain ⟨j, hjk, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hsize := hinj j k hj
  have hpre (c') (hc' : c' ∈ (e.program.drop j).take (k - j)) : c' ∈ e.program ∧ c'.size = 0 := by
    have := e.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((e.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact ⟨(List.drop_sublist _ _).subset ((List.take_sublist _ _).subset hc'),
      List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc')⟩
  have haddr (m : Nat) (hjm : j ≤ m) (hmk : m ≤ k) : e.addrOf m = e.addrOf k := by
    grind [Executable.addrOf, e.sizeBefore_mono hjm, e.sizeBefore_mono hmk]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := by grind [hinj (k + 1) k]
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  rw [Executable.directivesAtAddress, Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc, Option.toList]
  · grind [Executable.getElem?_withAddresses_eq, Executable.sizeBefore_mono]
  · grind [Executable.getElem?_withAddresses_eq]

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
    (Program.map_size_toExecutable_eq prog ▸ Layout.IsWellFormed.no_overflow)

theorem Program.sizeBefore_eq_of_addrOf_eq (prog : Program Instr Const) [WellFormedLayout prog]
    {j k : Nat} (h : prog.toExecutable.addrOf j = prog.toExecutable.addrOf k) :
    prog.toExecutable.sizeBefore j = prog.toExecutable.sizeBefore k := by
  have hj := Program.sizeBefore_lt prog j
  have hk := Program.sizeBefore_lt prog k
  grind [Executable.addrOf]

def Directive.isLabel (lbl : Label) : Directive Instr Const → Bool
  | .label l => l == lbl
  | _ => false

@[simp] theorem Directive.isLabel_iff {lbl : Label} {d : Directive Instr Const} :
    d.isLabel lbl = true ↔ d = .label lbl := by
  cases d <;> simp [Directive.isLabel]

theorem Executable.withAddresses_findSome?_label_mk [DecidableEq Instr] [DecidableEq Const] :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (lbl : Label) (k : Nat),
      program.findIdx? (·.directive.isLabel lbl) = some k →
      (Executable.withAddresses {startAddr, program}).findSome?
        (fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none) =
        some (Executable.addrOf {startAddr, program} k)
  | [], _, _, _, hk => by simp at hk
  | c :: program, startAddr, lbl, k, hk => by
    rw [Executable.withAddresses, List.findSome?_cons]
    rw [List.findIdx?_cons] at hk
    by_cases h : c.directive = .label lbl
    · have his : c.directive.isLabel lbl = true := Directive.isLabel_iff.mpr h
      simp [his] at hk
      subst hk
      simp [h]
    · have his : c.directive.isLabel lbl = false :=
        Bool.eq_false_iff.mpr (mt Directive.isLabel_iff.mp h)
      simp [his] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp only [h, ↓reduceIte, withAddresses_findSome?_label_mk program _ lbl k' hk']
      simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
      grind

theorem Layout.map_directive_apply (prog : Program Instr Const) [l : Layout prog] :
    prog.toExecutable.program.map (·.directive) = prog := by
  apply List.ext_getElem?
  simp [Layout.apply, Function.comp_def]

/-- If `k` is the index of the first `.label lbl` directive in `prog`, looking up `lbl` in
`prog.toExecutable.withAddresses` yields `some (prog.toExecutable.addrOf k)`. -/
theorem Layout.withAddresses_findSome?_label [DecidableEq Instr] [DecidableEq Const]
    (prog : Program Instr Const) [l : Layout prog] (lbl : Label) {k : Nat}
    (hk : prog.findIdx? (·.isLabel lbl) = some k) :
    (prog.toExecutable.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none)) =
      some (prog.toExecutable.addrOf k) := by
  apply Executable.withAddresses_findSome?_label_mk
  rw [← l.map_directive_apply prog, List.findIdx?_map] at hk
  exact hk

end Kraken
