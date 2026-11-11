module

import Kraken.ForLean
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

def Program.labels (p : Program Instr Const) : List Label := p.filterMap fun
  | .label l => l
  | _ => none

-- NOTE: Maybe this should not be a property on `Layout`, but on `Program`...
class Layout.IsWellFormed (p : Program Instr Const) [Layout p] where
  no_overflow : p.size < 2^64
  unique_labels : p.labels.Nodup

class abbrev WellFormedLayout (p : Program Instr Const) := Layout p, Layout.IsWellFormed p

def Layout.apply (prog : Program Instr Const) (l : Layout prog) : Executable Instr Const :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size directive i})}

abbrev Program.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

abbrev _root_.List.toExecutable (prog : Program Instr Const) [l : Layout prog] := l.apply prog

@[instance_reducible]
def Layout.drop (p₁ : Program Instr Const) {p₂} [l : Layout (p₁ ++ p₂)] : Layout p₂ where
  start := l.start + .ofNat (p₁.mapIdx (fun i d => l.size d i) |>.sum)
  instrSize i := l.instrSize (i + p₁.length)

@[instance_reducible]
def Layout.take (p₁ : Program Instr Const) {p₂} [l : Layout (p₁ ++ p₂)] : Layout p₁ where
  start := l.start
  instrSize i := l.instrSize i

@[simp]
theorem Layout.size_drop (p₁ : Program Instr Const) {p₂} [l : Layout (p₁ ++ p₂)]
    (d : Directive Instr Const) (i : Nat) :
    (l.drop p₁).size d i = l.size d (i + p₁.length) := by
  cases d <;> rfl

@[simp]
theorem Layout.size_take (p₁ : Program Instr Const) {p₂} [l : Layout (p₁ ++ p₂)]
    (d : Directive Instr Const) (i : Nat) :
    (l.take p₁).size d i = l.size d i := by
  cases d <;> rfl

theorem Program.size_append (p₁ p₂ : Program Instr Const) [layout : Layout (p₁ ++ p₂)] :
    letI := layout.take p₁
    letI := layout.drop p₁
    (p₁ ++ p₂).size = p₁.size + p₂.size
    := by
  simp only [size, Layout.size_take, Layout.size_drop]
  grind

@[instance_reducible]
nonrec def WellFormedLayout.drop (p₁ : Program Instr Const) {p₂} [l : WellFormedLayout (p₁ ++ p₂)] :
    WellFormedLayout p₂ := {l.drop p₁ with
    no_overflow := Nat.lt_of_add_left_lt <| Program.size_append p₁ p₂ (layout := l.toLayout) ▸ l.no_overflow
    unique_labels := by grind [Program.labels, l.unique_labels]
  }

@[instance_reducible]
nonrec def WellFormedLayout.take (p₁ : Program Instr Const) {p₂} [l : WellFormedLayout (p₁ ++ p₂)] :
    WellFormedLayout p₁ := {l.take p₁ with
    no_overflow := Nat.lt_of_add_right_lt <| Program.size_append p₁ p₂ (layout := l.toLayout) ▸ l.no_overflow
    unique_labels := by grind [Program.labels, l.unique_labels]
  }

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

private theorem add_ofNat_add (a : Int64) (b c : Nat) :
    a + .ofNat b + .ofNat c = a + .ofNat (b + c) := by grind

theorem Executable.withAddresses_eq_mapIdx (e : Executable Instr Const) :
    e.withAddresses = e.program.mapIdx fun idx c => {c with addr := e.addrOf idx} :=
  List.ext_getElem? fun k => by
    simpa [List.getElem?_mapIdx] using e.getElem?_withAddresses_eq k

theorem Program.withAddresses_toExecutable (p : Program Instr Const) [layout : Layout p] :
    p.toExecutable.withAddresses =
      p.mapIdx fun idx directive =>
        {directive, size := layout.size directive idx, addr := p.toExecutable.addrOf idx} :=
  List.ext_getElem? fun k => by
    simp [Executable.withAddresses_eq_mapIdx, Program.toExecutable, Layout.apply,
      List.getElem?_mapIdx, Function.comp_def]

@[simp] theorem Program.map_directive_toExecutable (p : Program Instr Const) [Layout p] :
    p.toExecutable.program.map (·.directive) = p :=
  List.ext_getElem? fun k => by
    simp [Program.toExecutable, Layout.apply, List.getElem?_mapIdx, Function.comp_def]

@[simp] theorem Program.map_directive_withAddresses (p : Program Instr Const) [Layout p] :
    p.toExecutable.withAddresses.map (·.directive) = p :=
  List.ext_getElem? fun k => by
    simp [Program.withAddresses_toExecutable, List.getElem?_mapIdx, Function.comp_def]

private theorem mem_withAddresses_toExecutable (p : Program Instr Const) [layout : Layout p]
    {x : Addressable (Directive Instr Const)} (hx : x ∈ p.toExecutable.withAddresses) :
    ∃ i : Fin p.length,
      x = {directive := p[i], size := layout.size p[i] i, addr := p.toExecutable.addrOf i} ∧
      p.toExecutable.sizeBefore i + x.size ≤ p.size := by
  rw [Program.withAddresses_toExecutable] at hx
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_mapIdx, List.getElem_mapIdx] at hi heq
  have hc : p.toExecutable.program[i]? = some {directive := p[i], size := layout.size p[i] i} := by
    simp [Program.toExecutable, Layout.apply, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
  refine ⟨⟨i, hi⟩, heq.symm, ?_⟩
  have hle := p.toExecutable.sizeBefore_succ hc ▸ p.toExecutable.sizeBefore_le (i + 1)
  rw [Program.map_size_toExecutable_eq] at hle
  simpa [← heq] using hle

theorem Program.mem_directivesAtAddress (p : Program Instr Const) [layout : Layout p]
    {a : Int64} {c : Sized (Directive Instr Const)} (h : c ∈ p.toExecutable.directivesAtAddress a) :
    ∃ i : Fin p.length,
      c = {directive := p[i], size := layout.size p[i] i} ∧ p.toExecutable.addrOf i = a := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have haddr : x.addr = a := by simpa using List.mem_takeWhile hx
  obtain ⟨i, rfl, -⟩ := mem_withAddresses_toExecutable p
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))
  exact ⟨i, rfl, haddr⟩

theorem Program.toExecutable_append_withAddresses (p₁ p₂ : Program Instr Const)
    [l : Layout (p₁ ++ p₂)] :
    letI := l.take p₁; letI := l.drop p₁
    (p₁ ++ p₂).toExecutable.withAddresses =
      p₁.toExecutable.withAddresses ++ p₂.toExecutable.withAddresses := by
  letI := l.take p₁; letI := l.drop p₁
  have hprog : (p₁ ++ p₂).toExecutable.program =
      p₁.toExecutable.program ++ p₂.toExecutable.program := by
    simp only [Layout.apply, List.mapIdx_append]
    congr 1; simp [Layout.size_drop]
  have hlen : p₁.toExecutable.program.length = p₁.length := by simp [Layout.apply]
  rw [Program.withAddresses_toExecutable (p₁ ++ p₂), Program.withAddresses_toExecutable p₁,
      Program.withAddresses_toExecutable p₂, List.mapIdx_append]
  congr 1
  · refine List.ext_getElem? fun i => ?_
    by_cases hi : i < p₁.length
    · have hadr : (p₁ ++ p₂).toExecutable.addrOf i = p₁.toExecutable.addrOf i := by
        rw [Executable.addrOf, Executable.addrOf, Executable.sizeBefore, Executable.sizeBefore,
            hprog, List.take_append_of_le_length (by omega)]; rfl
      simp only [List.getElem?_mapIdx, List.getElem?_eq_getElem hi, Option.map_some, hadr, Layout.size_take]
    · simp [List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · refine List.ext_getElem? fun i => ?_
    have hadr : (p₁ ++ p₂).toExecutable.addrOf (i + p₁.length) = p₂.toExecutable.addrOf i := by
      rw [Nat.add_comm, Executable.addrOf, Executable.sizeBefore_add, Executable.sizeBefore,
          Executable.addrOf, Executable.sizeBefore, hprog, List.take_left' hlen,
          List.drop_left' hlen, Program.map_size_toExecutable_eq p₁]
      change l.start + .ofNat (_ + _) = l.start + .ofNat _ + .ofNat _
      rw [← add_ofNat_add]; simp [Program.size]
    simp only [List.getElem?_mapIdx, hadr, Layout.size_drop]

theorem Program.directivesAtAddress_take_eq (p₁ p₂ : Program Instr Const)
    [layout : WellFormedLayout (p₁ ++ p₂)] (pc : Int64)
    (hpos : letI := layout.take p₁; ∃ c ∈ p₁.toExecutable.directivesAtAddress pc, 0 < c.size) :
    letI := layout.take p₁
    (p₁ ++ p₂).toExecutable.directivesAtAddress pc = p₁.toExecutable.directivesAtAddress pc := by
  letI l₁ : Layout p₁ := layout.toLayout.take p₁
  letI l₂ : Layout p₂ := layout.toLayout.drop p₁
  change (p₁ ++ p₂).toExecutable.directivesAtAddress pc = p₁.toExecutable.directivesAtAddress pc
  obtain ⟨_, hc, hcsz⟩ : ∃ c ∈ p₁.toExecutable.directivesAtAddress pc, 0 < c.size := hpos
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  have hx_drop : x ∈ p₁.toExecutable.withAddresses.dropWhile (·.addr ≠ pc) :=
    (List.takeWhile_sublist _).subset hx
  have hx_addr : x.addr = pc := by simpa using List.mem_takeWhile hx
  obtain ⟨i₁, hx₁, hi₁⟩ := mem_withAddresses_toExecutable p₁ ((List.dropWhile_sublist _).subset hx_drop)
  have haddr₁ : x.addr = p₁.toExecutable.addrOf i₁ := congrArg Addressable.addr hx₁
  have hsum_lt : p₁.size + p₂.size < UInt64.size :=
    Program.size_append p₁ p₂ (layout := layout.toLayout) ▸ layout.no_overflow
  have htw₂ : p₂.toExecutable.withAddresses.takeWhile (·.addr = pc) = [] := by
    cases h : p₂.toExecutable.withAddresses.takeWhile (·.addr = pc) with
    | nil => rfl
    | cons y _ =>
      have hy_mem : y ∈ p₂.toExecutable.withAddresses :=
        (List.takeWhile_sublist _).subset (h ▸ List.mem_cons_self)
      have hy_addr : y.addr = pc := by
        have := List.mem_takeWhile (h ▸ List.mem_cons_self); simpa using this
      obtain ⟨i₂, hy₂, hi₂⟩ := mem_withAddresses_toExecutable p₂ hy_mem
      have haddr₂ : y.addr = p₂.toExecutable.addrOf i₂ := congrArg Addressable.addr hy₂
      have he₂ : p₂.toExecutable.startAddr = p₁.toExecutable.startAddr + .ofNat p₁.size := by
        change layout.start + .ofNat (p₁.mapIdx (fun i d => layout.size d i) |>.sum) =
          layout.start + .ofNat p₁.size
        simp [Program.size, l₁]
      simp only [Executable.addrOf, he₂, add_ofNat_add] at haddr₁ haddr₂
      have := Int64.add_ofNat_inj (by omega) (by omega) ((hx_addr ▸ haddr₁).symm.trans (hy_addr ▸ haddr₂))
      omega
  have happ : (p₁ ++ p₂).toExecutable.withAddresses =
      p₁.toExecutable.withAddresses ++ p₂.toExecutable.withAddresses :=
    Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  have hne_emp : (p₁.toExecutable.withAddresses.dropWhile (·.addr ≠ pc)).isEmpty = false :=
    Bool.eq_false_iff.mpr (mt List.isEmpty_iff.mp (List.ne_nil_of_mem hx_drop))
  dsimp only [Executable.directivesAtAddress]
  simp only [happ, List.dropWhile_append, hne_emp, Bool.false_eq_true, ↓reduceIte, List.takeWhile_append]
  split
  · rename_i hlen
    rw [htw₂, List.append_nil, (List.takeWhile_sublist _).eq_of_length hlen]
  · rfl

theorem Program.directivesAtAddress_drop_eq (p₁ p₂ : Program Instr Const)
    [layout : WellFormedLayout (p₁ ++ p₂)] (pc : Int64)
    (hpos : letI := layout.drop p₁; ∃ c ∈ p₂.toExecutable.directivesAtAddress pc, 0 < c.size) :
    letI := layout.drop p₁
    ∃ pre, (p₁ ++ p₂).toExecutable.directivesAtAddress pc = pre ++ p₂.toExecutable.directivesAtAddress pc ∧
      ∀ c ∈ pre, c.size = 0 := by
  letI l₁ : Layout p₁ := layout.toLayout.take p₁
  letI l₂ : Layout p₂ := layout.toLayout.drop p₁
  change ∃ pre, (p₁ ++ p₂).toExecutable.directivesAtAddress pc = pre ++ p₂.toExecutable.directivesAtAddress pc ∧ _
  obtain ⟨_, hc₀, _⟩ : ∃ c ∈ p₂.toExecutable.directivesAtAddress pc, 0 < c.size := hpos
  obtain ⟨i₂, _, haddr₂⟩ := Program.mem_directivesAtAddress p₂ hc₀
  have hi₂ : p₂.toExecutable.sizeBefore i₂ ≤ p₂.size :=
    Program.map_size_toExecutable_eq p₂ ▸ p₂.toExecutable.sizeBefore_le i₂
  have hsum_lt : p₁.size + p₂.size < UInt64.size :=
    Program.size_append p₁ p₂ (layout := layout.toLayout) ▸ layout.no_overflow
  have he₂ : p₂.toExecutable.startAddr = p₁.toExecutable.startAddr + .ofNat p₁.size := by
    change layout.start + .ofNat (p₁.mapIdx (fun i d => layout.size d i) |>.sum) =
      layout.start + .ofNat p₁.size
    simp [Program.size, l₁]
  have happ : (p₁ ++ p₂).toExecutable.withAddresses =
      p₁.toExecutable.withAddresses ++ p₂.toExecutable.withAddresses :=
    Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  let w₁' := p₁.toExecutable.withAddresses.dropWhile (·.addr ≠ pc)
  cases h_emp : w₁'.isEmpty with
  | true =>
    refine ⟨[], ?_, by simp⟩
    dsimp only [Executable.directivesAtAddress]
    rw [happ, List.dropWhile_append, h_emp, List.nil_append]; rfl
  | false =>
    have hne : w₁' ≠ [] := fun h => by simp [h] at h_emp
    let j := p₁.toExecutable.withAddresses.findIdx (fun a => !decide (a.addr ≠ pc))
    have hw₁' : w₁' = p₁.toExecutable.withAddresses.drop j := List.dropWhile_eq_drop_findIdx_not
    have hj_lt : j < p₁.toExecutable.withAddresses.length :=
      Classical.byContradiction fun hge => hne (hw₁'.trans (List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)))
    have hj_addr : p₁.toExecutable.addrOf j = pc := by
      have hhead : !decide (p₁.toExecutable.withAddresses[j].addr ≠ pc) = true :=
        List.findIdx_getElem (w := hj_lt)
      have hget := Executable.getElem?_withAddresses_eq p₁.toExecutable j
      rw [List.getElem?_eq_getElem hj_lt] at hget
      obtain ⟨_, -, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have : p₁.toExecutable.withAddresses[j].addr = p₁.toExecutable.addrOf j :=
        congrArg Addressable.addr heq.symm
      grind
    simp only [Executable.addrOf, he₂, add_ofNat_add] at hj_addr haddr₂
    have hj_le : p₁.toExecutable.sizeBefore j ≤ p₁.size :=
      Program.map_size_toExecutable_eq p₁ ▸ p₁.toExecutable.sizeBefore_le j
    have hoff_eq : p₁.toExecutable.sizeBefore j = p₁.size + p₂.toExecutable.sizeBefore i₂ :=
      Int64.add_ofNat_inj (by omega) (by omega) (hj_addr.trans haddr₂.symm)
    have hpc_e₂ : p₂.toExecutable.startAddr = pc := by
      rw [← hj_addr, he₂]; congr 1; congr 1; omega
    have hw₁'_prop : ∀ x ∈ w₁', x.addr = pc ∧ x.size = 0 := by
      intro x hx
      rw [hw₁'] at hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      simp only [List.getElem_drop]
      have hget := Executable.getElem?_withAddresses_eq p₁.toExecutable (j + i)
      rw [List.getElem?_eq_getElem (by rw [List.length_drop] at hi; omega)] at hget
      obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have hmono := p₁.toExecutable.sizeBefore_mono (Nat.le_add_right j i)
      have hsucc : p₁.toExecutable.sizeBefore (j + i) + c.size ≤ p₁.size :=
        Program.map_size_toExecutable_eq p₁ ▸
          (p₁.toExecutable.sizeBefore_succ hc ▸ p₁.toExecutable.sizeBefore_le (j + i + 1))
      rw [← heq]
      refine ⟨?_, by dsimp; omega⟩
      dsimp [Executable.addrOf]
      rw [← hj_addr]; congr 1; congr 1; omega
    have hdrop₂ : p₂.toExecutable.withAddresses.dropWhile (·.addr ≠ pc) = p₂.toExecutable.withAddresses := by
      simpa only [← hpc_e₂, Executable.addrOf_zero, List.drop_zero] using
        p₂.toExecutable.withAddresses_dropWhile_addrOf 0 0 rfl (by omega)
    refine ⟨w₁'.map (·.toSized), ?_, fun c hc => ?_⟩
    · dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
      simp only [happ, List.dropWhile_append, h_emp, Bool.false_eq_true, ↓reduceIte, hdrop₂]
      rw [List.takeWhile_append_of_pos (fun x hx => decide_eq_true (hw₁'_prop x hx).1), List.map_append]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact (hw₁'_prop x hx).2

end Kraken
