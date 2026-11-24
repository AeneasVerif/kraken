module

import Kraken.ForLean
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

/-- `ds₁` is `ds₂` preceded by zero-size directives. -/
def ZeroSizePrefix {D : Type} (ds₁ ds₂ : List (Sized D)) : Prop :=
  ∃ pre, ds₁ = pre ++ ds₂ ∧ ∀ c ∈ pre, c.size = 0

abbrev Program Instr Const := List (Directive Instr Const)

structure Executable (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))

variable {Instr Const : Type}

def Executable.sizeAt (e : Executable Instr Const) (n : Nat) : Nat :=
  (e.program[n]?.map (·.size)).getD 0

/-- `offsetOf` definition tuned for unification performance. -/
def Executable.offsetOf (e : Executable Instr Const) : Nat → Nat
  | 0 => 0
  | n + 1 => e.offsetOf n + e.sizeAt n

/-- `offsetOf` definition tuned for runtime performance. -/
def Executable.offsetOf.efficient (e : Executable Instr Const) (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/-- Replace `offsetOf` with `efficient` on compilation. -/
@[csimp] theorem Executable.offsetOf_eq_efficient :
    @Executable.offsetOf = @Executable.offsetOf.efficient := by
  funext _ _ e n
  induction n <;> grind [offsetOf, offsetOf.efficient, sizeAt, List.take_add_one]

/-- `addrOf` definition tuned for unification performance. -/
def Executable.addrOf (e : Executable Instr Const) : Nat → Int64
  | 0 => e.startAddr
  | n + 1 => e.addrOf n + .ofNat (e.sizeAt n)

@[defeq, simp] theorem Executable.addrOf_zero (e : Executable Instr Const) : e.addrOf 0 = e.startAddr := rfl

/-- `addrOf` definition tuned for runtime performance. -/
def Executable.addrOf.efficient (e : Executable Instr Const) (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.offsetOf n)

/-- Replace `addrOf` with `efficient` on compilation. -/
@[csimp] theorem Executable.addrOf_eq_efficient : @Executable.addrOf = @Executable.addrOf.efficient := by
  funext _ _ e n
  unfold addrOf.efficient
  induction n <;> simp [*, addrOf, offsetOf, Int64.ofNat_add, Int64.add_assoc]

theorem Executable.addrOf_eq_add_offsetOf (e : Executable Instr Const) (n : Nat) :
    e.addrOf n = e.startAddr + .ofNat (e.offsetOf n) := by
  rw [Executable.addrOf_eq_efficient, addrOf.efficient]

theorem Executable.offsetOf_mono (e : Executable Instr Const) {j k : Nat} (h : j ≤ k) :
    e.offsetOf j ≤ e.offsetOf k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
local grind_pattern Executable.offsetOf_mono => e.offsetOf j, e.offsetOf k

/-- Past the end of the program, offsets stop growing. -/
theorem Executable.offsetOf_le_length (e : Executable Instr Const) (n : Nat) :
    e.offsetOf n ≤ e.offsetOf e.program.length := by
  by_cases h : n ≤ e.program.length
  · exact e.offsetOf_mono h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h)
    refine Nat.le_of_eq ?_
    clear h
    induction m with
    | zero => rfl
    | succ m ih => grind [offsetOf, sizeAt]

theorem Executable.offsetOf_append_left {e e₁ e₂ : Executable Instr Const}
    (h : e.program = e₁.program ++ e₂.program) {i : Nat} (hi : i ≤ e₁.program.length) :
    e.offsetOf i = e₁.offsetOf i := by
  induction i <;> grind [offsetOf, sizeAt]

theorem Executable.offsetOf_append_right {e e₁ e₂ : Executable Instr Const}
    (h : e.program = e₁.program ++ e₂.program) (k : Nat) :
    e.offsetOf (e₁.program.length + k) = e₁.offsetOf e₁.program.length + e₂.offsetOf k := by
  induction k <;> grind [offsetOf, sizeAt, offsetOf_append_left]

/-- A placement of a program in memory. We have `instrSize` implemented as a `Nat → Nat` because on X64 the same directive might be encoded in different ways in different parts of the program. -/
structure Layout where
  start : Int64 -- NOTE: Why is `start` a `Int64`?
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

def Layout.dirSize (p : Program Instr Const) (l : Layout) (i : Nat) : Nat :=
  match p[i]? with
  | some <| .instr _ => l.instrSize i
  | some <| .label _ => 0
  | some <| .byteArray arr => arr.size
  | some <| .word bytes _ => bytes
  | none => 0

def Program.labels (p : Program Instr Const) : List Label := p.filterMap fun
  | .label l => l
  | _ => none

-- NOTE: The list is built with `List.zipIdx` and `List.map`, which unfold one element at a time, instead
-- of `List.mapIdx` which goes through an `Array` accumulator and makes definitional unfolding time out.
def Layout.apply (prog : Program Instr Const) (l : Layout) : Executable Instr Const :=
  {startAddr := l.start, program := prog.zipIdx.map fun (d, i) => {directive := d, size := l.dirSize prog i}}

@[simp] theorem Layout.length_apply_program (prog : Program Instr Const) (l : Layout) :
    (l.apply prog).program.length = prog.length := by
  simp only [Layout.apply, List.length_map, List.length_zipIdx]

theorem Layout.apply_getElem? (prog : Program Instr Const) (l : Layout) (i : Nat) :
    (l.apply prog).program[i]? = prog[i]?.map fun d => {directive := d, size := l.dirSize prog i} := by
  simp only [Layout.apply, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add]
  rfl

theorem Layout.map_directive_apply (prog : Program Instr Const) (l : Layout) :
    (l.apply prog).program.map (·.directive) = prog := by
  simp only [Layout.apply, List.map_map]
  exact List.zipIdx_map_fst 0 prog

/-- The total size of `p` laid out with `l`: the offset at which it ends. -/
def Program.size (p : Program Instr Const) (l : Layout) : Nat :=
  (l.apply p).offsetOf p.length

def Layout.offset (p₁ : Program Instr Const) (l : Layout) : Layout where
  start := (l.apply p₁).addrOf p₁.length
  instrSize i := l.instrSize (i + p₁.length)
  instrSize_pos i := l.instrSize_pos (i + p₁.length)

@[simp]
theorem Layout.dirSize_offset (p₁ p₂ : Program Instr Const) (l : Layout) (i : Nat) :
    (l.offset p₁).dirSize p₂ i = l.dirSize (p₁ ++ p₂) (i + p₁.length) := by
  dsimp only [Layout.dirSize, Layout.offset]
  rw [List.getElem?_append_right (Nat.le_add_left p₁.length i), Nat.add_sub_cancel]

theorem Layout.dirSize_append_left (p₁ p₂ : Program Instr Const) (l : Layout)
    {i : Nat} (hi : i < p₁.length) :
    l.dirSize (p₁ ++ p₂) i = l.dirSize p₁ i := by
  dsimp only [Layout.dirSize]
  rw [List.getElem?_append_left hi]

theorem Layout.apply_append_program (p₁ p₂ : Program Instr Const) (l : Layout) :
    (l.apply (p₁ ++ p₂)).program = (l.apply p₁).program ++ ((l.offset p₁).apply p₂).program := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < p₁.length
  · rw [List.getElem?_append_left (by simpa using hi), Layout.apply_getElem?, Layout.apply_getElem?,
      List.getElem?_append_left hi, Layout.dirSize_append_left p₁ p₂ l hi]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    rw [List.getElem?_append_right (by simp), Layout.length_apply_program, Nat.add_sub_cancel_left,
      Layout.apply_getElem?, Layout.apply_getElem?, List.getElem?_append_right (by grind),
      Nat.add_sub_cancel_left, Layout.dirSize_offset, Nat.add_comm j]

theorem Program.size_append (p₁ p₂ : Program Instr Const) (l : Layout) :
    (p₁ ++ p₂).size l = p₁.size l + p₂.size (l.offset p₁) := by
  have h := Executable.offsetOf_append_right (Layout.apply_append_program p₁ p₂ l) p₂.length
  rw [Layout.length_apply_program] at h
  rw [Program.size, List.length_append, h]
  rfl

theorem Program.offsetOf_le_size (p : Program Instr Const) (l : Layout) (n : Nat) :
    (l.apply p).offsetOf n ≤ p.size l := by
  have := (l.apply p).offsetOf_le_length n
  rwa [Layout.length_apply_program] at this

class Layout.WellFormed (l : Layout) (p : Program Instr Const) : Prop where
  no_overflow : p.size l < 2^64
  unique_labels : p.labels.Nodup

theorem Layout.WellFormed.append_left {p₁ p₂ : Program Instr Const} {l : Layout}
    (h : l.WellFormed (p₁ ++ p₂)) : l.WellFormed p₁ where
  no_overflow := by grind only [Program.size_append, Layout.WellFormed]
  unique_labels := by grind [Program.labels, h.unique_labels]

theorem Layout.WellFormed.append_right {p₁ p₂ : Program Instr Const} {l : Layout}
    (h : l.WellFormed (p₁ ++ p₂)) : (l.offset p₁).WellFormed p₂ where
  no_overflow := by grind only [Program.size_append, Layout.WellFormed]
  unique_labels := by grind [Program.labels, h.unique_labels]

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

@[simp] theorem Executable.withAddresses_nil (startAddr : Int64) :
    Executable.withAddresses {startAddr, program := ([] : List (Sized (Directive Instr Const)))} = [] := by
  rw [withAddresses]

@[simp] theorem Executable.withAddresses_cons (startAddr : Int64) :
    Executable.withAddresses {startAddr, program := c :: program} =
      {c with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat c.size, program} := by
  rw [withAddresses]

theorem Executable.length_withAddresses : e.withAddresses.length = e.program.length := by
  simpa using congrArg List.length (withAddresses_map_snd e.program e.startAddr)

theorem Executable.addrOf_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  simp [addrOf, sizeAt, hc]

/-- Past the first directive, addresses are those of the remaining directives, starting after it. -/
theorem Executable.addrOf_cons_succ (startAddr : Int64) (k : Nat) :
    Executable.addrOf {startAddr, program := c :: program} (k + 1) =
      Executable.addrOf {startAddr := startAddr + .ofNat c.size, program} k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + _) ih

theorem Executable.getElem?_withAddresses_eq (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) := by
  obtain ⟨startAddr, program⟩ := e
  induction program generalizing startAddr k with
  | nil => simp only [withAddresses_nil, List.getElem?_nil, Option.map_none]
  | cons c program ih =>
    rw [withAddresses_cons]
    cases k with
    | zero => rfl
    | succ k => rw [List.getElem?_cons_succ, ih, addrOf_cons_succ, List.getElem?_cons_succ]

/-- The addresses of `xs ++ ys` are those of `xs`, followed by those of `ys` starting where `xs`
ends. -/
theorem Executable.withAddresses_append (startAddr : Int64) (xs ys : List (Sized (Directive Instr Const))) :
    Executable.withAddresses {startAddr, program := xs ++ ys} =
      Executable.withAddresses {startAddr, program := xs} ++
        Executable.withAddresses
          {startAddr := Executable.addrOf {startAddr, program := xs} xs.length, program := ys} := by
  induction xs generalizing startAddr with
  | nil => simp only [List.nil_append, withAddresses_nil, List.length_nil, addrOf_zero]
  | cons c xs ih =>
    simp only [List.cons_append, withAddresses_cons, ih, List.length_cons, addrOf_cons_succ]

private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by grind))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by grind) _ (List.getElem?_eq_getElem hi)]

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

theorem Program.offsetOf_lt {prog : Program Instr Const} {l : Layout} (hl : l.WellFormed prog)
    (n : Nat) :
    (l.apply prog).offsetOf n < 2^64 :=
  Nat.lt_of_le_of_lt (Program.offsetOf_le_size prog l n) hl.no_overflow

theorem Program.offsetOf_eq_of_addrOf_eq {prog : Program Instr Const} {l : Layout}
    (hl : l.WellFormed prog)
    {j k : Nat} (h : (l.apply prog).addrOf j = (l.apply prog).addrOf k) :
    (l.apply prog).offsetOf j = (l.apply prog).offsetOf k := by
  have hj := Program.offsetOf_lt hl j
  have hk := Program.offsetOf_lt hl k
  grind [Executable.addrOf_eq_add_offsetOf]

/-- If the `k`-th directive `d` of `prog` has positive size (`0 < l.dirSize prog k`), then
`(l.apply prog).directivesAtAddress ((l.apply prog).addrOf k)` consists of a prefix of
zero-size directives at `(l.apply prog).addrOf k` followed by `[{directive := d, size := l.dirSize prog k}]`. -/
theorem Program.directivesAtAddress_addrOf {prog : Program Instr Const} {l : Layout}
    (hl : l.WellFormed prog)
    {k : Nat} {d : Directive Instr Const} (hd : prog[k]? = some d) (hz : 0 < l.dirSize prog k) :
    ZeroSizePrefix ((l.apply prog).directivesAtAddress ((l.apply prog).addrOf k))
      [{directive := d, size := l.dirSize prog k}] := by
  let e := l.apply prog
  have hc : e.program[k]? = some {directive := d, size := l.dirSize prog k} := by
    simp [e, Layout.apply_getElem?, hd]
  obtain ⟨j, hjk, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hoff : e.offsetOf j = e.offsetOf k := Program.offsetOf_eq_of_addrOf_eq hl hj
  have hpre (c') (hc' : c' ∈ (e.program.drop j).take (k - j)) : c'.size = 0 := by
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hc'
    -- The size at `j + t` enters through `offsetOf (j + t + 1)`, which `grind` cannot invent.
    have : e.offsetOf (j + t + 1) = e.offsetOf (j + t) + e.sizeAt (j + t) := rfl
    grind [Executable.sizeAt]
  have haddr (m : Nat) (hjm : j ≤ m) (hmk : m ≤ k) : e.addrOf m = e.addrOf k := by
    grind [Executable.addrOf_eq_add_offsetOf]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := fun h => by
    have := Program.offsetOf_eq_of_addrOf_eq hl h
    grind [Executable.offsetOf, Executable.sizeAt]
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  rw [Executable.directivesAtAddress, Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc, Option.toList]
  · grind [Executable.getElem?_withAddresses_eq]
  · grind [Executable.getElem?_withAddresses_eq]

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
      simp [h, Executable.addrOf_zero]
    · have his : c.directive.isLabel lbl = false :=
        Bool.eq_false_iff.mpr (mt Directive.isLabel_iff.mp h)
      simp [his] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp only [h, ↓reduceIte, withAddresses_findSome?_label_mk program _ lbl k' hk',
        addrOf_cons_succ]

/-- If `k` is the index of the first `.label lbl` directive in `prog`, looking up `lbl` in
`(l.apply prog).withAddresses` yields `some ((l.apply prog).addrOf k)`. -/
theorem Layout.withAddresses_findSome?_label [DecidableEq Instr] [DecidableEq Const]
    (prog : Program Instr Const) (l : Layout) (lbl : Label) {k : Nat}
    (hk : prog.findIdx? (·.isLabel lbl) = some k) :
    ((l.apply prog).withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none)) =
      some ((l.apply prog).addrOf k) := by
  apply Executable.withAddresses_findSome?_label_mk
  rw [← l.map_directive_apply prog, List.findIdx?_map] at hk
  exact hk

@[simp] theorem Program.map_directive_withAddresses (p : Program Instr Const) (l : Layout) :
    (l.apply p).withAddresses.map (·.directive) = p := by
  have h := congrArg (List.map (·.directive)) (Executable.withAddresses_map_snd (l.apply p).program l.start)
  rw [List.map_map] at h
  exact h.trans (Layout.map_directive_apply p l)

private theorem mem_withAddresses_apply (p : Program Instr Const) (l : Layout)
    {x : Addressable (Directive Instr Const)} (hx : x ∈ (l.apply p).withAddresses) :
    ∃ i : Fin p.length,
      x = {directive := p[i], size := l.dirSize p i, addr := (l.apply p).addrOf i} ∧
      (l.apply p).offsetOf i + x.size ≤ p.size l := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  have hip : i < p.length := by simpa [Executable.length_withAddresses] using hi
  have hc : (l.apply p).program[i]? = some {directive := p[i], size := l.dirSize p i} := by
    rw [Layout.apply_getElem?, List.getElem?_eq_getElem hip, Option.map_some]
  have hx' := (l.apply p).getElem?_withAddresses_eq i
  rw [List.getElem?_eq_getElem hi, heq, hc, Option.map_some, Option.some.injEq] at hx'
  refine ⟨⟨i, hip⟩, hx', ?_⟩
  have := Program.offsetOf_le_size p l (i + 1)
  grind [Executable.offsetOf, Executable.sizeAt]

theorem Program.mem_directivesAtAddress (p : Program Instr Const) (l : Layout)
    {a : Int64} {c : Sized (Directive Instr Const)} (h : c ∈ (l.apply p).directivesAtAddress a) :
    ∃ i : Fin p.length,
      c = {directive := p[i], size := l.dirSize p i} ∧ (l.apply p).addrOf i = a := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have haddr : x.addr = a := by simpa using List.mem_takeWhile hx
  obtain ⟨i, rfl, -⟩ := mem_withAddresses_apply p l
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))
  exact ⟨i, rfl, haddr⟩

theorem Program.mem_of_zeroSizePrefix {p : Program Instr Const} {l : Layout}
    {pc : Int64} {pre rest : List (Sized (Directive Instr Const))}
    (hpre : (l.apply p).directivesAtAddress pc = pre ++ rest) (hz : ∀ c ∈ pre, c.size = 0)
    {c : Sized (Directive Instr Const)} (hc : c ∈ pre) :
    ∃ m d, p[m]? = some d ∧ c = {directive := d, size := 0} ∧ l.dirSize p m = 0 := by
  obtain ⟨i, rfl, -⟩ := Program.mem_directivesAtAddress p l (hpre ▸ List.mem_append_left _ hc)
  have hcz : l.dirSize p i = 0 := hz _ hc
  exact ⟨i, p[i], List.getElem?_eq_getElem i.isLt, by congr, hcz⟩

theorem Program.apply_append_withAddresses (p₁ p₂ : Program Instr Const) (l : Layout) :
    (l.apply (p₁ ++ p₂)).withAddresses =
      (l.apply p₁).withAddresses ++ ((l.offset p₁).apply p₂).withAddresses := by
  have h := Executable.withAddresses_append l.start (l.apply p₁).program
    ((l.offset p₁).apply p₂).program
  rw [Layout.length_apply_program, ← Layout.apply_append_program] at h
  exact h

/-- `p` covers address `pc`, i.e. `pc` lies in `[l.start, l.start + p.size l)` (modulo 2⁶⁴). -/
def Program.ContainsAddr (p : Program Instr Const) (l : Layout) (pc : Int64) : Prop :=
  ∃ off < p.size l, pc = l.start + .ofNat off

/-- If `p` has a positive-size directive at `pc`, then `p` contains `pc`. -/
theorem Program.containsAddr_of_mem_directivesAtAddress (p : Program Instr Const) (l : Layout)
    {pc : Int64} {c : Sized (Directive Instr Const)}
    (hc : c ∈ (l.apply p).directivesAtAddress pc) (hsz : 0 < c.size) :
    p.ContainsAddr l pc := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, hi_eq, hi_le⟩ := mem_withAddresses_apply p l
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))
  have hx_addr : x.addr = pc := by simpa using List.mem_takeWhile hx
  exact ⟨(l.apply p).offsetOf i, by grind,
    hx_addr.symm.trans ((congrArg Addressable.addr hi_eq).trans ((l.apply p).addrOf_eq_add_offsetOf i))⟩

theorem Program.directivesAtAddress_append_left {p₁ p₂ : Program Instr Const} {l : Layout}
    (hl : l.WellFormed (p₁ ++ p₂)) (pc : Int64)
    (hpc : p₁.ContainsAddr l pc) :
    (l.apply (p₁ ++ p₂)).directivesAtAddress pc = (l.apply p₁).directivesAtAddress pc := by
  have hno₂ : ∀ y ∈ ((l.offset p₁).apply p₂).withAddresses, y.addr ≠ pc := by
    intro y hy hy_addr
    obtain ⟨i₂, rfl, hi₂⟩ := mem_withAddresses_apply p₂ (l.offset p₁) hy
    obtain ⟨off, hoff_lt, hpc_eq⟩ := hpc
    have hsum : p₁.size l + p₂.size (l.offset p₁) < 2 ^ 64 := by
      grind [Program.size_append, hl.no_overflow]
    have hstart₂ : ((l.offset p₁).apply p₂).startAddr = l.start + .ofNat (p₁.size l) :=
      (l.apply p₁).addrOf_eq_add_offsetOf p₁.length
    grind [Executable.addrOf_eq_add_offsetOf]
  dsimp only [Executable.directivesAtAddress]
  rw [Program.apply_append_withAddresses p₁ p₂ l, List.dropWhile_append]
  cases h₁ : ((l.apply p₁).withAddresses.dropWhile (·.addr ≠ pc)).isEmpty with
  | true =>
    simp only [↓reduceIte, List.isEmpty_iff.mp h₁]
    rw [List.dropWhile_eq_drop_findIdx_not,
      List.drop_eq_nil_of_le (Nat.le_of_eq (List.findIdx_eq_length.mpr fun y hy => by simpa using hno₂ y hy).symm)]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.takeWhile_append]
    split
    · rename_i hlen
      have htw₂ : ((l.offset p₁).apply p₂).withAddresses.takeWhile (·.addr = pc) = [] := by
        cases h : ((l.offset p₁).apply p₂).withAddresses with
        | nil => rfl
        | cons y _ => simp [hno₂ y (h ▸ List.mem_cons_self)]
      rw [htw₂, List.append_nil, (List.takeWhile_sublist _).eq_of_length hlen]
    · rfl

theorem Program.directivesAtAddress_append_right {p₁ p₂ : Program Instr Const} {l : Layout}
    (hl : l.WellFormed (p₁ ++ p₂)) (pc : Int64)
    (hpc : p₂.ContainsAddr (l.offset p₁) pc) :
    ZeroSizePrefix ((l.apply (p₁ ++ p₂)).directivesAtAddress pc)
      (((l.offset p₁).apply p₂).directivesAtAddress pc) := by
  let w₁' := (l.apply p₁).withAddresses.dropWhile (·.addr ≠ pc)
  cases h_emp : w₁'.isEmpty with
  | true =>
    refine ⟨[], ?_, by simp⟩
    dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
    rw [Program.apply_append_withAddresses p₁ p₂ l, List.dropWhile_append, h_emp]
    rfl
  | false =>
    obtain ⟨off, hoff_lt, hpc_eq⟩ := hpc
    have hsum : p₁.size l + p₂.size (l.offset p₁) < 2 ^ 64 := by
      grind [Program.size_append, hl.no_overflow]
    have hstart₂ : (l.offset p₁).start = l.start + .ofNat (p₁.size l) :=
      (l.apply p₁).addrOf_eq_add_offsetOf p₁.length
    let j := (l.apply p₁).withAddresses.findIdx (fun a => !decide (a.addr ≠ pc))
    have hw₁' : w₁' = (l.apply p₁).withAddresses.drop j := List.dropWhile_eq_drop_findIdx_not
    have hj_lt : j < (l.apply p₁).withAddresses.length :=
      Classical.byContradiction fun hge => by
        simp [hw₁', List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)] at h_emp
    have hj_addr : (l.apply p₁).addrOf j = pc := by
      have hhead := List.findIdx_getElem (w := hj_lt)
      have hget := Executable.getElem?_withAddresses_eq (l.apply p₁) j
      rw [List.getElem?_eq_getElem hj_lt] at hget
      obtain ⟨_, -, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      grind
    have hoff_eq : (l.apply p₁).offsetOf j = p₁.size l ∧ off = 0 := by
      have : (l.apply p₁).offsetOf j ≤ p₁.size l := Program.offsetOf_le_size p₁ l j
      have hstart₁ : (l.apply p₁).startAddr = l.start := rfl
      grind [Executable.addrOf_eq_add_offsetOf]
    have hw₁'_prop : ∀ x ∈ w₁', x.addr = pc ∧ x.size = 0 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hw₁' ▸ hx)
      have hget := Executable.getElem?_withAddresses_eq (l.apply p₁) (j + k)
      rw [List.getElem?_eq_getElem (by grind)] at hget
      obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have := Program.offsetOf_le_size p₁ l (j + k + 1)
      simp only [List.getElem_drop, ← heq]
      grind [Executable.addrOf_eq_add_offsetOf, Executable.offsetOf, Executable.sizeAt]
    have hdrop₂ : ((l.offset p₁).apply p₂).withAddresses.dropWhile (·.addr ≠ pc) =
        ((l.offset p₁).apply p₂).withAddresses := by
      have hpc₂ : ((l.offset p₁).apply p₂).startAddr = pc := by
        change (l.offset p₁).start = pc; grind
      rw [← hpc₂]
      exact ((l.offset p₁).apply p₂).withAddresses_dropWhile_addrOf 0 0 rfl (by grind)
    refine ⟨w₁'.map (·.toSized), ?_, fun c hc => ?_⟩
    · dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
      rw [Program.apply_append_withAddresses p₁ p₂ l, List.dropWhile_append, h_emp]
      simp only [Bool.false_eq_true, ↓reduceIte, hdrop₂]
      rw [List.takeWhile_append_of_pos (fun x hx => decide_eq_true (hw₁'_prop x hx).1),
        List.map_append]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact (hw₁'_prop x hx).2
end Kraken
