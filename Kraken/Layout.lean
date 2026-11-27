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

def Program.size (p : Program Instr Const) (l : Layout) : Nat :=
  p.mapIdx (fun idx _ => l.dirSize p idx) |>.sum

def Program.labels (p : Program Instr Const) : List Label := p.filterMap fun
  | .label l => l
  | _ => none

def Layout.apply (prog : Program Instr Const) (l : Layout) : Executable Instr Const :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.dirSize prog i})}

def Layout.offset (p₁ : Program Instr Const) (l : Layout) : Layout where
  start := l.start + .ofNat (p₁.size l)
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

@[local simp]
private theorem Layout.mapIdx_dirSize_append_left (p₁ p₂ : Program Instr Const) (l : Layout)
    {α : Type _} (f : Nat → Directive Instr Const → Nat → α) :
    (p₁.mapIdx fun i d => f i d (l.dirSize (p₁ ++ p₂) i)) =
      p₁.mapIdx fun i d => f i d (l.dirSize p₁ i) :=
  List.ext_getElem? fun i => by
    by_cases hi : i < p₁.length
    · simp [List.getElem?_mapIdx, List.getElem?_eq_getElem hi, Layout.dirSize_append_left p₁ p₂ l hi]
    · simp [List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

@[local simp]
private theorem Layout.mapIdx_dirSize_append_left_const (p₁ p₂ : Program Instr Const) (l : Layout) :
    (p₁.mapIdx fun i _ => l.dirSize (p₁ ++ p₂) i) = p₁.mapIdx fun i _ => l.dirSize p₁ i :=
  Layout.mapIdx_dirSize_append_left p₁ p₂ l (fun _ _ sz => sz)

theorem Program.size_append (p₁ p₂ : Program Instr Const) (l : Layout) :
    (p₁ ++ p₂).size l = p₁.size l + p₂.size (l.offset p₁) := by
  simp only [size, Layout.mapIdx_dirSize_append_left_const, Layout.dirSize_offset,
    List.mapIdx_append, List.sum_append]

class Program.AssemblableWith (p : Program Instr Const) (l : Layout) : Prop where
  no_overflow : p.size l < 2^64
  unique_labels : p.labels.Nodup

theorem Program.AssemblableWith.append_left {p₁ p₂ : Program Instr Const} {l : Layout}
    (h : (p₁ ++ p₂).AssemblableWith l) : p₁.AssemblableWith l where
  no_overflow := by grind only [Program.size_append, Program.AssemblableWith]
  unique_labels := by grind [Program.labels, h.unique_labels]

theorem Program.AssemblableWith.append_right {p₁ p₂ : Program Instr Const} {l : Layout}
    (h : (p₁ ++ p₂).AssemblableWith l) : p₂.AssemblableWith (l.offset p₁) where
  no_overflow := by grind only [Program.size_append, Program.AssemblableWith]
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

theorem Layout.apply_getElem? (prog : Program Instr Const) (l : Layout)
    (i : Nat) :
    (l.apply prog).program[i]? = prog[i]?.map fun d => {directive := d, size := l.dirSize prog i} := by
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

theorem Program.map_size_apply_eq (p : Program Instr Const) (l : Layout) :
    ((l.apply p).program.map (·.size)).sum = p.size l := by
  dsimp [Layout.apply, Program.size]
  congr 1
  generalize (l.dirSize p) = sz
  induction p generalizing sz <;> simp [List.mapIdx_cons, *]

theorem Executable.sizeBefore_le (n : Nat) :
    e.sizeBefore n ≤ (e.program.map (·.size)).sum := by
  simpa [sizeBefore, List.take_of_length_le (Nat.le_max_right n e.program.length)] using
    e.sizeBefore_mono (Nat.le_max_left n e.program.length)

theorem Program.sizeBefore_lt {prog : Program Instr Const} {l : Layout} (hl : prog.AssemblableWith l)
    (n : Nat) :
    (l.apply prog).sizeBefore n < 2^64 :=
  Nat.lt_of_le_of_lt ((l.apply prog).sizeBefore_le n)
    (Program.map_size_apply_eq prog l ▸ hl.no_overflow)

theorem Program.sizeBefore_eq_of_addrOf_eq {prog : Program Instr Const} {l : Layout}
    (hl : prog.AssemblableWith l)
    {j k : Nat} (h : (l.apply prog).addrOf j = (l.apply prog).addrOf k) :
    (l.apply prog).sizeBefore j = (l.apply prog).sizeBefore k := by
  have hj := Program.sizeBefore_lt hl j
  have hk := Program.sizeBefore_lt hl k
  grind [Executable.addrOf]

/-- If the `k`-th directive `d` of `prog` has positive size (`0 < l.dirSize prog k`), then
`(l.apply prog).directivesAtAddress ((l.apply prog).addrOf k)` consists of a prefix of
zero-size directives at `(l.apply prog).addrOf k` followed by `[{directive := d, size := l.dirSize prog k}]`. -/
theorem Program.directivesAtAddress_addrOf {prog : Program Instr Const} {l : Layout}
    (hl : prog.AssemblableWith l)
    {k : Nat} {d : Directive Instr Const} (hd : prog[k]? = some d) (hz : 0 < l.dirSize prog k) :
    ZeroSizePrefix ((l.apply prog).directivesAtAddress ((l.apply prog).addrOf k))
      [{directive := d, size := l.dirSize prog k}] := by
  let e := l.apply prog
  have hc : e.program[k]? = some {directive := d, size := l.dirSize prog k} := by
    simp [e, Layout.apply_getElem?, hd]
  obtain ⟨j, hjk, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hsize : e.sizeBefore j = e.sizeBefore k := Program.sizeBefore_eq_of_addrOf_eq hl hj
  have hpre (c') (hc' : c' ∈ (e.program.drop j).take (k - j)) : c'.size = 0 := by
    have := e.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((e.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc')
  have haddr (m : Nat) (hjm : j ≤ m) (hmk : m ≤ k) : e.addrOf m = e.addrOf k := by
    grind [Executable.addrOf, e.sizeBefore_mono hjm, e.sizeBefore_mono hmk]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := fun h => by
    have : e.sizeBefore (k + 1) = e.sizeBefore k := Program.sizeBefore_eq_of_addrOf_eq hl h
    grind
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  rw [Executable.directivesAtAddress, Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc, Option.toList]
  · grind [Executable.getElem?_withAddresses_eq, Executable.sizeBefore_mono]
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
      simp [h]
    · have his : c.directive.isLabel lbl = false :=
        Bool.eq_false_iff.mpr (mt Directive.isLabel_iff.mp h)
      simp [his] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp only [h, ↓reduceIte, withAddresses_findSome?_label_mk program _ lbl k' hk']
      simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
      grind

theorem Layout.map_directive_apply (prog : Program Instr Const) (l : Layout) :
    (l.apply prog).program.map (·.directive) = prog := by
  apply List.ext_getElem?
  simp [Layout.apply, Function.comp_def]

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

theorem Executable.withAddresses_eq_mapIdx (e : Executable Instr Const) :
    e.withAddresses = e.program.mapIdx fun idx c => {c with addr := e.addrOf idx} :=
  List.ext_getElem? fun k => by
    simpa [List.getElem?_mapIdx] using e.getElem?_withAddresses_eq k

theorem Program.withAddresses_apply (p : Program Instr Const) (l : Layout) :
    (l.apply p).withAddresses =
      p.mapIdx fun idx directive =>
        {directive, size := l.dirSize p idx, addr := (l.apply p).addrOf idx} :=
  List.ext_getElem? fun k => by
    simp [Executable.withAddresses_eq_mapIdx, Layout.apply,
      List.getElem?_mapIdx, Function.comp_def]

@[simp] theorem Program.map_directive_withAddresses (p : Program Instr Const) (l : Layout) :
    (l.apply p).withAddresses.map (·.directive) = p :=
  List.ext_getElem? fun k => by
    simp [Program.withAddresses_apply, List.getElem?_mapIdx, Function.comp_def]

private theorem mem_withAddresses_apply (p : Program Instr Const) (l : Layout)
    {x : Addressable (Directive Instr Const)} (hx : x ∈ (l.apply p).withAddresses) :
    ∃ i : Fin p.length,
      x = {directive := p[i], size := l.dirSize p i, addr := (l.apply p).addrOf i} ∧
      (l.apply p).sizeBefore i + x.size ≤ p.size l := by
  rw [Program.withAddresses_apply] at hx
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_mapIdx, List.getElem_mapIdx] at hi heq
  have hc : (l.apply p).program[i]? = some {directive := p[i], size := l.dirSize p i} := by
    simp [Layout.apply, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
  refine ⟨⟨i, hi⟩, heq.symm, ?_⟩
  have hle := (l.apply p).sizeBefore_succ hc ▸ (l.apply p).sizeBefore_le (i + 1)
  rw [Program.map_size_apply_eq] at hle
  simpa [← heq] using hle

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
  have hprog : (l.apply (p₁ ++ p₂)).program =
      (l.apply p₁).program ++ ((l.offset p₁).apply p₂).program := by
    simp only [Layout.apply, List.mapIdx_append]
    congr 1 <;> simp
  have hlen : (l.apply p₁).program.length = p₁.length := by simp [Layout.apply]
  rw [Program.withAddresses_apply (p₁ ++ p₂), Program.withAddresses_apply p₁,
      Program.withAddresses_apply p₂, List.mapIdx_append]
  congr 1
  · refine List.ext_getElem? fun i => ?_
    by_cases hi : i < p₁.length
    · have hadr : (l.apply (p₁ ++ p₂)).addrOf i = (l.apply p₁).addrOf i := by
        rw [Executable.addrOf, Executable.addrOf, Executable.sizeBefore, Executable.sizeBefore,
            hprog, List.take_append_of_le_length (by omega)]; rfl
      simp only [List.getElem?_mapIdx, List.getElem?_eq_getElem hi, Option.map_some, hadr,
        Layout.dirSize_append_left p₁ p₂ l hi]
    · simp [List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · refine List.ext_getElem? fun i => ?_
    have hadr : (l.apply (p₁ ++ p₂)).addrOf (i + p₁.length) = ((l.offset p₁).apply p₂).addrOf i := by
      rw [Nat.add_comm, Executable.addrOf, Executable.sizeBefore_add, Executable.sizeBefore,
          Executable.addrOf, Executable.sizeBefore, hprog, List.take_left' hlen,
          List.drop_left' hlen, Program.map_size_apply_eq p₁]
      change l.start + .ofNat (_ + _) = l.start + .ofNat _ + .ofNat _
      grind
    simp only [List.getElem?_mapIdx, hadr, Layout.dirSize_offset]

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
  exact ⟨(l.apply p).sizeBefore i, by omega, hx_addr.symm.trans (congrArg Addressable.addr hi_eq)⟩

theorem Program.directivesAtAddress_append_left {p₁ p₂ : Program Instr Const} {l : Layout}
    (hl : (p₁ ++ p₂).AssemblableWith l) (pc : Int64)
    (hpc : p₁.ContainsAddr l pc) :
    (l.apply (p₁ ++ p₂)).directivesAtAddress pc = (l.apply p₁).directivesAtAddress pc := by
  have hno₂ : ∀ y ∈ ((l.offset p₁).apply p₂).withAddresses, y.addr ≠ pc := by
    intro y hy hy_addr
    obtain ⟨i₂, rfl, hi₂⟩ := mem_withAddresses_apply p₂ (l.offset p₁) hy
    obtain ⟨off, hoff_lt, hpc_eq⟩ := hpc
    have hsum : p₁.size l + p₂.size (l.offset p₁) < 2 ^ 64 := by
      have := Program.size_append p₁ p₂ l
      have := hl.no_overflow
      omega
    have hstart₂ : ((l.offset p₁).apply p₂).startAddr = l.start + .ofNat (p₁.size l) := rfl
    grind [Executable.addrOf]
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
    (hl : (p₁ ++ p₂).AssemblableWith l) (pc : Int64)
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
      have := Program.size_append p₁ p₂ l
      have := hl.no_overflow
      omega
    have hstart₂ : (l.offset p₁).start = l.start + .ofNat (p₁.size l) := rfl
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
    have hoff_eq : (l.apply p₁).sizeBefore j = p₁.size l ∧ off = 0 := by
      have := Program.map_size_apply_eq p₁ l ▸ (l.apply p₁).sizeBefore_le j
      have hstart₁ : (l.apply p₁).startAddr = l.start := rfl
      grind [Executable.addrOf]
    have hw₁'_prop : ∀ x ∈ w₁', x.addr = pc ∧ x.size = 0 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hw₁' ▸ hx)
      have hget := Executable.getElem?_withAddresses_eq (l.apply p₁) (j + k)
      rw [List.getElem?_eq_getElem (by rw [List.length_drop] at hk; omega)] at hget
      obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have := (l.apply p₁).sizeBefore_mono (Nat.le_add_right j k)
      have := Program.map_size_apply_eq p₁ l ▸
        ((l.apply p₁).sizeBefore_succ hc ▸ (l.apply p₁).sizeBefore_le (j + k + 1))
      simp only [List.getElem_drop, ← heq]
      grind [Executable.addrOf]
    have hdrop₂ : ((l.offset p₁).apply p₂).withAddresses.dropWhile (·.addr ≠ pc) =
        ((l.offset p₁).apply p₂).withAddresses := by
      have hpc₂ : ((l.offset p₁).apply p₂).startAddr = pc := by
        change (l.offset p₁).start = pc; grind
      simpa only [← hpc₂, Executable.addrOf_zero, List.drop_zero] using
        ((l.offset p₁).apply p₂).withAddresses_dropWhile_addrOf 0 0 rfl (by omega)
    refine ⟨w₁'.map (·.toSized), ?_, fun c hc => ?_⟩
    · dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
      rw [Program.apply_append_withAddresses p₁ p₂ l, List.dropWhile_append, h_emp]
      simp only [Bool.false_eq_true, ↓reduceIte, hdrop₂]
      rw [List.takeWhile_append_of_pos (fun x hx => decide_eq_true (hw₁'_prop x hx).1),
        List.map_append]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact (hw₁'_prop x hx).2
end Kraken
