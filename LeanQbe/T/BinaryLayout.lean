module

public import Kraken.Layout

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Prove `Array.all (· > 0)` from the kernel-reducible `List.all (· > 0)` check. -/
theorem all_pos_of_toList {sizes : Array Nat}
    (h : sizes.toList.all (· > 0) = true) :
    sizes.all (· > 0) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hmem : sizes[i] ∈ sizes.toList := Array.getElem_mem_toList hi
  exact List.all_eq_true.mp h _ hmem

/-- Every entry produced by the binary size-table lookup is strictly positive. -/
theorem tableInstrSize_pos (sizes : Array Nat) (hpos : sizes.all (· > 0) = true)
    (i : Nat) : 0 < if h : i < sizes.size then sizes[i] else 4 := by
  split
  case isTrue h =>
    exact of_decide_eq_true (Array.all_eq_true.mp hpos i h)
  case isFalse =>
    omega

/-- Target-generic specification of a concrete binary layout table. -/
structure BinaryLayoutSpec where
  start : Int64
  sizes : Array Nat
  hpos : sizes.all (· > 0) = true

/-- Build a `Kraken.Layout` backed by a concrete per-directive byte-size array. -/
@[instance_reducible, expose] def tableLayout (Instr Const : Type) (start : Int64)
    (sizes : Array Nat) (hpos : sizes.all (· > 0) = true) :
    Kraken.Layout Instr Const where
  start := start
  instrSize idx := if h : idx < sizes.size then sizes[idx] else 4
  instrSize_pos := tableInstrSize_pos sizes hpos

/-- Convert a `BinaryLayoutSpec` to a `Kraken.Layout` for any ISA. -/
@[instance_reducible, expose] def BinaryLayoutSpec.toLayout (Instr Const : Type)
    (spec : BinaryLayoutSpec) : Kraken.Layout Instr Const :=
  tableLayout Instr Const spec.start spec.sizes spec.hpos

/-- Byte size contributed by one directive when instruction positions use `sz`. -/
@[expose] def tableDirSize {Instr Const : Type}
    (d : Kraken.Directive Instr Const) (sz : Nat) : Nat :=
  match d with
  | .instr _ => sz
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

/-- Linear-time accumulator for total assembled byte size over `sizes.toList`. -/
@[expose] def tableSumAux {Instr Const : Type} (acc : Nat)
    (ss : List Nat) (ds : List (Kraken.Directive Instr Const)) : Nat :=
  match ds with
  | [] => acc
  | d :: rest => tableSumAux (acc + tableDirSize d (ss.headD 4)) ss.tail rest

/-- Total byte size of `prog` under per-directive size table `sizes`. -/
@[expose] def tableProgSize {Instr Const : Type} (sizes : Array Nat)
    (prog : List (Kraken.Directive Instr Const)) : Nat :=
  tableSumAux 0 sizes.toList prog

/-- Kernel-reducible O(N) check that `prog` fits within 64-bit address space. -/
@[expose] def tableProgSmall {Instr Const : Type} (sizes : Array Nat)
    (prog : List (Kraken.Directive Instr Const)) : Bool :=
  decide (tableProgSize sizes prog < 2 ^ 64)

/-- Indexed reference form of `tableSumAux` used in `tableLayout_sizeBefore`. -/
@[expose] def tableIndexedSum {Instr Const : Type} (sizes : Array Nat) :
    Nat → List (Kraken.Directive Instr Const) → Nat
  | _, [] => 0
  | k, d :: ds =>
    tableDirSize d (if _ : k < sizes.size then sizes[k] else 4) +
      tableIndexedSum sizes (k + 1) ds

theorem tableSumAux_eq {Instr Const : Type} (sizes : Array Nat) (k acc : Nat)
    (ds : List (Kraken.Directive Instr Const)) :
    tableSumAux acc (sizes.toList.drop k) ds =
      acc + tableIndexedSum sizes k ds := by
  induction ds generalizing k acc with
  | nil =>
    simp [tableSumAux, tableIndexedSum]
  | cons d rest ih =>
    simp only [tableSumAux, tableIndexedSum]
    have hhead :
        (sizes.toList.drop k).headD 4 =
          if _ : k < sizes.size then sizes[k] else 4 := by
      by_cases hk : k < sizes.size
      · have hk' : k < sizes.toList.length := by simpa using hk
        simp [hk, List.drop_eq_getElem_cons hk']
      · have hk' : sizes.toList.length ≤ k := by
          have := Nat.not_lt.mp hk
          simpa using this
        simp [hk, List.drop_of_length_le hk']
    have htail : (sizes.toList.drop k).tail = sizes.toList.drop (k + 1) := by
      simp [List.tail_drop]
    rw [hhead, htail, ih]
    omega

theorem tableLayout_size {Instr Const : Type} (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (d : Kraken.Directive Instr Const) (idx : Nat) :
    (tableLayout Instr Const start sizes hpos).size d idx =
      tableDirSize d (if _ : idx < sizes.size then sizes[idx] else 4) := by
  cases d <;> rfl

private theorem map_mapIdx_eq {α β γ : Type} (f : Nat → α → β) (g : β → γ)
    (xs : List α) :
    (xs.mapIdx f).map g = xs.mapIdx (fun i x => g (f i x)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih =>
    simp [List.mapIdx_cons, ih]

private theorem mapIdx_tableDirSize_sum {Instr Const : Type} (sizes : Array Nat)
    (k : Nat) (ds : List (Kraken.Directive Instr Const)) :
    (ds.mapIdx (fun idx d =>
      tableDirSize d (if _ : k + idx < sizes.size then sizes[k + idx] else 4))).sum =
      tableIndexedSum sizes k ds := by
  induction ds generalizing k with
  | nil =>
    simp [tableIndexedSum]
  | cons d rest ih =>
    rw [List.mapIdx_cons, List.sum_cons, tableIndexedSum]
    have h0 : k + 0 = k := Nat.add_zero k
    simp only [h0]
    congr 1
    have hcongr :
        (fun i (x : Kraken.Directive Instr Const) =>
          tableDirSize x
            (if _ : k + (i + 1) < sizes.size then sizes[k + (i + 1)] else 4)) =
        (fun i x =>
          tableDirSize x
            (if _ : k + 1 + i < sizes.size then sizes[k + 1 + i] else 4)) := by
      funext i x
      have hidx : k + (i + 1) = k + 1 + i := by omega
      simp only [hidx]
    rw [hcongr]
    exact ih (k + 1)

theorem tableLayout_sizeBefore {Instr Const : Type} (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : List (Kraken.Directive Instr Const)) :
    ((tableLayout Instr Const start sizes hpos).apply prog).sizeBefore prog.length =
      tableProgSize sizes prog := by
  unfold Kraken.Executable.sizeBefore Kraken.Layout.apply
  dsimp only
  have hlen :
      (prog.mapIdx fun idx directive =>
        ({ directive := directive
           size := (tableLayout Instr Const start sizes hpos).size directive idx } :
            Kraken.Sized (Kraken.Directive Instr Const))).length =
        prog.length := by
    simp
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]
  rw [map_mapIdx_eq]
  have hfn :
      (fun idx (d : Kraken.Directive Instr Const) =>
        ({ directive := d
           size := (tableLayout Instr Const start sizes hpos).size d idx } :
            Kraken.Sized (Kraken.Directive Instr Const)).size) =
      (fun idx d =>
        tableDirSize d (if _ : 0 + idx < sizes.size then sizes[0 + idx] else 4)) := by
    funext idx d
    dsimp only
    rw [tableLayout_size, Nat.zero_add]
  rw [hfn, mapIdx_tableDirSize_sum]
  unfold tableProgSize
  have hsum := tableSumAux_eq sizes 0 0 prog
  simpa using hsum.symm

/-- Bridge from `tableProgSmall` to `Kraken.Host.ofLayout`'s `< 2 ^ 64` precondition. -/
theorem tableLayout_small {Instr Const : Type} (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : List (Kraken.Directive Instr Const))
    (hsmall : tableProgSmall sizes prog = true) :
    ((tableLayout Instr Const start sizes hpos).apply prog).sizeBefore prog.length <
      2 ^ 64 := by
  rw [tableLayout_sizeBefore]
  exact of_decide_eq_true hsmall

/-- Target-agnostic skeleton tag of a `Kraken.Directive` for elaborator alignment. -/
inductive DirTag where
  | instr
  | label (name : String)
  | byteArray (size : Nat)
  | word (bytes : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Extract label symbol name from a `Kraken.Directive`, matching `Program.definedLabels`. -/
@[expose] def dirLabel? {Instr Const : Type} : Kraken.Directive Instr Const → Option String
  | .label s => some s
  | _ => none

/-- Extract the `DirTag` skeleton of a single `Kraken.Directive`. -/
@[expose] def dirTag {Instr Const : Type} : Kraken.Directive Instr Const → DirTag
  | .instr _ => .instr
  | .label s => .label s
  | .byteArray arr => .byteArray arr.size
  | .word bytes _ => .word bytes

/-- Extract the directive skeleton list of a `Kraken.Program`. -/
@[expose] def progTags {Instr Const : Type} (prog : List (Kraken.Directive Instr Const)) :
    List DirTag :=
  prog.map dirTag

end LeanQbe.T

end
