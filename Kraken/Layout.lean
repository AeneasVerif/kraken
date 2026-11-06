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

theorem Executable.withAddresses_map_snd {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

/-- Total byte size of the executable. -/
def Executable.size {Instr : Type} (e : Executable Instr) : Nat :=
  (e.program.map (·.size)).sum

/-- An executable is well-formed if its total byte size fits in the 64-bit address space. -/
def Executable.WellFormed {Instr : Type} (e : Executable Instr) : Prop :=
  e.size < UInt64.size

instance {Instr : Type} (e : Executable Instr) : Decidable e.WellFormed :=
  inferInstanceAs (Decidable (e.size < UInt64.size))

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

private theorem add_ofNat_ne_self (a : Int64) {n : Nat} (hpos : 0 < n) (hlt : n < UInt64.size) :
    a + .ofNat n ≠ a := by
  grind

private theorem add_ofNat_add (a : Int64) (m n : Nat) :
    a + .ofNat m + .ofNat n = a + .ofNat (m + n) := by
  grind

/--
Given a well-formed program (whose total byte size is `< 2^64`), if dropping directives up to
address `a` and then dropping all directives at address `a` leaves `y :: ys`, then:
1. No earlier directive in the program has address `y.addr` (so dropping while `addr ≠ y.addr`
   from the start of `withAddresses` lands on `y :: ys`).
2. `y :: ys` is the `withAddresses` layout of the remaining directives starting at `y.addr`.
3. `y.addr` equals `a` plus the sum of sizes of the directives at `a` (`directivesAtAddress a`).
4. `y.addr` is at a positive byte offset `0 < offset ≤ total_size` from `startAddr`.
-/
private theorem withAddresses_dropWhile_WellFormed {Instr : Type}
    (program : List (Sized (Directive Instr))) (startAddr a : Int64)
    (hwf : (program.map (·.size)).sum < UInt64.size)
    {y : Addressable (Directive Instr)} {ys : List (Addressable (Directive Instr))}
    (h : ((Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ a)).dropWhile (·.addr = a) = y :: ys) :
    (Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ y.addr) = y :: ys ∧
    y :: ys = Executable.withAddresses {startAddr := y.addr, program := (y :: ys).map (·.toSized)} ∧
    (Executable.directivesAtAddress {startAddr, program} a).foldl (fun p d => p + .ofNat d.size) a = y.addr ∧
    ∃ offset, 0 < offset ∧ offset ≤ (program.map (·.size)).sum ∧ y.addr = startAddr + .ofNat offset := by
  induction program generalizing startAddr with
  | nil =>
    rw [Executable.withAddresses] at h
    contradiction
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons] at hwf
    by_cases ha : startAddr = a
    · subst ha
      rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses] at h
      simp only [List.dropWhile_cons, decide_true, ↓reduceIte] at h
      by_cases hc : c.size = 0
      · have ha0 : startAddr + .ofNat c.size = startAddr := by simp [hc]
        rw [ha0, ← Executable.withAddresses_dropWhile_start rest startAddr] at h
        obtain ⟨hdrop, hys_eq, hfold, offset, hpos, hle, hy⟩ := ih startAddr (by omega) h
        have hne : startAddr ≠ y.addr := by
          rw [hy]; exact Ne.symm (add_ofNat_ne_self startAddr hpos (by omega))
        refine ⟨?_, hys_eq, ?_, offset, hpos, by simp; omega, hy⟩
        · rw [Executable.withAddresses]
          simp only [List.dropWhile_cons, ne_eq, hne, not_false_eq_true, decide_true, ↓reduceIte, ha0]
          exact hdrop
        · dsimp [Executable.directivesAtAddress] at hfold ⊢
          rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses]
          simp only [List.takeWhile_cons, decide_true, ↓reduceIte, List.map_cons, List.foldl_cons, ha0]
          rw [← Executable.withAddresses_dropWhile_start rest startAddr]
          exact hfold
      · have hpos : 0 < c.size := Nat.pos_of_ne_zero hc
        have hne : startAddr + .ofNat c.size ≠ startAddr := add_ofNat_ne_self startAddr hpos (by omega)
        cases rest with
        | nil => rw [Executable.withAddresses] at h; contradiction
        | cons d rest' =>
          have h_rest : Executable.withAddresses {startAddr := startAddr + .ofNat c.size, program := d :: rest'} = y :: ys := by
            rw [Executable.withAddresses] at h
            simp only [List.dropWhile_cons, hne, decide_false, Bool.false_eq_true, ↓reduceIte] at h
            rw [Executable.withAddresses, h]
          rw [Executable.withAddresses] at h
          simp only [List.dropWhile_cons, hne, decide_false, Bool.false_eq_true, ↓reduceIte] at h
          injection h with hy hys
          have hy_addr : y.addr = startAddr + .ofNat c.size := by rw [← hy]
          refine ⟨?_, ?_, ?_, c.size, hpos, by simp, hy_addr⟩
          · rw [Executable.withAddresses]
            simp only [List.dropWhile_cons, ne_eq, hy_addr, hne.symm, not_false_eq_true, decide_true, ↓reduceIte]
            rw [Executable.withAddresses_dropWhile_start, h_rest]
          · rw [← h_rest, Executable.withAddresses_map_snd, hy_addr]
          · dsimp [Executable.directivesAtAddress]
            rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses]
            simp only [List.takeWhile_cons, decide_true, ↓reduceIte]
            rw [Executable.withAddresses]
            simp [hne, hy_addr]
    · rw [Executable.withAddresses] at h
      simp only [List.dropWhile_cons, ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte] at h
      obtain ⟨hdrop, hys_eq, hfold, offset', hpos', hle', hy⟩ := ih (startAddr + .ofNat c.size) (by omega) h
      rw [add_ofNat_add] at hy
      have hne : startAddr ≠ y.addr := by
        rw [hy]; exact Ne.symm (add_ofNat_ne_self startAddr (by omega) (by omega))
      refine ⟨?_, hys_eq, ?_, c.size + offset', by omega, by simp; omega, hy⟩
      · rw [Executable.withAddresses]
        simp only [List.dropWhile_cons, ne_eq, hne, not_false_eq_true, decide_true, ↓reduceIte]
        exact hdrop
      · dsimp [Executable.directivesAtAddress] at hfold ⊢
        rw [Executable.withAddresses]
        simp only [List.dropWhile_cons, ha, not_false_eq_true, decide_true, ↓reduceIte]
        exact hfold

/--
In a well-formed executable `e`, if the directives starting at `pc` correspond to suffix `ds`, then
either `ds` consists solely of the directives at `pc` (`e.directivesAtAddress pc`), or `ds` splits
into `e.directivesAtAddress pc ++ ds'` where `ds'` is a strictly shorter suffix starting at the
next address `pc'`.
-/
theorem Executable.WellFormed.step_split {Instr : Type}
    {e : Executable Instr} (hwf : e.WellFormed) {pc : Int64} {ds : List (Sized (Directive Instr))}
    (h_at : e.withAddresses.dropWhile (·.addr ≠ pc) = Executable.withAddresses {startAddr := pc, program := ds}) :
    let at_pc := e.directivesAtAddress pc
    let pc' := at_pc.foldl (fun p d => p + .ofNat d.size) pc
    ds = at_pc ∨
    ∃ ds', ds = at_pc ++ ds' ∧ ds'.length < ds.length ∧
      e.withAddresses.dropWhile (·.addr ≠ pc') = Executable.withAddresses {startAddr := pc', program := ds'} := by
  rcases e with ⟨startAddr, program⟩
  dsimp only
  have h_ds : ds = (Executable.directivesAtAddress {startAddr, program} pc) ++
      (((Executable.withAddresses {startAddr := pc, program := ds}).dropWhile (·.addr = pc)).map (·.toSized)) := by
    dsimp [Executable.directivesAtAddress]
    rw [h_at, ← List.map_append, List.takeWhile_append_dropWhile, Executable.withAddresses_map_snd]
  have h_drop : ((Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ pc)).dropWhile (·.addr = pc) =
      (Executable.withAddresses {startAddr := pc, program := ds}).dropWhile (·.addr = pc) := by
    rw [h_at]
  cases h_after : (Executable.withAddresses {startAddr := pc, program := ds}).dropWhile (·.addr = pc) with
  | nil =>
    left
    simpa [h_after] using h_ds
  | cons y ys =>
    right
    rw [h_after] at h_drop h_ds
    obtain ⟨h_next_from, h_ys_eq, h_fold, _⟩ := withAddresses_dropWhile_WellFormed program startAddr pc hwf h_drop
    refine ⟨(y :: ys).map (·.toSized), h_ds, ?_, ?_⟩
    · have h_len := congrArg List.length h_ds
      rw [List.length_append] at h_len
      have h_pos : 0 < (Executable.directivesAtAddress {startAddr, program} pc).length := by
        dsimp [Executable.directivesAtAddress]
        rw [h_at]
        cases ds with
        | nil => rw [Executable.withAddresses] at h_after; contradiction
        | cons c rest =>
          rw [Executable.withAddresses]
          simp
      omega
    · rw [h_fold, h_next_from, ← h_ys_eq]

theorem Executable.mem_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))

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
