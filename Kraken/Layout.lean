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
  | align (alignment : Nat) (fill : Nat)
  | nopalign (alignment : Nat)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr := List (Directive Instr)

structure Executable (Instr : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr))

class Layout (Instr : Type) where
  start : Int64
  instrSize : Nat → {n : Nat // 0 < n} -- size depends on position due to alignment, jump-distance bit length, etc
  alignSize : Nat → Nat

variable {Instr : Type}

def Layout.size (l : Layout Instr) : Directive Instr → Nat → Nat
  | .instr _, i => l.instrSize i
  | .label _, _ => 0
  | .byteArray b, _ => b.size
  | .align .., i | .nopalign _, i => l.alignSize i

def Layout.apply (l : Layout Instr) (prog : Program Instr) : Executable Instr :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size directive i})}

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
  go e.startAddr e.program
where go (startAddr : Int64) : List (Sized (Directive Instr)) → List (Addressable (Directive Instr))
  | [] => []
  | instr :: program => {instr with addr := startAddr} :: go (startAddr + .ofNat instr.size) program

@[simp] theorem Executable.withAddresses_nil {Instr : Type} (a : Int64) :
    Executable.withAddresses (Instr := Instr) ⟨a, []⟩ = [] := rfl

@[simp] theorem Executable.withAddresses_cons {Instr : Type} (a : Int64) (c : Sized (Directive Instr))
    (cs : List (Sized (Directive Instr))) :
    Executable.withAddresses ⟨a, c :: cs⟩ =
      {c with addr := a} :: Executable.withAddresses ⟨a + .ofNat c.size, cs⟩ := rfl

def Executable.directivesAtAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  (e.withAddresses.filter (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> simp_all

theorem Executable.withAddresses_dropWhile_start {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> simp

theorem Executable.directivesFromStart {Instr : Type} [layout : Layout Instr] (prog : Program Instr) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size directive i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

theorem Executable.mem_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem (List.mem_filter.mp hx).1

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
  | [], a, k => by simp
  | c :: program, a, 0 => by simp
  | c :: program, a, k + 1 => by
    simp only [withAddresses_cons, List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq {Instr : Type} (e : Executable Instr) (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k


theorem Executable.directivesAtAddress_addrOf {Instr : Type} (e : Executable Instr)
    (hinj : ∀ j k, e.addrOf j = e.addrOf k → e.sizeBefore j = e.sizeBefore k)
    {k : Nat} {c : Sized (Directive Instr)} (hc : e.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Sized (Directive Instr)), e.directivesAtAddress (e.addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 := by
  have hat : ∀ j x, e.withAddresses[j]? = some x → x.addr = e.addrOf j ∧ e.program[j]? = some x.toSized := by
    grind [Executable.getElem?_withAddresses_eq]
  obtain ⟨hklt, hkx⟩ := List.getElem?_eq_some_iff.mp
    (by simp [Executable.getElem?_withAddresses_eq, hc] : e.withAddresses[k]? = some {c with addr := e.addrOf k})
  refine ⟨((e.withAddresses.take k).filter (·.addr = e.addrOf k)).map (·.toSized), ?_, ?_⟩
  · have hdrop : (e.withAddresses.drop (k + 1)).filter (·.addr = e.addrOf k) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx hxa => by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
        have := hinj _ _ ((hat _ _ (List.getElem?_drop .. ▸ hi)).1.symm.trans (of_decide_eq_true hxa))
        have := e.sizeBefore_mono (Nat.le_add_right (k + 1) i)
        have := e.sizeBefore_succ hc
        omega
    unfold Executable.directivesAtAddress
    conv => lhs; rw [← List.take_append_drop k e.withAddresses, List.drop_eq_getElem_cons hklt, hkx]
    simp [hdrop]
  · intro c' hc'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hxt, hxa⟩ := List.mem_filter.mp hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxt
    obtain ⟨hilt, hi⟩ : i + 1 ≤ k ∧ e.withAddresses[i]? = some x := by grind
    obtain ⟨ha, hp⟩ := hat _ _ hi
    have := hinj _ _ (ha.symm.trans (of_decide_eq_true hxa))
    have := e.sizeBefore_succ hp
    have := e.sizeBefore_mono hilt
    omega

theorem Executable.exists_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) :
    ∃ k, e.program[k]? = some c ∧ e.addrOf k = a := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨k, _⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hx).1
  grind [Executable.getElem?_withAddresses_eq]

theorem Executable.sizeBefore_eq_of_addrOf_eq {Instr : Type} (e : Executable Instr)
    (hfit : (e.program.map (·.size)).sum < 2 ^ 64) {j k : Nat} (h : e.addrOf j = e.addrOf k) :
    e.sizeBefore j = e.sizeBefore k := by
  have hle : ∀ n, e.sizeBefore n ≤ (e.program.map (·.size)).sum := fun n => by
    grind [Executable.sizeBefore, List.take_append_drop]
  have := hle j
  have := hle k
  have h' := congrArg Int64.toBitVec h
  simp only [Executable.addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat_grind] at h'
  bv_omega

end Kraken
