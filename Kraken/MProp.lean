/-
The assertion type of the separation logic. `MProp w` is the type of
predicates over a `w`-bit byte memory, with `∗` the disjoint-split
conjunction of Kraken/Separation.lean and `emp` the empty memory. `bs.AtM a`
owns exactly the bytes `bs` at `a`, the assertion counterpart of the memory
`bs.At a`, and `v.AtM a` owns a word in the width of `v`.

`MProp`, `mk` and `get` are irreducible from the end of this file on: the
lemmas of this file are their whole interface.
-/
import Kraken.SeparationMem
import Std.Tactic.Do

open Std.WP
open Lean.Order

/-! ## The assertion type -/

/-- Assertions over a `w`-bit byte memory: the carrier of the separation
algebra. `mk` states a predicate on memories as an assertion, `get` reads
it back, and an assertion applies to a memory as a function. `MProp`, `mk`
and `get` are irreducible from the end of this file on: the lemmas of this
file are their whole interface. -/
def MProp (w : Nat) : Type := Mem w → Prop

namespace MProp

variable {w : Nat}

/-- The assertion that states `P`. -/
def mk (P : Mem w → Prop) : MProp w := P

/-- The predicate an assertion states. -/
def get (P : MProp w) : Mem w → Prop := P

instance : CoeFun (MProp w) (fun _ => Mem w → Prop) := ⟨get⟩

@[simp] theorem get_mk (P : Mem w → Prop) : (mk P).get = P := rfl

@[simp] theorem mk_get (P : MProp w) : mk P.get = P := rfl

@[ext] theorem ext {P Q : MProp w} (h : ∀ m, P.get m ↔ Q.get m) : P = Q :=
  funext fun m => propext (h m)

instance : CompleteLattice (MProp w) :=
  inferInstanceAs (CompleteLattice (Mem w → Prop))

/-- Entailment is pointwise implication of the predicates. -/
theorem le_def (P Q : MProp w) : (P ⊑ Q) ↔ ∀ m, P.get m → Q.get m := Iff.rfl

/-- Separating conjunction: the memory splits into disjoint halves. -/
def sep (P Q : MProp w) : MProp w := mk (Std.ExtHashMap.sep P.get Q.get)

@[inherit_doc sep] infixr:65 " ∗ " => MProp.sep

/-- The empty assertion: no memory is owned. -/
def emp : MProp w := mk Std.ExtHashMap.emp

/-- `P ∗ Q` holds at a memory that splits into disjoint halves, one for `P`
and one for `Q`. -/
theorem get_sep_apply_iff (P Q : MProp w) (m : Mem w) :
    (P ∗ Q).get m ↔ ∃ m₁ m₂, m₁.union m₂ = m ∧ m₁.inter m₂ = ∅ ∧ P.get m₁ ∧ Q.get m₂ :=
  Iff.rfl

/-- `emp` holds at the empty memory alone. -/
theorem get_emp_apply_iff (m : Mem w) : (emp : MProp w).get m ↔ m = ∅ := Iff.rfl

theorem sep_assoc (P Q R : MProp w) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) :=
  Std.ExtHashMap.sep_assoc P.get Q.get R.get

theorem sep_comm (P Q : MProp w) : P ∗ Q = Q ∗ P :=
  Std.ExtHashMap.sep_comm P.get Q.get

@[simp] theorem emp_sep (P : MProp w) : emp ∗ P = P := Std.ExtHashMap.emp_sep P.get

@[simp] theorem sep_emp (P : MProp w) : P ∗ emp = P := Std.ExtHashMap.sep_emp P.get

instance : Std.Associative (MProp.sep (w := w)) := ⟨sep_assoc⟩
instance : Std.Commutative (MProp.sep (w := w)) := ⟨sep_comm⟩
instance : Std.LawfulIdentity (MProp.sep (w := w)) emp where
  left_id := emp_sep
  right_id := sep_emp

/-- The generic sup on `MProp`, pointwise; from the lattice axioms alone. -/
theorem get_sup_apply_iff (s : MProp w → Prop) (m : Mem w) :
    (CompleteLattice.sup s : MProp w).get m ↔ ∃ P, s P ∧ P.get m := by
  constructor
  · exact fun hm => sup_le s (x := mk fun m => ∃ P, s P ∧ P.get m)
      (fun P hP m' hPm' => ⟨P, hP, hPm'⟩) m hm
  · rintro ⟨P, hP, hPm⟩
    exact le_sup (c := s) hP m hPm

/-- The meet on `MProp`, pointwise; from the lattice axioms alone. A memory
spec's precondition is a meet of its pure conjunct and its footprint, and this
reads both off the owned memory. -/
theorem get_meet_apply_iff (P Q : MProp w) (m : Mem w) : (P ⊓ Q).get m ↔ P.get m ∧ Q.get m := by
  constructor
  · exact fun h => ⟨meet_le_left P Q m h, meet_le_right P Q m h⟩
  · rintro ⟨hp, hq⟩
    have hR : mk (fun m' => m' = m ∧ P.get m ∧ Q.get m) ⊑ P ⊓ Q := by
      apply le_meet <;> intro m' h' <;> obtain ⟨rfl, _, _⟩ := h' <;> assumption
    exact hR m ⟨rfl, hp, hq⟩

/-- A pure assertion holds at a memory exactly when its proposition holds. -/
theorem get_ofProp_apply_iff (p : Prop) (m : Mem w) : (⌜p⌝ : MProp w).get m ↔ p := by
  constructor
  · exact fun h => ofProp_le p (mk fun _ => p) (fun hp _ _ => hp) m h
  · exact fun hp => le_ofProp (mk fun m' => m' = m) p hp m rfl

/-- `(F ∗ ·)` preserves suprema: the split existential commutes with the
join. Its upper adjoint is the magic wand, which the frame closure takes. -/
instance (F : MProp w) : PreservesSup (MProp.sep F) where
  map_sup s := by
    apply ext
    intro m
    rw [get_sep_apply_iff, get_sup_apply_iff (fun y => ∃ x, s x ∧ y = MProp.sep F x) m]
    constructor
    · rintro ⟨m₁, m₂, hu, hd, hF, hsup⟩
      obtain ⟨P, hP, hPm⟩ := (get_sup_apply_iff s m₂).mp hsup
      exact ⟨F ∗ P, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
    · rintro ⟨g, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
      exact ⟨m₁, m₂, hu, hd, hF, (get_sup_apply_iff s m₂).mpr ⟨P, hP, hPm⟩⟩

theorem sep_mono_right (P : MProp w) {Q Q' : MProp w} (h : Q ⊑ Q') : P ∗ Q ⊑ P ∗ Q' :=
  PreservesSup.map_mono (MProp.sep P) h

/-- The separating implication: `P -∗ Q` owns what, joined with a disjoint
`P`, yields `Q`. It is the upper adjoint of `(P ∗ ·)`, which `vcgen`
decomposes. -/
noncomputable abbrev wand (P Q : MProp w) : MProp w := PreservesSup.upperAdjoint (MProp.sep P) Q

@[inherit_doc wand] infixr:60 " -∗ " => MProp.wand

/-- `P -∗ Q` holds at `m` when every disjoint memory satisfying `P`, joined
with `m`, satisfies `Q`. -/
theorem get_wand_apply_iff (P Q : MProp w) (m : Mem w) :
    (P -∗ Q).get m ↔ ∀ m', m'.inter m = ∅ → P.get m' → Q.get (m'.union m) := by
  unfold wand PreservesSup.upperAdjoint
  rw [get_sup_apply_iff]
  constructor
  · rintro ⟨X, hX, hx⟩ m' hd hp
    exact (le_def _ _).mp hX _ ((get_sep_apply_iff _ _ _).mpr ⟨m', m, rfl, hd, hp, hx⟩)
  · intro h
    refine ⟨mk fun n => n = m, (le_def _ _).mpr fun n hn => ?_, by rw [get_mk]⟩
    obtain ⟨m₁, m₂, hu, hd, hp, hx⟩ := (get_sep_apply_iff _ _ _).mp hn
    rw [get_mk] at hx
    subst hx hu
    exact h m₁ hd hp

theorem wand_intro {P Q R : MProp w} (h : P ∗ Q ⊑ R) : Q ⊑ P -∗ R :=
  PreservesSup.le_upperAdjoint (MProp.sep P) h

theorem sep_wand_elim (P Q : MProp w) : P ∗ (P -∗ Q) ⊑ Q :=
  PreservesSup.upperAdjoint_le (MProp.sep P) Q

/-- An assertion entails `mk P` when every memory it holds at satisfies `P`. -/
theorem le_mk_of {X : MProp w} {P : Mem w → Prop} (h : ∀ m, X.get m → P m) : X ⊑ mk P :=
  (le_def _ _).mpr fun m hx => (get_mk P) ▸ h m hx

/-- A proposition that the right side of `F ∗ X` entails holds wherever
`F ∗ X` does. -/
theorem of_get_sep {F X : MProp w} {p : Prop} {m : Mem w} (h : (F ∗ X).get m) (hX : X ⊑ ⌜p⌝) : p :=
  have ⟨_, m₂, _, _, _, hx⟩ := (get_sep_apply_iff F X m).mp h
  (get_ofProp_apply_iff p m₂).mp ((le_def _ _).mp hX m₂ hx)

end MProp

/-! ## The atoms

`bs.AtM a` owns exactly the bytes `bs` at `a`, the assertion counterpart of
the memory `bs.At a`; `v.AtM a` owns a word, in the width of `v`. -/

/-- The bytes `bs` sit at `a`, and nothing else is owned. -/
def List.AtM {w : Nat} (bs : List UInt8) (a : BitVec w) : MProp w := MProp.mk (Eq (bs.At a))

/-- `bs.AtM a` states the memory `bs.At a` of the baseline. -/
theorem List.get_AtM {w : Nat} (bs : List UInt8) (a : BitVec w) : (bs.AtM a).get = Eq (bs.At a) :=
  rfl

/-- A baseline memory that splits into `bs.At a` and `R` satisfies `bs.AtM a`
next to the frame `R`. -/
theorem List.get_AtM_sep {w : Nat} {bs : List UInt8} {a : BitVec w} {R : _root_.Mem w → Prop}
    {m : _root_.Mem w} (h : m =⋆ Eq (bs.At a) ⋆ R) : (bs.AtM a ∗ MProp.mk R).get m :=
  h


/-- Reading `n` bytes at `a` from a memory that owns `bs` there, next to any
frame, yields `bs`. -/
theorem Mem.loadInt_eq_of_AtM {w : Nat} {bs : List UInt8} {a : BitVec w} {n : Nat} {F : MProp w}
    {m : Mem w} (h : (bs.AtM a ∗ F).get m) (hlen : bs.length = n) (hw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) :=
  Mem.loadInt_sep bs a n F.get m h hlen hw

/-- Storing `n` bytes of `v` at `a` into a memory that owns `bs` there
replaces them, next to any frame. -/
theorem Mem.get_AtM_sep_storeInt {w : Nat} {bs : List UInt8} {a : BitVec w} {n : Nat} {F : MProp w}
    {m : Mem w} (h : (bs.AtM a ∗ F).get m) (hlen : bs.length = n) (v : Int) :
    ((Int.toBytes n v).AtM a ∗ F).get (m.storeInt a n v) :=
  Mem.storeInt_sep a n bs F.get m ⟨h, hlen⟩ v

/-- The eight bytes of `v` sit at `a`. -/
abbrev UInt64.AtM {w : Nat} (v : UInt64) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- `v.AtM a` states the memory `v.At a` of the baseline. -/
theorem UInt64.get_AtM {w : Nat} (v : UInt64) (a : BitVec w) : (v.AtM a).get = Eq (v.At a) := rfl

/-- A baseline memory that splits into `v.At a` and `R` satisfies `v.AtM a`
next to the frame `R`. -/
theorem UInt64.get_AtM_sep {w : Nat} {v : UInt64} {a : BitVec w} {R : _root_.Mem w → Prop}
    {m : _root_.Mem w} (h : m =⋆ Eq (v.At a) ⋆ R) : (v.AtM a ∗ MProp.mk R).get m :=
  h

/-- The four bytes of `v` sit at `a`. -/
abbrev UInt32.AtM {w : Nat} (v : UInt32) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The two bytes of `v` sit at `a`. -/
abbrev UInt16.AtM {w : Nat} (v : UInt16) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The byte `v` sits at `a`. -/
abbrev UInt8.AtM {w : Nat} (v : UInt8) (a : BitVec w) : MProp w := v.toBytes.AtM a

attribute [irreducible] MProp MProp.mk MProp.get
