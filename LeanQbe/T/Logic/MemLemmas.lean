module

public import LeanQbe.T.Logic.Mem
import LeanQbe.T.OpsLemmas
public import Kraken.SeparationMem
import all Kraken.Separation
import all Kraken.Mem

/-!
# Separation-logic and memory framing lemmas for `LeanQbe.T`

* Separation glue: `sep_ex_l`, `sep_ex_r`, `sep_pure_l`, `sep_pure_r`, `sep_cast`,
  `eq_empty_eq_emp`, `ProofUtil.sep_ac`, `sep_mono`, `sep_mono_r`, `sep_mono2`, `sep_mono_mid`.
* Typed `cell` and `cell64` rules (`loadVal_cell`, `store_cell`, `loadVal_cell64`, `store_cell64`).
* Typed `array` and `array64` focusing/load/store rules (`array_focus`, `array_set`,
  `loadVal_array`, `store_array`, `array64_focus`, `array64_set`, `loadVal_array64`,
  `store_array64`).
* Generic `Int.toBytes` cell access (`loadVal_toBytes_bits`, `store_toBytes_bits`) and
  `bytes` / `Eq m` framing (`loadVal_frame`, `storeOk_frame`, `storeMem_frame`, `loadVal_bytes_at`).
* Satisfiability: `bytesOf` / `array_bytes`, `bytes64` / `array64_bytes`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## Separation glue -/

theorem sep_ex_l {α : Type} {P : α → Mem 64 → Prop} {R : Mem 64 → Prop} {m : Mem 64} :
    ((fun m => ∃ x, P x m) ⋆ R) m ↔ ∃ x, (P x ⋆ R) m := by
  constructor
  · rintro ⟨a, b, hu, hi, ⟨x, hp⟩, hr⟩; exact ⟨x, a, b, hu, hi, hp, hr⟩
  · rintro ⟨x, a, b, hu, hi, hp, hr⟩; exact ⟨a, b, hu, hi, ⟨x, hp⟩, hr⟩

theorem sep_ex_r {α : Type} {P : Mem 64 → Prop} {R : α → Mem 64 → Prop} {m : Mem 64} :
    (P ⋆ (fun m => ∃ x, R x m)) m ↔ ∃ x, (P ⋆ R x) m := by
  rw [sep_comm, sep_ex_l]
  exact ⟨fun ⟨x, h⟩ => ⟨x, by rwa [sep_comm]⟩, fun ⟨x, h⟩ => ⟨x, by rwa [sep_comm]⟩⟩

theorem sep_pure_l {φ : Prop} {P R : Mem 64 → Prop} {m : Mem 64} :
    ((fun m => φ ∧ P m) ⋆ R) m ↔ φ ∧ (P ⋆ R) m := by
  constructor
  · rintro ⟨a, b, hu, hi, ⟨h, hp⟩, hr⟩; exact ⟨h, a, b, hu, hi, hp, hr⟩
  · rintro ⟨h, a, b, hu, hi, hp, hr⟩; exact ⟨a, b, hu, hi, ⟨h, hp⟩, hr⟩

theorem sep_pure_r {φ : Prop} {P R : Mem 64 → Prop} {m : Mem 64} :
    (P ⋆ (fun m => φ ∧ R m)) m ↔ φ ∧ (P ⋆ R) m := by
  rw [sep_comm, sep_pure_l, sep_comm]

theorem sep_cast {P P' : Mem 64 → Prop} {m : Mem 64} (h : P m) (e : P = P') : P' m := e ▸ h

theorem eq_empty_eq_emp : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
  funext m; exact propext eq_comm

theorem sep_mono {P P' Q : Mem 64 → Prop} (h : ∀ x, P x → P' x) {M : Mem 64} :
    (P ⋆ Q) M → (P' ⋆ Q) M := by
  rintro ⟨a, b, hu, hd, ha, hb⟩
  exact ⟨a, b, hu, hd, h a ha, hb⟩

theorem sep_mono_r {P Q Q' : Mem 64 → Prop} (h : ∀ x, Q x → Q' x) {M : Mem 64} :
    (P ⋆ Q) M → (P ⋆ Q') M := by
  rintro ⟨a, b, hu, hd, ha, hb⟩
  exact ⟨a, b, hu, hd, ha, h b hb⟩

theorem sep_mono2 {P1 P1' P2 P2' : Mem 64 → Prop}
    (h1 : ∀ f, P1 f → P1' f) (h2 : ∀ f, P2 f → P2' f) :
    ∀ f, (P1 ⋆ P2) f → (P1' ⋆ P2') f :=
  fun _ h => sep_mono h1 (sep_mono_r h2 h)

theorem sep_mono_mid {A B B' C : Mem 64 → Prop} {m : Mem 64}
    (h : ∀ f, B f → B' f) (hm : (A ⋆ B ⋆ C) m) : (A ⋆ B' ⋆ C) m := by
  obtain ⟨f12, f3, hu1, hd1, ⟨f1, f2, hu2, hd2, hA, hB⟩, hC⟩ := hm
  exact ⟨f12, f3, hu1, hd1, ⟨f1, f2, hu2, hd2, hA, h f2 hB⟩, hC⟩

namespace ProofUtil
scoped macro "sep_ac" h:term : term => `(sep_cast $h (by ac_rfl))
end ProofUtil

/-! ## Helpers for `ofInt` / `setWidth` -/

private theorem ofInt_setWidth_eq (t : Ty) (i : Int) :
    BitVec.ofInt t.size i = (BitVec.ofInt (8 * t.bytes) i).setWidth t.size := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have hdvd : (2 ^ t.size : Int) ∣ (2 ^ (8 * t.bytes) : Int) := by
    have hle := Ty.size_le_eight_bytes t
    refine ⟨(2 ^ (8 * t.bytes - t.size) : Int), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' hle]
  have hmod : (i % (2 : Int) ^ (8 * t.bytes)) % (2 : Int) ^ t.size = i % (2 : Int) ^ t.size :=
    Int.emod_emod_of_dvd i hdvd
  have hnn : 0 ≤ i % (2 : Int) ^ (8 * t.bytes) :=
    Int.emod_nonneg i (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hnn2 : 0 ≤ i % (2 : Int) ^ t.size :=
    Int.emod_nonneg i (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hcast1 : ((i % (2 : Int) ^ t.size).toNat : Int) = i % (2 : Int) ^ t.size :=
    Int.toNat_of_nonneg hnn2
  have hcast2 : (((i % (2 : Int) ^ (8 * t.bytes)).toNat % 2 ^ t.size : Nat) : Int) =
      (i % (2 : Int) ^ (8 * t.bytes)) % (2 : Int) ^ t.size := by
    push_cast
    rw [Int.toNat_of_nonneg hnn]
  exact Int.ofNat.inj (by
    show ((i % (2 : Int) ^ t.size).toNat : Int) =
      (((i % (2 : Int) ^ (8 * t.bytes)).toNat % 2 ^ t.size : Nat) : Int)
    rw [hcast1, hcast2, hmod])

/-! ## Typed `cell` and `cell64` -/

theorem cell64_eq_cell (a v : BitVec 64) : cell64 a v = cell (t := i64) a v := rfl

theorem loadVal_cell {t : Ty} {a : BitVec 64} {v : Val t} {R : Mem 64 → Prop} {m : Mem 64}
    (hb : t.bytes ≤ 2 ^ 64) (h : (cell a v ⋆ R) m) : loadVal m t a = some v := by
  let bs := Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt
  have hloadInt : m.loadInt a t.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep _ a t.bytes R m h (Int.toBytes_length _ _) hb
  simp only [loadVal, hloadInt, Option.bind_some]
  have hbv : BitVec.ofInt (8 * t.bytes) (Int.ofBytes bs) = (toBits t v).setWidth (8 * t.bytes) :=
    BitVec.ofInt_ofBytes_toBytes (8 * t.bytes) t.bytes rfl _
  cases t with
  | bool =>
    cases v
    · have hi0 : Int.ofBytes bs = 0 := by dsimp only [bs, toBits, Ty.bytes, Ty.size]; decide
      simp [hi0]
    · have hi1 : Int.ofBytes bs = 1 := by dsimp only [bs, toBits, Ty.bytes, Ty.size]; decide
      simp [hi1]
  | bits _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.bits _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]
  | float _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.float _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]
  | pair _ _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.pair _ _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]

theorem store_cell {t : Ty} {a : BitVec 64} {v0 : Val t} (v : Val t)
    {R : Mem 64 → Prop} {m : Mem 64} (hb : t.bytes ≤ 2 ^ 64)
    (h : (cell a v0 ⋆ R) m) :
    storeOk m t a ∧ (cell a v ⋆ R) (storeMem m t a v) :=
  ⟨⟨_, Mem.loadInt_sep _ a t.bytes R m h (Int.toBytes_length _ _) hb⟩,
    Mem.storeInt_sep a t.bytes _ R m ⟨h, Int.toBytes_length _ _⟩ _⟩

theorem loadVal_cell64 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v ⋆ R) m) : loadVal m i64 a = some v :=
  loadVal_cell (t := i64) (by decide) h

theorem store_cell64 {a v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 a v0 ⋆ R) m) :
    storeOk m i64 a ∧ (cell64 a v ⋆ R) (storeMem m i64 a v) :=
  store_cell (t := i64) v (by decide) h

/-! ## Typed `array` and `array64` -/

@[simp] theorem array_nil {t : Ty} (a : BitVec 64) : array (t := t) a [] = emp := rfl
@[simp] theorem array_cons {t : Ty} (a : BitVec 64) (v : Val t) (vs : List (Val t)) :
    array a (v :: vs) = (cell a v ⋆ array (a + BitVec.ofNat 64 t.bytes) vs) := rfl

theorem array_append {t : Ty} (a : BitVec 64) (xs ys : List (Val t)) :
    array a (xs ++ ys) = (array a xs ⋆ array (a + BitVec.ofNat 64 (t.bytes * xs.length)) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, array_cons, array_cons, ih, ← sep_assoc, List.length_cons]
    congr 2; exact BitVec.eq_of_toNat_eq (by grind)

/-- Element `i` of a typed array, and the rest. -/
theorem array_focus {t : Ty} (a : BitVec 64) (xs : List (Val t)) {i : Nat} (hi : i < xs.length) :
    array a xs = (cell (a + BitVec.ofNat 64 (t.bytes * i)) xs[i] ⋆
      (array a (xs.take i) ⋆
        array (a + BitVec.ofNat 64 (t.bytes * i) + BitVec.ofNat 64 t.bytes)
          (xs.drop (i + 1)))) := by
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi]
  rw [array_append, array_cons, List.length_take_of_le (Nat.le_of_lt hi),
    ← sep_assoc, sep_comm (array a (xs.take i)), sep_assoc]

theorem array_set {t : Ty} (a : BitVec 64) (xs : List (Val t)) {i : Nat} (hi : i < xs.length)
    (v : Val t) :
    array a (xs.set i v) = (cell (a + BitVec.ofNat 64 (t.bytes * i)) v ⋆
      (array a (xs.take i) ⋆
        array (a + BitVec.ofNat 64 (t.bytes * i) + BitVec.ofNat 64 t.bytes)
          (xs.drop (i + 1)))) := by
  rw [array_focus a (xs.set i v) (i := i) (by simp [hi])]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem loadVal_array {t : Ty} {a : BitVec 64} {xs : List (Val t)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hb : t.bytes ≤ 2 ^ 64) (hi : i < xs.length)
    (h : (array a xs ⋆ R) m) :
    loadVal m t (a + BitVec.ofNat 64 (t.bytes * i)) = some xs[i] := by
  rw [array_focus a xs hi, sep_assoc] at h
  exact loadVal_cell hb h

theorem store_array {t : Ty} {a : BitVec 64} {xs : List (Val t)} {i : Nat} (v : Val t)
    {R : Mem 64 → Prop} {m : Mem 64} (hb : t.bytes ≤ 2 ^ 64) (hi : i < xs.length)
    (h : (array a xs ⋆ R) m) :
    storeOk m t (a + BitVec.ofNat 64 (t.bytes * i)) ∧
      (array a (xs.set i v) ⋆ R) (storeMem m t (a + BitVec.ofNat 64 (t.bytes * i)) v) := by
  rw [array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_cell v hb h
  exact ⟨h1, by rwa [array_set a xs hi, sep_assoc]⟩

@[simp] theorem array64_nil (a : BitVec 64) : array64 a [] = emp := rfl
@[simp] theorem array64_cons (a v : BitVec 64) (vs : List (BitVec 64)) :
    array64 a (v :: vs) = (cell64 a v ⋆ array64 (a + 8) vs) := rfl

theorem array64_eq_array (a : BitVec 64) (xs : List (BitVec 64)) :
    array64 a xs = array (t := i64) a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [array64_cons, array_cons, cell64_eq_cell, ih]
    rfl

theorem array64_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    array64 a (xs ++ ys) = (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  simp only [array64_eq_array]
  exact array_append (t := i64) a xs ys

theorem array64_focus (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    array64 a xs = (cell64 (a + BitVec.ofNat 64 (8 * i)) xs[i] ⋆
      (array64 a (xs.take i) ⋆ array64 (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  simp only [array64_eq_array, cell64_eq_cell]
  exact array_focus (t := i64) a xs hi

theorem array64_set (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length)
    (v : BitVec 64) :
    array64 a (xs.set i v) = (cell64 (a + BitVec.ofNat 64 (8 * i)) v ⋆
      (array64 a (xs.take i) ⋆ array64 (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  simp only [array64_eq_array, cell64_eq_cell]
  exact array_set (t := i64) a xs hi v

theorem loadVal_array64 {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [array64_focus a xs hi, sep_assoc] at h
  exact loadVal_cell64 h

theorem store_array64 {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length) (h : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array64 a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [array64_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_cell64 v h
  exact ⟨h1, by rwa [array64_set a xs hi, sep_assoc]⟩

/-! ## Any byte-aligned width: `Int.toBytes n x` cells -/

private theorem toInt_cast_bv {m n : Nat} (h : m = n) (v : BitVec m) :
    (v.cast h).toInt = v.toInt := by
  subst h; rfl

private theorem toBytes_ofInt_eq (b : Nat) (x : Int) :
    Int.toBytes b (BitVec.ofInt (8 * b) x).toInt = Int.toBytes b x := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := x)]
  congr 1
  simp only [Int.take, BitVec.toInt_eq_msb_cond]
  have hpos : (0 : Int) < 2 ^ (8 * b) := Int.pow_pos (by decide)
  have hx : ((BitVec.ofInt (8 * b) x).toNat : Int) = x % (2 ^ (8 * b) : Int) := by
    rw [BitVec.toNat_ofInt]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hpos))
  rw [hx]
  cases (BitVec.ofInt (8 * b) x).msb
  · simp
  · simp only [↓reduceIte]
    rw [show (2 : Int) ^ (8 * b) = ((2 ^ (8 * b) : Nat) : Int) by push_cast; rfl]
    rw [Int.sub_emod_right, Int.emod_emod]

private theorem ofInt_setWidth_le {m n : Nat} (h : m ≤ n) (z : Int) :
    (BitVec.ofInt n z).setWidth m = BitVec.ofInt m z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hdvd : (2 ^ m : Int) ∣ (2 ^ n : Int) := by
    refine ⟨(2 ^ (n - m) : Int), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' h]
  have hnn1 : 0 ≤ z % (2 : Int) ^ n := Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hnn2 : 0 ≤ z % (2 : Int) ^ m := Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
  apply Int.ofNat.inj
  show (((z % ↑(2 ^ n)).toNat % 2 ^ m : Nat) : Int) = (((z % ↑(2 ^ m)).toNat : Nat) : Int)
  rw [Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg hnn1,
    Int.toNat_of_nonneg hnn2, Int.emod_emod_of_dvd _ hdvd]

theorem loadVal_toBytes_bits {n : Nat} {a : BitVec 64} {x : Int}
    {R : Mem 64 → Prop} {m : Mem 64} (hb : (Ty.bits n).bytes ≤ 2 ^ 64)
    (h : (Eq ((Int.toBytes (Ty.bits n).bytes x).At a) ⋆ R) m) :
    loadVal m (.bits n) a = some (BitVec.ofInt n x) := by
  have hloadInt : m.loadInt a (Ty.bits n).bytes =
      some (Int.ofBytes (Int.toBytes (Ty.bits n).bytes x)) :=
    Mem.loadInt_sep _ a (Ty.bits n).bytes R m h (Int.toBytes_length _ _) hb
  simp only [loadVal, hloadInt, Option.bind_some, ofBits, Option.some.injEq]
  have hle : n ≤ 8 * (Ty.bits n).bytes := Ty.size_le_eight_bytes (.bits n)
  show BitVec.ofInt n (Int.ofBytes (Int.toBytes (Ty.bits n).bytes x)) = BitVec.ofInt n x
  rw [← ofInt_setWidth_le hle, ← toBytes_ofInt_eq,
    BitVec.ofInt_ofBytes_toBytes (8 * (Ty.bits n).bytes) (Ty.bits n).bytes rfl,
    ofInt_setWidth_le hle]

theorem store_toBytes_bits {n : Nat} {a : BitVec 64} {x : Int} (v : BitVec n)
    {R : Mem 64 → Prop} {m : Mem 64} (hn : n = 8 * (Ty.bits n).bytes)
    (hb : (Ty.bits n).bytes ≤ 2 ^ 64)
    (h : (Eq ((Int.toBytes (Ty.bits n).bytes x).At a) ⋆ R) m) :
    storeOk m (.bits n) a ∧
      (Eq ((Int.toBytes (Ty.bits n).bytes v.toNat).At a) ⋆ R) (storeMem m (.bits n) a v) := by
  refine ⟨⟨_, Mem.loadInt_sep _ a (Ty.bits n).bytes R m h (Int.toBytes_length _ _) hb⟩, ?_⟩
  have hst : storeMem m (.bits n) a v = m.storeInt a (Ty.bits n).bytes v.toInt := by
    simp only [storeMem, toBits]
    have hsw : v.setWidth (8 * (Ty.bits n).bytes) = v.cast hn :=
      BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth, ← hn])
    rw [hsw, toInt_cast_bv]
  have heq :
      Int.toBytes (Ty.bits n).bytes (v.toNat : Int) = Int.toBytes (Ty.bits n).bytes v.toInt := by
    rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := v.toInt)]
    congr 1
    simp only [Int.take, ← hn]
    have hmod : v.toInt % (2 ^ n : Int) = (v.toNat : Int) := by
      rw [BitVec.toInt_eq_msb_cond]
      have ha : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < (2 ^ n : Int) :=
        ⟨Int.natCast_nonneg _, by exact_mod_cast v.isLt⟩
      cases v.msb
      · simp [Int.emod_eq_of_lt ha.1 ha.2]
      · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]
        rw [Int.sub_emod_right, Int.emod_eq_of_lt ha.1 ha.2]
    rw [hmod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)]
  rw [hst, heq]
  exact Mem.storeInt_sep a (Ty.bits n).bytes _ R m ⟨h, Int.toBytes_length _ _⟩ v.toInt

private theorem toBytes_take_le : ∀ {b m : Nat} (v : Int),
    b ≤ m → (Int.toBytes m v).take b = Int.toBytes b v
  | 0, _, _, _ => by simp [Int.toBytes]
  | b + 1, m + 1, v, h => by
    simp only [Int.toBytes, List.take_succ_cons]
    congr 1
    exact toBytes_take_le (v / 256) (by omega)

/-- Reading a sub-word (`8/16/32/64` bits) from a 64-bit `cell64` yields `v64.setWidth n`. -/
theorem loadVal_bits_of_cell64 {n : Nat} {a v64 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (h : (cell64 a v64 ⋆ R) m) :
    loadVal m (.bits n) a = some (v64.setWidth n) := by
  have hb8 : (Ty.bits n).bytes ≤ 8 := by rcases hn with rfl | rfl | rfl | rfl <;> decide
  have hbw : (Ty.bits n).bytes ≤ 2 ^ 64 := Nat.le_trans hb8 (by decide)
  have hnle : n ≤ 64 := by rcases hn with rfl | rfl | rfl | rfl <;> decide
  let b := (Ty.bits n).bytes
  let bs := Int.toBytes 8 v64.toInt
  have hsplit : bs = Int.toBytes b v64.toInt ++ bs.drop b := by
    rw [← toBytes_take_le v64.toInt hb8, List.take_append_drop]
  have hlen : (Int.toBytes b v64.toInt).length + (bs.drop b).length ≤ 2 ^ 64 := by
    simp only [Int.toBytes_length, List.length_drop, bs]; omega
  have heq : cell64 a v64 =
      (Eq ((Int.toBytes b v64.toInt).At a) ⋆
        Eq ((bs.drop b).At (a + BitVec.ofNat 64 b))) := by
    change Eq (bs.At a) = _
    conv => lhs; rw [hsplit]
    have ha := Mem.At_append_sep (Int.toBytes b v64.toInt) (bs.drop b) a hlen
    simpa [Int.toBytes_length] using ha
  have hm' : (Eq ((Int.toBytes b v64.toInt).At a) ⋆
      (Eq ((bs.drop b).At (a + BitVec.ofNat 64 b)) ⋆ R)) m := by
    rw [heq] at h; exact sep_cast h (by ac_rfl)
  rw [loadVal_toBytes_bits hbw hm', ← ofInt_setWidth_le hnle, BitVec.ofInt_toInt]

/-! ## Framing `T.loadVal`, `T.storeOk`, `T.storeMem` over `(Eq m ⋆ F) M` -/

private theorem allSome_isSome {α : Type} :
    ∀ {l : List (Option α)} {bs : List α}, l.mapM id = some bs → ∀ x ∈ l, x.isSome
  | [], _, _, x, hx => by cases hx
  | _ :: l, bs, h, x, hx => by
    simp only [List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, rfl, bs', hl, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact allSome_isSome hl x hx

theorem Mem.mem_of_loadBytes {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a n = some bs) {i : Nat} (hi : i < n) : a + BitVec.ofNat w i ∈ m := by
  have := allSome_isSome h (m.get? (a + BitVec.ofNat w i))
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  rwa [ExtHashMap.get?_eq_getElem?, ← ExtHashMap.mem_iff_isSome_getElem?] at this

private theorem getElem?_union_left {m b : Mem 64} (hd : m.inter b = ∅) {k : BitVec 64}
    (hk : k ∈ m) : (m.union b)[k]? = m[k]? := by
  have hkb : k ∉ b := fun hkb =>
    (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd k)
      (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hk, hkb⟩)
  rw [ExtHashMap.union_eq, ExtHashMap.getElem?_union, ExtHashMap.getElem?_eq_none hkb]
  simp

private theorem loadBytes_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M)
    {a : BitVec 64} {n : Nat} {bs : List UInt8} (h : m.loadBytes a n = some bs) :
    M.loadBytes a n = some bs := by
  obtain ⟨m1, b, rfl, hd, rfl, -⟩ := hM
  rw [← h, Mem.loadBytes, Mem.loadBytes]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.get?_eq_getElem?,
    getElem?_union_left hd (Mem.mem_of_loadBytes h (List.mem_range.mp hi))]

private theorem loadInt_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M)
    {a : BitVec 64} {n : Nat} {i : Int} (h : m.loadInt a n = some i) :
    M.loadInt a n = some i := by
  rw [Mem.loadInt, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  rw [Mem.loadInt, loadBytes_frame hM hbs]
  rfl

theorem loadVal_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {t : Ty}
    {a : BitVec 64} {v : Val t} (h : loadVal m t a = some v) : loadVal M t a = some v := by
  rw [loadVal, Option.bind_eq_some_iff] at h
  obtain ⟨i, hi, hv⟩ := h
  rw [loadVal, loadInt_frame hM hi, Option.bind_some]
  exact hv

theorem storeOk_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {t : Ty}
    {a : BitVec 64} (h : storeOk m t a) : storeOk M t a := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, loadInt_frame hM hi⟩

theorem Mem.storeInt_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {a : BitVec 64}
    {n : Nat} (hmap : ∀ i < n, a + BitVec.ofNat 64 i ∈ m) (v : Int) :
    (Eq (m.storeInt a n v) ⋆ F) (M.storeInt a n v) := by
  obtain ⟨m1, b, rfl, hd, hm, hF⟩ := hM
  subst hm
  have hsub : ∀ k, k ∈ (Int.toBytes n v).At a → k ∈ m := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hk
    exact hmap i (by simpa [Int.toBytes_length] using hi)
  have hnb : ∀ k, k ∈ m → k ∉ b := fun k hk hkb =>
    (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd k)
      (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hk, hkb⟩)
  refine ⟨m.storeInt a n v, b, ?_, ?_, rfl, hF⟩
  · simp only [Mem.storeInt, Mem.storeBytes]
    apply ExtHashMap.ext_getElem?
    intro k
    simp only [ExtHashMap.union_eq, ExtHashMap.getElem?_union]
    grind
  · simp only [Mem.storeInt, Mem.storeBytes]
    apply ExtHashMap.eq_empty_iff_forall_not_mem.mpr
    intro k hk
    rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff, ExtHashMap.union_eq,
      ExtHashMap.mem_union_iff] at hk
    grind

theorem storeMem_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {t : Ty}
    {a : BitVec 64} (h : storeOk m t a) (v : Val t) :
    (Eq (storeMem m t a v) ⋆ F) (storeMem M t a v) := by
  obtain ⟨i, hi⟩ := h
  rw [Mem.loadInt, Option.map_eq_some_iff] at hi
  obtain ⟨bs, hbs, -⟩ := hi
  have hmap := fun j (hj : j < t.bytes) => Mem.mem_of_loadBytes hbs hj
  exact Mem.storeInt_frame hM hmap _

/-! ## Satisfiability (`bytes64`, `array64_bytes`, `bytesOf`, `array_bytes`) -/

/-- The bytes of a list of 64-bit words, 8 per word, little-endian. -/
@[expose] def bytes64 (xs : List (BitVec 64)) : List UInt8 :=
  xs.flatMap fun v => Int.toBytes 8 v.toInt

theorem bytes64_length (xs : List (BitVec 64)) : (bytes64 xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [bytes64, List.flatMap_cons, List.length_append, Int.toBytes_length] at ih ⊢
    rw [ih, List.length_cons]; omega

/-- Every 64-bit array that fits in the address space is satisfied by its bytes. -/
theorem array64_bytes (a : BitVec 64) (xs : List (BitVec 64)) (h : 8 * xs.length ≤ 2 ^ 64) :
    array64 a xs ((bytes64 xs).At a) := by
  induction xs generalizing a with
  | nil =>
    show _ = ∅
    apply ExtHashMap.ext_getElem?; intro k
    simp [bytes64, List.At]
  | cons x xs ih =>
    have hl : (Int.toBytes 8 x.toInt).length + (bytes64 xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytes64_length]; simp at h; omega
    have : bytes64 (x :: xs) = Int.toBytes 8 x.toInt ++ bytes64 xs := rfl
    have hd := List.disjoint_At_append _ _ a hl
    rw [array64_cons, this, List.At_append _ _ _ hl]
    rw [Int.toBytes_length] at hd ⊢
    exact ⟨_, _, rfl, hd, rfl, ih _ (by simp at h; omega)⟩

/-- The bytes of a list of typed values, `t.bytes` per element, little-endian. -/
@[expose] def bytesOf {t : Ty} (xs : List (Val t)) : List UInt8 :=
  xs.flatMap fun v => Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt

theorem bytesOf_length {t : Ty} (xs : List (Val t)) :
    (bytesOf xs).length = t.bytes * xs.length := by
  induction xs with
  | nil => simp [bytesOf]
  | cons x xs ih =>
    simp only [bytesOf, List.flatMap_cons, List.length_append, Int.toBytes_length] at ih ⊢
    rw [ih, List.length_cons, Nat.mul_succ]; omega

/-- Every typed array that fits in the address space is satisfied by its bytes. -/
theorem array_bytes {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (h : t.bytes * xs.length ≤ 2 ^ 64) :
    array a xs ((bytesOf xs).At a) := by
  induction xs generalizing a with
  | nil =>
    show _ = ∅
    apply ExtHashMap.ext_getElem?; intro k
    simp [bytesOf, List.At]
  | cons x xs ih =>
    have hmul : t.bytes * xs.length + t.bytes ≤ 2 ^ 64 := by
      rw [List.length_cons, Nat.mul_succ] at h; exact h
    have hl : (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).length +
        (bytesOf xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytesOf_length]; omega
    have : bytesOf (x :: xs) =
        Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt ++ bytesOf xs := rfl
    have hd := List.disjoint_At_append _ _ a hl
    rw [array_cons, this, List.At_append _ _ _ hl]
    rw [Int.toBytes_length] at hd ⊢
    exact ⟨_, _, rfl, hd, rfl, ih _ (by omega)⟩

/-- Converse of `array_bytes`: any heap satisfying `array a xs` equals `(bytesOf xs).At a`. -/
theorem array_eq_bytesOf {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (h : t.bytes * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array a xs m) :
    m = (bytesOf xs).At a := by
  induction xs generalizing a m with
  | nil =>
    simp only [array_nil, bytesOf, List.flatMap_nil] at hm ⊢
    have hm0 : m = ∅ := hm; subst hm0
    apply ExtHashMap.ext_getElem?; intro k; simp [List.At]
  | cons x xs ih =>
    rw [array_cons] at hm
    obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm
    have h1' : m1 = (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).At a :=
      h1.symm
    have h2' : m2 = (bytesOf xs).At (a + BitVec.ofNat 64 t.bytes) :=
      ih _ (by simp only [List.length_cons, Nat.mul_succ] at h; omega) h2
    have hl : (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).length +
        (bytesOf xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytesOf_length]
      simp only [List.length_cons, Nat.mul_succ] at h; omega
    have hat := List.At_append
      (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt) (bytesOf xs) a hl
    rw [Int.toBytes_length] at hat
    rw [h1', h2', ← hat]
    rfl

private theorem mapM_id_map_some {α : Type} :
    ∀ xs : List α, (xs.map some).mapM id = some xs
  | [] => rfl
  | x :: xs => by simp [mapM_id_map_some xs]

/-- Reading `bs.length` bytes at `a` from a heap containing `Eq (bs.At a) ⋆ R` returns `bs`. -/
theorem loadBytes_sep_At {a : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : bs.length ≤ 2 ^ 64)
    (hm : (Eq (bs.At a) ⋆ R) m) :
    m.loadBytes a bs.length = some bs := by
  obtain ⟨m1, m2, hm_eq, hd, rfl, _⟩ := hm
  subst hm_eq
  unfold Mem.loadBytes
  have hmap : (List.range bs.length).map
      (fun i => (bs.At a ∪ m2).get? (a + .ofNat 64 i)) = bs.map some := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.length_map, List.length_range] at hi1
    simp only [List.getElem_map, List.getElem_range]
    have hmem : a + BitVec.ofNat 64 i ∈ bs.At a :=
      (mem_At_iff bs a _).mpr ⟨i, hi1, rfl⟩
    have hnot : a + BitVec.ofNat 64 i ∉ m2 := fun h2 =>
      (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd _)
        (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hmem, h2⟩)
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.getElem?_union,
      ExtHashMap.getElem?_eq_none hnot, Option.none_or, ← ExtHashMap.get?_eq_getElem?]
    rw [get?_At_idx bs a i (Nat.lt_of_lt_of_le hi1 hlen) hlen, List.getElem?_eq_getElem hi1]
  rw [← ExtHashMap.union_eq] at hmap
  rw [hmap, mapM_id_map_some]

/-! ## Cell bytes and post-`t_wp_unfold` step helpers -/

theorem cell_bytes {t : Ty} (a : BitVec 64) (v : Val t) :
    cell a v ((Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt).At a) := rfl

theorem cell64_bytes (a v : BitVec 64) :
    cell64 a v ((Int.toBytes 8 v.toInt).At a) := rfl

theorem load_cell_step {m : Mem 64} {p : BitVec 64} {t : Ty} {Q : Val t → Prop}
    (a : BitVec 64) {v : Val t} {R : Mem 64 → Prop} (hb : t.bytes ≤ 2 ^ 64)
    (hm : (cell a v ⋆ R) m) (heq : p = a := by rfl) (hk : Q v) :
    ∃ x, loadVal m t p = some x ∧ Q x :=
  ⟨v, heq ▸ loadVal_cell hb hm, hk⟩

theorem store_cell_step {m : Mem 64} {p : BitVec 64} {t : Ty}
    (a : BitVec 64) {v0 : Val t} (v : Val t) {R : Mem 64 → Prop} {Q : Mem 64 → Prop}
    (hb : t.bytes ≤ 2 ^ 64) (hm : (cell a v0 ⋆ R) m) (heq : p = a := by rfl)
    (hk : ∀ m', (cell a v ⋆ R) m' → Q m') :
    storeOk m t p ∧ Q (storeMem m t p v) := by
  obtain ⟨h1, h2⟩ := store_cell v hb hm
  rw [heq]
  exact ⟨h1, hk _ h2⟩

theorem load_cell64_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 64 → Prop}
    (a : BitVec 64) {v : BitVec 64} {R : Mem 64 → Prop}
    (hm : (cell64 a v ⋆ R) m) (heq : p = a := by rfl) (hk : Q v) :
    ∃ x, loadVal m i64 p = some x ∧ Q x :=
  ⟨v, heq ▸ loadVal_cell64 hm, hk⟩

theorem store_cell64_step {m : Mem 64} {p : BitVec 64}
    (a : BitVec 64) {v0 : BitVec 64} (v : BitVec 64) {R : Mem 64 → Prop} {Q : Mem 64 → Prop}
    (hm : (cell64 a v0 ⋆ R) m) (heq : p = a := by rfl)
    (hk : ∀ m', (cell64 a v ⋆ R) m' → Q m') :
    storeOk m i64 p ∧ Q (storeMem m i64 p v) := by
  obtain ⟨h1, h2⟩ := store_cell64 v hm
  rw [heq]
  exact ⟨h1, hk _ h2⟩

theorem load_array_step {m : Mem 64} {p : BitVec 64} {t : Ty} {Q : Val t → Prop}
    (a : BitVec 64) (i : Nat) {xs : List (Val t)} {R : Mem 64 → Prop}
    (hb : t.bytes ≤ 2 ^ 64) (hi : i < xs.length) (hm : (array a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (t.bytes * i) := by rfl) (hk : Q xs[i]) :
    ∃ x, loadVal m t p = some x ∧ Q x :=
  ⟨xs[i], heq ▸ loadVal_array hb hi hm, hk⟩

theorem store_array_step {m : Mem 64} {p : BitVec 64} {t : Ty}
    (a : BitVec 64) (i : Nat) {xs : List (Val t)} (v : Val t) {R : Mem 64 → Prop}
    {Q : Mem 64 → Prop} (hb : t.bytes ≤ 2 ^ 64) (hi : i < xs.length)
    (hm : (array a xs ⋆ R) m) (heq : p = a + BitVec.ofNat 64 (t.bytes * i) := by rfl)
    (hk : ∀ m', (array a (xs.set i v) ⋆ R) m' → Q m') :
    storeOk m t p ∧ Q (storeMem m t p v) := by
  obtain ⟨h1, h2⟩ := store_array v hb hi hm
  rw [heq]
  exact ⟨h1, hk _ h2⟩

theorem load_array64_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 64 → Prop}
    (a : BitVec 64) (i : Nat) {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hi : i < xs.length) (hm : (array64 a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (8 * i) := by rfl) (hk : Q xs[i]) :
    ∃ x, loadVal m i64 p = some x ∧ Q x :=
  ⟨xs[i], heq ▸ loadVal_array64 hi hm, hk⟩

theorem store_array64_step {m : Mem 64} {p : BitVec 64}
    (a : BitVec 64) (i : Nat) {xs : List (BitVec 64)} (v : BitVec 64) {R : Mem 64 → Prop}
    {Q : Mem 64 → Prop} (hi : i < xs.length) (hm : (array64 a xs ⋆ R) m)
    (heq : p = a + BitVec.ofNat 64 (8 * i) := by rfl)
    (hk : ∀ m', (array64 a (xs.set i v) ⋆ R) m' → Q m') :
    storeOk m i64 p ∧ Q (storeMem m i64 p v) := by
  obtain ⟨h1, h2⟩ := store_array64 v hi hm
  rw [heq]
  exact ⟨h1, hk _ h2⟩

private theorem mapM_id_length {α : Type} :
    ∀ {xs : List (Option α)} {bs : List α}, xs.mapM id = some bs → bs.length = xs.length
  | [], _, h => by simp at h; subst h; rfl
  | x :: xs, bs, h => by
    simp only [List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, -, bs', h', rfl⟩ := h
    simp [mapM_id_length h']

private theorem mapM_id_append {α : Type} :
    ∀ {xs ys : List (Option α)} {bs : List α}, (xs ++ ys).mapM id = some bs →
      ∃ bs1 bs2, xs.mapM id = some bs1 ∧ ys.mapM id = some bs2 ∧ bs = bs1 ++ bs2
  | [], ys, bs, h => ⟨[], bs, rfl, h, rfl⟩
  | x :: xs, ys, bs, h => by
    simp only [List.cons_append, List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hx, bs', h', rfl⟩ := h
    obtain ⟨bs1, bs2, h1, h2, rfl⟩ := mapM_id_append h'
    exact ⟨b :: bs1, bs2, by simp [hx, h1], h2, rfl⟩

private theorem loadBytes_take {m : Mem 64} {a : BitVec 64} {k n : Nat} {bs : List UInt8}
    (hk : k ≤ n) (h : m.loadBytes a n = some bs) : m.loadBytes a k = some (bs.take k) := by
  unfold Mem.loadBytes at h ⊢
  rw [show n = k + (n - k) by omega, List.range_add, List.map_append] at h
  obtain ⟨bs1, bs2, h1, _, rfl⟩ := mapM_id_append h
  have hlen : bs1.length = k := (mapM_id_length h1).trans (by simp)
  rw [List.take_left' hlen]
  exact h1

private theorem ofBytes_take_mod : ∀ (k : Nat) (bs : List UInt8),
    Int.ofBytes bs % (2 : Int) ^ (8 * k) = Int.ofBytes (bs.take k) % (2 : Int) ^ (8 * k)
  | 0, _ => by simp
  | k + 1, [] => by simp
  | k + 1, b :: bs => by
    simp only [List.take_succ_cons, Int.ofBytes_cons]
    have hpow : (2 : Int) ^ (8 * (k + 1)) = (2 : Int) ^ (8 * k) * 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Int.pow_add]; rfl
    rw [hpow, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd : (2 : Int) ^ (8 * k) ∣ Int.ofBytes bs - Int.ofBytes (bs.take k) :=
      Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (ofBytes_take_mod k bs))
    obtain ⟨q, hq⟩ := hdvd
    have hsub : Int.ofBytes bs * 256 + ↑b.toNat - (Int.ofBytes (bs.take k) * 256 + ↑b.toNat) =
        ((2 : Int) ^ (8 * k) * 256) * q := by
      calc Int.ofBytes bs * 256 + ↑b.toNat - (Int.ofBytes (bs.take k) * 256 + ↑b.toNat)
          = (Int.ofBytes bs - Int.ofBytes (bs.take k)) * 256 := by omega
        _ = ((2 : Int) ^ (8 * k) * q) * 256 := by rw [hq]
        _ = ((2 : Int) ^ (8 * k) * 256) * q := Int.mul_right_comm _ q 256
    rw [hsub]
    exact Int.mul_emod_right _ _

/-- Truncating an `8/16/32/64`-bit load result to `8/16/32` bits equals loading at the narrower
bit width from the same memory and address. -/
theorem loadVal_bits_truncate {M : Mem 64} {a : BitVec 64} {m n : Nat} {vm : BitVec m}
    (hm : m = 16 ∨ m = 32 ∨ m = 64) (hn : n = 8 ∨ n = 16 ∨ n = 32) (hnm : n < m)
    (hl : loadVal M (.bits m) a = some vm) :
    loadVal M (.bits n) a = some (vm.truncate n) := by
  have hm_eq : 8 * (Ty.bits m).bytes = m := by rcases hm with rfl | rfl | rfl <;> rfl
  have hn_eq : 8 * (Ty.bits n).bytes = n := by rcases hn with rfl | rfl | rfl <;> rfl
  have hbnm : (Ty.bits n).bytes ≤ (Ty.bits m).bytes := by
    rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
      first | exact absurd hnm (by decide) | decide
  simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    ofBits, Option.some.injEq] at hl ⊢
  obtain ⟨z, ⟨bs, hbs, rfl⟩, rfl⟩ := hl
  refine ⟨Int.ofBytes (bs.take (Ty.bits n).bytes),
    ⟨bs.take (Ty.bits n).bytes, loadBytes_take hbnm hbs, rfl⟩, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hle : n ≤ m := Nat.le_of_lt hnm
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hdvd : (2 ^ n : Int) ∣ (2 ^ m : Int) := by
    refine ⟨(2 ^ (m - n) : Int), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' hle]
  have hnn1 : 0 ≤ Int.ofBytes bs % (2 : Int) ^ m :=
    Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hnn2 : 0 ≤ Int.ofBytes (bs.take (Ty.bits n).bytes) % (2 : Int) ^ n :=
    Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
  apply Int.ofNat.inj
  show (((Int.ofBytes (bs.take (Ty.bits n).bytes) % ↑(2 ^ n)).toNat : Nat) : Int) =
    (((Int.ofBytes bs % ↑(2 ^ m)).toNat % 2 ^ n : Nat) : Int)
  rw [Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg hnn1,
    Int.toNat_of_nonneg hnn2, Int.emod_emod_of_dvd _ hdvd]
  have hpow : (2 : Int) ^ n = (2 : Int) ^ (8 * (Ty.bits n).bytes) := by rw [hn_eq]
  rw [hpow]
  exact (ofBytes_take_mod (Ty.bits n).bytes bs).symm

end LeanQbe.T
