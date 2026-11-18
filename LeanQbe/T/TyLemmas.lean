module

public import LeanQbe.T.Ty

/-!
# Lemmas about `LeanQbe.T.Ty`

* Vector size, mask, and leaf-predicate properties (`vec_size`, `hasFloat_vec`, `isFloatTree_vec`).
* Bit-view round-trip theorems (`ofBits_toBits`, `toBits_ofBits`, `bitcastVal_self`,
  `bitcastVal_bitcastVal`) and byte-width bounds (`size_le_eight_bytes`, `setWidth_bytes_size`).
* Tuple and context helper lemmas (`Tup.get_map`, `TRel.mono`, `envRel_toTup`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Vector and size lemmas -/

theorem Ty.vec_size (k : Nat) (t : Ty) : (Ty.vec k t).size = 2 ^ k * t.size := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Ty.size, ih, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.two_mul]

@[simp] theorem Ty.hasFloat_vec (k : Nat) (t : Ty) : (Ty.vec k t).hasFloat = t.hasFloat := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ty.hasFloat, ih]

@[simp] theorem Ty.isFloatTree_vec (k : Nat) (t : Ty) :
    (Ty.vec k t).isFloatTree = t.isFloatTree := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ty.isFloatTree, ih]

@[simp] theorem Ty.bswapOk_vec (k : Nat) (t : Ty) : (Ty.vec k t).bswapOk = t.bswapOk := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ty.bswapOk, ih]

theorem Ty.size_le_eight_bytes (t : Ty) : t.size ≤ 8 * t.bytes := by
  simp only [Ty.bytes]
  omega

theorem setWidth_bytes_size (t : Ty) (x : BitVec t.size) :
    (x.setWidth (8 * t.bytes)).setWidth t.size = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (Ty.size_le_eight_bytes t), BitVec.setWidth_eq]

/-! ## `toBits` / `ofBits` round-trips -/

theorem ofBits_toBits : ∀ (t : Ty) (v : Val t), ofBits t (toBits t v) = v
  | .bool, b => by cases b <;> rfl
  | .bits _, _ => rfl
  | .float _, _ => rfl
  | .pair a b, (x, y) => by
    simp only [toBits, ofBits]
    have h1 : ((toBits b y ++ toBits a x).cast (Nat.add_comm b.size a.size)).extractLsb' 0 a.size =
        toBits a x := by
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append,
        Nat.zero_add, hi, ↓reduceIte]
      exact BitVec.getLsbD_eq_getElem hi
    have h2 :
        ((toBits b y ++ toBits a x).cast (Nat.add_comm b.size a.size)).extractLsb' a.size b.size =
          toBits b y := by
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append]
      have hge : ¬ a.size + i < a.size := by omega
      simp only [hge, ↓reduceIte, Nat.add_sub_cancel_left]
      exact BitVec.getLsbD_eq_getElem hi
    rw [h1, h2, ofBits_toBits a x, ofBits_toBits b y]

theorem toBits_ofBits : ∀ (t : Ty) (x : BitVec t.size), toBits t (ofBits t x) = x
  | .bool, x => by
    ext i hi
    simp only [Ty.size] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [toBits, ofBits, ← BitVec.getLsbD_eq_getElem hi]
    cases x.getLsbD 0 <;> rfl
  | .bits _, _ => rfl
  | .float _, _ => rfl
  | .pair a b, x => by
    simp only [ofBits, toBits]
    rw [toBits_ofBits a, toBits_ofBits b]
    ext i hi
    simp only [Ty.size] at hi
    simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
    split <;> rename_i h
    · simp only [Nat.zero_add]
      exact BitVec.getLsbD_eq_getElem (by omega)
    · rw [BitVec.getLsbD_eq_getElem (by show a.size + (i - a.size) < (a.pair b).size; simp only [Ty.size]; omega)]
      congr 1; omega

theorem toBits_inj {t : Ty} {x y : Val t} (h : toBits t x = toBits t y) : x = y := by
  have h' := congrArg (ofBits t) h
  simpa [ofBits_toBits] using h'

theorem ofBits_inj {t : Ty} {x y : BitVec t.size} (h : ofBits t x = ofBits t y) : x = y := by
  have h' := congrArg (toBits t) h
  simpa [toBits_ofBits] using h'

@[simp] theorem bitcastVal_self (t : Ty) (x : Val t) : bitcastVal t t rfl x = x := by
  simp [bitcastVal, ofBits_toBits]

theorem bitcastVal_bitcastVal {t u w : Ty} (h1 : t.size = u.size) (h2 : u.size = w.size)
    (x : Val t) :
    bitcastVal u w h2 (bitcastVal t u h1 x) = bitcastVal t w (h1.trans h2) x := by
  simp only [bitcastVal, toBits_ofBits]
  rfl

/-! ## Tuple and context lemmas -/

theorem Tup.get_map {α : Type} {f g : α → Type} (h : ∀ a, f a → g a) :
    {as : List α} → {a : α} → (xs : Tup f as) → (i : Member a as) →
    (xs.map h).get i = h a (xs.get i)
  | _ :: _, _, _, .here => rfl
  | _ :: _, _, xs, .there i => Tup.get_map h xs.2 i

theorem TRel.mono {α : Type} {f g : α → Type} {R S : ∀ a, f a → g a → Prop}
    (h : ∀ a x y, R a x y → S a x y) :
    {as : List α} → {xs : Tup f as} → {ys : Tup g as} → TRel R xs ys → TRel S xs ys
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons hr hrs => .cons (h _ _ _ hr) (TRel.mono h hrs)

theorem envRel_toTup : {α : Type} → {f g : α → Type} → {as : List α} →
    (xs₁ : Tup f as) → (xs₂ : Tup g as) → EnvRel (Tup.zip xs₁ xs₂) xs₁ xs₂
  | _, _, _, [], _, _ => fun _ i => nomatch i
  | _, _, _, _ :: _, xs₁, xs₂ => fun a i => by
    cases i with
    | here => exact List.mem_cons_self
    | there i => exact List.mem_cons_of_mem _ (envRel_toTup xs₁.2 xs₂.2 a i)

end LeanQbe.T
