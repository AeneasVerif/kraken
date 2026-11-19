module

public import LeanQbe.T.Logic.Ops

/-!
# Vector lane kit for `Ty.vec k t` (`T4`)

* `setLane`, `splatV`, `ofLaneFn`, `maskLane`, and extensionality `vec_ext`.
* `lane` / `setLane` / `splatV` identities (`lane_setLane`, `lane_splatV`, `setLane_lane`).
* Leaf-wise lifting lane lemmas: `lane_lift1`, `lane_lift2`, `lane_lift3`, plus **`lane_liftCmp`**
  and **`lane_blendV`** (from `T1` review `#18` #7) and bitvector-leaf specializations.
* Vector opcode lane specs (`vpaddd`/`add`, `vpternlogd`/`ternlog`, `vprord`/`rotr`, `vpsrld`/`lshr`,
  `rotl`, `shl`, `ashr`, `xor`, `and`, `or`, `not`, `cmp`, `blend`).
* Generic `Lanewise1`, `Lanewise2`, `Lanewise3`, `Lanewise4`, and arity-generic `LanewiseX`
  predicates by induction on `k`, with equivalences to `∀ i < 2 ^ k, ...` and transfer lemmas.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Type-level vector lemmas and lane constructors -/

theorem Ty.vec_mask (k : Nat) (t : Ty) : (Ty.vec k t).mask = Ty.vec k t.mask := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ty.vec, Ty.mask, ih]

/-- Update lane `i` (0-indexed from the low end) of a balanced `2^k`-lane vector. -/
def setLane : (k : Nat) → {t : Ty} → Val (Ty.vec k t) → Nat → Val t → Val (Ty.vec k t)
  | 0, _, _, _, v => v
  | k + 1, _, x, i, v =>
    if i < 2 ^ k then (setLane k x.1 i v, x.2) else (x.1, setLane k x.2 (i - 2 ^ k) v)

/-- Broadcast a scalar leaf across all `2^k` lanes. -/
def splatV : (k : Nat) → {t : Ty} → Val t → Val (Ty.vec k t)
  | 0, _, v => v
  | k + 1, _, v => (splatV k v, splatV k v)

/-- Construct a `2^k`-lane vector from a lane function `f`. -/
def ofLaneFn : (k : Nat) → {t : Ty} → (Nat → Val t) → Val (Ty.vec k t)
  | 0, _, f => f 0
  | k + 1, _, f => (ofLaneFn k f, ofLaneFn k fun i => f (i + 2 ^ k))

/-- Lane `i` of a comparison mask tree `Val (Ty.vec k t).mask` (cast-free). -/
def maskLane (t : Ty) : (k : Nat) → Val (Ty.vec k t).mask → Nat → Val t.mask
  | 0, x, _ => x
  | k + 1, x, i => if i < 2 ^ k then maskLane t k x.1 i else maskLane t k x.2 (i - 2 ^ k)

/-- Update lane `i` of a comparison mask tree `Val (Ty.vec k t).mask`. -/
def setMaskLane (t : Ty) : (k : Nat) → Val (Ty.vec k t).mask → Nat → Val t.mask → Val (Ty.vec k t).mask
  | 0, _, _, v => v
  | k + 1, x, i, v =>
    if i < 2 ^ k then (setMaskLane t k x.1 i v, x.2)
    else (x.1, setMaskLane t k x.2 (i - 2 ^ k) v)

/-- Broadcast a mask leaf across all `2^k` lanes of `Val (Ty.vec k t).mask`. -/
def splatMask (t : Ty) : (k : Nat) → Val t.mask → Val (Ty.vec k t).mask
  | 0, v => v
  | k + 1, v => (splatMask t k v, splatMask t k v)

/-! ## Core `lane` / `setLane` / `splatV` / `ofLaneFn` identities -/

theorem lane_setLane_self : ∀ (k : Nat) {t : Ty} (x : Val (Ty.vec k t)) (i : Nat),
    i < 2 ^ k → (v : Val t) → lane k (setLane k x i v) i = v
  | 0, _, _, _, _, _ => rfl
  | k + 1, _, x, i, hi, v => by
    simp only [setLane, lane]
    split <;> rename_i hlt
    · simp [lane_setLane_self k x.1 i hlt v]
    · have hlt2 : i - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
      simp [lane_setLane_self k x.2 (i - 2 ^ k) hlt2 v]

theorem lane_setLane_ne : ∀ (k : Nat) {t : Ty} (x : Val (Ty.vec k t)) {i j : Nat},
    i < 2 ^ k → j < 2 ^ k → j ≠ i → (v : Val t) →
    lane k (setLane k x i v) j = lane k x j
  | 0, _, _, i, j, hi, hj, hne, _ => by omega
  | k + 1, _, x, i, j, hi, hj, hne, v => by
    simp only [setLane, lane]
    by_cases hij : i < 2 ^ k <;> by_cases hjj : j < 2 ^ k <;> simp [hij, hjj]
    · exact lane_setLane_ne k x.1 hij hjj hne v
    · have hi2 : i - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
      have hj2 : j - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hj; omega
      exact lane_setLane_ne k x.2 hi2 hj2 (by omega) v

theorem lane_setLane (k : Nat) {t : Ty} (x : Val (Ty.vec k t)) {i j : Nat}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (v : Val t) :
    lane k (setLane k x i v) j = if j = i then v else lane k x j := by
  by_cases h : j = i
  · subst h; simp [lane_setLane_self k x j hj v]
  · simp [h, lane_setLane_ne k x hi hj h v]

theorem setLane_lane : ∀ (k : Nat) {t : Ty} (x : Val (Ty.vec k t)) (i : Nat),
    setLane k x i (lane k x i) = x
  | 0, _, _, _ => rfl
  | k + 1, _, x, i => by
    simp only [setLane, lane]
    split
    · rw [setLane_lane k x.1 i]
    · rw [setLane_lane k x.2 (i - 2 ^ k)]

theorem setLane_setLane_self : ∀ (k : Nat) {t : Ty} (x : Val (Ty.vec k t)) (i : Nat) (v₁ v₂ : Val t),
    setLane k (setLane k x i v₁) i v₂ = setLane k x i v₂
  | 0, _, _, _, _, _ => rfl
  | k + 1, _, x, i, v₁, v₂ => by
    simp only [setLane]
    split <;> simp [setLane_setLane_self]

theorem vec_ext : ∀ {k : Nat} {t : Ty} {x y : Val (Ty.vec k t)},
    (∀ i < 2 ^ k, lane k x i = lane k y i) → x = y
  | 0, _, _, _, h => h 0 (by decide)
  | k + 1, _, x, y, h => by
    apply Prod.ext
    · apply vec_ext (k := k)
      intro i hi
      simpa [lane, hi] using h i (Nat.lt_of_lt_of_le hi (by rw [Nat.pow_succ]; omega))
    · apply vec_ext (k := k)
      intro i hi
      have hge : ¬ (i + 2 ^ k) < 2 ^ k := by omega
      have hlt : i + 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      simpa [lane, hge] using h (i + 2 ^ k) hlt

@[simp] theorem lane_splatV : ∀ (k : Nat) {t : Ty} (v : Val t) (i : Nat),
    lane k (splatV k v) i = v
  | 0, _, _, _ => rfl
  | k + 1, _, v, i => by
    simp only [splatV, lane]
    split <;> exact lane_splatV k v _

theorem lane_ofLaneFn : ∀ (k : Nat) {t : Ty} (f : Nat → Val t) (i : Nat),
    i < 2 ^ k → lane k (ofLaneFn k f) i = f i
  | 0, _, f, i, hi => by
    obtain rfl : i = 0 := by omega
    rfl
  | k + 1, _, f, i, hi => by
    simp only [ofLaneFn, lane]
    split <;> rename_i hlt
    · exact lane_ofLaneFn k f i hlt
    · have hi2 : i - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
      rw [lane_ofLaneFn k (fun j => f (j + 2 ^ k)) (i - 2 ^ k) hi2]
      congr 1; omega

theorem ofLaneFn_lane : ∀ (k : Nat) {t : Ty} (x : Val (Ty.vec k t)),
    ofLaneFn k (lane k x) = x
  | 0, _, _ => rfl
  | k + 1, _, x => by
    apply vec_ext
    intro i hi
    rw [lane_ofLaneFn (k + 1) (lane (k + 1) x) i hi]

@[simp] theorem maskLane_splatMask (t : Ty) : ∀ (k : Nat) (v : Val t.mask) (i : Nat),
    maskLane t k (splatMask t k v) i = v
  | 0, _, _ => rfl
  | k + 1, v, i => by
    simp only [splatMask, maskLane]
    split <;> exact maskLane_splatMask t k v _

/-! ## Leaf-wise lane lifting (`lift1`, `lift2`, `lift3`, `liftCmp`, `blendV`) -/

theorem lane_lift3 (f : ∀ {n}, BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) (t : Ty) :
    ∀ (k : Nat) (a b c : Val (Ty.vec k t)) (i : Nat),
      lane k (lift3 f g (Ty.vec k t) a b c) i =
        lift3 f g t (lane k a i) (lane k b i) (lane k c i)
  | 0, _, _, _, _ => rfl
  | k + 1, a, b, c, i => by
    simp only [lane, lift3]
    split <;> exact lane_lift3 f g t k _ _ _ _

/-- Lane lemma for `liftCmp` (`T1` review `#18` #7). -/
theorem lane_liftCmp (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool) (t : Ty) :
    ∀ (k : Nat) (a b : Val (Ty.vec k t)) (i : Nat),
      maskLane t k (liftCmp f g (Ty.vec k t) a b) i =
        liftCmp f g t (lane k a i) (lane k b i)
  | 0, _, _, _ => rfl
  | k + 1, a, b, i => by
    simp only [maskLane, liftCmp, lane]
    split <;> exact lane_liftCmp f g t k _ _ _

/-- Lane lemma for `blendV` (`T1` review `#18` #7). -/
theorem lane_blendV (t : Ty) :
    ∀ (k : Nat) (c : Val (Ty.vec k t).mask) (a b : Val (Ty.vec k t)) (i : Nat),
      lane k (blendV (Ty.vec k t) c a b) i =
        blendV t (maskLane t k c i) (lane k a i) (lane k b i)
  | 0, _, _, _, _ => rfl
  | k + 1, c, a, b, i => by
    simp only [lane, blendV, maskLane]
    split <;> exact lane_blendV t k _ _ _ _

/-- Combined lane lemma for `blendV` over `liftCmp` (`T1` review `#18` #7). -/
theorem lane_blend_liftCmp (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool) (t : Ty)
    (k : Nat) (a b x y : Val (Ty.vec k t)) (i : Nat) :
    lane k (blendV (Ty.vec k t) (liftCmp f g (Ty.vec k t) a b) x y) i =
      blendV t (liftCmp f g t (lane k a i) (lane k b i)) (lane k x i) (lane k y i) := by
  rw [lane_blendV, lane_liftCmp]

/-- Lane lemma for `liftFCmp`. -/
theorem lane_liftFCmp (o : FCmpOp) (t : Ty) :
    ∀ (k : Nat) (a b : Val (Ty.vec k t)) (i : Nat),
      maskLane t k (liftFCmp o (Ty.vec k t) a b) i =
        liftFCmp o t (lane k a i) (lane k b i)
  | 0, _, _, _ => rfl
  | k + 1, a, b, i => by
    simp only [maskLane, liftFCmp, lane]
    split <;> exact lane_liftFCmp o t k _ _ _

theorem lane_liftFCmp_float (o : FCmpOp) (f : Fmt) (k : Nat)
    (a b : Val (Ty.vec k (.float f))) (i : Nat) :
    maskLane (.float f) k (liftFCmp o (Ty.vec k (.float f)) a b) i =
      fcmpLeaf o f (lane k a i) (lane k b i) :=
  lane_liftFCmp o (.float f) k a b i

/-! ### Bitvector-leaf specializations (`vec k (bits n)`) -/

theorem lane_lift1_bits (f : ∀ {n}, BitVec n → BitVec n) (g : Bool → Bool)
    (n k : Nat) (a : Val (Ty.vec k (.bits n))) (i : Nat) :
    lane k (lift1 f g (Ty.vec k (.bits n)) a) i = f (lane k a i) :=
  lane_lift1 f g (.bits n) k a i

theorem lane_lift2_bits (f : ∀ {n}, BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool)
    (n k : Nat) (a b : Val (Ty.vec k (.bits n))) (i : Nat) :
    lane k (lift2 f g (Ty.vec k (.bits n)) a b) i = f (lane k a i) (lane k b i) :=
  lane_lift2 f g (.bits n) k a b i

theorem lane_lift3_bits (f : ∀ {n}, BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) (n k : Nat) (a b c : Val (Ty.vec k (.bits n))) (i : Nat) :
    lane k (lift3 f g (Ty.vec k (.bits n)) a b c) i = f (lane k a i) (lane k b i) (lane k c i) :=
  lane_lift3 f g (.bits n) k a b c i

theorem lane_liftCmp_bits (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool)
    (n k : Nat) (a b : Val (Ty.vec k (.bits n))) (i : Nat) :
    maskLane (.bits n) k (liftCmp f g (Ty.vec k (.bits n)) a b) i =
      f (lane k a i) (lane k b i) :=
  lane_liftCmp f g (.bits n) k a b i

theorem lane_blendV_bits (n k : Nat) (c : Val (Ty.vec k (.bits n)).mask)
    (a b : Val (Ty.vec k (.bits n))) (i : Nat) :
    lane k (blendV (Ty.vec k (.bits n)) c a b) i =
      if maskLane (.bits n) k c i then lane k a i else lane k b i :=
  lane_blendV (.bits n) k c a b i

theorem lane_blend_liftCmp_bits (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool)
    (n k : Nat) (a b x y : Val (Ty.vec k (.bits n))) (i : Nat) :
    lane k (blendV (Ty.vec k (.bits n)) (liftCmp f g (Ty.vec k (.bits n)) a b) x y) i =
      if f (lane k a i) (lane k b i) then lane k x i else lane k y i :=
  lane_blend_liftCmp f g (.bits n) k a b x y i

/-! ## Vector opcode lane specs (`vpaddd`, `vpternlogd`, `vprord`, `vpsrld`, `vumin`, `qrStep`) -/

section
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}

theorem wp_vec_add {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i + lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_add_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (· + ·) (· ^^ ·) n k a.val b.val i

theorem wp_vec_sub {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i - lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_sub_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (· - ·) (· ^^ ·) n k a.val b.val i

theorem wp_vec_mul {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i * lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_mul_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (· * ·) (· && ·) n k a.val b.val i

theorem wp_vec_neg {n k : Nat} (a : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = -lane k a.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.neg (Ty.vec k (.bits n))) (a, ())) cont) m := by
  rw [wp_let_neg_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift1_bits (- ·) id n k a.val i

theorem wp_vec_and {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i &&& lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_and_eq]
  exact h _ fun i => lane_lift2_bits (· &&& ·) (· && ·) n k a.val b.val i

theorem wp_vec_or {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i ||| lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_or_eq]
  exact h _ fun i => lane_lift2_bits (· ||| ·) (· || ·) n k a.val b.val i

theorem wp_vec_xor {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = lane k a.val i ^^^ lane k b.val i) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_xor_eq]
  exact h _ fun i => lane_lift2_bits (· ^^^ ·) (· ^^ ·) n k a.val b.val i

theorem wp_vec_not {n k : Nat} (a : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = ~~~(lane k a.val i)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.not (Ty.vec k (.bits n))) (a, ())) cont) m := by
  rw [wp_let_not_eq]
  exact h _ fun i => lane_lift1_bits (~~~ ·) (! ·) n k a.val i

theorem wp_vec_ternlog {n k : Nat} (imm : BitVec 8) (a b c : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = ternaryLogic (lane k a.val i) (lane k b.val i) (lane k c.val i) imm) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ternlog (Ty.vec k (.bits n)) imm) (a, b, c, ())) cont) m := by
  rw [wp_let_ternlog_eq]
  exact h _ fun i =>
    lane_lift3_bits (fun x y z => ternaryLogic x y z imm)
      (fun x y z => ternaryLogicBool x y z imm) n k a.val b.val c.val i

theorem wp_vec_shl {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i) <<< ((lane k b.val i).toNat % n)) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_shl_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (fun {w} x y => x <<< (y.toNat % w)) (fun x _ => x) n k a.val b.val i

theorem wp_vec_lshr {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i) >>> ((lane k b.val i).toNat % n)) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_lshr_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (fun {w} x y => x >>> (y.toNat % w)) (fun x _ => x) n k a.val b.val i

theorem wp_vec_ashr {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).sshiftRight ((lane k b.val i).toNat % n)) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ashr (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_ashr_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (fun {w} x y => x.sshiftRight (y.toNat % w)) (fun x _ => x) n k a.val b.val i

theorem wp_vec_rotl {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).rotateLeft ((lane k b.val i).toNat % n)) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotl (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_rotl_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (fun {w} x y => x.rotateLeft (y.toNat % w)) (fun x _ => x) n k a.val b.val i

theorem wp_vec_rotr {n k : Nat} (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).rotateRight ((lane k b.val i).toNat % n)) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotr (Ty.vec k (.bits n))) (a, b, ())) cont) m := by
  rw [wp_let_rotr_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_lift2_bits (fun {w} x y => x.rotateRight (y.toNat % w)) (fun x _ => x) n k a.val b.val i

theorem wp_vec_shl_splat {n k : Nat} (a : Arg Val (Ty.vec k (.bits n))) (s : BitVec n)
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i) <<< (s.toNat % n)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl (Ty.vec k (.bits n))) (a, .imm (splatV k s), ())) cont) m :=
  wp_vec_shl a (.imm (splatV k s)) cont fun r hr => h r fun i => by simpa [lane_splatV] using hr i

theorem wp_vec_lshr_splat {n k : Nat} (a : Arg Val (Ty.vec k (.bits n))) (s : BitVec n)
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i) >>> (s.toNat % n)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr (Ty.vec k (.bits n))) (a, .imm (splatV k s), ())) cont) m :=
  wp_vec_lshr a (.imm (splatV k s)) cont fun r hr => h r fun i => by simpa [lane_splatV] using hr i

theorem wp_vec_ashr_splat {n k : Nat} (a : Arg Val (Ty.vec k (.bits n))) (s : BitVec n)
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).sshiftRight (s.toNat % n)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.ashr (Ty.vec k (.bits n))) (a, .imm (splatV k s), ())) cont) m :=
  wp_vec_ashr a (.imm (splatV k s)) cont fun r hr => h r fun i => by simpa [lane_splatV] using hr i

theorem wp_vec_rotl_splat {n k : Nat} (a : Arg Val (Ty.vec k (.bits n))) (s : BitVec n)
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).rotateLeft (s.toNat % n)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotl (Ty.vec k (.bits n))) (a, .imm (splatV k s), ())) cont) m :=
  wp_vec_rotl a (.imm (splatV k s)) cont fun r hr => h r fun i => by simpa [lane_splatV] using hr i

theorem wp_vec_rotr_splat {n k : Nat} (a : Arg Val (Ty.vec k (.bits n))) (s : BitVec n)
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i = (lane k a.val i).rotateRight (s.toNat % n)) → wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.rotr (Ty.vec k (.bits n))) (a, .imm (splatV k s), ())) cont) m :=
  wp_vec_rotr a (.imm (splatV k s)) cont fun r hr => h r fun i => by simpa [lane_splatV] using hr i

theorem wp_vec_cmp {n k : Nat} (o : CmpOp) {mt : Ty} (hm : mt = (Ty.vec k (.bits n)).mask)
    (a b : Arg Val (Ty.vec k (.bits n))) (cont : Tup Val [mt] → Expr Val Cont rs)
    (h : ∀ c : Val mt,
      (∀ i, maskLane (.bits n) k (cast (congrArg Val hm) c) i =
        o.evalBits (lane k a.val i) (lane k b.val i)) →
      wp Γ Q X (cont (c, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (Ty.vec k (.bits n)) mt hm) (a, b, ())) cont) m := by
  subst hm
  rw [wp_let_cmp_eq]
  simp only [Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  exact h _ fun i => lane_liftCmp_bits o.evalBits o.evalBool n k a.val b.val i

theorem wp_vec_blend {n k : Nat} {mt : Ty} (hm : mt = (Ty.vec k (.bits n)).mask)
    (c : Arg Val mt) (a b : Arg Val (Ty.vec k (.bits n)))
    (cont : Tup Val [Ty.vec k (.bits n)] → Expr Val Cont rs)
    (h : ∀ r : Val (Ty.vec k (.bits n)),
      (∀ i, lane k r i =
        if maskLane (.bits n) k (cast (congrArg Val hm) c.val) i
        then lane k a.val i else lane k b.val i) →
      wp Γ Q X (cont (r, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.blend (Ty.vec k (.bits n)) mt hm) (c, a, b, ())) cont) m := by
  subst hm
  rw [wp_let_blend_eq]
  exact h _ fun i => lane_blendV_bits n k c.val a.val b.val i

end

/-! ## Generic `Lanewise1`/`Lanewise2`/`Lanewise3`/`Lanewise4` and `LanewiseX` by induction on `k` -/

def Lanewise1 {t : Ty} (P : Val t → Prop) : (k : Nat) → Val (Ty.vec k t) → Prop
  | 0, x => P x
  | k + 1, x => Lanewise1 P k x.1 ∧ Lanewise1 P k x.2

def Lanewise2 {t₁ t₂ : Ty} (P : Val t₁ → Val t₂ → Prop) :
    (k : Nat) → Val (Ty.vec k t₁) → Val (Ty.vec k t₂) → Prop
  | 0, x, y => P x y
  | k + 1, x, y => Lanewise2 P k x.1 y.1 ∧ Lanewise2 P k x.2 y.2

def Lanewise3 {t₁ t₂ t₃ : Ty} (P : Val t₁ → Val t₂ → Val t₃ → Prop) :
    (k : Nat) → Val (Ty.vec k t₁) → Val (Ty.vec k t₂) → Val (Ty.vec k t₃) → Prop
  | 0, x, y, z => P x y z
  | k + 1, x, y, z => Lanewise3 P k x.1 y.1 z.1 ∧ Lanewise3 P k x.2 y.2 z.2

def Lanewise4 {t₁ t₂ t₃ t₄ : Ty} (P : Val t₁ → Val t₂ → Val t₃ → Val t₄ → Prop) :
    (k : Nat) → Val (Ty.vec k t₁) → Val (Ty.vec k t₂) → Val (Ty.vec k t₃) →
      Val (Ty.vec k t₄) → Prop
  | 0, w, x, y, z => P w x y z
  | k + 1, w, x, y, z => Lanewise4 P k w.1 x.1 y.1 z.1 ∧ Lanewise4 P k w.2 x.2 y.2 z.2

def tupFst {k : Nat} : {ts : List Ty} →
    Tup (fun t => Val (Ty.vec (k + 1) t)) ts → Tup (fun t => Val (Ty.vec k t)) ts
  | [], () => ()
  | _ :: _, (x, xs) => (x.1, tupFst xs)

def tupSnd {k : Nat} : {ts : List Ty} →
    Tup (fun t => Val (Ty.vec (k + 1) t)) ts → Tup (fun t => Val (Ty.vec k t)) ts
  | [], () => ()
  | _ :: _, (x, xs) => (x.2, tupSnd xs)

def tupLane (k : Nat) : {ts : List Ty} →
    Tup (fun t => Val (Ty.vec k t)) ts → Nat → Tup Val ts
  | [], (), _ => ()
  | _ :: _, (x, xs), i => (lane k x i, tupLane k xs i)

/-- Arity-generic lanewise predicate for arbitrary signature `ts : List Ty`. -/
def LanewiseX {ts : List Ty} (P : Tup Val ts → Prop) :
    (k : Nat) → Tup (fun t => Val (Ty.vec k t)) ts → Prop
  | 0, xs => P xs
  | k + 1, xs => LanewiseX P k (tupFst xs) ∧ LanewiseX P k (tupSnd xs)

theorem tupLane_succ_lt (k : Nat) : {ts : List Ty} →
    (xs : Tup (fun t => Val (Ty.vec (k + 1) t)) ts) → {i : Nat} → i < 2 ^ k →
    tupLane (k + 1) xs i = tupLane k (tupFst xs) i
  | [], (), _, _ => rfl
  | _ :: _, (x, xs), i, hi => by
    simp [tupLane, tupFst, lane, hi, tupLane_succ_lt k xs hi]

theorem tupLane_succ_ge (k : Nat) : {ts : List Ty} →
    (xs : Tup (fun t => Val (Ty.vec (k + 1) t)) ts) → {i : Nat} → ¬ i < 2 ^ k →
    tupLane (k + 1) xs i = tupLane k (tupSnd xs) (i - 2 ^ k)
  | [], (), _, _ => rfl
  | _ :: _, (x, xs), i, hge => by
    simp [tupLane, tupSnd, lane, hge, tupLane_succ_ge k xs hge]

private theorem tupLane_zero : {ts : List Ty} → (xs : Tup Val ts) → tupLane 0 xs 0 = xs
  | [], () => rfl
  | _ :: _, (_, _) => Prod.ext rfl (tupLane_zero _)

theorem lanewiseX_iff_lane {ts : List Ty} (P : Tup Val ts → Prop) :
    ∀ (k : Nat) (xs : Tup (fun t => Val (Ty.vec k t)) ts),
      LanewiseX P k xs ↔ ∀ i < 2 ^ k, P (tupLane k xs i)
  | 0, xs => by
    have h0 : P xs ↔ P (tupLane 0 xs 0) := by rw [tupLane_zero]
    constructor
    · intro hp i hi
      obtain rfl : i = 0 := by omega
      exact h0.mp hp
    · intro h
      exact h0.mpr (h 0 (by decide))
  | k + 1, xs => by
    rw [LanewiseX, lanewiseX_iff_lane P k (tupFst xs), lanewiseX_iff_lane P k (tupSnd xs)]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hlt : i < 2 ^ k
      · rw [tupLane_succ_lt k xs hlt]; exact h1 i hlt
      · rw [tupLane_succ_ge k xs hlt]; exact h2 (i - 2 ^ k) (by rw [Nat.pow_succ] at hi; omega)
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have h' := h i (Nat.lt_of_lt_of_le hi (by rw [Nat.pow_succ]; omega))
        rwa [tupLane_succ_lt k xs hi] at h'
      · have h' := h (i + 2 ^ k) (by rw [Nat.pow_succ]; omega)
        have hge : ¬ i + 2 ^ k < 2 ^ k := by omega
        rw [tupLane_succ_ge k xs hge, Nat.add_sub_cancel] at h'
        exact h'

private theorem lanewise_succ_iff (k : Nat) (Q₁ Q₂ R : Nat → Prop)
    (h_lt : ∀ i, i < 2 ^ k → (R i ↔ Q₁ i))
    (h_ge : ∀ i, ¬ i < 2 ^ k → (R i ↔ Q₂ (i - 2 ^ k))) :
    ((∀ i < 2 ^ k, Q₁ i) ∧ (∀ i < 2 ^ k, Q₂ i)) ↔ ∀ i < 2 ^ (k + 1), R i := by
  constructor
  · rintro ⟨h1, h2⟩ i hi
    by_cases hlt : i < 2 ^ k
    · exact (h_lt i hlt).mpr (h1 i hlt)
    · exact (h_ge i hlt).mpr (h2 (i - 2 ^ k) (by rw [Nat.pow_succ] at hi; omega))
  · intro h
    refine ⟨fun i hi =>
        (h_lt i hi).mp (h i (Nat.lt_of_lt_of_le hi (by rw [Nat.pow_succ]; omega))),
      fun i hi => ?_⟩
    have h' := (h_ge (i + 2 ^ k) (by omega)).mp (h (i + 2 ^ k) (by rw [Nat.pow_succ]; omega))
    simpa only [Nat.add_sub_cancel] using h'

theorem lanewise1_iff_lane {t : Ty} (P : Val t → Prop) :
    ∀ (k : Nat) (x : Val (Ty.vec k t)), Lanewise1 P k x ↔ ∀ i < 2 ^ k, P (lane k x i)
  | 0, x => ⟨fun h _ _ => h, fun h => h 0 (by decide)⟩
  | k + 1, x => by
    rw [Lanewise1, lanewise1_iff_lane P k x.1, lanewise1_iff_lane P k x.2]
    exact lanewise_succ_iff k _ _ _ (fun _ h => by simp [lane, h]) (fun _ h => by simp [lane, h])

theorem lanewise2_iff_lane {t₁ t₂ : Ty} (P : Val t₁ → Val t₂ → Prop) :
    ∀ (k : Nat) (x : Val (Ty.vec k t₁)) (y : Val (Ty.vec k t₂)),
      Lanewise2 P k x y ↔ ∀ i < 2 ^ k, P (lane k x i) (lane k y i)
  | 0, x, y => ⟨fun h _ _ => h, fun h => h 0 (by decide)⟩
  | k + 1, x, y => by
    rw [Lanewise2, lanewise2_iff_lane P k x.1 y.1, lanewise2_iff_lane P k x.2 y.2]
    exact lanewise_succ_iff k _ _ _ (fun _ h => by simp [lane, h]) (fun _ h => by simp [lane, h])

theorem lanewise3_iff_lane {t₁ t₂ t₃ : Ty} (P : Val t₁ → Val t₂ → Val t₃ → Prop) :
    ∀ (k : Nat) (x : Val (Ty.vec k t₁)) (y : Val (Ty.vec k t₂)) (z : Val (Ty.vec k t₃)),
      Lanewise3 P k x y z ↔ ∀ i < 2 ^ k, P (lane k x i) (lane k y i) (lane k z i)
  | 0, x, y, z => ⟨fun h _ _ => h, fun h => h 0 (by decide)⟩
  | k + 1, x, y, z => by
    rw [Lanewise3, lanewise3_iff_lane P k x.1 y.1 z.1, lanewise3_iff_lane P k x.2 y.2 z.2]
    exact lanewise_succ_iff k _ _ _ (fun _ h => by simp [lane, h]) (fun _ h => by simp [lane, h])

theorem lanewise4_iff_lane {t₁ t₂ t₃ t₄ : Ty} (P : Val t₁ → Val t₂ → Val t₃ → Val t₄ → Prop) :
    ∀ (k : Nat) (w : Val (Ty.vec k t₁)) (x : Val (Ty.vec k t₂)) (y : Val (Ty.vec k t₃))
      (z : Val (Ty.vec k t₄)),
      Lanewise4 P k w x y z ↔ ∀ i < 2 ^ k, P (lane k w i) (lane k x i) (lane k y i) (lane k z i)
  | 0, w, x, y, z => ⟨fun h _ _ => h, fun h => h 0 (by decide)⟩
  | k + 1, w, x, y, z => by
    rw [Lanewise4, lanewise4_iff_lane P k w.1 x.1 y.1 z.1,
      lanewise4_iff_lane P k w.2 x.2 y.2 z.2]
    exact lanewise_succ_iff k _ _ _ (fun _ h => by simp [lane, h]) (fun _ h => by simp [lane, h])

theorem lanewise1_splatV {t : Ty} (P : Val t → Prop) (k : Nat) {v : Val t} (hv : P v) :
    Lanewise1 P k (splatV k v) :=
  (lanewise1_iff_lane P k _).2 fun _ _ => by simpa using hv

theorem lanewise2_lift1 {t : Ty} (P : Val t → Val t → Prop)
    (f : ∀ {n}, BitVec n → BitVec n) (g : Bool → Bool)
    (h : ∀ x : Val t, P (lift1 f g t x) x) :
    ∀ (k : Nat) (a : Val (Ty.vec k t)), Lanewise2 P k (lift1 f g (Ty.vec k t) a) a
  | 0, a => h a
  | k + 1, a => ⟨lanewise2_lift1 P f g h k a.1, lanewise2_lift1 P f g h k a.2⟩

theorem lanewise3_lift2 {t : Ty} (P : Val t → Val t → Val t → Prop)
    (f : ∀ {n}, BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool)
    (h : ∀ x y : Val t, P (lift2 f g t x y) x y) :
    ∀ (k : Nat) (a b : Val (Ty.vec k t)), Lanewise3 P k (lift2 f g (Ty.vec k t) a b) a b
  | 0, a, b => h a b
  | k + 1, a, b => ⟨lanewise3_lift2 P f g h k a.1 b.1, lanewise3_lift2 P f g h k a.2 b.2⟩

theorem lanewise4_lift3 {t : Ty} (P : Val t → Val t → Val t → Val t → Prop)
    (f : ∀ {n}, BitVec n → BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool → Bool)
    (h : ∀ x y z : Val t, P (lift3 f g t x y z) x y z) :
    ∀ (k : Nat) (a b c : Val (Ty.vec k t)),
      Lanewise4 P k (lift3 f g (Ty.vec k t) a b c) a b c
  | 0, a, b, c => h a b c
  | k + 1, a, b, c =>
    ⟨lanewise4_lift3 P f g h k a.1 b.1 c.1, lanewise4_lift3 P f g h k a.2 b.2 c.2⟩

theorem lanewise3_blend_cmp {t : Ty} (P : Val t → Val t → Val t → Prop)
    (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool)
    (h : ∀ x y : Val t, P (blendV t (liftCmp f g t x y) x y) x y) :
    ∀ (k : Nat) (a b : Val (Ty.vec k t)),
      Lanewise3 P k (blendV (Ty.vec k t) (liftCmp f g (Ty.vec k t) a b) a b) a b
  | 0, a, b => h a b
  | k + 1, a, b =>
    ⟨lanewise3_blend_cmp P f g h k a.1 b.1, lanewise3_blend_cmp P f g h k a.2 b.2⟩

theorem lanewise1_mono {t : Ty} {P Q : Val t → Prop} (h : ∀ x, P x → Q x) :
    ∀ (k : Nat) (x : Val (Ty.vec k t)), Lanewise1 P k x → Lanewise1 Q k x
  | 0, x, hp => h x hp
  | k + 1, x, ⟨h1, h2⟩ => ⟨lanewise1_mono h k x.1 h1, lanewise1_mono h k x.2 h2⟩

theorem lanewise2_mono {t₁ t₂ : Ty} {P Q : Val t₁ → Val t₂ → Prop} (h : ∀ x y, P x y → Q x y) :
    ∀ (k : Nat) (x : Val (Ty.vec k t₁)) (y : Val (Ty.vec k t₂)),
      Lanewise2 P k x y → Lanewise2 Q k x y
  | 0, x, y, hp => h x y hp
  | k + 1, x, y, ⟨h1, h2⟩ => ⟨lanewise2_mono h k x.1 y.1 h1, lanewise2_mono h k x.2 y.2 h2⟩

theorem lanewise3_mono {t₁ t₂ t₃ : Ty} {P Q : Val t₁ → Val t₂ → Val t₃ → Prop}
    (h : ∀ x y z, P x y z → Q x y z) :
    ∀ (k : Nat) (x : Val (Ty.vec k t₁)) (y : Val (Ty.vec k t₂)) (z : Val (Ty.vec k t₃)),
      Lanewise3 P k x y z → Lanewise3 Q k x y z
  | 0, x, y, z, hp => h x y z hp
  | k + 1, x, y, z, ⟨h1, h2⟩ =>
    ⟨lanewise3_mono h k x.1 y.1 z.1 h1, lanewise3_mono h k x.2 y.2 z.2 h2⟩

theorem lanewise4_mono {t₁ t₂ t₃ t₄ : Ty} {P Q : Val t₁ → Val t₂ → Val t₃ → Val t₄ → Prop}
    (h : ∀ w x y z, P w x y z → Q w x y z) :
    ∀ (k : Nat) (w : Val (Ty.vec k t₁)) (x : Val (Ty.vec k t₂))
      (y : Val (Ty.vec k t₃)) (z : Val (Ty.vec k t₄)),
      Lanewise4 P k w x y z → Lanewise4 Q k w x y z
  | 0, w, x, y, z, hp => h w x y z hp
  | k + 1, w, x, y, z, ⟨h1, h2⟩ =>
    ⟨lanewise4_mono h k w.1 x.1 y.1 z.1 h1, lanewise4_mono h k w.2 x.2 y.2 z.2 h2⟩

theorem lanewiseX_mono {ts : List Ty} {P Q : Tup Val ts → Prop} (h : ∀ xs, P xs → Q xs) :
    ∀ (k : Nat) (xs : Tup (fun t => Val (Ty.vec k t)) ts), LanewiseX P k xs → LanewiseX Q k xs
  | 0, xs, hp => h xs hp
  | k + 1, _, ⟨h1, h2⟩ => ⟨lanewiseX_mono h k _ h1, lanewiseX_mono h k _ h2⟩

/-! ## 128-bit `v4i32` bitvector-lane & `shuffleDwords` lemmas -/

theorem bvLane_toBits_v4i32 (w0 w1 w2 w3 : BitVec 32) :
    bvLane 32 0 (toBits v4i32 ((w0, w1), (w2, w3))) = w0 ∧
    bvLane 32 1 (toBits v4i32 ((w0, w1), (w2, w3))) = w1 ∧
    bvLane 32 2 (toBits v4i32 ((w0, w1), (w2, w3))) = w2 ∧
    bvLane 32 3 (toBits v4i32 ((w0, w1), (w2, w3))) = w3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bvLane, toBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast,
      BitVec.getLsbD_append]
    grind

theorem bvOfLanes_128_32_eq (f : Nat → BitVec 32) :
    bvOfLanes 128 32 f =
      (((f 0).setWidth 128 ||| ((f 1).setWidth 128 <<< 32)) |||
        ((f 2).setWidth 128 <<< 64)) ||| ((f 3).setWidth 128 <<< 96) := by
  have hrange : List.range (128 / 32) = [0, 1, 2, 3] := by decide
  unfold bvOfLanes
  rw [hrange]
  simp only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.mul_one,
    BitVec.shiftLeft_zero, BitVec.zero_or]

theorem ofBits_bvOfLanes_v4i32 (f : Nat → BitVec 32) :
    ofBits v4i32 (bvOfLanes v4i32.size 32 f) = ((f 0, f 1), (f 2, f 3)) := by
  show ofBits v4i32 (bvOfLanes 128 32 f) = ((f 0, f 1), (f 2, f 3))
  rw [bvOfLanes_128_32_eq]
  simp only [ofBits, Ty.size]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    grind

def v4i32LaneGet (r : Val v4i32) (j : Nat) : BitVec 32 :=
  match j % 4 with
  | 0 => r.1.1
  | 1 => r.1.2
  | 2 => r.2.1
  | _ => r.2.2

theorem ofBits_shuffleDwords_v4i32 (r : Val v4i32) (imm : BitVec 8) :
    ofBits v4i32 (shuffleDwords (toBits v4i32 r) imm) =
      ((v4i32LaneGet r (imm.toNat % 4), v4i32LaneGet r ((imm.toNat >>> 2) % 4)),
       (v4i32LaneGet r ((imm.toNat >>> 4) % 4), v4i32LaneGet r ((imm.toNat >>> 6) % 4))) := by
  rcases r with ⟨⟨w0, w1⟩, ⟨w2, w3⟩⟩
  have ⟨h0, h1, h2, h3⟩ := bvLane_toBits_v4i32 w0 w1 w2 w3
  unfold shuffleDwords
  rw [ofBits_bvOfLanes_v4i32]
  have hlane : ∀ k : Nat, bvLane 32 (k % 4) (toBits v4i32 ((w0, w1), (w2, w3))) =
      v4i32LaneGet ((w0, w1), (w2, w3)) (k % 4) := fun k => by
    have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hk with h | h | h | h <;> simp [v4i32LaneGet, h, h0, h1, h2, h3]
  simp only [Nat.zero_div, Nat.mul_zero, Nat.zero_add]
  refine Prod.ext (Prod.ext (hlane imm.toNat) ?_) (Prod.ext ?_ ?_)
  · dsimp only
    rw [show 4 * (1 / 4) = 0 from rfl, show 2 * (1 % 4) = 2 from rfl, Nat.zero_add]
    exact hlane (imm.toNat >>> 2)
  · dsimp only
    rw [show 4 * (2 / 4) = 0 from rfl, show 2 * (2 % 4) = 4 from rfl, Nat.zero_add]
    exact hlane (imm.toNat >>> 4)
  · dsimp only
    rw [show 4 * (3 / 4) = 0 from rfl, show 2 * (3 % 4) = 6 from rfl, Nat.zero_add]
    exact hlane (imm.toNat >>> 6)

theorem shufd_v4i32_39 (r : Val v4i32) :
    ofBits v4i32 (shuffleDwords (toBits v4i32 r) (0x39 : BitVec 8)) =
      ((r.1.2, r.2.1), (r.2.2, r.1.1)) := by
  rw [ofBits_shuffleDwords_v4i32]; rfl

theorem shufd_v4i32_4e (r : Val v4i32) :
    ofBits v4i32 (shuffleDwords (toBits v4i32 r) (0x4e : BitVec 8)) =
      ((r.2.1, r.2.2), (r.1.1, r.1.2)) := by
  rw [ofBits_shuffleDwords_v4i32]; rfl

theorem shufd_v4i32_93 (r : Val v4i32) :
    ofBits v4i32 (shuffleDwords (toBits v4i32 r) (0x93 : BitVec 8)) =
      ((r.2.2, r.1.1), (r.1.2, r.2.1)) := by
  rw [ofBits_shuffleDwords_v4i32]; rfl

end LeanQbe.T
