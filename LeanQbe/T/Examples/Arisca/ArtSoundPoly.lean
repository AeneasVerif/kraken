module

public import LeanQbe.T.Examples.Arisca.ArtCore

/-!
# Polynomial algebra soundness for the ART checker (`ArtCore.lean`)

Semantics: a symbol valuation `σ : Nat → Bool`; a monomial `m` (bitset) evaluates to `1` iff every
symbol in it is true; coefficients live in `BitVec w` (so `mod 2^w` is native). All lemmas are
pure value equations, NO sortedness / canonicity invariants are needed for soundness.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca

@[expose] public section

/-- every symbol of `m` is true under `σ` -/
def MonoTrue (σ : Nat → Bool) (m : Nat) : Prop := ∀ i, m.testBit i = true → σ i = true

open Classical in
noncomputable def monoVal (w : Nat) (σ : Nat → Bool) (m : Nat) : BitVec w :=
  if MonoTrue σ m then 1 else 0

/-- `0/1` value of a Boolean -/
def bv (w : Nat) (b : Bool) : BitVec w := if b then 1 else 0

noncomputable def evalP (w : Nat) (σ : Nat → Bool) : Poly → BitVec w
  | .nil => 0
  | .cons c m p => BitVec.ofNat w c * monoVal w σ m + evalP w σ p

noncomputable def evalL (w : Nat) (σ : Nat → Bool) (ps : List Poly) : BitVec w :=
  ps.foldr (fun p acc => evalP w σ p + acc) 0

/-- `van` only flags monomials that are `0` under `σ` -/
def VanOk (w : Nat) (σ : Nat → Bool) (van : Nat → Bool) : Prop :=
  ∀ m, van m = true → monoVal w σ m = 0

/-- value of a pending element -/
noncomputable def optV (w : Nat) (σ : Nat → Bool) : Option Poly → BitVec w
  | none => 0
  | some p => evalP w σ p

end

public section

variable {w : Nat} {σ : Nat → Bool}

/-! ## Helpers: arithmetic -/

theorem bv_add (x y : Nat) :
    BitVec.ofNat w (Nat.add x y) = BitVec.ofNat w x + BitVec.ofNat w y := BitVec.ofNat_add x y

theorem bv_mul (x y : Nat) :
    BitVec.ofNat w (Nat.mul x y) = BitVec.ofNat w x * BitVec.ofNat w y := BitVec.ofNat_mul x y

theorem bv_mod (M x : Nat) (hM : M = 2 ^ w) : BitVec.ofNat w (Nat.mod x M) = BitVec.ofNat w x := by
  subst hM
  apply BitVec.eq_of_toNat_eq
  show (x % 2 ^ w) % 2 ^ w = x % 2 ^ w
  exact Nat.mod_mod _ _

theorem bv_zero_of_mod (M x : Nat) (hM : M = 2 ^ w) (h : Nat.mod x M = 0) :
    BitVec.ofNat w x = 0 := by
  rw [← bv_mod M x hM, h]; rfl

theorem bv_one : BitVec.ofNat w 1 = 1 := rfl

theorem bv_pred (M : Nat) (hM : M = 2 ^ w) : BitVec.ofNat w (Nat.sub M 1) = -1 := by
  subst hM
  have h1 : BitVec.ofNat w (2 ^ w - 1) + 1 = 0 := by
    rw [← bv_one, ← BitVec.ofNat_add, Nat.sub_add_cancel Nat.one_le_two_pow]
    apply BitVec.eq_of_toNat_eq
    simp
  show BitVec.ofNat w (2 ^ w - 1) = -1
  grind

/-! ## Helpers: monomials -/

theorem monoVal_true (m : Nat) (h : MonoTrue σ m) : monoVal w σ m = 1 := by
  simp [monoVal, h]

theorem monoVal_false (m : Nat) (h : ¬ MonoTrue σ m) : monoVal w σ m = 0 := by
  simp [monoVal, h]

theorem tb_eq (m i : Nat) : tb m i = m.testBit i := by
  show Nat.beq ((m >>> i) &&& 1) 1 = (1 &&& (m >>> i) != 0)
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

theorem monoTrue_lor (m m' : Nat) :
    MonoTrue σ (Nat.lor m m') ↔ MonoTrue σ m ∧ MonoTrue σ m' := by
  have e : ∀ i, (Nat.lor m m').testBit i = (m.testBit i || m'.testBit i) :=
    fun i => Nat.testBit_or m m' i
  constructor
  · intro h
    exact ⟨fun i hi => h i (by rw [e, hi]; rfl), fun i hi => h i (by rw [e, hi]; simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    rw [e] at hi
    cases hm : m.testBit i
    · rw [hm] at hi; exact h2 i (by simpa using hi)
    · exact h1 i hm

theorem monoVal_lor (m m' : Nat) :
    monoVal w σ (Nat.lor m m') = monoVal w σ m * monoVal w σ m' := by
  by_cases h1 : MonoTrue σ m
  · by_cases h2 : MonoTrue σ m'
    · rw [monoVal_true _ ((monoTrue_lor m m').2 ⟨h1, h2⟩), monoVal_true m h1, monoVal_true m' h2]
      grind
    · rw [monoVal_false _ (fun h => h2 ((monoTrue_lor m m').1 h).2), monoVal_false m' h2]; grind
  · rw [monoVal_false _ (fun h => h1 ((monoTrue_lor m m').1 h).1), monoVal_false m h1]; grind

theorem monoVal_zero : monoVal w σ 0 = 1 := by
  apply monoVal_true
  intro i h
  simp at h

theorem monoTrue_pow (s : Nat) : MonoTrue σ (Nat.pow 2 s) ↔ σ s = true := by
  show (∀ i, (2 ^ s).testBit i = true → σ i = true) ↔ σ s = true
  simp [Nat.testBit_two_pow]

theorem monoVal_pow (s : Nat) : monoVal w σ (Nat.pow 2 s) = bv w (σ s) := by
  cases hs : σ s
  · apply monoVal_false; rw [monoTrue_pow, hs]; simp
  · apply monoVal_true; rw [monoTrue_pow, hs]

theorem monoTrue_split (m s : Nat) (h : m.testBit s = true) :
    MonoTrue σ m ↔ σ s = true ∧ MonoTrue σ (Nat.xor m (Nat.pow 2 s)) := by
  have e : ∀ i, (Nat.xor m (Nat.pow 2 s)).testBit i = (m.testBit i ^^ decide (s = i)) := by
    intro i
    show (m ^^^ 2 ^ s).testBit i = _
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
  constructor
  · intro hm
    refine ⟨hm s h, fun i hi => ?_⟩
    rw [e] at hi
    by_cases hi' : s = i
    · subst hi'; simp [h] at hi
    · simp [hi'] at hi; exact hm i hi
  · rintro ⟨hs, hx⟩ i hi
    by_cases hi' : s = i
    · subst hi'; exact hs
    · exact hx i (by rw [e]; simp [hi', hi])

theorem monoVal_split (m s : Nat) (h : m.testBit s = true) :
    monoVal w σ m = bv w (σ s) * monoVal w σ (Nat.xor m (Nat.pow 2 s)) := by
  by_cases h2 : MonoTrue σ (Nat.xor m (Nat.pow 2 s))
  · cases hs : σ s
    · rw [monoVal_false m (fun hm => by rw [((monoTrue_split m s h).1 hm).1] at hs; cases hs)]
      simp [bv]
    · rw [monoVal_true m ((monoTrue_split m s h).2 ⟨hs, h2⟩), monoVal_true _ h2]; simp [bv]
  · rw [monoVal_false m (fun hm => h2 ((monoTrue_split m s h).1 hm).2), monoVal_false _ h2]
    grind

theorem negC_ofNat (M c : Nat) (hM : M = 2 ^ w) :
    BitVec.ofNat w (negC M c) = - BitVec.ofNat w c := by
  subst hM
  show BitVec.ofNat w ((2 ^ w - c % 2 ^ w) % 2 ^ w) = -BitVec.ofNat w c
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_mod]

/-! ## Equation lemmas -/

theorem evalP_nil : evalP w σ .nil = 0 := rfl
theorem evalP_cons (c m : Nat) (p : Poly) :
    evalP w σ (.cons c m p) = BitVec.ofNat w c * monoVal w σ m + evalP w σ p := rfl
theorem evalL_nil : evalL w σ [] = 0 := rfl
theorem evalL_cons (p : Poly) (ps : List Poly) :
    evalL w σ (p :: ps) = evalP w σ p + evalL w σ ps := rfl

theorem merge_nil (M : Nat) (q : Poly) : merge M .nil q = q := rfl
theorem merge_cons_nil (M c m : Nat) (p : Poly) : merge M (.cons c m p) .nil = .cons c m p := rfl
theorem merge_cc (M c₁ m₁ c₂ m₂ : Nat) (p₁ q₂ : Poly) :
    merge M (.cons c₁ m₁ p₁) (.cons c₂ m₂ q₂) =
      Bool.rec (motive := fun _ => Poly)
        (Bool.rec (motive := fun _ => Poly) (Poly.cons c₂ m₂ (merge M (.cons c₁ m₁ p₁) q₂))
          (Poly.cons c₁ m₁ (merge M p₁ (Poly.cons c₂ m₂ q₂))) (Nat.ble m₂ m₁))
        (Bool.rec (motive := fun _ => Poly)
          (Poly.cons (Nat.mod (Nat.add c₁ c₂) M) m₁ (merge M p₁ q₂))
          (merge M p₁ q₂) (Nat.beq (Nat.mod (Nat.add c₁ c₂) M) 0))
        (Nat.beq m₁ m₂) := rfl

theorem scaleP_nil (M k : Nat) : scaleP M k .nil = .nil := rfl
theorem scaleP_cons (M k c m : Nat) (p : Poly) :
    scaleP M k (.cons c m p) =
      Bool.rec (motive := fun _ => Poly) (Poly.cons (Nat.mod (Nat.mul k c) M) m (scaleP M k p))
        (scaleP M k p) (Nat.beq (Nat.mod (Nat.mul k c) M) 0) := rfl

theorem foldM_nil (M : Nat) : foldM M [] = .nil := rfl
theorem foldM_cons (M : Nat) (a : Poly) (t : List Poly) :
    foldM M (a :: t) = merge M a (foldM M t) :=
  rfl

theorem pairs_nil_none (M : Nat) : pairs M [] none = [] := rfl
theorem pairs_nil_some (M : Nat) (p : Poly) : pairs M [] (some p) = [p] := rfl
theorem pairs_cons_none (M : Nat) (a : Poly) (t : List Poly) :
    pairs M (a :: t) none = pairs M t (some a) := rfl
theorem pairs_cons_some (M : Nat) (a p : Poly) (t : List Poly) :
    pairs M (a :: t) (some p) = merge M p a :: pairs M t none := rfl

theorem sumGo_zero (M : Nat) (ps : List Poly) : sumGo M 0 ps = foldM M ps := rfl
theorem sumGo_succ_nil (M n : Nat) : sumGo M (n + 1) [] = .nil := rfl
theorem sumGo_succ_one (M n : Nat) (a : Poly) : sumGo M (n + 1) [a] = a := rfl
theorem sumGo_succ_two (M n : Nat) (a b : Poly) (t : List Poly) :
    sumGo M (n + 1) (a :: b :: t) = sumGo M n (pairs M (a :: b :: t) none) := rfl

theorem mulTerm_nil (M : Nat) (van : Nat → Bool) (c m : Nat) (acc : List Poly) :
    mulTerm M van c m .nil acc = acc := rfl
theorem mulTerm_cons (M : Nat) (van : Nat → Bool) (c m c' m' : Nat) (R : Poly) (acc : List Poly) :
    mulTerm M van c m (.cons c' m' R) acc =
      Bool.rec (motive := fun _ => List Poly)
        (Bool.rec (motive := fun _ => List Poly)
          (Poly.cons (Nat.mod (Nat.mul c c') M) (Nat.lor m m') Poly.nil ::
            mulTerm M van c m R acc)
          (mulTerm M van c m R acc) (van (Nat.lor m m')))
        (mulTerm M van c m R acc) (Nat.beq (Nat.mod (Nat.mul c c') M) 0) := rfl

theorem mulTerms_nil (M : Nat) (van : Nat → Bool) (R : Poly) : mulTerms M van .nil R = [] := rfl
theorem mulTerms_cons (M : Nat) (van : Nat → Bool) (c m : Nat) (W R : Poly) :
    mulTerms M van (.cons c m W) R = mulTerm M van c m R (mulTerms M van W R) := rfl

theorem normP_nil (van : Nat → Bool) : normP van .nil = .nil := rfl
theorem normP_cons (van : Nat → Bool) (c m : Nat) (p : Poly) :
    normP van (.cons c m p) =
      Bool.rec (motive := fun _ => Poly) (Poly.cons c m (normP van p)) (normP van p) (van m) := rfl

theorem collectS_nil (bs : Nat) : collectS bs .nil = .nil := rfl
theorem collectS_cons (bs c m : Nat) (p : Poly) :
    collectS bs (.cons c m p) =
      Bool.rec (motive := fun _ => Poly) Poly.nil
        (Bool.rec (motive := fun _ => Poly) (Poly.cons c (Nat.xor m bs) (collectS bs p))
          (collectS bs p) (Nat.beq (Nat.land m bs) 0))
        (Nat.ble bs m) := rfl

theorem filterS_nil (bs : Nat) : filterS bs .nil = .nil := rfl
theorem filterS_cons (bs c m : Nat) (p : Poly) :
    filterS bs (.cons c m p) =
      Bool.rec (motive := fun _ => Poly) (Poly.cons c m p)
        (Bool.rec (motive := fun _ => Poly) (filterS bs p) (Poly.cons c m (filterS bs p))
          (Nat.beq (Nat.land m bs) 0))
        (Nat.ble bs m) := rfl

/-! ## Main lemmas -/

theorem merge_eval (M : Nat) (hM : M = 2 ^ w) (p q : Poly) :
    evalP w σ (merge M p q) = evalP w σ p + evalP w σ q := by
  induction p generalizing q with
  | nil => rw [merge_nil, evalP_nil]; grind
  | cons c₁ m₁ p₁ ih₁ =>
    induction q with
    | nil => rw [merge_cons_nil, evalP_nil]; grind
    | cons c₂ m₂ q₂ ih₂ =>
      rw [merge_cc]
      cases h1 : Nat.beq m₁ m₂
      · cases h2 : Nat.ble m₂ m₁
        · dsimp only
          rw [evalP_cons, ih₂, evalP_cons, evalP_cons]; grind
        · dsimp only
          rw [evalP_cons, ih₁, evalP_cons, evalP_cons]; grind
      · have hm : m₁ = m₂ := Nat.eq_of_beq_eq_true h1
        subst hm
        cases h2 : Nat.beq (Nat.mod (Nat.add c₁ c₂) M) 0
        · dsimp only
          rw [evalP_cons, ih₁, evalP_cons, evalP_cons, bv_mod M _ hM, bv_add]; grind
        · dsimp only
          have h0 := bv_zero_of_mod M _ hM (Nat.eq_of_beq_eq_true h2)
          rw [bv_add] at h0
          rw [ih₁, evalP_cons, evalP_cons]; grind

theorem single_eval (M : Nat) (hM : M = 2 ^ w) (c m : Nat) :
    evalP w σ (single M c m) = BitVec.ofNat w c * monoVal w σ m := by
  show evalP w σ (Bool.rec (motive := fun _ => Poly) (Poly.cons (Nat.mod c M) m Poly.nil) Poly.nil
    (Nat.beq (Nat.mod c M) 0)) = _
  cases h : Nat.beq (Nat.mod c M) 0
  · dsimp only
    rw [evalP_cons, evalP_nil, bv_mod M c hM]; grind
  · dsimp only
    rw [evalP_nil, bv_zero_of_mod M c hM (Nat.eq_of_beq_eq_true h)]; grind

theorem scaleP_eval (M : Nat) (hM : M = 2 ^ w) (k : Nat) (p : Poly) :
    evalP w σ (scaleP M k p) = BitVec.ofNat w k * evalP w σ p := by
  induction p with
  | nil => rw [scaleP_nil, evalP_nil]; grind
  | cons c m p ih =>
    rw [scaleP_cons]
    cases h : Nat.beq (Nat.mod (Nat.mul k c) M) 0
    · dsimp only
      rw [evalP_cons, evalP_cons, ih, bv_mod M _ hM, bv_mul]; grind
    · dsimp only
      have h0 := bv_zero_of_mod M _ hM (Nat.eq_of_beq_eq_true h)
      rw [bv_mul] at h0
      rw [evalP_cons, ih]; grind

theorem foldM_eval (M : Nat) (hM : M = 2 ^ w) (ps : List Poly) :
    evalP w σ (foldM M ps) = evalL w σ ps := by
  induction ps with
  | nil => rfl
  | cons a t ih => rw [foldM_cons, merge_eval M hM, ih, evalL_cons]

theorem pairs_eval (M : Nat) (hM : M = 2 ^ w) (ps : List Poly) (pend : Option Poly) :
    evalL w σ (pairs M ps pend) = optV w σ pend + evalL w σ ps := by
  induction ps generalizing pend with
  | nil =>
    cases pend with
    | none => rw [pairs_nil_none]; simp [optV, evalL_nil]
    | some p => rw [pairs_nil_some, evalL_cons, evalL_nil]; simp [optV]
  | cons a t ih =>
    cases pend with
    | none => rw [pairs_cons_none, ih, evalL_cons]; simp [optV]
    | some p =>
      rw [pairs_cons_some, evalL_cons, ih, merge_eval M hM, evalL_cons]; simp [optV]; grind

theorem sumGo_eval (M : Nat) (hM : M = 2 ^ w) (n : Nat) (ps : List Poly) :
    evalP w σ (sumGo M n ps) = evalL w σ ps := by
  induction n generalizing ps with
  | zero => rw [sumGo_zero, foldM_eval M hM]
  | succ n ih =>
    match ps with
    | [] => rfl
    | [a] => rw [sumGo_succ_one, evalL_cons, evalL_nil]; grind
    | a :: b :: t => rw [sumGo_succ_two, ih, pairs_eval M hM]; simp [optV]

theorem sumB_eval (M : Nat) (hM : M = 2 ^ w) (ps : List Poly) :
    evalP w σ (sumB M ps) = evalL w σ ps := sumGo_eval M hM 64 ps

theorem mulTerm_eval (M : Nat) (hM : M = 2 ^ w) (van : Nat → Bool) (hv : VanOk w σ van)
    (c m : Nat) (R : Poly) (acc : List Poly) :
    evalL w σ (mulTerm M van c m R acc) =
      BitVec.ofNat w c * monoVal w σ m * evalP w σ R + evalL w σ acc := by
  induction R with
  | nil => rw [mulTerm_nil, evalP_nil]; grind
  | cons c' m' R ih =>
    rw [mulTerm_cons]
    cases h : Nat.beq (Nat.mod (Nat.mul c c') M) 0
    · cases hvm : van (Nat.lor m m')
      · dsimp only
        rw [evalL_cons, ih, evalP_cons, evalP_cons, evalP_nil, bv_mod M _ hM, bv_mul,
          monoVal_lor]
        grind
      · dsimp only
        have h0 := hv _ hvm
        rw [monoVal_lor] at h0
        rw [ih, evalP_cons]; grind
    · dsimp only
      have h0 := bv_zero_of_mod M _ hM (Nat.eq_of_beq_eq_true h)
      rw [bv_mul] at h0
      rw [ih, evalP_cons]; grind

theorem mulTerms_eval (M : Nat) (hM : M = 2 ^ w) (van : Nat → Bool) (hv : VanOk w σ van)
    (W R : Poly) : evalL w σ (mulTerms M van W R) = evalP w σ W * evalP w σ R := by
  induction W with
  | nil => rw [mulTerms_nil, evalL_nil, evalP_nil]; grind
  | cons c m W ih => rw [mulTerms_cons, mulTerm_eval M hM van hv, ih, evalP_cons]; grind

theorem noVan_ok : VanOk w σ noVan := by
  intro m h
  exact absurd h Bool.false_ne_true

theorem mulP_eval (M : Nat) (hM : M = 2 ^ w) (p q : Poly) :
    evalP w σ (mulP M p q) = evalP w σ p * evalP w σ q := by
  show evalP w σ (sumB M (mulTerms M noVan p q)) = _
  rw [sumB_eval M hM, mulTerms_eval M hM noVan noVan_ok]

theorem normP_eval (van : Nat → Bool) (hv : VanOk w σ van) (p : Poly) :
    evalP w σ (normP van p) = evalP w σ p := by
  induction p with
  | nil => rfl
  | cons c m p ih =>
    rw [normP_cons]
    cases h : van m
    · dsimp only; rw [evalP_cons, evalP_cons, ih]
    · dsimp only; rw [ih, evalP_cons, hv m h]; grind

theorem testBit_of_land_ne (m s : Nat) (h : Nat.land m (Nat.pow 2 s) ≠ 0) : m.testBit s = true := by
  cases hb : m.testBit s
  · exfalso; apply h
    apply Nat.eq_of_testBit_eq
    intro i
    show (m &&& 2 ^ s).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : s = i
    · subst hi; simp [hb]
    · simp [hi]
  · rfl

theorem split_eval (s : Nat) (P : Poly) :
    evalP w σ P = evalP w σ (filterS (Nat.pow 2 s) P) +
      bv w (σ s) * evalP w σ (collectS (Nat.pow 2 s) P) := by
  induction P with
  | nil => rw [filterS_nil, collectS_nil, evalP_nil]; grind
  | cons c m p ih =>
    rw [filterS_cons, collectS_cons]
    cases h1 : Nat.ble (Nat.pow 2 s) m
    · dsimp only; rw [evalP_nil]; grind
    · cases h2 : Nat.beq (Nat.land m (Nat.pow 2 s)) 0
      · dsimp only
        have hb := testBit_of_land_ne m s (Nat.ne_of_beq_eq_false h2)
        rw [evalP_cons, evalP_cons, ih, monoVal_split m s hb]; grind
      · dsimp only
        rw [evalP_cons, evalP_cons, ih]; grind

/-- the SUBST step preserves the value when `σ s = value of R`. -/
theorem substP_eval (M : Nat) (hM : M = 2 ^ w) (van : Nat → Bool) (hv : VanOk w σ van)
    (s : Nat) (R P : Poly) (hR : bv w (σ s) = evalP w σ R) :
    evalP w σ (substP M van s R P) = evalP w σ P := by
  show evalP w σ (merge M (sumB M (mulTerms M van (collectS (Nat.pow 2 s) P) R))
    (filterS (Nat.pow 2 s) P)) = _
  rw [merge_eval M hM, sumB_eval M hM, mulTerms_eval M hM van hv, split_eval (w := w) (σ := σ) s P,
    ← hR]
  grind

theorem oneSub_eval (M : Nat) (hM : M = 2 ^ w) (R : Poly) :
    evalP w σ (oneSub M R) = 1 - evalP w σ R := by
  show evalP w σ (merge M (scaleP M (Nat.sub M 1) R) (single M 1 0)) = _
  rw [merge_eval M hM, scaleP_eval M hM, single_eval M hM, bv_pred M hM, monoVal_zero, bv_one]
  grind

theorem litP_eval (M : Nat) (hM : M = 2 ^ w) (neg : Bool) (s : Nat) :
    evalP w σ (litP M neg s) = if neg then 1 - bv w (σ s) else bv w (σ s) := by
  cases neg
  · show evalP w σ (single M 1 (Nat.pow 2 s)) = _
    rw [single_eval M hM, monoVal_pow, bv_one]; simp
  · show evalP w σ (oneSub M (single M 1 (Nat.pow 2 s))) = _
    rw [oneSub_eval M hM, single_eval M hM, monoVal_pow, bv_one]; simp

theorem isNil_eval (p : Poly) (h : isNil p = true) : evalP w σ p = 0 := by
  cases p with
  | nil => rfl
  | cons c m q => exact absurd h Bool.false_ne_true

theorem land_eq_self_iff (m S : Nat) :
    Nat.land m S = m ↔ ∀ i, m.testBit i = true → S.testBit i = true := by
  show m &&& S = m ↔ _
  constructor
  · intro h i hi
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hm : m.testBit i
    · rfl
    · rw [h i hm]; rfl

/-- kernel evaluation at the bitset assignment `TS` agrees with `evalP` when every monomial is
inside `S` and `TS` agrees with `σ` on `S`. -/
theorem evalK_eval (M : Nat) (hM : M = 2 ^ w) (S TS : Nat) (p : Poly)
    (hsub : subAll S p = true) (hag : ∀ i, S.testBit i = true → TS.testBit i = σ i) :
    BitVec.ofNat w (evalK M TS p) = evalP w σ p := by
  induction p with
  | nil => rfl
  | cons c m p ih =>
    have hsub' : Bool.rec (motive := fun _ => Bool) false (subAll S p)
        (Nat.beq (Nat.land m S) m) = true := hsub
    cases hb : Nat.beq (Nat.land m S) m
    · rw [hb] at hsub'; exact absurd hsub' Bool.false_ne_true
    · rw [hb] at hsub'
      have hmS := (land_eq_self_iff m S).1 (Nat.eq_of_beq_eq_true hb)
      have ih' := ih hsub'
      show BitVec.ofNat w (Nat.mod (Nat.add (Bool.rec (motive := fun _ => Nat) 0 c
        (Nat.beq (Nat.land m TS) m)) (evalK M TS p)) M) = _
      rw [bv_mod M _ hM, bv_add, ih', evalP_cons]
      congr 1
      have hiff : Nat.land m TS = m ↔ MonoTrue σ m := by
        rw [land_eq_self_iff]
        constructor
        · intro h i hi; rw [← hag i (hmS i hi)]; exact h i hi
        · intro h i hi; rw [hag i (hmS i hi)]; exact h i hi
      cases ht : Nat.beq (Nat.land m TS) m
      · dsimp only
        rw [monoVal_false m (fun h => Nat.ne_of_beq_eq_false ht (hiff.2 h))]; grind
      · dsimp only
        rw [monoVal_true m (hiff.1 (Nat.eq_of_beq_eq_true ht))]; grind

end

end LeanQbe.T.Examples.Arisca
