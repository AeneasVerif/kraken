module

public import LeanQbe.T.Examples.Arisca.ArtSoundPoly

/-!
# Auxiliary soundness lemmas for the ART checker: vanishing pairs, flips, rule validation,
initial polynomial.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca

@[expose] public section

/-- registered HA pairs are never both true -/
def PairsOk (σ : Nat → Bool) (P : Pairs) : Prop :=
  ∀ c s, P.pt.get P.d c = some s → ¬ (σ (2 * c) = true ∧ σ (2 * s) = true)

/-- `vanGo` with the `ilog` hint abstracted (keeps `ilog` away from `Nat` literal reduction,
which is exponential on a symbolic argument). -/
noncomputable def vanGoI (P : Pairs) (m : Nat) (I : Nat → Nat) (fuel : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih T =>
      Bool.rec
        (Bool.rec (ih (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1)))))
          true
          (pairHit P m (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)))
        false (Nat.beq T 0))
    fuel

/-- `flipR` with the `ilog` hint abstracted. -/
noncomputable def flipRI (M : Nat) (I : Nat → Nat) (fuel : Nat) : Nat → Poly → Poly :=
  Nat.rec (motive := fun _ => Nat → Poly → Poly) (fun _ R => R)
    (fun _ ih T R =>
      Bool.rec
        (ih (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1))))
          (substP M noVan (Nat.mul 2 (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1))
            (oneSub M (single M 1 (Nat.pow 2 (Nat.add (Nat.mul 2
              (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)) 1)))) R))
        R (Nat.beq T 0))
    fuel

/-- the row loop of `validate` -/
noncomputable def valRows (M : Nat) (env : List (Nat × Nat)) (Q : Poly) (tab : Nat) (rows : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => Bool.rec false ih
      (Nat.beq (evalK M (tset env t) Q) (Nat.land (Nat.shiftRight tab t) 1)))
    rows

/-- `Σ_j 2^(j0+j) · (σ(2·net_j) ⊕ neg_j)` for out_ref words `net<<1|neg` -/
noncomputable def outSum (w : Nat) (σ : Nat → Bool) : List Nat → Nat → BitVec w
  | [], _ => 0
  | r :: rs, j =>
    BitVec.ofNat w (2 ^ j) * bv w (σ (2 * (r / 2)) ^^ (r % 2 == 1)) + outSum w σ rs (j + 1)

/-- `Σ_i c_i · σ(2·x_i)`, `c_i = 2^i` except `-2^i` for the top bit `i = n-1` when signed -/
noncomputable def inSum (w : Nat) (σ : Nat → Bool) (signed : Bool) (n : Nat) :
    List Nat → Nat → BitVec w
  | [], _ => 0
  | x :: xs, i =>
    (if signed = true ∧ i + 1 = n then - BitVec.ofNat w (2 ^ i) else BitVec.ofNat w (2 ^ i)) *
      bv w (σ (2 * x)) + inSum w σ signed n xs (i + 1)

/-- `woTerms` from a given start weight -/
noncomputable def woFrom (M : Nat) (refs : List Nat) : Nat → List Poly :=
  List.rec (motive := fun _ => Nat → List Poly) (fun _ => [])
    (fun r _ ih j =>
      scaleP M (Nat.pow 2 j) (litP M (Nat.beq (Nat.land r 1) 1) (Nat.mul 2 (Nat.shiftRight r 1)))
        :: ih (Nat.succ j))
    refs

/-- `Σ c·m` over weighted terms -/
noncomputable def wSum (w : Nat) (σ : Nat → Bool) (A : List (Nat × Nat)) : BitVec w :=
  A.foldr (fun a acc => BitVec.ofNat w a.1 * monoVal w σ a.2 + acc) 0

/-- one row of `prodTerms` -/
noncomputable def prodRow (M : Nat) (a : Nat × Nat) (tail : List Poly) (B : List (Nat × Nat)) :
    List Poly :=
  List.rec (motive := fun _ => List Poly) tail
    (fun b _ ih' => single M (negC M (Nat.mul a.1 b.1)) (Nat.lor a.2 b.2) :: ih') B

/-- `wTerms` from a given start index -/
noncomputable def wFrom (M : Nat) (signed : Bool) (n : Nat) (nets : List Nat) :
    Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih i =>
      (Bool.rec (Nat.pow 2 i)
        (Bool.rec (Nat.pow 2 i) (negC M (Nat.pow 2 i)) (Nat.beq (Nat.succ i) n))
        signed, Nat.pow 2 (Nat.mul 2 x)) :: ih (Nat.succ i))
    nets

end

public section

variable {w : Nat} {σ : Nat → Bool}

/-! ## Vanishing pairs -/

theorem pairHit_spec (P : Pairs) (m c : Nat) (h : pairHit P m c = true) :
    ∃ s, P.pt.get P.d c = some s ∧ m.testBit (2 * c) = true ∧ m.testBit (2 * s) = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Option.rec (motive := fun _ => Bool) false (fun s => tb m (Nat.mul 2 s)) (P.pt.get P.d c))
      (tb m (Nat.mul 2 c)) = true := h
  cases hc : tb m (Nat.mul 2 c)
  · rw [hc] at h'; exact absurd h' Bool.false_ne_true
  · rw [hc] at h'
    cases hg : P.pt.get P.d c with
    | none => rw [hg] at h'; exact absurd h' Bool.false_ne_true
    | some s =>
      rw [hg] at h'
      refine ⟨s, rfl, ?_, ?_⟩
      · rw [← tb_eq]; exact hc
      · rw [← tb_eq]; exact h'

theorem vanGoI_succ (P : Pairs) (m : Nat) (I : Nat → Nat) (n T : Nat) :
    vanGoI P m I (n + 1) T =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (vanGoI P m I n (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1)))))
          true
          (pairHit P m (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)))
        false (Nat.beq T 0) := rfl

theorem vanGoI_spec (P : Pairs) (m : Nat) (I : Nat → Nat) (fuel : Nat) :
    ∀ T, vanGoI P m I fuel T = true → ∃ c, pairHit P m c = true := by
  induction fuel with
  | zero => intro T h; exact absurd h Bool.false_ne_true
  | succ n ih =>
    intro T h
    rw [vanGoI_succ] at h
    cases h0 : Nat.beq T 0
    · rw [h0] at h
      cases hp : pairHit P m (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)
      · rw [hp] at h; exact ih _ h
      · exact ⟨_, hp⟩
    · rw [h0] at h; exact absurd h Bool.false_ne_true

theorem van_ok (P : Pairs) (h : PairsOk σ P) : VanOk w σ (van P) := by
  intro m hm
  have hm' : vanGoI P m ilog 64 (Nat.land m P.pc) = true := hm
  obtain ⟨c, hc⟩ := vanGoI_spec P m ilog 64 _ hm'
  obtain ⟨s, hg, h1, h2⟩ := pairHit_spec P m c hc
  apply monoVal_false
  intro hmt
  exact h c s hg ⟨hmt _ h1, hmt _ h2⟩

/-! ## Flips -/

theorem flipPoly_eval (M : Nat) (hM : M = 2 ^ w) (hflip : ∀ x, σ (2 * x + 1) = !σ (2 * x))
    (v : Nat) :
    evalP w σ (oneSub M (single M 1 (Nat.pow 2 (Nat.add (Nat.mul 2 v) 1)))) =
      bv w (σ (Nat.mul 2 v)) := by
  rw [oneSub_eval M hM, single_eval M hM, monoVal_pow, bv_one]
  show 1 - 1 * bv w (σ (2 * v + 1)) = bv w (σ (2 * v))
  rw [hflip v]
  cases σ (2 * v) <;> simp [bv]

theorem flipRI_succ (M : Nat) (I : Nat → Nat) (n T : Nat) (R : Poly) :
    flipRI M I (n + 1) T R =
      Bool.rec (motive := fun _ => Poly)
        (flipRI M I n (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1))))
          (substP M noVan (Nat.mul 2 (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1))
            (oneSub M (single M 1 (Nat.pow 2 (Nat.add (Nat.mul 2
              (Nat.shiftRight (I (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)) 1)))) R))
        R (Nat.beq T 0) := rfl

theorem flipRI_eval (M : Nat) (hM : M = 2 ^ w) (hflip : ∀ x, σ (2 * x + 1) = !σ (2 * x))
    (I : Nat → Nat) (fuel T : Nat) (R : Poly) : evalP w σ (flipRI M I fuel T R) = evalP w σ R := by
  induction fuel generalizing T R with
  | zero => rfl
  | succ n ih =>
    rw [flipRI_succ]
    cases Nat.beq T 0
    · dsimp only
      rw [ih, substP_eval M hM noVan noVan_ok _ _ _ (flipPoly_eval M hM hflip _).symm]
    · rfl

theorem flipR_eval (M : Nat) (hM : M = 2 ^ w) (hflip : ∀ x, σ (2 * x + 1) = !σ (2 * x))
    (fuel T : Nat) (R : Poly) : evalP w σ (flipR M fuel T R) = evalP w σ R :=
  flipRI_eval M hM hflip ilog fuel T R

/-! ## Rule validation -/

theorem tset_bit (env : List (Nat × Nat)) (t : Nat)
    (henv : ∀ x ∈ env, x.2.testBit t = σ x.1) (i : Nat) :
    (tset env t).testBit i = ((sAll env).testBit i && σ i) := by
  induction env with
  | nil => show (0 : Nat).testBit i = ((0 : Nat).testBit i && σ i); simp
  | cons a env ih =>
    have ha := henv a (by simp)
    have ih' := ih (fun x hx => henv x (by simp [hx]))
    show (Bool.rec (motive := fun _ => Nat) 0 (2 ^ a.1) (tb a.2 t) ||| tset env t).testBit i =
      ((2 ^ a.1 ||| sAll env).testBit i && σ i)
    rw [Nat.testBit_or, Nat.testBit_or, ih', Nat.testBit_two_pow]
    rw [tb_eq, ha]
    cases hb : σ a.1
    · dsimp only
      rw [Nat.zero_testBit]
      by_cases hi : a.1 = i
      · subst hi; simp [hb]
      · simp [hi]
    · dsimp only
      rw [Nat.testBit_two_pow]
      by_cases hi : a.1 = i
      · subst hi; simp [hb]
      · simp [hi]

theorem tset_agree (env : List (Nat × Nat)) (t : Nat)
    (henv : ∀ x ∈ env, x.2.testBit t = σ x.1) (i : Nat) (hi : (sAll env).testBit i = true) :
    (tset env t).testBit i = σ i := by
  rw [tset_bit env t henv i, hi]; rfl

theorem validate_eq (M : Nat) (env : List (Nat × Nat)) (rows : Nat) (Q : Poly) (tab : Nat) :
    validate M env rows Q tab =
      Bool.rec (motive := fun _ => Bool) false (valRows M env Q tab rows) (subAll (sAll env) Q) :=
  rfl

theorem valRows_succ (M : Nat) (env : List (Nat × Nat)) (Q : Poly) (tab n : Nat) :
    valRows M env Q tab (n + 1) =
      Bool.rec (motive := fun _ => Bool) false (valRows M env Q tab n)
        (Nat.beq (evalK M (tset env n) Q) (Nat.land (Nat.shiftRight tab n) 1)) := rfl

theorem valRows_spec (M : Nat) (env : List (Nat × Nat)) (Q : Poly) (tab rows : Nat)
    (h : valRows M env Q tab rows = true) :
    ∀ t, t < rows → evalK M (tset env t) Q = Nat.land (Nat.shiftRight tab t) 1 := by
  induction rows with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ n ih =>
    intro t ht
    rw [valRows_succ] at h
    cases hb : Nat.beq (evalK M (tset env n) Q) (Nat.land (Nat.shiftRight tab n) 1)
    · rw [hb] at h; exact absurd h Bool.false_ne_true
    · rw [hb] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | ht'
      · exact ih h t ht'
      · subst ht'; exact Nat.eq_of_beq_eq_true hb

theorem validate_ok (M : Nat) (hM : M = 2 ^ w) (env : List (Nat × Nat)) (rows : Nat) (Q : Poly)
    (tab : Nat) (h : validate M env rows Q tab = true) (t : Nat) (ht : t < rows)
    (henv : ∀ x ∈ env, x.2.testBit t = σ x.1) : evalP w σ Q = bv w (tab.testBit t) := by
  rw [validate_eq] at h
  cases hs : subAll (sAll env) Q
  · rw [hs] at h; exact absurd h Bool.false_ne_true
  · rw [hs] at h
    have hk := evalK_eval M hM (sAll env) (tset env t) Q hs
      (fun i hi => tset_agree env t henv i hi)
    rw [← hk, valRows_spec M env Q tab rows h t ht, ← tb_eq]
    show BitVec.ofNat w (Nat.land (Nat.shiftRight tab t) 1) =
      bv w (Nat.beq (Nat.land (Nat.shiftRight tab t) 1) 1)
    have h01 : Nat.land (Nat.shiftRight tab t) 1 = 0 ∨ Nat.land (Nat.shiftRight tab t) 1 = 1 := by
      show (tab >>> t) &&& 1 = 0 ∨ (tab >>> t) &&& 1 = 1
      rw [Nat.and_one_is_mod]; exact Nat.mod_two_eq_zero_or_one _
    rcases h01 with h0 | h0 <;> rw [h0] <;> rfl

theorem xmask_bit (j t : Nat) (hj : j < 6) (ht : t < 64) : (xmask j).testBit t = t.testBit j := by
  have H : ∀ j, j < 6 → ∀ t, t < 64 → (xmask j).testBit t = t.testBit j := by decide +kernel
  exact H j hj t ht

/-! ## Initial polynomial -/

theorem evalL_append (l₁ l₂ : List Poly) :
    evalL w σ (l₁ ++ l₂) = evalL w σ l₁ + evalL w σ l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, evalL_nil]; grind
  | cons a t ih => rw [List.cons_append, evalL_cons, evalL_cons, ih]; grind

theorem woTerms_eq (M : Nat) (refs : List Nat) : woTerms M refs = woFrom M refs 0 := rfl

theorem woFrom_cons (M r : Nat) (rs : List Nat) (j : Nat) :
    woFrom M (r :: rs) j =
      scaleP M (Nat.pow 2 j) (litP M (Nat.beq (Nat.land r 1) 1) (Nat.mul 2 (Nat.shiftRight r 1)))
        :: woFrom M rs (j + 1) := rfl

theorem woFrom_eval (M : Nat) (hM : M = 2 ^ w) (refs : List Nat) (j : Nat) :
    evalL w σ (woFrom M refs j) = outSum w σ refs j := by
  induction refs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [woFrom_cons, evalL_cons, ih, scaleP_eval M hM, litP_eval M hM]
    simp only [outSum]
    have hs : Nat.mul 2 (Nat.shiftRight r 1) = 2 * (r / 2) := by
      show 2 * (r >>> 1) = 2 * (r / 2)
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hl : Nat.land r 1 = r % 2 := Nat.and_one_is_mod r
    rw [hs, hl]
    show BitVec.ofNat w (2 ^ j) * _ + _ = _
    have e0 : Nat.beq 0 1 = false := rfl
    have e1 : Nat.beq 1 1 = true := rfl
    rcases Nat.mod_two_eq_zero_or_one r with h | h <;> rw [h] <;> cases σ (2 * (r / 2)) <;>
      simp [bv, e0]

theorem wSum_nil : wSum w σ [] = 0 := rfl
theorem wSum_cons (a : Nat × Nat) (A : List (Nat × Nat)) :
    wSum w σ (a :: A) = BitVec.ofNat w a.1 * monoVal w σ a.2 + wSum w σ A := rfl

theorem prodRow_cons (M : Nat) (a : Nat × Nat) (tail : List Poly) (b : Nat × Nat)
    (B : List (Nat × Nat)) :
    prodRow M a tail (b :: B) =
      single M (negC M (Nat.mul a.1 b.1)) (Nat.lor a.2 b.2) :: prodRow M a tail B := rfl

theorem prodTerms_cons (M : Nat) (a : Nat × Nat) (A B : List (Nat × Nat)) :
    prodTerms M (a :: A) B = prodRow M a (prodTerms M A B) B := rfl

theorem prodRow_eval (M : Nat) (hM : M = 2 ^ w) (a : Nat × Nat) (tail : List Poly)
    (B : List (Nat × Nat)) :
    evalL w σ (prodRow M a tail B) =
      -(BitVec.ofNat w a.1 * monoVal w σ a.2) * wSum w σ B + evalL w σ tail := by
  induction B with
  | nil => show evalL w σ tail = _; rw [wSum_nil]; grind
  | cons b B ih =>
    rw [prodRow_cons, evalL_cons, ih, single_eval M hM, negC_ofNat M _ hM, bv_mul, monoVal_lor,
      wSum_cons]
    grind

theorem prodTerms_eval (M : Nat) (hM : M = 2 ^ w) (A B : List (Nat × Nat)) :
    evalL w σ (prodTerms M A B) = -(wSum w σ A * wSum w σ B) := by
  induction A with
  | nil => show (0 : BitVec w) = _; rw [wSum_nil]; grind
  | cons a A ih => rw [prodTerms_cons, prodRow_eval M hM, ih, wSum_cons]; grind

theorem wTerms_eq (M : Nat) (signed : Bool) (n : Nat) (nets : List Nat) :
    wTerms M signed n nets = wFrom M signed n nets 0 := rfl

theorem wFrom_cons (M : Nat) (signed : Bool) (n x : Nat) (xs : List Nat) (i : Nat) :
    wFrom M signed n (x :: xs) i =
      (Bool.rec (motive := fun _ => Nat) (Nat.pow 2 i)
        (Bool.rec (motive := fun _ => Nat) (Nat.pow 2 i) (negC M (Nat.pow 2 i))
          (Nat.beq (Nat.succ i) n)) signed,
        Nat.pow 2 (Nat.mul 2 x)) :: wFrom M signed n xs (i + 1) := rfl

theorem wFrom_eval (M : Nat) (hM : M = 2 ^ w) (signed : Bool) (n : Nat) (xs : List Nat) (i : Nat) :
    wSum w σ (wFrom M signed n xs i) = inSum w σ signed n xs i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    rw [wFrom_cons, wSum_cons, ih]
    simp only [inSum]
    rw [monoVal_pow]
    show _ * bv w (σ (2 * x)) + _ = _
    congr 2
    cases signed
    · show BitVec.ofNat w (2 ^ i) = _
      simp
    · cases hb : Nat.beq (Nat.succ i) n
      · have hne : ¬ (i + 1 = n) := Nat.ne_of_beq_eq_false hb
        show BitVec.ofNat w (2 ^ i) = _
        simp [hne]
      · have heq : i + 1 = n := Nat.eq_of_beq_eq_true hb
        show BitVec.ofNat w (negC M (2 ^ i)) = _
        rw [negC_ofNat M _ hM]
        simp [heq]

theorem initP_eval (M : Nat) (hM : M = 2 ^ w) (pr : Pairs) (hv : VanOk w σ (van pr))
    (signed : Bool) (n : Nat) (inNet outRef : List Nat) :
    evalP w σ (initP M pr signed n inNet outRef) =
      outSum w σ outRef 0 -
        inSum w σ signed n (takeN n inNet) 0 * inSum w σ signed n (dropN n inNet) 0 := by
  show evalP w σ (normP (van pr) (sumB M (woTerms M outRef ++
    prodTerms M (wTerms M signed n (takeN n inNet)) (wTerms M signed n (dropN n inNet))))) = _
  rw [normP_eval _ hv, sumB_eval M hM, evalL_append, woTerms_eq, woFrom_eval M hM,
    prodTerms_eval M hM, wTerms_eq, wTerms_eq, wFrom_eval M hM, wFrom_eval M hM]
  grind

end

end LeanQbe.T.Examples.Arisca
