module

public import LeanQbe.T.CondThreadOpt
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
public import LeanQbe.T.Module
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.FoldLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Soundness Proofs for `CondThreadOpt` — Part 0 (`pathCondOpt` WP & Bit/Arg Relations)

Proves `PEnv` / `SymBits` / `cmpImplies` / `cmpConstImplies` / `factImpliesCmpBits` /
`FactsOk` / `PInfoOk` / `PGood` invariants, `pcStep_wp`, `pathCondOpt_wp`, and `pcCmpBitsSym_rel`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open CondThreadOpt

namespace CondThreadOptImpl

/-! ## Part 1: Soundness of `pathCondOpt` -/

/-! ### Identity environment and symbolic key evaluation -/

/-- Identity valuation environment for `pathCondOpt`. -/
abbrev PEnv : Type := Nat → Option ((t : Ty) × Val t)

@[expose] def PEnv.upd (ρ : PEnv) {t : Ty} (b : Nat) (v : Val t) : PEnv :=
  fun k => if k = b then some ⟨t, v⟩ else ρ k

@[expose] def PEnv.updTup (ρ : PEnv) (b : Nat) : {ts : List Ty} → Tup Val ts → PEnv
  | [], () => ρ
  | _ :: _, (x, xs) => PEnv.updTup (PEnv.upd ρ b x) (b + 1) xs

theorem PEnv.upd_eq (ρ : PEnv) {t : Ty} (b : Nat) (v : Val t) :
    PEnv.upd ρ b v b = some ⟨t, v⟩ := by
  simp [PEnv.upd]

theorem PEnv.upd_ne (ρ : PEnv) {t : Ty} {b k : Nat} (v : Val t) (h : k ≠ b) :
    PEnv.upd ρ b v k = ρ k := by
  simp [PEnv.upd, h]

theorem PEnv.updTup_lt (ρ : PEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → {b k : Nat} → k < b → PEnv.updTup ρ b xs k = ρ k
  | [], (), _, _, _ => rfl
  | _ :: _, (x, xs), b, k, hk => by
    dsimp only [PEnv.updTup]
    rw [PEnv.updTup_lt (PEnv.upd ρ b x) xs (by omega)]
    exact PEnv.upd_ne ρ x (by omega)

@[expose] def FKey.InScope (b : Nat) : {t : Ty} → FKey t → Prop
  | _, .imm _ => True
  | _, .var i => i < b

@[expose] def FKey.eval (ρ : PEnv) : {t : Ty} → FKey t → Option (Val t)
  | _, .imm c => some c
  | t, .var i =>
    match ρ i with
    | some ⟨t', v⟩ => castTy t' t v
    | none => none

@[expose] def SymBits.InScope (b : Nat) : {w : Nat} → SymBits w → Prop
  | _, .fkey k => FKey.InScope b k
  | _, .ext _ _ _ _ k => FKey.InScope b k

@[expose] def SymBits.eval (ρ : PEnv) : {w : Nat} → SymBits w → Option (BitVec w)
  | _, .fkey k => FKey.eval ρ k
  | _, .ext .zext _ w _ k => (FKey.eval ρ k).map (·.setWidth w)
  | _, .ext .sext _ w _ k => (FKey.eval ρ k).map (·.signExtend w)

theorem FKey.InScope.mono {b₁ b₂ : Nat} (hb : b₁ ≤ b₂) {t : Ty} :
    {k : FKey t} → FKey.InScope b₁ k → FKey.InScope b₂ k
  | .imm _, _ => trivial
  | .var _, hk => Nat.lt_of_lt_of_le hk hb

theorem SymBits.InScope.mono {b₁ b₂ : Nat} (hb : b₁ ≤ b₂) {w : Nat} :
    {s : SymBits w} → SymBits.InScope b₁ s → SymBits.InScope b₂ s
  | .fkey _k, hk => FKey.InScope.mono hb hk
  | .ext _ _ _ _ _k, hk => FKey.InScope.mono hb hk

theorem FKey.eval_mono {ρ ρ' : PEnv} {b : Nat} (hρ : ∀ k, k < b → ρ' k = ρ k) {t : Ty} :
    {k : FKey t} → FKey.InScope b k → FKey.eval ρ' k = FKey.eval ρ k
  | .imm _, _ => rfl
  | .var i, hk => by dsimp only [FKey.eval]; rw [hρ i hk]

theorem SymBits.eval_mono {ρ ρ' : PEnv} {b : Nat} (hρ : ∀ k, k < b → ρ' k = ρ k) {w : Nat} :
    {s : SymBits w} → SymBits.InScope b s → SymBits.eval ρ' s = SymBits.eval ρ s
  | .fkey k, hk => FKey.eval_mono hρ hk
  | .ext .zext _ _ _ k, hk => by dsimp only [SymBits.eval]; rw [FKey.eval_mono hρ hk]
  | .ext .sext _ _ _ k, hk => by dsimp only [SymBits.eval]; rw [FKey.eval_mono hρ hk]

theorem symBitsBeq_eq {w : Nat} : {x y : SymBits w} → symBitsBeq x y = true → x = y
  | .fkey k₁, .fkey k₂, h => by
    dsimp only [symBitsBeq] at h
    rw [fKeyBeq_iff_eq.mp h]
  | .ext k₁ m₁ _ h₁ s₁, .ext k₂ m₂ _ h₂ s₂, h => by
    dsimp only [symBitsBeq] at h
    split at h
    · next he =>
      rcases he with ⟨rfl, rfl⟩
      have hs : s₁ = s₂ := fKeyBeq_iff_eq.mp h
      subst hs
      rfl
    · cases h
  | .fkey _, .ext _ _ _ _ _, h | .ext _ _ _ _ _, .fkey _, h => by
    dsimp only [symBitsBeq] at h; cases h

theorem castTy_self {V : Ty → Type} : (t : Ty) → (v : V t) → castTy t t v = some v
  | .bool, _ => rfl
  | .bits _, _ => by dsimp only [castTy]; simp
  | .float _, _ => by dsimp only [castTy]; simp
  | .pair a b, v => by
    dsimp only [castTy]
    cases ha : tyDecEq a a with
    | isFalse hne => exact absurd rfl hne
    | isTrue ea =>
      cases hb : tyDecEq b b with
      | isFalse hne => exact absurd rfl hne
      | isTrue eb => cases ea; cases eb; rfl

/-! ### Comparison implication soundness -/

theorem cmpImplies_bits_sound (o₁ o₂ : CmpOp) (b : Bool) :
    cmpImplies o₁ o₂ = some b →
    ∀ {w : Nat} (x y : BitVec w), CmpOp.evalBits o₁ x y = true → CmpOp.evalBits o₂ x y = b := by
  intro h w x y hxy
  dsimp only [cmpImplies] at h
  by_cases heq : (o₁ == o₂) = true
  · simp only [heq, ↓reduceIte, Option.some.injEq] at h
    cases h; rw [beq_iff_eq.mp heq] at hxy; exact hxy
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hneg : (o₁ == o₂.neg) = true
    · simp only [hneg, ↓reduceIte, Option.some.injEq] at h; cases h
      have hne := beq_iff_eq.mp hneg
      rw [hne, CmpOp.neg_evalBits] at hxy
      simpa using hxy
    · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at h
      cases o₁ <;> cases o₂ <;> dsimp only at h <;> try cases h
      all_goals
        simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
          decide_eq_true_eq, decide_eq_false_iff_not] at hxy ⊢
        first
        | (subst hxy; simp)
        | omega
        | (intro h'; subst h'; omega)

theorem cmpImplies_bool_sound (o₁ o₂ : CmpOp) (b : Bool) :
    cmpImplies o₁ o₂ = some b →
    ∀ (x y : Bool), CmpOp.evalBool o₁ x y = true → CmpOp.evalBool o₂ x y = b := by
  intro h x y hxy
  cases o₁ <;> cases o₂ <;> cases b <;>
    first
    | (exfalso; revert h; decide)
    | (cases x <;> cases y <;> simp_all [CmpOp.evalBool])

private theorem uUpper?_sound {n : Nat} {o : CmpOp} {c : BitVec n} {u : Nat}
    (h : uUpper? o c = some u) {x : BitVec n} (hx : CmpOp.evalBits o x c = true) :
    x.toNat ≤ u := by
  cases o with
  | ult =>
    dsimp only [uUpper?] at h
    split at h <;> cases h
    simp only [CmpOp.evalBits, BitVec.ult, decide_eq_true_eq] at hx; omega
  | ule =>
    dsimp only [uUpper?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.ule, decide_eq_true_eq] at hx; exact hx
  | _ => cases h

private theorem uLower?_sound {n : Nat} {o : CmpOp} {c : BitVec n} {l : Nat}
    (h : uLower? o c = some l) {x : BitVec n} (hx : CmpOp.evalBits o x c = true) :
    l ≤ x.toNat := by
  cases o with
  | ne =>
    dsimp only [uLower?] at h
    split at h
    · next hc0 =>
      cases h
      have hc0' : c = 0#n := beq_iff_eq.mp hc0
      subst hc0'
      simp only [CmpOp.evalBits, decide_eq_true_eq] at hx
      have hn : x.toNat ≠ 0 := by intro h0; apply hx; apply BitVec.eq_of_toNat_eq; simpa using h0
      omega
    · cases h
  | ugt =>
    dsimp only [uLower?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.ult, decide_eq_true_eq] at hx; omega
  | uge =>
    dsimp only [uLower?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.ule, decide_eq_true_eq] at hx; exact hx
  | _ => cases h

private theorem sUpper?_sound {n : Nat} {o : CmpOp} {c : BitVec n} {u : Int}
    (h : sUpper? o c = some u) {x : BitVec n} (hx : CmpOp.evalBits o x c = true) :
    x.toInt ≤ u := by
  cases o with
  | slt =>
    dsimp only [sUpper?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.slt, decide_eq_true_eq] at hx; omega
  | sle =>
    dsimp only [sUpper?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.sle, decide_eq_true_eq] at hx; exact hx
  | _ => cases h

private theorem sLower?_sound {n : Nat} {o : CmpOp} {c : BitVec n} {l : Int}
    (h : sLower? o c = some l) {x : BitVec n} (hx : CmpOp.evalBits o x c = true) :
    l ≤ x.toInt := by
  cases o with
  | sgt =>
    dsimp only [sLower?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.slt, decide_eq_true_eq] at hx; omega
  | sge =>
    dsimp only [sLower?] at h; cases h
    simp only [CmpOp.evalBits, BitVec.sle, decide_eq_true_eq] at hx; exact hx
  | _ => cases h

theorem cmpConstImplies_sound {n : Nat} (o₁ : CmpOp) (c₁ : BitVec n) (o₂ : CmpOp) (c₂ : BitVec n)
    (b : Bool) (h : cmpConstImplies o₁ c₁ o₂ c₂ = some b) {x : BitVec n}
    (hx : CmpOp.evalBits o₁ x c₁ = true) : CmpOp.evalBits o₂ x c₂ = b := by
  dsimp only [cmpConstImplies] at h
  by_cases heq : (o₁ == .eq) = true
  · simp only [heq, ↓reduceIte, Option.some.injEq] at h; cases h
    have ho : o₁ = .eq := beq_iff_eq.mp heq; subst ho
    simp [CmpOp.evalBits] at hx; subst hx; rfl
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hne1 : (o₁ == .ne && o₂ == .eq && c₁ == c₂) = true
    · simp only [hne1, ↓reduceIte, Option.some.injEq] at h; cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hne1
      rcases hne1 with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [CmpOp.evalBits] at hx ⊢; exact hx
    · simp only [hne1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hne2 : (o₁ == .ne && o₂ == .ne && c₁ == c₂) = true
      · simp only [hne2, ↓reduceIte, Option.some.injEq] at h; cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hne2
        rcases hne2 with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hx
      · simp only [hne2, Bool.false_eq_true, ↓reduceIte] at h
        cases hu : uUpper? o₁ c₁ with
        | some u =>
          rw [hu] at h
          have hxu := uUpper?_sound hu hx
          cases o₂ <;> dsimp only at h <;> try cases h
          all_goals
            split at h <;> cases h
            simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, decide_eq_true_eq,
              decide_eq_false_iff_not]
            first
            | omega
            | (intro h'; subst h'; omega)
        | none =>
          rw [hu] at h
          cases hl : uLower? o₁ c₁ with
          | some l =>
            rw [hl] at h
            have hxl := uLower?_sound hl hx
            cases o₂ <;> dsimp only at h <;> try cases h
            all_goals
              split at h <;> cases h
              simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, decide_eq_true_eq,
                decide_eq_false_iff_not]
              first
              | omega
              | (intro h'; subst h'; omega)
          | none =>
            rw [hl] at h
            cases hsu : sUpper? o₁ c₁ with
            | some u =>
              rw [hsu] at h
              have hxu := sUpper?_sound hsu hx
              cases o₂ <;> dsimp only at h <;> try cases h
              all_goals
                split at h <;> cases h
                simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, decide_eq_true_eq,
                  decide_eq_false_iff_not]
                first
                | omega
                | (intro h'; subst h'; omega)
            | none =>
              rw [hsu] at h
              cases hsl : sLower? o₁ c₁ with
              | some l =>
                rw [hsl] at h
                have hxl := sLower?_sound hsl hx
                cases o₂ <;> dsimp only at h <;> try cases h
                all_goals
                  split at h <;> cases h
                  simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, decide_eq_true_eq,
                    decide_eq_false_iff_not]
                  first
                  | omega
                  | (intro h'; subst h'; omega)
              | none => rw [hsl] at h; cases h

theorem factImpliesCmpBits_sound {ρ : PEnv} {w : Nat}
    {o₁ : CmpOp} {x₁ y₁ : SymBits w} {o₂ : CmpOp} {x y : SymBits w} {b : Bool}
    (himpl : factImpliesCmpBits o₁ x₁ y₁ o₂ x y = some b)
    {vx₁ vy₁ vx vy : BitVec w}
    (hx₁ : SymBits.eval ρ x₁ = some vx₁) (hy₁ : SymBits.eval ρ y₁ = some vy₁)
    (hx : SymBits.eval ρ x = some vx) (hy : SymBits.eval ρ y = some vy)
    (hrel : CmpOp.evalBits o₁ vx₁ vy₁ = true) :
    CmpOp.evalBits o₂ vx vy = b := by
  dsimp only [factImpliesCmpBits] at himpl
  by_cases h1 : (symBitsBeq x x₁ && symBitsBeq y y₁) = true
  · simp only [h1, ↓reduceIte] at himpl
    simp only [Bool.and_eq_true] at h1
    rw [symBitsBeq_eq h1.1] at hx; rw [hx₁] at hx; cases hx
    rw [symBitsBeq_eq h1.2] at hy; rw [hy₁] at hy; cases hy
    exact cmpImplies_bits_sound o₁ o₂ b himpl _ _ hrel
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at himpl
    by_cases h2 : (symBitsBeq x y₁ && symBitsBeq y x₁) = true
    · simp only [h2, ↓reduceIte] at himpl
      simp only [Bool.and_eq_true] at h2
      rw [symBitsBeq_eq h2.1] at hx; rw [hy₁] at hx; cases hx
      rw [symBitsBeq_eq h2.2] at hy; rw [hx₁] at hy; cases hy
      have hsw := cmpImplies_bits_sound o₁ o₂.swap b himpl _ _ hrel
      rwa [CmpOp.swap_evalBits] at hsw
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at himpl
      cases y₁ with
      | fkey ky =>
        cases ky with
        | imm c₁ =>
          cases y with
          | ext => cases himpl
          | fkey k =>
            cases k with
            | var => cases himpl
            | imm c₂ =>
              dsimp only at himpl
              split at himpl
              · next hxmatch =>
                rw [symBitsBeq_eq hxmatch] at hx; rw [hx₁] at hx; cases hx
                have hc1 : vy₁ = c₁ := by simp [SymBits.eval, FKey.eval] at hy₁; exact hy₁.symm
                have hc2 : vy = c₂ := by simp [SymBits.eval, FKey.eval] at hy; exact hy.symm
                cases hc1; cases hc2
                exact cmpConstImplies_sound o₁ _ o₂ _ b himpl hrel
              · cases himpl
        | var _ =>
          cases y with
          | ext => cases himpl
          | fkey k =>
            cases k with
            | var => cases himpl
            | imm c₂ =>
              have hcy : vy = c₂ := by simp [SymBits.eval, FKey.eval] at hy; exact hy.symm
              subst vy
              dsimp only at himpl
              split at himpl
              · next hm =>
                have hxpos : 1 ≤ vx.toNat := by
                  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
                  rcases hm with ⟨rfl, hxy⟩ | ⟨rfl, hxx⟩
                  · rw [symBitsBeq_eq hxy] at hx; rw [hy₁] at hx; cases hx
                    simp [CmpOp.evalBits, BitVec.ult] at hrel; omega
                  · rw [symBitsBeq_eq hxx] at hx; rw [hx₁] at hx; cases hx
                    simp [CmpOp.evalBits, BitVec.ult] at hrel; omega
                split at himpl
                · next hc0 =>
                  have hcz : c₂ = 0#w := beq_iff_eq.mp hc0; subst hcz
                  have h0nat : (0#w).toNat = 0 := by simp
                  cases o₂ <;> simp only at himpl <;> try cases himpl
                  all_goals
                    simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, h0nat,
                      decide_eq_true_eq, decide_eq_false_iff_not]
                    first | omega | (intro h'; subst h'; simp at hxpos)
                · split at himpl
                  · next hc1 =>
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc1
                    rcases hc1 with ⟨rfl, hw⟩
                    have h1nat : (1#w).toNat = 1 := by
                      simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt
                          (Nat.one_lt_two_pow (by omega))
                    cases o₂ <;> simp only at himpl <;> cases himpl <;>
                      simp [CmpOp.evalBits, BitVec.ult, BitVec.ule, h1nat] <;> omega
                  · cases himpl
              · cases himpl
      | ext =>
        cases y with
        | ext => cases himpl
        | fkey k =>
          cases k with
          | var => cases himpl
          | imm c₂ =>
            have hcy : vy = c₂ := by simp [SymBits.eval, FKey.eval] at hy; exact hy.symm
            subst vy
            dsimp only at himpl
            split at himpl
            · next hm =>
              have hxpos : 1 ≤ vx.toNat := by
                simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
                rcases hm with ⟨rfl, hxy⟩ | ⟨rfl, hxx⟩
                · rw [symBitsBeq_eq hxy] at hx; rw [hy₁] at hx; cases hx
                  simp [CmpOp.evalBits, BitVec.ult] at hrel; omega
                · rw [symBitsBeq_eq hxx] at hx; rw [hx₁] at hx; cases hx
                  simp [CmpOp.evalBits, BitVec.ult] at hrel; omega
              split at himpl
              · next hc0 =>
                have hcz : c₂ = 0#w := beq_iff_eq.mp hc0; subst hcz
                have h0nat : (0#w).toNat = 0 := by simp
                cases o₂ <;> simp only at himpl <;> try cases himpl
                all_goals
                  simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, h0nat,
                    decide_eq_true_eq, decide_eq_false_iff_not]
                  first | omega | (intro h'; subst h'; simp at hxpos)
              · split at himpl
                · next hc1 =>
                  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc1
                  rcases hc1 with ⟨rfl, hw⟩
                  have h1nat : (1#w).toNat = 1 := by
                    simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt
                        (Nat.one_lt_two_pow (by omega))
                  cases o₂ <;> simp only at himpl <;> cases himpl <;>
                    simp [CmpOp.evalBits, BitVec.ult, BitVec.ule, h1nat] <;> omega
                · cases himpl
            · cases himpl

/-! ### Path-fact invariants (`BoolFact.Holds`, `FactsOk`, `PInfoOk`, `PGood`) -/

@[expose] def BoolFact.Holds (ρ : PEnv) (b : Nat) : BoolFact → Prop
  | .varEq i c => i < b ∧ ρ i = some ⟨.bool, c⟩
  | .cmpBits o w l r =>
      SymBits.InScope b l ∧ SymBits.InScope b r ∧
        ∃ xl xr : BitVec w, SymBits.eval ρ l = some xl ∧ SymBits.eval ρ r = some xr ∧
          CmpOp.evalBits o xl xr = true
  | .cmpBool o l r =>
      FKey.InScope b l ∧ FKey.InScope b r ∧
        ∃ xl xr : Bool, FKey.eval ρ l = some xl ∧ FKey.eval ρ r = some xr ∧
          CmpOp.evalBool o xl xr = true

@[expose] def FactsOk (ρ : PEnv) (b : Nat) (F : List BoolFact) : Prop :=
  ∀ f ∈ F, BoolFact.Holds ρ b f

theorem BoolFact.Holds.mono {ρ ρ' : PEnv} {b b' : Nat} (hb : b ≤ b')
    (hρ : ∀ k, k < b → ρ' k = ρ k) : {f : BoolFact} → BoolFact.Holds ρ b f → BoolFact.Holds ρ' b' f
  | .varEq i _c, ⟨hi, h⟩ => ⟨Nat.lt_of_lt_of_le hi hb, (hρ i hi).trans h⟩
  | .cmpBits _ _ _l _r, ⟨hl, hr, xl, xr, hxl, hxr, hc⟩ =>
    ⟨SymBits.InScope.mono hb hl, SymBits.InScope.mono hb hr, xl, xr,
      (SymBits.eval_mono hρ hl).trans hxl, (SymBits.eval_mono hρ hr).trans hxr, hc⟩
  | .cmpBool _ _l _r, ⟨hl, hr, xl, xr, hxl, hxr, hc⟩ =>
    ⟨FKey.InScope.mono hb hl, FKey.InScope.mono hb hr, xl, xr,
      (FKey.eval_mono hρ hl).trans hxl, (FKey.eval_mono hρ hr).trans hxr, hc⟩

theorem FactsOk.mono {ρ ρ' : PEnv} {b b' : Nat} (hb : b ≤ b')
    (hρ : ∀ k, k < b → ρ' k = ρ k) {F : List BoolFact} (h : FactsOk ρ b F) :
    FactsOk ρ' b' F := fun f hf =>
  BoolFact.Holds.mono hb hρ (h f hf)

theorem FactsOk.updTup {ρ : PEnv} {b : Nat} {F : List BoolFact} (h : FactsOk ρ b F)
    {ts : List Ty} (xs : Tup Val ts) : FactsOk (PEnv.updTup ρ b xs) (b + ts.length) F :=
  h.mono (Nat.le_add_right _ _) fun _ hk => PEnv.updTup_lt ρ xs hk

theorem FactsOk.append {ρ : PEnv} {b : Nat} {F₁ F₂ : List BoolFact} (h₁ : FactsOk ρ b F₁)
    (h₂ : FactsOk ρ b F₂) : FactsOk ρ b (F₁ ++ F₂) := fun f hf =>
  (List.mem_append.1 hf).elim (h₁ f) (h₂ f)

theorem FactsOk.nil {ρ : PEnv} {b : Nat} : FactsOk ρ b [] := fun _ hf => nomatch hf

theorem FactsOk.take {ρ : PEnv} {b : Nat} {F : List BoolFact} (n : Nat) (h : FactsOk ρ b F) :
    FactsOk ρ b (F.take n) := fun f hf =>
  h f (List.mem_of_mem_take hf)

theorem queryCmpBits_sound {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {o : CmpOp} {w : Nat} {x y : SymBits w} {res : Bool}
    (hq : queryCmpBits F o w x y = some res)
    {vx vy : BitVec w} (hx : SymBits.eval ρ x = some vx) (hy : SymBits.eval ρ y = some vy) :
    CmpOp.evalBits o vx vy = res := by
  induction F with
  | nil => cases hq
  | cons f rest ih =>
    have hf := hF f List.mem_cons_self
    have hrest : FactsOk ρ b rest := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    cases f with
    | varEq _ _ | cmpBool _ _ _ =>
      dsimp only [queryCmpBits] at hq
      exact ih hrest hq
    | cmpBits o₁ w₁ x₁ y₁ =>
      dsimp only [queryCmpBits] at hq
      by_cases hw : w₁ = w
      · subst hw
        simp only [↓reduceDIte] at hq
        cases hi : factImpliesCmpBits o₁ x₁ y₁ o x y with
        | some b' =>
          rw [hi] at hq; cases hq
          rcases hf with ⟨_, _, vx₁, vy₁, hx₁, hy₁, hrel⟩
          exact factImpliesCmpBits_sound hi hx₁ hy₁ hx hy hrel
        | none =>
          rw [hi] at hq
          exact ih hrest hq
      · simp only [hw, ↓reduceDIte] at hq
        exact ih hrest hq

theorem queryCmpBool_sound {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {o : CmpOp} {x y : FKey .bool} {res : Bool}
    (hq : queryCmpBool F o x y = some res)
    {vx vy : Bool} (hx : FKey.eval ρ x = some vx) (hy : FKey.eval ρ y = some vy) :
    CmpOp.evalBool o vx vy = res := by
  induction F with
  | nil => cases hq
  | cons f rest ih =>
    have hf := hF f List.mem_cons_self
    have hrest : FactsOk ρ b rest := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    cases f with
    | varEq _ _ | cmpBits _ _ _ _ =>
      dsimp only [queryCmpBool] at hq
      exact ih hrest hq
    | cmpBool o₁ x₁ y₁ =>
      dsimp only [queryCmpBool] at hq
      by_cases h1 : (fKeyBeq x x₁ && fKeyBeq y y₁) = true
      · simp only [h1, ↓reduceIte] at hq
        cases hi : cmpImplies o₁ o with
        | some b' =>
          rw [hi] at hq; cases hq
          simp only [Bool.and_eq_true, fKeyBeq_iff_eq] at h1
          rcases h1 with ⟨rfl, rfl⟩
          rcases hf with ⟨_, _, vx₁, vy₁, hx₁, hy₁, hrel⟩
          rw [hx] at hx₁; cases hx₁; rw [hy] at hy₁; cases hy₁
          exact cmpImplies_bool_sound o₁ o res hi _ _ hrel
        | none => rw [hi] at hq; exact ih hrest hq
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hq
        by_cases h2 : (fKeyBeq x y₁ && fKeyBeq y x₁) = true
        · simp only [h2, ↓reduceIte] at hq
          cases hi : cmpImplies o₁ o.swap with
          | some b' =>
            rw [hi] at hq; cases hq
            simp only [Bool.and_eq_true, fKeyBeq_iff_eq] at h2
            rcases h2 with ⟨rfl, rfl⟩
            rcases hf with ⟨_, _, vx₁, vy₁, hx₁, hy₁, hrel⟩
            rw [hy] at hx₁; cases hx₁; rw [hx] at hy₁; cases hy₁
            have hsw := cmpImplies_bool_sound o₁ o.swap res hi _ _ hrel
            rwa [CmpOp.swap_evalBool] at hsw
          | none => rw [hi] at hq; exact ih hrest hq
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hq
          exact ih hrest hq

theorem lookupVarFact_sound {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {i : Nat} {c : Bool} (hl : lookupVarFact F i = some c) :
    i < b ∧ ρ i = some ⟨.bool, c⟩ := by
  induction F with
  | nil => cases hl
  | cons f rest ih =>
    have hf := hF f List.mem_cons_self
    have hrest : FactsOk ρ b rest := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    cases f with
    | cmpBits _ _ _ _ | cmpBool _ _ _ =>
      dsimp only [lookupVarFact] at hl
      exact ih hrest hl
    | varEq j b' =>
      dsimp only [lookupVarFact] at hl
      by_cases he : (i == j) = true
      · simp only [he, ↓reduceIte, Option.some.injEq] at hl; cases hl
        have hj : i = j := beq_iff_eq.mp he; subst hj
        exact hf
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hl; exact ih hrest hl

theorem factRefuted_sound {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {f : BoolFact} (hr : factRefuted F f = true) : ¬ BoolFact.Holds ρ b f := by
  intro hf
  cases f with
  | varEq i c =>
    dsimp only [factRefuted] at hr
    cases hl : lookupVarFact F i with
    | none => rw [hl] at hr; cases hr
    | some c' =>
      rw [hl] at hr
      have hc' := lookupVarFact_sound hF hl
      rw [hf.2] at hc'
      cases hc'.2 with | refl => simp at hr
  | cmpBits o w l r =>
    dsimp only [factRefuted] at hr
    have hq : queryCmpBits F o w l r = some false := beq_iff_eq.mp hr
    rcases hf with ⟨_, _, xl, xr, hxl, hxr, hc⟩
    have hres := queryCmpBits_sound hF hq hxl hxr
    rw [hres] at hc; cases hc
  | cmpBool o l r =>
    dsimp only [factRefuted] at hr
    have hq : queryCmpBool F o l r = some false := beq_iff_eq.mp hr
    rcases hf with ⟨_, _, xl, xr, hxl, hxr, hc⟩
    have hres := queryCmpBool_sound hF hq hxl hxr
    rw [hres] at hc; cases hc

/-- Metadata soundness for `PInfo` under identity environment `ρ` and scope bound `b`. -/
@[expose] def PInfoOk (ρ : PEnv) (b : Nat) {t : Ty} (info : PInfo) (v : Val t) : Prop :=
  (∀ k, info.id = some k → k < b ∧ ρ k = some ⟨t, v⟩) ∧
  (match t, v with
   | .bool, bval => (bval = true → FactsOk ρ b info.tf) ∧ (bval = false → FactsOk ρ b info.ff)
   | _, _ => True) ∧
  (∀ e : ExtProv, info.ext? = some e →
    match t, v with
    | .bits w, bval => ∃ (srcV : BitVec e.m), w = e.w ∧ FKey.InScope b e.src ∧
        FKey.eval ρ e.src = some srcV ∧
        bval = (match e.kind with | .zext => srcV.setWidth w | .sext => srcV.signExtend w)
    | _, _ => False)

@[expose] def PGood (ρ : PEnv) (b : Nat) {t : Ty} (p : PVal Val t) (v : Val t) : Prop :=
  p.out.val = v ∧ PInfoOk ρ b p.info v

@[expose] def PGoodArg (ρ : PEnv) (b : Nat) {t : Ty} (a : Arg (PVal Val) t) (v : Val t) : Prop :=
  (pOut a).val = v ∧ PInfoOk ρ b (pInfo a) v

@[expose] def PGoodCtx (ρ : PEnv) (b : Nat) (G : Ctx (PVal Val) Val) : Prop :=
  ∀ p ∈ G, PGood ρ b p.2.1 p.2.2

theorem PInfoOk.mono {ρ ρ' : PEnv} {b b' : Nat} (hb : b ≤ b') (hρ : ∀ k, k < b → ρ' k = ρ k)
    {t : Ty} {info : PInfo} {v : Val t} (h : PInfoOk ρ b info v) : PInfoOk ρ' b' info v := by
  refine ⟨fun k hk => ⟨by have := (h.1 k hk).1; omega, (hρ k (h.1 k hk).1).trans (h.1 k hk).2⟩,
    ?_, fun e he => ?_⟩
  · cases t with
    | bool => exact ⟨fun hv => (h.2.1.1 hv).mono hb hρ, fun hv => (h.2.1.2 hv).mono hb hρ⟩
    | _ => trivial
  · cases t with
    | bits w =>
      rcases h.2.2 e he with ⟨srcV, hw, hsc, heval, hv⟩
      exact ⟨srcV, hw, FKey.InScope.mono hb hsc, (FKey.eval_mono hρ hsc).trans heval, hv⟩
    | _ => exact h.2.2 e he

theorem PInfoOk.empty {ρ : PEnv} {b : Nat} {t : Ty} (v : Val t) : PInfoOk ρ b {} v := by
  refine ⟨fun _ h => (nomatch h), ?_, fun _ h => (nomatch h)⟩
  cases t with
  | bool => exact ⟨fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
  | _ => trivial

theorem PGoodCtx.mono {ρ ρ' : PEnv} {b b' : Nat} (hb : b ≤ b') (hρ : ∀ k, k < b → ρ' k = ρ k)
    {G : Ctx (PVal Val) Val} (h : PGoodCtx ρ b G) : PGoodCtx ρ' b' G := fun p hp =>
  ⟨(h p hp).1, (h p hp).2.mono hb hρ⟩

theorem PGoodCtx.updTup {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (h : PGoodCtx ρ b G)
    {ts : List Ty} (xs : Tup Val ts) : PGoodCtx (PEnv.updTup ρ b xs) (b + ts.length) G :=
  h.mono (Nat.le_add_right _ _) fun _ hk => PEnv.updTup_lt ρ xs hk

theorem PGoodCtx.cons {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G)
    {t : Ty} {a : PVal Val t} {v : Val t} (ha : PGood ρ b a v) :
    PGoodCtx ρ b (⟨t, a, v⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

private theorem PVal.fresh_out {V : Ty → Type} (t : Ty) (v : V t) (k : Nat) :
    (PVal.fresh t v k).out = .var v := by
  cases t <;> rfl

private theorem PInfoOk.fresh {ρ : PEnv} {b k : Nat} {t : Ty} {v : Val t}
    (hk : k < b) (hρ : ρ k = some ⟨t, v⟩) :
    PInfoOk ρ b (PVal.fresh t v k).info v := by
  cases t with
  | bool =>
    refine ⟨fun _ h => by cases h; exact ⟨hk, hρ⟩, ⟨?_, ?_⟩, fun _ h => by cases h⟩
    · intro hv f hf
      dsimp only [PVal.fresh] at hf
      rw [List.mem_singleton] at hf; subst hf; subst hv
      exact ⟨hk, hρ⟩
    · intro hv f hf
      dsimp only [PVal.fresh] at hf
      rw [List.mem_singleton] at hf; subst hf; subst hv
      exact ⟨hk, hρ⟩
  | bits _ | float _ | pair _ _ =>
    exact ⟨fun _ h => by cases h; exact ⟨hk, hρ⟩, trivial, fun _ h => by cases h⟩

private theorem PGoodCtx.freshPVals_only (ρ : PEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    PGoodCtx (PEnv.updTup ρ b xs) (b + ts.length) (Tup.zip (freshPVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | t :: ts, (x, xs), b => by
    dsimp only [freshPVals, tupFreshWith, Tup.zip, PEnv.updTup]
    intro p hp
    cases hp with
    | head =>
      refine ⟨by dsimp only; rw [PVal.fresh_out]; rfl, PInfoOk.fresh (by simp) ?_⟩
      rw [PEnv.updTup_lt (PEnv.upd ρ b x) xs (by omega), PEnv.upd_eq]
    | tail _ hp =>
      have ih := PGoodCtx.freshPVals_only (PEnv.upd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem PGoodCtx.freshPVals {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G)
    {ts : List Ty} (xs : Tup Val ts) :
    PGoodCtx (PEnv.updTup ρ b xs) (b + ts.length) (Tup.zip (freshPVals ts xs b) xs ++ G) :=
  fun p hp => (List.mem_append.1 hp).elim (PGoodCtx.freshPVals_only ρ xs b p)
    ((hG.updTup xs) p)

theorem PGoodCtx.freshOne {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G)
    {t : Ty} (v : Val t) :
    PGoodCtx (PEnv.upd ρ b v) (b + 1) (⟨t, PVal.fresh t v b, v⟩ :: G) :=
  (hG.updTup (ts := [t]) (v, ())).cons
    ⟨by rw [PVal.fresh_out]; rfl, PInfoOk.fresh (by simp) (PEnv.upd_eq ρ b v)⟩

theorem argRel_pGood {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G)
    {t : Ty} : {a₁ : Arg (PVal Val) t} → {a₂ : Arg Val t} → ArgRel G t a₁ a₂ →
    PGoodArg ρ b a₁ a₂.val
  | .var _, _, .var h => hG _ h
  | .imm _, _, .imm c => ⟨rfl, PInfoOk.empty c⟩

theorem PGoodArg.toPVal {ρ : PEnv} {b : Nat} {t : Ty} {a : Arg (PVal Val) t} {v : Val t}
    (h : PGoodArg ρ b a v) : PGood ρ b (toPVal a) v := by
  cases a <;> exact h

theorem trel_pOut_vals {ρ : PEnv} {b : Nat} {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (PVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → vals (tupPOut as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha hs =>
    Prod.ext (argRel_pGood hG ha).1 (trel_pOut_vals hG hs)

theorem PGoodArg.imm_eq {ρ : PEnv} {b : Nat} {t : Ty} {a : Arg (PVal Val) t} {v c : Val t}
    (ha : PGoodArg ρ b a v) (hc : (pOut a).imm? = some c) : v = c := by
  rw [← ha.1]
  cases ho : pOut a <;> rw [ho] at hc <;> cases hc; rfl

theorem PGoodArg.pFKey_eval {ρ : PEnv} {b : Nat} {t : Ty} {a : Arg (PVal Val) t} {v : Val t}
    (ha : PGoodArg ρ b a v) {k : FKey t} (hk : pFKey a = some k) :
    FKey.InScope b k ∧ FKey.eval ρ k = some v := by
  dsimp only [pFKey] at hk
  cases ho : pOut a <;> rw [ho] at hk
  · cases hid : (pInfo a).id with
    | none => rw [hid] at hk; cases hk
    | some idx =>
      rw [hid] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
      obtain ⟨hlt, hρ⟩ := ha.2.1 idx hid
      exact ⟨hlt, by dsimp only [FKey.eval]; rw [hρ]; exact castTy_self _ _⟩
  · cases hk
    have hvc : v = _ := ha.imm_eq (by rw [ho]; rfl)
    subst hvc
    exact ⟨trivial, rfl⟩

theorem PGoodArg.symBits_eval {ρ : PEnv} {b : Nat} {w : Nat}
    {a : Arg (PVal Val) (.bits w)} {v : BitVec w}
    (ha : PGoodArg ρ b a v) {s : SymBits w} (hs : symBits? a = some s) :
    SymBits.InScope b s ∧ SymBits.eval ρ s = some v := by
  dsimp only [symBits?] at hs
  cases ho : pOut a with
  | imm c =>
    rw [ho] at hs; cases hs
    have hvc : v = c := ha.imm_eq (by rw [ho]; rfl)
    subst hvc
    exact ⟨trivial, rfl⟩
  | var _ =>
    rw [ho] at hs
    cases hext : (pInfo a).ext? with
    | none =>
      rw [hext] at hs
      cases hid : (pInfo a).id with
      | none => rw [hid] at hs; cases hs
      | some idx =>
        rw [hid] at hs; cases hs
        obtain ⟨hlt, hρ⟩ := ha.2.1 idx hid
        exact ⟨hlt, by dsimp only [SymBits.eval, FKey.eval]; rw [hρ]; exact castTy_self _ _⟩
    | some e =>
      rw [hext] at hs
      dsimp only at hs
      split at hs
      · next hw =>
        cases hs
        rcases ha.2.2.2 e hext with ⟨srcV, hweq, hsc, heval, hv⟩
        subst hweq
        refine ⟨hsc, ?_⟩
        dsimp only [SymBits.eval]
        cases hkd : e.kind <;> rw [hkd] at hv <;> simp [hv, heval]
      · cases hid : (pInfo a).id with
        | none => rw [hid] at hs; cases hs
        | some idx =>
          rw [hid] at hs; cases hs
          obtain ⟨hlt, hρ⟩ := ha.2.1 idx hid
          exact ⟨hlt, by dsimp only [SymBits.eval, FKey.eval]; rw [hρ]; exact castTy_self _ _⟩

theorem resolveBool?_sound {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {a : Arg (PVal Val) .bool} {v : Bool} (ha : PGoodArg ρ b a v) {c : Bool}
    (hr : resolveBool? F a = some c) : v = c := by
  dsimp only [resolveBool?] at hr
  cases ho : pOut a with
  | imm bv =>
    rw [ho] at hr; cases hr
    exact ha.imm_eq (by rw [ho]; rfl)
  | var _ =>
    rw [ho] at hr
    cases hbind : (pInfo a).id.bind (lookupVarFact F) with
    | some bv =>
      rw [hbind] at hr; cases hr
      cases hid : (pInfo a).id with
      | none => rw [hid] at hbind; cases hbind
      | some idx =>
        rw [hid] at hbind
        dsimp only [Option.bind_some] at hbind
        have hl := lookupVarFact_sound hF hbind
        have hρ := (ha.2.1 idx hid).2
        rw [hρ] at hl
        cases hl.2; rfl
    | none =>
      rw [hbind] at hr
      by_cases htf : (pInfo a).tf.any (factRefuted F) = true
      · simp only [htf, ↓reduceIte, Option.some.injEq] at hr; cases hr
        rcases List.any_eq_true.mp htf with ⟨f, hf, href⟩
        cases hv : v
        · rfl
        · exact absurd ((ha.2.2.1.1 hv) f hf) (factRefuted_sound hF href)
      · simp only [htf, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hff : (pInfo a).ff.any (factRefuted F) = true
        · simp only [hff, ↓reduceIte, Option.some.injEq] at hr; cases hr
          rcases List.any_eq_true.mp hff with ⟨f, hf, href⟩
          cases hv : v
          · exact absurd ((ha.2.2.1.2 hv) f hf) (factRefuted_sound hF href)
          · rfl
        · simp only [hff, Bool.false_eq_true, ↓reduceIte] at hr; cases hr

private theorem PInfoOk.emptyBool {ρ : PEnv} {b : Nat} (v : Val .bool) : PInfoOk ρ b {} v :=
  PInfoOk.empty v

theorem resolveBoolArg_good {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {a : Arg (PVal Val) .bool} {v : Bool} (ha : PGoodArg ρ b a v) :
    PGoodArg ρ b (resolveBoolArg F a) v := by
  dsimp only [resolveBoolArg]
  cases hr : resolveBool? F a with
  | none => exact ha
  | some c =>
    have hvc := resolveBool?_sound hF ha hr
    exact ⟨hvc.symm, PInfoOk.emptyBool _⟩

theorem trel_resolveBoolArgs_vals {ρ : PEnv} {b : Nat} {F : List BoolFact} (hF : FactsOk ρ b F)
    {G : Ctx (PVal Val) Val} (hG : PGoodCtx ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (PVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → vals (tupPOut (resolveBoolArgs F as₁)) = vals as₂
  | [], (), (), .nil => rfl
  | .bool :: _, (_, _), (_, _), .cons ha hs => by
    dsimp only [resolveBoolArgs, tupPOut, tupMapArg, vals]
    exact Prod.ext (resolveBoolArg_good hF (argRel_pGood hG ha)).1
        (trel_resolveBoolArgs_vals hF hG hs)
  | .bits _ :: _, (_, _), (_, _), .cons ha hs
  | .float _ :: _, (_, _), (_, _), .cons ha hs
  | .pair _ _ :: _, (_, _), (_, _), .cons ha hs => by
    dsimp only [resolveBoolArgs, tupPOut, tupMapArg, vals]
    exact Prod.ext (argRel_pGood hG ha).1 (trel_resolveBoolArgs_vals hF hG hs)

/-! ### `pcStep` correctness (`pcStep_wp`) -/

theorem CmpOp.evalBool_isRefl (o : CmpOp) (b : Bool) : o.evalBool b b = o.isRefl := by
  cases o <;> cases b <;> rfl

theorem CmpOp.neg_evalBool (o : CmpOp) (a b : Bool) : o.neg.evalBool a b = !(o.evalBool a b) := by
  cases o <;> cases a <;> cases b <;> rfl

private theorem wrapBool_good {ρ : PEnv} {next : Nat} (r : Bool)
    {tf ff : List BoolFact} (htf : r = true → FactsOk ρ next tf)
        (hff : r = false → FactsOk ρ next ff) :
    PGood (PEnv.upd (t := .bool) ρ next r) (next + 1) ((wrapBool next tf ff (r, ())).1) r := by
  have hup : ∀ k, k < next → PEnv.upd (t := .bool) ρ next r k = ρ k :=
    fun k hk => PEnv.upd_ne (t := .bool) (b := next) (k := k) ρ r (by omega)
  refine ⟨rfl, fun k hk => ?_, ⟨?_, ?_⟩, fun _ h => by cases h⟩
  · cases hk; exact ⟨Nat.lt_succ_self _, PEnv.upd_eq (t := .bool) ρ next r⟩
  · intro hr f hf
    dsimp only [wrapBool] at hf
    rw [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨Nat.lt_succ_self _, by rw [PEnv.upd_eq (t := .bool), hr]⟩
    · exact BoolFact.Holds.mono (Nat.le_succ _) hup (htf hr f hf)
  · intro hr f hf
    dsimp only [wrapBool] at hf
    rw [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨Nat.lt_succ_self _, by rw [PEnv.upd_eq (t := .bool), hr]⟩
    · exact BoolFact.Holds.mono (Nat.le_succ _) hup (hff hr f hf)

def pcCmpBitsSym {V : Ty → Type} {w : Nat} (F : List BoolFact) (next : Nat)
    (o o' : CmpOp) (a b a' b' : Arg (PVal V) (.bits w)) : PCStep V [.bool] :=
  match symBits? a', symBits? b' with
  | some sa, some sb =>
    if symBitsBeq sa sb then .elim (pBoolImm o'.isRefl, ())
    else
      match queryCmpBits F o' w sa sb with
      | some res => .elim (pBoolImm res, ())
      | none =>
        .emit (op2 (.cmp o' (.bits w)) (pOut a') (pOut b'))
          (wrapBool next [.cmpBits o' w sa sb] [.cmpBits o'.neg w sa sb])
  | _, _ =>
    .emit (op2 (.cmp o (.bits w)) (pOut a) (pOut b))
      (fun xs => freshPVals [.bool] xs next)

theorem pcStepAux_cmpBits_n_ {V : Ty → Type} {w : Nat} (F : List BoolFact)
    (next : Nat) (o : CmpOp) {a b : Arg (PVal V) (.bits w)} (ha : (pOut a).imm? = none) :
    pcStepAux (.cmp o (.bits w)) (a, b, ()) F next = pcCmpBitsSym F next o o a b a b := by
  cases hb : (pOut b).imm? <;> simp only [pcStepAux, pcCmpBitsSym, ha, hb] <;> rfl

theorem pcStepAux_cmpBits_sn {V : Ty → Type} {w : Nat} (F : List BoolFact)
    (next : Nat) (o : CmpOp) {a b : Arg (PVal V) (.bits w)} {ca : BitVec w}
    (ha : (pOut a).imm? = some ca) (hb : (pOut b).imm? = none) :
    pcStepAux (.cmp o (.bits w)) (a, b, ()) F next = pcCmpBitsSym F next o o.swap a b b a := by
  simp only [pcStepAux, pcCmpBitsSym, ha, hb]
  rfl

theorem pcStepAux_cmpBits_ss {V : Ty → Type} {w : Nat} (F : List BoolFact)
    (next : Nat) (o : CmpOp) {a b : Arg (PVal V) (.bits w)} {ca cb : BitVec w}
    (ha : (pOut a).imm? = some ca) (hb : (pOut b).imm? = some cb) :
    pcStepAux (.cmp o (.bits w)) (a, b, ()) F next =
      .elim (pBoolImm (CmpOp.evalBits o ca cb), ()) := by
  simp only [pcStepAux, ha, hb]

private theorem pcCmpBitsSym_wp {ρ : PEnv} {next w : Nat} {G : Ctx (PVal Val) Val}
    (hG : PGoodCtx ρ next G) {F : List BoolFact} (hF : FactsOk ρ next F)
    (o o' : CmpOp) {a b a' b' : Arg (PVal Val) (.bits w)} {va vb va' vb' : BitVec w}
    (hga0 : PGoodArg ρ next a va) (hgb0 : PGoodArg ρ next b vb)
    (hga : PGoodArg ρ next a' va') (hgb : PGoodArg ρ next b' vb')
    (hoEval : CmpOp.evalBits o' va' vb' = CmpOp.evalBits o va vb)
    {post : Tup Val [.bool] → Prop} (hw : post (CmpOp.evalBits o va vb, ())) :
    match pcCmpBitsSym F next o o' a b a' b' with
    | .elim res => ∃ ys, post ys ∧ PGoodCtx ρ next (Tup.zip res ys ++ G)
    | .emit op' wrap => op'.wp fun ys => post ys ∧
        PGoodCtx (PEnv.updTup ρ next ys) (next + 1) (Tup.zip (wrap ys) ys ++ G) := by
  dsimp only [pcCmpBitsSym]
  cases hsa : symBits? a' <;> cases hsb : symBits? b'
  case some.some sa sb =>
    obtain ⟨hsaSc, hsaEv⟩ := hga.symBits_eval hsa
    obtain ⟨hsbSc, hsbEv⟩ := hgb.symBits_eval hsb
    by_cases hbeq : symBitsBeq sa sb = true
    · simp only [hbeq, ↓reduceIte]
      have heq := symBitsBeq_eq hbeq
      subst heq
      have heqv := Option.some.inj (hsaEv.symm.trans hsbEv)
      rw [← hoEval, heqv, cmpOp_evalBits_self] at hw
      exact ⟨(o'.isRefl, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      cases hq : queryCmpBits F o' w sa sb with
      | some res =>
        rw [← hoEval, queryCmpBits_sound hF hq hsaEv hsbEv] at hw
        exact ⟨(res, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
      | none =>
        dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← hoEval] at hw
        rw [hga.1, hgb.1]
        refine ⟨hw, ?_⟩
        have htf : CmpOp.evalBits o' va' vb' = true → FactsOk ρ next [.cmpBits o' w sa sb] := by
          intro hres f hf
          rw [List.mem_singleton] at hf; subst hf
          exact ⟨hsaSc, hsbSc, _, _, hsaEv, hsbEv, hres⟩
        have hff : CmpOp.evalBits o' va' vb' = false → FactsOk ρ next [.cmpBits o'.neg w sa sb] :=
            by
          intro hres f hf
          rw [List.mem_singleton] at hf; subst hf
          exact ⟨hsaSc, hsbSc, _, _, hsaEv, hsbEv, by rw [CmpOp.neg_evalBits, hres]; rfl⟩
        exact (hG.updTup (ts := [.bool]) (CmpOp.evalBits o' va' vb', ())).cons
          (wrapBool_good (CmpOp.evalBits o' va' vb') htf hff)
  all_goals
    dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hga0.1, hgb0.1]
    exact ⟨hw, hG.freshPVals _⟩

private theorem pcStep_wp {ρ : PEnv} {next : Nat} {G : Ctx (PVal Val) Val}
    (hG : PGoodCtx ρ next G) {F : List BoolFact} (hF : FactsOk ρ next F)
    {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (PVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {post : Tup Val ts → Prop}
    (hw : code.wp (vals args₂) post) :
    match pcStepAux code args₁ F next with
    | .elim res => ∃ ys, post ys ∧ PGoodCtx ρ next (Tup.zip res ys ++ G)
    | .emit op' wrap => op'.wp fun ys => post ys ∧
        PGoodCtx (PEnv.updTup ρ next ys) (next + ts.length) (Tup.zip (wrap ys) ys ++ G) := by
  cases code with
  | copy _ =>
    rcases args₁ with ⟨a, _⟩; rcases args₂ with ⟨a₂, _⟩
    cases hargs with
    | cons ha _ =>
      have hg := argRel_pGood hG ha
      dsimp only [pcStepAux]
      cases a with
      | var _ => exact ⟨(a₂.val, ()), hw, hG.cons hg⟩
      | imm c =>
        have hvc : a₂.val = c := hg.imm_eq rfl
        subst hvc
        exact ⟨(a₂.val, ()), hw, hG.cons ⟨rfl, PInfoOk.empty _⟩⟩
  | not t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a, _⟩; rcases args₂ with ⟨a₂, _⟩
      cases hargs with
      | cons ha _ =>
        have hg := resolveBoolArg_good hF (argRel_pGood hG ha)
        dsimp only [pcStepAux]
        cases ho : pOut (resolveBoolArg F a) with
        | imm bv =>
          have hvc : a₂.val = bv := hg.imm_eq (by rw [ho]; rfl)
          subst hvc
          exact ⟨(!a₂.val, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
        | var p =>
          have hpa : (Arg.var p).val = a₂.val := by rw [← ho, hg.1]
          dsimp only [Op.wp, op1, OpCode.wp, lift1, vals] at hw ⊢
          rw [hpa]
          refine ⟨hw, ?_⟩
          have hg' := wrapBool_good (!a₂.val)
            (fun hv => hg.2.2.1.2 (by revert hv; cases a₂.val <;> decide))
            (fun hv => hg.2.2.1.1 (by revert hv; cases a₂.val <;> decide))
          exact (hG.updTup (ts := [.bool]) (!a₂.val, ())).cons hg'
    | bits _ | float _ | pair _ _ =>
      dsimp only [pcStepAux, Op.wp]
      rw [trel_pOut_vals hG hargs]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw
  | and t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a, b, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have hga := resolveBoolArg_good hF (argRel_pGood hG ha)
      have hgb := resolveBoolArg_good hF (argRel_pGood hG hb)
      dsimp only [pcStepAux]
      cases hoa : pOut (resolveBoolArg F a) with
      | var pa =>
        have hpa : (Arg.var pa).val = a₂.val := by rw [← hoa, hga.1]
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          have hpb : (Arg.var pb).val = b₂.val := by rw [← hob, hgb.1]
          dsimp only
          by_cases heq : ((pInfo (resolveBoolArg F a)).id == (pInfo (resolveBoolArg F b)).id &&
              (pInfo (resolveBoolArg F a)).id.isSome) = true
          · simp only [heq, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at heq
            rcases heq with ⟨hid, k, hk⟩
            have haρ := (hga.2.1 k hk).2
            have hbρ := (hgb.2.1 k (hk ▸ hid.symm)).2
            rw [haρ] at hbρ
            have heqv : a₂.val = b₂.val := eq_of_heq (Sigma.mk.inj (Option.some.inj hbρ)).2
            dsimp only [OpCode.wp, lift2, vals] at hw
            rw [← heqv] at hw
            have heqb : (a₂.val && a₂.val) = a₂.val := by cases a₂.val <;> rfl
            rw [heqb] at hw
            exact ⟨(a₂.val, ()), hw, hG.cons hga.toPVal⟩
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            dsimp only [Op.wp, op2, OpCode.wp, lift2, vals] at hw ⊢
            rw [hpa, hpb]
            refine ⟨hw, ?_⟩
            have htf : (a₂.val && b₂.val) = true →
                FactsOk ρ next
                    ((pInfo (resolveBoolArg F a)).tf ++ (pInfo (resolveBoolArg F b)).tf) := by
              intro hab
              simp only [Bool.and_eq_true] at hab
              exact (hga.2.2.1.1 hab.1).append (hgb.2.2.1.1 hab.2)
            exact (hG.updTup (ts := [.bool]) (a₂.val && b₂.val, ())).cons
              (wrapBool_good (a₂.val && b₂.val) htf (fun _ => FactsOk.nil))
        | imm cb =>
          have hvc : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases cb
          · exact ⟨(false, ()), by simpa [hvc] using hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(a₂.val, ()), by simpa [hvc] using hw, hG.cons hga.toPVal⟩
      | imm ca =>
        have hva : a₂.val = ca := hga.imm_eq (by rw [hoa]; rfl)
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases ca
          · exact ⟨(false, ()), by simpa [hva] using hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(b₂.val, ()), by simpa [hva] using hw, hG.cons hgb.toPVal⟩
        | imm cb =>
          have hvb : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          rw [hva, hvb] at hw
          cases ca <;> cases cb
          · exact ⟨(false, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(false, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(false, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(b₂.val, ()), by simpa [hvb] using hw, hG.cons hgb.toPVal⟩
    | bits _ | float _ | pair _ _ =>
      dsimp only [pcStepAux, Op.wp]
      rw [trel_pOut_vals hG hargs]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw
  | or t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a, b, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have hga := resolveBoolArg_good hF (argRel_pGood hG ha)
      have hgb := resolveBoolArg_good hF (argRel_pGood hG hb)
      dsimp only [pcStepAux]
      cases hoa : pOut (resolveBoolArg F a) with
      | var pa =>
        have hpa : (Arg.var pa).val = a₂.val := by rw [← hoa, hga.1]
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          have hpb : (Arg.var pb).val = b₂.val := by rw [← hob, hgb.1]
          dsimp only
          by_cases heq : ((pInfo (resolveBoolArg F a)).id == (pInfo (resolveBoolArg F b)).id &&
              (pInfo (resolveBoolArg F a)).id.isSome) = true
          · simp only [heq, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at heq
            rcases heq with ⟨hid, k, hk⟩
            have haρ := (hga.2.1 k hk).2
            have hbρ := (hgb.2.1 k (hk ▸ hid.symm)).2
            rw [haρ] at hbρ
            have heqv : a₂.val = b₂.val := eq_of_heq (Sigma.mk.inj (Option.some.inj hbρ)).2
            dsimp only [OpCode.wp, lift2, vals] at hw
            rw [← heqv] at hw
            have heqb : (a₂.val || a₂.val) = a₂.val := by cases a₂.val <;> rfl
            rw [heqb] at hw
            exact ⟨(a₂.val, ()), hw, hG.cons hga.toPVal⟩
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            dsimp only [Op.wp, op2, OpCode.wp, lift2, vals] at hw ⊢
            rw [hpa, hpb]
            refine ⟨hw, ?_⟩
            have hff : (a₂.val || b₂.val) = false →
                FactsOk ρ next
                    ((pInfo (resolveBoolArg F a)).ff ++ (pInfo (resolveBoolArg F b)).ff) := by
              intro hab
              simp only [Bool.or_eq_false_iff] at hab
              exact (hga.2.2.1.2 hab.1).append (hgb.2.2.1.2 hab.2)
            exact (hG.updTup (ts := [.bool]) (a₂.val || b₂.val, ())).cons
              (wrapBool_good (a₂.val || b₂.val) (fun _ => FactsOk.nil) hff)
        | imm cb =>
          have hvc : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases cb
          · exact ⟨(a₂.val, ()), by simpa [hvc] using hw, hG.cons hga.toPVal⟩
          · exact ⟨(true, ()), by simpa [hvc] using hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
      | imm ca =>
        have hva : a₂.val = ca := hga.imm_eq (by rw [hoa]; rfl)
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases ca
          · exact ⟨(b₂.val, ()), by simpa [hva] using hw, hG.cons hgb.toPVal⟩
          · exact ⟨(true, ()), by simpa [hva] using hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
        | imm cb =>
          have hvb : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          rw [hva, hvb] at hw
          cases ca <;> cases cb
          · exact ⟨(b₂.val, ()), by simpa [hvb] using hw, hG.cons hgb.toPVal⟩
          · exact ⟨(true, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(true, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · exact ⟨(true, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
    | bits _ | float _ | pair _ _ =>
      dsimp only [pcStepAux, Op.wp]
      rw [trel_pOut_vals hG hargs]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw
  | xor t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a, b, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have hga := resolveBoolArg_good hF (argRel_pGood hG ha)
      have hgb := resolveBoolArg_good hF (argRel_pGood hG hb)
      dsimp only [pcStepAux]
      cases hoa : pOut (resolveBoolArg F a) with
      | var pa =>
        have hpa : (Arg.var pa).val = a₂.val := by rw [← hoa, hga.1]
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          have hpb : (Arg.var pb).val = b₂.val := by rw [← hob, hgb.1]
          dsimp only
          by_cases heq : ((pInfo (resolveBoolArg F a)).id == (pInfo (resolveBoolArg F b)).id &&
              (pInfo (resolveBoolArg F a)).id.isSome) = true
          · simp only [heq, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at heq
            rcases heq with ⟨hid, k, hk⟩
            have haρ := (hga.2.1 k hk).2
            have hbρ := (hgb.2.1 k (hk ▸ hid.symm)).2
            rw [haρ] at hbρ
            have heqv : a₂.val = b₂.val := eq_of_heq (Sigma.mk.inj (Option.some.inj hbρ)).2
            dsimp only [OpCode.wp, lift2, vals] at hw
            rw [← heqv] at hw
            have heqb : (a₂.val ^^ a₂.val) = false := by cases a₂.val <;> rfl
            rw [heqb] at hw
            exact ⟨(false, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            dsimp only [Op.wp, op2, OpCode.wp, lift2, vals] at hw ⊢
            rw [hpa, hpb]
            exact ⟨hw, hG.freshPVals _⟩
        | imm cb =>
          have hvc : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases cb
          · exact ⟨(a₂.val, ()), by simpa [hvc] using hw, hG.cons hga.toPVal⟩
          · dsimp only [Op.wp, op2, OpCode.wp, lift2, vals]
            rw [hvc] at hw
            rw [hpa]
            refine ⟨hw, ?_⟩
            have hg' := wrapBool_good (a₂.val ^^ true)
              (fun hv => hga.2.2.1.2 (by revert hv; cases a₂.val <;> decide))
              (fun hv => hga.2.2.1.1 (by revert hv; cases a₂.val <;> decide))
            exact (hG.updTup (ts := [.bool]) (a₂.val ^^ true, ())).cons hg'
      | imm ca =>
        have hva : a₂.val = ca := hga.imm_eq (by rw [hoa]; rfl)
        cases hob : pOut (resolveBoolArg F b) with
        | var pb =>
          have hpb : (Arg.var pb).val = b₂.val := by rw [← hob, hgb.1]
          dsimp only [OpCode.wp, lift2, vals] at hw
          cases ca
          · exact ⟨(b₂.val, ()), by simpa [hva] using hw, hG.cons hgb.toPVal⟩
          · dsimp only [Op.wp, op2, OpCode.wp, lift2, vals]
            rw [hva] at hw
            rw [hpb]
            refine ⟨hw, ?_⟩
            have hg' := wrapBool_good (true ^^ b₂.val)
              (fun hv => hgb.2.2.1.2 (by revert hv; cases b₂.val <;> decide))
              (fun hv => hgb.2.2.1.1 (by revert hv; cases b₂.val <;> decide))
            exact (hG.updTup (ts := [.bool]) (true ^^ b₂.val, ())).cons hg'
        | imm cb =>
          have hvb : b₂.val = cb := hgb.imm_eq (by rw [hob]; rfl)
          dsimp only [OpCode.wp, lift2, vals] at hw
          rw [hva, hvb] at hw
          cases ca <;> cases cb <;>
            exact ⟨(_, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
    | bits _ | float _ | pair _ _ =>
      dsimp only [pcStepAux, Op.wp]
      rw [trel_pOut_vals hG hargs]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw
  | select t =>
    rcases args₁ with ⟨c, x, y, _⟩; rcases args₂ with ⟨c₂, x₂, y₂, _⟩
    rcases hargs with _ | ⟨hc, _ | ⟨hx, _ | ⟨hy, _⟩⟩⟩
    have hgc := resolveBoolArg_good hF (argRel_pGood hG hc)
    dsimp only [pcStepAux]
    cases hoc : pOut (resolveBoolArg F c) with
    | imm cb =>
      have hvc : c₂.val = cb := hgc.imm_eq (by rw [hoc]; rfl)
      dsimp only [OpCode.wp, vals] at hw
      cases cb
      · exact ⟨(y₂.val, ()), by simpa [hvc] using hw, hG.cons (argRel_pGood hG hy).toPVal⟩
      · exact ⟨(x₂.val, ()), by simpa [hvc] using hw, hG.cons (argRel_pGood hG hx).toPVal⟩
    | var pc =>
      have hpc : pc = c₂.val := (congrArg Arg.val hoc).symm.trans hgc.1
      have hx1 := (argRel_pGood hG hx).1
      have hy1 := (argRel_pGood hG hy).1
      dsimp only [Arg.val] at hx1 hy1
      dsimp only [Op.wp, op3, OpCode.wp, vals] at hw ⊢
      cases hpc_b : (pc : Bool)
      · have hc2 : c₂.val = false := hpc.symm.trans hpc_b
        rw [hc2] at hw
        simp only [Arg.val, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        rw [hy1]
        exact ⟨hw, hG.freshPVals _⟩
      · have hc2 : c₂.val = true := hpc.symm.trans hpc_b
        rw [hc2] at hw
        simp only [Arg.val, ↓reduceIte] at hw ⊢
        rw [hx1]
        exact ⟨hw, hG.freshPVals _⟩
  | zext m n =>
    rcases args₁ with ⟨a, _⟩; rcases args₂ with ⟨a₂, _⟩
    rcases hargs with _ | ⟨ha, _⟩
    have hga := argRel_pGood hG ha
    dsimp only [OpCode.wp, vals] at hw
    dsimp only [pcStepAux]
    simp only [hw.1, ↓reduceDIte]
    cases hpk : pFKey a with
    | none =>
      dsimp only [Op.wp, op1, OpCode.wp, vals]
      rw [hga.1]
      exact ⟨hw.1, hw.2, hG.freshPVals _⟩
    | some sk =>
      dsimp only [Op.wp, op1, OpCode.wp, vals]
      rw [hga.1]
      refine ⟨hw.1, hw.2, ?_⟩
      obtain ⟨hsc, heval⟩ := hga.pFKey_eval hpk
      have hup : ∀ k, k < next → PEnv.upd (t := .bits n) ρ next (a₂.val.setWidth n) k = ρ k :=
        fun k hk => PEnv.upd_ne (t := .bits n) (b := next) (k := k) ρ _ (by omega)
      refine (hG.updTup (ts := [.bits n]) (a₂.val.setWidth n, ())).cons
        ⟨rfl, fun k hk => ?_, trivial, fun e he => ?_⟩
      · cases hk; exact ⟨Nat.lt_succ_self _, PEnv.upd_eq (t := .bits n) ρ next _⟩
      · cases he
        exact ⟨a₂.val, rfl, FKey.InScope.mono (Nat.le_succ _) hsc,
          (FKey.eval_mono hup hsc).trans heval, rfl⟩
  | sext m n =>
    rcases args₁ with ⟨a, _⟩; rcases args₂ with ⟨a₂, _⟩
    rcases hargs with _ | ⟨ha, _⟩
    have hga := argRel_pGood hG ha
    dsimp only [OpCode.wp, vals] at hw
    dsimp only [pcStepAux]
    simp only [hw.1, ↓reduceDIte]
    cases hpk : pFKey a with
    | none =>
      dsimp only [Op.wp, op1, OpCode.wp, vals]
      rw [hga.1]
      exact ⟨hw.1, hw.2, hG.freshPVals _⟩
    | some sk =>
      dsimp only [Op.wp, op1, OpCode.wp, vals]
      rw [hga.1]
      refine ⟨hw.1, hw.2, ?_⟩
      obtain ⟨hsc, heval⟩ := hga.pFKey_eval hpk
      have hup : ∀ k, k < next → PEnv.upd (t := .bits n) ρ next (a₂.val.signExtend n) k = ρ k :=
        fun k hk => PEnv.upd_ne (t := .bits n) (b := next) (k := k) ρ _ (by omega)
      refine (hG.updTup (ts := [.bits n]) (a₂.val.signExtend n, ())).cons
        ⟨rfl, fun k hk => ?_, trivial, fun e he => ?_⟩
      · cases hk; exact ⟨Nat.lt_succ_self _, PEnv.upd_eq (t := .bits n) ρ next _⟩
      · cases he
        exact ⟨a₂.val, rfl, FKey.InScope.mono (Nat.le_succ _) hsc,
          (FKey.eval_mono hup hsc).trans heval, rfl⟩
  | cmp o t m h =>
    cases t with
    | bits w =>
      dsimp only [Ty.mask] at h
      subst h
      have hlen : ([Ty.bool] : List Ty).length = 1 := rfl
      rw [hlen]
      rcases args₁ with ⟨a, b, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have hga0 := argRel_pGood hG ha
      have hgb0 := argRel_pGood hG hb
      dsimp only [OpCode.wp, vals, liftCmp, Ty.hasFloat] at hw
      simp only [Bool.false_eq_true, ↓reduceIte] at hw
      cases hia0 : (pOut a).imm? <;> cases hib0 : (pOut b).imm?
      · rw [pcStepAux_cmpBits_n_ F next o hia0]
        have hpc := pcCmpBitsSym_wp hG hF o o hga0 hgb0 hga0 hgb0 rfl hw
        cases hst : pcCmpBitsSym F next o o a b a b <;> simp only [hst] at hpc ⊢ <;> exact hpc
      · rw [pcStepAux_cmpBits_n_ F next o hia0]
        have hpc := pcCmpBitsSym_wp hG hF o o hga0 hgb0 hga0 hgb0 rfl hw
        cases hst : pcCmpBitsSym F next o o a b a b <;> simp only [hst] at hpc ⊢ <;> exact hpc
      · rw [pcStepAux_cmpBits_sn F next o hia0 hib0]
        have hpc := pcCmpBitsSym_wp hG hF o o.swap hga0 hgb0 hgb0 hga0
          (CmpOp.swap_evalBits o a₂.val b₂.val) hw
        cases hst : pcCmpBitsSym F next o o.swap a b b a <;> simp only [hst] at hpc ⊢ <;> exact hpc
      · rename_i ca cb
        rw [pcStepAux_cmpBits_ss F next o hia0 hib0]
        have hca := hga0.imm_eq hia0
        have hcb := hgb0.imm_eq hib0
        rw [hca, hcb] at hw
        exact ⟨(CmpOp.evalBits o ca cb, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
    | bool =>
      dsimp only [Ty.mask] at h
      subst h
      rcases args₁ with ⟨a, b, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have hga := resolveBoolArg_good hF (argRel_pGood hG ha)
      have hgb := resolveBoolArg_good hF (argRel_pGood hG hb)
      dsimp only [OpCode.wp, vals, liftCmp, Ty.hasFloat] at hw
      simp only [Bool.false_eq_true, ↓reduceIte] at hw
      have hn1 : ((none : Option Bool) == some true) = false := rfl
      have hn2 : ((none : Option Bool) == some false) = false := rfl
      dsimp only [pcStepAux]
      cases hia : (pOut (resolveBoolArg F a)).imm? <;>
        cases hib : (pOut (resolveBoolArg F b)).imm? <;> dsimp only
      · simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases hka : pFKey (resolveBoolArg F a) <;> cases hkb : pFKey (resolveBoolArg F b)
        case some.some ka kb =>
          obtain ⟨hkaSc, hkaEv⟩ := hga.pFKey_eval hka
          obtain ⟨hkbSc, hkbEv⟩ := hgb.pFKey_eval hkb
          by_cases hbeq : fKeyBeq ka kb = true
          · simp only [hbeq, ↓reduceIte]
            have heq := fKeyBeq_iff_eq.mp hbeq
            subst heq
            have heqv := Option.some.inj (hkaEv.symm.trans hkbEv)
            rw [heqv, CmpOp.evalBool_isRefl] at hw
            exact ⟨(o.isRefl, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
          · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            cases hq : queryCmpBool F o ka kb with
            | some res =>
              rw [queryCmpBool_sound hF hq hkaEv hkbEv] at hw
              exact ⟨(res, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
            | none =>
              dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [hga.1, hgb.1]
              refine ⟨hw, ?_⟩
              have htf : CmpOp.evalBool o a₂.val b₂.val = true →
                  FactsOk ρ next [.cmpBool o ka kb] := by
                intro hr f hf; rw [List.mem_singleton] at hf; subst hf
                exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, hr⟩
              have hff : CmpOp.evalBool o a₂.val b₂.val = false →
                  FactsOk ρ next [.cmpBool o.neg ka kb] := by
                intro hr f hf; rw [List.mem_singleton] at hf; subst hf
                exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, by rw [CmpOp.neg_evalBool, hr]; rfl⟩
              exact (hG.updTup (ts := [.bool]) (CmpOp.evalBool o a₂.val b₂.val, ())).cons
                (wrapBool_good (CmpOp.evalBool o a₂.val b₂.val) htf hff)
        all_goals
          dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hga.1, hgb.1]
          exact ⟨hw, hG.freshPVals _⟩
      · rename_i cb
        have hcb := hgb.imm_eq hib
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : (o == .eq && some cb == some true) = true
        · simp only [h1, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h1
          rcases h1 with ⟨rfl, rfl⟩
          have he : CmpOp.evalBool .eq a₂.val b₂.val = a₂.val := by
            rw [hcb]; cases a₂.val <;> rfl
          rw [he] at hw
          exact ⟨(a₂.val, ()), hw, hG.cons hga.toPVal⟩
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : (o == .ne && some cb == some false) = true
          · simp only [h3, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h3
            rcases h3 with ⟨rfl, rfl⟩
            have he : CmpOp.evalBool .ne a₂.val b₂.val = a₂.val := by
              rw [hcb]; cases a₂.val <;> rfl
            rw [he] at hw
            exact ⟨(a₂.val, ()), hw, hG.cons hga.toPVal⟩
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            cases hka : pFKey (resolveBoolArg F a) <;> cases hkb : pFKey (resolveBoolArg F b)
            case some.some ka kb =>
              obtain ⟨hkaSc, hkaEv⟩ := hga.pFKey_eval hka
              obtain ⟨hkbSc, hkbEv⟩ := hgb.pFKey_eval hkb
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]
                have heq := fKeyBeq_iff_eq.mp hbeq
                subst heq
                have heqv := Option.some.inj (hkaEv.symm.trans hkbEv)
                rw [heqv, CmpOp.evalBool_isRefl] at hw
                exact ⟨(o.isRefl, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases hq : queryCmpBool F o ka kb with
                | some res =>
                  rw [queryCmpBool_sound hF hq hkaEv hkbEv] at hw
                  exact ⟨(res, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
                | none =>
                  dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [hga.1, hgb.1]
                  refine ⟨hw, ?_⟩
                  have htf : CmpOp.evalBool o a₂.val b₂.val = true →
                      FactsOk ρ next (.cmpBool o ka kb ::
                        (if o == .eq && some cb == some false then (pInfo (resolveBoolArg F a)).ff
                         else if o == .ne && some cb == some true then
                             (pInfo (resolveBoolArg F a)).ff
                         else [])) := by
                    intro hr f hf; rw [List.mem_cons] at hf
                    rcases hf with rfl | hf
                    · exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, hr⟩
                    · rw [hcb] at hr
                      by_cases heqf : (o == .eq && some cb == some false) = true
                      · simp only [heqf, ↓reduceIte] at hf
                        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at heqf
                        rcases heqf with ⟨rfl, rfl⟩
                        have ha0 : a₂.val = false := by
                          revert hr; cases a₂.val <;> decide
                        exact hga.2.2.1.2 ha0 f hf
                      · simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hf
                        by_cases hnet : (o == .ne && some cb == some true) = true
                        · simp only [hnet, ↓reduceIte] at hf
                          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hnet
                          rcases hnet with ⟨rfl, rfl⟩
                          have ha0 : a₂.val = false := by
                            revert hr; cases a₂.val <;> decide
                          exact hga.2.2.1.2 ha0 f hf
                        · simp only [hnet, Bool.false_eq_true, ↓reduceIte] at hf
                          cases hf
                  have hff : CmpOp.evalBool o a₂.val b₂.val = false →
                      FactsOk ρ next (.cmpBool o.neg ka kb ::
                        (if o == .eq && some cb == some false then (pInfo (resolveBoolArg F a)).tf
                         else if o == .ne && some cb == some true then
                             (pInfo (resolveBoolArg F a)).tf
                         else [])) := by
                    intro hr f hf; rw [List.mem_cons] at hf
                    rcases hf with rfl | hf
                    · exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, by rw [CmpOp.neg_evalBool, hr]; rfl⟩
                    · rw [hcb] at hr
                      by_cases heqf : (o == .eq && some cb == some false) = true
                      · simp only [heqf, ↓reduceIte] at hf
                        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at heqf
                        rcases heqf with ⟨rfl, rfl⟩
                        have ha1 : a₂.val = true := by
                          revert hr; cases a₂.val <;> decide
                        exact hga.2.2.1.1 ha1 f hf
                      · simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hf
                        by_cases hnet : (o == .ne && some cb == some true) = true
                        · simp only [hnet, ↓reduceIte] at hf
                          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hnet
                          rcases hnet with ⟨rfl, rfl⟩
                          have ha1 : a₂.val = true := by
                            revert hr; cases a₂.val <;> decide
                          exact hga.2.2.1.1 ha1 f hf
                        · simp only [hnet, Bool.false_eq_true, ↓reduceIte] at hf
                          cases hf
                  exact (hG.updTup (ts := [.bool]) (CmpOp.evalBool o a₂.val b₂.val, ())).cons
                    (wrapBool_good (CmpOp.evalBool o a₂.val b₂.val) htf hff)
            all_goals
              dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [hga.1, hgb.1]; exact ⟨hw, hG.freshPVals _⟩
      · rename_i ca
        have hca := hga.imm_eq hia
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (o == .eq && some ca == some true) = true
        · simp only [h2, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h2
          rcases h2 with ⟨rfl, rfl⟩
          have he : CmpOp.evalBool .eq a₂.val b₂.val = b₂.val := by
            rw [hca]; cases b₂.val <;> rfl
          rw [he] at hw
          exact ⟨(b₂.val, ()), hw, hG.cons hgb.toPVal⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (o == .ne && some ca == some false) = true
          · simp only [h4, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h4
            rcases h4 with ⟨rfl, rfl⟩
            have he : CmpOp.evalBool .ne a₂.val b₂.val = b₂.val := by
              rw [hca]; cases b₂.val <;> rfl
            rw [he] at hw
            exact ⟨(b₂.val, ()), hw, hG.cons hgb.toPVal⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            cases hka : pFKey (resolveBoolArg F a) <;> cases hkb : pFKey (resolveBoolArg F b)
            case some.some ka kb =>
              obtain ⟨hkaSc, hkaEv⟩ := hga.pFKey_eval hka
              obtain ⟨hkbSc, hkbEv⟩ := hgb.pFKey_eval hkb
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]
                have heq := fKeyBeq_iff_eq.mp hbeq
                subst heq
                have heqv := Option.some.inj (hkaEv.symm.trans hkbEv)
                rw [heqv, CmpOp.evalBool_isRefl] at hw
                exact ⟨(o.isRefl, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases hq : queryCmpBool F o ka kb with
                | some res =>
                  rw [queryCmpBool_sound hF hq hkaEv hkbEv] at hw
                  exact ⟨(res, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
                | none =>
                  dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [hga.1, hgb.1]
                  refine ⟨hw, ?_⟩
                  have htf : CmpOp.evalBool o a₂.val b₂.val = true →
                      FactsOk ρ next (.cmpBool o ka kb ::
                        (if o == .eq && some ca == some false then (pInfo (resolveBoolArg F b)).ff
                         else if o == .ne && some ca == some true then
                             (pInfo (resolveBoolArg F b)).ff
                         else [])) := by
                    intro hr f hf; rw [List.mem_cons] at hf
                    rcases hf with rfl | hf
                    · exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, hr⟩
                    · rw [hca] at hr
                      by_cases heqf : (o == .eq && some ca == some false) = true
                      · simp only [heqf, ↓reduceIte] at hf
                        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at heqf
                        rcases heqf with ⟨rfl, rfl⟩
                        have hb0 : b₂.val = false := by
                          revert hr; cases b₂.val <;> decide
                        exact hgb.2.2.1.2 hb0 f hf
                      · simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hf
                        by_cases hnet : (o == .ne && some ca == some true) = true
                        · simp only [hnet, ↓reduceIte] at hf
                          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hnet
                          rcases hnet with ⟨rfl, rfl⟩
                          have hb0 : b₂.val = false := by
                            revert hr; cases b₂.val <;> decide
                          exact hgb.2.2.1.2 hb0 f hf
                        · simp only [hnet, Bool.false_eq_true, ↓reduceIte] at hf
                          cases hf
                  have hff : CmpOp.evalBool o a₂.val b₂.val = false →
                      FactsOk ρ next (.cmpBool o.neg ka kb ::
                        (if o == .eq && some ca == some false then (pInfo (resolveBoolArg F b)).tf
                         else if o == .ne && some ca == some true then
                             (pInfo (resolveBoolArg F b)).tf
                         else [])) := by
                    intro hr f hf; rw [List.mem_cons] at hf
                    rcases hf with rfl | hf
                    · exact ⟨hkaSc, hkbSc, _, _, hkaEv, hkbEv, by rw [CmpOp.neg_evalBool, hr]; rfl⟩
                    · rw [hca] at hr
                      by_cases heqf : (o == .eq && some ca == some false) = true
                      · simp only [heqf, ↓reduceIte] at hf
                        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at heqf
                        rcases heqf with ⟨rfl, rfl⟩
                        have hb1 : b₂.val = true := by
                          revert hr; cases b₂.val <;> decide
                        exact hgb.2.2.1.1 hb1 f hf
                      · simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hf
                        by_cases hnet : (o == .ne && some ca == some true) = true
                        · simp only [hnet, ↓reduceIte] at hf
                          simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hnet
                          rcases hnet with ⟨rfl, rfl⟩
                          have hb1 : b₂.val = true := by
                            revert hr; cases b₂.val <;> decide
                          exact hgb.2.2.1.1 hb1 f hf
                        · simp only [hnet, Bool.false_eq_true, ↓reduceIte] at hf
                          cases hf
                  exact (hG.updTup (ts := [.bool]) (CmpOp.evalBool o a₂.val b₂.val, ())).cons
                    (wrapBool_good (CmpOp.evalBool o a₂.val b₂.val) htf hff)
            all_goals
              dsimp only [Op.wp, op2, OpCode.wp, vals, liftCmp, Ty.hasFloat]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [hga.1, hgb.1]; exact ⟨hw, hG.freshPVals _⟩
      · rename_i ca cb
        have hca := hga.imm_eq hia
        have hcb := hgb.imm_eq hib
        rw [hca, hcb] at hw
        exact ⟨(CmpOp.evalBool o ca cb, ()), hw, hG.cons ⟨rfl, PInfoOk.emptyBool _⟩⟩
    | float _ | pair _ _ =>
      subst h
      dsimp only [pcStepAux, Op.wp]
      rw [trel_pOut_vals hG hargs]
      exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw
  | _ =>
    dsimp only [pcStepAux, Op.wp]
    rw [trel_pOut_vals hG hargs]
    exact OpCode.wp_mono _ _ (fun ys hys => ⟨hys, hG.freshPVals ys⟩) hw

/-! ### `pathCondOpt` `wp`, `wf`, and `callsOk` -/

theorem pathCondOptB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (F : List BoolFact) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (PVal V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (pathCondOptB next F bs).get i xs = pathCondOpt (next + ts.length) F
        (bs.get i (freshPVals ts xs next))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => pathCondOptB_get next F bs i xs

theorem pathCondOpt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (PVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (PVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ next ρ F, PGoodCtx ρ next G → FactsOk ρ next F →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (pathCondOpt next F e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD next ρ F hG hF m hw
    dsimp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hstep := pcStep_wp hG hF hargs hw
      unfold pathCondOpt
      dsimp only [pcStep]
      cases hcl : pcStepAux code args₁ F next with
      | elim res =>
        rw [hcl] at hstep
        rcases hstep with ⟨ys, hk2, hG'⟩
        exact ih res ys hD next ρ F hG' hF m hk2
      | emit op' wrap =>
        rw [hcl] at hstep
        dsimp only [wp]
        exact Op.wp_mono (fun ys hy =>
          ih (wrap ys) ys hD (next + ts.length) _ F hy.2 (hF.updTup ys) m hy.1) hstep
  | load t ha _ ih =>
    intro hD next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, (argRel_pGood hG ha).1 ▸ hv,
      ih (PVal.fresh t v next) v hD (next + 1) (PEnv.upd ρ next v) F (hG.freshOne v)
        (hF.updTup (ts := [t]) (v, ())) m hk⟩
  | store hv ha _ ih =>
    intro hD next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    rw [(argRel_pGood hG ha).1, (argRel_pGood hG hv).1]
    exact ⟨hw.1, ih hD next ρ F hG hF _ hw.2⟩
  | call f hargs _ ih =>
    intro hD next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [trel_pOut_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshPVals _ r next) r hD (next + _) (PEnv.updTup ρ next r) F (hG.freshPVals r)
        (hF.updTup r) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD next ρ F hG hF m hw
    dsimp only [pathCondOpt]
    have hcg := argRel_pGood hG hc
    cases hres : resolveBool? F _ with
    | some bv =>
      have hbv := resolveBool?_sound hF hcg hres
      cases bv
      · exact ihe hD next ρ F hG hF m (hw.2 hbv)
      · exact iht hD next ρ F hG hF m (hw.1 hbv)
    | none =>
      dsimp only [wp] at hw ⊢
      rw [hcg.1]
      exact ⟨fun ht => iht hD next ρ (pushFacts (pInfo _).tf F) hG
        (FactsOk.take 48 ((hcg.2.2.1.1 ht).append hF)) m (hw.1 ht),
        fun hf => ihe hD next ρ (pushFacts (pInfo _).ff F) hG
          (FactsOk.take 48 ((hcg.2.2.1.2 hf).append hF)) m (hw.2 hf)⟩
  | jump hj hargs =>
    intro hD next ρ F hG hF m hw
    have hj' := hD _ hj
    dsimp only at hj'
    dsimp only [wp, pathCondOpt] at hw ⊢
    rw [hj', trel_resolveBoolArgs_vals hF hG hargs]
    exact hw
  | ret hvs =>
    intro _ next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    rw [trel_resolveBoolArgs_vals hF hG hvs]
    exact hw
  | exit f hargs =>
    intro _ next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    rw [trel_resolveBoolArgs_vals hF hG hargs]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hw; exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD next ρ F hG hF m hw
    dsimp only [wp, pathCondOpt] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) next ρ F hG hF m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have h := ihb Js Js i (freshPVals ts xs next) xs (tup_zip_self_eq hD Js) (next + ts.length)
      (PEnv.updTup ρ next xs) F (hG.freshPVals xs) (hF.updTup xs) m' hb
    rw [← pathCondOptB_get next F (b₁ Js) i xs] at h
    exact hclosed i xs m' h

/-! ### `pathCondOpt_wf` and `pathCondOpt_callsOk` -/

section
variable {V₁ V₂ : Ty → Type}

@[expose] def PRelVal (G' : Ctx V₁ V₂) {t : Ty} (a₁ : PVal V₁ t) (a₂ : PVal V₂ t) : Prop :=
  ArgRel G' t a₁.out a₂.out ∧ a₁.info = a₂.info

@[expose] def PRelG (G' : Ctx V₁ V₂) (G : Ctx (PVal V₁) (PVal V₂)) : Prop :=
  ∀ p ∈ G, PRelVal G' p.2.1 p.2.2

theorem PRelVal.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {t : Ty}
    {a₁ : PVal V₁ t} {a₂ : PVal V₂ t} (h : PRelVal G₁ a₁ a₂) : PRelVal G₂ a₁ a₂ :=
  ⟨h.1.weaken hsub, h.2⟩

theorem PRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {t : Ty} {a₁ : PVal V₁ t} {a₂ : PVal V₂ t} (ha : PRelVal G' a₁ a₂) :
    PRelG G' (⟨t, a₁, a₂⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

theorem PRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (hsub : ∀ p ∈ G', p ∈ G'') : PRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem PRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (PVal V₁) ts} → {r₂ : Tup (PVal V₂) ts} →
    TRel (fun _ => PRelVal G') r₁ r₂ → PRelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hr hs => (PRelG.append_tup hG hs).cons hr

theorem PRelVal.fresh {G' : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} (b : Nat)
    (hm : ⟨t, v₁, v₂⟩ ∈ G') : PRelVal G' (PVal.fresh t v₁ b) (PVal.fresh t v₂ b) := by
  cases t <;> exact ⟨.var hm, rfl⟩

private theorem PRelG.freshPVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    PRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshPVals ts xs₁ b) (freshPVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun {t} x n => PVal.fresh t x n) (fun {t} x n => PVal.fresh t x n)
    (P := fun G' _ c₁ c₂ => PRelVal G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => PRelVal.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

theorem PRelG.freshPVals {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    PRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshPVals ts xs₁ b) (freshPVals ts xs₂ b) ++ G) := fun p hp =>
  (List.mem_append.1 hp).elim
    (fun hp => (PRelG.freshPVals_only xs₁ xs₂ b p hp).weaken fun _ hq => List.mem_append_left G' hq)
    (fun hp => (hG p hp).weaken fun _ hq => List.mem_append_right _ hq)

theorem PRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    PRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, PVal.fresh t v₁ b, PVal.fresh t v₂ b⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons (PRelVal.fresh b List.mem_cons_self)

theorem trel_freshPVals_rel {G' : Ctx V₁ V₂} {ts : List Ty} (xs₁ : Tup V₁ ts)
    (xs₂ : Tup V₂ ts) (b : Nat) :
    TRel (fun _ => PRelVal (Tup.zip xs₁ xs₂ ++ G')) (freshPVals ts xs₁ b)
      (freshPVals ts xs₂ b) :=
  TRel_tupFreshWith (fun {t} x n => PVal.fresh t x n) (fun {t} x n => PVal.fresh t x n)
    (P := fun G' _ c₁ c₂ => PRelVal G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => PRelVal.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

theorem argRel_cases {G' : Ctx V₁ V₂} {t : Ty} {x₁ : Arg V₁ t} {x₂ : Arg V₂ t}
    (h : ArgRel G' t x₁ x₂) :
    (∃ v₁ v₂, x₁ = .var v₁ ∧ x₂ = .var v₂ ∧ ⟨t, v₁, v₂⟩ ∈ G') ∨ (∃ c, x₁ = .imm c ∧ x₂ = .imm c) :=
        by
  cases h with
  | var hm => exact .inl ⟨_, _, rfl, rfl, hm⟩
  | imm c => exact .inr ⟨c, rfl, rfl⟩

theorem argRel_pRel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {t : Ty} : {a₁ : Arg (PVal V₁) t} → {a₂ : Arg (PVal V₂) t} → ArgRel G t a₁ a₂ →
    ArgRel G' t (pOut a₁) (pOut a₂) ∧ pInfo a₁ = pInfo a₂
  | .var _, .var _, .var h => hG _ h
  | .imm c, _, .imm _ => ⟨.imm c, rfl⟩

theorem argRel_toPVal_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {t : Ty} : {a₁ : Arg (PVal V₁) t} → {a₂ : Arg (PVal V₂) t} → ArgRel G t a₁ a₂ →
    PRelVal G' (toPVal a₁) (toPVal a₂)
  | .var _, .var _, .var h => hG _ h
  | .imm c, _, .imm _ => ⟨.imm c, rfl⟩

theorem pRelArg_imm?_eq {G' : Ctx V₁ V₂} {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t}
    (h : ArgRel G' t a₁ a₂) : a₁.imm? = a₂.imm? := by
  cases h <;> rfl

theorem pRelArg_pFKey_eq {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {t : Ty} {a₁ : Arg (PVal V₁) t} {a₂ : Arg (PVal V₂) t} (h : ArgRel G t a₁ a₂) :
    pFKey a₁ = pFKey a₂ := by
  obtain ⟨ho, hi⟩ := argRel_pRel hG h
  dsimp only [pFKey]; rw [hi]
  rcases argRel_cases ho with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]

theorem pRelArg_symBits_eq {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {w : Nat} {a₁ : Arg (PVal V₁) (.bits w)} {a₂ : Arg (PVal V₂) (.bits w)}
    (h : ArgRel G (.bits w) a₁ a₂) : symBits? a₁ = symBits? a₂ := by
  obtain ⟨ho, hi⟩ := argRel_pRel hG h
  dsimp only [symBits?]; rw [hi]
  rcases argRel_cases ho with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]

theorem pRelArg_resolveBool?_eq {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) {a₁ : Arg (PVal V₁) .bool} {a₂ : Arg (PVal V₂) .bool}
    (h : ArgRel G .bool a₁ a₂) : resolveBool? F a₁ = resolveBool? F a₂ := by
  obtain ⟨ho, hi⟩ := argRel_pRel hG h
  dsimp only [resolveBool?]; rw [hi]
  rcases argRel_cases ho with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]

theorem argRel_resolveBoolArg {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) {a₁ : Arg (PVal V₁) .bool} {a₂ : Arg (PVal V₂) .bool}
    (h : ArgRel G .bool a₁ a₂) :
    ArgRel G' .bool (pOut (resolveBoolArg F a₁)) (pOut (resolveBoolArg F a₂)) ∧
      pInfo (resolveBoolArg F a₁) = pInfo (resolveBoolArg F a₂) := by
  dsimp only [resolveBoolArg]
  rw [pRelArg_resolveBool?_eq hG F h]
  cases resolveBool? F a₂ with
  | some _ => exact ⟨.imm _, rfl⟩
  | none => exact argRel_pRel hG h

theorem argRel_resolveBoolArg_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) {a₁ : Arg (PVal V₁) .bool} {a₂ : Arg (PVal V₂) .bool}
    (h : ArgRel G .bool a₁ a₂) :
    PRelVal G' (toPVal (resolveBoolArg F a₁)) (toPVal (resolveBoolArg F a₂)) := by
  dsimp only [resolveBoolArg]
  rw [pRelArg_resolveBool?_eq hG F h]
  cases resolveBool? F a₂ with
  | some _ => exact ⟨.imm _, rfl⟩
  | none => exact argRel_toPVal_rel hG h

theorem trel_pOut_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (PVal V₁)) ts} {as₂ : Tup (Arg (PVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupPOut as₁) (tupPOut as₂) :=
  TRel.tupMapArg_rel (fun _ => pOut) (fun _ => pOut) (fun ha => (argRel_pRel hG ha).1) h

theorem trel_resolveBoolArgs_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) :
    {ts : List Ty} → {as₁ : Tup (Arg (PVal V₁)) ts} → {as₂ : Tup (Arg (PVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ →
    TRel (ArgRel G') (tupPOut (resolveBoolArgs F as₁)) (tupPOut (resolveBoolArgs F as₂))
  | [], (), (), .nil => .nil
  | .bool :: _, (_, _), (_, _), .cons ha hs =>
    .cons (argRel_resolveBoolArg hG F ha).1 (trel_resolveBoolArgs_rel hG F hs)
  | .bits _ :: _, (_, _), (_, _), .cons ha hs
  | .float _ :: _, (_, _), (_, _), .cons ha hs
  | .pair _ _ :: _, (_, _), (_, _), .cons ha hs =>
    .cons (argRel_pRel hG ha).1 (trel_resolveBoolArgs_rel hG F hs)

inductive PStepRel (G' : Ctx V₁ V₂) : {ts : List Ty} → PCStep V₁ ts → PCStep V₂ ts → Prop
  | elim {ts : List Ty} {r₁ : Tup (PVal V₁) ts} {r₂ : Tup (PVal V₂) ts} :
      TRel (fun _ => PRelVal G') r₁ r₂ → PStepRel G' (.elim r₁) (.elim r₂)
  | emit {ts : List Ty} {o₁ : Op V₁ ts} {o₂ : Op V₂ ts}
      {w₁ : Tup V₁ ts → Tup (PVal V₁) ts} {w₂ : Tup V₂ ts → Tup (PVal V₂) ts} :
      OpRel G' o₁ o₂ →
      (∀ xs₁ xs₂, TRel (fun _ => PRelVal (Tup.zip xs₁ xs₂ ++ G')) (w₁ xs₁) (w₂ xs₂)) →
      PStepRel G' (.emit o₁ w₁) (.emit o₂ w₂)

theorem wrapBool_rel {G' : Ctx V₁ V₂} (next : Nat) (tf ff : List BoolFact)
    (xs₁ : Tup V₁ [.bool]) (xs₂ : Tup V₂ [.bool]) :
    TRel (fun _ => PRelVal (Tup.zip xs₁ xs₂ ++ G'))
      (wrapBool next tf ff xs₁) (wrapBool next tf ff xs₂) :=
  .cons ⟨.var List.mem_cons_self, rfl⟩ .nil

theorem wrapExt_rel {G' : Ctx V₁ V₂} (next : Nat) (kind : CondThreadOpt.ExtKind)
    (m w : Nat) (hle : m ≤ w) (src : FKey (.bits m)) (xs₁ : Tup V₁ [.bits w])
        (xs₂ : Tup V₂ [.bits w]) :
    TRel (fun _ => PRelVal (Tup.zip xs₁ xs₂ ++ G'))
      (wrapExt next kind m w hle src xs₁) (wrapExt next kind m w hle src xs₂) :=
  .cons ⟨.var List.mem_cons_self, rfl⟩ .nil

theorem pRelVal_imm {G' : Ctx V₁ V₂} (c : Bool) :
    PRelVal G' (pBoolImm c) (pBoolImm c) :=
  ⟨ArgRel.imm (t := .bool) c, rfl⟩

theorem pcCmpBitsSym_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) (next : Nat) {w : Nat} (o o' : CmpOp)
    {a₁ b₁ a₁' b₁' : Arg (PVal V₁) (.bits w)} {a₂ b₂ a₂' b₂' : Arg (PVal V₂) (.bits w)}
    (ha0 : ArgRel G (.bits w) a₁ a₂) (hb0 : ArgRel G (.bits w) b₁ b₂)
    (ha' : ArgRel G (.bits w) a₁' a₂') (hb' : ArgRel G (.bits w) b₁' b₂') :
    PStepRel G' (pcCmpBitsSym F next o o' a₁ b₁ a₁' b₁')
      (pcCmpBitsSym F next o o' a₂ b₂ a₂' b₂') := by
  obtain ⟨hoa, _⟩ := argRel_pRel hG ha0
  obtain ⟨hob, _⟩ := argRel_pRel hG hb0
  obtain ⟨hoa', _⟩ := argRel_pRel hG ha'
  obtain ⟨hob', _⟩ := argRel_pRel hG hb'
  dsimp only [pcCmpBitsSym]
  rw [pRelArg_symBits_eq hG ha', pRelArg_symBits_eq hG hb']
  cases symBits? a₂' <;> cases symBits? b₂' <;> dsimp only
  case some.some sa sb =>
    by_cases hbeq : symBitsBeq sa sb = true
    · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      cases queryCmpBits F o' w sa sb with
      | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
      | none =>
        exact .emit (.mk _ (.cons hoa' (.cons hob' .nil)))
          fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
  all_goals
    exact .emit (.mk _ (.cons hoa (.cons hob .nil))) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next


end

end CondThreadOptImpl

end LeanQbe.T
