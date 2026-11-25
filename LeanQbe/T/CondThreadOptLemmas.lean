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
# Soundness Proofs for `CondThreadOpt`

Proves relational well-formedness (`*_wf`), weakest-precondition semantics preservation (`*_spec`
and `condThread_ok`), and call/exit well-scopedness (`*_callsOk`) for:

* `Func.pathCondOpt` (lexical identity tracking, symbolic `zext`/`sext` keys, comparison
  implication tables `cmpImplies` / `cmpConstImplies` / `factImpliesCmpBits`, and dominating edge
  fact refutation),
* `Func.condThreadWithPlan` / `Func.condThreadPass` (verified `validateCTPlan` + bool-parameter
  splitting and depth-1 bounded constant-arg head threading),
* Combined entrypoints `Func.condThreadOpt`, `condThread_ok`, `Fn.condThreadOpt`, and
  `Func.condThreadLateOpt`.
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

def PEnv.upd (ρ : PEnv) {t : Ty} (b : Nat) (v : Val t) : PEnv :=
  fun k => if k = b then some ⟨t, v⟩ else ρ k

def PEnv.updTup (ρ : PEnv) (b : Nat) : {ts : List Ty} → Tup Val ts → PEnv
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

def FKey.InScope (b : Nat) : {t : Ty} → FKey t → Prop
  | _, .imm _ => True
  | _, .var i => i < b

def FKey.eval (ρ : PEnv) : {t : Ty} → FKey t → Option (Val t)
  | _, .imm c => some c
  | t, .var i =>
    match ρ i with
    | some ⟨t', v⟩ => castTy t' t v
    | none => none

def SymBits.InScope (b : Nat) : {w : Nat} → SymBits w → Prop
  | _, .fkey k => FKey.InScope b k
  | _, .ext _ _ _ _ k => FKey.InScope b k

def SymBits.eval (ρ : PEnv) : {w : Nat} → SymBits w → Option (BitVec w)
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
  · simp only [heq, ↓reduceIte, Option.some.injEq] at h; cases h; rw [beq_iff_eq.mp heq] at hxy; exact hxy
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
                      simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
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
                    simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
                  cases o₂ <;> simp only at himpl <;> cases himpl <;>
                    simp [CmpOp.evalBits, BitVec.ult, BitVec.ule, h1nat] <;> omega
                · cases himpl
            · cases himpl

/-! ### Path-fact invariants (`BoolFact.Holds`, `FactsOk`, `PInfoOk`, `PGood`) -/

def BoolFact.Holds (ρ : PEnv) (b : Nat) : BoolFact → Prop
  | .varEq i c => i < b ∧ ρ i = some ⟨.bool, c⟩
  | .cmpBits o w l r =>
      SymBits.InScope b l ∧ SymBits.InScope b r ∧
        ∃ xl xr : BitVec w, SymBits.eval ρ l = some xl ∧ SymBits.eval ρ r = some xr ∧
          CmpOp.evalBits o xl xr = true
  | .cmpBool o l r =>
      FKey.InScope b l ∧ FKey.InScope b r ∧
        ∃ xl xr : Bool, FKey.eval ρ l = some xl ∧ FKey.eval ρ r = some xr ∧
          CmpOp.evalBool o xl xr = true

def FactsOk (ρ : PEnv) (b : Nat) (F : List BoolFact) : Prop :=
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
def PInfoOk (ρ : PEnv) (b : Nat) {t : Ty} (info : PInfo) (v : Val t) : Prop :=
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

def PGood (ρ : PEnv) (b : Nat) {t : Ty} (p : PVal Val t) (v : Val t) : Prop :=
  p.out.val = v ∧ PInfoOk ρ b p.info v

def PGoodArg (ρ : PEnv) (b : Nat) {t : Ty} (a : Arg (PVal Val) t) (v : Val t) : Prop :=
  (pOut a).val = v ∧ PInfoOk ρ b (pInfo a) v

def PGoodCtx (ρ : PEnv) (b : Nat) (G : Ctx (PVal Val) Val) : Prop :=
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
    exact Prod.ext (resolveBoolArg_good hF (argRel_pGood hG ha)).1 (trel_resolveBoolArgs_vals hF hG hs)
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
    {tf ff : List BoolFact} (htf : r = true → FactsOk ρ next tf) (hff : r = false → FactsOk ρ next ff) :
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

private def pcCmpBitsSym {V : Ty → Type} {w : Nat} (F : List BoolFact) (next : Nat)
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

private theorem pcStepAux_cmpBits_n_ {V : Ty → Type} {w : Nat} (F : List BoolFact)
    (next : Nat) (o : CmpOp) {a b : Arg (PVal V) (.bits w)} (ha : (pOut a).imm? = none) :
    pcStepAux (.cmp o (.bits w)) (a, b, ()) F next = pcCmpBitsSym F next o o a b a b := by
  cases hb : (pOut b).imm? <;> simp only [pcStepAux, pcCmpBitsSym, ha, hb] <;> rfl

private theorem pcStepAux_cmpBits_sn {V : Ty → Type} {w : Nat} (F : List BoolFact)
    (next : Nat) (o : CmpOp) {a b : Arg (PVal V) (.bits w)} {ca : BitVec w}
    (ha : (pOut a).imm? = some ca) (hb : (pOut b).imm? = none) :
    pcStepAux (.cmp o (.bits w)) (a, b, ()) F next = pcCmpBitsSym F next o o.swap a b b a := by
  simp only [pcStepAux, pcCmpBitsSym, ha, hb]
  rfl

private theorem pcStepAux_cmpBits_ss {V : Ty → Type} {w : Nat} (F : List BoolFact)
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
        have hff : CmpOp.evalBits o' va' vb' = false → FactsOk ρ next [.cmpBits o'.neg w sa sb] := by
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
                FactsOk ρ next ((pInfo (resolveBoolArg F a)).tf ++ (pInfo (resolveBoolArg F b)).tf) := by
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
                FactsOk ρ next ((pInfo (resolveBoolArg F a)).ff ++ (pInfo (resolveBoolArg F b)).ff) := by
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
                         else if o == .ne && some cb == some true then (pInfo (resolveBoolArg F a)).ff
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
                         else if o == .ne && some cb == some true then (pInfo (resolveBoolArg F a)).tf
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
                         else if o == .ne && some ca == some true then (pInfo (resolveBoolArg F b)).ff
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
                         else if o == .ne && some ca == some true then (pInfo (resolveBoolArg F b)).tf
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
    (pathCondOptB next F bs).get i xs = pathCondOpt (next + ts.length) F (bs.get i (freshPVals ts xs next))
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

def PRelVal (G' : Ctx V₁ V₂) {t : Ty} (a₁ : PVal V₁ t) (a₂ : PVal V₂ t) : Prop :=
  ArgRel G' t a₁.out a₂.out ∧ a₁.info = a₂.info

def PRelG (G' : Ctx V₁ V₂) (G : Ctx (PVal V₁) (PVal V₂)) : Prop :=
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

private theorem argRel_cases {G' : Ctx V₁ V₂} {t : Ty} {x₁ : Arg V₁ t} {x₂ : Arg V₂ t}
    (h : ArgRel G' t x₁ x₂) :
    (∃ v₁ v₂, x₁ = .var v₁ ∧ x₂ = .var v₂ ∧ ⟨t, v₁, v₂⟩ ∈ G') ∨ (∃ c, x₁ = .imm c ∧ x₂ = .imm c) := by
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
    (m w : Nat) (hle : m ≤ w) (src : FKey (.bits m)) (xs₁ : Tup V₁ [.bits w]) (xs₂ : Tup V₂ [.bits w]) :
    TRel (fun _ => PRelVal (Tup.zip xs₁ xs₂ ++ G'))
      (wrapExt next kind m w hle src xs₁) (wrapExt next kind m w hle src xs₂) :=
  .cons ⟨.var List.mem_cons_self, rfl⟩ .nil

private theorem pRelVal_imm {G' : Ctx V₁ V₂} (c : Bool) :
    PRelVal G' (pBoolImm c) (pBoolImm c) :=
  ⟨ArgRel.imm (t := .bool) c, rfl⟩

private theorem pcCmpBitsSym_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
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

theorem pcStep_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) (next : Nat) {sig ts : List Ty} (code : OpCode sig ts)
    {args₁ : Tup (Arg (PVal V₁)) sig} {args₂ : Tup (Arg (PVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    PStepRel G' (pcStepAux code args₁ F next) (pcStepAux code args₂ F next) := by
  cases code with
  | copy _ =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    cases ha with
    | var h => exact .elim (.cons (hG _ h) .nil)
    | imm c => exact .elim (.cons ⟨.imm c, rfl⟩ .nil)
  | not t =>
    cases t with
    | bool =>
      rcases hargs with _ | ⟨ha, _⟩
      obtain ⟨ho, hi⟩ := argRel_resolveBoolArg hG F ha
      dsimp only [pcStepAux]
      rw [hi]
      rcases argRel_cases ho with ⟨_, _, h1, h2, hm⟩ | ⟨c, h1, h2⟩ <;> simp [h1, h2]
      · exact .emit (.mk _ (.cons (.var hm) .nil)) fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · exact .elim (.cons (pRelVal_imm (!c)) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | and t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases cb
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hva .nil)
      · cases ca
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hvb .nil)
      · cases ca <;> cases cb
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hvb .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | or t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases cb
        · exact .elim (.cons hva .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
      · cases ca
        · exact .elim (.cons hvb .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
      · cases ca <;> cases cb
        · exact .elim (.cons hvb .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | xor t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm false) .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · cases cb
        · exact .elim (.cons hva .nil)
        · rw [hia]
          exact .emit (.mk _ (.cons (.var hma) (.cons (ArgRel.imm (t := .bool) true) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases ca
        · exact .elim (.cons hvb .nil)
        · rw [hib]
          exact .emit (.mk _ (.cons (ArgRel.imm (t := .bool) true) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases ca <;> cases cb <;> exact .elim (.cons (pRelVal_imm _) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | select t =>
    rcases hargs with _ | ⟨hc, _ | ⟨hx, _ | ⟨hy, _⟩⟩⟩
    obtain ⟨hoc, _⟩ := argRel_resolveBoolArg hG F hc
    dsimp only [pcStepAux]
    rcases argRel_cases hoc with ⟨_, _, h1, h2, hm⟩ | ⟨cb, h1, h2⟩ <;> simp [h1, h2]
    · exact .emit (.mk _ (.cons (.var hm) (.cons (argRel_pRel hG hx).1 (.cons (argRel_pRel hG hy).1 .nil))))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · cases cb
      · exact .elim (.cons (argRel_toPVal_rel hG hy) .nil)
      · exact .elim (.cons (argRel_toPVal_rel hG hx) .nil)
  | zext m n =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    rw [pRelArg_pFKey_eq hG ha]
    by_cases hm : m ≤ n
    · simp only [hm, ↓reduceDIte]
      cases pFKey _ with
      | some sk =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => wrapExt_rel next .zext m n hm sk xs₁ xs₂
      | none =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · simp only [hm, ↓reduceDIte]
      exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | sext m n =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    rw [pRelArg_pFKey_eq hG ha]
    by_cases hm : m ≤ n
    · simp only [hm, ↓reduceDIte]
      cases pFKey _ with
      | some sk =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => wrapExt_rel next .sext m n hm sk xs₁ xs₂
      | none =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · simp only [hm, ↓reduceDIte]
      exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | cmp o t m h =>
    subst h
    cases t with
    | bits w =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, _⟩ := argRel_pRel hG ha
      obtain ⟨hob, _⟩ := argRel_pRel hG hb
      have hiea := pRelArg_imm?_eq hoa
      have hieb := pRelArg_imm?_eq hob
      cases h2a : (pOut a₂).imm? <;> cases h2b : (pOut b₂).imm?
      · have h1a : (pOut a₁).imm? = none := hiea.trans h2a
        rw [pcStepAux_cmpBits_n_ F next o h1a, pcStepAux_cmpBits_n_ F next o h2a]
        exact pcCmpBitsSym_rel hG F next o o ha hb ha hb
      · have h1a : (pOut a₁).imm? = none := hiea.trans h2a
        rw [pcStepAux_cmpBits_n_ F next o h1a, pcStepAux_cmpBits_n_ F next o h2a]
        exact pcCmpBitsSym_rel hG F next o o ha hb ha hb
      · rename_i ca
        have h1a : (pOut a₁).imm? = some ca := hiea.trans h2a
        have h1b : (pOut b₁).imm? = none := hieb.trans h2b
        rw [pcStepAux_cmpBits_sn F next o h1a h1b, pcStepAux_cmpBits_sn F next o h2a h2b]
        exact pcCmpBitsSym_rel hG F next o o.swap ha hb hb ha
      · rename_i ca cb
        have h1a : (pOut a₁).imm? = some ca := hiea.trans h2a
        have h1b : (pOut b₁).imm? = some cb := hieb.trans h2b
        rw [pcStepAux_cmpBits_ss F next o h1a h1b, pcStepAux_cmpBits_ss F next o h2a h2b]
        exact .elim (.cons (pRelVal_imm _) .nil)
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      have hn1 : ((none : Option Bool) == some true) = false := rfl
      have hn2 : ((none : Option Bool) == some false) = false := rfl
      dsimp only [pcStepAux]
      have hiea := pRelArg_imm?_eq hoa
      have hieb := pRelArg_imm?_eq hob
      have hfka : pFKey (resolveBoolArg F a₁) = pFKey (resolveBoolArg F a₂) := by
        dsimp only [pFKey]; rw [hia]
        rcases argRel_cases hoa with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
      have hfkb : pFKey (resolveBoolArg F b₁) = pFKey (resolveBoolArg F b₂) := by
        dsimp only [pFKey]; rw [hib]
        rcases argRel_cases hob with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
      rw [hiea, hieb, hfka, hfkb, hia, hib]
      cases (pOut (resolveBoolArg F a₂)).imm? <;>
        cases (pOut (resolveBoolArg F b₂)).imm? <;>
        dsimp only
      · simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
        case some.some ka kb =>
          by_cases hbeq : fKeyBeq ka kb = true
          · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
          · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            cases queryCmpBool F o ka kb with
            | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
            | none =>
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
        all_goals
          exact .emit (.mk _ (.cons hoa (.cons hob .nil))) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · rename_i cb
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : (o == .eq && some cb == some true) = true
        · simp only [h1, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : (o == .ne && some cb == some false) = true
          · simp only [h3, ↓reduceIte]; exact .elim (.cons hva .nil)
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
            case some.some ka kb =>
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases queryCmpBool F o ka kb with
                | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
                | none =>
                  exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                    fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
            all_goals
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · rename_i ca
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (o == .eq && some ca == some true) = true
        · simp only [h2, ↓reduceIte]; exact .elim (.cons hvb .nil)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (o == .ne && some ca == some false) = true
          · simp only [h4, ↓reduceIte]; exact .elim (.cons hvb .nil)
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
            case some.some ka kb =>
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases queryCmpBool F o ka kb with
                | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
                | none =>
                  exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                    fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
            all_goals
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · exact .elim (.cons (pRelVal_imm _) .nil)
    | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | _ =>
    exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next

end

theorem pathCondOpt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (PVal V₁) (PVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (PVal V₁) L₁ rs} {e₂ : Expr (PVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, PRelG G' G → ∀ b F, Wf G' D (pathCondOpt b F e₁) (pathCondOpt b F e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b F
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hrel := pcStep_rel hG F b code hargs
      unfold pathCondOpt
      dsimp only [pcStep]
      generalize pcStepAux code args₁ F b = st₁ at hrel ⊢
      generalize pcStepAux code args₂ F b = st₂ at hrel ⊢
      cases hrel with
      | elim hr => exact ih _ _ (hG.append_tup hr) b F
      | emit hop' hw =>
        refine .let_ hop' fun xs₁ xs₂ => ?_
        have hG' : PRelG (Tup.zip xs₁ xs₂ ++ G') G :=
          hG.weaken fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG'.append_tup (hw xs₁ xs₂)) (b + ts.length) F
  | load t ha _ ih =>
    intro G' hG b F
    exact .load t (argRel_pRel hG ha).1 fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1) F
  | store hv ha _ ih =>
    intro G' hG b F
    exact .store (argRel_pRel hG hv).1 (argRel_pRel hG ha).1 (ih hG b F)
  | call f hargs _ ih =>
    intro G' hG b F
    exact .call f (trel_pOut_rel hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshPVals xs₁ xs₂ b) (b + _) F
  | jnz hc _ _ iht ihe =>
    intro G' hG b F
    obtain ⟨ho, hi⟩ := argRel_pRel hG hc
    dsimp only [pathCondOpt]
    rw [pRelArg_resolveBool?_eq hG F hc]
    cases resolveBool? F _ with
    | some bv => cases bv with | false => exact ihe hG b F | true => exact iht hG b F
    | none => rw [hi]; exact .jnz ho (iht hG b _) (ihe hG b _)
  | jump hj hargs =>
    intro G' hG _ F
    exact .jump hj (trel_resolveBoolArgs_rel hG F hargs)
  | ret hvs =>
    intro G' hG _ F
    exact .ret (trel_resolveBoolArgs_rel hG F hvs)
  | exit f hargs =>
    intro G' hG _ F
    exact .exit f (trel_resolveBoolArgs_rel hG F hargs)
  | hlt => intro _ _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b F
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b F)
    rw [pathCondOptB_get, pathCondOptB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshPVals xs₁ xs₂ b) (b + _) F

private theorem pathCondOptB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (b : Nat) (F : List BoolFact) :
    {sig : List (List Ty)} → (bs₁ : Blocks (PVal (fun _ => Unit)) (fun _ => Unit) rs sig) →
    (bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (pathCondOpt (b + ts.length) F (bs₁.get i (freshPVals ts (Tup.units ts) b))).callsOk
        allowed exits) →
    bs₂.callsOk allowed exits → (pathCondOptB b F bs₁).callsOk allowed exits
  | _, .nil, .nil, _, _ => trivial
  | _, .cons _ _, .cons _ _, h, hc =>
    ⟨h .here hc.1, pathCondOptB_callsOk b F _ _ (fun i => h (.there i)) hc.2⟩

theorem pathCondOpt_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (PVal (fun _ => Unit)) (fun _ => Unit)} {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (PVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b F, e₂.callsOk allowed exits → (pathCondOpt b F e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro b F hc
    unfold pathCondOpt
    dsimp only [pcStep]
    cases pcStepAux op₁.code op₁.args F b with
    | elim res => exact ih res (Tup.units ts) b F hc
    | emit op' wrap => exact ih (wrap (Tup.units ts)) (Tup.units ts) (b + ts.length) F hc
  | load _ _ _ ih => intro b F hc; exact ih _ () (b + 1) F hc
  | store _ _ _ ih => intro b F hc; exact ih b F hc
  | call _ _ _ ih => intro b F hc; exact ⟨hc.1, ih _ (Tup.units _) (b + _) F hc.2⟩
  | jnz _ _ _ iht ihe =>
    intro b F ⟨ht, he⟩
    dsimp only [pathCondOpt]
    cases resolveBool? F _ with
    | some bv => cases bv with | false => exact ihe b F he | true => exact iht b F ht
    | none => exact ⟨iht b _ ht, ihe b _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _; trivial
  | exit _ _ => intro _ _ hc; exact hc
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro b F hc
    exact ⟨pathCondOptB_callsOk b F _ _
      (fun i hci => ihb (Tup.units sig) (Tup.units sig) i _ (Tup.units _) _ F hci) hc.1,
      ihk (Tup.units sig) (Tup.units sig) b F hc.2⟩

end CondThreadOptImpl

theorem Func.pathCondOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.pathCondOpt f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (PVal V₁) (PVal V₂) L₁ L₂ (freshPVals as xs₁ 0) (freshPVals as xs₂ 0)
  have hrel : CondThreadOptImpl.PRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshPVals as xs₁ 0) (freshPVals as xs₂ 0)) := by
    simpa using CondThreadOptImpl.PRelG.freshPVals (G := []) (G' := [])
      (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact CondThreadOptImpl.pathCondOpt_wf hwf hrel as.length []

theorem Func.pathCondOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.pathCondOpt f) xs m Q X := by
  have hwf := hf (PVal Val) Val Cont Cont (freshPVals as xs 0) xs
  have hgood : CondThreadOptImpl.PGoodCtx (CondThreadOptImpl.PEnv.updTup (fun _ => none) 0 xs)
      as.length (Tup.zip (freshPVals as xs 0) xs) := by
    simpa using CondThreadOptImpl.PGoodCtx.freshPVals (ρ := fun _ => none) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact CondThreadOptImpl.pathCondOpt_wp hwf (fun _ hp => nomatch hp) as.length _ [] hgood
    CondThreadOptImpl.FactsOk.nil m h

theorem Func.pathCondOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.pathCondOpt f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits :=
  CondThreadOptImpl.pathCondOpt_callsOk
    (hf (PVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
      (freshPVals as (Tup.units as) 0) (Tup.units as)) as.length [] hc

/-! ## Part 2: Soundness of `condThreadPass` -/

namespace CondThreadOptImpl

/-! ### `Member` tuple operations (`getTupMem`, `dropTupMem`, `insertTupMem`) -/

theorem getTupMem_insertTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (v : f u) → (xs : Tup f (eraseMem m)) →
    getTupMem m (insertTupMem m v xs) = v
  | _ :: _, .here, _, _ => rfl
  | _ :: _, .there m, v, xs => getTupMem_insertTupMem m v xs.2

theorem dropTupMem_insertTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (v : f u) → (xs : Tup f (eraseMem m)) →
    dropTupMem m (insertTupMem m v xs) = xs
  | _ :: _, .here, _, _ => rfl
  | _ :: _, .there m, v, xs => Prod.ext rfl (dropTupMem_insertTupMem m v xs.2)

theorem insertTupMem_get_drop {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup f ts) →
    insertTupMem m (getTupMem m xs) (dropTupMem m xs) = xs
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => Prod.ext rfl (insertTupMem_get_drop m xs)

theorem getTupMem_vals {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (args : Tup (Arg Val) ts) →
    (getTupMem m args).val = getTupMem m (vals args)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, args) => getTupMem_vals m args

theorem dropTupMem_vals {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (args : Tup (Arg Val) ts) →
    vals (dropTupMem m args) = dropTupMem m (vals args)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, args) => Prod.ext rfl (dropTupMem_vals m args)

theorem getTupMem_toArgTup {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup V ts) →
    getTupMem m (toArgTup xs) = .var (getTupMem m xs)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => getTupMem_toArgTup m xs

theorem dropTupMem_toArgTup {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup V ts) →
    dropTupMem m (toArgTup xs) = toArgTup (dropTupMem m xs)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => Prod.ext rfl (dropTupMem_toArgTup m xs)

theorem trel_getTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {xs : Tup f ts} → {ys : Tup g ts} →
    TRel R xs ys → R u (getTupMem m xs) (getTupMem m ys)
  | _ :: _, .here, (_, _), (_, _), .cons h _ => h
  | _ :: _, .there m, (_, _), (_, _), .cons _ hs => trel_getTupMem m hs

theorem trel_dropTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {xs : Tup f ts} → {ys : Tup g ts} →
    TRel R xs ys → TRel R (dropTupMem m xs) (dropTupMem m ys)
  | _ :: _, .here, (_, _), (_, _), .cons _ hs => hs
  | _ :: _, .there m, (_, _), (_, _), .cons h hs => .cons h (trel_dropTupMem m hs)

theorem trel_insertTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {v₁ : f u} → {v₂ : g u} →
    R u v₁ v₂ → {xs : Tup f (eraseMem m)} → {ys : Tup g (eraseMem m)} →
    TRel R xs ys → TRel R (insertTupMem m v₁ xs) (insertTupMem m v₂ ys)
  | _ :: _, .here, _, _, hv, _, _, hxs => .cons hv hxs
  | _ :: _ :: _, .there m, _, _, hv, _, _, hxs => by
    cases hxs with
    | cons hx hxs' => exact .cons hx (trel_insertTupMem m hv hxs')

/-! ### `immsTup` and `evalThreadLet?` lemmas -/

private theorem tupImms?_vals :
    {ts : List Ty} → {a : Tup (Arg Val) ts} → {cs : Tup Val ts} →
    tupImms? a = some cs → vals a = cs
  | [], (), (), _ => rfl
  | _ :: _, (.imm _, _), (_, _), h => by
    dsimp only [tupImms?, Arg.imm?, Option.bind] at h
    cases hc : tupImms? _ with
    | none => rw [hc] at h; cases h
    | some cs' =>
      rw [hc] at h; simp only [Option.pure_def] at h
      cases h; exact Prod.ext rfl (tupImms?_vals hc)
  | _ :: _, (.var _, _), (_, _), h => by dsimp only [tupImms?, Arg.imm?] at h; cases h

theorem immsTup_vals : {ts : List Ty} → (cs : Tup Val ts) → vals (immsTup cs) = cs
  | [], () => rfl
  | _ :: _, (_, cs) => Prod.ext rfl (immsTup_vals cs)

theorem trel_immsTup {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (cs : Tup Val ts) → TRel (ArgRel G) (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (c, cs) => .cons (.imm c) (trel_immsTup cs)

theorem trel_immsTup_shape {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (cs : Tup Val ts) →
    TRel (fun _ a₁ a₂ => @Arg.imm? V₁ _ a₁ = @Arg.imm? V₂ _ a₂) (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (_, cs) => .cons rfl (trel_immsTup_shape cs)

theorem tupImms?_shape_eq {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} →
    TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂ →
    tupImms? a₁ = tupImms? a₂
  | [], (), (), .nil => rfl
  | _ :: _, (x₁, xs₁), (x₂, xs₂), .cons hx hxs => by
    dsimp only [tupImms?]
    rw [hx, tupImms?_shape_eq hxs]

theorem evalThreadLet?_wp {sig dts : List Ty} (code : OpCode sig dts)
    {args₁ : Tup (Arg Val) sig} {args₂ : Tup (Arg Val) sig} (hargs : vals args₁ = vals args₂)
    {out : Tup (Arg Val) dts} (heval : evalThreadLet? code args₁ = some out)
    {post : Tup Val dts → Prop} (hw : code.wp (vals args₂) post) :
    post (vals out) := by
  rw [← hargs] at hw
  cases code with
  | copy _ =>
    rcases args₁ with ⟨a, _⟩
    dsimp only [evalThreadLet?] at heval; cases heval
    exact hw
  | _ =>
    all_goals
      dsimp only [evalThreadLet?] at heval
      split at heval
      · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heval
        rcases heval with ⟨cs, hcs, rfl⟩
        rw [immsTup_vals]
        rcases hcs with ⟨vts, hv, hev⟩
        have hvv := tupImms?_vals hv
        rw [hvv] at hw
        exact OpCode.eval?_sound _ vts post hev hw
      · cases heval

theorem evalThreadLet?_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg V₁) sig} {a₂ : Tup (Arg V₂) sig}
    (ha : TRel (ArgRel G') a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (ArgRel G') o₁ o₂ := by
  have hsh : TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂ :=
    TRel.mono (fun _ _ _ h => by cases h <;> rfl) ha
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases ha with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

theorem evalThreadLet?_shape {V₁ V₂ : Ty → Type} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg V₁) sig} {a₂ : Tup (Arg V₂) sig}
    (hsh : TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) o₁ o₂ := by
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases hsh with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup_shape cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

/-! ### Relational invariants for `CTOptV`, `rewriteCTAux`, and `validateCTPlan` -/

/-- Shape compatibility between `Arg V₁` and `Arg V₂` (identical immediate/variable tag and constant). -/
def ArgShapeEq {V₁ V₂ : Ty → Type} {t : Ty} (a₁ : Arg V₁ t) (a₂ : Arg V₂ t) : Prop :=
  a₁.imm? = a₂.imm?

theorem ArgShapeEq.flattenArg {V₁ V₂ : Ty → Type} {G : Ctx (Arg V₁) (Arg V₂)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} :
    ArgRel G t a₁ a₂ → ArgShapeEq (LeanQbe.T.flattenArg a₁) (LeanQbe.T.flattenArg a₂)
  | .var hm => hG _ hm
  | .imm _ => rfl

theorem trel_flattenArgs_shape {V₁ V₂ : Ty → Type} {G : Ctx (Arg V₁) (Arg V₂)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) {ts : List Ty} {a₁ : Tup (Arg (Arg V₁)) ts}
    {a₂ : Tup (Arg (Arg V₂)) ts} (ha : TRel (ArgRel G) a₁ a₂) :
    TRel (fun _ => ArgShapeEq) (flattenArgs a₁) (flattenArgs a₂) :=
  TRel.tupMapArg_rel (fun _ => flattenArg) (fun _ => flattenArg)
    (fun h => ArgShapeEq.flattenArg hG h) ha

theorem toOptArgTup_shape_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (toOptArgTup xs₁) (toOptArgTup xs₂), ArgShapeEq p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact toOptArgTup_shape_zip _ _ _ hp

theorem none_toOptArgTup_shape_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (noneArgTup (V := V₁) ts) (toOptArgTup xs₂), ArgShapeEq p.2.1 p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact none_toOptArgTup_shape_zip _ _ hp

theorem ArgShapeEq.mem_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} →
    TRel (fun _ => ArgShapeEq) a₁ a₂ → ∀ p ∈ Tup.zip a₁ a₂, ArgShapeEq p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact ArgShapeEq.mem_zip hs _ hp

/-- Optionalized operand relation disallowing `.var none`. -/
inductive OptArgRel {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) :
    (t : Ty) → Arg (CTOptV V₁) t → Arg (CTOptV V₂) t → Prop
  | var {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} : ⟨t, v₁, v₂⟩ ∈ G' →
      OptArgRel G' t (.var (some v₁)) (.var (some v₂))
  | imm {t : Ty} (c : Val t) : OptArgRel G' t (.imm c) (.imm c)

theorem OptArgRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) {t : Ty} {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G₁ t a₁ a₂ → OptArgRel G₂ t a₁ a₂
  | .var hm => .var (hG _ hm)
  | .imm c => .imm c

theorem OptArgRel.shape {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G' t a₁ a₂ → ArgShapeEq a₁ a₂
  | .var _ => rfl
  | .imm _ => rfl

theorem OptArgRel.toRealArg? {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G' t a₁ a₂ →
    ∃ r₁ r₂, LeanQbe.T.CondThreadOpt.toRealArg? a₁ = some r₁ ∧
      LeanQbe.T.CondThreadOpt.toRealArg? a₂ = some r₂ ∧ ArgRel G' t r₁ r₂
  | .var hm => ⟨.var _, .var _, rfl, rfl, .var hm⟩
  | .imm c => ⟨.imm c, .imm c, rfl, rfl, .imm c⟩

theorem trel_toRealArgs?_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {a₁ : Tup (Arg (CTOptV V₁)) ts} → {a₂ : Tup (Arg (CTOptV V₂)) ts} →
    TRel (OptArgRel G') a₁ a₂ →
    ∃ r₁ r₂, LeanQbe.T.CondThreadOpt.toRealArgs? a₁ = some r₁ ∧
      LeanQbe.T.CondThreadOpt.toRealArgs? a₂ = some r₂ ∧ TRel (ArgRel G') r₁ r₂
  | [], (), (), .nil => ⟨(), (), rfl, rfl, .nil⟩
  | _ :: _, (_, _), (_, _), .cons ha has => by
    obtain ⟨r₁, r₂, hr₁, hr₂, hra⟩ := ha.toRealArg?
    obtain ⟨rs₁, rs₂, hrs₁, hrs₂, hras⟩ := trel_toRealArgs?_rel has
    refine ⟨(r₁, rs₁), (r₂, rs₂), ?_, ?_, .cons hra hras⟩
    · dsimp only [LeanQbe.T.CondThreadOpt.toRealArgs?]; rw [hr₁, hrs₁]; rfl
    · dsimp only [LeanQbe.T.CondThreadOpt.toRealArgs?]; rw [hr₂, hrs₂]; rfl

theorem OptArgRel.flattenArg {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {t : Ty}
    {a₁ : Arg (Arg (CTOptV V₁)) t} {a₂ : Arg (Arg (CTOptV V₂)) t} :
    ArgRel G t a₁ a₂ → OptArgRel G' t (LeanQbe.T.flattenArg a₁) (LeanQbe.T.flattenArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

theorem trel_flattenArgs_opt {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {ts : List Ty}
    {a₁ : Tup (Arg (Arg (CTOptV V₁))) ts} {a₂ : Tup (Arg (Arg (CTOptV V₂))) ts}
    (ha : TRel (ArgRel G) a₁ a₂) :
    TRel (OptArgRel G') (flattenArgs a₁) (flattenArgs a₂) :=
  TRel.tupMapArg_rel (fun _ => flattenArg) (fun _ => flattenArg)
    (fun h => OptArgRel.flattenArg hG h) ha

theorem toOptArgTup_trel {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (OptArgRel (Tup.zip xs₁ xs₂)) (toOptArgTup xs₁) (toOptArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_x₁, xs₁), (_x₂, xs₂) =>
    .cons (.var List.mem_cons_self)
      (TRel.mono (fun _ _ _ h => h.weaken (fun _ hp => List.mem_cons_of_mem _ hp))
        (toOptArgTup_trel xs₁ xs₂))

theorem mem_zip_optArgRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {a₁ : Tup (Arg (CTOptV V₁)) ts} → {a₂ : Tup (Arg (CTOptV V₂)) ts} →
    TRel (OptArgRel G') a₁ a₂ → ∀ p ∈ Tup.zip a₁ a₂, OptArgRel G' p.1 p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact mem_zip_optArgRel hs _ hp

theorem ctx_optArgRel_append {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} {H' : Ctx V₁ V₂}
    {H : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    (hH : ∀ p ∈ H, OptArgRel H' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G, OptArgRel (H' ++ G') p.1 p.2.1 p.2.2 := fun p hp =>
  (List.mem_append.1 hp).elim
    (fun hm => (hH p hm).weaken (fun _ h => List.mem_append_left _ h))
    (fun hm => (hG p hm).weaken (fun _ h => List.mem_append_right _ h))

theorem ctx_optArgRel_append_same {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} {H : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    (hH : ∀ p ∈ H, OptArgRel G' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G, OptArgRel G' p.1 p.2.1 p.2.2 := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hG p)

theorem ctx_optArgRel_cons_var {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    ∀ p ∈ (⟨t, .var (some v₁), .var (some v₂)⟩ :: G),
      OptArgRel (⟨t, v₁, v₂⟩ :: G') p.1 p.2.1 p.2.2 := fun p hp => by
  cases hp with
  | head => exact .var List.mem_cons_self
  | tail _ hm => exact (hG p hm).weaken (fun _ h => List.mem_cons_of_mem _ h)

theorem mem_zip_toOptArgTup {V₁ V₂ : Ty → Type} {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    ∀ p ∈ Tup.zip (toOptArgTup xs₁) (toOptArgTup xs₂), OptArgRel (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2 :=
  mem_zip_optArgRel (toOptArgTup_trel xs₁ xs₂)

theorem trel_immsTup_opt {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → (cs : Tup Val ts) →
    TRel (OptArgRel G') (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (c, cs) => .cons (.imm c) (trel_immsTup_opt cs)

theorem evalThreadLet?_opt_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg (CTOptV V₁)) sig} {a₂ : Tup (Arg (CTOptV V₂)) sig}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (OptArgRel G') o₁ o₂ := by
  have hsh : TRel (fun _ => ArgShapeEq) a₁ a₂ := TRel.mono (fun _ _ _ h => h.shape) ha
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases ha with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup_opt cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

/-- Structural shape equivalence between two `CTTarget`s (agreeing on `.canEmit`). -/
def CTTargetShape {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} :
    {ts : List Ty} → CTTarget V₁ L₁ ts → CTTarget V₂ L₂ ts → Prop
  | _, .keep _, .keep _ => True
  | _, .dead, .dead => True
  | _, .split m₁ lT1? lF1? lD1?, .split m₂ lT2? lF2? lD2? =>
      HEq m₁ m₂ ∧ (lT1?.isSome = lT2?.isSome) ∧ (lF1?.isSome = lF2?.isSome) ∧
        (lD1?.isSome = lD2?.isSome)
  | _, _, _ => False

theorem CTTargetShape.canEmit_eq {W₁ W₂ V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {ts : List Ty} {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts}
    (ht : CTTargetShape t₁ t₂) {a₁ : Tup (Arg W₁) ts} {a₂ : Tup (Arg W₂) ts}
    (ha : TRel (fun _ => ArgShapeEq) a₁ a₂) : t₁.canEmit a₁ = t₂.canEmit a₂ := by
  cases t₁ <;> cases t₂ <;> dsimp only [CTTargetShape] at ht <;> try contradiction
  · rfl
  · rfl
  · rcases ht with ⟨hm, hT, hF, hD⟩
    cases hm
    have hmem := trel_getTupMem ‹Member .bool ts› ha
    dsimp only [CTTarget.canEmit]
    cases e₁ : getTupMem _ a₁ <;> cases e₂ : getTupMem _ a₂ <;> rw [e₁, e₂] at hmem
    · simp only [hD, hT, hF]
    · dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
    · dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
    · rename_i b₁ b₂
      dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
      first | (cases b₁ <;> simp only [hT, hF]) | (cases b₂ <;> simp only [hT, hF])

/-- Full relational invariant on `CTTarget` for `Wf` proofs (`rewriteCTAux_wf`). -/
def CTTargetRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    (D' : Ctx L₁ L₂) : {ts : List Ty} → CTTarget V₁ L₁ ts → CTTarget V₂ L₂ ts → Prop
  | ts, .keep l₁, .keep l₂ => ⟨ts, l₁, l₂⟩ ∈ D'
  | _, .dead, .dead => True
  | ts, .split m₁ lT1? lF1? lD1?, .split m₂ lT2? lF2? lD2? =>
      ∃ hm : m₁ = m₂,
        ORel (fun l₁ l₂ => ⟨eraseMem m₁, l₁, l₂⟩ ∈ D') lT1? (hm ▸ lT2?) ∧
        ORel (fun l₁ l₂ => ⟨eraseMem m₁, l₁, l₂⟩ ∈ D') lF1? (hm ▸ lF2?) ∧
        ORel (fun l₁ l₂ => ⟨ts, l₁, l₂⟩ ∈ D') lD1? lD2?
  | _, _, _ => False

theorem CTTargetRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {D₁ D₂ : Ctx L₁ L₂} (hD : ∀ p ∈ D₁, p ∈ D₂) {ts : List Ty}
    {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} :
    CTTargetRel D₁ t₁ t₂ → CTTargetRel D₂ t₁ t₂ := by
  cases t₁ with
  | keep _ =>
    cases t₂ <;> dsimp only [CTTargetRel] <;> try exact fun h => h
    exact fun h => hD _ h
  | dead => cases t₂ <;> dsimp only [CTTargetRel] <;> exact fun h => h
  | split m₁ lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ | dead => dsimp only [CTTargetRel]; exact fun h => h
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel]
      rintro ⟨rfl, hT, hF, hDi⟩
      refine ⟨rfl, ?_, ?_, ?_⟩
      · cases lT1? <;> cases lT2? <;> simp_all [ORel]
      · cases lF1? <;> cases lF2? <;> simp_all [ORel]
      · cases lD1? <;> cases lD2? <;> simp_all [ORel]

theorem CTTargetRel.shape {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {D' : Ctx L₁ L₂} {ts : List Ty} {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} :
    CTTargetRel D' t₁ t₂ → CTTargetShape t₁ t₂ := by
  cases t₁ with
  | keep _ | dead =>
    cases t₂ <;> dsimp only [CTTargetRel, CTTargetShape] <;>
      first | exact fun h => h | exact fun _ => trivial
  | split m₁ lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ | dead => dsimp only [CTTargetRel, CTTargetShape]; exact fun h => h
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel, CTTargetShape]
      rintro ⟨rfl, hT, hF, hD⟩
      refine ⟨HEq.rfl, ?_, ?_, ?_⟩
      · cases lT1? <;> cases lT2? <;> simp_all [ORel]
      · cases lF1? <;> cases lF2? <;> simp_all [ORel]
      · cases lD1? <;> cases lD2? <;> simp_all [ORel]

theorem CTTargetRel.emit_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {rs ts : List Ty}
    {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} (ht : CTTargetRel D' t₁ t₂)
    {a₁ : Tup (Arg (CTOptV V₁)) ts} {a₂ : Tup (Arg (CTOptV V₂)) ts}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    Wf G' D' (t₁.emit (rs := rs) a₁) (t₂.emit (rs := rs) a₂) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel ha
  cases t₁ with
  | keep _ =>
    cases t₂ <;> dsimp only [CTTargetRel] at ht <;> try contradiction
    dsimp only [CTTarget.emit]; rw [hr₁, hr₂]; exact .jump ht hr
  | dead =>
    cases t₂ <;> dsimp only [CTTargetRel] at ht <;> try contradiction
    exact .hlt
  | split m lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ => dsimp only [CTTargetRel] at ht; try exact False.elim ht
    | dead => dsimp only [CTTargetRel] at ht; try exact False.elim ht
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel] at ht
      rcases ht with ⟨rfl, hT, hF, hD⟩
      have hmem := trel_getTupMem m ha
      obtain ⟨dr₁, dr₂, hdr₁, hdr₂, hdr⟩ := trel_toRealArgs?_rel (trel_dropTupMem m ha)
      dsimp only [CTTarget.emit]
      cases e₁ : getTupMem m a₁ <;> cases e₂ : getTupMem m a₂ <;> rw [e₁, e₂] at hmem
      · cases hmem
        · rename_i v₁ v₂ hm
          dsimp only
          cases lD1? <;> cases lD2? <;> dsimp only [ORel] at hD <;> try contradiction
          · rw [hdr₁, hdr₂]
            cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hT <;> try contradiction
            · exact .hlt
            · cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hF <;> try contradiction
              · exact .hlt
              · exact .jnz (.var hm) (.jump hT hdr) (.jump hF hdr)
          · rw [hr₁, hr₂]; exact .jump hD hr
      · cases hmem
      · cases hmem
      · cases hmem; next b =>
        cases b
        · rw [hdr₁, hdr₂]
          cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hF <;> try contradiction
          · exact .hlt
          · exact .jump hF hdr
        · rw [hdr₁, hdr₂]
          cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hT <;> try contradiction
          · exact .hlt
          · exact .jump hT hdr

/-- `CTLabelRel` pairs two `CTLabel`s for both `Wf` proofs and `validateInline` simulation. -/
def CTLabelRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) {ts : List Ty}
    (l₁ : CTLabel V₁ L₁ rs ts) (l₂ : CTLabel V₂ L₂ rs ts) : Prop :=
  CTTargetRel D' l₁.target l₂.target ∧
    (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
      ∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
        TRel (OptArgRel G'') a₁ a₂ → ORel (Wf G'' D'') (l₁.inline? a₁) (l₂.inline? a₂)) ∧
    (∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
      TRel (fun _ => ArgShapeEq) a₁ a₂ → (l₁.inline? a₁).isSome = (l₂.inline? a₂).isSome)

theorem CTLabelRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂) {ts : List Ty}
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (h : CTLabelRel G₁ D₁ l₁ l₂) : CTLabelRel G₂ D₂ l₁ l₂ :=
  ⟨h.1.weaken hD,
   fun hG' hD' => h.2.1 (fun _ hp => hG' _ (hG _ hp)) (fun _ hp => hD' _ (hD _ hp)),
   h.2.2⟩

def CTDRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂)
    (D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, CTLabelRel G' D' p.2.1 p.2.2

theorem CTDRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂} {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂) (h : CTDRel G₁ D₁ D) : CTDRel G₂ D₂ D :=
  fun p hp => (h p hp).weaken hG hD

theorem CTDRel.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {H D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hH : CTDRel G' D' H) (hD : CTDRel G' D' D) : CTDRel G' D' (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

/-- Inline-safety coherence for `CTLabel`: matching `canEmit` and `inline?.isSome` under shape eq. -/
def CTLabelSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (l₁ : CTLabel V₁ L₁ rs ts) (l₂ : CTLabel V₂ L₂ rs ts) : Prop :=
  CTTargetShape l₁.target l₂.target ∧
    ∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
      TRel (fun _ => ArgShapeEq) a₁ a₂ → (l₁.inline? a₁).isSome = (l₂.inline? a₂).isSome

def CTDSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, CTLabelSim p.2.1 p.2.2

theorem CTDSim.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {H D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hH : CTDSim H) (hD : CTDSim D) : CTDSim (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem CTLabelRel.toSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {ts : List Ty}
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (h : CTLabelRel G' D' l₁ l₂) : CTLabelSim l₁ l₂ :=
  ⟨h.1.shape, h.2.2⟩

theorem CTDRel.toSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} (h : CTDRel G' D' D) : CTDSim D :=
  fun p hp => (h p hp).toSim

theorem CTLabel.emitJump_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (tryInl : Bool)
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts} (hl : CTLabelRel G' D' l₁ l₂)
    {a₁ : Tup (Arg (CTOptV V₁)) ts} {a₂ : Tup (Arg (CTOptV V₂)) ts}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    Wf G' D' (l₁.emitJump tryInl a₁) (l₂.emitJump tryInl a₂) := by
  dsimp only [CTLabel.emitJump]
  cases tryInl
  · exact hl.1.emit_wf ha
  · have hor := hl.2.1 (fun _ h => h) (fun _ h => h) a₁ a₂ ha
    cases e₁ : l₁.inline? a₁ <;> cases e₂ : l₂.inline? a₂ <;> rw [e₁, e₂] at hor <;>
      dsimp only [ORel] at hor
    · exact hl.1.emit_wf ha
    · exact hor

/-! ### Inline peeling, inline validation, and `rewriteCTInline` relational soundness -/

theorem peelThreadHead_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → {G' : Ctx V₁ V₂} →
    (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) →
    let r₁ := peelThreadHead fuel res p e₁
    let r₂ := peelThreadHead fuel res p e₂
    r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
      ∃ G₁, (∀ p ∈ G₁, OptArgRel G' p.1 p.2.1 p.2.2) ∧ Wf G₁ D r₁.2.2 r₂.2.2
  | 0, _, _, G, _, _, _, hwf, _, hG => ⟨rfl, rfl, G, hG, hwf⟩
  | fuel + 1, res, p, G, D, _, _, hwf, G', hG => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_opt_rel code (trel_flattenArgs_opt hG hargs)
        dsimp only [peelThreadHead]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]; exact ⟨rfl, rfl, G, hG, .let_ (.mk code hargs) hk⟩
        · rw [he₁, he₂]
          exact peelThreadHead_wf fuel res pk (hk o₁ o₂)
            (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        have hfl := OptArgRel.flattenArg hG hc
        dsimp only [peelThreadHead]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
        · exact ⟨rfl, rfl, G, hG, .jnz hc ht he⟩
        · cases hfl
        · cases hfl
        · cases hfl; next c => cases c with
          | false => exact peelThreadHead_wf fuel true pe he hG
          | true => exact peelThreadHead_wf fuel true pt ht hG
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | _ => exact ⟨rfl, rfl, G, hG, hwf⟩

theorem peelThreadHead_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → (∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) →
    let r₁ := peelThreadHead fuel res p e₁
    let r₂ := peelThreadHead fuel res p e₂
    r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
      ∃ G₁, (∀ p ∈ G₁, ArgShapeEq p.2.1 p.2.2) ∧ Wf G₁ D r₁.2.2 r₂.2.2
  | 0, _, _, G, _, _, _, hwf, hG => ⟨rfl, rfl, G, hG, hwf⟩
  | fuel + 1, res, p, G, D, _, _, hwf, hG => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hG hargs)
        dsimp only [peelThreadHead]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]; exact ⟨rfl, rfl, G, hG, .let_ (.mk code hargs) hk⟩
        · rw [he₁, he₂]
          exact peelThreadHead_sim fuel res pk (hk o₁ o₂) fun p hp =>
            (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hG p)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        have hsh := ArgShapeEq.flattenArg hG hc
        dsimp only [peelThreadHead]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hsh
        · exact ⟨rfl, rfl, G, hG, .jnz hc ht he⟩
        · cases hsh
        · cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          first
          | (cases b₁ <;> first
            | exact peelThreadHead_sim fuel true pe he hG
            | exact peelThreadHead_sim fuel true pt ht hG)
          | (cases b₂ <;> first
            | exact peelThreadHead_sim fuel true pe he hG
            | exact peelThreadHead_sim fuel true pt ht hG)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | _ => exact ⟨rfl, rfl, G, hG, hwf⟩

private theorem mem_zip_noneArgTup_shape {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → ∀ p ∈ Tup.zip (noneArgTup (V := V₁) ts) (noneArgTup (V := V₂) ts),
      ArgShapeEq p.2.1 p.2.2
  | [], _, hp => nomatch hp
  | _ :: _, _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact mem_zip_noneArgTup_shape _ hp

theorem validateInline_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (budget : Nat) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → (∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) → CTDSim D →
    validateInline budget p e₁ = validateInline budget p e₂
  | 0, _, _, _, _, _, _, _, _ => by simp only [validateInline]
  | b + 1, p, G, D, _, _, hwf, hG, hD => by
    cases p with
    | node1 pk =>
      cases hwf with
      | let_ hop hk =>
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hG hargs)
        dsimp only [validateInline]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
            (fun p hp => (List.mem_append.1 hp).elim
              (mem_zip_noneArgTup_shape p) (hG p)) hD)
        · rw [he₁, he₂]
          exact validateInline_sim (b + 1) pk (hk o₁ o₂)
            (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hG p)) hD
      | load _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
          (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hG p hp') hD)
      | store _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk hk hG hD)
      | call _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
          (fun p hp => (List.mem_append.1 hp).elim (mem_zip_noneArgTup_shape p) (hG p)) hD)
      | _ => rfl
    | node2 pt pe =>
      cases hwf with
      | jnz hc ht he =>
        have hsh := ArgShapeEq.flattenArg hG hc
        dsimp only [validateInline]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hsh
        · rw [validateInline_sim b pt ht hG hD]
          dsimp only [Bind.bind, Option.bind]
          cases validateInline b pt _ with
          | none => rfl
          | some st => dsimp only; rw [validateInline_sim (b - st) pe he hG hD]
        · cases hsh
        · cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          first
          | cases b₁ with
            | false => exact validateInline_sim (b + 1) pe he hG hD
            | true => exact validateInline_sim (b + 1) pt ht hG hD
          | cases b₂ with
            | false => exact validateInline_sim (b + 1) pe he hG hD
            | true => exact validateInline_sim (b + 1) pt ht hG hD
      | _ => rfl
    | jump _ =>
      cases hwf with
      | jump hj hargs =>
        obtain ⟨hts, hsinl⟩ := hD _ hj
        have hfa := trel_flattenArgs_shape hG hargs
        dsimp only [validateInline]
        rw [hts.canEmit_eq hfa, hsinl _ _ hfa]
      | _ => rfl
    | leaf => cases hwf <;> rfl
    | group _ _ _ => cases hwf <;> rfl

theorem rewriteCTInline_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan) {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) → CTDRel G' D' D →
      Wf G' D' (rewriteCTInline p e₁) (rewriteCTInline p e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      cases hop with
      | mk code hargs =>
        have hfa := trel_flattenArgs_opt hG hargs
        have hel := evalThreadLet?_opt_rel code hfa
        dsimp only [rewriteCTInline]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel hfa
          rw [hr₁, hr₂]
          exact .let_ (.mk code hr) fun xs₁ xs₂ =>
            ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
              (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
              (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · rw [he₁, he₂]
          exact ih o₁ o₂ pk (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG) hD
    | _ => exact .hlt
  | load t ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTInline]
      rw [hr₁, hr₂]
      exact .load t hr fun v₁ v₂ =>
        ih (.var (some v₁)) (.var (some v₂)) pk (ctx_optArgRel_cons_var hG v₁ v₂)
          (hD.weaken (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h))
    | _ => exact .hlt
  | store hv ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨rv₁, rv₂, hrv₁, hrv₂, hrv⟩ := (OptArgRel.flattenArg hG hv).toRealArg?
      obtain ⟨ra₁, ra₂, hra₁, hra₂, hra⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTInline]
      rw [hrv₁, hrv₂, hra₁, hra₂]
      exact .store hrv hra (ih pk hG hD)
    | _ => exact .hlt
  | call f hargs _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTInline]
      rw [hr₁, hr₂]
      exact .call f hr fun xs₁ xs₂ =>
        ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
          (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | jnz hc _ _ iht ihe =>
    intro p G' D' hG hD
    cases p with
    | node2 pt pe =>
      have hfl := OptArgRel.flattenArg hG hc
      dsimp only [rewriteCTInline]
      cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
      · cases hfl; exact .jnz (.var ‹_›) (iht pt hG hD) (ihe pe hG hD)
      · cases hfl
      · cases hfl
      · cases hfl; next c => cases c with | false => exact ihe pe hG hD | true => exact iht pt hG hD
    | _ => exact .hlt
  | jump hj hargs =>
    intro p G' D' hG hD
    cases p with
    | jump _ =>
      have hhl := hD _ hj
      have hfa := trel_flattenArgs_opt hG hargs
      have hsh : TRel (fun _ => ArgShapeEq) (flattenArgs _) (flattenArgs _) :=
        TRel.mono (fun _ _ _ h => h.shape) hfa
      dsimp only [rewriteCTInline]
      rw [hhl.1.shape.canEmit_eq hsh]
      split
      · exact hhl.1.emit_wf hfa
      · have hor := hhl.2.1 (fun _ h => h) (fun _ h => h) _ _ hfa
        cases e₁ : CTLabel.inline? _ (flattenArgs _) <;>
          cases e₂ : CTLabel.inline? _ (flattenArgs _) <;>
          rw [e₁, e₂] at hor <;> dsimp only [ORel] at hor
        · exact .hlt
        · exact hor
    | _ => exact .hlt
  | ret hvs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hvs)
      dsimp only [rewriteCTInline]; rw [hr₁, hr₂]; exact .ret hr
    | _ => exact .hlt
  | exit f hargs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTInline]; rw [hr₁, hr₂]; exact .exit f hr
    | _ => exact .hlt
  | hlt => intro p _ _ _ _; cases p <;> exact .hlt
  | group _ _ _ _ => intro p _ _ _ _; cases p <;> exact .hlt

/-! ### `splitLabelTup`, `buildTargets`, `attachInlines`, `rewriteCTBlocks`, and `rewriteCTAux_wf` -/

theorem splitLabelTup_rel {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂} :
    (as bs : List (List Ty)) → (js₁ : Tup L₁ (as ++ bs)) → (js₂ : Tup L₂ (as ++ bs)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    (∀ p ∈ Tup.zip (splitLabelTup as bs js₁).1 (splitLabelTup as bs js₂).1, p ∈ D') ∧
      (∀ p ∈ Tup.zip (splitLabelTup as bs js₁).2 (splitLabelTup as bs js₂).2, p ∈ D')
  | [], _, js₁, js₂, h => ⟨fun _ hp => (nomatch hp), h⟩
  | _ :: as, bs, (j₁, js₁), (j₂, js₂), h => by
    have ih := splitLabelTup_rel as bs js₁ js₂ fun _ hp => h _ (List.mem_cons_of_mem _ hp)
    dsimp only [splitLabelTup]
    refine ⟨fun p hp => ?_, ih.2⟩
    cases hp with
    | head => exact h _ List.mem_cons_self
    | tail _ hp' => exact ih.1 _ hp'

theorem splitOptLabel_rel {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂} {ts : List Ty} :
    (b : Bool) → {rest : List (List Ty)} →
    (js₁ : Tup L₁ ((if b then [ts] else []) ++ rest)) →
    (js₂ : Tup L₂ ((if b then [ts] else []) ++ rest)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    ORel (fun l₁ l₂ => ⟨ts, l₁, l₂⟩ ∈ D')
      (splitOptLabel b js₁).1 (splitOptLabel b js₂).1 ∧
    (∀ p ∈ Tup.zip (splitOptLabel b js₁).2 (splitOptLabel b js₂).2, p ∈ D')
  | false, _, _, _, h => ⟨trivial, h⟩
  | true, _, (_, _), (_, _), h =>
    ⟨h _ List.mem_cons_self, fun _ hp => h _ (List.mem_cons_of_mem _ hp)⟩

theorem mkActTarget_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂}
    (ts : List Ty) (act : BlockAct)
    (js₁ : Tup L₁ (actSig ts act)) (js₂ : Tup L₂ (actSig ts act))
    (h : ∀ p ∈ Tup.zip js₁ js₂, p ∈ D') :
    CTTargetRel (V₁ := V₁) (V₂ := V₂) D' (mkActTarget ts act js₁) (mkActTarget ts act js₂) := by
  cases act with
  | keep kb _ =>
    cases kb with
    | true => exact h _ List.mem_cons_self
    | false => exact trivial
  | splitBool p keepT keepF keepDisp _ _ =>
    dsimp only [actSig] at js₁ js₂ h
    dsimp only [mkActTarget]
    revert js₁ js₂ h
    generalize splitMember? p ts = sp
    cases sp with
    | none => intro js₁ js₂ h; exact h _ List.mem_cons_self
    | some _ =>
      intro js₁ js₂ h
      have hD := splitOptLabel_rel keepDisp _ _ h
      have hT := splitOptLabel_rel keepT _ _ hD.2
      have hF := splitOptLabel_rel keepF _ _ hT.2
      exact ⟨rfl, hT.1, hF.1, hD.1⟩

theorem buildTargets_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    (js₁ : Tup L₁ (threadSig acts sig)) → (js₂ : Tup L₂ (threadSig acts sig)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    CTDRel G' D' (Tup.zip (buildTargets (V := V₁) (rs := rs) acts sig js₁)
      (buildTargets (V := V₂) (rs := rs) acts sig js₂))
  | _, [], (), (), _, _, hp => nomatch hp
  | [], ts :: sig, (j₁, js₁), (j₂, js₂), h, _, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨h _ List.mem_cons_self, fun _ _ _ _ _ => trivial, fun _ _ _ => rfl⟩
    | tail _ hp' =>
      exact buildTargets_rel [] sig js₁ js₂ (fun _ hq => h _ (List.mem_cons_of_mem _ hq)) _ hp'
  | a :: acts, ts :: sig, js₁, js₂, h, p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    have hsp := splitLabelTup_rel (actSig ts a) (threadSig acts sig) js₁ js₂ h
    cases hp with
    | head => exact ⟨mkActTarget_rel ts a _ _ hsp.1, fun _ _ _ _ _ => trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact buildTargets_rel acts sig _ _ hsp.2 p hp'

theorem tryMakeInlineLabel_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) (hD : CTDRel G' D' D)
    {b₁ : Tup (Arg (CTOptV V₁)) ts → Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {b₂ : Tup (Arg (CTOptV V₂)) ts → Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hb : ∀ a₁ a₂, Wf (Tup.zip a₁ a₂ ++ G) D (b₁ a₁) (b₂ a₂))
    (a : BlockAct) (pb : CTPlan) {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTLabelRel G' D' l₁ l₂) :
    CTLabelRel G' D' (tryMakeInlineLabel a pb b₁ l₁) (tryMakeInlineLabel a pb b₂ l₂) := by
  have hGsh : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2 := fun p hp => (hG p hp).shape
  have hsim : ∀ a₁ a₂, TRel (fun _ => ArgShapeEq) a₁ a₂ →
      ∀ (budget : Nat),
      (let (res₁, p₁', e₁') := peelThreadHead 4 false pb (b₁ a₁)
       let (res₂, p₂', e₂') := peelThreadHead 4 false pb (b₂ a₂)
       res₁ = res₂ ∧ p₁' = p₂' ∧
         (validateInline budget p₁' e₁').isSome = (validateInline budget p₂' e₂').isSome ∧
         (res₁ → (validateInline 8 p₁' e₁').isSome = (validateInline 8 p₂' e₂').isSome)) := by
    intro a₁ a₂ ha budget
    obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_sim 4 false pb (hb a₁ a₂) fun p hp =>
      (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ha p) (hGsh p)
    refine ⟨hres, hp', ?_, fun _ => ?_⟩
    · rw [hp', validateInline_sim budget _ hwf₁ hG₁ hD.toSim]
    · rw [hp', validateInline_sim 8 _ hwf₁ hG₁ hD.toSim]
  cases a with
  | keep _ allow =>
    cases allow
    · exact hl
    · refine ⟨hl.1, ?_, ?_⟩
      · intro G'' D'' hG'' hD'' a₁ a₂ ha
        have hG' : ∀ p ∈ G, OptArgRel G'' p.1 p.2.1 p.2.2 := fun p hp => (hG p hp).weaken hG''
        obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_wf 4 false pb (hb a₁ a₂)
          (ctx_optArgRel_append_same (mem_zip_optArgRel ha) hG')
        obtain ⟨_, _, hval, _⟩ := hsim a₁ a₂ (TRel.mono (fun _ _ _ h => h.shape) ha)
          (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
        dsimp only [tryMakeInlineLabel]
        simp only [hp'] at hval
        simp only [hres, hp']
        rw [hval]
        by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true
        · simp only [hc, ↓reduceIte, ORel]
          rw [← hp']
          exact rewriteCTInline_wf hwf₁ _ hG₁ (hD.weaken hG'' hD'')
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, ORel]
      · intro a₁ a₂ ha
        obtain ⟨hres, hp', hval, _⟩ := hsim a₁ a₂ ha
          (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
        dsimp only [tryMakeInlineLabel]
        simp only [hp'] at hval
        simp only [hres, hp']
        rw [hval]
        by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
          simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
  | splitBool _ _ _ _ inlT inlF =>
    dsimp only [tryMakeInlineLabel]
    by_cases hinl : (inlT || inlF) = true
    · simp only [hinl, ↓reduceIte]
      refine ⟨hl.1, ?_, ?_⟩
      · intro G'' D'' hG'' hD'' a₁ a₂ ha
        have hG' : ∀ p ∈ G, OptArgRel G'' p.1 p.2.1 p.2.2 := fun p hp => (hG p hp).weaken hG''
        obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_wf 4 false pb (hb a₁ a₂)
          (ctx_optArgRel_append_same (mem_zip_optArgRel ha) hG')
        obtain ⟨_, _, _, hval8⟩ := hsim a₁ a₂ (TRel.mono (fun _ _ _ h => h.shape) ha) 8
        by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
        · have hvi := hval8 (hres.trans hres₂)
          simp only [hp'] at hvi
          simp only [hres, hres₂, hp', Bool.true_and]
          rw [hvi]
          by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
              (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true
          · simp only [hc, ↓reduceIte, ORel]
            rw [← hp']
            exact rewriteCTInline_wf hwf₁ _ hG₁ (hD.weaken hG'' hD'')
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, ORel]
        · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
            Bool.eq_false_iff.2 hres₂
          simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ORel]
      · intro a₁ a₂ ha
        obtain ⟨hres, hp', _, hval8⟩ := hsim a₁ a₂ ha 8
        by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
        · have hvi := hval8 (hres.trans hres₂)
          simp only [hp'] at hvi
          simp only [hres, hres₂, hp', Bool.true_and]
          rw [hvi]
          by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
              (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
        · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
            Bool.eq_false_iff.2 hres₂
          simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            Option.isSome_none]
    · simp only [hinl, Bool.false_eq_true, ↓reduceIte]
      exact hl

theorem attachInlines_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) (hD : CTDRel G' D' D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    WfB G D bs₁ bs₂ →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDRel G' D' (Tup.zip ls₁ ls₂) →
    CTDRel G' D' (Tup.zip (attachInlines acts pbs bs₁ ls₁) (attachInlines acts pbs bs₂ ls₂))
  | _, _, [], .nil, .nil, _, (), (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons hb hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head =>
      exact tryMakeInlineLabel_rel hG hD hb a pb (hls _ List.mem_cons_self)
    | tail _ hp' =>
      exact attachInlines_rel hG hD acts pbs bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_rel hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_rel hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

theorem tryMakeInlineLabel_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) (hD : CTDSim D)
    {b₁ : Tup (Arg (CTOptV V₁)) ts → Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {b₂ : Tup (Arg (CTOptV V₂)) ts → Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hb : ∀ a₁ a₂, Wf (Tup.zip a₁ a₂ ++ G) D (b₁ a₁) (b₂ a₂))
    (a : BlockAct) (pb : CTPlan) {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTLabelSim l₁ l₂) :
    CTLabelSim (tryMakeInlineLabel a pb b₁ l₁) (tryMakeInlineLabel a pb b₂ l₂) := by
  have hcheck : ∀ a₁ a₂, TRel (fun _ => ArgShapeEq) a₁ a₂ → ∀ (budget : Nat),
      (let (res₁, p₁', e₁') := peelThreadHead 4 false pb (b₁ a₁)
       let (res₂, p₂', e₂') := peelThreadHead 4 false pb (b₂ a₂)
       res₁ = res₂ ∧ p₁' = p₂' ∧
         (validateInline budget p₁' e₁').isSome = (validateInline budget p₂' e₂').isSome ∧
         (validateInline 8 p₁' e₁').isSome = (validateInline 8 p₂' e₂').isSome) := by
    intro a₁ a₂ ha budget
    have hsh : ∀ p ∈ Tup.zip a₁ a₂ ++ G, ArgShapeEq p.2.1 p.2.2 := fun p hp =>
      (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ha p) (hG p)
    obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_sim 4 false pb (hb a₁ a₂) hsh
    refine ⟨hres, hp', ?_, ?_⟩
    · rw [hp', validateInline_sim budget _ hwf₁ hG₁ hD]
    · rw [hp', validateInline_sim 8 _ hwf₁ hG₁ hD]
  cases a with
  | keep _ allow =>
    cases allow
    · exact hl
    · refine ⟨hl.1, fun a₁ a₂ ha => ?_⟩
      obtain ⟨hres, hp', hval, _⟩ := hcheck a₁ a₂ ha (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
      dsimp only [tryMakeInlineLabel]
      simp only [hp'] at hval
      simp only [hres, hp']
      rw [hval]
      by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
          (peelThreadHead 4 false pb (b₂ a₂)).2.1
          (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
  | splitBool _ _ _ _ inlT inlF =>
    dsimp only [tryMakeInlineLabel]
    by_cases hinl : (inlT || inlF) = true
    · simp only [hinl, ↓reduceIte]
      refine ⟨hl.1, fun a₁ a₂ ha => ?_⟩
      obtain ⟨hres, hp', _, hval8⟩ := hcheck a₁ a₂ ha 8
      simp only [hp'] at hval8
      by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
      · simp only [hres, hres₂, hp', Bool.true_and]
        rw [hval8]
        by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
          simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
      · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
          Bool.eq_false_iff.2 hres₂
        simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
    · simp only [hinl, Bool.false_eq_true, ↓reduceIte]
      exact hl

theorem attachInlines_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) (hD : CTDSim D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    WfB G D bs₁ bs₂ →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDSim (Tup.zip ls₁ ls₂) →
    CTDSim (Tup.zip (attachInlines acts pbs bs₁ ls₁) (attachInlines acts pbs bs₂ ls₂))
  | _, _, [], .nil, .nil, _, (), (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons hb hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact tryMakeInlineLabel_sim hG hD hb a pb (hls _ List.mem_cons_self)
    | tail _ hp' =>
      exact attachInlines_sim hG hD acts pbs bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_sim hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_sim hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

theorem validTargets_buildTargets_sim {V₂ : Ty → Type} {L₂ : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → (Js₂ : Tup L₂ (threadSig acts sig)) →
    CTDSim (Tup.zip (validTargets (rs := rs) acts sig) (buildTargets (V := V₂) (rs := rs) acts sig Js₂))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js₂), p, hp => by
    dsimp only [validTargets, buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact validTargets_buildTargets_sim [] sig js₂ p hp'
  | a :: acts, ts :: sig, js₂, p, hp => by
    dsimp only [validTargets, buildTargets, Tup.zip] at hp
    cases hp with
    | head =>
      refine ⟨?_, fun _ _ _ => rfl⟩
      cases a with
      | keep kb _ => cases kb <;> trivial
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [threadSig, actSig] at js₂ ⊢
        dsimp only [mkActTarget]
        revert js₂
        generalize splitMember? p ts = sp
        cases sp with
        | none => intro _; trivial
        | some _ =>
          intro _
          dsimp only [CTTargetShape]
          refine ⟨HEq.rfl, ?_, ?_, ?_⟩
          · cases keepT <;> cases keepDisp <;> rfl
          · cases keepT <;> cases keepF <;> cases keepDisp <;> rfl
          · cases keepDisp <;> rfl
    | tail _ hp' =>
      exact validTargets_buildTargets_sim acts sig _ p hp'

theorem buildTargets_self_sim {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → (Js : Tup L (threadSig acts sig)) →
    CTDSim (Tup.zip (buildTargets (V := V) (rs := rs) acts sig Js)
      (buildTargets (V := V) (rs := rs) acts sig Js))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js), p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact buildTargets_self_sim [] sig js p hp'
  | a :: acts, ts :: sig, js, p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head =>
      refine ⟨?_, fun _ _ _ => rfl⟩
      cases a with
      | keep kb _ => cases kb <;> trivial
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [threadSig, actSig] at js ⊢
        dsimp only [mkActTarget]
        revert js
        generalize splitMember? p ts = sp
        cases sp with
        | none => intro _; trivial
        | some _ => intro _; exact ⟨HEq.rfl, rfl, rfl, rfl⟩
    | tail _ hp' => exact buildTargets_self_sim acts sig _ p hp'

theorem blocksAppend_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    {s₁ s₂ : List (List Ty)} →
    {bs₁ : Blocks V₁ L₁ rs s₁} → {bs₁' : Blocks V₂ L₂ rs s₁} →
    {bs₂ : Blocks V₁ L₁ rs s₂} → {bs₂' : Blocks V₂ L₂ rs s₂} →
    WfB G D bs₁ bs₁' → WfB G D bs₂ bs₂' →
    WfB G D (blocksAppend bs₁ bs₂) (blocksAppend bs₁' bs₂')
  | [], _, .nil, .nil, _, _, .nil, hbs₂ => hbs₂
  | _ :: _, _, .cons _ _, .cons _ _, _, _, .cons hb₁ ht₁, hbs₂ =>
    .cons hb₁ (blocksAppend_wf ht₁ hbs₂)

theorem condConsBlock_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (b : Bool)
    {blk₁ : Unit → Tup V₁ ts → Expr V₁ L₁ rs} {blk₂ : Unit → Tup V₂ ts → Expr V₂ L₂ rs}
    {rest : List (List Ty)} {tl₁ : Blocks V₁ L₁ rs rest} {tl₂ : Blocks V₂ L₂ rs rest}
    (hblk : b = true → ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (blk₁ () xs₁) (blk₂ () xs₂))
    (htl : WfB G D tl₁ tl₂) :
    WfB G D (condConsBlock b blk₁ tl₁) (condConsBlock b blk₂ tl₂) := by
  cases b
  · exact htl
  · exact .cons (hblk rfl) htl

theorem mkHltBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    (sig : List (List Ty)) → WfB G D (mkHltBlocks (V := V₁) (rs := rs) sig)
      (mkHltBlocks (V := V₂) (rs := rs) sig)
  | [] => .nil
  | _ :: sig => .cons (fun _ _ => .hlt) (mkHltBlocks_wf sig)

private theorem eq_cast_wfb {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {s₁ s₂ : List (List Ty)} (h : s₁ = s₂)
    {b₁ : Blocks V₁ L₁ rs s₁} {b₂ : Blocks V₂ L₂ rs s₁} (hb : WfB G D b₁ b₂) :
    WfB G D (h ▸ b₁) (h ▸ b₂) := by
  subst h; exact hb

theorem mkSplitBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (m : Member .bool ts)
    (keepDisp keepT keepF : Bool)
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTTargetRel D l₁.target l₂.target)
    {rwT₁ rwF₁ : Tup V₁ (eraseMem m) → Expr V₁ L₁ rs}
    {rwT₂ rwF₂ : Tup V₂ (eraseMem m) → Expr V₂ L₂ rs}
    (hT : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (rwT₁ xs₁) (rwT₂ xs₂))
    (hF : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (rwF₁ xs₁) (rwF₂ xs₂)) :
    WfB G D (mkSplitBlocks m keepDisp keepT keepF l₁ rwT₁ rwF₁)
      (mkSplitBlocks m keepDisp keepT keepF l₂ rwT₂ rwF₂) := by
  refine condConsBlock_wf keepDisp (fun _ xs₁ xs₂ => ?_)
    (condConsBlock_wf keepT (fun _ => hT) (condConsBlock_wf keepF (fun _ => hF) .nil))
  revert hl
  cases l₁.target <;> cases l₂.target <;> intro hl
  · exact .hlt
  · exact .hlt
  · dsimp only [CTTargetRel] at hl
  · exact .hlt
  · exact .hlt
  · dsimp only [CTTargetRel] at hl
  · dsimp only [CTTargetRel] at hl
  · dsimp only [CTTargetRel] at hl
  · rename_i m₁ lT1? lF1? _ m₂ lT2? lF2? _
    dsimp only [CTTargetRel] at hl
    rcases hl with ⟨rfl, hlt, hlf, _⟩
    cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hlt <;> try exact .hlt
    cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hlf <;> try exact .hlt
    have hvar : ArgRel (Tup.zip xs₁ xs₂ ++ G) .bool
        (.var (getTupMem m₁ xs₁)) (.var (getTupMem m₁ xs₂)) := by
      have hm := trel_getTupMem m₁ (toArgTup_trel xs₁ xs₂)
      rw [getTupMem_toArgTup, getTupMem_toArgTup] at hm
      exact hm.weaken (fun _ hp => List.mem_append_left _ hp)
    have hdrop : TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G))
        (dropTupMem m₁ (toArgTup xs₁)) (dropTupMem m₁ (toArgTup xs₂)) :=
      TRel.argRel_weaken (fun _ hp => List.mem_append_left _ hp)
        (trel_dropTupMem m₁ (toArgTup_trel xs₁ xs₂))
    exact .jnz hvar (.jump hlt hdrop) (.jump hlf hdrop)

theorem rewriteCTBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDRel G' D' (Tup.zip ls₁ ls₂) →
    (∀ {ts} (i : Member ts sig) pb (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts)
        {H'}, (∀ p ∈ Tup.zip a₁ a₂, OptArgRel H' p.1 p.2.1 p.2.2) →
        Wf (H' ++ G') D' (rewriteCTAux pb (bs₁.get i a₁)) (rewriteCTAux pb (bs₂.get i a₂))) →
    WfB G' D' (rewriteCTBlocks acts pbs bs₁ ls₁) (rewriteCTBlocks acts pbs bs₂ ls₂)
  | acts, _, [], .nil, .nil, (), (), _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | [], _, _ :: _, .cons _ _, .cons _ _, _, _, _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | _ :: _, .nil, _ :: _, .cons _ _, .cons _ _, _, _, _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | a :: acts, .cons pb pbs, ts :: _, .cons _ tl₁, .cons _ tl₂, (l₁, tls₁), (l₂, tls₂), hls, h => by
    have htl := rewriteCTBlocks_wf acts pbs tl₁ tl₂ tls₁ tls₂
      (fun _ hp => hls _ (List.mem_cons_of_mem _ hp)) (fun i => h (.there i))
    unfold rewriteCTBlocks
    refine blocksAppend_wf ?_ htl
    cases a with
    | keep kb _ =>
      cases kb with
      | true =>
        exact .cons (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_toOptArgTup xs₁ xs₂)) .nil
      | false => exact .nil
    | splitBool p keepT keepF keepDisp _ _ =>
      dsimp only [actSig]
      generalize splitMember? p ts = sp
      cases sp with
      | none =>
        exact .cons (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_toOptArgTup xs₁ xs₂)) .nil
      | some m =>
        exact mkSplitBlocks_wf m keepDisp keepT keepF (hls _ List.mem_cons_self).1
          (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_optArgRel
            (trel_insertTupMem m (OptArgRel.imm (t := .bool) true) (toOptArgTup_trel xs₁ xs₂))))
          (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_optArgRel
            (trel_insertTupMem m (OptArgRel.imm (t := .bool) false) (toOptArgTup_trel xs₁ xs₂))))

theorem rewriteCTAux_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan) {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) → CTDRel G' D' D →
      Wf G' D' (rewriteCTAux p e₁) (rewriteCTAux p e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      cases hop with
      | mk code hargs =>
        have hfa := trel_flattenArgs_opt hG hargs
        have hel := evalThreadLet?_opt_rel code hfa
        dsimp only [rewriteCTAux]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel hfa
          rw [hr₁, hr₂]
          exact .let_ (.mk code hr) fun xs₁ xs₂ =>
            ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
              (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
              (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · rw [he₁, he₂]
          exact ih o₁ o₂ pk (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG) hD
    | _ => exact .hlt
  | load t ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTAux]
      rw [hr₁, hr₂]
      exact .load t hr fun v₁ v₂ =>
        ih (.var (some v₁)) (.var (some v₂)) pk (ctx_optArgRel_cons_var hG v₁ v₂)
          (hD.weaken (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h))
    | _ => exact .hlt
  | store hv ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨rv₁, rv₂, hrv₁, hrv₂, hrv⟩ := (OptArgRel.flattenArg hG hv).toRealArg?
      obtain ⟨ra₁, ra₂, hra₁, hra₂, hra⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTAux]
      rw [hrv₁, hrv₂, hra₁, hra₂]
      exact .store hrv hra (ih pk hG hD)
    | _ => exact .hlt
  | call f hargs _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTAux]
      rw [hr₁, hr₂]
      exact .call f hr fun xs₁ xs₂ =>
        ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
          (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | jnz hc _ _ iht ihe =>
    intro p G' D' hG hD
    cases p with
    | node2 pt pe =>
      have hfl := OptArgRel.flattenArg hG hc
      dsimp only [rewriteCTAux]
      cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
      · cases hfl; exact .jnz (.var ‹_›) (iht pt hG hD) (ihe pe hG hD)
      · cases hfl
      · cases hfl
      · cases hfl; next c => cases c with | false => exact ihe pe hG hD | true => exact iht pt hG hD
    | _ => exact .hlt
  | jump hj hargs =>
    intro p G' D' hG hD
    cases p with
    | jump tryInl =>
      exact CTLabel.emitJump_wf tryInl (hD _ hj) (trel_flattenArgs_opt hG hargs)
    | _ => exact .hlt
  | ret hvs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hvs)
      dsimp only [rewriteCTAux]; rw [hr₁, hr₂]; exact .ret hr
    | _ => exact .hlt
  | exit f hargs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTAux]; rw [hr₁, hr₂]; exact .exit f hr
    | _ => exact .hlt
  | hlt => intro p _ _ _ _; cases p <;> exact .hlt
  | @group _ Dc sig b₁ b₂ k₁ k₂ hb _ ihb ihk =>
    intro p G' D' hG hD
    cases p with
    | group acts pbs pk =>
      refine .group (sig := threadSig acts sig) (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
      · let lsNo₁ := buildTargets (V := V₁) (rs := rs) acts sig Js₁
        let lsNo₂ := buildTargets (V := V₂) (rs := rs) acts sig Js₂
        let D'_new := Tup.zip Js₁ Js₂ ++ D'
        have hNo : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂) :=
          buildTargets_rel acts sig Js₁ Js₂ fun _ hp => List.mem_append_left _ hp
        have hD_no : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂ ++ Dc) :=
          hNo.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        let lsBody₁ := attachInlines acts pbs (b₁ lsNo₁) lsNo₁
        let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
        have hBody : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂) :=
          attachInlines_rel hG hD_no acts pbs (b₁ lsNo₁) (b₂ lsNo₂)
            (hb lsNo₁ lsNo₂) lsNo₁ lsNo₂ hNo
        have hD_body : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂ ++ Dc) :=
          hBody.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        exact rewriteCTBlocks_wf acts pbs (b₁ lsBody₁) (b₂ lsBody₂) lsNo₁ lsNo₂ hNo
          fun {ts} i pb a₁ a₂ {H'} ha =>
            ihb lsBody₁ lsBody₂ i a₁ a₂ pb (ctx_optArgRel_append ha hG)
              (hD_body.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
      · let lsNo₁ := buildTargets (V := V₁) (rs := rs) acts sig Js₁
        let lsNo₂ := buildTargets (V := V₂) (rs := rs) acts sig Js₂
        let D'_new := Tup.zip Js₁ Js₂ ++ D'
        have hNo : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂) :=
          buildTargets_rel acts sig Js₁ Js₂ fun _ hp => List.mem_append_left _ hp
        have hD_no : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂ ++ Dc) :=
          hNo.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        let lsBody₁ := attachInlines acts pbs (b₁ lsNo₁) lsNo₁
        let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
        have hBody : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂) :=
          attachInlines_rel hG hD_no acts pbs (b₁ lsNo₁) (b₂ lsNo₂)
            (hb lsNo₁ lsNo₂) lsNo₁ lsNo₂ hNo
        have hD_body : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂ ++ Dc) :=
          hBody.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        exact ihk lsBody₁ lsBody₂ pk hG hD_body
    | _ => exact .hlt

/-! ### Weakest-precondition refinement (`peelThreadHead_wp`, `rewriteCTInline_wp`, `rewriteCTAux_wp`) -/

/-- Value-recovery invariant linking `Arg (CTOptV Val)` bindings to concrete `Val` values,
forbidding `.var none`. -/
def OptValCtx (G : Ctx (Arg (CTOptV Val)) Val) : Prop :=
  ∀ q ∈ G, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2

theorem OptValCtx.flattenArg {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G)
    {t : Ty} {a : Arg (Arg (CTOptV Val)) t} {v : Arg Val t} (ha : ArgRel G t a v) :
    ∃ ra : Arg Val t, toRealArg? (LeanQbe.T.flattenArg a) = some ra ∧ ra.val = v.val := by
  cases ha with
  | imm c => exact ⟨.imm c, rfl, rfl⟩
  | var hm => exact hG _ hm

theorem trel_toRealArgs?_flattenArgs_wp {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → {as : Tup (Arg (Arg (CTOptV Val))) ts} → {vs : Tup (Arg Val) ts} →
    TRel (ArgRel G) as vs →
    ∃ ras : Tup (Arg Val) ts, toRealArgs? (flattenArgs as) = some ras ∧ vals ras = vals vs
  | [], (), (), .nil => ⟨(), rfl, rfl⟩
  | _ :: _, (_, _), (_, _), .cons ha has => by
    obtain ⟨ra, hra, hval⟩ := hG.flattenArg ha
    obtain ⟨ras, hras, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG has
    refine ⟨(ra, ras), ?_, Prod.ext hval hvals⟩
    dsimp only [flattenArgs, tupMapArg, toRealArgs?]
    rw [hra, hras]; rfl

theorem OptValCtx.of_toRealArgs? {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → {as : Tup (Arg (CTOptV Val)) ts} → {ras : Tup (Arg Val) ts} →
    toRealArgs? as = some ras → OptValCtx (Tup.zip as (vals ras) ++ G)
  | [], (), (), _, q, hq => by
    dsimp only [vals, Tup.zip] at hq
    exact hG q hq
  | _ :: _, (a, as), (ra, ras), h, q, hq => by
    dsimp only [toRealArgs?] at h
    cases ha : toRealArg? a <;> rw [ha] at h
    · simp at h
    cases has : toRealArgs? as <;> rw [has] at h
    · simp at h
    cases h
    dsimp only [vals, Tup.zip] at hq
    cases hq with
    | head => exact ⟨_, ha, rfl⟩
    | tail _ hq' => exact OptValCtx.of_toRealArgs? hG has q hq'

theorem OptValCtx.of_toOptArgTup {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → (xs : Tup Val ts) → OptValCtx (Tup.zip (toOptArgTup xs) xs ++ G)
  | [], (), q, hq => hG q hq
  | _ :: _, (x, xs), q, hq => by
    cases hq with
    | head => exact ⟨.var x, rfl, rfl⟩
    | tail _ hq' => exact OptValCtx.of_toOptArgTup hG xs q hq'

theorem OptValCtx.cons_var {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G)
    {t : Ty} (v : Val t) : OptValCtx (⟨t, .var (some v), v⟩ :: G) := fun q hq => by
  cases hq with
  | head => exact ⟨.var v, rfl, rfl⟩
  | tail _ hq' => exact hG q hq'

theorem OptValCtx.toRealArgs?_zip {G : Ctx (Arg (CTOptV Val)) Val} (_hG : OptValCtx G) :
    {ts : List Ty} → {a : Tup (Arg (CTOptV Val)) ts} → {xs : Tup Val ts} →
    (∀ q ∈ Tup.zip a xs, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2) →
    ∃ ra : Tup (Arg Val) ts, toRealArgs? a = some ra ∧ vals ra = xs
  | [], (), (), _ => ⟨(), rfl, rfl⟩
  | _ :: _, (a, as), (x, xs), ha => by
    obtain ⟨ra₁, hra₁, hv₁⟩ := ha _ List.mem_cons_self
    obtain ⟨ras, hras, hvs⟩ := OptValCtx.toRealArgs?_zip _hG (fun _ hp => ha _ (List.mem_cons_of_mem _ hp))
    refine ⟨(ra₁, ras), ?_, Prod.ext hv₁ hvs⟩
    dsimp only [toRealArgs?]
    rw [hra₁, hras]; rfl

theorem toRealArgs?_immsTup {V : Ty → Type} :
    {ts : List Ty} → (cs : Tup Val ts) →
    toRealArgs? (V := V) (immsTup cs) = some (immsTup cs)
  | [], () => rfl
  | _ :: _, (c, cs) => by
    dsimp only [immsTup, toRealArgs?, toRealArg?]
    rw [toRealArgs?_immsTup cs]; rfl

theorem toRealArgs?_getTupMem {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {a : Tup (Arg (CTOptV V)) ts} → {ra : Tup (Arg V) ts} →
    toRealArgs? a = some ra → toRealArg? (getTupMem m a) = some (getTupMem m ra)
  | _ :: _, .here, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact ha
  | _ :: _, .there m, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact toRealArgs?_getTupMem m hr

theorem toRealArgs?_dropTupMem {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {a : Tup (Arg (CTOptV V)) ts} → {ra : Tup (Arg V) ts} →
    toRealArgs? a = some ra → toRealArgs? (dropTupMem m a) = some (dropTupMem m ra)
  | _ :: _, .here, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact hr
  | _ :: _, .there m, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩
    simp only [dropTupMem, toRealArgs?, Option.bind, Bind.bind, ha, toRealArgs?_dropTupMem m hr]; rfl

theorem OptValCtx.tup_insertTupMem {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (b : Val u) → (xs : Tup Val (eraseMem m)) →
    ∀ q ∈ Tup.zip (insertTupMem m (.imm b) (toOptArgTup xs)) (insertTupMem m b xs),
      ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2
  | _ :: _, .here, b, xs, _, hq => by
    have h1 : insertTupMem Member.here (.imm b) (toOptArgTup xs) = (.imm b, toOptArgTup xs) := rfl
    have h2 : insertTupMem Member.here b xs = (b, xs) := rfl
    rw [h1, h2] at hq
    cases hq with
    | head => exact ⟨.imm b, rfl, rfl⟩
    | tail _ hq' =>
      exact OptValCtx.of_toOptArgTup (fun _ h => by cases h) xs _ (List.mem_append_left [] hq')
  | _ :: _, .there m, b, xs, _, hq => by
    rcases xs with ⟨x, xs⟩
    have h1 : insertTupMem m.there (.imm b) (toOptArgTup (x, xs)) =
        (.var (some x), insertTupMem m (.imm b) (toOptArgTup xs)) := rfl
    have h2 : insertTupMem m.there b (x, xs) = (x, insertTupMem m b xs) := rfl
    rw [h1, h2] at hq
    cases hq with
    | head => exact ⟨.var x, rfl, rfl⟩
    | tail _ hq' => exact OptValCtx.tup_insertTupMem m b xs _ hq'

theorem tupImms?_real_eq :
    {ts : List Ty} → {a : Tup (Arg (CTOptV Val)) ts} → {ra : Tup (Arg Val) ts} → {vts : Tup Val ts} →
    toRealArgs? a = some ra → tupImms? a = some vts → vals ra = vts
  | [], (), (), (), _, _ => rfl
  | _ :: _, (x, xs), (rx, rxs), (v, vs), hr, hi => by
    dsimp only [toRealArgs?, Bind.bind, Option.bind] at hr
    cases hx : toRealArg? x <;> rw [hx] at hr <;> simp at hr
    cases hxs : toRealArgs? xs <;> rw [hxs] at hr <;> simp at hr
    rcases hr with ⟨rfl, rfl⟩
    dsimp only [tupImms?, Option.bind] at hi
    cases x with
    | var _ => cases hi
    | imm c =>
      dsimp only [Arg.imm?] at hi
      cases hixs : tupImms? xs <;> rw [hixs] at hi <;> simp at hi
      rcases hi with ⟨rfl, rfl⟩
      dsimp only [toRealArg?] at hx; cases hx
      exact Prod.ext rfl (tupImms?_real_eq hxs hixs)

theorem evalThreadLet?_opt_wp {sig dts : List Ty} (code : OpCode sig dts)
    {args₁ : Tup (Arg (CTOptV Val)) sig} {ra₁ : Tup (Arg Val) sig} {vs₂ : Tup Val sig}
    (hreal : toRealArgs? args₁ = some ra₁) (hvs : vals ra₁ = vs₂)
    {out : Tup (Arg (CTOptV Val)) dts} (heval : evalThreadLet? code args₁ = some out)
    {post : Tup Val dts → Prop} (hw : code.wp vs₂ post) :
    ∃ rout : Tup (Arg Val) dts, toRealArgs? out = some rout ∧ post (vals rout) := by
  rw [← hvs] at hw
  cases code with
  | copy _ =>
    rcases args₁ with ⟨a, _⟩; rcases ra₁ with ⟨r, _⟩
    dsimp only [evalThreadLet?] at heval; cases heval
    exact ⟨(r, ()), hreal, hw⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?] at heval
      split at heval
      · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heval
        rcases heval with ⟨cs, hcs, rfl⟩
        rcases hcs with ⟨vts, hv, hev⟩
        have hvv := tupImms?_real_eq hreal hv
        rw [hvv] at hw
        exact ⟨immsTup cs, toRealArgs?_immsTup cs,
          by rw [immsTup_vals]; exact OpCode.eval?_sound _ vts post hev hw⟩
      · cases heval

/-- Target-side `Closed` predicate for `ctSrcCont`. -/
def ctSrcTargetPred {ts : List Ty} (tgt : CTTarget Val Cont ts) (xs : Tup Val ts) (m : Mem 64) : Prop :=
  match tgt with
  | .keep j => j xs m
  | .dead => True
  | .split mem lT? lF? lD? =>
    (match lD? with | some jD => jD xs m | none => True) ∧
    (getTupMem mem xs = true → match lT? with | some jT => jT (dropTupMem mem xs) m | none => True) ∧
    (getTupMem mem xs = false → match lF? with | some jF => jF (dropTupMem mem xs) m | none => True)

/-- Weakest-precondition label invariant for `(l : CTLabel Val Cont rs ts, J : Cont ts)`. -/
def CTTargetWp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) {ts : List Ty}
    (tgt : CTTarget Val Cont ts) (J : Cont ts) : Prop :=
  ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) (m : Mem 64),
    toRealArgs? a = some ra → tgt.canEmit a = true → J (vals ra) m →
    wp Γ Q X (tgt.emit (rs := rs) a) m

def CTJumpWp (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (l : CTLabel Val Cont rs ts) (J : Cont ts) : Prop :=
  CTTargetWp Γ Q X l.target J ∧
    ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) e_out m,
      l.inline? a = some e_out → toRealArgs? a = some ra → J (vals ra) m → wp Γ Q X e_out m

def CTWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (CTLabel Val Cont rs) Cont) : Prop :=
  ∀ p ∈ D, CTJumpWp Γ Q X p.2.1 p.2.2

theorem CTWpD.append {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {H D : Ctx (CTLabel Val Cont rs) Cont}
    (hH : CTWpD Γ Q X H) (hD : CTWpD Γ Q X D) : CTWpD Γ Q X (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem ctSrcTargetPred_to_wp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {tgt : CTTarget Val Cont ts} {J : Cont ts}
    (h : ∀ xs m, J xs m → ctSrcTargetPred tgt xs m) :
    CTTargetWp Γ Q X tgt J := by
  intro a ra m hreal hcan hJ
  have hp := h (vals ra) m hJ
  cases tgt with
  | keep j =>
    dsimp only [CTTarget.emit]; rw [hreal]; exact hp
  | dead => simp [CTTarget.canEmit] at hcan
  | split mem lT? lF? lD? =>
    dsimp only [ctSrcTargetPred] at hp
    rcases hp with ⟨hpD, hpT, hpF⟩
    have hget := toRealArgs?_getTupMem mem hreal
    have hdrop := toRealArgs?_dropTupMem mem hreal
    dsimp only [CTTarget.canEmit] at hcan
    dsimp only [CTTarget.emit]
    cases e₁ : getTupMem mem a <;> rw [e₁] at hcan hget
    · rename_i ov
      cases ov with
      | none => dsimp only [toRealArg?] at hget; cases hget
      | some v =>
        dsimp only [toRealArg?] at hget
        have hv : getTupMem mem ra = .var v := Option.some.inj hget.symm
        have hvv : v = getTupMem mem (vals ra) := by
          have := getTupMem_vals mem ra; rw [hv] at this; exact this
        cases lD? with
        | some jD =>
          dsimp only; rw [hreal]; exact hpD
        | none =>
          dsimp only at hcan
          simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hcan
          rcases hcan with ⟨hTs, hFs⟩
          cases eT : lT? <;> rw [eT] at hTs <;> simp at hTs
          cases eF : lF? <;> rw [eF] at hFs <;> simp at hFs
          dsimp only
          rw [hdrop]; dsimp only [wp]
          refine ⟨fun ht => ?_, fun hf => ?_⟩
          · rw [dropTupMem_vals]; simpa [eT] using hpT (by rw [← hvv]; exact ht)
          · rw [dropTupMem_vals]; simpa [eF] using hpF (by rw [← hvv]; exact hf)
    · rename_i b
      dsimp only [toRealArg?] at hget
      have hb : getTupMem mem ra = .imm b := Option.some.inj hget.symm
      have hbv : b = getTupMem mem (vals ra) := by
        have := getTupMem_vals mem ra; rw [hb] at this; exact this
      cases b
      · rw [hdrop]
        cases eF : lF? <;> rw [eF] at hcan <;> simp at hcan
        dsimp only [wp]; rw [dropTupMem_vals]
        simpa [eF] using hpF (by rw [← hbv])
      · rw [hdrop]
        cases eT : lT? <;> rw [eT] at hcan <;> simp at hcan
        dsimp only [wp]; rw [dropTupMem_vals]
        simpa [eT] using hpT (by rw [← hbv])

/-- Source continuation tuple used for `Closed` in the `.group` case of `rewriteCTAux_wp`. -/
def ctSrcCont (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (l : CTLabel Val Cont rs ts) : Cont ts :=
  fun xs m =>
    ctSrcTargetPred l.target xs m ∧
    ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) e_out,
      l.inline? a = some e_out → toRealArgs? a = some ra → vals ra = xs → wp Γ Q X e_out m

def ctSrcConts (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → Tup (CTLabel Val Cont rs) sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (l, ls) => (ctSrcCont Γ Q X l, ctSrcConts Γ Q X ls)

private theorem ctSrcConts_get (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (ls : Tup (CTLabel Val Cont rs) sig) →
    {ts : List Ty} → (i : Member ts sig) →
    (ctSrcConts Γ Q X ls).get i = ctSrcCont Γ Q X (ls.get i)
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, ls), _, .there i => ctSrcConts_get Γ Q X ls i

theorem ctSrcConts_wpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (ls : Tup (CTLabel Val Cont rs) sig) →
    CTWpD Γ Q X (Tup.zip ls (ctSrcConts Γ Q X ls))
  | [], (), _, hp => nomatch hp
  | _ :: _, (l, ls), p, hp => by
    cases hp with
    | head =>
      refine ⟨ctSrcTargetPred_to_wp (fun _ _ h => h.1), fun a ra e_out m he hreal hJ => ?_⟩
      exact hJ.2 a ra e_out he hreal rfl
    | tail _ hp' => exact ctSrcConts_wpD Γ Q X ls p hp'

/-- Target equality between two label tuples (ignoring `.inline?`). -/
def TargetsEq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Tup (CTLabel V L rs) sig → Tup (CTLabel V L rs) sig → Prop
  | [], (), () => True
  | _ :: _, (l₁, ls₁), (l₂, ls₂) => l₁.target = l₂.target ∧ TargetsEq ls₁ ls₂

theorem attachInlines_targetsEq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig) →
    (ls : Tup (CTLabel V L rs) sig) →
    TargetsEq ls (attachInlines acts pbs bs ls)
  | _, _, [], .nil, () => trivial
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls) => by
    refine ⟨?_, attachInlines_targetsEq acts pbs bs ls⟩
    cases a with
    | keep _ allow => cases allow <;> rfl
    | splitBool _ _ _ _ inlT inlF =>
      dsimp only [tryMakeInlineLabel]
      split <;> rfl
  | [], _, _ :: _, .cons _ bs, (_, ls) =>
    ⟨rfl, attachInlines_targetsEq [] .nil bs ls⟩
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, ls) =>
    ⟨rfl, attachInlines_targetsEq [] .nil bs ls⟩

theorem ctSrcConts_noInl_wpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (lsNo lsBody : Tup (CTLabel Val Cont rs) sig) →
    (∀ {ts} (i : Member ts sig) a, (lsNo.get i).inline? a = none) →
    TargetsEq lsNo lsBody →
    CTWpD Γ Q X (Tup.zip lsNo (ctSrcConts Γ Q X lsBody))
  | [], (), (), _, _, _, hp => nomatch hp
  | _ :: _, (l₁, ls₁), (l₂, ls₂), hno, ⟨ht, hts⟩, p, hp => by
    cases hp with
    | head =>
      refine ⟨ctSrcTargetPred_to_wp (fun xs m h => ht ▸ h.1),
        fun a _ _ _ he => by have hget : l₁.inline? a = none := hno .here a; rw [hget] at he; cases he⟩
    | tail _ hp' =>
      exact ctSrcConts_noInl_wpD Γ Q X ls₁ ls₂ (fun i => hno (.there i)) hts p hp'

theorem buildTargets_noInl_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → {sig : List (List Ty)} → (Js : Tup L (threadSig acts sig)) →
    ∀ {ts} (i : Member ts sig) a, ((buildTargets (V := V) (rs := rs) acts sig Js).get i).inline? a = none
  | [], _ :: _, (_, _), _, .here, _ => rfl
  | [], _ :: _, (_, js), _, .there i, a => buildTargets_noInl_get [] js i a
  | _ :: _, _ :: _, _, _, .here, _ => rfl
  | _ :: acts, _ :: _, _, _, .there i, a => buildTargets_noInl_get acts _ i a

theorem peelThreadHead_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV Val)) Val} → {D : Ctx (CTLabel Val Cont rs) Cont} →
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} → {e₃ : Expr Val Cont rs} →
    Wf G D e₂ e₃ → OptValCtx G → ∀ {m}, wp Γ Q X e₃ m →
    let r := peelThreadHead fuel res p e₂
    ∃ G' e₃', Wf G' D r.2.2 e₃' ∧ OptValCtx G' ∧ wp Γ Q X e₃' m
  | 0, _, _, _, _, _, _, hwf, hG, _, hw => ⟨_, _, hwf, hG, hw⟩
  | fuel + 1, res, p, _, _, _, _, hwf, hG, _, hw => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [peelThreadHead]
        cases he : evalThreadLet? code (flattenArgs _) with
        | none => exact ⟨_, _, .let_ (.mk code hargs) hk, hG, hw⟩
        | some out =>
          obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he hw
          exact peelThreadHead_wp fuel res pk (hk out (vals rout))
            (OptValCtx.of_toRealArgs? hG hrout) hkw
      all_goals exact ⟨_, _, hwf0, hG, hw⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        obtain ⟨ra, hra, hval⟩ := hG.flattenArg hc
        dsimp only [peelThreadHead]
        cases ef : flattenArg _ with
        | imm b =>
          rw [ef] at hra
          dsimp only [toRealArg?] at hra; cases hra
          cases b with
          | false => exact peelThreadHead_wp fuel true pe he hG (hw.2 hval.symm)
          | true => exact peelThreadHead_wp fuel true pt ht hG (hw.1 hval.symm)
        | var _ => exact ⟨_, _, .jnz hc ht he, hG, hw⟩
      all_goals exact ⟨_, _, hwf0, hG, hw⟩
    | _ => exact ⟨_, _, hwf, hG, hw⟩

theorem rewriteCTInline_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg (CTOptV Val)) Val} {D : Ctx (CTLabel Val Cont rs) Cont}
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} {e₃ : Expr Val Cont rs}
    (hwf : Wf G D e₂ e₃) :
    ∀ {G_s : Ctx (Arg (CTOptV Val)) (Arg (CTOptV Val))}
      {D_s : Ctx (CTLabel Val Cont rs) (CTLabel Val Cont rs)}
      {e_chk : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs}
      (_hwf_s : Wf G_s D_s e_chk e₂)
      {budget : Nat} {p : CTPlan} {n : Nat},
      validateInline budget p e_chk = some n →
      (∀ q ∈ G_s, ArgShapeEq q.2.1 q.2.2) → CTDSim D_s →
      OptValCtx G → CTWpD Γ Q X D →
      ∀ m, wp Γ Q X e₃ m → wp Γ Q X (rewriteCTInline p e₂) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_let with ⟨op_chk, k_chk, rfl, hop_s, hk_s⟩
    cases hop with
    | mk code hargs =>
      cases hop_s with
      | mk code_s hargs_s =>
        cases budget with
        | zero => cases p <;> simp [validateInline] at hval
        | succ b =>
          cases p with
          | node1 pk =>
            have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hGs hargs_s)
            dsimp only [validateInline] at hval
            dsimp only [rewriteCTInline]
            rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
            · rw [he₁] at hval; rw [he₂]
              obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
              rw [hra]
              cases hsub : validateInline b pk (k_chk (noneArgTup _)) with
              | none => rw [hsub] at hval; simp at hval
              | some n' =>
                dsimp only [wp, Op.wp] at hw3 ⊢
                rw [← hvals] at hw3
                exact OpCode.wp_mono code _ (fun r hr =>
                  ih (toOptArgTup r) r (hk_s (noneArgTup _) (toOptArgTup r)) hsub
                    (fun p hp => (List.mem_append.1 hp).elim (none_toOptArgTup_shape_zip r p) (hGs p))
                    hDs (OptValCtx.of_toOptArgTup hG r) hD m hr) hw3
            · rw [he₁] at hval; rw [he₂]
              obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
              obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he₂ hw3
              exact ih o₂ (vals rout) (hk_s o₁ o₂) hval
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hGs p))
                hDs (OptValCtx.of_toRealArgs? hG hrout) hD m hkw
          | _ => simp [validateInline] at hval
  | load t ha _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨v, hv, hw3⟩
    rcases hwf_s.rhs_load with ⟨a_chk, k_chk, rfl, ha_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨ra, hra, hval'⟩ := hG.flattenArg ha
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk (k_chk (.var none)) with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hra]; dsimp only [wp]; rw [hval']
          exact ⟨v, hv, ih (.var (some v)) v (hk_s (.var none) (.var (some v))) hsub
            (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGs p hp')
            hDs (hG.cons_var v) hD m hw3⟩
      | _ => simp [validateInline] at hval
  | store hv ha _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨hok, hw3⟩
    rcases hwf_s.rhs_store with ⟨v_chk, a_chk, k_chk, rfl, hv_s, ha_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨rv, hrv, hvalv⟩ := hG.flattenArg hv
        obtain ⟨ra, hra, hvala⟩ := hG.flattenArg ha
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk k_chk with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hrv, hra]; dsimp only [wp]; rw [hvalv, hvala]
          exact ⟨hok, ih hk_s hsub hGs hDs hG hD _ hw3⟩
      | _ => simp [validateInline] at hval
  | call f hargs _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwf_s.rhs_call with ⟨args_chk, k_chk, rfl, hargs_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk (k_chk (noneArgTup _)) with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hra]; dsimp only [wp]; rw [hvals]
          exact ⟨P, E, hΓ, fun r m' hr =>
            ih (toOptArgTup r) r (hk_s (noneArgTup _) (toOptArgTup r)) hsub
              (fun p hp => (List.mem_append.1 hp).elim (none_toOptArgTup_shape_zip r p) (hGs p))
              hDs (OptValCtx.of_toOptArgTup hG r) hD m' (hP r m' hr), hE⟩
      | _ => simp [validateInline] at hval
  | jnz hc _ _ iht ihe =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_jnz with ⟨c_chk, t_chk, e_chk', rfl, hc_s, ht_s, he_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node2 pt pe =>
        have hsh := ArgShapeEq.flattenArg hGs hc_s
        obtain ⟨rc, hrc, hvalc⟩ := hG.flattenArg hc
        dsimp only [validateInline] at hval
        dsimp only [rewriteCTInline]
        cases e₁ : flattenArg c_chk <;> cases e₂ : flattenArg _ <;>
          rw [e₁, e₂] at hsh <;> rw [e₁] at hval <;> rw [e₂] at hrc
        · rename_i ov
          cases ov with
          | none => dsimp only [toRealArg?] at hrc; cases hrc
          | some v =>
            dsimp only [toRealArg?] at hrc
            have hvc := (congrArg Arg.val (Option.some.inj hrc)).trans hvalc
            dsimp only [Bind.bind, Option.bind] at hval
            cases ht : validateInline b pt t_chk <;> rw [ht] at hval <;> simp at hval
            cases he : validateInline (b - _) pe e_chk' <;> rw [he] at hval <;> simp at hval
            dsimp only [wp]
            exact ⟨fun hvt => iht ht_s ht hGs hDs hG hD m (hw3.1 (hvc ▸ hvt)),
                   fun hvf => ihe he_s he hGs hDs hG hD m (hw3.2 (hvc ▸ hvf))⟩
        · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          dsimp only [toRealArg?] at hrc; cases hrc
          first
          | (cases b₁
             · exact ihe he_s hval hGs hDs hG hD m (hw3.2 hvalc.symm)
             · exact iht ht_s hval hGs hDs hG hD m (hw3.1 hvalc.symm))
          | (cases b₂
             · exact ihe he_s hval hGs hDs hG hD m (hw3.2 hvalc.symm)
             · exact iht ht_s hval hGs hDs hG hD m (hw3.1 hvalc.symm))
      | _ => simp [validateInline] at hval
  | jump hj hargs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_jump with ⟨j_chk, args_chk, rfl, hj_s, hargs_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | jump _ =>
        obtain ⟨hts, hsinl⟩ := hDs _ hj_s
        have hfa := trel_flattenArgs_shape hGs hargs_s
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [validateInline] at hval
        rw [hts.canEmit_eq hfa, hsinl _ _ hfa] at hval
        dsimp only [rewriteCTInline]
        split
        · rename_i hcan
          exact (hD _ hj).1 _ ra m hra hcan (by simpa [wp, hvals] using hw3)
        · rename_i hnocan
          rw [Bool.eq_false_iff.2 hnocan, Bool.false_or] at hval
          split at hval
          · rename_i hsome
            rcases Option.isSome_iff_exists.1 hsome with ⟨e_out, heout⟩
            rw [heout]
            exact (hD _ hj).2 _ ra e_out m heout hra (by simpa [wp, hvals] using hw3)
          · cases hval
      | _ => simp [validateInline] at hval
  | ret hvs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG _ m hw3
    rcases hwf_s.rhs_ret with ⟨_, rfl, _⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hvs
        dsimp only [rewriteCTInline, wp]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
      | _ => simp [validateInline] at hval
  | exit f hargs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG _ m hw3
    rcases hwf_s.rhs_exit with ⟨_, rfl, _⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [rewriteCTInline, wp]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
      | _ => simp [validateInline] at hval
  | hlt =>
    intro G_s D_s e_chk hwf_s budget p n hval _ _ _ _ m hw3
    rcases hwf_s.rhs_hlt with rfl
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf => exact hw3
      | _ => simp [validateInline] at hval
  | group _ _ _ _ =>
    intro _ _ _ hwf_s budget p _ hval
    rcases hwf_s.rhs_group with ⟨_, _, rfl, _, _⟩
    cases budget <;> cases p <;> simp [validateInline] at hval

private theorem attachInlines_get_inline_some {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig) →
    (ls : Tup (CTLabel V L rs) sig) →
    ∀ {ts} (i : Member ts sig) a e_out,
      (ls.get i).inline? a = none →
      ((attachInlines acts pbs bs ls).get i).inline? a = some e_out →
      ∃ pb budget,
        let r := peelThreadHead 4 false pb ((bs.get i) a)
        (validateInline budget r.2.1 r.2.2).isSome = true ∧
        e_out = rewriteCTInline r.2.1 r.2.2
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls), _, .here, arg, e_out, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    cases a with
    | keep _ allow =>
      cases allow with
      | false =>
        dsimp only [tryMakeInlineLabel] at he
        rw [hno] at he; cases he
      | true =>
        dsimp only [tryMakeInlineLabel] at he
        by_cases hvs : (validateInline (if (peelThreadHead 4 false pb (b arg)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b arg)).2.1
            (peelThreadHead 4 false pb (b arg)).2.2).isSome = true
        · simp only [hvs, ↓reduceIte, Option.some.injEq] at he
          cases he
          exact ⟨pb, _, hvs, rfl⟩
        · simp only [hvs, Bool.false_eq_true, ↓reduceIte] at he
          cases he
    | splitBool _ _ _ _ inlT inlF =>
      dsimp only [tryMakeInlineLabel] at he
      by_cases hinl : (inlT || inlF) = true
      · simp only [hinl, ↓reduceIte] at he
        by_cases hc : ((peelThreadHead 4 false pb (b arg)).1 &&
            (validateInline 8 (peelThreadHead 4 false pb (b arg)).2.1
              (peelThreadHead 4 false pb (b arg)).2.2).isSome) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at he
          simp only [Bool.and_eq_true] at hc
          cases he
          exact ⟨pb, 8, hc.2, rfl⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at he
          cases he
      · simp only [hinl, Bool.false_eq_true, ↓reduceIte] at he
        rw [hno] at he; cases he
  | _ :: acts, .cons pb pbs, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some acts pbs bs ls i arg e_out hno he
  | [], _, _ :: _, .cons _ bs, (l, ls), _, .here, arg, _, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    rw [hno] at he; cases he
  | [], _, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some [] .nil bs ls i arg e_out hno he
  | _ :: _, .nil, _ :: _, .cons _ bs, (l, ls), _, .here, arg, _, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    rw [hno] at he; cases he
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some [] .nil bs ls i arg e_out hno he

private theorem closed_blocksAppend_splitLabelTup (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (s₁ s₂ : List (List Ty)) → (bs₁ : Blocks Val Cont rs s₁) → (bs₂ : Blocks Val Cont rs s₂) →
    (Js : Tup Cont (s₁ ++ s₂)) →
    Closed Γ Q X (blocksAppend bs₁ bs₂) Js →
    Closed Γ Q X bs₁ (splitLabelTup s₁ s₂ Js).1 ∧ Closed Γ Q X bs₂ (splitLabelTup s₁ s₂ Js).2
  | [], _, .nil, _, Js, hcl => ⟨trivial, hcl⟩
  | _ :: s₁, s₂, .cons _ bs₁, bs₂, (j, Js), hcl => by
    rcases hcl with ⟨hb, htl⟩
    have hrest := closed_blocksAppend_splitLabelTup Γ Q X s₁ s₂ bs₁ bs₂ Js htl
    exact ⟨⟨hb, hrest.1⟩, hrest.2⟩

private theorem condConsBlock_closed (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (b : Bool) (blk : Unit → Tup Val ts → Expr Val Cont rs) {rest : List (List Ty)}
    (tl : Blocks Val Cont rs rest) (js : Tup Cont ((if b then [ts] else []) ++ rest))
    (hcl : Closed Γ Q X (condConsBlock b blk tl) js) :
    (∀ j' (_h : (splitOptLabel b js).1 = some j') xs m, wp Γ Q X (blk () xs) m → j' xs m) ∧
      Closed Γ Q X tl (splitOptLabel b js).2 := by
  cases b
  · exact ⟨(fun _ h => by cases h), hcl⟩
  · exact ⟨fun _ h xs m hw => by cases h; exact hcl.1 xs m hw, hcl.2⟩

private theorem ArgShapeEq.refl_mem_zip {V : Ty → Type} :
    {ts : List Ty} → (a : Tup (Arg (CTOptV V)) ts) →
    ∀ p ∈ Tup.zip a a, ArgShapeEq p.2.1 p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, as), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp' => exact ArgShapeEq.refl_mem_zip as _ hp'

private theorem splitOptLabel_true_of_some {L : List Ty → Type} {ts : List Ty} {b : Bool}
    {rest : List (List Ty)} {js : Tup L ((if b then [ts] else []) ++ rest)} {j : L ts}
    (h : (splitOptLabel b js).1 = some j) : b = true := by
  cases b <;> simp [splitOptLabel] at h ⊢

private theorem splitBool_head_target (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (keepT keepF keepDisp : Bool) (sp : Option (Member .bool ts))
    (headJs : Tup Cont (splitMemberSig ts keepT keepF keepDisp sp))
    (rwId : Tup Val ts → Expr Val Cont rs)
    (rwSplit : (mem : Member .bool ts) → Bool → Tup Val (eraseMem mem) → Expr Val Cont rs)
    (hact : ∀ mem, sp = some mem → (!keepDisp || (keepT && keepF)) = true)
    (hcl : Closed Γ Q X (mkSplitCurBlocks keepT keepF keepDisp
      (CTLabel.noInline (mkSplitTarget ts keepT keepF keepDisp sp headJs)) rwId rwSplit sp) headJs)
    (xs : Tup Val ts) (m : Mem 64)
    (hId : sp = none → wp Γ Q X (rwId xs) m)
    (hSp : ∀ (mem : Member .bool ts), sp = some mem →
      (keepT = true → getTupMem mem xs = true → wp Γ Q X (rwSplit mem true (dropTupMem mem xs)) m) ∧
      (keepF = true → getTupMem mem xs = false → wp Γ Q X (rwSplit mem false (dropTupMem mem xs)) m)) :
    ctSrcTargetPred (mkSplitTarget (V := Val) ts keepT keepF keepDisp sp headJs) xs m := by
  cases sp with
  | none =>
    dsimp only [mkSplitTarget, mkSplitCurBlocks, ctSrcTargetPred] at hcl ⊢
    exact hcl.1 xs m (hId rfl)
  | some mem =>
    revert headJs hact hcl hSp
    cases keepDisp with
    | false =>
      intro headJs _ hcl hSp
      dsimp only [mkSplitTarget, mkSplitCurBlocks, mkSplitBlocks,
        ctSrcTargetPred, splitOptLabel] at hcl ⊢
      have hD_cl := condConsBlock_closed Γ Q X false _ _ _ hcl
      have hT_cl := condConsBlock_closed Γ Q X keepT _ _ _ hD_cl.2
      have hF_cl := condConsBlock_closed Γ Q X keepF _ _ _ hT_cl.2
      have hT_ok : getTupMem mem xs = true →
          match (splitOptLabel keepT headJs).1 with
          | some jT => jT (dropTupMem mem xs) m
          | none => True := by
        intro hget
        cases hkj : (splitOptLabel keepT headJs).1 with
        | none => trivial
        | some jT =>
          have hkt := splitOptLabel_true_of_some hkj
          exact hT_cl.1 jT hkj (dropTupMem mem xs) m ((hSp mem rfl).1 hkt hget)
      have hF_ok : getTupMem mem xs = false →
          match (splitOptLabel keepF (splitOptLabel keepT headJs).2).1 with
          | some jF => jF (dropTupMem mem xs) m
          | none => True := by
        intro hget
        cases hkj : (splitOptLabel keepF (splitOptLabel keepT headJs).2).1 with
        | none => trivial
        | some jF =>
          have hkf := splitOptLabel_true_of_some hkj
          exact hF_cl.1 jF hkj (dropTupMem mem xs) m ((hSp mem rfl).2 hkf hget)
      exact ⟨trivial, hT_ok, hF_ok⟩
    | true =>
      intro headJs hact hcl hSp
      have hact' := hact mem rfl
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hact'
      rcases hact' with ⟨rfl, rfl⟩
      dsimp only [mkSplitTarget, mkSplitCurBlocks, mkSplitBlocks, condConsBlock,
        ctSrcTargetPred, splitOptLabel] at hcl ⊢
      rcases headJs with ⟨jD, jT, jF, _⟩
      rcases hcl with ⟨hD, hT, hF, _⟩
      have hT_ok : getTupMem mem xs = true → jT (dropTupMem mem xs) m :=
        fun hget => hT _ _ ((hSp mem rfl).1 rfl hget)
      have hF_ok : getTupMem mem xs = false → jF (dropTupMem mem xs) m :=
        fun hget => hF _ _ ((hSp mem rfl).2 rfl hget)
      have hdisp_wp : wp Γ Q X (.jnz (.var (getTupMem mem xs))
          (.jump jT (dropTupMem mem (toArgTup xs)))
          (.jump jF (dropTupMem mem (toArgTup xs)))) m := by
        dsimp only [wp]
        refine ⟨fun ht => ?_, fun hf => ?_⟩
        · have := hT_ok ht; rwa [dropTupMem_toArgTup, toArgTup_vals]
        · have := hF_ok hf; rwa [dropTupMem_toArgTup, toArgTup_vals]
      exact ⟨hD _ _ hdisp_wp, hT_ok, hF_ok⟩

private theorem validateAct_splitBool_goal {ts : List Ty} {p : Nat} {keepT keepF keepDisp inlT inlF : Bool}
    (h : validateAct ts (.splitBool p keepT keepF keepDisp inlT inlF) = true) :
    ∀ m, splitMember? p ts = some m → (!keepDisp || (keepT && keepF)) = true := by
  intro m hm; dsimp only [validateAct] at h; rwa [hm] at h

private theorem ctSrcConts_closed_targets (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bk : Blocks (Arg (CTOptV UnitV)) (ValidL rs) rs sig) →
    (b₂ : Blocks (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs sig) →
    (b₃ : Blocks Val Cont rs sig) →
    (Js_out : Tup Cont (threadSig acts sig)) →
    (lsNo lsBody : Tup (CTLabel Val Cont rs) sig) →
    TargetsEq lsNo lsBody →
    lsNo = buildTargets acts sig Js_out →
    validateCTBlocks acts pbs bk = true →
    Closed Γ Q X (rewriteCTBlocks acts pbs b₂ lsNo) Js_out →
    (∀ {ts} (i : Member ts sig) pb (ak : Tup (Arg (CTOptV UnitV)) ts)
        (a₂ : Tup (Arg (CTOptV Val)) ts) (xs : Tup Val ts),
      TRel (fun _ => ArgShapeEq) ak a₂ →
      (∀ q ∈ Tup.zip a₂ xs, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2) →
      validateCTPlan pb (bk.get i ak) = true →
      ∀ m, wp Γ Q X (b₃.get i xs) m → wp Γ Q X (rewriteCTAux pb (b₂.get i a₂)) m) →
    ∀ {ts} (i : Member ts sig) xs m,
      wp Γ Q X (b₃.get i xs) m → ctSrcTargetPred (lsBody.get i).target xs m
  | [], .nil, [], .nil, .nil, .nil, (), (), (), _, _, _, _, _, _, i => nomatch i
  | [], .cons _ _, [], .nil, .nil, .nil, _, _, _, _, _, _, _, _, _, i => nomatch i
  | _ :: _, pbs, [], .nil, .nil, .nil, _, _, _, _, _, hval, _, _, _, _ => by
    cases pbs <;> simp [validateCTBlocks] at hval
  | [], pbs, _ :: _, .cons _ _, .cons _ _, .cons _ _, _, _, _, _, _, hval, _, _, _, _ => by
    cases pbs <;> simp [validateCTBlocks] at hval
  | _ :: _, .nil, _ :: _, .cons _ _, .cons _ _, .cons _ _, _, _, _, _, _, hval, _, _, _, _ => by
    simp [validateCTBlocks] at hval
  | a :: acts, .cons pb pbs, ts :: _, .cons bkh bkt, .cons b₂h b₂t, .cons _ b₃t, Js_out,
      (lno, lsNo), (lb, lsBody), ⟨hteq, hteqs⟩, hbt, hval, hcl, hblk, _, i => by
    intro xs m hw3
    unfold validateCTBlocks at hval
    simp only [Bool.and_eq_true] at hval
    rcases hval with ⟨⟨hact, hbody⟩, hvaltl⟩
    dsimp only [buildTargets] at hbt
    simp only [Prod.mk.injEq] at hbt
    rcases hbt with ⟨rfl, hls⟩
    unfold rewriteCTBlocks at hcl
    have hsp := closed_blocksAppend_splitLabelTup Γ Q X _ _ _ _ _ hcl
    cases i with
    | here =>
      change ctSrcTargetPred lb.target xs m
      rw [← hteq]
      cases a with
      | keep kb _ =>
        cases kb with
        | false => trivial
        | true =>
          dsimp only [CTLabel.noInline, mkActTarget, ctSrcTargetPred]
          have hw2 := hblk .here pb _ _ xs
            (TRel.mono (fun _ _ _ h => h.shape) (toOptArgTup_trel (Tup.units ts) xs))
            (fun q hq => OptValCtx.of_toOptArgTup (G := []) (fun _ h => by cases h) xs q
              (List.mem_append_left [] hq))
            hbody m hw3
          exact hsp.1.1 xs m hw2
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [CTLabel.noInline, mkActTarget]
        refine splitBool_head_target Γ Q X keepT keepF keepDisp (splitMember? p ts)
          (splitLabelTup _ _ Js_out).1
          (fun xs' => rewriteCTAux pb (b₂h (toOptArgTup xs')))
          (fun mem bVal xs' => rewriteCTAux pb (b₂h (insertTupMem mem (.imm bVal) (toOptArgTup xs'))))
          (validateAct_splitBool_goal hact) hsp.1 xs m ?_ ?_
        · intro hmem
          dsimp only at hbody
          simp only [hmem] at hbody
          exact hblk .here pb _ _ xs
            (TRel.mono (fun _ _ _ h => h.shape) (toOptArgTup_trel (Tup.units ts) xs))
            (fun q hq => OptValCtx.of_toOptArgTup (G := []) (fun _ h => by cases h) xs q
              (List.mem_append_left [] hq))
            hbody m hw3
        · intro mem hmem
          dsimp only at hbody
          simp only [hmem, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hbody
          refine ⟨fun hkeepT hget => ?_, fun hkeepF hget => ?_⟩
          · have hbt' : validateCTPlan pb (bkh (insertTupMem mem (.imm true)
                (toOptArgTup (Tup.units (eraseMem mem))))) = true := by
              rcases hbody.1 with hc | hc
              · rw [hkeepT] at hc; cases hc
              · exact hc
            have hsh : TRel (fun _ => ArgShapeEq)
                (insertTupMem mem (.imm true) (toOptArgTup (Tup.units (eraseMem mem))))
                (insertTupMem mem (.imm true) (toOptArgTup (dropTupMem mem xs))) :=
              trel_insertTupMem mem rfl (TRel.mono (fun _ _ _ h => h.shape)
                (toOptArgTup_trel _ _))
            have hopt : ∀ q ∈ Tup.zip (insertTupMem mem (.imm true) (toOptArgTup (dropTupMem mem xs))) xs,
                ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2 := by
              have heqxs : insertTupMem mem true (dropTupMem mem xs) = xs := by
                rw [← hget, insertTupMem_get_drop]
              have hopt0 := OptValCtx.tup_insertTupMem mem true (dropTupMem mem xs)
              rwa [heqxs] at hopt0
            exact hblk .here pb _ _ xs hsh hopt hbt' m hw3
          · have hbf' : validateCTPlan pb (bkh (insertTupMem mem (.imm false)
                (toOptArgTup (Tup.units (eraseMem mem))))) = true := by
              rcases hbody.2 with hc | hc
              · rw [hkeepF] at hc; cases hc
              · exact hc
            have hsh : TRel (fun _ => ArgShapeEq)
                (insertTupMem mem (.imm false) (toOptArgTup (Tup.units (eraseMem mem))))
                (insertTupMem mem (.imm false) (toOptArgTup (dropTupMem mem xs))) :=
              trel_insertTupMem mem rfl (TRel.mono (fun _ _ _ h => h.shape)
                (toOptArgTup_trel _ _))
            have hopt : ∀ q ∈ Tup.zip (insertTupMem mem (.imm false) (toOptArgTup (dropTupMem mem xs))) xs,
                ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2 := by
              have heqxs : insertTupMem mem false (dropTupMem mem xs) = xs := by
                rw [← hget, insertTupMem_get_drop]
              have hopt0 := OptValCtx.tup_insertTupMem mem false (dropTupMem mem xs)
              rwa [heqxs] at hopt0
            exact hblk .here pb _ _ xs hsh hopt hbf' m hw3
    | there i =>
      exact ctSrcConts_closed_targets Γ Q X acts pbs bkt b₂t b₃t (splitLabelTup _ _ Js_out).2
        lsNo lsBody hteqs hls hvaltl hsp.2 (fun j => hblk (.there j)) i xs m hw3

theorem rewriteCTAux_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg (CTOptV Val)) Val} {D : Ctx (CTLabel Val Cont rs) Cont}
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} {e₃ : Expr Val Cont rs}
    (hwf : Wf G D e₂ e₃) :
    ∀ {Gk : Ctx (Arg (CTOptV UnitV)) (Arg (CTOptV Val))}
      {Dk : Ctx (ValidL rs) (CTLabel Val Cont rs)}
      {ek : Expr (Arg (CTOptV UnitV)) (ValidL rs) rs} (_hwk : Wf Gk Dk ek e₂)
      {G_s : Ctx (Arg (CTOptV Val)) (Arg (CTOptV Val))}
      {D_s : Ctx (CTLabel Val Cont rs) (CTLabel Val Cont rs)}
      {e_s : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} (_hwf_s : Wf G_s D_s e_s e₂)
      (plan : CTPlan) (_hval : validateCTPlan plan ek = true),
      (∀ q ∈ Gk, ArgShapeEq q.2.1 q.2.2) → CTDSim Dk →
      (∀ q ∈ G_s, ArgShapeEq q.2.1 q.2.2) → CTDSim D_s →
      OptValCtx G → CTWpD Γ Q X D →
      ∀ m, wp Γ Q X e₃ m → wp Γ Q X (rewriteCTAux plan e₂) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_let with ⟨op_k, k_k, rfl, hop_k, hk_k⟩
    rcases hwf_s.rhs_let with ⟨op_s, k_s, rfl, hop_s, hk_s⟩
    cases hop with
    | mk code hargs =>
      cases hop_k with
      | mk _ hargs_k =>
        cases hop_s with
        | mk _ hargs_s =>
          cases plan with
          | node1 pk =>
            have helk := evalThreadLet?_shape code (trel_flattenArgs_shape hGk hargs_k)
            have hels := evalThreadLet?_shape code (trel_flattenArgs_shape hGs hargs_s)
            dsimp only [validateCTPlan] at hval
            dsimp only [rewriteCTAux]
            rcases helk with ⟨hek, he₂⟩ | ⟨ok, o₂, hek, he₂, hok⟩
            · rw [hek] at hval; rw [he₂]
              rcases hels with ⟨_, he₂'⟩ | ⟨os, o₂', _, he₂', _⟩
              · obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
                rw [hra]
                dsimp only [wp, Op.wp] at hw3 ⊢
                rw [← hvals] at hw3
                exact OpCode.wp_mono code _ (fun r hr =>
                  ih (toOptArgTup r) r (hk_k (toOptArgTup (Tup.units _)) (toOptArgTup r))
                    (hk_s (toOptArgTup r) (toOptArgTup r)) pk hval
                    (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGk p))
                    hDk
                    (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGs p))
                    hDs (OptValCtx.of_toOptArgTup hG r) hD m hr) hw3
              · rw [he₂] at he₂'; cases he₂'
            · rw [hek] at hval; rw [he₂]
              rcases hels with ⟨_, he₂'⟩ | ⟨os, o₂', _, he₂', hos⟩
              · rw [he₂] at he₂'; cases he₂'
              · rw [he₂] at he₂'; cases he₂'
                obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
                obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he₂ hw3
                exact ih o₂ (vals rout) (hk_k ok o₂) (hk_s os o₂) pk hval
                  (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hok p) (hGk p))
                  hDk
                  (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hos p) (hGs p))
                  hDs (OptValCtx.of_toRealArgs? hG hrout) hD m hkw
          | _ => dsimp only [validateCTPlan] at hval; cases hval
  | load t ha _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨v, hv, hw3⟩
    rcases hwk.rhs_load with ⟨_, k_k, rfl, _, hk_k⟩
    rcases hwf_s.rhs_load with ⟨_, k_s, rfl, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨ra, hra, hval'⟩ := hG.flattenArg ha
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hra]; dsimp only [wp]; rw [hval']
      exact ⟨v, hv, ih (.var (some v)) v (hk_k (.var (some ())) (.var (some v)))
        (hk_s (.var (some v)) (.var (some v))) pk hval
        (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGk p hp') hDk
        (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGs p hp') hDs
        (hG.cons_var v) hD m hw3⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | store hv ha _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨hok, hw3⟩
    rcases hwk.rhs_store with ⟨_, _, k_k, rfl, _, _, hk_k⟩
    rcases hwf_s.rhs_store with ⟨_, _, k_s, rfl, _, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨rv, hrv, hvalv⟩ := hG.flattenArg hv
      obtain ⟨ra, hra, hvala⟩ := hG.flattenArg ha
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hrv, hra]; dsimp only [wp]; rw [hvalv, hvala]
      exact ⟨hok, ih hk_k hk_s pk hval hGk hDk hGs hDs hG hD _ hw3⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | call f hargs _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨_, k_k, rfl, _, hk_k⟩
    rcases hwf_s.rhs_call with ⟨_, k_s, rfl, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hra]; dsimp only [wp]; rw [hvals]
      exact ⟨P, E, hΓ, fun r m' hr =>
        ih (toOptArgTup r) r (hk_k (toOptArgTup (Tup.units _)) (toOptArgTup r))
          (hk_s (toOptArgTup r) (toOptArgTup r)) pk hval
          (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGk p)) hDk
          (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGs p)) hDs
          (OptValCtx.of_toOptArgTup hG r) hD m' (hP r m' hr), hE⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | jnz hc _ _ iht ihe =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_jnz with ⟨c_k, t_k, e_k, rfl, hc_k, ht_k, he_k⟩
    rcases hwf_s.rhs_jnz with ⟨c_s, t_s, e_s', rfl, hc_s, ht_s, he_s⟩
    cases plan with
    | node2 pt pe =>
      have hsh := ArgShapeEq.flattenArg hGk hc_k
      obtain ⟨rc, hrc, hvalc⟩ := hG.flattenArg hc
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      cases e₁ : flattenArg c_k <;> cases e₂ : flattenArg _ <;>
        rw [e₁, e₂] at hsh <;> rw [e₁] at hval <;> rw [e₂] at hrc
      · rename_i ov
        cases ov with
        | none => dsimp only [toRealArg?] at hrc; cases hrc
        | some v =>
          dsimp only [toRealArg?] at hrc
          have hvc := (congrArg Arg.val (Option.some.inj hrc)).trans hvalc
          simp only [Bool.and_eq_true] at hval
          dsimp only [wp]
          exact ⟨fun hvt => iht ht_k ht_s pt hval.1 hGk hDk hGs hDs hG hD m (hw3.1 (hvc ▸ hvt)),
                 fun hvf => ihe he_k he_s pe hval.2 hGk hDk hGs hDs hG hD m (hw3.2 (hvc ▸ hvf))⟩
      · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
      · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
      · rename_i b₁ b₂
        dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        dsimp only [toRealArg?] at hrc; cases hrc
        cases b₁
        · exact ihe he_k he_s pe hval hGk hDk hGs hDs hG hD m (hw3.2 hvalc.symm)
        · exact iht ht_k ht_s pt hval hGk hDk hGs hDs hG hD m (hw3.1 hvalc.symm)
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | jump hj hargs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk _ _ hG hD m hw3
    rcases hwk.rhs_jump with ⟨j_k, args_k, rfl, hj_k, hargs_k⟩
    cases plan with
    | jump tryInl =>
      obtain ⟨hts, hsinl⟩ := hDk _ hj_k
      have hfa := trel_flattenArgs_shape hGk hargs_k
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      have hcan := hts.canEmit_eq hfa
      have his := hsinl _ _ hfa
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux, CTLabel.emitJump]
      cases tryInl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hval ⊢
        rw [hcan] at hval
        exact (hD _ hj).1 _ ra m hra hval (by simpa [wp, hvals] using hw3)
      · simp only [↓reduceIte] at hval ⊢
        cases he_k : j_k.inline? (flattenArgs args_k) <;>
          cases he_2 : CTLabel.inline? _ (flattenArgs _) <;>
          rw [he_k] at hval his <;> rw [he_2] at his
        · rw [hcan] at hval
          exact (hD _ hj).1 _ ra m hra hval (by simpa [wp, hvals] using hw3)
        · simp at his
        · simp at his
        · exact (hD _ hj).2 _ ra _ m he_2 hra (by simpa [wp, hvals] using hw3)
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | ret hvs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ hG _ m hw3
    rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hvs
      dsimp only [rewriteCTAux]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | exit f hargs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ hG _ m hw3
    rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      dsimp only [rewriteCTAux]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | hlt =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ _ _ m hw3
    rcases hwk.rhs_hlt with rfl
    cases plan with
    | leaf => exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | @group G D sig b₂ b₃ k₂ k₃ hb _ ihb ihk =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    rcases hwf_s.rhs_group with ⟨bs, ks, rfl, hbs, hks⟩
    cases plan with
    | group acts pbs pk =>
      dsimp only [validateCTPlan] at hval
      simp only [Bool.and_eq_true] at hval
      rcases hval with ⟨hvalb, hvalk⟩
      dsimp only [rewriteCTAux, wp]
      intro Js_out hcl_out
      let lsNok := validTargets (rs := rs) acts sig
      let lsNo₂ := buildTargets (V := Val) (rs := rs) acts sig Js_out
      have hNoSim : CTDSim (Tup.zip lsNok lsNo₂) := validTargets_buildTargets_sim acts sig Js_out
      have hNoSelf : CTDSim (Tup.zip lsNo₂ lsNo₂) := buildTargets_self_sim acts sig Js_out
      let lsBodyk := attachInlines acts pbs (bk lsNok) lsNok
      let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
      let lsBody_s := attachInlines acts pbs (bs lsNo₂) lsNo₂
      have hBodySim : CTDSim (Tup.zip lsBodyk lsBody₂) :=
        attachInlines_sim hGk (hNoSim.append hDk) acts pbs (bk lsNok) (b₂ lsNo₂)
          (hbk lsNok lsNo₂) lsNok lsNo₂ hNoSim
      have hBodySelf : CTDSim (Tup.zip lsBody_s lsBody₂) :=
        attachInlines_sim hGs (hNoSelf.append hDs) acts pbs (bs lsNo₂) (b₂ lsNo₂)
          (hbs lsNo₂ lsNo₂) lsNo₂ lsNo₂ hNoSelf
      let Js_src := ctSrcConts Γ Q X lsBody₂
      have hD_body : CTWpD Γ Q X (Tup.zip lsBody₂ Js_src ++ D) :=
        (ctSrcConts_wpD Γ Q X lsBody₂).append hD
      have hD_no : CTWpD Γ Q X (Tup.zip lsNo₂ Js_src ++ D) :=
        (ctSrcConts_noInl_wpD Γ Q X lsNo₂ lsBody₂ (buildTargets_noInl_get acts Js_out)
          (attachInlines_targetsEq acts pbs (b₂ lsNo₂) lsNo₂)).append hD
      have hcl_src : Closed Γ Q X (b₃ Js_src) Js_src := by
        rw [closed_iff]
        intro ts i xs m' hw_src
        rw [ctSrcConts_get]
        dsimp only [ctSrcCont]
        refine ⟨?_, fun a ra e_out heout hreal hvals => ?_⟩
        · exact ctSrcConts_closed_targets Γ Q X acts pbs (bk lsBodyk) (b₂ lsBody₂) (b₃ Js_src)
            Js_out lsNo₂ lsBody₂ (attachInlines_targetsEq acts pbs (b₂ lsNo₂) lsNo₂) rfl hvalb hcl_out
            (fun i' pb ak a₂ xs' hsh hopt hvb m'' hw'' => by
              obtain ⟨r_xs, hrx, hvsx⟩ := hG.toRealArgs?_zip hopt
              exact ihb lsBody₂ Js_src i' a₂ xs' ((hbk lsBodyk lsBody₂).get i' ak a₂)
                ((hbs lsBody_s lsBody₂).get i' a₂ a₂) pb hvb
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hsh p) (hGk p))
                (hBodySim.append hDk)
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.refl_mem_zip a₂ p) (hGs p))
                (hBodySelf.append hDs)
                (by simpa [hvsx] using OptValCtx.of_toRealArgs? hG hrx) hD_body m'' hw'')
            i xs m' hw_src
        · obtain ⟨pb, budget, hvi, rfl⟩ := attachInlines_get_inline_some acts pbs (b₂ lsNo₂) lsNo₂
            i a e_out (buildTargets_noInl_get acts Js_out i a) heout
          have hwf_s_blk := (hbs lsNo₂ lsNo₂).get i a a
          have hsh_a : ∀ p ∈ Tup.zip a a ++ G_s, ArgShapeEq p.2.1 p.2.2 := fun p hp =>
            (List.mem_append.1 hp).elim (ArgShapeEq.refl_mem_zip a p) (hGs p)
          obtain ⟨_, hp'_s, G_s', hG_s', hpeel_wf_s⟩ := peelThreadHead_sim 4 false pb hwf_s_blk hsh_a
          have hwf_wp_blk := (hb lsNo₂ Js_src).get i a (vals ra)
          have hG_a : OptValCtx (Tup.zip a (vals ra) ++ G) :=
            OptValCtx.of_toRealArgs? hG hreal
          obtain ⟨G_peel, e₃', hwf_peel, hG_peel, hw_peel⟩ :=
            peelThreadHead_wp 4 false pb hwf_wp_blk hG_a (by simpa [hvals] using hw_src)
          have hvi_s : validateInline budget (peelThreadHead 4 false pb ((bs lsNo₂).get i a)).2.1
              (peelThreadHead 4 false pb ((bs lsNo₂).get i a)).2.2 =
              validateInline budget (peelThreadHead 4 false pb ((b₂ lsNo₂).get i a)).2.1
              (peelThreadHead 4 false pb ((b₂ lsNo₂).get i a)).2.2 := by
            rw [hp'_s]
            exact validateInline_sim budget _ hpeel_wf_s hG_s' (hNoSelf.append hDs)
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hvi
          rw [← hp'_s]
          exact rewriteCTInline_wp hwf_peel hpeel_wf_s (hvi_s.trans hn)
            hG_s' (hNoSelf.append hDs) hG_peel hD_no m' hw_peel
      exact ihk lsBody₂ Js_src (hkk lsBodyk lsBody₂) (hks lsBody_s lsBody₂) pk hvalk
        hGk (hBodySim.append hDk) hGs (hBodySelf.append hDs) hG hD_body m (hw3 Js_src hcl_src)
    | _ => dsimp only [validateCTPlan] at hval; cases hval

/-! ### Call-set well-scopedness (`*_callsOk`) -/

private def CTCallsOkD (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)) : Prop :=
  ∀ p ∈ D, ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits

private theorem CTCallsOkD.append {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {H D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hH : CTCallsOkD allowed exits H) (hD : CTCallsOkD allowed exits D) :
    CTCallsOkD allowed exits (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem ctTarget_emit_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (t : CTTarget UnitV (fun _ => Unit) ts) (a : Tup (Arg (CTOptV UnitV)) ts) :
    (t.emit (rs := rs) a).callsOk allowed exits := by
  cases t with
  | keep _ => dsimp only [CTTarget.emit]; split <;> trivial
  | dead => trivial
  | split m lT? lF? lD? =>
    dsimp only [CTTarget.emit]
    cases getTupMem m a with
    | imm b => cases b <;> dsimp only <;> split <;> trivial
    | var ov =>
      cases ov with
      | none => trivial
      | some _ =>
        dsimp only
        cases lD? with
        | some _ => dsimp only; split <;> trivial
        | none => dsimp only; split <;> trivial

private theorem peelThreadHead_keep_wf {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)} →
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)} →
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs} →
    {e₂ : Expr UnitV (fun _ => Unit) rs} →
    Wf G D e₁ e₂ → e₂.callsOk allowed exits →
    let r := peelThreadHead fuel res p e₁
    ∃ G' e₂', Wf G' D r.2.2 e₂' ∧ e₂'.callsOk allowed exits
  | 0, _, _, G, _, _, e₂, hwf, hc => ⟨G, e₂, hwf, hc⟩
  | fuel + 1, res, p, G, D, _, _, hwf, hc => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        dsimp only [peelThreadHead]
        cases evalThreadLet? code (flattenArgs _) with
        | none => exact ⟨G, _, .let_ (.mk code hargs) hk, hc⟩
        | some out =>
          exact peelThreadHead_keep_wf fuel res pk (hk out (Tup.units _)) hc
      all_goals exact ⟨G, _, hwf0, hc⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc_arg ht he =>
        clear hwf0
        dsimp only [peelThreadHead]
        cases flattenArg _ with
        | imm b =>
          cases b with
          | false => exact peelThreadHead_keep_wf fuel true pe he hc.2
          | true => exact peelThreadHead_keep_wf fuel true pt ht hc.1
        | var _ => exact ⟨G, _, .jnz hc_arg ht he, hc⟩
      all_goals exact ⟨G, _, hwf0, hc⟩
    | _ => exact ⟨G, _, hwf, hc⟩

private theorem rewriteCTInline_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)}
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan), CTCallsOkD allowed exits D → e₂.callsOk allowed exits →
      (rewriteCTInline p e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      cases hop with
      | mk code _ =>
        dsimp only [rewriteCTInline]
        cases evalThreadLet? code _ with
        | some out => exact ih out (Tup.units _) pk hD hc
        | none =>
          cases toRealArgs? _ with
          | none => trivial
          | some _ => exact ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc
    | _ => trivial
  | load _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArg? _ with
      | none => trivial
      | some _ => exact ih (.var (some ())) () pk hD hc
    | _ => trivial
  | store _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArg? _ <;> cases toRealArg? _ <;> first | trivial | exact ih pk hD hc
    | _ => trivial
  | call _ _ _ ih =>
    intro p hD ⟨hf, hc⟩
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArgs? _ with
      | none => trivial
      | some _ => exact ⟨hf, ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro p hD ⟨hct, hce⟩
    cases p with
    | node2 pt pe =>
      dsimp only [rewriteCTInline]
      cases flattenArg _ with
      | imm b => cases b with | false => exact ihe pe hD hce | true => exact iht pt hD hct
      | var ov =>
        cases ov with
        | none => trivial
        | some _ => exact ⟨iht pt hD hct, ihe pe hD hce⟩
    | _ => trivial
  | jump hj _ =>
    intro p hD _
    cases p with
    | jump _ =>
      dsimp only [rewriteCTInline]
      split
      · exact ctTarget_emit_callsOk _ _
      · cases he : CTLabel.inline? _ (flattenArgs _) with
        | none => trivial
        | some e_out => exact hD _ hj _ e_out he
    | _ => trivial
  | ret _ =>
    intro p _ _
    cases p with | leaf => dsimp only [rewriteCTInline]; cases toRealArgs? _ <;> trivial | _ => trivial
  | exit _ _ =>
    intro p _ hc
    cases p with
    | leaf => dsimp only [rewriteCTInline]; cases toRealArgs? _ with | none => trivial | some _ => exact hc
    | _ => trivial
  | hlt => intro p _ _; cases p <;> trivial
  | group _ _ _ _ => intro p _ _; cases p <;> trivial

private theorem attachInlines_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)}
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : CTCallsOkD allowed exits D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs sig) →
    (bs₂ : Blocks UnitV (fun _ => Unit) rs sig) →
    WfB G D bs₁ bs₂ → bs₂.callsOk allowed exits →
    (ls : Tup (CTLabel UnitV (fun _ => Unit) rs) sig) →
    (∀ p ∈ Tup.zip ls (Tup.units sig), ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits) →
    ∀ p ∈ Tup.zip (attachInlines acts pbs bs₁ ls) (Tup.units sig),
      ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits
  | _, _, [], .nil, .nil, _, _, (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons b tl₁, .cons _ tl₂, .cons hb hbs, hc,
      (l, ls), hls, p, hp => by
    rcases hc with ⟨hcb, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head =>
      intro arg e_out he
      simp only [attachInlines] at he
      have hl0 : ∀ a e, l.inline? a = some e → e.callsOk allowed exits :=
        hls _ List.mem_cons_self
      cases a with
      | keep _ allow =>
        cases allow with
        | false => exact hl0 arg e_out he
        | true =>
          dsimp only [tryMakeInlineLabel] at he
          by_cases hvs : (validateInline (if (peelThreadHead 4 false pb (b arg)).1 then 8 else 3)
              (peelThreadHead 4 false pb (b arg)).2.1
              (peelThreadHead 4 false pb (b arg)).2.2).isSome = true
          · simp only [hvs, ↓reduceIte, Option.some.injEq] at he
            cases he
            obtain ⟨_, _, hwf_p, hc_p⟩ := peelThreadHead_keep_wf 4 false pb (hb arg (Tup.units _)) hcb
            exact rewriteCTInline_callsOk hwf_p _ hD hc_p
          · simp only [hvs, Bool.false_eq_true, ↓reduceIte] at he
            cases he
      | splitBool _ _ _ _ inlT inlF =>
        dsimp only [tryMakeInlineLabel] at he
        by_cases hinl : (inlT || inlF) = true
        · simp only [hinl, ↓reduceIte] at he
          by_cases hc : ((peelThreadHead 4 false pb (b arg)).1 &&
              (validateInline 8 (peelThreadHead 4 false pb (b arg)).2.1
                (peelThreadHead 4 false pb (b arg)).2.2).isSome) = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at he
            cases he
            obtain ⟨_, _, hwf_p, hc_p⟩ := peelThreadHead_keep_wf 4 false pb (hb arg (Tup.units _)) hcb
            exact rewriteCTInline_callsOk hwf_p _ hD hc_p
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at he
            cases he
        · simp only [hinl, Bool.false_eq_true, ↓reduceIte] at he
          exact hl0 arg e_out he
    | tail _ hp' =>
      exact attachInlines_callsOk hD acts pbs tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ tl₁, .cons _ tl₂, .cons _ hbs, hc, (_, ls), hls, p, hp => by
    rcases hc with ⟨_, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_callsOk hD [] .nil tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ tl₁, .cons _ tl₂, .cons _ hbs, hc, (_, ls), hls, p, hp => by
    rcases hc with ⟨_, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_callsOk hD [] .nil tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

private theorem buildTargets_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    (Js : Tup (fun _ => Unit) (threadSig acts sig)) →
    CTCallsOkD allowed exits (Tup.zip (buildTargets (V := UnitV) (rs := rs) acts sig Js) (Tup.units sig))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js), p, hp => by
    dsimp only [buildTargets, Tup.units, Tup.zip] at hp
    cases hp with
    | head => intro _ _ he; cases he
    | tail _ hp' => exact buildTargets_callsOk [] sig js p hp'
  | a :: acts, ts :: sig, js, p, hp => by
    dsimp only [buildTargets, Tup.units, Tup.zip] at hp
    cases hp with
    | head => intro _ _ he; cases he
    | tail _ hp' => exact buildTargets_callsOk acts sig (splitLabelTup _ _ js).2 p hp'

private theorem blocksAppend_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {s₁ s₂ : List (List Ty)} → {bs₁ : Blocks (fun _ => Unit) (fun _ => Unit) rs s₁} →
    {bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs s₂} →
    bs₁.callsOk allowed exits → bs₂.callsOk allowed exits →
    (blocksAppend bs₁ bs₂).callsOk allowed exits
  | [], _, .nil, _, _, h₂ => h₂
  | _ :: _, _, .cons _ _, _, h₁, h₂ => ⟨h₁.1, blocksAppend_callsOk h₁.2 h₂⟩

private theorem condConsBlock_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (b : Bool) (blk : Unit → Tup (fun _ => Unit) ts → Expr (fun _ => Unit) (fun _ => Unit) rs)
    {rest : List (List Ty)} (tl : Blocks (fun _ => Unit) (fun _ => Unit) rs rest)
    (hblk : b = true → (blk () (Tup.units ts)).callsOk allowed exits)
    (htl : tl.callsOk allowed exits) :
    (condConsBlock b blk tl).callsOk allowed exits := by
  cases b with
  | false => exact htl
  | true => exact ⟨hblk rfl, htl⟩

private theorem mkHltBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (sig : List (List Ty)) → (mkHltBlocks (V := fun _ => Unit) (L := fun _ => Unit) (rs := rs) sig).callsOk allowed exits
  | [] => trivial
  | _ :: sig => ⟨trivial, mkHltBlocks_callsOk sig⟩

private theorem mkSplitBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (m : Member .bool ts) (keepDisp keepT keepF : Bool) (lbl : CTLabel UnitV (fun _ => Unit) rs ts)
    {rwT rwF : Tup UnitV (eraseMem m) → Expr UnitV (fun _ => Unit) rs}
    (hT : (rwT (Tup.units _)).callsOk allowed exits)
    (hF : (rwF (Tup.units _)).callsOk allowed exits) :
    (mkSplitBlocks m keepDisp keepT keepF lbl rwT rwF).callsOk allowed exits := by
  refine condConsBlock_callsOk keepDisp _ _ (fun _ => ?_)
    (condConsBlock_callsOk keepT _ _ (fun _ => hT) (condConsBlock_callsOk keepF _ _ (fun _ => hF) trivial))
  dsimp only
  cases lbl.target with
  | keep _ | dead => trivial
  | split m' lT? lF? _ => cases lT? <;> cases lF? <;> simp [Expr.callsOk]

private theorem rewriteCTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs sig) →
    (ls : Tup (CTLabel UnitV (fun _ => Unit) rs) sig) →
    (∀ {ts} (i : Member ts sig) pb (a₁ : Tup (Arg (CTOptV UnitV)) ts),
      (rewriteCTAux pb (bs₁.get i a₁)).callsOk allowed exits) →
    (rewriteCTBlocks acts pbs bs₁ ls).callsOk allowed exits
  | acts, _, [], .nil, (), _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | [], _, _ :: _, .cons _ _, _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | _ :: _, .nil, _ :: _, .cons _ _, _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | a :: acts, .cons pb pbs, ts :: _, .cons _ tl₁, (_, tls), h => by
    unfold rewriteCTBlocks
    refine blocksAppend_callsOk ?_ (rewriteCTBlocks_callsOk acts pbs tl₁ tls (fun i => h (.there i)))
    cases a with
    | keep kb _ =>
      cases kb with
      | false => trivial
      | true => exact ⟨h .here pb _, trivial⟩
    | splitBool p keepT keepF keepDisp _ _ =>
      dsimp only [actSig]
      generalize splitMember? p ts = sp
      cases sp with
      | none => exact ⟨h .here pb _, trivial⟩
      | some m => exact mkSplitBlocks_callsOk m keepDisp keepT keepF _ (h .here pb _) (h .here pb _)

private theorem rewriteCTAux_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) UnitV} {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan), CTCallsOkD allowed exits D → e₂.callsOk allowed exits →
      (rewriteCTAux p e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      cases hop with
      | mk code _ =>
        dsimp only [rewriteCTAux]
        cases evalThreadLet? code _ with
        | some out => exact ih out (Tup.units _) pk hD hc
        | none =>
          cases toRealArgs? _ with
          | none => trivial
          | some _ => exact ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc
    | _ => trivial
  | load _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArg? _ with
      | none => trivial
      | some _ => exact ih (.var (some ())) () pk hD hc
    | _ => trivial
  | store _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArg? _ <;> cases toRealArg? _ <;> first | trivial | exact ih pk hD hc
    | _ => trivial
  | call _ _ _ ih =>
    intro p hD ⟨hf, hc⟩
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArgs? _ with
      | none => trivial
      | some _ => exact ⟨hf, ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro p hD ⟨hct, hce⟩
    cases p with
    | node2 pt pe =>
      dsimp only [rewriteCTAux]
      cases flattenArg _ with
      | imm b => cases b with | false => exact ihe pe hD hce | true => exact iht pt hD hct
      | var ov =>
        cases ov with
        | none => trivial
        | some _ => exact ⟨iht pt hD hct, ihe pe hD hce⟩
    | _ => trivial
  | jump hj _ =>
    intro p hD _
    cases p with
    | jump tryInl =>
      dsimp only [rewriteCTAux, CTLabel.emitJump]
      cases tryInl
      · exact ctTarget_emit_callsOk _ _
      · cases he : CTLabel.inline? _ (flattenArgs _) with
        | none => exact ctTarget_emit_callsOk _ _
        | some e_out => exact hD _ hj _ e_out he
    | _ => trivial
  | ret _ =>
    intro p _ _
    cases p with | leaf => dsimp only [rewriteCTAux]; cases toRealArgs? _ <;> trivial | _ => trivial
  | exit _ _ =>
    intro p _ hc
    cases p with
    | leaf => dsimp only [rewriteCTAux]; cases toRealArgs? _ with | none => trivial | some _ => exact hc
    | _ => trivial
  | hlt => intro p _ _; cases p <;> trivial
  | @group _ D sig b₁ b₂ k₁ k₂ hb _ ihb ihk =>
    intro p hD ⟨hcb, hck⟩
    cases p with
    | group acts pbs pk =>
      dsimp only [rewriteCTAux, Expr.callsOk]
      let lsNo := buildTargets (V := UnitV) (rs := rs) acts sig (Tup.units _)
      have hNo : CTCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig)) :=
        buildTargets_callsOk acts sig (Tup.units _)
      have hD_no : CTCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig) ++ D) := hNo.append hD
      let lsBody := attachInlines acts pbs (b₁ lsNo) lsNo
      have hBody : CTCallsOkD allowed exits (Tup.zip lsBody (Tup.units sig)) :=
        attachInlines_callsOk hD_no acts pbs (b₁ lsNo) (b₂ (Tup.units sig)) (hb lsNo (Tup.units sig))
          hcb lsNo hNo
      have hD_body : CTCallsOkD allowed exits (Tup.zip lsBody (Tup.units sig) ++ D) := hBody.append hD
      refine ⟨rewriteCTBlocks_callsOk acts pbs (b₁ lsBody) lsNo (fun i pb a₁ =>
        ihb lsBody (Tup.units sig) i a₁ (Tup.units _) pb hD_body (Blocks.callsOk_get hcb i)),
        ihk lsBody (Tup.units sig) pk hD_body hck⟩
    | _ => trivial

private theorem denoteB_toTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → {bs₁ : Blocks K KL rs sig} → {bs₂ : Blocks UnitV (fun _ => Unit) rs sig} →
    (nv nl : Nat) → (vs : List ((_t : Ty) × Unit)) → (ls : List ((_ts : List Ty) × Unit)) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (denote UnitV (fun _ => Unit)
        (toTFlat (bs₁.get i (Tup.levels ts nv)) (nv + ts.length) nl)
        (pushTup (Tup.units ts) vs) ls).callsOk allowed exits) →
    bs₂.callsOk allowed exits →
    (denoteB UnitV (fun _ => Unit) (toTBlocks bs₁ nv nl) vs ls).callsOk allowed exits
  | [], .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, nv, nl, vs, ls, h, hc =>
    ⟨h .here hc.1, denoteB_toTBlocks_callsOk nv nl vs ls (fun i => h (.there i)) hc.2⟩

private theorem denote_toTFlat_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx K UnitV} {D : Ctx KL (fun _ => Unit)}
    {e₁ : Expr K KL rs} {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (nv nl : Nat) (vs : List ((_t : Ty) × Unit)) (ls : List ((_ts : List Ty) × Unit)),
      e₂.callsOk allowed exits →
      (denote UnitV (fun _ => Unit) (toTFlat e₁ nv nl) vs ls).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArgs vs (idxArgs nv op₁.args) with
    | none => trivial
    | some _ => exact ih (Tup.levels ts nv) (Tup.units ts) (nv + ts.length) nl _ ls hc
  | load _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs (idxArg nv _) with
    | none => trivial
    | some _ => exact ih nv () (nv + 1) nl _ ls hc
  | store _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ <;> cases denoteArg vs _ <;> first | trivial | exact ih nv nl vs ls hc
  | call _ _ _ ih =>
    intro nv nl vs ls ⟨hf, hc⟩
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ with
    | none => trivial
    | some _ => exact ⟨hf, ih (Tup.levels _ nv) (Tup.units _) (nv + _) nl _ ls hc⟩
  | jnz _ _ _ iht ihe =>
    intro nv nl vs ls ⟨ht, he⟩
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ with
    | none => trivial
    | some _ => exact ⟨iht nv nl vs ls ht, ihe nv nl vs ls he⟩
  | jump _ _ =>
    intro nv nl vs ls _
    dsimp only [toTFlat, denote]
    cases lookupL ls _ _ <;> cases denoteArgs vs _ <;> trivial
  | ret _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | exit _ _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | hlt => intro _ _ _ _ _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl vs ls ⟨hb, hk⟩
    dsimp only [toTFlat, denote, Expr.callsOk]
    exact ⟨denoteB_toTBlocks_callsOk nv (nl + sig.length) vs _
        (fun i hci => ihb (Tup.levels sig nl) (Tup.units sig) i (Tup.levels _ nv) (Tup.units _)
          (nv + _) (nl + sig.length) _ _ hci) hb,
      ihk (Tup.levels sig nl) (Tup.units sig) nv (nl + sig.length) vs _ hk⟩

end CondThreadOptImpl

/-! ## Top-level soundness theorems (`condThread_ok` and entrypoints) -/

open CondThreadOpt CondThreadOptImpl

/-- `Func.condThreadWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadWithPlan_wf {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadWithPlan plan f).Wf := by
  dsimp only [Func.condThreadWithPlan]
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact rewriteCTAux_wf
      (hf (Arg (CTOptV V₁)) (Arg (CTOptV V₂)) (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)
        (toOptArgTup xs₁) (toOptArgTup xs₂))
      plan (mem_zip_toOptArgTup xs₁ xs₂) (fun _ hp => nomatch hp)
  · exact hf

/-- `Func.condThreadWithPlan` refines `Func.wp` / `Func.spec` when `f` is well-formed. -/
theorem Func.condThreadWithPlan_spec {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.condThreadWithPlan plan f) xs m Q X := by
  dsimp only [Func.condThreadWithPlan]
  split
  · rename_i hval
    have hwf := hf (Arg (CTOptV Val)) Val (CTLabel Val Cont rs) Cont (toOptArgTup xs) xs
    have hwk := hf (Arg (CTOptV UnitV)) (Arg (CTOptV Val)) (ValidL rs) (CTLabel Val Cont rs)
      (toOptArgTup (Tup.units as)) (toOptArgTup xs)
    have hwfs := hf (Arg (CTOptV Val)) (Arg (CTOptV Val)) (CTLabel Val Cont rs) (CTLabel Val Cont rs)
      (toOptArgTup xs) (toOptArgTup xs)
    exact rewriteCTAux_wp hwf hwk hwfs plan hval
      (toOptArgTup_shape_zip _ _) (fun _ hp => nomatch hp)
      (toOptArgTup_shape_zip _ _) (fun _ hp => nomatch hp)
      (by simpa [List.append_nil] using
        OptValCtx.of_toOptArgTup (G := []) (fun _ hp => nomatch hp) xs)
      (fun _ hp => nomatch hp) m h
  · exact h

/-- `Func.condThreadWithPlan` preserves `Expr.callsOk`. -/
theorem Func.condThreadWithPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadWithPlan plan f) UnitV (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  dsimp only [Func.condThreadWithPlan]
  split
  · exact rewriteCTAux_callsOk
      (hf (Arg (CTOptV UnitV)) UnitV (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)
        (toOptArgTup (Tup.units as)) (Tup.units as))
      plan (fun _ hp => nomatch hp) hc
  · exact hc

/-- `Func.condThreadPass` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadPass_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadPass f).Wf := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_wf _ hf
  · exact Func.wf_of_denote (reifyFunc f) rfl

/-- `Func.condThreadPass` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadPass_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadPass f) xs m Q X := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_spec _ hf h
  · exact Func.renorm_spec hf h

/-- `Func.condThreadPass` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadPass_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadPass f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_callsOk _ hf hc
  · simpa [denoteFunc, reifyFunc] using
      denote_toTFlat_callsOk
        (hf K UnitV KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
        as.length 0 (pushTup (Tup.units as) []) [] hc

/-- `Func.condThreadOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadOpt f).Wf :=
  Func.condThreadPass_wf (Func.pathCondOpt_wf hf)

/-- `Func.condThreadOpt` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadOpt f) xs m Q X :=
  Func.condThreadPass_spec (Func.pathCondOpt_wf hf) (Func.pathCondOpt_spec hf h)

/-- Full semantic preservation of `Func.condThreadOpt` under `Func.wp` / `Func.spec`. -/
theorem condThread_ok {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.wp Γ f xs m Q X) : Func.wp Γ (Func.condThreadOpt f) xs m Q X :=
  Func.condThreadOpt_spec hf h

/-- `Func.condThreadOpt` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadOpt f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.condThreadPass_callsOk (Func.pathCondOpt_wf hf) (Func.pathCondOpt_callsOk hf hc)

/-- `Fn.condThreadOpt` preserves `Fn.Wf`. -/
theorem Fn.condThreadOpt_wf {fn : Fn} (hf : fn.Wf) : (fn.condThreadOpt).Wf :=
  Func.condThreadOpt_wf hf

/-- `Fn.condThreadOpt` refines `Func.spec`. -/
theorem Fn.condThreadOpt_spec {fn : Fn} (hf : fn.Wf)
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (fn.condThreadOpt).body xs m Q X :=
  Func.condThreadOpt_spec hf h

/-- `Fn.condThreadOpt` preserves `Fn.callsOk`. -/
theorem Fn.condThreadOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hf : fn.Wf) (hc : fn.callsOk allowed exits) :
    (fn.condThreadOpt).callsOk allowed exits :=
  Func.condThreadOpt_callsOk hf hc

/-- `Func.condThreadLateOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadLateOpt_wf {as rs : List Ty} (f : Func as rs) :
    (Func.condThreadLateOpt f).Wf :=
  Func.renorm_wf _

/-- `Func.condThreadLateOpt` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadLateOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadLateOpt f) xs m Q X :=
  Func.renorm_spec (Func.condThreadOpt_wf hf) (Func.condThreadOpt_spec hf h)

/-- `Func.condThreadLateOpt` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadLateOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadLateOpt f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  simpa [Func.condThreadLateOpt, Func.renorm, denoteFunc, reifyFunc] using
    denote_toTFlat_callsOk
      ((Func.condThreadOpt_wf hf) K UnitV KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
      as.length 0 (pushTup (Tup.units as) []) [] (Func.condThreadOpt_callsOk hf hc)

end LeanQbe.T
