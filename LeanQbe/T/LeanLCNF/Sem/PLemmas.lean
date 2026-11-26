module

public import LeanQbe.T.LeanLCNF.Sem.P

/-!
# Tier-P Metatheory, Monotonicity, Join Rules, and Soundness (`PLemmas`)

Core metatheory and soundness theorems for `LeanQbe.T.LeanLCNF.Sem.P`:
1. Order properties (`PSpec.le_refl`, `PSpec.le_trans`, `PEnv.le_refl`, `PEnv.le_trans`,
   `PJEnv.le_refl`, `PJEnv.le_set`).
2. Consequence, monotonicity, frame, and join-point rules (`PApply_conseq`, `PVal.wp_conseq`,
   `PWp_conseq`, `PWp_mono`, `PWp_env_mono`, `PWp_jp_mono`, `PWp_frame_pure`, `PWp_jp_loop`,
   `PWp_jp_rule`).
3. Fuel monotonicity and determinism of `PEval` (`PEvalCode_fuel_mono`, `PEval_fuel_mono`,
   `PEvalCode_det`, `PEval_det`).
4. Soundness of `PWp` against `PEval` (`PWp_sound_PEval`, `PWp_sound_PEval_idx`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Order Lemmas -/

theorem PSpec.le_refl (S : PSpec) : PSpec.le S S := fun _ _ _ h => h

theorem PSpec.le_trans {S₁ S₂ S₃ : PSpec} (h12 : PSpec.le S₁ S₂) (h23 : PSpec.le S₂ S₃) :
    PSpec.le S₁ S₃ := fun as Q X h => h23 as Q X (h12 as Q X h)

theorem PEnv.le_refl (Δ : PEnv) : PEnv.le Δ Δ := fun _ => PSpec.le_refl _

theorem PEnv.le_trans {Δ₁ Δ₂ Δ₃ : PEnv} (h12 : PEnv.le Δ₁ Δ₂) (h23 : PEnv.le Δ₂ Δ₃) :
    PEnv.le Δ₁ Δ₃ := fun f => PSpec.le_trans (h12 f) (h23 f)

theorem PJEnv.le_refl (J : PJEnv) : PJEnv.le J J := fun _ _ h => h

theorem PJEnv.le_set {J₁ J₂ : PJEnv} (hJ : PJEnv.le J₁ J₂) (j : Nat)
    (Jj : List PVal → Prop) : PJEnv.le (J₁.set j Jj) (J₂.set j Jj) := by
  intro i as h
  dsimp only [PJEnv.set] at h ⊢
  by_cases heq : i = j
  · simp [heq] at h ⊢; exact h
  · simp [heq] at h ⊢; exact hJ i as h

/-! ## 2. Consequence, Monotonicity, Frame, and Join-Point Rules -/

theorem PApply_conseq {Δ₁ Δ₂ : PEnv} {K₁ K₂ : PPost} {X₁ X₂ : PXPost}
    (hΔ : PEnv.le Δ₁ Δ₂) (hK : ∀ r, K₁ r → K₂ r) (hX : ∀ c, X₁ c → X₂ c)
    (fn : PVal) (args : List PVal) (h : PApply Δ₁ fn args K₁ X₁) :
    PApply Δ₂ fn args K₂ X₂ := by
  cases fn with
  | clo f arity fixed =>
    unfold PApply at h ⊢
    by_cases hemp : args.isEmpty = true
    · rw [ite_eq_left hemp] at h ⊢; exact hK _ h
    · rw [ite_eq_right hemp] at h ⊢
      by_cases hrem : arity - fixed.length = 0
      · rw [dite_eq_left hrem] at h ⊢; exact hX _ h
      · rw [dite_eq_right hrem] at h ⊢
        by_cases hlt : args.length < arity - fixed.length
        · rw [dite_eq_left hlt] at h ⊢; exact hK _ h
        · rw [dite_eq_right hlt] at h ⊢
          by_cases heq : args.length = arity - fixed.length
          · rw [dite_eq_left heq] at h ⊢
            rcases h with ⟨P, E, hcall, hP, hE⟩
            exact ⟨P, E, hΔ _ _ _ _ hcall, fun r hr => hK _ (hP r hr),
              fun c hc => hX _ (hE c hc)⟩
          · rw [dite_eq_right heq] at h ⊢
            rcases h with ⟨P, E, hcall, hP, hE⟩
            exact ⟨P, E, hΔ _ _ _ _ hcall,
              fun r hr => PApply_conseq hΔ hK hX r (args.drop (arity - fixed.length)) (hP r hr),
              fun c hc => hX _ (hE c hc)⟩
  | erased | bits _ _ | nat _ | int _ | ctor _ _ _ | str _ | arr _ | barr _ =>
    unfold PApply at h ⊢; exact hX _ h
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

theorem PVal.wp_conseq {ar : PArity} {Δ₁ Δ₂ : PEnv} {ρ : PValEnv} {ty : LcTy}
    {v : LcVal} {K₁ K₂ : PPost} {X₁ X₂ : PXPost}
    (hΔ : PEnv.le Δ₁ Δ₂) (hK : ∀ r, K₁ r → K₂ r) (hX : ∀ c, X₁ c → X₂ c)
    (h : PVal.wp ar Δ₁ ρ ty v K₁ X₁) : PVal.wp ar Δ₂ ρ ty v K₂ X₂ := by
  cases v with
  | lit l => cases l <;> exact hK _ h
  | erased => exact hK _ h
  | ap f as =>
    dsimp only [PVal.wp] at h ⊢
    cases hf : ρ f <;> cases has : ρ.evalArgs as <;> simp [hf, has] at h ⊢
    exact PApply_conseq hΔ hK hX _ _ h
  | ctor ci as =>
    dsimp only [PVal.wp] at h ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at h
    | some vs =>
      simp only [has] at h ⊢
      cases hmk : PVal.mkCtor ty ci vs with
      | none => simp [hmk] at h
      | some r => simp only [hmk] at h ⊢; exact hK r h
  | oproj i x =>
    dsimp only [PVal.wp] at h ⊢
    cases hp : (ρ x).bind (·.getObj? i) with
    | none => simp [hp] at h
    | some r => simp only [hp] at h ⊢; exact hK r h
  | uproj i x =>
    dsimp only [PVal.wp] at h ⊢
    cases hp : (ρ x).bind (·.getUsize? i) with
    | none => simp [hp] at h
    | some r => simp only [hp] at h ⊢; exact hK r h
  | sproj n off x =>
    dsimp only [PVal.wp] at h ⊢
    cases hp : (ρ x).bind (·.getScalar? n off ty) with
    | none => simp [hp] at h
    | some r => simp only [hp] at h ⊢; exact hK r h
  | fap f as =>
    dsimp only [PVal.wp] at h ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at h
    | some vs =>
      simp only [has] at h ⊢
      by_cases hoob : (f == "outOfBounds._redArg") = true
      · rw [ite_eq_left hoob] at h ⊢
        by_cases hlen : (vs.length == 1) = true
        · rw [ite_eq_left hlen] at h ⊢; exact hX _ h
        · rw [ite_eq_right hlen] at h; exact False.elim h
      · rw [ite_eq_right hoob] at h ⊢
        by_cases hp : pIsPrimName f = true
        · rw [ite_eq_left hp] at h ⊢
          cases hpr : primP f vs with
          | none => simp [hpr] at h
          | some r => simp only [hpr] at h ⊢; exact hK r h
        · rw [ite_eq_right hp] at h ⊢
          rcases h with ⟨P, E, hcall, hP, hE⟩
          exact ⟨P, E, hΔ _ _ _ _ hcall, fun r hr => hK r (hP r hr), fun c hc => hX c (hE c hc)⟩
  | pap f as =>
    dsimp only [PVal.wp] at h ⊢
    cases ha : ar f <;> cases has : ρ.evalArgs as <;> simp [ha, has] at h ⊢
    exact ⟨h.1, hK _ h.2⟩
  | reset _ x =>
    dsimp only [PVal.wp] at h ⊢
    cases hx : ρ x with
    | none => simp [hx] at h
    | some _ => simp only [hx] at h ⊢; exact hK _ h
  | reuse x ci _ as =>
    dsimp only [PVal.wp] at h ⊢
    cases hx : ρ x <;> cases has : ρ.evalArgs as <;> simp [hx, has] at h ⊢
    rename_i vs
    cases hmk : PVal.mkCtor ty ci vs with
    | none => simp [hmk] at h
    | some r => simp only [hmk] at h ⊢; exact hK r h
  | box t x =>
    dsimp only [PVal.wp] at h ⊢
    cases hb : (ρ x).bind (PVal.box t) with
    | none => simp [hb] at h
    | some r => simp only [hb] at h ⊢; exact hK r h
  | unbox x =>
    dsimp only [PVal.wp] at h ⊢
    cases hu : (ρ x).bind (PVal.unbox ty) with
    | none => simp [hu] at h
    | some r => simp only [hu] at h ⊢; exact hK r h
  | isShared x => exact ⟨h.1, fun b => hK _ (h.2 b)⟩

mutual
/-- Unified consequence / monotonicity theorem for `PWp` in `Δ`, `J`, `Q`, and `X`. -/
theorem PWp_conseq {ar : PArity} {Δ₁ Δ₂ : PEnv} {Q₁ Q₂ : PPost} {X₁ X₂ : PXPost}
    (hΔ : PEnv.le Δ₁ Δ₂) (hQ : ∀ r, Q₁ r → Q₂ r) (hX : ∀ c, X₁ c → X₂ c) :
    ∀ (c : LcCode) {J₁ J₂ : PJEnv}, PJEnv.le J₁ J₂ → ∀ (ρ : PValEnv),
      PWp ar Δ₁ J₁ ρ Q₁ X₁ c → PWp ar Δ₂ J₂ ρ Q₂ X₂ c
  | .let_ x ty v k, _, _, hJ, ρ, h =>
    PVal.wp_conseq hΔ (fun r hk => PWp_conseq hΔ hQ hX k hJ (ρ.set x r) hk) hX h
  | .jp j ps body k, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    intro Jj hcl
    refine PWp_conseq hΔ hQ hX k (PJEnv.le_set hJ j Jj) ρ (h Jj fun as hlen hb => ?_)
    exact hcl as hlen (PWp_conseq hΔ hQ hX body (PJEnv.le_set hJ j Jj) (ρ.bindAll ps as) hb)
  | .jmp j as, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at h
    | some ws => simp only [has] at h ⊢; exact hJ j ws h
  | .cases x alts, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases ht : (ρ x).bind PVal.tag? with
    | none => simp [ht] at h
    | some tag =>
      simp only [ht] at h ⊢
      exact PWpCtorAlts_conseq hΔ hQ hX tag alts
        (PWpDfltAlts_conseq hΔ hQ hX alts hJ ρ) hJ ρ h
  | .ret a, _, _, _, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases ha : ρ.evalArg a with
    | none => simp [ha] at h
    | some v => simp only [ha] at h ⊢; exact hQ v h
  | .unreach, _, _, _, _, h => hX _ h
  | .oset x i y k, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setObj i yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PWp_conseq hΔ hQ hX k hJ (ρ.set x xv') h
  | .uset x i y k, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setUsize i yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PWp_conseq hΔ hQ hX k hJ (ρ.set x xv') h
  | .sset x n off y ty k, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setScalar n off ty yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PWp_conseq hΔ hQ hX k hJ (ρ.set x xv') h
  | .setTag x cidx k, _, _, hJ, ρ, h => by
    dsimp only [PWp] at h ⊢
    cases hs : (ρ x).bind (·.setTag cidx) with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PWp_conseq hΔ hQ hX k hJ (ρ.set x xv') h
  | .inc _ _ _ k, _, _, hJ, ρ, h => PWp_conseq hΔ hQ hX k hJ ρ h
  | .dec _ _ _ k, _, _, hJ, ρ, h => PWp_conseq hΔ hQ hX k hJ ρ h
  | .del _ k, _, _, hJ, ρ, h => PWp_conseq hΔ hQ hX k hJ ρ h

theorem PWpCtorAlts_conseq {ar : PArity} {Δ₁ Δ₂ : PEnv} {Q₁ Q₂ : PPost} {X₁ X₂ : PXPost}
    (hΔ : PEnv.le Δ₁ Δ₂) (hQ : ∀ r, Q₁ r → Q₂ r) (hX : ∀ c, X₁ c → X₂ c)
    (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) {kD₁ kD₂ : Prop}, (kD₁ → kD₂) →
      ∀ {J₁ J₂ : PJEnv}, PJEnv.le J₁ J₂ → ∀ (ρ : PValEnv),
      PWpCtorAlts ar Δ₁ J₁ ρ Q₁ X₁ tag alts kD₁ →
      PWpCtorAlts ar Δ₂ J₂ ρ Q₂ X₂ tag alts kD₂
  | [], _, _, hkD, _, _, _, _, h => hkD h
  | (.ctor ci _, b) :: rest, _, _, hkD, _, _, hJ, ρ, h => by
    dsimp only [PWpCtorAlts] at h ⊢
    by_cases hci : ci = tag
    · rw [ite_eq_left hci] at h ⊢; exact PWp_conseq hΔ hQ hX b hJ ρ h
    · rw [ite_eq_right hci] at h ⊢; exact PWpCtorAlts_conseq hΔ hQ hX tag rest hkD hJ ρ h
  | (.dflt, _) :: rest, _, _, hkD, _, _, hJ, ρ, h =>
    PWpCtorAlts_conseq hΔ hQ hX tag rest hkD hJ ρ h

theorem PWpDfltAlts_conseq {ar : PArity} {Δ₁ Δ₂ : PEnv} {Q₁ Q₂ : PPost} {X₁ X₂ : PXPost}
    (hΔ : PEnv.le Δ₁ Δ₂) (hQ : ∀ r, Q₁ r → Q₂ r) (hX : ∀ c, X₁ c → X₂ c) :
    ∀ (alts : List (LcPat × LcCode)) {J₁ J₂ : PJEnv}, PJEnv.le J₁ J₂ → ∀ (ρ : PValEnv),
      PWpDfltAlts ar Δ₁ J₁ ρ Q₁ X₁ alts → PWpDfltAlts ar Δ₂ J₂ ρ Q₂ X₂ alts
  | [], _, _, _, _, h => False.elim h
  | (.dflt, b) :: _, _, _, hJ, ρ, h => PWp_conseq hΔ hQ hX b hJ ρ h
  | (.ctor _ _, _) :: rest, _, _, hJ, ρ, h => PWpDfltAlts_conseq hΔ hQ hX rest hJ ρ h
end

/-- Postcondition / exit-postcondition monotonicity of `PWp`. -/
theorem PWp_mono {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q₁ Q₂ : PPost} {X₁ X₂ : PXPost} {c : LcCode}
    (hQ : ∀ r, Q₁ r → Q₂ r) (hX : ∀ e, X₁ e → X₂ e) (h : PWp ar Δ J ρ Q₁ X₁ c) :
    PWp ar Δ J ρ Q₂ X₂ c :=
  PWp_conseq (PEnv.le_refl Δ) hQ hX c (PJEnv.le_refl J) ρ h

/-- Environment monotonicity of `PWp`. -/
theorem PWp_env_mono {ar : PArity} {Δ₁ Δ₂ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {c : LcCode} (hΔ : PEnv.le Δ₁ Δ₂) (h : PWp ar Δ₁ J ρ Q X c) :
    PWp ar Δ₂ J ρ Q X c :=
  PWp_conseq hΔ (fun _ h => h) (fun _ h => h) c (PJEnv.le_refl J) ρ h

/-- Join-environment monotonicity of `PWp`. -/
theorem PWp_jp_mono {ar : PArity} {Δ : PEnv} {J₁ J₂ : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {c : LcCode} (hJ : PJEnv.le J₁ J₂) (h : PWp ar Δ J₁ ρ Q X c) :
    PWp ar Δ J₂ ρ Q X c :=
  PWp_conseq (PEnv.le_refl Δ) (fun _ h => h) (fun _ h => h) c hJ ρ h

/-- Pure-proposition frame rule for `PWp`. -/
theorem PWp_frame_pure {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {c : LcCode} {φ : Prop}
    (hφ : φ) (h : PWp ar Δ J ρ Q X c) :
    PWp ar Δ J ρ (fun r => φ ∧ Q r) (fun e => φ ∧ X e) c :=
  PWp_mono (fun _ hq => ⟨hφ, hq⟩) (fun _ hx => ⟨hφ, hx⟩) h

/-- Measure-indexed join-point induction rule for `PWp`. -/
theorem PWp_jp_loop {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {j : Nat} {ps : List LcParam} {body k : LcCode}
    (Inv : Nat → List PVal → Prop)
    (hpm : ∀ n as, Inv n as → as.length = ps.length)
    (hbody : ∀ (Jj : List PVal → Prop) n as,
      (∀ n' ys, n' < n → Inv n' ys → Jj ys) → Inv n as →
      PWp ar Δ (J.set j Jj) (ρ.bindAll ps as) Q X body)
    (hk : ∀ (Jj : List PVal → Prop), (∀ n as, Inv n as → Jj as) →
      PWp ar Δ (J.set j Jj) ρ Q X k) :
    PWp ar Δ J ρ Q X (.jp j ps body k) := by
  dsimp only [PWp]
  intro Jj hcl
  refine hk Jj fun n => ?_
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro as hinv
    exact hcl as (hpm n as hinv)
      (hbody Jj n as (fun n' ys hlt hi => ih n' hlt ys hi) hinv)

/-- Non-recursive join-point introduction rule for `PWp`. -/
theorem PWp_jp_rule {ar : PArity} {Δ : PEnv} {J : PJEnv} {ρ : PValEnv}
    {Q : PPost} {X : PXPost} {j : Nat} {ps : List LcParam} {body k : LcCode}
    (P : List PVal → Prop) (hpm : ∀ as, P as → as.length = ps.length)
    (hbody : ∀ (Jj : List PVal → Prop) as, P as →
      PWp ar Δ (J.set j Jj) (ρ.bindAll ps as) Q X body)
    (hk : ∀ (Jj : List PVal → Prop), (∀ as, P as → Jj as) → PWp ar Δ (J.set j Jj) ρ Q X k) :
    PWp ar Δ J ρ Q X (.jp j ps body k) :=
  PWp_jp_loop (fun _ => P) (fun _ => hpm) (fun Jj _ as _ h => hbody Jj as h)
    (fun Jj hJ => hk Jj (hJ 0))

/-! ## 3. `PEval` Monotonicity & Determinism -/

/-- Outcome satisfaction predicate linking `POutcome` to Tier-P `Q` and `X`. -/
@[expose] def OutcomeOk (Q : PPost) (X : PXPost) : POutcome → Prop
  | .ret v => Q v
  | .panic c => X c

theorem OutcomeOk_mono {Q₁ Q₂ : PPost} {X₁ X₂ : PXPost}
    (hQ : ∀ r, Q₁ r → Q₂ r) (hX : ∀ c, X₁ c → X₂ c) :
    ∀ {out}, OutcomeOk Q₁ X₁ out → OutcomeOk Q₂ X₂ out
  | .ret _, h => hQ _ h
  | .panic _, h => hX _ h

/-- Helper shorthand for `PEvalCode`'s recursive `callFn` at fuel `f`. -/
@[expose] def PEvalCallAt (m : LcModule) (shared : Bool) (f : Nat)
    (fn : String) (args : List PVal) : Option POutcome :=
  match m.decls.find? (·.name == fn) with
  | some d =>
    if args.length == d.params.length then
      PEvalCode f m shared [] (PValEnv.empty.bindAll d.params args) d.body
    else none
  | none => none

theorem PEvalCallAt_eq_PEval (m : LcModule) (shared : Bool) (f : Nat) (fn : String)
    (args : List PVal) : PEvalCallAt m shared f fn args = PEval f m fn args shared := rfl

theorem PEvalCode_succ_eq (f : Nat) (m : LcModule) (shared : Bool) (jps : List PJEntry)
    (ρ : PValEnv) (code : LcCode) :
    PEvalCode (f + 1) m shared jps ρ code =
      PEvalStep m shared (PEvalCallAt m shared f) (PEvalCode f m shared) jps ρ code := rfl

theorem PEvalApply_mono {c1 c2 : String → List PVal → Option POutcome}
    (hc : ∀ f as out, c1 f as = some out → c2 f as = some out)
    (fn : PVal) (args : List PVal) {out : POutcome}
    (h : PEvalApply c1 fn args = some out) : PEvalApply c2 fn args = some out := by
  cases fn with
  | clo f arity fixed =>
    unfold PEvalApply at h ⊢
    by_cases hemp : args.isEmpty = true
    · rw [ite_eq_left hemp] at h ⊢; exact h
    · rw [ite_eq_right hemp] at h ⊢
      by_cases hrem : arity - fixed.length = 0
      · rw [dite_eq_left hrem] at h ⊢; exact h
      · rw [dite_eq_right hrem] at h ⊢
        by_cases hlt : args.length < arity - fixed.length
        · rw [dite_eq_left hlt] at h ⊢; exact h
        · rw [dite_eq_right hlt] at h ⊢
          by_cases heq : args.length = arity - fixed.length
          · rw [dite_eq_left heq] at h ⊢; exact hc _ _ _ h
          · rw [dite_eq_right heq] at h ⊢
            cases hres : c1 f (fixed ++ args.take (arity - fixed.length)) with
            | none => simp [hres] at h
            | some o1 =>
              rw [hres] at h
              rw [hc _ _ _ hres]
              cases o1 with
              | ret r => exact PEvalApply_mono hc r _ h
              | panic c => exact h
  | erased | bits _ _ | nat _ | int _ | ctor _ _ _ | str _ | arr _ | barr _ =>
    unfold PEvalApply at h ⊢; exact h
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

theorem PEvalVal_mono {m : LcModule} {shared : Bool}
    {c1 c2 : String → List PVal → Option POutcome}
    (hc : ∀ f as out, c1 f as = some out → c2 f as = some out)
    {ρ : PValEnv} {ty : LcTy} {v : LcVal} {out : POutcome}
    (h : PEvalVal m shared c1 ρ ty v = some out) :
    PEvalVal m shared c2 ρ ty v = some out := by
  cases v with
  | ap f as =>
    dsimp only [PEvalVal] at h ⊢
    cases hf : ρ f <;> cases has : ρ.evalArgs as <;> simp [hf, has] at h ⊢
    exact PEvalApply_mono hc _ _ h
  | fap f as =>
    dsimp only [PEvalVal] at h ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at h
    | some vs =>
      simp only [has, Option.bind_some] at h ⊢
      by_cases hoob : (f == "outOfBounds._redArg") = true
      · rw [ite_eq_left hoob] at h ⊢; exact h
      · rw [ite_eq_right hoob] at h ⊢
        by_cases hp : pIsPrimName f = true
        · rw [ite_eq_left hp] at h ⊢; exact h
        · rw [ite_eq_right hp] at h ⊢; exact hc f vs out h
  | lit l => cases l <;> dsimp only [PEvalVal] at h ⊢ <;> exact h
  | erased | ctor _ _ | oproj _ _ | uproj _ _ | sproj _ _ _
  | pap _ _ | reset _ _ | reuse _ _ _ _ | box _ _ | unbox _ | isShared _ =>
    dsimp only [PEvalVal] at h ⊢; exact h

mutual
theorem PEvalStep_mono {m : LcModule} {shared : Bool}
    {c1 c2 : String → List PVal → Option POutcome}
    {j1 j2 : List PJEntry → PValEnv → LcCode → Option POutcome}
    (hc : ∀ f as out, c1 f as = some out → c2 f as = some out)
    (hj : ∀ jps ρ b out, j1 jps ρ b = some out → j2 jps ρ b = some out) :
    ∀ (code : LcCode) (jps : List PJEntry) (ρ : PValEnv) {out : POutcome},
      PEvalStep m shared c1 j1 jps ρ code = some out →
      PEvalStep m shared c2 j2 jps ρ code = some out
  | .let_ x ty v k, jps, ρ, out, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hv : PEvalVal m shared c1 ρ ty v with
    | none => simp [hv] at h
    | some ov =>
      rw [hv] at h
      rw [PEvalVal_mono hc hv]
      cases ov with
      | ret r => exact PEvalStep_mono hc hj k jps (ρ.set x r) h
      | panic c => exact h
  | .jp j ps body k, jps, ρ, _, h =>
    PEvalStep_mono hc hj k ((j, ps, body, ρ) :: jps) ρ h
  | .jmp j as, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hdw : jps.dropWhile (fun e => e.1 != j) with
    | nil => simp [hdw] at h
    | cons hd outer =>
      rcases hd with ⟨j1', ps, body, ρ0⟩
      cases has : ρ.evalArgs as with
      | none => simp [hdw, has] at h
      | some vs =>
        simp only [hdw, has] at h ⊢
        by_cases hlen : (vs.length == ps.length) = true
        · rw [ite_eq_left hlen] at h ⊢; exact hj _ _ _ _ h
        · rw [ite_eq_right hlen] at h; simp at h
  | .cases x alts, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases ht : (ρ x).bind PVal.tag? with
    | none => simp [ht] at h
    | some tag =>
      simp only [ht] at h ⊢
      exact PEvalCtorAlts_mono hc hj tag alts jps ρ
        (fun _ h => PEvalDfltAlts_mono hc hj alts jps ρ h) h
  | .ret _, _, _, _, h => h
  | .unreach, _, _, _, h => h
  | .oset x i y k, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setObj i yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PEvalStep_mono hc hj k jps (ρ.set x xv') h
  | .uset x i y k, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setUsize i yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PEvalStep_mono hc hj k jps (ρ.set x xv') h
  | .sset x n off y ty k, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
    rename_i xv yv
    cases hs : xv.setScalar n off ty yv with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PEvalStep_mono hc hj k jps (ρ.set x xv') h
  | .setTag x cidx k, jps, ρ, _, h => by
    dsimp only [PEvalStep] at h ⊢
    cases hs : (ρ x).bind (·.setTag cidx) with
    | none => simp [hs] at h
    | some xv' => simp only [hs] at h ⊢; exact PEvalStep_mono hc hj k jps (ρ.set x xv') h
  | .inc _ _ _ k, jps, ρ, _, h => PEvalStep_mono hc hj k jps ρ h
  | .dec _ _ _ k, jps, ρ, _, h => PEvalStep_mono hc hj k jps ρ h
  | .del _ k, jps, ρ, _, h => PEvalStep_mono hc hj k jps ρ h

theorem PEvalCtorAlts_mono {m : LcModule} {shared : Bool}
    {c1 c2 : String → List PVal → Option POutcome}
    {j1 j2 : List PJEntry → PValEnv → LcCode → Option POutcome}
    (hc : ∀ f as out, c1 f as = some out → c2 f as = some out)
    (hj : ∀ jps ρ b out, j1 jps ρ b = some out → j2 jps ρ b = some out)
    (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (ρ : PValEnv)
      {d1 d2 : Option POutcome}, (∀ out, d1 = some out → d2 = some out) →
      ∀ {out}, PEvalCtorAlts m shared c1 j1 jps ρ tag alts d1 = some out →
      PEvalCtorAlts m shared c2 j2 jps ρ tag alts d2 = some out
  | [], _, _, _, _, hd, _, h => hd _ h
  | (.ctor ci _, b) :: rest, jps, ρ, _, _, hd, _, h => by
    dsimp only [PEvalCtorAlts] at h ⊢
    by_cases hci : (ci == tag) = true
    · rw [ite_eq_left hci] at h ⊢; exact PEvalStep_mono hc hj b jps ρ h
    · rw [ite_eq_right hci] at h ⊢; exact PEvalCtorAlts_mono hc hj tag rest jps ρ hd h
  | (.dflt, _) :: rest, jps, ρ, _, _, hd, _, h =>
    PEvalCtorAlts_mono hc hj tag rest jps ρ hd h

theorem PEvalDfltAlts_mono {m : LcModule} {shared : Bool}
    {c1 c2 : String → List PVal → Option POutcome}
    {j1 j2 : List PJEntry → PValEnv → LcCode → Option POutcome}
    (hc : ∀ f as out, c1 f as = some out → c2 f as = some out)
    (hj : ∀ jps ρ b out, j1 jps ρ b = some out → j2 jps ρ b = some out) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (ρ : PValEnv) {out},
      PEvalDfltAlts m shared c1 j1 jps ρ alts = some out →
      PEvalDfltAlts m shared c2 j2 jps ρ alts = some out
  | [], _, _, _, h => by simp [PEvalDfltAlts] at h
  | (.dflt, b) :: _, jps, ρ, _, h => PEvalStep_mono hc hj b jps ρ h
  | (.ctor _ _, _) :: rest, jps, ρ, _, h => PEvalDfltAlts_mono hc hj rest jps ρ h
end

theorem PEvalCode_fuel_mono {m : LcModule} {shared : Bool} :
    ∀ {f1 f2 : Nat}, f1 ≤ f2 → ∀ {jps ρ code out},
      PEvalCode f1 m shared jps ρ code = some out →
      PEvalCode f2 m shared jps ρ code = some out
  | 0, _, _, _, _, _, _, h => by simp [PEvalCode] at h
  | _ + 1, 0, hle, _, _, _, _, _ => by omega
  | f1 + 1, f2 + 1, hle, jps, ρ, code, out, h => by
    have hlt : f1 ≤ f2 := Nat.le_of_succ_le_succ hle
    rw [PEvalCode_succ_eq] at h ⊢
    refine PEvalStep_mono (c1 := PEvalCallAt m shared f1) (c2 := PEvalCallAt m shared f2)
      (j1 := PEvalCode f1 m shared) (j2 := PEvalCode f2 m shared)
      (fun fn args out' hcall => ?_)
      (fun jps' ρ' b' out' hj => PEvalCode_fuel_mono hlt hj) code jps ρ h
    dsimp only [PEvalCallAt] at hcall ⊢
    cases hd : m.decls.find? (·.name == fn) with
    | none => simp [hd] at hcall
    | some d =>
      simp only [hd] at hcall ⊢
      by_cases hlen : (args.length == d.params.length) = true
      · rw [ite_eq_left hlen] at hcall ⊢; exact PEvalCode_fuel_mono hlt hcall
      · rw [ite_eq_right hlen] at hcall; simp at hcall

theorem PEvalCallAt_mono {m : LcModule} {shared : Bool} {f1 f2 : Nat} (hle : f1 ≤ f2)
    (fn : String) (args : List PVal) {out : POutcome}
    (h : PEvalCallAt m shared f1 fn args = some out) :
    PEvalCallAt m shared f2 fn args = some out := by
  dsimp only [PEvalCallAt] at h ⊢
  cases hd : m.decls.find? (·.name == fn) with
  | none => simp [hd] at h
  | some d =>
    simp only [hd] at h ⊢
    by_cases hl : (args.length == d.params.length) = true
    · rw [ite_eq_left hl] at h ⊢; exact PEvalCode_fuel_mono hle h
    · rw [ite_eq_right hl] at h; simp at h

theorem PEval_fuel_mono {m : LcModule} {shared : Bool} {fn : String} {args : List PVal}
    {f1 f2 : Nat} {out : POutcome} (hle : f1 ≤ f2)
    (h : PEval f1 m fn args shared = some out) : PEval f2 m fn args shared = some out :=
  PEvalCallAt_mono hle fn args h

theorem PEvalCode_det {m : LcModule} {shared : Bool} {f1 f2 : Nat} {jps : List PJEntry}
    {ρ : PValEnv} {code : LcCode} {o1 o2 : POutcome}
    (h1 : PEvalCode f1 m shared jps ρ code = some o1)
    (h2 : PEvalCode f2 m shared jps ρ code = some o2) : o1 = o2 := by
  have h1' := PEvalCode_fuel_mono (Nat.le_max_left f1 f2) h1
  have h2' := PEvalCode_fuel_mono (Nat.le_max_right f1 f2) h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

theorem PEval_det {m : LcModule} {shared : Bool} {f1 f2 : Nat} {fn : String}
    {args : List PVal} {o1 o2 : POutcome}
    (h1 : PEval f1 m fn args shared = some o1)
    (h2 : PEval f2 m fn args shared = some o2) : o1 = o2 := by
  have h1' := PEval_fuel_mono (Nat.le_max_left f1 f2) h1
  have h2' := PEval_fuel_mono (Nat.le_max_right f1 f2) h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

/-! ## 4. Soundness of `PWp` wrt `PEval` -/

theorem dropWhile_head_fst {α : Type} (p : α → Nat) (j : Nat) :
    ∀ (xs : List α) {hd tl}, xs.dropWhile (fun e => p e != j) = hd :: tl → p hd = j
  | [], _, _, h => by simp at h
  | x :: rest, hd, tl, h => by
    simp only [List.dropWhile_cons] at h
    by_cases hx : (p x != j) = true
    · rw [ite_eq_left hx] at h; exact dropWhile_head_fst p j rest h
    · rw [ite_eq_right hx] at h
      cases h
      simpa using hx

theorem dropWhile_ne_cons {α : Type} (p : α → Nat) {j' : Nat} (e : α)
    (hne : p e ≠ j') (xs : List α) :
    (e :: xs).dropWhile (fun x => p x != j') = xs.dropWhile (fun x => p x != j') := by
  simp [bne_iff_ne, hne]

theorem find_eq_some_mem {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {a : α}, xs.find? p = some a → a ∈ xs
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.find?_cons] at h
    cases hx : p x <;> simp [hx] at h
    · exact List.mem_cons_of_mem _ (find_eq_some_mem h)
    · subst h; exact List.mem_cons_self

theorem find_eq_some_pred {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {a : α}, xs.find? p = some a → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.find?_cons] at h
    cases hx : p x <;> simp [hx] at h
    · exact find_eq_some_pred h
    · subst h; exact hx

/-- Join-point invariant for `PWp` → `PEvalCode` soundness up to fuel `k`. -/
@[expose] def JPEvalOk (m : LcModule) (shared : Bool) (Q : PPost) (X : PXPost)
    (J : PJEnv) (jps : List PJEntry) (k : Nat) : Prop :=
  ∀ j vs ps body ρ0 outer,
    J j vs →
    jps.dropWhile (fun e => e.1 != j) = (j, ps, body, ρ0) :: outer →
    vs.length = ps.length →
    ∀ f ≤ k, ∀ out,
      PEvalCode f m shared ((j, ps, body, ρ0) :: outer) (ρ0.bindAll ps vs) body = some out →
      OutcomeOk Q X out

private theorem JPEvalOk_shrink {m : LcModule} {shared : Bool} {Q : PPost} {X : PXPost}
    {J : PJEnv} {jps : List PJEntry} {f k : Nat} (hle : f ≤ k)
    (h : JPEvalOk m shared Q X J jps k) : JPEvalOk m shared Q X J jps f :=
  fun j vs ps body ρ0 outer hJ hdw hlen g hg out hev =>
    h j vs ps body ρ0 outer hJ hdw hlen g (Nat.le_trans hg hle) out hev

private theorem PApply_sound_PEvalApply {Δ : PEnv} {callFn : String → List PVal → Option POutcome}
    (hcall : ∀ fn args P E, Δ fn args P E → ∀ out, callFn fn args = some out → OutcomeOk P E out)
    {K : PPost} {X : PXPost} (fn : PVal) (args : List PVal) (h : PApply Δ fn args K X)
    {out : POutcome} (hev : PEvalApply callFn fn args = some out) : OutcomeOk K X out := by
  cases fn with
  | clo f arity fixed =>
    unfold PApply at h
    unfold PEvalApply at hev
    by_cases hemp : args.isEmpty = true
    · rw [ite_eq_left hemp] at h hev; cases hev; exact h
    · rw [ite_eq_right hemp] at h hev
      by_cases hrem : arity - fixed.length = 0
      · rw [dite_eq_left hrem] at h hev; cases hev; exact h
      · rw [dite_eq_right hrem] at h hev
        by_cases hlt : args.length < arity - fixed.length
        · rw [dite_eq_left hlt] at h hev; cases hev; exact h
        · rw [dite_eq_right hlt] at h hev
          by_cases heq : args.length = arity - fixed.length
          · rw [dite_eq_left heq] at h hev
            rcases h with ⟨P, E, hd, hP, hE⟩
            exact OutcomeOk_mono hP hE (hcall f (fixed ++ args) P E hd out hev)
          · rw [dite_eq_right heq] at h hev
            rcases h with ⟨P, E, hd, hP, hE⟩
            cases hres : callFn f (fixed ++ args.take (arity - fixed.length)) with
            | none => simp [hres] at hev
            | some o1 =>
              rw [hres] at hev
              have hok := hcall f _ P E hd o1 hres
              cases o1 with
              | ret r =>
                exact PApply_sound_PEvalApply hcall r (args.drop (arity - fixed.length))
                  (hP r hok) hev
              | panic c =>
                cases hev; exact hE c hok
  | erased | bits _ _ | nat _ | int _ | ctor _ _ _ | str _ | arr _ | barr _ =>
    unfold PApply at h; unfold PEvalApply at hev; cases hev; exact h
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

mutual
private theorem PWp_sound_go {m : LcModule} {shared : Bool} {Δ : PEnv} {k : Nat}
    (ihCall : ∀ fn args P E, Δ fn args P E → ∀ out,
      PEvalCallAt m shared k fn args = some out → OutcomeOk P E out)
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      JPEvalOk m shared Q X J jps f → PWp (modArityOf m) Δ J ρ Q X c →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out) :
    ∀ (c : LcCode) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv) (Q : PPost) (X : PXPost),
      JPEvalOk m shared Q X J jps k → PWp (modArityOf m) Δ J ρ Q X c →
      ∀ out, PEvalCode (k + 1) m shared jps ρ c = some out → OutcomeOk Q X out
  | .let_ x ty v kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases v with
    | lit l =>
      cases l <;>
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x _) Q X hJ hwp out hev
    | erased => exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x .erased) Q X hJ hwp out hev
    | ap f as =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hf : ρ f <;> cases has : ρ.evalArgs as <;> simp [hf, has] at hwp hev
      rename_i fn vs
      cases hap : PEvalApply (PEvalCallAt m shared k) fn vs with
      | none => simp [hap] at hev
      | some o1 =>
        rw [hap] at hev
        have hok := PApply_sound_PEvalApply ihCall fn vs hwp hap
        cases o1 with
        | ret r => exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hok out hev
        | panic c => cases hev; exact hok
    | ctor ci as =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases has : ρ.evalArgs as with
      | none => simp [has] at hwp
      | some vs =>
        simp only [has, Option.bind_some] at hwp hev
        cases hmk : PVal.mkCtor ty ci vs with
        | none => simp [hmk] at hwp
        | some r =>
          simp only [hmk, Option.map_some] at hwp hev
          exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | oproj i y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hp : (ρ y).bind (·.getObj? i) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | uproj i y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hp : (ρ y).bind (·.getUsize? i) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | sproj n off y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hp : (ρ y).bind (·.getScalar? n off ty) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | fap f as =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases has : ρ.evalArgs as with
      | none => simp [has] at hwp
      | some vs =>
        simp only [has, Option.bind_some] at hwp hev
        by_cases hoob : (f == "outOfBounds._redArg") = true
        · rw [ite_eq_left hoob] at hwp hev
          by_cases hlen : (vs.length == 1) = true
          · rw [ite_eq_left hlen] at hwp hev; cases hev; exact hwp
          · rw [ite_eq_right hlen] at hwp; exact False.elim hwp
        · rw [ite_eq_right hoob] at hwp hev
          by_cases hp : pIsPrimName f = true
          · rw [ite_eq_left hp] at hwp hev
            cases hpr : primP f vs with
            | none => simp [hpr] at hwp
            | some r =>
              simp only [hpr, Option.map_some] at hwp hev
              exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
          · rw [ite_eq_right hp] at hwp hev
            rcases hwp with ⟨P, E, hd, hP, hE⟩
            cases hres : PEvalCallAt m shared k f vs with
            | none => simp [hres] at hev
            | some o1 =>
              rw [hres] at hev
              have hok := ihCall f vs P E hd o1 hres
              cases o1 with
              | ret r =>
                exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ (hP r hok) out hev
              | panic c => cases hev; exact hE c hok
    | pap f as =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases ha : modArityOf m f <;> cases has : ρ.evalArgs as <;> simp [ha, has] at hwp hev
      rename_i a vs
      rw [ite_eq_left (by simpa using hwp.1)] at hev
      exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x (.clo f a vs)) Q X hJ hwp.2 out hev
    | reset _ y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hy : ρ y with
      | none => simp [hy] at hwp
      | some _ =>
        simp only [hy, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x .erased) Q X hJ hwp out hev
    | reuse y ci _ as =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hy : ρ y <;> cases has : ρ.evalArgs as <;> simp [hy, has] at hwp hev
      rename_i vs
      cases hmk : PVal.mkCtor ty ci vs with
      | none => simp [hmk] at hwp
      | some r =>
        simp only [hmk, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | box t y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hb : (ρ y).bind (PVal.box t) with
      | none => simp [hb] at hwp
      | some r =>
        simp only [hb, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | unbox y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hu : (ρ y).bind (PVal.unbox ty) with
      | none => simp [hu] at hwp
      | some r =>
        simp only [hu, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x r) Q X hJ hwp out hev
    | isShared y =>
      dsimp only [PVal.wp] at hwp
      dsimp only [PEvalVal] at hev
      cases hy : ρ y with
      | none => simp [hy] at hwp
      | some _ =>
        simp only [hy, Option.map_some] at hwp hev
        exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x (PVal.bool shared)) Q X hJ
          (hwp.2 shared) out hev
  | .jp j ps body kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    dsimp only [PWp] at hwp
    let Jj : List PVal → Prop := fun vs =>
      vs.length = ps.length ∧
      ∀ f ≤ k, ∀ out',
        PEvalCode f m shared ((j, ps, body, ρ) :: jps) (ρ.bindAll ps vs) body = some out' →
        OutcomeOk Q X out'
    have hJ' : JPEvalOk m shared Q X (J.set j Jj) ((j, ps, body, ρ) :: jps) k := by
      intro j' vs ps' body' ρ0' outer hmem hdw hlen f hf out' hev'
      by_cases heq : j' = j
      · subst heq
        simp only [List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.cons.injEq, Prod.mk.injEq] at hdw
        rcases hdw with ⟨⟨_, rfl, rfl, rfl⟩, rfl⟩
        simp only [PJEnv.set, ↓reduceIte] at hmem
        exact hmem.2 f hf out' hev'
      · have hne : (j, ps, body, ρ).1 ≠ j' := fun h => heq h.symm
        rw [dropWhile_ne_cons (·.1) (j, ps, body, ρ) hne jps] at hdw
        simp only [PJEnv.set] at hmem
        rw [ite_eq_right heq] at hmem
        exact hJ j' vs ps' body' ρ0' outer hmem hdw hlen f hf out' hev'
    have hcl : ∀ as, as.length = ps.length →
        PWp (modArityOf m) Δ (J.set j Jj) (ρ.bindAll ps as) Q X body → Jj as := by
      intro as has hbody
      refine ⟨has, fun f hf out' hev' => ?_⟩
      cases f with
      | zero => simp [PEvalCode] at hev'
      | succ f' =>
        have hlt : f' < k := by omega
        exact ihJmp f' hlt ((j, ps, body, ρ) :: jps) (J.set j Jj) (ρ.bindAll ps as) body Q X
          (JPEvalOk_shrink (by omega) hJ') hbody out' hev'
    exact PWp_sound_go ihCall ihJmp kcode ((j, ps, body, ρ) :: jps) (J.set j Jj) ρ Q X hJ'
      (hwp Jj hcl) out hev
  | .jmp j as, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases hdw : jps.dropWhile (fun e => e.1 != j) with
    | nil => simp [hdw] at hev
    | cons hd outer =>
      rcases hd with ⟨j1, ps, body, ρ0⟩
      cases has : ρ.evalArgs as with
      | none => simp [has] at hwp
      | some vs =>
        simp only [has] at hwp
        simp only [hdw, has] at hev
        have hj1 : j1 = j := dropWhile_head_fst (·.1) j jps hdw
        subst hj1
        by_cases hlen : (vs.length == ps.length) = true
        · rw [ite_eq_left hlen] at hev
          exact hJ j1 vs ps body ρ0 outer hwp hdw (beq_iff_eq.mp hlen) k (Nat.le_refl k) out hev
        · rw [ite_eq_right hlen] at hev; simp at hev
  | .cases x alts, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases ht : (ρ x).bind PVal.tag? with
    | none => simp [ht] at hwp
    | some tag =>
      simp only [ht] at hwp hev
      exact PWpCtorAlts_sound_go ihCall ihJmp tag alts jps J ρ Q X hJ
        (PWpDfltAlts_sound_go ihCall ihJmp alts jps J ρ Q X hJ) hwp out hev
  | .ret a, _, _, ρ, _, _, _, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases ha : ρ.evalArg a with
    | none => simp [ha] at hwp
    | some v => simp only [ha, Option.map_some] at hwp hev; cases hev; exact hwp
  | .unreach, _, _, _, _, _, _, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev; cases hev; exact hwp
  | .oset x i y kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at hwp hev
    rename_i xv yv
    cases hs : xv.setObj i yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp hev
      exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x xv') Q X hJ hwp out hev
  | .uset x i y kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hwp hev
    rename_i xv yv
    cases hs : xv.setUsize i yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp hev
      exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x xv') Q X hJ hwp out hev
  | .sset x n off y ty kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hwp hev
    rename_i xv yv
    cases hs : xv.setScalar n off ty yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp hev
      exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x xv') Q X hJ hwp out hev
  | .setTag x cidx kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp] at hwp
    cases hs : (ρ x).bind (·.setTag cidx) with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp hev
      exact PWp_sound_go ihCall ihJmp kcode jps J (ρ.set x xv') Q X hJ hwp out hev
  | .inc _ _ _ kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev =>
    PWp_sound_go ihCall ihJmp kcode jps J ρ Q X hJ hwp out hev
  | .dec _ _ _ kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev =>
    PWp_sound_go ihCall ihJmp kcode jps J ρ Q X hJ hwp out hev
  | .del _ kcode, jps, J, ρ, Q, X, hJ, hwp, out, hev =>
    PWp_sound_go ihCall ihJmp kcode jps J ρ Q X hJ hwp out hev

private theorem PWpCtorAlts_sound_go {m : LcModule} {shared : Bool} {Δ : PEnv} {k : Nat}
    (ihCall : ∀ fn args P E, Δ fn args P E → ∀ out,
      PEvalCallAt m shared k fn args = some out → OutcomeOk P E out)
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      JPEvalOk m shared Q X J jps f → PWp (modArityOf m) Δ J ρ Q X c →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out)
    (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost) {kDW : Prop} {kDE : Option POutcome},
      JPEvalOk m shared Q X J jps k →
      (kDW → ∀ out, kDE = some out → OutcomeOk Q X out) →
      PWpCtorAlts (modArityOf m) Δ J ρ Q X tag alts kDW →
      ∀ out, PEvalCtorAlts m shared (PEvalCallAt m shared k) (PEvalCode k m shared)
        jps ρ tag alts kDE = some out → OutcomeOk Q X out
  | [], _, _, _, _, _, _, _, _, hd, hwp, out, hev => hd hwp out hev
  | (.ctor ci _, b) :: rest, jps, J, ρ, Q, X, _, _, hJ, hd, hwp, out, hev => by
    dsimp only [PWpCtorAlts] at hwp
    dsimp only [PEvalCtorAlts] at hev
    by_cases hci : ci = tag
    · rw [ite_eq_left hci] at hwp
      rw [ite_eq_left (beq_iff_eq.mpr hci)] at hev
      exact PWp_sound_go ihCall ihJmp b jps J ρ Q X hJ hwp out hev
    · rw [ite_eq_right hci] at hwp
      rw [ite_eq_right (mt beq_iff_eq.mp hci)] at hev
      exact PWpCtorAlts_sound_go ihCall ihJmp tag rest jps J ρ Q X hJ hd hwp out hev
  | (.dflt, _) :: rest, jps, J, ρ, Q, X, _, _, hJ, hd, hwp, out, hev =>
    PWpCtorAlts_sound_go ihCall ihJmp tag rest jps J ρ Q X hJ hd hwp out hev

private theorem PWpDfltAlts_sound_go {m : LcModule} {shared : Bool} {Δ : PEnv} {k : Nat}
    (ihCall : ∀ fn args P E, Δ fn args P E → ∀ out,
      PEvalCallAt m shared k fn args = some out → OutcomeOk P E out)
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      JPEvalOk m shared Q X J jps f → PWp (modArityOf m) Δ J ρ Q X c →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost),
      JPEvalOk m shared Q X J jps k →
      PWpDfltAlts (modArityOf m) Δ J ρ Q X alts →
      ∀ out, PEvalDfltAlts m shared (PEvalCallAt m shared k) (PEvalCode k m shared)
        jps ρ alts = some out → OutcomeOk Q X out
  | [], _, _, _, _, _, _, hwp, _, _ => False.elim hwp
  | (.dflt, b) :: _, jps, J, ρ, Q, X, hJ, hwp, out, hev =>
    PWp_sound_go ihCall ihJmp b jps J ρ Q X hJ hwp out hev
  | (.ctor _ _, _) :: rest, jps, J, ρ, Q, X, hJ, hwp, out, hev =>
    PWpDfltAlts_sound_go ihCall ihJmp rest jps J ρ Q X hJ hwp out hev
end

private theorem PWp_sound_PEvalCode_of_modOk {m : LcModule} {Δ : PEnv} (hm : PModuleOk Δ m)
    {shared : Bool} :
    ∀ k jps J ρ c Q X,
      JPEvalOk m shared Q X J jps k →
      PWp (modArityOf m) Δ J ρ Q X c →
      ∀ out, PEvalCode (k + 1) m shared jps ρ c = some out → OutcomeOk Q X out := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro jps J ρ c Q X hJ hwp out hev
    refine PWp_sound_go (fun fn args P E hd out' hcall => ?_)
      (fun f hf jps' J' ρ' c' Q' X' hJ' hwp' out' hev' =>
        ih f hf jps' J' ρ' c' Q' X' hJ' hwp' out' hev')
      c jps J ρ Q X hJ hwp out hev
    dsimp only [PEvalCallAt] at hcall
    cases hfd : m.decls.find? (·.name == fn) with
    | none => simp [hfd] at hcall
    | some d =>
      simp only [hfd] at hcall
      by_cases hlen : (args.length == d.params.length) = true
      · rw [ite_eq_left hlen] at hcall
        cases k with
        | zero => simp [PEvalCode] at hcall
        | succ k' =>
          have hmem := find_eq_some_mem hfd
          have hnm : d.name = fn :=
            beq_iff_eq.mp (find_eq_some_pred (p := fun (d : LcDecl) => d.name == fn) hfd)
          subst hnm
          exact ih k' (by omega) [] PJEnv.empty (PValEnv.empty.bindAll d.params args) d.body P E
            (fun _ _ _ _ _ _ hbot => False.elim hbot)
            (hm d hmem args P E (beq_iff_eq.mp hlen) hd) out' hcall
      · rw [ite_eq_right hlen] at hcall; simp at hcall

/-- Soundness of `PModuleOk` against `PEval`: any normal return or panic produced by `PEval`
satisfies the contract `(Q, X)`. Works for all `LcModule`s including `.isShared`. -/
theorem PWp_sound_PEval {m : LcModule} {Δ : PEnv} (hm : PModuleOk Δ m)
    {fuel : Nat} {fn : String} {args : List PVal} {Q : PPost} {X : PXPost}
    {shared : Bool} {out : POutcome}
    (hspec : Δ fn args Q X) (hev : PEval fuel m fn args shared = some out) :
    OutcomeOk Q X out := by
  dsimp only [PEval] at hev
  cases hfd : m.decls.find? (·.name == fn) with
  | none => simp [hfd] at hev
  | some d =>
    simp only [hfd] at hev
    by_cases hlen : (args.length == d.params.length) = true
    · rw [ite_eq_left hlen] at hev
      cases fuel with
      | zero => simp [PEvalCode] at hev
      | succ f =>
        have hmem := find_eq_some_mem hfd
        have hnm : d.name = fn :=
          beq_iff_eq.mp (find_eq_some_pred (p := fun (d : LcDecl) => d.name == fn) hfd)
        subst hnm
        exact PWp_sound_PEvalCode_of_modOk hm f [] PJEnv.empty
          (PValEnv.empty.bindAll d.params args) d.body Q X
          (fun _ _ _ _ _ _ hbot => False.elim hbot)
          (hm d hmem args Q X (beq_iff_eq.mp hlen) hspec) out hev
    · rw [ite_eq_right hlen] at hev; simp at hev

/-- Soundness of measure-indexed `PModuleOkIdx` against `PEval`. -/
theorem PWp_sound_PEval_idx {m : LcModule} {Δ : Nat → PEnv} (hm : PModuleOkIdx Δ m) :
    ∀ (depth : Nat) {fuel : Nat} {fn : String} {args : List PVal} {Q : PPost} {X : PXPost}
      {shared : Bool} {out : POutcome},
      Δ depth fn args Q X → PEval fuel m fn args shared = some out → OutcomeOk Q X out := by
  intro depth
  induction depth using Nat.strongRecOn with
  | _ depth ihD =>
    let Δcur : PEnv := (fun (n : Nat) => match n with | 0 => PEnv.bot | d' + 1 => Δ d') depth
    have hcode : ∀ (shared : Bool) (k : Nat) jps J ρ c Q X,
        JPEvalOk m shared Q X J jps k →
        PWp (modArityOf m) Δcur J ρ Q X c →
        ∀ out, PEvalCode (k + 1) m shared jps ρ c = some out → OutcomeOk Q X out := by
      intro shared k
      induction k using Nat.strongRecOn with
      | _ k ihK =>
        intro jps J ρ c Q X hJ hwp out hev
        refine PWp_sound_go (Δ := Δcur) (fun fn args P E hd out' hcall => ?_)
          (fun f hf jps' J' ρ' c' Q' X' hJ' hwp' out' hev' =>
            ihK f hf jps' J' ρ' c' Q' X' hJ' hwp' out' hev')
          c jps J ρ Q X hJ hwp out hev
        cases depth with
        | zero => exact False.elim hd
        | succ d' =>
          rw [PEvalCallAt_eq_PEval] at hcall
          exact ihD d' (by omega) hd hcall
    intro fuel fn args Q X shared out hspec hev
    dsimp only [PEval] at hev
    cases hfd : m.decls.find? (·.name == fn) with
    | none => simp [hfd] at hev
    | some d =>
      simp only [hfd] at hev
      by_cases hlen : (args.length == d.params.length) = true
      · rw [ite_eq_left hlen] at hev
        cases fuel with
        | zero => simp [PEvalCode] at hev
        | succ f =>
          have hmem := find_eq_some_mem hfd
          have hnm : d.name = fn :=
            beq_iff_eq.mp (find_eq_some_pred (p := fun (d : LcDecl) => d.name == fn) hfd)
          subst hnm
          exact hcode shared f [] PJEnv.empty (PValEnv.empty.bindAll d.params args) d.body Q X
            (fun _ _ _ _ _ _ hbot => False.elim hbot)
            (hm.2 depth d hmem args Q X (beq_iff_eq.mp hlen) hspec) out hev
      · rw [ite_eq_right hlen] at hev; simp at hev

end LeanQbe.T.LeanLCNF.Sem
