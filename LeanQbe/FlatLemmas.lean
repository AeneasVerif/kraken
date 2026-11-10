module

public import LeanQbe.Flat
public import LeanQbe.Wf
public meta import Lean.Elab.Tactic

/-!
# Every denotation is well-formed; `wf_reify`

`denote_wf`: for every `flat` and any two instantiations, `denote` gives `Wf`-related terms (the
contexts are zipped). With the reification equation `f = fun V L => denote V L (toFlat (f Nat Nat) 0 0) …`,
checked by the kernel (`kernel_rfl`), this proves `Func.Wf f` for a concrete `f` (`wf_reify`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Both `none`, or both `some` and related. -/
def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

section
variable {V₁ V₂ : Type} (vs₁ : List V₁) (vs₂ : List V₂) (n : Nat)

theorem lookup_rel (h₁ : vs₁.length = n) (h₂ : vs₂.length = n) (i : Nat) :
    ORel (fun a b => (a, b) ∈ vs₁.zip vs₂) (lookup vs₁ n i) (lookup vs₂ n i) := by
  unfold lookup
  split
  · have hj₁ : n - 1 - i < vs₁.length := by omega
    have hj₂ : n - 1 - i < vs₂.length := by omega
    rw [List.getElem?_eq_getElem hj₁, List.getElem?_eq_getElem hj₂]
    simp only [ORel]
    refine List.mem_iff_getElem.2 ⟨n - 1 - i, by simp [List.length_zip]; omega, ?_⟩
    simp [List.getElem_zip]
  · trivial

theorem denoteArg_rel (h₁ : vs₁.length = n) (h₂ : vs₂.length = n) (a : Arg Nat) :
    ORel (ArgRel (vs₁.zip vs₂)) (denoteArg vs₁ n a) (denoteArg vs₂ n a) := by
  cases a with
  | var i =>
    have hr := lookup_rel vs₁ vs₂ n h₁ h₂ i
    simp only [denoteArg]
    cases e₁ : lookup vs₁ n i <;> cases e₂ : lookup vs₂ n i <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    exact .var hr
  | imm c => exact .imm c

theorem denoteArgs_rel (h₁ : vs₁.length = n) (h₂ : vs₂.length = n) :
    ∀ as : List (Arg Nat),
      ORel (Forall₂ (ArgRel (vs₁.zip vs₂))) (denoteArgs vs₁ n as) (denoteArgs vs₂ n as)
  | [] => .nil
  | a :: as => by
    have ha := denoteArg_rel vs₁ vs₂ n h₁ h₂ a
    have has := denoteArgs_rel h₁ h₂ as
    simp only [denoteArgs]
    cases e₁ : denoteArg vs₁ n a <;> cases e₂ : denoteArg vs₂ n a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : denoteArgs vs₁ n as <;> cases f₂ : denoteArgs vs₂ n as <;> rw [f₁, f₂] at has <;>
      simp only [ORel] at has ⊢
    exact .cons ha has

theorem denoteOp_rel (h₁ : vs₁.length = n) (h₂ : vs₂.length = n) (op : Op Nat) :
    ORel (OpRel (vs₁.zip vs₂)) (denoteOp vs₁ n op) (denoteOp vs₂ n op) := by
  cases op with
  | bin k o a b =>
    have ha := denoteArg_rel vs₁ vs₂ n h₁ h₂ a
    have hb := denoteArg_rel vs₁ vs₂ n h₁ h₂ b
    simp only [denoteOp]
    cases e₁ : denoteArg vs₁ n a <;> cases e₂ : denoteArg vs₂ n a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : denoteArg vs₁ n b <;> cases f₂ : denoteArg vs₂ n b <;> rw [f₁, f₂] at hb <;>
      simp only [ORel] at hb ⊢
    exact .bin k o ha hb
  | cmp k o a b =>
    have ha := denoteArg_rel vs₁ vs₂ n h₁ h₂ a
    have hb := denoteArg_rel vs₁ vs₂ n h₁ h₂ b
    simp only [denoteOp]
    cases e₁ : denoteArg vs₁ n a <;> cases e₂ : denoteArg vs₂ n a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : denoteArg vs₁ n b <;> cases f₂ : denoteArg vs₂ n b <;> rw [f₁, f₂] at hb <;>
      simp only [ORel] at hb ⊢
    exact .cmp k o ha hb
  | ext k s sg a =>
    have ha := denoteArg_rel vs₁ vs₂ n h₁ h₂ a
    simp only [denoteOp]
    cases e₁ : denoteArg vs₁ n a <;> cases e₂ : denoteArg vs₂ n a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢
    exact .ext k s sg ha
  | copy k a =>
    have ha := denoteArg_rel vs₁ vs₂ n h₁ h₂ a
    simp only [denoteOp]
    cases e₁ : denoteArg vs₁ n a <;> cases e₂ : denoteArg vs₂ n a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢
    exact .copy k ha

end

theorem denote_wf {V₁ V₂ L₁ L₂ : Type} (flat : Flat) :
    ∀ (vs₁ : List V₁) (vs₂ : List V₂) (nv : Nat) (ls₁ : List L₁) (ls₂ : List L₂) (nl : Nat),
      vs₁.length = nv → vs₂.length = nv → ls₁.length = nl → ls₂.length = nl →
      Wf (vs₁.zip vs₂) (ls₁.zip ls₂) (denote V₁ L₁ flat vs₁ nv ls₁ nl) (denote V₂ L₂ flat vs₂ nv ls₂ nl) := by
  induction flat with
  | let_ op k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hr := denoteOp_rel vs₁ vs₂ nv h₁ h₂ op
    simp only [denote]
    cases e₁ : denoteOp vs₁ nv op <;> cases e₂ : denoteOp vs₂ nv op <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .let_ hr fun v₁ v₂ => ih (v₁ :: vs₁) (v₂ :: vs₂) (nv + 1) ls₁ ls₂ nl
        (by simp [h₁]) (by simp [h₂]) h₃ h₄
  | load c s sg a k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hr := denoteArg_rel vs₁ vs₂ nv h₁ h₂ a
    simp only [denote]
    cases e₁ : denoteArg vs₁ nv a <;> cases e₂ : denoteArg vs₂ nv a <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .load c s sg hr fun v₁ v₂ => ih (v₁ :: vs₁) (v₂ :: vs₂) (nv + 1) ls₁ ls₂ nl
        (by simp [h₁]) (by simp [h₂]) h₃ h₄
  | store s v a k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hv := denoteArg_rel vs₁ vs₂ nv h₁ h₂ v
    have ha := denoteArg_rel vs₁ vs₂ nv h₁ h₂ a
    simp only [denote]
    cases e₁ : denoteArg vs₁ nv v <;> cases e₂ : denoteArg vs₂ nv v <;> rw [e₁, e₂] at hv <;>
      simp only [ORel] at hv ⊢ <;>
      cases f₁ : denoteArg vs₁ nv a <;> cases f₂ : denoteArg vs₂ nv a <;> rw [f₁, f₂] at ha <;>
      simp only [ORel] at ha ⊢ <;> first | exact .hlt | exact .store s hv ha (ih vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄)
  | call f as k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hr := denoteArgs_rel vs₁ vs₂ nv h₁ h₂ as
    simp only [denote]
    cases e₁ : denoteArgs vs₁ nv as <;> cases e₂ : denoteArgs vs₂ nv as <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .call f hr (ih vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄)
  | jnz c t e iht ihe =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hr := denoteArg_rel vs₁ vs₂ nv h₁ h₂ c
    simp only [denote]
    cases e₁ : denoteArg vs₁ nv c <;> cases e₂ : denoteArg vs₂ nv c <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .jnz hr (iht vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄) (ihe vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄)
  | jump j as =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    have hj := lookup_rel ls₁ ls₂ nl h₃ h₄ j
    have hr := denoteArgs_rel vs₁ vs₂ nv h₁ h₂ as
    simp only [denote]
    cases e₁ : lookup ls₁ nl j <;> cases e₂ : lookup ls₂ nl j <;> rw [e₁, e₂] at hj <;>
      simp only [ORel] at hj ⊢ <;>
      cases f₁ : denoteArgs vs₁ nv as <;> cases f₂ : denoteArgs vs₂ nv as <;> rw [f₁, f₂] at hr <;>
      simp only [ORel] at hr ⊢ <;> first | exact .hlt | exact .jump hj hr
  | ret rs =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ _ _
    have hr := denoteArgs_rel vs₁ vs₂ nv h₁ h₂ rs
    simp only [denote]
    cases e₁ : denoteArgs vs₁ nv rs <;> cases e₂ : denoteArgs vs₂ nv rs <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .ret hr
  | exit f as =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ _ _
    have hr := denoteArgs_rel vs₁ vs₂ nv h₁ h₂ as
    simp only [denote]
    cases e₁ : denoteArgs vs₁ nv as <;> cases e₂ : denoteArgs vs₂ nv as <;> rw [e₁, e₂] at hr <;>
      simp only [ORel] at hr ⊢
    · exact .hlt
    · exact .exit f hr
  | hlt => intro _ _ _ _ _ _ _ _ _ _; exact .hlt
  | param k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    exact .param fun v₁ v₂ => ih (v₁ :: vs₁) (v₂ :: vs₂) (nv + 1) ls₁ ls₂ nl
      (by simp [h₁]) (by simp [h₂]) h₃ h₄
  | label k ih =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    exact .label fun j₁ j₂ => ih vs₁ vs₂ nv (j₁ :: ls₁) (j₂ :: ls₂) (nl + 1) h₁ h₂
      (by simp [h₃]) (by simp [h₄])
  | block b r ihb ihr =>
    intro vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄
    exact .block (ihb vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄) (ihr vs₁ vs₂ nv ls₁ ls₂ nl h₁ h₂ h₃ h₄)

/-- A function equal to the denotation of its own first-order image is well-formed. -/
theorem Func.wf_of_reify {f : Func}
    (h : f = fun V L => denote V L (toFlat (f Nat Nat) 0 0) [] 0 [] 0) : f.Wf := by
  intro V₁ V₂ L₁ L₂
  have h₁ : f V₁ L₁ = denote V₁ L₁ (toFlat (f Nat Nat) 0 0) [] 0 [] 0 := congrFun (congrFun h V₁) L₁
  have h₂ : f V₂ L₂ = denote V₂ L₂ (toFlat (f Nat Nat) 0 0) [] 0 [] 0 := congrFun (congrFun h V₂) L₂
  rw [h₁, h₂]
  exact denote_wf _ [] [] 0 [] [] 0 rfl rfl rfl rfl

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` with `Eq.refl lhs`, checked by the kernel only (Spike A). The elaborator's
`isDefEq` is skipped: it is several times slower on large PHOAS terms and gives up on some. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

/-- Proves `Func.Wf f` for a concrete `f` by reification: the kernel checks
`f = fun V L => denote V L (toFlat (f Nat Nat) 0 0) [] 0 [] 0`, and `denote_wf` does the rest.
Linear in the size of `f` (where `wf_tac` is quadratic). -/
macro "wf_reify" : tactic => `(tactic| (refine Func.wf_of_reify ?_; kernel_rfl))

end LeanQbe
