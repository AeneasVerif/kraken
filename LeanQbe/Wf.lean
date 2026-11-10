module

public import LeanQbe.IL

/-!
# Well-formedness: relatedness of two instantiations (Chlipala)

`Wf G D e₁ e₂` says that `e₁ : Expr V₁ L₁` and `e₂ : Expr V₂ L₂` are the same term, read at two
instantiations, where `G` pairs the variables and `D` the labels bound so far (newest first). A closed
function is well-formed when every two instantiations are related with empty contexts (`Func.Wf`).

This is the interface between passes (decision D7): a pass consumes one instantiation while reading a
second one at another type, and its correctness proof inducts on `Wf`.

For a concrete program, `wf_tac` proves `Func.Wf` (every constructor is syntax-directed).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b as bs} : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

section
variable {V₁ V₂ : Type}

inductive ArgRel (G : List (V₁ × V₂)) : Arg V₁ → Arg V₂ → Prop
  | var {a₁ a₂} : (a₁, a₂) ∈ G → ArgRel G (.var a₁) (.var a₂)
  | imm (c : Val) : ArgRel G (.imm c) (.imm c)

inductive OpRel (G : List (V₁ × V₂)) : Op V₁ → Op V₂ → Prop
  | bin (k : Cls) (o : BinOp) {a₁ b₁ a₂ b₂} : ArgRel G a₁ a₂ → ArgRel G b₁ b₂ →
      OpRel G (.bin k o a₁ b₁) (.bin k o a₂ b₂)
  | cmp (k : Cls) (o : CmpOp) {a₁ b₁ a₂ b₂} : ArgRel G a₁ a₂ → ArgRel G b₁ b₂ →
      OpRel G (.cmp k o a₁ b₁) (.cmp k o a₂ b₂)
  | ext (k : Cls) (s : Sz) (sg : Bool) {a₁ a₂} : ArgRel G a₁ a₂ →
      OpRel G (.ext k s sg a₁) (.ext k s sg a₂)
  | copy (k : Cls) {a₁ a₂} : ArgRel G a₁ a₂ → OpRel G (.copy k a₁) (.copy k a₂)

end

inductive Wf {V₁ V₂ L₁ L₂ : Type} :
    List (V₁ × V₂) → List (L₁ × L₂) → Expr V₁ L₁ → Expr V₂ L₂ → Prop
  | let_ {G D op₁ op₂ k₁ k₂} : OpRel G op₁ op₂ →
      (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (k₁ v₁) (k₂ v₂)) → Wf G D (.let_ op₁ k₁) (.let_ op₂ k₂)
  | load {G D} (c : Cls) (s : Sz) (sg : Bool) {a₁ a₂ k₁ k₂} : ArgRel G a₁ a₂ →
      (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (k₁ v₁) (k₂ v₂)) →
      Wf G D (.load c s sg a₁ k₁) (.load c s sg a₂ k₂)
  | store {G D} (s : Sz) {v₁ v₂ a₁ a₂ k₁ k₂} : ArgRel G v₁ v₂ → ArgRel G a₁ a₂ → Wf G D k₁ k₂ →
      Wf G D (.store s v₁ a₁ k₁) (.store s v₂ a₂ k₂)
  | call {G D} (f : Sym) {as₁ as₂ k₁ k₂} : Forall₂ (ArgRel G) as₁ as₂ → Wf G D k₁ k₂ →
      Wf G D (.call f as₁ k₁) (.call f as₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} : ArgRel G c₁ c₂ → Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D j₁ j₂ as₁ as₂} : (j₁, j₂) ∈ D → Forall₂ (ArgRel G) as₁ as₂ →
      Wf G D (.jump j₁ as₁) (.jump j₂ as₂)
  | ret {G D vs₁ vs₂} : Forall₂ (ArgRel G) vs₁ vs₂ → Wf G D (.ret vs₁) (.ret vs₂)
  | exit {G D} (f : Sym) {as₁ as₂} : Forall₂ (ArgRel G) as₁ as₂ →
      Wf G D (.exit f as₁) (.exit f as₂)
  | hlt {G D} : Wf G D .hlt .hlt
  | param {G D f₁ f₂} : (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (f₁ v₁) (f₂ v₂)) →
      Wf G D (.param f₁) (.param f₂)
  | label {G D f₁ f₂} : (∀ j₁ j₂, Wf G ((j₁, j₂) :: D) (f₁ j₁) (f₂ j₂)) →
      Wf G D (.label f₁) (.label f₂)
  | block {G D b₁ b₂ r₁ r₂} : Wf G D b₁ b₂ → Wf G D r₁ r₂ →
      Wf G D (.block b₁ r₁) (.block b₂ r₂)

/-- Every two instantiations of a closed function are related. -/
def Func.Wf (f : Func) : Prop :=
  ∀ V₁ V₂ L₁ L₂ : Type, LeanQbe.Wf ([] : List (V₁ × V₂)) ([] : List (L₁ × L₂)) (f V₁ L₁) (f V₂ L₂)

/-- Proves `Wf` / `Func.Wf` goals for a concrete program. Membership goals are found by trying the head
of the context first; since the binders are distinct variables, the first match is the right one. -/
macro "wf_tac" : tactic =>
  `(tactic| ((try intro _ _ _ _); repeat (first | intro _ _ | constructor!)))

end LeanQbe
