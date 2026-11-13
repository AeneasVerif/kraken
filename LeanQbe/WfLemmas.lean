module

public import LeanQbe.Wf

/-!
# Lemmas about `Wf`

Weakening of the contexts; the basic tool for pass proofs that go under binders.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

theorem Forall₂.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as bs}, Forall₂ R as bs → Forall₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (Forall₂.imp h hs)

theorem Forall₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as bs}, Forall₂ R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg (· + 1) (Forall₂.length_eq hs)

section
variable {V₁ V₂ : Type} {G G' : List (V₁ × V₂)}

theorem ArgRel.weaken (hG : ∀ p ∈ G, p ∈ G') {a₁ : Arg V₁} {a₂ : Arg V₂} :
    ArgRel G a₁ a₂ → ArgRel G' a₁ a₂
  | .var h => .var (hG _ h)
  | .imm c => .imm c

theorem OpRel.weaken (hG : ∀ p ∈ G, p ∈ G') {o₁ : Op V₁} {o₂ : Op V₂} :
    OpRel G o₁ o₂ → OpRel G' o₁ o₂
  | .bin k o ha hb => .bin k o (ha.weaken hG) (hb.weaken hG)
  | .cmp k o ha hb => .cmp k o (ha.weaken hG) (hb.weaken hG)
  | .ext k s sg ha => .ext k s sg (ha.weaken hG)
  | .copy k ha => .copy k (ha.weaken hG)

end

private theorem cons_sub {α : Type} {p : α} {G G' : List α} (h : ∀ q ∈ G, q ∈ G') :
    ∀ q ∈ p :: G, q ∈ p :: G' := by
  grind

/-- Weakening: `Wf` is preserved by enlarging both contexts. -/
theorem Wf.weaken {V₁ V₂ L₁ L₂ : Type} {G : List (V₁ × V₂)} {D : List (L₁ × L₂)}
    {e₁ : Expr V₁ L₁} {e₂ : Expr V₂ L₂} (h : Wf G D e₁ e₂) :
    ∀ {G' D'}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') → Wf G' D' e₁ e₂ := by
  induction h with
  | let_ ho _ ih => intro G' D' hG hD; exact .let_ (ho.weaken hG) fun v₁ v₂ => ih v₁ v₂ (cons_sub hG) hD
  | load c s sg ha _ ih =>
    intro G' D' hG hD; exact .load c s sg (ha.weaken hG) fun v₁ v₂ => ih v₁ v₂ (cons_sub hG) hD
  | store s hv ha _ ih => intro G' D' hG hD; exact .store s (hv.weaken hG) (ha.weaken hG) (ih hG hD)
  | call f has _ ih =>
    intro G' D' hG hD; exact .call f (has.imp fun _ _ h => h.weaken hG) (ih hG hD)
  | jnz hc _ _ iht ihe => intro G' D' hG hD; exact .jnz (hc.weaken hG) (iht hG hD) (ihe hG hD)
  | jump hj has => intro G' D' hG hD; exact .jump (hD _ hj) (has.imp fun _ _ h => h.weaken hG)
  | ret has => intro G' D' hG _; exact .ret (has.imp fun _ _ h => h.weaken hG)
  | exit f has => intro G' D' hG _; exact .exit f (has.imp fun _ _ h => h.weaken hG)
  | hlt => intro _ _ _ _; exact .hlt
  | param _ ih => intro G' D' hG hD; exact .param fun v₁ v₂ => ih v₁ v₂ (cons_sub hG) hD
  | label _ ih => intro G' D' hG hD; exact .label fun j₁ j₂ => ih j₁ j₂ hG (cons_sub hD)
  | block _ _ ihb ihr => intro G' D' hG hD; exact .block (ihb hG hD) (ihr hG hD)

end LeanQbe
