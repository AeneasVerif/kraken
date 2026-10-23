module

public import Kraken.OmniSemantics

/--
The weakest precondition of a while loop as a least fixpoint.
Introduction forms are `While.stop` and `While.step`.
It is equivalent to `Eventually` with a stop condition, cf. `While.iff_eventually`.
-/
public inductive While {σ : Type} (cond : σ → Prop) (body : (σ → Prop) → σ → Prop) (done : σ → Prop) :
    σ → Prop where
  | stop {x : σ} (hc : ¬ cond x) (hd : done x) : While cond body done x
  | step {x : σ} {«continue» : σ → Prop} (hc : cond x) (hb : body «continue» x)
      (h : ∀ y, «continue» y → While cond body done y) : While cond body done x

section
variable {σ : Type} {cond : σ → Prop} {body : (σ → Prop) → σ → Prop} {done : σ → Prop}

public theorem While.iff_eventually {x : σ} :
    While cond body done x ↔
      Eventually (fun st «continue» => cond st ∧ body «continue» st) (fun st => ¬ cond st ∧ done st) x := by
  constructor
  · intro h
    induction h with
    | stop hc hd => exact .done _ ⟨hc, hd⟩
    | step hc hb _ ih => exact .step _ _ ⟨hc, hb⟩ ih
  · intro h
    induction h with
    | done y hd => exact While.stop hd.1 hd.2
    | step y U ht _ ih => exact While.step ht.1 ht.2 ih

public theorem While.mono {body₂ : (σ → Prop) → σ → Prop} {done₂ : σ → Prop}
    (hb : ∀ U y, cond y → body U y → body₂ U y) (hd : ∀ y, ¬ cond y → done y → done₂ y) {x : σ}
    (h : While cond body done x) : While cond body₂ done₂ x := by
  induction h with
  | stop hc hdy => exact .stop hc (hd _ hc hdy)
  | step hc hbU _ ih => exact .step hc (hb _ _ hc hbU) ih

/--
Splits `while cond₂ do body` at the first state where a stronger condition `cond` fails:
`while cond do body; while cond₂ do body ⊑ while cond₂ do body`.
-/
public theorem While.split {cond₂ : σ → Prop} (I : σ → Prop) (hcond : ∀ y, I y → cond y → cond₂ y)
    (hI : ∀ U y, I y → cond y → body U y → body (fun z => U z ∧ I z) y) {x : σ} (hx : I x)
    (h : While cond body (While cond₂ body done) x) : While cond₂ body done x := by
  induction h with
  | stop _ hd => exact hd
  | step hc hb _ ih => exact .step (hcond _ hx hc) (hI _ _ hx hc hb) fun z hz => ih z hz.1 hz.2

public theorem While.and {body₁ body₂ : (σ → Prop) → σ → Prop} {done₁ done₂ : σ → Prop}
    (hb : ∀ U V y, cond y → body₁ U y → body₂ V y → body (fun z => U z ∧ V z) y) {x : σ}
    (h₁ : While cond body₁ done₁ x) (h₂ : While cond body₂ done₂ x) :
    While cond body (fun z => done₁ z ∧ done₂ z) x := by
  induction h₁ with
  | stop hc hd₁ => cases h₂ with
    | stop _ hd₂ => exact .stop hc ⟨hd₁, hd₂⟩
    | step hc₂ => exact absurd hc₂ hc
  | step hc hb₁ _ ih => cases h₂ with
    | stop hc₂ => exact absurd hc hc₂
    | step _ hb₂ hV => exact .step hc (hb _ _ _ hc hb₁ hb₂) fun z hz => ih z hz.1 (hV z hz.2)

open Lean.Order in
@[partial_fixpoint_monotone] public theorem While.monotone {α : Type} [PartialOrder α] {init : σ}
    (f : α → (σ → Prop) → σ → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => While cond (f x) done init) := by
  intro x y hxy hx
  induction hx with
  | stop hc hd => exact .stop hc hd
  | step hc hb _ ih => exact .step hc (hf _ _ hxy _ _ hb) ih

end
