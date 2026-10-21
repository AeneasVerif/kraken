module

public import Kraken.OmniSemantics

/--
The weakest precondition of a while loop as a least fixpoint.
Introduction forms are `While.stop` and `While.step`.
It is equivalent to `Eventually` with a stop condition, cf. `While.iff_eventually`.
-/
public def While {σ : Type} (cond : σ → Prop) (body : (σ → Prop) → σ → Prop) (done : σ → Prop) (x : σ) :
    Prop :=
  (cond x ∧ ∃ «continue», body «continue» x ∧ ∀ y, «continue» y → While cond body done y) ∨ (¬ cond x ∧ done x)
inductive_fixpoint

section
variable {σ : Type} {cond : σ → Prop} {body : (σ → Prop) → σ → Prop} {done : σ → Prop}

public theorem While.stop {x : σ} (hc : ¬ cond x) (hd : done x) : While cond body done x := by
  rw [While]; exact .inr ⟨hc, hd⟩

public theorem While.step {x : σ} {«continue» : σ → Prop} (hc : cond x) (hb : body «continue» x)
    (h : ∀ y, «continue» y → While cond body done y) : While cond body done x := by
  rw [While]; exact .inl ⟨hc, _, hb, h⟩

public theorem While.iff_eventually {x : σ} :
    While cond body done x ↔
      Eventually (fun st «continue» => cond st ∧ body «continue» st) (fun st => ¬ cond st ∧ done st) x := by
  constructor
  · intro h
    refine While.induct cond body done _ (fun y hy => ?_) x h
    rcases hy with ⟨hc, U, hb, hU⟩ | hd
    · exact .step y U ⟨hc, hb⟩ hU
    · exact .done y hd
  · intro h
    induction h with
    | done y hd => exact While.stop hd.1 hd.2
    | step y U ht _ ih => exact While.step ht.1 ht.2 ih

public theorem While.mono {body₂ : (σ → Prop) → σ → Prop} {done₂ : σ → Prop}
    (hb : ∀ U y, cond y → body U y → body₂ U y) (hd : ∀ y, ¬ cond y → done y → done₂ y) {x : σ}
    (h : While cond body done x) : While cond body₂ done₂ x := by
  refine While.induct cond body done _ (fun y hy => ?_) x h
  rcases hy with ⟨hc, U, hbU, hU⟩ | ⟨hc, hdy⟩
  · exact While.step hc (hb U y hc hbU) hU
  · exact While.stop hc (hd y hc hdy)

/--
Splits `while cond₂ do body` at the first state where a stronger condition `cond` fails:
`while cond do body; while cond₂ do body ⊑ while cond₂ do body`.
-/
public theorem While.split {cond₂ : σ → Prop} (I : σ → Prop) (hcond : ∀ y, I y → cond y → cond₂ y)
    (hI : ∀ U y, I y → cond y → body U y → body (fun z => U z ∧ I z) y) {x : σ} (hx : I x)
    (h : While cond body (While cond₂ body done) x) : While cond₂ body done x := by
  refine While.induct cond body (While cond₂ body done) (fun y => I y → While cond₂ body done y)
    (fun y hy hIy => ?_) x h hx
  rcases hy with ⟨hc, U, hb, hU⟩ | ⟨-, hd⟩
  · exact While.step (hcond y hIy hc) (hI U y hIy hc hb) fun z hz => hU z hz.1 hz.2
  · exact hd

public theorem While.and {body₁ body₂ : (σ → Prop) → σ → Prop} {done₁ done₂ : σ → Prop}
    (hb : ∀ U V y, cond y → body₁ U y → body₂ V y → body (fun z => U z ∧ V z) y) {x : σ}
    (h₁ : While cond body₁ done₁ x) (h₂ : While cond body₂ done₂ x) :
    While cond body (fun z => done₁ z ∧ done₂ z) x := by
  refine While.induct cond body₁ done₁
    (fun y => While cond body₂ done₂ y → While cond body (fun z => done₁ z ∧ done₂ z) y)
    (fun y hy h₂ => ?_) x h₁ h₂
  rw [While] at h₂
  rcases hy with ⟨hc, U, hb₁, hU⟩ | ⟨hc, hd₁⟩ <;> rcases h₂ with ⟨hc₂, V, hb₂, hV⟩ | ⟨hc₂, hd₂⟩
  · exact While.step hc (hb U V y hc hb₁ hb₂) fun z hz => hU z hz.1 (hV z hz.2)
  · exact absurd hc hc₂
  · exact absurd hc₂ hc
  · exact While.stop hc ⟨hd₁, hd₂⟩

open Lean.Order in
@[partial_fixpoint_monotone] public theorem While.monotone {α : Type} [PartialOrder α] {init : σ}
    (f : α → (σ → Prop) → σ → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => While cond (f x) done init) := by
  intro x y hxy hx
  refine While.induct cond (f x) done _ (fun st hst => ?_) init hx
  rcases hst with ⟨hc, U, hb, hU⟩ | ⟨hc, hd⟩
  · exact While.step hc (hf _ _ hxy U st hb) hU
  · exact While.stop hc hd

end
