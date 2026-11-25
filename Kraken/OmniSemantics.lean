module

public section

/-
Common Kraken Temporal Logic and OmniSemantics.
-/

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)

-- Tailrec-style loop rule
theorem tailrec_loop {State : Type} {Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  P v0 g0 initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → post state) →
  Eventually trans post initial := by
  intro hP hbody hpost
  induction v0 using Hwf.induction generalizing g0 initial with
  | h v ih =>
    refine eventually_trans trans _ post initial (hbody v g0 initial hP) ?_
    rintro mid_s (hQ | ⟨v', g', hP', hlt, hQ'⟩)
    · exact .done mid_s (hpost mid_s hQ)
    · exact ih v' hlt mid_s g' hP' (fun t h => hpost t (hQ' t h))
