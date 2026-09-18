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

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro h
    exact .step initial _ h (fun _ => id)

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
-- Adapted from: https://github.com/mit-plv/bedrock2/blob/8ec2c459bbf16d6cf2baa7d433ae211a243b1011/bedrock2/src/bedrock2/Loops.v#L48
-- This version moves the choice inside the Eventually postcondition.
theorem tailrec_loop {State Measure Ghost : Type}
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
  have h_general : ∀ v g state, P v g state → (∀ t_s, Q v g t_s → Q v0 g0 t_s) → Eventually trans post state := by
    intro v
    induction v using Hwf.induction with
    | h v ih =>
      intro g state hP_state hQ_impl
      have hstep := hbody v g state hP_state
      apply eventually_trans trans _ post state hstep
      intro mid_state h_mid
      match h_mid with
      | .inl hQ =>
        apply Eventually.done
        apply hpost
        apply hQ_impl
        apply hQ
      | .inr ⟨v', ⟨g', ⟨hP_mid, hlt, hQ_impl'⟩⟩⟩ =>
        apply ih v' hlt g' mid_state hP_mid
        intro t_s hQ_t
        apply hQ_impl
        apply hQ_impl'
        apply hQ_t
  apply h_general v0 g0 initial hP
  intro t_s hQ_t
  apply hQ_t

