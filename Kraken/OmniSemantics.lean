import Std

/-!
Architecture-independent proof infrastructure for effectful execution.

Architecture modules provide a one-step transition relation; `Eventually`
composes it into finite executions and supplies reusable sequencing and loop
lemmas.
-/

abbrev Post {State : Type} := State → Prop

/-- A finite sequence of `trans` steps eventually establishes `post`. -/
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial : State) :
      post initial →
      Eventually trans post initial
  | step (initial : State) :
      (mid_p : Post) →
      trans initial mid_p →
      (∀ mid : State, mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post)
    (initial : State) :
    trans initial (fun mid => Eventually trans post mid) →
      Eventually trans post initial := by
  intro h
  exact .step initial _ h (fun _ => id)

theorem eventually_trans {State : Type} (trans : State → Post → Prop)
    (p q : Post) (initial : State)
    (e : Eventually trans p initial)
    (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial := by
  induction e with
  | done initial hp => exact h initial hp
  | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop)
    (p q : Post) (initial : State)
    (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial := by
  exact fun hp => eventually_trans trans p q initial hp fun s hs =>
    .done s (h s hs)

/-- Iterate an invariant indexed by a natural number down to zero. -/
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop)
    (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
    invariant n initial ∧
      (∀ state, invariant 0 state → Eventually trans post state) ∧
      (∀ state k, k ≠ 0 → invariant k state →
        Eventually trans (invariant (k - 1)) state) →
    Eventually trans post initial := by
  rintro ⟨hinv, hzero, hnz⟩
  if h : n = 0 then
    exact hzero initial (h ▸ hinv)
  else
    exact eventually_trans trans (invariant (n - 1)) post initial
      (hnz initial n h hinv) fun s hs =>
        reg_dec_loop trans post s invariant (n - 1) ⟨hs, hzero, hnz⟩
