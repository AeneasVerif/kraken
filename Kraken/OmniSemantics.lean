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

-- Loop body postcondition for `tailrec_loop`: either exit the loop (`break`),
-- or re-enter (`loop`) with a strictly smaller ghost state and an exit-postcondition update.
inductive LoopPost {State : Type} {Ghost : Sort _}
    (onLoop onExit : Ghost → Post)
    (lt : Ghost → Ghost → Prop) (g : Ghost) (mid_s : State) : Prop where
  | break (exit : onExit g mid_s)
  | loop (g' : Ghost) (inv : onLoop g' mid_s)
      (dec : lt g' g) (upd : ∀ t_s, onExit g' t_s → onExit g t_s)

-- Tailrec-style loop rule
theorem tailrec_loop {State : Type} {Ghost : Sort _}
    {trans : State → Post → Prop} {post : Post} {initial : State}
    (onLoop onExit : Ghost → Post)
    (lt : Ghost → Ghost → Prop)
    (Hwf : WellFounded lt)
    (g0 : Ghost) :
    onLoop g0 initial →
    (∀ g state, onLoop g state →
      Eventually trans (LoopPost onLoop onExit lt g) state) →
    (∀ state, onExit g0 state → post state) →
    Eventually trans post initial := by
  intro hP hbody hpost
  induction g0 using Hwf.induction generalizing initial with
  | h g ih =>
    refine eventually_trans trans _ post initial (hbody g initial hP) ?_
    rintro mid_s (⟨hQ⟩ | ⟨g', hP', hlt, hQ'⟩)
    · exact .done mid_s (hpost mid_s hQ)
    · exact ih g' hlt hP' (fun t h => hpost t (hQ' t h))
