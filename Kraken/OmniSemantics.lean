/-
Kraken - Proof Tactics

Core tactics and theorems for stepping through assembly proofs.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For advanced tactics (SymM), see kraken-experimental/KrakenExp/Tactics.lean.
-/

import Kraken.Semantics

-- PROOF INFRASTRUCTURE

abbrev Post {State : Type} := State → Prop

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

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
  fun h => Eventually.step initial _ h (fun _ h => h)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step_hyp rest_hyp ind_h =>
        apply Eventually.step
        <;> assumption

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    intro hp
    induction ih: hp  -- Q: why does this not work with `induction ... with`?
    . apply Eventually.done
      grind
    . apply Eventually.step
      <;> try assumption
      grind

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (∀ state, invariant 0 state → Eventually trans post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (∀ state k, k ≠ 0 → invariant k state → Eventually trans (invariant (k - 1)) state) →
  -- then: we can prove the post
  Eventually trans post initial
  := by
    intro misc
    rcases misc with ⟨ initial_invariant, case_zero, case_nonzero ⟩
    if n = 0 then
      apply case_zero
      grind
    else
      apply eventually_trans trans (invariant (n - 1)) post
      grind
      intros srec _
      apply reg_dec_loop trans post srec invariant (n - 1)
      grind

def step1 [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step p s .done).All post

def straightlineStep [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline p s .done).All post
