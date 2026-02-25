/-
Kraken - Proof Infrastructure

Theorems about the assembly interpreter semantics.
Requires Lean 4.28.0+ for the grind tactic.

For the core semantics, see AsmInterp/Core.lean.
For examples, see AsmInterp/Examples.lean.
-/

import Lean.Meta.Sym.Grind
import AsmInterp.Core

open Lean Meta Sym

theorem step_cps {p : Program} (post: Post) (initial: MachineState):
  step1 p initial (fun mid => eventually p post mid) → eventually p post initial :=
  by
    intro
    apply eventually.step
    <;> try assumption
    grind

theorem eventually_trans (program: Program) (p q: Post) (initial: MachineState)
  (e: eventually program p initial)
  (h: forall s, p s → eventually program q s):
    eventually program q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step pred ind_h =>
        apply eventually.step
        <;> assumption -- Q: why does `grind` not work here?

theorem eventually_weaken (program: Program) (p q: Post)
  (h: forall s, p s → q s):
    eventually program p initial → eventually program q initial
  := by
    intro hp
    induction ih: hp -- Q: why does this not work with `induction ... with`?
    . apply eventually.done
      grind
    . apply eventually.step
      <;> try assumption
      grind

-- A loop down to 0
theorem reg_dec_loop (prog: Program) (post: Post) (initial: MachineState) (invariant: Nat → Post) (n: Nat):
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (forall state, invariant 0 state → eventually prog post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (forall state k, k ≠ 0 → invariant k state → eventually prog (invariant (k - 1)) state) →
  -- then: we can prove the post
  eventually prog post initial
  := by
    intro misc
    rcases misc with ⟨ initial_invariant, case_zero, case_nonzero ⟩
    if n = 0 then
      apply case_zero
      grind
    else
      apply eventually_trans prog (invariant (n - 1)) post
      grind
      intros srec _
      apply reg_dec_loop prog post srec invariant (n - 1)
      grind
