/-
Kraken - Proof Tactics

Core tactics and theorems for stepping through assembly proofs.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For advanced tactics (SymM), see kraken-experimental/KrakenExp/Tactics.lean.
-/

import Kraken.X64.Semantics

-- PROOF INFRASTRUCTURE

abbrev Post {State : Type} := State → Prop

def Effects.All (post : MachineState → Prop) : Effects → Prop
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
    rintro ⟨hinv, hzero, hnz⟩
    if h : n = 0 then
      exact hzero initial (h ▸ hinv)
    else
      exact eventually_trans trans (invariant (n - 1)) post initial
        (hnz initial n h hinv) fun s hs =>
          reg_dec_loop trans post s invariant (n - 1) ⟨hs, hzero, hnz⟩

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

theorem directivesAtFromPrefix (e: Executable) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest
:= by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a)).map (·.2), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem eventually_step [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState):
    step1 e s (fun s => straightlineStep e s post) → straightlineStep e s post := by
  sorry
