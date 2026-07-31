/-
Kraken - AArch64 Proof Tactics and OmniSemantics

Core tactics and theorems for stepping through AArch64 assembly proofs.
Compatible with Lean 4.22.0+.
-/

import Kraken.AArch64.Semantics

-- PROOF INFRASTRUCTURE FOR AArch64

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
    intro
    apply Eventually.step
    <;> try assumption
    grind

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
    induction ih: hp
    . apply Eventually.done
      grind
    . apply Eventually.step
      <;> try assumption
      grind

def step1 [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step p s .done).All post

def straightlineStep [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline p s .done).All post

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress,Executable.withAddresses,Layout.apply]
