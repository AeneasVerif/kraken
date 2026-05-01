/-
Kraken - Proof Tactics

Core tactics and theorems for stepping through assembly proofs.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For advanced tactics (SymM), see kraken-experimental/KrakenExp/Tactics.lean.
-/

import Kraken.Theorems

-- PROOF INFRASTRUCTURE

abbrev Post := MachineState → Prop

def Effects.all (s : Effects) (post : MachineState → Prop) : Prop :=
  match s with
  | .done a => post a
  | .unimplemented _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).all post
  | .require_read_access _ _ cont => (cont ()).all post
  | .require_write_access _ _ cont => (cont ()).all post
  | .require_exec_access _ cont => (cont ()).all post

instance (T: Type): Undefined T Prop where
  undefined ret := ∀ (v: T), ret v

inductive Eventually {State : Type} (trans : State → (State → Prop) → Prop) (post : State → Prop) : State → Prop
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: State → Prop) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

-- ============================================================================
-- Omnisemantics Proof Rules
-- ============================================================================

theorem step_cps {State : Type} (trans : State → (State → Prop) → Prop) (post : State → Prop) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro
    apply Eventually.step
    <;> try assumption
    grind

theorem eventually_trans {State : Type} (trans : State → (State → Prop) → Prop) (p q : State → Prop) (initial : State)
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

theorem eventually_weaken {State : Type} (trans : State → (State → Prop) → Prop) (p q : State → Prop) (initial : State)
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

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → (State → Prop) → Prop) (post : State → Prop) (initial : State) (invariant : Nat → State → Prop) (n : Nat) :
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

-- ============================================================================
-- Concrete Transition Rules
-- ============================================================================

def step1 [Layout] (p: Executable) (s: MachineState) (post: Post) :=
  Executable.step p s post

def straightline_step [Layout] (p: Executable) (s: MachineState) (post: Post) :=
  Executable.straightline p s post

theorem step_interp_eq [Layout] (p: Executable) (pc: Int64) (s: MachineData) (d: Directive) (sz: Nat) (ds: List (Directive × Nat)) (post: MachineState → Prop):
  p.directivesFromAddress pc = (d, sz) :: ds →
  let _labels : Labels := p.labels;
  (Executable.step p (s, pc) (fun s' => post s') ↔
   d.interp s (.mk pc (pc+.ofNat sz)) (jmp:=fun pc' s' => post (s', pc')) (next := fun s' => post (s', pc+.ofNat sz))) := by
  sorry

theorem straightline_to_eventually [Layout] (p: Executable) (initial: MachineState) (post: Post):
  straightline_step p initial post → Eventually (step1 p) post initial := by
  intro h
  unfold straightline_step at h
  unfold Executable.straightline at h
  let _labels : Labels := p.labels
  have h_gen : ∀ (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64),
    ds = p.directivesFromAddress pc →
    Directives.interp ds s pc (fun pc' s' => post (s', pc')) →
    Eventually (step1 p) post (s, pc) := by
    intro ds
    induction ds with
    | nil =>
        intros s pc h_eq h_nil
        dsimp [Directives.interp] at h_nil
        apply Eventually.done
        exact h_nil
    | cons d_sz ds' ih =>
        intros s pc h_eq h_cons
        dsimp [Directives.interp] at h_cons
        obtain ⟨d, sz⟩ := d_sz
        let mid_p := fun (mid : MachineState) =>
          post mid ∨ Directives.interp ds' mid.1 mid.2 (fun pc' s' => post (s', pc'))
        apply Eventually.step (s, pc) mid_p
        · -- Prove step1 p (s, pc) mid_p
          unfold step1
          -- Use step_interp_eq here to connect Executable.step to h_cons
          sorry
        · -- Prove ∀ mid, mid_p mid → Eventually (step1 p) post mid
          intros mid h_mid
          cases h_mid with
          | inl h_post =>
              apply Eventually.done
              exact h_post
          | inr h_interp =>
              -- Need to show ds' = p.directivesFromAddress mid.2 to use ih
              sorry
  apply h_gen (p.directivesFromAddress initial.2) initial.1 initial.2 (by rfl)
  exact h

theorem eventually_straightline_to_eventually [Layout] (p: Executable) (initial: MachineState) (post: Post)
  (h: Eventually (straightline_step p) post initial):
  Eventually (step1 p) post initial := by
  induction h with
  | done initial h_post =>
      apply Eventually.done
      assumption
  | step initial mid_p h_step h_rest ih =>
      have h_ev := straightline_to_eventually p initial mid_p h_step
      apply eventually_trans (step1 p) mid_p post initial h_ev ih


-- ============================================================================
-- Tactic Macros
-- ============================================================================

-- Example 2: fine-grained tactics to step through the goal without un-necessary
-- steps, and relying only on low-level tactics

-- STEP TACTIC: reduce a match
syntax "step_match" : tactic
macro_rules
  | `(tactic|step_match) =>
  `(tactic|
    -- JP: looks like reducing a match needs both beta and iota?
    -- the match in the goal below does not reduce properly if I remove beta := true
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
  )

-- STEP TACTIC: reduce the lookup of the next instruction
-- TODO: bail if the state's .rip is not a constant
syntax "step_instr" : tactic
macro_rules
  | `(tactic|step_instr) =>
  `(tactic|
    delta step1 eval1 fetch;
    dsimp only [List.findIdx?,List.findIdx,getElem?,List.get?Internal];
    dsimp only [Instr.is_ctrl];
    dsimp only [Bool.false_eq_true, ↓dreduceIte]; -- special simproc for if https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean#L25-L40
    delta next
  )

-- NOTES: why is the right way of doing this? Ideally, we would not ask to
-- simplify anything that is not an internal definition, because it is not
-- modular. Problematic things here include, e.g., List.findIdx? (what if the
-- user uses this very function in their post-condition?).
--
-- Something equivalent to `match goal with` might work. Alternatively, we could
-- have copies of definitions, e.g. `def my_findIdx := normalize List.findIdx?`.
-- TODO: determine how to do that in Lean.
--
-- Furthermore, it would be nice to be able to specify that reducing e.g. a
-- projector should only be done if the left-hand side is not a variable.
syntax "step_one" : tactic
macro_rules
  | `(tactic|step_one) =>
  `(tactic|
    simp [
      step1,Program.straightline,
      Program.position_of_addr,Program.positions,Program.positions',layout,List.filter,Position.Label,
      List.dropWhile,bne,BEq.beq,instBEqDirective.beq,dropInstrs,Program.straightline',Instr.interp,Operation.interp,Operand.interp];
    simp (ground:=True);
    simp [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp];
    simp (ground:=True)
       <;> try decide)
