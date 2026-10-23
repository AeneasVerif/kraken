module

public import Kraken.X64.Natural
public import Kraken.X64.WP.Host

/-! # Weakest precondition of a single debugger step

Imagine a debugger like `gdb`. It comes with 3 sorts of stepping operations:
* step inside: Execute a single instruction and follow its control flow. If it's a call instruction,
  *step inside* the callee.
* step outside: Execute all instructions until a return *steps outside* the current stack frame.
* step over: Step inside. When the instruction was a call, then step outside afterwards. Thus,
  *step over* any single instruction, including call instructions.

The definitions `Executable.StepIn`, `Executable.StepOut` and `Executable.StepOver` in this module
implement a notion of weakest precondition based on this intuition and `Directives.interp` that is
*conjunctive* (cf. `Program.wp_and`).
-/

/--
`Executable.StepIn e next jump st` defines the weakest precondition of the non-inert directive
at `st.pc` in `e`. Fall-through states must satisfy `next`; post-jump states must satisfy `jump`.
A call is regarded as a jump, so this definition *steps into* called functions.

In contrast to the very similar definition `Executable.step1`, this definition distinguishes
fall-through from jumps.
-/
@[expose] public def Executable.StepIn (e : Executable) (next jump : MachineState → Prop) (st₀ : MachineState) : Prop :=
  haveI := e.labels
  ∀ (P : MachineState → Prop) (ret : MachineData → Effects) (jmp : MachineState → Effects),
    (∀ s, next { data := s, pc := e.nextAddr st₀.pc } → (ret s).All P) →
    (∀ st₁, jump st₁ → (jmp st₁).All P) →
      (Directives.interp (e.directivesAtAddress st₀.pc) st₀.data st₀.pc (fun _ s => ret s)
        (fun a s => jmp { data := s, pc := a })).All P

namespace Executable.StepIn
variable {e : Executable} {st : MachineState}

public theorem mono {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h : e.StepIn next₁ jump₁ st)
    (hn : ∀ u, u.pc = e.nextAddr st.pc → next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) :
    e.StepIn next₂ jump₂ st :=
  fun _ _ _ hr hk => h _ _ _ (fun s h => hr s (hn _ rfl h)) (fun u h => hk u (hj u h))

public theorem all [Layout] {next jump post : MachineState → Prop} (h : e.StepIn next jump st)
    (hn : ∀ u, next u → post u) (hj : ∀ u, jump u → post u) : step1 e st post := by
  unfold step1 Executable.step
  change (@Directives.interp e.labels (e.directivesAtAddress st.pc) st.data st.pc
    (fun a s => Effects.done { data := s, pc := a })
    (fun a s => Effects.done { data := s, pc := a })).All post
  rw [@Directives.interp_ret_congr e.labels _ _ _ _
    (fun _ s => Effects.done { data := s, pc := e.nextAddr st.pc }) _ (fun _ => rfl)]
  exact h _ _ _ (fun _ h => hn _ h) (fun _ h => hj _ h)

open Lean.Order in
@[partial_fixpoint_monotone] public theorem monotone {α : Type} [PartialOrder α] {next : MachineState → Prop}
    (f : α → MachineState → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepIn next (f x) st) :=
  fun _ _ hxy hx => hx.mono (fun _ _ h => h) fun u => hf _ _ hxy u

end Executable.StepIn

/-- The stack pointer of `s₁` lies below that of the reference state `s₀`. -/
@[expose] public def MachineData.StackBelow (s₁ s₀ : MachineData) : Prop :=
  0 < (s₀.regs.get64 .rsp - s₁.regs.get64 .rsp).toInt

/-- The stack pointer of `s₁` lies at or below that of the reference state `s₀`. -/
public abbrev MachineData.StackAtOrBelow (s₁ s₀ : MachineData) : Prop := ¬ s₀.StackBelow s₁

open Classical in
/--
`Executable.StepOut e funs st₀ next jump st₁` defines the weakest precondition of the jump from
`st₀` to `st₁`. If the jump is not a call (cf. below), then `jump st₁` must hold.

The jump is considered a call iff
* `funs st₁.pc = some wp`,
* the stack pointer of `st₁` is below that of `st₀`.

In this case, the callee's activation is traced through `wp`, ending in a state `st₂`. Two cases:
* Return: If `st₂.pc = e.nextAddr st₀.pc`, then the callee returned to the instruction after
  `st₀.pc`. In this case, `next st₂` must hold and the effect is that of *stepping out* of the
  callee state at `st₁` back into the caller at `st₂`.
* Jump: Otherwise, `jump st₂` must hold, treating any jump of the callee like a jump of the call
  instruction.
-/
@[expose] public def Executable.StepOut (e : Executable)
    (funs : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (st₀ : MachineState) (next jump : MachineState → Prop) (st₁ : MachineState) : Prop :=
  match funs st₁.pc with
  | some wp =>
    if st₁.data.StackBelow st₀.data then
      wp (fun st₂ => if st₂.pc = e.nextAddr st₀.pc then next st₂ else jump st₂) st₁.data
    else jump st₁
  | none => jump st₁

/--
`Executable.StepOver e funs next jump st` defines the weakest precondition of the non-inert
directive at `st.pc` in `e`, where a call to a function in `funs` is a single step.
Fall-through states and returns from a call must satisfy `next`.
All other post-jump states must satisfy `jump`.
-/
@[expose] public def Executable.StepOver (e : Executable)
    (funs : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  e.StepIn next (e.StepOut funs st next jump) st

namespace Executable
variable {e : Executable} {st₀ : MachineState}
  {funs funs₁ funs₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)}

theorem StepOut.mono_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ s, (∀ u, R₁ u → R₂ u) → g₁ b R₁ s → g₂ b R₂ s)
    {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, u.pc = e.nextAddr st₀.pc → next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u)
    {st₁ : MachineState} (h : e.StepOut (fun a => (o a).map g₁) st₀ next₁ jump₁ st₁) :
    e.StepOut (fun a => (o a).map g₂) st₀ next₂ jump₂ st₁ := by
  unfold StepOut at h ⊢
  cases ho : o st₁.pc with
  | none =>
    simp only [ho, Option.map_none] at h ⊢
    exact hj _ h
  | some b =>
    simp only [ho, Option.map_some] at h ⊢
    by_cases hb : st₁.data.StackBelow st₀.data
    · simp only [hb, ite_true] at h ⊢
      refine hg b _ _ _ (fun u a => ?_) h
      by_cases hu : u.pc = e.nextAddr st₀.pc
      · simp only [hu, ite_true] at a ⊢
        exact hn _ hu a
      · simp only [hu, ite_false] at a ⊢
        exact hj _ a
    · simp only [hb, ite_false] at h ⊢
      exact hj _ h

public theorem StepOver.mono_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ s, (∀ u, R₁ u → R₂ u) → g₁ b R₁ s → g₂ b R₂ s)
    {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, u.pc = e.nextAddr st₀.pc → next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u)
    (h : e.StepOver (fun a => (o a).map g₁) next₁ jump₁ st₀) :
    e.StepOver (fun a => (o a).map g₂) next₂ jump₂ st₀ :=
  StepIn.mono h hn fun _ => StepOut.mono_map o hg hn hj

theorem StepOver.of_funs {next jump : MachineState → Prop}
    (hc : ∀ a, Option.Rel (fun wp₁ wp₂ => ∀ R s, wp₁ R s → wp₂ R s) (funs₁ a) (funs₂ a))
    (h : e.StepOver funs₁ next jump st₀) : e.StepOver funs₂ next jump st₀ := by
  refine StepIn.mono h (fun _ _ h => h) fun st₁ h => ?_
  unfold StepOut at h ⊢
  have hca := hc st₁.pc
  revert h
  cases h₁ : funs₁ st₁.pc <;> cases h₂ : funs₂ st₁.pc <;> rw [h₁, h₂] at hca <;> cases hca
  · exact id
  · rename_i hw
    dsimp only
    split
    · exact hw _ _
    · exact id

open Lean.Order in
@[partial_fixpoint_monotone] public theorem StepOver.monotone_map {α β : Type} [PartialOrder α]
    {next jump : MachineState → Prop} (o : Int64 → Option β)
    (g : α → β → (MachineState → Prop) → MachineData → ImplicationOrder) (hg : monotone g) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepOver (fun a => (o a).map (g x)) next jump st₀) := by
  intro x y hxy hx
  refine StepOver.of_funs (fun a => ?_) hx
  cases o a with
  | none => exact Option.Rel.none
  | some b => exact Option.Rel.some fun R s h => hg _ _ hxy b R s h

open Lean.Order in
@[partial_fixpoint_monotone] public theorem StepOver.monotone_map_fun {α β : Type} [PartialOrder α]
    {next jump : MachineState → Prop} (o : Int64 → Option β)
    (g : α → β → (MachineState → Prop) → MachineData → ImplicationOrder) (hg : monotone g) :
    @monotone _ _ _ (@instOrderPi MachineState (fun _ => ImplicationOrder) fun _ => ImplicationOrder.instOrder)
      (fun x => e.StepOver (fun a => (o a).map (g x)) next jump) :=
  fun _ _ hxy st₀ => StepOver.monotone_map (st₀ := st₀) o g hg _ _ hxy

end Executable

section
variable [Host]

public theorem Host.stepIn_addrOf {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d)
    (hz : 0 < Kraken.Layout.size Directive k) {s₀ : MachineData} {next jump : MachineState → Prop}
    (h : ∀ (P : MachineState → Prop) (n : MachineData → Effects) (j : Int64 → MachineData → Effects),
      (∀ s₁, next { data := s₁, pc := Host.addrOf (k + 1) } → (n s₁).All P) →
      (∀ a s₁, jump { data := s₁, pc := a } → (j a s₁).All P) →
      (d.interp s₀ ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ n j).All P) :
    Host.exe.StepIn next jump { data := s₀, pc := Host.addrOf k } := by
  intro P r j hr hj
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  change (@Directives.interp Host.exe.labels (Host.exe.directivesAtAddress (Host.addrOf k)) s₀ (Host.addrOf k) _ _).All P
  rw [Host.nextAddr_addrOf hd hz] at hr
  rw [hat, Directives.interp_inert_append hinert s₀ _ _ P (fun a s₀ => j { data := s₀, pc := a })]
  simp only [Directives.interp]
  rw [← Host.addrOf_succ hd]
  exact h _ _ _ (fun s₁ hn => hr _ hn) (fun a s₁ hj' => hj _ hj')
end
