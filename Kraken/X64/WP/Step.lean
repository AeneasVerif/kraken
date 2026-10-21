module

public import Kraken.X64.Natural
public import Kraken.X64.WP.Host

/-! # Weakest precondition of a single step over a call

Imagine a debugger like `gdb`. It comes with 3 sorts of stepping operations:
* step inside: execute a single instruction and follow its control flow. If it's a call instruction,
  *step inside* the callee.
* step outside: execute all instructions until a return *steps outside* the current stack frame.
* step over: step inside. When the instruction was a call, then step outside afterwards. Thus,
  *step over* a call instruction.

The definitions `Executable.StepIn`, `Executable.StepOut` and `Executable.StepOver` in this module
implement a notion of weakest precondition based on this intuition and `Directives.interp` that is
*conjunctive* (cf. `Executable.StepIn.and`).

`Executable.StepOver e callee next jump st` is the weakest precondition of the directives at
address `st.pc` of the executable `e`. `next` is the postcondition when control falls through to
`e.fallthrough st.pc`, and `jump` is the postcondition at every other target.
`callee a = some wp` declares a function at address `a` with weakest precondition `wp`.

The definition of `StepOver` works by
1. Considering the weakest precondition `Executable.StepIn` of the directives at `st.pc`.
   Fall-through must satisfy `next`, and a jump must satisfy `jump`.
2. Deciding for each jump target `st'` whether the jump is a call, via `Executable.StepOut`.
   * If `callee st'.pc = some wp` and the stack pointer of `st'` is below its value in `st`, then
     the jump is a call. `wp` must hold at `st'`. A return to `e.fallthrough st.pc` must satisfy
     `next`, and a return to any other address must satisfy `jump`.
   * Any other jump must satisfy `jump`.

For example, let `call f` be the directive at `st.pc`, with `callee (label f) = some wp_f`.
`call f` pushes the return address and jumps to the state `st'` with `st'.pc = label f`.
The stack pointer of `st'` is below its value in `st`, so `StepOver e callee next jump st` holds
if `wp_f R st'.data` holds, where `R` is `next` at `e.fallthrough st.pc` and `jump` elsewhere.

`StepOver` is monotone in `callee` (cf. `Executable.StepOver.monotone_map_fun`), so `Program.wp`
can apply `StepOver` to its own weakest precondition in an inductive fixpoint.
-/

@[expose] public def Executable.StepIn (e : Executable) (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  let := e.labels
  ∀ ⦃P : MachineState → Prop⦄ ⦃ret jmp : MachineState → Effects⦄,
    (∀ st', next st' → (ret st').All P) → (∀ st', jump st' → (jmp st').All P) →
      (Directives.interp (e.directivesAtAddress st.pc) st.data st.pc (fun a s => ret ⟨s, a⟩)
        (fun a s => jmp ⟨s, a⟩)).All P

namespace Executable.StepIn
variable {e : Executable} {st : MachineState}

public theorem mono {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h : e.StepIn next₁ jump₁ st)
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) : e.StepIn next₂ jump₂ st :=
  fun _ _ _ hr hk => h (fun u h => hr u (hn u h)) (fun u h => hk u (hj u h))

open Classical in
public theorem restrict {next jump : MachineState → Prop} (h : e.StepIn next jump st) :
    e.StepIn (fun u => next u ∧ u.pc = e.fallthrough st.pc) jump st := by
  intro P r j hr hj
  let probe : Prop → Effects := fun c => if c then .done st else .unimplemented ""
  have hprobe : ∀ c, (probe c).All (fun _ => True) ↔ c := fun c => by
    by_cases hc : c <;> simp [probe, hc, Effects.All]
  have t := @h (fun _ => True) (fun u => probe (next u)) (fun u => probe (jump u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  have e₁ := @Directives.interp_ret_congr e.labels (e.directivesAtAddress st.pc) st.data st.pc
    (fun a s => probe (next ⟨s, a⟩)) (fun _ s => probe (next ⟨s, e.fallthrough st.pc⟩))
    (fun a s => probe (jump ⟨s, a⟩)) (fun _ => rfl)
  have e₂ := @Directives.interp_ret_congr e.labels (e.directivesAtAddress st.pc) st.data st.pc
    (fun a s => r ⟨s, a⟩) (fun _ s => r ⟨s, e.fallthrough st.pc⟩) (fun a s => j ⟨s, a⟩) (fun _ => rfl)
  change (@Directives.interp e.labels _ _ _ _ _).All _ at t
  change (@Directives.interp e.labels _ _ _ _ _).All _
  rw [e₁] at t
  rw [e₂]
  refine @Directives.interp_natural e.labels (e.directivesAtAddress st.pc) st.data st.pc _ _ P
    (Sum.elim (fun x => probe (next ⟨x.2, e.fallthrough st.pc⟩)) (fun x => probe (jump ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => probe (next ⟨x.2, e.fallthrough st.pc⟩)) (fun x => probe (jump ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => r ⟨x.2, e.fallthrough st.pc⟩) (fun x => j ⟨x.2, x.1⟩)) ?_ t t
  rintro (⟨a, s⟩ | ⟨a, s⟩) e₁ _
  · exact hr _ ⟨(hprobe _).mp e₁, rfl⟩
  · exact hj _ ((hprobe _).mp e₁)

public theorem all [Layout] {next jump post : MachineState → Prop} (h : e.StepIn next jump st)
    (hn : ∀ u, next u → post u) (hj : ∀ u, jump u → post u) : step1 e st post := by
  unfold step1 Executable.step
  exact h (fun _ h => hn _ h) (fun _ h => hj _ h)

open Lean.Order in
@[partial_fixpoint_monotone] public theorem monotone {α : Type} [PartialOrder α] {next : MachineState → Prop}
    (f : α → MachineState → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepIn next (f x) st) :=
  fun _ _ hxy hx => hx.mono (fun _ h => h) fun u => hf _ _ hxy u

end Executable.StepIn

-- the stack pointer of `s'` lies below that of the reference state `s`
@[expose] public def MachineData.StackBelow (s' s : MachineData) : Prop :=
  0 < (s.regs.get64 .rsp - s'.regs.get64 .rsp).toInt

-- the stack pointer of `s'` lies at or below that of the reference state `s`
public abbrev MachineData.StackAtOrBelow (s' s : MachineData) : Prop := ¬ s.StackBelow s'

open Classical in
@[expose] public def Executable.StepOut (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (st : MachineState) (next jump : MachineState → Prop) (st' : MachineState) : Prop :=
  match callee st'.pc with
  | some wp =>
    if st'.data.StackBelow st.data then
      wp (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' else jump st'') st'.data
    else jump st'
  | none => jump st'

@[expose] public def Executable.StepOver (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  e.StepIn next (e.StepOut callee st next jump) st

namespace Executable
variable {e : Executable} {st : MachineState}
  {callee callee₁ callee₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)}

public theorem StepOut.mono_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ s, (∀ u, R₁ u → R₂ u) → g₁ b R₁ s → g₂ b R₂ s)
    {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) {st' : MachineState}
    (h : e.StepOut (fun a => (o a).map g₁) st next₁ jump₁ st') :
    e.StepOut (fun a => (o a).map g₂) st next₂ jump₂ st' := by
  unfold StepOut at h ⊢
  cases ho : o st'.pc with
  | none =>
    simp only [ho, Option.map_none] at h ⊢
    exact hj _ h
  | some b =>
    simp only [ho, Option.map_some] at h ⊢
    by_cases hb : st'.data.StackBelow st.data
    · simp only [hb, ite_true] at h ⊢
      refine hg b _ _ _ (fun u a => ?_) h
      by_cases hu : u.pc = e.fallthrough st.pc
      · simp only [hu, ite_true] at a ⊢
        exact hn _ a
      · simp only [hu, ite_false] at a ⊢
        exact hj _ a
    · simp only [hb, ite_false] at h ⊢
      exact hj _ h

public theorem StepOver.mono_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ s, (∀ u, R₁ u → R₂ u) → g₁ b R₁ s → g₂ b R₂ s)
    {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u)
    (h : e.StepOver (fun a => (o a).map g₁) next₁ jump₁ st) :
    e.StepOver (fun a => (o a).map g₂) next₂ jump₂ st :=
  StepIn.mono h hn fun _ => StepOut.mono_map o hg hn hj

public theorem StepOver.restrict {next jump : MachineState → Prop} (h : e.StepOver callee next jump st) :
    e.StepOver callee (fun u => next u ∧ u.pc = e.fallthrough st.pc) jump st := by
  refine StepIn.mono (StepIn.restrict h) (fun _ h => h) fun st' h => ?_
  have hR : (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' ∧ st''.pc = e.fallthrough st.pc
      else jump st'') = (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' else jump st'') :=
    funext fun u => by by_cases hu : u.pc = e.fallthrough st.pc <;> simp [hu]
  unfold StepOut at h ⊢
  rw [hR]
  exact h

public theorem StepOver.of_callee {next jump : MachineState → Prop}
    (hc : ∀ a, Option.Rel (fun wp₁ wp₂ => ∀ R s, wp₁ R s → wp₂ R s) (callee₁ a) (callee₂ a))
    (h : e.StepOver callee₁ next jump st) : e.StepOver callee₂ next jump st := by
  refine StepIn.mono h (fun _ h => h) fun st' h => ?_
  unfold StepOut at h ⊢
  have hca := hc st'.pc
  revert h
  cases h₁ : callee₁ st'.pc <;> cases h₂ : callee₂ st'.pc <;> rw [h₁, h₂] at hca <;> cases hca
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
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepOver (fun a => (o a).map (g x)) next jump st) := by
  intro x y hxy hx
  refine StepOver.of_callee (fun a => ?_) hx
  cases o a with
  | none => exact Option.Rel.none
  | some b => exact Option.Rel.some fun R s h => hg _ _ hxy b R s h

open Lean.Order in
@[partial_fixpoint_monotone] public theorem StepOver.monotone_map_fun {α β : Type} [PartialOrder α]
    {next jump : MachineState → Prop} (o : Int64 → Option β)
    (g : α → β → (MachineState → Prop) → MachineData → ImplicationOrder) (hg : monotone g) :
    @monotone _ _ _ (@instOrderPi MachineState (fun _ => ImplicationOrder) fun _ => ImplicationOrder.instOrder)
      (fun x => e.StepOver (fun a => (o a).map (g x)) next jump) :=
  fun _ _ hxy st => StepOver.monotone_map (st := st) o g hg _ _ hxy

end Executable

section
variable [Host]

public theorem Host.stepIn_addrOf {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d)
    (hz : 0 < Kraken.Layout.size Directive k) {s : MachineData} {next jump : MachineState → Prop}
    (h : ∀ ⦃P : MachineState → Prop⦄ ⦃n : MachineData → Effects⦄ ⦃j : Int64 → MachineData → Effects⦄,
      (∀ s', next ⟨s', Host.addrOf (k + 1)⟩ → (n s').All P) → (∀ a s', jump ⟨s', a⟩ → (j a s').All P) →
      (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ n j).All P) :
    Host.exe.StepIn next jump ⟨s, Host.addrOf k⟩ := by
  intro P r j hr hj
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  change (@Directives.interp Host.exe.labels (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _ _).All P
  rw [hat, Directives.interp_inert_append hinert s _ _ P (fun a s => j ⟨s, a⟩)]
  simp only [Directives.interp]
  rw [← Host.addrOf_succ hd]
  exact h (fun s' hn => hr _ hn) (fun a s' hj' => hj _ hj')
end
