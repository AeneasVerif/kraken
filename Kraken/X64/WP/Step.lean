module

public import Kraken.X64.Natural

@[expose] public def Directives.endPc (ds : List (Kraken.Sized Directive)) (pc : Int64) : Int64 :=
  match ds with
  | [] => pc
  | c :: ds => Directives.endPc ds (pc + .ofNat c.size)

public theorem Directives.endPc_append (ds ds' : List (Kraken.Sized Directive)) (pc : Int64) :
    Directives.endPc (ds ++ ds') pc = Directives.endPc ds' (Directives.endPc ds pc) := by
  induction ds generalizing pc with
  | nil => rfl
  | cons c ds ih => exact ih _

public theorem Directives.endPc_of_size_zero {ds : List (Kraken.Sized Directive)} (h : ∀ c ∈ ds, c.size = 0)
    (pc : Int64) : Directives.endPc ds pc = pc := by
  induction ds generalizing pc with
  | nil => rfl
  | cons c ds ih =>
    have hc : pc + Int64.ofNat c.size = pc := by rw [h c List.mem_cons_self]; simp
    simp only [Directives.endPc, hc]
    exact ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) pc

public theorem Directives.interp_ret_congr [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) {ret ret' jmp : Int64 → MachineData → Effects}
    (h : ∀ s, ret (Directives.endPc ds pc) s = ret' (Directives.endPc ds pc) s) :
    Directives.interp ds s pc ret jmp = Directives.interp ds s pc ret' jmp := by
  induction ds generalizing s pc with
  | nil => exact h s
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    simp only [Directives.interp]
    congr 1
    funext s'
    exact ih s' _ h

@[expose] public def Executable.fallthrough (e : Executable) (a : Int64) : Int64 :=
  Directives.endPc (e.directivesAtAddress a) a

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
public theorem and {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h₁ : e.StepIn next₁ jump₁ st)
    (h₂ : e.StepIn next₂ jump₂ st) :
    e.StepIn (fun u => next₁ u ∧ next₂ u) (fun u => jump₁ u ∧ jump₂ u) st := by
  intro P r j hr hj
  let probe : Prop → Effects := fun c => if c then .done st else .unimplemented ""
  have hprobe : ∀ c, (probe c).All (fun _ => True) ↔ c := fun c => by
    by_cases hc : c <;> simp [probe, hc, Effects.All]
  have t₁ := @h₁ (fun _ => True) (fun u => probe (next₁ u)) (fun u => probe (jump₁ u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  have t₂ := @h₂ (fun _ => True) (fun u => probe (next₂ u)) (fun u => probe (jump₂ u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  refine @Directives.interp_natural e.labels (e.directivesAtAddress st.pc) st.data st.pc _ _ P
    (Sum.elim (fun x => probe (next₁ ⟨x.2, x.1⟩)) (fun x => probe (jump₁ ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => probe (next₂ ⟨x.2, x.1⟩)) (fun x => probe (jump₂ ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => r ⟨x.2, x.1⟩) (fun x => j ⟨x.2, x.1⟩)) ?_ t₁ t₂
  rintro (⟨a, s⟩ | ⟨a, s⟩) e₁ e₂
  · exact hr _ ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩
  · exact hj _ ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩

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

-- `callee₂` asks no more than `callee₁` at every address, for a weaker exit post
@[expose] public def Executable.CalleeLe (callee₁ callee₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)) :
    Prop :=
  ∀ a, Option.Rel (fun wp₁ wp₂ => ∀ (R₁ R₂ : MachineState → Prop) s, (∀ u, R₁ u → R₂ u) → wp₁ R₁ s → wp₂ R₂ s)
    (callee₁ a) (callee₂ a)

namespace Executable
variable {e : Executable} {st : MachineState}
  {callee callee₁ callee₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)}

public theorem StepOut.imp (hc : CalleeLe callee₁ callee₂) {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) {st' : MachineState}
    (h : e.StepOut callee₁ st next₁ jump₁ st') : e.StepOut callee₂ st next₂ jump₂ st' := by
  unfold StepOut at h ⊢
  have hca := hc st'.pc
  revert h
  cases h₁ : callee₁ st'.pc <;> cases h₂ : callee₂ st'.pc <;> rw [h₁, h₂] at hca <;> cases hca
  · exact hj _
  · rename_i wp₁ wp₂ hw
    dsimp only
    split
    · exact hw _ _ _ fun u => by split <;> simp_all
    · exact hj _

public theorem StepOver.imp (hc : CalleeLe callee₁ callee₂) {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (h : e.StepOver callee₁ next₁ jump₁ st) (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) :
    e.StepOver callee₂ next₂ jump₂ st :=
  StepIn.mono h hn fun _ => StepOut.imp hc hn hj

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
