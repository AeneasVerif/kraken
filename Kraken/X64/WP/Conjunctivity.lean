module

public import Kraken.X64.WP.Basic

namespace Executable
variable {e : Executable} {st : MachineState}

open Classical in
public theorem StepIn.and {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h₁ : e.StepIn next₁ jump₁ st)
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

public theorem StepOut.and_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ g : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ R s, (∀ u, R₁ u → R₂ u → R u) → g₁ b R₁ s → g₂ b R₂ s → g b R s)
    {next₁ next₂ next jump₁ jump₂ jump : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u → next u) (hj : ∀ u, jump₁ u → jump₂ u → jump u) {st' : MachineState}
    (h₁ : e.StepOut (fun a => (o a).map g₁) st next₁ jump₁ st')
    (h₂ : e.StepOut (fun a => (o a).map g₂) st next₂ jump₂ st') :
    e.StepOut (fun a => (o a).map g) st next jump st' := by
  unfold StepOut at h₁ h₂ ⊢
  cases ho : o st'.pc with
  | none =>
    simp only [ho, Option.map_none] at h₁ h₂ ⊢
    exact hj _ h₁ h₂
  | some b =>
    simp only [ho, Option.map_some] at h₁ h₂ ⊢
    by_cases hb : st'.data.StackBelow st.data
    · simp only [hb, ite_true] at h₁ h₂ ⊢
      refine hg b _ _ _ _ (fun u a b => ?_) h₁ h₂
      by_cases hu : u.pc = e.fallthrough st.pc
      · simp only [hu, ite_true] at a b ⊢
        exact hn _ a b
      · simp only [hu, ite_false] at a b ⊢
        exact hj _ a b
    · simp only [hb, ite_false] at h₁ h₂ ⊢
      exact hj _ h₁ h₂

public theorem StepOver.and_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ g : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ R s, (∀ u, R₁ u → R₂ u → R u) → g₁ b R₁ s → g₂ b R₂ s → g b R s)
    {next₁ next₂ next jump₁ jump₂ jump : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u → next u) (hj : ∀ u, jump₁ u → jump₂ u → jump u)
    (h₁ : e.StepOver (fun a => (o a).map g₁) next₁ jump₁ st)
    (h₂ : e.StepOver (fun a => (o a).map g₂) next₂ jump₂ st) :
    e.StepOver (fun a => (o a).map g) next jump st :=
  StepIn.mono (StepIn.and h₁ h₂) (fun u h => hn u h.1 h.2)
    fun _ h => StepOut.and_map o hg hn hj h.1 h.2

end Executable

section
variable [Host] [FunDecls]

omit [FunDecls] in
public theorem Program.continueAtOwnLabel_and {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} {u : MachineState}
    (h₁ : p.ContinueAtOwnLabel s c₁ e₁ u) (h₂ : p.ContinueAtOwnLabel s c₂ e₂ u) :
    p.ContinueAtOwnLabel s (fun u => c₁ u ∧ c₂ u) (fun u => e₁ u ∧ e₂ u) u := by
  unfold Program.ContinueAtOwnLabel at h₁ h₂ ⊢
  by_cases hcond : p.IsLabelAddr u.pc ∧ u.data.StackAtOrBelow s
  · rw [ite_eq_left hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩
  · rw [ite_eq_right hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩

public theorem Program.wp_and {p : Program} {done₁ done₂ exit₁ exit₂ : MachineState → Prop} {s : MachineData}
    (h₁ : p.wp done₁ exit₁ s) (h₂ : p.wp done₂ exit₂ s) :
    p.wp (fun u => done₁ u ∧ done₂ u) (fun u => exit₁ u ∧ exit₂ u) s := by
  refine Program.wp.induct
    (fun p done exit s => ∀ done' exit' : MachineState → Prop, p.wp done' exit' s →
      p.wp (fun u => done u ∧ done' u) (fun u => exit u ∧ exit' u) s)
    ?_ p done₁ exit₁ s h₁ done₂ exit₂ h₂
  intro p done exit s hw done' exit' hw'
  rw [Program.wp_eq] at hw' ⊢
  intro H
  refine While.and (fun U V y _ hU hV => ?_) (hw H) (hw' H)
  refine Executable.StepOver.and_map FunDecls.at ?_ (fun _ h₁ h₂ => ⟨h₁, h₂⟩)
    (fun _ h₁ h₂ => Program.continueAtOwnLabel_and h₁ h₂) hU hV
  exact fun _ _ _ _ _ hR h₁ h₂ => Program.wp_mono (fun _ h => h.1) (fun u h => hR u h.1 h.2) (h₁ _ _ h₂)

end
