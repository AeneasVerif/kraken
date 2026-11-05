module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .next _ => False
  | .unimplemented _ => False
  | .unaligned_sp .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.bind_mono (eff : Effects)
    {k₁ k₂ : MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hk : ∀ s, (k₁ s).All post₁ → (k₂ s).All post₂)
    (hdone : ∀ st, post₁ st → post₂ st) :
    (eff.bind k₁).All post₁ → (eff.bind k₂).All post₂ := by
  induction eff <;> grind [Effects.bind, Effects.All]

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s).All post

theorem Directives.interp_split [Labels]
    (ds1 ds2 : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64)
    {post₁ post₂ : MachineState → Prop}
    (hdone : ∀ st, post₁ st → post₂ st)
    (hnext : ∀ s',
      (Directives.interp ds2 s' (ds1.foldl (fun p d => p + Int64.ofNat d.size) pc)).All post₁ →
      post₂ ⟨s', ds1.foldl (fun p d => p + Int64.ofNat d.size) pc⟩)
    (h : (Directives.interp (ds1 ++ ds2) s pc).All post₁) :
    (Directives.interp ds1 s pc).All post₂ := by
  induction ds1 generalizing s pc with
  | nil =>
    rw [Directives.interp, List.nil_append] at *
    exact hnext s h
  | cons d tail ih =>
    rw [List.cons_append, Directives.interp] at h
    rw [Directives.interp]
    exact Effects.bind_mono _ (fun s' => ih s' (pc + Int64.ofNat d.size) hnext) hdone h

theorem eventually_step [Layout] (e: Executable) (hwf : e.WellFormed) (st: MachineState) (post: @Post MachineState) :
    (letI := Executable.labels e
     Directives.interp (e.directivesFromAddress st.pc) st.data st.pc).All post →
    Eventually (step1 e) post st := by
  rcases st with ⟨s, pc⟩
  intro h
  apply step_cps (step1 e) post ⟨s, pc⟩
  dsimp [step1, Executable.step] at *
  letI := Executable.labels e
  rcases hwf.directivesFromAddress_split pc with h_end | ⟨h_split, h_len⟩
  · rw [h_end, ← List.append_nil (e.directivesAtAddress pc)] at h
    apply Directives.interp_split (e.directivesAtAddress pc) [] s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    rw [Directives.interp] at h_after
    exact Eventually.done _ h_after
  · rw [h_split] at h
    apply Directives.interp_split (e.directivesAtAddress pc) _ s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    exact eventually_step e hwf ⟨s', _⟩ post h_after
termination_by (e.withAddresses.dropWhile (·.addr ≠ st.pc)).length
decreasing_by exact h_len

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (st : MachineState) (post : @Post MachineState) :
    (letI := Executable.labels e
     Directives.interp (e.directivesFromAddress st.pc) st.data st.pc).All
      (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post st
    (eventually_step e hwf st _ h) (fun _ => id)
