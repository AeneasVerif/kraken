module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .next _ => False
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.bind_mono (eff : Effects)
    {k₁ k₂ : MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hk : ∀ s, (k₁ s).All post₁ → (k₂ s).All post₂)
    (hdone : ∀ st, post₁ st → post₂ st) :
    (eff.bind k₁).All post₁ → (eff.bind k₂).All post₂ := by
  induction eff <;> grind [Effects.bind, Effects.All]

@[ksimp] theorem Effects.bind_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (k : MachineData → Effects) :
    (require_access require_read_access addr bytes ok).bind k =
      require_access require_read_access addr bytes (fun u => (ok u).bind k) := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.bind_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (k : MachineData → Effects) :
    (require_access require_write_access addr bytes ok).bind k =
      require_access require_write_access addr bytes (fun u => (ok u).bind k) := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

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

private theorem eventually_step_aux [Layout] (e : Executable) (hwf : e.WellFormed)
    (ds : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64) (post : @Post MachineState)
    (h_at : e.withAddresses.dropWhile (·.addr ≠ pc) = Kraken.Executable.withAddresses {startAddr := pc, program := ds}) :
    (letI := Executable.labels e
     Directives.interp ds s pc).All post →
    Eventually (step1 e) post ⟨s, pc⟩ := by
  intro h
  apply step_cps (step1 e) post ⟨s, pc⟩
  dsimp [step1, Executable.step] at *
  letI := Executable.labels e
  rcases hwf.step_split h_at with h_end | ⟨ds', h_split, h_len, h_at'⟩
  · rw [h_end, ← List.append_nil (e.directivesAtAddress pc)] at h
    apply Directives.interp_split (e.directivesAtAddress pc) [] s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    rw [Directives.interp] at h_after
    exact Eventually.done _ h_after
  · rw [h_split] at h
    apply Directives.interp_split (e.directivesAtAddress pc) ds' s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    exact eventually_step_aux e hwf ds' s' _ post h_at' h_after
termination_by ds.length
decreasing_by exact h_len

theorem eventually_step [Layout] (e : Executable) (hwf : e.WellFormed)
    (s : MachineData) (post : @Post MachineState) :
    (letI := Executable.labels e
     Directives.interp e.program s e.startAddr).All post →
    Eventually (step1 e) post ⟨s, e.startAddr⟩ :=
  eventually_step_aux e hwf e.program s e.startAddr post
    (Kraken.Executable.withAddresses_dropWhile_start e.program e.startAddr)

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (s : MachineData) (post : @Post MachineState) :
    (letI := Executable.labels e
     Directives.interp e.program s e.startAddr).All
      (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post ⟨s, e.startAddr⟩ := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post ⟨s, e.startAddr⟩
    (eventually_step e hwf s _ h) (fun _ => id)
