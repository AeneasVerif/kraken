/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.All_of_false {_e₁ e₂ : Effects} {_post₁ post₂ : MachineState → Prop}
    (h : False) : e₂.All post₂ := False.elim h

theorem Effects.All_undefined {α : Type} [NondetSupportingType α]
    {cont₁ cont₂ : α → Effects} {post₁ post₂ : MachineState → Prop}
    (hcont : ∀ v, (cont₁ v).All post₁ → (cont₂ v).All post₂)
    (h : (@Effects.undefined α _ cont₁).All post₁) :
    (@Effects.undefined α _ cont₂).All post₂ :=
  fun v => hcont v (h v)

theorem Effects.All_ite {c : Prop} [Decidable c] {t₁ t₂ e₁ e₂ : Effects} {post₁ post₂ : MachineState → Prop}
    (ht : t₁.All post₁ → t₂.All post₂) (he : e₁.All post₁ → e₂.All post₂) :
    (if c then t₁ else e₁).All post₁ → (if c then t₂ else e₂).All post₂ := by
  split
  · exact ht
  · exact he

theorem Effects.All_dite {c : Prop} [Decidable c] {t₁ t₂ : c → Effects} {e₁ e₂ : ¬c → Effects} {post₁ post₂ : MachineState → Prop}
    (ht : ∀ h, (t₁ h).All post₁ → (t₂ h).All post₂) (he : ∀ h, (e₁ h).All post₁ → (e₂ h).All post₂) :
    (if h : c then t₁ h else e₁ h).All post₁ → (if h : c then t₂ h else e₂ h).All post₂ := by
  split
  · exact ht ‹_›
  · exact he ‹_›

#gen_mono
  Reg.interp
  MachineData.load
  MachineData.loadAvx
  MachineData.store
  MachineData.storeAvx
  RegOrMem.interp
  AvxRegOrMem.interp
  MachineData.set
  MachineData.setAvx
  MachineData.setAvxLegacy
  Operand.interp
  AvxOperand.interp
  RelRegOrMem.interp
  AvxOperation.interp
  Operation.interp
  Instr.interp
  Directive.interp

theorem Directives.interp_mono [Labels]
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    {ret₁ ret₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hret : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (h : (Directives.interp ds s pc ret₁).All post₁) :
    (Directives.interp ds s pc ret₂).All post₂ := by
  induction ds generalizing s pc with
  | nil =>
    exact hret pc s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz))
      hret
      h

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

theorem Directives.interp_split [Labels]
    (ds1 ds2 : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (ret₁ ret₂ : Int64 → MachineData → Effects)
    {post₁ post₂ : MachineState → Prop}
    (hjmp : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (hnext : ∀ s',
      (Directives.interp ds2 s' (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) ret₁).All post₁ →
      (ret₂ (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) s').All post₂)
    (h : (Directives.interp (ds1 ++ ds2) s pc ret₁).All post₁) :
    (Directives.interp ds1 s pc ret₂).All post₂ := by
  induction ds1 generalizing s pc with
  | nil =>
    dsimp [Directives.interp] at *
    exact hnext s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz) hnext)
      hjmp
      h

theorem eventually_step [Layout] (e: Executable) (hwf : e.WellFormed) (st: MachineState) (post: @Post MachineState):
    straightlineStep e st post →
    Eventually (step1 e) post st
    := by
  intro h
  let _ : Labels := Executable.labels e
  let s := st.1
  let pc := st.2
  apply step_cps (step1 e) post (s, pc)
  dsimp [step1, straightlineStep, Executable.step, Executable.straightline] at *
  rw [Kraken.directivesAtFromPrefix e pc] at h
  apply Directives.interp_split (e.directivesAtAddress pc) _ s pc
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' hp => Eventually.done (s', pc') hp)
    _ h
  intro s' h_after
  dsimp [Effects.All]
  generalize h_drop : (e.withAddresses.dropWhile (·.1 ≠ pc)).dropWhile (·.1 = pc) = after_pc at h_after
  cases after_pc with
  | nil =>
    dsimp [Directives.interp, Effects.All] at h_after
    exact Eventually.done _ h_after
  | cons y ys =>
    have h_starts_ne : e.withAddresses.dropWhile (·.1 ≠ pc) ≠ [] := by
      intro h_nil
      rw [h_nil] at h_drop
      contradiction
    obtain ⟨x, xs, h_starts⟩ := List.exists_cons_of_ne_nil h_starts_ne
    have h_starts' : (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ pc) = x :: xs := h_starts
    obtain ⟨hx_eq, ds', h_ds'⟩ := Kraken.withAddresses_dropWhile_eq e.1 e.2 (·.1 ≠ pc) h_starts'
    have hx_pc : x.1 = pc := by simpa using hx_eq
    rw [hx_pc] at h_ds'
    have h_fold : (e.directivesAtAddress pc).foldl (fun p (_, sz) => p + .ofNat sz) pc = y.1 := by
      dsimp [Kraken.Executable.directivesAtAddress]
      rw [h_starts, h_ds'] at h_drop ⊢
      exact Kraken.withAddresses_takeWhile_foldl pc ds' (·.1 = pc) h_drop
    rw [h_fold] at h_after ⊢
    have h_next_from : e.withAddresses.dropWhile (·.1 ≠ y.1) = y :: ys := hwf pc y ys h_drop
    have h_straightline_next : straightlineStep e (s', y.1) post := by
      dsimp [straightlineStep, Executable.straightline, Kraken.Executable.directivesFromAddress]
      rw [h_next_from]
      exact h_after
    have h_len : (e.withAddresses.dropWhile (·.1 ≠ y.1)).length < (e.withAddresses.dropWhile (·.1 ≠ pc)).length := by
      rw [h_next_from]
      have h_split := List.takeWhile_append_dropWhile (p := (·.1 = pc)) (l := e.withAddresses.dropWhile (·.1 ≠ pc))
      have h_len_eq := congrArg List.length h_split
      rw [List.length_append, h_drop] at h_len_eq
      have h_take_pos : 0 < ((e.withAddresses.dropWhile (·.1 ≠ pc)).takeWhile (·.1 = pc)).length := by
        rw [h_starts, List.takeWhile_cons]
        simp [hx_pc]
      omega
    exact eventually_step e hwf (s', y.1) post h_straightline_next
termination_by (e.withAddresses.dropWhile (·.1 ≠ st.2)).length
decreasing_by exact h_len

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post st
    (eventually_step e hwf st _ h) (fun _ => id)


theorem straightlineStep_mono [Layout] (e : Executable) (st : MachineState)
    {p q : @Post MachineState} (hpq : ∀ s, p s → q s) :
    straightlineStep e st p → straightlineStep e st q :=
  let _ := e.labels
  Directives.interp_mono _ _ _ (fun _ _ => hpq _)

theorem tailrec_loop_straightline [Layout] (e : Executable) (hwf : e.WellFormed)
    (post : @Post MachineState) (initial : MachineState)
    (P : Nat → @Post MachineState) (v0 : Nat) (hP : P v0 initial)
    (hbody : ∀ v state, P v state →
      straightlineStep e state (fun mid_s => post mid_s ∨ ∃ v', P v' mid_s ∧ v' < v)) :
    straightlineStep e initial (fun mid => Eventually (step1 e) post mid) := by
  refine straightlineStep_mono e initial ?_ (hbody v0 initial hP)
  rintro mid_s (hpost | ⟨v', hP', _⟩)
  · exact .done mid_s hpost
  · refine tailrec_loop (step1 e) post mid_s (fun v () => P v) (fun _ _ => post)
      (· < ·) Nat.lt_wfRel.wf v' () hP' (fun v _ st hst => eventually_step e hwf st _ ?_) (fun _ => id)
    refine straightlineStep_mono e st ?_ (hbody v st hst)
    rintro s (hp | ⟨v'', hp', hlt⟩)
    · exact .inl hp
    · exact .inr ⟨v'', (), hp', hlt, fun _ => id⟩

