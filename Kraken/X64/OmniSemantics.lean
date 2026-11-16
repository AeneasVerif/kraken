module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

open Kraken (Layout WellFormedLayout)

@[kstep] def Effects.All [Labels] (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .resolve_label lbl k =>
    match label? lbl with
    | .some a => (k a).All post
    | .none => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_resolve_label [Labels] (lbl : Label) (k : Int64 → Effects)
    (post : MachineState → Prop) :
    (Effects.resolve_label lbl k).All post =
      (match label? lbl with | .some a => (k a).All post | .none => False) := by
  rw [Effects.All]

@[ksimp] theorem Effects.All_require_read_access [Labels] (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access [Labels] (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  letI := e.labels
  (Executable.step e s .done).All post

private theorem Directives.interp_size_zero_append {p : Program} [l : Layout p]
    {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, ∃ m d', p[m]? = some d' ∧ c = {directive := d', size := 0} ∧ l.size m = 0)
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, d', hd', rfl, hz0⟩ := hpre c List.mem_cons_self
    simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero hd' hz0]
    exact ih (fun c' hc' => hpre c' (List.mem_cons_of_mem _ hc')) s

theorem eventually_of_interp {p : Program} [l : WellFormedLayout p]
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ := by
  have hc : p.toExecutable.program[k]? = some {directive := d, size := l.size k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := p.toExecutable.addrOf_succ hc
  letI : Labels := Executable.labels p.toExecutable
  match hsize : l.size k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero hd hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    obtain ⟨pre, hat, hpre⟩ := Kraken.Program.directivesAtAddress_addrOf p hd (by grind only)
    unfold step1 Executable.step
    dsimp only
    rw [hat, Directives.interp_size_zero_append hpre]
    simpa [Directives.interp, hsucc, hsize] using h

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

theorem step_at {p : Program} [WellFormedLayout p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 p.toExecutable) post)) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hd h) fun _ => id

theorem label?_eq_some_addrOf {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels p.toExecutable) lbl = some (p.toExecutable.addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p lbl hk

/-- `L₁ ⊆ L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

private theorem Effects.All_mono_labels {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂)
    {post : MachineState → Prop} (e : Effects)
    (h : @Effects.All L₁ post e) : @Effects.All L₂ post e := by
  match e with
  | .done _ | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => exact h
  | .resolve_label lbl k =>
    simp only [Effects.All_resolve_label] at h ⊢
    cases hlbl : L₁.label? lbl <;> rw [hlbl] at h
    · exact False.elim h
    · rw [hL lbl _ hlbl]; exact All_mono_labels hL (k _) h
  | @Effects.undefined _ _ cont => exact fun v => All_mono_labels hL (cont v) (h v)
  | .require_read_access _ cont | .require_write_access _ cont | .require_exec_access _ cont =>
    exact All_mono_labels hL (cont ()) h

private theorem label?_eq_some_mem {p : Program} [Kraken.Layout p] {l : Label} {a : Int64}
    (h : (Executable.labels p.toExecutable).label? l = some a) : l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    Kraken.Program.map_directive_withAddresses p ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

private theorem labels_take_subset {p₁ p₂ : Program} [l : Kraken.Layout (p₁ ++ p₂)] :
    letI := l.take p₁
    Executable.labels p₁.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  change (List.findSome? _ _) = some a at ha ⊢
  rw [Kraken.Program.toExecutable_append_withAddresses p₁ p₂, List.findSome?_append, ha]; rfl

variable (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]

private theorem labels_drop_subset :
    letI := layout.drop p₁
    Executable.labels p₂.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := by
    letI := layout.toLayout.drop p₁; exact label?_eq_some_mem ha
  have happ := Kraken.Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  change List.findSome? _ _ = some a at ha ⊢
  rw [happ, List.findSome?_append]
  cases h₁ : List.findSome? _ (letI := layout.toLayout.take p₁; p₁.toExecutable).withAddresses with
  | none => exact ha
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := by
      letI := layout.toLayout.take p₁; exact label?_eq_some_mem h₁
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using layout.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂)

private theorem Eventually.lift_sub {p_sub p_full : Program}
    [l_sub : Layout p_sub] [l_full : Layout p_full]
    (hL : Executable.labels p_sub.toExecutable ⊆ Executable.labels p_full.toExecutable)
    (hat : ∀ pc, (∃ c ∈ p_sub.toExecutable.directivesAtAddress pc, 0 < c.size) →
      ∃ pre, p_full.toExecutable.directivesAtAddress pc = pre ++ p_sub.toExecutable.directivesAtAddress pc ∧
        ∀ c ∈ pre, c.size = 0)
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 p_sub.toExecutable) post init) :
    Eventually (step1 p_full.toExecutable) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpos : ∃ c ∈ p_sub.toExecutable.directivesAtAddress s.pc, 0 < c.size
    · obtain ⟨pre, heq, hpre⟩ := hat s.pc hpos
      have hpre' : ∀ c ∈ pre,
          ∃ m d', p_full[m]? = some d' ∧ c = {directive := d', size := 0} ∧ l_full.size m = 0 := fun c hc => by
        obtain ⟨i, rfl, -⟩ := Kraken.Program.mem_directivesAtAddress p_full (heq ▸ List.mem_append_left _ hc)
        exact ⟨i, p_full[i], List.getElem?_eq_getElem i.isLt, by congr; exact hpre _ hc, hpre _ hc⟩
      refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [heq, Directives.interp_size_zero_append hpre']
      exact Effects.All_mono_labels hL _ hstep
    · have hall0 : ∀ c ∈ p_sub.toExecutable.directivesAtAddress s.pc,
          ∃ m d', p_sub[m]? = some d' ∧ c = {directive := d', size := 0} ∧ l_sub.size m = 0 :=
        fun c hc => by
          have hz := Classical.byContradiction fun h => hpos ⟨c, hc, Nat.pos_of_ne_zero h⟩
          obtain ⟨i, rfl, -⟩ := Kraken.Program.mem_directivesAtAddress p_sub hc
          exact ⟨i, p_sub[i], List.getElem?_eq_getElem i.isLt, by congr, hz⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels p_sub.toExecutable
      rw [← List.append_nil (p_sub.toExecutable.directivesAtAddress s.pc),
          Directives.interp_size_zero_append hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.prepend
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.drop p₁
       Eventually (step1 p₂.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.drop p₁
  Eventually.lift_sub (labels_drop_subset p₁ p₂)
    (Kraken.Program.directivesAtAddress_drop_eq p₁ p₂) h

theorem Eventually.append
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.take p₁
       Eventually (step1 p₁.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.take p₁
  Eventually.lift_sub (labels_take_subset (l := layout.toLayout))
    (fun pc hpos => ⟨[], by rw [List.nil_append]; exact Kraken.Program.directivesAtAddress_take_eq p₁ p₂ pc hpos, by simp⟩) h
