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

private theorem Directives.interp_directivesAtAddress_of_zeroSizePrefix
    {p : Program} [l : Layout p] {pc : Int64} {rest : List (Kraken.Sized Directive)}
    (h : Kraken.ZeroSizePrefix (p.toExecutable.directivesAtAddress pc) rest)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp (p.toExecutable.directivesAtAddress pc) s pc ret =
      Directives.interp rest s pc ret := by
  obtain ⟨pre, hpre, hz⟩ := h
  rw [hpre]
  have hmem := fun c (hc : c ∈ pre) => Kraken.Program.mem_of_zeroSizePrefix hpre hz hc
  clear hpre hz
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, d', hd', rfl, hz0⟩ := hmem c List.mem_cons_self
    simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero hd' hz0]
    exact ih s (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))

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
    unfold step1 Executable.step
    dsimp only
    rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
      (Kraken.Program.directivesAtAddress_addrOf p hd (by grind only))]
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

private theorem labels_infix_subset (p₁ p p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ (p ++ p₂))] :
    letI := (layout.drop p₁).take p
    Executable.labels p.toExecutable ⊆ Executable.labels (p₁ ++ (p ++ p₂)).toExecutable := by
  intro lbl a ha
  letI l₂₃ : Kraken.Layout (p ++ p₂) := layout.toLayout.drop p₁
  have hmem : lbl ∈ Kraken.Program.labels p := by
    letI := l₂₃.take p; exact label?_eq_some_mem ha
  have happ : (p₁ ++ (p ++ p₂)).toExecutable.withAddresses =
      (letI := layout.toLayout.take p₁; p₁.toExecutable.withAddresses) ++
      ((letI := l₂₃.take p; p.toExecutable.withAddresses) ++
       (letI := l₂₃.drop p; p₂.toExecutable.withAddresses)) := by
    rw [Kraken.Program.toExecutable_append_withAddresses p₁ (p ++ p₂) (l := layout.toLayout),
        Kraken.Program.toExecutable_append_withAddresses p p₂ (l := l₂₃)]
  change List.findSome? _ _ = some a at ha ⊢
  dsimp only [Kraken.WellFormedLayout.toLayout, Kraken.WellFormedLayout.drop,
    Kraken.WellFormedLayout.take] at ha
  rw [happ, List.findSome?_append]
  cases h₁ : List.findSome? _ (letI := layout.toLayout.take p₁; p₁.toExecutable).withAddresses with
  | none =>
    rw [List.findSome?_append]
    rw [show List.findSome? (fun x => if x.1.directive = .label lbl then some x.addr else none)
          (letI := l₂₃.take p; p.toExecutable.withAddresses) = some a from ha]
    rfl
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := by
      letI := layout.toLayout.take p₁; exact label?_eq_some_mem h₁
    have hmem₂₃ : lbl ∈ Kraken.Program.labels (p ++ p₂) := by
      simpa [Kraken.Program.labels, List.filterMap_append] using Or.inl hmem
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels (p ++ p₂)).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using layout.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂₃)

theorem Eventually.infix (p₁ p p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ (p ++ p₂))]
    (post : MachineState → Prop) (init : MachineState)
    (h : letI := (layout.drop p₁).take p
         Eventually (step1 p.toExecutable) post init) :
    Eventually (step1 (p₁ ++ (p ++ p₂)).toExecutable) post init := by
  letI l_sub := (layout.drop p₁).take p
  change Eventually (step1 p.toExecutable) post init at h
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpos : ∃ c ∈ p.toExecutable.directivesAtAddress s.pc, 0 < c.size
    · refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
        (Kraken.Program.directivesAtAddress_infix_eq p₁ p p₂ s.pc hpos)]
      exact Effects.All_mono_labels (labels_infix_subset p₁ p p₂) _ hstep
    · have hall0 : Kraken.ZeroSizePrefix (p.toExecutable.directivesAtAddress s.pc) [] :=
        ⟨p.toExecutable.directivesAtAddress s.pc, by simp,
          fun c hc => Classical.byContradiction fun hz => hpos ⟨c, hc, Nat.pos_of_ne_zero hz⟩⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels p.toExecutable
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.prepend (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : letI := layout.drop p₁
         Eventually (step1 p₂.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init := by
  have hcast : ∀ {a b : Program} (hab : a = b) (la : Kraken.WellFormedLayout a),
      b.toExecutable (l := (hab ▸ la).toLayout) = a.toExecutable (l := la.toLayout) := by rintro _ _ rfl _; rfl
  let hnil : p₁ ++ p₂ = p₁ ++ (p₂ ++ []) := congrArg (p₁ ++ ·) (List.append_nil p₂).symm
  letI l' : Kraken.WellFormedLayout (p₁ ++ (p₂ ++ [])) := hnil ▸ layout
  have htake : ((l'.drop p₁).take p₂).toLayout = (layout.drop p₁).toLayout := by
    have : ∀ {q} (hq : p₁ ++ p₂ = q) (lq : Kraken.WellFormedLayout q),
        lq = hq ▸ layout →
        ({ start := lq.start + .ofNat (p₁.mapIdx (fun i _ => lq.size i) |>.sum),
           instrSize := fun i => lq.instrSize (i + p₁.length),
           instrSize_pos := fun i => lq.instrSize_pos (i + p₁.length) } : Kraken.Layout p₂) =
          layout.toLayout.drop p₁ := by
      rintro _ rfl _ rfl; rfl
    exact this hnil l' rfl
  rw [← hcast hnil layout]
  exact Eventually.infix p₁ p₂ [] post init (htake ▸ h)

theorem Eventually.append (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : letI := layout.take p₁
         Eventually (step1 p₁.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init := by
  have hdrop_take : ((layout.drop []).take p₁).toLayout = (layout.take p₁).toLayout := by
    dsimp only [Kraken.Layout.drop, Kraken.Layout.take, Kraken.WellFormedLayout.toLayout,
      Kraken.WellFormedLayout.drop, Kraken.WellFormedLayout.take]
    congr 1; exact Int64.add_zero _
  exact @Eventually.infix [] p₁ p₂ layout post init (hdrop_take ▸ h)
