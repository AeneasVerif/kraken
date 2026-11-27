module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

open Kraken (Layout)

@[kstep] def Effects.All [Labels] (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .resolve_label lbl k =>
    match label? lbl with
    | .some a => (k a).All post
    | .none => False
  | .unaligned_sp .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_resolve_label [Labels] (lbl : Label) (k : Int64 → Effects)
    (post : MachineState → Prop) :
    (Effects.resolve_label lbl k).All post =
      (match label? lbl with | .some a => (k a).All post | .none => False) := by
  rw [Effects.All]

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  letI := e.labels
  (Executable.step e s .done).All post

theorem Directives.interp_directivesAtAddress_of_zeroSizePrefix
    {p : Program} {l : Layout} {pc : Int64} {rest : List (Kraken.Sized Directive)}
    (h : Kraken.ZeroSizePrefix ((l.apply p).directivesAtAddress pc) rest)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp ((l.apply p).directivesAtAddress pc) s pc ret =
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

/- More general version of `step_at` theorem which does not constrain the shape of the postcondition. -/
theorem eventually_of_interp {p : Program} {l : Layout} (hl : p.AssemblableWith l)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ := by
  have hc : (l.apply p).program[k]? = some {directive := d, size := l.dirSize p k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := (l.apply p).addrOf_succ hc
  letI : Labels := Executable.labels (l.apply p)
  match hsize : l.dirSize p k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero hd hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    unfold step1 Executable.step
    dsimp only
    rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
      (Kraken.Program.directivesAtAddress_addrOf hl hd (by grind only))]
    simpa [Directives.interp, hsucc, hsize] using h

/- This theorem is meant to be used when the user is doing a proof over `Eventually` and wants to keep the
   state of the goal as an `Eventually` -/
theorem step_at {p : Program} {l : Layout} [hl : p.AssemblableWith l] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (l.apply p)) post)) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hl hd h) fun _ => id

theorem label?_eq_some_addrOf {p : Program} {l : Layout} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels (l.apply p)) lbl = some ((l.apply p).addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p l lbl hk

/-- `L₁ ⊆ L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

theorem Effects.All_mono_labels {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂)
    {post : MachineState → Prop} (e : Effects)
    (h : @Effects.All L₁ post e) : @Effects.All L₂ post e := by
  match e with
  | .done _ | .unimplemented _ | .unaligned_sp .. | .nonmem_load .. | .nonmem_store .. => exact h
  | .resolve_label lbl k =>
    simp only [Effects.All_resolve_label] at h ⊢
    cases hlbl : L₁.label? lbl <;> rw [hlbl] at h
    · exact False.elim h
    · rw [hL lbl _ hlbl]; exact All_mono_labels hL (k _) h
  | @Effects.undefined _ _ cont => exact fun v => All_mono_labels hL (cont v) (h v)
  | .require_read_access _ _ cont | .require_write_access _ _ cont | .require_exec_access _ cont =>
    exact All_mono_labels hL (cont ()) h

theorem label?_eq_some_mem {p : Program} {layout : Layout} {l : Label} {a : Int64}
    (h : (Executable.labels (layout.apply p)).label? l = some a) : l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    Kraken.Program.map_directive_withAddresses p layout ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

theorem labels_append_left_subset (p₁ p₂ : Program) (l : Layout) :
    Executable.labels (l.apply p₁) ⊆ Executable.labels (l.apply (p₁ ++ p₂)) := by
  intro lbl a ha
  change List.findSome? _ _ = some a at ha ⊢
  rw [Kraken.Program.apply_append_withAddresses p₁ p₂ l, List.findSome?_append, ha]
  rfl

theorem labels_append_right_subset {p₁ p₂ : Program} {l : Layout} (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l) :
    Executable.labels ((l.offset p₁).apply p₂) ⊆ Executable.labels (l.apply (p₁ ++ p₂)) := by
  intro lbl a ha
  change List.findSome? _ _ = some a at ha ⊢
  rw [Kraken.Program.apply_append_withAddresses p₁ p₂ l, List.findSome?_append]
  cases h₁ : List.findSome? _ (l.apply p₁).withAddresses with
  | none => exact ha
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := label?_eq_some_mem h₁
    have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := label?_eq_some_mem ha
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using hl.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂)

theorem Eventually.mono_of_zeroSizePrefix {p q : Program} {lp lq : Layout}
    (hlabels : Executable.labels (lp.apply p) ⊆ Executable.labels (lq.apply q))
    (hdirs : ∀ pc, Kraken.Program.ContainsAddr p lp pc →
      Kraken.ZeroSizePrefix ((lq.apply q).directivesAtAddress pc)
        ((lp.apply p).directivesAtAddress pc))
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 (lp.apply p)) post init) :
    Eventually (step1 (lq.apply q)) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpc : Kraken.Program.ContainsAddr p lp s.pc
    · refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix (hdirs s.pc hpc)]
      exact Effects.All_mono_labels hlabels _ hstep
    · have hall0 : Kraken.ZeroSizePrefix ((lp.apply p).directivesAtAddress s.pc) [] :=
        ⟨(lp.apply p).directivesAtAddress s.pc, by simp,
          fun c hc => Classical.byContradiction fun hz =>
            hpc (Kraken.Program.containsAddr_of_mem_directivesAtAddress p lp hc (Nat.pos_of_ne_zero hz))⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels (lp.apply p)
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.append_left {p₁ p₂ : Program} {l : Layout} (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l)
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 (l.apply p₁)) post init) :
    Eventually (step1 (l.apply (p₁ ++ p₂))) post init :=
  Eventually.mono_of_zeroSizePrefix (labels_append_left_subset p₁ p₂ l)
    (fun pc hpc => ⟨[], by simp [Kraken.Program.directivesAtAddress_append_left hl pc hpc], by simp⟩) h

theorem Eventually.append_right {p₁ p₂ : Program} {l : Layout} (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l)
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 ((l.offset p₁).apply p₂)) post init) :
    Eventually (step1 (l.apply (p₁ ++ p₂))) post init :=
  Eventually.mono_of_zeroSizePrefix (labels_append_right_subset hl)
    (Kraken.Program.directivesAtAddress_append_right hl) h
