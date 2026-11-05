module

public import Kraken.X64.OmniSemantics
import Kraken.X64.Inert

@[expose] public section

abbrev Directives.size (ds : List (Kraken.Sized Directive)) : Nat := (ds.map (·.size)).sum

def Labels.Sub (labels₁ labels₂ : Labels) : Prop := ∀ l a, labels₁ l = some a → labels₂ l = some a

theorem Labels.Sub.refl (labels : Labels) : labels.Sub labels := fun _ _ h => h

private theorem Labels.guard_mono {labels₁ labels₂ : Labels} (hL : labels₁.Sub labels₂)
    (ls : List Label) {k₁ k₂ : Effects} {post : @Post MachineState}
    (hk : (∀ l ∈ ls, labels₁ l = labels₂ l) → k₁ = k₂)
    (h : (labels₁.guard ls k₁).All post) : (labels₂.guard ls k₂).All post := by
  induction ls with
  | nil => rwa [← hk nofun]
  | cons l ls ih =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
      (by cases hl : (labels₁ l).isSome <;> simp_all [Labels.guard, Effects.All])
    have hb := hL l a ha
    simp only [Labels.guard, ha, hb, Option.isSome_some, Bool.cond_true] at h ⊢
    exact ih (fun hk' => hk fun l' hl' => by rcases List.mem_cons.mp hl' with rfl | hl' <;> simp_all) h

private theorem Directive.interp_mono {labels₁ labels₂ : Labels} (hL : labels₁.Sub labels₂)
    (d : Directive) (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) {post : @Post MachineState}
    (h : (d.interp labels₁ s p next jmp).All post) :
    (d.interp labels₂ s p next jmp).All post := by
  refine Labels.guard_mono hL d.labels (fun heq => ?_) h
  cases d <;> try rfl
  dsimp only; congr 1; unfold Labels.restrict; congr; funext l; split <;> simp_all

section
variable {labels₁ labels₂ : Labels} {Q₁ P Q₂ : List (Kraken.Sized Directive)} {a : Int64}

private theorem addrOf_infix {k : Nat} (hk : k < P.length) :
    (⟨a, Q₁ ++ P ++ Q₂⟩ : Executable).addrOf (Q₁.length + k) =
      (⟨a + .ofNat (Directives.size Q₁), P⟩ : Executable).addrOf k := by
  simp [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, Directives.size, List.take_append,
    Nat.sub_eq_zero_of_le (Nat.le_of_lt hk), Int64.ofNat_add, Int64.add_assoc,
    List.take_of_length_le (l := Q₁.map (·.size)) (by simp : (Q₁.map (·.size)).length ≤ Q₁.length + k)]

private theorem Directives.interp_directivesAtAddress_addrOf (labels : Labels) {e : Executable}
    (hfit : Directives.size e.program < 2 ^ 64)
    (hinert : ∀ c ∈ e.program, c.size = 0 → Directive.Inert c.directive)
    {k : Nat} {c : Kraken.Sized Directive} (hk : e.program[k]? = some c) (hz : 0 < c.size)
    (s : MachineData) (ret : Int64 → MachineData → Effects) (post : @Post MachineState) :
    (Directives.interp labels (e.directivesAtAddress (e.addrOf k)) s (e.addrOf k) ret).All post ↔
      (Directives.interp labels [c] s (e.addrOf k) ret).All post := by
  obtain ⟨pre, hat, hpre⟩ :=
    e.directivesAtAddress_addrOf (fun _ _ => e.sizeBefore_eq_of_addrOf_eq hfit) hk hz
  rw [hat, Directives.interp_inert_append labels fun c' hc' => ⟨hpre c' hc', hinert c'
    (Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc')) (hpre c' hc')⟩]

private theorem step1_infix_of_sub (hL : labels₁.Sub labels₂)
    (hfit : Directives.size (Q₁ ++ P ++ Q₂) < 2 ^ 64)
    (hinert : ∀ c ∈ Q₁ ++ P ++ Q₂, c.size = 0 → c.directive.Inert)
    {s : MachineState} {post : @Post MachineState}
    (h : step1 ⟨a + .ofNat (Directives.size Q₁), P⟩ labels₁ s post) :
    post s ∨ step1 ⟨a, Q₁ ++ P ++ Q₂⟩ labels₂ s post := by
  rcases s with ⟨md, pc⟩
  have hinertP : ∀ c ∈ P, c.size = 0 → c.directive.Inert := fun c hc => hinert c (by simp [hc])
  unfold step1 Executable.step at h ⊢
  by_cases hpos : ∃ c ∈ Kraken.Executable.directivesAtAddress ⟨a + .ofNat (Directives.size Q₁), P⟩ pc,
      0 < c.size
  · obtain ⟨c, hc, hz⟩ := hpos
    obtain ⟨k, hk, rfl⟩ := Kraken.Executable.exists_of_mem_directivesAtAddress hc
    have hkP : k < P.length := (List.getElem?_eq_some_iff.mp hk).1
    have hkB : (Q₁ ++ P ++ Q₂)[Q₁.length + k]? = some c := by grind
    rw [Directives.interp_directivesAtAddress_addrOf labels₁ (by grind) hinertP hk hz] at h
    right
    rw [← addrOf_infix hkP, Directives.interp_directivesAtAddress_addrOf labels₂ hfit hinert hkB hz,
      addrOf_infix hkP]
    exact Directive.interp_mono hL c.directive _ _ _ _ h
  · left
    rw [← List.append_nil (Kraken.Executable.directivesAtAddress _ _),
      Directives.interp_inert_append labels₁ fun c hc => ?_] at h
    · simpa [Directives.interp, Effects.All] using h
    exact ⟨by grind, hinertP c (Kraken.Executable.mem_of_mem_directivesAtAddress hc) (by grind)⟩

private theorem eventually_infix_of_sub (hL : labels₁.Sub labels₂)
    (hfit : Directives.size (Q₁ ++ P ++ Q₂) < 2 ^ 64)
    (hinert : ∀ c ∈ Q₁ ++ P ++ Q₂, c.size = 0 → c.directive.Inert)
    {s : MachineState} {post : @Post MachineState}
    (h : Eventually (step1 ⟨a + .ofNat (Directives.size Q₁), P⟩ labels₁) post s) :
    Eventually (step1 ⟨a, Q₁ ++ P ++ Q₂⟩ labels₂) post s := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid hstep _ ih =>
    rcases step1_infix_of_sub hL hfit hinert hstep with hs | hstep'
    · exact ih s hs
    · exact .step s mid hstep' ih

end

private theorem Executable.withAddresses_append (a : Int64) (xs ys : List (Kraken.Sized Directive)) :
    Kraken.Executable.withAddresses (⟨a, xs ++ ys⟩ : Executable) =
      Kraken.Executable.withAddresses (⟨a, xs⟩ : Executable) ++
        Kraken.Executable.withAddresses (⟨a + .ofNat (Directives.size xs), ys⟩ : Executable) := by
  induction xs generalizing a <;>
    grind [Kraken.Executable.withAddresses_nil, Kraken.Executable.withAddresses_cons, Int64.ofNat_add,
      Int64.add_assoc]

private theorem Executable.labels_eq_none_iff {a : Int64} {cs : List (Kraken.Sized Directive)} {l : Label} :
    Executable.labels ⟨a, cs⟩ l = none ↔ l ∉ Program.definedLabels (cs.map (·.directive)) := by
  induction cs generalizing a <;>
    grind [Program.definedLabels, Kraken.Executable.withAddresses_nil,
      Kraken.Executable.withAddresses_cons]

private theorem Executable.labels_sub_infix (a : Int64) (Q₁ P Q₂ : List (Kraken.Sized Directive))
    (hdisj : ∀ l ∈ Program.definedLabels (Q₁.map (·.directive)),
      l ∉ Program.definedLabels (P.map (·.directive))) :
    (Executable.labels ⟨a + .ofNat (Directives.size Q₁), P⟩).Sub
      (Executable.labels ⟨a, Q₁ ++ P ++ Q₂⟩) := by
  intro l x h
  have hQ₁ : Executable.labels ⟨a, Q₁⟩ l = none :=
    Executable.labels_eq_none_iff.mpr fun hl =>
      hdisj l hl (Classical.byContradiction fun hn => by simp [Executable.labels_eq_none_iff.mpr hn] at h)
  dsimp only [CoeFun.coe, Executable.labels, Labels.label?] at hQ₁ h ⊢
  simp [List.append_assoc, Executable.withAddresses_append, List.findSome?_append, hQ₁, h]

@[instance_reducible] def Layout.after (layout : Layout) (q : Program) : Layout :=
  { start := layout.start + .ofNat (Directives.size (layout q).program)
    instrSize := fun i => layout.instrSize (i + q.length)
    alignSize := fun i => layout.alignSize (i + q.length) }

theorem Layout.apply_append (layout : Layout) (p q : Program) :
    layout (p ++ q) = ⟨layout.start, (layout p).program ++ ((layout.after p) q).program⟩ := by
  simp only [Kraken.Layout.apply, List.mapIdx_append]
  congr; funext i d; cases d <;> rfl

private theorem Layout.apply_map_directive (layout : Layout) (p : Program) :
    (layout p).program.map (·.directive) = p :=
  List.ext_getElem? fun _ => by grind [Kraken.Layout.apply]

@[simp] theorem Layout.after_nil (layout : Layout) : layout.after [] = layout := by
  cases layout; exact congrArg (Kraken.Layout.mk · _ _) (Int64.add_zero _)

section
variable (layout : Layout) {labels labels₁ labels₂ : Labels} {q₁ p q₂ q : Program} {s : MachineState}
  {d : Directive} {md : MachineData} {mid post : @Post MachineState}

theorem Layout.size_left_lt (h : Directives.size (layout (p ++ q)).program < 2 ^ 64) :
    Directives.size (layout p).program < 2 ^ 64 := by
  simp [Layout.apply_append, Directives.size] at h ⊢; omega

theorem Layout.size_after_lt (h : Directives.size (layout (p ++ q)).program < 2 ^ 64) :
    Directives.size (layout.after p q).program < 2 ^ 64 := by
  simp [Layout.apply_append, Directives.size] at h ⊢; omega

theorem Layout.eventually_infix_of_sub (hL : labels₁.Sub labels₂)
    (hfit : Directives.size (layout (q₁ ++ p ++ q₂)).program < 2 ^ 64)
    (h : Eventually (step1 (layout.after q₁ p) labels₁) post s) :
    Eventually (step1 (layout (q₁ ++ p ++ q₂)) labels₂) post s := by
  have hinert := fun c hc => layout.inert_of_mem (p := q₁ ++ p ++ q₂) (c := c) hc
  rw [Layout.apply_append, Layout.apply_append] at hfit hinert ⊢
  exact _root_.eventually_infix_of_sub hL hfit hinert h

theorem Layout.eventually_append_right (hL : labels₁.Sub labels₂)
    (hfit : Directives.size (layout (p ++ q)).program < 2 ^ 64)
    (h : Eventually (step1 (layout p) labels₁) post s) :
    Eventually (step1 (layout (p ++ q)) labels₂) post s :=
  layout.eventually_infix_of_sub (q₁ := []) hL hfit ((Layout.after_nil layout).symm ▸ h)

theorem Layout.eventually_append_left (hL : labels₁.Sub labels₂)
    (hfit : Directives.size (layout (q ++ p)).program < 2 ^ 64)
    (h : Eventually (step1 (layout.after q p) labels₁) post s) :
    Eventually (step1 (layout (q ++ p)) labels₂) post s := by
  rw [← List.append_nil (q ++ p)] at hfit ⊢
  exact layout.eventually_infix_of_sub hL hfit h

private theorem Layout.labels_sub_infix (q₁ p q₂ : Program)
    (hdisj : ∀ l ∈ q₁.definedLabels, l ∉ p.definedLabels) :
    (Executable.labels (layout.after q₁ p)).Sub (Executable.labels (layout (q₁ ++ p ++ q₂))) := by
  rw [Layout.apply_append, Layout.apply_append]
  exact Executable.labels_sub_infix layout.start (layout q₁).program (layout.after q₁ p).program
    (layout.after (q₁ ++ p) q₂).program (by simpa only [Layout.apply_map_directive])

theorem Layout.eventually_step1_append_right
    (hfit : Directives.size (layout (p ++ q)).program < 2 ^ 64)
    (h : Eventually (step1 (layout p)) post s) :
    Eventually (step1 (layout (p ++ q))) post s :=
  layout.eventually_append_right (by simpa using layout.labels_sub_infix [] p q nofun) hfit h

theorem Layout.eventually_step1_append_left
    (hfit : Directives.size (layout (q ++ p)).program < 2 ^ 64)
    (hdisj : ∀ l ∈ q.definedLabels, l ∉ p.definedLabels)
    (h : Eventually (step1 (layout.after q p)) post s) :
    Eventually (step1 (layout (q ++ p))) post s :=
  layout.eventually_append_left (by simpa using layout.labels_sub_infix q p [] hdisj) hfit h

theorem Layout.eventually_single
    (h : (d.interp labels md ⟨layout.start, layout.start + .ofNat (layout.size d 0)⟩
      (fun s' => .done ⟨s', layout.start + .ofNat (layout.size d 0)⟩)
      (fun a' s' => .done ⟨s', a'⟩)).All post) :
    Eventually (step1 (layout [d]) labels) post ⟨md, layout.start⟩ := by
  refine .step _ post ?_ fun _ => .done _
  simpa [step1, Executable.step, Directives.interp, Kraken.Executable.directivesAtAddress,
    Kraken.Layout.apply] using h

theorem Layout.eventually_seq
    (hfit : Directives.size (layout (p ++ q)).program < 2 ^ 64)
    (h₁ : Eventually (step1 (layout p) labels) mid s)
    (h₂ : ∀ st', mid st' → Eventually (step1 (layout.after p q) labels) post st') :
    Eventually (step1 (layout (p ++ q)) labels) post s :=
  eventually_trans _ _ _ _ (layout.eventually_append_right (.refl labels) hfit h₁)
    fun st' hst' => layout.eventually_append_left (.refl labels) hfit (h₂ st' hst')

end
