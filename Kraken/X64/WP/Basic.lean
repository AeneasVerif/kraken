module

public import Kraken.X64.WP.Host
public import Kraken.X64.WP.Step
public import Kraken.While

/-! # Weakest precondition of a fragment of a host program

`Program.wp p done exit s` is the weakest precondition of the fragment `p` in the ambient, laid out
`Host` program, where `done` is the postcondition at the end address of `p` and `exit` is the
postcondition at every other address where control leaves `p`.
This definition is the bridge to `Std.WP` and thus `vcgen`.

The definition of `wp` works by
1. Considering the weakest precondition `Executable.StepOver` of a single directive in the laid out
   executable.
   * Fall-through continues the loop.
   * A jump to a label `f` starting a fragment of `FunDecls` after pushing onto the stack is a call
     (cf. `Executable.StepOut`). `StepOver` steps over the call and applies the weakest precondition
     of `f`.
   * Any other jump continues the loop if it targets a label in `p` and the stack pointer is at or
     below its value in `s`. Otherwise it leaves `p` and must satisfy `exit`.
2. Taking the least fixpoint of step 1 via `While`.
   A state `st` satisfies the fixpoint iff every execution from `st` terminates in one of two ways.
   Either it reaches the end address of `p` for the first time in a state that satisfies `done`,
   or it leaves `p` in a state that satisfies `exit`.
3. Considering every possible way in which the fragment `p` may occur in the `Host` program.
   Only properties can be proved that hold for *all possible embeddings* `Embedding p` of the
   fragment `p`. This ensures proof modularity.

`Program.wp` is an inductive fixpoint, because step 1 uses `wp` of the functions in `FunDecls`.

The `Host` program is a parameter to be able to reason compositionally about function calls.
It is an instance implicit parameter so that uses refer implicitly to an ambient host program
without users needing to specify it explicitly everywhere.

The `FunDecls` instance influences which jumps are considered as calls for `StepOver`.
Undeclared functions are regular jumps and exit if jumping outside the fragment `p`.
-/

public def Program.IsLabelAddr [Host] (p : Program) (a : Int64) : Prop :=
  ∃ l ∈ p.labels, label l = a

open Classical in
@[expose] public def Program.ContinueAtOwnLabel [Host] (p : Program) (s : MachineData)
    («continue» exit : MachineState → Prop) (st : MachineState) : Prop :=
  if p.IsLabelAddr st.pc ∧ st.data.StackAtOrBelow s then «continue» st else exit st

/--
Weakest precondition of a `Program` fragment of the host program.
`p.wp done exit s` holds if every execution of `p` from `s` at the start of `p` reaches the end
of `p` for the first time in a state that satisfies `done`, or leaves `p` in a state that satisfies
`exit`.
-/
public def Program.wp [Host] [FunDecls] (p : Program) (done exit : MachineState → Prop)
    (s : MachineData) : Prop :=
  let callee a := (FunDecls.at a).map fun f => f.prog.wp (fun _ => False)
  ∀ h : Embedding p,
    While (·.pc ≠ h.endAddr)
      (fun «continue» => Host.exe.StepOver callee «continue» (p.ContinueAtOwnLabel s «continue» exit))
      done { data := s, pc := h.startAddr }
inductive_fixpoint

section
variable [Host] [FunDecls]

public theorem Program.wp_eq {p : Program} {done exit : MachineState → Prop} {s : MachineData} :
    p.wp done exit s = ∀ h : Embedding p, While (·.pc ≠ h.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» (p.ContinueAtOwnLabel s «continue» exit))
      done { data := s, pc := h.startAddr } := by
  rw [Program.wp]

omit [FunDecls] in
theorem Program.continueAtOwnLabel_mono {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} (hc : ∀ u, c₁ u → c₂ u) (he : ∀ u, e₁ u → e₂ u) {u : MachineState}
    (h : p.ContinueAtOwnLabel s c₁ e₁ u) : p.ContinueAtOwnLabel s c₂ e₂ u := by
  unfold Program.ContinueAtOwnLabel at h ⊢
  by_cases hcond : p.IsLabelAddr u.pc ∧ u.data.StackAtOrBelow s
  · rw [ite_eq_left hcond] at h ⊢; exact hc _ h
  · rw [ite_eq_right hcond] at h ⊢; exact he _ h

omit [FunDecls] in
theorem Program.continueAtOwnLabel_of_not_isLabelAddr {p : Program} (h : ∀ a, ¬ p.IsLabelAddr a)
    {s : MachineData} {c e : MachineState → Prop} : p.ContinueAtOwnLabel s c e = e :=
  funext fun u => by simp [Program.ContinueAtOwnLabel, h]

omit [FunDecls] in
theorem Program.not_isLabelAddr_of_labels_eq_nil {p : Program} (hN : p.labels = []) (a : Int64) :
    ¬ p.IsLabelAddr a :=
  fun ⟨l, hl, _⟩ => by simp [hN] at hl

public theorem Program.wp_mono {p : Program} {done₁ done₂ exit₁ exit₂ : MachineState → Prop}
    (hd : ∀ u, done₁ u → done₂ u) (he : ∀ u, exit₁ u → exit₂ u) {s : MachineData}
    (h : p.wp done₁ exit₁ s) : p.wp done₂ exit₂ s := by
  refine Program.wp.induct
    (fun p done exit s => ∀ done' exit' : MachineState → Prop, (∀ u, done u → done' u) →
      (∀ u, exit u → exit' u) → p.wp done' exit' s)
    ?_ p done₁ exit₁ s h done₂ exit₂ hd he
  intro p done exit s hw done' exit' hd he
  rw [Program.wp_eq]
  intro H
  refine While.mono (fun U y _ hy => ?_) (fun y _ h => hd y h) (hw H)
  refine Executable.StepOver.mono_map FunDecls.at ?_ (fun _ _ h => h)
    (fun u hu => Program.continueAtOwnLabel_mono (fun _ h => h) he hu) hy
  exact fun _ _ _ _ hR hm => hm _ _ (fun _ h => h.elim) hR


public theorem Program.wp_nil {done exit : MachineState → Prop} {s : MachineData}
    (hd : ∀ pc, done { data := s, pc := pc }) :
    Program.wp [] done exit s := by
  rw [Program.wp_eq]
  intro h
  exact While.stop (by simp [Embedding.endAddr, Embedding.startAddr]) (hd _)

public theorem Program.wp_cons {d : Directive} {p : Program} {done exit : MachineState → Prop} {s : MachineData}
    (hN : Program.labels (d :: p) = []) (hw : Program.wp [d] (fun st => p.wp done exit st.data) exit s) :
    Program.wp (d :: p) done exit s := by
  have nd := Program.not_isLabelAddr_of_labels_eq_nil (p := [d]) (by cases d <;> simp_all)
  have np := Program.not_isLabelAddr_of_labels_eq_nil (p := p) (by cases d <;> simp_all)
  have ndp := Program.not_isLabelAddr_of_labels_eq_nil hN
  rw [Program.wp_eq] at hw ⊢
  intro H
  have hd := H.isInfixAt.cons.1
  have hw := hw H.head
  simp only [Program.continueAtOwnLabel_of_not_isLabelAddr nd] at hw
  simp only [Program.continueAtOwnLabel_of_not_isLabelAddr ndp]
  refine While.split (fun y => y.pc ≠ Host.addrOf (H.start + 1) → y.pc = Host.addrOf H.start)
    (fun y hI hc => ?_) (fun U y hI hc hb => ?_) (fun _ => rfl) (While.mono (fun U y _ hb => hb) (fun st hc hst => ?_) hw)
  · have := hI hc
    grind
  · have hy := hI hc
    have hz : 0 < Kraken.Layout.size Directive H.start := by grind
    have hft : Host.exe.fallthrough y.pc = Host.addrOf (H.start + 1) := by
      rw [hy]; exact Host.fallthrough_addrOf hd hz
    refine Executable.StepOver.mono_map FunDecls.at ?_
      (fun u hpc hu => ⟨hu, fun hne => absurd (hpc.trans hft) hne⟩) (fun _ h => h) hb
    exact fun _ _ _ _ hR h => Program.wp_mono (fun _ h => h) hR h
  · rw [Program.wp_eq] at hst
    have hst := hst H.tail
    simp only [Program.continueAtOwnLabel_of_not_isLabelAddr np] at hst
    rwa [show H.tail.startAddr = st.pc by grind, show H.tail.endAddr = H.endAddr by grind] at hst

public theorem Program.wp_single {d : Directive} {done exit : MachineState → Prop} {s₀ : MachineData}
    (hw : ∀ (h : Embedding [d]) ⦃P : MachineState → Prop⦄ ⦃next : MachineData → Effects⦄
        ⦃jmp : Int64 → MachineData → Effects⦄,
      (∀ s₁, done { data := s₁, pc := h.endAddr } → (next s₁).All P) →
      (∀ a s₁, Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        { data := s₀, pc := h.startAddr } (fun u => u.pc = h.endAddr ∧ done u) exit
        { data := s₁, pc := a } →
          (jmp a s₁).All P) →
      (d.interp s₀ ⟨h.startAddr, h.endAddr⟩ next jmp).All P) :
    Program.wp [d] done exit s₀ := by
  rw [Program.wp_eq]
  intro h
  have hw := hw h
  have hdk : Host.prog[h.start]? = some d := h.isInfixAt.cons.1
  have hend : h.endAddr = Host.addrOf (h.start + 1) := rfl
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive h.start) with h0 | hz
  · have hq := (Host.inert_of_getElem? hdk h0 s₀ _ (fun s₁ => .done { data := s₁, pc := 0 })
      (fun _ s₁ => .done { data := s₁, pc := 1 })
      (fun st => st.pc = 0 → done { data := st.data, pc := h.endAddr })).mp
      (@hw (fun st => st.pc = 0 → done { data := st.data, pc := h.endAddr }) _ _ (fun _ hq _ => hq)
        fun _ _ _ h => by simp at h)
    have ha : h.startAddr = h.endAddr := by grind
    refine While.stop (by simp [ha]) ?_
    rw [ha]
    exact hq rfl
  · have nd : ∀ a, ¬ Program.IsLabelAddr [d] a := by
      rintro a ⟨l, hl, -⟩
      cases d with
      | label l' => exact absurd (Host.label_size _ l' hdk) (by omega)
      | _ => simp at hl
    simp only [Program.continueAtOwnLabel_of_not_isLabelAddr nd]
    refine While.step («continue» := fun u => u.pc = h.endAddr ∧ done u) (by grind) ?_
      fun u hu => While.stop (by simp [hu.1]) hu.2
    exact Host.stepIn_addrOf hdk hz fun P n j hn hj =>
      hw (fun s₁ hd' => hn s₁ ⟨hend, hd'⟩) fun a s₁ h' => hj a s₁ h'

public theorem Program.step1_of_wp {p : Program} (h : Embedding p) {done exit : MachineState → Prop}
    {s : MachineData} {post : MachineState → Prop} (hw : p.wp done exit s)
    (hd : ∀ u, u.pc = h.endAddr → done u → post u) (he : ∀ u, exit u → post u) :
    Eventually (step1 Host.exe) post { data := s, pc := h.startAddr } := by
  refine Program.wp.induct
    (fun p done exit s => ∀ (h : Embedding p) (post : MachineState → Prop),
      (∀ u, u.pc = h.endAddr → done u → Eventually (step1 Host.exe) post u) →
      (∀ u, exit u → Eventually (step1 Host.exe) post u) →
      Eventually (step1 Host.exe) post { data := s, pc := h.startAddr })
    ?_ p done exit s hw h post (fun u hu h => .done _ (hd u hu h)) (fun u h => .done _ (he u h))
  intro p done exit s hw h post hd he
  have hw := While.iff_eventually.mp (hw h)
  generalize ({ data := s, pc := h.startAddr } : MachineState) = x at hw ⊢
  induction hw with
  | done y hy => exact hd y (Classical.not_not.mp hy.1) hy.2
  | step y next ht _ ih =>
    have hcal : ∀ u, p.ContinueAtOwnLabel s next exit u → Eventually (step1 Host.exe) post u := fun u hu => by
      unfold Program.ContinueAtOwnLabel at hu
      split at hu
      · exact ih u hu
      · exact he u hu
    refine Eventually.step y _ (Executable.StepIn.all ht.2 (fun u hu => ih u hu) fun st₁ hst => ?_) fun _ h => h
    unfold Executable.StepOut at hst
    cases hf : FunDecls.at st₁.pc with
    | none =>
      simp only [hf, Option.map_none] at hst
      exact hcal _ hst
    | some f =>
      simp only [hf, Option.map_some] at hst
      split at hst
      · have := hst f.embedding (Eventually (step1 Host.exe) post) (fun _ _ h => h.elim) fun u hu => by
          split at hu
          · exact .done _ (ih u hu)
          · exact .done _ (hcal u hu)
        have hstart : f.embedding.startAddr = st₁.pc := FunDecls.startAddr_of_at hf
        rw [hstart] at this
        exact eventually_trans _ _ _ _ this fun _ h => h
      · exact hcal _ hst

end
