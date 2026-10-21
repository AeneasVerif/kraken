module

public import Kraken.X64.WP.Host
public import Kraken.X64.WP.Step
public import Kraken.X64.WP.Embedding
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
   * A jump to a label `f` in `FunDecls` that pushes onto the stack is a call (cf. `Executable.StepOut`).
     `StepOver` steps over the call and applies the weakest precondition of `f`.
   * Any other jump continues the loop if it targets a label in `p` and the stack pointer is at or
     below its value in `s`. Otherwise it leaves `p` and must satisfy `exit`.
2. Taking the least fixpoint of step 1 via `While`, the set of pre states which inevitably
   reach the end address of `p` in a state that satisfies `done`.
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

@[expose] public def Program.IsLabelAddr [Host] (p : Program) (a : Int64) : Prop :=
  ∃ l ∈ p.labels, label l = a

public class FunDecls [Host] where
  funs : List ((p : Program) × Embedding p)

@[expose] public def FunDecls.at [Host] [FunDecls] (a : Int64) : Option ((p : Program) × Embedding p) :=
  FunDecls.funs.find? (·.2.startAddr == a)

public theorem FunDecls.startAddr_of_at [Host] [FunDecls] {a : Int64} {f : (p : Program) × Embedding p}
    (h : FunDecls.at a = some f) : f.2.startAddr = a := by
  simpa using List.find?_some h

open Classical in
@[expose] public def Program.ContinueAtOwnLabel [Host] (p : Program) (s : MachineData)
    («continue» exit : MachineState → Prop) (st : MachineState) : Prop :=
  if p.IsLabelAddr st.pc ∧ st.data.StackAtOrBelow s then «continue» st else exit st

/-- Weakest precondition of a `Program` fragment of the host program. -/
public def Program.wp [Host] [FunDecls] (p : Program) (done exit : MachineState → Prop)
    (s : MachineData) : Prop :=
  let callee a := (FunDecls.at a).map fun f => f.1.wp (fun _ => False)
  ∀ h : Embedding p,
    While (·.pc ≠ h.endAddr)
      (fun «continue» => Host.exe.StepOver callee «continue» (p.ContinueAtOwnLabel s «continue» exit))
      done ⟨s, h.startAddr⟩
inductive_fixpoint

section
variable [Host] [FunDecls]

public theorem Program.wp_eq {p : Program} {done exit : MachineState → Prop} {s : MachineData} :
    p.wp done exit s = ∀ h : Embedding p, While (·.pc ≠ h.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.1.wp (fun _ => False))
        «continue» (p.ContinueAtOwnLabel s «continue» exit))
      done ⟨s, h.startAddr⟩ := by
  rw [Program.wp]

omit [FunDecls] in
public theorem Program.continueAtOwnLabel_mono {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} (hc : ∀ u, c₁ u → c₂ u) (he : ∀ u, e₁ u → e₂ u) {u : MachineState}
    (h : p.ContinueAtOwnLabel s c₁ e₁ u) : p.ContinueAtOwnLabel s c₂ e₂ u := by
  unfold Program.ContinueAtOwnLabel at h ⊢
  by_cases hcond : p.IsLabelAddr u.pc ∧ u.data.StackAtOrBelow s
  · rw [ite_eq_left hcond] at h ⊢; exact hc _ h
  · rw [ite_eq_right hcond] at h ⊢; exact he _ h

omit [FunDecls] in
public theorem Program.continueAtOwnLabel_and {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} {u : MachineState}
    (h₁ : p.ContinueAtOwnLabel s c₁ e₁ u) (h₂ : p.ContinueAtOwnLabel s c₂ e₂ u) :
    p.ContinueAtOwnLabel s (fun u => c₁ u ∧ c₂ u) (fun u => e₁ u ∧ e₂ u) u := by
  unfold Program.ContinueAtOwnLabel at h₁ h₂ ⊢
  by_cases hcond : p.IsLabelAddr u.pc ∧ u.data.StackAtOrBelow s
  · rw [ite_eq_left hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩
  · rw [ite_eq_right hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩

omit [FunDecls] in
public theorem Program.continueAtOwnLabel_of_not_isLabelAddr {p : Program} (h : ∀ a, ¬ p.IsLabelAddr a)
    {s : MachineData} {c e : MachineState → Prop} : p.ContinueAtOwnLabel s c e = e :=
  funext fun u => by simp [Program.ContinueAtOwnLabel, h]

omit [FunDecls] in
public theorem Program.not_isLabelAddr_of_labels_eq_nil {p : Program} (hN : p.labels = []) (a : Int64) :
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
  refine While.imp (fun U y _ hy => Executable.StepOver.imp ?_ hy (fun _ h => h)
    fun u hu => Program.continueAtOwnLabel_mono (fun _ h => h) he hu) (fun y _ h => hd y h) (hw H)
  intro a
  dsimp only
  cases FunDecls.at a with
  | none => exact Option.Rel.none
  | some f => exact Option.Rel.some fun R₁ R₂ s hR hm => hm _ _ (fun _ h => h.elim) hR

public theorem Program.callee_le :
    Executable.CalleeLe (fun a => (FunDecls.at a).map fun f => f.1.wp (fun _ => False))
      (fun a => (FunDecls.at a).map fun f => f.1.wp (fun _ => False)) := by
  intro a
  dsimp only
  cases FunDecls.at a with
  | none => exact Option.Rel.none
  | some f => exact Option.Rel.some fun R₁ R₂ s hR hm => Program.wp_mono (fun _ h => h) hR hm

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
  refine Executable.StepIn.mono (Executable.StepIn.and hU hV) (fun _ h => h) fun st' ⟨h₁, h₂⟩ => ?_
  unfold Executable.StepOut at h₁ h₂ ⊢
  cases hf : FunDecls.at st'.pc with
  | none =>
    simp only [hf, Option.map_none] at h₁ h₂ ⊢
    exact Program.continueAtOwnLabel_and h₁ h₂
  | some f =>
    simp only [hf, Option.map_some] at h₁ h₂ ⊢
    by_cases hb : st'.data.StackBelow y.data
    · simp only [hb, ite_true] at h₁ h₂ ⊢
      refine Program.wp_mono (fun _ h => h.1) (fun u ⟨a, b⟩ => ?_) (h₁ _ _ h₂)
      by_cases hu : u.pc = Host.exe.fallthrough y.pc
      · simp only [hu, ite_true] at a b ⊢
        exact ⟨a, b⟩
      · simp only [hu, ite_false] at a b ⊢
        exact Program.continueAtOwnLabel_and a b
    · simp only [hb, ite_false] at h₁ h₂ ⊢
      exact Program.continueAtOwnLabel_and h₁ h₂

end

section
variable [Host]

public theorem Host.addrOf_ne_of_succ_ne {k n : Nat} (h : Host.addrOf k ≠ Host.addrOf (k + 1)) :
    Host.addrOf k ≠ Host.addrOf (k + 1 + n) := by
  intro he
  have h₁ := Host.sizeBefore_eq_of_addrOf_eq he
  have h₂ := Host.exe.sizeBefore_mono (show k + 1 ≤ k + 1 + n by omega)
  have h₃ := Host.exe.sizeBefore_mono (show k ≤ k + 1 by omega)
  exact h (by simp only [Host.addrOf, Kraken.Executable.addrOf]; congr 2; omega)

public theorem Host.addrOf_succ_ne {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) : Host.addrOf k ≠ Host.addrOf (k + 1) := by
  intro h
  have := Host.sizeBefore_eq_of_addrOf_eq h
  have := Host.exe.sizeBefore_succ (n := k) hc
  omega

public theorem Host.fallthrough_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    Host.exe.fallthrough (Host.addrOf k) = Host.addrOf (k + 1) := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hc hz
  have hk : Host.prog[k]? = some c.directive := by
    rw [Host.exe_getElem?] at hc; grind
  have hzk : Kraken.Layout.size Directive k = c.size := by
    rw [Host.exe_getElem?] at hc; grind
  unfold Executable.fallthrough
  rw [hat, Directives.endPc_append, Directives.endPc_of_size_zero hpre, Host.addrOf_succ hk, hzk]
  rfl

public theorem Host.stepIn_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {s : MachineData} {next jump : MachineState → Prop}
    (h : ∀ ⦃P : MachineState → Prop⦄ ⦃n : MachineData → Effects⦄ ⦃j : Int64 → MachineData → Effects⦄,
      (∀ s', next ⟨s', Host.addrOf (k + 1)⟩ → (n s').All P) → (∀ a s', jump ⟨s', a⟩ → (j a s').All P) →
      (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ n j).All P) :
    Host.exe.StepIn next jump ⟨s, Host.addrOf k⟩ := by
  intro P r j hr hj
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hc hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  have hk : Host.prog[k]? = some c.directive := by
    rw [Host.exe_getElem?] at hc; grind
  have hzk : Kraken.Layout.size Directive k = c.size := by
    rw [Host.exe_getElem?] at hc; grind
  have hsucc : Host.addrOf (k + 1) = Host.addrOf k + .ofNat c.size := by rw [Host.addrOf_succ hk, hzk]
  change (@Directives.interp Host.exe.labels (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _ _).All P
  rw [hat, Directives.interp_inert_append hinert s _ _ P (fun a s => j ⟨s, a⟩)]
  obtain ⟨d, z⟩ := c
  simp only [Directives.interp] at hsucc ⊢
  rw [← hsucc]
  exact h (fun s' hn => hr _ hn) (fun a s' hj' => hj _ hj')

end

section
variable [Host] [FunDecls]

public theorem Program.wp_nil {done exit : MachineState → Prop} {s : MachineData} (hd : ∀ pc, done ⟨s, pc⟩) :
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
  have hk := H.isInfixAt
  have hw := hw (H.ofIsInfixAt (List.isInfixAt_cons_head d p))
  simp only [Program.continueAtOwnLabel_of_not_isLabelAddr nd] at hw
  simp only [Program.continueAtOwnLabel_of_not_isLabelAddr ndp]
  have hd : Host.exe.program[H.start]? =
      some {directive := d, size := Kraken.Layout.size Directive H.start} := by
    rw [Host.exe_getElem?, hk.cons.1]; rfl
  refine While.split (fun y => y.pc ≠ Host.addrOf (H.start + 1) → y.pc = Host.addrOf H.start)
    (fun y hI hc => ?_) (fun U y hI hc hb => ?_) (fun _ => rfl) (While.imp (fun U y _ hb => hb) (fun st hc hst => ?_) hw)
  · have hy := hI hc
    rw [hy]
    show Host.addrOf H.start ≠ Host.addrOf (H.start + (p.length + 1))
    rw [show H.start + (p.length + 1) = H.start + 1 + p.length by omega]
    exact Host.addrOf_ne_of_succ_ne (hy ▸ hc)
  · have hy := hI hc
    have hz : 0 < Kraken.Layout.size Directive H.start := by
      refine Nat.pos_of_ne_zero fun h0 => hc ?_
      rw [hy]; show _ = Host.addrOf (H.start + 0 + 1)
      rw [Host.addrOf_succ hk.cons.1, h0]; simp
    have hft : Host.exe.fallthrough y.pc = Host.addrOf (H.start + 1) := by
      rw [hy]; exact Host.fallthrough_addrOf hd hz
    exact Executable.StepOver.imp Program.callee_le (Executable.StepOver.restrict hb)
      (fun u ⟨hu, hpc⟩ => ⟨hu, fun hne => absurd (hpc.trans hft) hne⟩) fun _ h => h
  · have hpc : st.pc = Host.addrOf (H.start + 1) := by
      have := Classical.not_not.mp hc
      change st.pc = Host.addrOf (H.start + 0 + 1) at this
      simpa using this
    rw [Program.wp_eq] at hst
    have hst := hst (H.ofIsInfixAt (List.isInfixAt_cons_tail d p))
    simp only [Program.continueAtOwnLabel_of_not_isLabelAddr np] at hst
    have hstart : (H.ofIsInfixAt (List.isInfixAt_cons_tail d p)).startAddr = st.pc := by
      show Host.addrOf (H.start + 1) = st.pc
      exact hpc.symm
    have hend : (H.ofIsInfixAt (List.isInfixAt_cons_tail d p)).endAddr = H.endAddr := by
      show Host.addrOf (H.start + 1 + p.length) = Host.addrOf (H.start + (p.length + 1))
      congr 1
      omega
    rw [hstart, hend] at hst
    exact hst
end

section
variable [Host] [FunDecls]

public theorem Program.wp_single {d : Directive} {done exit : MachineState → Prop} {s : MachineData}
    (hw : ∀ (h : Embedding [d]) ⦃P : MachineState → Prop⦄ ⦃next : MachineData → Effects⦄
        ⦃jmp : Int64 → MachineData → Effects⦄,
      (∀ s', done ⟨s', h.endAddr⟩ → (next s').All P) →
      (∀ a s', Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.1.wp (fun _ => False))
        ⟨s, h.startAddr⟩ (fun u => u.pc = h.endAddr ∧ done u) exit ⟨s', a⟩ →
          (jmp a s').All P) →
      (d.interp s ⟨h.startAddr, h.endAddr⟩ next jmp).All P) :
    Program.wp [d] done exit s := by
  rw [Program.wp_eq]
  intro h
  have hk := h.isInfixAt
  have hw := hw h
  have hdk : Host.prog[h.start]? = some d := hk.cons.1
  have hd : Host.exe.program[h.start]? =
      some {directive := d, size := Kraken.Layout.size Directive h.start} := by
    rw [Host.exe_getElem?, hdk]; rfl
  have hend : h.endAddr = Host.addrOf (h.start + 1) := rfl
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive h.start) with h0 | hz
  · have ha : Host.addrOf (h.start + 1) = Host.addrOf h.start := by
      rw [Host.addrOf_succ hdk, h0]; simp
    rw [h0] at hd
    have hq := (Host.inert_of_size_zero (List.mem_of_getElem? hd) s _ (fun s' => .done ⟨s', 0⟩)
      (fun _ s' => .done ⟨s', 1⟩) (fun st => st.pc = 0 → done ⟨st.data, h.endAddr⟩)).mp
      (@hw (fun st => st.pc = 0 → done ⟨st.data, h.endAddr⟩) _ _ (fun _ hq _ => hq)
        fun _ _ _ h => by simp at h)
    refine While.stop (by simp [hend, ha, Embedding.startAddr]) ?_
    have : (⟨s, h.startAddr⟩ : MachineState) = ⟨s, h.endAddr⟩ := by
      simp [hend, ha, Embedding.startAddr]
    rw [this]
    exact hq rfl
  · have nd : ∀ a, ¬ Program.IsLabelAddr [d] a := by
      rintro a ⟨l, hl, -⟩
      cases d with
      | label l' => exact absurd (Host.label_size _ l' hdk) (by omega)
      | _ => simp at hl
    simp only [Program.continueAtOwnLabel_of_not_isLabelAddr nd]
    refine While.step («continue» := fun u => u.pc = h.endAddr ∧ done u)
      (Host.addrOf_succ_ne hd hz ∘ fun h' => h'.trans hend) ?_
      fun u hu => While.stop (by simp [hu.1]) hu.2
    exact Host.stepIn_addrOf hd hz fun P n j hn hj =>
      hw (fun s' hd' => hn s' ⟨hend, hd'⟩) fun a s' h' => hj a s' h'

public theorem Program.step1_of_wp {p : Program} (h : Embedding p) {done exit : MachineState → Prop}
    {s : MachineData} {post : MachineState → Prop} (hw : p.wp done exit s)
    (hd : ∀ u, u.pc = h.endAddr → done u → post u) (he : ∀ u, exit u → post u) :
    Eventually (step1 Host.exe) post ⟨s, h.startAddr⟩ := by
  refine Program.wp.induct
    (fun p done exit s => ∀ (h : Embedding p) (post : MachineState → Prop),
      (∀ u, u.pc = h.endAddr → done u → Eventually (step1 Host.exe) post u) →
      (∀ u, exit u → Eventually (step1 Host.exe) post u) →
      Eventually (step1 Host.exe) post ⟨s, h.startAddr⟩)
    ?_ p done exit s hw h post (fun u hu h => .done _ (hd u hu h)) (fun u h => .done _ (he u h))
  intro p done exit s hw h post hd he
  have hw := While.iff_eventually.mp (hw h)
  generalize (⟨s, h.startAddr⟩ : MachineState) = x at hw ⊢
  induction hw with
  | done y hy => exact hd y (Classical.not_not.mp hy.1) hy.2
  | step y next ht _ ih =>
    have hcal : ∀ u, p.ContinueAtOwnLabel s next exit u → Eventually (step1 Host.exe) post u := fun u hu => by
      unfold Program.ContinueAtOwnLabel at hu
      split at hu
      · exact ih u hu
      · exact he u hu
    refine Eventually.step y _ (Executable.StepIn.all ht.2 (fun u hu => ih u hu) fun st' hst => ?_) fun _ h => h
    unfold Executable.StepOut at hst
    cases hf : FunDecls.at st'.pc with
    | none =>
      simp only [hf, Option.map_none] at hst
      exact hcal _ hst
    | some f =>
      simp only [hf, Option.map_some] at hst
      split at hst
      · have := hst f.2 (Eventually (step1 Host.exe) post) (fun _ _ h => h.elim) fun u hu => by
          split at hu
          · exact .done _ (ih u hu)
          · exact .done _ (hcal u hu)
        have hstart : f.2.startAddr = st'.pc := FunDecls.startAddr_of_at hf
        rw [hstart] at this
        exact eventually_trans _ _ _ _ this fun _ h => h
      · exact hcal _ hst

end
