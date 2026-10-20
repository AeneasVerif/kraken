module

public import Kraken.X64.WP.Host
public import Kraken.X64.WP.Step

/-
# Weakest precondition of a fragment of a host program

`Program.wp p done exit s` is the weakest precondition of the fragment `p` in the ambient `Host`
program, for every embedding of `p`.
This definition is the bridge to `Std.WP` and thus `vcgen`.

The run of `p` is a `While` loop over `Executable.StepOver`, which steps over calls to the functions in
`FunDecls`. A fall-through successor continues the loop. A jump successor continues the loop at an
internal target of `p` while the run still owns the stack, and leaves the loop with `exit` otherwise.
The loop stops at the end address of `p`, where `done` must hold.
-/

@[expose] public def While {σ : Type} (cond : σ → Prop) (body : (σ → Prop) → σ → Prop) (done : σ → Prop) :
    σ → Prop :=
  Eventually (fun st «continue» => cond st ∧ body «continue» st) (fun st => ¬ cond st ∧ done st)

section
variable {σ : Type} {cond : σ → Prop} {body : (σ → Prop) → σ → Prop} {done : σ → Prop}

public theorem While.stop {x : σ} (hc : ¬ cond x) (hd : done x) : While cond body done x :=
  Eventually.done _ ⟨hc, hd⟩

public theorem While.step {x : σ} {«continue» : σ → Prop} (hc : cond x) (hb : body «continue» x)
    (h : ∀ y, «continue» y → While cond body done y) : While cond body done x :=
  Eventually.step _ _ ⟨hc, hb⟩ h

public theorem While.imp {body₂ : (σ → Prop) → σ → Prop} {done₂ : σ → Prop}
    (hb : ∀ U y, cond y → body U y → body₂ U y) (hd : ∀ y, ¬ cond y → done y → done₂ y) {x : σ}
    (h : While cond body done x) : While cond body₂ done₂ x := by
  induction h with
  | done y h => exact Eventually.done y ⟨h.1, hd y h.1 h.2⟩
  | step y mid ht _ ih => exact Eventually.step y mid ⟨ht.1, hb mid y ht.1 ht.2⟩ ih

public theorem While.seq {cond₂ : σ → Prop} (I : σ → Prop) (hcond : ∀ y, I y → cond y → cond₂ y)
    (hI : ∀ U y, I y → cond y → body U y → body (fun z => U z ∧ I z) y) {x : σ} (hx : I x)
    (h : While cond body (While cond₂ body done) x) : While cond₂ body done x := by
  induction h with
  | done _ h => exact h.2
  | step y mid ht _ ih =>
    exact Eventually.step y (fun z => mid z ∧ I z) ⟨hcond y hx ht.1, hI mid y hx ht.1 ht.2⟩
      fun z hz => ih z hz.1 hz.2

public theorem While.and {body₁ body₂ : (σ → Prop) → σ → Prop} {done₁ done₂ : σ → Prop}
    (hb : ∀ U V y, cond y → body₁ U y → body₂ V y → body (fun z => U z ∧ V z) y) {x : σ}
    (h₁ : While cond body₁ done₁ x) (h₂ : While cond body₂ done₂ x) :
    While cond body (fun z => done₁ z ∧ done₂ z) x := by
  induction h₁ with
  | done y hd => cases h₂ with
    | done _ hd₂ => exact Eventually.done _ ⟨hd.1, hd.2, hd₂.2⟩
    | step _ _ ht _ => exact absurd ht.1 hd.1
  | step y U₁ ht₁ _ ih => cases h₂ with
    | done _ hd₂ => exact absurd ht₁.1 hd₂.1
    | step _ U₂ ht₂ hr₂ =>
      exact Eventually.step _ (fun z => U₁ z ∧ U₂ z) ⟨ht₁.1, hb _ _ _ ht₁.1 ht₁.2 ht₂.2⟩
        fun z ⟨hz₁, hz₂⟩ => ih z hz₁ (hr₂ z hz₂)

public theorem While.not_of_inv (Inv : σ → Prop) (hdone : ∀ y, Inv y → ¬ cond y → ¬ done y)
    (hstep : ∀ U y, Inv y → cond y → body U y → ∃ z, U z ∧ Inv z) {x : σ} (hx : Inv x) :
    ¬ While cond body done x := by
  intro h
  unfold While at h
  induction h with
  | done y h => exact hdone y hx h.1 h.2
  | step y U ht _ ih =>
    obtain ⟨z, hz, hiz⟩ := hstep U y hx ht.1 ht.2
    exact ih z hz hiz

open Lean.Order in
@[partial_fixpoint_monotone] public theorem While.monotone {α : Type} [PartialOrder α] {init : σ}
    (f : α → (σ → Prop) → σ → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => While cond (f x) done init) := by
  intro x y hxy hx
  induction hx with
  | done st hp => exact Eventually.done _ hp
  | step st U ht _ ih => exact Eventually.step _ U ⟨ht.1, hf _ _ hxy U st ht.2⟩ ih

end

public theorem Effects.All_mono {P₁ P₂ : MachineState → Prop} {e : Effects}
    (h : ∀ st, P₁ st → P₂ st) (h₁ : e.All P₁) : e.All P₂ := by
  induction e with
  | done a => exact h _ h₁
  | unimplemented | gp_unaligned | nonmem_load | nonmem_store => exact h₁
  | undefined ret ih => exact fun v => ih v (h₁ v)
  | require_read_access _ _ ok ih => exact ih () h₁
  | require_write_access _ _ ok ih => exact ih () h₁
  | require_exec_access _ ok ih => exact ih () h₁

public theorem step1_mono [Layout] {e : Executable} {x : MachineState} {P₁ P₂ : MachineState → Prop}
    (h : ∀ st, P₁ st → P₂ st) (h₁ : step1 e x P₁) : step1 e x P₂ :=
  Effects.All_mono h h₁

public theorem Effects.All_and {P₁ P₂ : MachineState → Prop} {e : Effects}
    (h₁ : e.All P₁) (h₂ : e.All P₂) : e.All fun st => P₁ st ∧ P₂ st := by
  induction e with
  | done a => exact ⟨h₁, h₂⟩
  | unimplemented | gp_unaligned | nonmem_load | nonmem_store => exact h₁
  | undefined ret ih => exact fun v => ih v (h₁ v) (h₂ v)
  | require_read_access _ _ ok ih => exact ih () h₁ h₂
  | require_write_access _ _ ok ih => exact ih () h₁ h₂
  | require_exec_access _ ok ih => exact ih () h₁ h₂

open Lean.Order in
@[partial_fixpoint_monotone] public theorem step1_monotone [Layout] {α : Type} [PartialOrder α]
    {e : Executable} {st : MachineState} (f : α → MachineState → ImplicationOrder) (h : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => step1 e st (f x)) :=
  fun _ _ hxy => Effects.All_mono fun st' => h _ _ hxy st'


public theorem List.IsInfixAt.trans {α : Type} {l₁ l₂ l₃ : List α} {i j : Nat}
    (h₁ : l₁.IsInfixAt l₂ i) (h₂ : l₂.IsInfixAt l₃ j) : l₁.IsInfixAt l₃ (j + i) := by
  rw [List.isInfixAt_iff_getElem?] at *
  intro n hn
  have := h₁ n hn
  have := h₂ (i + n) (by grind [List.getElem?_eq_some_iff])
  grind

public theorem List.isInfixAt_cons_head {α : Type} (d : α) (p : List α) : [d].IsInfixAt (d :: p) 0 :=
  ⟨p, rfl⟩

public theorem List.isInfixAt_cons_tail {α : Type} (d : α) (p : List α) : p.IsInfixAt (d :: p) 1 :=
  ⟨[], List.append_nil p⟩

public structure Embedding [Host] (p : Program) where
  start : Nat
  isInfixAt : p.IsInfixAt Host.prog start

public class Embeds [Host] (p : Program) where
  embedding : Embedding p

@[expose] public def Embedding.ofIsInfixAt [Host] {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : Embedding p :=
  ⟨e.start + i, List.IsInfixAt.trans h e.isInfixAt⟩

public abbrev Embeds.ofIsInfixAt [Host] {p q : Program} (hq : Embeds q) {i : Nat}
    (h : p.IsInfixAt q i) : Embeds p := ⟨hq.embedding.ofIsInfixAt h⟩

public abbrev Embeds.ofIsInfix [Host] {p : Program} (h : p.IsInfix Host.prog) : Embeds p :=
  ⟨⟨p.infixIdx Host.prog h, List.isInfixAt_infixIdx h⟩⟩

public class NoLabels (p : Program) : Prop where
  out : p.labels = []

public instance : NoLabels [] := ⟨rfl⟩

public instance {i : Instr} {p : Program} [h : NoLabels p] : NoLabels (.instr i :: p) :=
  ⟨by simpa using h.out⟩

@[expose] public def Program.InternalTarget [Host] (p : Program) (a : Int64) : Prop :=
  ∃ l ∈ p.labels, label l = a

public structure Fragment [Host] where
  prog : Program
  [embeds : Embeds prog]

section
variable [Host]

@[expose] public def Embedding.startAddr {p : Program} (e : Embedding p) : Int64 := Host.addrOf e.start

@[expose] public def Embedding.endAddr {p : Program} (e : Embedding p) : Int64 :=
  Host.addrOf (e.start + p.length)

public abbrev Fragment.startAddr (f : Fragment) : Int64 := f.embeds.embedding.startAddr

end

public class FunDecls [Host] where
  funs : List Fragment

public instance [Host] : FunDecls := ⟨[]⟩

@[expose] public def FunDecls.at [Host] [FunDecls] (a : Int64) : Option Fragment :=
  FunDecls.funs.find? (·.startAddr == a)

@[simp, grind =] public theorem FunDecls.at_default [Host] (a : Int64) :
    (FunDecls.at a : Option Fragment) = none := rfl

public theorem FunDecls.startAddr_of_at [Host] [FunDecls] {a : Int64} {f : Fragment}
    (h : FunDecls.at a = some f) : f.startAddr = a := by
  simpa using List.find?_some h

open Classical in
@[expose] public def Program.ContinueOnInternalExit [Host] (p : Program) (s : MachineData)
    («continue» exit : MachineState → Prop) (st : MachineState) : Prop :=
  if p.InternalTarget st.pc ∧ st.data.StackAtOrBelow s then «continue» st else exit st

/-- Weakest precondition of a `Program` fragment of the host program. -/
public def Program.wp [Host] [FunDecls] (p : Program) (done exit : MachineState → Prop)
    (s : MachineData) : Prop :=
  let callee a := (FunDecls.at a).map fun f => f.prog.wp (fun _ => False)
  ∀ [h : Embeds p],
    While (·.pc ≠ h.embedding.endAddr)
      (fun «continue» => Host.exe.StepOver callee «continue» (p.ContinueOnInternalExit s «continue» exit))
      done ⟨s, h.embedding.startAddr⟩
inductive_fixpoint

section
variable [Host] [FunDecls]

public theorem Program.wp_eq {p : Program} {done exit : MachineState → Prop} {s : MachineData} :
    p.wp done exit s = ∀ [h : Embeds p], While (·.pc ≠ h.embedding.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» (p.ContinueOnInternalExit s «continue» exit))
      done ⟨s, h.embedding.startAddr⟩ := by
  rw [Program.wp]

omit [FunDecls] in
public theorem Program.continueOnInternalExit_mono {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} (hc : ∀ u, c₁ u → c₂ u) (he : ∀ u, e₁ u → e₂ u) {u : MachineState}
    (h : p.ContinueOnInternalExit s c₁ e₁ u) : p.ContinueOnInternalExit s c₂ e₂ u := by
  unfold Program.ContinueOnInternalExit at h ⊢
  by_cases hcond : p.InternalTarget u.pc ∧ u.data.StackAtOrBelow s
  · rw [if_pos hcond] at h ⊢; exact hc _ h
  · rw [if_neg hcond] at h ⊢; exact he _ h

omit [FunDecls] in
public theorem Program.continueOnInternalExit_and {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} {u : MachineState}
    (h₁ : p.ContinueOnInternalExit s c₁ e₁ u) (h₂ : p.ContinueOnInternalExit s c₂ e₂ u) :
    p.ContinueOnInternalExit s (fun u => c₁ u ∧ c₂ u) (fun u => e₁ u ∧ e₂ u) u := by
  unfold Program.ContinueOnInternalExit at h₁ h₂ ⊢
  by_cases hcond : p.InternalTarget u.pc ∧ u.data.StackAtOrBelow s
  · rw [if_pos hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩
  · rw [if_neg hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩

omit [FunDecls] in
public theorem Program.continueOnInternalExit_of_noInternal {p : Program} (h : ∀ a, ¬ p.InternalTarget a)
    {s : MachineData} {c e : MachineState → Prop} : p.ContinueOnInternalExit s c e = e :=
  funext fun u => by simp [Program.ContinueOnInternalExit, h]

omit [FunDecls] in
public theorem Program.noInternal_of_noLabels {p : Program} (hN : p.labels = []) (a : Int64) :
    ¬ p.InternalTarget a :=
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
    fun u hu => Program.continueOnInternalExit_mono (fun _ h => h) he hu) (fun y _ h => hd y h) hw
  intro a
  dsimp only
  cases FunDecls.at a with
  | none => exact Option.Rel.none
  | some f => exact Option.Rel.some fun R₁ R₂ s hR hm => hm _ _ (fun _ h => h.elim) hR

public theorem Program.callee_le :
    Executable.CalleeLe (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
      (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False)) := by
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
  refine While.and (fun U V y _ hU hV => ?_) hw hw'
  refine Executable.StepIn.mono (Executable.StepIn.and hU hV) (fun _ h => h) fun st' ⟨h₁, h₂⟩ => ?_
  unfold Executable.StepOut at h₁ h₂ ⊢
  cases hf : FunDecls.at st'.pc with
  | none =>
    simp only [hf, Option.map_none] at h₁ h₂ ⊢
    exact Program.continueOnInternalExit_and h₁ h₂
  | some f =>
    simp only [hf, Option.map_some] at h₁ h₂ ⊢
    by_cases hb : st'.data.StackBelow y.data
    · simp only [hb, ite_true] at h₁ h₂ ⊢
      refine Program.wp_mono (fun _ h => h.1) (fun u ⟨a, b⟩ => ?_) (h₁ _ _ h₂)
      by_cases hu : u.pc = Host.exe.fallthrough y.pc
      · simp only [hu, ite_true] at a b ⊢
        exact ⟨a, b⟩
      · simp only [hu, ite_false] at a b ⊢
        exact Program.continueOnInternalExit_and a b
    · simp only [hb, ite_false] at h₁ h₂ ⊢
      exact Program.continueOnInternalExit_and h₁ h₂

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

public theorem Host.addrOf_ne {i m j : Nat} {ins : Instr} (hm : Host.prog[m]? = some (.instr ins))
    (hpad : ¬ ins.IsPadding) (him : i ≤ m) (hmj : m < j) : Host.addrOf i ≠ Host.addrOf j := by
  intro he
  have hz := Host.instr_size_pos _ _ hm hpad
  have hs := Host.exe.sizeBefore_succ (n := m) (c := {directive := .instr ins, size := Kraken.Layout.size Directive m})
    (by rw [Host.exe_getElem?, hm]; rfl)
  have h₁ := Host.sizeBefore_eq_of_addrOf_eq he
  have h₂ := Host.exe.sizeBefore_mono him
  have h₃ := Host.exe.sizeBefore_mono (show m + 1 ≤ j by omega)
  dsimp only at hs
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

public theorem Host.interp_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) (s : MachineData)
    (ret jmp : MachineState → Effects) (P : MachineState → Prop) :
    (@Directives.interp Host.exe.labels (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k)
        (fun a s => ret ⟨s, a⟩) (fun a s => jmp ⟨s, a⟩)).All P ↔
      (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun s' => ret ⟨s', Host.addrOf (k + 1)⟩)
        (fun a s' => jmp ⟨s', a⟩)).All P := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hc hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  have hk : Host.prog[k]? = some c.directive := by
    rw [Host.exe_getElem?] at hc; grind
  have hzk : Kraken.Layout.size Directive k = c.size := by
    rw [Host.exe_getElem?] at hc; grind
  have hsucc : Host.addrOf (k + 1) = Host.addrOf k + .ofNat c.size := by rw [Host.addrOf_succ hk, hzk]
  rw [hat, Directives.interp_inert_append hinert s _ _ P (fun a s => jmp ⟨s, a⟩)]
  obtain ⟨d, z⟩ := c
  simp only [Directives.interp] at hsucc ⊢
  rw [← hsucc]

public theorem Host.stepIn_elim {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {s : MachineData} {next jump : MachineState → Prop}
    (h : Host.exe.StepIn next jump ⟨s, Host.addrOf k⟩) {P : MachineState → Prop} {ret jmp : MachineState → Effects}
    (hr : ∀ st, next st → (ret st).All P) (hj : ∀ st, jump st → (jmp st).All P) :
    (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun s' => ret ⟨s', Host.addrOf (k + 1)⟩)
      (fun a s' => jmp ⟨s', a⟩)).All P :=
  (Host.interp_addrOf hc hz s ret jmp P).mp (h hr hj)

public theorem Host.step1_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {s : MachineData} {P : MachineState → Prop}
    (h : (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All P) :
    step1 Host.exe ⟨s, Host.addrOf k⟩ P :=
  (Host.interp_addrOf hc hz s .done .done P).mpr h

end

section
variable [Host] [FunDecls]

public theorem Program.wp_nil {done exit : MachineState → Prop} {s : MachineData} (hd : ∀ pc, done ⟨s, pc⟩) :
    Program.wp [] done exit s := by
  rw [Program.wp_eq]
  intro h
  exact While.stop (by simp [Embedding.endAddr, Embedding.startAddr]) (hd _)

end

section
variable [Host]

@[grind =] public theorem Embedding.endAddr_def {p : Program} (e : Embedding p) :
    e.endAddr = Host.addrOf (e.start + p.length) := rfl

@[grind =] public theorem Embedding.startAddr_def {p : Program} (e : Embedding p) :
    e.startAddr = Host.addrOf e.start := rfl

@[grind =] public theorem Embedding.start_ofIsInfixAt {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : (e.ofIsInfixAt h).start = e.start + i := rfl

@[grind =] public theorem Embedding.endAddr_cons_head (d : Directive) (p : Program) (e : Embedding (d :: p)) :
    (e.ofIsInfixAt (List.isInfixAt_cons_head d p)).endAddr =
      (e.ofIsInfixAt (List.isInfixAt_cons_tail d p)).startAddr :=
  rfl

@[grind =] public theorem Embedding.startAddr_label_cons (l : Label) (p : Program)
    (e : Embedding (.label l :: p)) : e.startAddr = label l :=
  (Host.label_eq (i := 0) e.isInfixAt rfl).symm

@[grind =_] public theorem Embedding.startAddr_label_cons_tail (l : Label) (p : Program)
    (t : Embedding (.label l :: p)) :
    (t.ofIsInfixAt (List.isInfixAt_cons_tail (.label l) p)).startAddr = t.startAddr := by
  have hk : Host.prog[t.start + 0]? = some (.label l) := by
    rw [List.isInfixAt_iff_getElem?.mp t.isInfixAt 0 (by simp)]; rfl
  simp only [Embedding.startAddr, Embedding.start_ofIsInfixAt, Host.addrOf_succ hk, Host.label_size _ _ hk]
  simp

end

section
variable [Host]

public theorem Host.lt_length_of_addrOf_ne {j e : Nat} (hje : j ≤ e)
    (hne : Host.addrOf j ≠ Host.addrOf e) : j < Host.prog.length := by
  refine Nat.lt_of_not_ge fun hj => hne ?_
  have hlen : Host.exe.program.length = Host.prog.length := by
    simp [Host.exe, Kraken.Layout.apply]
  simp only [Host.addrOf, Kraken.Executable.addrOf, Kraken.Executable.sizeBefore,
    List.take_of_length_le (show Host.exe.program.length ≤ j by omega),
    List.take_of_length_le (show Host.exe.program.length ≤ e by omega)]

public theorem Host.at_of_ne {j e : Nat} (hje : j ≤ e) (hne : Host.addrOf j ≠ Host.addrOf e) :
    ∃ m c, j ≤ m ∧ m < e ∧ Host.exe.program[m]? = some c ∧ 0 < c.size ∧ Host.addrOf m = Host.addrOf j := by
  induction h : e - j generalizing j with
  | zero => exact absurd (by rw [show j = e by omega]) hne
  | succ n ih =>
    have hje' : j < e := Nat.lt_of_le_of_ne hje fun h => hne (by rw [h])
    have hjl := Host.lt_length_of_addrOf_ne hje hne
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (by simpa using hjl : Host.prog[j]?.isSome)
    have hc : Host.exe.program[j]? = some {directive := d, size := Kraken.Layout.size Directive j} := by
      rw [Host.exe_getElem?, hd]; rfl
    rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive j) with h0 | hz
    · have ha : Host.addrOf (j + 1) = Host.addrOf j := by rw [Host.addrOf_succ hd, h0]; simp
      obtain ⟨m, c, hm₁, hm₂, hm₃, hm₄, hm₅⟩ := ih (j := j + 1) hje' (ha ▸ hne) (by omega)
      exact ⟨m, c, by omega, hm₂, hm₃, hm₄, hm₅.trans ha⟩
    · exact ⟨j, _, Nat.le_refl _, hje', hc, hz, rfl⟩

public theorem Host.addrOf_ne_of_le {j e f : Nat} (hje : j ≤ e) (hef : e ≤ f)
    (hne : Host.addrOf j ≠ Host.addrOf e) : Host.addrOf j ≠ Host.addrOf f := by
  intro h
  have h₁ := Host.sizeBefore_eq_of_addrOf_eq h
  have h₂ := Host.exe.sizeBefore_mono hje
  have h₃ := Host.exe.sizeBefore_mono hef
  exact hne (by simp only [Host.addrOf, Kraken.Executable.addrOf]; congr 2; omega)

end

section
variable [Host] [FunDecls]

public theorem Program.wp_cons {d : Directive} {p : Program} {done exit : MachineState → Prop} {s : MachineData}
    (hN : Program.labels (d :: p) = []) (hw : Program.wp [d] (fun st => p.wp done exit st.data) exit s) :
    Program.wp (d :: p) done exit s := by
  have nd := Program.noInternal_of_noLabels (p := [d]) (by cases d <;> simp_all)
  have np := Program.noInternal_of_noLabels (p := p) (by cases d <;> simp_all)
  have ndp := Program.noInternal_of_noLabels hN
  rw [Program.wp_eq] at hw ⊢
  intro H
  have hk := H.embedding.isInfixAt
  have hw := @hw (.ofIsInfixAt H (List.isInfixAt_cons_head d p))
  simp only [Program.continueOnInternalExit_of_noInternal nd] at hw
  simp only [Program.continueOnInternalExit_of_noInternal ndp]
  have hd : Host.exe.program[H.embedding.start]? =
      some {directive := d, size := Kraken.Layout.size Directive H.embedding.start} := by
    rw [Host.exe_getElem?, hk.cons.1]; rfl
  refine While.seq (fun y => y.pc ≠ Host.addrOf (H.embedding.start + 1) → y.pc = Host.addrOf H.embedding.start)
    (fun y hI hc => ?_) (fun U y hI hc hb => ?_) (fun _ => rfl) (While.imp (fun U y _ hb => hb) (fun st hc hst => ?_) hw)
  · have hy := hI hc
    rw [hy]
    show Host.addrOf H.embedding.start ≠ Host.addrOf (H.embedding.start + (p.length + 1))
    rw [show H.embedding.start + (p.length + 1) = H.embedding.start + 1 + p.length by omega]
    exact Host.addrOf_ne_of_succ_ne (hy ▸ hc)
  · have hy := hI hc
    have hz : 0 < Kraken.Layout.size Directive H.embedding.start := by
      refine Nat.pos_of_ne_zero fun h0 => hc ?_
      rw [hy]; show _ = Host.addrOf (H.embedding.start + 0 + 1)
      rw [Host.addrOf_succ hk.cons.1, h0]; simp
    have hft : Host.exe.fallthrough y.pc = Host.addrOf (H.embedding.start + 1) := by
      rw [hy]; exact Host.fallthrough_addrOf hd hz
    exact Executable.StepOver.imp Program.callee_le (Executable.StepOver.restrict hb)
      (fun u ⟨hu, hpc⟩ => ⟨hu, fun hne => absurd (hpc.trans hft) hne⟩) fun _ h => h
  · have hpc : st.pc = Host.addrOf (H.embedding.start + 1) := by
      have := Classical.not_not.mp hc
      change st.pc = Host.addrOf (H.embedding.start + 0 + 1) at this
      simpa using this
    rw [Program.wp_eq] at hst
    have hst := @hst (.ofIsInfixAt H (List.isInfixAt_cons_tail d p))
    simp only [Program.continueOnInternalExit_of_noInternal np] at hst
    have hstart : (Embeds.ofIsInfixAt H (List.isInfixAt_cons_tail d p)).embedding.startAddr = st.pc := by
      show Host.addrOf (H.embedding.start + 1) = st.pc
      exact hpc.symm
    have hend : (Embeds.ofIsInfixAt H (List.isInfixAt_cons_tail d p)).embedding.endAddr = H.embedding.endAddr := by
      show Host.addrOf (H.embedding.start + 1 + p.length) = Host.addrOf (H.embedding.start + (p.length + 1))
      congr 1
      omega
    rw [hstart, hend] at hst
    exact hst
end

section
variable [Host] [FunDecls]

public theorem Program.wp_single {d : Directive} {done exit : MachineState → Prop} {s : MachineData}
    (hw : ∀ (h : Embeds [d]) ⦃P : MachineState → Prop⦄ ⦃next : MachineData → Effects⦄
        ⦃jmp : Int64 → MachineData → Effects⦄,
      (∀ s', done ⟨s', h.embedding.endAddr⟩ → (next s').All P) →
      (∀ a s', Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        ⟨s, h.embedding.startAddr⟩ (fun u => u.pc = h.embedding.endAddr ∧ done u) exit ⟨s', a⟩ →
          (jmp a s').All P) →
      (d.interp s ⟨h.embedding.startAddr, h.embedding.endAddr⟩ next jmp).All P) :
    Program.wp [d] done exit s := by
  rw [Program.wp_eq]
  intro h
  have hk := h.embedding.isInfixAt
  have hw := hw h
  have hdk : Host.prog[h.embedding.start]? = some d := hk.cons.1
  have hd : Host.exe.program[h.embedding.start]? =
      some {directive := d, size := Kraken.Layout.size Directive h.embedding.start} := by
    rw [Host.exe_getElem?, hdk]; rfl
  have hend : h.embedding.endAddr = Host.addrOf (h.embedding.start + 1) := rfl
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive h.embedding.start) with h0 | hz
  · have ha : Host.addrOf (h.embedding.start + 1) = Host.addrOf h.embedding.start := by
      rw [Host.addrOf_succ hdk, h0]; simp
    rw [h0] at hd
    have hq := (Host.inert_of_size_zero (List.mem_of_getElem? hd) s _ (fun s' => .done ⟨s', 0⟩)
      (fun _ s' => .done ⟨s', 1⟩) (fun st => st.pc = 0 → done ⟨st.data, h.embedding.endAddr⟩)).mp
      (@hw (fun st => st.pc = 0 → done ⟨st.data, h.embedding.endAddr⟩) _ _ (fun _ hq _ => hq)
        fun _ _ _ h => by simp at h)
    refine While.stop (by simp [hend, ha, Embedding.startAddr]) ?_
    have : (⟨s, h.embedding.startAddr⟩ : MachineState) = ⟨s, h.embedding.endAddr⟩ := by
      simp [hend, ha, Embedding.startAddr]
    rw [this]
    exact hq rfl
  · have nd : ∀ a, ¬ Program.InternalTarget [d] a := by
      rintro a ⟨l, hl, -⟩
      cases d with
      | label l' => exact absurd (Host.label_size _ l' hdk) (by omega)
      | _ => simp at hl
    simp only [Program.continueOnInternalExit_of_noInternal nd]
    refine While.step («continue» := fun u => u.pc = h.embedding.endAddr ∧ done u)
      (Host.addrOf_succ_ne hd hz ∘ fun h' => h'.trans hend) ?_
      fun u hu => While.stop (by simp [hu.1]) hu.2
    exact Host.stepIn_addrOf hd hz fun P n j hn hj =>
      hw (fun s' hd' => hn s' ⟨hend, hd'⟩) fun a s' h' => hj a s' h'

public theorem Program.step1_of_wp {p : Program} [h : Embeds p] {done exit : MachineState → Prop}
    {s : MachineData} {post : MachineState → Prop} (hw : p.wp done exit s)
    (hd : ∀ u, u.pc = h.embedding.endAddr → done u → post u) (he : ∀ u, exit u → post u) :
    Eventually (step1 Host.exe) post ⟨s, h.embedding.startAddr⟩ := by
  refine Program.wp.induct
    (fun p done exit s => ∀ (h : Embeds p) (post : MachineState → Prop),
      (∀ u, u.pc = h.embedding.endAddr → done u → Eventually (step1 Host.exe) post u) →
      (∀ u, exit u → Eventually (step1 Host.exe) post u) →
      Eventually (step1 Host.exe) post ⟨s, h.embedding.startAddr⟩)
    ?_ p done exit s hw h post (fun u hu h => .done _ (hd u hu h)) (fun u h => .done _ (he u h))
  intro p done exit s hw h post hd he
  have hw := @hw h
  unfold While at hw
  generalize (⟨s, h.embedding.startAddr⟩ : MachineState) = x at hw ⊢
  induction hw with
  | done y hy => exact hd y (Classical.not_not.mp hy.1) hy.2
  | step y next ht _ ih =>
    have hcie : ∀ u, p.ContinueOnInternalExit s next exit u → Eventually (step1 Host.exe) post u := fun u hu => by
      unfold Program.ContinueOnInternalExit at hu
      split at hu
      · exact ih u hu
      · exact he u hu
    refine Eventually.step y _ (Executable.StepIn.all ht.2 (fun u hu => ih u hu) fun st' hst => ?_) fun _ h => h
    unfold Executable.StepOut at hst
    cases hf : FunDecls.at st'.pc with
    | none =>
      simp only [hf, Option.map_none] at hst
      exact hcie _ hst
    | some f =>
      simp only [hf, Option.map_some] at hst
      split at hst
      · have := hst f.embeds (Eventually (step1 Host.exe) post) (fun _ _ h => h.elim) fun u hu => by
          split at hu
          · exact .done _ (ih u hu)
          · exact .done _ (hcie u hu)
        have hstart : f.embeds.embedding.startAddr = st'.pc := FunDecls.startAddr_of_at hf
        rw [hstart] at this
        exact eventually_trans _ _ _ _ this fun _ h => h
      · exact hcie _ hst

end

section
variable [Host] [FunDecls]

public theorem Program.run_infix {p q : Program} [Hp : Embeds p] {o : Nat} (hq : q.IsInfixAt p o)
    (hlenq : o + q.length ≤ p.length) (hq₀ : ∀ a, ¬ q.InternalTarget a) {s₀ : MachineData}
    {done exit done' exit' : MachineState → Prop} {s : MachineData} (hw : q.wp done' exit' s)
    (hQ : ∀ st, st.pc = Host.addrOf (Hp.embedding.start + o + q.length) → done' st →
      While (·.pc ≠ Hp.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done st)
    (hE : ∀ st, exit' st → p.ContinueOnInternalExit s₀
      (While (·.pc ≠ Hp.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done) exit st) :
    While (·.pc ≠ Hp.embedding.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done
      ⟨s, Host.addrOf (Hp.embedding.start + o)⟩ := by
  have hp := Hp.embedding.isInfixAt
  rw [Program.wp_eq] at hw
  have hw := @hw (Hp.ofIsInfixAt hq)
  simp only [Program.continueOnInternalExit_of_noInternal hq₀] at hw
  change While (·.pc ≠ Host.addrOf (Hp.embedding.start + o + q.length)) _ done'
    ⟨s, Host.addrOf (Hp.embedding.start + o)⟩ at hw
  change While (·.pc ≠ Host.addrOf (Hp.embedding.start + p.length)) _ done ⟨s, Host.addrOf (Hp.embedding.start + o)⟩
  change ∀ st, _ → _ → While (·.pc ≠ Host.addrOf (Hp.embedding.start + p.length)) _ done st at hQ
  change ∀ st, _ → p.ContinueOnInternalExit s₀
    (While (·.pc ≠ Host.addrOf (Hp.embedding.start + p.length)) _ done) exit st at hE
  generalize Hp.embedding.start = k at hp hQ hE hw ⊢
  refine (?_ : ∀ x, While (·.pc ≠ Host.addrOf (k + o + q.length))
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» exit') done' x →
      (∃ j, k + o ≤ j ∧ j ≤ k + o + q.length ∧ x.pc = Host.addrOf j) →
      While (·.pc ≠ Host.addrOf (k + p.length))
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done x) _ hw ⟨k + o, Nat.le_refl _, by omega, rfl⟩
  intro x h
  unfold While at h
  induction h with
  | done y h =>
    intro _
    exact hQ y (Classical.not_not.mp h.1) h.2
  | step y next ht _ ih =>
    rintro ⟨j, hj₁, hj₂, hjy⟩
    obtain ⟨hns, hst⟩ := ht
    have hne : Host.addrOf j ≠ Host.addrOf (k + o + q.length) := hjy ▸ hns
    refine While.step («continue» := While (·.pc ≠ Host.addrOf (k + p.length))
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done)
      (fun h => Host.addrOf_ne_of_le hj₂ (by omega) hne (hjy ▸ h)) ?_ fun _ h => h
    obtain ⟨m, c, hm₁, hm₂, hc, hz, hma⟩ := Host.at_of_ne hj₂ hne
    have hft : Host.exe.fallthrough y.pc = Host.addrOf (m + 1) := by
      rw [hjy, ← hma]; exact Host.fallthrough_addrOf hc hz
    exact Executable.StepOver.imp Program.callee_le (Executable.StepOver.restrict hst)
      (fun u ⟨hu, hpc⟩ => ih u hu ⟨m + 1, by omega, by omega, hpc.trans hft⟩) fun u hu => hE u hu

end
