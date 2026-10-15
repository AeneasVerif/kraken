module

public import Kraken.X64.WP.Host
public import Std.Data.ExtHashSet

/-
# Weakest precondition of a fragment of a host program

`Program.wp p Q E s` is the weakest precondition of the fragment `p`, embedded at the index that the
instance `Embeds p` names in the ambient `Host` program.
This definition is the bridge to `Std.WP` and thus `vcgen`.

The run of `p` starts at the address of `p` and steps the laid out `Host` executable by `step1`.
It stops at the first arrival at the end address of `p`, where `Q` must hold.
A successor continues the run along an edge of `p`: the fall-through successor, or the entry of a
block of `p` whose label is in `BlockEntries.labels`. Every other successor exits the run to `E`.
An exit to the start of a fragment in `FunDecls.funs` is a call: the run of the callee replaces the
arrival, and each exit of the callee continues or exits the run of `p`.
-/

open Classical in
@[expose] public def Run {σ : Type} (step : σ → (σ → Prop) → Prop) (edge : σ → σ → Prop)
    (stop : σ → Prop) (P E : σ → Prop) : σ → Prop :=
  Eventually (fun st next => ¬ stop st ∧ step st fun st' => if edge st st' then next st' else E st')
    (fun st => stop st ∧ P st)

section
variable {σ : Type} {tr : σ → (σ → Prop) → Prop} {edge : σ → σ → Prop} {stop : σ → Prop}

public theorem Run.done {P E : σ → Prop} {x : σ} (hs : stop x) (hp : P x) : Run tr edge stop P E x :=
  Eventually.done _ ⟨hs, hp⟩

open Classical in
public theorem Run.step {P E : σ → Prop} {x : σ} {next : σ → Prop} (hs : ¬ stop x)
    (ht : tr x fun y => if edge x y then next y else E y) (h : ∀ y, next y → Run tr edge stop P E y) :
    Run tr edge stop P E x :=
  Eventually.step _ _ ⟨hs, ht⟩ h

open Classical in
public theorem Run.imp {tr₂ : σ → (σ → Prop) → Prop} {edge₂ : σ → σ → Prop} {P₁ P₂ E₁ E₂ : σ → Prop}
    (hstep : ∀ y (U : σ → Prop), ¬ stop y → tr y (fun z => if edge y z then U z else E₁ z) →
      tr₂ y (fun z => if edge₂ y z then U z else E₂ z))
    (hP : ∀ y, stop y → P₁ y → P₂ y) {x : σ} (h : Run tr edge stop P₁ E₁ x) :
    Run tr₂ edge₂ stop P₂ E₂ x := by
  induction h with
  | done y h => exact Eventually.done y ⟨h.1, hP y h.1 h.2⟩
  | step y mid ht _ ih => exact Eventually.step y mid ⟨ht.1, hstep y mid ht.1 ht.2⟩ ih

public theorem Run.mono {P₁ P₂ E₁ E₂ : σ → Prop}
    (hmono : ∀ y U V, tr y U → (∀ z, U z → V z) → tr y V)
    (hP : ∀ y, P₁ y → P₂ y) (hE : ∀ y, E₁ y → E₂ y) {x : σ} (h : Run tr edge stop P₁ E₁ x) :
    Run tr edge stop P₂ E₂ x :=
  Run.imp (fun y U _ hy => hmono y _ _ hy fun z hz => by split at hz <;> simp_all) (fun y _ => hP y) h

open Classical in
public theorem Run.seq {stop₂ : σ → Prop} {P E : σ → Prop} (I : σ → Prop)
    (hstop : ∀ y, I y → ¬ stop y → ¬ stop₂ y)
    (hmono : ∀ y U V, tr y U → (∀ z, U z → V z) → tr y V)
    (hI : ∀ y z, I y → ¬ stop y → edge y z → I z)
    {x : σ} (hx : I x) (h : Run tr edge stop (Run tr edge stop₂ P E) E x) :
    Run tr edge stop₂ P E x := by
  induction h with
  | done _ h => exact h.2
  | step y mid ht _ ih =>
    refine Eventually.step y (fun z => mid z ∧ I z)
      ⟨hstop y hx ht.1, hmono y _ _ ht.2 fun z hz => ?_⟩ fun z hz => ih z hz.1 hz.2
    by_cases he : edge y z
    · simp only [he, ↓reduceIte] at hz ⊢
      exact ⟨hz, hI y z hx ht.1 he⟩
    · simpa only [he, ↓reduceIte] using hz

public theorem Run.and {tr₁ tr₂ : σ → (σ → Prop) → Prop} {P₁ P₂ E₁ E₂ : σ → Prop}
    (hstep : ∀ y U V, ¬ stop y → tr₁ y U → tr₂ y V → tr y fun z => U z ∧ V z)
    (hmono : ∀ y U V, tr y U → (∀ z, U z → V z) → tr y V) {x : σ}
    (h₁ : Run tr₁ edge stop P₁ E₁ x) (h₂ : Run tr₂ edge stop P₂ E₂ x) :
    Run tr edge stop (fun z => P₁ z ∧ P₂ z) (fun z => E₁ z ∧ E₂ z) x := by
  induction h₁ with
  | done y hd => cases h₂ with
    | done _ hd₂ => exact Eventually.done _ ⟨hd.1, hd.2, hd₂.2⟩
    | step _ _ ht _ => exact absurd hd.1 ht.1
  | step y U₁ ht₁ _ ih => cases h₂ with
    | done _ hd₂ => exact absurd hd₂.1 ht₁.1
    | step _ U₂ ht₂ hr₂ =>
      refine Eventually.step _ (fun z => U₁ z ∧ U₂ z)
        ⟨ht₁.1, hmono _ _ _ (hstep _ _ _ ht₁.1 ht₁.2 ht₂.2) fun z ⟨hz₁, hz₂⟩ => ?_⟩
        fun z ⟨hz₁, hz₂⟩ => ih z hz₁ (hr₂ z hz₂)
      split at hz₁ <;> simp_all

open Lean.Order in
@[partial_fixpoint_monotone] public theorem Run.monotone {α : Type} [PartialOrder α]
    {P E : σ → Prop} {init : σ} (f : α → σ → (σ → Prop) → ImplicationOrder) (h : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => Run (f x) edge stop P E init) := by
  intro x y hxy hx
  induction hx with
  | done st hp => exact Eventually.done _ hp
  | step st U ht _ ih => exact Eventually.step _ U ⟨ht.1, h _ _ hxy st _ ht.2⟩ ih

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


@[expose] public def Executable.fallthrough (e : Executable) (a : Int64) : Int64 :=
  a + .ofNat ((e.directivesAtAddress a).map (·.size)).sum

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

public abbrev Embeds.start [Host] (p : Program) [h : Embeds p] : Nat := h.embedding.start

@[expose] public def Embedding.ofIsInfixAt [Host] {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : Embedding p :=
  ⟨e.start + i, List.IsInfixAt.trans h e.isInfixAt⟩

@[expose] public def Embedding.cast [Host] {p q : Program} (h : p = q) (e : Embedding p) : Embedding q :=
  ⟨e.start, h ▸ e.isInfixAt⟩

public abbrev Embeds.ofIsInfixAt [Host] {p q : Program} (hq : Embeds q) {i : Nat}
    (h : p.IsInfixAt q i) : Embeds p := ⟨hq.embedding.ofIsInfixAt h⟩

public abbrev Embeds.cast [Host] {p q : Program} (h : p = q) (e : Embeds p) : Embeds q :=
  ⟨e.embedding.cast h⟩

public abbrev Embeds.ofIsInfix [Host] {p : Program} (h : p.IsInfix Host.prog) : Embeds p :=
  ⟨⟨p.infixIdx Host.prog h, List.isInfixAt_infixIdx h⟩⟩

public class BlockEntries where
  labels : Std.ExtHashSet Label

public instance : BlockEntries := ⟨∅⟩

@[simp, grind =] public theorem BlockEntries.labels_empty : (BlockEntries.labels : Std.ExtHashSet Label) = ∅ := rfl

attribute [grind .] Std.ExtHashSet.not_mem_empty

@[expose] public def BlockEntries.ofLabels (ls : List Label) : BlockEntries := ⟨Std.ExtHashSet.ofList ls⟩

public theorem BlockEntries.mem_ofLabels {ls : List Label} {l : Label} (h : l ∈ ls) :
    l ∈ (BlockEntries.ofLabels ls).labels :=
  Std.ExtHashSet.mem_ofList.mpr (List.contains_iff_mem.mpr h)

@[expose] public def Program.NoEntries [BlockEntries] (p : Program) : Prop :=
  ∀ l ∈ p.labels, l ∉ BlockEntries.labels

@[simp, grind =] public theorem Program.noEntries_nil [BlockEntries] : Program.NoEntries [] ↔ True := by
  simp [Program.NoEntries]

@[simp, grind =] public theorem Program.noEntries_cons_instr [BlockEntries] (i : Instr) (p : Program) :
    Program.NoEntries (.instr i :: p) ↔ Program.NoEntries p := by
  simp [Program.NoEntries]

@[simp, grind =] public theorem Program.noEntries_cons_byteArray [BlockEntries] (a : ByteArray) (p : Program) :
    Program.NoEntries (.byteArray a :: p) ↔ Program.NoEntries p := by
  simp [Program.NoEntries]

@[simp, grind =] public theorem Program.noEntries_cons_label [BlockEntries] (l : Label) (p : Program) :
    Program.NoEntries (.label l :: p) ↔ l ∉ BlockEntries.labels ∧ Program.NoEntries p := by
  simp [Program.NoEntries]

public class NotEntry [BlockEntries] (l : Label) : Prop where
  out : l ∉ BlockEntries.labels

public instance {l : Label} : @NotEntry ⟨∅⟩ l := ⟨Std.ExtHashSet.not_mem_empty⟩

public class NoEntries [BlockEntries] (p : Program) : Prop where
  out : Program.NoEntries p

public instance [BlockEntries] : NoEntries [] := ⟨by simp⟩

public instance [BlockEntries] {i : Instr} {p : Program} [h : NoEntries p] : NoEntries (.instr i :: p) :=
  ⟨by simpa using h.out⟩

public instance [BlockEntries] {l : Label} {p : Program} [h : NoEntries p] [hl : NotEntry l] :
    NoEntries (.label l :: p) :=
  ⟨by simpa using ⟨hl.out, h.out⟩⟩

@[expose] public def Program.Entry [Host] [BlockEntries] (p : Program) (a : Int64) : Prop :=
  ∃ l ∈ BlockEntries.labels, l ∈ p.labels ∧ label l = a

public structure Fragment [Host] where
  prog : Program
  [embeds : Embeds prog]

public meta section

macro "frag% " e:term:max : term => `((Fragment.mk $e : Fragment))

@[app_unexpander Fragment.mk] def Fragment.unexpandMk : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `(frag% $p)
  | _ => throw ()

end

public structure DirectiveAt [Host] where
  directive : Directive
  [embeds : Embeds [directive]]

section
variable [Host]

@[expose] public def Embedding.startAddr {p : Program} (e : Embedding p) : Int64 := Host.addrOf e.start

@[expose] public def Embedding.endAddr {p : Program} (e : Embedding p) : Int64 :=
  Host.addrOf (e.start + p.length)

public abbrev Fragment.startAddr (f : Fragment) : Int64 := f.embeds.embedding.startAddr

public abbrev Fragment.endAddr (f : Fragment) : Int64 := f.embeds.embedding.endAddr

end

@[expose] public def Program.Edge [Host] [BlockEntries] (p : Program) (a a' : Int64) : Prop :=
  a' = Host.exe.fallthrough a ∨ p.Entry a'

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
@[expose] public noncomputable def Program.callee [Host] [BlockEntries] [FunDecls] (p : Program)
    (a a' : Int64) : Option Fragment :=
  if p.Edge a a' then none else FunDecls.at a'

mutual
public def Program.step [Host] [BlockEntries] [FunDecls] (p : Program) (st : MachineState)
    (post : MachineState → Prop) : Prop :=
  step1 Host.exe st fun st' =>
    match p.callee st.pc st'.pc with
    | some f => Program.wp f.prog (h := f.embeds) (fun _ => False) (fun a t => post ⟨t, a⟩) st'.data
    | none => post st'
inductive_fixpoint

/-- Weakest precondition of a `Program` fragment embedded in a host program. -/
public def Program.wp [Host] [BlockEntries] [FunDecls] (p : Program) [h : Embeds p]
    (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  Run (Program.step p) (fun st st' => p.Edge st.pc st'.pc)
    (fun st => st.pc = Host.addrOf (h.embedding.start + p.length)) (fun st => Q st.data)
    (fun st => E st.pc st.data) ⟨s, Host.addrOf h.embedding.start⟩
inductive_fixpoint
end

section
variable [Host] [BlockEntries] [FunDecls]

public theorem Program.wp_eq {p : Program} {h : Embeds p} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} :
    @Program.wp _ _ _ p h Q E s = Run p.step (fun st st' => p.Edge st.pc st'.pc)
      (fun st => st.pc = Host.addrOf (h.embedding.start + p.length)) (fun st => Q st.data)
      (fun st => E st.pc st.data) ⟨s, Host.addrOf h.embedding.start⟩ := by
  rw [Program.wp]

@[expose] public def FunDecls.exit (R E : Int64 → MachineData → Prop) (a : Int64) (s : MachineData) :
    Prop :=
  match FunDecls.at a with
  | some f => @Program.wp _ _ _ f.prog f.embeds (fun _ => False) R s
  | none => E a s

public theorem Program.wp_mono {p : Program} [Embeds p] {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : p.wp Q₁ E₁ s) : p.wp Q₂ E₂ s := by
  refine Program.wp.induct
    (fun p st post => ∀ post' : MachineState → Prop, (∀ u, post u → post' u) → p.step st post')
    (fun p _ Q₁ E₁ s => ∀ (Q₂ : MachineData → Prop) (E₂ : Int64 → MachineData → Prop),
      (∀ s, Q₁ s → Q₂ s) → (∀ a s, E₁ a s → E₂ a s) → p.wp Q₂ E₂ s)
    ?_ ?_ p Q₁ E₁ s h Q₂ E₂ hQ hE
  · intro p st post h post' hp
    rw [Program.step]
    refine Effects.All_mono (fun st' hc => ?_) h
    split at hc
    next f _ => exact hc _ _ (fun _ h => h.elim) (fun _ _ => hp _)
    next => exact hp _ hc
  · intro p _ Q₁ E₁ s h Q₂ E₂ hQ hE
    rw [Program.wp_eq]
    exact Run.imp (tr := fun st post => ∀ post' : MachineState → Prop, (∀ u, post u → post' u) → p.step st post')
      (fun y U _ hy => hy _ fun z hz => by dsimp only at hz ⊢; split at hz <;> simp_all) (fun _ _ => hQ _) h

public theorem Program.step_of_callee_eq {p q : Program} {st : MachineState} {U V : MachineState → Prop}
    (hc : ∀ a', q.callee st.pc a' = p.callee st.pc a') (h : q.step st U) (hUV : ∀ z, U z → V z) :
    p.step st V := by
  rw [Program.step] at h ⊢
  refine Effects.All_mono (fun st' hs => ?_) h
  rw [← hc]
  split at hs
  next f _ => exact @Program.wp_mono _ _ _ f.prog f.embeds _ _ _ _ (fun _ h => h) (fun _ _ => hUV _) _ hs
  next => exact hUV _ hs

public theorem Program.step_mono {p : Program} {st : MachineState} {U V : MachineState → Prop}
    (h : p.step st U) (hUV : ∀ z, U z → V z) : p.step st V :=
  Program.step_of_callee_eq (fun _ => rfl) h hUV

public theorem Program.wp_and {p : Program} [Embeds p] {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} {s : MachineData} (h₁ : p.wp Q₁ E₁ s) (h₂ : p.wp Q₂ E₂ s) :
    p.wp (fun s => Q₁ s ∧ Q₂ s) (fun a s => E₁ a s ∧ E₂ a s) s := by
  refine Program.wp.induct
    (fun p st post => ∀ post' : MachineState → Prop, p.step st post' → p.step st fun u => post u ∧ post' u)
    (fun p _ Q₁ E₁ s => ∀ (Q₂ : MachineData → Prop) (E₂ : Int64 → MachineData → Prop), p.wp Q₂ E₂ s →
      p.wp (fun s => Q₁ s ∧ Q₂ s) (fun a s => E₁ a s ∧ E₂ a s) s)
    ?_ ?_ p Q₁ E₁ s h₁ Q₂ E₂ h₂
  · intro p st post h post' h'
    rw [Program.step] at h' ⊢
    refine Effects.All_mono (fun st' ⟨hc, hc'⟩ => ?_) (Effects.All_and h h')
    split at hc <;> rename_i heq <;> simp only [heq] at hc' <;> revert hc hc'
    next f => intro hc hc'; exact @Program.wp_mono _ _ _ f.prog f.embeds _ _ _ _ (fun _ h => h.1) (fun _ _ h => h) _ (hc _ _ hc')
    next => exact fun hc hc' => ⟨hc, hc'⟩
  · intro p _ Q₁ E₁ s h Q₂ E₂ h'
    rw [Program.wp_eq] at h' ⊢
    exact Run.and (tr₁ := fun st post => ∀ post' : MachineState → Prop, p.step st post' → p.step st fun u => post u ∧ post' u)
      (fun y U V _ hU hV => hU _ hV) (fun y U V hy hUV => Program.step_mono hy hUV) h h'

public theorem Program.at_of_callee {p : Program} {a a' : Int64} {f : Fragment}
    (h : p.callee a a' = some f) : FunDecls.at a' = some f := by
  unfold Program.callee at h
  split at h
  · cases h
  · exact h

omit [FunDecls] in
public theorem Program.entry_of_labels_disjoint {p : Program}
    (hN : ∀ l ∈ Program.labels p, l ∉ BlockEntries.labels) (a : Int64) : ¬ p.Entry a :=
  fun ⟨l, hl, hp, _⟩ => hN l hp hl

omit [FunDecls] in
public theorem Program.edge_iff_of_labels_disjoint {p : Program}
    (hN : ∀ l ∈ Program.labels p, l ∉ BlockEntries.labels) (a a' : Int64) :
    p.Edge a a' ↔ a' = Host.exe.fallthrough a := by
  simp only [Program.Edge, Program.entry_of_labels_disjoint hN, or_false]

open Classical in
public theorem Program.run_congr {p q : Program} (h : ∀ a a', p.Edge a a' ↔ q.Edge a a')
    {stop P₁ P₂ E : MachineState → Prop} {x : MachineState} (hP : ∀ y, stop y → P₁ y → P₂ y)
    (hr : Run p.step (fun st st' => p.Edge st.pc st'.pc) stop P₁ E x) :
    Run q.step (fun st st' => q.Edge st.pc st'.pc) stop P₂ E x :=
  Run.imp (fun y U _ hy => Program.step_of_callee_eq (fun a' => by simp only [Program.callee, h]) hy
    fun z hz => by simpa only [h] using hz) hP hr

end

@[simp, grind =] public theorem FunDecls.exit_default [Host] [BlockEntries]
    {R E : Int64 → MachineData → Prop} {a : Int64} {s : MachineData} : FunDecls.exit R E a s = E a s :=
  rfl

section
variable [Host]

public theorem Host.fallthrough_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    Host.exe.fallthrough (Host.addrOf k) = Host.addrOf (k + 1) := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hc hz
  have hk : Host.prog[k]? = some c.directive := by
    rw [Host.exe_getElem?] at hc; grind
  have hzk : Kraken.Layout.size Directive k = c.size := by
    rw [Host.exe_getElem?] at hc; grind
  have hsum : (pre.map (·.size)).sum = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mpr fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hpre c hc
  rw [Executable.fallthrough, hat, List.map_append, List.sum_append, hsum, Host.addrOf_succ hk, hzk]
  simp

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

public theorem Host.step1_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {s : MachineData} {post : @Post MachineState} :
    step1 Host.exe ⟨s, Host.addrOf k⟩ post ↔
      (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hc hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  have hk : Host.prog[k]? = some c.directive := by
    rw [Host.exe_getElem?] at hc; grind
  have hzk : Kraken.Layout.size Directive k = c.size := by
    rw [Host.exe_getElem?] at hc; grind
  unfold step1 Executable.step
  change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _).All post ↔ _
  rw [hat, Directives.interp_inert_append hinert, Host.addrOf_succ hk, hzk]
  rfl

public theorem Host.eventually_of_interp {k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt Host.prog k) {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hd : Host.exe.program[k]? = some {directive := d, size := Kraken.Layout.size Directive k} := by
    rw [Host.exe_getElem?, hdp.cons.1]
    rfl
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive k) with h0 | hz
  · rw [Host.addrOf_succ hdp.cons.1] at h
    rw [h0] at hd h
    rw [Host.inert_of_size_zero (List.mem_of_getElem? hd)] at h
    have h0' : Host.addrOf k + Int64.ofNat 0 = Host.addrOf k := by simp
    simp only [Effects.All, h0'] at h
    exact Eventually.done _ h
  · exact Eventually.step _ post ((Host.step1_addrOf hd hz).mpr h) fun _ hb => Eventually.done _ hb

end
section
variable [Host] [BlockEntries] [FunDecls]

public theorem Program.wp_cons {d : Directive} {p : Program} [H : Embeds (d :: p)]
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (hN : Program.NoEntries (d :: p))
    (hw : haveI : Embeds [d] := .ofIsInfixAt H (List.isInfixAt_cons_head d p)
          Program.wp [d] (fun s' =>
            haveI : Embeds p := .ofIsInfixAt H (List.isInfixAt_cons_tail d p)
            Program.wp p Q E s') E s) :
    Program.wp (d :: p) Q E s := by
  have hNd : ∀ l ∈ Program.labels [d], l ∉ BlockEntries.labels := fun l hl =>
    hN l (by cases d <;> simp_all [Program.labels_cons_label])
  have hNp : ∀ l ∈ Program.labels p, l ∉ BlockEntries.labels := fun l hl =>
    hN l (by cases d <;> simp_all [Program.labels_cons_label])
  have cd := Program.edge_iff_of_labels_disjoint hNd
  have cp := Program.edge_iff_of_labels_disjoint hNp
  have cdp := Program.edge_iff_of_labels_disjoint hN
  have hk := H.embedding.isInfixAt
  rw [Program.wp_eq] at hw ⊢
  have hw : Run (Program.step (d :: p)) (fun st st' => Program.Edge (d :: p) st.pc st'.pc)
      (·.pc = Host.addrOf (H.embedding.start + 1))
      (Run (Program.step (d :: p)) (fun st st' => Program.Edge (d :: p) st.pc st'.pc)
        (·.pc = Host.addrOf (H.embedding.start + (p.length + 1))) (Q ·.data) (fun st => E st.pc st.data))
      (fun st => E st.pc st.data) ⟨s, Host.addrOf H.embedding.start⟩ := by
    refine Program.run_congr (fun a a' => (cd a a').trans (cdp a a').symm) (fun st h₁ h₂ => ?_) hw
    obtain ⟨u, a⟩ := st
    dsimp only at h₁ h₂ ⊢
    subst h₁
    rw [Program.wp_eq] at h₂
    have h₂ := Program.run_congr (fun a a' => (cp a a').trans (cdp a a').symm) (fun _ _ h => h) h₂
    change Run _ _ (fun st : MachineState => st.pc = Host.addrOf (H.embedding.start + 1 + p.length)) _ _ _ at h₂
    rwa [show H.embedding.start + 1 + p.length = H.embedding.start + (p.length + 1) by omega] at h₂
  show Run _ _ (fun st : MachineState => st.pc = Host.addrOf (H.embedding.start + (p.length + 1))) _ _ _
  generalize H.embedding.start = k at hk hw ⊢
  have hd : Host.exe.program[k]? = some {directive := d, size := Kraken.Layout.size Directive k} := by
    rw [Host.exe_getElem?, hk.cons.1]; rfl
  refine Run.seq (tr := Program.step (d :: p)) (fun y => y.pc ≠ Host.addrOf (k + 1) → y.pc = Host.addrOf k)
    (fun y hI hs => ?_) (fun _ _ _ hy hUV => Program.step_mono hy hUV) (fun y z hI hs he hne => ?_)
    (fun _ => rfl) hw
  · rw [hI hs, show k + (p.length + 1) = k + 1 + p.length by omega]
    exact Host.addrOf_ne_of_succ_ne (hI hs ▸ hs)
  · have hz : 0 < Kraken.Layout.size Directive k := by
      refine Nat.pos_of_ne_zero fun h0 => hs ?_
      rw [hI hs, Host.addrOf_succ hk.cons.1, h0]; simp
    have := (cdp _ _).mp he
    rw [hI hs, Host.fallthrough_addrOf hd hz] at this
    exact absurd this hne

@[expose] public def Cls (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (a' : Int64)
    (u : MachineState) : Prop :=
  if u.pc = a' then Q u.data else FunDecls.exit (fun a t => if a = a' then Q t else E a t) E u.pc u.data

public theorem Program.wp_single {d : Directive} [h : Embeds [d]] {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (hw : (d.interp s ⟨Host.addrOf h.embedding.start, Host.addrOf (h.embedding.start + 1)⟩
        (fun s' => .done ⟨s', Host.addrOf (h.embedding.start + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All
          (Cls Q E (Host.addrOf (h.embedding.start + 1)))) :
    Program.wp [d] Q E s := by
  have hk := h.embedding.isInfixAt
  rw [Program.wp_eq]
  generalize h.embedding.start = k at hk hw ⊢
  have hdk : Host.prog[k]? = some d := hk.cons.1
  have hd : Host.exe.program[k]? = some {directive := d, size := Kraken.Layout.size Directive k} := by
    rw [Host.exe_getElem?, hdk]; rfl
  show Run _ _ (fun st : MachineState => st.pc = Host.addrOf (k + 1)) _ _ _
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive k) with h0 | hz
  · have ha : Host.addrOf (k + 1) = Host.addrOf k := by
      rw [Host.addrOf_succ hdk, h0]; simp
    rw [h0] at hd
    rw [Host.inert_of_size_zero (List.mem_of_getElem? hd)] at hw
    simp only [Effects.All, Cls, ha, ite_true] at hw
    exact Run.done ha.symm hw
  · have hNd : ∀ l ∈ Program.labels [d], l ∉ BlockEntries.labels := by
      intro l hl
      cases d with
      | label l' => exact absurd (Host.label_size k l' hdk) (by omega)
      | _ => simp at hl
    have hedge : ∀ a', Program.Edge [d] (Host.addrOf k) a' ↔ a' = Host.addrOf (k + 1) := fun a' => by
      rw [Program.edge_iff_of_labels_disjoint hNd, Host.fallthrough_addrOf hd hz]
    refine Run.step (next := fun u => u.pc = Host.addrOf (k + 1) ∧ Q u.data)
      (Host.addrOf_succ_ne hd hz) ?_ fun u hu => Run.done hu.1 hu.2
    rw [Program.step]
    refine (Host.step1_addrOf hd hz).mpr (Effects.All_mono (fun st₀ hs => ?_) hw)
    simp only [Program.callee, hedge]
    unfold Cls FunDecls.exit at hs
    by_cases hu : st₀.pc = Host.addrOf (k + 1)
    · simp only [hu, ↓reduceIte, true_and] at hs ⊢
      exact hs
    · simp only [hu, ↓reduceIte] at hs ⊢
      split at hs
      next f hf =>
        simp only [hf]
        exact @Program.wp_mono _ _ _ f.prog f.embeds _ _ _ _ (fun _ h => h)
          (fun a t h => by by_cases ha : a = Host.addrOf (k + 1) <;> simp_all) _ hs
      next hf =>
        simp only [hf]
        exact hs

public theorem Program.wp_nil [h : Embeds []] {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} (hq : Q s) : Program.wp [] Q E s := by
  rw [Program.wp_eq]
  exact Run.done (by simp) hq

end

/--
Soundness of `Program.wp`: if `p.wp Q E s` holds, then the run from `s` at the address of `p`
eventually reaches the postcondition `Q` at the end address of `p` or the exit condition `E`.
-/
public theorem Program.step1_of_wp [Host] [BlockEntries] [FunDecls] {p : Program} [h : Embeds p]
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post ⟨s', Host.addrOf (h.embedding.start + p.length)⟩)
    (hE : ∀ a s', E a s' → post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩ := by
  refine Program.wp.induct
    (fun _ st U => ∀ post : MachineState → Prop, (∀ u, U u → Eventually (step1 Host.exe) post u) →
      Eventually (step1 Host.exe) post st)
    (fun p h Q E s => ∀ post : MachineState → Prop,
      (∀ s', Q s' → post ⟨s', Host.addrOf (h.embedding.start + p.length)⟩) →
      (∀ a s', E a s' → post ⟨s', a⟩) → Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩)
    ?_ ?_ p Q E s hwp post hQ hE
  · intro p st U hst post hU
    refine Eventually.step st _ (Effects.All_mono (fun st' h => ?_) hst) fun _ h => h
    split at h
    next f hf =>
      have hstart : Host.addrOf f.embeds.embedding.start = st'.pc :=
        FunDecls.startAddr_of_at (Program.at_of_callee hf)
      have := h (Eventually (step1 Host.exe) post) (fun _ h => h.elim) (fun a t hu => hU _ hu)
      rw [hstart] at this
      exact eventually_trans _ _ _ _ this fun _ h => h
    next => exact hU _ h
  · intro p h Q E s hrun post hQ hE
    generalize (⟨s, Host.addrOf h.embedding.start⟩ : MachineState) = x at hrun ⊢
    induction hrun with
    | done y hy =>
      obtain ⟨u, a⟩ := y
      obtain ⟨hs, hq⟩ := hy
      dsimp only at hs hq
      subst hs
      exact .done _ (hQ _ hq)
    | step y next ht _ ih =>
      refine ht.2 post fun u hu => ?_
      by_cases he : p.Edge y.pc u.pc
      · simp only [he, ↓reduceIte] at hu
        exact ih u hu
      · simp only [he, ↓reduceIte] at hu
        exact .done _ (hE _ _ hu)

section
variable [Host]

@[expose] public def Embedding.FallsThroughTo {p : Program} (e : Embedding p) (a : Int64) : Prop :=
  a = e.endAddr

public instance {p : Program} (e : Embedding p) (a : Int64) : Decidable (e.FallsThroughTo a) :=
  inferInstanceAs (Decidable (_ = _))

public abbrev Fragment.FallsThroughTo (f : Fragment) (a : Int64) : Prop :=
  f.embeds.embedding.FallsThroughTo a

public abbrev DirectiveAt.FallsThroughTo (d : DirectiveAt) (a : Int64) : Prop :=
  d.embeds.embedding.FallsThroughTo a

public abbrev DirectiveAt.startAddr (d : DirectiveAt) : Int64 := d.embeds.embedding.startAddr

@[grind =] public theorem Embedding.fallsThroughTo_iff {p : Program} (e : Embedding p) (a : Int64) :
    e.FallsThroughTo a ↔ a = e.endAddr := Iff.rfl

@[grind =] public theorem Embedding.endAddr_def {p : Program} (e : Embedding p) :
    e.endAddr = Host.addrOf (e.start + p.length) := rfl

@[grind =] public theorem Embedding.startAddr_def {p : Program} (e : Embedding p) :
    e.startAddr = Host.addrOf e.start := rfl

@[grind =] public theorem Embedding.start_ofIsInfixAt {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : (e.ofIsInfixAt h).start = e.start + i := rfl

@[grind =] public theorem Embedding.start_cast {p q : Program} (h : p = q) (e : Embedding p) :
    (e.cast h).start = e.start := rfl

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

public theorem Embedding.isPadding_of_fallsThroughTo_before {ins : Instr} {l : Label} {p q r : Program}
    (f : Embedding p) (g : Embedding (.label l :: q)) (t : Embedding (.instr ins :: r))
    (h₁ : g.start ≤ t.start) (h₂ : t.start < f.start + p.length) :
    f.FallsThroughTo (label l) → ins.IsPadding := by
  refine fun hft => Classical.byContradiction fun hpad => absurd hft ?_
  have hl : label l = Host.addrOf (g.start + 0) := Host.label_eq g.isInfixAt rfl
  have hk : Host.prog[t.start + 0]? = some (.instr ins) := by
    rw [List.isInfixAt_iff_getElem?.mp t.isInfixAt 0 (by simp)]; rfl
  rw [Embedding.fallsThroughTo_iff, Embedding.endAddr_def, hl]
  exact Host.addrOf_ne hk hpad h₁ h₂

public theorem Embedding.isPadding_of_fallsThroughTo_after {ins : Instr} {l : Label} {p q r : Program}
    (f : Embedding p) (g : Embedding (.label l :: q)) (t : Embedding (.instr ins :: r))
    (h₁ : f.start + p.length ≤ t.start) (h₂ : t.start < g.start) :
    f.FallsThroughTo (label l) → ins.IsPadding := by
  refine fun hft => Classical.byContradiction fun hpad => absurd hft ?_
  have hl : label l = Host.addrOf (g.start + 0) := Host.label_eq g.isInfixAt rfl
  have hk : Host.prog[t.start + 0]? = some (.instr ins) := by
    rw [List.isInfixAt_iff_getElem?.mp t.isInfixAt 0 (by simp)]; rfl
  rw [Embedding.fallsThroughTo_iff, Embedding.endAddr_def, hl]
  exact fun h => Host.addrOf_ne hk hpad h₁ h₂ h.symm

grind_pattern Embedding.isPadding_of_fallsThroughTo_before => f.FallsThroughTo (label l), g.start, t.start
grind_pattern Embedding.isPadding_of_fallsThroughTo_after => f.FallsThroughTo (label l), g.start, t.start

public theorem Embedding.isPadding_of_fallsThroughTo_next {j ins : Instr} {l : Label} {r : Program}
    (e : Embedding (.instr j :: .instr ins :: r)) :
    (e.ofIsInfixAt (List.isInfixAt_cons_head _ _)).FallsThroughTo (label l) → j.IsPadding ∨ ins.IsPadding := by
  intro hft
  refine Classical.byContradiction fun hpad => ?_
  simp only [not_or] at hpad
  have hj : Host.prog[e.start + 0]? = some (.instr j) := by
    rw [List.isInfixAt_iff_getElem?.mp e.isInfixAt 0 (by simp)]; rfl
  have hi : Host.prog[e.start + 1]? = some (.instr ins) := by
    rw [List.isInfixAt_iff_getElem?.mp e.isInfixAt 1 (by simp)]; rfl
  simp only [Embedding.fallsThroughTo_iff, Embedding.endAddr_def, Embedding.start_ofIsInfixAt,
    List.length_singleton, Nat.add_zero] at hft hj
  rcases Host.label_cases l with h | ⟨i, hil, hla⟩
  · exact Host.instr_addr_ne _ _ hi (show Host.addrOf (e.start + 1) = -1 from hft.symm.trans h)
  · rw [hla] at hft
    rcases Nat.lt_trichotomy i e.start with hlt | heq | hgt
    · exact Host.addrOf_ne hj hpad.1 (Nat.le_of_lt hlt) (Nat.lt_succ_self _) hft
    · subst heq; rw [hil] at hj; cases hj
    · rcases Nat.lt_or_ge (e.start + 1) i with hlt' | hle
      · exact Host.addrOf_ne hi hpad.2 (Nat.le_refl _) hlt' hft.symm
      · have : i = e.start + 1 := by omega
        subst this; rw [hil] at hi; cases hi

grind_pattern Embedding.isPadding_of_fallsThroughTo_next =>
  (e.ofIsInfixAt (List.isInfixAt_cons_head (Directive.instr j) (Directive.instr ins :: r))).FallsThroughTo (label l)

end

section
variable [Host] [BlockEntries]

public theorem Host.lt_length_of_addrOf_ne {j e : Nat} (hje : j ≤ e)
    (hne : Host.addrOf j ≠ Host.addrOf e) : j < Host.prog.length := by
  refine Nat.lt_of_not_ge fun hj => hne ?_
  have hlen : Host.exe.program.length = Host.prog.length := by
    simp [Host.exe, Kraken.Layout.apply]
  simp only [Host.addrOf, Kraken.Executable.addrOf, Kraken.Executable.sizeBefore,
    List.take_of_length_le (show Host.exe.program.length ≤ j by omega),
    List.take_of_length_le (show Host.exe.program.length ≤ e by omega)]

public theorem Host.fallthrough_addrOf_of_ne {j e : Nat} (hje : j ≤ e)
    (hne : Host.addrOf j ≠ Host.addrOf e) :
    ∃ m, j ≤ m ∧ m < e ∧ Host.exe.fallthrough (Host.addrOf j) = Host.addrOf (m + 1) := by
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
      obtain ⟨m, hm₁, hm₂, hm₃⟩ := ih (j := j + 1) hje' (ha ▸ hne) (by omega)
      exact ⟨m, by omega, hm₂, ha ▸ hm₃⟩
    · exact ⟨j, Nat.le_refl _, hje', Host.fallthrough_addrOf hc hz⟩

public theorem Host.addrOf_ne_of_le {j e f : Nat} (hje : j ≤ e) (hef : e ≤ f)
    (hne : Host.addrOf j ≠ Host.addrOf e) : Host.addrOf j ≠ Host.addrOf f := by
  intro h
  have h₁ := Host.sizeBefore_eq_of_addrOf_eq h
  have h₂ := Host.exe.sizeBefore_mono hje
  have h₃ := Host.exe.sizeBefore_mono hef
  exact hne (by simp only [Host.addrOf, Kraken.Executable.addrOf]; congr 2; omega)

public theorem Program.entry_of_infix {p q : Program} {o : Nat} (hq : q.IsInfixAt p o) {a : Int64}
    (h : q.Entry a) : p.Entry a := by
  obtain ⟨l, hl, hql, hla⟩ := h
  exact ⟨l, hl, Program.mem_labels.mpr (hq.isInfix.subset (Program.mem_labels.mp hql)), hla⟩

variable [FunDecls]

public theorem Program.callee_infix {p q : Program} {o : Nat}
    (hq : q.IsInfixAt p o) (hcall : ∀ a, p.Entry a → ¬ q.Entry a → FunDecls.at a = none) (a a' : Int64) :
    q.callee a a' = p.callee a a' := by
  unfold Program.callee
  by_cases hqe : q.Edge a a'
  · have hpe : p.Edge a a' := hqe.imp id (Program.entry_of_infix hq)
    simp only [hqe, hpe, ↓reduceIte]
  · by_cases hpe : p.Edge a a'
    · have hent : p.Entry a' := hpe.resolve_left fun hft => hqe (Or.inl hft)
      simp only [hqe, hpe, ↓reduceIte]
      exact hcall a' hent fun h => hqe (Or.inr h)
    · simp only [hqe, hpe, ↓reduceIte]

open Classical in
public theorem Program.run_infix {p q : Program} [Hp : Embeds p]
    {o : Nat} (hq : q.IsInfixAt p o) (hlenq : o + q.length ≤ p.length)
    (hcall : ∀ a, p.Entry a → ¬ q.Entry a → FunDecls.at a = none)
    {E : Int64 → MachineData → Prop} {P : MachineState → Prop}
    {Q' : MachineData → Prop} {E' : Int64 → MachineData → Prop} {s : MachineData}
    (hw : @Program.wp _ _ _ q (Hp.ofIsInfixAt hq) Q' E' s)
    (hQ : ∀ s', Q' s' → Run p.step (fun st st' => p.Edge st.pc st'.pc)
      (·.pc = Host.addrOf (Hp.embedding.start + p.length)) P (fun st => E st.pc st.data)
      ⟨s', Host.addrOf (Hp.embedding.start + o + q.length)⟩)
    (hE : ∀ a s', E' a s' →
      (p.Entry a → Run p.step (fun st st' => p.Edge st.pc st'.pc)
        (·.pc = Host.addrOf (Hp.embedding.start + p.length)) P (fun st => E st.pc st.data) ⟨s', a⟩) ∧
      (¬ p.Entry a → E a s')) :
    Run p.step (fun st st' => p.Edge st.pc st'.pc) (·.pc = Host.addrOf (Hp.embedding.start + p.length)) P
      (fun st => E st.pc st.data) ⟨s, Host.addrOf (Hp.embedding.start + o)⟩ := by
  have hp := Hp.embedding.isInfixAt
  rw [Program.wp_eq] at hw
  change Run q.step (fun st st' => q.Edge st.pc st'.pc) (·.pc = Host.addrOf (Hp.embedding.start + o + q.length))
    (Q' ·.data) (fun st => E' st.pc st.data) ⟨s, Host.addrOf (Hp.embedding.start + o)⟩ at hw
  generalize Hp.embedding.start = k at hp hQ hE hw ⊢
  have hqh : q.IsInfixAt Host.prog (k + o) := List.IsInfixAt.trans hq hp
  refine (?_ : ∀ x, Run q.step (fun st st' => q.Edge st.pc st'.pc) (·.pc = Host.addrOf (k + o + q.length))
      (Q' ·.data) (fun st => E' st.pc st.data) x →
      (∃ j, k + o ≤ j ∧ j ≤ k + o + q.length ∧ x.pc = Host.addrOf j) →
      Run p.step (fun st st' => p.Edge st.pc st'.pc) (·.pc = Host.addrOf (k + p.length)) P
        (fun st => E st.pc st.data) x) _ hw ⟨k + o, Nat.le_refl _, by omega, rfl⟩
  intro x h
  induction h with
  | done y h =>
    intro _
    obtain ⟨u, a⟩ := y
    obtain ⟨hs, hq'⟩ := h
    dsimp only at hs hq'
    subst hs
    exact hQ u hq'
  | step y next ht _ ih =>
    rintro ⟨j, hj₁, hj₂, hjy⟩
    obtain ⟨hns, hst⟩ := ht
    have hne : Host.addrOf j ≠ Host.addrOf (k + o + q.length) := hjy ▸ hns
    refine Run.step (next := Run p.step (fun st st' => p.Edge st.pc st'.pc)
        (·.pc = Host.addrOf (k + p.length)) P (fun st => E st.pc st.data))
      (fun h => Host.addrOf_ne_of_le hj₂ (by omega) hne (hjy ▸ h)) ?_ fun _ h => h
    refine Program.step_of_callee_eq (Program.callee_infix hq hcall y.pc) hst fun z hz => ?_
    by_cases hc : q.Edge y.pc z.pc
    · have hI : ∃ j, k + o ≤ j ∧ j ≤ k + o + q.length ∧ z.pc = Host.addrOf j := by
        rcases hc with hft | ⟨l, -, hql, hla⟩
        · obtain ⟨m, hm₁, hm₂, hm₃⟩ := Host.fallthrough_addrOf_of_ne hj₂ hne
          exact ⟨m + 1, by omega, by omega, by rw [hft, hjy, hm₃]⟩
        · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (Program.mem_labels.mp hql)
          have hilt : i < q.length := (List.getElem?_eq_some_iff.mp hi).1
          exact ⟨k + o + i, by omega, by omega, by rw [← hla, Host.label_eq hqh hi]⟩
      have hpc : p.Edge y.pc z.pc := hc.imp id (Program.entry_of_infix hq)
      simp only [hc, hpc, ↓reduceIte] at hz ⊢
      exact ih z hz hI
    · simp only [hc, ↓reduceIte] at hz
      have hE' := hE _ _ hz
      have hiff : p.Edge y.pc z.pc ↔ p.Entry z.pc :=
        ⟨fun h => h.resolve_left fun hft => hc (Or.inl hft), Or.inr⟩
      by_cases hpe : p.Edge y.pc z.pc
      · simp only [hpe, ↓reduceIte]
        exact hE'.1 (hiff.mp hpe)
      · simp only [hpe, ↓reduceIte]
        exact hE'.2 fun h' => hpe (hiff.mpr h')

end
