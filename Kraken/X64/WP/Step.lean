module

public import Kraken.X64.OmniSemantics
import Kraken.Attribute

/-
`Natural F` relates three runs of the CPS functional `F` that differ only in their continuations.
The proofs below use only the continuation, the `Effects` constructors, `ite`, `dite`, `match` on
data and the CPS helpers. So the same proofs show the property for every relation
`R : (ι → Effects) → Prop` on an indexed tuple of trees that is closed under each `Effects`
constructor, applied componentwise with the same non-continuation arguments:
`(∀ x, R fun i => k i x) → R fun i => F (k i)`.
`Natural` is the instance `ι := Fin 3`, `R e := (e 0).All P₁ → (e 1).All P₂ → (e 2).All P`.
For that general form, each closure lemma becomes one closure field of `R`.
-/
@[expose] public def Natural {α : Type} (F : (α → Effects) → Effects) : Prop :=
  ∀ ⦃P₁ P₂ P : MachineState → Prop⦄ ⦃k₁ k₂ k : α → Effects⦄,
    (∀ x, (k₁ x).All P₁ → (k₂ x).All P₂ → (k x).All P) →
    (F k₁).All P₁ → (F k₂).All P₂ → (F k).All P

namespace Natural
variable {α : Type}

@[natural] public theorem cont (x : α) : Natural (fun k : α → Effects => k x) := fun _ _ _ _ _ _ h => h x

public theorem bind {β : Type} {F : (α → Effects) → Effects} {G : α → (β → Effects) → Effects}
    (hF : Natural F) (hG : ∀ x, Natural (G x)) : Natural (fun k => F (fun x => G x k)) :=
  fun _ _ _ _ _ _ hk => hF fun x => hG x hk

@[natural] public theorem unimplemented (m : String) : Natural (fun _ : α → Effects => Effects.unimplemented m) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] public theorem gp_unaligned (a : BitVec 64) (n : Nat) : Natural (fun _ : α → Effects => Effects.gp_unaligned a n) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] public theorem undefined {β : Type} [NondetSupportingType β] {G : β → (α → Effects) → Effects}
    (h : ∀ v, Natural (G v)) : Natural (fun k => Effects.undefined (fun v => G v k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ v => h v hk (h₁ v) (h₂ v)

@[natural] public theorem nonmem_load {dm : DataMem} {a : BitVec 64} {w : Width} {G : w.type → DataMem → (α → Effects) → Effects} :
    Natural (fun k => Effects.nonmem_load dm a w (fun v d => G v d k)) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] public theorem nonmem_store {dm : DataMem} {a : BitVec 64} {w : Width} {v : w.type} {G : DataMem → (α → Effects) → Effects} :
    Natural (fun k => Effects.nonmem_store dm a v (fun d => G d k)) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] public theorem require_read_access {a : BitVec 64} {w : Width} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_read_access a w (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () hk h₁ h₂

@[natural] public theorem require_write_access {a : BitVec 64} {w : Width} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_write_access a w (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () hk h₁ h₂

@[natural] public theorem require_exec_access {r : Std.Rco Int64} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_exec_access r (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () hk h₁ h₂

@[natural] public theorem ite {c : Prop} [Decidable c] {F G : (α → Effects) → Effects} (hF : Natural F) (hG : Natural G) :
    Natural (fun k => if c then F k else G k) := by
  by_cases hc : c
  · rw [show (fun k => if c then F k else G k) = F from funext fun _ => if_pos hc]; exact hF
  · rw [show (fun k => if c then F k else G k) = G from funext fun _ => if_neg hc]; exact hG

@[natural] public theorem dite {c : Prop} [Decidable c] {F : c → (α → Effects) → Effects} {G : ¬ c → (α → Effects) → Effects}
    (hF : ∀ h, Natural (F h)) (hG : ∀ h, Natural (G h)) :
    Natural (fun k => if h : c then F h k else G h k) := by
  by_cases hc : c
  · rw [show (fun k => if h : c then F h k else G h k) = F hc from funext fun _ => dif_pos hc]; exact hF hc
  · rw [show (fun k => if h : c then F h k else G h k) = G hc from funext fun _ => dif_neg hc]; exact hG hc

end Natural

variable {α : Type}

@[natural] public theorem MachineData.load_natural {s : MachineData} {a : BitVec 64} {w : Width}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => s.load a w (fun v s => G v s k)) := by
  unfold MachineData.load
  refine Natural.require_read_access fun _ => ?_
  split
  · exact h _ _
  · exact Natural.nonmem_load

@[natural] public theorem MachineData.store_natural {s : MachineData} {a : BitVec 64} {w : Width} {v : w.type}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.store a v (fun s => G s k)) := by
  unfold MachineData.store
  refine Natural.require_write_access fun _ => ?_
  split
  · exact h _
  · exact Natural.nonmem_store


@[natural] public theorem MachineData.loadAvx_natural {s : MachineData} {a : BitVec 64} {w : AvxWidth} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => s.loadAvx a w (fun v s => G v s k) ca) := by
  unfold MachineData.loadAvx
  refine Natural.ite (Natural.gp_unaligned _ _) (Natural.require_read_access fun _ => ?_)
  split
  · exact h _ _
  · exact Natural.unimplemented _

@[natural] public theorem MachineData.storeAvx_natural {s : MachineData} {a : BitVec 64} {w : AvxWidth} {v : w.type} {ca : Bool}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.storeAvx a v (fun s => G s k) ca) := by
  unfold MachineData.storeAvx
  refine Natural.ite (Natural.gp_unaligned _ _) (Natural.require_write_access fun _ => ?_)
  split
  · exact h _
  · exact Natural.unimplemented _

local macro "natural" d:ident : tactic =>
  `(tactic| simp (maxDischargeDepth := 64) [natural, $d:ident])

section
variable [Labels] [AddressSize]

@[natural] public theorem AvxRegOrMem.interp_natural {w} {o : AvxRegOrMem w} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k) ca) := by
  cases o
  · exact h _ _
  · exact MachineData.loadAvx_natural h

@[natural] public theorem AvxOperand.interp_natural {w} {o : AvxOperand w} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k) ca) := by
  cases o
  exact AvxRegOrMem.interp_natural h

@[natural] public theorem MachineData.setAvx_natural {w} {d : AvxDst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.setAvx d v p (fun s => G s k) ca) := by
  cases d
  · exact h _
  · exact MachineData.storeAvx_natural h

@[natural] public theorem MachineData.setAvxLegacy_natural {w} {d : AvxDst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.setAvxLegacy d v p (fun s => G s k) ca) := by
  cases d
  · exact h _
  · exact MachineData.storeAvx_natural h


@[natural] public theorem RegOrMem.interp_natural {w} {o : RegOrMem w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact h _ _
  · exact MachineData.load_natural h

@[natural] public theorem Operand.interp_natural {w} {o : Operand w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact RegOrMem.interp_natural h
  · exact h _ _

@[natural] public theorem MachineData.set_natural {w} {d : Dst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.set d v p (fun s => G s k)) := by
  cases d
  · exact h _
  · exact MachineData.store_natural h

@[natural] public theorem RelRegOrMem.interp_natural {o : RelRegOrMem} {s : MachineData} {p : Std.Rco Int64}
    {G : BitVec 64 → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact h _ _
  · exact h _ _
  · exact MachineData.load_natural h


@[natural] public theorem Reg.interp_natural {w} {r : Reg w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => r.interp s p (fun v s => G v s k)) := h _ _

@[natural] public theorem Operation.interp_natural {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      op.interp p s (fun s => k (.inl s)) (fun a s => k (.inr (a, s)))) := by
  cases op <;> natural Operation.interp <;> cases w <;> natural Operation.interp

@[natural] public theorem AvxOperation.interp_natural {w} (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      op.interp p s (fun s => k (.inl s))) := by
  cases op <;> natural AvxOperation.interp

end

@[natural] public theorem Instr.interp_natural [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      i.interp s p (fun s => k (.inl s)) (fun a s => k (.inr (a, s)))) := by
  cases i <;> natural Instr.interp

public theorem Directive.interp_natural [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      d.interp s p (fun s => k (.inl s)) (fun a s => k (.inr (a, s)))) := by
  cases d <;> natural Directive.interp

public theorem Directives.interp_natural [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) :
    Natural (fun k : (Int64 × MachineData) ⊕ (Int64 × MachineData) → Effects =>
      Directives.interp ds s pc (fun a s => k (.inl (a, s))) (fun a s => k (.inr (a, s)))) := by
  induction ds generalizing s pc with
  | nil => exact Natural.cont _
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    exact Natural.bind (Directive.interp_natural d s ⟨pc, pc + .ofNat z⟩)
      (G := fun x k => Sum.elim (fun s' => Directives.interp ds s' (pc + .ofNat z) (fun a s => k (Sum.inl (a, s)))
        (fun a s => k (Sum.inr (a, s)))) (fun x => k (Sum.inr x)) x)
      fun x => by
        rcases x with s' | x
        · exact ih s' _
        · exact Natural.cont _

@[expose] public def Directives.endPc (ds : List (Kraken.Sized Directive)) (pc : Int64) : Int64 :=
  match ds with
  | [] => pc
  | c :: ds => Directives.endPc ds (pc + .ofNat c.size)

public theorem Directives.endPc_append (ds ds' : List (Kraken.Sized Directive)) (pc : Int64) :
    Directives.endPc (ds ++ ds') pc = Directives.endPc ds' (Directives.endPc ds pc) := by
  induction ds generalizing pc with
  | nil => rfl
  | cons c ds ih => exact ih _

public theorem Directives.endPc_of_size_zero {ds : List (Kraken.Sized Directive)} (h : ∀ c ∈ ds, c.size = 0)
    (pc : Int64) : Directives.endPc ds pc = pc := by
  induction ds generalizing pc with
  | nil => rfl
  | cons c ds ih =>
    have hc : pc + Int64.ofNat c.size = pc := by rw [h c List.mem_cons_self]; simp
    simp only [Directives.endPc, hc]
    exact ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) pc

public theorem Directives.interp_ret_congr [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) {ret ret' jmp : Int64 → MachineData → Effects}
    (h : ∀ s, ret (Directives.endPc ds pc) s = ret' (Directives.endPc ds pc) s) :
    Directives.interp ds s pc ret jmp = Directives.interp ds s pc ret' jmp := by
  induction ds generalizing s pc with
  | nil => exact h s
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    simp only [Directives.interp]
    congr 1
    funext s'
    exact ih s' _ h

@[expose] public def Executable.fallthrough (e : Executable) (a : Int64) : Int64 :=
  Directives.endPc (e.directivesAtAddress a) a

@[expose] public def Executable.StepIn (e : Executable) (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  let := e.labels
  ∀ ⦃P : MachineState → Prop⦄ ⦃ret jmp : MachineState → Effects⦄,
    (∀ st', next st' → (ret st').All P) → (∀ st', jump st' → (jmp st').All P) →
      (Directives.interp (e.directivesAtAddress st.pc) st.data st.pc (fun a s => ret ⟨s, a⟩)
        (fun a s => jmp ⟨s, a⟩)).All P

namespace Executable.StepIn
variable {e : Executable} {st : MachineState}

public theorem mono {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h : e.StepIn next₁ jump₁ st)
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) : e.StepIn next₂ jump₂ st :=
  fun _ _ _ hr hk => h (fun u h => hr u (hn u h)) (fun u h => hk u (hj u h))

open Classical in
public theorem and {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h₁ : e.StepIn next₁ jump₁ st)
    (h₂ : e.StepIn next₂ jump₂ st) :
    e.StepIn (fun u => next₁ u ∧ next₂ u) (fun u => jump₁ u ∧ jump₂ u) st := by
  intro P r j hr hj
  let probe : Prop → Effects := fun c => if c then .done st else .unimplemented ""
  have hprobe : ∀ c, (probe c).All (fun _ => True) ↔ c := fun c => by
    by_cases hc : c <;> simp [probe, hc, Effects.All]
  have t₁ := @h₁ (fun _ => True) (fun u => probe (next₁ u)) (fun u => probe (jump₁ u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  have t₂ := @h₂ (fun _ => True) (fun u => probe (next₂ u)) (fun u => probe (jump₂ u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  refine @Directives.interp_natural e.labels (e.directivesAtAddress st.pc) st.data st.pc _ _ P
    (Sum.elim (fun x => probe (next₁ ⟨x.2, x.1⟩)) (fun x => probe (jump₁ ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => probe (next₂ ⟨x.2, x.1⟩)) (fun x => probe (jump₂ ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => r ⟨x.2, x.1⟩) (fun x => j ⟨x.2, x.1⟩)) ?_ t₁ t₂
  rintro (⟨a, s⟩ | ⟨a, s⟩) e₁ e₂
  · exact hr _ ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩
  · exact hj _ ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩

open Classical in
public theorem restrict {next jump : MachineState → Prop} (h : e.StepIn next jump st) :
    e.StepIn (fun u => next u ∧ u.pc = e.fallthrough st.pc) jump st := by
  intro P r j hr hj
  let probe : Prop → Effects := fun c => if c then .done st else .unimplemented ""
  have hprobe : ∀ c, (probe c).All (fun _ => True) ↔ c := fun c => by
    by_cases hc : c <;> simp [probe, hc, Effects.All]
  have t := @h (fun _ => True) (fun u => probe (next u)) (fun u => probe (jump u))
    (fun _ h => (hprobe _).mpr h) (fun _ h => (hprobe _).mpr h)
  have e₁ := @Directives.interp_ret_congr e.labels (e.directivesAtAddress st.pc) st.data st.pc
    (fun a s => probe (next ⟨s, a⟩)) (fun _ s => probe (next ⟨s, e.fallthrough st.pc⟩))
    (fun a s => probe (jump ⟨s, a⟩)) (fun _ => rfl)
  have e₂ := @Directives.interp_ret_congr e.labels (e.directivesAtAddress st.pc) st.data st.pc
    (fun a s => r ⟨s, a⟩) (fun _ s => r ⟨s, e.fallthrough st.pc⟩) (fun a s => j ⟨s, a⟩) (fun _ => rfl)
  change (@Directives.interp e.labels _ _ _ _ _).All _ at t
  change (@Directives.interp e.labels _ _ _ _ _).All _
  rw [e₁] at t
  rw [e₂]
  refine @Directives.interp_natural e.labels (e.directivesAtAddress st.pc) st.data st.pc _ _ P
    (Sum.elim (fun x => probe (next ⟨x.2, e.fallthrough st.pc⟩)) (fun x => probe (jump ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => probe (next ⟨x.2, e.fallthrough st.pc⟩)) (fun x => probe (jump ⟨x.2, x.1⟩)))
    (Sum.elim (fun x => r ⟨x.2, e.fallthrough st.pc⟩) (fun x => j ⟨x.2, x.1⟩)) ?_ t t
  rintro (⟨a, s⟩ | ⟨a, s⟩) e₁ _
  · exact hr _ ⟨(hprobe _).mp e₁, rfl⟩
  · exact hj _ ((hprobe _).mp e₁)

public theorem all [Layout] {next jump post : MachineState → Prop} (h : e.StepIn next jump st)
    (hn : ∀ u, next u → post u) (hj : ∀ u, jump u → post u) : step1 e st post := by
  unfold step1 Executable.step
  exact h (fun _ h => hn _ h) (fun _ h => hj _ h)

open Lean.Order in
@[partial_fixpoint_monotone] public theorem monotone {α : Type} [PartialOrder α] {next : MachineState → Prop}
    (f : α → MachineState → ImplicationOrder) (hf : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepIn next (f x) st) :=
  fun _ _ hxy hx => hx.mono (fun _ h => h) fun u => hf _ _ hxy u

end Executable.StepIn

-- the stack pointer of `s'` lies below that of the reference state `s`
@[expose] public def MachineData.StackBelow (s' s : MachineData) : Prop :=
  0 < (s.regs.get64 .rsp - s'.regs.get64 .rsp).toInt

-- the stack pointer of `s'` lies at or below that of the reference state `s`
public abbrev MachineData.StackAtOrBelow (s' s : MachineData) : Prop := ¬ s.StackBelow s'

@[grind <=] public theorem MachineData.stackBelow_of_add_eight {s s' : MachineData}
    (h : s'.regs.get64 .rsp + 8#64 = s.regs.get64 .rsp) : s'.StackBelow s := by
  show 0 < (s.regs.get64 .rsp - s'.regs.get64 .rsp).toInt
  rw [← h]
  generalize s'.regs.get64 .rsp = x
  rw [show x + 8#64 - x = 8#64 by bv_omega]
  decide

public theorem MachineData.stackAtOrBelow_of_rsp_eq {s s' : MachineData}
    (h : s'.regs.get64 .rsp = s.regs.get64 .rsp) : s'.StackAtOrBelow s := by
  show ¬ 0 < (s'.regs.get64 .rsp - s.regs.get64 .rsp).toInt
  rw [h]
  simp

open Classical in
@[expose] public def Executable.StepOut (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (st : MachineState) (next jump : MachineState → Prop) (st' : MachineState) : Prop :=
  match callee st'.pc with
  | some wp =>
    if st'.data.StackBelow st.data then
      wp (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' else jump st'') st'.data
    else jump st'
  | none => jump st'

@[expose] public def Executable.StepOver (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (next jump : MachineState → Prop) (st : MachineState) : Prop :=
  e.StepIn next (e.StepOut callee st next jump) st

-- `callee₂` asks no more than `callee₁` at every address, for a weaker exit post
@[expose] public def Executable.CalleeLe (callee₁ callee₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)) :
    Prop :=
  ∀ a, Option.Rel (fun wp₁ wp₂ => ∀ (R₁ R₂ : MachineState → Prop) s, (∀ u, R₁ u → R₂ u) → wp₁ R₁ s → wp₂ R₂ s)
    (callee₁ a) (callee₂ a)

namespace Executable
variable {e : Executable} {st : MachineState}
  {callee callee₁ callee₂ : Int64 → Option ((MachineState → Prop) → MachineData → Prop)}

public theorem StepOut.of_not_below {next jump : MachineState → Prop} {st' : MachineState}
    (h : ¬ st'.data.StackBelow st.data) : e.StepOut callee st next jump st' ↔ jump st' := by
  unfold StepOut
  split <;> simp [h]

public theorem StepOut.of_not_below_data {next jump : MachineState → Prop} {s s' : MachineData} {pc a : Int64}
    (h : ¬ s'.StackBelow s) :
    e.StepOut callee ⟨s, pc⟩ next jump ⟨s', a⟩ ↔ jump ⟨s', a⟩ :=
  StepOut.of_not_below (st := ⟨s, pc⟩) (st' := ⟨s', a⟩) h

public theorem StepOut.imp (hc : CalleeLe callee₁ callee₂) {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) {st' : MachineState}
    (h : e.StepOut callee₁ st next₁ jump₁ st') : e.StepOut callee₂ st next₂ jump₂ st' := by
  unfold StepOut at h ⊢
  have hca := hc st'.pc
  revert h
  cases h₁ : callee₁ st'.pc <;> cases h₂ : callee₂ st'.pc <;> rw [h₁, h₂] at hca <;> cases hca
  · exact hj _
  · rename_i wp₁ wp₂ hw
    dsimp only
    split
    · exact hw _ _ _ fun u => by split <;> simp_all
    · exact hj _

public theorem StepOver.imp (hc : CalleeLe callee₁ callee₂) {next₁ next₂ jump₁ jump₂ : MachineState → Prop}
    (h : e.StepOver callee₁ next₁ jump₁ st) (hn : ∀ u, next₁ u → next₂ u) (hj : ∀ u, jump₁ u → jump₂ u) :
    e.StepOver callee₂ next₂ jump₂ st :=
  StepIn.mono h hn fun _ => StepOut.imp hc hn hj

public theorem StepOver.restrict {next jump : MachineState → Prop} (h : e.StepOver callee next jump st) :
    e.StepOver callee (fun u => next u ∧ u.pc = e.fallthrough st.pc) jump st := by
  refine StepIn.mono (StepIn.restrict h) (fun _ h => h) fun st' h => ?_
  have hR : (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' ∧ st''.pc = e.fallthrough st.pc
      else jump st'') = (fun st'' => if st''.pc = e.fallthrough st.pc then next st'' else jump st'') :=
    funext fun u => by by_cases hu : u.pc = e.fallthrough st.pc <;> simp [hu]
  unfold StepOut at h ⊢
  rw [hR]
  exact h

public theorem StepOver.of_callee {next jump : MachineState → Prop}
    (hc : ∀ a, Option.Rel (fun wp₁ wp₂ => ∀ R s, wp₁ R s → wp₂ R s) (callee₁ a) (callee₂ a))
    (h : e.StepOver callee₁ next jump st) : e.StepOver callee₂ next jump st := by
  refine StepIn.mono h (fun _ h => h) fun st' h => ?_
  unfold StepOut at h ⊢
  have hca := hc st'.pc
  revert h
  cases h₁ : callee₁ st'.pc <;> cases h₂ : callee₂ st'.pc <;> rw [h₁, h₂] at hca <;> cases hca
  · exact id
  · rename_i hw
    dsimp only
    split
    · exact hw _ _
    · exact id

open Lean.Order in
@[partial_fixpoint_monotone] public theorem StepOver.monotone_map {α β : Type} [PartialOrder α]
    {next jump : MachineState → Prop} (o : Int64 → Option β)
    (g : α → β → (MachineState → Prop) → MachineData → ImplicationOrder) (hg : monotone g) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => e.StepOver (fun a => (o a).map (g x)) next jump st) := by
  intro x y hxy hx
  refine StepOver.of_callee (fun a => ?_) hx
  cases o a with
  | none => exact Option.Rel.none
  | some b => exact Option.Rel.some fun R s h => hg _ _ hxy b R s h

open Lean.Order in
@[partial_fixpoint_monotone] public theorem StepOver.monotone_map_fun {α β : Type} [PartialOrder α]
    {next jump : MachineState → Prop} (o : Int64 → Option β)
    (g : α → β → (MachineState → Prop) → MachineData → ImplicationOrder) (hg : monotone g) :
    @monotone _ _ _ (@instOrderPi MachineState (fun _ => ImplicationOrder) fun _ => ImplicationOrder.instOrder)
      (fun x => e.StepOver (fun a => (o a).map (g x)) next jump) :=
  fun _ _ hxy st => StepOver.monotone_map (st := st) o g hg _ _ hxy

end Executable
