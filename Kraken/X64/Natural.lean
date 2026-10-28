module

public import Kraken.X64.OmniSemantics
import Kraken.Attribute

/-
`Natural F` says that `F k` is one fixed `Effects` tree with the continuation `k` at its leaves.
So `(F k₁).All P₁`, `(F k₂).All P₂` and `(F k).All P` check the same inner nodes and differ only in
the leaves `k₁ x`, `k₂ x` and `k x`. Thus, if `(k₁ x).All P₁ → (k₂ x).All P₂ → (k x).All P` holds at
each leaf `x`, then `(F k₁).All P₁ → (F k₂).All P₂ → (F k).All P` holds as well.
`Executable.StepIn.and` uses this to combine two runs with different continuations into one run.

The proofs follow the syntax of `F`: each `@[natural]` lemma states that one `Effects` constructor
or helper preserves `Natural`, and `simp [natural]` composes them along a definition, like `fun_prop`.
-/
@[expose] public def Natural {α : Type} (F : (α → Effects) → Effects) : Prop :=
  ∀ (P₁ P₂ P : MachineState → Prop) (k₁ k₂ k : α → Effects),
    (∀ x, (k₁ x).All P₁ → (k₂ x).All P₂ → (k x).All P) →
    (F k₁).All P₁ → (F k₂).All P₂ → (F k).All P

namespace Natural
variable {α : Type}

@[natural] theorem cont (x : α) : Natural (fun k : α → Effects => k x) := fun _ _ _ _ _ _ h => h x

theorem bind {β : Type} {F : (α → Effects) → Effects} {G : α → (β → Effects) → Effects}
    (hF : Natural F) (hG : ∀ x, Natural (G x)) : Natural (fun k => F (fun x => G x k)) :=
  fun _ _ _ _ _ _ hk => hF _ _ _ _ _ _ fun x => hG x _ _ _ _ _ _ hk

@[natural] theorem unimplemented (m : String) : Natural (fun _ : α → Effects => Effects.unimplemented m) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] theorem gp_unaligned (a : BitVec 64) (n : Nat) : Natural (fun _ : α → Effects => Effects.gp_unaligned a n) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] theorem undefined {β : Type} [NondetSupportingType β] {G : β → (α → Effects) → Effects}
    (h : ∀ v, Natural (G v)) : Natural (fun k => Effects.undefined (fun v => G v k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ v => h v _ _ _ _ _ _ hk (h₁ v) (h₂ v)

@[natural] theorem nonmem_load {dm : DataMem} {a : BitVec 64} {w : Width} {G : w.type → DataMem → (α → Effects) → Effects} :
    Natural (fun k => Effects.nonmem_load dm a w (fun v d => G v d k)) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] theorem nonmem_store {dm : DataMem} {a : BitVec 64} {w : Width} {v : w.type} {G : DataMem → (α → Effects) → Effects} :
    Natural (fun k => Effects.nonmem_store dm a v (fun d => G d k)) :=
  fun _ _ _ _ _ _ _ h => h.elim

@[natural] theorem require_read_access {a : BitVec 64} {w : Width} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_read_access a w (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () _ _ _ _ _ _ hk h₁ h₂

@[natural] theorem require_write_access {a : BitVec 64} {w : Width} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_write_access a w (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () _ _ _ _ _ _ hk h₁ h₂

@[natural] theorem require_exec_access {r : Std.Rco Int64} {G : Unit → (α → Effects) → Effects}
    (h : ∀ u, Natural (G u)) : Natural (fun k => Effects.require_exec_access r (fun u => G u k)) :=
  fun _ _ _ _ _ _ hk h₁ h₂ => h () _ _ _ _ _ _ hk h₁ h₂

@[natural] theorem ite {c : Prop} [Decidable c] {F G : (α → Effects) → Effects} (hF : Natural F) (hG : Natural G) :
    Natural (fun k => if c then F k else G k) := by
  by_cases hc : c
  · rw [show (fun k => if c then F k else G k) = F from funext fun _ => ite_eq_left hc]; exact hF
  · rw [show (fun k => if c then F k else G k) = G from funext fun _ => ite_eq_right hc]; exact hG

@[natural] theorem dite {c : Prop} [Decidable c] {F : c → (α → Effects) → Effects} {G : ¬ c → (α → Effects) → Effects}
    (hF : ∀ h, Natural (F h)) (hG : ∀ h, Natural (G h)) :
    Natural (fun k => if h : c then F h k else G h k) := by
  by_cases hc : c
  · rw [show (fun k => if h : c then F h k else G h k) = F hc from funext fun _ => dite_eq_left hc]; exact hF hc
  · rw [show (fun k => if h : c then F h k else G h k) = G hc from funext fun _ => dite_eq_right hc]; exact hG hc

end Natural

variable {α : Type}

@[natural] theorem MachineData.load_natural {s : MachineData} {a : BitVec 64} {w : Width}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => s.load a w (fun v s => G v s k)) := by
  unfold MachineData.load
  refine Natural.require_read_access fun _ => ?_
  split
  · exact h _ _
  · exact Natural.nonmem_load

@[natural] theorem MachineData.store_natural {s : MachineData} {a : BitVec 64} {w : Width} {v : w.type}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.store a v (fun s => G s k)) := by
  unfold MachineData.store
  refine Natural.require_write_access fun _ => ?_
  split
  · exact h _
  · exact Natural.nonmem_store


@[natural] theorem MachineData.loadAvx_natural {s : MachineData} {a : BitVec 64} {w : AvxWidth} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => s.loadAvx a w (fun v s => G v s k) ca) := by
  unfold MachineData.loadAvx
  refine Natural.ite (Natural.gp_unaligned _ _) (Natural.require_read_access fun _ => ?_)
  split
  · exact h _ _
  · exact Natural.unimplemented _

@[natural] theorem MachineData.storeAvx_natural {s : MachineData} {a : BitVec 64} {w : AvxWidth} {v : w.type} {ca : Bool}
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

@[natural] theorem AvxRegOrMem.interp_natural {w} {o : AvxRegOrMem w} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k) ca) := by
  cases o
  · exact h _ _
  · exact MachineData.loadAvx_natural h

@[natural] theorem AvxOperand.interp_natural {w} {o : AvxOperand w} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k) ca) := by
  cases o
  exact AvxRegOrMem.interp_natural h

@[natural] theorem MachineData.setAvx_natural {w} {d : AvxDst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.setAvx d v p (fun s => G s k) ca) := by
  cases d
  · exact h _
  · exact MachineData.storeAvx_natural h

@[natural] theorem MachineData.setAvxLegacy_natural {w} {d : AvxDst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64} {ca : Bool}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.setAvxLegacy d v p (fun s => G s k) ca) := by
  cases d
  · exact h _
  · exact MachineData.storeAvx_natural h


@[natural] theorem RegOrMem.interp_natural {w} {o : RegOrMem w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact h _ _
  · exact MachineData.load_natural h

@[natural] theorem Operand.interp_natural {w} {o : Operand w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact RegOrMem.interp_natural h
  · exact h _ _

@[natural] theorem MachineData.set_natural {w} {d : Dst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64}
    {G : MachineData → (α → Effects) → Effects} (h : ∀ s, Natural (G s)) :
    Natural (fun k => s.set d v p (fun s => G s k)) := by
  cases d
  · exact h _
  · exact MachineData.store_natural h

@[natural] theorem RelRegOrMem.interp_natural {o : RelRegOrMem} {s : MachineData} {p : Std.Rco Int64}
    {G : BitVec 64 → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => o.interp s p (fun v s => G v s k)) := by
  cases o
  · exact h _ _
  · exact h _ _
  · exact MachineData.load_natural h


omit [Labels] [AddressSize] in
@[natural] theorem Reg.interp_natural {w} {r : Reg w} {s : MachineData} {p : Std.Rco Int64}
    {G : w.type → MachineData → (α → Effects) → Effects} (h : ∀ v s, Natural (G v s)) :
    Natural (fun k => r.interp s p (fun v s => G v s k)) := h _ _

@[natural] theorem Operation.interp_natural {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      op.interp p s (fun s => k (.inl s)) (fun a s => k (.inr (a, s)))) := by
  cases op <;> natural Operation.interp <;> cases w <;> natural Operation.interp

@[natural] theorem AvxOperation.interp_natural {w} (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      op.interp p s (fun s => k (.inl s))) := by
  cases op <;> natural AvxOperation.interp

end

@[natural] theorem Instr.interp_natural [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64) :
    Natural (fun k : MachineData ⊕ (Int64 × MachineData) → Effects =>
      i.interp s p (fun s => k (.inl s)) (fun a s => k (.inr (a, s)))) := by
  cases i <;> natural Instr.interp

theorem Directive.interp_natural [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64) :
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
