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
  · rw [show (fun k => if c then F k else G k) = F from funext fun _ => ite_eq_left hc]; exact hF
  · rw [show (fun k => if c then F k else G k) = G from funext fun _ => ite_eq_right hc]; exact hG

@[natural] public theorem dite {c : Prop} [Decidable c] {F : c → (α → Effects) → Effects} {G : ¬ c → (α → Effects) → Effects}
    (hF : ∀ h, Natural (F h)) (hG : ∀ h, Natural (G h)) :
    Natural (fun k => if h : c then F h k else G h k) := by
  by_cases hc : c
  · rw [show (fun k => if h : c then F h k else G h k) = F hc from funext fun _ => dite_eq_left hc]; exact hF hc
  · rw [show (fun k => if h : c then F h k else G h k) = G hc from funext fun _ => dite_eq_right hc]; exact hG hc

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


omit [Labels] [AddressSize] in
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

public theorem Directives.interp_ret_congr [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) {ret ret' jmp : Int64 → MachineData → Effects}
    (h : ∀ s, ret (pc + .ofNat (ds.map (·.size)).sum) s = ret' (pc + .ofNat (ds.map (·.size)).sum) s) :
    Directives.interp ds s pc ret jmp = Directives.interp ds s pc ret' jmp := by
  induction ds generalizing s pc with
  | nil => simpa [Directives.interp] using h s
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    simp only [Directives.interp]
    congr 1
    funext s'
    refine ih s' _ fun s => ?_
    simpa only [List.map_cons, List.sum_cons, Int64.ofNat_add, Int64.add_assoc] using h s
