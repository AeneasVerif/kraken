module

public import Kraken.X64.OmniSemantics
public import Kraken.Data.List.Infix

@[grind hom] public theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

namespace Kraken.Executable

@[expose] public def sizeBefore (e : Kraken.Executable Directive) (n : Nat) : Nat := ((e.2.take n).map (·.2)).sum

@[expose] public def addrOf (e : Kraken.Executable Directive) (n : Nat) : Int64 := e.1 + .ofNat (e.sizeBefore n)

@[simp] public theorem addrOf_zero (e : Kraken.Executable Directive) : e.addrOf 0 = e.1 := by
  grind [sizeBefore, addrOf]

public theorem sizeBefore_succ (e : Kraken.Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) :
    e.sizeBefore (n + 1) = e.sizeBefore n + z := by
  grind [sizeBefore, List.take_add_one]

public theorem addrOf_succ (e : Kraken.Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) : e.addrOf (n + 1) = e.addrOf n + .ofNat z := by
  grind [addrOf, sizeBefore, List.take_add_one]

@[expose] public def _root_.Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s p (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
    d.interp s p next jmp = next s

end Kraken.Executable

/-
# Weakest precondition of a fragment of a linked program

A linked program defines a transition system over the machine states.

`LinkedProgram.step` below encodes the must-predecessor relation of the transition system.
Given a set of successor machine states `P`, `LinkedProgram.step st P` holds iff
`∀ st', (st ⤳ st') → st' ∈ P`.
This definition is expressed in terms of `Directive.interp`, which is considered ground truth.

`Program.wp` packages up the predecessor relation into a notion of weakest precondition, independent
of particular linking decisions. This definition is the bridge to `Std.WP` and thus `vcgen`.
The definition of `wp` works by
1. taking the least fixpoint of the predecessor relation via `Eventually`
   (equivalent notions of `lfp` exist) so that it applies to a sequence
   of directives, and crucially
2. considering every possible way in which the sequence of directives
   may be linked into the final `LinkedProgram`.
   Only properties can be proved that hold for *all possible linking positions* of the ambient program.
   The ambient program is a parameter to be able to express function calls compositionally.

Side note: Cousot calls `LinkedProgram.step` the "dual preimage property transformer" in his
2021 book "Principles of Abstract Interpretation", as a starting point for theory exploration.
-/

public class Host where
  prog : Program
  labels_nodup : (Program.labels prog).Nodup

public instance [Host] [layout : Layout] : Labels := Executable.labels (layout Host.prog)

public class Layout.Valid [Host] [layout : Layout] : Prop where
  label_size : ∀ i l, Host.prog[i]? = some (.label l) → Kraken.Layout.size Directive i = 0
  zero_inert : ∀ i d, Host.prog[i]? = some d → Kraken.Layout.size Directive i = 0 → d.Inert
  fits : ∀ j k m, j ≤ m → m < k → k ≤ Host.prog.length →
    (layout Host.prog).addrOf j = (layout Host.prog).addrOf k → Kraken.Layout.size Directive m = 0

/-- The predecessor relation of the transition system induced by the linked program. -/
@[expose] public def Host.step [Host] [layout : Layout] (st : MachineState) (P : MachineState → Prop) :
    Prop :=
  match (layout Host.prog).fetch? st.2 with
  | none => False
  | some (d, z) =>
    let next := st.2 + .ofNat z
    (d.interp st.1 ⟨st.2, next⟩ (fun s => .done (s, next)) (fun a s => .done (s, a))).All P
    -- The AI helpfully simplified the `∀ R, ...` to
    --   ∀ R next jmp, (P ⊆ next⁻¹(All R)) → (P ⊆ jmp⁻¹(All R)) → (d.interp s … next jmp).All R
    -- which highlights the predecessor nature under the CPS encoding rather nicely.
    -- SG hopes that adjusting `Directive.interp` could make this definition simpler.

/-- Weakest precondition of a fragment embedded in a linked program. -/
@[expose] public def Program.wp [Host] [layout : Layout] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.IsInfixAt Host.prog k →
    Eventually Host.step
      (fun st => (st.2 = (layout Host.prog).addrOf (k + p.length) ∧ Q st.1) ∨ E st.2 st.1)
      (s, (layout Host.prog).addrOf k)

public theorem Program.wp_mono [Host] [Layout] {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.wp p Q₁ E₁ s) : Program.wp p Q₂ E₂ s :=
  fun k hk => eventually_trans _ _ _ _ (h k hk) fun _ hb => Eventually.done _ <|
    hb.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)

public theorem Program.wp_cons [Host] [Layout] {d : Directive} {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.wp [d] (fun s' => Program.wp p Q E s') E s) : Program.wp (d :: p) Q E s := by
  intro k hk
  obtain ⟨hd, hp⟩ := List.IsInfixAt.append (a := [d]) hk
  refine eventually_trans _ _ _ _ (h k hd) ?_
  rintro ⟨s', a⟩ (⟨ha, hrun⟩ | hE)
  · dsimp only at ha hrun
    subst ha
    refine eventually_trans _ _ _ _ (hrun (k + 1) hp) fun _ hb => Eventually.done _ ?_
    rcases hb with ⟨hend, hq⟩ | hE
    · exact Or.inl ⟨by rw [hend, List.length_cons]; congr 1; omega, hq⟩
    · exact Or.inr hE
  · exact Eventually.done _ (Or.inr hE)
