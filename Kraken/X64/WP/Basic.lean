module

public import Kraken.X64.OmniSemantics

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

public class LinkedProgram where
  exe : Executable

public instance [LinkedProgram] : Labels := Executable.labels LinkedProgram.exe

/-- The predecessor relation of the transition system induced by the linked program. -/
@[expose] public def LinkedProgram.step [LinkedProgram] (st : MachineState) (P : MachineState → Prop) : Prop :=
  ∃ j d z, LinkedProgram.exe.2[j]? = some (d, z) ∧ st.2 = LinkedProgram.exe.addrOf j ∧
    ∀ (R : MachineState → Prop) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects),
      (∀ s', P (s', LinkedProgram.exe.addrOf (j + 1)) → (next s').All R) →
      (∀ a s', P (s', a) → (jmp a s').All R) →
      (d.interp st.1 ⟨LinkedProgram.exe.addrOf j, LinkedProgram.exe.addrOf (j + 1)⟩ next jmp).All R
    -- The AI helpfully simplified the `∀ R, ...` to
    --   ∀ R next jmp, (P ⊆ next⁻¹(All R)) → (P ⊆ jmp⁻¹(All R)) → (d.interp s … next jmp).All R
    -- which highlights the predecessor nature under the CPS encoding rather nicely.
    -- SG hopes that adjusting `Directive.interp` could make this definition simpler.

@[expose] public def Program.LinkedAt [LinkedProgram] (p : Program) (k : Nat) : Prop :=
  p <+: (LinkedProgram.exe.2.map (·.1)).drop k ∧
  ∀ i l, p[i]? = some (Directive.label l) → label l = LinkedProgram.exe.addrOf (k + i)

/-- Weakest precondition of a fragment embedded in a linked program. -/
@[expose] public def Program.wp [LinkedProgram] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.LinkedAt k →
    Eventually LinkedProgram.step
      (fun st => (st.2 = LinkedProgram.exe.addrOf (k + p.length) ∧ Q st.1) ∨ E st.2 st.1)
      (s, LinkedProgram.exe.addrOf k)

public theorem Program.wp_mono [LinkedProgram] {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.wp p Q₁ E₁ s) : Program.wp p Q₂ E₂ s :=
  fun k hk => eventually_trans _ _ _ _ (h k hk) fun _ hb => Eventually.done _ <|
    hb.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)

public theorem List.cons_prefix_drop {α : Type} {d : α} {q L : List α} {k : Nat}
    (h : (d :: q) <+: L.drop k) : L[k]? = some d ∧ q <+: L.drop (k + 1) := by
  have hk : k < L.length := by
    have := h.length_le; grind
  rw [List.drop_eq_getElem_cons hk, List.cons_prefix_iff] at h
  grind

public theorem Program.LinkedAt.append [LinkedProgram] {a b : Program} {k : Nat}
    (h : Program.LinkedAt (a ++ b) k) : a.LinkedAt k ∧ b.LinkedAt (k + a.length) := by
  obtain ⟨⟨t, ht⟩, hlab⟩ := h
  refine ⟨⟨⟨b ++ t, by rw [← ht, List.append_assoc]⟩, fun i l hi => hlab i l ?_⟩,
    ⟨⟨t, ?_⟩, fun i l hi => ?_⟩⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
    exact hi
  · rw [← List.drop_drop, ← ht, List.append_assoc, List.drop_left]
  · rw [hlab (a.length + i) l (by rw [List.getElem?_append_right (by omega)]; simpa using hi),
      Nat.add_assoc]

public theorem Program.LinkedAt.drop [LinkedProgram] {p : Program} {k : Nat} (h : p.LinkedAt k) (m : Nat) :
    Program.LinkedAt (p.drop m) (k + m) := by
  by_cases hm : m ≤ p.length
  · have h' := (Program.LinkedAt.append (a := p.take m) (b := p.drop m)
      (by rwa [List.take_append_drop])).2
    rwa [List.length_take_of_le hm] at h'
  · rw [List.drop_eq_nil_of_le (show p.length ≤ m by omega)]
    exact ⟨List.nil_prefix, fun _ _ h => by simp at h⟩

public theorem Program.wp_cons [LinkedProgram] {d : Directive} {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.wp [d] (fun s' => Program.wp p Q E s') E s) : Program.wp (d :: p) Q E s := by
  intro k hk
  obtain ⟨hd, hp⟩ := Program.LinkedAt.append (a := [d]) hk
  refine eventually_trans _ _ _ _ (h k hd) ?_
  rintro ⟨s', a⟩ (⟨ha, hrun⟩ | hE)
  · dsimp only at ha hrun
    subst ha
    refine eventually_trans _ _ _ _ (hrun (k + 1) hp) fun _ hb => Eventually.done _ ?_
    rcases hb with ⟨hend, hq⟩ | hE
    · exact Or.inl ⟨by rw [hend, List.length_cons]; congr 1; omega, hq⟩
    · exact Or.inr hE
  · exact Eventually.done _ (Or.inr hE)

public theorem LinkedProgram.cell_of_prefix [LinkedProgram] {d : Directive} {p : Program} {k : Nat}
    (h : (d :: p) <+: (LinkedProgram.exe.2.map (·.1)).drop k) : ∃ z, LinkedProgram.exe.2[k]? = some (d, z) := by
  have hd := (List.cons_prefix_drop h).1
  rw [List.getElem?_map] at hd
  cases hc : LinkedProgram.exe.2[k]? with
  | none => rw [hc] at hd; cases hd
  | some c =>
    rw [hc] at hd
    obtain ⟨d', z⟩ := c
    cases hd
    exact ⟨z, rfl⟩

public theorem LinkedProgram.eventually_cell [LinkedProgram] {k : Nat} {d : Directive} {z : Nat}
    (hd : LinkedProgram.exe.2[k]? = some (d, z)) {B : MachineState → Prop} {s : MachineData}
    (h : ∀ (R : MachineState → Prop) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects),
      (∀ s', B (s', LinkedProgram.exe.addrOf (k + 1)) → (next s').All R) →
      (∀ a s', B (s', a) → (jmp a s').All R) →
      (d.interp s ⟨LinkedProgram.exe.addrOf k, LinkedProgram.exe.addrOf (k + 1)⟩ next jmp).All R) :
    Eventually LinkedProgram.step B (s, LinkedProgram.exe.addrOf k) :=
  Eventually.step _ _ ⟨k, d, z, hd, rfl, h⟩ fun _ h => Eventually.done _ h
