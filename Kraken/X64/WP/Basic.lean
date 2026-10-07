module

public import Kraken.X64.OmniSemantics
public import Kraken.Data.List.Infix

/-
# Weakest precondition of a fragment of a host program

An executable defines a transition system over the machine states.

`Executable.step'` below encodes the must-predecessor relation of the transition system.
Given a set of successor machine states `post`, `exe.step' st post` holds iff
`∀ st', (st ⤳[exe] st') → st' ∈ P`.
This definition is expressed in terms of `Directive.interp`, which is considered ground truth.

`Program.wp` packages up the `Executable`-induced predecessor relation into a notion of weakest
precondition on `Program` fragments occuring in a particular `Host` program, given a particular
`Layout` decision. Typical use universally quantifies over both `Host` and `Layout` and constrains
only where necessary.

This definition is the bridge to `Std.WP` and thus `vcgen`. The definition of `wp` works by
1. taking the least fixpoint of the predecessor relation via `Eventually`
   (equivalent notions of `lfp` exist) so that it applies to a sequence
   of directives, and crucially
2. considering every possible way in which the sequence of directives
   may occur in the host program.
   Only properties can be proved that hold for *all possible infix positions* of the `Program` fragment.
   The host program is a parameter to be able to express function calls compositionally.
   It is an instance implicit parameter so that uses refer implicitly to an ambient host program
   without users needing to specify it explicitly everywhere.

Side note: Cousot calls `Executable.step'` the "dual preimage property transformer" in his
2021 book "Principles of Abstract Interpretation", as a starting point for theory exploration.
-/

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

/-- The predecessor relation of the transition system induced by an executable. -/
-- This could replace `step` in the future. It doesn't rely on `Directives.interp` and
-- it is otherwise equivalent, given the usual assumptions about an `Executable`.
@[expose] public def step' (exe : Executable Directive)
    (st : MachineState) (P : MachineState → Prop) : Prop :=
  match exe.fetch? st.2 with
  | none => False
  | some (d, z) =>
    let next := st.2 + .ofNat z
    haveI := Executable.labels exe
    (d.interp st.1 ⟨st.2, next⟩ (fun s => .done (s, next)) (fun a s => .done (s, a))).All P

end Kraken.Executable

-- TODO: I think the below isn't really x64 specific and should maybe go into the Kraken namespace?!
-- Although there is no definition `Kraken.Program`. I'm just confused.

public class Host where
  prog : Program
  labels_nodup : (Program.labels prog).Nodup

public instance [Host] [layout : Layout] : Labels := Executable.labels (layout Host.prog)

/-- A set of abstract assumptions about the `Layout` of a `Host` program that most specs need and
that every reasonable assembler satisfies. -/
public class Layout.Valid [Host] [layout : Layout] : Prop where
  /-- Labels have size zero. -/
  label_size : ∀ i l, Host.prog[i]? = some (.label l) → Kraken.Layout.size Directive i = 0
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, Host.prog[i]? = some d → Kraken.Layout.size Directive i = 0 → d.Inert
  /-- The laid out executable fits into 2^64 bytes of address space. -/
  fits : ∀ j k m, j ≤ m → m < k → k ≤ Host.prog.length →
    (layout Host.prog).addrOf j = (layout Host.prog).addrOf k → Kraken.Layout.size Directive m = 0

/-- Weakest precondition of a `Program` fragment embedded in a host program. -/
@[expose] public def Program.wp [Host] [layout : Layout] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.IsInfixAt Host.prog k →
    Eventually (layout Host.prog).step'
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
