module

public import Kraken.X64.OmniSemantics
public import Kraken.X64.WP.Host

/-
# Weakest precondition of a fragment of a host program

`Program.wp p Q E s` is the weakest precondition of the fragment `p` in the ambient, laid out `Host`
program.
This definition is the bridge to `Std.WP` and thus `vcgen`.

The definition of `wp` works by
1. considering the weakest precondition `step1 Host.exe` of a single instruction in the laid out
   executable,
2. taking the least fixpoint of `X ↦ post ∪ step1 X` via `Eventually step1`, the set of pre states
   which inevitably reach the postcondition, and crucially,
3. considering every possible way in which the fragment `p` may occur in the `Host` program.
   Only properties can be proved that hold for *all possible infix positions* of the fragment `p`.
   This ensures proof modularity.

The `Host` program is a parameter to be able to reason compositionally about function calls.
It is an instance implicit parameter so that uses refer implicitly to an ambient host program
without users needing to specify it explicitly everywhere.
-/

/-- Weakest precondition of a `Program` fragment embedded in a host program. -/
@[expose] public def Program.wp [Host] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.IsInfixAt Host.prog k →
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + p.length) ∧ Q st.data) ∨ E st.pc st.data)
      ⟨s, Host.addrOf k⟩

public theorem Program.wp_mono [Host] {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.wp p Q₁ E₁ s) : Program.wp p Q₂ E₂ s :=
  fun k hk => eventually_trans _ _ _ _ (h k hk) fun _ hb => Eventually.done _ <|
    hb.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)

public theorem Program.wp_cons [Host] {d : Directive} {p : Program} {Q : MachineData → Prop}
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

section
variable [Host]

public theorem Host.eventually_of_interp {k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt Host.prog k) {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  _root_.eventually_of_interp Host.addr_determines_offset hdp.cons.1 h

end

/--
Soundness of `Program.wp`: if `p` is a fragment of a `Host` program at index `k` and `p.wp Q E s`
holds, then `p` eventually reaches the postcondition `Q` at the fall-through address or the error
condition `E` from the initial state `s`.
-/
public theorem Program.step1_of_wp_at [Host] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} {k : Nat} (hk : p.IsInfixAt Host.prog k) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post ⟨s', Host.addrOf (k + p.length)⟩) (hE : ∀ a s', E a s' → post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hwp k hk)
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha
    rw [ha]
    exact hQ s' hq
  · exact hE a s' he

/--
Soundness of `Program.wp`, cf. `Program.step1_of_wp_at`. In comparison to `Program.step1_of_wp_at`,
this theorem asserts a fact about the first occurrence of the fragment in the `Host` program, rather
than the occurrence at a specific index `k`. When there is only a single occurrence of the fragment,
it has the same meaning as `Program.step1_of_wp_at` and is a bit simpler to read.
-/
public theorem Program.step1_of_wp [Host] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} (h : p.IsInfix Host.prog) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post ⟨s', endAddr h⟩) (hE : ∀ a s', E a s' → post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, startAddr h⟩ :=
  Program.step1_of_wp_at (List.isInfixAt_infixIdx h) hwp hQ hE
