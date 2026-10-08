module

public import Kraken.X64.WP.Host
public import Kraken.X64.WP.Step

/-
# Weakest precondition of a fragment of a host program

`Program.wp p Q E s` is the weakest precondition of the fragment `p` in the ambient `Host` program,
laid out by the ambient `Layout`. This definition is the bridge to `Std.WP` and thus `vcgen`.

The definition of `wp` works by
1. laying out the `Host` into an `Executable`, which in turn induces a transition system via
   `Executable.step'`,
2. taking the least fixpoint of `X ↦ post ∪ step' X` via `Eventually step'`, the set of pre states
   which inevitably reach the postcondition, and crucially,
3. considering every possible way in which the fragment `p` may occur in the `Host` program.
   Only properties can be proved that hold for *all possible infix positions* of the fragment `p`.
   This ensures proof modularity.

The `Host` program and `Layout` is a parameter to be able to reason compositionally about function
calls. It is an instance implicit parameter so that uses refer implicitly to an ambient host program
without users needing to specify it explicitly everywhere.
-/

/-- Weakest precondition of a `Program` fragment embedded in a host program. -/
@[expose] public def Program.wp [Host] [Layout] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.IsInfixAt Host.prog k →
    Eventually Host.exe.step'
      (fun st => (st.2 = Host.addrOf (k + p.length) ∧ Q st.1) ∨ E st.2 st.1)
      (s, Host.addrOf k)

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

section
variable [Host] [Layout] [hv : Layout.Valid]

public theorem Host.eventually_of_interp {k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt Host.prog k) {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done (s', Host.addrOf (k + 1))) (fun a s' => .done (s', a))).All post) :
    Eventually Host.exe.step' post (s, Host.addrOf k) := by
  have hd : Host.exe.2[k]? = some (d, Kraken.Layout.size Directive k) := by
    rw [Host.exe_getElem?, hdp.cons.1]
    rfl
  rw [Host.addrOf_succ hdp.cons.1] at h
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive k) with h0 | hz
  · rw [h0] at hd h
    rw [Host.inert_of_size_zero hd] at h
    have h0' : Host.addrOf k + Int64.ofNat 0 = Host.addrOf k := by simp
    simp only [Effects.All, h0'] at h
    exact Eventually.done _ h
  · refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    unfold Kraken.Executable.step'
    rw [Host.fetch?_addrOf hd hz]
    exact h

end
