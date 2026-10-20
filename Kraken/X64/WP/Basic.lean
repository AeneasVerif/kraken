module

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
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hd : Host.exe.program[k]? = some {directive := d, size := Kraken.Layout.size Directive k} := by
    rw [Host.exe_getElem?, hdp.cons.1]
    rfl
  rw [Host.addrOf_succ hdp.cons.1] at h
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Directive k) with h0 | hz
  · rw [h0] at hd h
    rw [Host.inert_of_size_zero (List.mem_of_getElem? hd)] at h
    have h0' : Host.addrOf k + Int64.ofNat 0 = Host.addrOf k := by simp
    simp only [Effects.All, h0'] at h
    exact Eventually.done _ h
  · refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
    have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
      ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
        Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
    unfold step1 Executable.step
    change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k) _).All post
    rw [hat]
    exact (Directives.interp_inert_append hinert _ _ _ _).mpr h

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
