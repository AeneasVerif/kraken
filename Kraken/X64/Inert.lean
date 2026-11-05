module

public import Kraken.X64.OmniSemantics

@[expose] public section

/--
`d` is inert if it falls through with the same machine state and no observable effect.

Inertness is only required of directives occupying no space, so `d` is run on an empty range.
Presently, labels, empty byte arrays, empty alignment padding, and no-op instructions like `nop`
and `mov %rax, %rax` are inert.
-/
def Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s (pc : Int64) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) post,
    (d.interp s ⟨pc, pc⟩ next jmp).All post ↔ (next s).All post

theorem Layout.inert_of_mem (l : Layout) {p : Program} {c : Kraken.Sized Directive}
    (hc : c ∈ (l p).program) (h : c.size = 0) : c.directive.Inert := by
  obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp hc
  generalize p[i] = d at h ⊢; cases d with
  | instr _ => exact absurd h (Nat.ne_of_gt (l.instrSize i).property)
  | label _ | nopalign _ => exact fun _ _ _ _ _ => Iff.rfl
  | align _ _ => intro _ _ _ _ _ _; simp [Directive.interp]
  | byteArray b =>
    intro _ _ _ _ _ _
    simp [Directive.interp, ByteArray.isEmpty, show b.size = 0 from h]

theorem Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) (post : @Post MachineState) :
    (Directives.interp (pre ++ rest) s pc ret).All post ↔ (Directives.interp rest s pc ret).All post := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc)) s
