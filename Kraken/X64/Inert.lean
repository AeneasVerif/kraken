module

public import Kraken.X64.Semantics

@[expose] public section

def Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s p (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
    d.interp s p next jmp = next s

theorem Directives.interp_inert_append [Labels] {pre rest : List (Directive × Nat)}
    (hpre : ∀ c ∈ pre, c.2 = 0 ∧ c.1.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc))
