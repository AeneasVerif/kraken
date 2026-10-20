module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

/-
# What `Eventually` proves and `Program.wp` refutes

Each example is a fragment `p` followed by host code `q`. An `Eventually` statement about `p`
asks for a state at the end address of `p`, the address right after its last directive. The run
reaches that address, but not only by falling off the end of `p`: host code can bring it there.
`Eventually` accepts any such arrival, so it proves posts that `p` does not establish.
`Program.wp` refutes them, in every host program that embeds `p`.
-/

namespace State.EventuallySurprises

variable [Host] [FunDecls]

omit [FunDecls] in
theorem fallthrough_step {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {d : MachineData} {U J : MachineState → Prop}
    (z₀ : MachineState) (h : Host.exe.StepIn U J ⟨d, Host.addrOf k⟩) :
    (c.directive.interp d ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩)
      (fun _ _ => .done z₀)).All (fun z => U z ∨ z = z₀) :=
  Host.stepIn_elim (P := fun z => U z ∨ z = z₀) (ret := Effects.done) (jmp := fun _ => .done z₀) hc hz h
    (fun _ h => Or.inl h) (fun _ _ => Or.inr rfl)

omit [FunDecls] in
theorem jump_step {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) {d : MachineData} {U J : MachineState → Prop}
    (z₀ : MachineState) (h : Host.exe.StepIn U J ⟨d, Host.addrOf k⟩) :
    (c.directive.interp d ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun _ => .done z₀)
      (fun a s' => .done ⟨s', a⟩)).All (fun z => J z ∨ z = z₀) :=
  Host.stepIn_elim (P := fun z => J z ∨ z = z₀) (ret := fun _ => .done z₀) (jmp := Effects.done) hc hz h
    (fun _ _ => Or.inr rfl) (fun _ h => Or.inl h)

local macro "step_simp" : tactic =>
  `(tactic| simp only [List.getElem_cons_succ, List.getElem_cons_zero, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All,
      ite_true, Int64.ofBitVec_toBitVec, Int64.add_sub_self_left])

local macro "step_simp" " at " h:ident : tactic =>
  `(tactic| simp only [List.getElem_cons_succ, List.getElem_cons_zero, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All,
      ite_true, Int64.ofBitVec_toBitVec, Int64.add_sub_self_left] at $h:ident)


local macro "pc_mem" : tactic =>
  `(tactic| repeat (first | exact rfl | exact Or.inl rfl | apply Or.inr))

set_option hygiene false in
local macro "estep " i:num " [" ids:ident,* "]" : tactic =>
  `(tactic| (
    apply step_cps
    apply Host.step1_addrOf (hcell $i (by decide)) (Host.instr_size_pos _ _ (hP $i (by decide)) (by rintro ⟨⟩))
    simp only [$[$ids:ident],*, List.cons_append, List.nil_append]
    step_simp))

/-! ## A second arrival at the end

`p` sets `rax = 7` and falls off its end. The host code `q` right after it sets `rax = 8` and
jumps back to the end of `p`. `Eventually` proves both that the run reaches the end of `p` with
`rax = 7` and that it reaches the end of `p` with `rax = 8`. `Program.wp` takes the first arrival:
it proves `rax = 7` and refutes `rax = 8`. -/

def p₁ : Program := parse("
  mov $7, %rax")

def q₁ : Program := parse("
back:
  mov $8, %rax
  jmp back")

omit [FunDecls] in
theorem p₁_ends_rax7_eventually {k : Nat} (hk : (p₁ ++ q₁).IsInfixAt Host.prog k) (s : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + p₁.length) ∧ st.data.regs.get64 .rax = 7) ⟨s, Host.addrOf k⟩ := by
  have hP : ∀ i (h : i < (p₁ ++ q₁).length), Host.prog[k + i]? = some (p₁ ++ q₁)[i] := fun i h =>
    List.isInfixAt_iff_getElem?.mp hk i h
  have hcell : ∀ i (h : i < (p₁ ++ q₁).length), Host.exe.program[k + i]? =
      some {directive := (p₁ ++ q₁)[i], size := Kraken.Layout.size Directive (k + i)} := by
    intro i h; rw [Host.exe_getElem?, hP i h]; rfl
  rw [show p₁.length = 1 from rfl]
  estep 0 [p₁, q₁]
  exact .done _ ⟨rfl, by simp⟩

omit [FunDecls] in
theorem p₁_ends_rax8_eventually {k : Nat} (hk : (p₁ ++ q₁).IsInfixAt Host.prog k) (s : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + p₁.length) ∧ st.data.regs.get64 .rax = 8) ⟨s, Host.addrOf k⟩ := by
  have hP : ∀ i (h : i < (p₁ ++ q₁).length), Host.prog[k + i]? = some (p₁ ++ q₁)[i] := fun i h =>
    List.isInfixAt_iff_getElem?.mp hk i h
  have hcell : ∀ i (h : i < (p₁ ++ q₁).length), Host.exe.program[k + i]? =
      some {directive := (p₁ ++ q₁)[i], size := Kraken.Layout.size Directive (k + i)} := by
    intro i h; rw [Host.exe_getElem?, hP i h]; rfl
  have hlab : Host.prog[k + 1]? = some (.label "back") := hP 1 (by decide)
  have h12 : Host.addrOf (k + 1) = Host.addrOf (k + 2) := by
    rw [Host.addrOf_succ hlab, Host.label_size _ _ hlab]; simp
  have hback : label "back" = Host.addrOf (k + 1) := Host.label_eq (i := 1) hk rfl
  rw [show p₁.length = 1 from rfl]
  estep 0 [p₁, q₁]
  simp only [Nat.add_zero]
  rw [h12]
  estep 2 [p₁, q₁]
  estep 3 [p₁, q₁]
  exact .done _ ⟨hback.trans h12, by simp⟩

theorem p₁_ends_rax7 (s : MachineData) :
    WP.wp p₁ (fun _ t => t.regs.get64 .rax = 7) (fun _ _ => False) s := by
  kvcgen64 [p₁] with finish

theorem p₁_not_ends_rax8 [H : Embeds p₁] (s : MachineData) :
    ¬ WP.wp p₁ (fun _ t => t.regs.get64 .rax = 8) (fun _ _ => False) s := by
  intro hw
  have hw : Program.wp p₁ (fun st => st.data.regs.get64 .rax = 8) (fun _ => False) s := hw
  rw [Program.wp_eq] at hw
  have hw := @hw H
  have hk := H.embedding.isInfixAt
  change While (fun st : MachineState => st.pc ≠ Host.addrOf (H.embedding.start + p₁.length)) _ _
    (⟨s, Host.addrOf H.embedding.start⟩ : MachineState) at hw
  generalize H.embedding.start = k at hk hw
  have hP : Host.prog[k + 0]? = some p₁[0] := List.isInfixAt_iff_getElem?.mp hk 0 (by decide)
  have hcell : Host.exe.program[k + 0]? =
      some {directive := p₁[0], size := Kraken.Layout.size Directive (k + 0)} := by
    rw [Host.exe_getElem?, hP]; rfl
  have hz := Host.instr_size_pos _ _ hP (by rintro ⟨⟩)
  have hne := Host.addrOf_succ_ne hcell hz
  refine While.not_of_inv (fun y => y.pc = Host.addrOf (k + 0) ∨
      (y.pc = Host.addrOf (k + 0 + 1) ∧ y.data.regs.get64 .rax = 7)) ?_ ?_ (Or.inl rfl) hw
  · rintro ⟨d, pc⟩ (hpc | ⟨-, h7⟩) hc h8
    · exact hc (by rw [hpc]; exact hne)
    · simp only at h7 h8; rw [h7] at h8; exact absurd h8 (by decide)
  · rintro U ⟨d, pc⟩ (hpc | ⟨hpc, -⟩) hc hb
    · dsimp only at hpc
      subst hpc
      have h := fallthrough_step hcell hz ⟨d, Host.addrOf (k + 0)⟩ hb
      simp only [p₁] at h
      step_simp at h
      rcases h with h | h
      · exact ⟨_, h, Or.inr ⟨rfl, by simp⟩⟩
      · exact absurd (congrArg MachineState.pc h) hne.symm
    · exact absurd hpc hc

/-! ## An arrival through host code

`p` jumps to `away`, a label of the host code `q`. The host code sets `rax = 8` and jumps to the
end of `p`. `Eventually` proves that the run reaches the end of `p` with `rax = 8`, although `p`
never falls off its end. `Program.wp` refutes every spec of `p` without an exit: `away` is no
label of `p`, so the run of `p` exits there. -/

def p₂ : Program := parse("
  jmp away")

def q₂ : Program := parse("
halt:
  jmp halt
away:
  mov $8, %rax
  jmp halt")

omit [FunDecls] in
theorem p₂_ends_rax8_eventually {k : Nat} (hk : (p₂ ++ q₂).IsInfixAt Host.prog k) (s : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + p₂.length) ∧ st.data.regs.get64 .rax = 8) ⟨s, Host.addrOf k⟩ := by
  have hP : ∀ i (h : i < (p₂ ++ q₂).length), Host.prog[k + i]? = some (p₂ ++ q₂)[i] := fun i h =>
    List.isInfixAt_iff_getElem?.mp hk i h
  have hcell : ∀ i (h : i < (p₂ ++ q₂).length), Host.exe.program[k + i]? =
      some {directive := (p₂ ++ q₂)[i], size := Kraken.Layout.size Directive (k + i)} := by
    intro i h; rw [Host.exe_getElem?, hP i h]; rfl
  have hlab : Host.prog[k + 3]? = some (.label "away") := hP 3 (by decide)
  have haway : label "away" = Host.addrOf (k + 4) := by
    rw [Host.label_eq (i := 3) hk rfl, Host.addrOf_succ hlab, Host.label_size _ _ hlab]; simp
  have hhalt : label "halt" = Host.addrOf (k + 1) := Host.label_eq (i := 1) hk rfl
  rw [show p₂.length = 1 from rfl]
  estep 0 [p₂, q₂]
  rw [haway]
  estep 4 [p₂, q₂]
  estep 5 [p₂, q₂]
  exact .done _ ⟨hhalt, by simp⟩

theorem p₂_no_wp [H : Embeds p₂] (Q : Unit → MachineData → Prop) (s : MachineData) :
    ¬ WP.wp p₂ Q (fun _ _ => False) s := by
  intro hw
  have hw : Program.wp p₂ (fun st => Q () st.data) (fun _ => False) s := hw
  rw [Program.wp_eq] at hw
  have hw := @hw H
  have hk := H.embedding.isInfixAt
  change While (fun st : MachineState => st.pc ≠ Host.addrOf (H.embedding.start + p₂.length)) _ _
    (⟨s, Host.addrOf H.embedding.start⟩ : MachineState) at hw
  generalize H.embedding.start = k at hk hw
  have hP : Host.prog[k + 0]? = some p₂[0] := List.isInfixAt_iff_getElem?.mp hk 0 (by decide)
  have hcell : Host.exe.program[k + 0]? =
      some {directive := p₂[0], size := Kraken.Layout.size Directive (k + 0)} := by
    rw [Host.exe_getElem?, hP]; rfl
  have hz := Host.instr_size_pos _ _ hP (by rintro ⟨⟩)
  have hne := Host.addrOf_succ_ne hcell hz
  refine While.not_of_inv (fun y => y.pc = Host.addrOf (k + 0)) ?_ ?_ rfl hw
  · rintro ⟨d, pc⟩ hpc hc -
    exact hc (by dsimp only at hpc; rw [hpc]; exact hne)
  · rintro U ⟨d, pc⟩ hpc - hb
    dsimp only at hpc
    subst hpc
    have h := jump_step hcell hz ⟨{ d with regs := d.regs.set64 .rax (d.regs.get64 .rax + 1) },
      Host.addrOf (k + 0)⟩ hb
    simp only [p₂] at h
    step_simp at h
    rcases h with h | h
    · rw [Executable.StepOut.of_not_below_data (Program.WP.MachineData.not_stackBelow_self d)] at h
      unfold Program.ContinueOnInternalExit at h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by rintro ⟨⟨l, hl, -⟩, -⟩; simp at hl))] at h
      exact h.elim
    · have := congrArg (fun z : MachineState => z.data.regs.get64 .rax) h
      simp only [Reg64s.get64_set64, ite_true] at this
      bv_omega

end State.EventuallySurprises
