module

import Kraken.X64.Parser
import Kraken.X64.Regs
import Kraken.X64.WP

/-! Tests for `Kraken.X64.WP`: the control-flow encodings and a concrete `Host`. -/

open Kraken.X64.Parser in
example : parse("jmp sym
  jnz sym
  call sym
  ret") = [.jmpTo "sym", .jccTo .nz "sym", .callTo "sym", .ret] := rfl

namespace WPTests

private def prog : Program := [.jmpTo "L", .label "L", .ret]

@[instance_reducible] private def layout : Layout := { start := 0x1000, size := fun i => if i = 1 then 0 else 2 }

private abbrev host : Host :=
  .ofLayout prog layout
    (fun i d hd hz => by
      have hz' : (if i = 1 then 0 else 2) = 0 := hz
      have hi : i = 1 := by
        by_cases h : i = 1
        · exact h
        · simp [h] at hz'
      subst hi
      simp only [prog, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
      exact ⟨"L", hd.symm⟩)
    (by decide)

attribute [local instance] host

private theorem labelsUnique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

/-- `jmp L; L: ret` returns to the address on the stack, with `rsp` 8 higher. -/
private theorem jmp_ret (s : MachineData) (ra : Int64) (R : DataMem → Prop)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.rsp = s.regs.rsp + 8)
      ⟨s, Host.addrOf 0⟩ := by
  have hk : Host.prog[1]? = some (.label "L") := rfl
  apply Host.eventually_jmp (k := 1) (L := "L") rfl hk (labelsUnique.first hk)
  apply Host.eventually_label hk
  exact Host.eventually_ret (i := 2) rfl hmem (.done _ ⟨rfl, rfl⟩)

end WPTests

namespace WPTests.Counter

/-- `L` is defined twice; the jump at index 1 sits between the two definitions. -/
private def prog : Program := [.label "L", .jmpTo "L", .label "L"]

@[instance_reducible] private def layout : Layout :=
  { start := 0x1000, size := fun i => if i = 1 then 2 else 0 }

private abbrev host : Host :=
  .ofLayout prog layout
    (fun i d hd hz => by
      have hz' : (if i = 1 then 2 else 0) = 0 := hz
      rcases i with _ | _ | _ | i
      · simp only [prog, List.getElem?_cons_zero, Option.some.injEq] at hd
        exact ⟨"L", hd.symm⟩
      · simp at hz'
      · simp only [prog, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
        exact ⟨"L", hd.symm⟩
      · simp [prog] at hd)
    (by decide)

attribute [local instance] host

/--
The first-definition hypothesis of `Host.eventually_jmp` cannot be dropped: index 1 is `jmp L` and
index 2 is `.label L`, but the jump goes to the first `L`, at the address of the jump itself.
-/
private theorem jmp_needs_first_definition :
    Host.prog[1]? = some (.jmpTo "L") ∧ Host.prog[2]? = some (.label "L") ∧
    ∃ (post : @Post MachineState) (s : MachineData),
      Eventually (step1 Host.exe) post ⟨s, Host.addrOf 2⟩ ∧
      ¬ Eventually (step1 Host.exe) post ⟨s, Host.addrOf 1⟩ := by
  refine ⟨rfl, rfl, fun st => st.pc = Host.addrOf 2, {}, .done _ rfl, ?_⟩
  have h01 : Host.addrOf 0 = Host.addrOf 1 := by decide
  have h12 : Host.addrOf 1 ≠ Host.addrOf 2 := by decide
  have hlab : Labels.label "L" = Host.addrOf 0 :=
    Host.label_eq_addrOf (k := 0) rfl (fun j hj => absurd hj (Nat.not_lt_zero j))
  have key : ∀ st, Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf 2) st →
      st.pc = Host.addrOf 1 → False := by
    intro st h
    induction h with
    | done st hp => exact fun hpc => h12 (hpc ▸ hp)
    | step st mid_p ht _ ih =>
      intro hpc
      obtain ⟨data, pc⟩ := st
      dsimp only at hpc
      subst hpc
      have hstep := (Host.step1_iff_interp (k := 1) (d := .jmpTo "L") rfl (by decide)).mp ht
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, Effects.All] at hstep
      rw [hlab, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel] at hstep
      exact ih _ hstep h01
  exact fun h => key _ h rfl

end WPTests.Counter
