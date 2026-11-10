module

import Kraken.AArch64.Parser
import Kraken.AArch64.Regs
import Kraken.AArch64.WP

/-! Tests for `Kraken.AArch64.WP`: the control-flow encodings and a concrete `Host`. -/

open Kraken.AArch64.Parser in
example : parseAArch64("b sym
  b.ne sym
  bl sym
  ret
  cbz x0, sym
  cbnz w1, sym") =
    [Directive.bTo "sym", Directive.bCondTo .NE "sym", Directive.blTo "sym", Directive.ret,
      Directive.cbzTo (w := .W64) (.reg .X0) "sym", Directive.cbnzTo (w := .W32) (.reg .X1) "sym"] :=
  rfl

namespace WPTests

private def prog : Program := [.blTo "f", .bTo "e", .label "f", .ret, .label "e"]

@[instance_reducible] private def layout : Layout :=
  { start := 0x1000, size := fun i => if i = 2 ∨ i = 4 then 0 else 4 }

private abbrev host : Host :=
  .ofLayout prog layout
    (fun i d hd hz => by
      have hz' : (if i = 2 ∨ i = 4 then 0 else 4) = 0 := hz
      rcases i with _ | _ | _ | _ | _ | i
      · simp at hz'
      · simp at hz'
      · simp only [prog, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
        exact ⟨"f", hd.symm⟩
      · simp at hz'
      · simp only [prog, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
        exact ⟨"e", hd.symm⟩
      · simp [prog] at hd)
    (by decide)

attribute [local instance] host

private theorem labelsUnique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

/-- `bl f; b e; f: ret; e:` calls `f`, returns, and reaches the end with `x30` set by `bl`. -/
private theorem bl_ret (s : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf 5 ∧ st.data.regs.X30 = (Host.addrOf 1).toUInt64)
      ⟨s, Host.addrOf 0⟩ := by
  have hf : Host.prog[2]? = some (.label "f") := rfl
  have he : Host.prog[4]? = some (.label "e") := rfl
  apply Host.eventually_bl (k := 2) rfl hf (labelsUnique.first hf)
  apply Host.eventually_label hf
  apply Host.eventually_ret (i := 3) (ra := Host.addrOf 1) rfl rfl
  apply Host.eventually_b (k := 4) rfl he (labelsUnique.first he)
  apply Host.eventually_label he
  exact .done _ ⟨rfl, rfl⟩

end WPTests
