module

import Kraken.AArch64.Parser
import Kraken.AArch64.Regs
import Kraken.AArch64.WP

/-! Tests for `Kraken.AArch64.WP`: the control-flow encodings and a concrete `Host`. -/

open Kraken.AArch64.Parser in
example : ⸨prog|
  b sym
  b.ne sym
  bl sym
  br x8
  blr x8
  ret
  cbz x0, sym
  cbnz w1, sym
  tbz x0, #3, sym
  tbnz w1, #5, sym ⸩ =
    [Directive.bTo "sym", Directive.bCondTo .NE "sym", Directive.blTo "sym",
      Directive.br (.reg .X8), Directive.blr (.reg .X8), Directive.ret,
      Directive.cbzTo (w := .W64) (.reg .X0) "sym", Directive.cbnzTo (w := .W32) (.reg .X1) "sym",
      Directive.tbzTo (w := .W64) (.reg .X0) 3 "sym",
      Directive.tbnzTo (w := .W32) (.reg .X1) 5 "sym"] :=
  rfl

namespace WPTests

private def prog : Program := [.blTo "f", .bTo "e", .label "f", .ret, .label "e"]

@[instance_reducible] private def layout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

private abbrev host : Host := .ofLayout prog layout (by decide)

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

namespace WPTests.Indirect

private def prog : Program :=
  [.blr (.reg .X30), .br (.reg .X8), .label "f", .ret, .label "e"]

@[instance_reducible] private def layout : Layout :=
  { start := 0x2000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

private abbrev host : Host := .ofLayout prog layout (by decide)

attribute [local instance] host

/-- `blr x30` reads `x30` before overwriting it with `ra`; `ret` returns and `br x8` exits. -/
private theorem blr_x30_br (s : MachineData)
    (hx30 : s.regs.X30 = (Host.addrOf 2).toUInt64)
    (hx8 : s.regs.X8 = (Host.addrOf 4).toUInt64) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf 5 ∧ st.data.regs.X30 = (Host.addrOf 1).toUInt64)
      ⟨s, Host.addrOf 0⟩ := by
  have hf : Host.prog[2]? = some (.label "f") := rfl
  have he : Host.prog[4]? = some (.label "e") := rfl
  apply Host.eventually_blr (i := 0) (r := .reg .X30) (tgt := Host.addrOf 2) rfl
    (by simp [Reg64s.getXReg, hx30])
  apply Host.eventually_label hf
  apply Host.eventually_ret (i := 3) (ra := Host.addrOf 1) rfl rfl
  apply Host.eventually_br (i := 1) (r := .reg .X8) (tgt := Host.addrOf 4) rfl
    (by simp [Reg64s.getXReg, Reg64s.setXReg, hx8])
  apply Host.eventually_label he
  exact .done _ ⟨rfl, rfl⟩

end WPTests.Indirect

namespace WPTests.Tbz

private def prog : Program :=
  [.tbzTo (w := .W64) (.reg .X0) 3 "zero", .tbnzTo (w := .W32) (.reg .X1) 5 "nz",
   .label "zero", .label "nz"]

@[instance_reducible] private def layout : Layout :=
  { start := 0x3000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

private abbrev host : Host := .ofLayout prog layout (by decide)

attribute [local instance] host

private theorem labelsUnique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

/-- `tbz x0, #3, zero` jumps when bit 3 is clear, and falls through to `tbnz` otherwise. -/
private theorem tbz_tbnz (s : MachineData)
    (hx0 : (s.regs.X0.toBitVec).getLsbD 3 = true)
    (hx1 : ((s.regs.X1.toBitVec).setWidth 32).getLsbD 5 = true) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf 4) ⟨s, Host.addrOf 0⟩ := by
  have hz : Host.prog[2]? = some (.label "zero") := rfl
  have hn : Host.prog[3]? = some (.label "nz") := rfl
  apply Host.eventually_tbz (k := 2) rfl hz (labelsUnique.first hz)
  simp only [Reg64s.getRegOrZr_reg64, Reg64s.getXReg, hx0, ↓reduceIte]
  apply Host.eventually_tbnz (k := 3) rfl hn (labelsUnique.first hn)
  simp only [Reg64s.getRegOrZr_reg32, Reg64s.getXReg, hx1, ↓reduceIte]
  apply Host.eventually_label hn
  exact .done _ rfl

end WPTests.Tbz
