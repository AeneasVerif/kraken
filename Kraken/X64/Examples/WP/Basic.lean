module

public import Kraken.X64.WP.Instance
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

theorem p1_correct [Host] [layout : Layout] [Layout.Valid] (hp : p1.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.1.regs.rax = 1) (s, startAddr hp) := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [p1] with finish

theorem swap_correct [Host] [layout : Layout] [Layout.Valid] (hp : swap.IsInfix Host.prog) (d : MachineData) :
    Eventually (step1 Host.exe)
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, startAddr hp) := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [swap] with finish

theorem p2_correct [Host] [layout : Layout] [Layout.Valid] (hp : p2.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.1.regs.rax = 2) (s, startAddr hp) := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [p2] with finish

theorem p4_correct [Host] [layout : Layout] [Layout.Valid] (hp : p4.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.1.regs.rax = 1) (s, startAddr hp) := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [p4] with finish

theorem p5_correct [Host] [layout : Layout] [Layout.Valid] (hp : p5.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.1.regs.rax = 0) (s, startAddr hp) := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [p5] with finish

end State
