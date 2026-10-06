module

public import Kraken.X64.WP.Instance
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

theorem p1_correct [layout : Layout] [Kraken.Executable.Assembled (layout p1)] (s : MachineData) :
    Eventually (straightlineStep (layout p1)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  apply Program.WP.straightline_of_wp
  kvcgen64 [p1] with finish

theorem swap_correct [layout : Layout] [Kraken.Executable.Assembled (layout swap)] (d : MachineData) :
    Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply Program.WP.straightline_of_wp
  kvcgen64 [swap] with finish

theorem p2_correct [layout : Layout] [Kraken.Executable.Assembled (layout p2)] (s : MachineData) :
    Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply Program.WP.straightline_of_wp
  kvcgen64 [p2] with finish

theorem p4_correct [layout : Layout] [Kraken.Executable.Assembled (layout p4)] (s : MachineData) :
    Eventually (straightlineStep (layout p4)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  apply Program.WP.straightline_of_wp
  kvcgen64 [p4] with finish

theorem p5_correct [layout : Layout] [Kraken.Executable.Assembled (layout p5)] (s : MachineData) :
    Eventually (straightlineStep (layout p5)) (fun s => s.1.regs.rax = 0) (s, layout.start) := by
  apply Program.WP.straightline_of_wp
  kvcgen64 [p5] with finish

end State
