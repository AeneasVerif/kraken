module

/- `p1`, `p2`, `p4`, `p5` and `swap` through the state wp, with the baseline's statements. -/
public import Kraken.StateWP
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped StateWP

set_option experimental.vcgen true

namespace State

theorem p1_correct [layout : Layout] (s : MachineData) :
    straightlineStep (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  apply straightlineStep_of_wp
  kvcgen64 [p1] with finish

theorem swap_correct [layout : Layout] (d : MachineData) :
    Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply eventually_straightlineStep_of_wp
  kvcgen64 [swap] with finish

theorem p2_correct [layout : Layout] (s : MachineData) :
    Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply eventually_straightlineStep_of_wp
  kvcgen64 [p2] with finish

theorem p4_correct [layout : Layout] (s : MachineData) :
    straightlineStep (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  apply straightlineStep_of_wp
  kvcgen64 [p4] with finish

theorem p5_correct [layout : Layout] (s : MachineData) :
    straightlineStep (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  apply straightlineStep_of_wp
  kvcgen64 [p5] with finish

end State
