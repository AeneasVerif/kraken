module

/-
The small examples of the baseline, through the state wp: the straight-line
programs `p1`, `p4`, `p5` and `swap`, and `p2`, whose conditional jump back to
its start is not taken. Each theorem states the baseline proposition over the
baseline's own program text, as an `Eventually` statement.
-/
public import Kraken.StateCfg
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

theorem p1_correct [Host] (hp : p1.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.data.regs.rax = 1) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .exit => t.regs.rax = 1
      | _ => t = s)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem swap_correct [Host] (hp : swap.IsInfix Host.prog) (d : MachineData) :
    Eventually (step1 Host.exe)
      (fun s' =>
          s'.data.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.data.regs.get Reg.rbx = d.regs.get Reg.rax)
      ⟨d, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [swap] with finish

theorem p2_correct [Host] (hp : p2.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.data.regs.rax = 2) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .exit => t.regs.rax = 2
      | _ => t = s)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem p4_correct [Host] (hp : p4.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.data.regs.rax = 1) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .exit => t.regs.rax = 1
      | _ => t = s)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem p5_correct [Host] (hp : p5.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun s => s.data.regs.rax = 0) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry | .label "start" => t = s
      | .label _ => t.regs.rax = 1 ∧ t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rax = 0)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State
