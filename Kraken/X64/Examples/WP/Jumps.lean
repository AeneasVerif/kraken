module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.Jumps

example [Host] [FunDecls] (l : Label) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) (hq : Q () s) :
    WP.wp ([Directive.label l]) Q E s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | _ => Q () t)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def jmpNext : Program := parse("
  jmp next
next:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jmpNext (fun _ t => t.regs.get64 .rax = 2) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => t.regs.rsp = s.regs.rsp
      | .exit => t.regs.get64 .rax = 2)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def decMid : Program := parse("
top:
  dec %rcx
  jnz top
  mov $1, %rax")

example [Host] [FunDecls] (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
    WP.wp decMid (fun _ t => t.regs.rcx = 0 ∧ t.regs.rax = 1) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => 0 < t.regs.rcx.toNat ∧ t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rcx = 0 ∧ t.regs.rax = 1)
    (fun _ t => t.regs.rcx.toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def jmpOver : Program := parse("
  jmp done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) (h : s.regs.rbx = 0) :
    WP.wp jmpOver (fun _ t => t.regs.rbx = 0 ∧ t.regs.rax = 2) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => t.regs.rbx = 0 ∧ t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rbx = 0 ∧ t.regs.rax = 2)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def jmpGap : Program := parse("
  jmp b
a:
b:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jmpGap (fun _ t => t.regs.rax = 2) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rax = 2)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def jccOver : Program := parse("
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] [FunDecls] (s : MachineData) :
    WP.wp jccOver (fun _ t => t.regs.rax = 2) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rax = 2)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def countdown : Program := parse("
top:
  dec %rcx
  jnz top")

example [Host] (hp : countdown.IsInfix Host.prog) (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rcx = 0) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => 0 < t.regs.rcx.toNat ∧ t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rcx = 0)
    (fun _ t => t.regs.rcx.toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

def skip : Program := parse("
start:
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] (hp : skip.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rax = 2) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label _ => t.regs.rsp = s.regs.rsp
      | .exit => t.regs.rax = 2)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State.Jumps
